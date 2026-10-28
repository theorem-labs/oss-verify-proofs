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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W17.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_enframe HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RF_ntf_A HP_RF_malloc_bigw HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W17 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmmap_entry"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W17.mm_ai"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W17.mm_st4"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_mmap_counter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.u32"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="hRP"] Lemma rmm_call_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W17 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))(3.$4.Lms',$5.(6.$5.R1.(7.(8.(9.&40.+40?88.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.(9.&40.=)R11.(9.&40.+3.)(9.&40.+22.)(9.&40.-1.)(9.&40.=)R14.R13.(9.&40.-1.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(9.&40.$:.)R3.(;.(0.&40.))R2.(<.$4.)))(7.(8.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)R3.(9.&40.+40?68.)R2.(;.(0.&40.))R1.(<.$4.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros. unfold rmmap_entry.
  step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="hRP"] Lemma rmm_ret_fail_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W17 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))(3.$4.Lms',$5.(6.$5.R1.(7.(8.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(9.&40.-1.)R18.R17.R16.R15.R14.R13.R12.(9.&40.-1.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(9.&40.+410;0.)R3.(;.(0.&40.))R2.(<.$4.)))(7.(8.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.-1.)R17.R16.R15.R14.R13.R12.R11.(9.&40.-1.)R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)R3.(9.&40.+40?88.)R2.(;.(0.&40.))R1.(<.$4.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= rceil.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00X0?L10824572241.70L11899637627.65L12378521055.72L13243977942.78L13568959351.67L15764576006.74L17212484973.63L17978446710.59L17980828837.60L18189295651.74L18192971005.73L21910439335.86L29007610482.71L3067974865.70 L31195403481.72L34324489854.71L35499711534.73L36495594395.68L37798740099.57L37926108622.71L39651076098.67L41352056401.70L41388557870.73L45093649260.64L45763430326.67L4587217297.70 L4783703437.73 L47871016736.78L51503707745.73L54383518033.63L54383848065.59L55347816901.63L55906581388.72L5808319357.59 L58686917929.72L59314923118.57L61081688940.72L62125365601.59L65104156229.59L7762923258.60 00000K00d01?02:02R03@03T03i04>04c05F05\06406B06^07;07O08508U09309K09g0:Y0:m0;E0;`0<;0<\0=30=J0=Z0>30>O0>\0?J0@00@K0@X0@m0AJS3st23cnt4size2nd2mt1G1d2K1S3st24size2nd1c2mt1G2CR1dS3st23cnt4size2nd2mt1G1d2GES3hRP3st24size2nd2xa2mt1G2SZ2ND1r3NDA2XA3XA23RCB1d1q4ND121HS3st24size2nd2mt1G1d3LENS3st23cnt4size2nd2mt1G3CNT2SZ2ND4Gpos1d2mn3MNRS3st24size2nd2mt1G1dS3st24size2nd2mt1G2SZS3st24size2nd2mt1G2SZS3st23cnt4size2nd2mt1G1d2mn3MNR3NE01nS3st23cnt4size2nd2mt1G1d2mn3MNR3NE0S3st24size2mt1G1d1r2H0S3st23cnt4size2nd2mt1G1dS2nd1G1d2D02D1S3st23cnt4size2nd2mt1G3CNT1dS3st23cnt4size2nd2mt1G1d2D01HS3st24size2nd2mt1G1dS3st24size2nd2mt1G2GI1d2HB5Ha_st5Hl_stS3hRP2nd2xa1G2ND2XA3XA23RCB4GposS3st23cnt4size2nd2mt1G3CNT1d1HS3st24size2nd2mt1G1d3LENS3st23cnt4size2nd2mt1G3CNT1dS3st23cnt4size2nd2mt1G3CNT2SZ2ND4Gpos1d2mn3MNR3NE0S3st24size2nd2mt1G1dS3st24size2nd2mt1G1d3LENS3st23cnt4size2nd2mt1G1d2K1S3st24size2nd2mt1G1d2D03NE0S3st24size2nd2mt1G2SZ1r3NDA1d1q1HS3st24size2nd2mt1G1d2mnS3st24size2nd2mt1G2ND1dS3st22nd2mt1G2NDS3st24size2nd1c2mt1G2CR1dS3st23cnt4size2nd2mt1G3CNT1dS3st22nd2mt1GS3st23cnt4size2nd2mt1G3CNT2SZ2ND4Gpos1d2mn3MNRS3hRP3st22nd2xa2mt1G2ND3XA23RCB4Gpos1KS3st23cnt4size2nd2mt1G1d2LTS3st22nd2mt1GS3st24size2nd2mt1G2SZS3st24size2nd2mt1G2SZ2ND4Gpos". (* [comment removed for export] *)
#[using="SC CNT SZ ND NDA XA XA2 MST REC HC CR"] Lemma rmm_ret_ok_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W17 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps7,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))P,(=.VhRP,Vst2,R1.)P,(>.$4.R2.)(3.$4.Lms',$5.(?.(0.&40.)La3',(0.&40.)(?.(0.&40.)La4',(0.&40.)(?.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(10.(6.$5.R4.(7.(8.R20.R1?.R1>.R1=.R1<.R1;.R1:.(9.&40.Vsc,)(9.&40.VG,)(9.&40.Vxa,)(9.&40.(11.Vcnt,+1.))(9.&40.(12.Vcnt,Vsize,))R3.R2.R15.R14.R13.(9.&40.-1.)(13.Vnd,)R12.R11.(9.&40.$14.)R10.(13.Vsize,)(13.Vcnt,)R?.R>.R=.R<.R;.R:.)R9.(9.&40.+40?>0.)R8.(;.(0.&40.))R1.(<.$4.)))(10.(15.(16.(17.$18.$18.)(19.$18.$18.VG,(1:.VG,+28.))(16.(17.$18.$18.)(19.$18.$18.(1:.$1;.+<.)(1:.$1;.+10.))(1<.(17.$18.$18.))))R7.R1.)(10.(1=.$4.R7.R1.)(10.(>.$4.R1.)(10.(=.VhRP,(1>.Vst2,Vnd,Vmt,)R1.)(6.$18.(1?.(20.(1>.Vst2,Vnd,Vmt,)))(21.(1:.Vc,+1.)))))))))))(7.(8.R1<.R1;.R1:.R19.R18.R17.R16.(9.&40.Vsc,)(9.&40.VG,)(9.&40.Vxa,)R15.R14.R13.R12.R11.R10.R?.(9.&40.-1.)(13.Vnd,)R>.R=.(9.&40.$14.)R<.(13.Vsize,)(13.Vcnt,)R;.R:.R9.R8.R7.R6.)R5.(9.&40.+40?88.)R4.(;.(0.&40.))R3.(<.$4.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until m. intros MR MI.
  pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  rceilb; unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
  clear K.
  (* [comment removed for export] *)
  step.
  rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
  rmeta_open G MUa WMa.
  step.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
  step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
  rewrite (divu_word 4080 size) by lia.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
  set (d := 4080 / size) in *.
  (* [comment removed for export] *)
  dpose MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. rewrite HC in CX1. unfold RCTX in CX1.
  step. rewrite (sx32_wz_sxv c) by lia.
  (* [comment removed for export] *)
  step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
  step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
  (* [comment removed for export] *)
  assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
  { unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
    change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia. }
  step.
  (* [comment removed for export] *)
  try replace (Z_to_bv 64 (sxv c + 1)) with (Z_to_bv 64 (bv_swrap 32 c + 1))
    by (symmetry; exact (unsigned_Z_to_bv_add (bv_swrap 32 c) 1)).
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
    [ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
    | clear MUa WMa H ] end.
  set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
  (* [comment removed for export] *)
  pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (512960 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
  clear CX1.
  st1.
  rewrite le4_swrap_succ by lia.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
  clear MR3.
  rraw_store_finish0 (512968 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
  assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
  { unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
  rewrite <- E4 in MR4.
  assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
    evt rsegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 512960) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x40fe0) fc None m' (seg_rom rsegs)
      /\ munch [(G, G + 40); (512968 + 12, 512968 + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 512960) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40fcc) fc None mX (seg_rom rsegs))) end.
  { intros a2v mn Hmn ->.
    assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
    replace (cnt + -1) with (cnt - 1) by lia.
    assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
    { unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
      destruct (Z.ltb_spec cnt d) as [LT|GE].
      - replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
        destruct (Z.eqb_spec d 0) as [E0|NE0].
        + rewrite E0. reflexivity.
        + replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
                  = Z_to_bv 64 (mm_ai cnt size)).
    { rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
      destruct (Z.eqb_spec mn 0) as [E0|NE0].
      - rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
      - rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
        change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
        destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    rewrite EA2.
    apply evt_done. deexists 3. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
  if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MMOK.

End RP_1.
