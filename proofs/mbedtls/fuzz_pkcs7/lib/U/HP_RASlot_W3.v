(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_enframe HP_RF_malloc_entry HP_RF_malloc_small HP_RF_ntf_A HP_RF_ntf_C HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B3.mw_ok"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.shiftl"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_W4.rt1_regs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W1.span_exit"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.span_loop"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mask_upto"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_active"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Unknown"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.g_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_group_active_idx"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L22069199602.9L45081068754.9L976659370.9  000001002009SSS2mq2WR". (* [comment removed for export] *)
#[using="hRP"] Lemma lw_slli52_srli58_sc mq : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "P,(0.O1.)(1.(2.&40.)(3.&40.(4.(5.&40.(3.&40.(6.(5.&40.(7.(3.&40.(8.O1.))))+34.)))+3:.))(3.&40.(9.O1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MWq. pose proof (meta_word_range _ MWq) as WR. dpose MWq as (LI & FB & SCR & ML).
  f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite swrap32_eq'.
  unfold meta_word.
  Z.div_mod_to_equations. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

(* [comment removed for export] *)
#[using="hRP mr MR MSL AV0"] Lemma ravz_pre_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pgw,(2.&40.)PF,(:.&5.(2.&40.))Pfc,(2.&20.)P,(1.$;.(5.&40.R3.)VG,)P,(<.$=.Vm,)(>.$=.Lms',$?.(1.$?.R1.(10.(11.Vsc0,R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R6.(12.=)R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R5.(3.&40.+40:00.)R4.(13.(2.&40.))Vm,(14.$=.)))(10.(11.Vsc0,R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R5.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R4.(3.&40.+409?4.)R3.(13.(2.&40.))Vm,(14.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros HG MI. unfold rt1_regs.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "00c0?L1297472924.88 L13957154548.93L16075584073.84L17147208227.93L20391242227.92L23834020845.91L25273856723.83L29087446882.85L29315121884.69L29317429958.77L30780937855.70L35497698861.84L35497698988.87L36105744810.76L36108089361.74L41416041421.80L42162764076.79L42165092875.82L42177831757.81L43217296612.70L44265534765.88L44744729046.77L45763346440.77L45763346440.78L45763430326.94L48432649896.93L49702840724.94L51907572202.92L53860174734.79L53862215849.80L56401721714.88L59308579543.14L59530220640.92L59531912551.93L59562705696.65L61765444619.84L61765822221.84L61977261507.88L63399210522.76L63399210522.77L63578588414.88L63582667343.88L63584909764.87L64266354221.93L64268764692.94L66151427842.18L68187596511.81L68191963033.82L8479065194.94 L9785857433.89 L9788380166.92 00000W01N01O02:02a03H03i03j04F04g05J05k06O07507[08<08b09H09n0:Q0;70;[0<L0==0=l0>c0?O0@90@]0AA0Ai0BC0Bg0CK0D=0E80Eh0FO0G00GQ0H;0Hg0Hh0IL0J40JQ0K70K]0LI0M40M_S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82K2S2st1g2gh1G2mr1f2ai3act4mask2sc4FR321y2w84Ypos2R32BR2K3FS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82K23SC7S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82BRS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82BRS2st1g2gh1G2mr1f2ai3act4mask1y2w8FS2st1g2gh1G2mr1f2ai3act4maskS2st1g2gh1G2mr1f2ai3act4mask1y2w8S2st1g2gh1G2mr1f2ai3act4mask2w83W8RS2st1g2gh1G2mr1f2ai3act4mask1y2w8S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w8S2st1g2gh1G2mr1f2ai3act4mask4FR322w81yS2st1g2gh1G2mr1f2ai3act4mask4FR322w81yS2st1g2gh1G2mr1f2ai3act4mask1y2w8S2st1g2gh1G2mr1f2ai3act4mask4FR321y2w8S2st1g2gh1G2mr1f2ai3act4mask4FR321y2w8S2st1g2gh1G2mr1f2ai3act4mask4FR321y2w8S2st1g2gh1G2mr1f2ai3act4mask2w83W8RS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w81HS2st1g2gh1G2mr1f2ai3act4mask2AI1y2w8S2st1g2gh1G2mr1f2ai3act4mask2AI2gw2HG1y2w83W8R2HBS2st1g2gh1G2mr1f2ai3act4mask2AI2gw2HG1y2w83W8R2HBS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82K23SC73LENS2st1g2gh1G2mr1f2ai3act4mask2sc4FR321y2w84Ypos2R32BR2K3S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w83SCR3LENS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82BR2K3S2st1g2gh1G2mr1f2ai3act4mask2AI1y2w8S2st1g2gh1G2mr1f2ai3act4mask2AI1y2w8S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w83SC7S2mr2sc3SCR1r2K21H1q2H02H1S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w8S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w8S3hRP2st1g2gh1G2mr1f2ai3act4mask3RCB2gw2HG4Gpos2GCS2st1g2gh1G2mr1f2ai3act4mask2AI4FR321y2w83W8R2R14Ypos2R22R3S2st1g2gh1G2mr1f2ai3act4mask2AI4FR321y2w83W8R2R1S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82K2S2st1g2gh1G2mr1f2ai3act4mask2w81yS2st1g2gh1G2mr1f2ai3act4mask1y2w8S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w83SCR1HS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w83SCR3SC7FS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w8S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w83LENS2st1g1G2r02G41q1r1H2H02q02H4S2st1g2gh1G2mr1f2ai3act4mask1y2w84YposS2st1g2gh1G2mr1f2ai3act4mask1y2w84YposS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w83SCR3LENS2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82K23SC7S2st1g2gh1G2mr1f2ai3act4mask2sc1y2w82K23SC7". (* [comment removed for export] *)
#[using="b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0"] Lemma ravz_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pgw,(2.&40.)PF,(:.&5.(2.&40.))Pfc,(2.&20.)P,(1.$;.(5.&40.R3.)VG,)P,(<.$=.Vm,)(>.$=.Lms',$?.(15.(2.&40.)La2',(2.&40.)(15.(2.&40.)La3',(2.&40.)(15.(2.&40.)La4',(2.&40.)(15.(2.&40.)La5',(2.&40.)(15.(2.&40.)La6',(2.&40.)(15.(2.&40.)La7',(2.&40.)(15.P,(2.&40.)(16.(2.&8.))Lm',P,(2.&40.)(16.(2.&8.))(17.(1.$?.R8.(10.(11.Vsc0,R26.R25.R24.R23.R22.R21.R20.R1?.R=.(12.(18.Vmask,))R7.R6.R5.R4.R3.R2.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R<.(3.&40.+40:78.)R;.(13.(2.&40.))R1.(14.$=.)))(17.(19.(1:.(1;.$;.$;.)(1<.$;.$;.VG,(1=.VG,+28.))(1:.(1;.$;.$;.)(1<.$;.$;.(1=.$1>.+370.)(1=.$1>.+390.))(1?.(1;.$;.$;.))))Vm,R1.)(17.(20.$=.Vm,R1.)(17.(<.$=.R1.)(21.VhRP,Vst5,R1.))))))))))))(10.(11.Vsc0,R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R5.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R4.(3.&40.+40:00.)R3.(13.(2.&40.))Vm,(14.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros HG MI. unfold rt1_regs.
  pose proof (munch_refl [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24). fold G in Gpos, GC, GI, G4, G24.
  pose proof (meta_word_range _ MW) as MWR.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
  { apply amo_aligned_intro; [rceilb; lia|]. rewrite HG. clear -G4. Z.div_mod_to_equations. lia. }
  clear G4 G24.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  (* [comment removed for export] *)
  step.
  destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8). unfold wa in RD8.
  pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
  step.
  (* [comment removed for export] *)
  step. step.
  assert (W8M : bv_unsigned w8 mod 32 = ai).
  { unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
  unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
  rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
  set (y := 2 ^ (ai + 1)).
  (* [comment removed for export] *)
  step. step. rewrite negw_word.
  (* [comment removed for export] *)
  pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
  step. rewrite sx32_wz_sxv by lia.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  (* [comment removed for export] *)
  clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  step. if_false.
  amo_step AMO.
  step. if_false.
  step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.
  (* [comment removed for export] *)
  step. rewrite addiw_m1_word.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  step.
  (* [comment removed for export] *)
  assert (AI31 : Z.land ai 31 = ai).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
  assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
  assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
  pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
  pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
  pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
  { rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
    eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tauto].
    unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
    rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
  clear MUa WMa.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.
  2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
      rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
  clear K1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HRW : ov_read_bytes rsegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
      by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read rsegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
  step. step. step.
  rewrite (lw_slli52_srli58_sc mr MW).
  dpose MW as (_ & _ & SCR & _). fold mr in SCR.
  set (sc := m_sizeclass mr) in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
  - (* [comment removed for export] *)
    assert (NR : (7 <=? sc) && (sc <? 39) = false).
    { destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
      apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
    apply evt_done. cbv beta. deexists 7. split; [rewrite <- ACT; reflexivity|].
    split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
  - (* [comment removed for export] *)
    assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear -K2 H SCR; Z.div_mod_to_equations; lia]).
    rewrite Z.mod_small in K2 by lia.
    assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    (* [comment removed for export] *)
    step.
    pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa (512968 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
    change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
    pose proof (BNC (sc - 7)) as BR.
    step. rewrite ?zxb_b8 by lia.
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      apply evt_done. cbv beta. deexists 7. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
    + (* [comment removed for export] *)
      step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
      dpose MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
      pose proof (u8arr_store_ok rsegs _ _ _ (sc - 7) (Z_to_bv 64 (512960 + (sc + -7) + 888)) X5
                    ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear X5 RDB.
      st1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
        pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold RCTX in MR5 end.
      rraw_store_finish0 (512968 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
      apply evt_done. cbv beta. deexists 7. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|].
      split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End AVZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L12947806344.46L17587606276.44L19495964943.46L19628692864.44L27991378352.44L29933087949.46L43973318371.45L43979528826.46L44220711856.44L44961050762.44L54865391209.46L55345573092.44L56233220482.46L59308518135.46L61455039654.46L61461278783.45L62117873896.44L64841880116.46L65106172084.44L66502672425.43L8392143385.43 00000@00V00f01<01G01O01_01o02E02[02`02k03>03P03S03V03c03k04604L04bS4size1F4span2SBS4size2SZ1F4span2S02SBS4size1F4span2GES4size2SZ1F4span2S02SBS1F1c2C02CBS1F1c2CBS4size1F4span2XRS4size1F4span2XRS4size2SZ1F4span2S02SBS4size2SZ1F4span2S02SBS1F1cS1F1c2C02CBS4size2SZ1F4span2S0S4size1F4span1K2LTS1FS1FS4size1F4spanS1F1c2C0S4size2SZ1FS4size2SZ1F4span2S02SBS4size2SZ1F4span2S02SB". (* [comment removed for export] *)
#[using="hRP SZ"] Lemma rspan_loop_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "PF,$22.Pc,$;.Pspan,$;.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PFr,(:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(16.(2.&8.))P,(23.=R1?.)P,(23.=R1?.)P,(24.(1=.R20.(25.Vsize,(1=.(26.R22.)+2.)))(27.+2.+1?.))P,(24.(1=.(1=.R22.+1.)(26.R23.))(27.+2.+1?.))P,(1.$28.(29.R24.R22.Vsize,)$2:.)P,(<.$=.R6.)(>.$=.Lms',$?.(15.(2.&40.)Lt0',(2.&40.)(15.(2.&40.)Lt1',(2.&40.)(15.(2.&40.)La6',(2.&40.)(1.$?.R4.(10.(2;.R27.R26.R25.R24.R3.R2.R22.R21.R20.R1?.R1>.R1=.R1<.(12.(2<.R2:.(1=.R29.+1.)R28.Vsize,))(12.Vsize,)R1.(3.&40.+1000.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(3.&40.+40>08.)R<.(13.(2.&40.))R;.(14.$=.))))))(10.(2;.R23.R22.R21.R20.(12.R24.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(12.R25.)(12.Vsize,)(12.(2=.(1=.R24.Vsize,)+1.))(3.&40.+1000.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(3.&40.+40=?4.)R8.(13.(2.&40.))R7.(14.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
  cbn [span_exit] in EX. cbn [span_loop].
  rewrite Nat2Z.inj_succ in SB, CB.
  pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.
  (* [comment removed for export] *)
  step. rewrite ?wz_unsigned by lia.
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
  rewrite (Z.lxor_comm (span + size - 1) span).
  (* [comment removed for export] *)
  step. if_cases K.
  - (* [comment removed for export] *)
    assert (LT : Z.lxor span (span + size - 1) < 4096).
    { unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
    replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
    replace (c + 2) with (c + 1 + 1) by lia.
    eapply (IH (c + 1) (span + size)); try assumption; try lia.
  - assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
    { intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
    replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. deexists 3. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SPANLOOP.
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L18422389228.9L2431248216.9 L29317573024.8L52483365436.9L63368325232.800000500;00<00A00BS1n1HS1n2HnSS1n1HS". (* [comment removed for export] *)
#[using="hRP"] Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
  Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof. rceilb.
  intros Hw Hv. apply Z.bits_inj'. intros n Hn.
  change 256 with (2^8). change 31 with (Z.ones 5).
  rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  replace 224 with (Z.shiftl 7 5) by reflexivity.
  destruct (Z.ltb_spec n 5).
  - rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
  - replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

(* [comment removed for export] *)
Ltac ract_prefix CH w8 :=
  rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
  step;
  let RD8 := fresh "RD8" in let L8 := fresh "L8" in
  destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
  let W8R := fresh "W8R" in
  pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
  step;
  let W8M := fresh "W8M" in
  assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
  step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
  step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
  step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L16077671799.63L23860999277.63L29315121884.59L30780937855.60L35495598355.63L43217296612.60L52689988.61   L54331152029.6100000100S00b01801J01`02602SFS2st1g2gh4mask1G3ai02w83W8R3MUR2LRS2st1g2gh1G3ai0S2st1g2gh1G3ai02w83W8RS2st1g2gh1G3ai02w8S2st1g2gh1G3ai02w83W8RS2st1g2gh1G3ai02w83MURS2st1g2gh4mask1G3ai05MASKR2w8". (* [comment removed for export] *)
#[using="hRP b mr MR MSL Hmem Hgh AI0 MASKR"] Lemma ract_skip_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PFr,(:.&5.(2.&40.))Pfc,(2.&20.)P,(2>.(1.$;.(2?.Vmask,(30.Vai0,))=))P,(<.$=.Vm,)(>.$=.Lms',$?.(15.(2.&40.)La1',(2.&40.)(15.(2.&40.)La2',(2.&40.)(15.(2.&40.)La3',(2.&40.)(15.(2.&40.)La4',(2.&40.)(1.$?.R5.(10.(11.Vsc,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(3.&40.VG,)R4.R3.R2.R1.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(3.&40.+409?4.)R8.(13.(2.&40.))Vm,(14.$=.)))))))(10.(11.Vsc,R1;.R1:.R19.R18.R17.R16.R15.R14.(3.&40.VG,)R13.R12.(12.(18.Vmask,))(3.&40.+2.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(3.&40.+409<<.)R3.(13.(2.&40.))Vm,(14.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros NZ MI. unfold rt1_regs.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  dpose (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
  step. if_cases K; zify_cond K.
  2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
      rewrite ?wz_unsigned in K by (apply sxv_range).
      first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
  apply evt_done. deexists 4. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L11803485471.73L13747413779.72L16077671799.72L18910182299.72L29315121884.69L29759295589.71L30780937855.70L43217296612.70L49702840724.73L52163693840.7300000I00c00d01B01Q01i02?02U03503US2st1g2gh2sc1G3ai02w83LENS3hRP1G3RCB4Gpos2GC2w83W8RFS3hRP2st3RCB2mn4Npos2NC2w83W8RS2st1g2gh1G3ai0S2st1g2gh2sc1G3ai02SC2w8S2st1g2gh1G3ai02w83W8RS2st1g2gh1G3ai02w83W8RS2st1g2gh2sc1G3ai02SC2w83W8R3LENS2st1g2gh2sc1G3ai02SC2w83W8R3LEN". (* [comment removed for export] *)
#[using="b MR MSL SC Hmem Hgh AI0"] Lemma ract_next_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PFr,(:.&5.(2.&40.))Pfc,(2.&20.)Pmn,$31.P,(1.$;.(2?.Vmask,(30.Vai0,))=)P,(1.$32.(33.Vmr,)(34.$31.R2.))P,(2>.(1.$31.R3.Vg,))P,(35.Vst,R4.)P,(<.$=.Vm,)(>.$=.Lms',$?.(15.(2.&40.)La1',(2.&40.)(15.(2.&40.)La2',(2.&40.)(15.(2.&40.)La3',(2.&40.)(15.(2.&40.)La4',(2.&40.)(15.P,(2.&40.)(16.(2.&8.))Lm',P,(2.&40.)(16.(2.&8.))(17.(1.$?.R6.(10.(11.Vsc,R25.R24.R23.R22.R21.R20.R1?.R1>.(3.&40.(36.Vst,R<.))R5.R4.R3.R2.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(3.&40.+409?4.)R=.(13.(2.&40.))R1.(14.$=.)))(17.(19.(1:.(1;.$;.$;.)(1<.$;.$;.(1=.(1=.$1>.+50.)(25.+8.Vsc,))(1=.(1=.(1=.$1>.+50.)(25.+8.Vsc,))+8.))(1?.(1;.$;.$;.)))Vm,R1.)(17.(20.$=.Vm,R1.)(17.(<.$=.R1.)(21.VhRP,(37.Vsc,(34.$31.R<.)Vst,)R1.))))))))))(10.(11.Vsc,R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(3.&40.VG,)R17.R16.(12.(18.Vmask,))(3.&40.+2.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R8.(3.&40.+409<<.)R7.(13.(2.&40.))Vm,(14.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until mn. intros ZR GN NEn MSn MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  dpose (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
  dpose (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN in CH. cbn [oconc] in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  dpose MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (512968 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (512968 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. deexists 5. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11805467289.66L12758671232.62L13423755692.62L18426631147.67L19246332541.68L22991479154.67L26793933996.63L35069597989.64L42744863137.64L49698585326.67L49705053714.66L51464776307.67L51464924291.62L5999227706.67 L6001281818.63 L7222886220.62 00000P00f01>01Y02802O02^03703R04804X05305K05f06<06KS2st1g1b2gh1G3ai04cnt22wv3nbv2HBS2st1g2gh1G3ai02wv3WVRS2st1g2gh1G3ai04cnt23C2RS2st1g2gh1G3ai04cnt22wv3nbvS2st1g2gh1G3ai04cnt22wv3nbv3NBRS2st1g2gh1G3ai04cnt22wvS2st1g2gh1G3ai0S2st1g2gh1G3ai02wv3WVR2L1S2st1g2gh1G3ai04cnt23C2R2L2S2st1g1b2gh1G3ai04cnt22wv3nbv2HB5Ha_stS2st1g1b2gh1G3ai04cnt22wv3nbv2HBS2st1g2gh1G3ai04cnt22wv3C2RS2st1g2gh1G3ai04cnt23C2RS2st1g2gh1G3ai04cnt22wv3WVRS2st1g2gh1G3ai02wv3WVRS2st1g2gh1G3ai0". (* [comment removed for export] *)
#[using="ai0 MR MSL Hgh AI0"] Lemma rspan_tail_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W3 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa3,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PFr,(:.&5.(2.&40.))Pfc,(2.&20.)Pcnt2,$;.Pwv,$;.P,(17.(23.+1.R2.)(23.R2.+20.))P,(17.(23.=R2.)(24.R2.+100.))P,Po,$;.P,(17.(23.=R1.)(24.R1.+9.))(15.$;.Lh,$;.(1.$38.(39.(3:.Vst,(3;.$3<.$;.Vb,))(1=.(3=.$3<.$;.Vb,)R3.))(3>.R1.)))P,(1.$32.(3?.Vgh,)(34.$31.Vg,))P,(1.$;.(40.Vmr,)=)P,(<.$=.Vm,)(>.$=.Lms',$?.(15.(2.&40.)La1',(2.&40.)(15.(2.&40.)La2',(2.&40.)(15.(2.&40.)La4',(2.&40.)(15.P,(2.&40.)(16.(2.&8.))Lm',P,(2.&40.)(16.(2.&8.))(17.(1.$?.R5.(10.(2;.R25.R24.R23.R22.R21.R20.R1?.(3.&40.Vsc,)R1>.(3.&40.VG,)R4.R3.R1=.R2.R1<.R1;.R1:.R19.R18.(3.&40.$41.)(3.&40.(1=.(1=.$1>.+50.)(25.+8.Vsc,)))(3.&40.$42.)(3.&40.(1=.$42.(25.+8.Vsc,)))R17.R16.R15.R14.R13.R12.R11.R10.)R?.(3.&40.+40:00.)R>.(13.(2.&40.))R1.(14.$=.)))(17.(19.(1:.(1;.$;.$;.)(1<.$;.$;.(36.Vst,Vb,)(1=.(36.Vst,Vb,)+9.))(1?.(1;.$;.$;.)))Vm,R1.)(17.(20.$=.Vm,R1.)(17.(<.$=.R1.)(21.VhRP,(43.Vb,(2=.R=.+1.)Vst,)R1.)))))))))(10.(2;.R20.R1?.R1>.R1=.R1<.R1;.R1:.(3.&40.Vsc,)R19.(3.&40.VG,)(3.&40.(36.Vst,Vb,))(3.&40.R7.)R18.(3.&40.R8.)R17.R16.R15.R14.R13.(3.&40.$41.)(3.&40.(1=.(1=.$1>.+50.)(25.+8.Vsc,)))(3.&40.$42.)(3.&40.(1=.$42.(25.+8.Vsc,)))R12.R11.R10.R?.R>.R=.R<.R;.)R:.(3.&40.+40>18.)R9.(13.(2.&40.))Vm,(14.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until wv. intros C2R WVR UNK GM AV0 MI.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  dpose (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  dpose MR as (_ & _ & _ & _ & GR & _). ddestruct (GR b gh Hgh) as (w8o & RWB & Hw8o). clear GR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl rsegs m) as WMb.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
  pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
  pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
  rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
  set (nbv := Z.lor _ _).
  (* [comment removed for export] *)
  step. rewrite (le1_mod nbv). mem_after_store.
  pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
  pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
  lazymatch goal with H : rw_cells rsegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
    [ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
    | ] end.
  { rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
  { lazymatch goal with H : rw_cells rsegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
  { rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }
  (* [comment removed for export] *)
  assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
  rmchunk MR2 MS2 CH.
  replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
  replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
  rewrite AV0 in CH.
  step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
  apply evt_done. deexists 4. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L10814688911.94L12187651427.89L13024519691.94L13747413779.79L14210379235.80L15527023617.89L16077671799.79L18216888022.89L19622189599.93L20318760449.89L2054185452.89 L28227313614.78L29315121884.76L29315560796.78L30780514786.78L30780937855.77L33617538779.70L33619727173.79L34699872640.79L35022200833.89L35639697341.89L36030225674.79L36030913969.92L38677700373.93L38919997489.89L39059932184.94L39239875037.92L40823361389.89L41354126673.89L42048713819.78L43217296612.77L47518959205.89L4832277617.89 L49502061597.89L51391009192.83L53178923665.89L55023333121.82L55307977729.80L55310024721.82L56368750025.78L57376891074.89L57380986544.89L58214683041.89L59291627427.93L61836119365.79L62339300063.93L65104380693.89L8754181500.94 00000L01G02@02\03Q04O04P04i05305X06506j07X08I09>0:30:e0;^0<S0=M0=j0>_0?<0?^0@C0@e0AK0Ad0BE0C60Ck0DM0Dj0E`0FQ0GO0HH0I=0J20Jg0KD0Kg0LI0M?0N80NU0O70OYS2st1g2gh1G2mr3ai03sc'2LI2w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span2w83W8R3SZB3CNB3SPB3EszS2st1g2gh1G2mr3ai03sc'3cnt4cnt12LI2w83W8R3W8M4Ecnt2CB1K1HS3hRP1G3RCB4Gpos2GC2w83W8R1KS2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt23SZR2w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span2w83W8R3SZB3CNB2PR3SPB3EszFS2st1g2gh1G2mr3ai03sc'2w8S2mr2LI2w8S2st1g2gh1G2mr3ai03sc'3cnt4size2w82PRS2st1g2gh1G2mr3ai03AI03sc'2w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt23MWR2w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt2S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w83W8RS2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w83W8RS2st1g2gh1G2mr3ai03SCR3sc'3cnt4size4span4cnt14cnt2S2st1g2gh1G2mr3ai03SCR3sc'3cnt4size4span4cnt14cnt22w83W8RS2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w83W5RS2st1g2gh1G2mr3ai03sc'3cnt4size2w83W8R3SZB3CNB2PR3Esz4EcntS2st1g2gh1G2mr3ai03sc'3SZR2w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt23MWR2w8S2st1g2gh1G2mr3ai03sc'3MWR2w8S2st1g2gh1G2mr3ai03sc'4cnt22w83C2RS2st1g2gh1G2mr3ai03sc'3cnt4size2w82PRS2st1g2gh1G2mr3ai03sc'4cnt12w81K1HS2st1g2gh1G2mr3ai03sc'3cnt2w83W8R4EcntS2st1g2gh1G2mr3ai03sc'2w8S2st1g2gh1G2mr3ai03sc'3cnt2w83CNBS2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w83W8RS2st1g2gh1G2mr3ai03sc'3cnt4size2w8S2st1g2gh1G2mr3ai03AI03sc'2w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span2w83W8R3SZB2PR3SPBS2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt22w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span2w83W8R3SZB3CNB2PR3SPB3EszS2st1g2gh1G2mr3ai03SCR3sc'3cnt4size4span4cnt14cnt22w83W8RS2st1g2gh1G2mr3ai03AI03sc'3cnt4size4span4cnt14cnt22w8S2st1g2gh1G2mr3ai03AI03sc'3cnt4size4span4cnt14cnt22w8S2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt23MWR2w8S2st1g2gh1G2mr3ai03AI03sc'2w8S2st1g2gh1G2mr3ai03sc'4size4span2w8S2st1g2gh1G2mr3ai03sc'4size2w83SZBS2st1g2gh1G2mr3ai03sc'3cnt4cnt12w83W8R3W8M3CNB4Ecnt2CBS2st1g2gh1G2mr3ai03sc'3cnt4size4span4cnt14cnt23SZR2w83W8RS2st1g2gh1G2mr3ai03sc'2w83W8RS2st1g2gh1G2mr3ai03sc'4size2w83SZBS2st1g2gh1G2mr3ai03sc'4cnt12w81K1H". (* [comment removed for export] *)
#[using="MR MSL Hmem Hgh AI0"] Lemma ract_span_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 ->
  mem_inv rsegs m ->
  let sc' := m_sizeclass mr in
  let cnt := ai0 + 2 in
  let size := size_class sc' * UNIT in
  let span := UNIT + size * cnt in
  let cnt1 := span_loop 300 cnt span size in
  let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
  evt rsegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
                   (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x40a00) fc None m' (seg_rom rsegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x409cc) fc None m (seg_rom rsegs)).
Proof. rceilb.
  intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  dpose (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  pose proof (meta_word_range _ MW) as MWR. dpose MW as (LI & FB & _ & ML).
  pose proof (size_class_range sc' ltac:(lia)) as SZR.
  unfold RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES in *.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.
  (* [comment removed for export] *)
  assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
  step.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ =>
    pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold RSIZE_CLASSES in SCRD end.
  step. rewrite zx16_wz by lia. clear SCRD.
  fold cnt.
  assert (SZB : 16 <= size <= 131056) by (unfold size, UNIT; lia).
  assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
  assert (PR : 0 <= cnt * size <= 33 * 131056) by nia.
  assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
  assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
  assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
  pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
  assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
  assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
  clearbody size cnt span cnt1 cnt2.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
  step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
  replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
  step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
  step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
  replace (span + size - 16 + 15) with (span + size - 1) by lia.
  step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
  step.
  (* [comment removed for export] *)
  eapply evt_cut.
  { change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
    eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
  (intros ms' dd_H; ddestruct dd_H as (t0' & t1' & a6' & ->)). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
  - replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. (intros ms2 dd_H; ddestruct dd_H as (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR')). deexists 10. split; [reflexivity|]. eauto.
  - (* [comment removed for export] *)
    step.
    replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. (intros ms2 dd_H; ddestruct dd_H as (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR')). deexists 10. split; [reflexivity|]. eauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ACT.

End RP_1.
