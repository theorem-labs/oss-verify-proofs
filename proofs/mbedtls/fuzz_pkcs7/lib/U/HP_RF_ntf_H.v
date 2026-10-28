(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F F_ntf_H MallocKit_A3 MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_free_A HP_RF_ntf_A HP_RF_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_ntf_H () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_H.ntf_cond"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.not"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RP_1.POST.RAT"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RP_1.rentry_cases"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_ntf_A.rntf_frame"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RP_1.ENTRY.rmid_ctx"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rentry_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.bit"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mask_upto"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.okay_to_free"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freeable"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs).

Definition rentry_cases (ms' : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "(0.(1.(2.$3.(4.Vst,Vg,Vi,)$5.)(1.(6.(2.$7.(8.(9.(:.Vst,Vg,))(;.(:.Vst,Vg,)))=))(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La0,(=.&40.)(<.(=.&40.)La2,(=.&40.)(<.(=.&40.)La3,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Ls2x,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(>.+40238.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R>.R=.R<.Vs0,(10.&40.$13.)R;.(14.(15.(16.+2.Vi,)))R:.R9.(10.&40.(11.(17.Vst,Vg,)+1<.))R8.R7.R6.R5.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))))))(0.(1.(2.$3.(4.Vst,Vg,Vi,)$5.)(1.(2.$7.(8.(9.(:.Vst,Vg,))(;.(:.Vst,Vg,)))=)(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La3,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Ls2x,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(>.+4001<.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R<.R;.R:.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))(14.(15.(16.+2.Vi,)))(10.&40.(18.(:.Vst,Vg,)))R9.(10.&40.(11.(17.Vst,Vg,)+1<.))R8.R7.R6.R5.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))))(0.(1.(2.$3.(4.Vst,Vg,Vi,)$19.)(1.(2.$1:.(1;.(:.Vst,Vg,))(1<.$1=.))(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La1,(=.&40.)(<.(=.&40.)La2,(=.&40.)(<.(=.&40.)La3,(=.&40.)(<.(=.&40.)La4,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(>.+400>0.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R>.R=.R<.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))R;.R:.R9.R8.R7.R6.R5.(10.&40.$1>.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))))))(0.(1.(2.$3.(4.Vst,Vg,Vi,)$19.)(1.(2.$1:.(1;.(:.Vst,Vg,))(1?.$1=.Vg,))(1.(20.(18.(:.Vst,Vg,))+30.)(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La3,(=.&40.)(<.(=.&40.)La4,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(>.+40074.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R<.R;.R:.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))(10.&40.(11.$1>.(21.(18.(:.Vst,Vg,))+8.)))(22.Vst,(23.Vst,(18.(:.Vst,Vg,))))R9.R8.R7.R6.R5.(10.&40.$1>.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.))))))))))))))))(1.(2.$3.(4.Vst,Vg,Vi,)$19.)(1.(20.(18.(:.Vst,Vg,))+30.)(<.$1=.Lnx,$1=.(1.(2.$1:.(1;.(:.Vst,Vg,))(1?.$1=.R1.))(1.(6.(2.$1=.R1.Vg,))(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La4,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(>.+3???0.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R;.R:.R9.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))(10.&40.(11.$1>.(21.(18.(:.Vst,Vg,))+8.)))(22.Vst,(23.Vst,(18.(:.Vst,Vg,))))(10.&40.(17.Vst,R<.))R8.R7.R6.R5.(10.&40.$1>.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))))))))))")
(* [comment removed for export] *).
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "Lms',$24.(<.P,(=.&40.)(25.(=.&8.))Lm1,P,(=.&40.)(25.(=.&8.))(<.(26.(=.&8.))Ljunk,(26.(=.&8.))(1.(27.O17.O16.O15.O14.O13.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.R2.R3.)(1.(28.(29.(2:.$7.$7.)(2;.$7.$7.(2<.(12.&40.O16.)+60.)(12.&40.O16.))(2=.(2:.$7.$7.)))O1.R2.)(1.(2>.$2?.O1.R2.)(1.(30.$2?.R2.)(1.(31.$2?.R2.O2.(11.(12.&40.O16.)-60.))(1.(32.$2?.R2.(11.(12.&40.O16.)-60.)(33.VhRP,R1.O10.O11.O12.O13.O17.))(34.VhRP,O5.R2.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L11427672333.9L11601703795.9L22069199602.9L33381437612.9L45081068754.9L56862877715.9L63348610430.9L8929260062.9 00000400500600:00;00<00F00TS2mrSSS2mrSSS2mr2LI2FBS2mr2LI2FB3SCR". (* [comment removed for export] *)
#[using="hRP"] Lemma meta_word_sc52 mr : mw_ok mr ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof. rceilb.
  intros MW. pose proof (meta_word_range mr MW) as MWR. dpose MW as (LI & FB & SCR & ML).
  rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L22703930437.8L46609756872.8L68569543065.800000400500<S2mrSS2mr2LI". (* [comment removed for export] *)
#[using="hRP"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. rceilb.
  intros MW. dpose MW as (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis LO : rceil <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

(* [comment removed for export] *)
Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "(1.(28.(29.(2:.$7.$7.)(2;.$7.$7.(2<.(12.&40.Vsp,)+60.)(12.&40.Vsp,))(2=.(2:.$7.$7.)))Vm,O2.)(1.(2>.$2?.Vm,O2.)(1.(30.$2?.O2.)(1.(31.$2?.O2.Vlo,(11.(12.&40.Vsp,)-60.))(1.(32.$2?.O2.(11.(12.&40.Vsp,)-60.)(33.VhRP,O1.Vs3,Vs2,Vs1,Vs0,Vra,))(34.VhRP,Vst,O2.))))))")
(* [comment removed for export] *).

#[using="hRP i EH"] Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. rceilb. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="hRP"] Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. rceilb. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L16077671799.56L35495598355.56L67019247552.56L8931259039.56 00000100200?00JFSS2st1g4MWR'1KS2st1g4MWR'". (* [comment removed for export] *)
#[using="EH"] Lemma rntf_notall : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2x,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Pm1,P,(=.&40.)(25.(=.&8.))Pjunk,(26.(=.&8.))P,(35.R2.R1.)P,(2.$3.(4.Vst,Vg,Vi,)$5.)(36.$2?.(37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vst,Vg,Vi,Vlo,Vm,)(38.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R10.R?.R>.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))(14.(15.(16.+2.Vi,)))(10.&40.(18.(:.Vst,Vg,)))(10.&40.(8.(15.(9.(:.Vst,Vg,)))(15.(;.(:.Vst,Vg,)))))R=.R<.R;.R:.R9.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(10.&40.+40014.)Vfc,(1<.(=.&40.))R4.(39.$2?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. (intros dd_H; ddestruct dd_H as (MU & WM & MI & ST & FR & MR); intros HC).
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). rceilb.
  st1. rewrite ?(unsigned_lit (conc st g)) by lia.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
  - (* [comment removed for export] *)
    rpost_common MU WM MI ST FR MR m1 junk.
    left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
    deexists 14. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  - (* [comment removed for export] *)
    assert (M0 : mask = 0) by (apply MZ; lia).
    rpost_common MU WM MI ST FR MR m1 junk.
    right; left. split; [exact HC|]. split; [exact M0|].
    deexists 12. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L14728680200.81L16075583950.80L20897545591.77L29784416474.80L34217400197.81L44434640635.79L44434640889.81L48095868254.77L49130514066.81L52033399223.80L52033474951.82L59308628566.75L59308628566.79L59308628695.80L59976465927.8000000600D00V00W00m01:01G01Q01]01g02102502B02O02]S2st1gS2st1g3G503SCRS3hRP2st3RCB2nx2B1SS3hRP2st1g3RCB3GB03GB1S2st2nx2N02N1S2st2nx2N02N1S2st2nx2B0S2st1g2nx2K5S2st1g3G50S2st1g3G50S2K3S2st2nx2N02K3S2st1g3G502K4S2st1g3G503SCR". (* [comment removed for export] *)
#[using="EH"] Lemma rntf_fge : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Pm1,P,(=.&40.)(25.(=.&8.))Pjunk,(26.(=.&8.))P,(35.R2.R1.)P,(2.$7.(11.(8.(9.(:.Vst,Vg,))(;.(:.Vst,Vg,)))(3:.Vi,))(3;.(3<.(:.Vst,Vg,))))P,(2.$3.(3=.Vst,Vg,)$19.)(36.$2?.(37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vst,Vg,Vi,Vlo,Vm,)(38.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R10.R?.R>.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))(14.(15.(16.+2.Vi,)))(10.&40.(18.(:.Vst,Vg,)))(10.&40.(8.(15.(9.(:.Vst,Vg,)))(15.(;.(:.Vst,Vg,)))))R=.R<.R;.R:.(10.&40.$1>.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(10.&40.+3??<<.)Vfc,(1<.(=.&40.))R5.(39.$2?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. (intros dd_H; ddestruct dd_H as (MU & WM & MI & ST & FR & MR); intros HALL OKT).
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  dpose MW as (LI & FB & SCR & ML).
  dpose (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
  rceilb; unfold RCTX in *.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
  assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
  { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. dpose (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
    split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
  rmeta_chunk MR MSL CH.
  (* [comment removed for export] *)
  st1. clear CH.
  destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
  - ddestruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
    specialize (G50 HC ltac:(congruence)).
    (* [comment removed for export] *)
    st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }
    (* [comment removed for export] *)
    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
    replace (wa (512968 + 80 + 8 * sc)) with (Z_to_bv 64 (512968 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    (* [comment removed for export] *)
    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    + pose proof (NINJ ltac:(lia)) as ->.
      rpost_common MU WM MI ST FR MR m1 junk.
      do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
      deexists 12. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
    + assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
      rpost_common MU WM MI ST FR MR m1 junk.
      do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
      deexists 11. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  - st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
    rpost_common MU WM MI ST FR MR m1 junk.
    do 2 right; left. split; [exact HC|]. split; [exact NX|].
    deexists 14. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0140@L1021090280.86  L11264020429.101L11899380396.99 L15524707589.86 L15526887604.84 L16073326931.81 L16073481288.86 L16073486922.101L16073539944.85 L16075578389.84 L16075578389.86 L16075578774.85 L16075583565.86 L16075584200.78 L16075585474.99 L16088068200.85 L20391243517.100L20391243646.99 L20897545591.93 L23834020845.99 L24624355554.97 L26912248502.86 L29315069148.84 L29709730541.97 L29713640445.86 L29784418006.99 L30386944003.101L32665339679.95 L32813721440.86 L34217400068.91 L34217400068.95 L34595564048.100L34705803648.85 L36424092992.76 L36436663440.86 L36438760653.86 L36438760782.85 L37657799404.78 L39918411166.100L40823396172.85 L40829527628.85 L42048681435.84 L44434640760.95 L48095868254.93 L49130513939.95 L49771033641.100L51962820296.84 L52033399602.78 L52037199928.78 L55860257713.84 L55860257713.86 L57685087760.84 L59308628949.91 L59310733137.86 L59314955108.96 L59602690054.85 L59963964939.79 L59976464395.99 L59976845609.80 L60457093243.99 L63944815795.84 L67098893166.99 L67497085089.85 L67507419553.85 L6753670684.85  L67788976708.96 L67795291514.95 L8495997724.100 00000600N00e01<01f02002902B02V02_02h03503M03W03d04804B04Y05;05R05j06A06B06\06b06c07;07<07S08708[09209D09]0:B0:h0;S0;c0<:0<;0<<0<=0<Z0=40=N0=e0>90>I0>[0>n0?A0?K0?f0@O0@h0@n0AD0AZ0B00B60B@0BW0Bg0C70C80CB0CL0CRS2st1gS2st1g2FB2ML3FRZ3MLF3K10S2st1g2FB2ML3FRZ3MLF2K8S2st1g2FB2ML3FRZ2SZ3MLFS2st1g4FRNZ4MWR'2MZ2FB2ML2M43FRZ4NB484MLNZS2st1g3MWRS2st1g2MLS2st1g2LIS2st1g3SCR2FB3FRZ2SZS2st1g2MLS2st1g2MLS2st1g2LI3MWRS2st1g2FB2ML3FRZ3MLF3GSRS2st1g3SCRS2st1g3SCR2LIS2st1g3MWR2FB3FRZ2SZS2st1g3USGS2st1g2FB2ML3FRZ3MLF2BRS3hRP2st1g3RCB2FB2ML3FRZ3MLF2nx2B1S2st1g2FB2ML3FRZ3MLF2BRS2st1g2FB2ML3FRZ3MLF3SR'S2st1g2FB2ML3FRZ3MLF2K5SS2st1g2FB2ML3FRZ3MLF2Sa2SbS2st1gSS2st1g2FB2ML3FRZ3MLF3K10FS2st1g2FB2ML3FRZ3MLF2K5S3hRP2st1g3RCB2FB2ML3GB03GB13FRZ3MLFS3hRP2st1g3RCB2FB2ML3GB03GB13FRZ3MLFS2st1g2FB2ML3FRZ3MLF2K9S2st1g2FB3FRZ4MW5RS2st1g4FRNZ4MWR'2MZ2FB2M4S2st1g1i4FRNZ4MWR'2MZ2FB2ML2M43FRZ2KmS2st1g4FRNZ4MWR'2MZ2LI2FB2ML2M43FRZ2KmS2st1g1i4FRNZ4MWR'2MZ2LI2FB2ML2M43FRZ2Km2KlS2st1g2FB3FRZ2K2S2st1g2FB2ML3FRZ3MLF2K9SSSS2st1g2nx2FB2ML3FRZ3MLF2N02N1S2st1g2FB2ML3FRZ3MLF2nx2B0S2st1g2nx2FB2ML3FRZ3MLF2K6S2st1g2LI2FB2ML3FRZ3MLFS2st1g3MLF2FB3FRZ2SZS2st1g2FB3FRZ2K2S2st1g2FB3FRZ4SC48S2st1g2FB2ML3FRZ2KmS2st1g2FB2ML3FRZ2KmS2st1g3MWRS2st1g2FB2ML3GB03FRZ3MLF2K6S2st1g1i4FRNZ4MWR'2MZ2FB2ML2M43FRZ2Km3Km2S2st1g2FB2ML3FRZ3MLF2K71ES2st1gS2st1g2FB3SCR3FRZ4SC48S2st1g2FB3SCR3FRZ4SC48S2st1g2FB3SCR3FRZ4SC48S2st1gS2st1g3MWRS2st1g2FB2ML3FRZ3MLF2K8S2st1g2FB3FRZ2SZS2st1g2FB3FRZ2SZSS2st1g3SCRS2st1g3SCRS2st1g". (* [comment removed for export] *)
#[using="EH"] Lemma rntf_okchk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa4,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Pm1,P,(=.&40.)(25.(=.&8.))Pjunk,(26.(=.&8.))P,(35.R2.R1.)P,(2.$7.(11.(8.(9.(:.Vst,Vg,))(;.(:.Vst,Vg,)))(3:.Vi,))(3;.(3<.(:.Vst,Vg,))))P,(6.(2.$7.(3>.(:.Vst,Vg,))=))(36.$2?.(37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vst,Vg,Vi,Vlo,Vm,)(38.(?.Vra,(10.&40.(11.(12.&40.Vsp,)-60.))Vgp,Vtp,R?.R>.R=.Vs0,(10.&40.$13.)(10.&40.(17.Vst,Vg,))(14.(15.(16.+2.Vi,)))(10.&40.(18.(:.Vst,Vg,)))(10.&40.(8.(15.(9.(:.Vst,Vg,)))(15.(;.(:.Vst,Vg,)))))R<.(10.&40.(3?.(:.Vst,Vg,)))R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(10.&40.+3??1<.)Vfc,(1<.(=.&40.))R5.(39.$2?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros MC HALL FRNZ. dpose MC as (MU & WM & MI & ST & FR & MR).
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  dpose MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
  dpose (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rceilb.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).
  (* [comment removed for export] *)
  st1. st1. st1.
  st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { (* [comment removed for export] *)
    eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
    rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  assert (SC48 : sc < 48) by lia. clear K2.
  assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
  specialize (USG SC48).
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  assert (RS' : ov_read_bytes rsegs m1 (Z_to_bv 64 (94460 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (94460 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
    apply rsize_classes_read; [assumption| lia]. }
  (* [comment removed for export] *)
  st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.
  (* [comment removed for export] *)
  assert (K690 : forall (t0' : word),
    m_maplen mr <> 0 ->
    evt rsegs POST
      (MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 94460) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 512968) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3ff70) fc None m1 (seg_rom rsegs))).
  { intros t0' MLNZ.
    assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
    assert (GSR : 0 < get_stride mr < 2^64).
    { unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }
    (* [comment removed for export] *)
    st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
    replace (94460 + sc * 2) with (94460 + 2 * sc) by lia.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    (* [comment removed for export] *)
    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    { eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
    assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
    assert (OKF : okay_to_free st g =
              if negb (optr_eqb (m_next mr) (Some g)) then true
              else if negb (is_bouncing sc st) then true
              else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
    { rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }
    (* [comment removed for export] *)
    rmeta_chunk MR MSL CH.
    st1. clear CH.
    assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
    { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. dpose (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
      split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
    destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
    2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
        eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
    ddestruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
    { assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
      cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
    pose proof (NINJ ltac:(lia)) as Enx. subst nx.
    rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.
    (* [comment removed for export] *)
    st1. rewrite ?(unsigned_lit sc) by lia. st1.
    st1. if_cases K7; zify_cond K7.
    { assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
      unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.
    (* [comment removed for export] *)
    st1.
    pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
    pose proof (BND (sc - 7)) as BR.
    replace (Z_to_bv 64 (512968 + 880 + (sc - 7))) with (Z_to_bv 64 (512968 + (sc + -7) + 880)) in RDB by (f_equal; lia).
    st1. clear RDB. st1.
    st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
    { replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.
    (* [comment removed for export] *)
    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    replace (wa (512968 + 464 + 8 * sc)) with (Z_to_bv 64 (512968 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.
    (* [comment removed for export] *)
    st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
    { replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
    replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.
    (* [comment removed for export] *)
    st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
    - replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
    - replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
  (* [comment removed for export] *)
  assert (K678 :
    (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt rsegs POST
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 94460) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 512968) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3ff58) fc None m1 (seg_rom rsegs))).
  { intros COND.
    assert (STR : get_stride mr = 16 * size_class sc).
    { unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    (* [comment removed for export] *)
    st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    (* [comment removed for export] *)
    st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
    - eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
    - replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
      apply K690. lia. }
  (* [comment removed for export] *)
  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  { apply K678. left. lia. }
  (* [comment removed for export] *)
  st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
  { apply K678. right. lia. }
  (* [comment removed for export] *)
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
  st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
  replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
  2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
  apply K690. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L12937216788.76L12937216788.77L16075706354.74L16077671799.75L30546037383.79L30547914802.78L34806984771.75L36180999398.73L36438766096.78L36511751956.76L36511751956.77L37678271015.75L43059266230.71L47696143756.75L50827569594.74L55866553043.75L57680763535.75L63045761903.74L66253577094.74L8931259039.75 00000Y01K01\01f02102<02E02I02Y03B04404<04H04[04\04g05105?05M05XS3hRP2ra2sp2lo2LO4LOLE3RCB2HB5Ha_st5Hl_stS3hRP2sp2s02lo2LO4LOLE3RCB2HB5Ha_st5Hl_st2s12s22s3S2st1g2AV3FRD3MWRS2st1g3MWRS2st1g1i2LIS2st1g1i2LIS2st1g2FBS2spS2st1g1i2HI2LI1KS3hRP2ra2sp2lo2LO4LOLE3RCB2HB5Ha_st5Hl_stS3hRP2sp2s02lo2LO4LOLE3RCB2HB5Ha_st5Hl_st2s12s22s3S2st1g1iS2sp2lo4LOLES3hRP2sp2lo2LO4LOLEFS2st1g2FB1KS2st1g3MWRS2st1g1i2HI2LIS2st1g1i2HI2LIS2st1g4MWR'". (* [comment removed for export] *)
#[using="EH MI0 LO LOLE"] Lemma rntf_entry : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_H ()) "Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(34.VhRP,Vst,Vm,)P,(31.$2?.Vm,Vlo,(12.&40.Vsp,))(36.$2?.(37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vst,Vg,Vi,Vlo,Vm,)(38.(?.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(10.&40.(17.Vst,Vg,))(10.&40.Vi,)R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(10.&40.+3?>;8.)Vfc,(1<.(=.&40.))Vm,(39.$2?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until t6. intros MR ST.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  dpose MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR.
  dpose (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof rmaskw_range as MWR'.
  dpose MR as (_ & _ & (_ & _ & _ & G4 & G5) & _).
  rceilb; unfold RGOT_SSP, RSSP_GUARD in *. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  clear MR G4 G5.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  rmeta_chunk MR1 MSL CH.
  (* [comment removed for export] *)
  st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
  st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
  st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  st1. rewrite (meta_word_freeable _ MW).
  st1. rewrite (meta_word_sc52 _ MW).
  clear CH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }
  (* [comment removed for export] *)
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
  rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
  st1. rewrite addiw_m1_word.
  (* [comment removed for export] *)
  pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
  st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
  - assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
      apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
  - (* [comment removed for export] *)
    apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
    eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ENTRY.

End RP_1.
