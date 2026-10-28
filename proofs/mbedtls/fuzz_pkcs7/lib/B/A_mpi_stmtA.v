(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_alloc_lib A_mpi_read_binary_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Export A_alloc_lib A_mpi_read_binary_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_mpi_stmtA () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.mpd_writable"; "mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "mpi_binop_postA"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.cshd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"].


(* [comment removed for export] *)
Definition mpd_writableA (R : art_layout) (LB LF : list blk) (SP top : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "(0.(1.(2.O6.)(3.$4.O5.(5.O4.))O3.O2.(6.O1.)+10.)P,(7.$8.(9.O1.)$:.)(;.(<.(=.(6.O1.)+10.)(>.O1.))(<.(=.(>.O1.)(?.+4.(10.O1.)))(6.O1.))))")
(* [comment removed for export] *).

Lemma mpd_writableA_of_P : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PR,$11.PLB,(12.$4.)PLF,(12.$4.)PSP,$13.Ptop,$13.Pd,$14.P,(15.(2.R6.)(3.$4.R5.(5.R4.))R3.R2.R1.)(16.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. (intros R LB LF SP top d dd_H; ddestruct dd_H as (A & _ & C)). split; assumption. Qed.

Lemma mpd_writableA_sp_mono : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PR,$11.PLB,(12.$4.)PLF,(12.$4.)PSP,$13.PSP',$13.Ptop,$13.Pd,$14.P,(16.R7.R6.R5.R4.R2.R1.)P,(<.R4.R5.)(16.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros R LB LF SP SP' top d [A C] HS. split; [| exact C]. eapply client_wrange_sp_mono; [exact HS| exact A].
Qed.

(* [comment removed for export] *)
Definition mpd_aobjA (segs : list Segment) (AL : asan_layout) (CS : Z -> Prop) (m : mem) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "(0.(17.O5.O4.O3.O2.(6.O1.)+10.)P,(7.$8.(9.O1.)$18.)(17.O5.O4.O3.O2.(>.O1.)(?.+4.(10.O1.))))")
(* [comment removed for export] *).

Lemma mpd_aobjA_limbs : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)PR,$11.PHIA,(1:.R2.R1.)Ph,(1;.R3.R2.R1.)PLB,(12.$4.)PLF,(12.$4.)Pm,P,(1<.&40.)(1=.(1<.&8.))Pd,$14.P,(1>.R8.R7.R6.R5.R4.R3.R2.)P,(1?.R9.R3.R5.R2.)P,(20.R:.(21.R9.)(22.R:.R9.R8.R7.)R4.R3.)P,(23.(7.$8.(9.R4.)$24.))(17.R<.(21.R;.)(22.R<.R;.R:.R9.)R6.(>.R5.)(?.+4.(10.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m d HH [HX _] [_ HS] HN.
  ddestruct HX as (_ & _ & _ & _ & _ & HOWN). destruct (md_own d) eqn:EO; [congruence| | apply HS; reflexivity].
  ddestruct HOWN as (_ & HIN & _). eapply hm_aobj_block; eauto.
Qed.

(* [comment removed for export] *)
Definition mpi_binop_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (dX : mpd) (Rr : Z -> mpd -> Prop) (PHI FR : Z) (lo : Z) (m : mem) (mo : Model)
    : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Lc,$25.(26.(1<.&40.)Lt0,(1<.&40.)(26.(1<.&40.)Lt1,(1<.&40.)(26.(1<.&40.)Lt2,(1<.&40.)(26.(1<.&40.)La1,(1<.&40.)(26.(1<.&40.)La2,(1<.&40.)(26.(1<.&40.)La3,(1<.&40.)(26.(1<.&40.)La4,(1<.&40.)(26.(1<.&40.)La5,(1<.&40.)(26.(1<.&40.)La6,(1<.&40.)(26.(1<.&40.)La7,(1<.&40.)(26.(1<.&40.)Lt3,(1<.&40.)(26.(1<.&40.)Lt4,(1<.&40.)(26.(1<.&40.)Lt5,(1<.&40.)(26.(1<.&40.)Lt6,(1<.&40.)(26.P,(1<.&40.)(1=.(1<.&8.))Lm',P,(1<.&40.)(1=.(1<.&8.))(26.$27.Lmo',$27.(26.(1;.O1?.O1>.O1=.)Lh',(1;.O1?.O1>.O1=.)(26.(12.$4.)LLB',(12.$4.)(26.$14.LdX',$14.(26.$13.Lr,$13.(0.(7.$25.R15.(28.(29.(2:.O1<.O1;.O1:.O19.R14.R13.R12.O18.O17.(2;.&40.R1.)R11.R10.R?.R>.R=.R<.R;.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R:.R9.R8.R7.)O<.(2<.O1<.)O;.(2=.(1<.&40.))R6.(2>.O1?.))R5.))(0.(2?.O1?.R6.)(0.(30.O1?.R6.O3.(31.&40.O1;.))(0.(32.O1.R5.)(0.(33.O1?.O1>.(34.O9.O7.)O8.(31.&40.O1;.)(35.O1>.)(36.O1?.O1>.O1=.O:.)(37.(38.$13.$13.)(39.$13.$13.(6.O7.)(=.(6.O7.)+10.))(3:.(38.$13.$13.)))O2.R6.)(0.(7.$13.(3;.O1?.O1>.O1=.R4.)(3;.O1?.O1>.O1=.O:.))(0.(7.$13.(36.O1?.O1>.O1=.R4.)(36.O1?.O1>.O1=.O:.))(0.(7.$13.(3<.O1?.O1>.O1=.R4.)(3<.O1?.O1>.O1=.O:.))(0.(3=.O1?.O1>.O1=.R4.R5.)(0.Px,$13.P,(22.O1?.O1>.O1=.O:.R1.)(22.O1?.O1>.O1=.R6.R2.)(0.(<.(3>.O1?.O1>.O1=.R4.)(=.(3>.O1?.O1>.O1=.O:.)O5.))(0.(<.(3?.O1?.O1>.O1=.R4.)(=.(3?.O1?.O1>.O1=.O:.)O4.))(0.(1>.O1?.O1>.O1=.R4.R3.O8.R6.)(0.(1?.O1?.R6.R3.R2.)(0.(40.O9.O7.R3.R2.)(0.Pb,$4.P,(41.$4.R1.(42.R3.))(;.(41.$4.R2.(42.O7.))(43.O1>.(34.O9.O7.)O8.(44.$13.$13.R2.)(45.$13.$13.R2.)))A2.O6.R1.R2.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_binop_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z)
    (PHI : mpd -> mpd -> mpd -> Z) (FRC : Z -> Z)
    (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Ph,(1;.O8.O7.O6.)PLB,(12.$4.)PLF,(12.$4.)Pra,(1<.&40.)Psp,(1<.&40.)Pgp,(1<.&40.)Ptp,(1<.&40.)Pt0,(1<.&40.)Pt1,(1<.&40.)Pt2,(1<.&40.)Ps0,(1<.&40.)Ps1,(1<.&40.)Pa0,(1<.&40.)Pa1,(1<.&40.)Pa2,(1<.&40.)Pa3,(1<.&40.)Pa4,(1<.&40.)Pa5,(1<.&40.)Pa6,(1<.&40.)Pa7,(1<.&40.)Ps2,(1<.&40.)Ps3,(1<.&40.)Ps4,(1<.&40.)Ps5,(1<.&40.)Ps6,(1<.&40.)Ps7,(1<.&40.)Ps8,(1<.&40.)Ps9,(1<.&40.)Ps10,(1<.&40.)Ps11,(1<.&40.)Pt3,(1<.&40.)Pt4,(1<.&40.)Pt5,(1<.&40.)Pt6,(1<.&40.)PF,(46.&5.(1<.&40.))Pfc,(1<.&20.)Pm,P,(1<.&40.)(1=.(1<.&8.))Pmo,$27.PdX,$14.PdA,$14.PdB,$14.Plo,$13.Pd,$13.P,(1>.O8.O7.O6.R2;.R2:.R29.R7.)P,(3=.O8.O7.O6.R2<.R7.)P,(1?.O8.R9.R2<.R7.)P,(1?.O8.R:.R2=.R7.)P,(1?.O8.R;.R2>.R7.)P,(47.R:.R9.)P,(47.R;.R9.)P,(47.R;.R:.)P,(23.(7.$8.(9.R=.)$18.))P,(48.R>.R=.R;.(31.&40.R30.))P,(48.R?.R=.R<.(31.&40.R31.))P,(49.(2.O7.)(3.$4.R35.(5.R34.))R=.(6.R?.)+10.)P,P,(7.$8.(9.R10.)$:.)(49.(2.O7.)(3.$4.R37.(5.R36.))R?.(>.R11.)(?.+4.(10.R11.)))P,(49.(2.O7.)(3.$4.R37.(5.R36.))R?.(6.R10.)+10.)P,P,(7.$8.(9.R11.)$:.)(49.(2.O7.)(3.$4.R39.(5.R38.))R11.(>.R12.)(?.+4.(10.R12.)))P,(16.O7.R39.R38.(31.&40.R36.)(3;.O8.O7.O6.R3:.)R14.)P,P,(23.(7.$8.(9.R15.)$24.))(;.(<.(=.(>.R16.)(?.+4.(10.R16.)))R13.)(<.(31.&40.R38.)(>.R16.)))P,(30.O8.R18.R13.(31.&40.R38.))P,(<.(35.O7.)R14.)P,(<.R15.(4:.(4:.(31.&40.R3:.)O4.)(4;.O7.)))P,(<.(31.&40.R3;.)(3;.O8.O7.O6.R3?.))P,(7.$13.(4<.(31.&40.R3<.)+10.)=)P,(7.(1<.&40.)R3;.(2;.&40.(4=.O7.)))P,(2?.O8.R1>.)P,(7.$13.(4<.(31.&40.R40.)+2.)=)P,(20.O8.(21.O7.)(22.O8.O7.O6.R44.)R20.R1>.)P,(20.O8.(21.O7.)(22.O8.O7.O6.R45.)R21.R1>.)P,(20.O8.(21.O7.)(22.O8.O7.O6.R46.)R22.R1>.)P,(<.(=.(3>.O8.O7.O6.R47.)A3.O3.R21.R20.R1?.)$4>.)P,(4?.O8.R24.(35.O7.)(36.O8.O7.O6.R48.)(31.&40.R3>.)(31.&40.R44.)R1>.)P,(50.O7.(6.R23.)+10.R1?.)P,(50.O7.(6.R23.)+10.R20.)P,(50.O7.(6.R23.)+10.R21.)P,(<.(=.(3?.O8.O7.O6.R4<.)A1.O2.R22.)$51.)P,(7.(1<.&40.)R41.(2;.&40.(6.R27.)))P,(7.(1<.&40.)R41.(2;.&40.(6.R27.)))P,(7.(1<.&40.)R41.(2;.&40.(6.R27.)))(52.O8.(53.O8.O7.O6.R4=.R4<.R4;.R4:.R46.R45.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R2>.R2=.R50.R4?.R4>.R2:.A4.O1.R4?.R2:.R29.R28.A3.O3.R2:.R29.R28.A1.O2.R26.R27.R2<.R2;.)(28.(29.(2:.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.)R2>.(2;.&40.O5.)R2=.(2=.(1<.&40.))R2<.(2>.O8.))R2;.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_intop_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z)
    (PHI : mpd -> mpd -> Z) (FRC : Z -> Z)
    (Rr : list blk -> mpd -> mpd -> Z -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Ph,(1;.O8.O7.O6.)PLB,(12.$4.)PLF,(12.$4.)Pra,(1<.&40.)Psp,(1<.&40.)Pgp,(1<.&40.)Ptp,(1<.&40.)Pt0,(1<.&40.)Pt1,(1<.&40.)Pt2,(1<.&40.)Ps0,(1<.&40.)Ps1,(1<.&40.)Pa0,(1<.&40.)Pa1,(1<.&40.)Pa2,(1<.&40.)Pa3,(1<.&40.)Pa4,(1<.&40.)Pa5,(1<.&40.)Pa6,(1<.&40.)Pa7,(1<.&40.)Ps2,(1<.&40.)Ps3,(1<.&40.)Ps4,(1<.&40.)Ps5,(1<.&40.)Ps6,(1<.&40.)Ps7,(1<.&40.)Ps8,(1<.&40.)Ps9,(1<.&40.)Ps10,(1<.&40.)Ps11,(1<.&40.)Pt3,(1<.&40.)Pt4,(1<.&40.)Pt5,(1<.&40.)Pt6,(1<.&40.)PF,(46.&5.(1<.&40.))Pfc,(1<.&20.)Pm,P,(1<.&40.)(1=.(1<.&8.))Pmo,$27.PdX,$14.PdA,$14.Pb,$13.Plo,$13.Pd,$13.P,(1>.O8.O7.O6.R2;.R2:.R29.R7.)P,(3=.O8.O7.O6.R2<.R7.)P,(1?.O8.R9.R2<.R7.)P,(1?.O8.R:.R2=.R7.)P,(47.R9.R8.)P,(23.(7.$8.(9.R:.)$18.))P,(48.R;.R:.R8.(31.&40.R2=.))P,(49.(2.O7.)(3.$4.R31.(5.R30.))R9.(6.R;.)+10.)P,P,(7.$8.(9.R<.)$:.)(49.(2.O7.)(3.$4.R33.(5.R32.))R;.(>.R=.)(?.+4.(10.R=.)))P,(16.O7.R33.R32.(31.&40.R30.)(3;.O8.O7.O6.R34.)R>.)P,(0.(<.(54.(55.+2.+1?.))R=.)(56.R=.(55.+2.+1?.)))P,P,(23.(7.$8.(9.R10.)$24.))(;.(<.(=.(>.R11.)(?.+4.(10.R11.)))R>.)(<.(31.&40.R33.)(>.R11.)))P,(30.O8.R13.R>.(31.&40.R33.))P,(<.(35.O7.)R?.)P,(<.R10.(4:.(4:.(31.&40.R35.)O4.)(4;.O7.)))P,(<.(31.&40.R36.)(3;.O8.O7.O6.R3:.))P,(7.$13.(4<.(31.&40.R37.)+10.)=)P,(7.(1<.&40.)R36.(2;.&40.(4=.O7.)))P,(2?.O8.R19.)P,(7.$13.(4<.(31.&40.R3;.)+2.)=)P,(20.O8.(21.O7.)(22.O8.O7.O6.R3?.)R1;.R19.)P,(20.O8.(21.O7.)(22.O8.O7.O6.R40.)R1<.R19.)P,(<.(=.(3>.O8.O7.O6.R41.)A2.O3.R1;.R1:.)$4>.)P,(4?.O8.R1>.(35.O7.)(36.O8.O7.O6.R42.)(31.&40.R38.)(31.&40.R3>.)R18.)P,(50.O7.(6.R1=.)+10.R19.)P,(50.O7.(6.R1=.)+10.R1:.)P,(<.(=.(3?.O8.O7.O6.R45.)A1.O2.R1;.)$51.)P,(7.(1<.&40.)R3:.(2;.&40.(6.R20.)))P,(7.(1<.&40.)R3:.(2;.&40.(6.R20.)))P,(7.(1<.&40.)R3:.(2;.&40.R20.))(52.O8.(53.O8.O7.O6.R46.R45.R44.R43.R3?.R3>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R49.R48.R47.R23.A4.O1.R48.R23.R22.R21.A2.O3.R23.R22.A1.O2.R1?.R20.R25.R24.)(28.(29.(2:.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(2;.&40.O5.)R26.(2=.(1<.&40.))R25.(2>.O8.))R24.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_xop_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z)
    (P : Z -> Prop) (PHI : mpd -> Z -> Z) (FRC : Z -> Z)
    (Rr : list blk -> mpd -> Z -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Ph,(1;.O9.O8.O7.)PLB,(12.$4.)PLF,(12.$4.)Pra,(1<.&40.)Psp,(1<.&40.)Pgp,(1<.&40.)Ptp,(1<.&40.)Pt0,(1<.&40.)Pt1,(1<.&40.)Pt2,(1<.&40.)Ps0,(1<.&40.)Ps1,(1<.&40.)Pa0,(1<.&40.)Pa1,(1<.&40.)Pa2,(1<.&40.)Pa3,(1<.&40.)Pa4,(1<.&40.)Pa5,(1<.&40.)Pa6,(1<.&40.)Pa7,(1<.&40.)Ps2,(1<.&40.)Ps3,(1<.&40.)Ps4,(1<.&40.)Ps5,(1<.&40.)Ps6,(1<.&40.)Ps7,(1<.&40.)Ps8,(1<.&40.)Ps9,(1<.&40.)Ps10,(1<.&40.)Ps11,(1<.&40.)Pt3,(1<.&40.)Pt4,(1<.&40.)Pt5,(1<.&40.)Pt6,(1<.&40.)PF,(46.&5.(1<.&40.))Pfc,(1<.&20.)Pm,P,(1<.&40.)(1=.(1<.&8.))Pmo,$27.PdX,$14.Pv,$13.Plo,$13.Pd,$13.P,(1>.O9.O8.O7.R2:.R29.R28.R6.)P,(3=.O9.O8.O7.R2;.R6.)P,(1?.O9.R8.R2;.R6.)P,(23.(7.$8.(9.R7.)$18.))P,A1.O4.R7.P,(16.O8.R2>.R2=.(31.&40.R2;.)(3;.O9.O8.O7.R2?.)R9.)P,P,(23.(7.$8.(9.R:.)$24.))(;.(<.(=.(>.R;.)(?.+4.(10.R;.)))R9.)(<.(31.&40.R2=.)(>.R;.)))P,(30.O9.R=.R9.(31.&40.R2=.))P,(<.(35.O8.)R:.)P,(<.R;.(4:.(4:.(31.&40.R2?.)O5.)(4;.O8.)))P,(<.(31.&40.R30.)(3;.O9.O8.O7.R34.))P,(7.$13.(4<.(31.&40.R31.)+10.)=)P,(7.(1<.&40.)R30.(2;.&40.(4=.O8.)))P,(2?.O9.R13.)P,(7.$13.(4<.(31.&40.R35.)+2.)=)P,(20.O9.(21.O8.)(22.O9.O8.O7.R39.)R15.R13.)P,(<.(=.(3>.O9.O8.O7.R3:.)A2.O3.R14.R13.)$4>.)P,(4?.O9.R17.(35.O8.)(36.O9.O8.O7.R3;.)(31.&40.R31.)(31.&40.R37.)R12.)P,(50.O8.(6.R16.)+10.R13.)P,(<.(=.(3?.O9.O8.O7.R3=.)A1.O2.R14.)$51.)P,(7.(1<.&40.)R32.(2;.&40.(6.R18.)))P,(7.(1<.&40.)R32.(2;.&40.R18.))(52.O9.(53.O9.O8.O7.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.R40.R3?.R3>.R1:.A3.O1.R3?.R1:.R19.A2.O3.R1:.R19.A1.O2.R17.R18.R1<.R1;.)(28.(29.(2:.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(2;.&40.O6.)R1=.(2=.(1<.&40.))R1<.(2>.O9.))R1;.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_MPI_INIT : Z := 0x09b9c0.          (* [comment removed for export] *)
Definition A_MPI_FREE : Z := 0x09ba64.          (* [comment removed for export] *)
Definition A_MPI_GROW : Z := 0x09b3dc.          (* [comment removed for export] *)
Definition A_MPI_RESIZE_CLEAR : Z := 0x09cfd4.  (* [comment removed for export] *)
Definition A_MPI_SHRINK : Z := 0x09bb74.        (* [comment removed for export] *)
Definition A_MPI_COPY : Z := 0x09be0c.          (* [comment removed for export] *)
Definition A_MPI_LSET : Z := 0x09c204.          (* [comment removed for export] *)
Definition A_MPI_GET_BIT : Z := 0x09c434.       (* [comment removed for export] *)
Definition A_MPI_SET_BIT : Z := 0x09c514.       (* [comment removed for export] *)
Definition A_MPI_BITLEN : Z := 0x09c8a8.        (* [comment removed for export] *)
Definition A_MPI_SIZE : Z := 0x09c91c.          (* [comment removed for export] *)
Definition A_MPI_MUL_INT : Z := 0x09c99c.       (* [comment removed for export] *)
Definition A_MPI_ADD_INT : Z := 0x09ccc0.       (* [comment removed for export] *)
Definition A_MPI_READ_BINARY_LE : Z := 0x09cef0. (* [comment removed for export] *)
Definition A_MPI_SHIFT_L : Z := 0x09d468.       (* [comment removed for export] *)
Definition A_MPI_SHIFT_R : Z := 0x09d670.       (* [comment removed for export] *)
Definition A_MPI_CMP_MPI : Z := 0x09d9a4.       (* [comment removed for export] *)
Definition A_MPI_CMP_INT : Z := 0x09dd64.       (* [comment removed for export] *)
Definition A_MPI_ADD_ABS : Z := 0x09df28.       (* [comment removed for export] *)
Definition A_MPI_SUB_ABS : Z := 0x09e4ec.       (* [comment removed for export] *)
Definition A_MPI_ADD_MPI : Z := 0x09e9d8.       (* [comment removed for export] *)
Definition A_ADD_SUB_MPI : Z := 0x09e9e0.       (* [comment removed for export] *)
Definition A_MPI_SUB_MPI : Z := 0x09eb68.       (* [comment removed for export] *)
Definition A_MPI_SUB_INT : Z := 0x09eb70.       (* [comment removed for export] *)
Definition A_MPI_MUL_MPI : Z := 0x09eda0.       (* [comment removed for export] *)
Definition A_MPI_DIV_MPI : Z := 0x09f48c.       (* [comment removed for export] *)
Definition A_MPI_MOD_MPI : Z := 0x0a04b0.       (* [comment removed for export] *)
Definition A_MPI_EXP_MOD : Z := 0x0a072c.       (* [comment removed for export] *)
Definition A_ZEROIZE_AND_FREE : Z := 0x0a7f14.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grow_PHI (nl : Z) : Z := 8 * nl + 2 * AVOL_CALL.

(* [comment removed for export] *)
Definition calls_FR (k d : Z) : Z := k * fr_charge d.
Lemma calls_FR_nonneg : forall k d, 0 <= k -> 0 <= d -> 0 <= calls_FR k d.
Proof. intros; unfold calls_FR, fr_charge; nia. Qed.

(* [comment removed for export] *)
Notation MPI_INIT_STACK_A := 16 (only parsing).
Notation ZEROIZE_AND_FREE_STACK_A := 16 (only parsing).
Notation MPI_FREE_STACK_A := 64 (only parsing).
Notation MPI_GROW_STACK_A := 96 (only parsing).
Notation MPI_RESIZE_CLEAR_STACK_A := 96 (only parsing).
Notation MPI_SHRINK_STACK_A := 96 (only parsing).
Notation MPI_COPY_STACK_A := 128 (only parsing).
Notation MPI_LSET_STACK_A := 96 (only parsing).
Notation MPI_SET_BIT_STACK_A := 128 (only parsing).
Notation MPI_SIZE_STACK_A := 32 (only parsing).
Notation MPI_SHIFT_L_STACK_A := 128 (only parsing).
Notation MPI_SHIFT_R_STACK_A := 64 (only parsing).
Notation MPI_CMP_INT_STACK_A := 128 (only parsing).
Notation MPI_ADD_ABS_STACK_A := 304 (only parsing).
Notation MPI_SUB_ABS_STACK_A := 224 (only parsing).
Notation MPI_ADD_SUB_STACK_A := 368 (only parsing).     (* [comment removed for export] *)
Notation MPI_ADD_INT_STACK_A := 496 (only parsing).     (* [comment removed for export] *)
Notation MPI_MUL_INT_STACK_A := 272 (only parsing).
Notation MPI_MUL_MPI_STACK_A := 528 (only parsing).     (* [comment removed for export] *)
Notation MPI_DIV_MPI_STACK_A := 720 (only parsing).     (* [comment removed for export] *)
Notation MPI_MOD_MPI_STACK_A := 864 (only parsing).
Notation MPI_EXP_MOD_STACK_A := 1264 (only parsing).    (* [comment removed for export] *)
Notation MPI_GET_MONT_R2_STACK_A := 912 (only parsing).
Notation MPI_MUL_MOD_STACK_A := 928 (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma client_wrange_where_A : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)PR,$11.PHIA,(1:.R2.R1.)Ph,(1;.R3.R2.R1.)PLB,(12.$4.)PLF,(12.$4.)Pm,P,(1<.&40.)(1=.(1<.&8.))PLB',(12.$4.)PSP,$13.PA,$13.Pk,$13.Plo,$13.P,(1>.R<.R;.R:.R9.R8.R7.R6.)P,Pb,$4.P,(41.$4.R1.R7.)(41.$4.R2.R;.)P,(1.(2.R=.)(3.$4.R7.(5.R9.))R6.(3;.R>.R=.R<.R;.)R5.R4.)P,(56.=R5.)P,(<.(35.R?.)R5.)P,(<.(=.R6.R7.)R9.)(;.(<.(=.R9.R8.)R7.)(<.R:.R9.))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m LB' SP A k lo HH HS CW Hk LOS Hlo.
  pose proof (art_lo segs R HIA) as ALO. pose proof (art_data_lo segs R HIA) as DHI.
  destruct (hm_apart segs R HIA h LB LF m HH) as [HBR _]. rewrite Forall_forall in HBR.
  assert (HL : forall x b, In b (LB' ++ fdata LF) -> fst b <= x < fst b + snd b -> x < (@alloc_ceiling (arl_L R))).
  { intros x b Hb Hr. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    - ddestruct (HBR b ltac:(apply in_app_iff; left; apply HS; exact Hb)) as (_ & _ & HC & _). lia.
    - ddestruct (in_fdata_hull LF b x Hb Hr) as (fb & Hfb & Hr2).
      ddestruct (HBR fb ltac:(apply in_app_iff; right; exact Hfb)) as (_ & _ & HC & _). lia. }
  assert (LOW : forall x, A <= x < A + k -> x < SP -> x < (@alloc_ceiling (arl_L R))).
  { intros x Hx HxS. destruct (CW x Hx) as [Hs|[[Hd _]|(b & Hb & Hr)]]; [exfalso; lia| lia| exact (HL x b Hb Hr)]. }
  destruct (Z_le_gt_dec SP A) as [Hs|Hs]; [right; exact Hs| left].
  pose proof (LOW A ltac:(lia) ltac:(lia)) as A0.
  destruct (Z_lt_ge_dec (A + k - 1) SP) as [H1|H1].
  - pose proof (LOW (A + k - 1) ltac:(lia) H1). lia.
  - exfalso. lia.
Qed.

(* [comment removed for export] *)



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_apart_app_l : forall (l1 l2 : list blk), blocks_apart (l1 ++ l2) -> blocks_apart l1.
Proof.
  intros l1 l2. induction l1 as [|[C j] r IH]; cbn; intros H; [exact I|].
  destruct H as [HC Hr]. split; [| apply IH; exact Hr]. intros B k Hb. apply HC. apply in_app_iff. left. exact Hb.
Qed.

Lemma blocks_apart_app_lr : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Pl1,(12.$4.)Pl2,(12.$4.)PB,$13.Pk,$13.PB',$13.Pk',$13.P,(57.(3.$4.R6.R5.))P,(41.(38.$13.$13.)(39.$13.$13.R5.R4.)R7.)P,(41.(38.$13.$13.)(39.$13.$13.R4.R3.)R7.)(;.(<.(=.R7.R6.)R5.)(<.(=.R5.R4.)R7.))")
(* [comment removed for export] *).
Proof.
  intros l1 l2 B k B' k'. induction l1 as [|[C j] r IH]; cbn; intros HA H1 H2; [destruct H1|].
  destruct HA as [HC Hr]. destruct H1 as [E|H1].
  - injection E as -> ->. apply HC. apply in_app_iff. right. exact H2.
  - apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma blocks_apart_dup : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Pl,(12.$4.)PB,$13.Pk,$13.PB',$13.Pk',$13.Px,$13.P,(57.R6.)P,(41.(38.$13.$13.)(39.$13.$13.R6.R5.)R7.)P,(41.(38.$13.$13.)(39.$13.$13.R5.R4.)R8.)P,(0.(<.R8.R4.)(56.R4.(=.R8.R7.)))P,(0.(<.R7.R5.)(56.R5.(=.R7.R6.)))(7.(38.$13.$13.)(39.$13.$13.R:.R9.)(39.$13.$13.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros l B k B' k' x. induction l as [|[C j] r IH]; cbn; intros HA H1 H2 R1 R2; [destruct H1|].
  destruct HA as [HC Hr]. destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - injection E1 as -> ->. destruct (HC B' k' H2); exfalso; lia.
  - injection E2 as -> ->. destruct (HC B k H1); exfalso; lia.
  - apply IH; assumption.
Qed.

Lemma cshd_mono_lb : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PR,$11.PLB,(12.$4.)PLB',(12.$4.)PLF,(12.$4.)PSSP,$13.PTOP,$13.Pc,$13.P,(58.R7.R6.R4.R3.R2.R1.)P,Pb,$4.P,(41.$4.R1.R8.)(41.$4.R2.R8.)(58.R9.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros R LB LB' LF SSP TOP c [H|[(b & Hb & Hr)|[H|H]]] HI; [left; exact H| right; left| right; right; left; exact H| right; right; right; exact H].
  exists b. split; [apply HI, Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma client_wrange_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PLx,$59.PLB,(12.$4.)PLF,(12.$4.)PSP,$13.PTOP,$13.Pd,$14.PA,$13.Pk,$13.P,(1.R8.(3.$4.R7.(5.R6.))R5.R4.R2.R1.)P,P,(7.$8.(9.R4.)$:.)(;.(<.(=.R4.R3.)(>.R5.))(<.(=.(>.R5.)(?.+4.(10.R5.)))R4.))(1.R:.(3.$4.(34.R9.R5.)(5.R8.))R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Lx LB LF SP TOP d A k CW AP x Hx. destruct (CW x Hx) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right].
  exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
  apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own d) eqn:EO; [intros []| | intros []].
  intros [E|[]]. subst b. cbn in Hr. specialize (AP eq_refl). lia.
Qed.

Lemma mpd_writableA_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PR,$11.PLB,(12.$4.)PLF,(12.$4.)PSP,$13.PTOP,$13.Pd,$14.P,(16.R6.R5.R4.R3.R2.R1.)(1.(2.R7.)(3.$4.(34.R6.R2.)(5.R5.))R4.R3.(6.R2.)+10.)")
(* [comment removed for export] *).
Proof. intros R LB LF SP TOP d [CW AP]. apply client_wrange_keep; assumption. Qed.

(* [comment removed for export] *)
Lemma in_keep_remove : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PLB,(12.(38.$13.$13.))Pd,$14.Pb,$4.P,(5:.$13.(5;.(38.$13.$13.)$13.(44.$13.$13.)R3.))P,(7.$8.(9.R3.)$:.)P,(41.(38.$13.$13.)(39.$13.$13.(>.R4.)(?.+4.(10.R4.)))R5.)P,(41.$4.R4.(34.R6.R5.))(41.$4.R5.(5<.(>.R6.)R7.))")
(* [comment removed for export] *).
Proof.
  intros LB d [B k] ND HO HIN Hb. unfold mpd_keep in Hb. rewrite HO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
  apply In_lb_remove_keep; [exact Hb|]. apply (nodup_fst_neq LB (md_p d) (4 * md_n d) B k ND HIN Hb).
  intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
Qed.

Lemma lb_remove_cons_other : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PA,$13.Pj,$13.PP,$13.PLB,(12.$4.)P,(23.(7.$13.R4.R2.))(7.(12.$4.)(5<.R3.(37.(38.$13.$13.)(39.$13.$13.R5.R4.)R2.))(37.(38.$13.$13.)(39.$13.$13.R5.R4.)(5<.R3.R2.)))")
(* [comment removed for export] *).
Proof. intros A j P LB NE. cbn. destruct (Z.eqb_spec A P); [contradiction| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma presA_drop_freed : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)PR,$11.PHIA,(1:.R2.R1.)Ph,(1;.R3.R2.R1.)PLB,(12.$4.)PLF,(12.$4.)PLBr,(12.(38.$13.$13.))PW,(12.(38.$13.$13.))PB,$13.Pk,$13.Pm0,P,(1<.&40.)(1=.(1<.&8.))Pm1,P,(1<.&40.)(1=.(1<.&8.))Pm2,P,(1<.&40.)(1=.(1<.&8.))PSP,$13.P,(1>.R>.R=.R<.R;.R:.R9.R4.)P,(41.(38.$13.$13.)(39.$13.$13.R7.R6.)R;.)P,Pb,(38.$13.$13.)Px,$13.P,(41.(38.$13.$13.)R2.R<.)P,(0.(<.(44.$13.$13.R3.)R2.)(56.R2.(=.(44.$13.$13.R3.)(45.$13.$13.R3.))))(0.(41.(38.$13.$13.)R4.R10.)(23.(7.(38.$13.$13.)R4.(39.$13.$13.R<.R;.))))P,(<.(5=.(2.R10.))(5>.(2.R10.)))P,(<.(5?.(2.R11.))(60.(2.R11.)))P,(<.(61.(2.R12.))R6.)P,(33.R14.R13.R>.R?.R7.(35.R13.)(36.R14.R13.R12.R11.)(37.(38.$13.$13.)(39.$13.$13.R<.(=.R<.R;.))R=.)R9.R8.)(33.R15.R14.R?.R10.R8.(35.R14.)(36.R15.R14.R13.R12.)R>.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF LBr W B k m0 m1 m2 SP HH HIN HR D1 D2 HSP [P S]. split; [| exact S].
  destruct (hm_apart segs R HIA h LB LF m0 HH) as [HF BA]. rewrite Forall_forall in HF.
  ddestruct (HF (B, k) ltac:(apply in_app_iff; left; exact HIN)) as (B0 & K0 & BC & BI). cbn in B0, K0, BC, BI.
  intros a Ha Hc Ho. apply P; [exact Ha| exact Hc|]. cbn [outside]. split; [| exact Ho].
  intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]].
  - clear - Hs Hin BC HSP. lia.
  - clear - Hd1 Hin BI D1 D2. lia.
  - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    + destruct (HR b a Hb Hr) as [HbL NE]. destruct b as [B' k']. cbn in Hr.
      apply NE. symmetry. eapply (blocks_apart_dup LB B k B' k' a); [eapply blocks_apart_app_l; exact BA| exact HIN| exact HbL| exact Hin| exact Hr].
    + ddestruct (in_fdata_hull LF b a Hb Hr) as ([FB n] & Hfb & Hr2). cbn in Hr2.
      destruct (blocks_apart_app_lr LB LF B k FB n BA HIN Hfb); [clear - H Hin Hr2; lia| clear - H Hin Hr2; lia].
Qed.

(* [comment removed for export] *)
Lemma fresh_apart_sub : forall R LB LF N k k', fresh_apart R LB LF N k -> 0 <= k' <= k -> fresh_apart R LB LF N k'.
Proof.
  (intros R LB LF N k k' dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros Hk). split; [exact F0|]. split; [lia|]. split; [lia|].
  intros B j Hb. destruct (F3 B j Hb); lia.
Qed.

(* [comment removed for export] *)
Lemma mpd_at_rebuild : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)Pm',P,(1<.&40.)(1=.(1<.&8.))PLB,(12.(38.$13.$13.))PX,$13.Psg,$13.Pn,$13.PP,$13.Plimbs,(12.(1<.&40.))Ppad,(1<.&40.)Pown,$8.P,(23.(7.$8.R1.$18.))P,(62.R;.R:.R8.(63.R5.(2;.&40.R7.)R6.R3.))P,(7.$13.(4<.R9.+8.)=)P,(56.=R:.)P,(7.$13.(64.(65.(1<.&40.)R7.))R9.)P,(0.(<.=R:.)(<.R:.$66.))P,(;.(7.$13.R<.+1.)(7.$13.R<.-1.))P,P,(7.$8.R8.$24.)(0.(7.$13.R<.=)(7.$13.R=.=))P,P,(7.$8.R9.$:.)(0.(<.+1.R>.)(0.(41.(38.$13.$13.)(39.$13.$13.R=.(?.+4.R>.))R11.)(0.(7.$13.(4<.R=.+10.)=)(67.R13.R12.R=.R<.))))(1?.R13.R12.R11.(68.R10.R?.R>.R=.R<.R;.R:.))")
(* [comment removed for export] *).
Proof.
  intros segs m' LB X sg n P limbs pad own HNS HX AL X0 LL NR SG HN HHp. split; [| exact SG].
  cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact HX|]. split; [exact AL|]. split; [exact X0|].
  split; [exact LL|]. split; [exact NR|]. destruct own; [exact (HN eq_refl)| exact (HHp eq_refl)| exfalso; exact (HNS eq_refl)].
Qed.

(* [comment removed for export] *)
Tactic Notation "acallxA_sp" constr(e) tactic3(apptac) :=
  lazymatch goal with
  | |- aevtA ?segs (KF _ ?R ?HIA ?h ?mo0) _ (MS _ _ _ _ _ ?m _) =>
      eapply (aevtA_cut_evtA_KF segs R HIA h mo0);
      [ apptac
      | lazymatch goal with |- forall x, ?P x -> _ => let hd := head_of P in try unfold hd end;
        rewrite ?(unsigned_lit e) by qlia; post_callA segs m ]
  end.

(* [comment removed for export] *)
Lemma presA_tail : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)PR,$11.PHIA,(1:.R2.R1.)Phh,(1;.R3.R2.R1.)PLBh,(12.$4.)PLBk,(12.$4.)PLF,(12.$4.)Plo,$13.PSP,$13.PX,$13.PmX,P,(1<.&40.)(1=.(1<.&8.))Pmm,P,(1<.&40.)(1=.(1<.&8.))Pm1,P,(1<.&40.)(1=.(1<.&8.))Pm2,P,(1<.&40.)(1=.(1<.&8.))P,(1>.R>.R=.R<.R;.R:.R8.R3.)P,Pb,$4.P,(41.$4.R1.R;.)(41.$4.R2.R=.)P,(<.(35.R?.)R9.)P,(<.R9.(3;.R11.R10.R?.R>.))P,(17.R12.(21.R11.)(22.R12.R11.R10.R?.)R8.R9.+10.)P,(69.(37.(38.$13.$13.)(39.$13.$13.R<.R;.)(37.(38.$13.$13.)(39.$13.$13.R:.(=.R:.+10.))(3:.(38.$13.$13.))))R7.R6.)P,(6:.R14.R8.R7.)(33.R15.R14.R10.R?.R=.(35.R14.)(36.R15.R14.R13.R12.)(37.(38.$13.$13.)(39.$13.$13.R<.(=.R<.+10.))(3:.(38.$13.$13.)))R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA hh LBh LBk LF lo SP X mX mm m1 m2 HH HI LOS TOP OX MU WM.
  pose proof (hcs_ok segs R HIA hh) as CSOK. pose proof (hm_top segs R HIA hh LBh LF mm HH) as HTOP. pose proof (hcs_stack segs R HIA hh) as SCS0.
  eapply (presA_weaken segs R LBh LBk LF LF SP SP (arl_stklo R) (arl_stklo R) (hstkhi segs R HIA hh) (hstkhi segs R HIA hh) [(X, X + 16)]);
    [| exact HI| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
  eapply (presA_drop_below segs R HIA hh LBh LF [(X, X + 16)] lo SP mm m1 m2); [exact HH| | clear; lia| exact LOS].
  eapply (presA_of_munch segs R LBh LF _ _ _ _ m1 m2 (hcs segs R HIA hh) CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
  unfold w_client. apply Forall_cons; [cbn [fst snd]|].
  { destruct (Z_lt_le_dec lo SP) as [Hl|Hl].
    - eapply crange_sub; [exact SCS0| exact LOS| clear - TOP HTOP Hl; lia].
    - intros x Hx. exfalso. clear - Hx Hl. lia. }
  apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil.
Qed.

Lemma presA_tail0 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)PR,$11.PHIA,(1:.R2.R1.)Phh,(1;.R3.R2.R1.)PLBh,(12.$4.)PLBk,(12.$4.)PLF,(12.$4.)Plo,$13.PSP,$13.Pmm,P,(1<.&40.)(1=.(1<.&8.))Pm1,P,(1<.&40.)(1=.(1<.&8.))Pm2,P,(1<.&40.)(1=.(1<.&8.))P,(1>.R<.R;.R:.R9.R8.R6.R3.)P,Pb,$4.P,(41.$4.R1.R9.)(41.$4.R2.R;.)P,(<.(35.R=.)R7.)P,(<.R7.(3;.R?.R>.R=.R<.))P,(69.(37.(38.$13.$13.)(39.$13.$13.R9.R8.)(3:.(38.$13.$13.)))R6.R5.)P,(6:.R11.R7.R6.)(33.R12.R11.R=.R<.R:.(35.R11.)(36.R12.R11.R10.R?.)(3:.$6;.)R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA hh LBh LBk LF lo SP mm m1 m2 HH HI LOS TOP MU WM.
  pose proof (hcs_ok segs R HIA hh) as CSOK. pose proof (hm_top segs R HIA hh LBh LF mm HH) as HTOP. pose proof (hcs_stack segs R HIA hh) as SCS0.
  eapply (presA_weaken segs R LBh LBk LF LF SP SP (arl_stklo R) (arl_stklo R) (hstkhi segs R HIA hh) (hstkhi segs R HIA hh) []);
    [| exact HI| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
  eapply (presA_drop_below segs R HIA hh LBh LF [] lo SP mm m1 m2); [exact HH| | clear; lia| exact LOS].
  eapply (presA_of_munch segs R LBh LF _ _ _ _ m1 m2 (hcs segs R HIA hh) CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
  unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
  destruct (Z_lt_le_dec lo SP) as [Hl|Hl].
  - eapply crange_sub; [exact SCS0| exact LOS| clear - TOP HTOP Hl; lia].
  - intros x Hx. exfalso. clear - Hx Hl. lia.
Qed.

(* [comment removed for export] *)
Lemma presA_nil_any : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "Psegs,(12.$19.)PR,$11.PLB,(12.$4.)PLF,(12.$4.)PSP,$13.PSSP,$13.PTOP,$13.PW,(12.$6;.)Pm,P,(1<.&40.)(1=.(1<.&8.))Pm',P,(1<.&40.)(1=.(1<.&8.))P,(33.R:.R9.R8.R7.R6.R5.R4.(3:.$6;.)R2.R1.)(33.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros. eapply presA_weaken; [eassumption| intros b Hb; exact Hb| intros b Hb; exact Hb| lia| lia| lia| intros y _; exact I].
Qed.

(* [comment removed for export] *)
Lemma client_range_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PLx,$59.PLB,(12.$4.)PLF,(12.$4.)Plo,$13.Pd,$14.PA,$13.Pk,$13.P,(49.R7.(3.$4.R6.(5.R5.))R4.R2.R1.)P,P,(7.$8.(9.R4.)$:.)(;.(<.(=.R4.R3.)(>.R5.))(<.(=.(>.R5.)(?.+4.(10.R5.)))R4.))(49.R9.(3.$4.(34.R8.R5.)(5.R7.))R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Lx LB LF lo d A k CR AP x Hx. destruct (CR x Hx) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right].
  exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
  apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own d) eqn:EO; [intros []| | intros []].
  intros [E|[]]. subst b. cbn in Hr. specialize (AP eq_refl). lia.
Qed.

(* [comment removed for export] *)
Lemma new_limbs_apartA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA ()) "PR,$11.PLB,(12.$4.)PLF,(12.$4.)Plo,$13.PdX,$14.PdX',$14.PA,$13.Pk,$13.P,Pb,$4.P,(41.$4.R1.(42.R4.))(;.(41.$4.R2.(42.R6.))(43.R:.(34.R9.R6.)R8.(44.$13.$13.R2.)(45.$13.$13.R2.)))P,(7.$8.(9.R4.)$:.)P,(<.+1.(10.R5.))P,(49.(2.R;.)(3.$4.R:.(5.R9.))R8.R5.R4.)P,P,(7.$8.(9.R8.)$:.)(;.(<.(=.R7.R6.)(>.R9.))(<.(=.(>.R9.)(?.+4.(10.R9.)))R7.))P,(<.(61.(2.R=.))R:.)P,(56.=R7.)(;.(<.(=.R9.R8.)(>.R:.))(<.(=.(>.R:.)(?.+4.(10.R:.)))R9.))")
(* [comment removed for export] *).
Proof.
  intros R LB LF lo dX dX' A k HF HO Hn CR AP HLO Hk.
  destruct (HF (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite HO; left; reflexivity)) as [HOLD|HFR].
  - unfold mpd_blk in HOLD. destruct (md_own dX) eqn:EO; [destruct HOLD| | destruct HOLD].
    destruct HOLD as [E|[]]. injection E as E1 E2. specialize (AP eq_refl). rewrite <- E1. replace (4 * md_n dX') with (4 * md_n dX) by lia. exact AP.
  - cbn [fst snd] in HFR.
    destruct (fresh_apart_client R (mpd_keep LB dX) LF lo A k (md_p dX') (4 * md_n dX') HFR
                ltac:(eapply client_range_keep; [exact CR| exact AP]) Hk ltac:(lia) HLO) as [H1|H1]; [right; exact H1| left; exact H1].
Qed.
