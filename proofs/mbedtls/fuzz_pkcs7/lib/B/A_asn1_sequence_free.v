(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Ltac2 gd_tbl_A_asn1_sequence_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove_all"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.True"; "Stdlib.Lists.List.NoDup"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "asn1_sequence_free_postA"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.chain"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "A_ASN1_SEQUENCE_FREE"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "A_WRAP_FREE"; "asn1_sequence_free_stmtA"].


Definition A_ASN1_SEQUENCE_FREE : Z := 0x09a5ec.
Definition A_WRAP_FREE : Z := 0x6947c.          (* [comment removed for export] *)
Notation ASN1_SEQUENCE_FREE_STACK_A := 32 (only parsing).   (* [comment removed for export] *)

Definition asn1_sequence_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (nodes : list Z) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1<.O1;.O1:.)Lh',(5.O1<.O1;.O1:.)(6.(7.$0.R13.(8.(9.(:.O16.O15.O14.O13.R12.R11.R10.O12.O11.R?.R>.R=.R<.R;.R:.R9.R8.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R7.R6.R5.R4.)O6.(;.O16.)O5.(<.(2.&40.))R3.(=.O1<.))R2.))(6.(>.O1<.R3.)(6.(?.O1<.R3.O3.(10.&40.O15.))(6.(11.O1.R2.)(6.(12.O1<.O1;.(13.O4.O18.)O17.(10.&40.O15.)(14.O1;.)(15.O1<.O1;.O1:.O19.)(16.$17.)O2.R3.)(6.(7.$18.(19.O1<.O1;.O1:.R1.)(19.O1<.O1;.O1:.O19.))(6.(7.$18.(15.O1<.O1;.O1:.R1.)(15.O1<.O1;.O1:.O19.))(6.(7.$18.(1:.O1<.O1;.O1:.R1.)(1:.O1<.O1;.O1:.O19.))(6.(1;.O1<.O1;.O1:.R1.R2.)(6.Px,$18.P,(1<.O1<.O1;.O1:.O19.R1.)(1<.O1<.O1;.O1:.R3.R2.)(6.(1=.(1>.O1<.O1;.O1:.R1.)(1?.(1>.O1<.O1;.O1:.O19.)(20.(21.(22.$18.O4.))$23.)))(6.(1=.(24.O1<.O1;.O1:.R1.)(1?.(24.O1<.O1;.O1:.O19.)(20.(21.(22.$18.O4.))(25.=))))(26.O1<.O1;.O1:.R1.(13.O4.O18.)O17.R3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_sequence_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "Ph,(5.O4.O3.O2.)PLB,(27.$28.)PLF,(27.$28.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(29.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pa,$18.Pnodes,(27.$18.)Plo,$18.P,(26.O4.O3.O2.R29.R28.R27.R5.)P,(1;.O4.O3.O2.R2:.R5.)P,(2:.O4.L,(27.$2;.)$2<.R7.R2:.R5.R4.)P,(2=.$18.R5.)P,(?.O4.R9.R5.(10.&40.R29.))P,(1=.(14.O3.)R6.)P,(1=.R7.(2>.(2>.(10.&40.R2;.)+20.)(2?.O3.)))P,(1=.(10.&40.R2<.)(19.O4.O3.O2.R30.))P,(7.$18.(30.(10.&40.R2=.)+10.)=)P,(7.(2.&40.)R2<.(31.&40.(32.O3.)))P,(>.O4.R?.)P,(1=.(1?.(1>.O4.O3.O2.R34.)(20.(21.(22.$18.R=.))$23.))$33.)P,(1=.(1?.(24.O4.O3.O2.R35.)(20.(21.(22.$18.R>.))(25.=)))$34.)P,(7.(2.&40.)R2:.(31.&40.R10.))(35.O4.(36.O4.O3.O2.R37.R36.R35.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R10.R?.R13.R12.)(8.(9.(:.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(31.&40.O1.)R14.(<.(2.&40.))R13.(=.O4.))R12.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma presW_sub_blocks_sf : ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "Psegs,(27.$37.)PR,$38.PHIA,(39.R2.R1.)Ph,(5.R3.R2.R1.)PLB,(27.$28.)PLBk,(27.$28.)PLF,(27.$28.)PSP,$18.PSSP,$18.PW,(27.$17.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))P,(3:.R<.R;.R:.R9.R8.R6.R5.R4.R3.R2.R1.)P,Pb,$28.P,(3;.$28.R1.R9.)(3;.$28.R2.R;.)(3:.R>.R=.R<.R;.R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros segs R HIA h LB LBk LF SP SSP W m0 m dd_H; ddestruct dd_H as (P & C1 & C2 & C3); intros HS).
  assert (HIB : forall x, in_block LBk x -> in_block LB x) by ((intros x dd_H; ddestruct dd_H as (b & Hb & Hr)); exists b; split; [apply HS, Hb| exact Hr]).
  split; [| split; [| split]].
  - eapply presA_weaken; [exact P| exact HS| intros b Hb; exact Hb| lia| lia| lia| intros x Hx; exact Hx].
  - intros c Hc. apply C1. destruct Hc as [A|[A|[A|A]]]; [left; exact A| right; left; apply HIB, A| right; right; left; exact A| right; right; right; exact A].
  - intros B j HB. apply C2. apply in_app_iff in HB. apply in_app_iff. destruct HB as [HB|HB]; [left; apply HS, HB| right; exact HB].
  - intros B j HB. apply C3. apply in_app_iff in HB. apply in_app_iff. destruct HB as [HB|HB]; [left; apply HS, HB| right; exact HB].
Qed.

Definition zchk_new : list Z := [0x9a610].
Lemma zchk_land1 x : Z.land x 1 = x mod 2. Proof. apply (Z.land_ones x 1); lia. Qed.
Lemma zchk_land3 x : Z.land x 3 = x mod 4. Proof. apply (Z.land_ones x 2); lia. Qed.
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Lemma zchk_land15 x : Z.land x 15 = x mod 16. Proof. apply (Z.land_ones x 4); lia. Qed.
Local Ltac zchk_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac zlia := zchk_clear; lia.
Local Ltac zchk_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; zlia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; zlia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; zlia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; zlia) ]
  end.
Local Ltac zchk_base :=
  first [ reflexivity
        | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.leb_le; zlia | apply Z.leb_gt; zlia
        | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Local Ltac zchk_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zchk_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zchk_rec
  | _ => zchk_base
  end.
Local Ltac zchk_solve :=
  rewrite ?zchk_land1, ?zchk_land3, ?zchk_land7, ?zchk_land15;
  zchk_dec;
  first [ reflexivity
        | unfold_cond; fold_lit_ux;
          repeat match goal with
                 | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
                 end;
          zchk_rec ].
Local Ltac zchk_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0x9a64c else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0x9a64c) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; zchk_solve]
  end.
Local Ltac zabsorb :=
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) zchk_new) with true => step; zsimp end
  end.
Local Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis FREE : arl_free R = A_WRAP_FREE.
  Hypothesis NEED0 : 0 <= arl_need_free R.
  Variables (LF : list blk).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z).
  (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB : list blk) (m : mem) (mo : Model).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SPL : lo <= bv_unsigned sp - 32 - arl_need_free R.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.

  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (art_data_lo asegs R HIA) as DHI;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh ?LBx LF ?mx, TOPx : bv_unsigned sp <= htop _ _ _ hh |- _ =>
      pose proof (hm_top asegs R HIA hh LBx LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPx HTOP; lia])
    end.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation POST := (asn1_sequence_free_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

  (* [comment removed for export] *)
  #[using="sp"] Lemma chain_presA_other : ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "Pns,$18.Pno,$18.PNP,P,(27.$2;.)SpPmm,P,(2.&40.)(3.(2.&8.))Pmm',P,(2.&40.)(3.(2.&8.))PLB0,(27.$28.)PSP,$18.PSSP,$18.PTP,$18.PA,$18.Pa,$18.Prest,(27.$18.)P,(3<.$3=.R<.R;.R:.R9.R7.R2.R1.)P,Px,$18.P,(3;.$18.R1.R3.)(3>.(7.$18.R2.R6.))P,(12.$3=.VR,(3?.R5.R9.)VLF,R8.R7.R6.(16.$17.)R;.R:.)P,(1=.=R?.)(3<.$3=.R10.R?.R>.R<.(3?.R7.R;.)R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros ns no NP mm mm' LB0 SP SSP TP A a rest HC HNE HP Hns.
    eapply chain_mem; [exact HC| |].
    - intros x Hx. apply In_lb_remove_keep; [| apply HNE; exact Hx]. eapply chain_nodes_in; eauto.
    - intros x cs Hx HR Hsz. eapply (presA_rw_cells asegs R); [exact HP| exact HR| | cbn; exact I].
      eapply client_range_block; [apply in_app_iff; left; apply In_lb_remove_keep; [eapply chain_nodes_in; eauto| apply HNE; exact Hx] | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG FREE NEED0 LOS SPL SPA TPV TOP"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "Prest,(27.$18.)Pa,$18.Phc,(5.$3=.VR,VHIA,)PLBc,(27.$28.)Pjk,(27.(2.&8.))Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.P,(3>.(7.(27.$18.)R17.(16.$18.)))P,(2=.$18.R18.)P,(2:.$3=.L,(27.$2;.)$2<.R4.R16.R18.R19.)P,(26.$3=.VR,VHIA,R18.R17.VLF,R5.)P,(1;.$3=.VR,VHIA,R19.R5.)P,(7.$18.(19.$3=.VR,VHIA,R1:.)(19.$3=.VR,VHIA,Vh,))P,(7.$18.(15.$3=.VR,VHIA,R1;.)(15.$3=.VR,VHIA,Vh,))P,(7.$18.(1:.$3=.VR,VHIA,R1<.)(1:.$3=.VR,VHIA,Vh,))P,Px,$18.P,(1<.$3=.VR,VHIA,Vh,R1.)(1<.$3=.VR,VHIA,R1?.R2.)P,(1=.(1?.(1>.$3=.VR,VHIA,R1>.)(20.(21.(22.$18.R20.))$23.))$33.)P,(1=.(1?.(24.$3=.VR,VHIA,R1?.)(20.(21.(22.$18.R21.))(25.=)))$34.)P,(3:.$3=.VR,VHIA,Vh,(13.R22.R1?.)VLF,(10.&40.Vsp,)(14.VR,)(16.$17.)Vm,R=.)P,(11.Vmo,R=.)P,(40.$3=.R?.(1?.(10.&40.Vsp,)-20.)(41.$2;.(42.#8.R20.)(41.$2;.(43.Vs1,)(41.$2;.(43.Vs0,)(41.$2;.(43.Vra,)(16.$2;.))))))P,(?.$3=.R10.Vlo,(1?.(10.&40.Vsp,)-20.))P,(>.$3=.R11.)(35.$3=.Lc,$0.(1.(2.&40.)Lx5',(2.&40.)(1.(2.&40.)Lx6',(2.&40.)(1.(2.&40.)Lx7',(2.&40.)(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lx28',(2.&40.)(1.(2.&40.)Lx29',(2.&40.)(1.(2.&40.)Lx30',(2.&40.)(1.(2.&40.)Lx31',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.$3=.VR,VHIA,)Lh',(5.$3=.VR,VHIA,)(6.(7.$0.R13.(8.(9.(:.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,R?.R>.R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(;.Vra,)Vfc,(<.(2.&40.))R3.(=.$3=.))R2.))(6.(>.$3=.R3.)(6.(?.$3=.R3.Vlo,(10.&40.Vsp,))(6.(11.Vmo,R2.)(6.(12.$3=.VR,(13.R3:.R37.)VLF,(10.&40.Vsp,)(14.VR,)(15.$3=.VR,VHIA,Vh,)(16.$17.)Vm,R3.)(6.(7.$18.(19.$3=.VR,VHIA,R1.)(19.$3=.VR,VHIA,Vh,))(6.(7.$18.(15.$3=.VR,VHIA,R1.)(15.$3=.VR,VHIA,Vh,))(6.(7.$18.(1:.$3=.VR,VHIA,R1.)(1:.$3=.VR,VHIA,Vh,))(6.(1;.$3=.VR,VHIA,R1.R2.)(6.Px,$18.P,(1<.$3=.VR,VHIA,Vh,R1.)(1<.$3=.VR,VHIA,R3.R2.)(6.(1=.(1>.$3=.VR,VHIA,R1.)(1?.(1>.$3=.VR,VHIA,R38.)(20.(21.(22.$18.R3:.))$23.)))(6.(1=.(24.$3=.VR,VHIA,R1.)(1?.(24.$3=.VR,VHIA,R38.)(20.(21.(22.$18.R3:.))(25.=))))(26.$3=.VR,VHIA,R1.(13.R3:.R37.)VLF,R3.)))))))))))))))))))))))))))))))(8.(9.(:.R22.(31.&40.(1?.(10.&40.Vsp,)-20.))Vgp,Vtp,R21.R20.R1?.(31.&40.(44.(45.VR,)))R1>.(31.&40.R26.)R1=.R1<.R1;.R1:.R19.R18.R17.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(31.&40.+9:60<.)Vfc,(<.(2.&40.))R12.(=.$3=.))R11.))")
(* [comment removed for export] *).
  Proof.
    induction rest as [|a' rest IH]; intros a hc LBc jk x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc
      HNE HND HC HH HKc HT HS HF HCS BUD BUDF PW MF FR ST MI; [congruence|].
    pose proof TOP as TOPc. rewrite <- HT in TOPc.
    rt_facts hc.
    destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nxt & post & H1 & H2 & HNODE & _ & HNX & HC').
    unfold SEQ_NEXT in HNX. unfold SEQ_SIZE in H2, HIN.
    pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite H2 in NB.
    pose proof (hm_aobj_block asegs R HIA hc LBc LF mm a 32 HH HIN) as OA.
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC') as NXB.
    cbn [length] in BUD, BUDF. rewrite Nat2Z.inj_succ in BUD, BUDF.
    pose proof (art_stk_high asegs R HIA) as SBLO.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ moc (conj HKc (mo_frame_refl moc))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_free asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (A := a) (n := 32) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; rewrite ?(unsigned_lit (al_sb AL)) by qlia;
        try eassumption; try reflexivity; try qlia.
      all: try (clear - BUD; unfold AVOL_CALL in *; lia).
      (* [comment removed for export] *)
      all: try (apply uwc_data; [clear; lia | clear - SBLO; lia]).
      all: try (clear - BUDF; unfold fr_charge in *; lia).
      all: match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]).
    { eapply (presA_rw_cells asegs R); [exact HP2| exact FR| | cbn; exact I]. simpl_sizes. apply client_range_stack. lia. }
    assert (HC2 : seq_chain asegs (fun _ => True) m2 (lb_remove a LBc) nxt rest).
    { eapply chain_presA_other; [exact HC'| | exact HP2| unfold SEQ_SIZE; lia].
      intros y Hy Hya. subst y. apply NoDup_cons_iff in HND. exact (proj1 HND Hy). }
    (* [comment removed for export] *)
    cbn [lb_remove_all] in PW.
    apply (presW_call asegs R HIA h _ LF _ _ [] m _ m2 (lb_remove a LBc) LF (bv_unsigned sp - 32) (arl_stklo R) (hstkhi asegs R HIA hc) []) in PW;
      [| exact HP2 | intros b Hb; eapply In_lb_remove_all; exact Hb | intros b Hb; exact Hb | clear; lia | clear; lia | rewrite HS; clear; lia | intros y Hy; exact Hy].
    clear FR HP2 HC HC' HNX HNODE OA MU WM ST MI.
    rewrite HT in HT2. rewrite HS in HS2. rewrite HF in HF2.
    assert (HCS2' : forall xq, hcs asegs R HIA h xq -> hcs asegs R HIA h2 xq) by (intros xq Hxq; apply HCS2, HCS, Hxq). clear HCS2. rename HCS2' into HCS2.
    pose proof TOP as TOP2. rewrite <- HT2 in TOP2.
    clear CSOK SB64 SCS0 SCS HTOP LAWS KINV ALWF' IMG' ALO DHI ACP SPR LO0.
    rt_facts h2.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF (mo_frame_trans _ _ _ MF1 MF2)))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KN by lia.
      destruct (chain_nonnull asegs _ _ _ _ _ _ _ HC2 KN) as (a2 & rest2 & ER).
      (* [comment removed for export] *)
      intros mo3 [HK3 MF3].
      eapply aevtS_mono.
      { eapply (IH nxt h2 (lb_remove a LBc)); try eassumption; try lia.
        all: try (rewrite ER; congruence).
        all: try (inversion HND; assumption).
        all: match goal with |- ?g => idtac "IH-LEFT:" g end. }
      intros c PO.
      ddestruct PO as (y5 & y6 & y7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m' & mo9 & h9 & E & Q).
      dexists y5, y6, y7, b0, b1, b2, b3, b4, b5, b6, b7, y28, y29, y30, y31, m', mo9, h9. split; [exact E|].
      ddestruct Q as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q10f & Q11).
      cbn [lb_remove_all]. repeat (split; [assumption|]). split; [| split; [| exact Q11]].
      + cbn [length]. rewrite Nat2Z.inj_succ. clear - Q10 HV2. unfold AVOL_CALL in *. lia.
      + cbn [length]. rewrite Nat2Z.inj_succ. clear - Q10f HFR2. unfold fr_charge in *. lia.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KN by lia.
      pose proof (chain_null_inv asegs _ _ _ _ _ _ ltac:(rewrite <- KN; exact HC2)) as ER. subst rest.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply aevtA_done. intros mo9 [HK9 MF9].
      deexists 15. dexists m2, mo9, h2.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      cbn [lb_remove_all]. split; [cbn [lb_remove_all] in PW; eapply presW_presA; exact PW|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
      split; [cbn [length]; clear - HV2; unfold AVOL_CALL in *; lia|].
      split; [cbn [length]; clear - HFR2; unfold fr_charge in *; lia|]. exact HH2.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG FREE NEED0 LOS SPL SPA TPV TOP"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "Pa,$18.Pnodes,(27.$18.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(26.$3=.VR,VHIA,Vh,VLB,VLF,Vm,)P,(1;.$3=.VR,VHIA,Vh,Vmo,)P,(2:.$3=.L,(27.$2;.)$2<.Vm,VLB,R12.R11.)P,(2=.$18.R12.)P,(?.$3=.Vm,Vlo,(10.&40.Vsp,))P,(>.$3=.Vm,)P,(1=.(1?.(1>.$3=.VR,VHIA,Vh,)(20.(21.(22.$18.R15.))$23.))$33.)P,(1=.(1?.(24.$3=.VR,VHIA,Vh,)(20.(21.(22.$18.R16.))(25.=)))$34.)(35.$3=.(36.$3=.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,R17.Vlo,Vm,Vmo,)(8.(9.(:.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(31.&40.R18.)R13.R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(31.&40.$46.)Vfc,(<.(2.&40.))Vm,(=.$3=.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros a nodes x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HH HKmo HC HND ST MI BUD BUDF. unfold A_ASN1_SEQUENCE_FREE.
    rt_facts h.
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC) as AB.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB0.
    pose proof (presW_sub_blocks_sf asegs R HIA h LB (lb_remove_all nodes LB) LF (bv_unsigned sp) (arl_stklo R) [] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia))
                  (fun b Hb => In_lb_remove_all nodes b LB Hb)) as PW.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      rewrite ?unsigned_lit in K0 by lia.
      pose proof (chain_null_inv asegs _ _ _ _ _ _ ltac:(rewrite <- K0; exact HC)) as ER. subst nodes.
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      release_frame FR ST (bv_unsigned sp).
      apply aevtA_done. intros mo9 [HK9 MF9].
      deexists 15. dexists m9, mo9, h.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      cbn [lb_remove_all length]. split; [cbn [lb_remove_all] in PW; eapply presW_presA; exact PW|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|]. split; [intros y Hy; exact Hy|].
      split; [clear; unfold AVOL_CALL; lia|]. split; [clear; unfold fr_charge; cbn; lia|]. assumption. }
    rewrite ?unsigned_lit in K0 by lia.
    destruct (chain_nonnull asegs _ _ _ _ _ _ _ HC K0) as (ahd & rest & ER).
    pose proof (abase_got _ _ _ AB0) as GOT. pose proof (abase_gsb _ _ _ AB0) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    intros mo1 [HK1 MF1].
    destruct (hm_apart asegs R HIA h LB LF _ HH) as [HBR _].
    eapply aevtS_mono.
    { eapply loop_walk with (rest := nodes) (LBc := LB) (hc := h); try eassumption; try reflexivity; try lia.
      all: try (rewrite ER; congruence).
      all: try (intros y Hy; exact Hy).
      - eapply chain_munch; [exact HC| exact MU| exact WM|].
        intros x Hx. pose proof (chain_nodes_in asegs _ _ _ _ _ _ _ HC x Hx) as HIN.
        rewrite Forall_forall in HBR. destruct (HBR _ ltac:(apply in_app_iff; left; exact HIN)) as (_ & _ & HCE & _). cbn [fst snd] in HCE.
        cbn [disjoint_from]. unfold SEQ_SIZE in *. clear - HCE LOS SPL NEED0 ALO. lia.
      all: match goal with |- ?g => idtac "LOOPCALL-LEFT:" g end. }
    intros c PO. exact PO.
  Qed.
End Walk.

Lemma A_asn1_sequence_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_asn1_sequence_free ()) "PR,$38.PHIA,(39.$3=.R1.)P,(47.(45.R2.))P,(7.$18.(48.R3.)$49.)P,(1=.=(2?.R4.))(4:.$3=.R5.R4.$46.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG FREE NEED0. unfold asn1_sequence_free_stmtA. intros until lo.
  intros HH HK HC HND ST LOS SLO TOP SPA TPV MI BUD BUDF ->.
  eapply main_walk; eassumption.
Qed.
