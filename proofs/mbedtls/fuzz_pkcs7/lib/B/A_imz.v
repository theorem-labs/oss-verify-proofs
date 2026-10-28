(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Ltac2 gd_tbl_A_imz () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.nth"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "Walk.imz_post"].


Lemma nth_upd_same : forall {X} (l : list X) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x d Hi; cbn in Hi |- *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma nth_upd_other : forall {X} (l : list X) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof. intros X l. induction l as [|y l IH]; intros [|i] [|j] x d Hij; cbn; try reflexivity; [lia|]. apply IH. lia. Qed.

Lemma lor_land15_nz : forall n P, 0 <= n -> 0 <= P -> n mod 16 <> 0 -> Z.land (Z.lor n P) 15 <> 0.
Proof.
  intros n P Hn HP Hm E. rewrite Z.land_lor_distr_l in E.
  apply Z.lor_eq_0_l in E. change 15 with (Z.ones 4) in E. rewrite Z.land_ones in E by lia. change (2^4) with 16 in E. lia.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imz_loop : ltac2:(CDefT.buildp (gd_tbl_A_imz ()) "Pk,$0.Pp,$1.Pq,$1.PP,$1.Pds,(2.(3.&8.))Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))P,(6.(7.R22.R23.)(8.R24.))P,(9.(6.R22.R24.)(:.R24.R23.))P,(;.$1.R24.(<.R23.(8.(=.(3.&8.)R22.))))P,(:.R25.(>.+2.+3?.))P,(?.$10.R5.R25.R24.)P,(11.VCS,R26.(8.(=.(3.&8.)R25.)))P,(:.=R27.)P,Pi,$0.P,(12.R1.(13.(7.R2;.R29.)))(;.(3.&8.)(14.(3.&8.)R2.R29.(15.&8.=))(15.&8.=))P,(16.$10.R9.)(17.$10.VAL,VCS,Lms',$18.(19.(3.&40.)La3',(3.&40.)(19.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(9.(;.$18.R3.(1:.(1;.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.(15.&40.=)(15.&40.R2>.)R2.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(15.&40.+7::7<.)R>.(1<.(3.&40.))R1.(1=.$10.)))(9.(1>.(1?.(20.$1.$1.)(21.$1.$1.R2=.R2>.)(22.(20.$1.$1.)))R=.R1.)(9.(23.$10.R=.R1.)(9.(16.$10.R1.)(?.$10.R1.R2=.(24.(3.&8.)(15.&8.=)(=.(3.&8.)R2<.)))))))))(1:.(1;.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.(15.&40.=)(15.&40.R2;.)(15.&40.R2<.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(15.&40.+7::70.)R;.(1<.(3.&40.))R:.(1=.$10.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros Hk Hp Hq Q63 ARR CR P0 ZS MI; [lia|]. al_facts.
    pose proof (munch_refl [(P, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (conj ARR Logic.I) as KEEP.
    assert (SOK : store_ok asegs m (Z_to_bv 64 p) 1 = true).
    { eapply (u8arr_store_ok asegs m P ds (p - P)); [exact ARR | lia | unfold wa; f_equal; lia]. }
    zstep. zstep. zstep.
    change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    destruct KEEP as [ARR0 _].
    pose proof (u8arr_write asegs m P ds (p - P) (Z_to_bv 8 0) ARR0 ltac:(lia)) as ARR1.
    replace (wa (P + (p - P))) with (Z_to_bv 64 p : word) in ARR1 by (unfold wa; f_equal; lia).
    set (m1 := write_to_mem m (Z_to_bv 64 p) [Z_to_bv 8 0]) in *.
    assert (MU1 : munch [(P, q)] m m1).
    { subst m1. replace (Z_to_bv 64 p : word) with (wa p) by reflexivity. apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; left; lia]. }
    assert (WM1 : wmono asegs m m1) by (subst m1; apply wmono_write; apply wmono_refl).
    assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    try clear MI.
    destruct (Z.eq_dec (p + 1) q) as [EQ|NE].
    - if_falseU. apply evtA_done. eexists _, m1. split; [rewrite EQ; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      replace (repeat (Z_to_bv 8 0) (length ds)) with (upd ds (Z.to_nat (p - P)) (Z_to_bv 8 0)); [exact ARR1|].
      apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0); [rewrite upd_length, repeat_length; reflexivity|].
      intros i Hi. rewrite upd_length in Hi. rewrite nth_repeat.
      destruct (Nat.eq_dec i (Z.to_nat (p - P))) as [->|NEi].
      + rewrite nth_upd_same by (rewrite ?upd_length; lia). reflexivity.
      + rewrite nth_upd_other by lia. apply ZS. lia.
    - if_trueU. eapply evtA_mono.
      + eapply (IH (p + 1) q P (upd ds (Z.to_nat (p - P)) (Z_to_bv 8 0))); rewrite ?upd_length; try eassumption; try lia.
        intros i Hi. destruct (Nat.eq_dec i (Z.to_nat (p - P))) as [->|NEi].
        -- rewrite nth_upd_same by (rewrite ?upd_length; lia). reflexivity.
        -- rewrite nth_upd_other by lia. apply ZS. lia.
      + cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & m' & -> & MU' & WM' & MI' & ARR')). dexists a3', m'. split; [reflexivity|].
        split; [eapply munch_trans; [exact MU1 | exact MU']|]. split; [eapply wmono_trans; [exact WM1 | exact WM']|].
        split; [exact MI'|]. rewrite upd_length in ARR'. exact ARR'.
  Qed.

  Definition imz_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (P n : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_imz ()) "Lms',$18.(19.(3.&40.)La2',(3.&40.)(19.(3.&40.)La3',(3.&40.)(19.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(9.(;.$18.R4.(1:.(1;.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.(15.&40.O3.)(15.&40.=)R3.R2.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O5.(25.O20.)O4.(1<.(3.&40.))R1.(1=.$10.)))(9.(1>.(1?.(20.$1.$1.)(21.$1.$1.O3.(<.O3.O2.))(22.(20.$1.$1.)))O1.R1.)(9.(23.$10.O1.R1.)(9.(16.$10.R1.)(?.$10.R1.O3.(24.(3.&8.)(15.&8.=)(13.O2.))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem imz_spec : ltac2:(CDefT.buildp (gd_tbl_A_imz ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))PP,$1.Pn,$1.Pds,(2.(3.&8.))P,(?.$10.R4.R3.R1.)P,(;.$1.(8.(=.(3.&8.)R2.))R3.)P,(6.+1.R4.)P,(26.(;.$1.(27.R5.+10.)=))P,(11.VCS,R7.R6.)P,(:.=R8.)P,(:.(<.R9.R8.)(>.+2.+3?.))P,(16.$10.R;.)P,(;.(3.&40.)R24.(15.&40.R;.))P,(;.(3.&40.)R24.(15.&40.=))P,(;.(3.&40.)R24.(15.&40.R<.))(17.$10.VAL,VCS,(28.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R>.R=.R?.)(1:.(1;.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(15.&40.+7::58.)R10.(1<.(3.&40.))R?.(1=.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until ds. intros ARR LEN N1 N16 CR P0 PH MI -> -> ->. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (lor_land15_nz n P ltac:(lia) ltac:(lia) N16) as NZ.
    assert (B15 : 0 <= Z.land (Z.lor n P) 15 < 16).
    { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16. apply Z.mod_pos_bound. lia. }
    if_falseU.
    (* [comment removed for export] *)
    zstep. if_falseU. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { eapply (imz_loop (Z.to_nat n) P (P + n) P ds); try eassumption; try lia.
      rewrite LEN. exact CR. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & m' & -> & MU & WM & MI' & ARR')).
    (* [comment removed for export] *)
    zstep. zstep.
    apply evtA_done. unfold imz_post. eexists _, _, m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    replace (Z.to_nat n) with (length ds) by lia. exact ARR'.
  Qed.
End Walk.
