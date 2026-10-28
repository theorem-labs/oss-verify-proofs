(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
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
Ltac2 gd_tbl_A_amem_lib () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Walk.memcpy_postZ"].


Lemma ltu_m65 : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Pn,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+28.)))(5.$6.(7.&40.(8.&40.-41.)(8.&40.(9.R2.-41.)))(:.(;.+1.R2.)(;.R2.+40.)))")
(* [comment removed for export] *).
Proof.
  intros n Hn. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace ((-65) mod 18446744073709551616) with 18446744073709551551 by reflexivity.
  destruct (Z_lt_le_dec n 1); [|destruct (Z_lt_le_dec 64 n)].
  - assert (n = 0) by lia. subst n. cbn. reflexivity.
  - replace ((n + -65) mod 18446744073709551616) with (n - 65) by (symmetry; apply Z.mod_small; lia).
    replace (1 <=? n) with true by (symmetry; apply Z.leb_le; lia). replace (n <=? 64) with false by (symmetry; apply Z.leb_gt; lia).
    cbn. apply Z.ltb_ge. lia.
  - replace ((n + -65) mod 18446744073709551616) with (18446744073709551616 + (n - 65)).
    2:{ pose proof (Z.div_mod (n + -65) 18446744073709551616 ltac:(lia)) as D.
        pose proof (Z.mod_pos_bound (n + -65) 18446744073709551616 ltac:(lia)) as B.
        assert ((n + -65) / 18446744073709551616 = -1) by (symmetry; apply Z.div_unique with (r := 18446744073709551616 + (n - 65)); lia). lia. }
    replace (1 <=? n) with true by (symmetry; apply Z.leb_le; lia). replace (n <=? 64) with true by (symmetry; apply Z.leb_le; lia).
    cbn. apply Z.ltb_lt. lia.
Qed.

Lemma hull_sh : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Pd,$0.P,(2.=R1.)(5.$0.(<.(9.+7???8000.(=.R2.+8.))(>.(9.+7???8000.(=.R2.+8.))+8.))(9.+7???8000.(=.(<.R2.(>.R2.+40.))+8.)))")
(* [comment removed for export] *).
Proof.
  intros d Hd.
  pose proof (Z.div_mod d 64 ltac:(lia)) as D64. pose proof (Z.mod_pos_bound d 64 ltac:(lia)) as M64.
  set (q := d / 64) in *. set (r := d mod 64) in *.
  assert (E8 : d / 8 = q * 8 + r / 8).
  { rewrite D64. replace (64 * q + r) with (r + (q * 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  rewrite E8.
  pose proof (Z.div_pos r 8 ltac:(lia) ltac:(lia)).
  assert (r / 8 < 8) by (apply Z.div_lt_upper_bound; lia).
  replace ((2147450880 + (q * 8 + r / 8)) mod 8) with (r / 8).
  2:{ replace (2147450880 + (q * 8 + r / 8)) with (r / 8 + (268431360 + q) * 8) by lia. rewrite Z.mod_add by lia.
      symmetry. apply Z.mod_small. lia. }
  replace (d - r) with (q * 8 * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_ex_range : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Psegs,(?.$10.)Pm,P,(11.&40.)(12.(11.&8.))PP,P,$0.SpPlo,$0.Pk,$13.P,Ps,$0.P,(1.(2.R3.R1.)(3.R1.(9.R3.(14.R2.))))(15.(11.&8.)Lb,(11.&8.)(16.R8.R7.R3.(17.(11.&8.)R1.(18.(11.&8.)))))P,(2.=R3.)P,(2.(9.R4.(14.R3.))(4.+2.+40.))(15.(?.(11.&8.))Lbs,(?.(11.&8.))(1.(5.$13.(19.(11.&8.)R1.)R5.)(16.R9.R8.R6.R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs m P lo k H Hlo Hhi.
  assert (G : forall j, (j <= k)%nat -> exists bs, length bs = j /\ forall i, (i < j)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
  { induction j as [|j IH]; intros Hj.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - ddestruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (lo + Z.of_nat j) ltac:(lia)) as [b (_ & _ & Hb)]. specialize (Hb 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in Hb. cbn [nth_error] in Hb.
      exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i j).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  ddestruct (G k ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. apply Hbs. rewrite <- Hlen. exact Hi.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Record amem_consts (m : mem) : Prop := {
    ac_gric : ro_cells asegs m 0x0f69b8 [C8 (Z_to_bv 64 0x10a6d9)];   (* [comment removed for export] *)
    ac_ric : ro_cells asegs m 0x10a6d9 [C1 (Z_to_bv 8 1)];            (* [comment removed for export] *)
    ac_rmemset : ro_cells asegs m 0x0f7cd0 [C8 (Z_to_bv 64 0x0eadc4)];(* [comment removed for export] *)
    ac_rmemcpy : ro_cells asegs m 0x0f7cc8 [C8 (Z_to_bv 64 0x0ea9c0)];(* [comment removed for export] *)
    ac_rip : rip_consts m
  }.

  (* [comment removed for export] *)
  Definition amem_apart (A n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "(1.(1:.(2.(9.O2.O1.)+?5>50.)(2.+?5>78.O2.))(1.(1:.(2.(9.O2.O1.)+?69;8.)(2.+?69<0.O2.))(1.(1:.(2.(9.O2.O1.)+?7<<8.)(2.+?7<=8.O2.))(1.(1:.(2.(9.O2.O1.)+1099?8.)(2.+109:00.O2.))(1:.(2.(9.O2.O1.)+10:6=8.)(2.+10:6?<.O2.))))))")
(* [comment removed for export] *).

  Definition amemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST v n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Lms',$1;.(15.(11.&40.)Lt0,(11.&40.)(15.(11.&40.)Lt1,(11.&40.)(15.(11.&40.)Lt2,(11.&40.)(15.(11.&40.)La1,(11.&40.)(15.(11.&40.)La2,(11.&40.)(15.(11.&40.)La3,(11.&40.)(15.(11.&40.)La4,(11.&40.)(15.(11.&40.)La5,(11.&40.)(15.(11.&40.)La6,(11.&40.)(15.(11.&40.)La7,(11.&40.)(15.(11.&40.)Lt3,(11.&40.)(15.(11.&40.)Lt4,(11.&40.)(15.(11.&40.)Lt5,(11.&40.)(15.(11.&40.)Lt6,(11.&40.)(15.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(1.(5.$1;.R10.(1<.(1=.O17.O16.O15.O14.R?.R>.R=.O13.O12.(8.&40.O5.)R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(1>.O17.)O6.(1?.(11.&40.))R1.(20.$21.)))(1.(22.(17.(23.$0.$0.)(24.$0.$0.O5.(9.O5.O3.))(17.(23.$0.$0.)(24.$0.$0.O2.(25.&40.O16.))(18.(23.$0.$0.))))O1.R1.)(1.(26.$21.O1.R1.)(1.(27.$21.R1.)(1.(28.$21.R1.O5.(29.(11.&8.)(8.&8.O4.)(2:.O3.)))(2;.$21.R1.O2.(25.&40.O16.))))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma amemset_orloop : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Pk,$13.Pp,$0.Pq,$0.Pra,(11.&40.)Psp,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0,(11.&40.)Ps1,(11.&40.)Pa0,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Ps2,(11.&40.)Ps3,(11.&40.)Ps4,(11.&40.)Ps5,(11.&40.)Ps6,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Plo,$0.Phi,$0.P,(2.(<.R23.R24.)(14.R25.))P,(1.(2.R3.R25.)(3.R25.R24.))P,(2.R25.R3.)P,(3.R4.(4.+2.+3?.))P,(2.=R6.)P,Px,$0.P,(1.(2.R8.R1.)(3.R1.R7.))(15.(11.&8.)Lb,(11.&8.)(16.$21.R;.R3.(17.(11.&8.)R1.(18.(11.&8.)))))P,Px,$0.P,(1.(2.R9.R1.)(3.R1.R8.))(2=.VAL,VCS,R2.)(2>.$21.VAL,VCS,Lms',$1;.(15.(11.&40.)La5',(11.&40.)(15.(11.&40.)La6',(11.&40.)(5.$1;.R3.(1<.(1=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(8.&40.R2=.)(8.&40.R2=.)R2.R1.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(8.&40.+68424.)R>.(1?.(11.&40.))R=.(20.$21.)))))(1<.(1=.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(8.&40.R2;.)(8.&40.R2:.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(8.&40.+68414.)R;.(1?.(11.&40.))R:.(20.$21.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until hi; intros Hk Hp Hq Hhi Hlo RD AOK; [lia|].
    al_facts.
    destruct (RD p ltac:(lia)) as [b B]. pose proof (bytes_at_read1 _ _ _ _ B) as RDB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec (p + 1) q) as [EQ|NE].
    - if_falseU. rewrite EQ. finish.
    - if_trueU. eapply IH; try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CSOK"] Lemma shrd_munch : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "PW,(?.$2?.)Pm,P,(11.&40.)(12.(11.&8.))Pm',P,(11.&40.)(12.(11.&8.))P,(30.VCS,R3.)P,(22.R4.R3.R2.)P,Pc,$0.P,A1.VCS,R1.(15.(11.&8.)Lb,(11.&8.)(16.$21.R7.(31.VAL,R3.)(17.(11.&8.)R1.(18.(11.&8.)))))Pc,$0.P,A1.VCS,R1.(15.(11.&8.)Lb,(11.&8.)(16.$21.R7.(31.VAL,R3.)(17.(11.&8.)R1.(18.(11.&8.)))))")
(* [comment removed for export] *).
  Proof.
    intros W m m' HW MU SH c Hc. destruct (SH c Hc) as [b B]. exists b.
    destruct CSOK as (C1 & _). ddestruct (C1 c Hc) as (R0 & R1 & R2 & NCS).
    eapply bytes_at_transport; [exact B | exact MU |]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply (disjoint1_of_not_cs CS); assumption.
  Qed.

  #[using="Type"] Lemma rip_consts_munch : forall lo hi m m',
    munch [(lo, hi)] m m' -> HSE < lo -> rip_consts m -> rip_consts m'.
  Proof.
    intros lo hi m m' MU LO [R1 R2 R3 R4 R5 R6 R7 R8].
    split; (eapply ro_cells_transport; [eassumption | exact MU | cbn; split; [lia | exact I]]).
  Qed.

  
  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma amemcpy_orloop : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Ppc,$0.Pk,$13.Pp,$0.Pq,$0.Pra,(11.&40.)Psp,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0,(11.&40.)Ps1,(11.&40.)Pa0,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Ps2,(11.&40.)Ps3,(11.&40.)Ps4,(11.&40.)Ps5,(11.&40.)Ps6,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Plo,$0.Phi,$0.P,(1:.(5.$0.R26.+68130.)(1:.(5.$0.R26.+681=4.)(1:.(5.$0.R26.+689=0.)(1:.(5.$0.R26.+68>78.)(5.$0.R26.+68?78.)))))P,(2.(<.R24.R25.)(14.R26.))P,(1.(2.R4.R26.)(3.R26.R25.))P,(2.R26.R4.)P,(3.R5.(4.+2.+3?.))P,(2.=R7.)P,Px,$0.P,(1.(2.R9.R1.)(3.R1.R8.))(15.(11.&8.)Lb,(11.&8.)(16.$21.R<.R3.(17.(11.&8.)R1.(18.(11.&8.)))))P,Px,$0.P,(1.(2.R:.R1.)(3.R1.R9.))(2=.VAL,VCS,R2.)(2>.$21.VAL,VCS,Lms',$1;.(15.(11.&40.)La5',(11.&40.)(15.(11.&40.)La6',(11.&40.)(5.$1;.R3.(1<.(1=.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.(8.&40.R2>.)(8.&40.R2>.)R2.R1.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(8.&40.(9.R31.+10.))R?.(1?.(11.&40.))R>.(20.$21.)))))(1<.(1=.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.(8.&40.R2<.)(8.&40.R2;.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(8.&40.R2>.)R<.(1?.(11.&40.))R;.(20.$21.)))")
(* [comment removed for export] *).
  Proof.
    intros pc k. intros until hi. intros PC.
    destruct PC as [-> | [-> | [-> | [-> | ->]]]];
      [ replace (426288 + 16) with 426304 by reflexivity | replace (426452 + 16) with 426468 by reflexivity
      | replace (428496 + 16) with 428512 by reflexivity | replace (429688 + 16) with 429704 by reflexivity
      | replace (429944 + 16) with 429960 by reflexivity ]; revert p a5 a6;
      (induction k as [|k IH]; intros p a5 a6 Hk Hp Hq Hhi Hlo RD AOK; [lia|]; al_facts;
       destruct (RD p ltac:(lia)) as [b B]; pose proof (bytes_at_read1 _ _ _ _ B) as RDB;
       zstep; zstep; zstep; zstep;
       destruct (Z.eq_dec (p + 1) q) as [EQ|NE];
       [ if_falseU; rewrite EQ; finish
       | if_trueU; eapply IH; try eassumption; lia ]).
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma qc_facts : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Pm,P,(11.&40.)(12.(11.&8.))PX,$0.Pn,$0.P,(32.$21.VAL,VCS,R3.R2.R1.)P,(1.(2.+1.R2.)(2.R2.+40.))P,(3.=R4.)P,(2.(9.(9.R5.R4.)+7.)+7???????????.)P,(33.VCS,(<.R6.(>.R6.+40.))+40.)P,(33.VCS,(<.(<.(9.R7.R6.)+1.)(>.(<.(9.R7.R6.)+1.)+40.))+40.)P,Pc,$0.P,A1.VCS,R1.(15.(11.&8.)Lb,(11.&8.)(16.$21.R<.(31.VAL,R3.)(17.(11.&8.)R1.(18.(11.&8.)))))(15.$0.Lq0,$0.(15.$0.Lq1,$0.(15.(?.(11.&8.))Lw0,(?.(11.&8.))(15.(?.(11.&8.))Lw1,(?.(11.&8.))(1.(5.$0.(=.(<.R=.(>.R=.+40.))+8.)(34.+8.R4.))(1.(5.$0.(=.(<.(<.(9.R=.R<.)+1.)(>.(<.(9.R=.R<.)+1.)+40.))+8.)(34.+8.R3.))(1.(1.(2.=R4.)(2.R4.R3.))(1.(2.(9.(34.+8.R3.)+8.)(4.+2.+2=.))(1.(1.(2.(34.+8.R4.)(=.R=.+8.))(1.(2.(=.R=.+8.)(=.(<.(9.R=.R<.)+1.)+8.))(2.(=.(<.(9.R=.R<.)+1.)+8.)(9.(34.+8.R3.)+7.))))(1.Px,$0.P,(1.(2.(9.+7???8000.(34.+8.R5.))R1.)(3.R1.(9.(9.+7???8000.(34.+8.R4.))+8.)))(2=.VAL,VCS,R2.)(1.Px,$0.P,(1.(2.(9.+7???8000.(34.+8.R5.))R1.)(3.R1.(9.(9.+7???8000.(34.+8.R4.))+8.)))(15.(11.&8.)Lb,(11.&8.)(16.$21.R11.R3.(17.(11.&8.)R1.(18.(11.&8.)))))(1.(5.(12.(?.(11.&8.)))(35.$21.R>.(8.&40.(9.+7???8000.(34.+8.R4.)))#8.)(36.(?.(11.&8.))R2.))(1.(5.(12.(?.(11.&8.)))(35.$21.R>.(8.&40.(9.+7???8000.(34.+8.R3.)))#8.)(36.(?.(11.&8.))R1.))(1.(1.(2.=(=.R=.+8.))(3.(=.R=.+8.)(4.+2.+2?.)))(1.(2.=(=.(<.(9.R=.R<.)+1.)+8.))(3.(=.(<.(9.R=.R<.)+1.)+8.)(4.+2.+2?.)))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros m X n OBJ Hn X0 XH HULL0 HULL1 SHRD. al_facts.
    pose proof (Z.mod_pos_bound X 64 ltac:(lia)) as M0. pose proof (Z.mod_pos_bound (X + n - 1) 64 ltac:(lia)) as M1.
    pose proof (Z.div_mod X 64 ltac:(lia)) as D0. pose proof (Z.div_mod (X + n - 1) 64 ltac:(lia)) as D1.
    set (q0 := X / 64) in *. set (q1 := (X + n - 1) / 64) in *.
    assert (Q01 : q0 <= q1) by (subst q0 q1; apply Z.div_le_mono; lia).
    clearbody q0 q1.
    replace (X - X mod 64) with (64 * q0) in * by lia.
    replace (X + n - 1 - (X + n - 1) mod 64) with (64 * q1) in * by lia.
    assert (CSPAN : forall c, 64 * q0 <= c < 64 * q1 + 64 -> CS c).
    { intros c Hc. destruct (Z_lt_le_dec c (64 * q0 + 64)); [apply HULL0; lia|]. destruct (Z_lt_le_dec c (64 * q1)); [|apply HULL1; lia].
      apply (aobj_crange _ _ _ _ _ _ OBJ). lia. }
    assert (AOKS : forall x, SB + 8 * q0 <= x < SB + 8 * q1 + 8 -> aok_addr AL CS x).
    { intros x Hx. right; left. exists (8 * (x - SB)). split; [apply CSPAN; lia|].
      unfold shadow_of. rewrite ASB. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    assert (RDS : forall x, SB + 8 * q0 <= x < SB + 8 * q1 + 8 -> exists b, bytes_at asegs m x [b]).
    { intros x Hx. destruct (SHRD (8 * (x - SB)) ltac:(apply CSPAN; lia)) as [b B]. exists b.
      replace x with (shadow_of AL (8 * (x - SB))) at 1; [exact B|].
      unfold shadow_of. rewrite ASB. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
   
    destruct (bytes_at_ex_range asegs m (fun _ => True) (2147450880 + 8 * q0) 8 ltac:(intros s' Hs; apply RDS; cbn in Hs; lia) ltac:(lia) ltac:(cbn; lia))
      as (w0 & Lw0 & Bw0).
    destruct (bytes_at_ex_range asegs m (fun _ => True) (2147450880 + 8 * q1) 8 ltac:(intros s' Hs; apply RDS; cbn in Hs; lia) ltac:(lia) ltac:(cbn; lia))
      as (w1 & Lw1 & Bw1).
    pose proof (bytes_at_read asegs m (2147450880 + 8 * q0) w0 0 8 Bw0 ltac:(lia) ltac:(rewrite Lw0; lia)) as RD0. rewrite Z.add_0_r in RD0.
    change (skipn (Z.to_nat 0) w0) with w0 in RD0. rewrite firstn_all2 in RD0 by lia. unfold wa in RD0.
    pose proof (bytes_at_read asegs m (2147450880 + 8 * q1) w1 0 8 Bw1 ltac:(lia) ltac:(rewrite Lw1; lia)) as RD1. rewrite Z.add_0_r in RD1.
    change (skipn (Z.to_nat 0) w1) with w1 in RD1. rewrite firstn_all2 in RD1 by lia. unfold wa in RD1.
    dexists q0, q1, w0, w1.
    pose proof (Z.div_pos X 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound X 8 (2^47) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (X + n - 1) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (X + n - 1) 8 (2^47) ltac:(lia) ltac:(lia)).
    split. { replace (64 * q0) with (q0 * 8 * 8) by lia. rewrite Z.div_mul by lia. lia. }
    split. { replace (64 * q1) with (q1 * 8 * 8) by lia. rewrite Z.div_mul by lia. lia. }
    split; [lia|]. split; [lia|].
    split.
    { split; [|split].
      - replace (8 * q0) with ((q0 * 8 * 8) / 8) by (rewrite Z.div_mul by lia; lia). apply Z.div_le_mono; lia.
      - apply Z.div_le_mono; lia.
      - replace (8 * q1 + 7) with ((63 + (q1 * 8) * 8) / 8) by (rewrite Z.div_add by lia; change (63 / 8) with 7; lia).
        apply Z.div_le_mono; lia. }
    split; [exact AOKS|]. split; [exact RDS|]. split; [exact RD0|]. split; [exact RD1|]. lia.
  Qed.

  Definition chkS_post (sp gp tp s0 s3 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Lms',$1;.(15.(11.&40.)Lra,(11.&40.)(15.(11.&40.)Lt0,(11.&40.)(15.(11.&40.)Lt1,(11.&40.)(15.(11.&40.)Lt2,(11.&40.)(15.(11.&40.)Ls1,(11.&40.)(15.(11.&40.)La3,(11.&40.)(15.(11.&40.)La4,(11.&40.)(15.(11.&40.)La5,(11.&40.)(15.(11.&40.)La6,(11.&40.)(15.(11.&40.)La7,(11.&40.)(15.(11.&40.)Ls2,(11.&40.)(15.(11.&40.)Ls5,(11.&40.)(15.(11.&40.)Ls7,(11.&40.)(15.(11.&40.)Lt3,(11.&40.)(15.(11.&40.)Lt4,(11.&40.)(15.(11.&40.)Lt5,(11.&40.)(15.(11.&40.)Lt6,(11.&40.)(15.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(1.(5.$1;.R13.(1<.(1=.R12.O11.O10.O?.R11.R10.R?.O>.R>.(8.&40.O5.)(8.&40.O4.)(8.&40.O3.)R=.R<.R;.R:.R9.R8.O=.O<.R7.(8.&40.(9.O3.-41.))R6.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.&40.+67>64.)O6.(1?.(11.&40.))R1.(20.$21.)))(1.(22.(17.(23.$0.$0.)(24.$0.$0.O2.(25.&40.O11.))(18.(23.$0.$0.)))O1.R1.)(1.(26.$21.O1.R1.)(1.(27.$21.R1.)(2;.$21.R1.O2.(25.&40.O11.))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition chkD_post (sp gp tp s0 s4 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Lms',$1;.(15.(11.&40.)Lra,(11.&40.)(15.(11.&40.)Lt0,(11.&40.)(15.(11.&40.)Lt1,(11.&40.)(15.(11.&40.)Lt2,(11.&40.)(15.(11.&40.)Ls1,(11.&40.)(15.(11.&40.)La3,(11.&40.)(15.(11.&40.)La4,(11.&40.)(15.(11.&40.)La5,(11.&40.)(15.(11.&40.)La6,(11.&40.)(15.(11.&40.)La7,(11.&40.)(15.(11.&40.)Ls2,(11.&40.)(15.(11.&40.)Ls3,(11.&40.)(15.(11.&40.)Ls5,(11.&40.)(15.(11.&40.)Ls7,(11.&40.)(15.(11.&40.)Lt3,(11.&40.)(15.(11.&40.)Lt4,(11.&40.)(15.(11.&40.)Lt5,(11.&40.)(15.(11.&40.)Lt6,(11.&40.)(15.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(1.(5.$1;.R14.(1<.(1=.R13.O11.O10.O?.R12.R11.R10.O>.R?.(8.&40.O5.)(8.&40.O4.)(8.&40.O3.)R>.R=.R<.R;.R:.R9.R8.O=.R7.O<.R6.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.&40.+67>:<.)O6.(1?.(11.&40.))R1.(20.$21.)))(1.(22.(17.(23.$0.$0.)(24.$0.$0.O2.(25.&40.O11.))(18.(23.$0.$0.)))O1.R1.)(1.(26.$21.O1.R1.)(1.(27.$21.R1.)(2;.$21.R1.O2.(25.&40.O11.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n : Z) (src : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Lms',$1;.(15.(11.&40.)Lt0,(11.&40.)(15.(11.&40.)Lt1,(11.&40.)(15.(11.&40.)Lt2,(11.&40.)(15.(11.&40.)La1',(11.&40.)(15.(11.&40.)La2',(11.&40.)(15.(11.&40.)La3,(11.&40.)(15.(11.&40.)La4,(11.&40.)(15.(11.&40.)La5,(11.&40.)(15.(11.&40.)La6,(11.&40.)(15.(11.&40.)La7,(11.&40.)(15.(11.&40.)Lt3,(11.&40.)(15.(11.&40.)Lt4,(11.&40.)(15.(11.&40.)Lt5,(11.&40.)(15.(11.&40.)Lt6,(11.&40.)(15.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(1.(5.$1;.R10.(1<.(1=.O17.O16.O15.O14.R?.R>.R=.O13.O12.(8.&40.O5.)R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(1>.O17.)O6.(1?.(11.&40.))R1.(20.$21.)))(1.(22.(17.(23.$0.$0.)(24.$0.$0.O5.(9.O5.O3.))(18.(23.$0.$0.)))O1.R1.)(1.(26.$21.O1.R1.)(1.(27.$21.R1.)(1.(37.$21.R1.O5.(17.$38.(39.(2:.O3.)O2.)(18.$38.)))(16.$21.R1.O4.O2.)))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG"] Lemma A_memcpy_evtA_Z : ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Pra,(11.&40.)Psp,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0,(11.&40.)Ps1,(11.&40.)Pa0,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Ps2,(11.&40.)Ps3,(11.&40.)Ps4,(11.&40.)Ps5,(11.&40.)Ps6,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))PDST,$0.PSRC,$0.Pn,$0.Psrc,(?.(11.&8.))Pjunk,(?.(11.&8.))P,(16.$21.R6.R4.R2.)P,(5.$13.(19.(11.&8.)R3.)(2:.R4.))P,(37.$21.R8.R7.(17.$38.(39.(2:.R5.)R3.)(18.$38.)))P,(1:.(2.(9.R7.R6.)R8.)(2.(9.R8.R6.)R7.))P,(27.$21.R:.)P,(33.VCS,R:.R8.)P,(33.VCS,R:.R9.)P,(3.=R<.)P,(3.=R<.)P,(2.=R<.)P,(3.(9.R?.R=.)(4.+2.+40.))P,(3.(9.R?.R>.)(4.+2.+40.))P,(5.(11.&40.)R2:.(8.&40.R11.))P,(5.(11.&40.)R2:.(8.&40.R11.))P,(5.(11.&40.)R2:.(8.&40.R11.))(2>.$21.VAL,VCS,(3:.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R14.R13.R12.R11.R15.)(1<.(1=.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(8.&40.+>:9<0.)R16.(1?.(11.&40.))R15.(20.$21.)))")
(* [comment removed for export] *).
  Proof.
    intros until junk. intros SRCB LEN DSTC SEP MI C0 C1 P0 P1 N0 B0 B1 -> -> ->.
    pose proof (A_memcpy_evtA AL CS IMG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as H.
    rewrite !unsigned_lit in H by lia.
    eapply evtA_cut; [apply H; assumption|].
    cbn beta. intros ms' P. apply evtA_done. hnf in P. rewrite !unsigned_lit in P by lia. exact P.
  Qed.

  Definition amemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (ss : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_amem_lib ()) "Lms',$1;.(15.(11.&40.)Lt0,(11.&40.)(15.(11.&40.)Lt1,(11.&40.)(15.(11.&40.)Lt2,(11.&40.)(15.(11.&40.)La1,(11.&40.)(15.(11.&40.)La2,(11.&40.)(15.(11.&40.)La3,(11.&40.)(15.(11.&40.)La4,(11.&40.)(15.(11.&40.)La5,(11.&40.)(15.(11.&40.)La6,(11.&40.)(15.(11.&40.)La7,(11.&40.)(15.(11.&40.)Lt3,(11.&40.)(15.(11.&40.)Lt4,(11.&40.)(15.(11.&40.)Lt5,(11.&40.)(15.(11.&40.)Lt6,(11.&40.)(15.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(1.(5.$1;.R10.(1<.(1=.O18.O17.O16.O15.R?.R>.R=.O14.O13.(8.&40.O6.)R<.R;.R:.R9.R8.R7.R6.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R5.R4.R3.R2.)O8.(1>.O18.)O7.(1?.(11.&40.))R1.(20.$21.)))(1.(22.(17.(23.$0.$0.)(24.$0.$0.O6.(9.O6.O4.))(17.(23.$0.$0.)(24.$0.$0.O3.(25.&40.O17.))(18.(23.$0.$0.))))O1.R1.)(1.(26.$21.O1.R1.)(1.(27.$21.R1.)(1.(28.$21.R1.O6.O2.)(1.(16.$21.R1.O5.O2.)(2;.$21.R1.O3.(25.&40.O17.)))))))))))))))))))))))")
(* [comment removed for export] *).

End Walk.
