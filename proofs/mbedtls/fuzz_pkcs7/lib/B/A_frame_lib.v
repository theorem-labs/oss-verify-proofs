(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_frame_lib () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.zcells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.sinv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"].


Definition hidden (P : Prop) : Prop := P.

Lemma zcells_app : forall a b, zcells (a + b) = zcells a ++ zcells b.
Proof. induction a as [|a IH]; intros b; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section WithR.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).

  (* [comment removed for export] *)
  #[using="Type"] Lemma presW_munch_sh : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)PSP,$4.PSSP,$4.PW,(2.$5.)Pm0,P,(6.&40.)(7.(6.&8.))Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pc,$4.Pn,$4.Plo',$4.Phi',$4.P,(8.$1.VR,VHIA,R=.R<.R;.R:.R9.R8.R7.R6.)P,(9.(:.(;.$4.$4.)(<.$4.$4.(=.(>.VR,)R5.)(?.(=.(>.VR,)R5.)R4.))(:.(;.$4.$4.)(<.$4.$4.R3.R2.)(10.(;.$4.$4.))))R7.R6.)P,(11.$1.R8.R7.)P,(12.(13.$1.VR,VHIA,R10.)R7.(14.+8.R6.))P,(15.VR,R10.R?.R=.(16.$1.VR,VHIA,R11.)R8.(14.+8.R7.))P,(17.(18.VR,)R7.)P,(17.R7.R10.)P,(17.(19.(1:.VR,))R11.)P,(1;.$4.(1<.R<.+8.)=)(8.$1.VR,VHIA,R16.R15.R14.R13.R12.R11.R10.R>.)")
(* [comment removed for export] *).
  Proof.
    (intros h LB LF SP SSP W m0 m m' c n lo' hi' dd_H; ddestruct dd_H as (P & C1 & C2 & C3); intros MU WM HC HF HLO HHI HSP Hc8).
    split; [| split; [exact C1| split; [exact C2| exact C3]]].
    eapply presA_trans; [exact P|].
    pose proof (hcs_ok asegs R HIA h) as OK. pose proof (art_lo asegs R HIA) as ALO. pose proof (art_data_lo asegs R HIA) as DLO.
    assert (NCS : forall x, shadow_of AL c <= x < shadow_of AL c + n -> ~ hcs asegs R HIA h x).
    { intros x Hx. eapply shadow_run_not_cs; [exact OK| exact HC| exact Hx]. }
    assert (BND : forall x, shadow_of AL c <= x < shadow_of AL c + n -> x < alloc_ceiling).
    { intros x Hx. replace x with (shadow_of AL (c + 8 * (x - shadow_of AL c))) by (rewrite shadow_of_plus; lia).
      apply (proj2 (hcs_shadow_band asegs R HIA h _ (HC (c + 8 * (x - shadow_of AL c)) ltac:(lia)))). }
    split.
    - intros a Ha Hcl Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| split; [| exact I]].
      + intros Hin.
        destruct Hcl as [Hs|[[Hd1 Hd2]|([B j] & Hb & Hr)]].
        * pose proof (BND a Hin). lia.
        * apply (NCS a Hin). apply (hcs_static asegs R HIA h). split; [cbn in *; lia| exact Hd2].
        * apply (NCS a Hin). cbn in Hr. replace a with (B + (a - B)) by lia. apply (C2 B j Hb). lia.
      + intros Hin. destruct Hcl as [Hs|[[Hd1 Hd2]|([B j] & Hb & Hr)]]; [lia| cbn in *; lia|].
        cbn in Hr. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        * pose proof (C3 B j ltac:(apply in_app_iff; left; exact Hb)). lia.
        * ddestruct (in_fdata_hull LF (B, j) a Hb Hr) as ([B' j'] & Hb' & Hr'). cbn in Hr'.
          pose proof (C3 B' j' ltac:(apply in_app_iff; right; exact Hb')). lia.
    - intros c' Hc' Hr. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| split; [| exact I]].
      + intros Hin. apply (HF c' Hc'). unfold shadow_of in *.
        pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.div_mod c' 8 ltac:(lia)). pose proof (Z.mod_pos_bound c' 8 ltac:(lia)). nia.
      + intros Hin. pose proof (hcs_shadow_band asegs R HIA h c' (C1 c' Hc')). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sshad_munch_sh : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "Ph,(0.$1.VR,VHIA,)Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pc,$4.Pn,$4.Plo',$4.Phi',$4.Pslo,$4.Pshi,$4.P,(1=.$1.(>.VR,)R8.R2.R1.)P,(9.(:.(;.$4.$4.)(<.$4.$4.(=.(>.VR,)R7.)(?.(=.(>.VR,)R7.)R6.))(:.(;.$4.$4.)(<.$4.$4.R5.R4.)(10.(;.$4.$4.))))R9.R8.)P,(11.$1.R:.R9.)P,(12.(13.$1.VR,VHIA,R<.)R5.(1>.R4.R5.))P,(1;.$4.(1<.R:.+8.)=)P,(1?.(17.(?.R;.(14.+8.R:.))R7.)(17.R6.R;.))P,(17.(18.VR,)R:.)(1=.$1.(>.VR,)R>.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    (intros h m m' c n lo' hi' slo shi dd_H; ddestruct dd_H as (S0 & S1 & SS); intros MU WM HC Hc8 HAP HLO). split; [exact S0|]. split; [exact S1|].
    intros g G1 G2 G3. pose proof (SS g G1 G2 G3) as H.
    pose proof (art_lo asegs R HIA) as ALO.
    eapply rw_cells_transport; [exact H| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from].
    pose proof (hcs_shadow_band asegs R HIA h g (HC g ltac:(lia))) as [_ B].
    split; [| split; [lia| exact I]].
    unfold shadow_of in *. pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.div_mod g 8 ltac:(lia)). nia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_presA : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "PLB,(2.$3.)PLF,(2.$3.)PSP,$4.PSSP,$4.PTOP,$4.PW,(2.$5.)Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pv,$4.PF,$4.Pd,$4.P,(20.$1.VR,R;.R:.R9.R8.R7.R6.R5.R4.)P,(21.$1.R6.(18.VR,)R8.R4.R3.R2.)P,(17.R;.R4.)P,Pa,$4.P,(22.(17.R6.R1.)(23.R1.R;.))(24.R;.R2.)P,(17.=R6.)P,(17.R<.(25.+2.+40.))(21.$1.R:.(18.VR,)R=.R9.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB LF SP SSP TOP W m m' v F d [P _] UW HSP HW HF HT.
    eapply uwc_transport; [exact UW|]. intros a Ha. apply (proj1 (P a ltac:(lia) ltac:(left; lia) (HW a Ha))).
  Qed.
End WithR.

Lemma cells_bytes_zcells : forall n, cells_bytes (zcells n) = repeat (Z_to_bv 8 0) n.
Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma zcells_CB : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "Psegs,(2.$26.)Pm,P,(6.&40.)(7.(6.&8.))PA,$4.Pn,$27.P,(28.#0.R1.)P,(29.R5.R4.R3.(2:.R2.))(29.R6.R5.R4.(:.$2;.(2<.R3.(2=.(6.&8.)(2>.&8.=)R3.))(10.$2;.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A n Hn H. eapply rw_cells_reshape; [exact H| |].
  - cbn. rewrite repeat_length. repeat split; try reflexivity; try lia.
  - cbn. rewrite app_nil_r, cells_bytes_zcells. reflexivity.
Qed.

Lemma cell_at_zcells : forall n i, (i < n)%nat -> cell_at (zcells n) i = Some (C1 (Z_to_bv 8 0)).
Proof.
  induction n as [|n IH]; intros i Hi; [lia|]. cbn [zcells cell_at csize].
  destruct i as [|i]; cbn [Nat.eqb Nat.ltb Nat.leb Nat.sub]; [reflexivity|]. apply IH. lia.
Qed.

Lemma CB_zcells : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "Psegs,(2.$26.)Pm,P,(6.&40.)(7.(6.&8.))PA,$4.Pn,$27.P,(29.R4.R3.R2.(:.$2;.(2<.R1.(2=.(6.&8.)(2>.&8.=)R1.))(10.$2;.)))(29.R5.R4.R3.(2:.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs m A n H. eapply rw_cells_reshape; [exact H| |].
  - clear H. induction n as [|k IH]; cbn; [exact I|]. split; [exact I| exact IH].
  - cbn. rewrite app_nil_r, cells_bytes_zcells. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma aobj_of_zshadow : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "Psegs,(2.$26.)PAL,$2?.PCS,P,$4.SpPm,P,(6.&40.)(7.(6.&8.))PB,$4.Pn,$27.P,(30.R5.R4.)P,(29.R7.R4.(?.(31.R3.+3.)(32.R6.))(:.$2;.(2<.R2.(2=.(6.&8.)(2>.&8.=)R2.))(10.$2;.)))P,(12.R6.R4.(14.+8.(33.R3.)))P,(1;.$4.(1<.R5.+8.)=)P,(17.=R6.)(34.R;.R:.R9.R8.R7.(14.+8.(33.R6.)))")
(* [comment removed for export] *).
Proof.
  intros segs AL CS m B n OK H HC HB H0.
  eapply (aobj_of_zero_shadow_sh segs AL CS m B (zcells n) B 0 n OK); [apply CB_zcells; exact H| exact HC| exact HB| exact H0| lia|].
  intros i Hi. apply cell_at_zcells. exact Hi.
Qed.

Lemma rw_cells_CB_of : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "Psegs,(2.$26.)Pm,P,(6.&40.)(7.(6.&8.))PA,$4.Pcs,(2.$2;.)P,(28.#0.(35.R1.))P,(29.R5.R4.R3.R2.)(29.R6.R5.R4.(:.$2;.(2<.(35.R3.)(36.R3.))(10.$2;.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A cs Hn H. eapply rw_cells_reshape; [exact H| |].
  - cbn. split; [| exact I]. apply cells_bytes_length. destruct H as [[W _] _]. exact W.
  - cbn. rewrite app_nil_r. reflexivity.
Qed.

Section WithR2.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Local Notation L := (arl_L R).

  (* [comment removed for export] *)
  #[using="Type"] Lemma presA_drop_fresh_gen : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "PLB,(2.$3.)PLF,(2.$3.)PSP,$4.PSSP,$4.PTOP,$4.PW,(2.(;.$4.$4.))PN,$4.Pk,$4.Pa,$4.Pb,$4.Pm1,P,(6.&40.)(7.(6.&8.))Pm2,P,(6.&40.)(7.(6.&8.))P,(20.$1.VR,R<.R;.R:.R9.R8.(:.(;.$4.$4.)(<.$4.$4.R4.R3.)R7.)R2.R1.)P,(37.VR,R=.R<.R7.R6.)P,(17.R8.R6.)P,(17.R6.(?.R9.R8.))P,(17.(19.(1:.VR,))R>.)(20.$1.VR,R11.R10.R?.R>.R=.R<.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    (intros LB LF SP SSP TOP W N k a b m1 m2 [P S] dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros Ha Hb HS). split; [| exact S].
    intros x Hx Hc Ho. apply P; [exact Hx| exact Hc|]. cbn [outside]. split; [| exact Ho].
    intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
    - clear - Hs Hin F1 HS Ha Hb. lia.
    - clear - Hd1 Hd2 Hin F2 Ha Hb. cbn in *. lia.
    - destruct bk as [B j]. cbn in Hr. pose proof (F3 B j Hbk). clear - Hr Hin H Ha Hb. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma client_range_raise : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "PLB,(2.$3.)Plo,$4.PSP,$4.PA,$4.Pn,$4.P,(38.(1:.VR,)R5.R4.R2.R1.)P,(1?.(17.(?.R3.R2.)R5.)(17.R4.R3.))(38.(1:.VR,)R7.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB lo SP A n H HD a Ha. destruct (H a Ha) as [X|[X|X]]; [| right; left; exact X| right; right; exact X].
    destruct HD; [exfalso; lia| left; lia].
  Qed.
End WithR2.

Lemma client_range_incl : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "PL,$39.PLB,(2.$3.)PLB',(2.$3.)PSP,$4.PA,$4.Pn,$4.P,(38.R6.R5.R3.R2.R1.)P,Pb,$3.P,(3:.$3.R1.R7.)(3:.$3.R2.R7.)(38.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L LB LB' SP A n H HI a Ha. destruct (H a Ha) as [X|[X|(b & Hb & Hr)]]; [left; exact X| right; left; exact X|].
  right; right. exists b. split; [apply HI, Hb| exact Hr].
Qed.

Lemma si_outside_above : forall (L : heap_layout) (SI : sinv L) a, hl_data_hi L <= a -> outside (si_fp SI) a.
Proof.
  intros L SI a Ha. destruct (outside_dec (si_fp SI) a) as [H|H]; [exact H|]. exfalso.
  pose proof (si_below L SI a H). lia.
Qed.
Lemma si_disjoint_off : ltac2:(CDefT.buildp (gd_tbl_A_frame_lib ()) "PL,$39.PSI,(3;.R1.)PA,$4.Pn,$4.P,(1?.(17.(?.R2.R1.)(3<.R4.))(17.(3=.R4.)R2.))(3>.(3?.R5.R4.)R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros L SI A n H. apply si_fp_disjoint_gen. intros u v Hin. destruct (si_win L SI u v Hin). lia.
Qed.

(* [comment removed for export] *)
Ltac shadow_client_of E ::=
  lazymatch E with
  | Z.add (Z.add (Z.add (Z.shiftr ?c 3) _) ?k1) ?k2 => constr:(Z.add c (Z.mul 8 (Z.add k1 k2)))
  | Z.add (Z.add (Z.add _ (Z.shiftr ?c 3)) ?k1) ?k2 => constr:(Z.add c (Z.mul 8 (Z.add k1 k2)))
  | Z.add (Z.add (Z.shiftr ?c 3) _) ?k => constr:(Z.add c (Z.mul 8 k))
  | Z.add (Z.add _ (Z.shiftr ?c 3)) ?k => constr:(Z.add c (Z.mul 8 k))
  | Z.add (Z.shiftr ?c 3) _ => c
  | Z.add _ (Z.shiftr ?c 3) => c
  | Z.add (shadow_of _ ?c) ?k => constr:(Z.add c (Z.mul 8 k))
  | shadow_of _ ?c => c
  end.

(* [comment removed for export] *)
Ltac apart_ss A2 n2 a len ::=
  let c1 := shadow_client_of a in let c2 := shadow_client_of A2 in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_shadow_shadow L c2 n2 c1 len A2 a); [ qlia | qlia | pqlia | shadow_addr_eq | shadow_addr_eq ]
  end.

