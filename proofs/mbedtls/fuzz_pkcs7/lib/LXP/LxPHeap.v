(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Export LxPTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxPHeap () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_opq"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_no_layout"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"].


Section HeapOpq.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.

  (* [comment removed for export] *)
  Lemma lxp_opq_HEAP : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "Ph,(0.Vsegs,VL,VHI,)PLB,(1.$2.)Pm,P,(3.&40.)(4.(3.&8.))Pmo,$5.Plo,$6.POKS,(1.$7.)P,(8.Vsegs,VL,VHI,R6.R5.R4.R3.)P,(9.(:.VL,)R3.)P,(;.(<.$6.$6.)Liv,(<.$6.$6.)(=.VL,R8.R5.(>.Vsegs,VL,VHI,R9.)(?.$6.$6.R1.)(10.(11.$6.$6.R1.)(?.$6.$6.R1.)))R3.)(12.Vsegs,$13.L,$6.$14.Lm,P,(3.&40.)(4.(3.&8.))(8.Vsegs,VL,VHI,R:.R9.R1.R7.)(15.(<.$6.$6.)(16.$6.$6.R5.(>.Vsegs,VL,VHI,R9.))R4.)(17.$7.)R7.)")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo lo OKS HH ACL HOK.
    apply (lx_opq_intro segs lx_no_layout (fun _ => True) (fun m => HEAP segs L HI h LB m mo)
             (client_waddr L LB lo (heap_top segs L HI h))); [exact HH| | | intros lo' hi' c [] ].
    - intros W m1 m2 H1 MU WM HW.
      eapply (heap_frame segs L HI); [exact H1| exact ACL| | exact WM].
      intros a Ha Hnc. destruct (outside_dec W a) as [Ho|Ho].
      + apply MU. rewrite wa_unsigned by lia. exact Ho.
      + exfalso. apply Hnc. clear -HW Ho.
        induction HW as [|iv W' Hiv HW' IH]; [exact (False_ind _ (Ho I))|].
        cbn [outside] in Ho. destruct iv as [u v]; cbn [fst snd] in *.
        destruct (Z_lt_dec a u) as [X|X]; [| destruct (Z_le_dec v a) as [Y|Y]]; [apply IH; intros Ho'; apply Ho; split; [lia| exact Ho'] .. | ].
        apply Hiv. lia.
    - intros lo' hi' a [E|Hin] Ha.
      + injection E as <- <-. left. exact Ha.
      + rewrite Forall_forall in HOK. pose proof (HOK _ Hin) as K. cbn [fst snd] in K. apply K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lxp_cw_mono : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "PLB,(1.$2.)PLB',(1.$2.)PSP,$6.PTOP,$6.PTOP',$6.PA,$6.Pn,$6.P,(=.VL,R7.R5.R4.R2.R1.)P,Pb,$2.P,(18.$2.R1.R9.)(18.$2.R2.R9.)P,(9.R6.R5.)(=.VL,R9.R8.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros LB LB' SP TOP TOP' A n H HS HT a Ha. destruct (H a Ha) as [X|[X|(b & Hb & Hr)]]; [left; lia| right; left; exact X|].
    right; right. exists b. split; [exact (HS b Hb)| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma lxp_opq_presx : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "PLB,(1.$2.)PSP,$6.PX,(1.$7.)Pm0,P,(3.&40.)(4.(3.&8.))Pm,P,(3.&40.)(4.(3.&8.))Plo,$6.P,(19.Vsegs,VL,R6.R5.R4.R3.R2.)P,(9.(:.VL,)R2.)P,(9.(1:.VL,)(:.VL,))P,(;.(<.$6.$6.)Lb,(<.$6.$6.)(1;.VL,(?.$6.$6.R1.)(11.$6.$6.R1.))R9.)(12.Vsegs,$13.L,$6.$14.Lm,P,(3.&40.)(4.(3.&8.))(19.Vsegs,VL,R;.R:.R9.R8.R1.)(1<.$7.R8.(15.(<.$6.$6.)(16.$6.$6.R5.R9.)(17.(<.$6.$6.))))(17.$7.)R6.)")
(* [comment removed for export] *).
  Proof.
    intros LB SP X m0 m lo HP ACL DHI HBR.
    apply (lx_opq_intro segs lx_no_layout (fun _ => True) (fun m => heap_presx segs L LB SP X m0 m)
             (fun a => ~ outside X a \/ ~ client_addr L LB SP a)); [exact HP| | | intros lo' hi' c [] ].
    - intros W m1 m2 H1 MU WM HW. eapply heap_presx_trans; [exact H1|].
      eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. destruct (outside_dec W a) as [O|O]; [exact O| exfalso].
      clear -HW O Hc Ho.
      induction HW as [|iv W' Hiv HW' IH]; [exact (O I)|].
      destruct iv as [u v]; cbn [outside fst snd] in *.
      destruct (Z_lt_dec a u) as [X1|X1]; [| destruct (Z_le_dec v a) as [Y|Y]]; [apply IH; intros O'; apply O; split; [lia| exact O'] .. | ].
      destruct (Hiv a ltac:(lia)) as [K|K]; [exact (K Ho)| exact (K Hc)].
    - intros lo' hi' a Hin Ha. apply in_app_or in Hin. destruct Hin as [Hin|[E|[]]].
      + left. clear -Hin Ha. intros Ho. induction X as [|[u v] X' IH]; [destruct Hin|].
        cbn [outside] in Ho. destruct Ho as [Ho1 Ho2]. destruct Hin as [E|Hin]; [injection E as -> ->; cbn in Ho1; lia| exact (IH Hin Ho2)].
      + injection E as <- <-. right. intros [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        rewrite Forall_forall in HBR. destruct (HBR b Hb) as (_ & _ & _ & Bc & _). destruct b as [B k]; cbn in Hr, Bc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lxp_fresh_not_client : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "PLB,(1.(<.$6.$6.))PSP,$6.PN,$6.Pn,$6.Pa,$6.P,(1;.VL,R3.R2.)P,PB,$6.Pk,$6.P,(18.(<.$6.$6.)(16.$6.$6.R2.R1.)R8.)(1=.(9.(1>.R7.R6.)R3.)(9.(1>.R3.R2.)R7.))P,(9.(1?.VL,)(20.VL,))P,(9.(1:.VL,)(21.VL,))P,(9.(:.VL,)R8.)P,(22.(9.R8.R6.)(23.R6.(1>.R8.R7.)))(24.(25.VL,R;.R:.R7.))")
(* [comment removed for export] *).
  Proof.
    intros LB SP N n a (HN1 & HN2 & HN3 & HN4 & HN5) HAP D1 D2 HSP Ha [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
    destruct b as [B k]. cbn in Hr. pose proof (HAP B k Hb). lia.
  Qed.
  Lemma lxp_opq_presx2 : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "PLB,(1.$2.)PSP,$6.PX,(1.$7.)Pm0,P,(3.&40.)(4.(3.&8.))Pm,P,(3.&40.)(4.(3.&8.))Plo,$6.PFB,(1.$7.)P,(19.Vsegs,VL,R7.R6.R5.R4.R3.)P,(9.(:.VL,)R3.)P,(9.(1:.VL,)(:.VL,))P,(;.(<.$6.$6.)Lb,(<.$6.$6.)(1;.VL,(?.$6.$6.R1.)(11.$6.$6.R1.))R:.)P,(;.(<.$6.$6.)Liv,(<.$6.$6.)Pa,$6.P,(22.(9.(?.$6.$6.R2.)R1.)(23.R1.(11.$6.$6.R2.)))(24.(25.VL,R>.R=.R2.))R5.)(12.Vsegs,$13.L,$6.$14.Lm,P,(3.&40.)(4.(3.&8.))(19.Vsegs,VL,R=.R<.R;.R:.R1.)(1<.$7.R:.(1<.$7.R6.(15.(<.$6.$6.)(16.$6.$6.R7.R;.)(17.(<.$6.$6.)))))(17.$7.)R8.)")
(* [comment removed for export] *).
  Proof.
    intros LB SP X m0 m lo FB HP ACL DHI HBR HFB.
    apply (lx_opq_intro segs lx_no_layout (fun _ => True) (fun m => heap_presx segs L LB SP X m0 m)
             (fun a => ~ outside X a \/ ~ client_addr L LB SP a)); [exact HP| | | intros lo' hi' c [] ].
    - intros W m1 m2 H1 MU WM HW. eapply heap_presx_trans; [exact H1|].
      eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. destruct (outside_dec W a) as [O|O]; [exact O| exfalso].
      clear -HW O Hc Ho.
      induction HW as [|iv W' Hiv HW' IH]; [exact (O I)|].
      destruct iv as [u v]; cbn [outside fst snd] in *.
      destruct (Z_lt_dec a u) as [X1|X1]; [| destruct (Z_le_dec v a) as [Y|Y]]; [apply IH; intros O'; apply O; split; [lia| exact O'] .. | ].
      destruct (Hiv a ltac:(lia)) as [K|K]; [exact (K Ho)| exact (K Hc)].
    - intros lo' hi' a Hin Ha. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| apply in_app_or in Hin; destruct Hin as [Hin|[E|[]]]].
      + left. clear -Hin Ha. intros Ho. induction X as [|[u v] X' IH]; [destruct Hin|].
        cbn [outside] in Ho. destruct Ho as [Ho1 Ho2]. destruct Hin as [E|Hin]; [injection E as -> ->; cbn in Ho1; lia| exact (IH Hin Ho2)].
      + right. rewrite Forall_forall in HFB. exact (HFB _ Hin a Ha).
      + injection E as <- <-. right. intros [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        rewrite Forall_forall in HBR. destruct (HBR b Hb) as (_ & _ & _ & Bc & _). destruct b as [B k]; cbn in Hr, Bc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lxp_presx_compose : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "PLB,(1.$2.)PLB1,(1.$2.)PLB2,(1.$2.)PSP,$6.PSP',$6.PX,(1.$7.)PX',(1.$7.)Pm0,P,(3.&40.)(4.(3.&8.))Pm1,P,(3.&40.)(4.(3.&8.))Pm2,P,(3.&40.)(4.(3.&8.))P,(19.Vsegs,VL,R9.R7.R5.R3.R2.)P,(19.Vsegs,VL,R9.R7.R5.R3.R2.)P,(9.R8.R9.)P,Pb,$2.P,(18.$2.R1.R>.)(18.$2.R2.R>.)P,Pb,$2.P,(18.$2.R1.R?.)(18.$2.R2.R>.)P,Pa,$6.P,(26.R;.R1.)(26.R;.R2.)(19.Vsegs,VL,R10.R=.R;.R9.R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB LB1 LB2 SP SP' X X' m0 m1 m2 H1 H2 HS HL1 HL2 HX a Ha Hc Ho.
    assert (Hc1 : client_addr L LB1 SP a).
    { destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right; exists b; split; [exact (HL1 _ Hb)| exact Hr]]. }
    assert (Hc2 : client_addr L LB2 SP' a).
    { destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right; exists b; split; [exact (HL2 _ Hb)| exact Hr]]. }
    destruct (H1 a Ha Hc1 Ho) as [E1 W1]. destruct (H2 a Ha Hc2 (HX a Ho)) as [E2 W2]. split; [congruence| auto].
  Qed.

  (* [comment removed for export] *)
  Lemma lxp_presx_nil : forall LB SP m0 m, heap_pres segs L LB SP m0 m <-> heap_presx segs L LB SP [] m0 m.
  Proof. intros LB SP m0 m. split; [intros H a Ha Hc _; exact (H a Ha Hc)| intros H a Ha Hc; exact (H a Ha Hc I)]. Qed.
  Lemma lxp_pres_to_x : forall LB SP m0 m, heap_pres segs L LB SP m0 m -> heap_presx segs L LB SP [] m0 m.
  Proof. intros. apply lxp_presx_nil. assumption. Qed.
  Lemma lxp_presx_to_pres : forall LB SP X m0 m, heap_presx segs L LB SP X m0 m -> X = [] -> heap_pres segs L LB SP m0 m.
  Proof. intros LB SP X m0 m H ->. apply lxp_presx_nil. exact H. Qed.
  Lemma lxp_x_to_pres : forall LB SP m0 m, heap_presx segs L LB SP [] m0 m -> heap_pres segs L LB SP m0 m.
  Proof. intros LB SP m0 m H. apply lxp_presx_nil. exact H. Qed.
  Lemma lxp_presx_ro_cells : ltac2:(CDefT.buildp (gd_tbl_LxPHeap ()) "PLB,(1.$2.)PSP,$6.PX,(1.$7.)Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))PA,$6.Pcs,(1.$27.)P,(19.Vsegs,VL,R7.R6.R5.R4.R3.)P,(28.Vsegs,R5.R3.R2.)P,(29.VL,R9.R8.R4.(2:.(2;.R3.)))P,(2<.R8.R5.(2:.(2;.R4.)))(28.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros LB SP X m m' A cs HP [Hwf HB] HR HD. split; [exact Hwf|].
    eapply heap_presx_bytes_at; [exact HP| exact HB| rewrite cells_bytes_length by assumption; exact HR| rewrite cells_bytes_length by assumption; exact HD].
  Qed.
End HeapOpq.

Lemma lxp_opq_holds' : forall segs AL CS (P : mem -> Prop) OK SH m, lx_opq segs AL CS P OK SH m -> P m.
Proof. intros. eapply lx_opq_holds. eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lxp_true_or_lia := first [ exact I | solve [ trivial ] | lia | tauto ].
Ltac lxp_outside_incl := intros a_; cbn [outside fst snd]; clear; intros; lxp_true_or_lia.
Ltac lxp_lb_incl :=
  first [ assumption                                         (* [comment removed for export] *)
        | exact (fun b Hb => Hb)
        | intros b_ Hb_;
          (* [comment removed for export] *)
          try match goal with E : ?X = _ |- In _ ?X' => is_var X; constr_eq X X'; rewrite E end;
          try match goal with E : ?X = _ |- _ => is_var X; lazymatch type of Hb_ with In _ ?Y => constr_eq X Y; rewrite E in Hb_ end end;
          first [ exact Hb_
                | apply in_or_app; right; exact Hb_                       (* [comment removed for export] *)
                | match goal with H : forall b, In b _ -> In b _ |- _ => exact (H _ Hb_) end
                | eapply lb_remove_sub; exact Hb_                           (* [comment removed for export] *)
                | eapply In_lb_remove_all; exact Hb_
                | match goal with H : forall b, In b _ -> In b _ |- _ => apply in_or_app; right; exact (H _ Hb_) end
                | lazymatch goal with |- In _ ?T => let h := head_of T in unfold h end;
                  first [ apply in_or_app; right; exact Hb_ | apply in_or_app; left; exact Hb_ ]
                | timeout 3 (revert Hb_; generalize b_; clear; cbn [In app map rev]; intros; tauto) ] ].   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)

(* [comment removed for export] *)
Ltac lxp_cw_list L LB lo top :=
  let rec go acc :=
    match goal with
    | H : client_wrange L _ lo _ ?A ?n |- _ =>
        lazymatch acc with
        | context [(A, A + n)] => fail
        | _ => go constr:((A, A + n) :: acc)
        end
    (* [comment removed for export] *)
    | H : In (?A, ?n) LB |- _ =>
        lazymatch acc with
        | context [(A, A + n)] => fail
        | _ => go constr:((A, A + n) :: acc)
        end
    | _ => acc
    end in
  go constr:(@nil ivl).

(* [comment removed for export] *)
Ltac lxp_fresh_list LB :=
  let rec go acc :=
    match goal with
    | H : forall B k, In (B, k) LB -> ?A + ?n <= B \/ B + k <= ?A |- _ =>
        lazymatch acc with context [(A, A + n)] => fail | _ => go constr:(@cons ivl (A, A + n) acc) end
    | _ => acc
    end in
  go constr:(@nil ivl).
Ltac lxp_fresh_obligations :=
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with
  | HAP : forall B k, In (B, k) ?LB -> ?A + ?n <= B \/ B + k <= ?A |- forall a, ?A <= a < _ -> ~ client_addr _ ?LB _ a =>
      intros a_ Ha_; eapply (@lxp_fresh_not_client _ LB _ A n a_);
      [ first [ eassumption
              | (* [comment removed for export] *)
                unfold block_range; repeat match goal with |- _ /\ _ => split end; first [ assumption | lxp_lia_fast ] ]
      | exact HAP | assumption | assumption | lxp_lia_fast | exact Ha_ ]
  end.
Ltac lxp_box_presx_term segs L LB SP X m0 mx HPterm :=
  lazymatch goal with
  | ACL : alloc_ceiling <= ?lo, DHI : hl_data_hi L <= alloc_ceiling |- _ =>
      let K := fresh "HPXo" in
      let FB := lxp_fresh_list LB in
      first [ lazymatch FB with nil => fail | _ => idtac end;
              first [ match goal with HBR : Forall (fun b => block_range L (fst b) (snd b)) LB |- _ =>
                        unshelve epose proof (lxp_opq_presx2 segs L LB SP X m0 mx lo FB HPterm ACL DHI HBR _) as K end
                    | match goal with HH : HEAP segs L ?HI ?h LB ?mm ?mo |- _ =>
                        unshelve epose proof (lxp_opq_presx2 segs L LB SP X m0 mx lo FB HPterm ACL DHI (proj1 (heap_blocks segs L HI h LB mm mo HH)) _) as K end ];
              [ lxp_fresh_obligations | ]
            | first [ match goal with HBR : Forall (fun b => block_range L (fst b) (snd b)) LB |- _ =>
                        pose proof (lxp_opq_presx segs L LB SP X m0 mx lo HPterm ACL DHI HBR) as K end
                    | match goal with HH : HEAP segs L ?HI ?h LB ?mm ?mo |- _ =>
                        pose proof (lxp_opq_presx segs L LB SP X m0 mx lo HPterm ACL DHI (proj1 (heap_blocks segs L HI h LB mm mo HH))) as K end ] ];
      cbn [fst snd app] in K
  end.
Ltac lxp_heap_box_at mx :=
  (* [comment removed for export] *)
  repeat match goal with
  | HH : HEAP ?segs ?L ?HI ?h ?LB mx ?mo |- _ =>
      first [ is_var LB; fail 1
            | let X := fresh "LXLB" in let E := fresh "ELXLB" in remember LB as X eqn:E in * ]
  end;
  (* [comment removed for export] *)
  repeat match goal with
  | HH : HEAP ?segs ?L ?HI ?h ?LB mx ?mo |- _ =>
      lazymatch goal with
      | _ : lx_opq _ _ _ (fun m => HEAP segs L HI h LB m mo) _ _ mx |- _ => fail
      | ACL : alloc_ceiling <= ?lo |- _ =>
          let oks := lxp_cw_list L LB lo constr:(heap_top segs L HI h) in
          let K := fresh "HHo" in
          unshelve epose proof (lxp_opq_HEAP segs L HI h LB mx mo lo oks HH ACL _) as K;
          [ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
            match goal with H : client_wrange _ _ _ _ ?A ?n |- client_wrange _ _ _ _ ?A ?k =>
              replace k with n by (clear; lia);
              first [ exact H
                    | apply (@lxp_cw_mono L _ _ _ _ _ A n H); [ lxp_lb_incl | first [ apply Z.le_refl | lxp_lia_fast ] ]
                    | idtac "lxp: client_wrange obligation at" A "not provable from" H ": HEAP box NOT posed"; fail ]
            | HB : In (?A, ?n) _ |- client_wrange _ _ _ _ ?A ?k =>
              replace k with n by (clear; lia);
              first [ eapply client_wrange_block; [ exact HB | clear; lia | clear; lia ]
                    | idtac "lxp: client_wrange obligation for block" A "not provable from" HB ": HEAP box NOT posed"; fail ] end
          | cbn [fst snd app] in K ]
      end
  end;
  (* [comment removed for export] *)
  repeat match goal with
  | HP : heap_presx ?segs ?L ?LB ?SP ?X ?m0 mx |- _ =>
      lazymatch goal with
      | _ : lx_opq _ _ _ (fun m => heap_presx segs L LB SP X m0 m) _ _ mx |- _ => fail
      | _ => lxp_box_presx_term segs L LB SP X m0 mx HP
      end
  | HP : heap_pres ?segs ?L ?LB ?SP ?m0 mx |- _ =>
      lazymatch goal with
      | _ : lx_opq _ _ _ (fun m => heap_presx segs L LB SP [] m0 m) _ _ mx |- _ => fail
      | _ => lxp_box_presx_term segs L LB SP constr:(@nil ivl) m0 mx constr:(lxp_pres_to_x segs L LB SP m0 mx HP)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_in_nth k := lazymatch k with O => left; reflexivity | S ?k' => right; lxp_in_nth k' end.
(* [comment removed for export] *)
Ltac lxp_base_of e := lazymatch e with ?u + ?c => lxp_base_of u | ?u - ?c => lxp_base_of u | _ => e end.
Ltac lxp_same_base x y := let bx := lxp_base_of x in let by_ := lxp_base_of y in constr_eq bx by_.
Ltac lxp_in_ok_go OK a b k :=
  lazymatch OK with
  | (?u, ?v) :: ?rest =>
      first [ first [ lxp_same_base a u | lxp_same_base b v | lxp_same_base a v | lxp_same_base b u ];
              exists u, v; split; [ lxp_in_nth k | cbn [fst snd]; first [ clear; lia | lxp_lia_fast ] ]
            | lxp_in_ok_go rest a b constr:(S k) ]
  end.
Ltac lxp_in_ok OK a b := lxp_in_ok_go OK a b constr:(O).
Ltac lxp_allowed_tac :=
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- opq_allowed _ _ ?OK _ (?a, ?b) => left; cbn [fst snd]; lxp_in_ok OK a b end.
Ltac lxp_opq_advance mx :=
  repeat match goal with
  | K : lx_opq ?segs ?AL ?CS ?P ?OK ?SH ?m1, MU : munch ?W ?m1 mx, WM : wmono ?segs ?m1 mx |- _ =>
      tryif constr_eq m1 mx then fail else
      (let K2 := fresh K in
       unshelve epose proof (lx_opq_transport segs AL CS P OK SH m1 mx W K MU WM _) as K2;
       [ lxp_allowed_tac | clear K ])
  end.

Ltac lxp_goal_mem :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mx _) => mx
  | |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => mx
  end.

Ltac lxp_heap_box :=
  let mx := lxp_goal_mem in
  (* [comment removed for export] *)
  lxp_heap_box_at mx;
  repeat match goal with
  | H : heap_presx _ _ _ _ _ _ ?m1, MU : munch _ ?m1 mx |- _ =>
      tryif constr_eq m1 mx then fail else
      (lazymatch goal with
       | _ : lx_opq _ _ _ _ _ _ m1 |- _ => fail
       | _ => lxp_heap_box_at m1 end)
  | H : heap_pres _ _ _ _ _ ?m1, MU : munch _ ?m1 mx |- _ =>
      tryif constr_eq m1 mx then fail else
      (lazymatch goal with
       | _ : lx_opq _ _ _ _ _ _ m1 |- _ => fail
       | _ => lxp_heap_box_at m1 end)
  | H : HEAP _ _ _ _ _ ?m1 _, MU : munch _ ?m1 mx |- _ =>
      tryif constr_eq m1 mx then fail else
      (lazymatch goal with
       | _ : lx_opq _ _ _ _ _ _ m1 |- _ => fail
       | _ => lxp_heap_box_at m1 end)
  end;
  lxp_opq_advance mx.

(* [comment removed for export] *)
Ltac lxp_heap_unbox :=
  let mx := lxp_goal_mem in
  repeat match goal with
  | K : lx_opq _ _ _ (fun m => HEAP ?segs ?L ?HI ?h ?LB m ?mo) _ _ mx |- _ =>
      lazymatch goal with
      | _ : HEAP segs L HI h LB mx mo |- _ => fail
      | _ => let H := fresh "HH" in pose proof (lxp_opq_holds' _ _ _ _ _ _ _ K) as H; cbv beta in H
      end
  | K : lx_opq _ _ _ (fun m => heap_presx ?segs ?L ?LB ?SP ?X ?m0 m) _ _ mx |- _ =>
      lazymatch goal with
      | _ : heap_presx segs L LB SP X m0 mx |- _ => fail
      | _ => let H := fresh "HPX" in pose proof (lxp_opq_holds' _ _ _ _ _ _ _ K) as H; cbv beta in H;
             (* [comment removed for export] *)
             try lazymatch X with
                 | nil => lazymatch goal with
                          | _ : heap_pres segs L LB SP m0 mx |- _ => idtac
                          | _ => let H2 := fresh "HP" in pose proof (lxp_x_to_pres segs L LB SP m0 mx H) as H2
                          end
                 end
      end
  end.

(* [comment removed for export] *)
Ltac lxp_heap_gc :=
  let mx := lxp_goal_mem in
  repeat match goal with
  | H : lx_opq _ _ _ _ _ _ ?mm |- _ => tryif constr_eq mm mx then fail else clear H
  end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxp_hrun pl := lxp_heap_box; lxp_run pl; try lxp_heap_unbox.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxp_presx_after HP' :=
  let HPx := fresh "LXHPc" in
  first [ lazymatch type of HP' with heap_pres ?segs ?L ?LB' ?SP' ?m1 ?m2 => pose proof (lxp_pres_to_x segs L LB' SP' m1 m2 HP') as HPx end
        | pose proof HP' as HPx ];
  lazymatch type of HPx with heap_presx ?segs ?L ?LB' ?SP' ?X' ?m1 ?m2 =>
    repeat match goal with
    | F : rw_cells segs m1 ?A ?cs |- _ =>
        first [ apply (heap_presx_rw_cells segs L _ _ _ _ _ _ _ HPx) in F;
                [| cbn [cells_size csize Nat.add]; first [ solve_client_range | assumption | apply client_range_stack; lxp_lia_fast ]
                 | cbn [cells_size csize Nat.add disjoint_from fst snd]; first [ exact I | lxp_lia_fast ] ]
              | clear F ]
    | F : bytes_at segs m1 ?A ?bs |- _ =>
        first [ apply (heap_presx_bytes_at segs L _ _ _ _ _ _ _ HPx) in F;
                [| first [ solve_client_range | assumption | apply client_range_stack; lxp_lia_fast ]
                 | cbn [disjoint_from fst snd]; first [ exact I | lxp_lia_fast ] ]
              | clear F ]
    | F : ro_cells segs m1 ?A ?cs |- _ =>
        first [ apply (lxp_presx_ro_cells segs L _ _ _ _ _ A cs HPx) in F;
                [| cbn [cells_size csize Nat.add]; first [ solve_client_range | assumption ]
                 | cbn [cells_size csize Nat.add disjoint_from fst snd]; first [ exact I | lxp_lia_fast ] ]
              | clear F ]
    end;
    (* [comment removed for export] *)
    let compose := fun HPt LB SP X m0 =>
      let K := fresh "HPX" in
      first [ assert (K : heap_presx segs L LB SP X m0 m2)          (* [comment removed for export] *)
                by (apply (lxp_presx_compose segs L LB LB LB' SP SP' X X' m0 m1 m2 HPt HPx); [ lxp_lia_fast | lxp_lb_incl | lxp_lb_incl | lxp_outside_incl ])
            | assert (K : heap_presx segs L LB' SP X m0 m2)         (* [comment removed for export] *)
                by (apply (lxp_presx_compose segs L LB' LB LB' SP SP' X X' m0 m1 m2 HPt HPx); [ lxp_lia_fast | lxp_lb_incl | lxp_lb_incl | lxp_outside_incl ]) ] in
    first [ match goal with HP : heap_presx segs L ?LB ?SP ?X ?m0 m1 |- _ =>
              tryif constr_eq HP HPx then fail else compose HP LB SP X m0 end
          | match goal with HP : heap_pres segs L ?LB ?SP ?m0 m1 |- _ =>
              tryif constr_eq HP HP' then fail else compose constr:(lxp_pres_to_x segs L LB SP m0 m1 HP) LB SP constr:(@nil ivl) m0 end
          | idtac ]
  end; try clear HPx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_hgoal :=
  first [ eassumption
        | lazymatch goal with
          | |- HEAP ?segs ?L ?HI _ _ ?m _ => lxp_heap_unbox; eassumption
          | |- heap_presx ?segs ?L _ _ _ _ ?m => lxp_heap_unbox; eassumption
          | |- heap_pres ?segs ?L _ _ _ ?m => lxp_heap_unbox; eapply (lxp_presx_to_pres segs L); [ eassumption | reflexivity ]
          | |- mo_frame ?a ?a => apply mo_frame_refl
          | |- mo_frame _ _ => first [ apply mo_frame_refl | eapply mo_frame_trans; [eassumption| first [eassumption | apply mo_frame_refl]] ]
          | |- heap_top _ _ _ _ = heap_top _ _ _ _ => first [ reflexivity | symmetry; eassumption | congruence ]
          | |- MOK _ => eapply heap_mok; eassumption
          end ].
Ltac lxp_lb_restore :=
  repeat match goal with E : ?X = _ |- _ =>
    is_var X; lazymatch type of X with list blk => subst X | list (Z * Z)%type => subst X end end.
Ltac lxp_hret := lxp_heap_unbox; lxp_lb_restore; lxp_ret; try lxp_hgoal.

(* [comment removed for export] *)
Ltac lxp_hfin :=
  try apply aevtM_done; cbv beta; hnf; lx_exs; lx_ands; [> reflexivity | ..];
  try (lazymatch goal with |- HEAP _ _ _ _ _ _ _ => eassumption end);
  try (lazymatch goal with
       | |- heap_presx _ _ _ _ _ _ _ => eassumption
       | |- heap_pres ?segs ?L _ _ _ _ => first [ eassumption | eapply (lxp_x_to_pres segs L); eassumption ]
       end);
  try assumption; try lxp_goal.
#[export] Ltac lxp_fin ::=
  lazymatch goal with
  | |- aevtM _ _ _ _ => lxp_hfin
  | |- evt _ (fun _ => aevtM _ _ _ _) _ => apply evt_done; cbv beta; lxp_hfin
  | |- _ => try apply aevtM_done; lx_post; try lxp_goal
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_ctor :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split
  | |- List.Forall _ _ => constructor
  | |- List.NoDup _ => constructor
  | |- @ex _ _ => fail
  | |- ?G => let h := head_of G in is_ind h; lazymatch goal with |- forall _, _ => fail | |- _ => constructor end
  end.
Ltac lxp_post_misc1 :=
  lazymatch goal with
  | |- aevtM _ _ _ _ => idtac
  | |- evt _ _ _ => idtac
  | |- forall x, In x ?l -> _ => first [ eassumption | intros ? [] | idtac ]     (* [comment removed for export] *)
  | |- ?A -> _ => first [ eassumption
                        | lazymatch goal with |- ?G => tryif has_evar G then fail else
                            (let Hn_ := fresh "Hn" in intros Hn_;
                             first [ exfalso; first [ exact (Hn_ eq_refl) | apply Hn_; reflexivity ]     (* [comment removed for export] *)
                                   | lxp_post_misc1 ]) end
                        | idtac ]                                                  (* [comment removed for export] *)
  | |- _ => first [ lxp_hgoal
                  | lazymatch goal with |- ?G => tryif has_evar G then fail else reflexivity end
                  | left; repeat split; reflexivity
                  | right; repeat split; first [ reflexivity | assumption | lxp_lia_fast ]
                  | progress (cbn [hd last map rev app]); first [ reflexivity | assumption | lxp_hgoal | lxp_ctor ]
                  | lazymatch goal with |- ?G => tryif has_evar G then fail else lxp_ctor end
                  | lxp_lia_fast
                  | idtac ]
  end.
(* [comment removed for export] *)
Ltac lxp_unfold_head :=
  lazymatch goal with |- ?G =>
    let h := head_of G in
    lazymatch h with
    | HEAP => fail | heap_presx => fail | heap_pres => fail | rw_cells => fail | bytes_at => fail | stk => fail
    | mem_inv => fail | mo_frame => fail | @eq => fail | Z.le => fail | Z.lt => fail | and => fail | or => fail
    | _ => unfold h
    end
  end.
Ltac lxp_post_misc :=
  lxp_post_misc1;
  try (lazymatch goal with
       | |- aevtM _ _ _ _ => idtac
       | |- evt _ _ _ => idtac
       | |- _ => progress lxp_unfold_head; cbn [hd last map rev app];
                 repeat match goal with |- _ /\ _ => split end; lxp_post_misc1
       end).

(* [comment removed for export] *)
Ltac lxp_inv_passes :=
  try (lazymatch goal with |- HEAP _ _ _ _ _ _ _ => eassumption end);
  try (lazymatch goal with |- heap_presx _ _ _ _ _ _ _ => eassumption | |- heap_pres ?sg ?L _ _ _ _ => first [ eassumption | eapply (lxp_x_to_pres sg L); eassumption ] end);
  try lxp_goal_shape;
  try assumption;
  try (lazymatch goal with |- exists _, _ => eexists; lxp_goal_shape end);
  try (lazymatch goal with |- @eq _ ?a ?b => first [ reflexivity | assumption | symmetry; assumption ] end);
  try lxp_post_misc1;
  try (lazymatch goal with |- ?G => tryif has_evar G then idtac else lxp_lia_fast end).
Ltac lxp_inv_goal :=
  lazymatch goal with
  | |- aevtM _ _ _ _ => fail
  | |- evt _ _ _ => fail
  | |- ?G => progress lxp_unfold_head; repeat match goal with |- _ /\ _ => split end; lxp_inv_passes
  end.
#[export] Ltac lxp_apply_extra ::= lxp_inv_goal.

(* [comment removed for export] *)
Ltac lxp_ret_open := lxp_pre_ret; lxp_selects; lxp_statics; lxp_heap_unbox; lxp_lb_restore.
Ltac lxp_ret_close :=
  (* [comment removed for export] *)
  try (hnf; lx_exs); try lx_ands; try (repeat match goal with |- _ /\ _ => split end);
  try (lazymatch goal with |- @eq machine_state _ _ => reflexivity | |- MS _ _ _ _ _ _ _ = _ => reflexivity end);
  lxp_inv_passes; try lxp_post_misc.


(* [comment removed for export] *)
(* [comment removed for export] *)
#[export] Ltac lxp_run_pre ::= try lxp_heap_box.
#[export] Ltac lxp_run_refrag ::= lxp_refrag.
(* [comment removed for export] *)
#[export] Ltac lxp_run_post ::= try lxp_heap_unbox; lxp_lb_restore.
#[export] Ltac lxp_pre_ret ::= try lxp_heap_unbox; lxp_lb_restore.
#[export] Ltac lxp_ret_post ::= lxp_post_misc.

(* [comment removed for export] *)
Ltac lxp_after_call :=
  let mx := lxp_goal_mem in
  try match goal with
      | HP' : heap_presx _ _ _ _ _ ?m1 mx |- _ => tryif constr_eq m1 mx then fail else lxp_presx_after HP'
      | HP' : heap_pres _ _ _ _ ?m1 mx |- _ => tryif constr_eq m1 mx then fail else lxp_presx_after HP'
      end;
  lxp_heap_gc; lxp_gc.
