(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxRun LxDenot LxSoundRun LxTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_SumsHeap () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "Stdlib.Lists.List.In"; "Kit.cwP"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_heapkit"; "Kit.hpP"; "Corelib.Init.Datatypes.cons"; "Kit.lawP"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_hcli"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_fprop"; "Kit.PROPSP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Kit.objP"; "Corelib.Numbers.BinNums.positive"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.HC"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.BENone"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.bleff"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XRep"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.BECons"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMXH"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "Stdlib.ZArith.BinInt.Z.of_N"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "havoc13"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.heapcall"; "HC_calloc1P"; "havoc11"; "HC_freeP"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_validH"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "PROPSP"; "hpP"; "cwP"; "lawP"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundRun.tgt_aevtM"; "SUM_calloc1P"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okM"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_no_layout"; "Corelib.Init.Logic.True"; "SUM_freeP"].


(* [comment removed for export] *)
Section Kit.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.

  (* [comment removed for export] *)
  Definition hpP (TOP : Z) (MO0 : Model) : lx_hpred := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "LLB,(0.(1.$2.$2.))Lm,P,(3.&40.)(4.(3.&8.))Lmo,$5.(6.(7.$8.VL,VHI,)Lh,(7.$8.VL,VHI,)(9.(:.$8.VL,VHI,R1.R4.R3.R2.)(9.(;.$2.(<.$8.VL,VHI,R1.)O2.)(=.O1.R2.))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Definition cwP (TOP : Z) : lx_cwpred := fun LB x => client_waddr L LB alloc_ceiling TOP x.
  (* [comment removed for export] *)
  Definition lawP : list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop := fun LB sp _ m m' => heap_pres usegs L LB sp m m'.

  Lemma hpP_frame : forall TOP MO0, hp_frame usegs (hpP TOP MO0) (cwP TOP).
  Proof.
    intros TOP MO0 LB m m' mo W (h & HH & HT & MF) MU WM HW. exists h. split; [|split; [exact HT| exact MF]].
    eapply (heap_frame usegs L HI); [exact HH| apply Z.le_refl| | exact WM].
    intros a Ha Hnc. destruct (outside_dec W a) as [Ho|Ho].
    - apply MU. rewrite wa_unsigned by lia. exact Ho.
    - exfalso. apply Hnc. rewrite HT. clear -HW Ho.
      induction HW as [|iv W' Hiv HW' IH]; [exact (False_ind _ (Ho I))|].
      cbn [outside] in Ho. destruct iv as [u v]; cbn [fst snd] in *.
      destruct (Z_lt_dec a u) as [X|X]; [| destruct (Z_le_dec v a) as [Y|Y]]; [apply IH; intros Ho'; apply Ho; split; [lia| exact Ho'] .. | ].
      apply Hiv. lia.
  Qed.
  Lemma cwP_blk : forall TOP, hp_blk (cwP TOP).
  Proof. intros TOP LB b k x Hin Hx. right; right. exists (b, k). split; [exact Hin| cbn; lia]. Qed.
  Lemma lawP_ok : hlaw_ok usegs lawP.
  Proof.
    intros LB sp X m1 m2 x H HR _ Hc. apply H; [exact HR|]. destruct Hc as [Hs|Hb]; [left; exact Hs| right; right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma heapkit_intro : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "Ph,(7.$8.VL,VHI,)PLB,(0.$>.)Pm,P,(3.&40.)(4.(3.&8.))Pmo,$5.POK,(0.$?.)P,(:.$8.VL,VHI,R5.R4.R3.R2.)P,(10.(1.$2.$2.)Liv,(1.$2.$2.)Px,$2.P,(9.(11.(12.$2.$2.R2.)R1.)(13.R1.(14.$2.$2.R2.)))PLB',(0.$>.)P,Pb,$>.P,(15.$>.R1.R:.)(15.$>.R2.R3.)(16.(<.$8.VL,VHI,R;.)R2.R4.)R2.)(17.$8.(18.(<.$8.VL,VHI,R7.)R4.)(16.(<.$8.VL,VHI,R7.))(19.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp$1:.(1;.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp))R6.R6.R3.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo OK HH HOK. split; [split; [| exact HOK]| split; [intros b Hb; exact Hb| split; [apply hpP_frame| split; [apply cwP_blk| constructor; [apply lawP_ok| constructor]]]]].
    exists h. split; [exact HH| split; [reflexivity| apply mo_frame_refl]].
  Qed.
  (* [comment removed for export] *)
  Lemma ok_stack : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.(1.$2.$2.))Plo,$2.PTOP,$2.P,(11.(1<.VL,)R2.)Px,$2.P,(9.(11.(12.$2.$2.(1=.$2.$2.R4.R3.))R1.)(13.R1.(14.$2.$2.(1=.$2.$2.R4.R3.))))PLB',(0.(1.$2.$2.))P,Pb,(1.$2.$2.)P,(15.(1.$2.$2.)R1.R8.)(15.(1.$2.$2.)R2.R3.)(16.R6.R2.R4.)")
(* [comment removed for export] *).
  Proof. intros LB lo TOP ACL x Hx LB' _. cbn [fst snd] in Hx. left. lia. Qed.
  Lemma ok_block : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.(1.$2.$2.))Pb,$2.Pk,$2.PTOP,$2.P,(15.(1.$2.$2.)(1=.$2.$2.R3.R2.)R4.)Px,$2.P,(9.(11.(12.$2.$2.(1=.$2.$2.R5.(1>.R5.R4.)))R1.)(13.R1.(14.$2.$2.(1=.$2.$2.R5.(1>.R5.R4.)))))PLB',(0.(1.$2.$2.))P,Pb,(1.$2.$2.)P,(15.(1.$2.$2.)R1.R9.)(15.(1.$2.$2.)R2.R3.)(16.R6.R2.R4.)")
(* [comment removed for export] *).
  Proof. intros LB b k TOP Hin x Hx LB' HX. cbn [fst snd] in Hx. right; right. exists (b, k). split; [apply HX; exact Hin| cbn; lia]. Qed.
  (* [comment removed for export] *)
  Lemma hcli_block : forall LB smax b k, In (b, k) LB -> lx_hcli usegs LB lawP smax b k.
  Proof.
    intros LB smax b k Hin LB' sp X m1 m2 x HX _ H Hx HR _. apply H; [exact HR|]. right; right. exists (b, k). split; [apply HX; exact Hin| cbn; lia].
  Qed.
  Lemma hcli_static : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.(1.$2.$2.))Psmax,$2.Pa,$2.Pn,$2.P,(11.(1?.VL,)R2.)P,(11.(1>.R3.R2.)(20.VL,))P,Px,$2.P,(9.(11.R5.R1.)(13.R1.(1>.R5.R4.)))(21.(22.VL,R2.))(23.$8.R7.$1:.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof. intros LB smax a n H1 H2 H3 LB' sp X m1 m2 x _ _ H Hx HR _. apply H; [exact HR|]. right; left. split; [lia| apply H3; exact Hx]. Qed.
  Lemma hcli_crange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.$>.)Plo,$2.Psmax,$2.Pb,$2.Pk,$2.P,(24.VL,R5.R4.R2.R1.)P,(25.(11.(1>.R3.R2.)R5.)(11.R4.R3.))(23.$8.R7.$1:.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB lo smax b k CR D LB' sp X m1 m2 x HX Hs H Hx HR _. apply H; [exact HR|].
    destruct (CR x Hx) as [S|[S|(bb & Hbb & Hr)]]; [left; lia| right; left; exact S| right; right].
    exists bb. split; [apply HX; exact Hbb| exact Hr].
  Qed.
  Lemma hcli_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.$>.)Plo,$2.PTOP,$2.Psmax,$2.Pb,$2.Pk,$2.P,(26.VL,R6.R5.R4.R2.R1.)P,(25.(11.(1>.R3.R2.)R6.)(11.R4.R3.))(23.$8.R8.$1:.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB lo TOP smax b k CR D. apply (hcli_crange LB lo); [|exact D]. intros x Hx.
    destruct (CR x Hx) as [S|[S|S]]; [left; lia| right; left; exact S| right; right; exact S].
  Qed.

  (* [comment removed for export] *)
  Definition objP (LB0 : list (Z * Z)) (vs : list Z) : Prop :=
    match vs with [b; k] => 0 <= k /\ client_range L LB0 alloc_ceiling b k | _ => True end.
  Definition PROPSP (LB0 : list (Z * Z)) : list (list Z -> Prop) := [objP LB0].
  Lemma obj_crange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.$>.)Plo,$2.Pb,$2.Pk,$2.P,(24.VL,R4.R3.R2.R1.)P,(11.(1<.VL,)R4.)P,(11.=R3.)(27.(28.R7.)#0.(19.$2.R5.(19.$2.R4.(1;.$2.))))")
(* [comment removed for export] *).
  Proof. intros LB lo b k H ACL Hk. split; [exact Hk|]. intros x Hx. destruct (H x Hx) as [X|[X|X]]; [left; lia| right; left; exact X| right; right; exact X]. Qed.
  Lemma obj_block : forall LB b k, In (b, k) LB -> 0 <= k -> lx_fprop (PROPSP LB) 0 [b; k].
  Proof. intros LB b k Hin Hk. split; [exact Hk|]. intros x Hx. right; right. exists (b, k). split; [exact Hin| cbn; lia]. Qed.
  (* [comment removed for export] *)
  Lemma obj_apart : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "Ph,(7.$8.VL,VHI,)PLB0,(0.(1.$2.$2.))PLB,(0.(1.$2.$2.))Pm,P,(3.&40.)(4.(3.&8.))Pmo,$5.PA,$2.Pn,$2.Pb,$2.Pk,$2.P,(:.$8.VL,VHI,R9.(19.(1.$2.$2.)(1=.$2.$2.R4.R3.)R7.)R6.R5.)P,Px,(1.$2.$2.)P,(15.(1.$2.$2.)R1.R:.)(15.(1.$2.$2.)R2.R:.)P,(11.(29.VL,)(1?.VL,))P,(11.(20.VL,)(2:.VL,))P,(2;.R<.(19.$2.R6.(19.$2.R5.(1;.$2.))))P,(13.=R8.)(25.(;.$2.R7.=)(25.(11.(1>.R:.R9.)R8.)(11.(1>.R8.R7.)R:.)))")
(* [comment removed for export] *).
  Proof.
    intros h LB0 LB m mo A n b k HH EXT D1 D2 [Hk0 HO] Hn. destruct (Z.eq_dec k 0) as [->|Hk]; [left; reflexivity| right].
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR [HAP _]]. inversion HBR as [|x l HA _]; subst. cbn [fst snd] in HA.
    destruct HA as (HA0 & _ & _ & HAC & HAI).
    assert (PW : forall x, b <= x < b + k -> A <= x < A + n -> False).
    { intros x Hx HxA. destruct (HO x Hx) as [X|[X|(bb & Hbb & Hr)]]; [lia| lia|].
      destruct bb as [B K]. cbn [fst snd] in Hr. pose proof (HAP B K (EXT _ Hbb)). lia. }
    destruct (Z_lt_dec b (A + n)); [|lia]. destruct (Z_lt_dec A (b + k)); [|lia]. exfalso.
    destruct (Z_le_dec b A); [apply (PW A); lia| apply (PW b); lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ok_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.$>.)Plo,$2.PTOP,$2.Pb,$2.Pk,$2.P,(26.VL,R5.R4.R3.R2.R1.)P,(11.(1<.VL,)R5.)Px,$2.P,(9.(11.(12.$2.$2.(1=.$2.$2.R5.(1>.R5.R4.)))R1.)(13.R1.(14.$2.$2.(1=.$2.$2.R5.(1>.R5.R4.)))))PLB',(0.$>.)P,Pbb,$>.P,(15.$>.R1.R;.)(15.$>.R2.R3.)(16.R9.R2.R4.)")
(* [comment removed for export] *).
  Proof.
    intros LB lo TOP b k CW ACL x Hx LB' HX. cbn [fst snd] in Hx. destruct (CW x Hx) as [S|[D|(bb & Hin & Hr)]].
    - left. lia. - right; left. exact D. - right; right. exists bb. split; [apply HX; exact Hin| exact Hr].
  Qed.
  (* [comment removed for export] *)
  Lemma obj_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PLB,(0.$>.)Plo,$2.PTOP,$2.Pb,$2.Pk,$2.P,(26.VL,R5.R4.R3.R2.R1.)P,(11.(1<.VL,)R5.)P,(11.=R3.)(27.(28.R8.)#0.(19.$2.R5.(19.$2.R4.(1;.$2.))))")
(* [comment removed for export] *).
  Proof.
    intros LB lo TOP b k CW ACL Hk. split; [exact Hk|]. intros x Hx. destruct (CW x Hx) as [S|[D|B]]; [left; lia| right; left; exact D| right; right; exact B].
  Qed.
End Kit.

(* [comment removed for export] *)
Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).
Definition havoc13 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "(19.(1.$2.$2<.)(1=.$2.$2<.+:.^<.)(19.(1.$2.$2<.)(1=.$2.$2<.+5.^=.)(19.(1.$2.$2<.)(1=.$2.$2<.+6.^>.)(19.(1.$2.$2<.)(1=.$2.$2<.+7.^?.)(19.(1.$2.$2<.)(1=.$2.$2<.+;.^10.)(19.(1.$2.$2<.)(1=.$2.$2<.+<.^11.)(19.(1.$2.$2<.)(1=.$2.$2<.+=.^12.)(19.(1.$2.$2<.)(1=.$2.$2<.+>.^13.)(19.(1.$2.$2<.)(1=.$2.$2<.+?.^14.)(19.(1.$2.$2<.)(1=.$2.$2<.+10.^15.)(19.(1.$2.$2<.)(1=.$2.$2<.+11.^16.)(19.(1.$2.$2<.)(1=.$2.$2<.+1<.^17.)(19.(1.$2.$2<.)(1=.$2.$2<.+1=.^18.)(19.(1.$2.$2<.)(1=.$2.$2<.+1>.^19.)(19.(1.$2.$2<.)(1=.$2.$2<.+1?.^1:.)(1;.(1.$2.$2<.)))))))))))))))))")
(* [comment removed for export] *).
Definition HC_calloc1P (n : N) : heapcall := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "(2=.#0.^3.(1;.$2>.)(2?.$2>.#0.)$30.(2?.(1.(1.(0.$31.)(0.$32.))$33.)(1=.(1.(0.$31.)(0.$32.))$33.(1=.(0.$31.)(0.$32.)(19.$31.(34.(35.=)(36.^<.))(19.$31.(37.(36.^<.)&4.)(19.$31.(38.(39.(36.^<.)(36.^2.))(36.^8.))(19.$31.(3:.(39.(36.^<.)(36.^2.))(36.^:.)(36.^;.)(36.^<.))(1;.$31.)))))(19.$32.(3;.(36.^4.)(36.^3.))(19.$32.(3<.(36.^<.)(19.$3=.(3>.O1.(35.=))(1;.$3=.)))(1;.$32.))))(3?.^<.(36.^2.)))))")
(* [comment removed for export] *).
Definition SUM_calloc1P (n : N) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "(40.+3?960.$41.#;.#?.#0.(19.(1.$2.$2<.)(1=.$2.$2<.+:.^1.)(19.(1.$2.$2<.)(1=.$2.$2<.+;.^2.)(19.(1.$2.$2<.)(1=.$2.$2<.+2.^3.)(19.(1.$2.$2<.)(1=.$2.$2<.+4.^5.)(1;.(1.$2.$2<.))))))(19.(1.$2<.$2>.)(1=.$2<.$2>.^6.#0.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^7.#1.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^8.#2.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^9.#3.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^:.#4.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^;.#5.)(1;.(1.$2<.$2>.))))))))(42.$2<.)(1;.$32.)(2?.(1.$2<.$2<.)(1=.$2<.$2<.^4.^3.))(1;.(1.(1.$2<.$2<.)$2<.))(1;.$32.)(19.$31.(43.(36.^1.)(35.+1.))(19.$31.(43.(36.^2.)(35.(44.O1.)))(19.$31.(43.(36.^5.)(36.^9.))(19.$31.(38.(36.^8.)(36.^4.))(19.$31.(38.(36.^4.)(39.(36.^3.)(45.-1.(36.^7.))))(19.$31.(38.(36.^3.)(36.^6.))(19.$31.(38.(35.=)(36.^7.))(19.$31.(34.(36.^3.)(35.(46.+2.+40.)))(1;.$31.)))))))))(1;.(1.$47.$47.))$48.(19.$32.(3;.(36.^4.)(36.^3.))(1;.$32.))(19.$31.(43.(36.^<.)(35.=))(1;.$31.))(1;.$2>.)(42.$2>.)(2?.$49.(4:.O1.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition havoc11 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "(19.(1.$2.$2<.)(1=.$2.$2<.+:.^;.)(19.(1.$2.$2<.)(1=.$2.$2<.+5.^<.)(19.(1.$2.$2<.)(1=.$2.$2<.+6.^=.)(19.(1.$2.$2<.)(1=.$2.$2<.+7.^>.)(19.(1.$2.$2<.)(1=.$2.$2<.+;.^?.)(19.(1.$2.$2<.)(1=.$2.$2<.+<.^10.)(19.(1.$2.$2<.)(1=.$2.$2<.+=.^11.)(19.(1.$2.$2<.)(1=.$2.$2<.+>.^12.)(19.(1.$2.$2<.)(1=.$2.$2<.+?.^13.)(19.(1.$2.$2<.)(1=.$2.$2<.+10.^14.)(19.(1.$2.$2<.)(1=.$2.$2<.+11.^15.)(19.(1.$2.$2<.)(1=.$2.$2<.+1<.^16.)(19.(1.$2.$2<.)(1=.$2.$2<.+1=.^17.)(19.(1.$2.$2<.)(1=.$2.$2<.+1>.^18.)(19.(1.$2.$2<.)(1=.$2.$2<.+1?.^19.)(1;.(1.$2.$2<.)))))))))))))))))")
(* [comment removed for export] *).
Definition HC_freeP : heapcall := HC 0%nat 2%positive [] None (BEPop 1%positive) None.
Definition SUM_freeP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "(40.+3?:98.$41.#:.#?.#0.(19.(1.$2.$2<.)(1=.$2.$2<.+:.^1.)(19.(1.$2.$2<.)(1=.$2.$2<.+2.^2.)(19.(1.$2.$2<.)(1=.$2.$2<.+4.^4.)(1;.(1.$2.$2<.)))))(19.(1.$2<.$2>.)(1=.$2<.$2>.^5.#0.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^6.#1.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^7.#2.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^8.#3.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^9.#4.)(19.(1.$2<.$2>.)(1=.$2<.$2>.^:.#5.)(1;.(1.$2<.$2>.))))))))(42.$2<.)(1;.$32.)(2?.(1.$2<.$2<.)(1=.$2<.$2<.^3.^2.))(1;.(1.(1.$2<.$2<.)$2<.))(1;.$32.)(19.$31.(43.(36.^4.)(36.^8.))(19.$31.(38.(36.^7.)(36.^3.))(19.$31.(38.(36.^3.)(39.(36.^2.)(45.-1.(36.^6.))))(19.$31.(38.(36.^2.)(36.^5.))(19.$31.(38.(35.=)(36.^6.))(19.$31.(34.(36.^2.)(35.(46.+2.+40.)))(1;.$31.)))))))(1;.(1.$47.$47.))$4;.(19.$32.(3;.(36.^3.)(36.^2.))(1;.$32.))(1;.$31.)(1;.$2>.)(42.$2>.)(2?.$49.$4<.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Section Valid.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = 0x3f960.
  Notation GS TOP := [TOP; hl_stack L; alloc_ceiling; hl_tp L; hl_img_lo L; hl_img_hi L].

  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.

  Lemma sum_calloc1P_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "Pn,$4=.PQ,P,$4>.SpPLB0,(0.(1.$2.$2.))PTOP,$2.PMO0,$5.PAL,$4?.POPS,(0.P,P,(3.&40.)(4.(3.&8.))Sp)PLAWS,(0.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp)PCS,P,$2.SpP,(9.(13.=(44.R9.))(13.(44.R9.)(46.+2.+20.)))(50.$8.R5.(19.$2.R7.(19.$2.(51.VL,)(19.$2.(1<.VL,)(19.$2.(52.VL,)(19.$2.(29.VL,)(19.$2.(2:.VL,)(1;.$2.)))))))R4.R3.(53.VL,R8.)R8.(54.VL,VHI,R7.R6.)(55.VL,R7.)(19.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp(56.VL,)(1;.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp))(57.$8.R9.)(58.R:.)(4:.R:.)R2.)")
(* [comment removed for export] *).
  Proof.
    intros n Q LB0 TOP MO0 AL OPS LAWS CS Hn. split; [reflexivity|]. unfold SUM_calloc1P, HC_calloc1P, havoc13, q. lx_sum_unfold.
    intros cnt sz SP LO TPV TOP' HLS ACE HLTP IMGLO IMGHI F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 R10 R11 R2 R4 ST P1 P2 P5 P3 P4 P6 P7 P8 EXT (h & HH & HT & MF) _ K1 K2.
    unfold tgt_aevtM. intros MK. subst x10 x11 x2 x4. rewrite P1. rewrite P5, G3 in K1, K2 |- *. rewrite P2 in K2 |- *.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64; lia).
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut.
    { eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := Z.of_N n) (lo := LO); rewrite ?HSP; try reflexivity; try eassumption; try lia. }
    intros ms' mo2 PO. unfold call_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO. destruct PO as (MI' & ST' & MF' & HPR & h' & HT' & CASES).
    destruct CASES as [[-> HH']| (A & -> & HBR & HH' & HNEW)]; lx_aevtM_zregs.
    - (* [comment removed for export] *)
      eapply (K1 0); try eassumption; try reflexivity; try exact I; try exact (heap_mok _ _ HI _ _ _ _ HH').
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
    - (* [comment removed for export] *)
      destruct HBR as (HA0 & HA16 & _ & HAC & HAI). rewrite Z.mul_1_l in HAC, HAI, HH', HNEW.
      destruct (heap_blocks _ _ HI _ _ _ _ HH') as [_ [HAP _]].
      assert (HOBJ : forall b k, objP L LB0 [b; k] -> k = 0 \/ A + Z.of_N n <= b \/ b + k <= A).
      { intros b k HO. eapply (obj_apart L HI); [exact HH'| exact EXT| exact DIM1| exact DIM2| exact HO| lia]. }
      eapply (K2 A); try eassumption; try lia; try exact (heap_mok _ _ HI _ _ _ _ HH'); try (split; [exact HAP| exact HOBJ]).
      all: try (replace (N.to_nat n) with (Z.to_nat (Z.of_N n)) by lia; exact HNEW).
      all: try (change (2 ^ Z.of_N 4) with 16; exact HA16).
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  Lemma SUMS_callocP_ok : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "Pn,$4=.PQ,P,$4>.SpPLB0,(0.(1.$2.$2.))PTOP,$2.PMO0,$5.P,(9.(13.=(44.R5.))(13.(44.R5.)(46.+2.+20.)))(10.$59.(5:.$8.$5;.(19.$2.R3.(19.$2.(51.VL,)(19.$2.(1<.VL,)(19.$2.(52.VL,)(19.$2.(29.VL,)(19.$2.(2:.VL,)(1;.$2.)))))))(1;.P,P,(3.&40.)(4.(3.&8.))Sp)(1;.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp)(53.VL,R4.)R4.(54.VL,VHI,R3.R2.)(55.VL,R3.)(19.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp(56.VL,)(1;.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp))(57.$8.R5.)L,$2.$5<.)(19.$59.(58.R6.)(1;.$59.)))")
(* [comment removed for export] *).
  Proof. intros. constructor; [|constructor]. eapply apply_summary_soundM. apply sum_calloc1P_valid. assumption. Qed.

  Hypothesis HFREE : hl_free L = 0x3fa98.
  Lemma sum_freeP_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "PQ,P,$4>.SpPLB0,(0.(1.$2.$2.))PTOP,$2.PMO0,$5.PAL,$4?.POPS,(0.P,P,(3.&40.)(4.(3.&8.))Sp)PLAWS,(0.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp)PCS,P,$2.Sp(50.$8.R4.(19.$2.R6.(19.$2.(51.VL,)(19.$2.(1<.VL,)(19.$2.(52.VL,)(19.$2.(29.VL,)(19.$2.(2:.VL,)(1;.$2.)))))))R3.R2.(53.VL,R7.)R7.(54.VL,VHI,R6.R5.)(55.VL,R6.)(19.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp(56.VL,)(1;.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp))(57.$8.R8.)$5=.$4<.R1.)")
(* [comment removed for export] *).
  Proof.
    intros Q LB0 TOP MO0 AL OPS LAWS CS. split; [reflexivity|]. unfold SUM_freeP, HC_freeP, havoc11, q. lx_sum_unfold.
    intros A SP LO TPV TOP' HLS ACE HLTP IMGLO IMGHI F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 R10 R2 R4 ST P1 P2 P3 P4 P5 P6 EXT (h & HH & HT & MF) (n & HIN) K1 _.
    unfold tgt_aevtM. intros MK. subst x10 x2 x4. rewrite P1, G3 in K1 |- *.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64; lia).
    replace (Z_to_bv 64 0x3fa98) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
    eapply aevtM_cut.
    { eapply (heap_free usegs L HI) with (lo := LO); rewrite ?HSP; try reflexivity; try eassumption; try lia. }
    intros ms' mo2 PO. unfold call_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO. destruct PO as (MI' & ST' & MF' & HPR & h' & HT' & HH').
    lx_aevtM_zregs.
    eapply (K1 (bv_unsigned a0')); try eassumption; try reflexivity; try exact I; try exact (heap_mok _ _ HI _ _ _ _ HH').
    exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma SUMS_heapP_ok : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeap ()) "Pn,$4=.PQ,P,$4>.SpPLB0,(0.(1.$2.$2.))PTOP,$2.PMO0,$5.P,(9.(13.=(44.R5.))(13.(44.R5.)(46.+2.+20.)))(10.$59.(5:.$8.$5;.(19.$2.R3.(19.$2.(51.VL,)(19.$2.(1<.VL,)(19.$2.(52.VL,)(19.$2.(29.VL,)(19.$2.(2:.VL,)(1;.$2.)))))))(1;.P,P,(3.&40.)(4.(3.&8.))Sp)(1;.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp)(53.VL,R4.)R4.(54.VL,VHI,R3.R2.)(55.VL,R3.)(19.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp(56.VL,)(1;.P,(0.(1.$2.$2.))P,$2.P,(0.(1.$2.$2.))P,P,(3.&40.)(4.(3.&8.))P,P,(3.&40.)(4.(3.&8.))Sp))(57.$8.R5.)L,$2.$5<.)(19.$59.(58.R6.)(19.$59.$5=.(1;.$59.))))")
(* [comment removed for export] *).
  Proof.
    intros. constructor; [|constructor; [|constructor]].
    - eapply apply_summary_soundM. apply sum_calloc1P_valid. assumption.
    - eapply apply_summary_soundM. apply sum_freeP_valid.
  Qed.
End Valid.

