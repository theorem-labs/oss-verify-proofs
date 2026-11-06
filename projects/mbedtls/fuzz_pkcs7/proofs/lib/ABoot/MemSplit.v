(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec SeqExec StepTac StoreOk StreamSim.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MemSplit () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.ABoot.CatExec.wbytes"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.nth"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Lists.ListDef.repeat"; "Corelib.Numbers.BinNums.Z"; "agree_above"; "win_lo"; "cmem"; "wfJ"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.ABoot.StreamSim.wseg_ok"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "Corelib.Init.Datatypes.None"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_inside : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Pbs,(0.(1.&8.))Pm,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Px,(1.&40.)P,(3.(4.(5.&40.R2.)(6.(7.(1.&8.)R4.)))(8.+2.+40.))P,(9.(3.(5.&40.R3.)(5.&40.R2.))(:.(5.&40.R2.)(4.(5.&40.R3.)(6.(7.(1.&8.)R5.)))))(;.(2.(1.&8.))(<.R5.R4.R6.R3.)(=.(1.&8.)(>.(1.&8.)(?.(10.(5.&40.R3.)(5.&40.R4.)))R6.(11.&8.=))))")
(* [comment removed for export] *).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Pbs,(0.(1.&8.))Pm,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Px,(1.&40.)P,(3.(4.(5.&40.R2.)(6.(7.(1.&8.)R4.)))(8.+2.+40.))P,(12.(:.(5.&40.R2.)(5.&40.R3.))(3.(4.(5.&40.R3.)(6.(7.(1.&8.)R5.)))(5.&40.R2.)))(;.(2.(1.&8.))(<.R5.R4.R6.R3.)A1.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = true) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then wbytes f a bs x else g x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = false) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then f x else wbytes g a bs x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_shadow : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Pm,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pbs1,(0.(1.&8.))Pbs2,(0.(1.&8.))P,(;.$13.(7.(1.&8.)R2.)(7.(1.&8.)R1.))P,(3.(4.(5.&40.R4.)(6.(7.(1.&8.)R2.)))(8.+2.+40.))(;.P,(1.&40.)(2.(1.&8.))(<.(<.R6.R5.R4.)R5.R3.)(<.R6.R5.R3.))")
(* [comment removed for export] *).
Proof.
  intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_const : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)Pm,Px,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.Pb,(1.&8.)P,(3.(4.(5.&40.R3.)(6.R2.))(8.+2.+40.))P,Px,(1.&40.)P,(9.(3.(5.&40.R5.)(5.&40.R1.))(:.(5.&40.R1.)(4.(5.&40.R5.)(6.R4.))))(;.(2.(1.&8.))A1.R7.R2.(=.(1.&8.)R4.))(;.(2.(0.(1.&8.)))(15.R7.R6.R5.R4.)(=.(0.(1.&8.))(16.(1.&8.)R3.R4.)))")
(* [comment removed for export] *).
Proof.
  intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat]. rewrite (Hall a) by lia.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
  win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
  fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
           else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

(* [comment removed for export] *)
Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
  forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_const : forall sp0 b, wfJ sp0 (fun _ => Some b).
Proof. intros sp0 b x _. discriminate. Qed.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

(* [comment removed for export] *)
Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
  forall x : word, lo <= bv_unsigned x -> J' x = J x.

Lemma agree_above_refl : forall lo J, agree_above lo J J.
Proof. intros lo J x _. reflexivity. Qed.

Lemma agree_above_trans : forall lo J1 J2 J3,
  agree_above lo J1 J2 -> agree_above lo J2 J3 -> agree_above lo J1 J3.
Proof. intros lo J1 J2 J3 H12 H23 x Hx. rewrite (H23 x Hx). apply H12. exact Hx. Qed.

Lemma agree_above_mono : forall lo lo' J J',
  lo <= lo' -> agree_above lo J J' -> agree_above lo' J J'.
Proof. intros lo lo' J J' Hle H x Hx. apply H. lia. Qed.

Lemma agree_above_wbytes : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Plo,$17.PJ,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pbs,(0.(1.&8.))P,(3.(4.(5.&40.R2.)(6.(7.(1.&8.)R1.)))R4.)(18.R5.R4.(<.R4.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros lo J a bs Hle x Hx. apply wbytes_above. lia.
Qed.

Lemma rdn_agree_above : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)Plo,$17.PJ,P,(1.&40.)(2.(1.&8.))PJ',P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.P,(18.R5.R4.R3.)P,(3.R6.(5.&40.R3.))P,(3.(4.(5.&40.R4.)(6.R3.))(8.+2.+40.))(;.(2.(0.(1.&8.)))(15.R9.R6.R5.R4.)(15.R9.R7.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs lo J J' a n H Hlo Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply H. lia.
Qed.

Section CMem.
  Variable sp0 : word.
  Variable mem0 : word -> option byte.

  Let csel := cmem sp0 mem0.

  #[using="sp0 mem0 csel"] Lemma stack_max_size_pos : 0 < stack_max_size.
  Proof. rewrite stack_max_size_val. lia. Qed.

  (* [comment removed for export] *)

  #[using="csel"] Lemma wbytes_cmem_win : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pbs,(0.(1.&8.))P,(3.(19.Vsp0,)(5.&40.R2.))P,(3.(4.(5.&40.R3.)(6.(7.(1.&8.)R2.)))(5.&40.Vsp0,))(;.P,(1.&40.)(2.(1.&8.))(<.(1:.Vsp0,Vmem0,R6.R5.)R4.R3.)(1:.Vsp0,Vmem0,(<.R6.R4.R3.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros J D a bs Hlo Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_le; lia]).
    reflexivity.
  Qed.

  #[using="csel"] Lemma wbytes_cmem_data : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pbs,(0.(1.&8.))P,(3.(4.(5.&40.R2.)(6.(7.(1.&8.)R1.)))(19.Vsp0,))(;.P,(1.&40.)(2.(1.&8.))(<.(1:.Vsp0,Vmem0,R5.R4.)R3.R2.)(1:.Vsp0,Vmem0,R5.(<.R4.R3.R2.)))")
(* [comment removed for export] *).
  Proof.
    intros J D a bs Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
    unfold win_lo in *.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)

  #[using="csel"] Lemma rdn_cmem_above : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.P,(3.(5.&40.Vsp0,)(5.&40.R2.))P,(3.(4.(5.&40.R3.)(6.R2.))(8.+2.+40.))(;.(2.(0.(1.&8.)))(15.R7.(1:.Vsp0,Vmem0,R6.R5.)R4.R3.)(15.R7.Vmem0,R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
    intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  #[using="csel"] Lemma rdn_cmem_win : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.P,(3.(19.Vsp0,)(5.&40.R2.))P,(3.(4.(5.&40.R3.)(6.R2.))(5.&40.Vsp0,))(;.(2.(0.(1.&8.)))(15.R7.(1:.Vsp0,Vmem0,R6.R5.)R4.R3.)(15.R7.R6.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  #[using="csel"] Lemma rdn_cmem_data : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.P,(3.(4.(5.&40.R2.)(6.R1.))(19.Vsp0,))(;.(2.(0.(1.&8.)))(15.R6.(1:.Vsp0,Vmem0,R5.R4.)R3.R2.)(15.R6.R4.R3.R2.))")
(* [comment removed for export] *).
  Proof.
    intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
    unfold win_lo in *.
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem, win_lo.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="csel"] Lemma cmem_at_above : forall J D (x : word),
    bv_unsigned sp0 <= bv_unsigned x -> cmem sp0 mem0 J D x = mem0 x.
  Proof. intros. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

  #[using="csel"] Lemma cmem_at_win : forall J D (x : word),
    in_win sp0 x -> cmem sp0 mem0 J D x = J x.
  Proof.
    intros J D x [Hlo Hhi]. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  #[using="csel"] Lemma cmem_at_data : forall J D (x : word),
    bv_unsigned x < win_lo sp0 -> cmem sp0 mem0 J D x = D x.
  Proof.
    intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  #[using="csel"] Lemma store_ok_cmem_win : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.P,(1;.Vsp0,R4.)P,(3.(19.Vsp0,)(5.&40.R3.))P,(3.(4.(5.&40.R4.)(6.R3.))(5.&40.Vsp0,))(;.$1<.(1=.R8.(1:.Vsp0,Vmem0,R7.R6.)R5.R4.)$1>.)")
(* [comment removed for export] *).
  Proof.
    intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
    apply store_ok_of_all; [lia|].
    intros x Hx. unfold wview.
    rewrite cmem_at_win by (unfold in_win; lia).
    destruct (J x) as [b|] eqn:E; [discriminate|].
    exfalso. apply (HJ x); [unfold in_win; lia | exact E].
  Qed.

  #[using="Type"] Lemma store_ok_cmem_data : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Psegs,(0.$14.)PJ,P,(1.&40.)(2.(1.&8.))PD,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$13.P,(;.$1<.(1?.R5.R2.R1.)$1>.)(;.$1<.(1=.R6.(1:.Vsp0,Vmem0,R5.R4.)R3.R2.)$1>.)")
(* [comment removed for export] *).
  Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

(* [comment removed for export] *)
Lemma cmem_init : ltac2:(CDefT.buildp (gd_tbl_MemSplit ()) "Pph,$20.Psp0,(1.&40.)Pav,(0.(0.(1.&8.)))Pev,(0.(0.(1.&8.)))Puid,(1.&40.)Phw,(1.&40.)Prdraw,$21.(;.P,(1.&40.)(2.(1.&8.))(22.R7.R6.R5.R4.R3.R2.R1.)(1:.R6.(22.R7.R6.R5.R4.R3.R2.R1.)L,(1.&40.)(=.(1.&8.)(11.&8.=))L,(1.&40.)(23.(1.&8.))))")
(* [comment removed for export] *).
Proof.
  intros ph sp0 av ev uid hw rdraw. apply functional_extensionality. intro x.
  unfold cmem.
  destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
  apply Z.leb_gt in E1.
  unfold wrap_mem, win_lo.
  assert (Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = None).
  { unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r. reflexivity.
Qed.
