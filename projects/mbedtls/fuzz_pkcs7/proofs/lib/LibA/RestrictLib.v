(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Exec Shape Mem Cells Arr Frame Step.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA Restrict.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RestrictLib () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.LibA.ALazy.aok_addr"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Dof"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.option"; "Dcov"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.LibA.Restrict.restrict"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "OSSVerify.KrLib.Lib.Cells.cells_at"; "OSSVerify.KrLib.Lib.Step.ro_cells"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "Corelib.Init.Datatypes.false"; "OSSVerify.KrLib.Lib.Frame.wmono"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.LibA.Restrict.rms"; "OSSVerify.KrLib.Lib.MState.MS"; "Corelib.Init.Logic.ex"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Dof (ivs : list (Z * Z)) : word -> bool :=
  fun a => existsb (fun iv => (fst iv <=? bv_unsigned a) && (bv_unsigned a <? snd iv)) ivs.

Definition Dcov (D : word -> bool) (lo hi : Z) : Prop :=
  forall z, lo <= z < hi -> D (wa z) = true.

Lemma Dof_true : forall ivs a, Dof ivs a = true <-> exists iv, In iv ivs /\ fst iv <= bv_unsigned a < snd iv.
Proof.
  intros ivs a. unfold Dof. rewrite existsb_exists. split.
  - intros (iv & Hin & Hb). exists iv. split; [exact Hin|].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - intros (iv & Hin & Hb). exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma Dof_cov : forall ivs lo hi, In (lo, hi) ivs -> 0 <= lo -> hi <= 2^64 -> Dcov (Dof ivs) lo hi.
Proof.
  intros ivs lo hi Hin Hlo Hhi z Hz. apply (proj2 (Dof_true ivs (wa z))). exists (lo, hi). split; [exact Hin|].
  cbn. rewrite wa_unsigned by lia. lia.
Qed.

Lemma Dcov_sub : forall D lo hi lo' hi', Dcov D lo hi -> lo <= lo' -> hi' <= hi -> Dcov D lo' hi'.
Proof. intros D lo hi lo' hi' H ? ? z Hz. apply H. lia. Qed.

Section WithLayout.
Variable L : asan_layout.
Variable CS : Z -> Prop.

#[using="Type"] Lemma Dof_DOK : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pivs,(0.(1.$2.$2.))P,(3.(1.$2.$2.)Liv,(1.$2.$2.)Pz,$2.P,(4.(5.(6.$2.$2.R2.)R1.)(7.R1.(8.$2.$2.R2.)))(9.VL,VCS,R2.)R1.)Pa,(:.&40.)P,(;.$<.(=.R3.R1.)$>.)(9.VL,VCS,(?.&40.R2.))")
(* [comment removed for export] *).
Proof.
  intros ivs H a Ha. apply Dof_true in Ha as (iv & Hin & Hb).
  apply Forall_forall with (x := iv) in H; [|exact Hin]. apply H. exact Hb.
Qed.

#[using="Type"] Lemma Dof_D0 : forall ivs,
  Forall (fun iv => 0 < fst iv) ivs -> Dof ivs (Z_to_bv 64 0) = false.
Proof.
  intros ivs H. destruct (Dof ivs (Z_to_bv 64 0)) eqn:E; [|reflexivity]. exfalso.
  apply Dof_true in E as (iv & Hin & Hb). apply Forall_forall with (x := iv) in H; [|exact Hin].
  rewrite Z_to_bv_unsigned in Hb. change (bv_wrap 64 0) with 0 in Hb. lia.
Qed.
End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Variable D : word -> bool.

#[warnings="-deprecated"] Notation rst := (restrict D).

#[using="Type"] Lemma mrd_restrict_in : forall m x, D x = true -> mrd segs (rst m) x = mrd segs m x.
Proof. intros m x H. unfold mrd. rewrite (restrict_in D m x H). reflexivity. Qed.

#[using="Type"] Lemma wview_restrict_in : forall m x, D x = true -> wview segs (rst m) x = wview segs m x.
Proof. intros m x H. unfold wview. rewrite (restrict_in D m x H). reflexivity. Qed.

#[using="Type"] Lemma bytes_at_restrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,P,(:.&40.)(10.(:.&8.))Pa,$2.Pbs,(0.(:.&8.))P,(11.VD,R2.(12.R2.(13.(14.(:.&8.)R1.))))(15.(16.Vsegs,(17.VD,R4.)R3.R2.)(16.Vsegs,R4.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros m a bs HD. unfold bytes_at. split; intros (H0 & H1 & H); (split; [exact H0|]; split; [exact H1|]);
    intros i Hi; specialize (H i Hi); rewrite mrd_restrict_in in *; auto; apply HD; lia.
Qed.

#[using="Type"] Lemma wr_at_restrict : forall m a n, Dcov D a (a + n) ->
  wr_at segs (rst m) a n <-> wr_at segs m a n.
Proof.
  intros m a n HD. unfold wr_at. split; intros (H0 & H1 & H); (split; [exact H0|]; split; [exact H1|]);
    intros i Hi; specialize (H i Hi); rewrite wview_restrict_in in *; auto; apply HD; lia.
Qed.

#[using="Type"] Lemma cells_at_restrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,P,(:.&40.)(10.(:.&8.))PA,$2.Pcs,(0.$18.)P,(11.VD,R2.(12.R2.(13.(19.R1.))))(15.(1:.Vsegs,(17.VD,R4.)R3.R2.)(1:.Vsegs,R4.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros m A cs HD. unfold cells_at. split; intros [Hwf Hb]; (split; [exact Hwf|]).
  - apply (proj1 (bytes_at_restrict m A (cells_bytes cs) ltac:(rewrite (cells_bytes_length cs Hwf); exact HD))). exact Hb.
  - apply (proj2 (bytes_at_restrict m A (cells_bytes cs) ltac:(rewrite (cells_bytes_length cs Hwf); exact HD))). exact Hb.
Qed.

#[using="Type"] Lemma ro_cells_restrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,P,(:.&40.)(10.(:.&8.))PA,$2.Pcs,(0.$18.)P,(11.VD,R2.(12.R2.(13.(19.R1.))))(15.(1;.Vsegs,(17.VD,R4.)R3.R2.)(1;.Vsegs,R4.R3.R2.))")
(* [comment removed for export] *).
Proof. intros. unfold ro_cells. apply cells_at_restrict. assumption. Qed.

#[using="Type"] Lemma rw_cells_restrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,P,(:.&40.)(10.(:.&8.))PA,$2.Pcs,(0.$18.)P,(11.VD,R2.(12.R2.(13.(19.R1.))))(15.(1<.Vsegs,(17.VD,R4.)R3.R2.)(1<.Vsegs,R4.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros m A cs HD. unfold rw_cells. rewrite cells_at_restrict by exact HD. rewrite wr_at_restrict by exact HD. tauto.
Qed.

#[using="Type"] Lemma u8arr_restrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,P,(:.&40.)(10.(:.&8.))PA,$2.Pbs,(0.(:.&8.))P,(11.VD,R2.(12.R2.(13.(14.(:.&8.)R1.))))(15.(1=.Vsegs,(17.VD,R4.)R3.R2.)(1=.Vsegs,R4.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros m A bs HD. unfold u8arr. rewrite bytes_at_restrict by exact HD. rewrite wr_at_restrict by exact HD. tauto.
Qed.

#[using="Type"] Lemma stk_restrict : forall m lo hi, Dcov D lo hi -> stk segs (rst m) lo hi <-> stk segs m lo hi.
Proof.
  intros m lo hi HD. unfold stk. split; intros (H0 & H1 & H); (split; [exact H0|]; split; [exact H1|]);
    intros a Ha; specialize (H a Ha); rewrite wview_restrict_in, mrd_restrict_in in *; auto.
Qed.

#[using="Type"] Lemma mem_inv_restrict : forall m, mem_inv segs m -> mem_inv segs (rst m).
Proof.
  intros m H a b Hb. unfold restrict in Hb. destruct (D a); [|discriminate]. exact (H a b Hb).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mem_inv_unrestrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,Px,(:.&40.)(10.(:.&8.))PM1,P,(:.&40.)(10.(:.&8.))P,(1>.Vsegs,(17.VD,R1.))P,Pa,(:.&40.)P,(;.$<.A1.VD,R1.$1?.)(;.(10.(:.&8.))A1.R4.R2.A1.R5.R2.)P,(1>.Vsegs,R4.)(1>.Vsegs,R4.)")
(* [comment removed for export] *).
Proof.
  intros m M1 HR Hout Hm a b Hb. destruct (D a) eqn:E.
  - apply (HR a b). rewrite (restrict_in D M1 a E). exact Hb.
  - rewrite (Hout a E) in Hb. exact (Hm a b Hb).
Qed.

#[using="Type"] Lemma munch_unrestrict : forall W m M1,
  munch W (rst m) (rst M1) -> (forall a, D a = false -> M1 a = m a) -> munch W m M1.
Proof.
  intros W m M1 HM Hout x Hx. destruct (D x) eqn:E.
  - specialize (HM x Hx). rewrite !(restrict_in D _ x E) in HM. exact HM.
  - apply Hout. exact E.
Qed.

#[using="Type"] Lemma wmono_unrestrict : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pm,P,(:.&40.)(10.(:.&8.))PM1,P,(:.&40.)(10.(:.&8.))P,(20.Vsegs,(17.VD,R2.)(17.VD,R1.))P,Pa,(:.&40.)P,(;.$<.A1.VD,R1.$1?.)(;.(10.(:.&8.))A1.R4.R2.A1.R5.R2.)(20.Vsegs,R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m M1 HW Hout x Hx. destruct (D x) eqn:E.
  - rewrite <- (wview_restrict_in M1 x E). apply HW. rewrite wview_restrict_in; assumption.
  - unfold wview in *. rewrite (Hout x E). exact Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rms_MS : forall R F pc fc rv m ro, rms D (MS R F pc fc rv m ro) = MS R F pc fc rv (rst m) ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rms_eq_MS : ltac2:(CDefT.buildp (gd_tbl_RestrictLib ()) "Pms1,$21.PR,(22.&5.(:.&40.))PF,(22.&5.(:.&40.))Ppc,(:.&40.)Pfc,(:.&20.)Prv,(10.(:.&40.))PmD,P,(:.&40.)(10.(:.&8.))Pro,P,(:.&40.)(10.(:.&8.))P,(;.$21.(23.VD,R8.)(24.R7.R6.R5.R4.R3.R2.R1.))(25.P,(:.&40.)(10.(:.&8.))LM1,P,(:.&40.)(10.(:.&8.))(4.(;.$21.R:.(24.R9.R8.R7.R6.R5.R1.R3.))(;.P,(:.&40.)(10.(:.&8.))(17.VD,R1.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros [R0 F0 pc0 svc rv0 fc0 m0 ro0] R F pc fc rv mD ro H. unfold rms, set_mem, MS in H. cbn in H.
  exists m0. split; [|congruence]. unfold MS. congruence.
Qed.

End WithSegs.
