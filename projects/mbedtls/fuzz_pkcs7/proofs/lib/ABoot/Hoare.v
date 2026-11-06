(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Hoare () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.bv_add"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "WithFP1.regset"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "WithFP1.regs_agree"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "WithFP1.memset"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "WithFP1.mem_agree"; "OSSVerify.KrLib.ABoot.CatExec.wbytes"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "WithFP1.triple"; "WithFP1.assn"; "Corelib.Init.Logic.or"; "WithFP1.frameable"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "WithFP1.ret_ok"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "WithFP1.ra_indep"; "WithFP1.proc"; "Corelib.Init.Datatypes.S"; "OSSVerify.KrLib.ABoot.CatSim.to_wexit"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

#[using="Type"] Lemma at_0 : forall base, at_ base 0 = base.
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. intros. unfold btgt. apply at_addi. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma at_lit : forall (base : word) (d : Z) (a : word),
  Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. intros. assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_succ_shift : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Pa,(0.&40.)Pi,$1.(2.(0.&40.)(3.&40.(4.(5.&40.(6.&40.R2.(7.&40.+1.$8.)))R1.))(3.&40.(4.(5.&40.R2.)(4.+1.R1.))))")
(* [comment removed for export] *).
Proof.
  intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

#[using="Type"] Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

#[using="Type"] Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. intros W m x _. reflexivity. Qed.

#[using="Type"] Lemma regs_agree_trans : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "PC,$9.Pregs1,(:.&5.(0.&40.))Pregs2,(:.&5.(0.&40.))Pregs3,(:.&5.(0.&40.))P,(;.R4.R3.R2.)P,(;.R5.R3.R2.)(;.R6.R5.R3.)")
(* [comment removed for export] *).
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

#[using="Type"] Lemma mem_agree_trans : forall W m1 m2 m3,
  mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

#[using="Type"] Lemma regs_agree_mono : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "PC,$9.PC',$9.Pregs,(:.&5.(0.&40.))Pregs',(:.&5.(0.&40.))P,Pr,(0.&5.)P,A1.R5.R1.A1.R5.R2.P,(;.R5.R3.R2.)(;.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

#[using="Type"] Lemma mem_agree_mono : forall (W W' : memset) m m',
  (forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_agree_upd : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "PC,$9.Pregs,(:.&5.(0.&40.))Pregs',(:.&5.(0.&40.))Pr,(0.&5.)Pv,(0.&40.)P,A1.R5.R2.P,(;.R6.R5.R4.)(;.R7.R6.(<.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

#[using="Type"] Lemma mem_agree_wbytes : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "PW,$=.Pm,P,(0.&40.)(>.(0.&8.))Pm',P,(0.&40.)(>.(0.&8.))Pa,(0.&40.)Pbs,(?.(0.&8.))P,Pi,$1.P,(10.(11.=R1.)(12.R1.(13.(14.(0.&8.)R2.))))A1.R7.(3.&40.(4.(5.&40.R4.)R2.))P,(15.R6.R5.R4.)(15.R7.R6.(16.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros W m m' a bs. revert m' a.
  induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
  assert (Ha : W a).
  { specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
  apply IH.
  - intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
  - intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
    + exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
      subst x. exact Ha.
    + apply H, Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop := ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,A3.O4.R3.R2.R1.(17.(:.&5.(0.&40.))Lregs',(:.&5.(0.&40.))(17.P,(0.&40.)(>.(0.&8.))Lmem',P,(0.&40.)(>.(0.&8.))(10.(18.O7.(19.Vfx,R6.O3.R5.R4.)(19.Vfx,R2.O2.R1.R4.))(10.A3.O1.R2.R1.R4.(10.(;.O6.R6.R2.)(15.O5.R5.R1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma triple_intro : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PP,Px,(:.&5.(0.&40.))Px0,P,(0.&40.)(>.(0.&8.))Px1,P,(0.&40.)(>.(0.&8.))SpPa,(0.&40.)Pb,(0.&40.)PQ,Px,(:.&5.(0.&40.))Px0,P,(0.&40.)(>.(0.&8.))Px1,P,(0.&40.)(>.(0.&8.))SpP,Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,A3.R7.R3.R2.R1.(17.(:.&5.(0.&40.))Lregs',(:.&5.(0.&40.))(17.P,(0.&40.)(>.(0.&8.))Lmem',P,(0.&40.)(>.(0.&8.))(10.(18.R=.(19.Vfx,R6.R9.R5.R4.)(19.Vfx,R2.R8.R1.R4.))(10.A3.R7.R2.R1.R4.(10.(;.R<.R6.R2.)(15.R;.R5.R1.))))))(1;.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof.
  intros segs C W P a regs mem rom HP.
  exists regs, mem. split; [apply mst_refl|].
  split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_seq : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC1,$9.PW1,$=.PC2,$9.PW2,$=.PP,$1<.PQ,$1<.PR,$1<.Pa,(0.&40.)Pb,(0.&40.)Pc,(0.&40.)P,(1;.R;.R:.R9.R6.R3.R2.R5.)P,(1;.R<.R9.R8.R6.R3.R2.R5.)(1;.R=.Lr,(0.&5.)(1=.A1.R=.R1.A1.R;.R1.)Lx,(0.&40.)(1=.A1.R<.R1.A1.R:.R1.)R8.R5.R3.R6.)")
(* [comment removed for export] *).
Proof.
  intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|]. split.
  - eapply regs_agree_trans;
      [ eapply regs_agree_mono; [|exact Hr1]
      | eapply regs_agree_mono; [|exact Hr2] ]; auto.
  - eapply mem_agree_trans;
      [ eapply mem_agree_mono; [|exact Hm1]
      | eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_conseq : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PC',Px,(0.&5.)SpPW,$=.PW',Px,(0.&40.)SpPP,$1<.PP',Px,(:.&5.(0.&40.))Px0,P,(0.&40.)(>.(0.&8.))Px1,P,(0.&40.)(>.(0.&8.))SpPQ,$1<.PQ',Px,(:.&5.(0.&40.))Px0,P,(0.&40.)(>.(0.&8.))Px1,P,(0.&40.)(>.(0.&8.))SpPa,(0.&40.)Pb,(0.&40.)P,(1;.R;.R:.R8.R6.R2.R1.R4.)P,Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,A3.R9.R3.R2.R1.A3.R;.R4.R3.R2.P,Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,A3.R9.R3.R2.R1.A3.R9.R4.R3.R2.P,Pr,(0.&5.)P,A1.R>.R1.A1.R>.R2.P,Px,(0.&40.)P,A1.R=.R1.A1.R=.R2.(1;.R10.R>.R<.R:.R7.R6.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
  destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
  exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
  split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.

#[using="Type"] Lemma triple_seq_same : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PP,$1<.PQ,$1<.PR,$1<.Pa,(0.&40.)Pb,(0.&40.)Pc,(0.&40.)P,(1;.R9.R8.R7.R6.R3.R2.R5.)P,(1;.R:.R9.R8.R6.R3.R2.R5.)(1;.R;.R:.R9.R8.R5.R3.R6.)")
(* [comment removed for export] *).
Proof.
  intros segs C W P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|].
  split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frameable (C : regset) (W : memset) (R : assn) : Prop := ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))Pregs',(:.&5.(0.&40.))Pmem',P,(0.&40.)(>.(0.&8.))P,(;.O3.R5.R2.)P,(15.O2.R5.R2.)P,A3.O1.R7.R6.R5.A3.O1.R5.R4.R6.")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma triple_frame : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PP,$1<.PQ,$1<.PR,$1<.Pa,(0.&40.)Pb,(0.&40.)P,(1;.R8.R7.R6.R5.R2.R1.R4.)P,(1>.R8.R7.R4.)(1;.R:.R9.R8.Lregs,(:.&5.(0.&40.))Lmem,P,(0.&40.)(>.(0.&8.))Lrom,P,(0.&40.)(>.(0.&8.))(10.A3.R:.R3.R2.R1.A3.R8.R3.R2.R1.)R4.R3.Lregs,(:.&5.(0.&40.))Lmem,P,(0.&40.)(>.(0.&8.))Lrom,P,(0.&40.)(>.(0.&8.))(10.A3.R9.R3.R2.R1.A3.R8.R3.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split; [exact Hst|].
  split; [split; [exact HQ | eapply HR; eassumption]|].
  split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frameable_and : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "PC,$9.PW,$=.PR1,$1<.PR2,$1<.P,(1>.R4.R3.R2.)P,(1>.R5.R4.R2.)(1>.R6.R5.Lregs,(:.&5.(0.&40.))Lmem,P,(0.&40.)(>.(0.&8.))Lrom,P,(0.&40.)(>.(0.&8.))(10.A3.R7.R3.R2.R1.A3.R6.R3.R2.R1.))")
(* [comment removed for export] *).
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.

#[using="Type"] Lemma frameable_reg : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "PC,$9.PW,$=.Pr,(0.&5.)Pv,(0.&40.)P,(1?.A1.R4.R2.)(1>.R5.R4.Lregs,(:.&5.(0.&40.))L,P,(0.&40.)(>.(0.&8.))L,P,(0.&40.)(>.(0.&8.))(2.(0.&40.)(20.R3.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
  rewrite (Hr r Hnc). exact Hv.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frameable_rdn : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.Pa,(0.&40.)Pn,$21.Pbs,(?.(0.&8.))P,Pi,$1.P,(10.(11.=R1.)(12.R1.(13.R3.)))(1?.A1.R6.(3.&40.(4.(5.&40.R5.)R2.)))(1>.R6.R5.L,(:.&5.(0.&40.))Lmem,P,(0.&40.)(>.(0.&8.))L,P,(0.&40.)(>.(0.&8.))(2.(>.(?.(0.&8.)))(22.R:.R2.R7.R6.)(23.(?.(0.&8.))R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
  rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
  induction n as [|n IH]; intros a Hdisj; [reflexivity|].
  assert (Ha : ~ W a).
  { specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
  cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
  intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

#[using="Type"] Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

#[using="Type"] Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop := ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Pk,(0.&40.)P,(24.R1.)(1;.O6.O5.O4.Lregs,(:.&5.(0.&40.))Lmem,P,(0.&40.)(>.(0.&8.))Lrom,P,(0.&40.)(>.(0.&8.))(10.A3.O3.R3.R2.R1.(2.(0.&40.)(20.R3.(7.&5.+1.$8.))R5.))O2.R2.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_call : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PP,$1<.PQ,$1<.Pcallsite,(0.&40.)Pentry,(0.&40.)Pret,(0.&40.)P,Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))(2.(25.$26.)(27.R;.(19.Vfx,R3.R6.R2.R1.))(28.$26.(19.Vfx,(<.R3.(7.&5.+1.$8.)R4.)R5.R2.R1.)))P,(24.R2.)P,(29.R7.)P,(2:.R;.R:.R9.R8.R5.R7.)(1;.R<.Lr,(0.&5.)(1=.A1.R<.R1.(2.(0.&5.)R1.(7.&5.+1.$8.)))R:.R9.R7.R5.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
  assert (Hpre : P (regupd regs 1 ret) mem rom
                 /\ getr (regupd regs 1 ret) 1 = ret).
  { split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
  destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
    as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split.
  - eapply mst_step; [reflexivity | apply Hjal | exact Hst].
  - split; [exact HQ|]. split; [|exact Hm].
    intros r Hr0.
    assert (HnC : ~ C r) by tauto.
    assert (Hne : r <> 1) by tauto.
    rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma triple_loop : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PI,P,$21.$1<.Phd,(0.&40.)Pout,(0.&40.)PQ,$1<.P,Pi,$21.(1;.R8.R7.R6.A1.R5.(2;.R1.)R4.R4.A1.R5.R1.)P,(1;.R8.R7.R6.A1.R5.#0.R4.R3.R2.)Pn,$21.(1;.R:.R9.R8.A1.R7.R1.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs C W I hd out Q Hbody Hexit n.
  induction n as [|n IH]; [exact Hexit|].
  eapply triple_seq_same; [apply Hbody | exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_loop_measure : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PI,P,$21.$1<.Phd,(0.&40.)Pout,(0.&40.)PQ,$1<.PP,$1<.P,Pi,$21.(1;.R9.R8.R7.A1.R6.(2;.R1.)R5.R5.A1.R6.R1.)P,(1;.R9.R8.R7.A1.R6.#0.R5.R4.R3.)P,Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,A3.R6.R3.R2.R1.(17.$21.Ln,$21.A4.R<.R1.R5.R4.R3.)(1;.R;.R:.R9.R4.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
  destruct (Hmeas _ _ _ HP) as (n & HI).
  exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma triple_msteps : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PP,$1<.Pa,(0.&40.)Pb,(0.&40.)PQ,$1<.Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,(1;.R:.R9.R8.R7.R6.R5.R4.)P,A3.R8.R4.R3.R2.(17.(:.&5.(0.&40.))Lregs',(:.&5.(0.&40.))(17.P,(0.&40.)(>.(0.&8.))Lmem',P,(0.&40.)(>.(0.&8.))(10.(18.R>.(19.Vfx,R7.R:.R6.R5.)(19.Vfx,R2.R9.R1.R5.))A3.R8.R2.R1.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs C W P a b Q regs mem rom H HP.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  exists regs', mem'. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_wexit : ltac2:(CDefT.buildp (gd_tbl_Hoare ()) "Psegs,(?.$1:.)PC,$9.PW,$=.PP,$1<.Pa,(0.&40.)Pb,(0.&40.)PQ,$1<.Pbufs,(?.(?.(0.&8.)))Pcode,(0.&40.)Pregs,(:.&5.(0.&40.))Pmem,P,(0.&40.)(>.(0.&8.))Prom,P,(0.&40.)(>.(0.&8.))P,(1;.R<.R;.R:.R9.R8.R7.R6.)P,A3.R:.R4.R3.R2.P,Pregs',(:.&5.(0.&40.))Pmem',P,(0.&40.)(>.(0.&8.))P,A3.R:.R2.R1.R5.(2<.R11.(19.Vfx,R3.R<.R2.R6.)R:.R9.)(2<.R?.(19.Vfx,R6.R;.R5.R4.)R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End WithFP1.

