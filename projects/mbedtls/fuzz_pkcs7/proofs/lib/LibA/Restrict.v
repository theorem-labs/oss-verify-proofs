(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Exec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Restrict () : Init.string Init.list := ["Stdlib.Lists.List.existsb"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.Some"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "Restrict.segcov"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "wplus"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Restrict.restrict"; "Corelib.Init.Peano.lt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.seg_ov_read_bytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Sem.eff"; "LinuxProcessSemantics.Riscv.Sem.core"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.interp_eff_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.false"; "accD"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fregs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc_val"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_resv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fcsr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.decode_exec_accesses"; "Restrict.rms"; "Restrict.set_mem"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "Restrict.unr"; "OSSVerify.KrLib.Lib.Exec.mstep"; "OSSVerify.KrLib.LibA.AEvtA.mstepA"; "OSSVerify.KrLib.Lib.Exec.msteps"; "OSSVerify.KrLib.LibA.AEvtA.mstepsA"; "OSSVerify.KrLib.Lib.Shape.msteps"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.LibA.AEvtA.evtA"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wplus (a : word) (i : nat) : word := (a + Z_to_bv 64 (Z.of_nat i))%bv.

Lemma wplus_0 : forall a, wplus a 0 = a.
Proof.
  intros a. unfold wplus. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. cbn [Z.of_nat].
  unfold bv_wrap. rewrite Zplus_mod_idemp_r, Z.add_0_r. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Lemma wplus_S : forall a i, wplus a (S i) = wplus (a + 1)%bv i.
Proof.
  intros a i. unfold wplus. apply bv_eq.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition rangeD (D : word -> bool) (a : word) (n : nat) : Prop :=
  (n <= 8)%nat /\ forall i, (i < n)%nat -> D (wplus a i) = true.

Definition accD (D : word -> bool) (acc : list memory_access) : Prop :=
  Forall (fun an => rangeD D (fst an) (snd an)) acc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Restrict.
Variable segs : list Segment.
Variable D : word -> bool.

(* [comment removed for export] *)
Definition segcov (z : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "(0.$1.Lseg,$1.(2.(3.(4.(5.R1.))O1.)(6.O1.(7.(4.(5.R1.))(4.(8.R1.)))))Vsegs,)")
(* [comment removed for export] *).

Hypothesis Dseg : forall a : word, segcov (bv_unsigned a) = true -> D a = true.
Hypothesis SEGTOP : forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 2^64) segs = true.

Definition restrict (m : word -> option byte) : word -> option byte :=
  fun a => if D a then m a else None.

(* [comment removed for export] *)
Definition unrestrict (mD m0 : word -> option byte) : word -> option byte :=
  fun a => if D a then mD a else m0 a.

#[using="Type"] Lemma restrict_in : forall m a, D a = true -> restrict m a = m a.
Proof. intros m a H. unfold restrict. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma restrict_out : forall m a, D a = false -> restrict m a = None.
Proof. intros m a H. unfold restrict. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma restrict_unrestrict : forall mD m0, (forall a, D a = false -> mD a = None) -> restrict (unrestrict mD m0) = mD.
Proof.
  intros mD m0 H. apply functional_extensionality. intros a. unfold restrict, unrestrict.
  destruct (D a) eqn:E; [reflexivity|]. symmetry. apply H. exact E.
Qed.
#[using="Type"] Lemma restrict_idem : forall m, restrict (restrict m) = restrict m.
Proof. intros m. apply functional_extensionality. intros a. unfold restrict. destruct (D a); reflexivity. Qed.
#[using="Type"] Lemma restrict_none_out : forall m a, D a = false -> restrict m a = None.
Proof. exact restrict_out. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma find_segment_cov : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pl,(9.$1.)Pz,$:.Pn,$:.Pseg,$1.P,(;.(<.$1.)(=.R4.R3.R2.)(>.$1.R1.))P,Pseg',$1.P,(?.$1.R1.R6.)(?.$1.R2.Vsegs,)Pi,$:.P,(10.(11.=R1.)(12.R1.R5.))(;.$13.(14.(7.R7.R2.))$15.)")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n seg Hf Hsub i Hi; cbn in Hf; [discriminate|].
  destruct (Z.leb_spec0 (Z.of_N (seg_base s)) z); destruct (Z.leb_spec0 (z + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb] in Hf.
  - unfold segcov. apply existsb_exists. exists s. split; [apply Hsub; left; reflexivity|].
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  - eapply IH; eauto. intros; apply Hsub; right; assumption.
  - eapply IH; eauto. intros; apply Hsub; right; assumption.
  - eapply IH; eauto. intros; apply Hsub; right; assumption.
Qed.

#[using="SEGTOP"] Lemma find_segment_top : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pl,(9.$1.)Pz,$:.Pn,$:.Pseg,$1.P,(;.(<.$1.)(=.R4.R3.R2.)(>.$1.R1.))P,Pseg',$1.P,(?.$1.R1.R6.)(?.$1.R2.Vsegs,)(11.(7.R5.R4.)(16.+2.+40.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n seg Hf Hsub; cbn in Hf; [discriminate|].
  assert (HT : Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 2^64).
  { pose proof SEGTOP as ST. apply forallb_forall with (x := s) in ST. apply Z.leb_le in ST. exact ST. apply Hsub. left; reflexivity. }
  destruct (Z.leb_spec0 (Z.of_N (seg_base s)) z); destruct (Z.leb_spec0 (z + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb] in Hf;
    try lia; (eapply IH; [exact Hf|]; intros; apply Hsub; right; assumption).
Qed.

(* [comment removed for export] *)
#[using="Dseg SEGTOP"] Lemma find_segment_D : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pa,(17.&40.)Pn,$:.Pseg,$1.P,(;.(<.$1.)(=.Vsegs,(18.&40.R3.)R2.)(>.$1.R1.))Pi,$19.P,(12.(1:.R1.)R4.)(;.$13.A1.VD,(1;.R6.R2.)$15.)")
(* [comment removed for export] *).
Proof.
  intros a n seg Hf i Hi. apply Dseg.
  pose proof (find_segment_top segs (bv_unsigned a) n seg Hf ltac:(auto)) as HT.
  pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  replace (bv_unsigned (wplus a i)) with (bv_unsigned a + Z.of_nat i).
  - eapply find_segment_cov; eauto. lia.
  - unfold wplus. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite Zplus_mod_idemp_r. symmetry. apply Z.mod_small. cbn in HT |- *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Dseg SEGTOP"] Lemma memory_read_1_D : forall a bs, memory_read segs a 1 = Some bs -> D a = true.
Proof.
  intros a bs H. unfold memory_read in H.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N 1)) as [seg|] eqn:E; [|discriminate].
  rewrite <- (wplus_0 a). eapply find_segment_D; [exact E|]. cbn. lia.
Qed.

#[using="Dseg SEGTOP"] Lemma ov_read_bytes_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pn,$19.Pm,P,(17.&40.)(<.(17.&8.))Pa,(17.&40.)Pbs,(9.(17.&8.))P,(;.(<.(9.(17.&8.)))(1<.Vsegs,(1=.R3.)R2.R4.)(>.(9.(17.&8.))R1.))(10.(;.(<.(9.(17.&8.)))(1<.Vsegs,R4.R3.R5.)(>.(9.(17.&8.))R2.))Pi,$19.P,(1>.R1.R6.)(;.$13.A1.VD,(1;.R5.R2.)$15.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m a bs H.
  - cbn in H |- *. split; [exact H|]. intros i Hi; lia.
  - cbn [ov_read_bytes] in H |- *.
    assert (HD : D a = true).
    { unfold restrict in H. destruct (D a) eqn:E; [reflexivity|].
      destruct (memory_read segs a 1) as [[|b l]|] eqn:M; try discriminate.
      pose proof (memory_read_1_D _ _ M); congruence. }
    rewrite (restrict_in m a HD) in H.
    destruct (match m a with Some b => Some b | None => match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end end) as [b|]; [|discriminate].
    destruct (ov_read_bytes segs (restrict m) (a + 1)%bv n) as [rest|] eqn:R; [|discriminate].
    destruct (IH _ _ _ R) as [-> HDi].
    split; [exact H|].
    intros [|i] Hi; [rewrite wplus_0; exact HD|]. rewrite wplus_S. apply HDi. lia.
Qed.

#[using="Type"] Lemma seg_ov_read_bytes_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pn,$19.Pm,P,(17.&40.)(<.(17.&8.))Pseg,$1.Pa,(17.&40.)P,Pi,$19.P,(1>.R1.R5.)(;.$13.A1.VD,(1;.R3.R2.)$15.)(;.(<.(9.(17.&8.)))(1?.(1=.R4.)R3.R2.R5.)(1?.R4.R3.R2.R5.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m seg a HD; [reflexivity|].
  cbn [seg_ov_read_bytes]. rewrite (restrict_in m a) by (rewrite <- (wplus_0 a); apply HD; lia).
  rewrite IH; [reflexivity|]. intros i Hi. rewrite <- wplus_S. apply HD. lia.
Qed.

#[using="Dseg SEGTOP"] Lemma code_read_ov_restrict : forall m a n, code_read_ov segs (restrict m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg); [|reflexivity].
  apply seg_ov_read_bytes_restrict. intros i Hi. eapply find_segment_D; [exact E|]. lia.
Qed.

#[using="Dseg SEGTOP"] Lemma fetch_word_ov_restrict : forall m a, fetch_word_ov segs (restrict m) a = fetch_word_ov segs m a.
Proof. intros. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

#[using="Dseg SEGTOP"] Lemma fetch_half_any_restrict : forall m a, fetch_half_any segs (restrict m) a = fetch_half_any segs m a.
Proof. intros. unfold fetch_half_any, fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

#[using="Dseg SEGTOP"] Lemma fetch_tail_any_restrict : forall m a, fetch_tail_any segs (restrict m) a = fetch_tail_any segs m a.
Proof. intros. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

#[using="Dseg SEGTOP"] Lemma fetch_failure_restrict : forall m a, fetch_failure segs (restrict m) a = fetch_failure segs m a.
Proof. intros. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Dseg SEGTOP"] Lemma wview_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pm,P,(17.&40.)(<.(17.&8.))Pa,(17.&40.)Pb,(17.&8.)P,(;.(<.(17.&8.))(20.Vsegs,(1=.R3.)R2.)(>.(17.&8.)R1.))(10.(;.$13.A1.VD,R3.$15.)(21.(17.&8.)Lb',(17.&8.)(;.(<.(17.&8.))(20.Vsegs,R5.R4.)(>.(17.&8.)R1.))))")
(* [comment removed for export] *).
Proof.
  intros m a b H. unfold wview in H |- *. unfold restrict in H.
  destruct (D a) eqn:E.
  - split; [reflexivity|]. destruct (m a); [eexists; reflexivity|].
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|discriminate].
    destruct (seg_writable seg); [|discriminate]. eexists; exact H.
  - destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:F; [|discriminate].
    exfalso. pose proof (find_segment_D a 1 seg F 0%nat ltac:(cbn; lia)) as HD. rewrite wplus_0 in HD. congruence.
Qed.

#[using="Dseg SEGTOP"] Lemma store_ok_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pn,$19.Pm,P,(17.&40.)(<.(17.&8.))Pa,(17.&40.)P,(;.$13.(22.Vsegs,(1=.R2.)R1.R3.)$15.)(10.(;.$13.(22.Vsegs,R3.R2.R4.)$15.)Pi,$19.P,(1>.R1.R5.)(;.$13.A1.VD,(1;.R4.R2.)$15.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m a H.
  - split; [reflexivity|]. intros; lia.
  - cbn [store_ok] in H |- *.
    destruct (wview segs (restrict m) a) as [b|] eqn:W; [|discriminate].
    destruct (wview_restrict _ _ _ W) as [HD [b' ->]].
    destruct (IH _ _ H) as [-> HDi]. split; [reflexivity|].
    intros [|i] Hi; [rewrite wplus_0; exact HD|]. rewrite wplus_S. apply HDi. lia.
Qed.

#[using="Type"] Lemma write_to_mem_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pbs,(9.(17.&8.))Pm,P,(17.&40.)(<.(17.&8.))Pa,(17.&40.)P,Pi,$19.P,(1>.R1.(23.(17.&8.)R4.))(;.$13.A1.VD,(1;.R3.R2.)$15.)(;.P,(17.&40.)(<.(17.&8.))(24.(1=.R3.)R2.R4.)(1=.(24.R3.R2.R4.)))")
(* [comment removed for export] *).
Proof.
  induction bs as [|b bs IH]; intros m a HD; [reflexivity|].
  cbn [write_to_mem].
  assert (HDa : D a = true) by (rewrite <- (wplus_0 a); apply HD; cbn; lia).
  replace (fun a0 : word => if bv_eqb a0 a then Some b else restrict m a0)
     with (restrict (fun a0 : word => if bv_eqb a0 a then Some b else m a0)).
  - apply IH. intros i Hi. rewrite <- wplus_S. apply HD. cbn; lia.
  - apply functional_extensionality. intros x. unfold restrict.
    destruct (bv_eqb x a) eqn:E; [|reflexivity].
    unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. rewrite HDa. reflexivity.
Qed.

#[using="Type"] Lemma write_to_mem_outside : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pbs,(9.(17.&8.))Pm,P,(17.&40.)(<.(17.&8.))Pa,(17.&40.)Px,(17.&40.)P,Pi,$19.P,(1>.R1.(23.(17.&8.)R5.))(25.(;.(17.&40.)R3.(1;.R4.R2.)))(;.(<.(17.&8.))(24.R4.R3.R5.R2.)A1.R4.R2.)")
(* [comment removed for export] *).
Proof.
  induction bs as [|b bs IH]; intros m a x Hx; [reflexivity|].
  cbn [write_to_mem]. rewrite IH.
  - destruct (bv_eqb x a) eqn:E; [|reflexivity].
    exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. apply (Hx 0%nat); [cbn; lia|]. rewrite wplus_0. exact E.
  - intros i Hi. rewrite <- wplus_S. apply Hx. cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma width_bytes_le8 : forall n, (width_bytes n <= 8)%nat.
Proof.
  intros n. unfold width_bytes.
  repeat (lazymatch goal with |- context [match ?x with _ => _ end] => destruct x | _ => fail end); cbn; lia.
Qed.

#[using="Dseg SEGTOP"] Lemma interp_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pt,$26.Pm,P,(17.&40.)(<.(17.&8.))Pc,$27.PmD',P,(17.&40.)(<.(17.&8.))Pacc,(9.$28.)P,(;.(29.(2:.(2;.$27.P,(17.&40.)(<.(17.&8.)))))(2<.Vsegs,R5.(1=.R4.))(2=.(2:.(2;.$27.P,(17.&40.)(<.(17.&8.))))(2>.(2;.$27.P,(17.&40.)(<.(17.&8.)))(2?.$27.P,(17.&40.)(<.(17.&8.))R3.R2.)R1.)))(21.P,(17.&40.)(<.(17.&8.))Lm',P,(17.&40.)(<.(17.&8.))(10.(;.(29.(2:.(2;.$27.P,(17.&40.)(<.(17.&8.)))))(2<.Vsegs,R7.R6.)(2=.(2:.(2;.$27.P,(17.&40.)(<.(17.&8.))))(2>.(2;.$27.P,(17.&40.)(<.(17.&8.)))(2?.$27.P,(17.&40.)(<.(17.&8.))R5.R1.)R3.)))(10.(;.P,(17.&40.)(<.(17.&8.))R4.(1=.R1.))(10.Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))A1.R3.R2.A1.R8.R2.)(31.VD,R3.)))))")
(* [comment removed for export] *).
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; intros m c mD' acc H; cbn [interp_eff_accesses] in H |- *;
    try discriminate.
  - injection H as <- <- <-. exists m. repeat split; auto. constructor.
  - destruct (ov_read_bytes segs (restrict m) a (width_bytes n)) as [bs|] eqn:R; [|discriminate].
    destruct (ov_read_bytes_restrict _ _ _ _ R) as [-> HD].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (restrict m)) as [[[c1 m1] acc1]| |] eqn:K; try discriminate.
    cbn in H. injection H as <- <- <-.
    destruct (IH _ _ _ _ _ K) as (m' & -> & HmD & Hout & HaccD). cbn.
    exists m'. repeat split; auto. constructor; [|exact HaccD]. cbn. split; [apply width_bytes_le8 | exact HD].
  - destruct (store_ok segs (restrict m) a (width_bytes n)) eqn:SO; [|discriminate].
    destruct (store_ok_restrict _ _ _ SO) as [-> HD].
    rewrite write_to_mem_restrict in H.
    2:{ intros i Hi. apply HD. rewrite length_Z_to_le_bytes in Hi. exact Hi. }
    destruct (interp_eff_accesses segs k (restrict (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))) as [[[c1 m1] acc1]| |] eqn:K; try discriminate.
    cbn in H. injection H as <- <- <-.
    destruct (IH _ _ _ _ K) as (m' & -> & HmD & Hout & HaccD). cbn.
    exists m'. repeat split; auto.
    + intros x Hx. rewrite (Hout x Hx). apply write_to_mem_outside. intros i Hi E.
      rewrite length_Z_to_le_bytes in Hi. specialize (HD i Hi). subst x. congruence.
    + constructor; [|exact HaccD]. cbn. split; [apply width_bytes_le8 | exact HD].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_mem (ms : machine_state) (m : word -> option byte) : machine_state := ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "(32.(33.O2.)(34.O2.)(35.O2.)(36.O2.)(37.O2.)(38.O2.)O1.(39.O2.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rms (ms : machine_state) : machine_state := set_mem ms (restrict (ms_mem ms)).
Definition unr (msD : machine_state) (m0 : word -> option byte) : machine_state := set_mem msD (unrestrict (ms_mem msD) m0).

#[using="Type"] Lemma set_mem_mem : forall ms, set_mem ms (ms_mem ms) = ms.
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma ms_mem_set_mem : forall ms m, ms_mem (set_mem ms m) = m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma rms_unr : forall msD m0, (forall a, D a = false -> ms_mem msD a = None) -> rms (unr msD m0) = msD.
Proof.
  intros msD m0 H. unfold rms, unr. cbn. rewrite restrict_unrestrict by exact H. destruct msD; reflexivity.
Qed.

#[using="Dseg SEGTOP"] Lemma decode_exec_accesses_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pms,$3:.Pw,(17.&20.)Pms1,$3:.Pacc,(9.$28.)P,(;.(29.(2:.$3:.))(3;.Vsegs,(3<.R4.)R3.)(2=.(2:.$3:.)(2>.$3:.R2.R1.)))(21.P,(17.&40.)(<.(17.&8.))Lm1,P,(17.&40.)(<.(17.&8.))(10.(;.(29.(2:.$3:.))(3;.Vsegs,R6.R5.)(2=.(2:.$3:.)(2>.$3:.(3=.R4.R1.)R3.)))(10.(;.P,(17.&40.)(<.(17.&8.))(3>.R4.)(1=.R1.))(10.Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))A1.R3.R2.(3>.R8.R2.))(31.VD,R3.)))))")
(* [comment removed for export] *).
Proof.
  intros ms w ms1 acc H. unfold decode_exec_accesses in H |- *.
  destruct (is_ecall w).
  - injection H as <- <-. exists (ms_mem ms). cbn. split; [destruct ms; reflexivity|].
    repeat split; auto. constructor.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [rms set_mem ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom] in H.
    destruct (interp_eff_accesses segs _ (restrict (ms_mem ms))) as [[[c mD'] acc0]| |] eqn:I; try discriminate.
    cbn in H. injection H as <- <-.
    destruct (interp_restrict _ _ _ _ _ I) as (m' & -> & HmD & Hout & HaccD). cbn.
    exists m'. repeat split; auto.
Qed.

#[using="Dseg SEGTOP"] Theorem step_accesses_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pms,$3:.Pms1,$3:.Pacc,(9.$28.)P,(;.(29.(2:.$3:.))(3?.Vsegs,(3<.R3.))(2=.(2:.$3:.)(2>.$3:.R2.R1.)))(21.P,(17.&40.)(<.(17.&8.))Lm1,P,(17.&40.)(<.(17.&8.))(10.(;.(29.(2:.$3:.))(3?.Vsegs,R5.)(2=.(2:.$3:.)(2>.$3:.(3=.R4.R1.)R3.)))(10.(;.P,(17.&40.)(<.(17.&8.))(3>.R4.)(1=.R1.))(10.Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))A1.R3.R2.(3>.R7.R2.))(31.VD,R3.)))))")
(* [comment removed for export] *).
Proof.
  intros ms ms1 acc H. unfold step_accesses in H |- *.
  change (ms_pc (rms ms)) with (ms_pc ms) in H.
  change (ms_mem (rms ms)) with (restrict (ms_mem ms)) in H.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in H.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (decode_exec_accesses_restrict _ _ _ _ H)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_accesses_restrict _ _ _ _ H)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_accesses_restrict _ _ _ _ H)|].
  (* [comment removed for export] *)
  exfalso. revert H. unfold fetch_failure.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)); [discriminate|]. cbn zeta.
  match goal with |- context [if ?b then MachineFault else MachineUnmodeled] => destruct b; discriminate end.
Qed.

(* [comment removed for export] *)
#[using="Dseg SEGTOP"] Corollary step_accesses_restrict' : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pms,$3:.Pms1,$3:.Pacc,(9.$28.)P,(;.(29.(2:.$3:.))(3?.Vsegs,(3<.R3.))(2=.(2:.$3:.)(2>.$3:.R2.R1.)))(10.(;.(29.(2:.$3:.))(3?.Vsegs,R4.)(2=.(2:.$3:.)(2>.$3:.(40.R3.(3>.R4.))R2.)))(10.(;.$3:.(3<.(40.R3.(3>.R4.)))R3.)(10.Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))(3>.(40.R5.(3>.R6.))R2.)(3>.R6.R2.))(31.VD,R2.))))")
(* [comment removed for export] *).
Proof.
  intros ms ms1 acc H.
  destruct (step_accesses_restrict _ _ _ H) as (m1 & Hs & Hm & Hout & HaccD).
  assert (E : unr ms1 (ms_mem ms) = set_mem ms1 m1).
  { unfold unr. f_equal. apply functional_extensionality. intros a. unfold unrestrict.
    rewrite Hm. unfold restrict. destruct (D a) eqn:Da; [reflexivity|]. symmetry. apply Hout. exact Da. }
  rewrite E. split; [exact Hs|]. split.
  - unfold rms. cbn. rewrite <- Hm. destruct ms1; reflexivity.
  - split; [|exact HaccD]. cbn. exact Hout.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ToAccOk.
Variable L : asan_layout.
Variable CS : Z -> Prop.
(* [comment removed for export] *)
Hypothesis DOK : forall a, D a = true -> aok_addr L CS (bv_unsigned a).
Hypothesis D0 : D (Z_to_bv 64 0) = false.

#[using="D0"] Lemma rangeD_nowrap : forall a n, rangeD D a n -> (0 < n)%nat -> bv_unsigned a + Z.of_nat n <= 2^64.
Proof.
  intros a n [Hn HD] Hpos.
  pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  destruct (Z.leb_spec0 (bv_unsigned a + Z.of_nat n) (2^64)) as [|Hw]; [assumption|exfalso].
  (* [comment removed for export] *)
  set (i0 := Z.to_nat (2^64 - bv_unsigned a)).
  assert (Hi0 : (i0 < n)%nat) by (unfold i0; lia).
  specialize (HD i0 Hi0).
  replace (wplus a i0) with (Z_to_bv 64 0) in HD; [congruence|].
  unfold wplus. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Zplus_mod_idemp_r. unfold i0. rewrite Z2Nat.id by lia.
  replace (bv_unsigned a + (2^64 - bv_unsigned a)) with (2^Z.of_N 64) by (cbn; lia).
  rewrite Z.mod_same; [reflexivity|]. cbn; lia.
Qed.

#[using="DOK D0"] Lemma accD_acc_ok : forall acc, accD D acc -> acc_ok L CS acc.
Proof.
  intros acc H z (a & n & HIn & Hz).
  apply Forall_forall with (x := (a, n)) in H; [|exact HIn]. cbn in H.
  pose proof H as [Hn HD].
  assert (Hpos : (0 < n)%nat) by lia.
  pose proof (rangeD_nowrap a n H Hpos) as NW.
  pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  set (i := Z.to_nat (z - bv_unsigned a)).
  assert (Hi : (i < n)%nat) by (unfold i; lia).
  specialize (HD i Hi). apply DOK in HD.
  replace (bv_unsigned (wplus a i)) with z in HD; [exact HD|].
  unfold wplus. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Zplus_mod_idemp_r. unfold i. rewrite Z2Nat.id by lia. cbn in NW |- *. rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Dseg SEGTOP DOK D0"] Lemma mstep_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "Pms,$3:.Pms1,$3:.P,(41.Vsegs,(3<.R2.)R1.)(10.(42.Vsegs,VL,VCS,R3.(40.R2.(3>.R3.)))(10.(;.$3:.(3<.(40.R2.(3>.R3.)))R2.)Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))(3>.(40.R4.(3>.R5.))R2.)(3>.R5.R2.))))")
(* [comment removed for export] *).
Proof.
  intros ms ms1 [Hsvc Hstep].
  change (ms_svc_pending ms = None) in Hsvc.
  rewrite <- drop_step_accesses in Hstep.
  destruct (step_accesses segs (rms ms)) as [[ms1' acc]| |] eqn:SA; cbn in Hstep; try discriminate.
  injection Hstep as ->.
  destruct (step_accesses_restrict' _ _ _ SA) as (Hs & Hr & Hout & HaccD).
  split; [|split; [exact Hr|exact Hout]].
  split; [exact Hsvc|]. exists acc. split; [exact Hs|]. apply accD_acc_ok. exact HaccD.
Qed.

(* [comment removed for export] *)
#[using="Dseg SEGTOP DOK D0"] Lemma msteps_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "PmsD,$3:.Pms1,$3:.P,(43.Vsegs,R2.R1.)Pms,$3:.P,(;.$3:.R4.(3<.R1.))(21.$3:.Lms1',$3:.(10.(44.Vsegs,VL,VCS,R3.R1.)(10.(;.$3:.(3<.R1.)R5.)Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))(3>.R3.R2.)(3>.R5.R2.)))))")
(* [comment removed for export] *).
Proof.
  intros msD ms1 H. induction H as [msD | msD msM ms1 Hst Hrest IH]; intros ms ->.
  - exists ms. split; [constructor|]. split; [reflexivity|]. auto.
  - destruct (mstep_restrict _ _ Hst) as (HA & Hr & Hout).
    destruct (IH (unr msM (ms_mem ms)) (eq_sym Hr)) as (ms1' & HA' & Hr' & Hout').
    exists ms1'. split; [eapply mstepsA_cons; eauto|]. split; [exact Hr'|].
    intros a Ha. rewrite (Hout' a Ha). apply Hout. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Dseg SEGTOP DOK D0"] Lemma smsteps_restrict : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "PmsD,$3:.Pms1,$3:.P,(45.Vsegs,R2.R1.)Pms,$3:.P,(;.$3:.R4.(3<.R1.))(21.$3:.Lms1',$3:.(10.(44.Vsegs,VL,VCS,R3.R1.)(10.(;.$3:.(3<.R1.)R5.)Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))(3>.R3.R2.)(3>.R5.R2.)))))")
(* [comment removed for export] *).
Proof.
  intros msD ms1 H. induction H as [msD | msD msM ms1 Hsvc Hstep Hrest IH]; intros ms ->.
  - exists ms. split; [constructor|]. split; [reflexivity|]. auto.
  - destruct (mstep_restrict ms msM (conj Hsvc Hstep)) as (HA & Hr & Hout).
    destruct (IH (unr msM (ms_mem ms)) (eq_sym Hr)) as (ms1' & HA' & Hr' & Hout').
    exists ms1'. split; [eapply mstepsA_cons; eauto|]. split; [exact Hr'|].
    intros a Ha. rewrite (Hout' a Ha). apply Hout. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Dseg SEGTOP DOK D0"] Lemma evt_restrict_evtA : ltac2:(CDefT.buildp (gd_tbl_Restrict ()) "PQ,P,$3:.SpPms,$3:.P,(46.Vsegs,R2.(3<.R1.))(47.Vsegs,VL,VCS,Lms1',$3:.(10.A1.R4.(3<.R1.)Pa,(17.&40.)P,(;.$13.A1.VD,R1.$30.)(;.(<.(17.&8.))(3>.R3.R2.)(3>.R5.R2.)))R2.)")
(* [comment removed for export] *).
Proof.
  intros Q ms (ms1 & Hm & HQ).
  destruct (msteps_restrict _ _ Hm ms eq_refl) as (ms1' & HA & Hr & Hout).
  exists ms1'. split; [exact HA|]. split; [rewrite Hr; exact HQ | exact Hout].
Qed.

End ToAccOk.
End Restrict.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
