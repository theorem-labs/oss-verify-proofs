(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg AgentLib Hoare RefLayout
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanNodesAux () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kentry"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kwritable"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.estart"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SA"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.regs_ok"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.edenot"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sr_upd"; "nb_lt"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ev"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cs_ok"; "OSSVerify.KrLib.ABoot.AsanAcct.lazy_cover"; "NodesD.Hv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.allowA"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.hid"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.ATOP"; "OSSVerify.KrLib.ABoot.AsanAcct.mrestrict"; "OSSVerify.KrLib.ABoot.StoreOk.mem_grows"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.Mr"].



Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

Lemma reg_neq : forall a b : Z, 0 <= a < 32 -> 0 <= b < 32 -> a <> b -> (Z_to_bv 5 a : bv 5) <> Z_to_bv 5 b.
Proof.
  intros a b Ha Hb Hne Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
  rewrite !Z.mod_small in Heq by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac rif :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?u else ?v] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let c := eval vm_compute in (bv_eqb a b) in
              lazymatch c with
              | true => change (if bv_eqb a b then u else v) with u
              | false => change (if bv_eqb a b then u else v) with v
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
Lemma signed12_0 : bv_signed (0 : bv 12) = 0. Proof. reflexivity. Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_eqb_sound : forall SEGS E M k n m,
  know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros SEGS E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
    cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "Psegs,(0.$1.)PE,$2.PM,P,(3.&40.)(4.(3.&8.))Pallkn,(0.$5.)Pk,(0.$5.)Pb,$6.Poff,$7.Pn,$7.P,(8.R8.R7.R6.R5.)P,(8.R9.R8.R7.R5.)P,(9.$:.(;.R7.R6.R5.R4.R3.)$<.)P,(=.=R4.)(>.(9.$:.(?.R<.R:.(10.&40.(11.R;.(12.R7.R6.)))(13.R5.))$<.)(>.(=.=(11.R;.(12.R7.R6.)))(=.(14.(11.R;.(12.R7.R6.))R5.)(15.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros segs E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
  destruct K; try exact (IH Hrest H).
  lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
  { intros A B. split; [|lia].
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
    pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
  - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
    apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
    apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
    destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
    unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall segs E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros segs E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
Lemma reg_lit5 : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof.
  intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma regs_ok_post2 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "PE,$2.Psr,(0.$6.)PR,(16.&5.(3.&40.))PR',(16.&5.(3.&40.))Pn1,$17.Pr1,(3.&5.)Pe1,$6.Pn2,$17.Pr2,(3.&5.)Pe2,$6.P,(18.R:.R9.R8.)P,(>.(19.#0.R7.)(19.R7.#20.))P,(>.(19.#0.R5.)(19.R5.#20.))P,(1:.(9.$17.R9.R6.))P,(9.$7.(1;.&5.R9.)(1<.R:.))P,(9.$7.(1;.&5.R7.)(1<.R8.))P,(9.(3.&40.)(1=.R=.R;.)(1>.R10.R:.))P,(9.(3.&40.)(1=.R>.R9.)(1>.R11.R8.))P,Pr,(3.&5.)P,(1:.(9.(3.&5.)R1.R>.))P,(1:.(9.(3.&5.)R2.R<.))(9.(3.&40.)(1=.R12.R3.)(1=.R13.R3.))(18.R13.(1?.(1?.R12.R?.R=.)R<.R:.)R10.)")
(* [comment removed for export] *).
Proof.
  intros E sr R R' n1 r1 e1 n2 r2 e2 HR Hn1 Hn2 Hne U1 U2 G1 G2 Gr.
  assert (E1 : r1 = Z_to_bv 5 (Z.of_nat n1)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U1).
  assert (E2 : r2 = Z_to_bv 5 (Z.of_nat n2)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U2).
  pose proof (regs_ok_set_n E _ _ n2 e2 (edenot E e2) (regs_ok_set_n E sr R n1 e1 (edenot E e1) HR Hn1 eq_refl) Hn2 eq_refl) as K.
  rewrite <- E1, <- E2 in K.
  assert (Z1 : r1 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U1 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
  assert (Z2 : r2 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U2 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
  assert (Z12 : r1 <> r2) by (intros H0; apply (f_equal bv_unsigned) in H0; lia).
  intros r. rewrite <- (K r).
  destruct (bv_eqb r r2) eqn:Q2.
  { unfold bv_eqb in Q2. apply Z.eqb_eq in Q2. apply bv_eq in Q2. subst r. rewrite getr_same by exact Z2. exact G2. }
  assert (N2 : r <> r2) by (intros ->; rewrite bv_eqb_refl in Q2; discriminate).
  rewrite (getr_other _ r2 _ r N2).
  destruct (bv_eqb r r1) eqn:Q1.
  { unfold bv_eqb in Q1. apply Z.eqb_eq in Q1. apply bv_eq in Q1. subst r. rewrite getr_same by exact Z1. exact G1. }
  assert (N1 : r <> r1) by (intros ->; rewrite bv_eqb_refl in Q1; discriminate).
  rewrite (getr_other _ r1 _ r N1). apply Gr; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint nb_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt b a && nb_lt b c
  | EExt _ _ _ a => nb_lt b a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_ev_agree : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "Pb,$17.PE,$2.PE',$2.Pe,$6.P,(9.$:.(20.R4.R1.)$<.)P,Pn,$17.P,(19.R1.R6.)(9.(3.&40.)(21.R6.R2.)(21.R5.R2.))(9.(3.&40.)(1>.R5.R3.)(1>.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(* [comment removed for export] *)
Lemma fetch_lit : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "Psegs,(0.$1.)Pz,$7.Pw,(3.&40.)Px,(3.&20.)P,(9.$7.(1;.&40.R2.)R3.)P,(9.(4.(3.&20.))(22.R5.R3.)(23.(3.&20.)R2.))(9.(4.(3.&20.))(22.R6.(10.&40.R5.))(23.(3.&20.)R3.))")
(* [comment removed for export] *).
Proof.
  intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
  apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma with_ss_idem : forall cs s1 s2, with_ss (with_ss cs s1) s2 = with_ss cs s2.
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : forall cs s, a_ss (with_ss cs s) = s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_le' : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "Pa,(3.&40.)(>.(=.(1;.&40.(24.R1.))(1;.&40.R1.))(>.(25.(1;.&40.R1.)(14.(1;.&40.(24.R1.))+1000.))(9.$7.(26.(1;.&40.(24.R1.))+1000.)=)))")
(* [comment removed for export] *).
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_in_ranges_bounds' : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "Pa,(3.&40.)Pl,(0.(27.(3.&40.)(3.&40.)))Plo,$7.Phi,$7.P,(28.(27.(3.&40.)(3.&40.))Liv,(27.(3.&40.)(3.&40.))(>.(=.R3.(1;.&40.(29.(3.&40.)(3.&40.)R1.)))(=.(14.(1;.&40.(29.(3.&40.)(3.&40.)R1.))(1;.&40.(2:.(3.&40.)(3.&40.)R1.)))R2.))R3.)P,(9.$:.(2;.(24.R5.)R4.)$<.)(>.(=.R4.(1;.&40.R6.))(=.(14.(1;.&40.R6.)+1.)(14.R3.+???.)))")
(* [comment removed for export] *).
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

Lemma A_wf_allowA' : forall A E cs, A_wf (allowA A E cs).
Proof.
  intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  assert (SH : forall p, iv = (pagedown (sh_lo A E p), pageup (sh_hi A E p)) -> (fst iv <= snd iv)%Z /\ (fst iv mod page_size = 0)%Z /\ (snd iv mod page_size = 0)%Z).
  { intros p ->. cbn [fst snd]. unfold page_size.
    pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
    pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  apply in_app_iff in Hin as [Hin|Hin]; apply in_flat_map in Hin as [p [_ Hin]].
  - unfold allow1 in Hin.
    pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
    destruct Hin as [<-|[E1|[]]]; [cbn [fst snd]; unfold page_size | exact (SH p (eq_sym E1))].
    pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - unfold allow_sh in Hin. destruct Hin as [E1|[]]. exact (SH p (eq_sym E1)).
Qed.

Section NodesD.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis HULL_cov : APS.hull_cov SEGS A.   (* [comment removed for export] *)
  Variable SP0 : Z.                        (* [comment removed for export] *)
  Hypothesis SP0_ok : APS.sp0_ok SP0.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "PE,$2.PM,Px,(3.&40.)(4.(3.&8.))PM',Px,(3.&40.)(4.(3.&8.))P,Pa,(3.&40.)P,(9.$:.A2.VargH,R4.R1.$<.)(9.(4.(3.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(3.&40.)P,(=.VSP0,(1;.&40.R1.))P,(1:.(9.(4.(3.&8.))A1.R5.R2.(2<.(3.&8.))))(1:.(9.(4.(3.&8.))A1.R5.R3.(2<.(3.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis SINV_sp : forall E M, SINV E M -> APS.uE_sp0 E = SP0.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A SP0 E cs model a).

  #[using="Type"] Lemma Hv_hid : forall E cs model a, Hv E cs model a = true -> hid A SP0 argH E cs model a = true.
  Proof. intros E cs model a H. unfold hid, Hv in *. rewrite H. apply orb_true_r. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma Hv_high : forall E cs model (a : word), ATOP SP0 <= bv_unsigned a -> Hv E cs model a = false.
  Proof.
    intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
    replace (ATOP SP0 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
    rewrite orb_true_r. reflexivity.
  Qed.

  #[using="Type"] Lemma Hv_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> Hv E cs model a = false.
  Proof. intros E cs model a Ha. unfold Hv, vis. rewrite Ha. reflexivity. Qed.

  #[using="HULL_ok"] Lemma lazy_cover_vis : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "PE,$2.Pcs,$2=.PR,(16.&5.(3.&40.))PFULL,P,(3.&40.)(4.(3.&8.))Pmodel,$2>.P,(2?.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.R4.R3.R2.R1.)(30.(31.R6.R5.R2.)(32.R2.)(33.VA,R6.R5.))")
(* [comment removed for export] *).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
    apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
    apply orb_prop in Hv0 as [Hv0|Hv0].
    - (* [comment removed for export] *)
      exfalso.
      pose proof Hlz as Hlz0. unfold page_in_ranges in Hlz0. apply existsb_exists in Hlz0 as [iv [Hin Hb]].
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
      pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as [L1 L2]. unfold hull_apart in L1.
      pose proof (page_base_le' w) as (P1 & P2 & P3). unfold page_size in *.
      apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_hull in Hv0. apply andb_prop in Hv0 as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2. lia.
      + apply Z.leb_le in Hv0. lia.
    - apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz in Hv0. cbn [negb orb] in Hv0.
      pose proof (page_base_le' w) as (P1 & P2 & P3).
      unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
        * apply in_or_app. left. apply in_flat_map. exists p. split; [exact Hin|]. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      + unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
        * apply in_or_app. left. apply in_flat_map. exists p. split; [exact Hin|]. right. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  #[using="HULL_ok"] Lemma lazy_cover_hid : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "PE,$2.Pcs,$2=.PR,(16.&5.(3.&40.))PFULL,P,(3.&40.)(4.(3.&8.))Pmodel,$2>.P,(2?.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.R4.R3.R2.R1.)(30.(34.VA,VSP0,VargH,R6.R5.R2.)(32.R2.)(33.VA,R6.R5.))")
(* [comment removed for export] *).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. apply (lazy_cover_vis E cs R FULL model HC w Hlz).
    unfold Hv. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hh]. exact Hh.
  Qed.

  #[using="SEGS_in_hull"] Lemma H_off_segments_vis : forall E cs model, H_off_segments SEGS (Hv E cs model).
  Proof.
    intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
    apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
    apply SEGS_in_hull. exact Hh.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma mrestrict_Hv_high : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "PE,$2.Pcs,$2=.Pmodel,$2>.PFULL,P,(3.&40.)(4.(3.&8.))Pa,(3.&40.)P,(=.(35.VSP0,)(1;.&40.R1.))(9.(4.(3.&8.))(36.(31.R6.R5.R4.)R3.R2.)A1.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma Mr_grows_Hv : ltac2:(CDefT.buildp (gd_tbl_AsanNodesAux ()) "PE,$2.Pcs,$2=.Pmodel,$2>.PFULL,P,(3.&40.)(4.(3.&8.))(37.(38.VA,VSP0,VargH,R4.R3.R2.R1.)(36.(31.R4.R3.R2.)R1.))")
(* [comment removed for export] *).
  Proof.
    intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
    destruct (argH E a), (vis A SP0 E cs model a); cbn; auto.
  Qed.

  #[using="Type"] Lemma munrestrict_mrestrict : forall (H : word -> bool) FULL, munrestrict H FULL (mrestrict H FULL) = FULL.
  Proof.
    intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
  Qed.

End NodesD.
