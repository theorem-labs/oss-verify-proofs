(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg AgentLib Hoare RefLayout
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib4Init5Logicm02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~n96edenotn94exprk14boolk16optionk14true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeu17Segment79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~hi07len_eqbn93envn96kentry79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~hn87know_okn92SAhn86estart46Stdlib6ZArith6BinInt1Zht92lem03and01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsig08store_okhi09kwritableht93addht93powht96to_nathf7Z_to_bvhi08kimg_cutht96of_natk13nat37Corelib4Init5Peanoioe2lthfbbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ir64getrm03not3h5LinuxProcessSemantics5Riscv7Preludeivf5bvmapn96sr_updhn87regs_okn92ev69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanNodesAux~~~~~~jk75nb_ltk14Someig0afetch_wordhi07with_sshi03acsn99sym_statehi04a_ss3h5LinuxProcessSemanticsfLinuxProcessSem5Statejsa9page_baseht92ltht96modulo69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~kh54A_wfhi06atable79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~km26allowAjsa5Modelk14negbkm23visk15false79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanNodesAux6NodesD~~~~~~ksf2Hvkm23TOPjsa9m_vm_lazykh5alazy_coverkm25cs_okkh5eH_off_segmentskh59mrestrictkm22Mr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~lmb9mem_growskh5bmunrestrict3h5LinuxProcessSemanticsfLinuxProcessSem2Fsls12Fsk14Noneig0cfind_segmentkm27in_hullkm27hull_ok" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_eqb_sound : ltac2:(zQ "e0!h9!jc!l9!n4!ra!s3!sa!t1!ta!hh6!hle!hm9!hmf!hrf>4SEGS@1$2$9>1E$b>1M>0@1$1@1$0#k0@1$7@1$1@1$0#8>1k@1$2$c>1n$5>1m$5>0@4$d^6^5^4^3>0@3$3$6@3$a^4^3^2$8@3$3@1$1@1$0#k0@2$4^7^4@2$4^7^3").
Proof.
  intros SEGS E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
    cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : ltac2:(zQ "h70!l9!h9!hsa!hsf!hv1!sa!ta!hv7!n4!hvd!hmf!hrf!jc!t1!hh6!ij7!ik3!hm9!s3!il0!il7!ile!im8>4segs@1$0$e>1E$h1>1M>0@1$c@1$1#k0@1$d@1$c@1$1#8>5allkn@1$0$a>1k@1$0$a>1b$h2>3off$9>1n$9>0@4$b^8^7^6^5>0@4$b^9^8^7^5>0@3$8$5@5$h0^7^6^5^4^3$6>0@2$4Z^4@2$7@3$8$5@4$f^c^a@2$h6@1$1#k0@2$3^b@2$2^7^6@1$h5^5$6@2$7@2$4Z@2$3^b@2$2^7^6@2$4@2$h3@2$3^b@2$2^7^6^5@2$h4+2+k0").
Proof.
  intros segs E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
  destruct K; try exact (IH Hrest H).
  lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. ndestruct Hfl' as (F1 & F2 & F3 & F4).
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
Lemma kimg_cut_sound : ltac2:(zQ "a0!l9!h9!hvd!hrf!jc!t1!hh6!in2!hm9!hmf>4segs@1$0$6>1E$8>1M>0@1$4@1$1#k0@1$5@1$4@1$1#8>1k@1$0$9>1a$2>1n$2>0@4$3^6^5^4^3@4$3^7^6^5@3$7^4^3^2").
Proof.
  intros segs E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. ndestruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
Lemma reg_lit5 : ltac2:(zQ "80!h9!ine!io8!n4!iq2!hvd!im8!iq8>1n$2>0@2$4^1Ni0@3$3$5@2$7@1$0#5@2$6@1$0#5@1$1^2@1$1^2").
Proof.
  intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma regs_ok_post2 : ltac2:(zQ "h20!h9!jc!n4!iq2!iv1!io8!iv9!s3!hv7!hvd!ji5!ra!jie!jj7!ine!iq8!l9!hm9>1E$h1>2sr@1$h0$7>1R@2$a@1$0#5@1$1@1$0#k0>2R'@2$a@1$0#5@1$1@1$0#k0>2n1$5>2r1@1$1@1$0#5>2e1$7>2n2$5>2r2@1$1@1$0#5>2e2$7>0@3$d^a^9^8>0@2$8@2$3N0^7@2$3^7Ni0>0@2$8@2$3N0^5@2$3^5Ni0>0@1$6@3$2$5^9^6>0@3$2$9@2$f@1$0#5^9@1$e^a>0@3$2$9@2$f@1$0#5^7@1$e^8>0@3$2@1$1@1$0#k0@2$4^d^b@2$b^h0^a>0@3$2@1$1@1$0#k0@2$4^e^9@2$b^h1^8>0>1r@1$1@1$0#5>0@1$6@3$2@1$1@1$0#5^1^e>0@1$6@3$2@1$1@1$0#5^2^c@3$2@1$1@1$0#k0@2$4^h2^3@2$4^h3^3@3$d^h3@3$c@3$c^h2^f^d^c^a^h0").
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

Lemma edenot_ev_agree : ltac2:(zQ "c0!n4!io8!h9!ra!hm9!jk2!jc!sa!ta!iq2!jo6!s3>1b$1>1E$4>2E'$4>1e$b>0@3$0$7@2$a^4^1$8>0>1n$1>0@2$9^1^6@3$0@1$6@1$2#k0@2$5^6^2@2$5^5^2@3$0@1$6@1$2#k0@2$3^5^3@2$3^4^3").
Proof.
  intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(* [comment removed for export] *)
Lemma fetch_lit : ltac2:(zQ "b0!h9!jc!n4!jof!t1!hvd!jp6!l9!hh6!im8!iq8>4segs@1$7$8>1z$5>1w@1$1@1$0#k0>1x@1$1@1$0#i0>0@3$2$5@2$a@1$0#k0^2^3>0@3$2@1$4@1$1@1$0#i0@2$6^5^3@2$3@1$1@1$0#i0^2@3$2@1$4@1$1@1$0#i0@2$6^6@2$9@1$0#k0^5@2$3@1$1@1$0#i0^3").
Proof.
  intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
  apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma with_ss_idem : ltac2:(zQ "40!jq4!jqf!jr6!n4>2cs$1>2s1$2>2s2$2@3$3$1@2$0@2$0^3^2^1@2$0^3^1").
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : ltac2:(zQ "50!jr6!n4!js2!jqf!jq4>2cs$3>1s$0@3$1$0@1$2@2$4^2^1^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_le' : ltac2:(zQ "b0!h9!iq8!jv8!hv7!n4!hvd!il0!hv1!kg5!kgb!jc>1a@1$a@1$0#k0@2$3@2$7@2$1@1$0#k0@1$2^1@2$1@1$0#k0^1@2$3@2$8@2$1@1$0#k0^1@2$6@2$1@1$0#k0@1$2^1+hgg0@3$4$5@2$9@2$1@1$0#k0@1$2^1+hgg0Z").
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma A_wf_allowA' : ltac2:(zQ "50!kl0!jqf!kl8!kq6!hm9>1A$2>1E$4>2cs$1@1$0@3$3^3^2^1").
Proof.
  intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
  pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
  - pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Section NodesD.
  (* [comment removed for export] *)
  Variable SEGS : ltac2:(zQ "20!l9!hh6@1$0$1").
  Variable A : ltac2:(zQ "10!kl8$0").
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : ltac2:(zQ "40!h9!jc!t1!hm9>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
  Variable argH : ltac2:(zQ "40!sa!h9!hm9!jc>0$2>0@1$3@1$1#k0$0").
  Variable FS0 : ltac2:(zQ "10!luc$0").
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : ltac2:(zQ "b0!h9!n4!hh6!iq8!lv2!sa!ks7!t1!lv9!mg9!jc>1a@1$a@1$0#k0>0@3$1$5@2$9?1A@2$3@1$0#k0^1$6@3$1@1$7$2@3$8?4SEGS@2$3@1$0#k0^2+1@1$4$2").
  Hypothesis HULL_ok : ltac2:(zQ "10!mh4@1$0?1A").
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition Hv : ltac2:(zQ "60!sa!h9!kr0!jqf!hm9!jc>1E$4>2cs$3>5model$2>0@1$5@1$1#k0$0") := ltac2:(zQ "70!kr9!h9!kr0!jqf!ks0!hm9!jc\1E$5\2cs$3\5model$2\1a@1$6@1$1#k0@1$0@5$4?1A^4^3^2^1").

  (* [comment removed for export] *)
  Lemma Hv_high : ltac2:(zQ "c0!h9!sa!ks7!n4!kr0!lh5!jqf!lhb!hm9!hv1!jc!iq8>1E$8>2cs$6>5model$4>1a@1$a@1$0#k0>0@2$9@1$7^2@2$b@1$0#k0^1@3$3$1@4$5^5^4^3^2$2").
  Proof.
    intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
    replace (TOP model <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
    rewrite orb_true_r. reflexivity.
  Qed.

  Lemma lazy_cover_vis : ltac2:(zQ "c0!h9!jc!t1!kr0!li2!ji5!lif!lh5!jqf!kq6!ljd!hm9>1E$b>2cs$8>1R@2$5@1$0#5@1$1@1$0#k0>4FULL>0@1$1@1$0#k0@1$2@1$1@1$0#8>5model$3>0@b$a?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^5^4^3^2^1@3$6@3$7^6^5^2@1$4^2@3$9?1A^6^5").
  Proof.
    intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
    apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
    pose proof Hlz as Hlz0.
    unfold page_in_ranges in Hlz. apply existsb_exists in Hlz as [iv [Hin Hb]].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as [L1 L2].
    npose (page_base_le' w) as (P1 & P2 & P3). unfold page_size in Hb2.
    pose proof HULL_ok as HU; unfold hull_ok in HU; ndestruct HU as (H0 & H1 & H2 & H3).
    apply orb_prop in Hv0 as [Hv0|Hv0].
    - exfalso. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_hull in Hv0. apply andb_prop in Hv0 as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        destruct L1 as [L1|L1]; lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + apply Z.leb_le in Hv0. lia.
    - apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz0 in Hv0. cbn [negb orb] in Hv0.
      unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hinp Hb]]. apply andb_prop in Hb as [Hb3 Hb4].
        apply Z.leb_le in Hb3. apply Z.ltb_lt in Hb4.
        exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hinp|]. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      + unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hinp Hb]]. apply andb_prop in Hb as [Hb3 Hb4].
        apply Z.leb_le in Hb3. apply Z.ltb_lt in Hb4.
        exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hinp|]. right. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)

  Lemma H_off_segments_vis : ltac2:(zQ "50!kr0!lk6!lh5!jqf!hm9>1E$4>2cs$3>5model$0@2$1?4SEGS@3$2^3^2^1").
  Proof.
    intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
    apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
    apply SEGS_in_hull. exact Hh.
  Qed.

  (* [comment removed for export] *)
  Lemma mrestrict_Hv_high : ltac2:(zQ "c0!h9!jc!t1!n4!kr0!ll8!lh5!jqf!lhb!hm9!hv1!iq8>1E$9>2cs$7>5model$4>4FULL>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>0@2$a@1$8^3@2$b@1$0#k0^1@3$3@1$2@1$1@1$0#8@3$5@3$6^6^5^4^3^2@1^3^2").
  Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Mr_grows_Hv : ltac2:(zQ "a0!h9!jc!t1!kr0!ll8!lh5!jqf!lm5!hm9!lq5>1E$8>2cs$6>5model$3>4FULL>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$9@6$7?1A?4argH^4^3^2^1@2$4@3$5^4^3^2^1").
  Proof.
    intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
    destruct (argH E a), (vis A E cs model a); cbn; auto.
  Qed.

  Lemma munrestrict_mrestrict : ltac2:(zQ "71!h9!jc!t1!sa!n4!ll8!lr2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$3>4FULL~0@3$4~0@3$6^2^1@2$5^2^1^1").
  Proof.
    intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
  Qed.

End NodesD.
(* [comment removed for export] *)
