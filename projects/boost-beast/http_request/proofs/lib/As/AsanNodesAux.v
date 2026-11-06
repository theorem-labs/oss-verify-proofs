(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg AgentLib Hoare RefLayout
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


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
Lemma kwritable_sound : forall segs E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
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

Lemma regs_ok_post2 : forall E sr R R' n1 (r1 : bv 5) e1 n2 (r2 : bv 5) e2,
  regs_ok E sr R -> (0 < n1 < 32)%nat -> (0 < n2 < 32)%nat -> n1 <> n2 ->
  bv_unsigned r1 = Z.of_nat n1 -> bv_unsigned r2 = Z.of_nat n2 ->
  getr R' r1 = edenot E e1 -> getr R' r2 = edenot E e2 ->
  (forall r, r <> r1 -> r <> r2 -> getr R' r = getr R r) ->
  regs_ok E (sr_upd (sr_upd sr n1 e1) n2 e2) R'.
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

Lemma edenot_ev_agree : forall b E E' e,
  nb_lt b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(* [comment removed for export] *)
Lemma fetch_lit : forall segs z (w : word) x,
  bv_unsigned w = z -> fetch_word segs w = Some x -> fetch_word segs (Z_to_bv 64 z) = Some x.
Proof.
  intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
  apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma with_ss_idem : forall cs s1 s2, with_ss (with_ss cs s1) s2 = with_ss cs s2.
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : forall cs s, a_ss (with_ss cs s) = s.
Proof. reflexivity. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma page_base_le' : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                       /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                       /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.ZArith.BinInt.Z.mod_mul); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base)|] [|@Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @__sat2; @H5; @H4; @r; @q; @H3; @H2; @H1; @H0; @H; @__sat0; @__sat1; @z; @__p1; @H6; @__p2; @a|] "#(8#6$/#M#l#@#m#k###$#r#%#'#&#)#6#.#*#W#q#<#/#`#u#y#E#H#J#(#Q#R#S#T#-#0#\#]#g#f#~$#$$#3$($)#:#9#=#C#G#I#K#+#,#1#_#^#c#b#a#d#e#h#j#s#w#x#|$%$&#}$'#4#2$*#5$,$-$/$.$0#?#B#>#A#i#L#;#O#o#n#P#F#N#Y#t#Z#[#X#V#{#U#D#p#v#z$+=#q%#r%#s%#t%#u+#v&#w$#x%#y'#z*#{%#|%#}%#~&$#*$$%$%$$&%$'&$(&$)($*$$+%$,%$-&$.))S$)#)#)#)#)#US=#US>#US?H&%H#E#8-8)VS@$#$'#%'#&,I).)#)#)#)#)#8#VS)*##E+#E%&7M.#'#E#k##&#k##(#VSA76$E8#E8$E8k##$#k##&##E=WSB>=Ij##S*#j#$%##E?k##S*#k#$(#&s#)LVS+#9(C:EUSC#&s#-S,.#=*>#-%?/$#(C'#k##)#VS-)s##$Es#$&s#6N-#s#&#E#$$s#(%$#k##(#VS.(s#+$s#,E&s#>Q-#s#.$s#/##$E%$#k##(#VS/(s#3&s#ESD.#s#5(C#Ek##?#VS0&s#8&s#JSE-#s#:(C#$k##s#$#.&s#=&s#OS1-#s#?&s#QP#E#$$s#L%$#*Ks#D#E#&s#WS%#%#%%#j##(#$&s#T&s#\S2#E#&s#^SF$#s#XUS2I#ENk##s#N#3S33#3#3#2C#USGS$VSHC#2C(WS4C$#2CS30C$#0C)#4#S&VSICs#_WSJC#'2C/0C#+0C/#0C&#4#S&VSK-#USLR5R$#5R-#USMRVS5CKVS5CMXS6C$I#USNCUSOC9CE9Cs#q+C$S##,&GDDF#JUSPDUSQS$:C#+C)S'#,+GDDF#J+C%S#*,-GDDF#J1.GDDF%#'/GDDF+*#+C.S(/,1GDDF#JZSR2GDDF#:Cs$;:CS$6C3#;C#/+C&S(#,8GDDF#J'9GDDF)4#+C9S'),;GDDF#J6C*:+C<S'#,>GDDF#J+C%S'.,@GDDF#J1AGDDF%#'BGDDF)=#'s##GDDF,>#'s#$GDDF7?#VSSs#%FVS7S8S9VSTHK(S8#S9m$%#WSUCEIXSVHK$#l#%*)#l#&s#/s#.#l#'s#4s#3#j#(C#j#)C#j#*C##EM$Ms$D%$#k##s$$#k##s$/SW*s$HK/#L(CM#k##&#*Ms$L#E##$L%$#k##/#k##(#k##.#k#(C#k#)C#k#*C#&s$gSXZHN#QPS%Ml#+8%#l#,s#hs#f#j#-s#j#j#.s#m#V#IHj##s#q#j##s#{#7s#|s#{s#t#S1l#/s$#C#l#0s$&C#l#1s$,s$(#l#2s$2s$.#l#3s$;s$4#l#4s$Ds$=#l#5s$Os$F#l#6s$Us$R#l#7s$_s$Z#l#,s$hs$a#.s$qs$j*#s$k#E##$s$t%$#&s%$K.#s$p*#s$q#Hs$n/Hs$s$s$p#-Hs$u(C#E%%#%(#j#8C##+-/,s${$/#-.s$}(C#E%%#VS)3s%$#E4.s$ls%&#E#k##s%%#k##&#VS+s$ls%*.s$ds%+*s%,#/#s$e(Cs$g#k##s$r#VS-s$is%0#Es$a$s$bs%2%$#k##s$n#VS.s$fs%5-s$`s%6$s%7##$E%$#k##s$l#VS/s$es%;(Cs$]Ek##s%%#VS0s$cs%>(Cs$^s$_k##s%(#.s$as%A-s$`s%B#Es$[%#s$X#s$_s$Xj##$#$s$Zs%Q#Es$Y&s%ZSY$#s%TUSZCXS6Cs$?I#<s$<GDDFL1s$=GDDF#s#{'s$>GDDF#s$9s#|l#%#s#xs#rl#&'s$A#l#'s$Is$F#j#(C#j#)C#j#9O#*Hs%V##I%K#*Is%Y##Kk##%#k#(C#k#)C#k#9O#*Qs%_#E#&s%rS[XH$#QS:l#+0'#l#,s$ss$q#j#:=#j#-@#V#IHj##s###j##s#(#7s#)s$~s#&#Pl#/s#+C#l#0s#-C#l#.s#1s#/#l#1s#5s#3#l#2s#<s#7#l#3s#Bs#>#l#4s#Is#D#l#6s%`s%]#l#7s%js%e#l#,s#Rs#M#/s%3s%u$s%-#j##s#5#2Cs%(0C#s$|0Cs%##4#S&5R#s$s<s$lGDDFS,1s$mGDDF#s$b's$nGDDFs$js$i#6Cs$ms$^;C#s$i+Cs$_S(#,s$rGDDF#J's$sGDDFs$cs$n#6Cs$cs$r;C#s$s+Cs$dS##,s$wGDDF#J's$xGDDF's$s#'s$yGDDF-s$t#l#%#s$Ws$Ql#&s$}s$|#l#'3s%%#j#(C#j#)C#j#*C#j#9O#%Ls$Pk##s%q#*s&8M/#L(CK#k##s$R#/s$Ns&<$K#k##%#k##*#k#(C#k#)C#k#*C#k#9O#ZHs%RNQs#APS%l#+2$#l#,s%Us%S#j#:s#[#j#-s#^#V#IHj##s#a#j##s#f#7s#gs%`s#3#Pl#/s#iC#l#0s#kC#l#.s#os#m#l#1s#ss#q#l#2s#zs#u#l#3s$$s#|#l#4s$+s$&#l#6s&Bs&?#l#7s&Ls&G#l#,s$4s$/#(CHEj#8C#VS7CEl#%s%9s%&s$|l#&s#ns%K#l#'s%Ss%P#l#+#s$tHWS\s$Ls&^#ZS;CE)(s$@#XS<s$Bs$@,#XS<s$Es$@s#K#VS]s&ss$O&s&t#$s%~s&n%s%~#j##s$$#WS4Cs%ms%d0C#s#M0Cs%q#4#S&5R#s%b1s%[GDDFs%Rs#M's%\GDDFs%Xs%W#<s%]GDDFN1s%^GDDFs%B#9Cs&|WS^C#s'&+Cs%PS##,s%bGDDF#J+Cs%IS#%,s%dGDDF#J1s%eGDDFs%I#'s%fGDDF&s%a#'s%gGDDF+s%b#'s%hGDDFs%Qs%c#'s%iGDDF/s%d#l#%#s%Gs%Al#&s%ms%l#l#'4s%q#j#(C#j#)C#j#*C#j#9O#j#;O#%s%BLk##s&b#%s&BN$Ls'4*Ls'+#E#$$s'7%$#k##'#k##)#k##s%D#k##,#k#(C#k#)C#k#*C#k#9O#k#;O##s$7s$5$Ns'9]H$#Ns$7QPS%S:Kl#+7&#l#,s&Ks&I#j#:s$Q#j#-s$T#V#IHj##s$W#j##s$\#7s$]s&Vs#:#Pl#/s$_C#l#0s$aC#l#.s$es$c#l#1s$is$g#l#2s$ps$k#l#3s$vs$r#l#4s$}s$x#l#6s'8s'5#l#7s'Bs'=#l#,s%*s%%#VS_s%:#ZS;Cs%;s%3s#Ks#I#l#5s%Ds%?#l#$s'_s'X#US`H&s'c###s'a/$s'T$s'c#-&s'V(C#E%%#%(#m#,#j#<s'k##"). Qed.

Lemma page_in_ranges_bounds' : forall (a : word) l lo hi,
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l ->
  page_in_ranges (page_base a) l = true ->
  lo <= bv_unsigned a /\ bv_unsigned a + 1 <= hi + 4095.
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.False Sort Prop.

Lemma A_wf_allowA' : forall A E cs, A_wf (allowA A E cs).
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.atable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.acs); (KReplay.sort_at constr:(@Stdlib.Lists.List.Forall_nil_iff) [0]); constr:(@Corelib.Init.Datatypes.list); constr:(@kc__1); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.Forall_forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.Lists.List.flat_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.allow1); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.a_vis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.a_ghost); (KReplay.sort_at constr:(@Stdlib.Lists.List.flat_map_app) [0]); (KReplay.sort_at constr:(@Stdlib.Lists.List.flat_map_app) [1; 0]); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.Lists.List.in_flat_map); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.edenot); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@kc__3); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pagedown); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pageup); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.sh_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.sh_hi); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pagedown_le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pageup_ge); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pagedown_mod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pageup_mod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.shadow_off); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Corelib.Init.Logic.False); constr:(@kc__4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.A_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.allowA); constr:(@kc__2 ((@Corelib.Init.Datatypes.prod) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr)))|] [|@x; @l; @P; @A; @iv; @y; @f; @B; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__p1; @__arith; @__sat1; @__sat2; @H0; @H; @__x5; @__x6; @__x7; @__x8; @__x9; @H14; @H13; @H12; @H11; @r0; @q0; @H10; @H9; @H8; @H7; @H6; @r; @q; @H5; @H4; @H3; @H2; @H1; @__sat3; @__sat4; @Hb; @Hn; @Hin; @_H; @p; @cs; @E|] "#-H#W$n#e#n$E#l##$F$D#$#%#'#&#k#(#+#)#,$M#*#-#.#5#3#4#7$L#1#0#:#6#9#2#W#@#}$7#8#;#<#>#?#/#=#A#D#E#F#G#H#I#L$l#]#d#t#s#x$.$/$1$2$5$<$8$=$P$Q$U$V$Y$Z$0$]$^$a$b$c$d#B#C#J#M#Q$j$m$n#U$%#o#c#v#{$#$4$6$@$A$C$N$R$T$W$X$S$_#K#N#O#P#R$g$f$e$i$k#V$o#w$q$p#\#[#Z#f#b#y#z#i#j#g$*#h#a#~$)$'$B$H$G#|$($9$\#q#r#p$:$J$&$;$-$>$,$?#_#m#u$I$$$+$K$3$[$`#^#`$O$hR$A%$B%$C%$D%$E&$F%$G&$H%$I&$J&$K%$L$$M$$N+$O'$P*$Q$$R%$S&$T%$U$$V$$W&$X%$Y%$Z'$[$#z&$\&$]'$^&$_%$`($a'$b%$c&$d$$e&$f$$g'$h$$i%$j$$k&#z%$l*$m&k##GS2MJNKJG,LGKULJk##$#k#$M#k##'#,MGJUMJk##$#k#$K#NMKJk##$#$)#NLMKk##,#j##%#j##$Gj##.#WSkKJGC0*&$#j#%7#j#&9#j#'SF#k#%:.k#&<#k#'SF#VSGCC)CCG+CCG#$#(%N'C#F(&N'C#F$%#$(#j#(,#VSGDDOMK7J8J9&$#D'2&#OLM7K8K9+$#D,7&#,8G#k##Js#4MKDLMKJ,MG#,QGMULG,OK#$%#j#$O#EO#k##)#,OGKUMG,LJ#$%#j#$L#EL#DOLMK,LJ#k##%#$,#,S$GLUOG,QM#$%#j#$Q#EQ#k##+#j##*#DQOLM,OK#k##8#j###Jj##9#YSlLMKJGC;2)$#j#)K#j#%s#&#j#*s#(#j#+SH#j#'SI#k#)KAk#%s#+#k#*s#-#k#+SH#k#'SI#OQO7L8L9s#?$#ZGs#@s#K&#KJ7O8O9s#C$#,s#DG#>S$QG,s#QM#$%#j#$s#H#Es#I#7Q8Q9s#L$#,s#MG#>PS$G,s#ZL#$%#j#$s#Q#Es#R#)CCL+CCL#$#(%N'C#F(&N'C#F$%#$(#j##,#7S$8S$9s#_$#,s#`G#>RPG,s#mO#$%#j#$s#d#U#G7P8P9s#h$#,s#iG#>S%RG,s#vQ#$%#7R8R9s#o$#,s#pJ#>S&S%J,s#}S$#$%#)CCP+CCP#$#(%N'C#F(&N'C#F$%#$(#j##,#>S;S&K,s$.P#7S&8S&9s$&$#,s$'M#>S,S-L,s$4S%#+DDO%S,#USJ#3S43#3#3#3#3#USm#&#+#F#G+G'VSn$#-'#$'#)DDQ%S1#USJ#&-$#F#-$*$$#)DDS$4S(#/#+DDS$4S(#*&#.#<CC'#'s$U#S-AS)S(S$/#?S)S(S$.#<CC%#USKs$[Hs$\$#,s$]S-#VSL+#)CCS,+CCS,#$#(%N'C#F(&N'C#F$%#$(#j##,#)DDP4S)#/#+DDP4S)#*&#.#<CC'#'s$q#S,)DDR4S'#/#+DDR4S'#*&#.#<CC'#USM)#)*)DDS%4S/#+DDS%4S/#*%#USN#.$#%#)DDS&%S*#&s#J#/#+DDS&%S*#&s#N#*'#.##(#3s#S3#3#3#3#3#G#(0#'C#F(-%'C#F$%#VSos#[s#Z-Fs#\#Fs#\-Fs#\k##$#k##&##Fs#aWSps#bs#aJj##SO#j#,%##Fs#ck##SO#k#,(#=SP=#=#:C#:C%:C':CSP5C$#5C&#5C(#VSQ#SRUSKS5HS5$#MS5BCLUSqC@C$K#BCM@C$J#USrCUSsC;Cs$)IS4;C#FC%#;Cs$.1C$S+#2)IEEH#S#UStE;CS41C#S++2-IEEH#S#VSSCF1C#S+,20IEEH#S#ZST1IEEHQP2IEEH$#1C*S+.24IEEH#S#05IEEH%-#06IEEH+.#07IEEH0/#VSu8HVSvSUSVVSwGK'SU#SVm$%#WSxCFJXSyGK$#l#-*)#l#.BA#l#/s#)s#(#j#0C#j#1C#j#2C#j#3C#j#4S2#*MK##J#JL#FL$#Q#MLk##$#k##'#k##)#k#0C#k#1C#k#2C#k#3C#k#4S2#+DDS,%S.#&s$X#-#s$T)DDS,%S.#&s$\#*#'.#/%\G)&*$#MLPl#5<.#l#6s#Ys#V#l#7s#cs#^#USWs#xUSXs#tJs#js#h$#Js#ts#h&#4S*s#~/#4S*s#|*%#.##&#('s#t'C#F(&s#v'C#F$%#$(#m#/#l#8s$2s$0#l#9s$:s$9##s$As$=(s$BN'C#F(s$@N'C#F$%#$(#m#*#)CCs$D+CCs$E#$#(%N'C#F(&N'C#F$%#$(#m#,#ZSYs&is$Ns&_#S1Gj#9s$W#U#Gj##s$u#AS'S)P/#?S'S)P.#<CC%#Hs&r#s$u,s&sS,#AS/S'R/#?S/S'R.#<CC%#'s&y#S1,s&zS1s$}VSL$#)CCS(+CCS(#$#(%N'C#F(&N'C#F$%#$(#j##,#AS*S/S%/#?S*S/S%.#<CC%#'s'/#S(AS6S*S&/#?S6S*S&.#<CC%#USM'#'(?S0S6S;USN#.$#%#KS.)DDS-%S0#&s%^#Gs%c6$#*(#/#+DDS-%S0#&s%e#**#6#**/#.##*#(+s$q'C#F(&s$s'C#F$%#)DDS1%S7#&s%r#VSZ#6#F$#F8)DDS)%S<#&s%x#6#<#F#k##(#k##*#)DDS(%S8#&s&##+DDS(%S8#&s&&#*&#VSZ#s#'#F$)DDS'%S9#&s&,#+DDS'%S9#&s&/#*&#6#s#0#F#k##<#k##-#VS[;s#4'Cs#5FUSz#6.s#7Ls#8#(0s#9*$#'C2#k##(#VS\4s#=-Fs#>)DDS/%S:#&s&B#(#s#B#F#-$s#D$$#k##*#VS](s#G-s#HF)DDS*%S3#&s&L#(#s#L-s#M##$F$$#k##*#VS^(s#Q)DDS6%S=#&s&U#6#s#U'C#Fk##s#$#VS_&s#X)DDS0%S`#&s&\#(#s#\'C#$k##s#+#6&s#_)DDS.%Sa#&s&c#(#s#c)DDS7%S>#&s&g#+DDS7%S>#&s&j#*&#VS[#s#k)DDS8%S?#&s&o#+DDS8%S?#&s&r#*&#6#s#sLs#t#(%s#u*$#'C'#k##s#D#VS\)s#y)DDS<%S@#&s&}#+DDS<%S@#&s'$#*&#(#s$%#F#-$s$'$$#k##s#I#VS](s$*)DDS9%SA#&s'.#+DDS9%SA#&s'1#*&#(#s$2-s$3##$F$$#k##s#L#VS^(s$7)DDS:%SB#&s';#+DDS:%SB#&s'>#*&#6#s$?'C#Fk##s#j#VS_&s$B)DDS3%SC#&s'F#+DDS3%SC#&s'I#*&#(#s$J'C#$k##s#u#6&s$M)DDS=%Sb#&s'Q#+DDS=%Sb#&s'T#*&#(#s$U)DDS`%S{#&s'Y##F#-$s'V$$#KSc*#R/#*%K.##%#j##)#)DDSa%SD#&s'f#-#s'b)DDS>%Sc#&s'j##F#)DDS?%S|#&s'n#-#s'j+DDS@%S}#&s'r##F#-$s'o$$#KSd*#S-/#*%Q.##%#j##)#+DDSA%S~#&s(##-#s'{+DDSB%Sd#&s('##F#+DDSC%T##&s(+#-#s('US.O#FS)k##s$t#=s&}=#=#=#=#:C#:C%:C'UT$S4VT%C#:C+WT&C$#VT'Cs%;:C/QC$#QC%s'/QC&s'-5Cs'/#5C%#5C'#5C+#5C0#5C2#5C4#VSQ#SRHS5#s'1BCP@C#Ls'/BCQ@C$K#BCR@C#Os'3BCS$@C$M#@C'J#VSSCs%R1Cs''Se#2s'4IEEH#S#Is([;C#1Cs'+S+#2s'8IEEH#S#1C%Se)2s':IEEH#S#Ps';IEEH%#0s'<IEEH*s'4#1C-SEs'12s'>IEEH#S#ZT(s'?IEEH#Is'>;C#WSfC2#FC#/1Cs'@SE#2s'EIEEH#S#0s'FIEEH)s'>#;Cs(l1Cs'<S+#2s'IIEEH#S#ZSTs'JIEEHS&Ps'KIEEH$#0s'LIEEH:s'D#3s'K;C#WSfC?#FC#+1Cs'PSE#2s'RIEEH#S#0s'SIEEH6s'K#Is({;C#FC#71C#S+s'R2s'XIEEH#S#FC&-1Cs'QS+#2s'[IEEH#S#1Cs'PS+s'[2s']IEEH#S#0s'^IEEHs'Ps'Vs'L0s'_IEEH$s'W#0s'`IEEH's'X#0s'aIEEH+s'Y#0s'bIEEH1s'Z#0s'cIEEH9s'[#0s'dIEEH@s'\#0s'eIEEHs#+s']#l#-#s'Ps'Jl#.s#8s'h#l#/s#Bs'o#j#0C#j#1C#j#2C#j#3C#j#:C#j#;C#j#<C#j#=C#j#>C#j#4S2##FR-Rs&8$$#k##s%Z#k##s%dSg*OLLs&=P*#S%'C%#k##'##FS%$#S;k##s%c#Ls&DR*#S&'CS$#k##.#*PS%##O*RS%#O##PRk##8#k##9#k##&#k##)#k##,#k##1#k##5#k##<#k#0C#k#1C#k#2C#k#3C#k#:C#k#;C#k#<C#k#=C#k#>C#k#4S2#-S)s&_KT))DDSD%Sh#&s)d#+DDSD%Sh#&s)g#*)S&.#*+S'/#fG.S%S)S&S'-*'%#S1S(S0S.S:S3S$Ml#5s#80#l#7s$Cs$A#j#?s$E#j#@s$J#V#JGj##s$P#j##s$^#Cs$_s$^s$V#S3j#As$d#j#Bs$i#V#JGj##s$o#j##s$}#Cs$~s$}s$u#S7l#Cs%'C#l#Ds%0C#l#Es%<s%2#l#Fs%Hs%>#l#Gs%Vs%J#l#Hs%ds%X#l#Is%ss%f#l#Js%|C#l#Ks&%C#l#Ls&-s&'#l#Ms&5s&/#l#Ns&@s&7#l#Os&Ks&B#l#Ps&Us&M#l#6s&cs&W#l#7s&us&l#l#Qs)&s)##l#Rs)0s)+#USWs'.USXs'(Js'%s'#$#Js'(s'#&#AS.S0S-/#?S.S0S-.##%#(&s)@'C#F(&s)B'C#F$%#$(#m#.#l#8s'Gs'E#l#9s'Ks'J##s'Ps'N(s'QN'C#F(s'QN'C#F$%#$(#m#*#)CCs'U+CCs'V#$#(%N'C#F(&N'C#F$%#$(#m#,#ZSYs,5s'_s,+#S)Gj#9s'e#U#Gj##s'y#,s,9S(s*<)CCS'+CCS'#$#(%N'C#F(&N'C#F$%#$(#j##Sg#VT*#Gj#9.#U#Gj##s(+#ZSis(-s(,s'}2#Gj#9s(4#U#Gj##s*L#ZSis*Us*Ms*Bs(>#Kl#Ss*cs*_#l#Ts*us*g#j#Us*y#j#Vs*|#V#JGj##s+&#j##s+6#Cs+7s+5s+*#Gj#9s+<#j#Ws,K#V#JGj##s+F#j#$s,N#YT+s,Os+\s+Q#Gl#Us+ns+e#l#9s+ys+t#j#Us,G#j#(s,^#XGs,_s,Us,O#l#9s,ds,a#WT,KJGUT-#m#%#j#XT.#j#YT/#j#'T0##"). Qed.

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
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A E cs model a).

  Lemma Hv_hid : forall E cs model a, Hv E cs model a = true -> hid A argH E cs model a = true.
  Proof. intros E cs model a H. unfold hid, Hv in *. rewrite H. apply orb_true_r. Qed.

  (* [comment removed for export] *)
  Lemma Hv_high : forall E cs model (a : word), TOP model <= bv_unsigned a -> Hv E cs model a = false.
  Proof.
    intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
    replace (TOP model <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
    rewrite orb_true_r. reflexivity.
  Qed.

  Lemma Hv_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> Hv E cs model a = false.
  Proof. intros E cs model a Ha. unfold Hv, vis. rewrite Ha. reflexivity. Qed.

  Lemma lazy_cover_vis : forall E cs R FULL model,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> lazy_cover (Hv E cs model) (m_vm_lazy model) (allowA A E cs).
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.acs); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.cs_ok); constr:(SEGS); constr:(A); constr:(LIMIT); constr:(SINV); constr:(argH); constr:(FS0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesAux.NodesD.Hv); constr:(@Corelib.Init.Datatypes.false); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.negb); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Bool.Bool.negb_false_iff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.vis); (KReplay.sort_at constr:(@Stdlib.Lists.List.partition) [0]); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.Lists.List.existsb); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.Lists.List.In); constr:(@Stdlib.Lists.List.existsb_exists); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Datatypes.snd); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.page_allowedb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.allowA); constr:(@Corelib.Init.Datatypes.andb_prop); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Corelib.Init.Logic.proj1); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.img_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.img_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.TOP); constr:(@Stdlib.Lists.List.Forall_forall); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.co_lazyb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanNodesAux.page_base_le'); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(HULL_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.hull_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.KHI); constr:(@Stdlib.Bool.Bool.orb_prop); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.in_hull); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.in_ivs); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.in_allow); constr:(@kc__3); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.Lists.List.flat_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.allow1); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.a_vis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.a_ghost); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.in_vis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.in_sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.uE); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pagedown); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.pageup); constr:(@Corelib.Init.Logic.conj); (KReplay.sort_at constr:(@Stdlib.Lists.List.flat_map_app) [0]); (KReplay.sort_at constr:(@Stdlib.Lists.List.flat_map_app) [1; 0]); constr:(@Stdlib.Lists.List.in_flat_map); constr:(@Stdlib.Lists.List.in_or_app); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.sh_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.sh_hi); constr:(@Corelib.Init.Datatypes.andb_true_intro); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.lazy_cover); constr:(@kc__2 ((@Corelib.Init.Datatypes.prod) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))))))|] [|@b; @x; @l; @f; @A; @r; @m; @n; @iv; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__p1; @__arith; @r1; @q1; @H17; @H16; @H15; @H14; @H13; @r0; @q0; @H12; @H11; @H10; @H9; @H8; @q; @H7; @H6; @H5; @H4; @H; @__sat4; @__sat5; @__sat6; @L1; @Hv2; @Hv1; @Hv0; @p; @y; @B; @r2; @q2; @H22; @H21; @H20; @H19; @H18; @__sat7; @__sat8; @Hb4; @Hb3; @Hb; @Hinp; @_H; @H3; @H2; @H1; @H0; @HU; @P3; @P2; @P1; @L2; @Hb2; @Hb1; @Hin; @Hlz; @Hlz0; @Hh; @w; @HC; @model; @FULL; @R; @cs; @E|] "#>Z$C%w$v%S##$X$\$R%i%T%R#$%)#%#'#&#*#(%Z#+#)#,#2$p%_$C#9#1#:%j#>#[#}%Y#3#?#X#\#_%:#|%G#f#p#r#-#0#5#@#<#Y#]#^%7#g%H%D%`#e#l#m#s#.#4#6%/%2%1%3#`#{#~%C%M%^#v#h#k#n#u#w%s%t%r%u$u#8#G#E#S#Z#d%E%J$$#o&$$L$^$d#=#A#V#i%5#a#t%q%~$%#7$&$'$($)#;$*$+$B$I$e$f$j#C#B%-#b#y%X%a%d#j#c%n%o%z&)$r$M$Q$S$T$U$V$]#/$z%'#H#D#K#P#O#W%I%K#N#q%w%v$#&#$<%}$H$N$P$b$c$i$x$|$}%#%$$y%%#L#F%+%,#Q#U#T#R%9%<#x#z%N%O%Q%U%[%b%e%f%c#I#J%6%g%x%y$4$5$6$7$8$9$:&&&%&(&'&*%*&+$O$G$F$W$m$o$w$a$l$Z%p%P$n$h$q%(%&$k%L%8%W%V%|%>%F%{$[$_$`$g$K$J$t%=%l$s$~%.%0%\%h$Y${%]%4%m%k%;%?%@%A%BU%F&%G%%H%%I%%J%%K%%L$%M%%N+%O&%P&%Q&%R%%S%%T%%U'%V%%W'%X*%Y&%Z%%[&%\&%]$%^(%_$%`%%a$%b$%c&%d%%e$%f%#%&%g$%h%%i%%j%%k'%l%%m%%n&%o'%p$%q&%r%%s%%t%%u%%v%>Sr?#UT,#>%>#>#>#>#UT,#UT?#VTY*#UT,)UT?#UTZ#k##'#_T[T@HTATBTCTDOPNLE)E:NJ$##F#GXTEQS%PL#F#Ss<E#F#Ss#FLGk##$##FEG<L#F#Ssk##%#''##FNGk##&#j##%#<N#F#Ssk##.#j###Lj##/#UT\E;1-)$#j#$F#k#$F3YT]HS&S$RPVE#L#F$G)O:S%J$##F#Gk##EFUT-LWT.NLE#F#G-OENUPE#F#G'%#j#%P#=P#k##)#-PELUNE#F#G'%#j#%N#=N#WT.PNL#F#Gk##%#',#-REPUOE#F#G'%#j#%O#=O#k##+#j##*#WT.OPN#F#Gk##8#j###Lj##9#WT^NLE;;2)$#j#&s#%#j#'s#'#j#(St#k#&s#(?k#'s#*#k#(St#VT/s#Us#U,s#Vs#VE$s#X#)Q$s#Z#(%#%$S(.s#\s#\E$s#^#%)#(&#1(#j#).#:S$XE0$#R:S&-2E##F(G'$#j#%5#=6#:S>-8E#)S$$s#n#(9#%$S((#41%##F#G'*#j#%A#=B#@HS,S?C#-#F#Gj##&#:SO-s#(E#)S&$s#~#(s#)#%$S((#s#$1%##F#G'*#j#%s#1#U#E:TF-s#4E#)S>$s$.#(s#5#%$S((#s#01%##F#G'*#:S?-s#>L#,s$6s$6L$s$8#)SO$s$:#(%#%$S(.s$<s$<L$s$>#%)#(&#1(##F#G'/#@HS@SP)TFC$##F#Gj##'#,s$Hs$HN$s$J#$s$K(($#%$S(.s$Ms$MN$s$O#%(#(&#1(##F#G:S'-s#]P#,s$Us$UO$s$W#)S,$s$Y#(%#%$S(.s$[s$[O$s$]#%)#(&#1(##F#G,s$as$aR$s$c#)S'$s$e#(%#%$S(.s$gs$gR$s$i#%)#(&#WSf(#E#F)G#F%G'$#,s$os$oS%$s$q#)S3$s$s#(%##F#G%%S(.s$vs$vS%$s$x#%*#(&##F#G')#@HS-S+)SPC$##F#Gj##'#$s%&&%#S(,s%'s%'Q$s%)#.s%)s%)Q$s%+#%%#((##F#G,s%.s%.S$$s%0#)S@$s%2#(%##F#G)SQ$s%6#%#S(,s%7s%7S&$s%9#.s%9s%9S&$s%;#%%#((##F#G(LE#F#G&NLk##$#&LE(NL#F#Gk##%#''#&PNk##&#j##%#(PN#F#Gk##.#j###Lj##/#VT_LE;1-)$#j#*C#j#+C#k#*C4k#+C#,s%Us%USO$s%W#)Sg$s%Y#D%#N&&$)S-$s%]#%#S(,s%^s%^S?$s%`#.s%`s%`S?$s%b#%%#D(#P&)$UT`H&s$f#UTaH&#s$oK%#ES/&s$k#'%#j#,s$v#:SuWTGs$x$#:S4-s$zE#ESv&s$s#'-#j#,s$~#U#Lk##(#k#%s%%#k##,#:S/-s%(E#ESA&s$}#'7#j#,s%,#U#Lk##(#k#%s%/#ES4&s%(#'>#j#,s%3#WTGs%4#/k##(#WTbs%6>=`TcT@HTATBTCTDSvSAS4S/SuSBZTd4%$#S,S>UAS,,s&1s&1S'$s&3#.s&3s&3S'$s&5#%%#&#s#/&s#.'K$#&&s#-'$#@HT0T1)SuC$##F#Gj##'#,s&@s&@S3$s&B#.s&Bs&BS3$s&D#%%#&#@,s&Fs&FSP$s&H#.s&Hs&HSP$s&J#%%#&#s#D&s#C'K$#,s&Ns&NS@$s&P#.s&Ps&PS@$s&R#%%#&#s#?UTeSA)SA$s&W#$s&XSA&$#>s&[>#>#>#>#>#UTH#%,#0,#/.%#C#M'%#'/#)Sv$s&h#$s&iSv&$#%%-0%#/'/#C#M'%#'(#@HTISh)T1C$##F#Gj##'#$s&vT1$s&w'%#:0%#/%<#C#M'%#)T0$s&~#$s'#T0&$#$s'%TJ)TJ$s''#%#s#&0&#/%s#(#C#M'%#$s'-Si)Si$s'/#%#s#.0&#/%s#0#C#M'%#@HTfTK)TgC$##F#Gj##'#$s':&/#s#9#C#M$s'=Sh)Sh$s'?#%#s#>0&#)TI$s'C#/#s#B#C#MUThH&Ms$?/s$@s#F#C#M/s$@s#H#C#M&s$BTi'$#''#'*#@HTjTL)TKC$##F#Gj##'#@HTkTl)TMC$##F#Gj##-#@HSCS5)SjC$##F#Gj##3#$s'_SwVSRH#ES5(#%F%#USSS5UST#G)#USU%G+#<#1&#)Sw:S5J$#<#MHS6S02F$#1)#WT21#Tm#F2G#F%GK$#$s'vTNVSRH#ESC(#%F%##F#GUSSSCUST#G*#USU%G,#<#1&#)TN:SCJ$#<#MHSDS63F$#1)##F#GK2#@HSESD)S5C$##F#Gj##'#$s(5S5VSRH#ESk(#%F%##F#G@HS7SE)SCC$##F#G$s(?SCVSRH#ES0(#%WT2%#E#F&G#F%GK$#$s(GSkVSRH##F#GES6(#&#F#GK&#j###SF$s(OS0VSRH##F#G$s(RS6(s%K#3$s%JWSf$#E#F%G#F%G'$#$s(YSD(s%R##F#G3%s%R#F#G'%#j###SF$s(`SE3#s%W#F#G$s(cS7(s%\##F#G$s(fSV3#s%]#F#G$s(iT3Ds%b#N&s%c$3LE#F#G0NLk##$#0LE3NL#F#Gk##%#''#0PNk##&#j##%#3PN#F#Gk##.#j###Lj##/#VTnLE;1-)$#j#*C#j#+C#k#*C4k#+C#$s)'SlD#s%zP0$s%{,s))s))S0$s)+#.s)+s)+S0$s)-#%%#&#s&'&s&&'K$#j###SF,s)2s)2S6$s)4#.s)4s)4S6$s)6#%%#&#s&0)SG$s):#VS8#s%9&M$&Ms%;)Sx$s)?#/#s%>&M#k##'#k##)#VS8s&:s%B&Ms&;&Ms$Zk##,#k##%#WS8s&As%GS4&Ms$`k##0#Ps&Ds%J#Cs%KMUTo#7s&Gs%MAs%N#%#s$g#Cs&J#k##'#Qs&Ls%R0Ms%S0s$ls%T'/#k##%#Rs&Qs%W0s%XM0s%Ys$q&s$rM'$#k##&#Ss&Ws%]#C3Mk##6#Ts&Zs%`#Cs$ys&[k##9#Ps&[s%c7s&\s%dAs%e#%#s$|#Cs&_#k##>#Qs&as%i0s%$s%j's#)#k##;#Rs&es%m0s%ns%(&s%)M'$#k##;#Ss&js%r#C1Mk##s#+#Ts&ms%u#Cs%0s&nk##s#.#)Tp$s){#P#s%z)T4$s)~#7#s%}As%~#/%s&#%$##C'#k##s#8#Q)s&')Tq$s*+#/#s&*&M#0$s&,'$#k##s#9#R(s&/)SW$s*3#/#s&20s&3#&$M'$#k##s#<#S(s&7)S9$s*;#7#s&:#C#Mk##s#O#T&s&=)S1$s*A#/#s&@#C#$k##s#U#7&s&C)SX$s*G#/#s&FUSHTOUSH#USH#USH#VS:C#VS:C%VS:C(VS:CTO8C$#8C&#8C(#VSm#SnUTPSIWSYSI$#UT-SIVSZCOVSZCQUTrC2C$S%#2C&N#VSZCS$2C&R#2C#P'2C&L#UTsCUTtCVT5Cs&aVT5CM4C$S2#5&KDDJ#S#ZTu'KDDJ#UTvD?Sr>#HC#?$HC#WS[C-#>s*vHC#LC%#4C)S2#53KDDJ#S#+4KDDJ/.#4C'S2356KDDJ#S#HCs*|4C6S)#59KDDJ#S#HCs+%HCs+'LC#;4C%SJ#5>KDDJ#S#HCSrHC9LC$#4C#S)-5s##KDDJ#S#4C,SJ;5s#%KDDJ#S#4C1S).5s#'KDDJ#S#4C.S))5s#)KDDJ#S#ZT6s#*KDDJS>+s#+KDDJ$s#%#+s#,KDDJ's#&#+s#-KDDJ*s#'#+s#.KDDJ-s#(#+s#/KDDJ3s#)#+s#0KDDJ9s#*#+s#1KDDJ=s#+#+s#2KDDJ@s#,#VTws#3JVT7FGVTxEN#F#Gm$%#WTyCMLXTzEN$#l#-*)#l#.s#=s#<#l#/s#Hs#G#j#0C#j#1C#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#8S*#k##s$[SFAs'IS$%#Q#CS%#k##&##CQM&MR%Os'O0Q#%OS%&#Q0S&S>&S&S>%S$s'U%QS&&$#k###S3k##'#k##)#k##+#k##.#k##1#k##3#k##5#k#0C#k#1C#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#8S*#$s+kSo.s+ks+kS\$s+m#)So$s+o#,s+os+oS\$s+q#eESFS&S$s(h)s(j'%#S,TQSwS0SBS/SAS]l#9s#,+#l#:s$.C#l#;s$2C#l#<s$9s$4#l#=s$@s$;#l#>s$Is$B#l#?s$Rs$K#l#@s$\s$T#l#As'3C#l#Bs$tC#l#Cs$ds$b#l#Ds$hs$f#l#Es$ns$j#l#Fs$ss$p#l#Gs$zs$u#l#)s'<C#l#Hs%6C#l#Is%$s$~#l#Js%(s%&#l#Ks%/s%*#l#Ls%5s%1#l#Ms%>s%7#l#Ns%Bs%@#l#Os%Hs%D#l#Ps%Rs%J#j#Qs%V#U#Ej##s%a#&s))s%]VS:Cs$H8C#s$C8Cs$F#8Cs$H#VSm#SnWSYSI#s$BVSZCPVSZCS%2C#Rs$@2C%N#2Cs$BOs$C2C#Qs$C2C%L#4Cs$$S)s$%5s$>KDDJ#S#4Cs$6S)s#~5s$@KDDJ#S#4Cs$$S)s$(5s$BKDDJ#S#ZT6s$CKDDJS&+s$DKDDJ$s$>#+s$EKDDJs#|s$?#+s$FKDDJs$#s$@#+s$GKDDJ)s$A#+s$HKDDJ,s$B#+s$IKDDJs$2s$C#+s$JKDDJs$6s$D#+s$KKDDJs$9s$E#l#-#s#ws#ql#.3s$N#l#/;s$Y#j#0C#j#1C#j#2C#j#3C#j#4C#j#5C#j#6C#j#8S*#As(YQ%#S%#CR#k##s#r##CS%M&MO&OS%&S$O0S$S&&S$S&&QS$k###S'k##%#k##'#k##)#k##+#k##-#k##/#k##1#k#0C#k#1C#k#2C#k#3C#k#4C#k#5C#k#6C#k#8S*#dESFS&S$s)ls#is)ns#es#cS,TQSwS7SBS/SAT8l#9?$#l#:s%2C#l#;s%6C#l#<s%=s%8#l#=s%Ds%?#l#>s%Ms%F#l#?s%Vs%O#l#@s%`s%X#l#As(7C#l#Bs%xC#l#Cs%hs%f#l#Ds%ls%j#l#Es%rs%n#l#Fs%ws%t#l#Gs%~s%y#l#)s(@C#l#Hs&:C#l#Is&(s&&#l#Js&,s&*#l#Ks&3s&.#l#Ls&9s&5#l#Ms&Bs&;#l#Ns&Fs&D#l#Os&Ls&H#l#Ps&Vs&N#j#Qs#_#U#Ej##s&d#ZSys&fs&es&cs#c#T{l#Rs&ns&m#l#Ms&ss&q#l#Ss'.s'-#l#Ms*Fs*D#j#Rs'2#j#Ss'6#V#LEj##s';#j##s'C#;s'Ds'Bs'@#El#Ts'Ks'H#j#Ts'P#U#Ej##s'Z#ESD(#s'V#F#GES7D#s'OL&$s'P)SE$s-M#VS8#s)L&M$)SV$s-Q#/#s)P&M#k##s&u#k##(#WS8s*Ns)TSQ8Cs$%s%d8Cs%h#VSm#SnWSYSI#s%c2Cs%aNs%_VSZCR2C#Ps%a2C%L#ZT6s%[KDDJQ+s%\KDDJs%5s%V#+s%]KDDJs%8s%W#+s%^KDDJs%=s%X#+s%_KDDJs%Cs%Y#l#-#s%/s%)l#.)s%b#l#/.s%m#j#0C#j#1C#j#2C#j#3C#j#4C#j#8S*#%Ls)k0O#%LP&#O&RS%%PR&s%$#k###S&k##&#k##(#k##+#k#0C#k#1C#k#2C#k#3C#k#4C#k#8S*#ESl.s-~s-~S5$s.$#)T3$s.&#,s.&s.&S5$s.(#^ESFs'z)'%#SuSiOT|l#9<+#l#Ns#3s'>#l#Os'Fs'B#l#Ps#=s#6#l#Ts#Bs#A#l#Ms+:s+8#j#Ts#F#U#Ej##s(D#ZSys(Hs(Es(Cs#L#El#Ts(Os(L#VT}s(U#j#Ts(Z#U#Ej##s(w#USSSkUST#Gs(d#USU%Gs(f#<#1&#:SkJs(n#<#MHSESDs(lF$#1(##F#GUSSS0UST#Gs(h#USU%Gs(j#<#1&#:S0Js(q#<#MHS7SEs(pF$#WSf(#E#F)G#F%G'$#USSS6UST#Gs(p#USU%Gs(r#<#1&##F#G)Sk:S6J$#<#MHSVS7s(zF$##F#G'*#@HSzSV)S0C$##F#Gj##'#:SDJ'#<#MHSzSVs(~F$##F#GUSSSEUST#Gs)$#USU%Gs)&#<#1&##F#G)SD:S7J$#<#MHT9T3s)'F$##F#G:SVJs$8#MHSKSls(~Fs.v##F#Gj#$F#ZT~F'#EGSC<GMHSlT9s)+F$##F#Gj##s.Ns.Cj##s.DEj##s.Z#;s.[s.R%#s.Cj#&s.e#j#'s.g#j#(St#k#&s.hs.Vk#'s.j#k#(St#VT/CC,CCE)Sz$s/=#(%#%$S(.CCE($#1&#j#,+#VT/IIVS.HS;BSKNSKO&$#I'1&#WT:S;SKs)BXT;HS;SKs)CWT2$#L#F%G#F%GK$#$s/PSzWT:SGS;##F#GXT;HSGS;%#F#GK%#VS.HSxBS]NS]O7$#I8B&#-s##E#)T9$s/]#(s#%#%$s+](#B1%##F#G'*#j#%s#,#=s#-#j##3#WT:S]SGs)\#F#G,IIE*S^#$s/kSK($#.IIE*S^#%'#3'#1'#j#Us#0#BSxXEs#2$#LBT8-s#4E##F(G'$#j#%s#7#=s#8#BS^-s#:E#*SL6$s/~S;($#*SL5%&#3&#1&##F#G'+#j#%s#D#=s#E#VS.HSMBSLNSLOs#I$#Is#Js#T&#-s#UE#(s#Us)V%s)Ws,1(#s#R1%##F#G'(#j#%s#\#=s#]#j##1#-s#UE0*SMs#1$s0=SG($#*SMs#0%&#3&#1&##F#G'+#j#%s#_#U#EBSM-s#bE#*S_s#>$s0JS]($#*S_s#=%&#3&#1&##F#G'+#BS_-s#mL#,IIL*Sp#$s0VSx($#.IIL*Sp#%'#3'#1'##F#G'-#VS.HTRBS<NS<Os#|$#Is#}s$+&#-s$,E#)S^$s0f#(s$.#%$s,f(#s$+1%##F#G'*#j#%s$5#=s$6#j##3#,IIN*S<#$s0rT8($#.IIN*S<#%'#3'#1'##F#G-s$8P<,IIO*S=#$s0}SL($#.IIO*S=#%'#3'#1'##F#G,IIR*SN#$s1+SM($#.IIR*SN#%'#3'#WSf'#E#F(G#F%G'$#,IIS%*S{#$s17S_($##F#G.IIS%*S{#%(#3(##F#G'(#VS.HS\BS`NS`Os$]$#Is$^s$h&#-s$iE#)S<$s1G#(s$k#%$s-G(#s$h1%##F#G'*#j#%s$r#=s$s#j##3#$s1QSp,IIQ*S`#.IIQ*S`#%%#3(##F#G,IIS$*S\#$s1[S<($##F#G$s1^TR,IIS&*Sa#.IIS&*Sa#%%#3(##F#G,IISO*T4#$s1hSND$#N&%$$s1kS`,IIS?*SW#.IIS?*SW#%%#D(#P0)$VS.HS1BS9NS9Os%4$#Is%5s%?&#-s%@E#)Sa$s1z#(s%B#%$s-z(#s%?1%##F#G'*#j#%s%I#,IIS,*S9#USb#.IIS,*S9#%&#USc#XSdCC'#VS.HS9BSWNSWOs%K$#Is%Ls%V&#-s%W(#,CC))S\$s26#(%#%$s.6.CC.($#1&##F#Gk##Ls1nUT-NIOPNL-PE#-S%EP-RNs1^'$#j#%R#=R#k##(#-REN-OLs1u'$#j#%O#=O#IROPN-OL#k##%#'+#IS%ROP-RN#k##/#j##&#j##$Ej##1#YU#OPNLE;3+&$#j#VN#j#&=#j#'?#j#WTS#j#(TT#k#VN1k#&B#k#'s#$#k#WTS#k#(TT#,IIS'*S1#USb#.IIS'*S1#%&#USc#XSdCC'#BS1NS1Os&*$#-s&+E#,IIS3*SX#USb#.IIS3*SX#%&#USc#XSdCC'#WS.HSXE-s&?$#'-#j#%s&7#-s&8S's#bWS.HS1S'-s&D5#-s&;S's#g-s&<S's#gWT<$#SOYU$s&>s#js#iS'##s&I::9HS1S'USb#6HS1S'USc#XSdCC%#UTPs&OWSYs&P$#-s&QB#VT7s&Rs##WT<,$#XSe42.#XS|s&K6S'#ZEs&Ls&Vs#ys#vs#'#l#Ms#5s#0#(s#js#\(s#[s#g#F$G#F$Gj##s0Os0Ij##s0JEj##s0V#;s0Ws0S%#s0Ij#*C#j#+C#k#*Cs0Vk#+C#VS8s$$s/>&Ms$%&Ms+{k##s,d#k##%#,IISP*TU#VS}#s/E&M$,IISQ*S~#7#s/I&M#k##s,n#k##(#WS8s0Gs/MTLP(s/N,IIT#*T$#7#s/QAs/R#/%s/S%$##C'#k##s,h#Q)s/W,IISg*T%#/#s/Z&M#0$s/\'$#k##s,i#R(s/_,IIS+*T&#/#s/b0s/c#&$M'$#k##s,l#S(s/g,IIS-*T'#7#s/j#C#Mk##s-##T&s/m,IIT(*T)#/#s/p#C#$k##s-)#7&s/s,IISB*T*#/#s/v)U%$s3z#P#s/y)U&$s3}#7#s/|As/}#/%s/~%$##C'#k##s-7#Q)s0&)U'$s4*#/#s0)&M#0$s0+'$#k##s-8#R(s0.)U($s42#/#s010s02#&$M'$#k##s-;#S(s06)U)$s4:#7#s09#C#Mk##s-N#T&s0<)U*$s4@#/#s0?#C#$k##s-T#7&s0B)U+$s4F#/#s0EUU,SrVU-C#USHs,\USH#VS:C#WSqC&#WSqC's,^8C#s,]8C%#VU.Cs0OWU/C#s,`USH*VS:C#VS:C-WSqC/#8Cs,gs+%8Cs,i#8C%#8C0#8C)#8C,#VSm#SnVTV0#WSYSI#s,h2Cs,eQs,d2C#Os,e2Cs,fN#2Cs)eQs+*2Cs+,Q#2C%L#?s4k>#HC#WS[Cs,d#?s4qHC#LC%#4Cs,PS2#5s,jKDDJ#S#+s,kKDDJs,fs,e#4Cs,jSJs,k5s,mKDDJ#S#?s,g?#HC#4Cs,oS)#5s,rKDDJ#S#[T=s,sKDDJ#s+2+s,tKDDJ)s,n#WS[Cs,ts,XLC#(4Cs,_S2#5s,xKDDJ#S#+s,yKDDJs,ts,s#4C5S2s,x5s,{KDDJ#S#4Cs,sSJs,b5s,}KDDJ#S#4Cs,fS)s,u5s-#KDDJ#S#WS[Cs,cs-#4C#S)s,h5s-&KDDJ#S#+s-'KDDJ&s,}#+s-(KDDJ)s,~#+s-)KDDJ,s-##+s-*KDDJ/s-$#+s-+KDDJ5s-%#+s-,KDDJ?s-&#l#-#s,Xs,Rl#.s#+s-/#l#/s#2s-:#j#0C#j#1C#j#2C#j#3C#j#4C#j#5C#j#6C#j#8S*#%s+?R#CN#k##s,R#&MQ'#S&k##s.J#As1@P%#S$#CR#k##s,Y#%Rs1D0Q#AS%s1F&#Qk##s+C#k##&#k##s,[#k##*#k##/#k##3#k#0C#k#1C#k#2C#k#3C#k#4C#k#5C#k#6C#k#8S*#0S+s1V$s5YTW,IISj*T+#)TW$s5]#bE(NS+L'%#S-QS/S4S=SNShl#9s#&*#l#Xs#wC#l#Ys#{C#l#Zs$&s#}#l#[s$-s$(#l#\s$6s$/#l#]s$?s$8#l#^s$Is$A#l#:s0{C#l#;s.`C#l#<s.Ps.N#l#=s.Ts.R#l#>s.Zs.V#l#?s._s.\#l#@s.fs.a#l#As1(C#l#Bs.~C#l#Cs.ls.j#l#Ds.ps.n#l#Es.ws.r#l#Fs.}s.y#l#Gs/*s/##l#)s$[C#l#Hs$_C#l#Is$fs$a#l#Js$ms$h#l#Ks$vs$o#l#Ls%#s$x#l#Ms%-s%%#l#Os%/s/3#l#Ps%8s%1#l#_s/<s/8#l#`s%As%=#&s%zs&dm#$#Ds%|s&f#l#Ms%Hs%F#?s#o?#?#?#?#?#?#?#UTH#%s%x#VS}#s20&M$,IIS@*So#.IIS@*So#%%#%#+7#s28&M#k##s/]#k##,#.IISQ*S~#%s%T#%#3P#s2@.IIT#*T$#%s%Q#%#87#s2EAs2F#/%s2G%$##C'#k##s/\#Q)s2K.IISg*T%#%s%S#%#s##/#s2P&M#0$s2R'$#k##s/_#R(s2U.IIS+*T&#%s%U#%#s#-/#s2Z0s2[#&$M'$#k##s/d#S(s2_.IIS-*T'#%s%W#%#s#77#s2d#C#Mk##s/y#T&s2g.IIT(*T)#%s%Y#%#s#?/#s2l#C#$k##s0%#7&s2o.IISB*T*#%s%[#%#s#G/#s2t8Cs/+s/)8Cs%.#WSqCs%2s%'WSqCs%3s//8C#s%&8Cs%)#8Cs%3#8C'#8Cs%/#VSm#SnVTV+#WSYSI#s//2Cs/(S$s/+2C#Os/,2Cs/-N#2Cs-MRs//2Cs-OS$#2C%L#4Cs.hS2s${5s/*KDDJ#S#+s/+KDDJs/&s/%#4Cs$vSJs/+5s/-KDDJ#S#[T=s/.KDDJs.b#+s//KDDJs$|s/)#HCs$|LCs.u#VT5Cs#dLC$#WS[Cs/3s.wLC#s%#4C%S2#5s/7KDDJ#S#+s/8KDDJs/3s/2#4Cs.xS)s/05s/:KDDJ#S#4Cs/2SJ,5s/<KDDJ#S#LCs.|s/<WS[Cs/%s/=4C$S)#5s/@KDDJ#S#+s/AKDDJ's/;#+s/BKDDJ*s/<#+s/CKDDJs%&s/=#+s/DKDDJ.s/>#+s/EKDDJ8s/?#+s/FKDDJ=s/@#l#-#s.rs.ll#.Bs/I#l#/s#)s/T#j#0C#j#1C#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#8S*#%s.jS%#CL#k##s.m#0S$s3X'S>#k##s0e#%RQ%#s$0As3]O%#S&#C%#k##s.v##CS$M&OQ0S$s.k%S%s3dAQs3e&$#k##&#k##(#k##*#k##,#k##3#k##7#k#0C#k#1C#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#8S*#&MS+.IISj*T+#cE%NS+L#s%$s$~S-s$|QS/S4S=SaSil#9s#('#l#Xs&8C#l#Ys&<C#l#Zs&Cs&>#l#[s&Js&E#l#\s&Ss&L#l#]s&\s&U#l#^s&fs&^#l#:s3<C#l#;s0}C#l#<s0ms0k#l#=s0qs0o#l#>s0ws0s#l#?s0|s0y#l#@s1's0~#l#As3EC#l#Bs1?C#l#Cs1-s1+#l#Ds11s1/#l#Es18s13#l#Fs1>s1:#l#Gs1Gs1@#l#)s#zC#l#Hs$$C#l#Is$-s$&#l#Js$6s$/#l#Ks$As$8#l#Ls$Ls$C#l#Ms$Xs$N#l#Os'Ls1P#l#Ps1Xs1T#l#_s$ks$`#l#`s'^s'Z#&s)#s(7m#$#Ds)%s(9#l#Ms'es'c#XSes'ms'ls$|#WTXs'ps'o#m##s(iXSes(ss(js's#XS|s+ms)&s(z#l#as)7s)6#l#Ms2)s2'#l#bs)As)@#l#Ms5Xs5V#j#as)G#j#bs)P#V#LEj##s)W#j##s)w#;s)xs)ss)a#El#cs*%s)~#j#cs*/#j#ds*:#V#LEj##s*=#j##s*d#;s*es*[s*I#Ej#Ms*h#j#Us+v#V#LEj##s*v#j#%s+y#YT>s+zs+8s+(#El#Ts+Ks+E#l#Ms7ns7k#j#Ts+Y#U#Ej##s+q#XT;HS]SGs2[#F#G9HS^E(#s+\6HS^E3s+^#1%#j#Us,+#XEs,,#s+YL#F%G's+X#j#%s,/#=s,0#9HSLE(#s+T6HSLE3s+V#1%##F#G's+[#j#%s,8#=s,9#j###s+E9HSME(#s+C6HSME3s+E#1%##F#G's+J#j#%s,B#U#E9HS_E(#s+?6HS_E3s+A#1%##F#G's+F#9HSpL(#s+:6HSpL3s+<#1%##F#G's+B#j###s+(9HS<N(#s+&6HS<N3s+(#1%##F#G9HS=O(#s*}6HS=O3s+##1%##F#G9HSNR(#s*y6HSNR3s*{#WSf%#E#F&G#F%G'$#9HS{S%(#s*u#F#G6HS{S%3s*x##F#G'&#j###s*c6HS`Q3s*c##F#G9HS\S$(#s*\#F#G6HSaS&3s*\##F#G9HT4SOD#s*UN&$s*V6HSWS?Ds*U#P0s*V$9HS9S,USb#6HS9S,USc#XSdCC%#-s-1#s*9,CC$(#s*7.CC&(s*7#1%##F#G9HSXS3USb#6HSXS3USc#XSdCC%#-s-=#s)]'s)g#j#%s-5#-s-@s)Ps)[#s-As)ns)Q-s-Bs)Rs)P#s-Cs)Ss)S-s-Ds)Ts)SVT7s-Es)UWT<%$#WU0('#XSes)d*s)^#XS|s-?,S'#ZEs-@s-Js*ms*js)Z#l#Ms*)s*$#(As*P(s*O@#F$G#F$G9HTUSPVS}#s6+&M$9HS~SQ7#s6.&M#k##s3S#k##'#P's629HT$T#7#s64As65#/%s66%$##C'#k##s3K#Q)s6:9HT%Sg/#s6<&M#0$s6>'$#k##s3K#R(s6A9HT&S+/#s6C0s6D#&$M'$#k##s3M#S(s6H9HT'S-7#s6J#C#Mk##s3_#T&s6M9HT)T(/#s6O#C#$k##s3d#7&s6R9HT*SB/#s6T9HT+SjbEs'^NS+Ls']#s'YS-QS/S4S=SNShl#9s'|s'`#l#Xs(qC#l#Ys(uC#l#Zs(|s(w#l#[s)'s(~#l#\s)0s))#l#]s)9s)2#l#^s)Cs);#l#:s5uC#l#;s3ZC#l#<s3Js3H#l#=s3Ns3L#l#>s3Ts3P#l#?s3Ys3V#l#@s3`s3[#l#As5~C#l#Bs3xC#l#Cs3fs3d#l#Ds3js3h#l#Es3qs3l#l#Fs3ws3s#l#Gs4$s3y#l#);C#l#H>C#l#Is#$@#l#Js#*s#&#l#Ks#2s#,#l#Ls#:s#4#l#Ms#Cs#<#l#Os*)s4-#l#Ps#Ls#F#l#_s46s42#l#`s*;s*7#&s*Us+^m#$#Ds*Ws+`#l#Ms*Bs*@#WS8s7vs6|TM6HSoS@%#s'RVS}#s7#&M$6HT$T#%#s'V7#s7'&M#k##s4L#k##(#6HS~SQ%#s'\P#s7-As7.)/+s7/%$##C-#k##s4D#Q/s736HT%Sg%#s'e/#s76&M#0$s78'$#k##s4E#R(s7;6HT&S+%#s'm/#s7>0s7?#&$M'$#k##s4H#S(s7C6HT'S-%#s'u7#s7F#C#Mk##s4[#T&s7I6HT)T(%#s'{/#s7L#C#$k##s4a#7&s7O6HT*SB%#s(%/#s7R2Cs)SPs3Y2Cs3ZN#2Cs0YOs1z2Cs3\Q#2C%L#[T=s3VKDDJs1qs'++s3WKDDJs)Hs3Q#LCs'*s'(4C#S2s'&5s3ZKDDJ#S#+s3[KDDJs3Vs3U#4Cs3SSJs'.5s3]KDDJ#S#+s3^KDDJ#s3Xs&|+s3_KDDJs''s3Y#+s3`KDDJs)Cs3Z#+s3aKDDJ(s3[#+s3bKDDJ-s3\#+s3cKDDJs':s3]#l#-#s33s3-l#.2s3f#l#/s'Fs3q#j#0C#j#1C#j#2C#j#3C#j#4C#j#5C#j#6C#j#8S*##CLs)9k##s3,#0Qs7s'S&#k##s5$#%S%s(J%s&xS$#C$#k##s33#0QS$k###s&sk##s1{#k##s32#k##'#k##,#k##0#k#0C#k#1C#k#2C#k#3C#k#4C#k#5C#k#6C#k#8S*#6HT+SjbEs&rNS+L#s)5S-s)1QS/S4S=SaSil#9=%#l#Xs*IC#l#Ys*MC#l#Zs*Ts*O#l#[s*[s*V#l#\s*ds*]#l#]s*ms*f#l#^s*ws*o#l#:s7MC#l#;s52C#l#<s4~s4|#l#=s5&s5$#l#>s5,s5(#l#?s51s5.#l#@s58s53#l#As7VC#l#Bs5PC#l#Cs5>s5<#l#Ds5Bs5@#l#Es5Is5D#l#Fs5Os5K#l#Gs5Xs5Q#l#)s#QC#l#Hs#UC#l#Is#\s#W#l#Js#cs#^#l#Ks#ls#e#l#Ls#us#n#l#Ms#|s#w#l#Os$+s$$#l#Ps$/s5b#l#_s5js5f#l#`s+os+k#&s-4s,+m#$#Ds-6s,-#l#Ms+vs+t#XSes%.s%-s$7#WTXs%1s%0#m##s%GXSes%Ns%Hs%4#XS|s/~s-7s%P#l#as%Ws%V#l#Ms6:s68#l#bs%\s%[#l#Ms9is9g#j#as%`#j#bs%d#V#LEj##s%i#j##s%r#;s%ss%ps%n#El#cs%zs%w#j#cs&$#j#ds.K#V#LEj##s&-#j##s.u#;s.vs&7s&5#Ej#Ms&>#j#Us0+#V#LEj##s&H#j#%s0.#YT>s0/s&Us&S#El#Ts&bs&^#l#Ms<#s;|#j#Ts&k#U#Ej##s0$#ZSys0's0%s/os&p#El#Ts0.s0+#VS.HSGBS;NS;Os0:$#Is0;s0E&#-s0FE##Fs0?G'$#j#%s0I#=s0J#m#-#XEs0Ls0Cs0=#l#Ms0Qs0N#@HSKSl)S7C$##F#Gm#'#l#Ts0bs0^#j#Ts0j#j#es0r#V#LEj##s0|#j##s14#;s15s1.s1(#El#Ts1As1>#j#Ts1O#U#Ej##s7i#ZSys7ys7js7ds1`#El#Ts8's8$#j#fs8N#j#gs8P#V#LEj##s8Q#j##s8S#;s8Ts8Ss8A#Ej#Ms8S#j#hs8X#V#LEj##s8V#j##s8[#;s8\s8Xs8L#Ej#Ms8X#j#is8`#V#LEj##s8[#j##s8c#;s8ds8]s8W#El#jU1s8f#j#ks8h#j#ls8m#V#LEj##s8t#j##s9$#;s9%s9#s8y#Ej#Ms9+#j#ms94#V#LEj##s9:#j##s9M#;s9Ns9Is9C#El#Ms9ds9S#j#ns9f#j#Qs9m#V#LEj##s9w#j##s:)#;s:*s:)s:##El#Ms:4s:3#l#os:]s:\#l#Ms:os:m#l#ps:is:h#l#Ms:qs:o#j#os;+#j#ps;6#V#LEj##s;>#j##s;T#;s;Us;Os;I#El#cs;_s;\#j#cs;k#j#qs;x#V#LEj##s;|#j##s<>#;s<?s<3s<-#Ej#Ms<B#j#,s<}#V#LEj##s<O#j#%s=$#YT>s=%s<bs<]#El#rs<ts<n#l#Ms=+s=(#l#sPs=S#l#ts=Ys=X#l#Ms=]s=\#j#ts=r#j#rs=u#j#us>$#WTEROL:L@HROWU2%$#m#'#j#vs>$#j#wU3#j#xs>'#j#ys>,#j#zU4#j#{U5##"). Qed.

  (* [comment removed for export] *)
  Lemma lazy_cover_hid : forall E cs R FULL model,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> lazy_cover (hid A argH E cs model) (m_vm_lazy model) (allowA A E cs).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. apply (lazy_cover_vis E cs R FULL model HC w Hlz).
    unfold Hv. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hh]. exact Hh.
  Qed.

  Lemma H_off_segments_vis : forall E cs model, H_off_segments SEGS (Hv E cs model).
  Proof.
    intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
    apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
    apply SEGS_in_hull. exact Hh.
  Qed.

  (* [comment removed for export] *)
  Lemma mrestrict_Hv_high : forall E cs model FULL (a : word),
    TOP model <= bv_unsigned a -> mrestrict (Hv E cs model) FULL a = FULL a.
  Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Mr_grows_Hv : forall E cs model FULL,
    mem_grows (Mr A argH E cs model FULL) (mrestrict (Hv E cs model) FULL).
  Proof.
    intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
    destruct (argH E a), (vis A E cs model a); cbn; auto.
  Qed.

  Lemma munrestrict_mrestrict : forall (H : word -> bool) FULL, munrestrict H FULL (mrestrict H FULL) = FULL.
  Proof.
    intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
  Qed.

End NodesD.
