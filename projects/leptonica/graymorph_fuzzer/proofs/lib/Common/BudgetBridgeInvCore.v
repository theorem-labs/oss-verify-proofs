(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import BudgetBridgeCore BudgetBridgeTac BudgetBridgeMm BudgetBridgeMove.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeInvCore () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.BudgetBridgeInvCore."; "OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.BudgetBridgeMm."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1pair"; "1prod"; "1unit"; "2eq"; "3Z"; "4arg"; "4emit"; "4get_fds"; "4get_model"; "4get_vmmaps"]; ["4input"; "4modify"; "4sysno"; "5FdEntry"; "5Model"; "5SyscallInput"; "5VmMaps"; "5event"; "5m_vmmaps"; "5map_remove"; "5maps_subtract"; "5two_pow_64"; "5vm_forget_range"; "5vm_maps"; "5vm_resize_backing"; "5with_vmmaps"]; ["6brk_maps_next"; "6forget_vm_ranges"; "6with_mmap_backing"; "6with_mmap_replacement"; "7Bnd"; "7Pres1"; "8maps_bounded"; "9add"; "9le"; "0a"; "0b"; "0dst"; "0evs"; "0f"; "0h"; "0hi"]; ["0i"; "0k"; "0l"; "0l1"; "0l2"; "0lo"; "0m"; "0n"; "0new_n"; "0old"; "0old_n"; "0r"; "0req"; "0rs"; ":bv"; ":bv_unsigned"]; ["0sz"; "0x"]]).
Definition Bnd (m : Model) : Prop := maps_bounded (vm_maps (m_vmmaps m)).
Definition Pres1 {A} (c : Sys A) (i : SyscallInput) (m : Model) : Prop :=
Bnd m -> forall x m' e, c i m (Ok x m' e) -> Bnd m'.
Lemma pres1_bind {A B} (c : Sys A) (k : A -> Sys B) i m :
Pres1 c i m ->
(forall x m1 e1, c i m (Ok x m1 e1) -> Pres1 (k x) i m1) ->
Pres1 (bind c k) i m.
Proof.
intros Hc Hk Hb y m2 e H. cbn in H.
destruct H as (x & m1 & e1 & e2 & H1 & H2 & _).
exact (Hk x m1 e1 H1 (Hc Hb x m1 e1 H1) y m2 e2 H2).
Qed.
Lemma pres1_pure {A} (v : A) i m : Pres1 (pure v) i m.
Proof. intros Hb x m' e H. unfold pure in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_get : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "9'E'D&Q5&>r2r1%445321pS>61pS281").
Proof. intros i m. intros Hb x m' e H. unfold get_model in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_input : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "9'E'D&Q5&@r2r1%446321pS>61pS281").
Proof. intros i m. intros Hb x m' e H. unfold input in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_sysno : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "<'E'D&Q5'QNyR0%211&Br2r1%744321pS>91pS2;1").
Proof. intros i m. intros Hb x m' e H. unfold sysno in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_arg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "@'4'E'D&Q5'QNyR0%211&;r3%211r2r1%946321pS>;1pS2=1pS4?1").
Proof. intros k i m. intros Hb x m' e H. unfold arg in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_get_fds : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "A'E'D&Q5'3'7'QNyR0%211'C%5221%711&=r2r1%<44321pS>>1pS2@1").
Proof. intros i m. intros Hb x m' e H. unfold get_fds in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_get_vmmaps : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore ":'E'D&Q5'F&?r2r1%544321pS>71pS291").
Proof. intros i m. intros Hb x m' e H. unfold get_vmmaps in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_choose {A} (P : A -> Prop) i m : Pres1 (choose P) i m.
Proof. intros Hb x m' e (y & _ & H). injection H as _ <- _. exact Hb. Qed.
Lemma pres1_emit : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "@'3'G%211'E'D&Q5'8&<r3%211r2r1%746321pS>91pS2;1pRJ=1").
Proof. intros evs i m. intros Hb x m' e H. unfold emit in H. injection H as _ <- _. exact Hb. Qed.
Lemma pres1_unmodeled {A} i m : Pres1 (@unmodeled A) i m.
Proof. intros Hb x m' e H. discriminate H. Qed.
Lemma pres1_modify : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "E'Dp011'E&Q4r1%211r4r2%211%611p051&Q5'8&A%118r3%544219p071pS>B1pS2A1pRLC1").
Proof. intros f i m. intros Hf Hb x m' e H. unfold modify in H. injection H as _ E _. rewrite E. exact (Hf Hb). Qed.
Lemma pres1_alt {A} (c d : Sys A) i m : Pres1 c i m -> Pres1 d i m -> Pres1 (alt c d) i m.
Proof. intros Hc Hd Hb x m' e [H|H]; [exact (Hc Hb x m' e H) | exact (Hd Hb x m' e H)]. Qed.
Lemma pres1_reader {A} (s : SyscallInput -> Sys A) i m :
Pres1 (s i) i m -> Pres1 (fun j => s j j) i m.
Proof. intros H. exact H. Qed.
Lemma m_vmmaps_vm_forget_range : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "@':'D'9'F&H&Lr3r2r1%43321%611%713%:3921pS><1pS0>1pS<?1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_forget_vm_ranges : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "D'3'7'QNyR0%211%4211%611'D'9'F&H&Q1r2r1%3221%511%613%93821pS>;1pSL=1").
Proof. induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "D'QNyR0%211'D'9'F&H&Q2r4r3r2r1%544321%711%813%;3:21pS>=1pS@?1pRD@1pRLA1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma m_vmmaps_with_mmap_replacement : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "D'QNyR0%211'D'9'F&H&Q3r4r3r2r1%544321%711%813%;3:21pS>=1pS@?1pRD@1pRLA1").
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.
Lemma m_vmmaps_with_vmmaps' : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "<'F'D'9&H&Or2r1%3221%511%73914pS>91pRN;1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_resize_backing : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "I'1'QNyR0%211'D'9'F&H&Nr6r5r4r3r2r1%76654321%911%:13%=3<21pS>?1pSBA1pRHB1pSFC1pSDD1pRFH1").
Proof. reflexivity. Qed.
Create Rewrite HintDb bb_vmm.
#[export] Hint Rewrite m_vmmaps_vm_forget_range m_vmmaps_forget_vm_ranges m_vmmaps_with_mmap_backing
m_vmmaps_with_mmap_replacement m_vmmaps_with_vmmaps' m_vmmaps_vm_resize_backing : bb_vmm.
Ltac bnd_tac := fail.
Lemma maps_bounded_nil : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "9&Q6(5'7'QNyR0%211%4211%611%811").
Proof. intros a sz []. Qed.
Lemma maps_bounded_cons : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "O'QNyR0%211'3'7%1233%311&Q8&Q7&QOr3%22:1r2%42<1%6231&K%9221&Q6%116(2(6r5r4%34EE21%53C1>%811p081p0;1pS6F1pT2K1pRDL1").
Proof. intros a sz l H1 H2 b s [E|Hin]; [injection E as <- <-; exact H1 | exact (H2 b s Hin)]. Qed.
Lemma maps_bounded_app : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "C'3'7'QNyR0%211%4211%611&Q6r2%211&0r4r3%33821%711p061p071pS:;1pS8<1").
Proof. intros l1 l2 H1 H2 a s Hin. apply in_app_or in Hin as [H|H]; eauto. Qed.
Lemma maps_bounded_map_remove : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "A'3'7'QNyR0%211%4211%611&Q6r2%211&Ir3%2214%611p051pT4;1pS6:1").
Proof.
intros l x H a s Hin. unfold map_remove in Hin. apply filter_In in Hin. exact (H a s (proj1 Hin)).
Qed.
Lemma maps_bounded_subtract : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "D'3'7'QNyR0%211%4211%611':&Q6r3%211&Jr4r2%33251%711p061pS0:1pS<;1pS6=1").
Proof.
intros l lo hi H b s Hin.
destruct (maps_subtract_In l lo hi b s Hin) as (a & sz & Hin0 & Hin1).
pose proof (iv_subtract_within a sz lo hi b s (H a sz Hin0) Hin1). pose proof (H a sz Hin0). lia.
Qed.
Lemma maps_bounded_brk_maps_next : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeInvCore "B'F'QNyR0%211&Q6&Mr3%211%411&Q0r4r2%33261%911p061pSH<1pSJ=1pRNA1").
Proof.
intros h req r H. unfold brk_maps_next.
destruct (_ && _); [apply maps_bounded_subtract; exact H|].
apply maps_bounded_app; [|exact H].
unfold brk_grants. destruct (brk_is_grow req r (vm_brk h)) eqn:E; [|apply maps_bounded_nil].
unfold brk_is_grow in E. apply andb_true_iff in E as [_ E]. apply Z.ltb_lt in E.
apply maps_bounded_cons; [|apply maps_bounded_nil].
pose proof (wrange r). pose proof (wrange (vm_brk h)).
rewrite bv_sub_unsigned. unfold bv_wrap. rewrite Z.mod_small; [unfold two_pow_64 in *; lia|].
change (bv_modulus 64) with two_pow_64. unfold two_pow_64 in *. lia.
Qed.
Ltac bfacts :=
repeat match goal with
| H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
| H : _ /\ _ |- _ => destruct H
| H : negb _ = false |- _ => apply negb_false_iff in H
| H : negb _ = true |- _ => apply negb_true_iff in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
end.
Ltac bnd_arith :=
unfold mremap_source_b, mremap_inplace_grow_b, mremap_fresh_b in *; cbv zeta in *;
bfacts;
repeat match goal with H : ?x = ?y |- _ => is_var x; lazymatch type of x with word => subst x end end;
repeat match goal with
| H : context [alloc_top ?h] |- _ =>
lazymatch goal with H' : alloc_top h < two_pow_64 |- _ => fail | _ => pose proof (alloc_top_lt' h) end
| |- context [alloc_top ?h] =>
lazymatch goal with H' : alloc_top h < two_pow_64 |- _ => fail | _ => pose proof (alloc_top_lt' h) end
end;
repeat match goal with
| |- context [bv_unsigned ?w] =>
lazymatch goal with H : 0 <= bv_unsigned w < two_pow_64 |- _ => fail | _ => pose proof (wrange w) end
end;
repeat match goal with
| |- context [page_round_up_Z (bv_unsigned ?w)] =>
lazymatch goal with
| H : 0 <= page_round_up_Z (bv_unsigned w) |- _ => fail
| _ => pose proof (page_round_up_Z_nonneg' (bv_unsigned w) (proj1 (wrange w)))
end
end;
u64s; unfold two_pow_64 in *; lia.
Ltac bnd_tac ::=
first
[ apply maps_bounded_cons; [ bnd_arith | ]
| apply maps_bounded_map_remove
| apply maps_bounded_subtract
| apply maps_bounded_brk_maps_next
| progress (unfold brk_model_next, mremap_maps_next, mmap_fixed_destroyed_next,
mmap_fixed_noaccess_span_next, mmap_fixed_rw_span_next, mmap_fixed_rw_next);
cbn [vm_maps] ].
Ltac bnd_leaf :=
let HB := fresh "HB" in
intros HB; unfold Bnd in *;
repeat (cbv beta iota zeta;
first [ exact HB
| progress cbn [vm_maps]
| progress (autorewrite with bb_vmm)
| bnd_tac
| match goal with
| |- context [match ?e with _ => _ end] =>
let x := innermost e in destruct x eqn:?
end
| match goal with
| |- maps_bounded (vm_maps (m_vmmaps (?f _))) => let h := headc f in progress (unfold h)
| |- maps_bounded (vm_maps (m_vmmaps (?f _ _))) => let h := headc f in progress (unfold h)
end ]).
Ltac pres_out He :=
lazymatch type of He with
| get_model _ _ _ => cbv [get_model] in He; injection He; intros; subst
| input _ _ _ => cbv [input] in He; injection He; intros; subst
| get_vmmaps _ _ _ => cbv [get_vmmaps] in He; injection He; intros; subst
| errno_from _ _ _ _ =>
cbv [errno_from choose] in He;
let r := fresh "r" in let Hr := fresh "Hr" in
destruct He as (r & Hr & He); injection He; intros; subst
| get_fds _ _ _ => cbv [get_fds] in He; injection He; intros; subst
| sysno _ _ _ => cbv [sysno] in He; injection He; intros; subst
| arg _ _ _ _ => cbv [arg] in He; injection He; intros; subst
| pure _ _ _ _ => cbv [pure] in He; injection He; intros; subst
| modify _ _ _ _ => cbv [modify] in He; injection He; intros; subst
| choose _ _ _ _ =>
cbv [choose] in He;
let r := fresh "r" in let Hr := fresh "Hr" in
destruct He as (r & Hr & He); injection He; intros; subst
| _ => idtac
end.
Ltac pres_step :=
lazymatch goal with
| |- Pres1 (bind _ _) _ _ =>
eapply pres1_bind;
[ | let x := fresh "x" in let m' := fresh "m'" in let e := fresh "e" in
let He := fresh "He" in intros x m' e He; cbv beta; pres_out He ]
| |- Pres1 (pure _) _ _ => apply pres1_pure
| |- Pres1 get_model _ _ => apply pres1_get
| |- Pres1 input _ _ => apply pres1_input
| |- Pres1 sysno _ _ => apply pres1_sysno
| |- Pres1 (arg _) _ _ => apply pres1_arg
| |- Pres1 get_fds _ _ => apply pres1_get_fds
| |- Pres1 get_vmmaps _ _ => apply pres1_get_vmmaps
| |- Pres1 (choose _) _ _ => apply pres1_choose
| |- Pres1 (emit _) _ _ => apply pres1_emit
| |- Pres1 unmodeled _ _ => apply pres1_unmodeled
| |- Pres1 (alt _ _) _ _ => apply pres1_alt
| |- Pres1 (modify _) _ _ => apply pres1_modify; bnd_leaf
| |- Pres1 (let _ := _ in _) _ _ => cbv zeta
| |- Pres1 ?X _ _ =>
lazymatch X with
| (match _ with _ => _ end) =>
match X with
| context [match ?e with _ => _ end] => let x := innermost e in destruct x eqn:?
end; cbv beta iota zeta
| _ => let h := headc X in progress (unfold h); cbv beta
end
end.
Ltac pres_auto := repeat pres_step.
