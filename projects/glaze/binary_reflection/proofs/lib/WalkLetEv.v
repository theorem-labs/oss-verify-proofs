(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
From Ltac2 Require Ltac2.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac wd_eexists :=
  lazymatch goal with
  | |- @ex (bvmap 5 word) (fun r => msteps _ _ (mkst r _ _ _) /\ _) =>
      let rf := fresh "wdRF" in
      evar (rf : bvmap 5 word);
      refine (ex_intro _ rf _);
      lazymatch goal with |- ?A /\ ?B => let B' := eval unfold rf in B in change (A /\ B') end
  | |- _ => eexists
  end.

(* [comment removed for export] *)
Ltac wd_refl :=
  lazymatch goal with
  | |- msteps _ (mkst ?X _ _ _) (mkst ?F _ _ _) =>
      try (match goal with H := ?b |- _ => constr_eq H F; is_evar b; unify b X end)
  | |- _ => idtac
  end;
  first [ exact (mst_refl _ _) | apply mst_refl ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wd_in_reg_b : forall (r : reg) (L : list reg), existsb (fun y => bv_eqb r y) L = true -> In r L.
Proof.
  intros r L H. apply existsb_exists in H as [y [Hy E]]. apply rl_bv_eqb_true_eq in E. subst y. exact Hy.
Qed.

Lemma wd_incl_reg_b : forall L1 L2 : list reg,
  forallb (fun x => existsb (fun y => bv_eqb x y) L2) L1 = true -> forall r, In r L1 -> In r L2.
Proof.
  intros L1 L2 H r Hr. rewrite forallb_forall in H. apply wd_in_reg_b, H, Hr.
Qed.

(* [comment removed for export] *)
Ltac wd_reg_lit r := lazymatch r with @BV _ ?z _ => is_Z_lit z end.
Ltac wd_regs_lit L :=
  lazymatch L with
  | nil => idtac
  | cons ?r ?t => wd_reg_lit r; wd_regs_lit t
  end.

Ltac wd_in_list :=
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch G with
  | In ?r ?L => wd_reg_lit r; wd_regs_lit L; change G; exact (wd_in_reg_b r L (@eq_refl bool true))
  end.
Ltac in_list_fast := first [ wd_in_list | (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat first [ left; reflexivity | right ] ].

Ltac wd_incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  let T := type of Hr in let T' := eval cbv beta in T in
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch T' with
  | In r ?L1 =>
      lazymatch G with
      | In r ?L2 => wd_regs_lit L1; wd_regs_lit L2; change G; exact (wd_incl_reg_b L1 L2 (@eq_refl bool true) r Hr)
      end
  end.
Ltac incl_list_fast :=
  first [ wd_incl_list
        | let r := fresh "r" in let Hr := fresh "Hr" in
          intros r Hr; cbn [In] in Hr;
          repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr ].

Ltac in_list ::= in_list_fast.
Ltac incl_list ::= incl_list_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wd_uZ : forall (z : Z) (P : Z -> Prop), ((0 <= z)%Z /\ (z < 2 ^ 64)%Z) /\ P z -> P (bv_unsigned (Z_to_bv 64 z)).
Proof. intros z P [[H1 H2] HP]. rewrite (u_Z2bv z H1 H2). exact HP. Qed.
Lemma wd_z2n : forall (z : Z) (P : Z -> Prop), (0 <= z)%Z /\ P z -> P (Z.of_nat (Z.to_nat z)).
Proof. intros z P [H1 HP]. rewrite (Z2Nat.id z H1). exact HP. Qed.
(* [comment removed for export] *)
Ltac wd_unorm1 :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ =>
               lazymatch goal with |- ?G =>
                 let P := eval pattern (bv_unsigned (Z_to_bv 64 z)) in G in
                 lazymatch P with ?F _ => apply (wd_uZ z F) end
               end
             end
         end.
Ltac wd_z2n1 :=
  repeat match goal with |- context [Z.of_nat (Z.to_nat ?z)] =>
    lazymatch goal with |- ?G =>
      let P := eval pattern (Z.of_nat (Z.to_nat z)) in G in
      lazymatch P with ?F _ => apply (wd_z2n z F) end
    end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Module WdX20.
Import Ltac2.Ltac2.
Ltac2 rec has_var (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var _ => true
  | Constr.Unsafe.App f args => if has_var f then true else Array.exist has_var args
  | Constr.Unsafe.Prod b t => if has_var (Constr.Binder.type b) then true else has_var t
  | Constr.Unsafe.Lambda b t => if has_var (Constr.Binder.type b) then true else has_var t
  | Constr.Unsafe.LetIn b v t => if has_var (Constr.Binder.type b) then true else if has_var v then true else has_var t
  | Constr.Unsafe.Cast c _ t => if has_var c then true else has_var t
  | Constr.Unsafe.Case _ _ _ x bl => if has_var x then true else Array.exist has_var bl
  | Constr.Unsafe.Proj _ _ c => has_var c
  | Constr.Unsafe.Evar _ args => Array.exist has_var args
  | Constr.Unsafe.Fix _ _ tys bds => if Array.exist (fun b => has_var (Constr.Binder.type b)) tys then true else Array.exist has_var bds
  | _ => false
  end.
Ltac2 goal_has_var () := if has_var (Control.goal ()) then () else Control.zero Not_found.
Ltac2 rec is_unat (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ => if Int.equal (Array.length args) 1 then is_unat (Array.get args 0) else false
      | _ => false
      end
  | _ => false
  end.
Ltac2 check_unat (c : Ltac1.t) := if is_unat (Option.get (Ltac1.to_constr c)) then () else Control.zero Not_found.
End WdX20.
Ltac wd_goal_has_var := ltac2:(Control.enter WdX20.goal_has_var).
(* [comment removed for export] *)
Ltac wd_natlit := ltac2:(n |- WdX20.check_unat n).
Ltac wd_zofnat :=
  repeat match goal with |- context [Z.of_nat ?n] => wd_natlit n; let z := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with z end.
Ltac wd_ulia := first [ solve [ wd_unorm1; wd_zofnat; lia ] | unorm; lia ].

(* [comment removed for export] *)
Lemma wd_rdn_wbytes_out3 : forall segs bs m (addr a : word) n,
  ((bv_unsigned a + Z.of_nat n <= bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)
   /\ bv_unsigned a + Z.of_nat n <= 2^64 /\ bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof. intros segs bs m addr a n (H1 & H2 & H3). apply rdn_wbytes_out; assumption. Qed.
(* [comment removed for export] *)
Ltac wd_cbn_nc := lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end.
Ltac wd_ulia_c := first [ solve [ wd_unorm1; wd_cbn_nc; wd_zofnat; lia ] | unorm; wd_cbn_nc; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wd_rf := bvmap 5 word.

Ltac wd_gres_fin_some_chk X r acc R0 w :=
  change (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_some r acc R0 w (@eq_refl bool false) (@eq_refl (option word) (Some w))).
Ltac wd_gres_fin_none_chk X r acc R0 :=
  change (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_none r acc R0 (@eq_refl bool false) (@eq_refl (option word) None)).
Ltac wd_gres_fin_some X r acc R0 w :=
  change_no_check (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_some r acc R0 w (@eq_refl bool false) ltac:(exact_no_check (@eq_refl (option word) (Some w)))).
Ltac wd_gres_fin_none X r acc R0 :=
  change_no_check (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_none r acc R0 (@eq_refl bool false) ltac:(exact_no_check (@eq_refl (option word) None))).

Module WdL2.
Import Ltac2.Ltac2.
Ltac2 Type env := { c_regupd : constant; c_rf : constant; k_BV : constructor; mk_cons : constr; mk_nil : constr; mk_RLP : constr }.
Ltac2 ck (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.zero Not_found end.
Ltac2 kk (r : Std.reference) : constructor := match r with Std.ConstructRef c => c | _ => Control.zero Not_found end.
Ltac2 mk_env () : env :=
  { c_regupd := ck reference:(regupd); c_rf := ck reference:(wd_rf); k_BV := kk reference:(BV);
    mk_cons := constr:(@cons rlp); mk_nil := constr:(@nil rlp); mk_RLP := constr:(RLP) }.
Ltac2 is_const (t : constr) (c : constant) : bool :=
  match Constr.Unsafe.kind t with Constr.Unsafe.Constant c' _ => Constant.equal c c' | _ => false end.
(* [comment removed for export] *)
Ltac2 reg_z (e : env) (t : constr) : constr option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor k _ =>
          if Bool.and (Constructor.equal k (e.(k_BV))) (Int.equal (Array.length args) 3) then Some (Array.get args 1) else None
      | _ => None
      end
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 rec is_num (z : constr) : bool :=
  match Constr.Unsafe.kind z with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => Array.for_all is_num args | _ => false end
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 letbody (e : env) (c : constr) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id =>
      match Control.hyp_value id with
      | Some b => if is_const (Constr.type c) (e.(c_rf)) then Some b else None
      | None => None
      end
  | _ => None
  end.
Ltac2 mkapp (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
(* [comment removed for export] *)
Ltac2 rec walk (e : env) (c : constr) (r : constr) (zr : constr) (acc : constr) : constr * constr * constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Bool.and (is_const f (e.(c_regupd))) (Int.equal (Array.length args) 3) then
        let r0 := Array.get args 0 in let rd := Array.get args 1 in let v := Array.get args 2 in
        let acc' := mkapp (e.(mk_cons)) [| mkapp (e.(mk_RLP)) [| rd; v |]; acc |] in
        if Constr.equal rd r then (acc', r0, Some v)
        else match reg_z e rd with
             | Some zd => if Bool.and (is_num zd) (Bool.neg (Constr.equal zd zr)) then walk e r0 r zr acc' else Control.zero Not_found
             | None => Control.zero Not_found
             end
      else (acc, c, None)
  | _ =>
      match letbody e c with
      | Some b => walk e b r zr acc
      | None => (acc, c, None)
      end
  end.
Ltac2 gres_l2 (x : Ltac1.t) (r : Ltac1.t) : unit :=
  let xc := Option.get (Ltac1.to_constr x) in let rc := Option.get (Ltac1.to_constr r) in
  let e := mk_env () in
  let zr := match reg_z e rc with Some z => if is_num z then z else Control.zero Not_found | None => Control.zero Not_found end in
  let (acc, r0, res) := walk e xc rc zr (e.(mk_nil)) in
  if Constr.equal acc (e.(mk_nil)) then Control.zero Not_found else
  match res with
  | Some w => ltac1:(x r acc r0 w |- wd_gres_fin_some x r acc r0 w) x r (Ltac1.of_constr acc) (Ltac1.of_constr r0) (Ltac1.of_constr w)
  | None => ltac1:(x r acc r0 |- wd_gres_fin_none x r acc r0) x r (Ltac1.of_constr acc) (Ltac1.of_constr r0)
  end.
End WdL2.
Ltac wd_gres_l2 := ltac2:(x r |- WdL2.gres_l2 x r).

(* [comment removed for export] *)
Ltac wd_isletR X := is_var X; let T := type of X in lazymatch T with wd_rf => idtac end.

(* [comment removed for export] *)
Ltac wd_setR_on :=
  lazymatch goal with
  | |- msteps ?s (mkst (regupd ?R ?rd ?v) ?pc ?m ?rom) ?F =>
      lazymatch R with
      | regupd _ _ _ =>
          let x := fresh "wR" in
          refine (let x : wd_rf := R in _);
          change (msteps s (mkst (regupd x rd v) pc m rom) F)
      | _ => idtac
      end
  | |- _ => idtac
  end.
Ltac wd_setR := idtac.
(* [comment removed for export] *)
Ltac wd_zx t :=
  match goal with
  | x := _ : wd_rf |- _ => lazymatch t with context [x] => let t' := eval unfold x in t in wd_zx t' end
  | _ => t
  end.
