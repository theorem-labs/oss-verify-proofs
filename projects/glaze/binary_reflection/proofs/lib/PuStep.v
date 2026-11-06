(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PuKeep.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma pk_not_in_regs : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => bv_eqb x r) l = false -> ~ In r l.
Proof.
  intros r l H Hin.
  assert (E : existsb (fun x => bv_eqb x r) l = true)
    by (apply existsb_exists; exists r; split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]).
  rewrite E in H. discriminate H.
Qed.

Ltac pk_reg_lit r := lazymatch r with @BV _ ?z _ => lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end end.

Ltac not_kept_fast :=
  first [ lazymatch goal with
          | |- ~ In ?r ?L => pk_reg_lit r; exact (pk_not_in_regs r L (@eq_refl bool false))
          end
        | cbv; intuition discriminate ].
End PuKeep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
From Ltac2 Require Ltac2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Definition pu_rf := bvmap 5 word.

Ltac pu_fin_some_chk X r acc R0 w :=
  change (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_some r acc R0 w (@eq_refl bool false) (@eq_refl (option word) (Some w))).
Ltac pu_fin_none_chk X r acc R0 :=
  change (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_none r acc R0 (@eq_refl bool false) (@eq_refl (option word) None)).
Ltac pu_fin_some X r acc R0 w :=
  change_no_check (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_some r acc R0 w (@eq_refl bool false) ltac:(exact_no_check (@eq_refl (option word) (Some w)))).
Ltac pu_fin_none X r acc R0 :=
  change_no_check (getr X r) with (getr (rl_build acc R0) r);
  rewrite (rl_none r acc R0 (@eq_refl bool false) ltac:(exact_no_check (@eq_refl (option word) None))).

Module PuL2.
Import Ltac2.Ltac2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac2 Type env := { c_regupd : constant; c_rf : constant; k_BV : constructor; mk_cons : constr; mk_nil : constr; mk_RLP : constr }.
Ltac2 ck (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.zero Not_found end.
Ltac2 kk (r : Std.reference) : constructor := match r with Std.ConstructRef c => c | _ => Control.zero Not_found end.
Ltac2 mk_env () : env :=
  { c_regupd := ck reference:(regupd); c_rf := ck reference:(pu_rf); k_BV := kk reference:(BV);
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
  | Some w => ltac1:(x r acc r0 w |- pu_fin_some x r acc r0 w) x r (Ltac1.of_constr acc) (Ltac1.of_constr r0) (Ltac1.of_constr w)
  | None => ltac1:(x r acc r0 |- pu_fin_none x r acc r0) x r (Ltac1.of_constr acc) (Ltac1.of_constr r0)
  end.
End PuL2.
Ltac pu_gres_l2 := ltac2:(x r |- PuL2.gres_l2 x r).

(* [comment removed for export] *)
Ltac pu_isletR X := is_var X; let T := type of X in lazymatch T with pu_rf => idtac end.

(* [comment removed for export] *)
Ltac pu_gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             first [ lazymatch X with regupd _ _ _ => idtac end; pu_gres_l2 X r
                   | pu_isletR X; pu_gres_l2 X r ]
         end;
  gres_fast.

(* [comment removed for export] *)
Ltac pu_K := constr:(3%nat).
Ltac pu_sub X K := lazymatch K with O => X | S ?k => lazymatch X with regupd ?R _ _ => pu_sub R k end end.
Ltac pu_cut X K x :=
  lazymatch K with
  | O => x
  | S ?k => lazymatch X with regupd ?R ?rd ?v => let R' := pu_cut R k x in constr:(regupd R' rd v) end
  end.
Ltac pu_setR :=
  lazymatch goal with
  | |- msteps ?s (mkst ?X ?pc ?m ?rom) ?F =>
      let K := pu_K in
      let R := match goal with _ => pu_sub X K | _ => constr:(tt) end in
      lazymatch R with
      | regupd _ _ _ =>
          let x := fresh "pR" in
          refine (let x : pu_rf := R in _);
          let X' := pu_cut X K x in
          change (msteps s (mkst X' pc m rom) F)
      | _ => idtac
      end
  | |- _ => idtac
  end.
Ltac pu_vnorm := vnorm_fast; pu_setR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PsL2.
Import Ltac2.Ltac2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac2 fail0 () := Control.zero (Tactic_failure None).
Ltac2 rec is_num (z : constr) : bool :=
  match Constr.Unsafe.kind z with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => Array.for_all is_num args | _ => false end
  | _ => false
  end.
Ltac2 z_lit (x : Ltac1.t) : unit :=
  match Ltac1.to_constr x with
  | Some z => if is_num z then () else fail0 ()
  | None => fail0 ()
  end.
Ltac2 rec closed_in (seen : ident list ref) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id =>
      if List.mem Ident.equal id (seen.(contents)) then true else
      match Control.hyp_value id with
      | Some b => seen.(contents) := id :: seen.(contents); closed_in seen b
      | None => false
      end
  | Constr.Unsafe.Evar _ _ => false
  | Constr.Unsafe.Meta _ => false
  | Constr.Unsafe.Rel _ => true
  | Constr.Unsafe.Sort _ => true
  | Constr.Unsafe.Constant _ _ => true
  | Constr.Unsafe.Ind _ _ => true
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f args => if closed_in seen f then Array.for_all (closed_in seen) args else false
  | _ =>
      let ok := { contents := true } in
      Constr.Unsafe.iter (fun t => if ok.(contents) then (if closed_in seen t then () else ok.(contents) := false) else ()) c;
      ok.(contents)
  end.
Ltac2 closed (x : Ltac1.t) : unit :=
  match Ltac1.to_constr x with
  | Some p => if closed_in { contents := [] } p then () else fail0 ()
  | None => fail0 ()
  end.
End PsL2.
Ltac ps_is_Z_lit := ltac2:(z |- PsL2.z_lit z).
Ltac ps_check_closed := ltac2:(p |- PsL2.closed p).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section PuPc.
Context {fx : FPState}.
Lemma pu_pc_eq : forall segs (R : bvmap 5 word) (p p' : word) m rom F,
  p = p' -> msteps segs (mkst R p' m rom) F -> msteps segs (mkst R p m rom) F.
Proof. intros segs R p p' m rom F E H. rewrite E. exact H. Qed.
End PuPc.


Ltac pu_norm_pc :=
  lazymatch goal with
  | |- msteps ?s (mkst ?R ?p ?m ?rom) ?F =>
      tryif has_evar (mkst R p m rom) then idtac else
      lazymatch p with
      | @BV _ _ _ => idtac
      | _ =>
          try (let l := word_lit p in
               refine (pu_pc_eq s R p l m rom F _ _); [ apply bv_eq; vm_compute; reflexivity | ])
      end
  | |- _ => norm_pc
  end.
Ltac pu_step_simpl :=
  reduce_bv_eqb_ifs;
  lazymatch goal with |- context [skipn O _] => rewrite ?skipn_O | |- _ => idtac end;
  pu_norm_pc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pu_mf := word -> option byte.
Ltac pu_isletM X := is_var X; let T := type of X in lazymatch T with pu_mf => idtac end.
Ltac pu_isletF x := is_var x; let b := eval unfold x in x in is_evar b.
Ltac pu_letF :=
  lazymatch goal with
  | |- msteps ?s ?st ?F =>
      tryif is_var F then idtac else
      tryif is_evar F then
        (let f := fresh "pF" in
         evar (f : machine_state);
         let e := eval unfold f in f in unify F e;
         change (msteps s st f))
      else
        lazymatch F with
        | mkst ?r ?pc ?m ?rom =>
            tryif is_evar r then
              (let f := fresh "pFR" in
               evar (f : bvmap 5 word);
               let e := eval unfold f in f in unify r e;
               change (msteps s st (mkst f pc m rom)))
            else idtac
        | _ => idtac
        end
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac pu_zx t :=
  match goal with
  | x := _ : pu_rf |- _ => lazymatch t with context [x] => let t' := eval unfold x in t in pu_zx t' end
  | x := _ : pu_mf |- _ => lazymatch t with context [x] => let t' := eval unfold x in t in pu_zx t' end
  | _ => t
  end.
Ltac pu_refl :=
  lazymatch goal with
  | |- msteps _ ?X ?F =>
      lazymatch F with
      | mkst ?f _ _ _ =>
          tryif pu_isletF f then
            (lazymatch X with mkst ?R _ _ _ => let b := eval unfold f in f in let R' := pu_zx R in unify b R' end;
             exact (mst_refl _ _))
          else apply mst_refl
      | _ =>
          tryif pu_isletF F then
            (let b := eval unfold F in F in let X' := pu_zx X in unify b X'; exact (mst_refl _ _))
          else apply mst_refl
      end
  | |- _ => apply mst_refl
  end.
(* [comment removed for export] *)
Ltac pu_chain_step0 :=
  first
  [ eapply CatExec.CatSim.mst_step
  | eapply CatExec.CatSim.tw_step
  | eapply MmapSim.twm_step
  | eapply MmapSim.twmt_step
  | eapply MmapSim.tmw_step
  | eapply AllocSim.StreamSim.twr_step
  | eapply AllocSim.StreamSim.trd_step
  | eapply AllocSim.WallSim.twt_step
  | eapply AllocSim.WallSim.twe_step
  | eapply Mh32.DrainSim.tout_step
  | eapply Mh32.DrainSim.trd_step
  | eapply ExitSim.te_step ].
Ltac pu_chain_step := pu_letF; pu_chain_step0.
