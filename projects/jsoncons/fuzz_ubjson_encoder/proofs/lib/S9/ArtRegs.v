(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma tset_tset_same {A} : forall (p : positive) (x y : A) t, tset p y (tset p x t) = tset p y t.
Proof.
  induction p; intros x y [|l v r]; cbn; try reflexivity; rewrite ?IHp; reflexivity.
Qed.

Lemma tset_tset_comm {A} : forall (p q : positive) (x y : A) t, p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  induction p; intros q x y t Hne; destruct q; destruct t as [|l v r]; cbn; try reflexivity;
    try (rewrite IHp by congruence; reflexivity); try congruence.
Qed.

Lemma regupd_shadow : forall regs (r : reg) x y, regupd (regupd regs r x) r y = regupd regs r y.
Proof. intros. unfold regupd, bvmap_set. apply tset_tset_same. Qed.

Lemma regupd_comm : forall regs (r s : reg) x y, r <> s -> regupd (regupd regs s y) r x = regupd (regupd regs r x) s y.
Proof.
  intros regs r s x y Hne. unfold regupd, bvmap_set. apply tset_tset_comm.
  intros E. apply Hne. apply bv_key_inj. exact E.
Qed.

Lemma regupd_eq3 : forall rg rg' (i : reg) v v', rg = rg' -> v = v' -> regupd rg i v = regupd rg' i v'.
Proof. intros; subst; reflexivity. Qed.

Ltac reg_index r := lazymatch r with Z_to_bv 5 ?z => z | @BV 5 ?z _ => z | _ => constr:(100%Z) end.
Ltac rnorm_raw :=
  repeat match goal with
  | |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
      first [ constr_eq r s; rewrite (regupd_shadow rg r y x)
            | let zr := eval cbv in (bv_unsigned r) in
              let zs := eval cbv in (bv_unsigned s) in
              lazymatch (eval cbv in (Z.ltb zr zs)) with
              | true => rewrite (regupd_comm rg r s x y) by (let E := fresh in intros E; discriminate E)
              end ]
  end.

Ltac rnorm_old :=
  lazymatch goal with
  | |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
      let mx := fresh "mx" in let bx := fresh "bx" in
      set (mx := M); set (bx := B); rnorm_raw; subst mx bx
  | |- _ => rnorm_raw
  end.

Fixpoint rchain (base : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
  match l with nil => base | (r, v) :: l' => regupd (rchain base l') r v end.

Fixpoint rins (r : reg) (v : word) (s : list (reg * word)) : list (reg * word) :=
  match s with
  | nil => (cons (r, v) nil)
  | (r', v') :: tl =>
      match Z.compare (bv_unsigned r') (bv_unsigned r) with
      | Lt => (r, v) :: s
      | Eq => (r, v) :: tl
      | Gt => (r', v') :: rins r v tl
      end
  end.
Definition rcanon (l : list (reg * word)) : list (reg * word) := fold_right (fun rv s => rins (fst rv) (snd rv) s) nil l.

Lemma rins_ok : forall base r v s, rchain base (rins r v s) = regupd (rchain base s) r v.
Proof.
  intros base r v s. induction s as [|[r' v'] tl IH]; [reflexivity|].
  cbn [rins]. destruct (Z.compare (bv_unsigned r') (bv_unsigned r)) eqn:E.
  - apply Z.compare_eq in E. apply bv_eq in E. subst r'. cbn [rchain]. symmetry. apply regupd_shadow.
  - reflexivity.
  - cbn [rchain]. rewrite IH. symmetry. apply regupd_comm. intros ->. rewrite Z.compare_refl in E. discriminate E.
Qed.
Lemma rchain_canon : forall base l, rchain base (rcanon l) = rchain base l.
Proof.
  intros base l. induction l as [|[r v] l IH]; [reflexivity|].
  unfold rcanon. cbn [fold_right fst snd]. fold (rcanon l). rewrite rins_ok, IH. reflexivity.
Qed.

Ltac zr_plit p := lazymatch p with xH => idtac | xO ?q => zr_plit q | xI ?q => zr_plit q end.
Ltac zr_idx r :=
  lazymatch r with
  | @BV 5 ?z _ => lazymatch z with Z0 => constr:(z) | Zpos ?p => let _ := constr:(ltac:(zr_plit p; exact tt)) in constr:(z) end
  | Z_to_bv 5 ?z => lazymatch z with Z0 => constr:(z) | Zpos ?p => let _ := constr:(ltac:(zr_plit p; exact tt)) in let z' := eval cbv in (bv_unsigned r) in constr:(z') end
  end.
Ltac zr_ins r v z l :=
  lazymatch l with
  | nil => constr:(cons (z, (r, v)) nil)
  | cons (?z', (?r', ?v')) ?tl =>
      let c := eval cbv in (Z.compare z' z) in
      lazymatch c with
      | Lt => constr:(cons (z, (r, v)) l)
      | Eq => lazymatch r with r' => constr:(cons (z, (r, v)) tl) end
      | Gt => let tl' := zr_ins r v z tl in constr:(cons (z', (r', v')) tl')
      end
  end.
Ltac zr_sort R :=
  lazymatch R with
  | regupd ?R' ?r ?v => let l := zr_sort R' in let z := zr_idx r in zr_ins r v z l
  | _ => constr:(@nil (Z * (reg * word)))
  end.
Ltac zr_list R := lazymatch R with regupd ?R' ?r ?v => let l := zr_list R' in constr:(cons (r, v) l) | _ => constr:(@nil (reg * word)) end.
Ltac zr_base R := lazymatch R with regupd ?R' _ _ => zr_base R' | _ => R end.
Ltac zr_build base l := lazymatch l with nil => base | cons (_, (?r, ?v)) ?tl => let R0 := zr_build base tl in constr:(regupd R0 r v) end.

Ltac rnorm_one R :=
  let base := zr_base R in
  let ls := zr_sort R in
  let R' := zr_build base ls in
  lazymatch R' with
  | R => fail
  | _ => let l0 := zr_list R in
         let e := constr:(rchain_canon base l0 : R' = R) in
         rewrite <- e
  end.

Ltac rnorm_bad :=
  match goal with
  | |- context [regupd (regupd _ ?s _) ?r _] =>
      first [ let zr := zr_idx r in let zs := zr_idx s in
              let c := eval cbv in (Z.ltb zs zr) in
              lazymatch c with true => fail 1 | false => idtac end
            | idtac ]
  end.

Ltac rnorm_all :=
  repeat match goal with
         | |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
             let zr := zr_idx r in let zs := zr_idx s in
             let c := eval cbv in (Z.leb zr zs) in
             lazymatch c with true => rnorm_one constr:(regupd (regupd rg s y) r x) end
         end.
Ltac rnorm_new R := try rnorm_one R; rnorm_all; tryif rnorm_bad then rnorm_raw else idtac.
Ltac rnorm :=
  lazymatch goal with
  | |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
      let mx := fresh "mx" in let bx := fresh "bx" in
      set (mx := M); set (bx := B); rnorm_new R; subst mx bx
  | |- _ => rnorm_all; tryif rnorm_bad then rnorm_raw else idtac
  end.
