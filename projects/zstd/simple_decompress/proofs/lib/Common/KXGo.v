(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive kz : Type :=
| KZRange (e lo hi : Z)             (* [comment removed for export] *)
| KZDisj (a1 n1 a2 n2 : Z)          (* [comment removed for export] *)
| KZWr (a n : Z)                    (* [comment removed for export] *)
| KZImg (lo hi : Z)                 (* [comment removed for export] *)
| KZAlign (e m : Z)                 (* [comment removed for export] *)
| KZWord (a : Z) (w : nat) (v : Z)  (* [comment removed for export] *)
| KZZero (a n : Z)                  (* [comment removed for export] *)
| KZTbl (a size stride off lo hi : Z)
| KZTblLog (a sh stride off lo hi : Z).
    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint reads_from (fuel j : nat) (scs : list sidecond) : list rdspec :=
  match fuel with
  | O => []
  | S f => match find_readbase j scs with
           | Some r => r :: reads_from f (S j) scs
           | None => []
           end
  end.
Definition kx_reads_of (nz nx : nat) (scs : list sidecond) : list rdspec := reads_from (nx - nz) nz scs.

Fixpoint kx_rk (kn0 : list kentry) (tfs : list tblfact) (j : nat) (reads : list rdspec) : list kentry :=
  match reads with
  | [] => []
  | (a, n, sx) :: rest =>
      (if (negb sx && Nat.ltb n 8)%bool then
         match (if Nat.eqb n 1 then find (fun tf => tbl_match kn0 tf a) tfs else None) with
         | Some (_, _, _, _, lo, hi, _) => [KRange (EVar j) lo hi]
         | None => [KRange (EVar j) 0 (2 ^ (8 * Z.of_nat n) - 1)]
         end
       else []) ++ kx_rk kn0 tfs (S j) rest
  end.

Section Run.
Variable segs : list Segment.

Definition kx_init (pc : Z) (rz : list zexp) (kn : list kentry) (nz : nat) : sym_state :=
  SS pc (ELit 0 :: map zx rz) [] kn nz.

(* [comment removed for export] *)
Definition kx_run0 (fuel : nat) (stops : list Z) (dirs : list bool) (pc : Z) (rz : list zexp) (zks : list zk) (nz : nat)
  : list kentry :=
  let '(ss, scs, _, _) := kx_exec segs fuel true stops (SCR dirs [] []) (kx_init pc rz (map zk_kentry zks) nz) [] [] in
  kx_rk (map zk_kentry zks) (zk_tfs zks) nz (kx_reads_of nz (s_next ss) scs).

Definition kx_run1 (fuel : nat) (stops : list Z) (dirs : list bool) (pc : Z) (rz : list zexp) (zks : list zk) (rk : list kentry)
                   (rs ws : list zreg) (nz : nat)
  : kxout * list rdspec * list sidecond * list (saddr * nat) * list expr :=
  let kn := map zk_kentry zks ++ rk in
  let out := kx_exec segs fuel true stops (SCR dirs [] []) (kx_init pc rz kn nz) [] [] in
  let '(ss, scs, _, accs) := out in
  (out, kx_reads_of nz (s_next ss) scs,
   List.filter (fun sc => negb (sc_auto kn rs sc)) scs,
   List.filter (fun an => negb (acc_auto kn ws an)) accs,
   map zx rz).

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ez (E : env) (zs : list Z) (e : expr) {struct e} : Z :=
  match e with
  | ELit z => z
  | EVar j => if Nat.ltb j (length zs) then znth j zs else bv_unsigned (ev E j)
  | EAlu ALU_ADD a b => ez E zs a + ez E zs b
  | EAlu ALU_SUB a b => ez E zs a - ez E zs b
  | EMd M_MUL a b => ez E zs a * ez E zs b
  | EAlu ALU_AND a b => Z.land (uz E zs a) (uz E zs b)
  | EAlu ALU_OR a b => Z.lor (uz E zs a) (uz E zs b)
  | EAlu ALU_XOR a b => Z.lxor (uz E zs a) (uz E zs b)
  | EAlu ALU_SRL a b => uz E zs a / 2 ^ (uz E zs b mod 64)
  | _ => bv_unsigned (edenot E e)
  end
with uz (E : env) (zs : list Z) (e : expr) {struct e} : Z :=
  match e with
  | ELit z => z mod 2^64
  | EVar j => if Nat.ltb j (length zs) then znth j zs mod 2^64 else bv_unsigned (ev E j)
  | EAlu ALU_ADD a b => (ez E zs a + ez E zs b) mod 2^64
  | EAlu ALU_SUB a b => (ez E zs a - ez E zs b) mod 2^64
  | EMd M_MUL a b => (ez E zs a * ez E zs b) mod 2^64
  | EAlu ALU_AND a b => Z.land (uz E zs a) (uz E zs b)
  | EAlu ALU_OR a b => Z.lor (uz E zs a) (uz E zs b)
  | EAlu ALU_XOR a b => Z.lxor (uz E zs a) (uz E zs b)
  | EAlu ALU_SRL a b => uz E zs a / 2 ^ (uz E zs b mod 64)
  | _ => bv_unsigned (edenot E e)
  end.

Lemma ez_uz_sound : forall zs E e, atoms_ok zs E ->
  edenot E e = Z_to_bv 64 (ez E zs e) /\ bv_unsigned (edenot E e) = uz E zs e.
Proof.
  intros zs E e HA.
  assert (D : forall x : word, x = Z_to_bv 64 (bv_unsigned x)) by (intro x; symmetry; apply Z_to_bv_bv_unsigned).
  assert (W : forall (x : word) z, x = Z_to_bv 64 z -> bv_unsigned x = z mod 2^64)
    by (intros x z ->; rewrite Z_to_bv_unsigned; reflexivity).
  induction e as [z|j|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    try (cbn [ez uz]; split; [apply D | reflexivity]).
  - cbn [ez uz edenot]. split; [reflexivity | rewrite Z_to_bv_unsigned; reflexivity].
  - cbn [ez uz]. destruct (Nat.ltb j (length zs)) eqn:L; [|split; [apply D | reflexivity]].
    apply Nat.ltb_lt in L. cbn [edenot]. rewrite (HA j L). split; [reflexivity | rewrite Z_to_bv_unsigned; reflexivity].
  - destruct IHa as [Ea Ua], IHb as [Eb Ub].
    destruct op; try (cbn [ez uz]; split; [apply D | reflexivity]); cbn [ez uz edenot].
    + assert (X : alu64 ALU_ADD (edenot E a) (edenot E b) = Z_to_bv 64 (ez E zs a + ez E zs b)).
      { rewrite Ea, Eb at 1. apply word_eq_Z. rewrite u_add64, !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod, <- Zplus_mod. reflexivity. }
      split; [exact X | exact (W _ _ X)].
    + assert (X : alu64 ALU_SUB (edenot E a) (edenot E b) = Z_to_bv 64 (ez E zs a - ez E zs b)).
      { rewrite Ea, Eb at 1. apply word_eq_Z. rewrite u_sub64, !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod, <- Zminus_mod. reflexivity. }
      split; [exact X | exact (W _ _ X)].
    + rewrite <- Ua, <- Ub, <- u_xor64. split; [apply D | reflexivity].
    + rewrite <- Ua, <- Ub, <- u_srl64. split; [apply D | reflexivity].
    + rewrite <- Ua, <- Ub, <- u_or64. split; [apply D | reflexivity].
    + rewrite <- Ua, <- Ub, <- u_and64. split; [apply D | reflexivity].
  - destruct IHa as [Ea Ua], IHb as [Eb Ub].
    destruct op; try (cbn [ez uz]; split; [apply D | reflexivity]); cbn [ez uz edenot].
    assert (X : mul_div M_MUL (edenot E a) (edenot E b) = Z_to_bv 64 (ez E zs a * ez E zs b)).
    { rewrite Ea, Eb at 1. apply word_eq_Z. rewrite u_mul64, !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod, <- Zmult_mod. reflexivity. }
    split; [exact X | exact (W _ _ X)].
Qed.

Lemma ez_sound : forall zs E e, atoms_ok zs E -> edenot E e = Z_to_bv 64 (ez E zs e).
Proof. intros zs E e HA. exact (proj1 (ez_uz_sound zs E e HA)). Qed.
Lemma uz_sound : forall zs E e, atoms_ok zs E -> bv_unsigned (edenot E e) = uz E zs e.
Proof. intros zs E e HA. exact (proj2 (ez_uz_sound zs E e HA)). Qed.

Lemma kx_keep : forall zs E rz (x : word), atoms_ok zs E -> zwf (length zs) rz = true ->
  x = Z_to_bv 64 (zden zs rz) -> edenot E (zx rz) = x.
Proof. intros zs E rz x HA HW ->. apply zx_sound; assumption. Qed.

Lemma kx_regs_mkRl : forall E sr xs, Forall2 (fun e x => edenot E e = x) (tl sr) xs -> length xs = 31%nat -> kx_regs E sr = mkRl xs.
Proof.
  intros E sr xs H L.
  assert (A : forall k, (k < 31)%nat -> edenot E (nth (S k) sr (ELit 0)) = nth k xs w0).
  { intros k Hk. replace (nth (S k) sr (ELit 0)) with (nth k (tl sr) (ELit 0)) by (destruct sr; [destruct k|]; reflexivity).
    revert k Hk. rewrite <- L. clear L. induction H as [|e x es xs Hx _ IH]; intros k Hk; [cbn in Hk; lia|].
    destruct k as [|k]; [exact Hx|]. cbn [nth]. apply IH. cbn [length] in Hk. lia. }
  unfold kx_regs, mkRl, mkRf. cbn [pred]. rewrite !A by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_is_pos p := lazymatch p with xH => idtac | xO ?q => kx_is_pos q | xI ?q => kx_is_pos q end.
Ltac kx_closedZ z :=
  lazymatch z with
  | Z0 => idtac | Zpos ?p => kx_is_pos p | Zneg ?p => kx_is_pos p
  | Z.add ?a ?b => kx_closedZ a; kx_closedZ b
  | Z.sub ?a ?b => kx_closedZ a; kx_closedZ b
  | Z.mul ?a ?b => kx_closedZ a; kx_closedZ b
  | Z.pow ?a ?b => kx_closedZ a; kx_closedZ b
  | Z.opp ?a => kx_closedZ a
  end.
Ltac kx_closedb z := constr:(ltac:(first [ kx_closedZ z; exact true | exact false ]) : bool).

(* [comment removed for export] *)
Ltac kx_idx a l :=
  lazymatch l with
  | @nil _ => constr:(O)
  | @cons _ ?h ?t =>
      let b := constr:(ltac:(first [ constr_eq a h; exact true | exact false ]) : bool) in
      lazymatch b with
      | true => constr:(O)
      | false => let n := kx_idx a t in constr:(S n)
      end
  end.
Ltac kx_len l := lazymatch l with @nil _ => constr:(O) | @cons _ _ ?t => let n := kx_len t in constr:(S n) end.
Ltac kx_snoc l a := lazymatch l with @nil _ => constr:(@cons Z a (@nil Z)) | @cons _ ?h ?t => let t' := kx_snoc t a in constr:(@cons Z h t') end.

(* [comment removed for export] *)
Ltac kx_atom l a :=
  let i := kx_idx a l in
  let n := kx_len l in
  let b := constr:(Nat.eqb i n) in
  let b := eval cbv in b in
  lazymatch b with
  | true => let l' := kx_snoc l a in constr:((l', ZA i))
  | false => constr:((l, ZA i))
  end.

(* [comment removed for export] *)
Ltac kx_rz l z :=
  let c := kx_closedb z in
  lazymatch c with
  | true => let v := eval vm_compute in z in constr:((l, ZL v))
  | false =>
      lazymatch z with
      | Z.add ?a ?b =>
          let r1 := kx_rz l a in
          lazymatch r1 with (?l1, ?e1) =>
            let r2 := kx_rz l1 b in
            lazymatch r2 with (?l2, ?e2) => constr:((l2, ZAdd e1 e2)) end end
      | Z.sub ?a ?b =>
          let r1 := kx_rz l a in
          lazymatch r1 with (?l1, ?e1) =>
            let r2 := kx_rz l1 b in
            lazymatch r2 with (?l2, ?e2) => constr:((l2, ZSub e1 e2)) end end
      | Z.mul ?a ?b =>
          let r1 := kx_rz l a in
          lazymatch r1 with (?l1, ?e1) =>
            let r2 := kx_rz l1 b in
            lazymatch r2 with (?l2, ?e2) => constr:((l2, ZMul e1 e2)) end end
      | Z.opp ?a =>
          let r1 := kx_rz l a in
          lazymatch r1 with (?l1, ?e1) => constr:((l1, ZOpp e1)) end
      | _ =>
          (* [comment removed for export] *)
          let isc := constr:(ltac:(first [ is_const z; exact true | exact false ]) : bool) in
          lazymatch isc with
          | false => kx_atom l z
          | true =>
              let v := eval vm_compute in z in
              let lit := constr:(ltac:(first [ kx_closedZ v; exact true | exact false ]) : bool) in
              lazymatch lit with
              | true => constr:((l, ZL v))
              | false => kx_atom l z
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac kx_rw l x :=
  lazymatch x with
  | Z_to_bv 64 ?z => kx_rz l z
  | _ => kx_atom l (bv_unsigned x)
  end.

(* [comment removed for export] *)
Ltac kx_rws l xs :=
  lazymatch xs with
  | @nil _ => constr:((l, @nil zexp))
  | @cons _ ?x ?t =>
      let r1 := kx_rw l x in
      lazymatch r1 with (?l1, ?e1) =>
        let r2 := kx_rws l1 t in
        lazymatch r2 with (?l2, ?es) => constr:((l2, @cons zexp e1 es)) end end
  end.

(* [comment removed for export] *)
Ltac kx_rk1 l k :=
  lazymatch k with
  | KZRange ?e ?lo ?hi =>
      let r := kx_rz l e in
      let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in
      lazymatch r with (?l1, ?e1) => constr:((l1, ZKRange e1 lo' hi')) end
  | KZDisj ?a1 ?n1 ?a2 ?n2 =>
      let r1 := kx_rz l a1 in lazymatch r1 with (?l1, ?ea1) =>
      let r2 := kx_rz l1 n1 in lazymatch r2 with (?l2, ?en1) =>
      let r3 := kx_rz l2 a2 in lazymatch r3 with (?l3, ?ea2) =>
      let r4 := kx_rz l3 n2 in lazymatch r4 with (?l4, ?en2) => constr:((l4, ZKDisj ea1 en1 ea2 en2)) end end end end
  | KZWr ?a ?n =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 n in lazymatch r2 with (?l2, ?en) => constr:((l2, ZKWr ea en)) end end
  | KZImg ?lo ?hi =>
      let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in constr:((l, ZKImg lo' hi'))
  | KZAlign ?e ?mm =>
      let r := kx_rz l e in let mm' := eval vm_compute in mm in
      lazymatch r with (?l1, ?e1) => constr:((l1, ZKAlign e1 mm')) end
  | KZWord ?a ?w ?v =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 v in lazymatch r2 with (?l2, ?ev) => constr:((l2, ZKWord ea w ev)) end end
  | KZZero ?a ?n =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 n in lazymatch r2 with (?l2, ?en) => constr:((l2, ZKZero ea en)) end end
  | KZTbl ?a ?size ?stride ?off ?lo ?hi =>
      let r1 := kx_rz l a in
      let size' := eval vm_compute in size in let stride' := eval vm_compute in stride in let off' := eval vm_compute in off in
      let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in
      lazymatch r1 with (?l1, ?ea) => constr:((l1, ZKTbl ea size' stride' off' lo' hi')) end
  | KZTblLog ?a ?sh ?stride ?off ?lo ?hi =>
      let stride' := eval vm_compute in stride in let off' := eval vm_compute in off in
      let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 sh in lazymatch r2 with (?l2, ?es) => constr:((l2, ZKTblLog ea es stride' off' lo' hi')) end end
  end.
Ltac kx_rks l ks :=
  lazymatch ks with
  | @nil _ => constr:((l, @nil zk))
  | @cons _ ?k ?t =>
      let r1 := kx_rk1 l k in
      lazymatch r1 with (?l1, ?k1) =>
        let r2 := kx_rks l1 t in
        lazymatch r2 with (?l2, ?ks') => constr:((l2, @cons zk k1 ks')) end end
  end.

(* [comment removed for export] *)
Ltac kx_cells_zk l A cs k acc :=     (* [comment removed for export] *)
  lazymatch cs with
  | @nil _ => constr:((l, acc))
  | @cons _ ?c ?rest =>
      let sz := eval cbv in (Z.of_nat (csize c)) in
      let k' := eval vm_compute in (k + sz) in
      let wv := lazymatch c with
                | C8 ?v => constr:(Some (8%nat, v)) | C4 ?v => constr:(Some (4%nat, v)) | C2 ?v => constr:(Some (2%nat, v))
                | _ => constr:(@None (nat * word)) end in
      lazymatch wv with
      | Some (?w, ?v) =>
          let r1 := kx_rz l (A + k) in
          lazymatch r1 with (?l1, ?ea) =>
            let r2 := kx_rw l1 v in
            lazymatch r2 with (?l2, ?ev) => kx_cells_zk l2 A rest k' (@cons zk (ZKWord ea w ev) acc) end end
      | None => kx_cells_zk l A rest k' acc
      end
  end.

(* [comment removed for export] *)
Ltac kx_chunks segs m acc :=
  match goal with
  | H : rw_cells segs m _ _ |- _ => lazymatch acc with context [H] => fail | _ => kx_chunks segs m (H, acc) end
  | H : ro_cells segs m _ _ |- _ => lazymatch acc with context [H] => fail | _ => kx_chunks segs m (H, acc) end
  | _ => acc
  end.

Ltac kx_chunks_zk segs m l chunks acc :=
  lazymatch chunks with
  | (?H, ?rest) =>
      let r := lazymatch type of H with
               | rw_cells _ _ ?A ?cs => kx_cells_zk l A cs 0%Z acc
               | ro_cells _ _ ?A ?cs => kx_cells_zk l A cs 0%Z acc
               end in
      lazymatch r with (?l1, ?acc1) => kx_chunks_zk segs m l1 rest acc1 end
  | _ => constr:((l, acc))
  end.

(* [comment removed for export] *)
Ltac kx_add_cells segs m l zks :=
  let chunks := kx_chunks segs m tt in
  let r := kx_chunks_zk segs m l chunks (@nil zk) in
  lazymatch r with (?l1, ?cz) => let z := eval cbv beta iota delta [app] in (zks ++ cz) in constr:((l1, z)) end.

(* [comment removed for export] *)
Ltac kx_rrs l rs :=
  lazymatch rs with
  | @nil _ => constr:((l, @nil zreg))
  | @cons _ (?a, ?n) ?t =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 n in lazymatch r2 with (?l2, ?en) =>
      let r3 := kx_rrs l2 t in lazymatch r3 with (?l3, ?rs') => constr:((l3, @cons zreg (ea, en) rs')) end end end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_mkR_fold :=
  lazymatch goal with
  | |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] => idtac
  | |- context [MS
    (TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
         (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
         (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))))
      ?F ?pc ?fc ?rv ?m ?ro] =>
      change (TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
         (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
         (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
      with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kx_bv_ranges :=
  repeat match goal with
  | |- context [@bv_unsigned 64 ?w] =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned w < 18446744073709551616 |- _ => fail
      | _ => pose proof (kx_u64_range w)
      end
  end.

Ltac kx_zoffs :=
  repeat match goal with |- context [zoff ?e] => let v := eval vm_compute in (zoff e) in change (zoff e) with v end.

(* [comment removed for export] *)
Ltac kx_is_arith T :=
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | not (@eq Z _ _) => idtac
  | and ?A ?B => kx_is_arith A; kx_is_arith B
  | or ?A ?B => kx_is_arith A; kx_is_arith B
  end.
(* [comment removed for export] *)
Ltac kx_shares T G :=
  match T with
  | context [?x] =>
      is_var x;
      let Tx := type of x in
      lazymatch Tx with Z => idtac | bv _ => idtac | list _ => idtac | nat => idtac end;
      lazymatch G with context [x] => idtac end
  end.
(* [comment removed for export] *)
Ltac kx_pull1 :=
  repeat match goal with
  | H : ?T |- ?G => kx_is_arith T; kx_shares T G; revert H
  end.
Ltac kx_pull := kx_pull1.
Ltac kx_lia_pruned :=
  kx_pull;
  repeat match goal with H : ?T |- _ => kx_is_arith T; clear H end;
  intros; lia.
(* [comment removed for export] *)
Ltac kx_lia_pruned2 :=
  kx_pull1; kx_pull1;
  repeat match goal with H : ?T |- _ => kx_is_arith T; clear H end;
  intros; lia.
Ltac kx_lia := kx_bv_ranges; first [ solve [kx_lia_pruned] | solve [kx_lia_pruned2] | lia ].

(* [comment removed for export] *)
Ltac kx_imgs ks :=
  lazymatch ks with
  | @nil _ => constr:(@nil (Z * Z))
  | @cons _ (KZImg ?lo ?hi) ?t =>
      let r := kx_imgs t in
      let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in constr:(@cons (Z * Z) (lo', hi') r)
  | @cons _ _ ?t => kx_imgs t
  end.
Ltac kx_wrimg_items ea en imgs acc :=
  lazymatch imgs with
  | @nil _ => acc
  | @cons _ (?lo, ?hi) ?t => kx_wrimg_items ea en t (@cons zk (ZKWrImg ea en lo hi) acc)
  end.
Ltac kx_wrimgs segs m l ks imgs acc :=      (* [comment removed for export] *)
  lazymatch ks with
  | @nil _ => acc
  | @cons _ (KZWr ?a ?n) ?t =>
      let ok0 := constr:(ltac:(first [ assert (0 < n) by kx_lia; exact true | exact false ]) : bool) in
      let ok := eval cbv beta zeta in ok0 in      (* [comment removed for export] *)
      lazymatch ok with
      | true =>
          let r1 := kx_rz l a in lazymatch r1 with (_, ?ea) =>
          let r2 := kx_rz l n in lazymatch r2 with (_, ?en) =>
          let acc' := kx_wrimg_items ea en imgs acc in kx_wrimgs segs m l t imgs acc' end end
      | false => kx_wrimgs segs m l t imgs acc
      end
  | @cons _ _ ?t => kx_wrimgs segs m l t imgs acc
  end.
Ltac kx_add_wrimgs segs m l KZS zks :=
  lazymatch goal with
  | _ : mem_inv segs m |- _ =>
      let imgs := kx_imgs KZS in
      lazymatch imgs with
      | @nil _ => zks
      | _ => let extra := kx_wrimgs segs m l KZS imgs (@nil zk) in
             eval cbv beta iota delta [app] in (zks ++ extra)
      end
  | _ => zks
  end.



(* [comment removed for export] *)
Ltac kx_wr_at :=
  lazymatch goal with
  | |- wr_at ?segs ?m ?A ?N =>
      match goal with
      | H : wr_at segs m ?A0 ?N0 |- _ => apply (wr_at_sub segs m A0 N0 A N H); kx_lia
      | H : u8arr segs m ?A0 ?bs |- _ => apply (wr_at_sub segs m A0 (Z.of_nat (length bs)) A N (proj2 H)); kx_lia
      | H : rw_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (wr_at_sub segs m A0 n A N (proj2 H)); kx_lia
      | H : stk segs m ?lo ?hi |- _ => apply (wr_at_sub segs m lo (hi - lo) A N); [apply (wr_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
      end
  end.

(* [comment removed for export] *)
Ltac kx_rd_at :=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
      | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
      | H : rw_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
      | H : ro_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
      | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
      | _ => (* [comment removed for export] *)
          let A' := eval lazy in A in
          lazymatch A' with
          | Z0 => idtac | Zpos _ => idtac
          | _ => fail 0 "kx_rd_at: no chunk hypothesis justifies the region at" A
          end;
          apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
      end
  end.

Ltac kx_zk_pre := lazy beta iota zeta delta [zk_prop zspan_ok]; kx_zoffs; lazy beta iota zeta delta [zden znth].

(* [comment removed for export] *)
Ltac kx_word_cell :=
  lazymatch goal with
  | |- rdn ?segs ?m (wa (?A + ?k)) ?w = Some (word_to_le_bytes ?w ?V) =>
      let fin := (first [ reflexivity
                        | (cbv beta iota delta [cbytes le8 le4 le2 word_to_le_bytes]; f_equal;
                           first [ reflexivity | rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range ]) ]) in
      match goal with
      | H : rw_cells segs m A ?cs |- _ =>
          eapply (kx_word_of_cells segs m A cs k _ w V (proj1 H)); [ lia | cells_cbv; reflexivity | reflexivity | fin ]
      | H : ro_cells segs m A ?cs |- _ =>
          eapply (kx_word_of_cells segs m A cs k _ w V H); [ lia | cells_cbv; reflexivity | reflexivity | fin ]
      end
  end.

Ltac kx_zk_solve :=
  lazymatch goal with
  | |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [kx_lia | split; [kx_lia | split; [kx_lia | kx_word_cell]]]
  | |- _ /\ _ /\ wr_at _ _ _ _ /\ mem_inv _ _ /\ _ = true =>
      split; [kx_lia | split; [kx_lia | split; [kx_wr_at | split; [assumption | vm_compute; reflexivity]]]]
  | |- _ /\ wr_at _ _ _ _ => split; [kx_lia | kx_wr_at]
  | |- _ /\ tbl_in _ _ _ _ _ _ _ _ =>
      split; [kx_lia | match goal with H : tbl_in _ _ _ _ _ _ _ _ |- _ => exact H end]
  | |- _ /\ _ /\ tbl_in_log _ _ _ _ _ _ _ _ =>
      split; [kx_lia | split; [kx_lia | match goal with H : tbl_in_log _ _ _ _ _ _ _ _ |- _ => exact H end]]
  | |- forall i, _ <= i < _ -> ?m (wa i) = None =>
      lazymatch goal with
      | |- forall i, ?lo <= i < ?hi -> _ =>
          let n := eval vm_compute in (Z.to_nat (hi - lo)) in
          match goal with MI : mem_inv ?segs m |- _ => apply (kx_img_none segs m lo n hi MI); [vm_compute; reflexivity | vm_compute; reflexivity] end
      end
  | |- _ => kx_lia
  end.

(* [comment removed for export] *)
Ltac kx_zks_solve :=
  repeat (apply Forall_cons; [kx_zk_pre; try solve [kx_zk_solve]|]); try apply Forall_nil.

Ltac kx_zreg_pre := lazy beta iota zeta delta [zreg_prop zspan_ok]; kx_zoffs; lazy beta iota zeta delta [zden znth].
Ltac kx_zreg_solve := split; [kx_lia | kx_rd_at].
Ltac kx_zregs_solve :=
  repeat (apply Forall_cons; [kx_zreg_pre; try solve [kx_zreg_solve]|]); try apply Forall_nil.

Ltac kx_regs_eqs :=
  repeat (apply Forall2_cons; [first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned]|]); apply Forall2_nil.

(* [comment removed for export] *)
Ltac kx_cert :=
  lazymatch goal with
  | |- ?c = true =>
      let v := eval vm_compute in c in
      lazymatch v with
      | true => vm_cast_no_check (@eq_refl bool true)
      | _ => fail 100 "KX: the boolean certificate evaluates to" v "- a KX bug or an ill-formed argument"
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_nth j l :=
  lazymatch j with
  | O => lazymatch l with @cons _ ?h _ => h end
  | S ?j' => lazymatch l with @cons _ _ ?t => kx_nth j' t end
  end.

Ltac kx_ez E zs nz e :=
  lazymatch e with
  | ELit ?z => z
  | EVar ?j =>
      let b := eval cbv in (Nat.ltb j nz) in
      lazymatch b with true => kx_nth j zs | false => constr:(bv_unsigned (ev E j)) end
  | EAlu ALU_ADD ?a ?b => let x := kx_ez E zs nz a in let y := kx_ez E zs nz b in constr:(x + y)
  | EAlu ALU_SUB ?a ?b => let x := kx_ez E zs nz a in let y := kx_ez E zs nz b in constr:(x - y)
  | EMd M_MUL ?a ?b => let x := kx_ez E zs nz a in let y := kx_ez E zs nz b in constr:(x * y)
  | EAlu ALU_AND ?a ?b => let x := kx_uz E zs nz a in let y := kx_uz E zs nz b in constr:(Z.land x y)
  | EAlu ALU_OR ?a ?b => let x := kx_uz E zs nz a in let y := kx_uz E zs nz b in constr:(Z.lor x y)
  | EAlu ALU_XOR ?a ?b => let x := kx_uz E zs nz a in let y := kx_uz E zs nz b in constr:(Z.lxor x y)
  | EAlu ALU_SRL ?a ?b => let x := kx_uz E zs nz a in let y := kx_ushamt E zs nz b in constr:(x / y)
  | _ => constr:(bv_unsigned (edenot E e))
  end
with kx_uz E zs nz e :=
  lazymatch e with
  | ELit ?z => let v := eval vm_compute in (z mod 2^64) in v
  | EVar ?j =>
      let b := eval cbv in (Nat.ltb j nz) in
      lazymatch b with
      | true => let a := kx_nth j zs in constr:(a mod 2^64)
      | false => constr:(bv_unsigned (ev E j))
      end
  | EAlu ALU_ADD _ _ => let z := kx_ez E zs nz e in constr:(z mod 2^64)
  | EAlu ALU_SUB _ _ => let z := kx_ez E zs nz e in constr:(z mod 2^64)
  | EMd M_MUL _ _ => let z := kx_ez E zs nz e in constr:(z mod 2^64)
  | EAlu ALU_AND _ _ => kx_ez E zs nz e
  | EAlu ALU_OR _ _ => kx_ez E zs nz e
  | EAlu ALU_XOR _ _ => kx_ez E zs nz e
  | EAlu ALU_SRL _ _ => kx_ez E zs nz e
  | _ => constr:(bv_unsigned (edenot E e))
  end
with kx_ushamt E zs nz b :=   (* [comment removed for export] *)
  lazymatch b with
  | ELit ?z => let v := eval vm_compute in (2 ^ ((z mod 2^64) mod 64)) in v
  | _ => let y := kx_uz E zs nz b in constr:(2 ^ (y mod 64))
  end.

(* [comment removed for export] *)
Ltac kx_word E zs nz e :=
  lazymatch e with
  | EVar ?j =>
      let b := eval cbv in (Nat.ltb j nz) in
      lazymatch b with
      | false => constr:(ev E j)
      | true => let z := kx_nth j zs in
                lazymatch z with bv_unsigned ?w => w | _ => constr:(Z_to_bv 64 z) end
      end
  | _ => let z := kx_ez E zs nz e in constr:(Z_to_bv 64 z)
  end.
Ltac kx_word_prf E zs KXA e :=
  first [ reflexivity | exact (ez_sound zs E e KXA) | (rewrite (ez_sound zs E e KXA); apply Z_to_bv_bv_unsigned) ].

(* [comment removed for export] *)
Ltac kx_exit_xs E zs nz es es0 xs :=
  lazymatch es with
  | @nil _ => constr:(@nil word)
  | @cons _ ?e ?et =>
      lazymatch es0 with @cons _ ?e0 ?et0 =>
      lazymatch xs with @cons _ ?x ?xt =>
        let rest := kx_exit_xs E zs nz et et0 xt in
        let b := constr:(ltac:(first [ constr_eq e e0; exact true | exact false ]) : bool) in
        lazymatch b with
        | true => constr:(@cons word x rest)
        | false => let W := kx_word E zs nz e in constr:(@cons word W rest)
        end
      end end
  end.

Ltac kx_exit_prf E zs KXA rzs :=
  (* [comment removed for export] *)
  lazymatch goal with
  | |- Forall2 _ (@nil _) (@nil _) => apply Forall2_nil
  | |- Forall2 _ (@cons _ ?e _) (@cons _ ?x _) =>
      lazymatch rzs with @cons _ ?rz ?rzt =>
        apply Forall2_cons;
        [ first [ reflexivity
                | exact (ez_sound zs E e KXA)
                | (rewrite (ez_sound zs E e KXA); apply Z_to_bv_bv_unsigned)
                | apply (kx_keep zs E rz x KXA); [vm_compute; reflexivity | first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned]] ]
        | kx_exit_prf E zs KXA rzt ]
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kx_split_rest :=
  repeat (apply Forall_cons; [|]); try apply Forall_nil.

Ltac kx_run_core STOPS FUEL DIRS KZS RRS :=
  kx_mkR_fold;
  lazymatch goal with
  | |- evt ?segs ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kx_add_cells segs m l2a zks0 in
      lazymatch r2b with (?l2, ?zks1) =>
      let zks := kx_add_wrimgs segs m l2 KZS zks1 in
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?zs, ?rs) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let rk := eval vm_compute in (kx_run0 segs FUEL stops DIRS pcv rz zks nz) in
      let out := eval vm_compute in (kx_run1 segs FUEL stops DIRS pcv rz zks rk rs (@nil zreg) nz) in
      lazymatch out with
      | (?ss', ?scs, ?scr', ?accs, ?reads, ?rest, _, ?es0) =>
          lazymatch ss' with
          | SSR ?pc' ?sr' ?log' ?kn' ?nx' _ =>
              change (evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
              refine (kx_go_evt segs F fc Q FUEL stops DIRS zs rz xs zks rk pcv m rom ss' scs scr' accs reads rs rest _ _ _ _ _ _ _);
              [ vm_cast_no_check (@eq_refl kxout (ss', scs, scr', accs))
              | kx_cert
              | kx_regs_eqs
              | kx_zks_solve
              | kx_zregs_solve
              | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
                intros E HE HK; kx_split_rest
              | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in let HLF := fresh "KXLF" in
                let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in let HMI := fresh "KXMI" in
                intros E HE HK HLF HMI; destruct HE as [KXA KXRD];
                change (reads_ok segs m nz reads E) in KXRD;
                change (log_flat E log') in HLF;
                change (mem_inv segs m -> mem_inv segs (mem_denot E m log')) in HMI;
                first [ match goal with MI0 : mem_inv segs m |- _ => specialize (HMI MI0) end | clear HMI ];
                change (evt segs Q (MS (kx_regs E sr') F (Z_to_bv 64 pc') fc None (mem_denot E m log') rom));
                lazymatch sr' with
                | @cons _ _ ?es =>
                    let xs' := kx_exit_xs E zs nz es es0 xs in
                    let HR := fresh "KXHR" in
                    assert (HR : kx_regs E sr' = mkRl xs') by (apply kx_regs_mkRl; [change (Forall2 (fun e x => edenot E e = x) es xs'); kx_exit_prf E zs KXA rz | reflexivity]);
                    rewrite HR; clear HR;
                    rewrite <- mkRl_mkR
                end;
                lazymatch log' with
                | @nil _ => change (mem_denot E m (@nil sentry)) with m in *; clear HLF
                | _ => idtac
                end
              ]
          end
      end end end end end
  end.

Tactic Notation "kx_run" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_run_core stops (FUEL : nat) (@nil bool) kzs rrs.
Tactic Notation "kx_rund" uconstr(STOPS) constr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let dirs := constr:(DIRS : list bool) in
  let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_run_core stops (FUEL : nat) dirs kzs rrs.
