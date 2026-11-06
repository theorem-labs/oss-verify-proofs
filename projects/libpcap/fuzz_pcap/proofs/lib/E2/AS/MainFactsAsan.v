(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AxSymExec3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require Import MainExport A3Kn.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition HHIMG : Z := 6303744.

(* Main-entry facts, computed from the knowledge at main (KNX1 / KNX2, the two stack-alignment worlds): one fact per
   knowledge entry that the fact language expresses. Facts of entries present in both worlds are in the shared lists. *)
Definition saddr_z (sa : saddr) : option zexp :=
  match zexp_of (a_base sa) with Some bz => Some (mkaddr bz (a_off sa)) | None => None end.

Definition gen_m (kn : list kentry) (HLO HHI : Z) (K : kentry) : list mfact :=
  match K with
  | KWord sa w e =>
      match saddr_z sa, zexp_of e with
      | Some a, Some v =>
          (if is_cellw w && covered kn sa (Z.of_nat w) then [MCell a w v] else [])
          ++ (match e with ELit 0 => if covered kn sa (Z.of_nat w) then [MZeroC a (Z.of_nat w)] else [] | _ => [] end)
          ++ [MRo a w v]
      | _, _ => []
      end
  | KZero sa (ELit n) =>
      match saddr_z sa with
      | Some a => (if covered kn sa n then [MZeroC a n] else []) ++ [MZero a n]
      | None => []
      end
  | KZero sa ne => match saddr_z sa, zexp_of ne with Some a, Some nz => [MZeroS a nz] | _, _ => [] end
  | KFill sa (ELit n) c => match saddr_z sa with Some a => [MFill a n c] | None => [] end
  | KImg lo hi => if (HLO <=? lo) && (hi <=? HHI) then [MImg lo hi] else []
  | KWr sa (ELit n) => match saddr_z sa with Some a => [MWr a n] | None => [] end
  | KWr sa ne => match saddr_z sa, zexp_of ne with Some a, Some nz => [MWrS a nz] | _, _ => [] end
  | _ => []
  end.

Definition gen_p (K : kentry) : list pfact :=
  match K with
  | KRange (EVar n) lo hi => [PVar n lo hi]
  | KRange e lo hi => match zexp_of e with Some z => [PRange z lo hi] | None => [] end
  | KDisj sa1 (ELit n1) sa2 (ELit n2) =>
      match saddr_z sa1, saddr_z sa2 with Some a1, Some a2 => [PDisj a1 n1 a2 n2] | _, _ => [] end
  | KDisj sa1 ne1 sa2 ne2 =>
      match saddr_z sa1, zexp_of ne1, saddr_z sa2, zexp_of ne2 with
      | Some a1, Some n1, Some a2, Some n2 => [PDisjS a1 n1 a2 n2] | _, _, _, _ => [] end
  | _ => []
  end.

Definition in_kn (kn : list kentry) (K : kentry) : bool := existsb (AsanPlanCore.APC.kentry_eqb K) kn.
Definition KNC : list kentry := Eval vm_compute in (List.filter (in_kn KNX2) KNX1).
Definition KN1o : list kentry := Eval vm_compute in (List.filter (fun K => negb (in_kn KNX2 K)) KNX1).
Definition KN2o : list kentry := Eval vm_compute in (List.filter (fun K => negb (in_kn KNX1 K)) KNX2).
Definition both_m (f : mfact) : bool :=
  mjustify KNX1 (var_ranges KNX1) 65536 HHIMG f && mjustify KNX2 (var_ranges KNX2) 65536 HHIMG f.
Definition both_p (f : pfact) : bool := pjustify KNX1 (var_ranges KNX1) f && pjustify KNX2 (var_ranges KNX2) f.

Definition asan_mem_facts_kn : list mfact :=
  Eval vm_compute in (List.filter both_m (flat_map (gen_m KNX1 65536 HHIMG) KNC)).
Definition asan_pure_facts_kn : list pfact :=
  Eval vm_compute in (List.filter both_p (flat_map gen_p KNC)).
Definition not_kn (f : mfact) : bool := negb (existsb (mfact_eqb f) asan_mem_facts_kn).
Definition asan_mem_facts_w1 : list mfact :=
  Eval vm_compute in (List.filter (fun f => mjustify KNX1 (var_ranges KNX1) 65536 HHIMG f && not_kn f) (flat_map (gen_m KNX1 65536 HHIMG) KNX1)).
Definition asan_mem_facts_w2 : list mfact :=
  Eval vm_compute in (List.filter (fun f => mjustify KNX2 (var_ranges KNX2) 65536 HHIMG f && not_kn f) (flat_map (gen_m KNX2 65536 HHIMG) KNX2)).
Definition asan_pure_facts_w1 : list pfact :=
  Eval vm_compute in (List.filter (pjustify KNX1 (var_ranges KNX1)) (flat_map gen_p KN1o)).
Definition asan_pure_facts_w2 : list pfact :=
  Eval vm_compute in (List.filter (pjustify KNX2 (var_ranges KNX2)) (flat_map gen_p KN2o)).

(* [comment removed for export] *)
Definition mjustifyL := Eval cbv delta [mjustify existsb andb orb covered addr_match val_match lit_len sym_len] beta in mjustify.
Definition pjustifyL := Eval cbv delta [pjustify existsb andb orb addr_match val_match lit_len sym_len] beta in pjustify.
Fixpoint forallbL {A : Type} (p : A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: t => if p x then forallbL p t else false end.
Lemma forallb_L : forall (A : Type) (p q : A -> bool) (l : list A), (forall x, p x = q x) -> forallb p l = forallbL q l.
Proof. intros A p q l H. induction l as [|x t IH]; cbn [forallb forallbL]; [reflexivity|]. rewrite H, IH. destruct (q x); reflexivity. Qed.
Lemma mjustify_L : forall kn VR lo hi f, mjustify kn VR lo hi f = mjustifyL kn VR lo hi f.
Proof. reflexivity. Qed.
Lemma pjustify_L : forall kn VR f, pjustify kn VR f = pjustifyL kn VR f.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_mem_facts_justified_w1 :
  forallb (mjustify KNX1 (var_ranges KNX1) 65536 6303744) (asan_mem_facts_kn ++ asan_mem_facts_w1) = true.
Proof. rewrite (forallb_L _ _ _ _ (mjustify_L _ _ _ _)). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_pure_facts_justified_w1 :
  forallb (pjustify KNX1 (var_ranges KNX1)) (asan_pure_facts_kn ++ asan_pure_facts_w1) = true.
Proof. rewrite (forallb_L _ _ _ _ (pjustify_L _ _)). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_mem_facts_justified_w2 :
  forallb (mjustify KNX2 (var_ranges KNX2) 65536 6303744) (asan_mem_facts_kn ++ asan_mem_facts_w2) = true.
Proof. rewrite (forallb_L _ _ _ _ (mjustify_L _ _ _ _)). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_pure_facts_justified_w2 :
  forallb (pjustify KNX2 (var_ranges KNX2)) (asan_pure_facts_kn ++ asan_pure_facts_w2) = true.
Proof. rewrite (forallb_L _ _ _ _ (pjustify_L _ _)). vm_cast_no_check (@eq_refl bool true). Qed.
