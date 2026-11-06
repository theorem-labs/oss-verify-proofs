(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlan MainExport.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mj1 (kn : list kentry) (VR : vranges) (HLO HHI : Z) (f : mfact) (K : kentry) : bool :=
    match f, K with
    | MCell a w v, KWord sa w' e =>
        if Nat.eqb w w' && is_cellw w && addr_match VR sa a && val_match e v then covered kn sa (Z.of_nat w) else false
    | MZeroC a n, KZero sa ne => if lit_len ne n && addr_match VR sa a then covered kn sa n else false
    | MZeroC a n, KWord sa w (ELit 0) => if Z.eqb n (Z.of_nat w) && addr_match VR sa a then covered kn sa n else false
    | MRo a w v, KWord sa w' e => Nat.eqb w w' && addr_match VR sa a && val_match e v
    | MZero a n, KZero sa ne => lit_len ne n && addr_match VR sa a
    | MFill a n c, KFill sa ne c' => Z.eqb c c' && lit_len ne n && addr_match VR sa a
    | MImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi' && (HLO <=? lo) && (hi <=? HHI)
    | MWr a n, KWr sa ne => lit_len ne n && addr_match VR sa a
    | MZeroS a n, KZero sa ne => sym_len VR ne n && addr_match VR sa a
    | MWrS a n, KWr sa ne => sym_len VR ne n && addr_match VR sa a
    | MBlobD a n, KBlob sa ne _ => lit_len ne n && addr_match VR sa a
    | _, _ => false
    end.

Lemma mjustify_mj1 : forall kn VR HLO HHI f, mjustify kn VR HLO HHI f = existsb (mj1 kn VR HLO HHI f) kn.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint mjust_hints (kn : list kentry) (VR : vranges) (HLO HHI : Z) (fs : list mfact) (hs : list N) : bool :=
  match fs, hs with
  | [], _ => true
  | f :: fs', h :: hs' =>
      match nth_error kn (N.to_nat h) with
      | Some K => if mj1 kn VR HLO HHI f K then mjust_hints kn VR HLO HHI fs' hs' else false
      | None => false
      end
  | _ :: _, [] => false
  end.

Lemma mjust_hints_sound : forall kn VR HLO HHI fs hs,
  mjust_hints kn VR HLO HHI fs hs = true -> forallb (mjustify kn VR HLO HHI) fs = true.
Proof.
  intros kn VR HLO HHI. induction fs as [|f fs IH]; intros hs H; [reflexivity|].
  destruct hs as [|h hs]; [discriminate|]. cbn [mjust_hints] in H.
  destruct (nth_error kn (N.to_nat h)) as [K|] eqn:EK; [|discriminate].
  destruct (mj1 kn VR HLO HHI f K) eqn:EJ; [|discriminate].
  cbn [forallb]. rewrite (IH hs H), Bool.andb_true_r, mjustify_mj1.
  apply existsb_exists. exists K. split; [exact (nth_error_In _ _ EK) | exact EJ].
Qed.

(* [comment removed for export] *)
Definition pj1 (VR : vranges) (f : pfact) (K : kentry) : bool :=
    match f, K with
    | PVar n lo hi, KRange (EVar n') lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
    | PRange e lo hi, KRange e' lo' hi' => val_match e' e && Z.eqb lo lo' && Z.eqb hi hi'
    | PDisj a1 n1 a2 n2, KDisj sa1 ne1 sa2 ne2 =>
        lit_len ne1 n1 && lit_len ne2 n2 && addr_match VR sa1 a1 && addr_match VR sa2 a2
    | PDisjS a1 n1 a2 n2, KDisj sa1 ne1 sa2 ne2 =>
        sym_len VR ne1 n1 && sym_len VR ne2 n2 && addr_match VR sa1 a1 && addr_match VR sa2 a2
    | _, _ => false
    end.

Lemma pjustify_pj1 : forall kn VR f, pjustify kn VR f = existsb (pj1 VR f) kn.
Proof. reflexivity. Qed.

Fixpoint pjust_hints (kn : list kentry) (VR : vranges) (fs : list pfact) (hs : list N) : bool :=
  match fs, hs with
  | [], _ => true
  | f :: fs', h :: hs' =>
      match nth_error kn (N.to_nat h) with
      | Some K => if pj1 VR f K then pjust_hints kn VR fs' hs' else false
      | None => false
      end
  | _ :: _, [] => false
  end.

Lemma pjust_hints_sound : forall kn VR fs hs,
  pjust_hints kn VR fs hs = true -> forallb (pjustify kn VR) fs = true.
Proof.
  intros kn VR. induction fs as [|f fs IH]; intros hs H; [reflexivity|].
  destruct hs as [|h hs]; [discriminate|]. cbn [pjust_hints] in H.
  destruct (nth_error kn (N.to_nat h)) as [K|] eqn:EK; [|discriminate].
  destruct (pj1 VR f K) eqn:EJ; [|discriminate].
  cbn [forallb]. rewrite (IH hs H), Bool.andb_true_r, pjustify_pj1.
  apply existsb_exists. exists K. split; [exact (nth_error_In _ _ EK) | exact EJ].
Qed.

