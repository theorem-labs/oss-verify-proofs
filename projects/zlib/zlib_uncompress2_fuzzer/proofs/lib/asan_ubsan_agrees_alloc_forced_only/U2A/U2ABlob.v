(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Inductive cshape := SH8 | SH4 | SH2 | SH1 | SHB (n : nat).
Definition shape_size (s : cshape) : nat := match s with SH8 => 8 | SH4 => 4 | SH2 => 2 | SH1 => 1 | SHB n => n end.
Fixpoint shapes_size (l : list cshape) : nat := match l with [] => 0 | s :: r => shape_size s + shapes_size r end.

Definition chop1 (s : cshape) (bs : list byte) : cell :=
  match s with
  | SH8 => C8 (le_bytes_to_word bs) | SH4 => C4 (le_bytes_to_word bs) | SH2 => C2 (le_bytes_to_word bs)
  | SH1 => C1 (nth 0 bs (Z_to_bv 8 0)) | SHB n => CB n bs
  end.
Fixpoint chop (l : list cshape) (bs : list byte) : list cell :=
  match l with
  | [] => []
  | s :: r => chop1 s (firstn (shape_size s) bs) :: chop r (skipn (shape_size s) bs)
  end.

Lemma lek_of_bytes : forall (k : nat) (bs : list byte), length bs = k -> (k <= 8)%nat ->
  Z_to_le_bytes k (bv_unsigned (le_bytes_to_word bs)) = bs.
Proof.
  intros k bs HL K8. unfold le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as HR. pose proof (bytes_le_to_Z_nonneg bs) as H0. rewrite HL in HR.
  assert (2 ^ (8 * Z.of_nat k) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64)%Z with (2^64)%Z; lia).
  rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma chop1_bytes : forall s bs, length bs = shape_size s -> cbytes (chop1 s bs) = bs /\ cell_wf (chop1 s bs).
Proof.
  intros s bs HL. destruct s; cbn [chop1 cbytes cell_wf shape_size] in *.
  - split; [| exact I]. unfold le8, word_to_le_bytes. apply lek_of_bytes; [exact HL| lia].
  - split; [| exact I]. unfold le4. apply lek_of_bytes; [exact HL| lia].
  - split; [| exact I]. unfold le2. apply lek_of_bytes; [exact HL| lia].
  - split; [| exact I]. destruct bs as [|b [|? ?]]; cbn in HL; try discriminate. reflexivity.
  - split; [reflexivity| exact HL].
Qed.

Lemma chop_props : forall l bs, length bs = shapes_size l ->
  cells_bytes (chop l bs) = bs /\ cells_wf (chop l bs) /\ cells_size (chop l bs) = shapes_size l.
Proof.
  induction l as [|s r IH]; intros bs HL; cbn [chop shapes_size cells_bytes cells_wf cells_size] in *.
  - destruct bs; [| discriminate]. repeat split.
  - assert (L1 : length (firstn (shape_size s) bs) = shape_size s) by (rewrite firstn_length; lia).
    assert (L2 : length (skipn (shape_size s) bs) = shapes_size r) by (rewrite skipn_length; lia).
    destruct (chop1_bytes s _ L1) as [B1 W1]. destruct (IH _ L2) as (B2 & W2 & S2).
    rewrite B1, B2, firstn_skipn. split; [reflexivity|]. split; [split; assumption|].
    rewrite S2. f_equal. destruct s; reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
Lemma rw_cells_chop : forall m A n junk l,
  rw_cells segs m A [CB n junk] -> shapes_size l = n -> rw_cells segs m A (chop l junk).
Proof.
  intros m A n junk l H HS.
  assert (HL : length junk = shapes_size l).
  { destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hwf _]. lia. }
  destruct (chop_props l junk HL) as (B & W & S).
  eapply rw_cells_recast; [exact H| exact W| |].
  - rewrite B. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite S. cbn [cells_size csize]. lia.
Qed.
End WithSegs.

Ltac chop_names_old H :=
  repeat match type of H with
         | context [le_bytes_to_word ?x] => let w := fresh "jw" in set (w := le_bytes_to_word x) in H; clearbody w
         | context [nth 0 ?x ?d] => let w := fresh "jb" in set (w := nth 0 x d) in H; clearbody w
         | context [CB ?n (firstn ?k ?x)] => let w := fresh "jbl" in set (w := firstn k x) in H; clearbody w
         end.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std Fresh Array List.
Set Default Proof Mode "Classic".

Ltac2 cn_head_is (f : constr) (r : constr) : bool :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Constant _ _ => Constr.equal f r
  | Constr.Unsafe.Constructor _ _ => Constr.equal f r
  | _ => false
  end.
Ltac2 cn_abs (acc : (constr * ident) list ref) (base : ident) (t : constr) : constr :=
  match List.find_opt (fun (u, _) => Constr.equal u t) (acc.(contents)) with
  | Some (_, id) => Control.hyp id
  | None =>
      let id := Fresh.in_goal base in
      Std.pose (Some id) t;
      acc.(contents) := (t, id) :: acc.(contents);
      Control.hyp id
  end.
Ltac2 rec cn_walk (acc : (constr * ident) list ref) (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let n := Array.length args in
      if (if Int.equal n 1 then cn_head_is f 'le_bytes_to_word else false) then cn_abs acc @jw t
      else if (if Int.equal n 4 then (if cn_head_is f '@nth then Constr.equal (Array.get args 1) 'O else false) else false) then cn_abs acc @jb t
      else if (if Int.equal n 2 then cn_head_is f 'CB else false) then
        (let b := Array.get args 1 in
         match Constr.Unsafe.kind b with
         | Constr.Unsafe.App g gargs =>
             if (if Int.equal (Array.length gargs) 3 then cn_head_is g '@firstn else false)
             then Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list [Array.get args 0; cn_abs acc @jbl b]))
             else t
         | _ => t
         end)
      else Constr.Unsafe.make (Constr.Unsafe.App f (Array.map (cn_walk acc) args))
  | _ => t
  end.
Ltac2 chop_names2 (h : ident) : unit :=
  let acc := { contents := [] } in
  let ty := Constr.type (Control.hyp h) in
  let ty' := cn_walk acc ty in
  match acc.(contents) with
  | [] => ()
  | l => Std.change None (fun _ => ty') { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)]; Std.on_concl := Std.NoOccurrences };
         Std.clearbody (List.map (fun (_, id) => id) l)
  end.
Ltac2 chop_names1 (h : Ltac1.t) : unit :=
  match Ltac1.to_ident h with
  | Some id => chop_names2 id
  | None =>
      match Ltac1.to_constr h with
      | Some c => (match Constr.Unsafe.kind c with Constr.Unsafe.Var id => chop_names2 id | _ => Control.zero (Tactic_failure (Some (Message.of_string "chop_names: not a hypothesis"))) end)
      | None => Control.zero (Tactic_failure (Some (Message.of_string "chop_names: not a hypothesis")))
      end
  end.
Ltac chop_names H := let f := ltac2:(h |- chop_names1 h) in f H.
