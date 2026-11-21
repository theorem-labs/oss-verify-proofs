(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state's environment and regions over the launch's whole ProcInput and mmap base, with the launch and E2BIG premises in place of entry_stack_fits: region 3 the auxv at the run's CONFIG_RSEQ value by Auxv.R3Tb, its launch-chosen words read from the vector's bytes (R3L_true, R3L_false, nth_flat_le8, nth_bg_bytes, bg_word_flat, bytes_val_word_le8); a cell holding another word of its region's background (slot_bg_copy); the region both CONFIG_RSEQ values imply holds wherever either value's does (R3A_of_R3Tb), and the same for the ASan and ASan+UBSan images' region 3, whose AT_PHNUM value is 11 (R3A_asan_of_R3Tb_asan; its end bound the plain regions' by end3_R3Tb_asan and end3_R3A_asan); the auxv's end bound at region 3's own size (f_end3T, f_end3A); region 1 from the start state's floor; argv[0]'s and argv[1]'s ends at most 2^47 - 9, was 2^47 - 16 (f_a0_end9, f_a1_end9), and the string area's end 8-aligned (f_str_end) in place of its start (f_align12); two_elems and nth_second_string at module level; imports Auxv, Regen, OblsLib, InitMem; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation Auxv Regen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require OblsLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan SI Auxv.
(* required after the imports above: its own dependencies bind short names
   ([Mem]) that would otherwise shadow FX's *)
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require InitMem.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module InitLib.

Lemma imap_of_bst : forall A (l : list (int * A)), IMap.bst (imap_of l).
Proof.
  intros A l. unfold imap_of.
  assert (G : forall acc, IMap.bst acc -> IMap.bst (fold_left (fun m kv => IMap.add (fst kv) (snd kv) m) l acc)).
  { induction l as [|kv l IH]; intros acc Hacc; cbn [fold_left]; [exact Hacc|]. apply IH. apply IMap.add_bst. exact Hacc. }
  apply G. exact I.
Qed.

Lemma find_in_elements : forall A k (v : A) m, IMap.bst m -> IMap.find k m = Some v -> In (k, v) (IMap.elements m).
Proof. intros A k v m Hb Hf. apply (proj2 (IMap.elements_spec k v m Hb)). exact Hf. Qed.

Lemma byte_of_le8 : forall (w : word) (i : nat), (i < 8)%nat -> nth i (word_le8 w) (Z_to_bv 8 0) = byte_of w (Z.of_nat i).
Proof. intros w i Hi. rewrite (word_le8_nth w i _ Hi). reflexivity. Qed.

(* Stated here, outside every section, because [argv] is [in_argv inp] now and
   a [destruct] on it inside [Section Entry] cannot abstract it: the section's
   [Let]s mention it ("Abstracting over the term l leads to a term ... which is
   ill-typed"). *)
Lemma two_elems : forall A (d : A) (l : list A),
  length l = 2%nat -> l = [hd d l; hd d (tl l)].
Proof. intros A d [|x [|y [|z r]]] H; cbn in H; try discriminate. reflexivity. Qed.

(* The second string of a two-element argv inside the launch's string area.
   Stated over plain lists at module level: inside [Section Entry] the
   right-associating [rewrite <- !app_assoc] leaves no [length (_ ++ _)] for
   the side conditions to match. *)
Lemma nth_second_string : forall (a b rest : list byte) (i : nat) d,
  (i <= length b)%nat ->
  nth (length a + 1 + i)
      (((a ++ [Z_to_bv 8 0]) ++ ((b ++ [Z_to_bv 8 0]) ++ [])) ++ rest) d
  = nth i (b ++ [Z_to_bv 8 0]) d.
Proof.
  intros a b rest i d Hi.
  rewrite app_nil_r, <- !app_assoc.
  rewrite app_nth2 by lia.
  replace (length a + 1 + i - length a)%nat with (S i) by lia.
  cbn [app nth].
  (* [cbn] has already turned [[Z_to_bv 8 0] ++ rest] into a cons, so there is
     no [b ++ [Z_to_bv 8 0] ++ rest] left for an [app_assoc] to find
     (reported at InitLib.v:59).  The case split closes it
     whether or not the term is syntactically exposed. *)
  destruct (Nat.lt_ge_cases i (length b)) as [Hlt|Hge].
  - rewrite !app_nth1 by lia. reflexivity.
  - assert (Heq : i = length b) by lia. subst i.
    rewrite !app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma ext_Z_false_id8 : forall u, 0 <= u < 2 ^ 64 -> ext_Z false 0 8 u = u.
Proof. intros u Hu. unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 8)) with (2 ^ 64). rewrite Z.div_1_r. apply Z.mod_small. exact Hu. Qed.

Lemma bytes_val_le8 : forall z, 0 <= z < 2 ^ 64 ->
  bytes_val false 8 (blob_bytes (Z_to_le_bytes 8 z) 0 8) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold bytes_val, blob_bytes. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 0) with 0%nat.
  rewrite skipn_O. rewrite firstn_all2 by (rewrite (length_Z_to_le_bytes 8%nat z); lia).
  rewrite bytes_le_to_Z_of_le_bytes by lia.
  change (8 * Z.of_nat 8) with 64. rewrite Z.mod_small by lia.
  rewrite ext_Z_false_id8; [reflexivity|]. lia.
Qed.

Definition segs_below (sgs : list Segment) (B : Z) : bool :=
  forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) B) sgs.

Lemma find_segment_bound : forall (sgs : list Segment) a n seg B,
  forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) B) sgs = true ->
  find_segment sgs a n = Some seg -> a + n <= B.
Proof.
  induction sgs as [|sg sgs IH]; intros a n seg B Hf H; cbn [find_segment] in H; [discriminate|].
  cbn [forallb] in Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:Hc.
  - apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. lia.
  - exact (IH a n seg B H2 H).
Qed.

Lemma find_segment_none : forall (sgs : list Segment) a n B,
  forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) B) sgs = true ->
  B <= a -> 0 < n -> find_segment sgs a n = None.
Proof.
  induction sgs as [|sg sgs IH]; intros a n B Hf Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1.
  replace (Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. exact (IH a n B H2 Ha Hn).
Qed.

(* The auxv region (region 3) of the start state, at LPS 727298f3, is
   [FX/Auxv.v]'s [R3Tb] at the run's CONFIG_RSEQ value: every type word a cell,
   a value word a cell only where the plan names its value, the launch-chosen
   values the region's [BGUnk] background, which [E0]'s [eg] reads off the
   vector's own bytes.  It was the released model's 20-word table. *)
Definition R3L_true := Eval vm_compute in IMap.elements (rg_cells (R3Tb true)).
Definition R3L_false := Eval vm_compute in IMap.elements (rg_cells (R3Tb false)).
Lemma R3_elements_true : IMap.elements (rg_cells (R3Tb true)) = R3L_true. Proof. vm_compute. reflexivity. Qed.
Lemma R3_elements_false : IMap.elements (rg_cells (R3Tb false)) = R3L_false. Proof. vm_compute. reflexivity. Qed.

(* Region 3 as both CONFIG_RSEQ values imply ([Auxv.R3A]) holds wherever the auxv at one value does: below
   granule 52 its cells are that value's (the same words at both values), its granules 52..57 are dirty and
   hold no cell, and its bound 432 is at most either vector's size. *)
Lemma dirty_from_bst : forall n g m, IMap.bst m -> IMap.bst (dirty_from g n m).
Proof. induction n as [|n IH]; intros g m Hm; cbn [dirty_from]; [exact Hm | apply IH; apply IMap.add_bst; exact Hm]. Qed.
Lemma R3A_bst : IMap.bst (rg_cells R3A).
Proof. unfold R3A. cbn [rg_cells]. apply dirty_from_bst. apply imap_of_bst. Qed.
Definition low52 (kv : int * gran) : bool := keyZ (fst kv) <? 52.
Lemma R3A_low : forall b, List.filter low52 (IMap.elements (rg_cells R3A)) = List.filter low52 (IMap.elements (rg_cells (R3Tb b))).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma R3A_high : forallb (fun kv => low52 kv || match snd kv with Gran true [] => keyZ (fst kv) <? 58 | _ => false end)
  (IMap.elements (rg_cells R3A)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma R3A_find_low : forall b g gr, keyZ g < 52 ->
  (IMap.find g (rg_cells R3A) = Some gr <-> IMap.find g (rg_cells (R3Tb b)) = Some gr).
Proof.
  intros b g gr Hg.
  assert (Bb : IMap.bst (rg_cells (R3Tb b))) by (unfold R3Tb; cbn [rg_cells]; apply imap_of_bst).
  assert (P : low52 (g, gr) = true) by (unfold low52; cbn [fst]; apply Z.ltb_lt; exact Hg).
  split; intros H.
  - apply (proj1 (IMap.elements_spec g gr _ Bb)). apply (proj2 (IMap.elements_spec g gr _ R3A_bst)) in H.
    assert (X : In (g, gr) (List.filter low52 (IMap.elements (rg_cells (R3Tb b)))))
      by (rewrite <- (R3A_low b); apply filter_In; split; [exact H | exact P]).
    exact (proj1 (proj1 (filter_In _ _ _) X)).
  - apply (proj1 (IMap.elements_spec g gr _ R3A_bst)). apply (proj2 (IMap.elements_spec g gr _ Bb)) in H.
    assert (X : In (g, gr) (List.filter low52 (IMap.elements (rg_cells R3A))))
      by (rewrite (R3A_low b); apply filter_In; split; [exact H | exact P]).
    exact (proj1 (proj1 (filter_In _ _ _) X)).
Qed.
Lemma R3A_find_high : forall g gr, IMap.find g (rg_cells R3A) = Some gr -> 52 <= keyZ g -> gr = Gran true [] /\ keyZ g < 58.
Proof.
  intros g gr F Hg. apply (proj2 (IMap.elements_spec g gr _ R3A_bst)) in F.
  pose proof (proj1 (forallb_forall _ _) R3A_high (g, gr) F) as X. cbv beta in X.
  unfold low52 in X. cbn [fst snd] in X.
  replace (keyZ g <? 52) with false in X by (symmetry; apply Z.ltb_ge; exact Hg). cbn [orb] in X.
  destruct gr as [[|] [|c l]]; try discriminate X. split; [reflexivity | apply Z.ltb_lt; exact X].
Qed.
Lemma R3A_of_R3Tb : forall segs priv E m b,
  region_ok segs priv E m 3%uint63 (R3Tb b) -> region_ok segs priv E m 3%uint63 R3A.
Proof.
  intros segs priv E m b RO.
  assert (K : PrimInt63.eqb 3%uint63 0%uint63 = false) by reflexivity.
  assert (HI : hiZ E R3A = 432) by reflexivity.
  assert (HIb : 432 <= hiZ E (R3Tb b))
    by (destruct b; [change (hiZ E (R3Tb true)) with 464 | change (hiZ E (R3Tb false)) with 432]; lia).
  assert (LO : loZ R3A = 0) by reflexivity.
  assert (LOb : loZ (R3Tb b) = 0) by reflexivity.
  constructor.
  - exact R3A_bst.
  - intros _. destruct (ro_range _ _ _ _ _ _ RO K) as [R1 R2]. rewrite LO, HI. rewrite LOb in R1. lia.
  - intros _ a Ha. rewrite LO, HI in Ha. apply (ro_valid _ _ _ _ _ _ RO K). rewrite LOb. lia.
  - intros g gr F. destruct (Z.lt_ge_cases (keyZ g) 52) as [Lt|Ge].
    + exact (ro_cells _ _ _ _ _ _ RO g gr (proj1 (R3A_find_low b g gr Lt) F)).
    + destruct (R3A_find_high g gr F Ge) as [-> _]. split; [exact I | constructor].
  - intros g gr c i F Hc Hi. cbv zeta. split; [| intros K'; rewrite K in K'; discriminate K'].
    intros _. rewrite LO, HI. destruct (Z.lt_ge_cases (keyZ g) 52) as [Lt|Ge].
    + pose proof (proj1 (R3A_find_low b g gr Lt) F) as Fb.
      pose proof (proj1 (ro_cells_in _ _ _ _ _ _ RO g gr c i Fb Hc Hi) K) as X. rewrite LOb in X.
      destruct (ro_cells _ _ _ _ _ _ RO g gr Fb) as [_ S].
      destruct (proj1 (Forall_forall _ _) S c Hc) as (C1 & C2 & C3 & _). lia.
    + destruct (R3A_find_high g gr F Ge) as [-> _]. destruct Hc.
  - intros o Ho _ Hunc. specialize (Ho K). rewrite LO, HI in Ho.
    destruct (Z.lt_ge_cases (o / 8) 52) as [Lt|Ge].
    + assert (U : uncovered (R3Tb b) o).
      { intros g gr Hg F. exact (Hunc g gr Hg (proj2 (R3A_find_low b g gr ltac:(lia)) F)). }
      assert (Ob : PrimInt63.eqb 3%uint63 0%uint63 = false -> loZ (R3Tb b) <= o < hiZ E (R3Tb b)) by (intros _; rewrite LOb; lia).
      exact (ro_bg _ _ _ _ _ _ RO o Ob (fun K' => ltac:(rewrite K in K'; discriminate K')) U).
    + exfalso. assert (D : o / 8 = 52 \/ o / 8 = 53) by (Z.div_mod_to_equations; lia).
      destruct D as [D|D].
      * destruct (Hunc 52%uint63 (Gran true []) ltac:(rewrite D; reflexivity) ltac:(vm_compute; reflexivity)) as [Hd _]. discriminate Hd.
      * destruct (Hunc 53%uint63 (Gran true []) ltac:(rewrite D; reflexivity) ltac:(vm_compute; reflexivity)) as [Hd _]. discriminate Hd.
Qed.

(* The same for the ASan and ASan+UBSan images' region 3 ([Auxv.R3Tb_asan], [Auxv.R3A_asan]: AT_PHNUM's
   value 11), and their end bound, which reads region 3's size only and so is the plain regions'. *)
Lemma R3A_asan_bst : IMap.bst (rg_cells R3A_asan).
Proof. unfold R3A_asan. cbn [rg_cells]. apply dirty_from_bst. apply imap_of_bst. Qed.
Lemma R3A_asan_low : forall b, List.filter low52 (IMap.elements (rg_cells R3A_asan)) = List.filter low52 (IMap.elements (rg_cells (R3Tb_asan b))).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma R3A_asan_high : forallb (fun kv => low52 kv || match snd kv with Gran true [] => keyZ (fst kv) <? 58 | _ => false end)
  (IMap.elements (rg_cells R3A_asan)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma R3A_asan_find_low : forall b g gr, keyZ g < 52 ->
  (IMap.find g (rg_cells R3A_asan) = Some gr <-> IMap.find g (rg_cells (R3Tb_asan b)) = Some gr).
Proof.
  intros b g gr Hg.
  assert (Bb : IMap.bst (rg_cells (R3Tb_asan b))) by (unfold R3Tb_asan; cbn [rg_cells]; apply imap_of_bst).
  assert (P : low52 (g, gr) = true) by (unfold low52; cbn [fst]; apply Z.ltb_lt; exact Hg).
  split; intros H.
  - apply (proj1 (IMap.elements_spec g gr _ Bb)). apply (proj2 (IMap.elements_spec g gr _ R3A_asan_bst)) in H.
    assert (X : In (g, gr) (List.filter low52 (IMap.elements (rg_cells (R3Tb_asan b)))))
      by (rewrite <- (R3A_asan_low b); apply filter_In; split; [exact H | exact P]).
    exact (proj1 (proj1 (filter_In _ _ _) X)).
  - apply (proj1 (IMap.elements_spec g gr _ R3A_asan_bst)). apply (proj2 (IMap.elements_spec g gr _ Bb)) in H.
    assert (X : In (g, gr) (List.filter low52 (IMap.elements (rg_cells R3A_asan))))
      by (rewrite (R3A_asan_low b); apply filter_In; split; [exact H | exact P]).
    exact (proj1 (proj1 (filter_In _ _ _) X)).
Qed.
Lemma R3A_asan_find_high : forall g gr, IMap.find g (rg_cells R3A_asan) = Some gr -> 52 <= keyZ g -> gr = Gran true [] /\ keyZ g < 58.
Proof.
  intros g gr F Hg. apply (proj2 (IMap.elements_spec g gr _ R3A_asan_bst)) in F.
  pose proof (proj1 (forallb_forall _ _) R3A_asan_high (g, gr) F) as X. cbv beta in X.
  unfold low52 in X. cbn [fst snd] in X.
  replace (keyZ g <? 52) with false in X by (symmetry; apply Z.ltb_ge; exact Hg). cbn [orb] in X.
  destruct gr as [[|] [|c l]]; try discriminate X. split; [reflexivity | apply Z.ltb_lt; exact X].
Qed.
Lemma R3A_asan_of_R3Tb_asan : forall segs priv E m b,
  region_ok segs priv E m 3%uint63 (R3Tb_asan b) -> region_ok segs priv E m 3%uint63 R3A_asan.
Proof.
  intros segs priv E m b RO.
  assert (K : PrimInt63.eqb 3%uint63 0%uint63 = false) by reflexivity.
  assert (HI : hiZ E R3A_asan = 432) by reflexivity.
  assert (HIb : 432 <= hiZ E (R3Tb_asan b))
    by (destruct b; [change (hiZ E (R3Tb_asan true)) with 464 | change (hiZ E (R3Tb_asan false)) with 432]; lia).
  assert (LO : loZ R3A_asan = 0) by reflexivity.
  assert (LOb : loZ (R3Tb_asan b) = 0) by reflexivity.
  constructor.
  - exact R3A_asan_bst.
  - intros _. destruct (ro_range _ _ _ _ _ _ RO K) as [R1 R2]. rewrite LO, HI. rewrite LOb in R1. lia.
  - intros _ a Ha. rewrite LO, HI in Ha. apply (ro_valid _ _ _ _ _ _ RO K). rewrite LOb. lia.
  - intros g gr F. destruct (Z.lt_ge_cases (keyZ g) 52) as [Lt|Ge].
    + exact (ro_cells _ _ _ _ _ _ RO g gr (proj1 (R3A_asan_find_low b g gr Lt) F)).
    + destruct (R3A_asan_find_high g gr F Ge) as [-> _]. split; [exact I | constructor].
  - intros g gr c i F Hc Hi. cbv zeta. split; [| intros K'; rewrite K in K'; discriminate K'].
    intros _. rewrite LO, HI. destruct (Z.lt_ge_cases (keyZ g) 52) as [Lt|Ge].
    + pose proof (proj1 (R3A_asan_find_low b g gr Lt) F) as Fb.
      pose proof (proj1 (ro_cells_in _ _ _ _ _ _ RO g gr c i Fb Hc Hi) K) as X. rewrite LOb in X.
      destruct (ro_cells _ _ _ _ _ _ RO g gr Fb) as [_ S].
      destruct (proj1 (Forall_forall _ _) S c Hc) as (C1 & C2 & C3 & _). lia.
    + destruct (R3A_asan_find_high g gr F Ge) as [-> _]. destruct Hc.
  - intros o Ho _ Hunc. specialize (Ho K). rewrite LO, HI in Ho.
    destruct (Z.lt_ge_cases (o / 8) 52) as [Lt|Ge].
    + assert (U : uncovered (R3Tb_asan b) o).
      { intros g gr Hg F. exact (Hunc g gr Hg (proj2 (R3A_asan_find_low b g gr ltac:(lia)) F)). }
      assert (Ob : PrimInt63.eqb 3%uint63 0%uint63 = false -> loZ (R3Tb_asan b) <= o < hiZ E (R3Tb_asan b)) by (intros _; rewrite LOb; lia).
      exact (ro_bg _ _ _ _ _ _ RO o Ob (fun K' => ltac:(rewrite K in K'; discriminate K')) U).
    + exfalso. assert (D : o / 8 = 52 \/ o / 8 = 53) by (Z.div_mod_to_equations; lia).
      destruct D as [D|D].
      * destruct (Hunc 52%uint63 (Gran true []) ltac:(rewrite D; reflexivity) ltac:(vm_compute; reflexivity)) as [Hd _]. discriminate Hd.
      * destruct (Hunc 53%uint63 (Gran true []) ltac:(rewrite D; reflexivity) ltac:(vm_compute; reflexivity)) as [Hd _]. discriminate Hd.
Qed.
Lemma end3_R3Tb_asan : forall b, Regen.end3_fact (R3Tb_asan b) = Regen.end3_fact (R3Tb b).
Proof. intros b. reflexivity. Qed.
Lemma end3_R3A_asan : Regen.end3_fact R3A_asan = Regen.end3_fact R3A.
Proof. reflexivity. Qed.

Lemma nth_flat_le8 : forall (l : list word) (i : nat), (i < 8 * length l)%nat ->
  nth i (flat_map word_le8 l) (Z_to_bv 8 0) = nth (i mod 8) (word_le8 (nth (i / 8) l (Z_to_bv 64 0))) (Z_to_bv 8 0).
Proof.
  induction l as [|w l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  cbn [flat_map]. destruct (Nat.lt_ge_cases i 8) as [H8|H8].
  - rewrite app_nth1 by (rewrite length_word_le8; exact H8).
    rewrite Nat.mod_small by exact H8. rewrite Nat.div_small by exact H8. reflexivity.
  - rewrite app_nth2 by (rewrite length_word_le8; exact H8). rewrite length_word_le8.
    rewrite IH by lia.
    assert (E1 : (i mod 8 = (i - 8) mod 8)%nat)
      by (replace i with ((i - 8) + 1 * 8)%nat at 1 by lia; apply Nat.Div0.mod_add).
    assert (E2 : (i / 8 = S ((i - 8) / 8))%nat)
      by (replace i with ((i - 8) + 1 * 8)%nat at 1 by lia; rewrite Nat.div_add by lia; lia).
    rewrite E1, E2. reflexivity.
Qed.

(* A [BGUnk] word of the vector read back as the word itself: the background of
   region 3 is the vector's bytes ([eg0 3]), so eight of them from a word's
   offset are that word ([Auxv.aux_val 22], AT_EGID's cell, is AT_GID's
   background word). *)
Lemma nth_bg_bytes : forall g n off i d, (i < n)%nat -> nth i (bg_bytes g off n) d = g (off + Z.of_nat i).
Proof.
  intros g n. induction n as [|n IH]; intros off i d Hi; [lia|].
  destruct i as [|i]; cbn [bg_bytes nth].
  - f_equal. lia.
  - rewrite IH by lia. f_equal. lia.
Qed.
Lemma length_bg_bytes : forall g n off, length (bg_bytes g off n) = n.
Proof. intros g n. induction n as [|n IH]; intros off; cbn [bg_bytes length]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma bg_word_flat : forall (l : list word) (j : nat), (j < length l)%nat ->
  bg_bytes (fun o => nth (Z.to_nat o) (flat_map word_le8 l) (Z_to_bv 8 0)) (8 * Z.of_nat j) 8
  = word_le8 (nth j l (Z_to_bv 64 0)).
Proof.
  intros l j Hj. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  - rewrite length_bg_bytes, length_word_le8. reflexivity.
  - intros i Hi. rewrite length_bg_bytes in Hi. rewrite nth_bg_bytes by exact Hi. cbv beta.
    replace (Z.to_nat (8 * Z.of_nat j + Z.of_nat i)) with (8 * j + i)%nat by lia.
    rewrite nth_flat_le8 by nia.
    replace ((8 * j + i) mod 8)%nat with i by (apply (Nat.mod_unique _ _ j); lia).
    replace ((8 * j + i) / 8)%nat with j by (apply (Nat.div_unique _ _ _ i); lia).
    reflexivity.
Qed.
Lemma bytes_val_word_le8 : forall w : word, bytes_val false 8 (word_le8 w) = w.
Proof.
  intros w. unfold bytes_val. rewrite OblsLib.OL.bytes_le_word_le8. pose proof (u64_range w) as Hw.
  rewrite ext_Z_false_id8 by (unfold two64 in Hw; lia). apply Z_to_bv_bv_unsigned.
Qed.

(* A cell holding eight background bytes from offset [off] of a region whose background reads memory from
   [base] ([BGUnk]): it holds wherever the cell's own word and the word at [off] are one word in memory
   (AT_EGID's value cell, AT_GID's word, at the main entry). *)
Lemma slot_bg_copy : forall segs E m (base A : Z) (k : int) (off : w64) (W : word),
  (forall o, eg E k o = match rb segs m (base + o) with Some b => b | None => Z_to_bv 8 0 end) ->
  (forall i, 0 <= i < 8 -> rb segs m (base + w2Zs off + i) = Some (byte_of W i)) ->
  (forall i, 0 <= i < 8 -> rb segs m (A + i) = Some (byte_of W i)) ->
  slot_ok segs E m A [Cell 0%uint63 8%uint63 (VBg false k off 8%uint63)].
Proof.
  intros segs E m base A k off W Heg H2 H1.
  assert (D : den E (VBg false k off 8%uint63) = W).
  { cbn [den]. change (Z.to_nat (to_Z 8%uint63)) with 8%nat. change (to_Z 8%uint63) with 8.
    replace (bg_bytes (eg E k) (w2Zs off) 8) with (word_le8 W); [apply bytes_val_word_le8|].
    apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
    - rewrite length_bg_bytes, length_word_le8. reflexivity.
    - intros i Hi. rewrite length_word_le8 in Hi. rewrite nth_bg_bytes by exact Hi. rewrite byte_of_le8 by exact Hi.
      rewrite Heg, Z.add_assoc, (H2 (Z.of_nat i) ltac:(lia)). reflexivity. }
  split; [exact (conj I I)|].
  constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v].
  change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. rewrite D. replace (A + 0 + i) with (A + i) by lia. exact (H1 i Hi).
Qed.

Section Image.
Variables (SEGS : list Segment) (PC : N) (PH : PhdrInfo) (SEGTOP : Z).
Hypothesis segs_below_top : segs_below SEGS SEGTOP = true.
Hypothesis segtop_low : SEGTOP <= 0x7fff7f800000.
Hypothesis HphA : Z.of_N (ph_addr PH) = 65600.
Hypothesis HphE : Z.of_N (ph_ent PH) = 56.
Hypothesis HphN : Z.of_N (ph_num PH) = 10.

Lemma memory_read_find : forall a bs, 0 <= a < 2 ^ 64 -> memory_read SEGS (Z_to_bv 64 a) 1 = Some bs -> a + 1 <= SEGTOP.
Proof.
  intros a bs Ha H. unfold memory_read in H. rewrite Z_to_bv64_unsigned in H by exact Ha.
  destruct (find_segment SEGS a (Z.of_N 1)) as [seg|] eqn:Hf; [|discriminate].
  exact (find_segment_bound SEGS a 1 seg SEGTOP segs_below_top Hf).
Qed.

Definition PB_STD (b : int -> list byte) : Prop :=
  exists (a0 : list byte) (eptrs : list word),
    b 1%uint63 = a0 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) a0 /\ Z.of_nat (length a0) <= 131071 /\
    b 2%uint63 = flat_map word_le8 eptrs ++ word_le8 (Z_to_bv 64 0) /\ Z.of_nat (length eptrs) <= 256 /\
    Forall (fun p => 0 < bv_unsigned p) eptrs /\
    b 8%uint63 = Z_to_le_bytes 8 (8 * Z.of_nat (length eptrs) + 8) /\
    b 9%uint63 = Z_to_le_bytes 8 (Z.of_nat (length a0) + 1) /\
    length (b 6%uint63) = 16%nat.

Definition PB_ARG1 (b : int -> list byte) : Prop :=
  exists (a1 : list byte),
    b 3%uint63 = a1 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) a1 /\ Z.of_nat (length a1) <= 131071 /\
    b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length a1) + 1).

Section Entry.
(* Parity with the ported sibling [StackInit.v:133-141].  At this revision
   [Run.init_machine_state] takes a whole [ProcInput] and the entry's mmap
   base, so argv, envp, the exec name and the ids come out of [inp].  They are
   Notations, not Variables, exactly as the sibling has them: a Notation is not
   a section variable, so it never appears in a discharged argument list and
   [E0] keeps the short signature its eleven consumers apply. *)
Variables (sp brk0 mbase : word) (inp : ProcInput) (draw : EntryDraw).
Notation argv := (in_argv inp).
Notation envp := (in_envp inp).
Notation execfn := (in_execfn inp).
Notation uid := (in_uid inp).
Notation gid := (in_gid inp).
Notation hwcap := (in_hwcap inp).
Variable xb : int -> list byte.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
(* [entry_stack_fits] no longer carries the launch geometry; the launch
   conjunct does ([StackInit.v:205]), and [Run.valid_entry_sv48] hands exactly
   this to every consumer. *)
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp.
Hypothesis Hhw : valid_hwcap hwcap.
(* The launch's argument and environment caps ([Run.valid_launch]).  Only the
   window below [sp] reads it ([WLO_floor]), so only [R1_ok] and [R1F_ok] and
   what is built on them take it (ALib/InitMem.v's stack_window_lo_valid). *)
Hypothesis Hvl : valid_launch inp.

(* The whole [SI] interface at this section's instantiation.  Shadowing the
   imported names with their applied forms keeps every use site below spelled
   as it was; where a proof needs to unfold one, it names the constant
   ([unfold SI.envp_off]), since [unfold] does not take an abbreviation. *)
Local Notation SP := (SI.SP sp).
Local Notation TOP := (SI.TOP draw).
Local Notation LA := (SI.LA sp mbase inp).
Local Notation HEAD := (SI.HEAD sp mbase inp).
Local Notation LSB := (SI.LSB inp).
Local Notation gap := (SI.gap inp).
Local Notation pad := (SI.pad sp mbase inp draw).
Local Notation WLO := (SI.WLO mbase inp draw).
Local Notation nargc := (SI.nargc inp).
Local Notation nenvc := (SI.nenvc inp).
Local Notation argcZ := (SI.argcZ inp).
Local Notation envcZ := (SI.envcZ inp).
Local Notation envp_off := (SI.envp_off inp).
Local Notation auxv_off := (SI.auxv_off inp).
Local Notation str_base := (SI.str_base inp draw).
Local Notation env_str_base := (SI.env_str_base inp draw).
Local Notation argv_ptrs := (SI.argv_ptrs inp draw).
Local Notation envp_ptrs := (SI.envp_ptrs inp draw).
Local Notation envp_img := (SI.envp_img inp draw).
Local Notation strarea := (SI.strarea inp).
Local Notation ARND := (SI.ARND sp mbase inp).
Local Notation AEXECFN := (SI.AEXECFN inp draw).
Local Notation ENTRY := (SI.ENTRY PC).
Local Notation auxws := (SI.auxws PC PH sp mbase inp draw).
Local Notation AUXV := (SI.AUXV PC PH sp mbase inp draw).
Local Notation BSB := (SI.BSB PC PH sp mbase inp draw).
Local Notation IMG := (SI.IMG PC PH sp mbase inp draw).
Local Notation mem0 := (SI.mem0 SEGS PC PH sp mbase inp draw).
Local Notation word_at := (SI.word_at SEGS PC PH sp mbase inp draw).

(* The two offsets the released model exported as [SI.sstruct] and
   [SI.raw_len + SI.pad] and this revision removed, because the launch is
   measured DOWN from [TOP] and neither is a function of the header alone.
   What this file used them for is their VALUES -- sp-to-string-area and
   sp-to-AT_RANDOM -- and those the revision still names: [SI.str_base_val]
   gives the first as [HEAD + pad], [SI.ARND_val] the second as [HEAD - 16].
   Defined here rather than reinstated in [StackInit.v], so that this file
   carries its own abbreviation and the sibling keeps saying what the model
   says. *)
Local Notation sstruct := (SI.HEAD sp mbase inp + SI.pad sp mbase inp draw)%nat.
Local Notation rndoff := (SI.HEAD sp mbase inp - 16)%nat.

Let a0 : list byte := hd [] argv.
Let a1 : list byte := hd [] (tl argv).
Let ms0 : machine_state := init_machine_state SEGS PC PH sp mbase draw inp.

Definition ev0 (k : int) : word :=
  match to_Z k with
  | 1 => sp
  | 2 => Z_to_bv 64 (SP + envp_off)
  | 3 => Z_to_bv 64 (SP + auxv_off)
  | 4 => len_word argv
  | 5 => str_base
  | 6 => ARND
  | 7 => hwcap
  | 8 => uid
  | 10 => Z_to_bv 64 (SP + Z.of_nat (sstruct) + Z.of_nat (length a0) + 1)
  | 12 => str_base
  | _ => Z_to_bv 64 0
  end.

Definition eb0 (j : int) : list byte :=
  match to_Z j with
  | 1 => a0 ++ [Z_to_bv 8 0]
  | 2 => envp_img
  | 3 => a1 ++ [Z_to_bv 8 0]
  | 6 => at_random_bytes (ed_random draw)
  | 8 => Z_to_le_bytes 8 (8 * envcZ + 8)
  | 9 => Z_to_le_bytes 8 (Z.of_nat (length a0) + 1)
  | 10 => Z_to_le_bytes 8 (Z.of_nat (length a1) + 1)
  | 12 => strarea
  | 15 => Z_to_le_bytes 8 (Z.of_nat (length (strarea)))
  | _ => xb j
  end.

Definition eg0 (k : int) (o : Z) : byte :=
  match to_Z k with
  | 3 => nth (Z.to_nat o) (flat_map word_le8 auxws) (Z_to_bv 8 0)
  | 6 => nth (Z.to_nat o) (at_random_bytes (ed_random draw)) (Z_to_bv 8 0)
  | _ => Z_to_bv 8 0
  end.

Definition E0 : env := Env ev0 eb0 eg0.

Let Hlo := SI.SP_lo sp Hsp.
Let Htop := SI.BSB_top PC PH sp brk0 mbase inp draw Hlaunch.
Let Hargc := SI.argc_range inp Hva.
Let Henvc := SI.envc_range inp Hve.
Let Hgeom := SI.geom sp brk0 mbase inp draw Hlaunch.
Let Hpadeq := SI.pad_eq sp brk0 mbase inp draw Hlaunch.
Let Htophi := SI.top_hi sp brk0 mbase inp draw Hlaunch.
Let Hheadeq := SI.HEAD_eq sp mbase inp.
Let Hlsbeq := SI.LSB_eq inp.

Lemma argv_eq : argv = a0 :: tl argv.
Proof.
  destruct (SI.argv_cons inp Hva) as (x & rest & Hx). unfold a0. rewrite Hx. reflexivity.
Qed.

Lemma a0_len : Z.of_nat (length a0) <= 131071.
Proof.
  pose proof Hva as (_ & _ & Hl & _). rewrite argv_eq in Hl. inversion Hl. assumption.
Qed.

Lemma a0_nonul : ~ In (Z_to_bv 8 0) a0.
Proof.
  pose proof Hva as (_ & _ & _ & Hn & _). rewrite argv_eq in Hn. inversion Hn. assumption.
Qed.

(* The entry block's length, in the revision's own terms.  [SI.length_BSB]
   is [HEAD + pad + LSB + 8]; [sstruct] is [HEAD + pad] by definition, so this
   is the same equation one abbreviation shorter. *)
Lemma len_BSB : Z.of_nat (length (BSB)) = Z.of_nat (sstruct) + Z.of_nat LSB + 8.
Proof. rewrite (SI.length_BSB PC PH sp mbase inp draw). lia. Qed.

(* [auxv_size (la_rseq LA)] is an ATOM with no bound: [kb_rseq] is free under
   [valid_input], so the vector is 27 entries or 29 and this file must not
   decide which.  [lia] is syntactic on atoms, so every arithmetic goal below
   that crosses the entry block needs this range in scope rather than a
   number.  432 = 16 * 27, 464 = 16 * 29. *)
(* Stated over an arbitrary boolean and then applied: a [destruct] on
   [la_rseq LA] inside the section cannot abstract it, because the section's
   [Let]s above mention it ("Abstracting over the term b leads to a term ...",
   measured). *)
Lemma auxv_size_rng_b : forall b : bool, 432 <= Z.of_nat (auxv_size b) <= 464.
Proof. intros b. unfold auxv_size, auxv_count. destruct b; cbn [Nat.mul]; lia. Qed.
Lemma auxv_size_rng : 432 <= Z.of_nat (auxv_size (la_rseq LA)) <= 464.
Proof. apply auxv_size_rng_b. Qed.

Lemma auxv_size_div8 : exists k, Z.of_nat (auxv_size (la_rseq LA)) = 8 * k.
Proof. exists (2 * Z.of_nat (auxv_count (la_rseq LA))). unfold auxv_size. lia. Qed.

Lemma gap_rng : 0 <= Z.of_nat (gap) <= 8.
Proof.
  unfold SI.gap. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia.
Qed.

Lemma gap_div8 : exists k, Z.of_nat (gap) = 8 * k.
Proof. exists (Z.of_nat (block_items argv envp mod 2)). unfold SI.gap. lia. Qed.

(* The released model's [sstruct] was [8 + (nargc+1)*8 + (nenvc+1)*8 + 160], a
   closed number because the vector was twenty words.  Its replacement keeps
   the same shape with the vector's size left as the atom it now is. *)
Lemma sstruct_val : Z.of_nat (sstruct)
  = 8 * argcZ + 8 * envcZ + 40 + Z.of_nat (auxv_size (la_rseq LA)) + Z.of_nat (gap) + Z.of_nat (pad).
Proof.
  rewrite Nat2Z.inj_add, Hheadeq. unfold SI.argcZ, SI.envcZ. lia.
Qed.

(* The one geometry fact the rest of the file leans on: the string area ends
   eight bytes below the stack VMA's top.  [SI.pad_eq] states the pad as
   [TOP - 8 - LSB - SP - HEAD], so [SP + HEAD + pad] collapses. *)
Lemma sstruct_eq_top : SP + Z.of_nat (sstruct) = bv_unsigned TOP - 8 - Z.of_nat LSB.
Proof. rewrite Nat2Z.inj_add, Hpadeq. lia. Qed.

(* [SI.argv0_byte], [SI.strarea_byte] and [argv1_byte] are all stated over
   [bv_unsigned str_base], where the released model stated them over
   [SP + sstruct].  The two are equal, but [rewrite] is syntactic: without this
   the rewrites find no subterm (reported at InitLib.v:576). *)
Lemma str_baseZ : bv_unsigned str_base = SP + Z.of_nat (sstruct).
Proof. apply (SI.str_base_val sp brk0 mbase inp draw Hsp Hlaunch). Qed.

Lemma HEAD_ge : 16 <= Z.of_nat HEAD.
Proof. rewrite Hheadeq. pose proof auxv_size_rng. pose proof gap_rng. lia. Qed.

Lemma rndoff_val : Z.of_nat (rndoff) = Z.of_nat HEAD - 16.
Proof. pose proof HEAD_ge. lia. Qed.

Lemma rndoff_le : Z.of_nat (rndoff) <= Z.of_nat (sstruct).
Proof. pose proof rndoff_val. rewrite Nat2Z.inj_add. lia. Qed.

(* The stack VMA's floor, bounded below by the launch's own clause on [TOP].
   [valid_stack_top_va]'s third conjunct (727298f3 Run.v:3619-3624) puts [TOP]
   within [stack_rnd_max + page_size] of [va_stack_top Sv48]; [SI.WLO] is a
   [Z.max] whose left arm is [TOP - stack_max_size], so this is the floor's
   worst case.  The image's segments end far below it, which is what [R0_ok]
   needs in place of the released model's [SP - stack_max_size]. *)
Lemma WLO_lo : 0x7fffbf800000 <= WLO.
Proof.
  pose proof Hlaunch as Hok. cbn [entry_launch_ok_va] in Hok.
  destruct Hok as ((_ & _ & Hlt) & _ & _).
  (* [valid_stack_top_va]'s own bound is [if kb_aslr … then stack_rnd_max +
     page_size else page_size], and [kb_aslr] is as free as [kb_rseq]: [lia] is
     syntactic on atoms and the [if] is one, so the branch gets a bound of its
     own rather than an unfold ("Cannot find witness",
     reported at InitLib.v:306). *)
  assert (Hb : (if kb_aslr (in_kernel inp) then stack_rnd_max + page_size else page_size)
               <= 0x40000000)
    by (unfold stack_rnd_max, page_size; destruct (kb_aslr (in_kernel inp)); lia).
  unfold SI.WLO, stack_window_lo.
  pose proof (Z.le_max_l (bv_unsigned (ed_top draw) - stack_max_size)
                         (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hm.
  unfold va_stack_top, sp_window_hi, stack_max_size in *. lia.
Qed.

(* [SI.ARND_aligned] went with the released model's [raw_len].  The fact it
   stated still holds and for a plainer reason: AT_RANDOM sits at [HEAD - 16]
   above [sp], [HEAD] is [8 * items + auxv_size + 8 * (items mod 2) + 16] and
   [auxv_size] is [16 * auxv_count], so [HEAD] is a multiple of 8 whichever
   way [la_rseq] falls. *)
Lemma HEAD_mod8 : Z.of_nat HEAD mod 8 = 0.
Proof.
  destruct auxv_size_div8 as [k1 H1]. destruct gap_div8 as [k2 H2].
  apply Z.mod_divide; [lia|].
  exists (Z.of_nat (SI.nargc inp) + Z.of_nat (SI.nenvc inp) + k1 + k2 + 5).
  rewrite Hheadeq, H1, H2. lia.
Qed.

Lemma ARND_aligned : bv_unsigned ARND mod 8 = 0.
Proof.
  rewrite (SI.ARND_val sp brk0 mbase inp draw Hlaunch).
  pose proof HEAD_mod8 as HM. pose proof Hsp as (_ & _ & Hal). fold (SI.SP sp) in Hal.
  apply Z.mod_divide; [lia|].
  apply (proj1 (Z.mod_divide (SI.SP sp) 16 ltac:(lia))) in Hal. destruct Hal as [q Hq].
  apply Z.mod_divide in HM; [|lia]. destruct HM as [r Hr].
  exists (2 * q + r - 2). lia.
Qed.

Lemma total_ge_a0 : Z.of_nat (length a0) + 1 <= Z.of_nat (total_nat argv).
Proof. pose proof argv_eq as E. replace (total_nat argv) with (total_nat (a0 :: tl argv)) by (rewrite <- E; reflexivity). cbn [total_nat]. lia. Qed.

Lemma ev0_0 : ev E0 0%uint63 = Z_to_bv 64 0. Proof. reflexivity. Qed.
Lemma ev0_1 : ev E0 1%uint63 = sp. Proof. reflexivity. Qed.
Lemma ev0_2 : bv_unsigned (ev E0 2%uint63) = SP + envp_off.
Proof. change (ev E0 2%uint63) with (Z_to_bv 64 (SP + envp_off)). apply Z_to_bv64_unsigned. unfold SI.envp_off. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. lia. Qed.
Lemma ev0_3 : bv_unsigned (ev E0 3%uint63) = SP + auxv_off.
Proof. change (ev E0 3%uint63) with (Z_to_bv 64 (SP + auxv_off)). apply Z_to_bv64_unsigned. unfold SI.auxv_off. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. lia. Qed.
Lemma ev0_4 : ev E0 4%uint63 = len_word argv. Proof. reflexivity. Qed.
Lemma ev0_5 : bv_unsigned (ev E0 5%uint63) = SP + Z.of_nat (sstruct).
Proof. change (ev E0 5%uint63) with (str_base). rewrite (SI.str_base_val sp brk0 mbase inp draw Hsp Hlaunch). reflexivity. Qed.
Lemma ev0_6 : bv_unsigned (ev E0 6%uint63) = SP + Z.of_nat (rndoff).
Proof.
  change (ev E0 6%uint63) with (ARND).
  rewrite (SI.ARND_val sp brk0 mbase inp draw Hlaunch), rndoff_val. lia.
Qed.
Lemma ev0_7 : ev E0 7%uint63 = hwcap. Proof. reflexivity. Qed.
Lemma ev0_8 : ev E0 8%uint63 = uid. Proof. reflexivity. Qed.
Lemma ev0_12 : bv_unsigned (ev E0 12%uint63) = SP + Z.of_nat (sstruct).
Proof. change (ev E0 12%uint63) with (str_base). rewrite (SI.str_base_val sp brk0 mbase inp draw Hsp Hlaunch). reflexivity. Qed.
(* The string area now carries the exec name, its NUL and the eight-byte slot
   under the VMA's end as well as the argv and envp strings: [SI.strarea] is
   [LSB + 8] long ([SI.length_strarea]).  The released model's [strarea] was
   the strings plus the pad, because the pad sat above them. *)
Lemma strarea_len : Z.of_nat (length (strarea)) = Z.of_nat LSB + 8.
Proof. rewrite (SI.length_strarea inp). lia. Qed.

Lemma den_VP0 : forall k, den E0 (VP k (wp 0%uint63)) = ev E0 k.
Proof. intros k. cbn [den]. apply bv_add_0_r. reflexivity. Qed.

Lemma den_SIZE8 : den E0 (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (8 * envcZ + 8).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. lia.
Qed.
Lemma den_SIZE9 : den E0 (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (Z.of_nat (length a0) + 1).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. pose proof a0_len. lia.
Qed.
Lemma den_SIZE15 : den E0 (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (Z.of_nat (length (strarea))).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. pose proof len_BSB. pose proof strarea_len. lia.
Qed.

Definition Z0 : sv := VL (wp 0%uint63).
Definition R0T : region := Region 0%uint63 (VL (wp 0%uint63)) false BGImage (imap_of []).

Definition R1NT : region := Region 9223372036848631295%uint63 (VL (wp 16%uint63)) true BGZero
  (imap_of [(0%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 4%uint63 (wp 0%uint63))]);
            (1%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))])]).

Definition R1FT : region := Region 9223372036848631295%uint63 (VL (wp 32%uint63)) true BGZero
  (imap_of [(0%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 2%uint63))]);
            (1%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))]);
            (2%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 10%uint63 (wp 0%uint63))]);
            (3%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))])]).
Definition R2T : region := Region 0%uint63 (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 2%uint63 0%uint63) (imap_of []).
Definition R3T : region := R3Tb (la_rseq LA).
Definition R5T : region := Region 0%uint63 (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 1%uint63 0%uint63) (imap_of []).
Definition R6T : region := Region 0%uint63 (VL (wp 16%uint63)) false (BGBlob 6%uint63 0%uint63) (imap_of []).
Definition R10T : region := Region 0%uint63 (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 3%uint63 0%uint63) (imap_of []).

Definition R12T : region := Region 0%uint63 (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 12%uint63 0%uint63) IMap.empty.

Lemma hiZ_R1 : hiZ E0 R1NT = 16. Proof. reflexivity. Qed.
Lemma loZ_R1 : loZ R1NT = - 6144513. Proof. reflexivity. Qed.
Lemma hiZ_R2 : hiZ E0 R2T = 8 * envcZ + 8.
Proof. unfold hiZ. change (rg_hi R2T) with (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63). rewrite den_SIZE8. apply Z_to_bv64_unsigned. lia. Qed.
Lemma hiZ_R3 : hiZ E0 R3T = Z.of_nat (auxv_size (la_rseq LA)).
Proof.
  unfold R3T, R3Tb, auxv_size, auxv_count.
  destruct (Bool.bool_dec (la_rseq LA) true) as [Hr|Hr]; [|apply Bool.not_true_is_false in Hr]; rewrite Hr; reflexivity.
Qed.
Lemma hiZ_R12 : hiZ E0 R12T = Z.of_nat (length (strarea)).
Proof. unfold hiZ. cbn [rg_hi R12T]. rewrite den_SIZE15. apply Z_to_bv64_unsigned. pose proof len_BSB. pose proof strarea_len. lia. Qed.
Lemma hiZ_R5 : hiZ E0 R5T = Z.of_nat (length a0) + 1.
Proof. unfold hiZ. change (rg_hi R5T) with (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63). rewrite den_SIZE9. apply Z_to_bv64_unsigned. pose proof a0_len. lia. Qed.
Lemma loZ_0 : forall r, rg_lo r = 0%uint63 -> loZ r = 0. Proof. intros r H. unfold loZ. rewrite H. reflexivity. Qed.

(* [mem0] is bound as a Local Notation at the head of this section now, with
   the rest of the [SI] interface. *)
Lemma ms0_mem : ms_mem ms0 = mem0. Proof. reflexivity. Qed.

Lemma rb_some : forall a b, mem0 (Z_to_bv 64 a) = Some b -> rb SEGS mem0 a = Some b.
Proof. intros a b H. unfold rb. rewrite H. reflexivity. Qed.
Lemma wb_some : forall a b, mem0 (Z_to_bv 64 a) = Some b -> wb SEGS mem0 a = true.
Proof. intros a b H. unfold wb, wview. rewrite H. reflexivity. Qed.

(* THE WINDOW BELOW [sp] IS NO LONGER EIGHT MEGABYTES WIDE, so these two say
   only what the block above [sp] gives.  At the released model [mem0] zero-
   filled [SP - stack_max_size, SP); at this revision the stack VMA is
   anchored at the TOP, [SI.WLO = Z.max (TOP - stack_max_size) (mbase + guard)]
   (727298f3 Run.v:1388-1391), and [SI.geom] forces [TOP > SP], so
   [WLO > SP - stack_max_size] for every input.  [R2]/[R3]/[R5]/[R6]/[R10]/[R12]
   all sit above [sp] and need nothing below it; [R1_ok] and [R1F_ok] do, and
   they are the sites this revision leaves red.  Each was checked, not
   assumed to follow the first. *)
Lemma stack_byte : forall a, SP <= a < SP + Z.of_nat (length (BSB)) ->
  exists b, mem0 (Z_to_bv 64 a) = Some b.
Proof.
  intros a Ha.
  destruct (nth_error (BSB) (Z.to_nat (a - SP))) as [b|] eqn:Hn.
  - exists b. replace a with (SP + Z.of_nat (Z.to_nat (a - SP))) by lia.
    apply (SI.mem0_block SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch). exact Hn.
  - exfalso. apply nth_error_None in Hn. lia.
Qed.

Lemma stack_valid : forall a, SP <= a < SP + Z.of_nat (length (BSB)) ->
  rb SEGS mem0 a <> None /\ wb SEGS mem0 a = true /\ find_segment SEGS a 1 = None.
Proof.
  intros a Ha. destruct (stack_byte a Ha) as [b Hb]. split; [|split].
  - rewrite (rb_some a b Hb). discriminate.
  - exact (wb_some a b Hb).
  - apply (find_segment_none SEGS a 1 SEGTOP segs_below_top); [|lia].
    pose proof segtop_low. pose proof Hlo. unfold SI.SP in *. lia.
Qed.

(* The stack VMA's floor is at least [6144513] bytes below [sp]: the depth
   the recorded [R1NT]/[R1FT] claim ([StoreOk.stack_window_depth]), from the
   launch's caps ([ALib.InitMem.stack_window_lo_valid]). *)
Lemma WLO_floor : WLO <= SP - 6144513.
Proof.
  pose proof (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.stack_window_lo_valid inp sp brk0 mbase draw Hvl Hlaunch) as H.
  unfold SI.WLO, SI.SP, stack_max_size in *. lia.
Qed.

Lemma stack_valid_lo : forall a, SP - 6144513 <= a < SP ->
  rb SEGS mem0 a <> None /\ wb SEGS mem0 a = true /\ find_segment SEGS a 1 = None.
Proof.
  intros a Ha. pose proof WLO_floor as HW. pose proof Hlo.
  assert (Hb : mem0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0))
    by (apply (SI.mem0_below SEGS PC PH sp mbase inp draw Hsp); lia).
  split; [|split].
  - rewrite (rb_some a _ Hb). discriminate.
  - exact (wb_some a _ Hb).
  - apply (find_segment_none SEGS a 1 SEGTOP segs_below_top); [|lia].
    pose proof segtop_low. unfold SI.SP in *. lia.
Qed.

Lemma slot_ok_word : forall base v w,
  word_at base w -> den E0 v = w ->
  slot_ok SEGS E0 mem0 base [Cell 0%uint63 8%uint63 v].
Proof.
  intros base v w Hw Hv. split; [exact (conj I I)|].
  constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v].
  change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (base + 0 + i) with (base + Z.of_nat (Z.to_nat i)) by lia.
  apply rb_some. rewrite (Hw (Z.to_nat i)) by lia. rewrite byte_of_le8 by lia. rewrite Z2Nat.id by lia. rewrite Hv. reflexivity.
Qed.

Definition R1L := Eval vm_compute in IMap.elements (rg_cells R1NT).
Lemma R1_elements : IMap.elements (rg_cells R1NT) = R1L. Proof. vm_compute. reflexivity. Qed.
Lemma R1_find : forall g gr, IMap.find g (rg_cells R1NT) = Some gr ->
  (g = 0%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 4%uint63 (wp 0%uint63))]) \/
  (g = 1%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))]).
Proof.
  intros g gr H. apply (find_in_elements _ g gr (rg_cells R1NT) (imap_of_bst _ _)) in H. rewrite R1_elements in H. unfold R1L in H.
  destruct H as [H|[H|[]]]; [left|right]; injection H as <- <-; split; reflexivity.
Qed.

(* AT_EGID's value cell ([Auxv.aux_val 22]) is AT_GID's background word: the
   vector's word 43, eight bytes of [eg0 3] from its offset. *)
Lemma den_gid_bg : den E0 (VBg false 3%uint63 (W64 false 344%uint63) 8%uint63) = nth 43 auxws (Z_to_bv 64 0).
Proof.
  cbn [den]. change (eg E0 3%uint63) with (fun o => nth (Z.to_nat o) (flat_map word_le8 auxws) (Z_to_bv 8 0)).
  change (w2Zs (W64 false 344%uint63)) with (8 * Z.of_nat 43).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat. change (to_Z 8%uint63) with 8.
  assert (H43 : forall b : bool, (43 < 2 * auxv_count b)%nat) by (intros [|]; apply Nat.ltb_lt; reflexivity).
  rewrite bg_word_flat by (rewrite SI.length_auxws; apply H43).
  apply bytes_val_word_le8.
Qed.

(* Every cell of [R3T] is one word of the vector, [nth j auxws], at its own
   index [j]: checked by computation at each flag value. *)
Lemma R3_cell : forall g gr, IMap.find g (rg_cells R3T) = Some gr ->
  exists (j : nat) (v : sv), keyZ g = Z.of_nat j /\ gr = cell1 v /\ (j < length auxws)%nat /\
    den E0 v = nth j auxws (Z_to_bv 64 0).
Proof.
  intros g gr H. apply (find_in_elements _ g gr (rg_cells R3T) (imap_of_bst _ _)) in H.
  rewrite SI.length_auxws. unfold auxws, auxv_entries. rewrite HphA, HphE, HphN. unfold R3T in H.
  (* one cell: name its index [j] as a nat literal, then compute *)
  Ltac one3 := lazymatch goal with
    | |- exists (j : nat) (v : sv), keyZ ?k = _ /\ _ =>
        let j := eval vm_compute in (Z.to_nat (keyZ k)) in
        exists j; eexists; split; [vm_compute; reflexivity|]; split; [reflexivity|];
        split; [apply Nat.ltb_lt; vm_compute; reflexivity|];
        cbn [nth flat_map app fst snd];
        first [reflexivity | (rewrite den_VP0; reflexivity) | (rewrite den_gid_bg; reflexivity)]
    end.
  Ltac tac3 := lazymatch goal with
    | H : In _ (_ :: _) |- _ => destruct H as [H|H]; [injection H as <- <-; one3 | tac3]
    | H : In _ [] |- _ => destruct H
    end.
  destruct (Bool.bool_dec (la_rseq LA) true) as [Hr|Hr]; [|apply Bool.not_true_is_false in Hr]; rewrite Hr in H |- *.
  - rewrite R3_elements_true in H. unfold R3L_true in H. tac3.
  - rewrite R3_elements_false in H. unfold R3L_false in H. tac3.
Qed.

(* A byte of the vector, at its offset from the vector's base. *)
Lemma auxv_byte : forall o, 0 <= o < 8 * Z.of_nat (length auxws) ->
  rb SEGS mem0 (SP + auxv_off + o) = Some (nth (Z.to_nat o) (flat_map word_le8 auxws) (Z_to_bv 8 0)).
Proof.
  intros o Ho. rewrite nth_flat_le8 by lia.
  set (i := Z.to_nat o).
  assert (Hi : o = 8 * Z.of_nat (i / 8) + Z.of_nat (i mod 8)).
  { unfold i. pose proof (Nat.div_mod (Z.to_nat o) 8 ltac:(lia)) as D. lia. }
  assert (Hj : (i / 8 < length auxws)%nat) by (apply Nat.div_lt_upper_bound; lia).
  assert (W : mem0 (Z_to_bv 64 (SP + auxv_off + 8 * Z.of_nat (i / 8) + Z.of_nat (i mod 8)))
              = Some (nth (i mod 8) (word_le8 (nth (i / 8) auxws (Z_to_bv 64 0))) (Z_to_bv 8 0))).
  { pose proof (SI.auxv_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch) as AW.
    unfold SI.word_at in AW. apply AW; [exact Hj | apply Nat.mod_upper_bound; lia]. }
  apply rb_some. rewrite Hi. replace (SP + auxv_off + (8 * Z.of_nat (i / 8) + Z.of_nat (i mod 8)))
    with (SP + auxv_off + 8 * Z.of_nat (i / 8) + Z.of_nat (i mod 8)) by lia. exact W.
Qed.

Lemma covered_not_uncovered : forall r o g v,
  keyZ g = o / 8 -> 0 <= o mod 8 < 8 ->
  IMap.find g (rg_cells r) = Some (Gran false [Cell 0%uint63 8%uint63 v]) -> ~ uncovered r o.
Proof.
  intros r o g v Hg Ho Hf Hu. destruct (Hu g _ Hg Hf) as [_ Hc].
  inversion Hc as [|c l Hn _]; subst. apply Hn. unfold covers. cbn [c_idx c_w].
  change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8. lia.
Qed.

Lemma R0_ok : region_ok SEGS [] E0 mem0 0%uint63 R0T.
Proof.
  split.
  - exact I.
  - intros H; discriminate H.
  - intros H; discriminate H.
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o _ Ho _. destruct (Ho eq_refl) as (Hr & [bs Hbs] & _).
    cbn [bg_byte rg_bg R0T]. unfold img_byte.
    pose proof (memory_read_find o bs ltac:(unfold two63 in Hr; lia) Hbs) as Hb.
    destruct (rom_of SEGS (Z_to_bv 64 o)) as [b|] eqn:Hrom; [|exact I].
    unfold rb. rewrite ev0_0. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l.
    assert (Hopos : 0 <= o) by (unfold two63 in Hr; lia).
    rewrite (SI.mem0_none_low SEGS PC PH sp mbase inp draw o);
      [exact Hrom
      | pose proof WLO_lo; pose proof segtop_low; lia
      | pose proof Hlo; pose proof segtop_low; unfold SI.SP in *; lia].
Qed.

Lemma R1_ok : region_ok SEGS [] E0 mem0 1%uint63 R1NT.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  split.
  - apply imap_of_bst.
  - intros _. rewrite ev0_1, loZ_R1, hiZ_R1. fold SP. unfold two64. lia.
  - intros _ a. rewrite ev0_1, loZ_R1, hiZ_R1. fold SP. intros Ha.
    destruct (Z.lt_ge_cases a SP) as [Hlt|Hge];
      [destruct (stack_valid_lo a ltac:(lia)) as (H1 & H2 & H3) | destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3)];
      cbn [rg_w R1NT]; auto.
  - intros g gr Hg. rewrite ev0_1. fold SP.
    destruct (R1_find g gr Hg) as [[-> ->]|[-> ->]]; cbn [g_cells].
    + change (keyZ 0%uint63) with 0. replace (SP + 8 * 0) with SP by lia.
      apply (slot_ok_word SP _ (len_word argv)); [apply (SI.argc_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch) | rewrite den_VP0; apply ev0_4].
    + change (keyZ 1%uint63) with 1. replace (SP + 8 * 1) with (SP + 8 + 8 * Z.of_nat 0) by lia.
      apply (slot_ok_word _ _ (nth 0 (argv_ptrs) (Z_to_bv 64 0))).
      * apply (SI.argv_ptr_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch). pose proof Hargc. unfold SI.argcZ in *. lia.
      * rewrite den_VP0. rewrite (SI.argv_ptr0 inp draw a0 (tl argv) argv_eq). reflexivity.
  - intros g gr c i Hg Hc Hi. split; [|intros H; discriminate H]. intros _. rewrite loZ_R1, hiZ_R1.
    destruct (R1_find g gr Hg) as [[-> ->]|[-> ->]]; cbn [g_cells] in Hc; destruct Hc as [<-|[]];
      cbn [c_idx c_w] in *; change (to_Z 0%uint63) with 0 in *; change (to_Z 8%uint63) with 8 in *;
      [change (keyZ 0%uint63) with 0 | change (keyZ 1%uint63) with 1]; lia.
  - intros o Ho _ Hu. specialize (Ho eq_refl). rewrite loZ_R1, hiZ_R1 in Ho. cbn [bg_byte rg_bg R1NT]. rewrite ev0_1. fold SP.
    destruct (Z.lt_ge_cases o 0) as [Hneg|Hpos].
    + pose proof WLO_floor. apply rb_some. apply (SI.mem0_below SEGS PC PH sp mbase inp draw Hsp). lia.
    + exfalso. destruct (Z.lt_ge_cases o 8) as [H8|H8].
      * apply (covered_not_uncovered R1NT o 0%uint63 (VP 4%uint63 (wp 0%uint63))); [change (keyZ 0%uint63) with 0; rewrite Z.div_small; lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1NT o 1%uint63 (VP 5%uint63 (wp 0%uint63))); [change (keyZ 1%uint63) with 1; apply (Z.div_unique_pos o 8 1 (o - 8)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
Qed.

Lemma R2_ok : region_ok SEGS [] E0 mem0 2%uint63 R2T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  split.
  - exact I.
  - intros _. rewrite ev0_2, (loZ_0 R2T eq_refl), hiZ_R2. unfold SI.envp_off, two64. lia.
  - intros _ a. rewrite ev0_2, (loZ_0 R2T eq_refl), hiZ_R2. unfold SI.envp_off. intros Ha.
    destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3). cbn [rg_w R2T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R2T eq_refl), hiZ_R2 in Ho.
    cbn [bg_byte rg_bg R2T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_2.
    pose proof (SI.length_envp_img inp draw) as Hlen.
    replace (SP + envp_off + o) with (SP + envp_off + Z.of_nat (Z.to_nat o)) by lia.
    apply rb_some. rewrite (SI.envp_img_byte SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch (Z.to_nat o)) by lia. reflexivity.
Qed.

Lemma R3_ok : region_ok SEGS [] E0 mem0 3%uint63 R3T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  assert (HSZ : Z.of_nat (auxv_size (la_rseq LA)) = 8 * Z.of_nat (length auxws))
    by (rewrite SI.length_auxws; unfold auxv_size; lia).
  split.
  - apply imap_of_bst.
  - intros _. rewrite ev0_3, (loZ_0 R3T eq_refl), hiZ_R3. unfold SI.auxv_off, two64. lia.
  - intros _ a. rewrite ev0_3, (loZ_0 R3T eq_refl), hiZ_R3. unfold SI.auxv_off. intros Ha.
    destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3). cbn [rg_w R3T R3Tb]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. rewrite ev0_3. destruct (R3_cell g gr Hg) as (j & v & Hk & -> & Hj & Hv). cbn [g_cells cell1]. rewrite Hk.
    apply (slot_ok_word _ _ (nth j (auxws) (Z_to_bv 64 0))); [|exact Hv].
    apply (SI.auxv_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch). exact Hj.
  - intros g gr c i Hg Hc Hi. split; [|intros H; discriminate H]. intros _. rewrite (loZ_0 R3T eq_refl), hiZ_R3.
    destruct (R3_cell g gr Hg) as (j & v & Hk & -> & Hj & _). cbn [g_cells cell1] in Hc. destruct Hc as [<-|[]].
    cbn [c_idx c_w] in *. change (to_Z 0%uint63) with 0 in *. change (to_Z 8%uint63) with 8 in *. rewrite Hk. lia.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R3T eq_refl), hiZ_R3 in Ho.
    cbn [bg_byte rg_bg R3T R3Tb eg E0 eg0]. change (to_Z 3%uint63) with 3. cbv iota. rewrite ev0_3.
    apply auxv_byte. lia.
Qed.

Lemma R5_ok : region_ok SEGS [] E0 mem0 5%uint63 R5T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof total_ge_a0 as HA.
  split.
  - exact I.
  - intros _. rewrite ev0_5, (loZ_0 R5T eq_refl), hiZ_R5. unfold two64. lia.
  - intros _ a. rewrite ev0_5, (loZ_0 R5T eq_refl), hiZ_R5. intros Ha.
    destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3). cbn [rg_w R5T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R5T eq_refl), hiZ_R5 in Ho.
    cbn [bg_byte rg_bg R5T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_5.
    replace (SP + Z.of_nat (sstruct) + o)
      with (bv_unsigned str_base + Z.of_nat (Z.to_nat o)) by (rewrite str_baseZ; lia).
    apply rb_some. rewrite (SI.argv0_byte SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch a0 (tl argv) (Z.to_nat o) argv_eq) by lia.
    reflexivity.
Qed.

Lemma R12_ok : region_ok SEGS [] E0 mem0 12%uint63 R12T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof strarea_len as HA.
  split.
  - exact I.
  - intros _. rewrite ev0_12, (loZ_0 R12T eq_refl), hiZ_R12. unfold two64. lia.
  - intros _ a. rewrite ev0_12, (loZ_0 R12T eq_refl), hiZ_R12. intros Ha.
    destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3). cbn [rg_w R12T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R12T eq_refl), hiZ_R12 in Ho.
    cbn [bg_byte rg_bg R12T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_12.
    replace (SP + Z.of_nat (sstruct) + o)
      with (bv_unsigned str_base + Z.of_nat (Z.to_nat o)) by (rewrite str_baseZ; lia).
    apply rb_some. rewrite (SI.strarea_byte SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch (Z.to_nat o)) by lia.
    reflexivity.
Qed.

Lemma w16 : bv_unsigned (wbv (wp 16%uint63)) = 16. Proof. reflexivity. Qed.
Lemma w0 : bv_unsigned (wbv (wp 0%uint63)) = 0. Proof. reflexivity. Qed.
Lemma sh3 : bv_unsigned (bv_and (wbv (wp 3%uint63)) (Z_to_bv 64 63)) = 3. Proof. reflexivity. Qed.

Lemma ext_Z_sx32_small : forall z, 0 <= z < 2 ^ 31 -> ext_Z true 0 4 z = z.
Proof.
  intros z Hz. unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 4 - 1)) with (2 ^ 31).
  rewrite Z.div_1_r, (Z.mod_small z) by lia.
  replace (2 ^ 31 <=? z) with false by (symmetry; apply Z.leb_gt; lia). unfold two64. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma fact_envp : den E0 (VP 2%uint63 (wp 0%uint63)) =
  den E0 (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VExt true 0%uint63 4%uint63 (VP 4%uint63 (wp 0%uint63))) (VL (wp 3%uint63)))).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  rewrite den_VP0. cbn [den alu64 alu]. rewrite ev0_1, ev0_4. unfold ext_word.
  apply bv_eq. rewrite ev0_2. rewrite !bv_add_unsigned, bv_shiftl_unsigned, sh3, w16, w0, !Z_to_bv_unsigned.
  rewrite (SI.len_word_argv inp Hva). change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4. rewrite Z.add_0_r.
  rewrite (bv_wrap_small 64 (argcZ)) by (unfold bv_modulus; lia).
  rewrite ext_Z_sx32_small by lia.
  rewrite (bv_wrap_small 64 (argcZ)) by (unfold bv_modulus; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap, bv_modulus, envp_off. change (2 ^ Z.of_N 64) with (2 ^ 64).
  fold (SI.SP sp). rewrite (Z.mod_small (SP + 16)), (Z.mod_small (argcZ * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fact_envp' : den E0 (VP 2%uint63 (wp 0%uint63)) =
  den E0 (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VP 4%uint63 (wp 0%uint63)) (VL (wp 3%uint63)))).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  change (den E0 (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VP 4%uint63 (wp 0%uint63)) (VL (wp 3%uint63)))))
    with (bv_add (den E0 (VP 1%uint63 (wp 16%uint63))) (bv_shiftl (den E0 (VP 4%uint63 (wp 0%uint63))) (bv_and (wbv (wp 3%uint63)) (Z_to_bv 64 63)))).
  rewrite !den_VP0. cbn [den]. rewrite ev0_1, ev0_4.
  apply bv_eq. rewrite ev0_2. rewrite !bv_add_unsigned, bv_shiftl_unsigned, sh3, w16.
  rewrite (SI.len_word_argv inp Hva).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap, bv_modulus, envp_off. change (2 ^ Z.of_N 64) with (2 ^ 64).
  fold (SI.SP sp). rewrite (Z.mod_small (SP + 16)), (Z.mod_small (argcZ * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fact_auxv : den E0 (VP 3%uint63 (wp 0%uint63)) =
  den E0 (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  change (den E0 (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)))
    with (bv_add (den E0 (VP 2%uint63 (wp 0%uint63))) (den E0 (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))).
  rewrite !den_VP0, den_SIZE8. apply bv_eq. rewrite bv_add_unsigned, ev0_2, ev0_3, Z_to_bv64_unsigned by lia.
  unfold SI.envp_off, auxv_off. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

Definition R1FL := Eval vm_compute in IMap.elements (rg_cells R1FT).
Lemma R1F_elements : IMap.elements (rg_cells R1FT) = R1FL. Proof. vm_compute. reflexivity. Qed.
Lemma R1F_find : forall g gr, IMap.find g (rg_cells R1FT) = Some gr ->
  (g = 0%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VL (wp 2%uint63))]) \/
  (g = 1%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))]) \/
  (g = 2%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 10%uint63 (wp 0%uint63))]) \/
  (g = 3%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))]).
Proof.
  intros g gr H. apply (find_in_elements _ g gr (rg_cells R1FT) (imap_of_bst _ _)) in H. rewrite R1F_elements in H. unfold R1FL in H.
  destruct H as [H|[H|[H|[H|[]]]]]; [left|right;left|right;right;left|right;right;right]; injection H as <- <-; split; reflexivity.
Qed.
Lemma hiZ_R1F : hiZ E0 R1FT = 32. Proof. reflexivity. Qed.
Lemma loZ_R1F : loZ R1FT = - 6144513. Proof. reflexivity. Qed.
Lemma ev0_10 : bv_unsigned (ev E0 10%uint63) = SP + Z.of_nat (sstruct) + Z.of_nat (length a0) + 1.
Proof.
  change (ev E0 10%uint63) with (Z_to_bv 64 (SP + Z.of_nat (sstruct) + Z.of_nat (length a0) + 1)).
  apply Z_to_bv64_unsigned. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0. lia.
Qed.

Section Family2.
Hypothesis Hargc2 : length argv = 2%nat.

Lemma argv_eq2 : argv = [a0; a1].
Proof. unfold a0, a1. exact (two_elems _ [] argv Hargc2). Qed.
Lemma a1_len : Z.of_nat (length a1) <= 131071.
Proof. pose proof Hva as (_ & _ & Hl & _). rewrite argv_eq2 in Hl. inversion Hl as [|? ? ? Hl']. inversion Hl'. assumption. Qed.
Lemma a1_nonul : ~ In (Z_to_bv 8 0) a1.
Proof. pose proof Hva as (_ & _ & _ & Hn & _). rewrite argv_eq2 in Hn. inversion Hn as [|? ? ? Hn']. inversion Hn'. assumption. Qed.
Lemma total2 : Z.of_nat (total_nat argv) = Z.of_nat (length a0) + 1 + Z.of_nat (length a1) + 1.
Proof. rewrite argv_eq2. cbn [total_nat]. lia. Qed.

(* [SI.argv1_byte] went with the released model's layout.  The same bytes are
   still named, one level up: [SI.strarea] is the whole string area from
   [str_base], and for a two-element argv its second string starts
   [length a0 + 1] into it.  Derived from [SI.strarea_byte] rather than from a
   reinstated export, so [StackInit.v] keeps saying what the model says. *)
Lemma argv1_byte : forall (i : nat), (i <= length a1)%nat ->
  mem0 (Z_to_bv 64 (bv_unsigned str_base + Z.of_nat (length a0) + 1 + Z.of_nat i))
  = Some (nth i (a1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
  intros i Hi.
  assert (Hlt : (length a0 + 1 + i < length (strarea))%nat).
  { pose proof strarea_len as HSA. pose proof Hlsbeq as HL. pose proof total2 as HT. lia. }
  pose proof (SI.strarea_byte SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch
                (length a0 + 1 + i)%nat Hlt) as Hb.
  replace (bv_unsigned str_base + Z.of_nat (length a0) + 1 + Z.of_nat i)
    with (bv_unsigned str_base + Z.of_nat (length a0 + 1 + i)) by lia.
  rewrite Hb. f_equal.
  unfold SI.strarea, flatten_strings. rewrite argv_eq2. cbn [flat_map].
  apply nth_second_string. exact Hi.
Qed.

Lemma den_SIZE10 : den E0 (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (Z.of_nat (length a1) + 1).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. pose proof a1_len. lia.
Qed.
Lemma hiZ_R10 : hiZ E0 R10T = Z.of_nat (length a1) + 1.
Proof. unfold hiZ. change (rg_hi R10T) with (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63). rewrite den_SIZE10. apply Z_to_bv64_unsigned. pose proof a1_len. lia. Qed.

Lemma R1F_ok : region_ok SEGS [] E0 mem0 1%uint63 R1FT.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof total2 as HT2.
  assert (Hac2 : argcZ = 2) by (unfold SI.argcZ, SI.nargc; rewrite Hargc2; reflexivity).
  split.
  - apply imap_of_bst.
  - intros _. rewrite ev0_1, loZ_R1F, hiZ_R1F. fold SP. unfold two64. lia.
  - intros _ a. rewrite ev0_1, loZ_R1F, hiZ_R1F. fold SP. intros Ha.
    destruct (Z.lt_ge_cases a SP) as [Hlt|Hge];
      [destruct (stack_valid_lo a ltac:(lia)) as (H1 & H2 & H3) | destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3)];
      cbn [rg_w R1FT]; auto.
  - intros g gr Hg. rewrite ev0_1. fold SP.
    destruct (R1F_find g gr Hg) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [g_cells].
    + change (keyZ 0%uint63) with 0. replace (SP + 8 * 0) with SP by lia.
      apply (slot_ok_word SP _ (len_word argv)); [apply (SI.argc_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch) |].
      apply bv_eq. rewrite (SI.len_word_argv inp Hva), Hac2. reflexivity.
    + change (keyZ 1%uint63) with 1. replace (SP + 8 * 1) with (SP + 8 + 8 * Z.of_nat 0) by lia.
      apply (slot_ok_word _ _ (nth 0 (argv_ptrs) (Z_to_bv 64 0))).
      * apply (SI.argv_ptr_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch). unfold nargc. rewrite Hargc2. lia.
      * rewrite den_VP0. rewrite (SI.argv_ptr0 inp draw a0 (tl argv) argv_eq). reflexivity.
    + change (keyZ 2%uint63) with 2. replace (SP + 8 * 2) with (SP + 8 + 8 * Z.of_nat 1) by lia.
      apply (slot_ok_word _ _ (nth 1 (argv_ptrs) (Z_to_bv 64 0))).
      * apply (SI.argv_ptr_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch). unfold nargc. rewrite Hargc2. lia.
      * rewrite den_VP0. apply bv_eq. rewrite ev0_10, (SI.argv_ptr1_val sp brk0 mbase inp draw Hsp Hlaunch a0 a1 [] argv_eq2), str_baseZ. reflexivity.
    + change (keyZ 3%uint63) with 3. replace (SP + 8 * 3) with (SP + 8 + 8 * argcZ) by lia.
      apply (slot_ok_word _ _ (Z_to_bv 64 0)); [apply (SI.argv_null_word SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch) | reflexivity].
  - intros g gr c i Hg Hc Hi. split; [|intros H; discriminate H]. intros _. rewrite loZ_R1F, hiZ_R1F.
    destruct (R1F_find g gr Hg) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [g_cells] in Hc; destruct Hc as [<-|[]];
      cbn [c_idx c_w] in *; change (to_Z 0%uint63) with 0 in *; change (to_Z 8%uint63) with 8 in *;
      [change (keyZ 0%uint63) with 0 | change (keyZ 1%uint63) with 1 | change (keyZ 2%uint63) with 2 | change (keyZ 3%uint63) with 3]; lia.
  - intros o Ho _ Hu. specialize (Ho eq_refl). rewrite loZ_R1F, hiZ_R1F in Ho. cbn [bg_byte rg_bg R1FT]. rewrite ev0_1. fold SP.
    destruct (Z.lt_ge_cases o 0) as [Hneg|Hpos].
    + pose proof WLO_floor. apply rb_some. apply (SI.mem0_below SEGS PC PH sp mbase inp draw Hsp). lia.
    + exfalso. destruct (Z.lt_ge_cases o 8) as [H8|H8]; [|destruct (Z.lt_ge_cases o 16) as [H16|H16]; [|destruct (Z.lt_ge_cases o 24) as [H24|H24]]].
      * apply (covered_not_uncovered R1FT o 0%uint63 (VL (wp 2%uint63))); [change (keyZ 0%uint63) with 0; rewrite Z.div_small; lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1FT o 1%uint63 (VP 5%uint63 (wp 0%uint63))); [change (keyZ 1%uint63) with 1; apply (Z.div_unique_pos o 8 1 (o - 8)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1FT o 2%uint63 (VP 10%uint63 (wp 0%uint63))); [change (keyZ 2%uint63) with 2; apply (Z.div_unique_pos o 8 2 (o - 16)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1FT o 3%uint63 (VL (wp 0%uint63))); [change (keyZ 3%uint63) with 3; apply (Z.div_unique_pos o 8 3 (o - 24)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
Qed.

Lemma R10_ok : region_ok SEGS [] E0 mem0 10%uint63 R10T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof total2 as HT2.
  split.
  - exact I.
  - intros _. rewrite ev0_10, (loZ_0 R10T eq_refl), hiZ_R10. unfold two64. lia.
  - intros _ a. rewrite ev0_10, (loZ_0 R10T eq_refl), hiZ_R10. intros Ha.
    destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3). cbn [rg_w R10T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R10T eq_refl), hiZ_R10 in Ho.
    cbn [bg_byte rg_bg R10T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_10.
    replace (SP + Z.of_nat (sstruct) + Z.of_nat (length a0) + 1 + o)
      with (bv_unsigned str_base + Z.of_nat (length a0) + 1 + Z.of_nat (Z.to_nat o))
      by (rewrite str_baseZ; lia).
    apply rb_some. rewrite (argv1_byte (Z.to_nat o)) by lia.
    reflexivity.
Qed.

Theorem PB1_E0 : PB_ARG1 (eb E0).
Proof.
  exists a1. cbn [eb E0]. unfold eb0.
  change (to_Z 3%uint63) with 3. change (to_Z 10%uint63) with 10. cbv iota.
  split; [reflexivity|]. split; [apply a1_nonul|]. split; [apply a1_len| reflexivity].
Qed.
End Family2.

Lemma hiZ_R6 : hiZ E0 R6T = 16. Proof. reflexivity. Qed.
Lemma R6_ok : region_ok SEGS [] E0 mem0 6%uint63 R6T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST.
  split.
  - exact I.
  - intros _. rewrite ev0_6, (loZ_0 R6T eq_refl), hiZ_R6. unfold two64. lia.
  - intros _ a. rewrite ev0_6, (loZ_0 R6T eq_refl), hiZ_R6. intros Ha.
    destruct (stack_valid a ltac:(lia)) as (H1 & H2 & H3). cbn [rg_w R6T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R6T eq_refl), hiZ_R6 in Ho.
    cbn [bg_byte rg_bg R6T eb E0 eb0]. change (to_Z 6%uint63) with 6. change (to_Z 0%uint63) with 0. cbv iota. rewrite Z.sub_0_r, ev0_6.
    (* [SI.random_byte] is stated over [SP + (Z.of_nat HEAD - 16)], a Z
       subtraction, where [rndoff] is the nat one; [rewrite] is syntactic, so
       the two have to be brought together here. *)
    replace (SP + Z.of_nat (rndoff) + o)
      with (SP + (Z.of_nat HEAD - 16) + Z.of_nat (Z.to_nat o))
      by (rewrite rndoff_val; lia).
    apply rb_some. rewrite (SI.random_byte SEGS PC PH sp brk0 mbase inp draw Hsp Hlaunch (Z.to_nat o)) by lia. reflexivity.
Qed.

(* [pad_spec] is gone with [SI.raw_len].  It existed only to give [f_sp_range]
   the slack between [sp] and the top of the window, and this revision states
   that directly: [SI.BSB_top] with [len_BSB] puts [SP + sstruct + LSB + 8]
   under 2^47, and the entry block alone is at least 472 bytes. *)
Lemma HEAD_lo : 472 <= Z.of_nat HEAD.
Proof. rewrite Hheadeq. pose proof auxv_size_rng. pose proof gap_rng. lia. Qed.

Lemma wp_ok : forall i, w2Z (wp i) = to_Z i.
Proof. intros i. unfold w2Z. cbn [wt wl wp]. lia. Qed.

Lemma f_sp_range : fact_holds E0 (FRange 1%uint63 (wp 140735340871680%uint63) (wp 140737488355112%uint63)).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof total_ge_a0 as HA.
  cbn [fact_holds]. rewrite !wp_ok, ev0_1. change (to_Z 140735340871680%uint63) with 140735340871680.
  change (to_Z 140737488355112%uint63) with 140737488355112. fold (SI.SP sp).
  pose proof HEAD_lo. rewrite Nat2Z.inj_add in HS, HL. lia.
Qed.
Lemma f_sp_align : fact_holds E0 (FAlign 1%uint63 4%uint63).
Proof. cbn [fact_holds]. rewrite ev0_1. change (2 ^ to_Z 4%uint63) with 16. pose proof Hsp as (_ & _ & Hal). exact Hal. Qed.
Lemma f_argc_range : fact_holds E0 (FRange 4%uint63 (wp 1%uint63) (wp 1024%uint63)).
Proof. cbn [fact_holds]. rewrite !wp_ok, ev0_4, (SI.len_word_argv inp Hva). change (to_Z 1%uint63) with 1. change (to_Z 1024%uint63) with 1024. lia. Qed.

Lemma window_fact : forall k, 140735340871680 <= bv_unsigned (ev E0 k) <= 140737488355328 ->
  fact_holds E0 (FRange k (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. intros k H. cbn [fact_holds]. rewrite !wp_ok. change (to_Z 140735340871680%uint63) with 140735340871680. change (to_Z 140737488355328%uint63) with 140737488355328. exact H. Qed.
Lemma f_win2 : fact_holds E0 (FRange 2%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. rewrite ev0_2. unfold SI.envp_off. lia. Qed.
Lemma f_win3 : fact_holds E0 (FRange 3%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. rewrite ev0_3. unfold SI.auxv_off. lia. Qed.
Lemma f_win5 : fact_holds E0 (FRange 5%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. rewrite ev0_5. lia. Qed.
Lemma f_win6 : fact_holds E0 (FRange 6%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof rndoff_le. rewrite ev0_6. lia. Qed.
Lemma f_win10 : fact_holds E0 (FRange 10%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0. rewrite ev0_10. lia. Qed.
Lemma f_hwcap : fact_holds E0 (FRange 7%uint63 (wp 4397%uint63) (wp 2101549%uint63)).
Proof.
  cbn [fact_holds]. rewrite !wp_ok, ev0_7. change (to_Z 4397%uint63) with 4397. change (to_Z 2101549%uint63) with 2101549.
  pose proof Hhw as [-> | ->]; unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite Z_to_bv64_unsigned; lia.
Qed.
Lemma f_envp : fact_holds E0 (FEq (VP 2%uint63 (wp 0%uint63))
  (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VExt true 0%uint63 4%uint63 (VP 4%uint63 (wp 0%uint63))) (VL (wp 3%uint63))))).
Proof. exact fact_envp. Qed.
Lemma f_envp' : fact_holds E0 (FEq (VP 2%uint63 (wp 0%uint63))
  (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VP 4%uint63 (wp 0%uint63)) (VL (wp 3%uint63))))).
Proof. exact fact_envp'. Qed.
Lemma f_auxv : fact_holds E0 (FEq (VP 3%uint63 (wp 0%uint63)) (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))).
Proof. exact fact_auxv. Qed.
Lemma f_size8_lo : fact_holds E0 (FULt (VL (wp 7%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof. cbn [fact_holds]. rewrite den_SIZE8, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 7%uint63)))) with 7. lia. Qed.
Lemma f_size8_hi : fact_holds E0 (FULe (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) (VL (wp 2056%uint63))).
Proof. cbn [fact_holds]. rewrite den_SIZE8, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 2056%uint63)))) with 2056. lia. Qed.
Lemma f_size9_lo : fact_holds E0 (FULe (VL (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof. pose proof a0_len. cbn [fact_holds]. rewrite den_SIZE9, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 1%uint63)))) with 1. lia. Qed.
Lemma f_size9_hi : fact_holds E0 (FULe (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VL (wp 131072%uint63))).
Proof. pose proof a0_len. cbn [fact_holds]. rewrite den_SIZE9, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 131072%uint63)))) with 131072. lia. Qed.
Lemma f_rnd_align : fact_holds E0 (FAlign 6%uint63 3%uint63).
Proof.
  cbn [fact_holds]. change (2 ^ to_Z 3%uint63) with 8. change (ev E0 6%uint63) with (ARND).
  exact ARND_aligned.
Qed.

Lemma f_sp_le_auxv : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 3%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_3. fold (SI.SP sp). pose proof Hargc. pose proof Henvc. unfold SI.auxv_off. lia.
Qed.
Lemma f_sp_le_rnd8 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 6%uint63 (wp 8%uint63))).
Proof.
  cbn [fact_holds]. rewrite den_VP0, ev0_1. cbn [den]. rewrite bv_add_unsigned, ev0_6.
  change (bv_unsigned (wbv (wp 8%uint63))) with 8. fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top.
  pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  pose proof rndoff_le. rewrite bv_wrap_small by (unfold bv_modulus in *; lia). lia.
Qed.
Lemma f_sp_le_rnd : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 6%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_6. fold (SI.SP sp). lia.
Qed.
Lemma f_sp_le_a0 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_5. fold (SI.SP sp). lia.
Qed.

Lemma f_a0_end : fact_holds E0 (FULe (VAlu ALU_ADD (VP 5%uint63 (wp 0%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                                  (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0. pose proof Htop as HT. pose proof a0_len.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_5, den_SIZE9, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_argc_ne2 : length argv <> 2%nat ->
  fact_holds E0 (FNe (VExt true 0%uint63 4%uint63 (VP 4%uint63 (wp 0%uint63))) (VL (wp 2%uint63))).
Proof.
  intros Hn. cbn [fact_holds]. intros X. apply (f_equal bv_unsigned) in X. revert X.
  cbn [den]. rewrite ev0_4. unfold ext_word. rewrite bv_add_unsigned, (SI.len_word_argv inp Hva), w0, Z.add_0_r.
  change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4.
  rewrite (bv_wrap_small 64 (argcZ)) by (unfold bv_modulus; lia). rewrite ext_Z_sx32_small by lia.
  rewrite !Z_to_bv64_unsigned by lia. change (bv_unsigned (wbv (wp 2%uint63))) with 2. unfold SI.argcZ, SI.nargc. lia.
Qed.
Lemma f_argc_ne2' : length argv <> 2%nat -> fact_holds E0 (FNe (VP 4%uint63 (wp 0%uint63)) (VL (wp 2%uint63))).
Proof.
  intros Hn. cbn [fact_holds]. intros X. apply (f_equal bv_unsigned) in X. revert X.
  rewrite den_VP0, ev0_4, (SI.len_word_argv inp Hva). change (bv_unsigned (den E0 (VL (wp 2%uint63)))) with 2. unfold SI.argcZ, SI.nargc. lia.
Qed.

Lemma f_win12 : fact_holds E0 (FRange 12%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. rewrite ev0_12. lia. Qed.
Lemma f_12_le_5 : fact_holds E0 (FULe (VP 12%uint63 (wp 0%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof. cbn [fact_holds]. rewrite !den_VP0, ev0_12, ev0_5. lia. Qed.
Lemma f_sp_le_12 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 12%uint63 (wp 0%uint63))).
Proof. cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_12. fold (SI.SP sp). lia. Qed.
Lemma f_end5_12 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 5%uint63 (wp 0%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                                   (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0. pose proof Htop as HT. pose proof a0_len. pose proof strarea_len.
  cbn [fact_holds]. change (den E0 (VAlu ALU_ADD ?a ?b)) with (bv_add (den E0 a) (den E0 b)) at 1.
  change (den E0 (VAlu ALU_ADD (VP 12%uint63 ?o) ?b)) with (bv_add (den E0 (VP 12%uint63 o)) (den E0 b)).
  rewrite !bv_add_unsigned, !den_VP0, ev0_5, ev0_12, den_SIZE9, den_SIZE15, !Z_to_bv64_unsigned by lia.
  rewrite !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_end12 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))
                                 (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Htop as HT. pose proof strarea_len.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_12, den_SIZE15, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

(* The string area ends at the stack's top, which the launch puts on a page
   boundary ([Run.valid_stack_top_va]), so its END is 8-aligned; its start is
   not (the strings' total length is the run's), which is why the released
   model's [FAlign 12 3] is gone. *)
Lemma f_str_end : fact_holds E0 Regen.STR_END.
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Htop as HT. pose proof strarea_len.
  pose proof Hlaunch as Hok. cbn [entry_launch_ok_va] in Hok. destruct Hok as ((Hpg & _ & _) & _ & _).
  unfold Regen.STR_END. cbn [fact_holds].
  change (den E0 (VAlu ALU_AND ?a ?b)) with (bv_and (den E0 a) (den E0 b)).
  change (den E0 (VAlu ALU_ADD ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  apply bv_eq. rewrite bv_and_unsigned, bv_add_unsigned, den_VP0, ev0_12, den_SIZE15, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 7%uint63)))) with 7. change (bv_unsigned (den E0 (VL (wp 0%uint63)))) with 0.
  rewrite bv_wrap_small by (unfold bv_modulus; lia).
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  match goal with |- ?x mod 8 = 0 => replace x with (bv_unsigned (ed_top draw)) by (unfold SI.TOP in *; lia) end.
  change page_size with 4096 in Hpg.
  pose proof (Z.div_mod (bv_unsigned (ed_top draw)) 4096 ltac:(lia)) as D. rewrite Hpg, Z.add_0_r in D. rewrite D.
  replace (4096 * (bv_unsigned (ed_top draw) / 4096)) with ((512 * (bv_unsigned (ed_top draw) / 4096)) * 8) by ring.
  apply Z.mod_mul. lia.
Qed.

Lemma f_end2 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))
                                (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Htop as HT.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_2, den_SIZE8, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  unfold SI.envp_off in *. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_end3 : fact_holds E0 (FULe (VP 3%uint63 (wp 160%uint63)) (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Htop as HT.
  cbn [fact_holds]. change (den E0 (VP 3%uint63 (wp 160%uint63))) with (bv_add (ev E0 3%uint63) (wbv (wp 160%uint63))).
  rewrite bv_add_unsigned, ev0_3. change (bv_unsigned (wbv (wp 160%uint63))) with 160.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  unfold SI.auxv_off in *. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
(* The auxv's end bound at region 3's own size ([Regen.end3_fact]): the vector at the run's CONFIG_RSEQ
   value ([R3T]) ends at VP 3 + auxv_size, and the 432 bytes both values share ([Auxv.R3A]) end no later.
   VP 3 + auxv_size = TOP - 24 - LSB - gap - pad (sstruct_val, sstruct_eq_top), at most 2^47 - 24. *)
Lemma f_end3T : fact_holds E0 (Regen.end3_fact R3T).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Htop as HT.
  unfold Regen.end3_fact. cbn [fact_holds].
  change (den E0 (VP 3%uint63 (Regen.r3_hi R3T))) with (bv_add (ev E0 3%uint63) (wbv (Regen.r3_hi R3T))).
  rewrite bv_add_unsigned, ev0_3. change (bv_unsigned (wbv (Regen.r3_hi R3T))) with (hiZ E0 R3T). rewrite hiZ_R3.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  unfold SI.auxv_off in *. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_end3A : fact_holds E0 (Regen.end3_fact R3A).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Htop as HT.
  unfold Regen.end3_fact. cbn [fact_holds].
  change (den E0 (VP 3%uint63 (Regen.r3_hi R3A))) with (bv_add (ev E0 3%uint63) (wbv (wp 432%uint63))).
  rewrite bv_add_unsigned, ev0_3. change (bv_unsigned (wbv (wp 432%uint63))) with 432.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  unfold SI.auxv_off in *. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

(* argv[0]'s and argv[1]'s ends: at LPS 727298f3 the strings sit at the stack's
   top, followed only by the later strings, the exec name and its NUL and the
   8-byte slot, so the end is at most [2^47 - 9]; it was [2^47 - 16]
   (the same change jsoncons/fuzz_bigint's port took). *)
Lemma f_a0_end9 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 5%uint63 (wp 0%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                                    (VL (wp 140737488355319%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0. pose proof Htop as HT. pose proof (SI.LSB_eq inp) as HLSB. pose proof a0_len.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_5, den_SIZE9, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355319%uint63)))) with 140737488355319.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_a0_base96 : fact_holds E0 (FULe (VP 1%uint63 (wp 96%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite (den_VP0 5%uint63), ev0_5. cbn [den]. rewrite bv_add_unsigned, ev0_1. change (bv_unsigned (wbv (wp 96%uint63))) with 96.
  fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_a0_base88 : fact_holds E0 (FULe (VP 1%uint63 (wp 88%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite (den_VP0 5%uint63), ev0_5. cbn [den]. rewrite bv_add_unsigned, ev0_1. change (bv_unsigned (wbv (wp 88%uint63))) with 88.
  fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Section F2.
Hypothesis Hargc2 : length argv = 2%nat.
Lemma f_envp2 : fact_holds E0 (FEq (VP 2%uint63 (wp 0%uint63)) (VP 1%uint63 (wp 32%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top.
  cbn [fact_holds den]. rewrite ev0_1. apply bv_eq. rewrite !bv_add_unsigned, ev0_2, w0. fold (SI.SP sp).
  change (bv_unsigned (wbv (wp 32%uint63))) with 32. unfold SI.envp_off. unfold SI.argcZ, SI.nargc. rewrite Hargc2.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.mod_small; lia.
Qed.
Lemma f_sp_le_a1 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 10%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_10. fold (SI.SP sp). lia.
Qed.
Lemma f_size10_lo : fact_holds E0 (FULe (VL (wp 1%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof. pose proof (a1_len Hargc2). cbn [fact_holds]. rewrite (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 1%uint63)))) with 1. lia. Qed.
Lemma f_size10_hi : fact_holds E0 (FULe (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63) (VL (wp 131072%uint63))).
Proof. pose proof (a1_len Hargc2). cbn [fact_holds]. rewrite (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 131072%uint63)))) with 131072. lia. Qed.
Lemma total_ge_a0a1 : Z.of_nat (length a0) + 1 + Z.of_nat (length a1) + 1 <= Z.of_nat (total_nat argv).
Proof. pose proof total2 as H. lia. Qed.
Lemma f_a1_end : fact_holds E0 (FULe (VAlu ALU_ADD (VP 10%uint63 (wp 0%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63))
                                  (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0a1. pose proof Htop as HT. pose proof (a1_len Hargc2).
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_10, (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

Lemma f_a1_end9 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 10%uint63 (wp 0%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63))
                                    (VL (wp 140737488355319%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0a1. pose proof Htop as HT. pose proof (SI.LSB_eq inp) as HLSB. pose proof (a1_len Hargc2).
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_10, (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355319%uint63)))) with 140737488355319.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_a1_base96 : fact_holds E0 (FULe (VP 1%uint63 (wp 96%uint63)) (VP 10%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite (den_VP0 10%uint63), ev0_10. cbn [den]. rewrite bv_add_unsigned, ev0_1. change (bv_unsigned (wbv (wp 96%uint63))) with 96.
  fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_12_le_10 : fact_holds E0 (FULe (VP 12%uint63 (wp 0%uint63)) (VP 10%uint63 (wp 0%uint63))).
Proof. cbn [fact_holds]. rewrite !den_VP0, ev0_12, ev0_10. lia. Qed.
Lemma f_end10_12 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 10%uint63 (wp 0%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63))
                                    (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof auxv_size_rng. pose proof gap_rng. pose proof sstruct_eq_top. pose proof total_ge_a0a1. pose proof Htop as HT. pose proof (a1_len Hargc2). pose proof strarea_len.
  cbn [fact_holds]. change (den E0 (VAlu ALU_ADD ?a ?b)) with (bv_add (den E0 a) (den E0 b)) at 1.
  change (den E0 (VAlu ALU_ADD (VP 12%uint63 ?o) ?b)) with (bv_add (den E0 (VP 12%uint63 o)) (den E0 b)).
  rewrite !bv_add_unsigned, !den_VP0, ev0_10, ev0_12, (den_SIZE10 Hargc2), den_SIZE15, !Z_to_bv64_unsigned by lia.
  rewrite !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
End F2.

Theorem PB_E0 : PB_STD (eb E0).
Proof.
  exists a0, (envp_ptrs). cbn [eb E0]. unfold eb0.
  change (to_Z 1%uint63) with 1. change (to_Z 2%uint63) with 2. change (to_Z 8%uint63) with 8. change (to_Z 9%uint63) with 9.
  change (to_Z 6%uint63) with 6. cbv iota.
  rewrite length_envp_ptrs. fold (envcZ).
  split; [reflexivity|]. split; [apply a0_nonul|]. split; [apply a0_len|]. split; [reflexivity|].
  split; [pose proof Henvc as H; unfold SI.envcZ in H; lia|]. split; [|split; [reflexivity|]; split; [reflexivity | apply length_at_random_bytes]].
  apply Forall_nth. intros k d Hk. rewrite length_envp_ptrs in Hk.
  rewrite (nth_indep _ d (Z_to_bv 64 0)) by (rewrite length_envp_ptrs; exact Hk).
  pose proof (SI.envp_ptr_val sp brk0 mbase inp draw Hsp Hlaunch k Hk). lia.
Qed.

Lemma so_regs0 : forall r,
  rget (Core (ms_regs ms0) (ms_fregs ms0) (ms_pc_val ms0) (ms_fcsr ms0) (ms_resv ms0)) (reg_of_r5 r)
  = den E0 (rf_get (rf_of Z0 [Z0; Z0; VP 1%uint63 (wp 0%uint63); Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0;
                           Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0]) r).
Proof.
  intros r. destruct r; try reflexivity.
  change (den E0 _) with (bv_add sp (wbv (wp 0%uint63))). rewrite bv_add_0_r by reflexivity. reflexivity.
Qed.
Lemma so_fregs0 : forall r, reg_get (ms_fregs ms0) (reg_of_r5 r) = den E0 (rf_get (rf_init Z0) r).
Proof. intros r. destruct r; reflexivity. Qed.
Lemma so_fcsr0 : bv_unsigned (ms_fcsr ms0) < 32.
Proof. change (bv_unsigned (Z_to_bv 32 0) < 32). rewrite Z_to_bv_small; [lia|]. unfold bv_modulus. lia. Qed.

Definition RFc : rf sv := rf_of Z0 [Z0; Z0; VP 1%uint63 (wp 0%uint63); Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0;
                                    Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0].
Definition FFc : rf sv := rf_of Z0 [Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0;
                                    Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0].
Definition REGS_N : IMap.t region :=
  imap_of [(0%uint63, R0T); (1%uint63, R1NT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (12%uint63, R12T)].
Definition REGS_F : IMap.t region :=
  imap_of [(0%uint63, R0T); (1%uint63, R1FT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (10%uint63, R10T); (12%uint63, R12T)].

Lemma REGS_N_elements : IMap.elements REGS_N = [(0%uint63, R0T); (1%uint63, R1NT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (12%uint63, R12T)].
Proof. vm_compute. reflexivity. Qed.
Lemma REGS_F_elements : IMap.elements REGS_F = [(0%uint63, R0T); (1%uint63, R1FT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (10%uint63, R10T); (12%uint63, R12T)].
Proof. vm_compute. reflexivity. Qed.

Lemma regs_N_cases : forall k r, IMap.find k REGS_N = Some r ->
  (k = 0%uint63 /\ r = R0T) \/ (k = 1%uint63 /\ r = R1NT) \/ (k = 2%uint63 /\ r = R2T) \/ (k = 3%uint63 /\ r = R3T)
  \/ (k = 5%uint63 /\ r = R5T) \/ (k = 6%uint63 /\ r = R6T) \/ (k = 12%uint63 /\ r = R12T).
Proof.
  intros k r H. apply (find_in_elements _ k r REGS_N (imap_of_bst _ _)) in H. rewrite REGS_N_elements in H.
  cbn [In] in H. intuition congruence.
Qed.
Lemma regs_F_cases : forall k r, IMap.find k REGS_F = Some r ->
  (k = 0%uint63 /\ r = R0T) \/ (k = 1%uint63 /\ r = R1FT) \/ (k = 2%uint63 /\ r = R2T) \/ (k = 3%uint63 /\ r = R3T)
  \/ (k = 5%uint63 /\ r = R5T) \/ (k = 6%uint63 /\ r = R6T) \/ (k = 10%uint63 /\ r = R10T) \/ (k = 12%uint63 /\ r = R12T).
Proof.
  intros k r H. apply (find_in_elements _ k r REGS_F (imap_of_bst _ _)) in H. rewrite REGS_F_elements in H.
  cbn [In] in H. intuition congruence.
Qed.

Lemma hiZ_R6' : hiZ E0 R6T = 16. Proof. reflexivity. Qed.

Ltac ranges Ha :=
  rewrite ?ev0_1 in Ha;
  rewrite ?ev0_2, ?ev0_3, ?ev0_5, ?ev0_6, ?ev0_10, ?ev0_12 in Ha;
  rewrite ?loZ_R1, ?hiZ_R1, ?loZ_R1F, ?hiZ_R1F, ?hiZ_R2, ?hiZ_R3, ?hiZ_R5, ?hiZ_R6, ?hiZ_R12,
          ?(loZ_0 R2T eq_refl), ?(loZ_0 R3T eq_refl), ?(loZ_0 R5T eq_refl), ?(loZ_0 R6T eq_refl), ?(loZ_0 R10T eq_refl), ?(loZ_0 R12T eq_refl) in Ha;
  fold (SI.SP sp) in Ha.

Lemma ms0_minv : forall a b, ms_mem ms0 a = Some b -> forall seg, find_segment SEGS (bv_unsigned a) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros a b Hb seg Hseg. exfalso. pose proof (u64_range a) as Ha. pose proof Hlo as Hlo'.
  destruct (Z_lt_le_dec (bv_unsigned a) (SI.WLO mbase inp draw)) as [Hlt|Hge].
  - rewrite ms0_mem, <- (Z_to_bv_bv_unsigned 64 a) in Hb.
    pose proof WLO_floor as HWf. rewrite (SI.mem0_none_low SEGS PC PH sp mbase inp draw) in Hb by (try (unfold SI.SP in *); lia). discriminate Hb.
  - rewrite (find_segment_none SEGS (bv_unsigned a) 1 SEGTOP segs_below_top) in Hseg; [discriminate Hseg | | lia].
    pose proof WLO_lo. pose proof segtop_low. lia.
Qed.

Theorem st_ok_N : forall (OPS : optable) (pc0 : int) (FACTS : list fact) model,
  Z_to_bv 64 (Z.of_N PC) = Z_to_bv 64 (to_Z pc0) -> facts_hold E0 FACTS -> plain_table OPS -> mfacts model ->
  st_ok SEGS OPS E0 (SS pc0 RFc FFc RNone REGS_N FACTS [] [] 64%uint63) ms0 model.
Proof.
  intros OPS pc0 FACTS model Hpc HF PL Hmf.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof total_ge_a0 as HA.
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv].
  - exact Hpc.
  - reflexivity.
  - apply so_regs0.
  - apply so_fregs0.
  - reflexivity.
  - reflexivity.
  - apply so_fcsr0.
  - reflexivity.
  - reflexivity.
  - apply imap_of_bst.
  - intros k r Hk. rewrite ms0_mem.
    destruct (regs_N_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]];
      [apply R0_ok | apply R1_ok | apply R2_ok | apply R3_ok | apply R5_ok | apply R6_ok | apply R12_ok].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 Hw a [Ha1 Ha2].
    destruct (regs_N_cases k1 r1 H1) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]; try discriminate Hk1;
    destruct (regs_N_cases k2 r2 H2) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]; try discriminate Hk2;
    try (exfalso; apply Hne; reflexivity);
    cbn [rg_w R1NT R2T R3T R5T R6T R12T] in Hw; try (exfalso; destruct Hw as [Hw|Hw]; discriminate Hw);
    ranges Ha1; ranges Ha2; unfold SI.envp_off, SI.auxv_off in *; lia.
  - intros r g gr c Hr Hg.
    destruct (regs_N_cases _ r Hr) as [[_ ->]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[H _]]]]]]]; try discriminate H. cbn in Hg. discriminate.
  - exact HF.
  - constructor.
  - constructor.
  - exact (plain_minv OPS _ PL Hmf).
  - intros a _. exact (plain_cover OPS _ a PL).
  - exact ms0_minv.
Qed.

Theorem st_ok_F : forall (OPS : optable) (pc0 : int) (FACTS : list fact) model,
  length argv = 2%nat ->
  Z_to_bv 64 (Z.of_N PC) = Z_to_bv 64 (to_Z pc0) -> facts_hold E0 FACTS -> plain_table OPS -> mfacts model ->
  st_ok SEGS OPS E0 (SS pc0 RFc FFc RNone REGS_F FACTS [] [] 64%uint63) ms0 model.
Proof.
  intros OPS pc0 FACTS model Hargc2 Hpc HF PL Hmf.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof auxv_size_rng as HAX. pose proof gap_rng as HG. pose proof sstruct_eq_top as HST. pose proof total_ge_a0 as HA. pose proof (total2 Hargc2) as HT2.
  pose proof (hiZ_R10 Hargc2) as H10. assert (Hac2 : argcZ = 2) by (unfold SI.argcZ, SI.nargc; rewrite Hargc2; reflexivity).
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv].
  - exact Hpc.
  - reflexivity.
  - apply so_regs0.
  - apply so_fregs0.
  - reflexivity.
  - reflexivity.
  - apply so_fcsr0.
  - reflexivity.
  - reflexivity.
  - apply imap_of_bst.
  - intros k r Hk. rewrite ms0_mem.
    destruct (regs_F_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]];
      [apply R0_ok | apply R1F_ok; exact Hargc2 | apply R2_ok | apply R3_ok | apply R5_ok | apply R6_ok | apply R10_ok; exact Hargc2 | apply R12_ok].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 Hw a [Ha1 Ha2].
    destruct (regs_F_cases k1 r1 H1) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try discriminate Hk1;
    destruct (regs_F_cases k2 r2 H2) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try discriminate Hk2;
    try (exfalso; apply Hne; reflexivity);
    cbn [rg_w R1FT R2T R3T R5T R6T R10T R12T] in Hw; try (exfalso; destruct Hw as [Hw|Hw]; discriminate Hw);
    ranges Ha1; ranges Ha2; rewrite ?H10 in Ha1; rewrite ?H10 in Ha2; unfold SI.envp_off, SI.auxv_off in *; lia.
  - intros r g gr c Hr Hg.
    destruct (regs_F_cases _ r Hr) as [[_ ->]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[H _]]]]]]]]; try discriminate H. cbn in Hg. discriminate.
  - exact HF.
  - constructor.
  - constructor.
  - exact (plain_minv OPS _ PL Hmf).
  - intros a _. exact (plain_cover OPS _ a PL).
  - exact ms0_minv.
Qed.

End Entry.
End Image.
End InitLib.
