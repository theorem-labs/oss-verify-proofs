(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require PrimInt63 Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import PrimInt63.
Open Scope Z_scope.

Module IMF.
#[local] Notation φ := Uint63.to_Z.

Definition i63_1 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 1.
Definition i63_2 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 2.
Definition i63_4 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 4.
Definition i63_16 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 16.
Definition i63_48 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 48.
Definition i63_57 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 57.
Definition i63_87 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 87.
Definition i63_97 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 97.
Definition i63_102 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 102.
Definition i63_256 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 256.
Definition hexv63 (c : PrimInt63.int) : PrimInt63.int :=
  if (Uint63.leb i63_48 c && Uint63.leb c i63_57)%bool then Uint63.sub c i63_48
  else if (Uint63.leb i63_97 c && Uint63.leb c i63_102)%bool then Uint63.sub c i63_87 else i63_16.
Definition hexb63 (s : PrimString.string) (i : PrimInt63.int) : PrimInt63.int :=   (* [comment removed for export] *)
  let h := hexv63 (PrimString.get s i) in
  let l := hexv63 (PrimString.get s (Uint63.add i i63_1)) in
  if (Uint63.ltb h i63_16 && Uint63.ltb l i63_16)%bool then Uint63.add (Uint63.lsl h i63_4) l else i63_256.
(* [comment removed for export] *)
Fixpoint page_segment (ss : list Segment) (lo len : Z) : option Segment :=
  match ss with
  | [] => None
  | sg :: rest =>
      let base := Z.of_N (seg_base sg) in let top := base + Z.of_N (seg_size sg) in
      if (Z.leb base lo && Z.leb (lo + len) top)%bool then Some sg
      else if (Z.leb (lo + len) base || Z.leb top lo)%bool then page_segment rest lo len
      else None
  end.
(* [comment removed for export] *)
Fixpoint rd_bytes63 (c : PrimString.string) (i : PrimInt63.int) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      let b := hexb63 c i in
      if Uint63.ltb b i63_256 then
        match rd_bytes63 c (Uint63.add i i63_2) n' with
        | Some r => Some (φ b :: r)
        | None => None
        end
      else None
  end.

(* [comment removed for export] *)
Fixpoint img_bytes (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match seg_rom segs (Z_to_bv 64 a) with
      | Some b => match img_bytes segs (a + 1) n' with
                  | Some r => Some (bv_unsigned b :: r)
                  | None => None
                  end
      | None => None
      end
  end.

Definition fast_try (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  let len := Z.of_nat n in
  if negb (Z.leb 0 a && Z.ltb (a + len) (2 ^ 64) && Z.ltb 0 len)%bool then None else
  match page_segment segs a len with
  | Some sg =>
      if negb (seg_readable sg) then None else
      match seg_bytes sg with
      | [c] => let off := a - Z.of_N (seg_base sg) in
               let clen := φ (PrimString.length c) in
               if (Z.leb 0 off && Z.leb (2 * (off + len)) clen && Z.ltb clen (2 ^ 62))%bool
               then rd_bytes63 c (Uint63.of_Z (2 * off)) n else None
      | _ => None
      end
  | None => None
  end.
Definition img_bytes_fast (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match fast_try segs a n with
  | Some r => Some r
  | None => img_bytes segs a n
  end.

(* [comment removed for export] *)
Lemma wB_val : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma i63_vals : φ i63_1 = 1 /\ φ i63_2 = 2 /\ φ i63_4 = 4 /\ φ i63_16 = 16 /\ φ i63_48 = 48
                 /\ φ i63_57 = 57 /\ φ i63_87 = 87 /\ φ i63_97 = 97 /\ φ i63_102 = 102 /\ φ i63_256 = 256.
Proof. repeat split; reflexivity. Qed.

Lemma hexv63_spec : forall c, φ (hexv63 c) = Z.of_N (hex_nybble c).
Proof.
  intros c. pose proof i63_vals as (V1 & V2 & V4 & V16 & V48 & V57 & V87 & V97 & V102 & V256).
  pose proof (Uint63.to_Z_bounded c) as Bc. rewrite wB_val in Bc.
  unfold hexv63, hex_nybble. cbv delta [i63_48 i63_57 i63_97 i63_102 i63_87 i63_16].
  cbv delta [i63_48 i63_57 i63_97 i63_102 i63_87 i63_16] in V16, V48, V57, V87, V97, V102.
  destruct (Uint63.leb 48%uint63 c) eqn:E1; destruct (Uint63.leb c 57%uint63) eqn:E2; cbn [andb].
  1: { apply Uint63.leb_spec in E1. apply Uint63.leb_spec in E2. rewrite V48 in E1. rewrite V57 in E2.
       rewrite Uint63.sub_spec, V48, wB_val, Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity. }
  all: destruct (Uint63.leb 97%uint63 c) eqn:E3; destruct (Uint63.leb c 102%uint63) eqn:E4; cbn [andb]; try (rewrite V16; reflexivity).
  all: apply Uint63.leb_spec in E3; apply Uint63.leb_spec in E4; rewrite V97 in E3; rewrite V102 in E4;
       rewrite Uint63.sub_spec, V87, wB_val, Z.mod_small by lia; rewrite Z2N.id by lia; reflexivity.
Qed.

Lemma ltb63 : forall x y, Uint63.ltb x y = Z.ltb (φ x) (φ y).
Proof.
  intros x y. destruct (Uint63.ltb x y) eqn:E.
  - apply Uint63.ltb_spec in E. symmetry. apply Z.ltb_lt. exact E.
  - symmetry. apply Z.ltb_ge. destruct (Z.ltb (φ x) (φ y)) eqn:E2; [|lia]. apply Z.ltb_lt in E2.
    apply (proj2 (Uint63.ltb_spec x y)) in E2. congruence.
Qed.

(* [comment removed for export] *)
Lemma hexb63_spec : forall s n i,
  φ i = 2 * Z.of_N n -> 2 * Z.of_N n + 1 < φ (PrimString.length s) ->
  hex_byte_at s n = (if Uint63.ltb (hexb63 s i) i63_256 then Some (Z_to_bv 8 (φ (hexb63 s i))) else None)
  /\ φ (hexb63 s i) <= 256.
Proof.
  intros s n i Hi Hlen. pose proof i63_vals as (V1 & V2 & V4 & V16 & V48 & V57 & V87 & V97 & V102 & V256).
  pose proof (Uint63.to_Z_bounded (PrimString.length s)) as BL. rewrite wB_val in BL.
  unfold hex_byte_at, hexb63.
  assert (Eci : Uint63.of_Z (Z.of_N (2 * n)) = i).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, wB_val, Z.mod_small; lia. }
  assert (Eci1 : Uint63.of_Z (Z.of_N (2 * n + 1)) = Uint63.add i i63_1).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.add_spec, V1, wB_val, !Z.mod_small; lia. }
  rewrite Eci, Eci1.
  assert (Hci1 : φ (Uint63.add i i63_1) = 2 * Z.of_N n + 1).
  { rewrite Uint63.add_spec, V1, wB_val, Z.mod_small; lia. }
  rewrite (ltb63 (Uint63.add i i63_1)), Hci1. replace (2 * Z.of_N n + 1 <? φ (PrimString.length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [orb].
  set (hc := PrimString.get s i). set (lc := PrimString.get s (Uint63.add i i63_1)).
  pose proof (hexv63_spec hc) as Hh. pose proof (hexv63_spec lc) as Hl.
  set (h := hexv63 hc) in *. set (l := hexv63 lc) in *.
  rewrite (ltb63 h i63_16), (ltb63 l i63_16), V16, Hh, Hl.
  destruct (N.ltb (hex_nybble hc) 16) eqn:Eh; destruct (N.ltb (hex_nybble lc) 16) eqn:El;
    rewrite ?N.ltb_lt, ?N.ltb_ge in Eh; rewrite ?N.ltb_lt, ?N.ltb_ge in El.
  - replace (Z.of_N (hex_nybble hc) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.of_N (hex_nybble lc) <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    assert (HV : φ (Uint63.add (Uint63.lsl h i63_4) l) = Z.of_N (hex_nybble hc * 16 + hex_nybble lc)).
    { rewrite Uint63.add_spec, Uint63.lsl_spec, V4, Hh, Hl, wB_val. change (2 ^ 4) with 16. rewrite !Z.mod_small; lia. }
    rewrite (ltb63 _ i63_256), V256, HV. replace (Z.of_N (hex_nybble hc * 16 + hex_nybble lc) <? 256) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [reflexivity | lia].
  - replace (Z.of_N (hex_nybble lc) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.of_N (hex_nybble hc) <? 16); cbn [andb]; rewrite (ltb63 _ i63_256), V256, Z.ltb_irrefl; split; first [reflexivity | lia].
  - replace (Z.of_N (hex_nybble hc) <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    rewrite (ltb63 _ i63_256), V256, Z.ltb_irrefl. split; [reflexivity | lia].
  - replace (Z.of_N (hex_nybble hc) <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    rewrite (ltb63 _ i63_256), V256, Z.ltb_irrefl. split; [reflexivity | lia].
Qed.

Lemma u_Z2bv8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

(* [comment removed for export] *)
Lemma page_segment_find1 : forall ss lo len sg pc,
  page_segment ss lo len = Some sg -> lo <= pc -> pc + 1 <= lo + len ->
  find_segment ss pc 1 = Some sg.
Proof.
  induction ss as [|s0 rest IH]; intros lo len sg pc H Hlo Hhi; cbn [page_segment] in H; [discriminate|].
  cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s0)) lo && Z.leb (lo + len) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - injection H as ->. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    replace (Z.of_N (seg_base sg) <=? pc) with true by (symmetry; apply Z.leb_le; lia).
    replace (pc + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - destruct (Z.leb (lo + len) (Z.of_N (seg_base s0)) || Z.leb (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) lo)%bool eqn:D; [|discriminate].
    assert (NC : ((Z.of_N (seg_base s0) <=? pc) && (pc + 1 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool = false).
    { apply orb_prop in D as [D|D]; apply Z.leb_le in D.
      - apply andb_false_intro1. apply Z.leb_gt. lia.
      - apply andb_false_intro2. apply Z.leb_gt. lia. }
    rewrite NC. exact (IH lo len sg pc H Hlo Hhi).
Qed.

(* [comment removed for export] *)
Lemma rd_bytes63_sound : forall segs sg c lo len n a i r,
  page_segment segs lo len = Some sg -> seg_readable sg = true -> seg_bytes sg = [c] ->
  0 <= lo -> lo + len < 2 ^ 64 ->
  0 <= lo - Z.of_N (seg_base sg) -> 2 * (lo - Z.of_N (seg_base sg) + len) <= φ (PrimString.length c) -> φ (PrimString.length c) < 2 ^ 62 ->
  lo <= a -> a + Z.of_nat n <= lo + len ->
  φ i = 2 * (a - Z.of_N (seg_base sg)) ->
  rd_bytes63 c i n = Some r -> img_bytes segs a n = Some r.
Proof.
  intros segs sg c lo len n. induction n as [|n IH]; intros a i r HP HR HB Hlo0 Hhi Hoff Hclen Hc62 Ha Han Hi H.
  - cbn [rd_bytes63] in H. injection H as <-. reflexivity.
  - cbn [rd_bytes63] in H. pose proof i63_vals as (V1 & V2 & V4 & V16 & V48 & V57 & V87 & V97 & V102 & V256).
    rewrite Nat2Z.inj_succ in Han.
    set (m := Z.to_N (a - Z.of_N (seg_base sg))).
    assert (Hm : Z.of_N m = a - Z.of_N (seg_base sg)) by (subst m; rewrite Z2N.id; lia).
    destruct (hexb63_spec c m i ltac:(rewrite Hm; exact Hi) ltac:(rewrite Hm; lia)) as [HB1 HB2].
    destruct (Uint63.ltb (hexb63 c i) i63_256) eqn:LT; [|discriminate].
    destruct (rd_bytes63 c (Uint63.add i i63_2) n) as [r'|] eqn:RR; [|discriminate]. injection H as <-.
    assert (Hb : 0 <= φ (hexb63 c i) < 256).
    { rewrite ltb63, V256 in LT. apply Z.ltb_lt in LT. pose proof (Uint63.to_Z_bounded (hexb63 c i)). lia. }
    cbn [img_bytes]. unfold seg_rom, memory_read.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (Z.of_N 64) with 64; lia).
    change (Z.of_N 1) with 1.
    rewrite (page_segment_find1 segs lo len sg a HP Ha ltac:(lia)). cbn beta iota zeta. rewrite HR, HB.
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. fold m.
    assert (LTm : (m <? Z.to_N (φ (PrimString.length c) / 2))%N = true).
    { apply N.ltb_lt. apply N2Z.inj_lt. rewrite Hm.
      assert (D : a - Z.of_N (seg_base sg) + 1 <= φ (PrimString.length c) / 2) by (apply Z.div_le_lower_bound; lia).
      rewrite Z2N.id by lia. lia. }
    rewrite LTm.
    rewrite HB1.
    assert (Hi2 : φ (Uint63.add i i63_2) = 2 * (a + 1 - Z.of_N (seg_base sg))).
    { rewrite Uint63.add_spec, V2, wB_val, Z.mod_small; lia. }
    cbn beta iota.
    rewrite (IH (a + 1) (Uint63.add i i63_2) r' HP HR HB Hlo0 Hhi Hoff Hclen Hc62 ltac:(lia) ltac:(lia) Hi2 RR).
    rewrite u_Z2bv8 by exact Hb. reflexivity.
Qed.

Theorem img_bytes_fast_eq : forall segs a n, img_bytes_fast segs a n = img_bytes segs a n.
Proof.
  intros segs a n. unfold img_bytes_fast. destruct (fast_try segs a n) as [r|] eqn:F; [|reflexivity].
  symmetry. unfold fast_try in F.
  destruct (Z.leb 0 a && Z.ltb (a + Z.of_nat n) (2 ^ 64) && Z.ltb 0 (Z.of_nat n))%bool eqn:C0; cbn [negb] in F; [|discriminate].
  apply andb_prop in C0 as [C0 C3]. apply andb_prop in C0 as [C1 C2].
  apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  destruct (page_segment segs a (Z.of_nat n)) as [sg|] eqn:HP; [|discriminate].
  destruct (seg_readable sg) eqn:HR; cbn [negb] in F; [|discriminate].
  destruct (seg_bytes sg) as [|c [|c2 rest]] eqn:HB; try discriminate.
  match type of F with (if ?cnd then _ else _) = _ => destruct cnd eqn:C4; [|discriminate] end.
  apply andb_prop in C4 as [C4 C6]. apply andb_prop in C4 as [C4 C5].
  apply Z.leb_le in C4. apply Z.leb_le in C5. apply Z.ltb_lt in C6.
  apply (rd_bytes63_sound segs sg c a (Z.of_nat n) n a (Uint63.of_Z (2 * (a - Z.of_N (seg_base sg)))) r HP HR HB C1 C2 C4 C5 C6);
    [lia | lia | | exact F].
  rewrite Uint63.of_Z_spec, wB_val, Z.mod_small; lia.
Qed.
End IMF.
