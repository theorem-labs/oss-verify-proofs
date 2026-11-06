(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_memset AI_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.
#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Lemma memset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (junk : list byte) (P : acc -> Prop),
  (forall a k, A <= a -> a + Z.of_nat k <= A + n -> P (Z_to_bv 64 a, k)) ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evtA asegs P (memsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e0e0) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros PDST DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evtA_mono. { eapply memset_spec; [| |exact MI]. { intros a k H1 H2. rewrite EA in H1. rewrite EA, En in H2. apply PDST; lia. } rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End RC__1.
Notation A_GTAB := 0xa9380%Z (only parsing).
Notation A_SB := 0x7fff8000%Z (only parsing).
Notation SHA_LO := 0x7fffc204%Z (only parsing).  Notation SHA_HI := 0x7fffc470%Z (only parsing).
Notation SHB_LO := 0x8000d1ec%Z (only parsing).  Notation SHB_HI := 0x8000d20c%Z (only parsing).
Notation SHC_LO := 0x8000d270%Z (only parsing).  Notation SHC_HI := 0x8000d498%Z (only parsing).

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition aglob_recs : list (Z * Z * bool) :=
  [(0x21020, 0x20, true); (0x21040, 0x60, true); (0x210a0, 0x40, true); (0x210e0, 0x60, true);
   (0x21140, 0x40, true); (0x21180, 0x40, true); (0x211c0, 0x40, true); (0x21200, 0x40, true);
   (0x21280, 0x20, true); (0x212a0, 0x60, true); (0x21300, 0x40, true); (0x21340, 0x20, true);
   (0x21360, 0x20, true); (0x21380, 0x20, true); (0x214a0, 0x40, true); (0x214e0, 0x60, true);
   (0x21540, 0x20, true); (0x21560, 0x20, true); (0x21580, 0x20, true); (0x215a0, 0x20, true);
   (0x215c0, 0x20, true); (0x215e0, 0x140, true); (0x21760, 0x20, true); (0x21780, 0x60, true);
   (0x217e0, 0x20, true); (0x21800, 0x20, true); (0x21820, 0x20, true); (0x21840, 0x20, true);
   (0x21860, 0x20, true); (0x21880, 0x20, true); (0x218a0, 0x40, true); (0x218e0, 0x20, true);
   (0x21900, 0x20, true); (0x21920, 0x60, true); (0x21980, 0x40, true); (0x21aa0, 0x40, true);
   (0x21ae0, 0x60, true); (0x21b40, 0x20, true); (0x21b60, 0x60, true); (0x21bc0, 0x40, true);
   (0x21c00, 0x40, true); (0x21c40, 0x60, true); (0x21ca0, 0x60, true); (0x21d00, 0x40, true);
   (0x21d40, 0x60, true); (0x21da0, 0x60, true); (0x21e00, 0x60, true); (0x21e60, 0x60, true);
   (0x21ec0, 0x20, true); (0x21ee0, 0x60, true); (0x21f40, 0x40, true); (0x21f80, 0x40, true);
   (0x22000, 0x20, true); (0x22020, 0x20, true); (0x22040, 0x20, true); (0x22060, 0x20, true);
   (0x22080, 0x20, true); (0x220a0, 0x20, true); (0x220c0, 0x20, true); (0x220e0, 0x20, true);
   (0x22100, 0x20, true); (0x22120, 0x60, true); (0x22180, 0x60, true); (0x221e0, 0x40, true);
   (0x22220, 0x20, true); (0x22240, 0x20, true); (0xa8f60, 0x80, false); (0xa8fe0, 0x40, false);
   (0xa9020, 0x40, false)].

Definition grec (i : nat) : Z * Z * bool := nth i aglob_recs (0, 0, true).
Definition gbeg (i : nat) : Z := fst (fst (grec i)).
Definition gsrz (i : nat) : Z := snd (fst (grec i)).
Definition ginA (i : nat) : bool := snd (grec i).
Definition rlo (inA : bool) : Z := if inA then SHA_LO else SHB_LO.
Definition rhi (inA : bool) : Z := if inA then SHA_HI else SHB_HI.

(* [comment removed for export] *)
Definition rec_wf (r : Z * Z * bool) : bool :=
  let '(beg, srz, inA) := r in
  (beg mod 8 =? 0) && (srz mod 8 =? 0) && (8 <=? srz) && (beg + srz <=? A_SB) && (0 <=? beg) &&
  (rlo inA <=? A_SB + beg / 8) && (A_SB + beg / 8 + srz / 8 <=? rhi inA) && (srz / 8 <? 0x10000).

Lemma aglob_recs_wf : forallb rec_wf aglob_recs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma aglob_recs_len : length aglob_recs = 69%nat.
Proof. reflexivity. Qed.

Lemma grec_wf : forall i, (i < 69)%nat ->
  gbeg i mod 8 = 0 /\ gsrz i mod 8 = 0 /\ 8 <= gsrz i /\ gbeg i + gsrz i <= A_SB /\ 0 <= gbeg i /\
  rlo (ginA i) <= A_SB + gbeg i / 8 /\ A_SB + gbeg i / 8 + gsrz i / 8 <= rhi (ginA i) /\ gsrz i / 8 < 0x10000.
Proof.
  intros i Hi. pose proof aglob_recs_wf as W. rewrite forallb_forall in W.
  assert (IN : In (grec i) aglob_recs) by (unfold grec; apply nth_In; rewrite aglob_recs_len; exact Hi).
  specialize (W _ IN). unfold gbeg, gsrz, ginA. destruct (grec i) as [[beg srz] inA]. cbn [fst snd].
  unfold rec_wf in W. rewrite !Bool.andb_true_iff in W.
  destruct W as (((((((W1 & W2) & W3) & W4) & W5) & W6) & W7) & W8).
  apply Z.eqb_eq in W1. apply Z.eqb_eq in W2. apply Z.leb_le in W3. apply Z.leb_le in W4. apply Z.leb_le in W5.
  apply Z.leb_le in W6. apply Z.leb_le in W7. apply Z.ltb_lt in W8. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition globals_tab (m : mem) : Prop :=
  forall i, (i < 69)%nat -> exists sz nm md dy lc,
    rw_cells asegs m (64 * Z.of_nat i + A_GTAB)
      [C8 (Z_to_bv 64 (gbeg i)); C8 sz; C8 (Z_to_bv 64 (gsrz i)); C8 nm; C8 md; C8 dy; C8 lc; C8 (Z_to_bv 64 (2^64 - 1))].

Lemma globals_tab_transport : forall W m m',
  globals_tab m -> munch W m m' -> wmono asegs m m' -> disjoint_from W A_GTAB 4416 -> globals_tab m'.
Proof.
  intros W m m' T MU WM D i Hi. destruct (T i Hi) as (sz & nm & md & dy & lc & R). exists sz, nm, md, dy, lc.
  eapply rw_cells_transport; [exact R | exact MU | exact WM |]. cbn. eapply disjoint_from_sub; [exact D | lia | lia].
Qed.

(* [comment removed for export] *)
Definition unreg_statics (m : mem) : Prop :=
     rw_cells asegs m 0xa49a8 [C8 (Z_to_bv 64 0xab378)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab390 [C4 (Z_to_bv 64 1)]             (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49b0 [C8 (Z_to_bv 64 0xadb78)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xadb78 [C8 (Z_to_bv 64 A_SB)]
  /\ rw_cells asegs m 0xa49b8 [C8 (Z_to_bv 64 0xae868)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49c0 [C8 (Z_to_bv 64 0xae870)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49c8 [C8 (Z_to_bv 64 0xae860)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13f720 [C8 (Z_to_bv 64 0xffffffffffffffff)]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49d0 [C8 (Z_to_bv 64 0xa6828)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6828 [C8 (Z_to_bv 64 0x9e0e0)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa4990 [C8 (Z_to_bv 64 0x13d620)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xad3dc [C1 (Z_to_bv 8 1)].             (* [comment removed for export] *)

End RC__2.
Ltac unreg_statics_open G :=
  unfold unreg_statics in G;
  destruct G as (?GFL & ?GRG & ?GSBP & ?GSB & ?GMB & ?GME & ?GHE & ?GCF & ?GTHR & ?GRSP & ?GRS & ?GPSC & ?GINI & ?GCPM).

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition unreg_statics_cells : list (Z * Z) :=
  [(0xa49a8, 8); (0xab390, 4); (0xa49b0, 8); (0xadb78, 8); (0xa49b8, 8); (0xa49c0, 8); (0xa49c8, 8);
   (0xa49a0, 8); (0x13f720, 8); (0xa49d0, 8); (0xa6828, 8); (0xa4990, 8); (0xae858, 1); (0xad3dc, 1)]%Z.

Lemma unreg_statics_transport : forall W m m',
  unreg_statics m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) unreg_statics_cells ->
  unreg_statics m'.
Proof.
  intros W m m' G MU WM D. unfold unreg_statics_cells in D.
  repeat match type of D with Forall _ (_ :: _) => apply Forall_cons_iff in D; destruct D as [? D] end. cbn [fst snd] in *.
  unreg_statics_open G.
  unfold unreg_statics.
  repeat match goal with
  | |- rw_cells asegs m' ?A2 ?cs2 /\ _ => split
  | |- rw_cells asegs m' ?A2 ?cs2 =>
      eapply (rw_cells_transport asegs W m m' A2 cs2); [ eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add]; assumption ]
  end.
Qed.

(* [comment removed for export] *)
End RC__3.
Ltac unreg_statics_disjoint :=
  unfold unreg_statics_cells; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; repeat split; lia|]); apply Forall_nil.

(* [comment removed for export] *)
Section RC__4.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rec_C8_CB8 : forall m A b sz (s : word) rest,
  rw_cells asegs m A (C8 b :: C8 sz :: C8 s :: rest) -> rw_cells asegs m A (C8 b :: C8 sz :: CB 8 (le8 s) :: rest).
Proof.
  intros m A b sz s rest [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. destruct W as (W1 & W2 & W3 & W4). split; [exact I|]. split; [exact I|]. split; [apply length_le8| exact W4].
  - exact B.
  - exact R.
Qed.
Lemma rec_CB8_C8 : forall m A b sz (s : word) rest,
  rw_cells asegs m A (C8 b :: C8 sz :: CB 8 (le8 s) :: rest) -> rw_cells asegs m A (C8 b :: C8 sz :: C8 s :: rest).
Proof.
  intros m A b sz s rest [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. destruct W as (W1 & W2 & W3 & W4). split; [exact I|]. split; [exact I|]. split; [exact I| exact W4].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le8 : forall v : word, firstn 1 (skipn 0 (le8 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma land7_of_mod8 : forall z, 0 <= z -> z mod 8 = 0 -> Z.land (z mod 256) 7 = 0.
Proof.
  intros z Hz H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
  replace (z mod 256) with (8 * ((z mod 256) / 8)).
  - rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
  - Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walk.
Variable P : acc -> Prop.
(* [comment removed for export] *)
Variables (sp gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 240.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHA : forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHB : forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000e048 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Notation UGW :=
  [(bv_unsigned sp - 240, bv_unsigned sp); (0xab430, 0xab438); (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z.

Notation Q := (Z_to_bv 64 (bv_unsigned sp + -176)).

(* [comment removed for export] *)
Definition ug_frame (m : mem) (j0 : list byte) (v40 v48 v56 v64 : word) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra : word) : Prop :=
  rw_cells asegs m (bv_unsigned sp + -176)
    [CB 8 j0; C8 (Z_to_bv 64 0xab438); C8 (Z_to_bv 64 0xab3f0); C8 (Z_to_bv 64 69); C8 (Z_to_bv 64 A_GTAB);
     C8 v40; C8 v48; C8 v56; C8 v64;
     C8 x27; C8 x26; C8 x25; C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 ra].

(* [comment removed for export] *)
Hypothesis G0 : unreg_statics m0.
Hypothesis TAB0 : globals_tab m0.

Lemma UGW_statics : Forall (fun c => disjoint_from UGW (fst c) (snd c)) unreg_statics_cells.
Proof. unreg_statics_disjoint. Qed.
Lemma UGW_tab : disjoint_from UGW A_GTAB 4416.
Proof. cbn [disjoint_from]. repeat split; lia. Qed.

(* [comment removed for export] *)
Definition ug_head (i : nat) (m : mem) (x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
  MS (mkR x1 Q gp tp t0 t1 t2 s0 (Z_to_bv 64 0x13f6a8) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 2) (Z_to_bv 64 0x1b3f4) (Z_to_bv 64 (64 * Z.of_nat i + A_GTAB)) (Z_to_bv 64 (2^61))
          (Z_to_bv 64 0xab3f0) (Z_to_bv 64 0xa6828) (Z_to_bv 64 0xab430) (Z_to_bv 64 0xab378)
          (Z_to_bv 64 0xadb78) (Z_to_bv 64 (69 - Z.of_nat i)) t3 t4 t5 t6)
     F0 (Z_to_bv 64 (if (i =? 69)%nat then 0x40ee4 else 0x40ce0)) fc0 None m (seg_rom asegs).

(* [comment removed for export] *)
Definition ug_kont (i : nat) (QQ : machine_state -> Prop) j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra : Prop :=
  forall (m' : mem) (x1' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> munch UGW m0 m' -> wmono asegs m0 m' ->
     stk asegs m' lo (bv_unsigned sp + -176) ->
     ug_frame m' j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
     rw_cells asegs m' 0xab430 [C8 (Z_to_bv 64 (2^60))] ->
     stk asegs m' SHA_LO SHA_HI -> stk asegs m' SHB_LO SHB_HI -> stk asegs m' SHC_LO SHC_HI ->
     evtA asegs P QQ (ug_head i m' x1' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6').

(* [comment removed for export] *)
Ltac ea_syn := first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].

(* [comment removed for export] *)
Lemma ug_iter_tail : forall (i : nat) (QQ : machine_state -> Prop) (m : mem)
    (x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra sz nm md dy lc,
  (i < 69)%nat ->
  mem_inv asegs m -> munch UGW m0 m -> wmono asegs m0 m ->
  stk asegs m lo (bv_unsigned sp + -176) ->
  ug_frame m j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  rw_cells asegs m 0xab430 [C8 (Z_to_bv 64 (2^60))] ->
  stk asegs m SHA_LO SHA_HI -> stk asegs m SHB_LO SHB_HI -> stk asegs m SHC_LO SHC_HI ->
  rw_cells asegs m (64 * Z.of_nat i + A_GTAB)
      [C8 (Z_to_bv 64 (gbeg i)); C8 sz; C8 (Z_to_bv 64 (gsrz i)); C8 nm; C8 md; C8 dy; C8 lc; C8 (Z_to_bv 64 (2^64 - 1))] ->
  ug_kont (S i) QQ j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  evtA asegs P QQ
    (MS (mkR x1 Q gp tp t0 t1 t2 s0 (Z_to_bv 64 0x13f6a8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b3f4) (Z_to_bv 64 (64 * Z.of_nat i + A_GTAB)) (Z_to_bv 64 (2^61))
             (Z_to_bv 64 0xab3f0) (Z_to_bv 64 0xa6828) (Z_to_bv 64 0xab430) (Z_to_bv 64 0xab378)
             (Z_to_bv 64 0xadb78) (Z_to_bv 64 (69 - Z.of_nat i)) t3 t4 t5 t6)
        F0 (Z_to_bv 64 0x40cc8) fc0 None m (seg_rom asegs)).
Proof.
  intros until lc. intros Hi MI MU WM ST FR MUT SA SB SC REC HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  stepA. zstepA.
  replace (Z_to_bv 64 (18446744073709551615 + 1)) with (Z_to_bv 64 0 : word) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
  stepA. if_false.
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. if_cases Kz; zify_cond Kz.
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in Kz by lia.
    unfold ug_kont, ug_head in HK. replace (S i =? 69)%nat with true in HK by (symmetry; apply Nat.eqb_eq; lia).
    lazymatch goal with |- evtA _ _ _ (MS ?R _ _ _ _ _ _) =>
      eapply evtA_eq; [ | eapply (HK m); ea_syn ] end.
    cbv delta [mkR]. repeat first [reflexivity | progress f_equal; try lia].
  - rewrite ?unsigned_lit in Kz by lia.
    unfold ug_kont, ug_head in HK. replace (S i =? 69)%nat with false in HK by (symmetry; apply Nat.eqb_neq; lia).
    lazymatch goal with |- evtA _ _ _ (MS ?R _ _ _ _ _ _) =>
      eapply evtA_eq; [ | eapply (HK m); ea_syn ] end.
    cbv delta [mkR]. repeat first [reflexivity | progress f_equal; try lia].
Qed.

(* [comment removed for export] *)
Lemma ug_iter : forall (i : nat) (QQ : machine_state -> Prop) (m : mem)
    (x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra,
  (i < 69)%nat ->
  mem_inv asegs m -> munch UGW m0 m -> wmono asegs m0 m ->
  stk asegs m lo (bv_unsigned sp + -176) ->
  ug_frame m j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  rw_cells asegs m 0xab430 [C8 (Z_to_bv 64 (2^60))] ->
  stk asegs m SHA_LO SHA_HI -> stk asegs m SHB_LO SHB_HI -> stk asegs m SHC_LO SHC_HI ->
  ug_kont (S i) QQ j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  evtA asegs P QQ
    (MS (mkR x1 Q gp tp t0 t1 t2 s0 (Z_to_bv 64 0x13f6a8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b3f4) (Z_to_bv 64 (64 * Z.of_nat i + A_GTAB)) (Z_to_bv 64 (2^61))
             (Z_to_bv 64 0xab3f0) (Z_to_bv 64 0xa6828) (Z_to_bv 64 0xab430) (Z_to_bv 64 0xab378)
             (Z_to_bv 64 0xadb78) (Z_to_bv 64 (69 - Z.of_nat i)) t3 t4 t5 t6)
        F0 (Z_to_bv 64 0x40ce0) fc0 None m (seg_rom asegs)).
Proof.
  intros until ra. intros Hi MI MU WM ST FR MUT SA SB SC HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (grec_wf i Hi) as (Wb8 & Ws8 & Ws & Wsum & Wb0 & Wlo & Whi & Wlen).
  pose proof (unreg_statics_transport _ _ _ G0 MU WM UGW_statics) as G.
  destruct (globals_tab_transport _ _ _ TAB0 MU WM UGW_tab i Hi) as (sz & nm & md & dy & lc & REC).
  unfold ug_frame in FR. unreg_statics_open G.
  (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. zstepA. zstepA. stepA. cbv beta.
  stepA. if_false.
  (* [comment removed for export] *)
  zstepA. stepA. if_true. stepA. if_false.
  (* [comment removed for export] *)
  stepA. stepA. zstepA. zstepA. zstepA. zstepA.
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  stepA. if_cases Kmem; zify_cond Kmem. 2:{ exfalso. rewrite ?unsigned_lit in Kmem by lia. lia. }
  clear Kmem.
  (* [comment removed for export] *)
  zstepA. replace (Z.land (gbeg i) 7) with 0 by (symmetry; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Wb8).
  stepA. if_false.
  apply rec_C8_CB8 in REC. stepA. rewrite firstn1_le8, zext_extract_le1. unfold zx8. apply rec_CB8_C8 in REC.
  zstepA. rewrite (land7_of_mod8 (gsrz i)) by lia.
  stepA. if_false.
  (* [comment removed for export] *)
  stepA. stepA. stepA. stepA. zstepA. stepA. cbv beta. stepA. if_false.
  (* [comment removed for export] *)
  stepA. stepA. stepA. zstepA. zstepA. zstepA. zstepA. zstepA. stepA. zstepA. zstepA. zstepA.
  assert (E1 : Z.shiftr (gbeg i) 3 = gbeg i / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (E2 : Z.shiftr (gbeg i + gsrz i + -8) 3 = gbeg i / 8 + gsrz i / 8 - 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. }
  rewrite E1, E2. clear E1 E2.
  match goal with |- context [Z_to_bv 64 (?x mod 18446744073709551616 - ?y mod 18446744073709551616)] =>
    replace (Z_to_bv 64 (x mod 18446744073709551616 - y mod 18446744073709551616)) with (Z_to_bv 64 (gsrz i / 8))
      by (f_equal; rewrite !Z.mod_small by lia; lia) end.
  stepA. if_cases Kth; zify_cond Kth. 2:{ exfalso. rewrite ?unsigned_lit in Kth by lia. lia. }
  clear Kth.
  (* [comment removed for export] *)
  stepA. zstepA.
  destruct (ginA i); cbn [rlo rhi] in Wlo, Whi.
  - destruct (stk_split _ _ _ (2147450880 + gbeg i / 8) _ SA ltac:(lia)) as [S1 S23].
    destruct (stk_split _ _ _ (2147450880 + gbeg i / 8 + gsrz i / 8) _ S23 ltac:(lia)) as [S2 S3]. clear S23 SA.
    destruct (stk_carve _ _ _ _ (Z.to_nat (gsrz i / 8)) S2 ltac:(lia)) as [_ [junk DST]]. clear S2.
    replace (2147450880 + gbeg i / 8 + gsrz i / 8 - Z.of_nat (Z.to_nat (gsrz i / 8))) with (2147450880 + gbeg i / 8) in DST by lia.
    stepA. (* [comment removed for export] *)
    callA (memset_specZ (2147450880 + gbeg i / 8) (gsrz i / 8) 0); [ | exact DST | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    { intros a k H1 H2; apply PSHA; lia. }
    lazymatch goal with H : rw_cells asegs ?mx (2147450880 + gbeg _ / 8) _ |- _ => rename H into DST' end.
    lazymatch type of DST' with rw_cells _ ?mx _ _ =>
      pose proof (stk_of_rw_cells _ _ _ _ DST') as S2'; cbn [cells_size csize Nat.add] in S2';
      replace (2147450880 + gbeg i / 8 + Z.of_nat (Z.to_nat (gsrz i / 8) + 0)) with (2147450880 + gbeg i / 8 + gsrz i / 8) in S2' by lia;
      pose proof (stk_merge _ _ _ _ _ S1 (stk_merge _ _ _ _ _ S2' S3 ltac:(lia)) ltac:(lia)) as SA; clear S1 S2' S3 DST' end.
    eapply (ug_iter_tail i); [exact Hi | | | | | unfold ug_frame; exact FR | | exact SA | | | exact REC | exact HK]; assumption.
  - destruct (stk_split _ _ _ (2147450880 + gbeg i / 8) _ SB ltac:(lia)) as [S1 S23].
    destruct (stk_split _ _ _ (2147450880 + gbeg i / 8 + gsrz i / 8) _ S23 ltac:(lia)) as [S2 S3]. clear S23 SB.
    destruct (stk_carve _ _ _ _ (Z.to_nat (gsrz i / 8)) S2 ltac:(lia)) as [_ [junk DST]]. clear S2.
    replace (2147450880 + gbeg i / 8 + gsrz i / 8 - Z.of_nat (Z.to_nat (gsrz i / 8))) with (2147450880 + gbeg i / 8) in DST by lia.
    stepA. (* [comment removed for export] *)
    callA (memset_specZ (2147450880 + gbeg i / 8) (gsrz i / 8) 0); [ | exact DST | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    { intros a k H1 H2; apply PSHB; lia. }
    lazymatch goal with H : rw_cells asegs ?mx (2147450880 + gbeg _ / 8) _ |- _ => rename H into DST' end.
    lazymatch type of DST' with rw_cells _ ?mx _ _ =>
      pose proof (stk_of_rw_cells _ _ _ _ DST') as S2'; cbn [cells_size csize Nat.add] in S2';
      replace (2147450880 + gbeg i / 8 + Z.of_nat (Z.to_nat (gsrz i / 8) + 0)) with (2147450880 + gbeg i / 8 + gsrz i / 8) in S2' by lia;
      pose proof (stk_merge _ _ _ _ _ S1 (stk_merge _ _ _ _ _ S2' S3 ltac:(lia)) ltac:(lia)) as SB; clear S1 S2' S3 DST' end.
    eapply (ug_iter_tail i); [exact Hi | | | | | unfold ug_frame; exact FR | | | exact SB | | exact REC | exact HK]; assumption.
Qed.

(* [comment removed for export] *)
Lemma ug_loop : forall (k i : nat) (QQ : machine_state -> Prop) (m : mem)
    (x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra,
  (i + k = 69)%nat ->
  mem_inv asegs m -> munch UGW m0 m -> wmono asegs m0 m ->
  stk asegs m lo (bv_unsigned sp + -176) ->
  ug_frame m j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  rw_cells asegs m 0xab430 [C8 (Z_to_bv 64 (2^60))] ->
  stk asegs m SHA_LO SHA_HI -> stk asegs m SHB_LO SHB_HI -> stk asegs m SHC_LO SHC_HI ->
  ug_kont 69 QQ j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  evtA asegs P QQ (ug_head i m x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof.
  induction k as [|k IH]; intros until ra; intros Hk MI MU WM ST FR MUT SA SB SC HK.
  - replace i with 69%nat by lia. eapply (HK m); ea_syn.
  - unfold ug_head. replace (i =? 69)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    eapply (ug_iter i QQ m); [lia | ea_syn .. |].
    unfold ug_kont. intros. eapply (IH (S i)); [lia | ea_syn .. ].
Qed.

End Walk.
End RC__4.
