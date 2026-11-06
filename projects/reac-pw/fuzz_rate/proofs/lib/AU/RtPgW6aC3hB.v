(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 654 of its 695 lines of code are new or changed and 285 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC3h.v at e4c0f4bfc262; ported to
   reac-pw/fuzz_rate's image A: module paths changed; rate's pcs, floats table (0x21140) and registers (the input left
   in s8, the cursor in s9, the input left before the kind byte in a5, the shadow offset in s2, the reloaded shadow
   address in s6); one frame cell [R+0xe8] read instead of role's [R+0xb0] and [R+0xf8]; the post is RtPgSteps.v's
   rts_blk_post and the chaining its rts_blk_seq; AR_laws comes from the kit's AR_laws_ok instead of a Section
   hypothesis; the copy of RtPgSteps' st_ok_pin_sv is dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aC3h.v at 88912827c774 for the same unit's
   image B (fuzz_rate.asan-ubsan): images.AsanUbsan, lib/AU/RtPgStepsB.v and RtPgW6aBaseB.v; image B's pcs and
   registers (the cursor s2, what is left s6, s10 = c - 1, t1 = |r| + 1, a6 = 1, the shadow offset s4); the head also
   passes the pointer-overflow test of s2 (decided by the engine from s2's and a6's atom ranges); the cell [R+0x150]
   is read inside the check of s2 and again in the table's load block; the table part starts from the byte m in a1
   and holds the out-of-range test `bgeu` whose other arm is the `unimp` (split, its trap arm refuted over the 256
   values of m); the load block also sets a4 := 4; AR_laws is a Section hypothesis; the branch and index arithmetic
   are checked over the 256 values of m in an environment that maps the atom to m. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the proof of w6b_c3h
   (lib/AU/RtPgW6aBaseB.v), the head of ent_build's case 3 (pod.h:304-324) in LLVMFuzzerTestOneInput (0x8076c), from
   0x81838 to 0x81e94 (m odd) or 0x820c0 (m even). Proves no function (kind: segment lemma).

   THE CODE (the neutral listing of image B):
     0x81838  beqz s6 -> 0x81b54                 no byte left: 0x81b54 a2 := 0, a1 := 0x21140; j 0x81fa0
     0x8183c  a0 := s2 + 1; 0x81840 bltu a6,a0 -> 0x81848 (else 0x81844 j 0x83098, the `unimp`: never, c >= 2)
     0x81848 .. 0x81858  the shadow check of s2 (slow block 0x822b0), s6 := [R+0x150] inside it
     0x8185c  lbu a1,0(s2) (= m); a2 := t1 - 2; a3 := m & 1; s2 := s10 + 2; 0x8186c bnez a3 -> 0x81e94 (m odd)
     0x81870  a3 := 254; beq a1,a3 -> 0x81f60: a1 := 0x7fc00000; j 0x820bc
     0x81878  a3 := 252; bne a1,a3 -> 0x81f68; 0x81880 a1 := 0x7f800000; j 0x820bc
     0x820bc  li a4,4                            (then 0x820c0, the tail's second entry)
     0x81f68 .. 0x81f8c  a3 := 4 ((m >> 1) - mulhu(m >> 1, [0x10310]) * 21) = 4 ((m >> 1) % 21), a1 := 0x21140
     0x81f90  not a4,a1; 0x81f94 bgeu a4,a3 -> 0x81f9c (else 0x81f98 j 0x83098); 0x81f9c a1 := a1 + a3
     0x81fa0 .. 0x81fb4  the shadow check of a1, 4 bytes (slow block 0x82304, taken at floats[20]), with
                         s6 := [R+0x150] and a4 := 4 inside it
     0x81fb8  lw a1,0(a1); j 0x820c0
   THE BLOCKS. The engine's shadow token needs the checked address in the form (x >> 3) + s4 with x an atom; a
   literal or computed a1 would not show the engine that form. So the head is cut at 0x81fa0 (no byte) and 0x81f68
   (m even, not 0xfe / 0xfc), and the table part is two blocks:
     c3_blkT  0x81f68 -> 0x81fa0   a1 = m (an atom, 0 <= m < 256): a1 = 0x21140 + 4 ((m >> 1) % 21) (the constant at
                                    0x10310 a base-free image region); the `bgeu` stops the engine, is split, and its
                                    trap arm is false for every m
     c3_blkL  0x81fa0 -> 0x820c0   a1 = &floats[idx] as the register's own atom, the entry as a fresh atom in a
                                    4-byte region at a1, the cell [R+0x150] as a region at s1: the token engine
                                    follows the slow block and leaves the obligation range_addressable a1 4, paid
                                    from range_addressable W6B_FLOATS 84.
   The head runs over a one-byte region at the cursor s2 (the byte m a fresh atom) and the cell [R+0x150] as a
   region at s1; its three branches on m stop the engine and are split (srr_branch_tok), each arm rerun with the
   branch's condition as a fact. The shadow base is s4's own atom (SOff 20 0), pinned to SHADOW_OFF by a fact.
   Every atom bound in a state's facts is a closed numeral. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgW6aBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgStepsB.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the engine's context ======================================== *)
Definition C3Bx : sv := SOff 20 0.
Definition C3span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition C3_T : Z := 0x81f68.   (* the table part: a1 = m *)
Definition C3_L : Z := 0x81fa0.   (* the table entry's check: a1 = &floats[idx] *)

(* ======================================== arithmetic and image facts ======================================== *)
Lemma c3_all : forall (n : Z) (f g : Z -> Z),
forallb (fun j => f j =? g j) (map Z.of_nat (seq 0 (Z.to_nat n))) = true -> forall j, 0 <= j < n -> f j = g j.
Proof.
intros n f g H j Hj. rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia].
Qed.
Lemma c3_allb : forall (n : Z) (f g : Z -> bool),
forallb (fun j => Bool.eqb (f j) (g j)) (map Z.of_nat (seq 0 (Z.to_nat n))) = true -> forall j, 0 <= j < n -> f j = g j.
Proof.
intros n f g H j Hj. rewrite forallb_forall in H. apply Bool.eqb_prop. apply H.
apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia].
Qed.
Lemma c3_float_range : forall idx, 0 <= idx < 21 -> 0 <= nth (Z.to_nat idx) Tables.float_bits 0 < 2 ^ 32.
Proof.
intros idx Hidx.
assert (H1 : forall j, 0 <= j < 21 -> (fun j => if (0 <=? nth (Z.to_nat j) Tables.float_bits 0) &&
  (nth (Z.to_nat j) Tables.float_bits 0 <? 2 ^ 32) then 1 else 0) j = (fun _ => 1) j)
  by (apply (c3_all 21); vm_compute; reflexivity).
specialize (H1 idx Hidx). cbv beta in H1.
destruct (0 <=? nth (Z.to_nat idx) Tables.float_bits 0) eqn:A; [|discriminate H1].
destruct (nth (Z.to_nat idx) Tables.float_bits 0 <? 2 ^ 32) eqn:B'; [|discriminate H1].
apply Z.leb_le in A. apply Z.ltb_lt in B'. lia.
Qed.
(* the image's bytes of floats[idx] (.rodata 0x21140 + 4 idx) *)
Definition c3_fbyte_ok (idx : Z) (k : nat) : bool :=
let a := W6B_FLOATS + 4 * idx + Z.of_nat k in
in_rom_b a && YP08.img_byte_ok rsegs a &&
match img_byte rsegs a with
| Some b => bv_unsigned b =? bv_unsigned (Z_to_bv 8 (le_byte (nth (Z.to_nat idx) Tables.float_bits 0) 4 k))
| None => false
end.
Lemma c3_fbytes : forall idx, 0 <= idx < 21 -> forall k, (k < 4)%nat -> c3_fbyte_ok idx k = true.
Proof.
intros idx Hidx k Hk.
assert (H1 : forall j, 0 <= j < 21 -> (fun j => if forallb (c3_fbyte_ok j) (seq 0 4) then 1 else 0) j = (fun _ => 1) j)
  by (apply (c3_all 21); vm_compute; reflexivity).
specialize (H1 idx Hidx). cbv beta in H1.
destruct (forallb (c3_fbyte_ok idx) (seq 0 4)) eqn:A; [|discriminate H1].
rewrite forallb_forall in A. apply A. apply in_seq. lia.
Qed.
(* case 3's value on the table path (m even, not 0xfe / 0xfc) *)
Lemma c3_fe_tbl : forall m, 0 <= m < 256 -> Z.odd m = false -> m <> 254 -> m <> 252 ->
w6b_float_even m = nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0.
Proof.
intros m Hm Ho H1 H2.
pose proof (c3_all 256 (fun m => if negb (Z.odd m) && negb (m =? 254) && negb (m =? 252) then w6b_float_even m
  else nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0) (fun m => nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0)
  ltac:(vm_compute; reflexivity) m Hm) as A.
cbv beta in A. rewrite Ho, (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2) in A. exact A.
Qed.
(* every atom holds z: a register's value computed over all 256 values of the byte m *)
Definition c3_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c3_val256 : forall (e : sv) (f : Z -> Z),
forallb (fun j => bv_unsigned (sv_denot (c3_envz j) e) =? bv_unsigned (Z_to_bv 64 (f j))) (map Z.of_nat (seq 0 256)) = true ->
forall j, 0 <= j < 256 -> sv_denot (c3_envz j) e = Z_to_bv 64 (f j).
Proof.
intros e f H j Hj. apply bv_eq. apply Z.eqb_eq. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia].
Qed.

(* ======================================== engine helpers ======================================== *)
Lemma c3_agree_ewset : forall k E n v, (k <= n)%nat -> env_agree k E (ewset E n v).
Proof. intros k E n v Hk. split; [intros i Hi; apply ew_ewset_other; lia | reflexivity]. Qed.
Lemma c3_agree_trans : forall k E1 E2 E3, env_agree k E1 E2 -> env_agree k E2 E3 -> env_agree k E1 E3.
Proof. intros k E1 E2 E3 [A1 D1] [A2 D2]. split; [intros n Hn; rewrite A2 by lia; apply A1; lia | congruence]. Qed.
Lemma c3_agree_le : forall k k' E E', (k <= k')%nat -> env_agree k' E E' -> env_agree k E E'.
Proof. intros k k' E E' Hk [A D]. split; [intros n Hn; apply A; lia | exact D]. Qed.
(* the token atoms of a run sit at K and above: the env agrees with the run's start below K *)
Ltac c3_agree :=
lazymatch goal with
| |- env_agree ?k ?E (ewset ?X ?n ?v) =>
  apply (c3_agree_trans k E X (ewset X n v)); [c3_agree | apply c3_agree_ewset; lia]
| |- env_agree ?k ?E ?E1 => split; [intros; reflexivity | reflexivity]
end.
(* the lowest token atom of an env made by a run (dflt if the run made none) *)
Ltac c3_kof E1 dflt :=
lazymatch E1 with
| ewset ?X ?n _ => lazymatch X with ewset _ _ _ => c3_kof X dflt | _ => n end
| _ => dflt
end.
Lemma c3_den : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = w64 v.
Proof. intros E e v H Hv. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia. exact H. Qed.
Lemma c3_sext32_mod : forall fv, 0 <= fv < 2 ^ 32 -> zcanon (bv_swrap 32 fv) mod 2 ^ 32 = fv.
Proof.
intros fv Hfv. unfold zcanon, M64.
rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2 ^ 32); reflexivity].
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. replace (fv + 2 ^ 31 - 2 ^ 31) with fv by lia. apply Z.mod_small. lia.
Qed.
Lemma c3_bt_eq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by assumption. reflexivity. Qed.
Lemma c3_U_lt : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. pose proof (U_range E e) as H. unfold M64 in H. exact H. Qed.
Lemma c3_if_true : forall W c (P Q : world rsegs -> config -> Prop) (bb : bool),
bb = true -> SRr rsegs W c P -> SRr rsegs W c (fun W2 c2 => if bb then P W2 c2 else Q W2 c2).
Proof. intros W c P Q bb -> H. eapply SRr_mono; [exact H | intros W2 c2 _ HP; exact HP]. Qed.
Lemma c3_if_false : forall W c (P Q : world rsegs -> config -> Prop) (bb : bool),
bb = false -> SRr rsegs W c Q -> SRr rsegs W c (fun W2 c2 => if bb then P W2 c2 else Q W2 c2).
Proof. intros W c P Q bb -> H. eapply SRr_mono; [exact H | intros W2 c2 _ HP; exact HP]. Qed.
(* a run over regions without write windows keeps every byte *)
Lemma c3_kept : forall E rs (H : word -> bool) (m1 m2 : word -> option byte),
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 HF Hw a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). rewrite forallb_forall in Hw. specialize (Hw r Hin). apply Z.leb_le in Hw. lia.
Qed.
Lemma c3_rom_kept : forall (W W1 : world rsegs) m m1, rom_view rsegs W m ->
(forall a, aview rsegs (w_H W1) m1 a = aview rsegs (w_H W) m a) -> rom_view rsegs W1 m1.
Proof. intros W W1 m m1 HR K a Ha. rewrite K. exact (HR a Ha). Qed.
Lemma c3_ra_kept : forall (rd1 rd2 : reader) a n,
range_addressable rd1 SHADOW_OFF a n -> (forall x, rd2 x = rd1 x) -> range_addressable rd2 SHADOW_OFF a n.
Proof. intros rd1 rd2 a n H K x Hx. rewrite K. exact (H x Hx). Qed.
(* side conditions on register names *)
Ltac c3_nz := let X := fresh "X" in intros X; cbv in X; discriminate X.
Ltac c3_notin :=
let X := fresh "X" in intros X; cbn [app In] in X;
repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; cbv in X; discriminate X|]); exact X.
(* a branch the engine stops at, its operands over the atom n holding m: Hc's truth value read off for all 256 m
   as g m *)
Ltac c3_brz Hc n m Fn Hm g :=
lazymatch type of Hc with branch_taken ?bc (sv_denot ?E1 ?a) (sv_denot ?E1 ?b) = _ =>
  let Hbr := fresh "Hbr" in
  assert (Hbr : forall E', ew E' n = Z_to_bv 64 m ->
    branch_taken bc (sv_denot E' a) (sv_denot E' b) = branch_taken bc (sv_denot (c3_envz m) a) (sv_denot (c3_envz m) b))
    by (let E' := fresh "E'" in let H' := fresh "H'" in intros E' H'; cbn [sv_denot ew c3_envz]; rewrite ?H'; reflexivity);
  rewrite (Hbr E1 Fn) in Hc; clear Hbr;
  let Hg := fresh "Hg" in
  pose proof (c3_allb 256 (fun j => branch_taken bc (sv_denot (c3_envz j) a) (sv_denot (c3_envz j) b)) g
    ltac:(vm_compute; reflexivity) m Hm) as Hg;
  cbv beta in Hg; rewrite Hg in Hc; clear Hg
end.
(* a register's sv over the atom n holding m: its value for all 256 m as f m *)
Ltac c3_valz n m Fn Hm f :=
lazymatch goal with |- sv_denot ?E1 ?e = _ =>
  let Hbr := fresh "Hbr" in
  assert (Hbr : forall E', ew E' n = Z_to_bv 64 m -> sv_denot E' e = sv_denot (c3_envz m) e)
    by (let E' := fresh "E'" in let H' := fresh "H'" in intros E' H'; cbn [sv_denot ew c3_envz]; rewrite ?H'; reflexivity);
  rewrite (Hbr E1 Fn); clear Hbr;
  exact (c3_val256 e f ltac:(vm_compute; reflexivity) m Hm)
end.

(* ======================================== the blocks' states ======================================== *)
(* the load block: a1 = &floats[idx] (atom 11), the entry's 4 bytes the value of slot 32, the cell [R+0x150] the
   value of slot 33 *)
Definition c3_fl : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition c3_vb : YP09.region := YP09.mkRegion (Some 9%nat) 0x150 0x158 0 0 [YP09.mkChunk 0x150 (CVal 8 (SOff 33 0))].
Definition c3_GL : facts :=
mkFacts [(11%nat, mkAF 135488 135568 2); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition c3_ssL : sstate := mkSS C3_L sr_atoms [c3_fl; c3_vb] None c3_GL.
Definition c3_RL (idx F : Z) (regs2 : bvmap 5 word) : Prop :=
(exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat idx) Tables.float_bits 0) /\
getr regs2 14 = w64 4 /\ getr regs2 22 = w64 (F + 0x210).
(* the index block: a1 = m (atom 11), the 8-byte constant at 0x10310 a base-free image region *)
Definition c3_k21 : YP09.region := YP09.mkRegion None 0x10310 (0x10310 + 8) 0 0 [YP09.mkChunk 0x10310 (CImg 8)].
Definition c3_GT : facts := mkFacts [(11%nat, mkAF 0 255 0)] [] [].
Definition c3_ssT : sstate := mkSS C3_T sr_atoms [c3_k21] None c3_GT.
Definition c3_RT (m : Z) (regs2 : bvmap 5 word) : Prop := getr regs2 11 = w64 (W6B_FLOATS + 4 * ((m / 2) mod 21)).
Definition c3_RTL (m F : Z) (regs2 : bvmap 5 word) : Prop :=
(exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0) /\
getr regs2 14 = w64 4 /\ getr regs2 22 = w64 (F + 0x210).
(* the head with a byte left: m at c (slot 32), [R+0x150] = F + 0x210 (slot 33); a6 = 1 and s2 = c >= 2 decide
   the pointer-overflow test *)
Definition c3_in : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition c3_G1 : facts := mkFacts [(16%nat, mkAF 1 1 0); (18%nat, mkAF 2 140737488355326 0);
  (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (22%nat, mkAF 1 140737488355328 0); (32%nat, mkAF 0 255 0)] [] [].
Definition c3_ss1 : sstate := mkSS W6B_D3 sr_atoms [c3_vb; c3_in] None c3_G1.
Definition c3_extra (m vb : Z) : list word := [w64 m; w64 vb].
(* the head with no byte left: s6 = 0 *)
Definition c3_G0 : facts :=
mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (22%nat, mkAF 0 0 0)] [mkAC BC_EQ (SOff 22 0) (SLit 0)] [].
Definition c3_ss0 : sstate := mkSS W6B_D3 sr_atoms [] None c3_G0.

(* the value of floats[idx] in memory, from rom_view *)
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c3_floats_val : forall (W : world rsegs) memc idx, rom_view rsegs W memc -> 0 <= idx < 21 ->
val_mem rsegs (mrestrict (w_H W) memc) (W6B_FLOATS + 4 * idx) 4 (nth (Z.to_nat idx) Tables.float_bits 0).
Proof.
intros W memc idx HR Hidx k Hk.
pose proof (c3_fbytes idx Hidx k Hk) as Hb. unfold c3_fbyte_ok in Hb.
apply andb_prop in Hb as [Hb Hv]. apply andb_prop in Hb as [Hr Hi].
destruct (mbyte_rom W memc _ HR Hr Hi) as (b & Eb & Mb). rewrite Eb in Hv. apply Z.eqb_eq in Hv.
rewrite Mb. f_equal. apply bv_eq. exact Hv.
Qed.
End b0.

Ltac c3_kio := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
(* after a run: fold the run's frame into KE (every byte kept since the block's start) *)
Ltac c3_keep :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, aview _ _ _ a = aview _ _ _ a |- _ =>
  let KS := fresh "KS" in
  pose proof (fun a => eq_trans (c3_kept _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a) (KE a)) as KS;
  clear KE; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the symbolic value of register r in the run's last state *)
Ltac c3_regs HS :=
rewrite !(st_ok_restrict_reg rsegs (w_H _) _ _ _ _ HS);
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  repeat match goal with |- context [sr_get (ss_regs ssf) ?r] =>
    let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end end.
Ltac c3_ew HA1 H := first [exact H | rewrite (proj1 HA1) by lia; exact H].
Ltac c3_side HA H := first [c3_ew HA H | lia].
Ltac c3_rk HS HAE :=
eapply (regs_kept_of_st_ok rsegs _ _ _ _ _ (w_H _) _ HS);
[ eapply c3_agree_trans; [exact HAE | c3_agree] | vm_compute; reflexivity ].
Ltac c3_rkept HS HAE HA1 :=
eapply (regs_kept_of_st_ok rsegs _ _ _ _ _ (w_H _) _ HS);
[ eapply c3_agree_trans; [exact HAE | eapply c3_agree_le; [| exact HA1]; lia]
| vm_compute; reflexivity ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the engine's last state at a block's end pc gives rtsb_blk_post *)
Lemma c3_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob (Rr : bvmap 5 word -> Prop)
E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
Rr (ms_regs ms) ->
SRr rsegs W (mkCfg ms md) (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr E ss ms md HS Hrv Hpc HJ Hio Hregs Hkept HR.
apply SRr_ret. exists lyc, Sc, (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hregs|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split; [exact Hio|]. split; [apply mo_le_refl; exact MTL|]. split; [exact Hkept | exact HR].
Qed.
(* a block run from an intermediate state, read back against the block's start *)
Lemma c3_then : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc clob1 clob2 clob
(R1 R2 : bvmap 5 word -> Prop) regs1 mem1 md1,
same_io mdc md1 ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
(forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
(forall r, In r clob1 -> In r clob) -> (forall r, In r clob2 -> In r clob) ->
(forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob2 -> getr regs2 r = getr regs1 r) -> R1 regs2 -> R2 regs2) ->
SRr rsegs W (cfg_at rsegs pc0 regs1 mem1 md1)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 lyc Sc W mem1 md1 pc clob2 R1) ->
SRr rsegs W (cfg_at rsegs pc0 regs1 mem1 md1)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc clob1 clob2 clob R1 R2 regs1 mem1 md1
Hio1 Hr1 Hk1 Hc1 Hc2 HRR H.
eapply SRr_mono; [exact H|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr r Hr0 ltac:(intros X; apply Hn; apply Hc2; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply Hc1; exact X]|].
split; [exact Hf|]. split; [exact Hp|]. split; [eapply same_io_trans; [exact Hio1 | exact Hio]|].
split; [exact Hmo|]. split; [intros a; rewrite (Hm a); apply Hk1|].
exact (HRR regs2 Hr HR).
Qed.

(* ===================== c3_blkL: 0x81fa0 .. 0x820c0, the check of &floats[idx], s6, a4 and the load ===================== *)
Lemma c3_blkL : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (R F idx : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
rom_view rsegs W memc -> 0 <= idx < 21 ->
getr regs 11 = w64 (W6B_FLOATS + 4 * idx) -> getr regs 20 = w64 SHADOW_OFF -> getr regs 9 = w64 R ->
0x100000 <= R -> R + 0x220 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) -> 0 <= F + 0x210 < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs C3_L regs memc mdc)
(rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc W6B_TB3 [10; 11; 13; 14; 22]%bv (c3_RL idx F)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R F idx HJ HR Hidx H11 H20 H9 HRlo HRhi Hvb Hvb64 Hra.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
set (fv := nth (Z.to_nat idx) Tables.float_bits 0).
assert (Hfv : 0 <= fv < 2 ^ 32) by (apply c3_float_range; exact Hidx).
pose proof (c3_floats_val W memc idx HR Hidx) as Hval. fold fv in Hval.
set (E := Ereg regs [w64 fv; w64 (F + 0x210)]).
assert (E11 : ew E 11 = Z_to_bv 64 (W6B_FLOATS + 4 * idx)) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 fv) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (F + 0x210)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs E c3_ssL (restrict (w_H W) (mkst regs (Z_to_bv 64 C3_L) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs [w64 fv; w64 (F + 0x210)]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, c3_fl. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E11, unsigned_lit_small by (unfold W6B_FLOATS; lia).
      split; [unfold W6B_FLOATS; lia|]. split; [unfold W6B_FLOATS; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0 4 (SOff 32 0) fv).
      * apply c3_den; [apply (U_atom E 32 fv E32); lia | lia].
      * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * cbn. lia.
      * rewrite Z.add_0_r. exact Hval.
    + unfold region_ok, c3_vb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0x150 8 (SOff 33 0) (F + 0x210));
        [apply c3_den; [apply (U_atom E 33 (F + 0x210) E33); lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | cbn; lia | exact Hvb].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c3_fl, c3_vb.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E11, E9, !unsigned_lit_small by (unfold W6B_FLOATS; lia).
    unfold W6B_FLOATS. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]]. cbn [c3_GL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E11, E20, !unsigned_lit_small by (unfold W6B_FLOATS, SHADOW_OFF; lia).
    change (2 ^ 2) with 4. change (2 ^ 0) with 1. unfold W6B_FLOATS, SHADOW_OFF. repeat split; try lia; try apply Z.mod_1_r.
    replace (135488 + 4 * idx) with ((33872 + idx) * 4) by lia. apply Z.mod_mul. lia. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HB : U E C3Bx = SHADOW_OFF) by (apply (U_atom E 20 SHADOW_OFF E20); unfold SHADOW_OFF; lia).
assert (HA0 : U E (SOff 11 0) = W6B_FLOATS + 4 * idx) by (apply (U_atom E 11 _ E11); unfold W6B_FLOATS; lia).
assert (HAE : env_agree 32 (Ereg regs [w64 fv; w64 (F + 0x210)]) E) by (subst E; split; [intros; reflexivity | reflexivity]).
unfold cfg_at. change (w64 C3_L) with (Z_to_bv 64 C3_L).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_TB3.
- cbn [ms_mem mkst]. rewrite HA0.
  apply (obl_of_range rsegs (w_H W) memc E C3Bx (W6B_FLOATS + 4 * idx) 4 W6B_FLOATS 84 Hra HB); lia.
- awr_ok_tac.
- lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA1 : env_agree 34 E E1) by c3_agree end.
  eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | | |].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [w64 fv; w64 (F + 0x210)] (w_H W) _ HS);
      [exact (c3_agree_trans 32 _ _ _ HAE (c3_agree_le 32 34 _ _ ltac:(lia) HA1)) | vm_compute; reflexivity].
  + exact (c3_kept _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
  + unfold c3_RL. c3_regs HS.
    split; [|split].
    * lazymatch goal with |- exists v, sv_denot ?E1 ?e = _ /\ _ => exists (U E1 e) end.
      split; [rewrite <- denot_lit_U; reflexivity|].
      rewrite U_SExt. cbv iota.
      destruct HA1 as [HA1 _]. rewrite (U_atom _ 32 fv) by (try rewrite HA1 by lia; first [exact E32 | lia]).
      change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small fv) by lia. apply c3_sext32_mod. exact Hfv.
    * reflexivity.
    * apply c3_den; [apply (U_atom _ 33 (F + 0x210)); [c3_ew HA1 E33 | lia] | lia].
Qed.

(* ===================== c3_blkT: 0x81f68 .. 0x81fa0, &floats[(m >> 1) % 21] ===================== *)
Lemma c3_k21_rom : rom_run_b 0x10310 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c3_blkT : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (m : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
rom_view rsegs W memc -> 0 <= m < 256 -> getr regs 11 = w64 m ->
SRr rsegs W (cfg_at rsegs C3_T regs memc mdc)
(rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc C3_L [11; 13; 14; 15]%bv (c3_RT m)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs m HJ HR Hm H11.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
set (E := Ereg regs []).
assert (E11 : ew E 11 = Z_to_bv 64 m) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HS : st_ok rsegs E c3_ssT (restrict (w_H W) (mkst regs (Z_to_bv 64 C3_T) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply img_region_ok_rom; [exact HR | lia | lia | lia | exact c3_k21_rom].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [c3_GT f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E11, unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros; reflexivity | reflexivity]).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C3_T) with (Z_to_bv 64 C3_T).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span C3_L.
- awr_ok_tac.
- (* stuck at 0x81f94: `bgeu a4,a3`, the out-of-range test *)
  c3_keep.
  lazymatch type of HS with st_ok _ ?E1 _ _ =>
    assert (HA : env_agree 32 E E1) by c3_agree;
    assert (F11 : ew E1 11 = Z_to_bv 64 m) by (c3_ew HA E11) end.
  srr_branch_tok w6b_tbl_ok HS SHOK C3span.
  + (* taken: on to 0x81f9c *)
    clear Hc.
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span C3_L.
    * awr_ok_tac.
    * c3_keep.
      eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
      unfold c3_RT. c3_regs HS.
      lazymatch type of HS with st_ok _ ?E2 _ _ => assert (G11 : ew E2 11 = Z_to_bv 64 m) by (c3_ew HA E11) end.
      c3_valz 11%nat m G11 Hm (fun j => W6B_FLOATS + 4 * ((j / 2) mod 21)).
  + (* not taken: the `unimp`; the test holds for every m *)
    exfalso. c3_brz Hc 11%nat m F11 Hm (fun _ : Z => true). discriminate Hc.
Qed.

(* ===================== c3_blkTL: 0x81f68 .. 0x820c0 ===================== *)
Lemma c3_blkTL : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (R F m : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
rom_view rsegs W memc -> 0 <= m < 256 -> getr regs 11 = w64 m -> getr regs 20 = w64 SHADOW_OFF ->
getr regs 9 = w64 R -> 0x100000 <= R -> R + 0x220 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) -> 0 <= F + 0x210 < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs C3_T regs memc mdc)
(rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc W6B_TB3
  ([11; 13; 14; 15] ++ [10; 11; 13; 14; 22])%bv (c3_RTL m F)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R F m HJ HR Hm H11 H20 H9 HRlo HRhi Hvb Hvb64 Hra.
eapply (rtsb_blk_seq B MT MTL); [exact (c3_blkT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs m HJ HR Hm H11)|].
intros W1 ly1 S1 regs1 mem1 md1 Hw HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HRT.
pose proof (Z.mod_pos_bound (m / 2) 21 ltac:(lia)) as Hjm.
exact (c3_blkL STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k0 regs1 R F ((m / 2) mod 21) HJ1
  (c3_rom_kept W W1 memc mem1 HR Hm1) Hjm HRT
  (eq_trans (Hr1 20%bv ltac:(c3_nz) ltac:(c3_notin)) H20)
  (eq_trans (Hr1 9%bv ltac:(c3_nz) ltac:(c3_notin)) H9) HRlo HRhi
  (val_mem_kept rsegs (w_H W) (w_H W1) memc mem1 (R + 0x150) 8 (F + 0x210) (fun i _ => Hm1 (R + 0x150 + i)) Hvb)
  Hvb64 (c3_ra_kept _ _ W6B_FLOATS 84 Hra Hm1)).
Qed.

(* ===================== the head's two table entries ===================== *)
(* from 0x81fa0 with a1 = &floats[idx] (no byte left): the load block ends the case at 0x820c0 *)
Lemma c3_to_ld : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (Rr : bvmap 5 word -> Prop) E ss ms md
R F idx,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = C3_L ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6b_head_clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
rom_view rsegs W memc -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_FLOATS 84 ->
0 <= idx < 21 -> getr (ms_regs ms) 11 = w64 (W6B_FLOATS + 4 * idx) -> getr regs 20 = w64 SHADOW_OFF ->
getr regs 9 = w64 R -> 0x100000 <= R -> R + 0x220 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) -> 0 <= F + 0x210 < 2 ^ 64 ->
(forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [10; 11; 13; 14; 22]%bv -> getr regs2 r = getr (ms_regs ms) r) ->
  c3_RL idx F regs2 -> Rr regs2) ->
SRr rsegs W (mkCfg ms md) (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_TB3 w6b_head_clob Rr).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc Rr E ss ms md R F idx HS Hrv Hpc HJ Hio Hregs Hkept HR Hra
Hidx H11 H20 H9 HRlo HRhi Hvb Hvb64 HRR.
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 C3_L) (ms_mem ms) (seg_rom rsegs))
  by (rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv)).
rewrite Ems at 1.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 C3_L) (ms_mem ms) (seg_rom rsegs)) md)
  with (cfg_at rsegs C3_L (ms_regs ms) (ms_mem ms) md).
apply (c3_then STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C3_L W6B_TB3 w6b_head_clob [10; 11; 13; 14; 22]%bv
  w6b_head_clob (c3_RL idx F) Rr (ms_regs ms) (ms_mem ms) md Hio Hregs Hkept (fun r H => H)); [|exact HRR|].
- intros r Hr. cbn [In] in Hr. unfold w6b_head_clob. cbn [In]. tauto.
- exact (c3_blkL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k (ms_regs ms) R F idx HJ
    (c3_rom_kept W W memc (ms_mem ms) HR Hkept) Hidx H11
    (eq_trans (Hregs 20%bv ltac:(c3_nz) ltac:(unfold w6b_head_clob; c3_notin)) H20)
    (eq_trans (Hregs 9%bv ltac:(c3_nz) ltac:(unfold w6b_head_clob; c3_notin)) H9) HRlo HRhi
    (val_mem_kept rsegs (w_H W) (w_H W) memc (ms_mem ms) (R + 0x150) 8 (F + 0x210) (fun i _ => Hkept (R + 0x150 + i)) Hvb)
    Hvb64 (c3_ra_kept _ _ _ _ Hra Hkept)).
Qed.
(* from 0x81f68 with a1 = m: the two table blocks end the case at 0x820c0 *)
Lemma c3_to_tbl : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (Rr : bvmap 5 word -> Prop) E ss ms md
R F m,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = C3_T ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6b_head_clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
rom_view rsegs W memc -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_FLOATS 84 ->
0 <= m < 256 -> getr (ms_regs ms) 11 = w64 m -> getr regs 20 = w64 SHADOW_OFF ->
getr regs 9 = w64 R -> 0x100000 <= R -> R + 0x220 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) -> 0 <= F + 0x210 < 2 ^ 64 ->
(forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r ([11; 13; 14; 15] ++ [10; 11; 13; 14; 22])%bv ->
  getr regs2 r = getr (ms_regs ms) r) -> c3_RTL m F regs2 -> Rr regs2) ->
SRr rsegs W (mkCfg ms md) (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_TB3 w6b_head_clob Rr).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc Rr E ss ms md R F m HS Hrv Hpc HJ Hio Hregs Hkept HR Hra
Hm H11 H20 H9 HRlo HRhi Hvb Hvb64 HRR.
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 C3_T) (ms_mem ms) (seg_rom rsegs))
  by (rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv)).
rewrite Ems at 1.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 C3_T) (ms_mem ms) (seg_rom rsegs)) md)
  with (cfg_at rsegs C3_T (ms_regs ms) (ms_mem ms) md).
apply (c3_then STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C3_T W6B_TB3 w6b_head_clob
  ([11; 13; 14; 15] ++ [10; 11; 13; 14; 22])%bv w6b_head_clob (c3_RTL m F) Rr (ms_regs ms) (ms_mem ms) md Hio Hregs Hkept
  (fun r H => H)); [|exact HRR|].
- intros r Hr. cbn [app In] in Hr. unfold w6b_head_clob. cbn [In]. tauto.
- exact (c3_blkTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k (ms_regs ms) R F m HJ
    (c3_rom_kept W W memc (ms_mem ms) HR Hkept) Hm H11
    (eq_trans (Hregs 20%bv ltac:(c3_nz) ltac:(unfold w6b_head_clob; c3_notin)) H20)
    (eq_trans (Hregs 9%bv ltac:(c3_nz) ltac:(unfold w6b_head_clob; c3_notin)) H9) HRlo HRhi
    (val_mem_kept rsegs (w_H W) (w_H W) memc (ms_mem ms) (R + 0x150) 8 (F + 0x210) (fun i _ => Hkept (R + 0x150 + i)) Hvb)
    Hvb64 (c3_ra_kept _ _ _ _ Hra Hkept)).
Qed.

(* ===================== the head: 0x81838 .. 0x81e94 / 0x820c0 / 0x81fa0 / 0x81f68 ===================== *)
(* no byte left: s6 = 0, 0x81b54 a2 := 0, a1 := 0x21140, to 0x81fa0, then floats[0] *)
Lemma c3_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z),
w6b_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6b_head_in W memc regs R F c [] ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs W6B_D3 regs memc mdc)
(fun W2 c2 => if Z.odd 0 then
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_U3 w6b_head_clob
  (fun regs2 => getr regs2 12 = w64 (Z.of_nat (length (@nil byte))) /\ getr regs2 18 = w64 (c + 1) /\
     getr regs2 22 = w64 (F + 0x210)) W2 c2
 else
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_TB3 w6b_head_clob
  (fun regs2 => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = w6b_float_even 0 mod 2 ^ 32) /\
     getr regs2 14 = w64 4 /\
     getr regs2 12 = w64 (Z.of_nat (length (@nil byte))) /\
     getr regs2 18 = w64 (c + Z.of_nat (length (@nil byte) - length (@nil byte))) /\
     getr regs2 22 = w64 (F + 0x210)) W2 c2).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c
(HJ & HR16 & HRsp & HRstk & Hown & HF & HR) (H9 & H20 & H18 & H22 & H26 & H6 & H16 & Hvb & Hvb64 & Hc1 & Hin) Hra.
eapply c3_if_false; [reflexivity|].
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in HRstk.
assert (HRlo : 0x100000 <= R) by lia.
assert (HRhi : R + 0x220 <= 2 ^ 64) by lia.
set (E := Ereg regs []).
assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
destruct Hin as (_ & _ & Hc0 & Hchi & Hamem & _). cbn [length] in Hchi.
assert (HS : st_ok rsegs E c3_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D3) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [|exact I]].
    + cbn [c3_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E20, E22, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. unfold SHADOW_OFF. repeat split; try lia; try apply Z.mod_1_r.
    + cbn [c3_G0 f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite (denot_lit_U E (SOff 22 0)), (denot_lit_U E (SLit 0)), c3_bt_eq by apply c3_U_lt.
      rewrite U_SLit, (U_atom E 22 0 E22) by lia. reflexivity. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros; reflexivity | reflexivity]).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 W6B_D3) with (Z_to_bv 64 W6B_D3).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span C3_L.
- awr_ok_tac.
- c3_keep.
  lazymatch type of HS with st_ok _ ?E1 _ _ => let kk := c3_kof E1 32%nat in assert (HA1 : env_agree kk E E1) by c3_agree end.
  eapply c3_to_ld with (idx := 0) (R := R) (F := F);
    [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rkept HS HAE HA1 | exact KE | exact HR
    | exact Hra | lia | | exact H20 | exact H9 | exact HRlo | exact HRhi | exact Hvb | exact Hvb64 |].
  + c3_regs HS. reflexivity.
  + intros regs2 Hk ((v & Hv11 & Hvm) & H14' & H22').
    rewrite (Hk 12%bv ltac:(c3_nz) ltac:(c3_notin)), (Hk 18%bv ltac:(c3_nz) ltac:(c3_notin)).
    c3_regs HS. cbn [length]. replace (c + Z.of_nat (0 - 0)) with c by lia.
    split; [exists v; split; [exact Hv11 | rewrite Hvm; vm_compute; reflexivity]|].
    split; [exact H14'|]. split; [reflexivity|]. split; [|exact H22'].
    apply c3_den; [|lia]. apply (U_atom _ 18 c); [c3_ew HA1 E18 | lia].
Qed.

(* a byte left: the pointer-overflow test and the check of s2, m = lbu, the three branches on m *)
Lemma c3_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z)
(bb : byte) (r' : list byte),
w6b_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6b_head_in W memc regs R F c (bb :: r') ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs W6B_D3 regs memc mdc)
(fun W2 c2 => if Z.odd (bv_unsigned bb) then
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_U3 w6b_head_clob
  (fun regs2 => getr regs2 12 = w64 (Z.of_nat (length r')) /\ getr regs2 18 = w64 (c + 1) /\
     getr regs2 22 = w64 (F + 0x210)) W2 c2
 else
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_TB3 w6b_head_clob
  (fun regs2 => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = w6b_float_even (bv_unsigned bb) mod 2 ^ 32) /\
     getr regs2 14 = w64 4 /\
     getr regs2 12 = w64 (Z.of_nat (length r')) /\
     getr regs2 18 = w64 (c + Z.of_nat (length (bb :: r') - length r')) /\
     getr regs2 22 = w64 (F + 0x210)) W2 c2).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c bb r'
(HJ & HR16 & HRsp & HRstk & Hown & HF & HR) (H9 & H20 & H18 & H22 & H26 & H6 & H16 & Hvb & Hvb64 & Hc1 & Hin) Hra.
assert (Hm : 0 <= bv_unsigned bb < 256) by apply Cursor.byte_range.
assert (Hj2 : 0 <= bv_unsigned bb / 2 < 128)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hjm : 0 <= (bv_unsigned bb / 2) mod 21 < 21) by (apply Z.mod_pos_bound; lia).
assert (Hlen : Z.of_nat (length (bb :: r')) = Z.of_nat (length r') + 1) by (cbn [length]; lia).
destruct Hin as (Hg & Hrin & Hc0 & Hchi & Hamem & Hdisj).
rewrite Hlen in H22, H6, Hrin, Hchi, Hamem, Hdisj.
replace (Z.of_nat (length r') + 1 + 1) with (Z.of_nat (length r') + 2) in H6 by lia.
assert (Hnl0 : 0 <= Z.of_nat (length r')) by lia.
set (m := bv_unsigned bb) in *. set (nl := Z.of_nat (length r')) in *.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in HRstk.
assert (HRlo : 0x100000 <= R) by lia.
assert (HRhi : R + 0x220 <= 2 ^ 64) by lia.
assert (Hbnd : c + (nl + 1) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem; lia).
assert (Hmv : val_mem rsegs (mrestrict (w_H W) memc) c 1 m).
{ destruct (Hg 0%nat ltac:(rewrite length_map; cbn [length]; lia)) as [Hv _].
  rewrite Z.add_0_r in Hv. cbn [map nth] in Hv. exact Hv. }
pose proof (Hdisj c ltac:(lia)) as (_ & Hdc). clear Hdisj.
set (E := Ereg regs (c3_extra m (F + 0x210))).
assert (E6 : ew E 6 = Z_to_bv 64 (nl + 2)) by (subst E; rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E16 : ew E 16 = Z_to_bv 64 1) by (subst E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 (nl + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (F + 0x210)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs E c3_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D3) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs (c3_extra m (F + 0x210))) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, c3_vb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0x150 8 (SOff 33 0) (F + 0x210));
        [apply c3_den; [apply (U_atom E 33 (F + 0x210) E33); lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | cbn; lia | exact Hvb].
    + unfold region_ok, c3_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E18, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0 1 (SOff 32 0) m);
        [apply c3_den; [apply (U_atom E 32 m E32); lia | lia] | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia
        | rewrite Z.add_0_r; exact Hmv].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c3_vb, c3_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E18, !unsigned_lit_small by lia.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]]. cbn [c3_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E16, E18, E20, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. unfold SHADOW_OFF. repeat split; try lia; try apply Z.mod_1_r. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HB : U E C3Bx = SHADOW_OFF) by (apply (U_atom E 20 SHADOW_OFF E20); unfold SHADOW_OFF; lia).
assert (HAE : env_agree 32 (Ereg regs (c3_extra m (F + 0x210))) E) by (subst E; split; [intros; reflexivity | reflexivity]).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 W6B_D3) with (Z_to_bv 64 W6B_D3).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_U3.
- cbn [ms_mem mkst]. rewrite (U_atom E 18 c E18) by lia.
  apply (obl_of_range rsegs (w_H W) memc E C3Bx c 1 c (nl + 1) Hrin HB); lia.
- awr_ok_tac.
- (* stuck at 0x8186c: m odd? *)
  c3_keep.
  lazymatch type of HS with st_ok _ ?E1 _ _ =>
    assert (HA : env_agree 34 E E1) by c3_agree;
    assert (F32 : ew E1 32 = Z_to_bv 64 m) by (c3_ew HA E32) end.
  srr_branch_tok w6b_tbl_ok HS SHOK C3span.
  + (* m odd: stop at 0x81e94 *)
    c3_brz Hc 32%nat m F32 Hm (fun j : Z => Z.odd j).
    eapply c3_if_true; [exact Hc|].
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_U3.
    * awr_ok_tac.
    * c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 34 E E1) by c3_agree end.
      eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
      c3_regs HS. split; [|split].
      -- apply c3_den; [rewrite (U_atom_off _ 6 (nl + 2) (-2)) by c3_side HA E6; lia | lia].
      -- apply c3_den; [rewrite (U_atom_off _ 26 (c - 1) 2) by c3_side HA E26; lia | lia].
      -- apply c3_den; [apply (U_atom _ 33 (F + 0x210)); [c3_ew HA E33 | lia] | lia].
  + (* m even *)
    c3_brz Hc 32%nat m F32 Hm (fun j : Z => Z.odd j).
    eapply c3_if_false; [exact Hc|]. rename Hc into Hodd.
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_TB3; [awr_ok_tac|]. c3_keep.
    srr_branch_tok w6b_tbl_ok HS SHOK C3span.
    * (* m = 0xfe: NaN, through 0x820bc *)
      c3_brz Hc 32%nat m F32 Hm (fun j : Z => j =? 254).
      apply Z.eqb_eq in Hc.
      aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_TB3.
      -- awr_ok_tac.
      -- c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 34 E E1) by c3_agree end.
         eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
         c3_regs HS. replace (Z.of_nat (length (bb :: r') - length r')) with 1 by (cbn [length]; lia).
         split; [|split; [|split; [|split]]].
         ++ exists 2143289344. split; [reflexivity|]. rewrite Hc. vm_compute. reflexivity.
         ++ reflexivity.
         ++ apply c3_den; [rewrite (U_atom_off _ 6 (nl + 2) (-2)) by c3_side HA E6; lia | lia].
         ++ apply c3_den; [rewrite (U_atom_off _ 26 (c - 1) 2) by c3_side HA E26; lia | lia].
         ++ apply c3_den; [apply (U_atom _ 33 (F + 0x210)); [c3_ew HA E33 | lia] | lia].
    * (* m <> 0xfe *)
      c3_brz Hc 32%nat m F32 Hm (fun j : Z => j =? 254).
      apply Z.eqb_neq in Hc. rename Hc into H254.
      aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_TB3; [awr_ok_tac|]. c3_keep.
      srr_branch_tok w6b_tbl_ok HS SHOK C3span.
      -- (* m <> 0xfc: the table *)
         c3_brz Hc 32%nat m F32 Hm (fun j : Z => negb (j =? 252)).
         apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. rename Hc into H252.
         aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span C3_T.
         ++ awr_ok_tac.
         ++ c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 34 E E1) by c3_agree end.
            eapply c3_to_tbl with (m := m) (R := R) (F := F);
              [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE | exact HR
              | exact Hra | exact Hm | | exact H20 | exact H9 | exact HRlo | exact HRhi | exact Hvb | exact Hvb64 |].
            ** c3_regs HS. apply c3_den; [apply (U_atom _ 32 m); [c3_ew HA E32 | lia] | lia].
            ** intros regs2 Hk ((v & Hv11 & Hvm) & H14' & H22').
               rewrite (Hk 12%bv ltac:(c3_nz) ltac:(c3_notin)), (Hk 18%bv ltac:(c3_nz) ltac:(c3_notin)).
               c3_regs HS. replace (Z.of_nat (length (bb :: r') - length r')) with 1 by (cbn [length]; lia).
               split; [|split; [exact H14'|split; [|split; [|exact H22']]]].
               --- exists v. split; [exact Hv11|]. rewrite Hvm, (c3_fe_tbl m Hm Hodd H254 H252).
                   symmetry. apply Z.mod_small. apply c3_float_range. exact Hjm.
               --- apply c3_den; [rewrite (U_atom_off _ 6 (nl + 2) (-2)) by c3_side HA E6; lia | lia].
               --- apply c3_den; [rewrite (U_atom_off _ 26 (c - 1) 2) by c3_side HA E26; lia | lia].
      -- (* m = 0xfc: inf, through 0x820bc *)
         c3_brz Hc 32%nat m F32 Hm (fun j : Z => negb (j =? 252)).
         apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
         aj_run_to_tok w6b_tbl_ok HS HJ SHOK C3span W6B_TB3.
         ++ awr_ok_tac.
         ++ c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 34 E E1) by c3_agree end.
            eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
            c3_regs HS. replace (Z.of_nat (length (bb :: r') - length r')) with 1 by (cbn [length]; lia).
            split; [|split; [|split; [|split]]].
            ** exists 2139095040. split; [reflexivity|]. rewrite Hc. vm_compute. reflexivity.
            ** reflexivity.
            ** apply c3_den; [rewrite (U_atom_off _ 6 (nl + 2) (-2)) by c3_side HA E6; lia | lia].
            ** apply c3_den; [rewrite (U_atom_off _ 26 (c - 1) 2) by c3_side HA E26; lia | lia].
            ** apply c3_den; [apply (U_atom _ 33 (F + 0x210)); [c3_ew HA E33 | lia] | lia].
Qed.

(* ===================== the theorem ===================== *)
Lemma w6b_c3h : w6b_c3h_stmt B MT.
Proof using MTL LAWS.
unfold w6b_c3h_stmt, w6b_case_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c r Hctx Hin Hra.
destruct r as [|bb r'].
- exact (c3_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c Hctx Hin Hra).
- exact (c3_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c bb r' Hctx Hin Hra).
Qed.

End d.
End b.

Print Assumptions w6b_c3h.
