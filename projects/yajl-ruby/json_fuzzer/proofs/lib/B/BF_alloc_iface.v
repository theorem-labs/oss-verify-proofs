(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_fakestack_rep B_slack5 B_bundle B_benv5 B_init5 B_balloc5 B_rtok5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_ALLOCATE : Z := 0x32a0c.
Definition A_INST : Z := 0xaaf58.
(* [comment removed for export] *)
Definition ASLACK : Z := 2^30.
Lemma ASLACK_covers : 4 * NMAXA + 2^20 + 2^23 + 3 * 4095 <= ASLACK.
Proof. unfold ASLACK, NMAXA. cbn. lia. Qed.
(* [comment removed for export] *)
Definition K_ALLOC : Z := 4096.

(* [comment removed for export] *)
Definition bst_key (len : Z) (ws : list word) : list Z := map bv_unsigned (firstn (Z.to_nat len) ws).

(* [comment removed for export] *)
Definition nbig_live (a : astate) : Z := Z.of_nat (length (List.filter (fun b => 64512 <? snd b) (live_blocks a))).

Section AllocIface.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).

(* [comment removed for export] *)
Definition AINV (a : astate) (m : mem) (mo : Model) : Prop :=
     ARep bsegs E0 (DepotR bsegs E0) a m /\ AWf E0 [] [] a /\ AKern E0 a mo /\ res_ok a /\ AQbound a /\ depot_inv E0 a /\ AsanBudget2.binv a
  /\ mem_inv bsegs m /\ rt_misc5 FSB0 PL0 E0 m
  /\ sstats_ok a                                   (* [comment removed for export] *)
  /\ csmall a.                                     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition abudget_pre (a : astate) (n : Z) : Prop :=
  0 <= as_nprim_ever a /\ 0 <= as_ndepot_ins a /\ 10000 * as_nprim_ever a + as_ndepot_ins a + acharge n <= kInitialCredit.

(* [comment removed for export] *)
Definition aacct (a a' : astate) (n : Z) : Prop :=
     as_nprim_ever a <= as_nprim_ever a' /\ as_ndepot_ins a <= as_ndepot_ins a' /\ zlen (as_residue a) <= zlen (as_residue a')
  /\ 10000 * as_nprim_ever a' + zlen (as_residue a') + as_ndepot_ins a' + arefund n
       <= 10000 * as_nprim_ever a + zlen (as_residue a) + as_ndepot_ins a + acharge n.

(* [comment removed for export] *)
Definition alloc_post_state (a a' : astate) (m m' : mem) (mo mo' : Model) (s : aps) (C C' n lo usp : Z) (key : list Z)
    (r : Z) (a0' : word) : Prop :=
     (* [comment removed for export] *)
     stk bsegs m' lo usp /\ wmono bsegs m m'
  /\ (exists W, munch W m m' /\ Forall (aw_ok E0 a a' lo usp) W
               /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W)
     (* [comment removed for export] *)
  /\ (exists fuel orc evs orc', arun fuel (amalloc_core E0 key n a) orc = Some (a', ONorm (Some r), evs, orc'))
  /\ AINV a' m' mo'
  /\ RTOKc (C - acharge n) (C' - ASLACK) (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ aacct a a' n
  /\ a0' = wz r /\ ablock_range ACONSTS r n
  /\ Permutation (live_blocks a') ((r, n) :: live_blocks a)
  /\ (exists junk, length junk = Z.to_nat n /\ rw_cells bsegs m' r [CB (Z.to_nat n) junk])
  /\ block_shadow bsegs m' A_SB r n.

(* [comment removed for export] *)
Definition allocate_srz_case (SIDE : aps -> Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps)
         (n lo B A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  SIDE s n ->
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> acharge n <= C -> ASLACK <= C' -> AINV a m mo -> abudget_pre a n ->
  0 < n <= 2^27 -> nbig_live a <= 8000 ->
  (* [comment removed for export] *)
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_ALLOC -> usp mod 16 = 0 ->
  tp = wz 0x5e1550 ->
  (* [comment removed for export] *)
  usp <= B -> B + 16 <= A -> A + 8 * zlen ws < 2^47 ->
  rw_cells bsegs m B [C8 (wz A); C8 (wz len)] -> u64arr bsegs m A ws -> 1 <= len <= zlen ws -> zlen ws <= 30 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate) (r : Z),
     alloc_post_state a a' m m' mo mo' s C C' n lo usp (bst_key len ws) r a0' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz n) (wz 8) (wz B) (wz 1) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_ALLOCATE) fc None m (seg_rom bsegs)) mo) K.

(* [comment removed for export] *)
Definition allocate_srz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps)
         (n lo B A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> acharge n <= C -> ASLACK <= C' -> AINV a m mo -> abudget_pre a n ->
  0 < n <= 2^27 -> nbig_live a <= 8000 ->
  (* [comment removed for export] *)
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_ALLOC -> usp mod 16 = 0 ->
  tp = wz 0x5e1550 ->
  (* [comment removed for export] *)
  usp <= B -> B + 16 <= A -> A + 8 * zlen ws < 2^47 ->
  rw_cells bsegs m B [C8 (wz A); C8 (wz len)] -> u64arr bsegs m A ws -> 1 <= len <= zlen ws -> zlen ws <= 30 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate) (r : Z),
     alloc_post_state a a' m m' mo mo' s C C' n lo usp (bst_key len ws) r a0' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz n) (wz 8) (wz B) (wz 1) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_ALLOCATE) fc None m (seg_rom bsegs)) mo) K.

Lemma allocate_srz_of_case : allocate_srz_case (fun _ _ => True) -> allocate_srz_stmt.
Proof. intros H. intro. intros. eapply H; eauto. Qed.

(* [comment removed for export] *)
Lemma allocate_srz_case_join : forall (S1 S2 S : aps -> Z -> Prop),
  (forall s n, S s n -> S1 s n \/ S2 s n) -> allocate_srz_case S1 -> allocate_srz_case S2 -> allocate_srz_case S.
Proof. intros S1 S2 S HS H1 H2. intro. intros. destruct (HS _ _ H) as [X|X]; [eapply H1| eapply H2]; eauto. Qed.
End AllocIface.
End RC__1.
