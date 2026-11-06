(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_unwind AF_depot1 AF_depot2 AF_depot3 AF_depot6.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanState AsanOps AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac cstep := stepA; try first [if_true | if_false].
(* [comment removed for export] *)
Ltac is_lit t := idtac; lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | ?x + ?y => is_lit x; is_lit y | ?x * ?y => is_lit x; is_lit y | ?x - ?y => is_lit x; is_lit y | - ?x => is_lit x
  | Z.land ?x ?y => is_lit x; is_lit y | Z.lor ?x ?y => is_lit x; is_lit y | Z.lxor ?x ?y => is_lit x; is_lit y
  | Z.shiftl ?x ?y => is_lit x; is_lit y | Z.shiftr ?x ?y => is_lit x; is_lit y | ?x mod ?y => is_lit x; is_lit y
  | Z.b2z (?x <? ?y) => is_lit x; is_lit y | Z.b2z (?x =? ?y) => is_lit x; is_lit y end.
Ltac is_num t := idtac; lazymatch t with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac evalc e := is_lit e; assert_fails (is_num e); let v := eval vm_compute in e in change e with v.
Ltac litc :=
  repeat match goal with
  | |- context [Z.b2z ?c] => evalc (Z.b2z c)
  | |- context [?a mod 18446744073709551616] => evalc (a mod 18446744073709551616)
  | |- context [?a mod 256] => evalc (a mod 256)
  | |- context [Z.land ?a ?b] => evalc (Z.land a b)
  | |- context [Z.lor ?a ?b] => evalc (Z.lor a b)
  | |- context [Z.lxor ?a ?b] => evalc (Z.lxor a b)
  end; rewrite ?Z.add_0_r, ?Z.add_0_l.
Ltac pg := match goal with |- ?g => idtac g end.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
(* [comment removed for export] *)
Lemma land_pow2_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k) = 0.
Proof.
  intros x k Hk Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k n) as [<-|NE]; [| apply andb_false_r].
  rewrite andb_true_r. apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma lxor_pow2_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.lxor x (2^k) = x + 2^k.
Proof. intros x k Hk Hx. symmetry. apply Z.add_nocarry_lxor. apply land_pow2_small; assumption. Qed.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section PUTS.
Variable P : acc -> Prop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo hi A len : Z) (ws : list word) (HS : list Z) (N : Z).
(* [comment removed for export] *)
Variables (blk fr : Z) (SBL : list Z).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation h := (AF_depot6.h len ws).
#[local] Notation bkt := (AF_depot6.bkt len ws).
#[local] Notation head := (AF_depot6.head len ws HS).
#[local] Notation TBA := (AF_depot6.TBA len ws).
Definition NA : Z := blk + 16 * ((N + 1) mod kDepotNodesPerBlock).
Definition count : Z := len + 1.
Definition b : Z := fr / kStoreBlockFrames.
Definition straddles : bool := negb (fr mod kStoreBlockFrames + count <=? kStoreBlockFrames).
Definition in_first : Z := kStoreBlockFrames - fr mod kStoreBlockFrames.
(* [comment removed for export] *)
Definition fst_start : Z := if straddles then fr + count else fr.
Definition bF : Z := if straddles then b + 1 else b.
Definition fr_end : Z := fst_start + count.
Definition packv : Z := if straddles then 1 else 0.
Definition BI (k : Z) : Z := SS + 16 + 16 * k.

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 640.
Hypothesis SPH : usp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis LEN : 1 <= len <= Z.of_nat (length ws).
Hypothesis LWS : Z.of_nat (length ws) <= 30.
Hypothesis TA : usp <= A /\ A + 8 * Z.of_nat (length ws) <= hi.
Hypothesis HN : 0 <= N /\ N + 2 < 2^31.
Hypothesis BLKR : placed blk kDepotNodeBlockBytes /\ blk mod 16 = 0.                (* [comment removed for export] *)
Hypothesis FR0 : 0 <= fr.
Hypothesis FR32 : fr + 64 <= 2^32.
Hypothesis FRB : b + 1 < kStoreBlockCount.
Hypothesis FRLE : fr <= kStoreBlockFrames * zlen SBL.                 (* [comment removed for export] *)
Hypothesis SBLR : forall sb, In sb SBL -> 0x603000 <= sb /\ sb + kStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= hi -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PNA : forall a n, NA <= a -> a + Z.of_nat n <= NA + 16 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Definition store_frame (j : list byte) (pack : Z) : list cell :=
  [CB 8 j; C8 (Z_to_bv 64 pack); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x7418c)].                 (* [comment removed for export] *)
Definition Store_frame (idx : Z) : list cell :=                                                (* [comment removed for export] *)
  [C8 (Z_to_bv 64 idx); C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 (TD + 0x400008)); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 TBA);
   C8 (Z_to_bv 64 NA); C8 (Z_to_bv 64 NA); C8 (Z_to_bv 64 0x73ca8)].
Definition Alloc_frame : list cell := [C8 (Z_to_bv 64 (usp - 136)); C8 (Z_to_bv 64 0x719e0)].

(* [comment removed for export] *)
Definition alloc_regs (pc_ra : word) (x5 x6 x7 x10 x14 x16 x17 x28 x29 x30 x31 : word) (s0v : Z) : bvmap 5 word :=
  mkR pc_ra (Z_to_bv 64 (usp - 224)) gp tp x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 SS) x10 (Z_to_bv 64 SS) (Z_to_bv 64 (usp - 208))
      (Z_to_bv 64 (usp - 136)) x14 (Z_to_bv 64 count) x16 x17
      (Z_to_bv 64 count) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1))
      (Z_to_bv 64 (TD + 0x400010)) (Z_to_bv 64 head) s10 s11 x28 x29 x30 x31.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma put_sa : forall (rax x11 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m : mem) (j8 : list byte) (j0 j1 j2 : word),
  stk asegs m lo (usp - 112) -> mem_inv asegs m ->
  rw_cells asegs m (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8) ->
  rw_cells asegs m NA [C8 j0; C4 j1; C4 j2] ->
  evtA asegs P (fun ms' => exists (x5 x6 x7 x14 x16 x17 x28 x29 x30 x31 : word) (js : list byte) m',
      ms' = MS (alloc_regs (Z_to_bv 64 0x719e0) x5 x6 x7 (Z_to_bv 64 SS) x14 x16 x17 x28 x29 x30 x31 (usp - 136)) F (Z_to_bv 64 0x71aa0) fc None m' (seg_rom asegs)
      /\ munch [(usp - 224, usp); (NA, NA + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (usp - 224)
      /\ rw_cells asegs m' (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8)
      /\ rw_cells asegs m' (usp - 144) (store_frame js 0)
      /\ rw_cells asegs m' (usp - 208) (Store_frame 0)
      /\ rw_cells asegs m' (usp - 224) Alloc_frame
      /\ rw_cells asegs m' NA [C8 (Z_to_bv 64 h); C4 j1; C4 j2])
    (MS (put_regs sp gp tp s10 s11 len ws HS N rax (Z_to_bv 64 blk) x11 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7416c) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until j2. intros SK MI FR NEWN.
  pose proof LOC as LOC0. aceil.
  pose proof BLKR as [(BR1 & BR2 & BR3) BR16]. aceil. unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in BR1, BR2, BR3. unfold kDepotNodeBlockBytes in BR2, BR3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= usp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  pose proof (depot_hash_range (AF_depot6.keyZ len ws)) as HR. change (depot_hash (AF_depot6.keyZ len ws)) with h in HR.
  pose proof (Z.mod_pos_bound (N + 1) kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)) as MB.
  assert (HNA : NA = blk + 16 * ((N + 1) mod kDepotNodesPerBlock)) by reflexivity.
  assert (NAR : 0x603000 <= NA /\ NA + 16 <= alloc_ceiling) by (rewrite HNA; unfold kDepotNodesPerBlock in *; lia).
  assert (MU : munch [(usp - 224, usp); (NA, NA + 8)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  unfold put_regs, put_frame in *. unfold AF_depot6.TBA, TD, SS in *.
  change (1636952 + 4194312) with 5831264. change (1636952 + 4194320) with 5831272.
  do 2 zstepA. (* [comment removed for export] *)
  change 65535 with (Z.ones 16). rewrite (Z.land_ones (N + 1) 16) by lia. change (2^16) with kDepotNodesPerBlock.
  replace (Z_to_bv 64 (Z.shiftl ((N + 1) mod kDepotNodesPerBlock) 4)) with (Z_to_bv 64 (16 * ((N + 1) mod kDepotNodesPerBlock)))
    by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstepA.      (* [comment removed for export] *)
  change (Z.ones 16) with 65535. rewrite <- HNA.
  do 4 cstep.  (* [comment removed for export] *)
  cstep.       (* [comment removed for export] *)
  (* [comment removed for export] *)
  rename FR into FRP. carve_frame 32%nat SK. replace (usp + -112 + -32) with (usp + -144) in * by lia.
  do 3 cstep.    (* [comment removed for export] *)
  do 2 cstep.    (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PNA; lia end.
  cstep.         (* [comment removed for export] *)
  do 3 cstep.    (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  (* [comment removed for export] *)
  rename FR into FR1. carve_frame 64%nat SK. replace (usp + -144 + -64) with (usp + -208) in * by lia.
  do 8 cstep.    (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply rw_cells_app_split with (cs1 := [CB 8 j8]) in FRP. destruct FRP as [FRa FRb]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRb.
  apply rw_cells_app_split with (cs1 := [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 len)]) in FRb. destruct FRb as [ARGS FRc].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRc.
  replace (Z_to_bv 64 len) with (Z_to_bv 64 (len + 2^32 * 0)) in ARGS by (f_equal; lia).
  apply (rw_cells_app_split asegs _ _ [C8 (Z_to_bv 64 A)] [C8 (Z_to_bv 64 (len + 2^32 * 0))]) in ARGS. destruct ARGS as [ARG1 ARG2].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in ARG2.
  apply rw_cells_c8_split in ARG2; [| lia| lia].
  replace (usp + -112 + Z.of_nat 8 + Z.of_nat 8) with (usp + -96) in ARG2 by lia.
  replace (usp + -112 + Z.of_nat 8) with (usp + -104) in ARG1 by lia.
  replace (usp + -112 + Z.of_nat 8 + Z.of_nat 16) with (usp + -88) in FRc by lia.
  cstep.         (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  assert (SX : sx32 (Z_to_bv 64 len) = Z_to_bv 64 len).
  { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
  rewrite ?SX. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  zstepA.        (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?Z.lor_0_r, ?unsigned_lit by lia. lia. }
  do 2 cstep.    (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  do 2 cstep.    (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
  cstep.         (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  do 5 cstep.    (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  (* [comment removed for export] *)
  rename FR into FR2. carve_frame 16%nat SK. replace (usp + -208 + -16) with (usp + -224) in * by lia.
  do 3 cstep.    (* [comment removed for export] *)
  do 2 cstep.    (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz end.
  apply (rw_cells_c8_join asegs) in ARG2; [| lia| lia].
  replace (len + 2^32 * 0) with len in ARG2 by lia.
  assert (FRP : rw_cells asegs mz (usp + -112) ([CB 8 j8] ++ [C8 (Z_to_bv 64 A)] ++ [C8 (Z_to_bv 64 len)] ++ [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply rw_cells_app_join; [exact FRa|]. cbn [cells_size csize Nat.add]. replace (usp + -112 + Z.of_nat 8) with (usp + -104) by lia.
    apply rw_cells_app_join; [exact ARG1|]. cbn [cells_size csize Nat.add]. replace (usp + -104 + Z.of_nat 8) with (usp + -96) by lia.
    apply rw_cells_app_join; [exact ARG2|]. cbn [cells_size csize Nat.add]. replace (usp + -96 + Z.of_nat 8) with (usp + -88) by lia. exact FRc. }
  cbn [app] in FRP. clear FRa ARG1 ARG2 FRc.
  apply evtA_done. do 12 eexists. split; [cbv delta [mkR alloc_regs]; unfold count, SS, TD; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SK|]. split; [exact FRP|].
  split; [exact FR1|]. split; [unfold Store_frame, AF_depot6.TBA, TD; exact FR2|]. split; [exact FR| exact NEWN].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition alloc_regs2 (x1 x5 x6 x7 x10 x14 x16 x17 x28 x29 x30 x31 : word) (s0v : Z) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 (usp - 224)) gp tp x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 SS) x10 (Z_to_bv 64 SS) (Z_to_bv 64 (usp - 208))
      (Z_to_bv 64 (usp - 136)) x14 (Z_to_bv 64 count) x16 x17
      (Z_to_bv 64 count) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1))
      (Z_to_bv 64 (TD + 0x400010)) (Z_to_bv 64 head) s10 s11 x28 x29 x30 x31.

Lemma straddles_false : straddles = false -> (fr + count - 1) / kStoreBlockFrames = b /\ bF = b /\ fst_start = fr /\ packv = 0.
Proof. aceil.
  intros Hs. unfold straddles in Hs. apply negb_false_iff in Hs. apply Z.leb_le in Hs. unfold bF, fst_start, packv, straddles.
  replace (fr mod kStoreBlockFrames + count <=? kStoreBlockFrames) with true by (symmetry; apply Z.leb_le; exact Hs). cbn [negb].
  split; [| repeat split; reflexivity]. unfold b, count in *. unfold kStoreBlockFrames in *.
  pose proof (Z.div_mod fr (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound fr (2^20) ltac:(lia)).
  symmetry. apply Z.div_unique with (r := fr mod 2^20 + len); lia.
Qed.
Lemma straddles_true : straddles = true ->
  (fr + count - 1) / kStoreBlockFrames = b + 1 /\ bF = b + 1 /\ fst_start = fr + count /\ packv = 1
  /\ (fr + count) / kStoreBlockFrames = b + 1 /\ (fr + count + count - 1) / kStoreBlockFrames = b + 1
  /\ 1 <= in_first < count.
Proof. aceil.
  intros Hs. unfold straddles in Hs. apply negb_true_iff in Hs. apply Z.leb_gt in Hs. unfold bF, fst_start, packv, straddles, in_first.
  replace (fr mod kStoreBlockFrames + count <=? kStoreBlockFrames) with false by (symmetry; apply Z.leb_gt; exact Hs). cbn [negb].
  unfold b, count in *. unfold kStoreBlockFrames in *.
  pose proof (Z.div_mod fr (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound fr (2^20) ltac:(lia)).
  split; [symmetry; apply Z.div_unique with (r := fr mod 2^20 + len - 2^20); lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [symmetry; apply Z.div_unique with (r := fr mod 2^20 + len + 1 - 2^20); lia|].
  split; [symmetry; apply Z.div_unique with (r := fr mod 2^20 + 2 * len + 1 - 2^20); lia|].
  lia.
Qed.

(* [comment removed for export] *)
Lemma put_sb : forall (x5 x6 x7 x14 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  straddles = false -> mem_inv asegs m ->
  rw_cells asegs m SS [C8 (Z_to_bv 64 fr)] ->
  evtA asegs P (fun ms' => exists (x14' x6' : word) m',
      ms' = MS (alloc_regs2 (Z_to_bv 64 0x719e0) (Z_to_bv 64 b) x6' x7 (Z_to_bv 64 len) x14' x16 x17 x28 x29 x30 x31 fr)
               F (Z_to_bv 64 0x71ab8) fc None m' (seg_rom asegs)
      /\ munch [(SS, SS + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' SS [C8 (Z_to_bv 64 (fr + count))])
    (MS (alloc_regs2 (Z_to_bv 64 0x719e0) x5 x6 x7 (Z_to_bv 64 SS) x14 x16 x17 x28 x29 x30 x31 (usp - 136))
        F (Z_to_bv 64 0x71aa0) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until m. intros NS MI SSC. pose proof (straddles_false NS) as (D1 & _).
  unfold alloc_regs2, SS, TD in *.
  change (1636952 + 4194320) with 5831272.
  assert (MU : munch [(1571400, 1571400 + 8)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  unfold count in *.
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  do 4 zstepA.   (* [comment removed for export] *)
  rewrite !Z.shiftr_div_pow2 by lia. change (2^20) with kStoreBlockFrames. fold b.
  replace (len + fr) with (fr + (len + 1) - 1) by lia. rewrite D1.
  zstepA. if_cases K2; zify_cond K2. { exfalso. lia. }
  apply evtA_done. do 3 eexists. replace (len + 1 - 1) with len by lia.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

(* [comment removed for export] *)
Lemma put_sc : forall (x5 x6 x7 x14 x16 x17 x28 x29 x30 x31 : word) (m : mem) (sbb sbb' : Z),
  straddles = true -> mem_inv asegs m ->
  rw_cells asegs m SS [C8 (Z_to_bv 64 fr)] ->
  rw_cells asegs m (BI b) [C8 (Z_to_bv 64 sbb); C4 (Z_to_bv 64 (stored_of fr b))] ->
  rw_cells asegs m (BI (b + 1)) [C8 (Z_to_bv 64 sbb'); C4 (Z_to_bv 64 (stored_of fr (b + 1)))] ->
  rw_cells asegs m (usp - 136) [C8 (Z_to_bv 64 0)] ->
  evtA asegs P (fun ms' => exists (x6' x7' x14' x16' x17' x28' : word) m',
      ms' = MS (alloc_regs2 (Z_to_bv 64 0x719e0) (Z_to_bv 64 (b + 1)) x6' x7' (Z_to_bv 64 len) x14' x16' x17' x28' x29 x30 x31 (fr + count))
               F (Z_to_bv 64 0x71ab8) fc None m' (seg_rom asegs)
      /\ munch [(SS, SS + 8); (BI b + 8, BI b + 12); (BI (b + 1) + 8, BI (b + 1) + 12); (usp - 136, usp - 128)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' SS [C8 (Z_to_bv 64 (fr + count + count))]
      /\ rw_cells asegs m' (BI b) [C8 (Z_to_bv 64 sbb); C4 (Z_to_bv 64 kStoreBlockFrames)]
      /\ rw_cells asegs m' (BI (b + 1)) [C8 (Z_to_bv 64 sbb'); C4 (Z_to_bv 64 (count - in_first))]
      /\ rw_cells asegs m' (usp - 136) [C8 (Z_to_bv 64 1)])
    (MS (alloc_regs2 (Z_to_bv 64 0x719e0) x5 x6 x7 (Z_to_bv 64 SS) x14 x16 x17 x28 x29 x30 x31 (usp - 136))
        F (Z_to_bv 64 0x71aa0) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until sbb'. intros STR MI SSC BLKb BLKb' PACK. pose proof (straddles_true STR) as (D1 & _ & _ & _ & D2 & D3 & IFR).
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (HB : 0 <= b) by (unfold b; apply Z.div_pos; unfold kStoreBlockFrames; lia).
  pose proof FRB as FRB'. unfold kStoreBlockCount in FRB'.
  pose proof (Z.mod_pos_bound fr kStoreBlockFrames ltac:(unfold kStoreBlockFrames; lia)) as FM.
  assert (FRE : fr = b * kStoreBlockFrames + fr mod kStoreBlockFrames) by (unfold b; rewrite Z.mul_comm; apply Z.div_mod; unfold kStoreBlockFrames; lia).
  assert (ST1 : stored_of fr b = fr mod kStoreBlockFrames) by (unfold stored_of; unfold kStoreBlockFrames in *; lia).
  assert (ST2 : stored_of fr (b + 1) = 0) by (unfold stored_of; unfold kStoreBlockFrames in *; lia).
  rewrite ST1 in BLKb. rewrite ST2 in BLKb'.
  unfold alloc_regs2, BI, SS, TD in *. unfold in_first, count in *. unfold kStoreBlockFrames in *.
  set (B0 := 1571400 + 16 + 16 * b) in *. assert (HB0 : B0 = 1571416 + 16 * b) by reflexivity. clearbody B0.
  set (B1 := 1571400 + 16 + 16 * (b + 1)) in *. assert (HB1 : B1 = B0 + 16) by lia. clearbody B1.
  assert (MU : munch [(1571400, 1571400 + 8); (B0 + 8, B0 + 12); (B1 + 8, B1 + 12); (usp - 136, usp - 128)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  do 4 zstepA.   (* [comment removed for export] *)
  rewrite !Z.shiftr_div_pow2 by lia. change (2^20) with kStoreBlockFrames. fold b.
  replace (len + fr) with (fr + (len + 1) - 1) by lia. unfold kStoreBlockFrames. change (2^20) with 1048576 in D1 |- *. rewrite D1.
  zstepA. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  zstepA.        (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3. { exfalso. revert K3. rewrite ?unsigned_lit by lia. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  change 1048575 with (Z.ones 20). rewrite (Z.land_ones fr 20) by lia. change (Z.ones 20) with 1048575. change (2^20) with 1048576.
  zstepA.        (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 b 4) by lia. change (2^4) with 16.
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  try replace (1571400 + 16 + b * 16) with B0 by lia. try replace (1571416 + b * 16) with B0 by lia.
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  assert (SX1 : sx32 (Z_to_bv 64 (fr mod 1048576)) = Z_to_bv 64 (fr mod 1048576)).
  { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
  rewrite ?SX1.
  zstepA.        (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 (b + 1) 4) by lia. change (2^4) with 16.
  zstepA.        (* [comment removed for export] *)
  try replace (1571400 + 16 + (b + 1) * 16) with B1 by lia. try replace (1571416 + (b + 1) * 16) with B1 by lia.
  zstepA.        (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?(unsigned_lit (fr mod 1048576)) by lia. rewrite ?(Z.mod_small (fr mod 1048576) 4294967296) by lia.
  zstepA.        (* [comment removed for export] *)
  replace (1048576 - fr mod 1048576 + fr mod 1048576) with 1048576 by lia.
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  (zstepA; litc). (* [comment removed for export] *)
  (zstepA; litc). (* [comment removed for export] *)
  (zstepA; litc). (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  zstepA.        (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  (zstepA; litc). (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  replace (Z.lxor (len + 1 - (1048576 - fr mod 1048576)) 1048576) with (len + 1 - (1048576 - fr mod 1048576) + 1048576)
    by (change 1048576 with (2^20); symmetry; apply lxor_pow2_small; lia).
  zstepA.        (* [comment removed for export] *)
  match goal with |- context [Z.b2z (?x <? 1)] => replace (Z.b2z (x <? 1)) with 0 by (symmetry; replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) end.
  (zstepA; litc). (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  do 3 zstepA.   (* [comment removed for export] *)
  rewrite !Z.shiftr_div_pow2 by lia. change (2^20) with 1048576 in *.
  replace (len + (fr + (len + 1))) with (fr + (len + 1) + (len + 1) - 1) by lia. rewrite D2, D3.
  cstep.         (* [comment removed for export] *)
  apply evtA_done. do 7 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  replace (fr mod 1048576 + (1048576 - fr mod 1048576)) with 1048576 in * by lia.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.


(* [comment removed for export] *)
Lemma put_sd : forall (x6 x7 x14 x16 x17 x28 x29 x30 x31 : word) (m : mem) (idx0 : Z),
  mem_inv asegs m ->
  rw_cells asegs m (usp - 208) (Store_frame idx0) ->
  (forall k, 0 <= k < kStoreBlockCount -> exists st, rw_cells asegs m (BI k) [C8 (Z_to_bv 64 (nthz SBL k)); C4 st]) ->
  evtA asegs P (fun ms' => exists m',
         munch [(usp - 208, usp - 200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (usp - 208) (Store_frame fst_start)
      /\ ( (bF < zlen SBL
            /\ ms' = MS (mkR (Z_to_bv 64 0x719e0) (Z_to_bv 64 (usp - 224)) gp tp (Z_to_bv 64 bF) x6 x7 (Z_to_bv 64 fst_start) (Z_to_bv 64 SS)
                             (Z_to_bv 64 (nthz SBL bF)) (Z_to_bv 64 SS) (Z_to_bv 64 (BI bF - 16)) (Z_to_bv 64 (usp - 136)) x14 (Z_to_bv 64 count) x16 x17
                             (Z_to_bv 64 count) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1))
                             (Z_to_bv 64 (TD + 0x400010)) (Z_to_bv 64 head) s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x71ae8) fc None m' (seg_rom asegs))
        \/ (bF = zlen SBL
            /\ ms' = MS (mkR (Z_to_bv 64 0x71ba0) (Z_to_bv 64 (usp - 224)) gp tp (Z_to_bv 64 bF) x6 x7 (Z_to_bv 64 fst_start) (Z_to_bv 64 SS)
                             (Z_to_bv 64 (BI bF)) (Z_to_bv 64 SS) (Z_to_bv 64 (BI bF - 16)) (Z_to_bv 64 (usp - 136)) x14 (Z_to_bv 64 count) x16 x17
                             (Z_to_bv 64 count) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1))
                             (Z_to_bv 64 (TD + 0x400010)) (Z_to_bv 64 head) s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x72474) fc None m' (seg_rom asegs)) ))
    (MS (alloc_regs2 (Z_to_bv 64 0x719e0) (Z_to_bv 64 bF) x6 x7 (Z_to_bv 64 len) x14 x16 x17 x28 x29 x30 x31 fst_start)
        F (Z_to_bv 64 0x71ab8) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until idx0. intros MI SFR BLKS.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (HB : 0 <= b) by (unfold b; apply Z.div_pos; unfold kStoreBlockFrames; lia).
  pose proof FRB as FRB'. unfold kStoreBlockCount in FRB'.
  assert (HBF : 0 <= bF <= b + 1) by (unfold bF; destruct straddles; lia).
  assert (FS32 : 0 <= fst_start /\ fst_start + count <= 2^32) by (unfold fst_start, count; destruct straddles; lia).
  assert (CNT1 : count = len + 1) by reflexivity.
  (* [comment removed for export] *)
  assert (BFLE : bF <= zlen SBL).
  { unfold bF. destruct straddles eqn:STR.
    - pose proof (straddles_true STR) as (D1 & _). unfold straddles in STR. apply negb_true_iff in STR. apply Z.leb_gt in STR.
      unfold b, count in *. unfold kStoreBlockFrames in *.
      assert (fr / 2^20 < zlen SBL); [| lia]. apply Z.div_lt_upper_bound; [lia|].
      destruct (Z_lt_le_dec fr (2^20 * zlen SBL)); [lia|]. exfalso.
      assert (fr = 2^20 * zlen SBL) by lia. rewrite H, Z.mul_comm, Z_mod_mult in STR. lia.
    - unfold b. unfold kStoreBlockFrames in *. apply Z.div_le_upper_bound; [lia|]. lia. }
  destruct (BLKS bF ltac:(unfold kStoreBlockCount; lia)) as [st BLK].
  unfold alloc_regs2, Store_frame, BI, SS, TD in *.
  set (B2 := 1571400 + 16 + 16 * bF) in *. assert (HB2 : B2 = 1571416 + 16 * bF) by reflexivity. clearbody B2.
  assert (MU : munch [(usp - 208, usp - 200)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA.        (* [comment removed for export] *)
  rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small fst_start (2^32)) by lia.
  cstep.         (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  do 2 zstepA.   (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 bF 4) by lia. change (2^4) with 16.
  replace (Z_to_bv 64 (1571400 + bF * 16)) with (Z_to_bv 64 (B2 + -16)) by (f_equal; lia).
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  destruct (Z_lt_le_dec bF (zlen SBL)) as [BLT|BGE].
  - assert (BIN : In (nthz SBL bF) SBL).
    { unfold nthz. replace ((0 <=? bF) && (bF <? zlen SBL)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      apply nth_In. unfold zlen in BLT. lia. }
    pose proof (SBLR _ BIN) as [R1 R2]. unfold kStoreBlockBytes in R2.
    zstepA. if_cases K3; zify_cond K3. { exfalso. revert K3. rewrite ?unsigned_lit by lia. lia. }
    apply evtA_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    left. split; [exact BLT|]. replace (B2 - 16) with (B2 + -16) by lia. cbv delta [mkR]. reflexivity.
  - assert (BEQ : bF = zlen SBL) by lia.
    assert (NZ : nthz SBL bF = 0).
    { unfold nthz. replace (bF <? zlen SBL) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. }
    rewrite NZ.
    zstepA. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3. rewrite ?unsigned_lit by lia. lia. }
    zstepA.      (* [comment removed for export] *)
    replace (B2 + -16 + 16) with B2 by lia.
    cstep.       (* [comment removed for export] *)
    apply evtA_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    right. split; [exact BEQ|]. replace (B2 - 16) with (B2 + -16) by lia. cbv delta [mkR]. reflexivity.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition se_fp (sbF : Z) : list (Z * Z) :=
  [(usp - 224, usp); (NA + 8, NA + 16); (TBA, TBA + 4); (BI bF + 8, BI bF + 12);
   (sbF + 8 * (fst_start mod kStoreBlockFrames), sbF + 8 * (fst_start mod kStoreBlockFrames) + 8 * count)].
Definition put_se_post (m : mem) (sbF : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (bs' : list byte) (pk : Z),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (N + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (se_fp sbF) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ rw_cells asegs m' TBA [C4 (Z_to_bv 64 (N + 1))]                                            (* [comment removed for export] *)
    /\ (exists sid, rw_cells asegs m' NA [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 head); C4 sid])      (* [comment removed for export] *)
    /\ rw_cells asegs m' (BI bF) [C8 (Z_to_bv 64 sbF); C4 (Z_to_bv 64 (fst_start mod kStoreBlockFrames + count))]   (* [comment removed for export] *)
    /\ u8arr asegs m' sbF bs' /\ Z.of_nat (length bs') = kStoreBlockBytes                          (* [comment removed for export] *)
    /\ 0 <= pk <= packv + 1.                                                                         (* [comment removed for export] *)

Lemma fst_facts : 0 <= fst_start /\ fst_start + count + 2 <= 2^32 /\ fst_start mod kStoreBlockFrames + count <= kStoreBlockFrames
                  /\ bF = fst_start / kStoreBlockFrames /\ 0 <= bF < kStoreBlockCount /\ 0 <= packv <= 1.
Proof.
  pose proof FRB as FRB'. unfold kStoreBlockCount in *.
  assert (HB : 0 <= b) by (unfold b; apply Z.div_pos; unfold kStoreBlockFrames; lia).
  pose proof (Z.mod_pos_bound fr kStoreBlockFrames ltac:(unfold kStoreBlockFrames; lia)) as FM.
  unfold packv. destruct straddles eqn:STR.
  - pose proof (straddles_true STR) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). rewrite D2, D3.
    unfold straddles in STR. apply negb_true_iff in STR. apply Z.leb_gt in STR.
    unfold in_first, count, b in *. unfold kStoreBlockFrames in *.
    assert (E : (fr + (len + 1)) mod 2^20 = fr mod 2^20 + (len + 1) - 2^20).
    { rewrite (Z.mod_eq (fr + (len + 1)) (2^20)) by lia. rewrite D5. rewrite (Z.mod_eq fr (2^20)) in * by lia. lia. }
    rewrite E. repeat split; try lia.
  - pose proof (straddles_false STR) as (D1 & D2 & D3 & D4). rewrite D2, D3.
    unfold straddles in STR. apply negb_false_iff in STR. apply Z.leb_le in STR.
    unfold count, b in *. unfold kStoreBlockFrames in *. repeat split; try lia.
Qed.

Lemma put_se : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem)
    (j8 js : list byte) (j1 j2 wl : word) (sbF : Z) (bs : list byte),
  stk asegs m lo (usp - 224) -> mem_inv asegs m ->
  rw_cells asegs m (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8) ->
  rw_cells asegs m (usp - 144) (store_frame js packv) ->
  rw_cells asegs m (usp - 208) (Store_frame fst_start) ->
  rw_cells asegs m (usp - 224) Alloc_frame ->
  rw_cells asegs m NA [C8 (Z_to_bv 64 h); C4 j1; C4 j2] ->
  u64arr asegs m A ws ->
  rw_cells asegs m TBA [C4 wl] ->
  rw_cells asegs m (BI bF) [C8 (Z_to_bv 64 sbF); C4 (Z_to_bv 64 (fst_start mod kStoreBlockFrames))] ->
  u8arr asegs m sbF bs -> Z.of_nat (length bs) = kStoreBlockBytes -> 0x603000 <= sbF -> sbF + kStoreBlockBytes <= alloc_ceiling ->
  (NA + 16 <= sbF \/ sbF + kStoreBlockBytes <= NA) ->
  rw_cells asegs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)] -> rw_cells asegs m (0x13f6a8 + 240) [C4 (Z_to_bv 64 0)] ->
  (forall a n, sbF <= a -> a + Z.of_nat n <= sbF + kStoreBlockBytes -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (put_se_post m sbF)
    (MS (mkR x1 (Z_to_bv 64 (usp - 224)) gp tp x5 x6 x7 (Z_to_bv 64 fst_start) (Z_to_bv 64 SS) (Z_to_bv 64 sbF) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 count) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1))
             (Z_to_bv 64 (TD + 0x400010)) (Z_to_bv 64 head) s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x71ae8) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until bs. intros SK MI FRP SFRs SFR AFR NODE TR TABL BLKF SB LSB SB1 SB2 NASB GOTF CFF PSB.
  pose proof LOC as LOC0. aceil.
  pose proof BLKR as [(BR1 & BR2 & BR3) BR16]. aceil. unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in BR1, BR2, BR3. unfold kDepotNodeBlockBytes in BR2, BR3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= usp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  pose proof (depot_hash_range (AF_depot6.keyZ len ws)) as HR. change (depot_hash (AF_depot6.keyZ len ws)) with h in HR.
  assert (BKR : 0 <= bkt < 2^20) by (unfold AF_depot6.bkt, bucket_of, kTabSize; apply Z.mod_pos_bound; lia).
  pose proof (Z.mod_pos_bound (N + 1) kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)) as MB.
  assert (HNA : NA = blk + 16 * ((N + 1) mod kDepotNodesPerBlock)) by reflexivity.
  assert (NAR : 0x603000 <= NA /\ NA + 16 <= alloc_ceiling) by (rewrite HNA; unfold kDepotNodesPerBlock in *; lia).
  pose proof fst_facts as (FS0 & FS32 & FSM & HBF & BFR & PKR).
  assert (CNT1 : count = len + 1) by reflexivity.
  pose proof (Z.mod_pos_bound fst_start kStoreBlockFrames ltac:(unfold kStoreBlockFrames; lia)) as FM.
  unfold put_frame, store_frame, Store_frame, Alloc_frame in *. unfold BI in *. unfold AF_depot6.TBA, TD, SS in *.
  unfold kStoreBlockBytes, kStoreBlockFrames, kStoreBlockCount in *. change (2^20) with 1048576 in *. change (2^23) with 8388608 in *.
  change (1636952 + 4194312) with 5831264 in *. change (1636952 + 4194320) with 5831272 in *. change (1308328 + 240) with 1308568 in CFF.
  set (B2 := 1571400 + 16 + 16 * bF) in *. assert (HB2 : B2 = 1571416 + 16 * bF) by reflexivity. clearbody B2.
  set (TBAv := 1636952 + 4 * bkt) in *. assert (HTB : TBAv = 1636952 + 4 * bkt) by reflexivity. clearbody TBAv.
  set (D0 := sbF + 8 * (fst_start mod 1048576)). assert (HD0 : D0 = sbF + 8 * (fst_start mod 1048576)) by reflexivity. clearbody D0.
  match goal with |- evtA _ _ ?Q _ => set (POST := Q) end.
  assert (MU : munch [(usp - 224, usp); (NA + 8, NA + 16); (TBAv, TBAv + 4); (B2 + 8, B2 + 12); (D0, D0 + 8 * count)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  (* [comment removed for export] *)
  replace (usp - 224) with (usp + -224) in * by lia. replace (usp - 208) with (usp + -208) in * by lia.
  replace (usp - 144) with (usp + -144) in * by lia. replace (usp - 136) with (usp + -136) in * by lia.
  replace (usp - 112) with (usp + -112) in * by lia. replace (usp - 104) with (usp + -104) in * by lia.
  (* [comment removed for export] *)
  do 3 zstepA.   (* [comment removed for export] *)
  change 41 with (44 - 3). rewrite (shl_shr_field fst_start 44 3) by lia. change (2^(64-44)) with 1048576. change (2^3) with 8.
  replace (Z_to_bv 64 (sbF + fst_start mod 1048576 * 8)) with (Z_to_bv 64 D0) by (f_equal; lia).
  do 4 cstep.    (* [comment removed for export] *)
  release_frame AFR SK (usp + -208).
  (* [comment removed for export] *)
  zstepA; if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. }
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  (zstepA; litc). (* [comment removed for export] *)
  rewrite ?Z.lor_0_l.
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (wr_at_store_ok asegs mx sbF (Z.of_nat (length bs)) (8 * (fst_start mod 1048576)) 8%nat (proj2 SB) ltac:(lia) ltac:(lia)) as SOK end.
  replace (Z_to_bv 64 D0) with (Z_to_bv 64 (sbF + 8 * (fst_start mod 1048576))) by (f_equal; lia).
  stepA.         (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PSB; lia end.
  match type of SB with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write_bytes asegs mx sbF bs (8 * (fst_start mod 1048576)) (le8 (Z_to_bv 64 len)) SB ltac:(lia)
                  ltac:(rewrite length_le8; lia)) as SB' end.
  clear SB. store_done. rename SB' into SB.
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  replace (Z_to_bv 64 (Z.shiftl len 3)) with (Z_to_bv 64 (8 * len)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (Z_to_bv 64 (sbF + 8 * (fst_start mod 1048576) + 8)) with (Z_to_bv 64 (sbF + (8 * (fst_start mod 1048576) + 8))) by (f_equal; lia).
  cstep.         (* [comment removed for export] *)
  match type of TR with u64arr _ ?mx _ _ =>
    assert (SRC : bytes_at asegs mx A (firstn (Z.to_nat (8 * len)) (u64s ws))) by (apply bytes_at_prefix; [exact (proj1 TR)| rewrite u64s_length; lia]) end.
  callA (imc_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A sbF (8 * (fst_start mod 1048576) + 8) (8 * len) (firstn (Z.to_nat (8 * len)) (u64s ws)) (Z.of_nat (length bs))
           SRC ltac:(rewrite length_firstn, u64s_length; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(intros; apply PSTK; lia) ltac:(intros; apply PSB; lia) _ _ _ ltac:(assumption) _ SB ltac:(rewrite upd_bytes_length; [reflexivity| rewrite length_le8; lia]) eq_refl eq_refl).
  rename PC into SB. rename POST0 into LSB'. rewrite LSB in LSB'.
  zstepA.        (* [comment removed for export] *)
  do 2 zstepA.   (* [comment removed for export] *)
  assert (AL : Z.land (Z.shiftr fst_start 16) 18446744073709551600 = 16 * bF).
  { change 18446744073709551600 with (2^64 - 2^4). rewrite land_align_down; [| rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia] | lia].
    rewrite Z.shiftr_div_pow2 by lia. rewrite HBF. change 1048576 with (2^16 * 2^4). rewrite <- Z.div_div by lia.
    rewrite (Z.mod_eq (fst_start / 2^16) (2^4)) by lia. lia. }
  rewrite AL. clear AL.
  do 2 zstepA.   (* [comment removed for export] *)
  replace (Z_to_bv 64 (1571400 + 16 * bF + 24)) with (Z_to_bv 64 (B2 + 8)) by (f_equal; lia).
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; lia end.
  assert (SX2 : sx32 (Z_to_bv 64 (fst_start mod 1048576)) = Z_to_bv 64 (fst_start mod 1048576)).
  { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
  rewrite ?SX2.
  do 3 zstepA.   (* [comment removed for export] *)
  rewrite ?(unsigned_lit (fst_start mod 1048576)) by lia. rewrite ?(Z.mod_small (fst_start mod 1048576) 4294967296) by lia.
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  replace (Z_to_bv 64 fst_start) with (Z_to_bv 64 (fst_start + 2^32 * 0)) in SFR by (f_equal; lia).
  apply rw_cells_c8_split in SFR; [| lia| lia].
  zstepA.        (* [comment removed for export] *)
  do 3 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  do 9 cstep.    (* [comment removed for export] *)
  release_frame SFR SK (usp + -144).
  (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PNA; lia end.
  match goal with |- context [Z_to_bv 64 (packv + ?e)] => set (pk := packv + e) in *; assert (PK : 0 <= pk <= packv + 1) by (subst pk; destruct (_ <? 1); cbn [Z.b2z]; lia) end.
  (* [comment removed for export] *)
  Ltac put_tail FRP SK :=
    zstepA;        (* [comment removed for export] *)
    [ ..| try lazymatch goal with |- P _ => apply PNA; lia end ];
    cstep;         (* [comment removed for export] *)
    cstep;         (* [comment removed for export] *)
    zstepA;        (* [comment removed for export] *)
    [ ..| try lazymatch goal with |- P _ => apply PDAT; lia end ];
    cstep;         (* [comment removed for export] *)
    do 12 cstep;   (* [comment removed for export] *)
    release_frame FRP SK (bv_unsigned sp);
    cstep.         (* [comment removed for export] *)
  zstepA; if_cases K5; zify_cond K5.
  - (* [comment removed for export] *)
    cstep.       (* [comment removed for export] *)
    carve_frame 16%nat SK.
    do 3 cstep.  (* [comment removed for export] *)
    do 3 cstep.  (* [comment removed for export] *)
    cstep.       (* [comment removed for export] *)
    do 4 cstep.  (* [comment removed for export] *)
    release_frame FR SK (usp + -144).
    do 4 cstep.  (* [comment removed for export] *)
    release_frame SFRs SK (usp + -112).
    put_tail FRP SK.
    apply evtA_done. subst POST. unfold put_se_post, se_fp. unfold BI, AF_depot6.TBA, TD, SS, kStoreBlockFrames. change (2^20) with 1048576.
    do 17 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx HB2 HTB HD0 CNT1 SPR; lia|].
    split; [assumption|]. split; [assumption|]. split; [exact SK|].
    split; [first [exact TABL | rewrite HTB in TABL; exact TABL]|].
    split; [eexists; exact NODE|].
    split; [first [exact BLKF | rewrite HB2 in BLKF; exact BLKF | replace (1571400 + 16 + 16 * bF) with B2 by lia; exact BLKF]|].
    split; [exact SB|]. split; [exact LSB'|]. exact PK.
  - do 4 cstep.  (* [comment removed for export] *)
    release_frame SFRs SK (usp + -112).
    put_tail FRP SK.
    apply evtA_done. subst POST. unfold put_se_post, se_fp. unfold BI, AF_depot6.TBA, TD, SS, kStoreBlockFrames. change (2^20) with 1048576.
    do 17 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx HB2 HTB HD0 CNT1 SPR; lia|].
    split; [assumption|]. split; [assumption|]. split; [exact SK|].
    split; [first [exact TABL | rewrite HTB in TABL; exact TABL]|].
    split; [eexists; exact NODE|].
    split; [first [exact BLKF | rewrite HB2 in BLKF; exact BLKF | replace (1571400 + 16 + 16 * bF) with B2 by lia; exact BLKF]|].
    split; [exact SB|]. split; [exact LSB'|]. exact PK.
Qed.
End PUTS.
End RC__1.
