(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_unwind.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
Notation uwfW sp B := [(bv_unsigned sp - 64, bv_unsigned sp); (B + 8, B + 12); (B + 16, B + 256)].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition uwf_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B : Z) : machine_state -> Prop :=
  fun ms' => exists (a2 a3 a4 a5 a6 a7 : word) m' (ws tr : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) pc0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (uwfW sp B) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u64arr bsegs m' (B + 16) ws /\ length ws = 30%nat /\ firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat
    /\ hd_error tr = Some pc0
    /\ rw_cells bsegs m' (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))].

Lemma firstn_S_upd : forall (tr ws : list word) x,
  firstn (length tr) ws = tr -> (length tr < length ws)%nat ->
  firstn (length (tr ++ [x])) (upd ws (length tr) x) = tr ++ [x].
Proof. aceil.
  intros tr ws x FT LT. rewrite upd_firstn_skipn by exact LT. rewrite FT.
  rewrite length_app. cbn [length]. rewrite firstn_app.
  pose proof (f_equal (@length word) FT) as L. rewrite length_firstn in L.
  replace (length tr + 1 - length tr)%nat with 1%nat by lia.
  rewrite firstn_all2 by lia. reflexivity.
Qed.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B SP top : Z).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis BSP : B + 2080 <= SP.
Hypothesis TOP : 4096 <= top < 2^64.
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= 2^64 -> P (Z_to_bv 64 a, n).

Notation POST := (uwf_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc0 F fc m lo B).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
Notation FRC := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Notation ST pc mm x9 x12 x13 x14 x15 x16 x17 :=
  (MS (mkR ra SP' gp tp t0 t1 t2 (Z_to_bv 64 30) x9 (Z_to_bv 64 B) pc0 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 0x13e060) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Notation T16 := (Z_to_bv 64 (top + -16)).

Lemma uwf_exit : forall mm ws tr x9 x12 x13 x14 x15 x16 x17,
  munch (uwfW sp B) m mm -> wmono bsegs m mm -> mem_inv bsegs mm -> stk bsegs mm lo (bv_unsigned sp + -64) ->
  rw_cells bsegs mm (bv_unsigned sp + -64) FRC ->
  rw_cells bsegs mm (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] -> u64arr bsegs mm (B + 16) ws -> length ws = 30%nat ->
  firstn (length tr) ws = tr -> (1 <= length tr <= 30)%nat -> hd_error tr = Some pc0 ->
  evtA bsegs P POST (ST 0x747f8 mm x9 x12 x13 x14 x15 x16 x17).
Proof. aceil.
  intros until x17. intros MU WM MI SK FR CSZ ARR LEN FT LT HD. clear TOP BSP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  do 10 cstep.
  release_frame FR SK (bv_unsigned sp). unfold uwf_post. finishA.
  all: first [exact ARR | exact LEN | exact FT | exact HD | exact CSZ | lia].
Qed.


Definition loop_facts (mm : mem) (ws tr : list word) : Prop :=
  munch (uwfW sp B) m mm /\ wmono bsegs m mm /\ mem_inv bsegs mm /\ stk bsegs mm lo (bv_unsigned sp + -64) /\
  rw_cells bsegs mm (bv_unsigned sp + -64) FRC /\
  rw_cells bsegs mm (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] /\ u64arr bsegs mm (B + 16) ws /\ length ws = 30%nat /\
  firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat /\ hd_error tr = Some pc0.

Lemma uwf_iter : forall (fr pc1 nf : word) mm ws tr x16 x17,
  rw_cells bsegs m (bv_unsigned fr + -16) [C8 nf; C8 pc1] ->
  SP <= bv_unsigned fr -> bv_unsigned fr + 16 < top ->
  loop_facts mm ws tr ->
  (forall mm' ws' tr' x15 x16' x17', loop_facts mm' ws' tr' -> x15 = Z_to_bv 64 (Z.of_nat (length tr')) ->
      bv_unsigned fr < bv_unsigned nf -> bv_unsigned nf + 16 < top -> bv_unsigned nf mod 8 = 0 ->
      evtA bsegs P POST (ST 0x747bc mm' T16 nf (Z_to_bv 64 4096) (Z_to_bv 64 (B + 16)) x15 x16' x17')) ->
  evtA bsegs P POST (ST 0x747bc mm T16 fr (Z_to_bv 64 4096) (Z_to_bv 64 (B + 16)) (Z_to_bv 64 (Z.of_nat (length tr))) x16 x17).
Proof. aceil.
  intros until x17. intros CL FR1 FR2 (MU & WM & MI & SK & FR & CSZ & ARR & LEN & FT & LT & HD) CONT.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ fr) as FRR. change (bv_modulus 64) with (2^64) in FRR.
  pose proof (bv_unsigned_in_range _ nf) as NFR. change (bv_modulus 64) with (2^64) in NFR.
  pose proof (bv_unsigned_in_range _ pc1) as PCR. change (bv_modulus 64) with (2^64) in PCR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  assert (CLm : rw_cells bsegs mm (bv_unsigned fr + -16) [C8 nf; C8 pc1]).
  { eapply rw_cells_agree; [| exact CL]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  zstepA. if_cases K0; zify_cond K0.
  { eapply uwf_exit; eassumption. }
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.
  { eapply uwf_exit; eassumption. }
  assert (TAIL : forall mm' ws' tr' x15 x16' x17', loop_facts mm' ws' tr' -> x15 = Z_to_bv 64 (Z.of_nat (length tr')) ->
             evtA bsegs P POST (ST 0x747e0 mm' T16 fr (Z_to_bv 64 4096) (Z_to_bv 64 (B + 16)) x15 x16' x17')).
  { clear mm ws tr x16 x17 MU WM MI SK FR CSZ ARR LEN FT LT HD CLm K0.
    intros mm ws tr x15 x16 x17 LF ->. pose proof LF as (MU & WM & MI & SK & FR & CSZ & ARR & LEN & FT & LT & HD).
    assert (CLm : rw_cells bsegs mm (bv_unsigned fr + -16) [C8 nf; C8 pc1]).
    { eapply rw_cells_agree; [| exact CL]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K3; zify_cond K3. { eapply uwf_exit; eassumption. }
    zstepA. if_cases K4; zify_cond K4. { eapply uwf_exit; eassumption. }
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. if_cases K5; zify_cond K5.
    - eapply CONT; [exact LF| reflexivity| lia| lia|].
      change 7 with (Z.ones 3) in K5. rewrite Z.land_ones in K5 by lia. exact K5.
    - eapply uwf_exit; eassumption. }
  zstepA. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *) eapply TAIL; [| reflexivity].
    exact (conj MU (conj WM (conj MI (conj SK (conj FR (conj CSZ (conj ARR (conj LEN (conj FT (conj LT HD)))))))))).
  - zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    set (i := Z.of_nat (length tr)) in *.
    replace (Z_to_bv 64 (B + 16 + Z.shiftl i 3)) with (Z_to_bv 64 (B + 16 + 8 * i)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bsegs mx (B + 16) ws i (Z_to_bv 64 (B + 16 + 8 * i)) ARR ltac:(rewrite LEN; lia)
                    ltac:(reflexivity)) as SOK end.
    stepA. (* [comment removed for export] *)
    all: lazymatch goal with |- P _ => apply PSTK; lia | _ => idtac end.
    match type of ARR with u64arr _ ?mx _ _ =>
      pose proof (u64arr_write bsegs mx (B + 16) ws i pc1 ARR ltac:(rewrite LEN; lia)) as ARR' end.
    clear ARR. store_done. rename ARR' into ARR.
    assert (FT' : firstn (length (tr ++ [pc1])) (upd ws (Z.to_nat i) pc1) = tr ++ [pc1]).
    { subst i. rewrite Nat2Z.id. apply firstn_S_upd; [exact FT| rewrite LEN; lia]. }
    assert (LT' : (1 <= length (tr ++ [pc1]) <= 30)%nat) by (rewrite length_app; cbn [length]; lia).
    assert (HD' : hd_error (tr ++ [pc1]) = Some pc0) by (destruct tr; [discriminate| exact HD]).
    assert (LEN' : length (upd ws (Z.to_nat i) pc1) = 30%nat) by (rewrite upd_length; exact LEN).
    replace (i + 1) with (Z.of_nat (length (tr ++ [pc1]))) in CSZ |- * by (rewrite length_app; cbn [length]; lia).
    eapply TAIL; [| reflexivity].
    exact (conj MU (conj WM (conj MI (conj SK (conj FR (conj CSZ (conj ARR (conj LEN' (conj FT' (conj LT' HD')))))))))).
Qed.

Lemma uwf_loop : forall FRz (pc1 nf : word), uanchor bsegs m FRz pc1 nf ->
  forall (fr : word) mm ws tr x16 x17, FRz = bv_unsigned fr ->
  rw_cells bsegs m (bv_unsigned fr + -16) [C8 nf; C8 pc1] ->
  SP <= bv_unsigned fr -> bv_unsigned fr + 16 < top ->
  loop_facts mm ws tr ->
  evtA bsegs P POST (ST 0x747bc mm T16 fr (Z_to_bv 64 4096) (Z_to_bv 64 (B + 16)) (Z_to_bv 64 (Z.of_nat (length tr))) x16 x17).
Proof. aceil.
  intros FRz pc1 nf U. induction U as [FRz pc1 nf H| FRz pc1 nf ra' s0' H1 H2 RC U IH];
    intros fr mm ws tr x16 x17 -> CL FR1 FR2 LF.
  - eapply uwf_iter; [exact CL| exact FR1| exact FR2| exact LF|].
    intros mm' ws' tr' x15 x16' x17' LF' -> C1 C2 C3. exfalso.
    pose proof (bv_unsigned_in_range _ sp) as SPR. aceil. lia.
  - eapply uwf_iter; [exact CL| exact FR1| exact FR2| exact LF|].
    intros mm' ws' tr' x15 x16' x17' LF' -> C1 C2 C3.
    eapply IH; [reflexivity| | lia| lia| exact LF'].
    replace (bv_unsigned nf + -16) with (bv_unsigned nf - 16) by lia. exact RC.
Qed.
End Walk.

Section Walk2.
Variable P : acc -> Prop.

Lemma uwf_walk2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B SP top bot : Z) (szj : word) (ws : list word) (s0c rac : word),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= B ->
  B + 2080 <= SP -> SP < 2^47 -> 0 <= bot < top -> top <= 2^47 ->
  mem_inv bsegs m ->
  rw_cells bsegs m 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs m 0x13e060 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (B + 8) [C4 szj] -> u64arr bsegs m (B + 16) ws -> length ws = 30%nat ->
  rw_cells bsegs m (SP + -16) [C8 s0c; C8 rac] -> uanchor bsegs m SP rac s0c ->
  (forall a n, lo <= a -> a + Z.of_nat n <= 2^64 -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (uwf_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc0 F fc m lo B)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) pc0 (Z_to_bv 64 SP) (Z_to_bv 64 top) (Z_to_bv 64 bot) (Z_to_bv 64 30) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x746fc) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until rac. intros SK LOC LO SPB BSP SPR2 BOT TOP MI G1 G2 CSZ ARR LEN CL U PSTK PDAT.
  aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  assert (MU : munch (uwfW sp B) m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (CL0 : id (rw_cells bsegs m (SP + -16) [C8 s0c; C8 rac])) by exact CL.
  carve_frame 64%nat SK.
  do 9 cstep.
  do 5 cstep. (* [comment removed for export] *)
  do 3 cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok bsegs mx (B + 16) ws 0 (Z_to_bv 64 (B + 16)) ARR ltac:(rewrite LEN; lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
  stepA. (* [comment removed for export] *)
  match type of ARR with u64arr _ ?mx _ _ =>
    pose proof (u64arr_write bsegs mx (B + 16) ws 0 pc0 ARR ltac:(rewrite LEN; lia)) as ARR' end.
  replace (B + 16 + 8 * 0) with (B + 16) in ARR' by lia. change (Z.to_nat 0) with 0%nat in ARR'.
  clear ARR. store_done. rename ARR' into ARR.
  (* [comment removed for export] *)
  assert (LEN' : length (upd ws 0%nat pc0) = 30%nat) by (rewrite upd_length; exact LEN).
  assert (FT' : firstn (length [pc0]) (upd ws 0%nat pc0) = [pc0]) by (destruct ws; [discriminate| reflexivity]).
  assert (LT' : (1 <= length [pc0] <= 30)%nat) by (cbn; lia).
  assert (HD' : hd_error [pc0] = Some pc0) by reflexivity.
  match type of CSZ with rw_cells _ ?mx _ _ =>
    assert (CSZ' : rw_cells bsegs mx (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length [pc0])))]) by exact CSZ end.
  Ltac exit0 MU WM MI SK FR CSZ' ARR LEN' FT' LT' HD' :=
    eapply uwf_exit; [ | | exact MU| exact WM| exact MI| exact SK| exact FR| exact CSZ'| exact ARR| exact LEN'| exact FT'| exact LT'| exact HD']; [lia| assumption].
  zstepA. if_cases K; zify_cond K.
  2:{ (* [comment removed for export] *) zstepA. exit0 MU WM MI SK FR CSZ' ARR LEN' FT' LT' HD'. }
  assert (TOP2 : 4096 <= top).
  { rewrite Z.shiftr_div_pow2 in K by lia. change (2^12) with 4096 in K. Z.div_mod_to_equations. lia. }
  zstepA. if_cases K1; zify_cond K1. { exfalso. lia. }                       (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.                                          (* [comment removed for export] *)
  { exit0 MU WM MI SK FR CSZ' ARR LEN' FT' LT' HD'. }
  zstepA. zstepA. if_cases K3; zify_cond K3.                                  (* [comment removed for export] *)
  { exit0 MU WM MI SK FR CSZ' ARR LEN' FT' LT' HD'. }
  zstepA. zstepA. if_cases K4; zify_cond K4.                                  (* [comment removed for export] *)
  { exit0 MU WM MI SK FR CSZ' ARR LEN' FT' LT' HD'. }
  zstepA. zstepA.
  eapply (uwf_loop P ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc0 F fc m lo B SP top
            LOC LO SPB BSP ltac:(lia) PSTK SP rac s0c U (Z_to_bv 64 SP) _ (upd ws 0%nat pc0) [pc0]).
  - symmetry. apply Z_to_bv_small. change (bv_modulus 64) with (2^64). lia.
  - rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia). exact CL0.
  - rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia). lia.
  - rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia). lia.
  - unfold loop_facts.
    exact (conj MU (conj WM (conj MI (conj SK (conj FR (conj CSZ' (conj ARR (conj LEN' (conj FT' (conj LT' HD')))))))))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation unwW sp B := [(bv_unsigned sp - 64, bv_unsigned sp); (B + 8, B + 12); (B + 16, B + 256); (B + 2056, B + 2064)].

Definition unwind_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a2 a3 a4 a5 a6 a7 : word) m' (ws tr : list word) (w : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) pc0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (unwW sp B) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u64arr bsegs m' (B + 16) ws /\ length ws = 30%nat /\ firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat
    /\ hd_error tr = Some pc0
    /\ rw_cells bsegs m' (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ rw_cells bsegs m' (B + 2056) [C8 w].

Lemma unwind_walk2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B SP top bot : Z) (szj bpj : word) (ws : list word) (s0c rac : word),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= B ->
  B + 2080 <= SP -> SP < 2^47 -> 0 <= bot < top -> top <= 2^47 ->
  mem_inv bsegs m ->
  rw_cells bsegs m 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs m 0x13e060 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (B + 8) [C4 szj] -> u64arr bsegs m (B + 16) ws -> length ws = 30%nat -> rw_cells bsegs m (B + 2056) [C8 bpj] ->
  rw_cells bsegs m (SP + -16) [C8 s0c; C8 rac] -> uanchor bsegs m SP rac s0c ->
  (forall a n, lo <= a -> a + Z.of_nat n <= 2^64 -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (unwind_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc0 F fc m lo B)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 30) pc0 (Z_to_bv 64 SP) (Z_to_bv 64 0) (Z_to_bv 64 top) (Z_to_bv 64 bot) (Z_to_bv 64 1)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x74d58) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until rac. intros SK LOC LO SPB BSP SPR2 BOT TOP MI G1 G2 CSZ ARR LEN BPJ CL U PSTK PDAT.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  assert (MU : munch (unwW sp B) m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof SK as SK0.
  carve_frame 64%nat SK.
  do 8 cstep.   (* [comment removed for export] *)
  do 6 cstep.   (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  do 3 cstep.   (* [comment removed for export] *)
  do 5 cstep.   (* [comment removed for export] *)
  do 8 cstep.   (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  cstep.        (* [comment removed for export] *)
  eapply evtA_mono.
  { eapply uwf_walk2; try eassumption; try lia.
    eapply uanchor_frame; [| exact U]. intros a Ha. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  cbv beta. intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & m' & ws' & tr' & -> & MU' & WM' & MI' & SK' & ARR' & LEN' & FT' & LT' & HD' & CSZ').
  unfold unwind_post. do 12 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. intuition lia. }
  split; [eapply wmono_trans; [exact WM| exact WM']|].
  split; [exact MI'|]. split; [exact SK'|]. split; [exact ARR'|]. split; [exact LEN'|]. split; [exact FT'|]. split; [exact LT'|].
  split; [exact HD'|]. split; [exact CSZ'|].
  eapply rw_cells_agree; [| exact BPJ]. cbn. intros x Hx. apply MU'. rewrite wa_unsigned by lia. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stack_top_walk2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (T top bot : Z),
  mem_inv bsegs m -> a0 = Z_to_bv 64 T -> 0 <= T -> T + 4096 <= alloc_ceiling -> 0 <= bot < top -> top < 2^64 ->
  rw_cells bsegs m (T + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (T + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  (forall a n, T <= a -> a + Z.of_nat n <= T + 4096 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (leaf_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d870) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until bot. intros MI -> HT0 HT1 HB HT2 C40 C8s PT. aceil.
  do 3 cstep.   (* [comment removed for export] *)
  do 5 cstep.   (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] =>
    replace (Z_to_bv 64 (Z.land x y)) with (Z_to_bv 64 top) end.
  2:{ rewrite v_sltu_b2z. rewrite (Z_to_bv_small 64 bot), (Z_to_bv_small 64 top) by (change (bv_modulus 64) with (2^64)%Z; lia).
      replace (bot <? top) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      match goal with |- context [bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))] =>
        let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) in
        change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with v end.
      change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
      rewrite (Z.mod_small top) by lia. reflexivity. }
  cstep. apply evtA_done. unfold leaf_post. eexists. reflexivity.
Qed.

Lemma stack_bottom_walk2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (T top bot : Z),
  mem_inv bsegs m -> a0 = Z_to_bv 64 T -> 0 <= T -> T + 4096 <= alloc_ceiling -> 0 <= bot < top -> top < 2^64 ->
  rw_cells bsegs m (T + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (T + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  (forall a n, T <= a -> a + Z.of_nat n <= T + 4096 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (leaf_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bot)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d8c8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until bot. intros MI -> HT0 HT1 HB HT2 C40 C8s PT. aceil.
  do 3 cstep.   (* [comment removed for export] *)
  do 5 cstep.   (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] =>
    replace (Z_to_bv 64 (Z.land x y)) with (Z_to_bv 64 bot) end.
  2:{ rewrite v_sltu_b2z. rewrite (Z_to_bv_small 64 bot), (Z_to_bv_small 64 top) by (change (bv_modulus 64) with (2^64)%Z; lia).
      replace (bot <? top) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      match goal with |- context [bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))] =>
        let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) in
        change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with v end.
      change 18446744073709551615 with (Z.ones 64). rewrite ?(Z.land_comm (Z.ones 64)), Z.land_ones by lia.
      rewrite (Z.mod_small bot) by lia. reflexivity. }
  cstep. apply evtA_done. unfold leaf_post. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation uwiW sp B T := [(bv_unsigned sp - 144, bv_unsigned sp); (B + 8, B + 12); (B + 16, B + 256); (B + 2056, B + 2064); (T + 3168, T + 3169)].

(* [comment removed for export] *)
Definition uthread_cells (m : mem) (tp : word) (TSD CTX T top bot : Z) : Prop :=
  thread_cells m tp TSD CTX T /\ rw_cells bsegs m (T + 40) [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m (T + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] /\ rw_cells bsegs m (T + 3168) [C1 (Z_to_bv 8 0)].

Definition unwind_impl_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B T : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word) m' (ws tr : list word) (w : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (uwiW sp B T) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u64arr bsegs m' (B + 16) ws /\ length ws = 30%nat /\ firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat
    /\ hd_error tr = Some pc0
    /\ rw_cells bsegs m' (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ rw_cells bsegs m' (B + 2056) [C8 w]
    /\ rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)].

Lemma unwind_impl_walk2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pc0 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B SP : Z) (TSD CTX T top bot : Z) (szj bpj : word) (ws : list word) (s0c rac : word),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp <= B ->
  B + 2080 <= SP -> SP < 2^47 -> 0 <= bot < top -> top <= 2^47 ->
  mem_inv bsegs m ->
  rw_cells bsegs m 0xaf298 [C1 (Z_to_bv 8 1)] ->                                                       (* [comment removed for export] *)
  rw_cells bsegs m 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs m 0x13e060 [C8 (Z_to_bv 64 4096)] ->   (* [comment removed for export] *)
  uthread_cells m tp TSD CTX T top bot -> 0xa5000 <= TSD -> TSD + 8 <= 0x603000 -> 0 < CTX -> CTX + 4096 <= alloc_ceiling ->
  (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) -> T + 4096 <= alloc_ceiling -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->   (* [comment removed for export] *) 0xa5000 + 88 <= bv_unsigned tp < 0x603000 ->
  rw_cells bsegs m (B + 8) [C4 szj] -> u64arr bsegs m (B + 16) ws -> length ws = 30%nat -> rw_cells bsegs m (B + 2056) [C8 bpj] ->
  rw_cells bsegs m (SP + -16) [C8 s0c; C8 rac] -> uanchor bsegs m SP rac s0c ->
  (forall a n, lo <= a -> a + Z.of_nat n <= 2^64 -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) ->
  (forall a n, T <= a -> a + Z.of_nat n <= T + 4096 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (unwind_impl_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc0 F fc m lo B T)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) pc0 (Z_to_bv 64 SP) a3 (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5bc44) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until rac. intros SK LOC LO SPB BSP SPR2 BOT TOP MI AI G1 G2 ((TC1 & TC2 & TC3 & TC4 & TC5) & T40 & T8 & TU) HT1 HT2 HC1 HC2 HT3 HT4 HTC HTP
         CSZ ARR LEN BPJ CL U PSTK PDAT PCTX PT.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PSTK' : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) by (intros; apply PSTK; lia).
  assert (MU : munch (uwiW sp B T) m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 80%nat SK.
  do 11 cstep.  (* [comment removed for export] *)
  do 6 cstep.   (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  eapply evtA_cut; [eapply asan_inited_walk; [exact MI| exact AI| exact PDAT]|]. cbv beta. intros ms' ->. ret_pc_lit.
  cstep.        (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  call_spA (get_current_thread_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
    [exact SK| exact LOC0| lia| lia| exact MI| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact HT1| exact HT2| exact HC1| aceil; lia
    | lia| exact HTP| intros; apply PSTK; lia| exact PDAT| exact PCTX|].
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }   (* [comment removed for export] *)
  rename POST into SK.
  do 4 cstep.   (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  eapply evtA_cut; [eapply (stack_top_walk2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T top bot);
    [eassumption| reflexivity| lia| aceil; lia| lia| lia| exact T40| exact T8| exact PT]|].
  cbv beta. intros ms' (a1' & ->). ret_pc_lit.
  do 3 cstep.   (* [comment removed for export] *)
  eapply evtA_cut; [eapply (stack_bottom_walk2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T top bot);
    [eassumption| reflexivity| lia| aceil; lia| lia| lia| exact T40| exact T8| exact PT]|].
  cbv beta. intros ms' (a1'' & ->). ret_pc_lit.
  cstep.        (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  do 8 cstep.   (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  call_spA (unwind_walk2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pc0 _ _ _ lo B SP top bot _ _ ws s0c rac);
    [exact SK| exact LOC0| lia| lia| lia| lia| lia| lia| eassumption| exact G1| exact G2| exact CSZ| exact ARR| exact LEN
    | exact BPJ| exact CL| | exact PSTK| exact PDAT|].
  { eapply uanchor_frame; [| exact U]. intros a Ha. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  rename PC into SK.
  cstep.        (* [comment removed for export] *)
  do 12 cstep.  (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp). unfold unwind_impl_post. finishA.
  all: first [exact PC0 | exact PC1 | exact PC2 | exact PC4 | exact PC5 | exact POST | lia].
Qed.
End Walk2.
End RC__1.
