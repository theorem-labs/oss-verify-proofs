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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_unwind BF_unwind_walk2 BF_free_kit BF_ia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
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
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section FREE0.
Variable P : acc -> Prop.
Variables (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (usp lo p : Z) (ii : bool) (izl : list byte) (TSD CTX T top bot : Z).   (* [comment removed for export] *)
Notation IA := 0xaf7c0.
(* [comment removed for export] *)
Hypothesis SK : stk bsegs m lo usp.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 4096.
Hypothesis SPH' : usp < 2^47.                                                 (* [comment removed for export] *)
Hypothesis TOP : top <= 2^47.
Hypothesis BOT : 0 <= bot < top.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis U : uanchor bsegs m usp ra s0.
Hypothesis MI : mem_inv bsegs m.
Hypothesis Hp : 0 <= p < 2^47.
(* [comment removed for export] *)
Hypothesis AI : rw_cells bsegs m 0xaf298 [C1 (Z_to_bv 8 1)].                  (* [comment removed for export] *)
Hypothesis G1 : rw_cells bsegs m 0xa5580 [C8 (Z_to_bv 64 0x13e060)].         (* [comment removed for export] *)
Hypothesis G2 : rw_cells bsegs m 0x13e060 [C8 (Z_to_bv 64 4096)].             (* [comment removed for export] *)
Hypothesis MCS : rw_cells bsegs m 0xaf2bc [C4 (Z_to_bv 64 30)].              (* [comment removed for export] *)
Hypothesis GCF : rw_cells bsegs m 0xa5590 [C8 (Z_to_bv 64 0x1400e8)].        (* [comment removed for export] *)
Hypothesis FUM : rw_cells bsegs m 0x14010a [C1 (Z_to_bv 8 1)].               (* [comment removed for export] *)
Hypothesis IAF : rw_cells bsegs m 0x13e048 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0].      (* [comment removed for export] *)
Hypothesis IWR : wr_at bsegs m IA 0x81030.                                     (* [comment removed for export] *)
Hypothesis IZ : u8arr bsegs m (IA + 8) izl.                                    (* [comment removed for export] *)
Hypothesis EZ : izl = repeat zb0 (Z.to_nat 0x40000).
Hypothesis IPV : ii = true -> rw_cells bsegs m (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))].
(* [comment removed for export] *)
Hypothesis UT : uthread_cells m tp TSD CTX T top bot.
Hypothesis HT1 : 0x5d0810 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.     (* [comment removed for export] *)
Hypothesis HC1 : 0x603000 <= CTX. Hypothesis HC2 : CTX + 4096 <= alloc_ceiling. (* [comment removed for export] *)
Hypothesis HT3 : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)).   (* [comment removed for export] *) Hypothesis HT4 : T + 4096 <= alloc_ceiling.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTP : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000.                 (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= 2^64 -> P (Z_to_bv 64 a, n).   (* [comment removed for export] *)
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a n, T <= a -> a + Z.of_nat n <= T + 4096 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Lemma free_pro :
  (forall m' (t0' t1' a3' a4' a5' a6' a7' s3' : word) (ws tr : list word) (j1800 j8 : list byte) (bpw : word),
     mem_inv bsegs m' -> stk bsegs m' lo (usp + -2128) -> wmono bsegs m m' ->
     munch [(lo, usp); (IA, IA + 0x81030); (0x13e048, 0x13e04c); (T + 3168, T + 3169)] m m' ->
     rw_cells bsegs m' 0x13e048 [C1 (Z_to_bv 8 1); C1 zb0] ->
     rw_cells bsegs m' (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))] ->
     u8arr bsegs m' (IA + 8) izl -> wr_at bsegs m' IA 0x81030 ->
     uthread_cells m' tp TSD CTX T top bot ->
     (* [comment removed for export] *)
     rw_cells bsegs m' (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C4 (Z_to_bv 64 (Z.of_nat (length tr))); C4 (Z_to_bv 64 0)] ->
     u64arr bsegs m' (usp + -2112) ws -> length ws = 30%nat -> firstn (length tr) ws = tr -> (1 <= length tr <= 30)%nat ->
     rw_cells bsegs m' (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells bsegs m' (usp + -1872) [CB 1800 j1800] -> rw_cells bsegs m' (usp + -72) [C8 bpw] -> rw_cells bsegs m' (usp + -64) [CB 8 j8] ->
     evtA bsegs P Q (MS (mkR (Z_to_bv 64 0x54058) (Z_to_bv 64 (usp + -2128)) gp tp t0' t1' t2 (Z_to_bv 64 usp) (Z_to_bv 64 p)
                             (Z_to_bv 64 p) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 1) a3' a4' a5' a6' a7'
                             (Z_to_bv 64 0x53fe8) s3' (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x326d0) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x53eb0) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros CONT.
  assert (IZL : Z.of_nat (length izl) = 0x40000) by (rewrite EZ, repeat_length; lia).
  (* [comment removed for export] *)
  assert (IPS : exists psz chk, rw_cells bsegs m (IA + 0x40dc0) [C8 psz; C8 chk] /\ (ii = true -> psz = Z_to_bv 64 4096 /\ chk = Z_to_bv 64 (IA + 0x40dd0))).
  { destruct ii.
    - exists (Z_to_bv 64 4096), (Z_to_bv 64 (IA + 0x40dd0)). split; [exact (IPV eq_refl)| intros _; split; reflexivity].
    - destruct (wr_at_c8c8 m (IA + 0x40dc0) ltac:(eapply wr_at_sub; [exact IWR| lia| lia])) as (v & w & H).
      exists v, w. split; [exact H| intros X; discriminate X]. }
  clear IPV. destruct IPS as (psz & chk & IPS & IPV).
  destruct UT as ((TC1 & TC2 & TC3 & TC4 & TC5) & T40 & T8 & TU).
  pose proof LOC as LOC0. aceil.
  assert (SPR : 0 <= usp < 2^64) by lia.
  assert (MU : munch [(lo, usp); (IA, IA + 0x81030); (0x13e048, 0x13e04c); (T + 3168, T + 3169)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 56%nat SK.     (* [comment removed for export] *)
  carve_frame 8%nat SK. rename FR0 into FJ8.     (* [comment removed for export] *)
  carve_frame 8%nat SK. rename FR0 into FBP.     (* [comment removed for export] *)
  carve_frame 1800%nat SK. rename FR0 into FJ1800. (* [comment removed for export] *)
  carve_frame 240%nat SK. rename FR0 into FBUF.  (* [comment removed for export] *)
  carve_frame 16%nat SK. rename FR0 into FOBJ.   (* [comment removed for export] *)
  frame_stores 8 FR. (* [comment removed for export] *)
  do 4 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply ia_walk2; rewrite ?(unsigned_lit (usp + -2128)) by lia; [exact SK| exact LOC0| lia| lia| exact MI| exact IAF| exact G2| exact G1| exact IWR| exact IZ| exact EZ| exact IPS| exact IPV
    | intros; apply PSTK; lia| exact PDAT|].
  clear MI SK IAF IWR IZ IPS IPV. intros m1 a1' a2' a3' a4' a5' a6' MI SK WM1 MU1 IAF PSC IZ IWR. rewrite ?(unsigned_lit (usp + -2128)) in SK, MU1 by lia.
  after_call m0 m1 MU1 WM1. ret_pc_lit.
  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  do 3 zstepA. (* [comment removed for export] *)
  set (k := Z.shiftr p 32) in *.
  assert (Hk : 0 <= k < 2^15) by (subst k; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  rewrite (Z.shiftl_mul_pow2 k 3) by lia. change (2^3) with 8.
  pose proof (bytes_at_read bsegs m1 (718784 + 8) izl (8 * k) 8 (proj1 IZ) ltac:(lia) ltac:(rewrite EZ, repeat_length; lia)) as RD.
  rewrite EZ, skipn_repeat0, firstn_repeat0 in RD by lia. cbn [repeat] in RD. replace (718784 + 8 + 8 * k) with (718784 + k * 8 + 8) in RD by lia.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  leafA (gmcs_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30); [exact MI| lia| exact MCS| exact PDAT|].
  zstepA. cstep. (* [comment removed for export] *)
  zstepA. leafA (getpc_walk P); [exact MI|].
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. leafA (gmcs_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30); [exact MI| lia| exact MCS| exact PDAT|].
  do 5 zstepA. (* [comment removed for export] *)
  replace (Z.land ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) usp) with usp.
  2:{ change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
      symmetry. apply Z.mod_small. change (2 ^ 64) with 18446744073709551616 in SPR. lia. }
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  do 6 zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (FOBJ2 : rw_cells bsegs mx (usp + -2128) ([C8 (Z_to_bv 64 (usp + -2112))] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]))
      by (eapply rw_cells_reshape; [| | exact FOBJ]; [cells_wf_triv| reflexivity]) end.
  clear FOBJ. apply rwc_split in FOBJ2. destruct FOBJ2 as [FOBJ CSZ]. cbn [cells_size csize Nat.add] in CSZ.
  replace (usp + -2128 + Z.of_nat 8) with (usp + -2128 + 8) in CSZ by lia.
  change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] with ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)]) in CSZ.
  apply rwc_split in CSZ. destruct CSZ as [CSZ TAG]. cbn [cells_size csize Nat.add] in TAG.
  replace (usp + -2128 + 8 + Z.of_nat 4) with (usp + -2128 + 12) in TAG by lia.
  destruct (u64arr_of_cb bsegs _ _ _ 30 FBUF) as (ws0 & LEN0 & ARR0). clear FBUF.
  change [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] with ([C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
  apply rwc_split in FR. destruct FR as [FR CL]. cbn [cells_size csize Nat.add] in CL.
  replace (usp + -56 + Z.of_nat 40) with (usp + -16) in CL by lia.
  zstepA. (* [comment removed for export] *)
  pose proof (unsigned_lit (usp + -2128) ltac:(lia)) as Hsp.
  callA (unwind_impl_walk2 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ _ TSD CTX T top bot _ _ ws0 s0 ra);
    rewrite ?Hsp;
    [exact SK| exact LOC0| lia| lia| lia| exact SPH'| exact BOT| exact TOP| exact MI| exact AI| exact G1| exact G2
    | exact (conj (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5)))) (conj T40 (conj T8 TU)))
    | lia| exact HT2| lia| exact HC2| exact HT3| exact HT4| lia| lia
    | exact CSZ
    | replace (usp + -2128 + 16) with (usp + -2112) by lia; exact ARR0| exact LEN0
    | replace (usp + -2128 + 2056) with (usp + -72) by lia; exact FBP
    | exact CL
    | eapply uanchor_frame; [| exact U]; intros a Ha; apply MU; rewrite wa_unsigned by lia; cbn; lia
    | exact PSTK| exact PDAT| exact PCTX| exact PT|].
  rewrite Hsp in PC. rename PC into SK. rename MI0 into MI.
  do 4 zstepA. zstepA. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (rwc_join_at bsegs mx _ _ _ _ FOBJ (rwc_join_at bsegs mx _ _ _ _ PC5 TAG ltac:(cbn; lia)) ltac:(cbn; lia)) as OBJ;
    pose proof (rwc_join_at bsegs mx _ _ _ _ FR CL ltac:(cbn; lia)) as FRX end.
  cbn [app] in OBJ, FRX.
  eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact IAF| exact PSC| exact IZ| exact IWR
    | exact (conj (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5)))) (conj T40 (conj T8 POST)))
    | exact OBJ| replace (usp + -2112) with (usp + -2128 + 16) by lia; exact PC0| exact PC1| exact PC2| exact PC3
    | exact FRX| exact FJ1800| replace (usp + -72) with (usp + -2128 + 2056) by lia; exact PC6| exact FJ8].
  Unshelve. all: exact (Z_to_bv 64 0).   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma dealloc0_walk : forall (rax spx bx cx a3x a4x a5x s0x s1x s2x s3x s4x s5x t0x t1x a6x a7x : word) mx lox,
  stk bsegs mx lox (bv_unsigned spx) -> alloc_ceiling <= lox -> lox <= bv_unsigned spx - 64 -> bv_unsigned spx <= 2^47 -> mem_inv bsegs mx ->
  (forall a n, lox <= a -> a + Z.of_nat n <= bv_unsigned spx -> P (Z_to_bv 64 a, n)) ->
  (forall m', mem_inv bsegs m' -> stk bsegs m' lox (bv_unsigned spx) -> wmono bsegs mx m' -> munch [(bv_unsigned spx - 64, bv_unsigned spx)] mx m' ->
     evtA bsegs P Q (MS (mkR rax spx gp tp t0x t1x t2 s0x s1x (Z_to_bv 64 0xaaf58) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) bx cx a6x a7x
                             s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rax) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR rax spx gp tp t0x t1x t2 s0x s1x (Z_to_bv 64 0) bx cx a3x a4x a5x a6x a7x
                          s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x326d0) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until lox. intros SKx LOCx LOx SPHx MIx PSTKx CONTx.
  aceil.
  pose proof (bv_unsigned_in_range _ spx) as SPRx. change (bv_modulus 64) with (2^64) in SPRx.
  assert (MUx : munch [(bv_unsigned spx - 64, bv_unsigned spx)] mx mx) by apply munch_refl.
  assert (WMx : wmono bsegs mx mx) by apply wmono_refl.
  do 10 zstepA. (* [comment removed for export] *)
  carve_frame 64%nat SKx.
  frame_stores 9 FR. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  do 9 zstepA. (* [comment removed for export] *)
  release_frame FR SKx (bv_unsigned spx).
  zstepA. (* [comment removed for export] *)
  eapply CONTx; [exact MIx| exact SKx| exact WMx| exact MUx].
Qed.

(* [comment removed for export] *)
Lemma free_null_walk : p = 0 ->
  (forall m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word),
     mem_inv bsegs m' -> stk bsegs m' lo usp -> wmono bsegs m m' ->
     munch [(lo, usp); (IA, IA + 0x81030); (0x13e048, 0x13e04c); (T + 3168, T + 3169)] m m' ->
     rw_cells bsegs m' 0x13e048 [C1 (Z_to_bv 8 1); C1 zb0] ->
     rw_cells bsegs m' (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))] ->
     u8arr bsegs m' (IA + 8) izl -> wr_at bsegs m' IA 0x81030 ->
     uthread_cells m' tp TSD CTX T top bot ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x53eb0) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros P0 CONT. pose proof LOC as LOC0. aceil.
  apply free_pro. clear MI SK. intros m1 t0' t1' a3' a4' a5' a6' a7' s3' ws tr j1800 j8 bpw MI1 SK1 WM1 MU1 IAF1 PSC1 IZ1 IWR1 UT1 OBJ ARR LEN FT LT FRX FJ1800 FBP FJ8.
  pose proof UT1 as ((TC1 & TC2 & TC3 & TC4 & TC5) & T40 & T8 & TU). clear UT1.
  assert (IZL : Z.of_nat (length izl) = 0x40000) by (rewrite EZ, repeat_length; lia).
  rewrite P0. pose proof (unsigned_lit (usp + -2128) ltac:(lia)) as Hsp.
  eapply dealloc0_walk; rewrite ?Hsp; [exact SK1| exact LOC0| lia| lia| exact MI1| intros; apply PSTK; lia|].
  clear MI1 SK1. intros m2 MI SK WM2 MU2. rewrite ?Hsp in SK, MU2.
  after_call m1 m2 MU2 WM2. ret_pc_lit.
  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 7 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  pose proof (cb_of_u64arr bsegs _ _ _ ARR) as FBUF. rewrite LEN in FBUF. clear ARR.
  release_frame OBJ SK (usp + -2112). release_frame FBUF SK (usp + -1872). release_frame FJ1800 SK (usp + -72).
  release_frame FBP SK (usp + -64). release_frame FJ8 SK (usp + -56). release_frame FRX SK usp.
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact SK| exact WM1| exact MU1| exact IAF1| exact PSC1| exact IZ1| exact IWR1
    | exact (conj (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5)))) (conj T40 (conj T8 TU)))].
Qed.
End FREE0.
End RC__1.
