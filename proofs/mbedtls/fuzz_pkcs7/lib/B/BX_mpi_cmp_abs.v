From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_mpi_cmp_mpi BX_mpi_cmp_abs_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition BX_CMPABS_H1 : Z := 0x9d740.
Definition BX_CMPABS_H2 : Z := 0x9d7f0.
Definition BX_CMPABS_H3 : Z := 0x9d878.

Lemma zlow32_range : forall x, 0 <= zlow 32 x < 2^32.
Proof. intros x. unfold zlow. apply Z.mod_pos_bound. lia. Qed.

Lemma zsw_lo : forall x, zlow 32 x < 2^31 -> zswrap 32 (zlow 32 x) = zlow 32 x.
Proof.
  intros x H. pose proof (zlow32_range x) as R. unfold zswrap. change (2 ^ (32 - 1)) with (2^31).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma zsw_hi : forall x, 2^31 <= zlow 32 x -> zswrap 32 (zlow 32 x) = zlow 32 x - 2^32.
Proof.
  intros x H. pose proof (zlow32_range x) as R. unfold zswrap. change (2 ^ (32 - 1)) with (2^31).
  rewrite <- (Z.mod_unique (zlow 32 x + 2^31) (2^32) 1 (zlow 32 x + 2^31 - 2^32)) by lia. lia.
Qed.

Lemma sxu_lo : forall x, zlow 32 x < 2^31 -> zlow 64 (zswrap 32 (zlow 32 x)) = zlow 32 x.
Proof.
  intros x H. rewrite (zsw_lo x H). pose proof (zlow32_range x) as R. unfold zlow at 1.
  apply Z.mod_small. lia.
Qed.

Lemma sxu_hi : forall x, 2^31 <= zlow 32 x -> zlow 64 (zswrap 32 (zlow 32 x)) = zlow 32 x + (2^64 - 2^32).
Proof.
  intros x H. rewrite (zsw_hi x H). pose proof (zlow32_range x) as R. unfold zlow at 1.
  rewrite <- (Z.mod_unique (zlow 32 x - 2^32) (2^64) (-1) (zlow 32 x + (2^64 - 2^32))) by lia. reflexivity.
Qed.

Lemma limb32_zlow : forall ws r w, nth_error ws (Z.to_nat (r - 1)) = Some w ->
  limb32 ws (Z.to_nat (r - 1)) = zlow 32 (bv_unsigned w).
Proof. intros ws r w H. rewrite (limb32_of_read ws r w H). reflexivity. Qed.

Lemma sgn_pos : forall a b, b < a -> Z.sgn (a - b) = 1.
Proof. intros a b H. apply Z.sgn_pos. lia. Qed.

Lemma sgn_neg : forall a b, a < b -> Z.sgn (a - b) = -1.
Proof. intros a b H. apply Z.sgn_neg. lia. Qed.

Ltac sxw w :=
  let Hw := fresh "Hw" in
  pose proof (zlow32_range (bv_unsigned w));
  destruct (Z_lt_le_dec (zlow 32 (bv_unsigned w)) (2^31)) as [Hw|Hw];
  [ rewrite ?(sxu_lo _ Hw), ?(zsw_lo _ Hw) in *
  | rewrite ?(sxu_hi _ Hw), ?(zsw_hi _ Hw) in * ].

Tactic Notation "lxa" uconstr(L) :=
  eapply evtA_eq; [ apply lx_MS_regs | eapply L ]; try lx_regs_eq; try lx_app.
Ltac post_munch := try (lazymatch goal with |- munch _ _ _ =>
  eapply munch_weaken; [| eassumption]; intros ?x ?Hx; cbn [outside] in *; lia end).

Lemma bytes_u32_keep : forall segs m m' A ws a b,
  bytes_at segs m A (u32s ws) -> munch [(a, b)] m m' ->
  (1 <= Z.of_nat (length ws) -> A + 4 * Z.of_nat (length ws) <= a \/ b <= A) ->
  bytes_at segs m' A (u32s ws).
Proof.
  intros segs m m' A ws a b H MU D. destruct ws as [|w ws'].
  - cbn in H |- *. pose proof (bytes_at_bound _ _ _ _ H) as B. cbn in B. apply bytes_at_nil. lia.
  - eapply bytes_at_transport; [exact H | exact MU |]. rewrite u32s_length. cbn [disjoint_from].
    split; [| exact I]. cbn [length] in D |- *. specialize (D ltac:(lia)). lia.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (lo : Z) (X P n sg : Z) (xs : list word) (pad : word) (Y Q n' sg' : Z) (ys : list word)
            (pad' : word).
  Hypothesis LXN : Z.of_nat (length xs) = n.
  Hypothesis HN : 0 <= n <= 10000.
  Hypothesis LYN : Z.of_nat (length ys) = n'.
  Hypothesis HN' : 0 <= n' <= 10000.
  Hypothesis XP : 0 < X.
  Hypothesis XA : X mod 8 = 0.
  Hypothesis YP : 0 < Y.
  Hypothesis YA : Y mod 8 = 0.
  Hypothesis PB : P + 4 * n <= 2^64.
  Hypothesis QB : Q + 4 * n' <= 2^64.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis XS : X + 16 <= lo \/ bv_unsigned sp <= X.
  Hypothesis YS : Y + 16 <= lo \/ bv_unsigned sp <= Y.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_cmp_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      (Z.sgn (lval xs n - lval ys n')) lo m).
  Notation W := [(bv_unsigned sp - 16, bv_unsigned sp)].
  Notation XC mm := (rw_cells asegs mm X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad]).
  Notation YC mm := (rw_cells asegs mm Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad']).

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Lemma loop3_walk : forall (k : nat) (r i : Z) (t2 t3 t4 t5 a3 a4 : word) (junk : list (bv 8)) (mm : mem),
    Z.to_nat r = k -> 0 <= r <= i -> SIGF xs n i -> SIGF ys n' i ->
    Z.sgn (lval xs i - lval ys i) = Z.sgn (lval xs r - lval ys r) ->
    (1 <= n -> 0 < P /\ P mod 4 = 0) -> (1 <= n' -> 0 < Q /\ Q mod 4 = 0) ->
    XC mm -> bytes_at asegs mm P (u32s xs) -> YC mm -> bytes_at asegs mm Q (u32s ys) ->
    aobj asegs AL CS mm X 16 -> aobj asegs AL CS mm Y 16 ->
    (1 <= n -> aobj asegs AL CS mm P (4 * n)) -> (1 <= n' -> aobj asegs AL CS mm Q (4 * n')) ->
    rw_cells asegs mm (bv_unsigned sp - 16) [CB 8 junk; C8 ra] -> stk asegs mm lo (bv_unsigned sp - 16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp (Z_to_bv 64 (r + 1)) (Z_to_bv 64 (al_sb AL + Y ≫ 3)) t2
               s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 1) a3 a4 (Z_to_bv 64 (al_sb AL))
               (Z_to_bv 64 (al_sb AL + X ≫ 3)) (Z_to_bv 64 (4 * r - 4)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BX_CMPABS_H3) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros r i t2 t3 t4 t5 a3 a4 junk mm Hk Hr SX SY Hsg PF QF
      CX BX CY BY OX OY OP OQ FR ST MU WM MI; al_facts; unfold BX_CMPABS_H3;
      pose proof SX as (SXi & SXv & SXt); pose proof SY as (SYi & SYv & SYt);
      lx_hide SX; lx_hide SY; lx_hide SXv; lx_hide SXt; lx_hide SYv; lx_hide SYt; lx_hide Hsg.
    - assert (r = 0) by lia. subst r.
      lx_hide OP; lx_hide OQ; lx_hide PF; lx_hide QF.
      lx_spell. lx_run_tac (PLAN [] [] 40%N). lx_tree.
      all: lx_unhide; try lx_same_mem.
      all: assert (E : Z.sgn (lval xs n - lval ys n') = 0)
             by (rewrite SXv, SYv, Hsg, !lval_0; reflexivity).
      all: rewrite E; lx_leaf.
      all: post_munch.
    - assert (R1 : 1 <= r) by lia.
      specialize (PF ltac:(lia)); specialize (QF ltac:(lia)); destruct PF as [PP PA]; destruct QF as [QP QA].
      specialize (OP ltac:(lia)); specialize (OQ ltac:(lia)).
      destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| exfalso; apply nth_error_None in NX; lia].
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| exfalso; apply nth_error_None in NY; lia].
      pose proof (u32ro_cell_at mm P xs (r - 1) (P + 4 * (r - 1)) wx BX NX ltac:(lia) eq_refl) as CSx.
      pose proof (u32ro_cell_at mm Q ys (r - 1) (Q + 4 * (r - 1)) wy BY NY ltac:(lia) eq_refl) as CSy.
      pose proof (limb32_zlow xs r wx NX) as LX1. pose proof (limb32_zlow ys r wy NY) as LY1.
      lx_hide LX1; lx_hide LY1.
      lx_spell. lx_run_tac (PLAN [BX_CMPABS_H3] [(0x9d8c0, DJoin); (0x9d908, DJoin)] 80%N). lx_tree.
      all: lx_unhide; try lx_same_mem; sxw wx; sxw wy.
      all: try (lazymatch goal with
           | |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
               first
                 [ assert (E : Z.sgn (lval xs n - lval ys n') = 1)
                     by (rewrite SXv, SYv, Hsg; apply cmp_step_gt; [lia | rewrite LX1, LY1; lia]);
                   rewrite E; lx_leaf
                 | assert (E : Z.sgn (lval xs n - lval ys n') = -1)
                     by (rewrite SXv, SYv, Hsg; apply cmp_step_lt; [lia | rewrite LX1, LY1; lia]);
                   rewrite E; lx_leaf ]
           end).
      all: post_munch.
      all: assert (Hsg' : Z.sgn (lval xs i - lval ys i) = Z.sgn (lval xs (r - 1) - lval ys (r - 1)))
                 by (rewrite Hsg; apply cmp_step_eq; [lia | rewrite LX1, LY1; lia]).
      all: lxa (IH (r - 1) i _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) SX SY Hsg'
                  (fun _ => conj PP PA) (fun _ => conj QP QA) CX BX CY BY OX OY (fun _ => OP) (fun _ => OQ)).
  Qed.

  Lemma loop2_walk : forall (k : nat) (i j : Z) (a4 t3 t4 t5 : word) (junk : list (bv 8)) (mm : mem),
    Z.to_nat j = k -> 0 <= j <= n' -> lval ys n' = lval ys j -> SIGF xs n i ->
    (1 <= n -> 0 < P /\ P mod 4 = 0) -> (1 <= n' -> 0 < Q /\ Q mod 4 = 0) ->
    XC mm -> bytes_at asegs mm P (u32s xs) -> YC mm -> bytes_at asegs mm Q (u32s ys) ->
    aobj asegs AL CS mm X 16 -> aobj asegs AL CS mm Y 16 ->
    (1 <= n -> aobj asegs AL CS mm P (4 * n)) -> (1 <= n' -> aobj asegs AL CS mm Q (4 * n')) ->
    rw_cells asegs mm (bv_unsigned sp - 16) [CB 8 junk; C8 ra] -> stk asegs mm lo (bv_unsigned sp - 16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (al_sb AL + Y ≫ 3))
               (Z_to_bv 64 (4 * j - 4)) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 j) (Z_to_bv 64 i) a4
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + X ≫ 3)) (Z_to_bv 64 (4 * i - 4))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BX_CMPABS_H2) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros i j a4 t3 t4 t5 junk mm Hk Hj HY SX PF QF
      CX BX CY BY OX OY OP OQ FR ST MU WM MI; al_facts; unfold BX_CMPABS_H2;
      pose proof SX as (SXi & SXv & SXt); lx_hide HY; lx_hide SX; lx_hide SXv; lx_hide SXt;
      lx_hide OP; lx_hide PF.
    - assert (j = 0) by lia. subst j.
      lx_hide OQ; lx_hide QF.
      lx_spell. lx_run_tac (PLAN [BX_CMPABS_H3] [] 40%N). lx_tree.
      all: lx_unhide; try lx_same_mem.
      all: assert (SY : SIGF ys n' 0) by (split; [lia | split; [exact HY | left; reflexivity]]).
      all: try lazymatch goal with
           | |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
               assert (E : Z.sgn (lval xs n - lval ys n') = 1)
                 by (apply sgn_pos; eapply SIGF_lt; [exact SX | exact SY | lia]);
               rewrite E; lx_leaf
           | |- _ =>
               assert (I0 : i = 0) by lia; subst i;
               lxa (loop3_walk _ 0 0 _ _ _ _ _ _ _ _ eq_refl ltac:(lia) SX SY eq_refl PF QF
                           CX BX CY BY OX OY OP OQ)
           end.
      all: post_munch.
    - assert (J1 : 1 <= j) by lia.
      pose proof (QF ltac:(lia)) as [QP QA]; pose proof (OQ ltac:(lia)) as OQ1.
      destruct (nth_error ys (Z.to_nat (j - 1))) as [wy|] eqn:NY; [| exfalso; apply nth_error_None in NY; lia].
      pose proof (u32ro_cell_at mm Q ys (j - 1) (Q + 4 * (j - 1)) wy BY NY ltac:(lia) eq_refl) as CSy.
      pose proof (limb32_zlow ys j wy NY) as LY1. lx_hide LY1. lx_hide OQ; lx_hide QF.
      lx_spell. lx_run_tac (PLAN [BX_CMPABS_H2; BX_CMPABS_H3] [(0x9d838, DJoin)] 80%N). lx_tree.
      all: lx_unhide; try lx_same_mem; sxw wy.
      all: try lazymatch goal with
           | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0x9d7f0) _ _ _ _) =>
               assert (HY' : lval ys n' = lval ys (j - 1))
                 by (rewrite HY; apply lval_drop_zero; [lia | rewrite LY1; lia]);
               lxa (IH i (j - 1) _ _ _ _ _ _ ltac:(lia) ltac:(lia) HY' SX PF QF
                           CX BX CY BY OX OY OP OQ)
           | |- _ =>
               assert (SY : SIGF ys n' j)
                 by (split; [lia | split; [exact HY | right; apply lval_top_nonzero; [lia | rewrite LY1; lia]]]);
               lazymatch goal with
               | |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
                   first
                     [ assert (E : Z.sgn (lval xs n - lval ys n') = 1)
                         by (apply sgn_pos; eapply SIGF_lt; [exact SX | exact SY | lia]);
                       rewrite E; lx_leaf
                     | assert (E : Z.sgn (lval xs n - lval ys n') = -1)
                         by (apply sgn_neg; eapply SIGF_lt; [exact SY | exact SX | lia]);
                       rewrite E; lx_leaf ]
               | |- _ =>
                   assert (IJ : i = j) by lia; subst i;
                   lxa (loop3_walk _ j j _ _ _ _ _ _ _ _ eq_refl ltac:(lia) SX SY eq_refl PF QF
                               CX BX CY BY OX OY OP OQ)
               end
           end.
      all: post_munch.
  Qed.

  Lemma loop1_walk : forall (k : nat) (i : Z) (t1 t2 a3 a7 t3 t4 t5 : word) (junk : list (bv 8)) (mm : mem),
    Z.to_nat i = k -> 0 <= i <= n -> lval xs n = lval xs i ->
    (1 <= n -> 0 < P /\ P mod 4 = 0) -> (1 <= n' -> 0 < Q /\ Q mod 4 = 0) ->
    XC mm -> bytes_at asegs mm P (u32s xs) -> YC mm -> bytes_at asegs mm Q (u32s ys) ->
    aobj asegs AL CS mm X 16 -> aobj asegs AL CS mm Y 16 ->
    (1 <= n -> aobj asegs AL CS mm P (4 * n)) -> (1 <= n' -> aobj asegs AL CS mm Q (4 * n')) ->
    rw_cells asegs mm (bv_unsigned sp - 16) [CB 8 junk; C8 ra] -> stk asegs mm lo (bv_unsigned sp - 16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp (Z_to_bv 64 (4 * i - 4)) t1 t2 s0 s1
               (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 i) a3 (Z_to_bv 64 (-4)) (Z_to_bv 64 (al_sb AL))
               (Z_to_bv 64 (al_sb AL + X ≫ 3)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BX_CMPABS_H1) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros i t1 t2 a3 a7 t3 t4 t5 junk mm Hk Hi HX PF QF
      CX BX CY BY OX OY OP OQ FR ST MU WM MI; al_facts; unfold BX_CMPABS_H1; lx_hide HX;
      lx_hide OQ; lx_hide QF.
    - assert (i = 0) by lia. subst i.
      lx_hide OP; lx_hide PF.
      lx_spell. lx_run_tac (PLAN [BX_CMPABS_H2] [(0x9d7d4, DJoin)] 80%N). lx_tree.
      all: lx_unhide; try lx_same_mem.
      all: assert (SX : SIGF xs n 0) by (split; [lia | split; [exact HX | left; reflexivity]]).
      all: try lxa (loop2_walk _ 0 n' _ _ _ _ _ _ eq_refl ltac:(lia) eq_refl SX PF QF CX BX CY BY OX OY OP OQ).
    - assert (I1 : 1 <= i) by lia.
      pose proof (PF ltac:(lia)) as [PP PA]; pose proof (OP ltac:(lia)) as OP1.
      destruct (nth_error xs (Z.to_nat (i - 1))) as [wx|] eqn:NX; [| exfalso; apply nth_error_None in NX; lia].
      pose proof (u32ro_cell_at mm P xs (i - 1) (P + 4 * (i - 1)) wx BX NX ltac:(lia) eq_refl) as CSx.
      pose proof (limb32_zlow xs i wx NX) as LX1. lx_hide LX1. lx_hide OP; lx_hide PF.
      lx_spell. lx_run_tac (PLAN [BX_CMPABS_H1; BX_CMPABS_H2] [(0x9d78c, DJoin); (0x9d7d4, DJoin)] 80%N). lx_tree.
      all: lx_unhide; try lx_same_mem; sxw wx.
      all: try lazymatch goal with
           | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0x9d740) _ _ _ _) =>
               assert (HX' : lval xs n = lval xs (i - 1))
                 by (rewrite HX; apply lval_drop_zero; [lia | rewrite LX1; lia]);
               lxa (IH (i - 1) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) HX' PF QF CX BX CY BY OX OY OP OQ)
           | |- _ =>
               assert (SX : SIGF xs n i)
                 by (split; [lia | split; [exact HX | right; apply lval_top_nonzero; [lia | rewrite LX1; lia]]]);
               lxa (loop2_walk _ i n' _ _ _ _ _ _ eq_refl ltac:(lia) eq_refl SX PF QF CX BX CY BY OX OY OP OQ)
           end.
  Qed.

  Lemma main_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 : word),
    (1 <= n -> 0 < P /\ P mod 4 = 0) -> (1 <= n' -> 0 < Q /\ Q mod 4 = 0) ->
    (1 <= n -> P + 4 * n <= lo \/ bv_unsigned sp <= P) -> (1 <= n' -> Q + 4 * n' <= lo \/ bv_unsigned sp <= Q) ->
    XC m -> bytes_at asegs m P (u32s xs) -> YC m -> bytes_at asegs m Q (u32s ys) ->
    mem_inv asegs m -> abase asegs AL m ->
    aobj asegs AL CS m X 16 -> aobj asegs AL CS m Y 16 ->
    (1 <= n -> aobj asegs AL CS m P (4 * n)) -> (1 <= n' -> aobj asegs AL CS m Q (4 * n')) ->
    stk asegs m lo (bv_unsigned sp) ->
    evtA asegs AL CS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BX_MPI_CMP_ABS) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 PF QF PS QS CX BX CY BY MI AB OX OY OP OQ ST. al_facts.
    unfold BX_MPI_CMP_ABS.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide OP; lx_hide OQ; lx_hide PS; lx_hide QS; lx_hide PF; lx_hide QF; lx_hide BX; lx_hide BY.
    carve_frame 16%nat ST.
    lx_spell. lx_run_tac (PLAN [BX_CMPABS_H1] [(0x9d724, DJoin)] 60%N). lx_tree.
    all: lx_unhide.
    all: lazymatch goal with H : munch [(?a, ?b)] m ?mx |- _ =>
           pose proof (bytes_u32_keep asegs m mx P xs a b BX H
                         ltac:(intros Hl; rewrite LXN in Hl |- *; destruct (PS Hl); lia)) as BX';
           pose proof (bytes_u32_keep asegs m mx Q ys a b BY H
                         ltac:(intros Hl; rewrite LYN in Hl |- *; destruct (QS Hl); lia)) as BY';
           assert (OP' : 1 <= n -> aobj asegs AL CS mx P (4 * n))
             by (intros Hn; eapply (aobj_munch asegs AL CS CSOK [(a, b)]);
                 first [ exact H | exact (OP Hn)
                       | unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS | lia | lia]
                                                            | apply Forall_nil] ]);
           assert (OQ' : 1 <= n' -> aobj asegs AL CS mx Q (4 * n'))
             by (intros Hn; eapply (aobj_munch asegs AL CS CSOK [(a, b)]);
                 first [ exact H | exact (OQ Hn)
                       | unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS | lia | lia]
                                                            | apply Forall_nil] ])
         end.
    all: lxa (loop1_walk _ n _ _ _ _ _ _ _ _ _ eq_refl ltac:(lia) eq_refl PF QF).
  Qed.
End Walk.

Theorem BX_mpi_cmp_abs_raw_spec : forall AL, asan_img_ok AL -> mpi_cmp_abs_raw_stmtA asegs AL BX_MPI_CMP_ABS.
Proof.
  intros AL IMG.
  unfold mpi_cmp_abs_raw_stmtA. intros until pad'.
  intros CX BX LX NX PBX XP ALX CY BY LY NY PBY YP ALY MI ALWF CSOK AB OX OY OP OQ ST LO0 SLO SPA SCS XS YS PS QS -> ->.
  unfold MPI_CMP_ABS_STACK_A in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  pose proof (u32ro_bound _ _ _ _ BX) as PBB. pose proof (u32ro_bound _ _ _ _ BY) as QBB.
  rewrite LX in PBB. rewrite LY in QBB.
  assert (PF : 1 <= n -> 0 < P /\ P mod 4 = 0) by (intros; destruct PBX; [lia | assumption]).
  assert (QF : 1 <= n' -> 0 < Q /\ Q mod 4 = 0) by (intros; destruct PBY; [lia | assumption]).
  eapply main_walk; try eassumption; try lia.
Qed.

Theorem BX_mpi_cmp_abs_spec : forall AL, asan_img_ok AL -> mpi_cmp_abs_stmtA asegs AL BX_MPI_CMP_ABS.
Proof.
  intros AL IMG. unfold mpi_cmp_abs_stmtA. intros until lo.
  intros HX HY PX PY MI ALWF CSOK AB OX OY OP OQ ST LO0 SLO SPA SCS XS YS PS QS -> ->.
  pose proof (proj1 (proj2 (proj1 HX))) as ALX. pose proof (proj1 (proj2 (proj1 HY))) as ALY.
  pose proof (proj1 (proj2 (proj2 (proj1 HX)))) as XP. pose proof (proj1 (proj2 (proj2 (proj1 HY)))) as YP.
  destruct (mpd_raw _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  destruct (mpd_raw _ _ _ _ HY PY) as (CY & BY & LY & NY & SY & ABY & PBY).
  rewrite !mpd_abs_lval by assumption.
  eapply BX_mpi_cmp_abs_raw_spec; try eassumption; try reflexivity.
Qed.
