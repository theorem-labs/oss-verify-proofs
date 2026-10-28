From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_MPI_CMP_ABS : Z := 0x20148.

Section WalkA.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X P n sg : Z) (xs : list word) (pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells usegs m X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at usegs m P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis CY : rw_cells usegs m Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at usegs m Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis YB : 0 <= Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis XA : X mod 8 = 0.
  Hypothesis XN : 0 < X.
  Hypothesis YA : Y mod 8 = 0.
  Hypothesis YN : 0 < Y.
  Hypothesis PR : 0 <= P /\ P + 4 * n <= 2^64.
  Hypothesis QR : 0 <= Q /\ Q + 4 * n' <= 2^64.

  Let POST (T : Z) := mpi_cmp_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T m.

  Local Ltac pc_norm :=
    repeat match goal with
    | H : context [zlow 64 (zswrap 32 (zlow 32 (bv_unsigned ?w)))] |- _ => rewrite (sw_sxz_w w) in H
    end;
    repeat match goal with
    | H : (sxz ?u <? sxz ?v) = _ |- _ => rewrite (sxz_ltb u v (w32_range _) (w32_range _)) in H
    end;
    repeat match goal with
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    end;
    repeat match goal with
    | H : context [zlow 64 ?x] |- _ => rewrite (zlow64_small x) in H by lia
    end;
    repeat match goal with
    | H : sxz (w32 ?w) = 0 |- _ => apply (sxz_zero_iff _ (w32_range w)) in H
    | H : sxz (w32 ?w) <> 0 |- _ => rewrite (sxz_zero_iff _ (w32_range w)) in H
    end.

  Local Ltac same_mem := lazymatch goal with H : ?l = m |- _ => subst l end.

  Local Ltac sxz_order wa wb :=
    destruct (Z.lt_trichotomy (w32 wa) (w32 wb)) as [SO|[SO|SO]];
    [ pose proof (proj2 (sxz_lt_iff _ _ (w32_range wa) (w32_range wb)) SO)
    | rewrite SO in *
    | pose proof (proj2 (sxz_lt_iff _ _ (w32_range wb) (w32_range wa)) SO) ].

  Local Ltac ret_post :=
    apply evt_done; subst POST; unfold mpi_cmp_post; cbv beta; do 14 eexists;
    split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl| assumption].

  Local Ltac ret_with T :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace (Z_to_bv 64 v) with (Z_to_bv 64 T); [ret_post|]
    end.

  Lemma a_loop3 : forall (k : nat) (r T : Z) (w2 w3 w4 a5 a6 a7 x0 x1 x2 : word),
    Z.to_nat r = k -> 1 <= r -> r <= n -> r <= n' ->
    T = Z.sgn (lval xs r - lval ys r) ->
    w2 = Z_to_bv 64 1 -> w3 = Z_to_bv 64 (4 * r - 4) -> w4 = Z_to_bv 64 r ->
    evt usegs (POST T)
      (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) w2 w3 w4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131616) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros r T w2 w3 w4 a5 a6 a7 x0 x1 x2 Hk Hr Rn Rn' HT -> -> ->; [lia|].
    destruct PB as [N0|[PP PAL]]; [lia|]. destruct QB as [N0|[QP QAL]]; [lia|].
    lx_limb HX (r - 1) wx VX. lx_limb HY (r - 1) wy VY.
    lx_run_tac (PLAN [131616; 131744] [] 200%N); lx_tree.
    all: same_mem; pc_norm.
    all: sxz_order wx wy.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 131616) _ _ _ _] =>
             eapply (IH (r - 1) T);
             [ lia | lia | lia | lia | rewrite HT, (cmp_step_eq xs ys r) by lia; reflexivity
             | reflexivity | f_equal; lia | f_equal; lia ]
         | |- _ =>
             ret_with T; f_equal; rewrite HT;
             first [ rewrite (cmp_step_gt xs ys r) by lia; lia
                   | rewrite (cmp_step_lt xs ys r) by lia; lia
                   | rewrite (cmp_step_eq xs ys r) by lia; replace (r - 1) with 0 by lia;
                     rewrite !lval_0, Z.sub_diag; reflexivity ]
         end.
  Qed.

  Lemma a_decide : forall (i j : Z) (w3 w4 w5 w6 a2 a7 x0 x1 x2 : word),
    SIGF xs n i -> SIGF ys n' j ->
    w3 = Z_to_bv 64 (4 * i - 4) -> w4 = Z_to_bv 64 (i + 1) -> w5 = Z_to_bv 64 i -> w6 = Z_to_bv 64 j ->
    evt usegs (POST (Z.sgn (lval xs n - lval ys n')))
      (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 w3 w4 w5 w6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131596) fc None m (seg_rom usegs)).
  Proof.
    intros i j w3 w4 w5 w6 a2 a7 x0 x1 x2 SX SY -> -> -> ->.
    pose proof SX as (I1 & I2 & I3). pose proof SY as (J1 & J2 & J3). lx_hide I3. lx_hide J3.
    pose proof (lval_range xs n ltac:(lia)) as RX. pose proof (lval_range ys n' ltac:(lia)) as RY.
    lx_run_tac (PLAN [131616; 131744] [] 200%N); lx_tree.
    all: same_mem; pc_norm.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 131616) _ _ _ _] =>
             assert (Eji : j = i) by lia;
             eapply (a_loop3 (Z.to_nat i) i);
             [ reflexivity | lia | lia | lia | rewrite I2, J2, Eji; reflexivity
             | reflexivity | f_equal; lia | f_equal; lia ]
         | |- _ =>
             ret_with (Z.sgn (lval xs n - lval ys n')); f_equal;
             destruct (Z.lt_trichotomy i j) as [L|[L|L]];
             [ pose proof (SIGF_lt ys n' j xs n i SY SX L)
             | destruct (SIGF_eq xs n i ys n' j SX SY L) as [(? & ? & ?)|(? & ? & ?)]
             | pose proof (SIGF_lt xs n i ys n' j SX SY L) ];
             match goal with |- Z.sgn ?e = _ => destruct (Z.sgn_spec e) as [[A B]|[[A B]|[A B]]]; rewrite B; lia end
         end.
  Qed.

  Lemma a_loop2 : forall (k : nat) (i j : Z) (w2 w3 w4 w5 a6 w7 x0 x1 x2 : word),
    Z.to_nat j = k -> 0 <= j <= n' -> lval ys n' = lval ys j -> SIGF xs n i ->
    w2 = Z_to_bv 64 (4 * j - 4) -> w3 = Z_to_bv 64 (4 * i - 4) -> w4 = Z_to_bv 64 (i + 1) ->
    w5 = Z_to_bv 64 i -> w7 = Z_to_bv 64 j ->
    evt usegs (POST (Z.sgn (lval xs n - lval ys n')))
      (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) w2 w3 w4 w5 a6 w7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131528) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i j w2 w3 w4 w5 a6 w7 x0 x1 x2 Hk Hj HYj HS -> -> -> -> ->;
      pose proof HS as (Hi & HXi & HT); lx_hide HT.
    - assert (j = 0) as -> by lia.
      lx_run_tac (PLAN [131528; 131596; 131744] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: eapply (a_decide i 0);
           [ exact HS | split; [lia|]; split; [exact HYj| left; reflexivity]
           | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ].
    - destruct QB as [N0|[QP QAL]]; [lia|].
      lx_limb HY (j - 1) wy VY.
      lx_run_tac (PLAN [131528; 131596; 131744] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 131528) _ _ _ _] =>
               eapply (IH i (j - 1));
               [ lia | lia | rewrite HYj; apply lval_drop_zero; lia | exact HS
               | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ]
           | |- _ =>
               eapply (a_decide i j);
               [ exact HS | split; [lia|]; split; [exact HYj| right; apply lval_top_nonzero; lia]
               | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ]
           end.
  Qed.

  Lemma a_loop1 : forall (k : nat) (i : Z) (w2 a3 w4 a5 w6 a7 x0 : word),
    Z.to_nat i = k -> 0 <= i <= n -> lval xs n = lval xs i ->
    w2 = Z_to_bv 64 (-4) -> w4 = Z_to_bv 64 (4 * i - 4) -> w6 = Z_to_bv 64 i ->
    evt usegs (POST (Z.sgn (lval xs n - lval ys n')))
      (MS (mkR ra sp gp tp x0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) w2 a3 w4 a5 w6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131428) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i w2 a3 w4 a5 w6 a7 x0 Hk Hi HXi -> -> ->.
    - assert (i = 0) as -> by lia.
      lx_run_tac (PLAN [131528; 131744] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: eapply (a_loop2 (Z.to_nat n') 0 n');
           [ reflexivity | lia | reflexivity | split; [lia|]; split; [exact HXi| left; reflexivity]
           | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ].
    - destruct PB as [N0|[PP PAL]]; [lia|].
      lx_limb HX (i - 1) wx VX.
      lx_run_tac (PLAN [131428; 131528; 131744] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 131428) _ _ _ _] =>
               eapply (IH (i - 1));
               [ lia | lia | rewrite HXi; apply lval_drop_zero; lia
               | f_equal; lia | f_equal; lia | f_equal; lia ]
           | |- _ =>
               eapply (a_loop2 (Z.to_nat n') i n');
               [ reflexivity | lia | reflexivity
               | split; [lia|]; split; [exact HXi| right; apply lval_top_nonzero; lia]
               | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ]
           end.
  Qed.

  Lemma a_cmp_abs : forall (a2 a3 a4 a5 a6 a7 : word),
    evt usegs (POST (Z.sgn (lval xs n - lval ys n')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 U_MPI_CMP_ABS) fc None m (seg_rom usegs)).
  Proof.
    intros a2 a3 a4 a5 a6 a7. unfold U_MPI_CMP_ABS.
    lx_run_tac (PLAN [131428; 131744] [] 200%N); lx_tree.
    all: same_mem; pc_norm.
    all: eapply (a_loop1 (Z.to_nat n) n); [ reflexivity | lia | reflexivity | f_equal; lia | f_equal; lia | f_equal; lia ].
  Qed.
End WalkA.

Theorem U_mpi_cmp_abs_spec_o : mpi_cmp_abs_stmt_o usegs U_MPI_CMP_ABS.
Proof.
  unfold mpi_cmp_abs_stmt_o. intros until dY. intros HX HY PX PY MI -> ->.
  pose proof (opnd_view _ _ _ _ _ HX) as ((_ & XA & XN & _) & _).
  pose proof (opnd_view _ _ _ _ _ HY) as ((_ & YA & YN & _) & _).
  destruct (opnd_raw _ _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  destruct (opnd_raw _ _ _ _ _ HY PY) as (CY & BY & LY & NY & SY & ABY & PBY).
  pose proof BX as PRX. apply bytes_at_bound in PRX. rewrite u32s_length in PRX.
  pose proof BY as PRY. apply bytes_at_bound in PRY. rewrite u32s_length in PRY.
  rewrite !mpd_abs_lval by assumption.
  eapply a_cmp_abs; try eassumption; lia.
Qed.

Theorem U_mpi_cmp_abs_spec : mpi_cmp_abs_stmt usegs U_MPI_CMP_ABS.
Proof.
  unfold mpi_cmp_abs_stmt. intros until dY. intros HX HY PX PY MI EA EB.
  eapply U_mpi_cmp_abs_spec_o; [apply opnd_at_mpd; exact HX | apply opnd_at_mpd; exact HY | exact PX | exact PY | exact MI | exact EA | exact EB].
Qed.
