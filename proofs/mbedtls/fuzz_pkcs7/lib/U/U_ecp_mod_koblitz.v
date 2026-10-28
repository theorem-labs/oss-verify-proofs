From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_mla U_mpi_core_add U_mpi_core_mul U_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsArr LxU_SumsEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_ECP_MOD_KOBLITZ : Z := 0x3d9d0.
Definition KOBLITZ_STACK : Z := 352.

Lemma kob_memcpy_limbs : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (X S : Z) (ws ss : list word) (i k : Z),
  u32arr usegs m X ws -> bytes_at usegs m S (u32s ss) -> 0 < X -> 0 <= i -> 0 <= k ->
  i + k <= Z.of_nat (length ws) -> k <= Z.of_nat (length ss) -> X + 4 * i < 2 ^ 64 -> S < 2 ^ 64 ->
  (S + 4 * k <= X + 4 * i \/ X + 4 * i + 4 * k <= S) -> mem_inv usegs m ->
  a0 = Z_to_bv 64 (X + 4 * i) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (4 * k) ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (m' : mem) (ws' : list word),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(X + 4 * i, X + 4 * i + 4 * k)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ u32arr usegs m' X ws' /\ length ws' = length ws)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46a40) fc None m (seg_rom usegs)).
Proof.
  intros until k. intros U HS XP Hi Hk Hik Hks XT ST4 AP MI -> -> ->.
  pose proof (u32arr_bound _ _ _ _ U) as UB. pose proof (u32ro_bound _ _ _ _ HS) as SB.
  destruct (split3 ws (Z.to_nat i) (Z.to_nat (i + k)) ltac:(lia) ltac:(lia)) as (EY & LA & LB).
  set (A := firstn (Z.to_nat i) ws) in *. set (Bm := firstn _ (skipn _ ws)) in *. set (C := skipn (Z.to_nat (i + k)) ws) in *.
  assert (LC : length C = (length ws - Z.to_nat (i + k))%nat) by (subst C; rewrite skipn_length; lia).
  pose proof U as U0. rewrite EY in U. apply u32arr_app in U. destruct U as [UA U]. apply u32arr_app in U. destruct U as [UBm UC].
  rewrite LA in UBm, UC. rewrite LB in UC. apply u32arr_cells in UBm. rewrite LB in UBm.
  replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) in UBm, UC by lia.
  pose proof HS as HS1. rewrite <- (firstn_skipn (Z.to_nat k) ss), u32s_app in HS1. apply bytes_at_app in HS1. destruct HS1 as [HS1 _].
  pose proof U_memcpy_spec as SP. unfold memcpy_stmt in SP.
  eapply evt_mono.
  { eapply SP with (src := u32s (firstn (Z.to_nat k) ss)); rewrite ?unsigned_lit by lia.
    - exact HS1.
    - rewrite u32s_length, firstn_length. lia.
    - replace (Z.to_nat (4 * k)) with (4 * (Z.to_nat (i + k) - Z.to_nat i))%nat by lia. exact UBm.
    - lia.
    - exact MI. }
  clear SP. intros ms' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & HZ & _).
  apply (u32arr_of_cells usegs m' _ _ _ (firstn (Z.to_nat k) ss)) in HZ; [| reflexivity ].
  do 15 eexists. exists (A ++ (firstn (Z.to_nat k) ss ++ C)).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split.
  - apply u32arr_app. split.
    + eapply u32arr_transport; [exact UA| exact MU| exact WM| cbn; rewrite LA; lia].
    + rewrite LA. apply u32arr_app. split.
      * replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) by lia. exact HZ.
      * rewrite firstn_length. replace (X + 4 * Z.of_nat (Z.to_nat i) + 4 * Z.of_nat (Nat.min (Z.to_nat k) (length ss))) with (X + 4 * i + 4 * Z.of_nat (Z.to_nat (i + k) - Z.to_nat i)) by lia.
        eapply u32arr_transport; [exact UC| exact MU| exact WM| cbn; rewrite LC; lia].
  - rewrite !app_length, firstn_length, LA, LC. lia.
Qed.

Definition SUM_memcpyWinU (k kS : nat) : summary :=
  SUMG 0x46a40 false 7 14 0 [(10, 3%positive); (11, 4%positive); (12, 5%positive)] [(1%positive, k); (2%positive, kS)] None
    [MArr (q 1) 4 (LBase 1) (q 6) true; MArr (q 2) 4 (LBase 2) (q 7) false] None [] []
    [FLe (q 2) (q 4); FAl (EAdd (q 4) (EMulC (-1) (q 2))) 2; FLe (q 1) (q 3); FAl (EAdd (q 3) (EMulC (-1) (q 1))) 2;
     FAl (q 5) 2; FLe (ELit 0) (q 5); FLe (EAdd (q 3) (q 5)) (EAdd (q 1) (EMulC 4 (q 6)));
     FLe (EAdd (q 4) (q 5)) (EAdd (q 2) (EMulC 4 (q 7))); FSep (q 4) (q 5) (q 3) (q 5);
     FLt (ELit 0) (q 1); FLt (q 3) (ELit (2 ^ 64)); FLt (q 2) (ELit (2 ^ 64))]
    [(q 3, EAdd (q 3) (q 5))]
    [(5, 8%positive); (6, 9%positive); (7, 10%positive); (11, 11%positive); (12, 12%positive); (13, 13%positive);
     (14, 14%positive); (15, 15%positive); (16, 16%positive); (17, 17%positive); (28, 18%positive); (29, 19%positive);
     (30, 20%positive); (31, 21%positive)]
    [MArr (q 1) 4 (LBase 3) (q 6) true] [].

Lemma sum_memcpyWinU_valid : forall AL GS k kS, summary_validG usegs AL GS (SUM_memcpyWinU k kS).
Proof.
  intros AL GS k kS. unfold SUM_memcpyWinU, q. lx_sum_unfold.
  intros X S p s n NX NS xs ss CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB1 GB2 R10 R11 R12 _ [HX LX] [HS LS] PS1 PS2 PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HS) as SB.
  set (i := (p - X) / 4). set (kk := n / 4). set (j := (s - S) / 4).
  assert (Ep : p = X + 4 * i) by (subst i; lia). assert (En : n = 4 * kk) by (subst kk; lia).
  assert (Es : s = S + 4 * j) by (subst j; lia).
  assert (Hj : (Z.to_nat j <= length ss)%nat) by (subst j; lia).
  pose proof (lxp_u32ro_skipn _ _ _ _ (Z.to_nat j) HS Hj) as HSj.
  replace (S + 4 * Z.of_nat (Z.to_nat j)) with s in HSj by lia.
  rewrite Ep in R10. rewrite En in R12.
  assert (SL : s < 2 ^ 64 \/ (s = 2 ^ 64 /\ kk = 0)) by lia.
  destruct SL as [SL | [SE K0]]; eapply evt_cut;
    [ eapply (kob_memcpy_limbs x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                               x24 x25 x26 x27 x28 x29 x30 x31 F fc m X s xs (skipn (Z.to_nat j) ss) i kk);
        first [exact HX | exact HSj | exact MI | exact R10 | exact R11 | exact R12 | rewrite skipn_length; lia | lia]
    | idtac
    | eapply (kob_memcpy_limbs x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                               x24 x25 x26 x27 x28 x29 x30 x31 F fc m X 0 xs [] i kk);
        first [exact HX | exact MI | exact R10 | exact R12 | (apply bytes_at_nil; lia)
              | (rewrite R11, SE; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) | (cbn [length]; lia) | lia]
    | idtac ].
  all: cbv beta; intros ms' PO;
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & -> & MU & WM & MI' & HX' & LEN');
    apply evt_done; rewrite <- Ep in MU; replace (p + 4 * kk) with (p + n) in MU by lia;
    try clear SE K0; try clear SL.
  - lx_sum_post.
  - lx_sum_post.
Qed.

Definition KOBSUMS : list summary := [SUM_memsetWP 0; SUM_coremulP; SUM_coreaddXXBP; SUM_memcpyWinU 1 0].

Lemma kobsums_ok : forall GS AL, Forall (summary_okG usegs AL GS) KOBSUMS.
Proof.
  intros GS AL. unfold KOBSUMS.
  apply Forall_cons; [apply apply_summary_soundG; apply sum_memsetWP_valid|].
  apply Forall_cons; [apply apply_summary_soundG; apply (summary_validG_ext usegs AL [] GS); [reflexivity| apply sum_coremulP_valid]|].
  apply Forall_cons; [apply apply_summary_soundG; apply (summary_validG_ext usegs AL [] GS); [reflexivity| apply sum_coreaddXXBP_valid]|].
  apply Forall_cons; [apply apply_summary_soundG; apply sum_memcpyWinU_valid|].
  apply Forall_nil.
Qed.

Definition koblitz_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (X : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (xs' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs) /\
    munch [(X, X + 4 * Z.of_nat (length xs)); (bv_unsigned sp - KOBLITZ_STACK, bv_unsigned sp)] m m' /\
    wmono segs m m' /\ mem_inv segs m' /\ u32arr segs m' X xs' /\ length xs' = length xs /\
    stk segs m' lo (bv_unsigned sp).

Definition koblitz_stmt (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (X R bits lo : Z) (xs rs : list word),
  (bits = 192 \/ bits = 224 \/ bits = 256) ->
  u32arr segs m X xs -> bits / 16 <= Z.of_nat (length xs) ->
  bytes_at segs m R (u32s rs) -> 2 <= Z.of_nat (length rs) ->
  X mod 4 = 0 -> R mod 4 = 0 -> 0 < X -> 0 < R ->
  X + 4 * Z.of_nat (length xs) < 2 ^ 64 -> R + 4 * Z.of_nat (length rs) < 2 ^ 64 ->
  (R + 4 * Z.of_nat (length rs) <= X \/ X + 4 * Z.of_nat (length xs) <= R) ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - KOBLITZ_STACK -> bv_unsigned sp mod 16 = 0 ->
  (X + 4 * Z.of_nat (length xs) <= lo \/ bv_unsigned sp <= X) ->
  (R + 4 * Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= R) ->
  mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  a0 = Z_to_bv 64 X -> a1 = Z_to_bv 64 R -> a2 = Z_to_bv 64 bits ->
  evt segs (koblitz_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X xs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma kob_fin : forall (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (X : Z) (xs : list word) (lo : Z) (m : mem)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (xs' : list word),
  munch [(X, X + 4 * Z.of_nat (length xs)); (bv_unsigned sp - 352, bv_unsigned sp)] m m' ->
  wmono segs m m' -> mem_inv segs m' -> u32arr segs m' X xs' -> length xs' = length xs ->
  stk segs m' lo (bv_unsigned sp) ->
  koblitz_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X xs lo m
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom segs)).
Proof.
  intros until xs'. intros MU WM MI HX LX ST. unfold koblitz_post, KOBLITZ_STACK.
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', xs'.
  split; [reflexivity|]. do 5 (split; [assumption|]). assumption.
Qed.

Lemma U_ecp_mod_koblitz_spec : koblitz_stmt usegs U_ECP_MOD_KOBLITZ.
Proof.
  unfold koblitz_stmt, U_ECP_MOD_KOBLITZ, KOBLITZ_STACK.
  intros until rs. intros HBITS HX LX HR LR ALX ALR NZX NZR XT RT DXR ST LO SPA SX SR MI RA -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  set (lx := Z.of_nat (length xs)) in *. assert (LXn : Z.of_nat (length xs) = lx) by reflexivity. clearbody lx.
  set (lr := Z.of_nat (length rs)) in *. assert (LRn : Z.of_nat (length rs) = lr) by reflexivity. clearbody lr.
  pose proof (munch_refl [(X, X + 4 * lx); (bv_unsigned sp - 352, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 176%nat ST.
  lxp_split_frame [40;32;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat.
  lxp_chunk_split FR 1%nat FM FR.
  lxp_chunk_split FR 1%nat FA FR.
  pose proof (lxp_CB_length usegs m _ [] _ _ [] FM) as LJM. pose proof (lxp_CB_length usegs m _ [] _ _ [] FA) as LJA.
  apply (u8arr_of_rw_cells usegs) in FM. apply (u8arr_of_rw_cells usegs) in FA.
  destruct (u32arr_of_u8arr usegs m _ _ 10 FM ltac:(rewrite LJM; reflexivity)) as (ml & UM & LM0).
  destruct (u32arr_of_u8arr usegs m _ _ 8 FA ltac:(rewrite LJA; reflexivity)) as (al & UA & LA0).
  assert (LM : Z.of_nat (length ml) = 10) by (rewrite LM0; reflexivity).
  assert (LA : Z.of_nat (length al) = 8) by (rewrite LA0; reflexivity).
  clear FM FA LM0 LA0 LJM LJA.
  pose proof (kobsums_ok [X; bv_unsigned sp + -136]) as LXSUMS.
  destruct HBITS as [->|[->| ->]];
    (lazymatch type of LX with ?a / 16 <= _ => let v := eval vm_compute in (a / 16) in change (a / 16) with v in LX end);
    lx_run_tac (PLANS [] [] 400%N KOBSUMS); lx_tree.
  all: try rewrite (Z_to_bv_bv_unsigned sp); apply evt_done.
  all: let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
    lx_release_frame;
    lazymatch goal with Hs : stk _ mx xlo ?h |- _ =>
      (tryif constr_eq h (bv_unsigned xsp) then idtac else replace h with (bv_unsigned xsp) in Hs by (clear; lia)) end;
    lazymatch goal with Hu : u32arr _ mx xX ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ xm mx |- _ =>
    lazymatch goal with Hw : wmono _ xm mx |- _ =>
    lazymatch goal with Hi : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx xlo (bv_unsigned xsp) |- _ =>
      eapply (kob_fin usegs) with (m' := mx) (xs' := l);
      [ eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx LXn; lia
      | exact Hw | exact Hi | exact Hu | apply Nat2Z.inj; rewrite Hl; reflexivity | exact Hs ]
    end end end end end end.
Qed.
