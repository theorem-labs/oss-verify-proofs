(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjDig SjPjItoa.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_ser_defs Pj_ser_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].

Lemma b2z_ltu_true : forall a b, (a < b)%Z -> Z.b2z (a <? b) = 1%Z.
Proof. intros a b H. rewrite (proj2 (Z.ltb_lt a b) H). reflexivity. Qed.

Ltac nst_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
  | |- _ => reflexivity
  end.
Ltac nst_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; nst_eq_tree
  | |- Some _ = Some _ => f_equal; nst_eq_leaf
  | |- _ => reflexivity
  end.
Ltac nst_eq :=
  cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; nst_eq_tree
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition itoa_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo OUT : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (n : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OUT + n)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 48, q); (OUT, OUT + 20)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ stk usegs m' OUT (OUT + 20) /\ 1 <= n <= 20.

Definition itoa_stmt (entry : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo OUT v : Z),
  stk usegs m lo q -> lo <= q - 48 -> GLOBALS_TOP <= lo -> q < 2^63 -> mem_inv usegs m ->
  q <= OUT -> OUT + 20 < 2^63 -> stk usegs m OUT (OUT + 20) -> 0 <= v < 2^64 ->
  evt usegs (itoa_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OUT m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom usegs)).

Section Itoa.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (q lo OUT : Z).
  Hypothesis ROOM : lo <= q - 48.
  Hypothesis GTOP : GLOBALS_TOP <= lo.
  Hypothesis QHI : q < 2^63.
  Hypothesis OQ : q <= OUT.
  Hypothesis OHI : OUT + 20 < 2^63.

  Definition ITINV (m : mem) : Prop :=
    stk usegs m (q + -48) (q + -24) /\ rw_cells usegs m (q + -24) [C8 s1; C8 s0; C8 ra] /\ stk usegs m lo (q + -48)
    /\ stk usegs m OUT (OUT + 20) /\ mem_inv usegs m /\ munch [(q + -48, q); (OUT, OUT + 20)]%Z m0 m /\ wmono usegs m0 m.

  Ltac it_open H := destruct H as (FRL & FRH & ST & OUTS & MI & MU & WM); unfold GLOBALS_TOP in *; pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.

  Notation POST := (itoa_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OUT m0).

  Lemma itoa_tail : forall (pc : Z) (k w sg : Z) (m : mem) (xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    pc = 0x3d4fc \/ pc = 0x3d440 ->
    ITINV m -> 0 <= w < 10 -> 0 <= sg <= 1 -> 0 <= k -> k + sg <= 19 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (q + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (OUT + sg)) s1
               xa0 (Z_to_bv 64 w) (Z_to_bv 64 (q + -25 - k)) xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
  Proof using ROOM GTOP QHI OQ OHI.
    intros until xt6. intros HPC I HW HSG K0 KB. it_open I.
    destruct HPC as [-> | ->].
    all:
         zstep; zstep; step; pj_store_done.
    all:
         zstep; try (replace (q + -24 + - (q + -25 - k))%Z with (k + 1)%Z by lia); try (replace (q + -48 + 24 + - (q + -25 - k))%Z with (k + 1)%Z by lia);
         step; step; step.
    all:
         destruct (stk_split usegs _ _ (q + -25 - k) _ FRL ltac:(lia)) as [FRL1 FRL2];
         destruct (stk_bytes usegs _ _ _ FRL2 ltac:(lia)) as (src & SL & SRC);
         destruct (stk_split usegs _ _ (OUT + sg) _ OUTS ltac:(lia)) as [O1 O23];
         destruct (stk_split usegs _ _ (OUT + sg + (k + 1)) _ O23 ltac:(lia)) as [O2 O3];
         destruct (stk_CB usegs _ _ _ O2 ltac:(lia)) as (junk & DC);
         replace (OUT + sg + (k + 1) - (OUT + sg)) with (k + 1) in DC by lia.

    all: step.
    all: eapply evt_cut;
         [eapply memcpy_callZ with (Dst := OUT + sg) (Src := q + -25 - k) (N := k + 1) (src := src) (junk := junk);
            [exact SRC| rewrite SL; lia| exact DC| lia| lia| lia| lia| exact MI] |].
    all: cbv beta; intros ms' PO; unfold memcpy_postZ in PO;
         destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & -> & MU' & WM' & MI' & DC' & SRC');
         lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    all: pose proof (agree_on_of_munch _ _ _ MU' WM') as AG;
         assert (OUTW : forall a, a < OUT + sg \/ OUT + sg + (k + 1) <= a -> outside [(OUT + sg, OUT + sg + (k + 1))] a) by (intros a Ha; cbn [outside]; split; [lia| exact I]);
         apply (rw_cells_agree _ _ _ _ _ AG) in FRH; [| intros a Ha; cbn in Ha; apply OUTW; lia];
         apply (stk_agree _ _ _ _ _ AG) in FRL; [| intros a Ha; apply OUTW; lia];
         apply (stk_agree _ _ _ _ _ AG) in ST; [| intros a Ha; apply OUTW; lia];
         apply (stk_agree _ _ _ _ _ AG) in O1; [| intros a Ha; apply OUTW; lia];
         apply (stk_agree _ _ _ _ _ AG) in O3; [| intros a Ha; apply OUTW; lia].
    all:
         zstep; unot; gtrap; zstep.
    all:
         step; step; step; zstep; step.
    all: pose proof (stk_merge usegs _ _ _ _ ST FRL ltac:(lia)) as ST2; clear ST FRL;
         release_frame FRH ST2 q.
    all: pose proof (stk_of_rw_cells usegs _ _ _ DC') as O2'; cbn [cells_size csize Nat.add] in O2'; rewrite Nat.add_0_r, Z2Nat.id in O2' by lia;
         pose proof (stk_merge usegs _ _ _ _ O1 (stk_merge usegs _ _ _ _ O2' O3 ltac:(lia)) ltac:(lia)) as OUTS'.
    all: apply evt_done; unfold itoa_post;
         do 14 eexists; exists m', (sg + (k + 1));
         split; [nst_eq|];
         split; [| split; [eapply wmono_trans; [exact WM| exact WM']| split; [exact MI'| split; [exact ST2| split; [exact OUTS'| lia]]]]].
    all: eapply munch_trans; [replace (q - 48) with (q + -48) by lia; exact MU|];
         eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia.
  Qed.

  Lemma itoa_u_loop : forall (f : nat) (k w : Z) (m : mem) (xt0 xt1 xt2 xa2 xa7 xt3 xt4 xt5 xt6 : word),
    ITINV m -> 10 <= w < 10 ^ (20 - k) -> w < 18446744073709551616 -> 0 <= k -> 20 - k <= Z.of_nat f ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (q + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 OUT) s1
               (Z_to_bv 64 10) (Z_to_bv 64 w) xa2 (Z_to_bv 64 (q + -25 - k)) (Z_to_bv 64 DIV10_MAGIC) (Z_to_bv 64 1) (Z_to_bv 64 99) xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x3d4c8) fc None m (seg_rom usegs)).
  Proof using ROOM GTOP QHI OQ OHI.
    induction f as [|f IH]; intros k w m xt0 xt1 xt2 xa2 xa7 xt3 xt4 xt5 xt6 I HW W64 K0 HFU.
    { exfalso. pose proof (pow10_ge2 w (20 - k) HW). lia. }
    pose proof (pow10_ge2 w (20 - k) HW) as J2.
    pose proof (pow10_step w (20 - k) ltac:(lia) ltac:(lia)) as HQ.
    it_open I.

    unfold DIV10_MAGIC. gtrap. zstep. zstep. zstep. zstep.
    rewrite SFModel.land_W64. change (2 ^ 64) with 18446744073709551616.
    change 14757395258967641293 with DIV10_MAGIC. rewrite (div10_machine w) by lia.

    zstep. zstep. zstep.
    step. pj_store_done.
    zstep. step.
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      eapply evt_eq; [| eapply (IH (k + 1) (w / 10)); [| | | lia| lia]].
      + nst_eq.
      + split; [exact FRL|]. split; [exact FRH|]. split; [exact ST|]. split; [exact OUTS|]. split; [exact MI|]. split; [exact MU| exact WM].
      + replace (20 - (k + 1)) with (20 - k - 1) by lia. split; [apply (div10_ge10 w); lia | lia].
      + Z.div_mod_to_equations. lia.
    - rewrite ?unsigned_lit in K by lia.

      step.
      eapply evt_eq; [| eapply (itoa_tail 0x3d4fc (k + 1) (w / 10) 0); [left; reflexivity| | | lia| lia|]].
      + nst_eq.
      + split; [exact FRL|]. split; [exact FRH|]. split; [exact ST|]. split; [exact OUTS|]. split; [exact MI|]. split; [exact MU| exact WM].
      + pose proof (div10_ge10 w ltac:(lia)). Z.div_mod_to_equations. lia.
      + assert (k + 1 + 1 <= 20 - 0); [| lia].
        assert (HP : 10 ^ (20 - k) <= 10 ^ 20) by (apply Z.pow_le_mono_r; lia).
        destruct (Z_lt_le_dec (k + 2) 21); [lia|]. exfalso.
        assert (HP2 : 10 ^ (20 - k) <= 10 ^ 1) by (apply Z.pow_le_mono_r; lia). change (10 ^ 1) with 10 in HP2. lia.
  Qed.

  Lemma itoa_s_loop : forall (f : nat) (k w sg : Z) (m : mem) (xt0 xt1 xt2 xa2 xa7 xt3 xt4 xt5 xt6 : word),
    ITINV m -> 10 <= w < 10 ^ (20 - sg - k) -> w < 18446744073709551616 -> 0 <= sg <= 1 -> 0 <= k -> 20 - sg - k <= Z.of_nat f ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (q + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (OUT + sg)) s1
               (Z_to_bv 64 (q + -25 - k)) (Z_to_bv 64 w) xa2 (Z_to_bv 64 10) (Z_to_bv 64 DIV10_MAGIC) (Z_to_bv 64 1) (Z_to_bv 64 99) xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x3d40c) fc None m (seg_rom usegs)).
  Proof using ROOM GTOP QHI OQ OHI.
    induction f as [|f IH]; intros k w sg m xt0 xt1 xt2 xa2 xa7 xt3 xt4 xt5 xt6 I HW W64 HSG K0 HFU.
    { exfalso. pose proof (pow10_ge2 w (20 - sg - k) HW). lia. }
    pose proof (pow10_ge2 w (20 - sg - k) HW) as J2.
    pose proof (pow10_step w (20 - sg - k) ltac:(lia) ltac:(lia)) as HQ.
    it_open I.

    unfold DIV10_MAGIC. gtrap. zstep. zstep. zstep. zstep.
    rewrite SFModel.land_W64. change (2 ^ 64) with 18446744073709551616.
    change 14757395258967641293 with DIV10_MAGIC. rewrite (div10_machine w) by lia.

    zstep. zstep. zstep.
    step. pj_store_done.
    zstep. step.
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      eapply evt_eq; [| eapply (IH (k + 1) (w / 10) sg); [| | | lia| lia| lia]].
      + nst_eq.
      + split; [exact FRL|]. split; [exact FRH|]. split; [exact ST|]. split; [exact OUTS|]. split; [exact MI|]. split; [exact MU| exact WM].
      + replace (20 - sg - (k + 1)) with (20 - sg - k - 1) by lia. split; [apply (div10_ge10 w); lia | lia].
      + Z.div_mod_to_equations. lia.
    - rewrite ?unsigned_lit in K by lia.

      step.
      eapply evt_eq; [| eapply (itoa_tail 0x3d440 (k + 1) (w / 10) sg); [right; reflexivity| | | lia| lia|]].
      + nst_eq.
      + split; [exact FRL|]. split; [exact FRH|]. split; [exact ST|]. split; [exact OUTS|]. split; [exact MI|]. split; [exact MU| exact WM].
      + pose proof (div10_ge10 w ltac:(lia)). Z.div_mod_to_equations. lia.
      + destruct (Z_lt_le_dec (k + 1 + sg) 20); [lia|]. exfalso.
        assert (HP2 : 10 ^ (20 - sg - k) <= 10 ^ 1) by (apply Z.pow_le_mono_r; lia). change (10 ^ 1) with 10 in HP2. lia.
  Qed.

  Lemma itoa_s_mag : forall (w sg : Z) (m : mem) (xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    ITINV m -> 0 <= sg <= 1 -> 0 <= w < 10 ^ (20 - sg) -> w < 18446744073709551616 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (q + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (OUT + sg)) s1
               xa0 (Z_to_bv 64 w) xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x3d3d8) fc None m (seg_rom usegs)).
  Proof using ROOM GTOP QHI OQ OHI.
    intros until xt6. intros I HSG HW W64. pose proof I as I'. it_open I.

    zstep. step. gtrap. zstep. rewrite b2z_ltu_true by lia. zstep. step. if_false.

    step. zstep. step. if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.

      step.
      eapply evt_eq; [| eapply (itoa_tail 0x3d440 0 w sg); [right; reflexivity| exact I'| lia| lia| lia| ]].
      + nst_eq.
      + destruct (Z_lt_le_dec sg 20); [| exfalso]; [lia|]. assert (HP2 : 10 ^ (20 - sg) <= 10 ^ 0) by (apply Z.pow_le_mono_r; lia). change (10 ^ 0) with 1 in HP2. lia.
    - rewrite ?unsigned_lit in K by lia.

      step. step. step. step.
      eapply evt_eq; [| eapply (itoa_s_loop 20%nat 0 w sg); [exact I'| | lia| lia| lia| lia]].
      + unfold DIV10_MAGIC. nst_eq.
      + replace (20 - sg - 0) with (20 - sg) by lia. lia.
  Qed.

  Lemma itoa_u_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (v : Z),
    stk usegs m0 lo q -> mem_inv usegs m0 -> stk usegs m0 OUT (OUT + 20) -> 0 <= v < 2^64 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_ITOA_U) fc None m0 (seg_rom usegs)).
  Proof using ROOM GTOP QHI OQ OHI.
    intros until v. intros ST MI OUTS HV. unfold PJ_ITOA_U, GLOBALS_TOP in *. pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    pose proof (munch_refl [(q + -48, q); (OUT, OUT + 20)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.

    zstep. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [24;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jj :: _) =>
      pose proof (proj1 (Sj_stage1_kit.rw_cells_app usegs m1 (q + -48) [CB 24 jj] [C8 s1; C8 s0; C8 ra]) FR) as [FRL0 FRH] end.
    cbn [cells_size csize Nat.add] in FRH. replace (q + -48 + Z.of_nat 24) with (q + -24) in FRH by lia.
    pose proof (stk_of_rw_cells usegs _ _ _ FRL0) as FRL. cbn [cells_size csize Nat.add] in FRL. replace (q + -48 + Z.of_nat 24) with (q + -24) in FRL by lia.
    clear FR FRL0.
    assert (I : ITINV m1).
    { split; [exact FRL|]. split; [exact FRH|]. split; [exact ST|]. split; [exact OUTS|]. split; [exact MI|]. split; [exact MU| exact WM]. }

    zstep. step. gtrap. step. step. gtrap. step. zstep.

    step. if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.

      step.
      eapply evt_eq; [| eapply (itoa_tail 0x3d4fc 0 v 0); [left; reflexivity| exact I| lia| lia| lia| lia]].
      nst_eq.
    - rewrite ?unsigned_lit in K by lia.

      step. step. step. step.
      eapply evt_eq; [| eapply (itoa_u_loop 20%nat 0 v); [exact I| | lia| lia| lia]].
      + unfold DIV10_MAGIC. nst_eq.
      + replace (20 - 0) with 20 by lia. split; [lia|]. apply u64_lt_pow10_20. lia.
  Qed.

  Lemma itoa_s_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (v : Z),
    stk usegs m0 lo q -> mem_inv usegs m0 -> stk usegs m0 OUT (OUT + 20) -> 0 <= v < 2^64 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_ITOA_S) fc None m0 (seg_rom usegs)).
  Proof using ROOM GTOP QHI OQ OHI.
    intros until v. intros ST MI OUTS HV. unfold PJ_ITOA_S, GLOBALS_TOP in *. pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    pose proof (munch_refl [(q + -48, q); (OUT, OUT + 20)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.

    zstep. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [24;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jj :: _) =>
      pose proof (proj1 (Sj_stage1_kit.rw_cells_app usegs m1 (q + -48) [CB 24 jj] [C8 s1; C8 s0; C8 ra]) FR) as [FRL0 FRH] end.
    cbn [cells_size csize Nat.add] in FRH. replace (q + -48 + Z.of_nat 24) with (q + -24) in FRH by lia.
    pose proof (stk_of_rw_cells usegs _ _ _ FRL0) as FRL. cbn [cells_size csize Nat.add] in FRL. replace (q + -48 + Z.of_nat 24) with (q + -24) in FRL by lia.
    clear FR FRL0.

    step. if_cases K; zify_cond K.
    -
      rewrite ?unsigned_lit in K by lia.
      eapply evt_eq; [| eapply (itoa_s_mag v 0); [| lia| | lia]].
      + nst_eq.
      + split; [exact FRL|]. split; [exact FRH|]. split; [exact ST|]. split; [exact OUTS|]. split; [exact MI|]. split; [exact MU| exact WM].
      + change (10 ^ (20 - 0)) with 100000000000000000000. lia.
    -
      rewrite ?unsigned_lit in K by lia.

      step. gtrap. step. step. pj_store_done. zstep. zstep.
      replace (Z_to_bv 64 (0 + - v)) with (Z_to_bv 64 (18446744073709551616 - v))
        by (apply Z_to_bv_eqm; change (2 ^ 64) with 18446744073709551616; Z.div_mod_to_equations; lia).
      eapply evt_eq; [| eapply (itoa_s_mag (18446744073709551616 - v) 1); [| lia| | lia]].
      + nst_eq.
      + split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
      + change (10 ^ (20 - 1)) with 10000000000000000000. lia.
  Qed.
End Itoa.

Lemma itoa_u_proof : itoa_stmt PJ_ITOA_U.
Proof.
  unfold itoa_stmt. intros until v. intros ST ROOM GTOP QHI MI OQ OHI OUTS HV.
  eapply itoa_u_body; eassumption.
Qed.

Lemma itoa_s_proof : itoa_stmt PJ_ITOA_S.
Proof.
  unfold itoa_stmt. intros until v. intros ST ROOM GTOP QHI MI OQ OHI OUTS HV.
  eapply itoa_s_body; eassumption.
Qed.

End WithCeiling0.
