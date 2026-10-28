(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2 Pj_defs Pj_kit.
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

Definition PJ_COPY_G : Z := 0x3d270.
Definition PJ_COPY_S : Z := 0x3d30c.
Definition PJ_COPY_STACK : Z := 48.

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Lemma slti0_nonneg : forall x, (0 <= x < 9223372036854775808)%Z -> Z.b2z (Z.lxor x 9223372036854775808 <? 9223372036854775808) = 0%Z.
Proof.
  intros x H. change 9223372036854775808%Z with (2^63)%Z. rewrite ZBridge.zb_lxor_pow2_small by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma b2z_ltu_false : forall a b, (b <= a)%Z -> Z.b2z (a <? b) = 0%Z.
Proof. intros a b H. rewrite (proj2 (Z.ltb_ge a b) H). reflexivity. Qed.

Ltac gref G := exfalso; rewrite ?unsigned_lit in G by lia; lia.
Ltac gtrap := let G := fresh "G" in zstep; if_cases G; zify_cond G; [gref G|]; try clear G.
Ltac gfall := let G := fresh "G" in zstep; if_cases G; zify_cond G; [|gref G]; try clear G.

Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Ltac uov := rewrite ?slti0_nonneg by lia; rewrite ?b2z_ltu_false by lia; change (Z.lxor (Z.lxor 0 0) 1) with 1%Z.

Ltac unot := rewrite ?ZBridge.zb_lxor_ones by lia.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition copy_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Src + N)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 48, q); (Dst, Dst + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at usegs m' Src src.

Lemma copy_fin : forall (pc : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m3 : mem) (q lo Dst Src N : Z) (src j8 : list byte),
  pc = 0x3d2ac \/ pc = 0x3d348 ->
  stk usegs m3 lo (q + -48) -> 0 <= lo -> lo <= q - 48 -> q < 2^64 -> mem_inv usegs m3 ->
  rw_cells usegs m3 (q + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(q + -48, q); (Dst, Dst + N)]%Z m m3 -> wmono usegs m m3 ->
  rw_cells usegs m3 Dst [CB (Z.to_nat N) src] -> bytes_at usegs m3 Src src ->
  0 <= N < 2^63 -> 0 < Src -> Src + N < 2^63 -> 0 < Dst -> Dst + N < 2^63 ->
  evt usegs (copy_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Dst Src N src m)
      (MS (mkR xra (Z_to_bv 64 (q + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (Src + N)) (Z_to_bv 64 N) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 Src) (Z_to_bv 64 Dst) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 pc) fc None m3 (seg_rom usegs)).
Proof.
  intros until j8. intros HPC ST LO0 ROOM QHI MI FR MU WM DC SRC HN HS HS2 HD HD2.
  destruct HPC as [-> | ->].
  all:
       zstep; gtrap;

       zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1%Z; zstep; if_false;

       zstep; zstep; unz; zstep; if_false;

       zstep; zstep; zstep; zstep; uov; zstep; if_false;
       gtrap;

       zstep; do 5 zstep; zstep; zstep;
       release_frame FR ST q;
       replace (q + -48)%Z with (q - 48)%Z in MU by lia;
       apply evt_done; unfold copy_post;
       do 14 eexists; eexists;
       (split; [cbv delta [mkR]; reflexivity|]);
       (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact ST|]);
       (split; [exact DC| exact SRC]).
Qed.

Lemma copy_spec : forall (entry : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo Dst Src N : Z) (src junk : list byte),
  entry = PJ_COPY_G \/ entry = PJ_COPY_S ->
  stk usegs m lo q -> lo <= q - PJ_COPY_STACK -> GLOBALS_TOP <= lo -> q < 2^64 -> mem_inv usegs m ->
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src) -> 0 <= N < 2^63 -> 0 < Src -> Src + N < 2^63 -> 0 < Dst -> Dst + N < 2^63 ->
  (Src + N <= lo \/ q <= Src) -> (Dst + N <= lo \/ q <= Dst) ->
  evt usegs (copy_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Dst Src N src m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Src) (Z_to_bv 64 (Src + N)) (Z_to_bv 64 Dst) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros HPC ST ROOM GTOP QHI MI SRC LEN DC SEP HN HS HS2 HD HD2 OS OD.
  unfold PJ_COPY_G, PJ_COPY_S, PJ_COPY_STACK, GLOBALS_TOP in *.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  pose proof (munch_refl [(q + -48, q); (Dst, Dst + N)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (LJ : length junk = Z.to_nat N) by (destruct DC as [[[HL _] _] _]; exact HL).
  pose proof (munch_refl [(q + -48, q)]%Z m) as MU0.
  hide DC. hide SRC.
  destruct HPC as [-> | ->].
  all: zstep; carve_frame 48%nat ST.
  all: apply (rw_cells_split_CB usegs _ _ [] 48 junk0 [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.

  all: do 5 zstep; zstep; zstep; zstep; zstep.
  all: try (replace (Src + N + - Src)%Z with N by lia).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  all: pose proof (agree_on_of_munch _ _ _ MU0 WM) as AG3.
  all: unhide DC; apply (rw_cells_agree _ _ _ _ _ AG3) in DC; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
  all: unhide SRC; apply (bytes_at_agree _ _ _ _ _ AG3) in SRC; [| intros a Ha; rewrite LEN in Ha; cbn [outside]; split; [lia| exact I]].
  all: clear AG3 MU0.

  all: zstep; if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  all: try (assert (N0 : N = 0) by lia; clear K).
  all: try (assert (N1 : 1 <= N) by lia; clear K).

  1,3: assert (EJ : junk = src) by (destruct junk; destruct src; cbn [length] in LJ, LEN; try reflexivity; lia); subst junk;
       eapply copy_fin; [| exact ST| exact LO0| lia| lia| exact MI| exact FR| exact MU| exact WM| exact DC| exact SRC| lia| lia| lia| lia| lia].
  1: left; reflexivity.
  1: right; reflexivity.

  all: zstep; zstep; zstep; zstep.
  all: eapply evt_cut;
       [eapply memmove_far_callZ with (Dst := Dst) (Src := Src) (N := N) (src := src) (junk := junk);
          [exact SRC| exact LEN| exact DC| lia| lia| lia| lia| lia| lia| assumption] |].
  all: intros ms' PO; unfold memcpy_postZ in PO;
       destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & DC4 & SRC4).
  all: lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  all: pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
  all: apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
  all: eapply copy_fin; [| | exact LO0| lia| lia| exact MI4| exact FR| | | exact DC4| exact SRC4| lia| lia| lia| lia| lia].
  1,5: solve [left; reflexivity| right; reflexivity].
  all: try (eapply stk_transport_disjoint; [exact ST| exact MU4| exact WM4| cbn [disjoint_from]; lia]).
  all: try (eapply wmono_trans; [exact WM| exact WM4]).
  all: eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU4]; unfold sub_fp; cbn [outside]; intros; lia.
Qed.

End WithCeiling0.
