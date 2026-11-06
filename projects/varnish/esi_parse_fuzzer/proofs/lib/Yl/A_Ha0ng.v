(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpwd0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_World A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_WSmsm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_WSmsm.

Module A_Ha5zr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpwd0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_World A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac icall_consts_in H ::= unfold set_shadow_post in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@SLO; @SHI; @H])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HSH_SIZES : list nat := [4;171;17;94;16;7;5;7;5;9;5;23;9;5;5;1;3;4;4;128;18]%nat.
Definition zb (n : nat) : list byte := repeat (Z_to_bv 8 0) n.
(* [comment removed for export] *)
Definition hsh_zero (SHB : Z) (m : mem) : Prop :=
     bytes_at rsegs m (SHB + 4) (zb 171) /\ bytes_at rsegs m (SHB + 192) (zb 94)
  /\ bytes_at rsegs m (SHB + 302) (zb 7) /\ bytes_at rsegs m (SHB + 314) (zb 7)
  /\ bytes_at rsegs m (SHB + 326) (zb 9) /\ bytes_at rsegs m (SHB + 340) (zb 23)
  /\ bytes_at rsegs m (SHB + 372) (zb 5) /\ bytes_at rsegs m (SHB + 382) (zb 1)
  /\ bytes_at rsegs m (SHB + 386) (zb 4) /\ bytes_at rsegs m (SHB + 394) (zb 128).

Lemma split21 : forall m A (bs : list byte),
  rw_cells rsegs m A [CB 540 bs] ->
  exists j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 : list byte,
    rw_cells rsegs m A [CB 4 j1; CB 171 j2; CB 17 j3; CB 94 j4; CB 16 j5; CB 7 j6; CB 5 j7; CB 7 j8; CB 5 j9; CB 9 j10; CB 5 j11;
                        CB 23 j12; CB 9 j13; CB 5 j14; CB 5 j15; CB 1 j16; CB 3 j17; CB 4 j18; CB 4 j19; CB 128 j20; CB 18 j21].
Proof.
  intros m A bs H. pose proof (rw_cells_split_CB rsegs m A [] 540 bs [] HSH_SIZES H eq_refl) as X.
  cbn [mk_CB_cells app HSH_SIZES] in X. hot_eexists_k21. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shjunk_post (pc ra' : Z) (sp gp tp s0 s1 s2 : word) (SHB : Z) (s6 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (bs' : list byte),
    ms' = MS (mkR (Z_to_bv 64 ra') sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + 394)) (Z_to_bv 64 (SHB + 192)) s6 (Z_to_bv 64 18446744073709551608)
                 (Z_to_bv 64 (SHB + 4)) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs)
    /\ munch [(SHB, SHB + 540)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' SHB [CB 540 bs'].

Definition unpoison_post (sp gp tp s0 s1 s2 : word) (SHB : Z) (s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (bs' : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x87270) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + 394)) (Z_to_bv 64 (SHB + 192)) s6 s7
                 (Z_to_bv 64 (SHB + 4)) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x87270) fc None m' (seg_rom rsegs)
    /\ munch [(SHB, SHB + 540)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' SHB [CB 540 bs'] /\ hsh_zero SHB m'.


Lemma rw_cells_merge1 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge rsegs m A [] cs [] ltac:(cbn [app]; rewrite app_nil_r; exact H)) as X.
  cbn [app] in X. exact X.
Qed.
Lemma rw_cells_forget1 : forall m A cs, rw_cells rsegs m A cs -> exists junk, rw_cells rsegs m A [CB (cells_size cs) junk].
Proof. intros m A cs H. exact (rw_cells_forget rsegs m A cs H). Qed.

(* [comment removed for export] *)
Ltac sb1 := zstep; rewrite le1_byte, ?unsigned_lit by lia;
  repeat match goal with |- context [(?x mod 256)%Z] => is_Zlit x; let v := eval vm_compute in (x mod 256)%Z in change ((x mod 256)%Z) with v end;
  mem_after_store_opt.

(* [comment removed for export] *)
Lemma rw_cells_iso3 : forall m A (pre mid post : list cell) A1 A2,
  A1 = A + Z.of_nat (cells_size pre) -> A2 = A + Z.of_nat (cells_size pre + cells_size mid) ->
  rw_cells rsegs m A (pre ++ mid ++ post) -> rw_cells rsegs m A pre /\ rw_cells rsegs m A1 mid /\ rw_cells rsegs m A2 post.
Proof.
  intros m A pre mid post A1 A2 -> -> H.
  apply (proj1 (rw_cells_app rsegs m A pre (mid ++ post))) in H. destruct H as [H1 H2].
  apply (proj1 (rw_cells_app rsegs m _ mid post)) in H2. destruct H2 as [H2 H3].
  split; [exact H1|]. split; [exact H2|]. eapply rwc_eq; [exact H3|]. rewrite Nat2Z.inj_add. lia.
Qed.
Lemma rw_cells_uniso3 : forall m A (pre mid post : list cell) A1 A2,
  A1 = A + Z.of_nat (cells_size pre) -> A2 = A + Z.of_nat (cells_size pre + cells_size mid) ->
  rw_cells rsegs m A pre -> rw_cells rsegs m A1 mid -> rw_cells rsegs m A2 post -> rw_cells rsegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post A1 A2 -> -> H1 H2 H3.
  apply (proj2 (rw_cells_app rsegs m A pre (mid ++ post))). split; [exact H1|].
  apply (proj2 (rw_cells_app rsegs m _ mid post)). split; [exact H2|]. eapply rwc_eq; [exact H3|]. rewrite Nat2Z.inj_add. lia.
Qed.
Section S.
  Context {Clg : Ceiling}.

  Local Ltac simpl_ofnat_in H :=
    repeat match type of H with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.
  (* [comment removed for export] *)
  Local Ltac sscells CE0 MU CF2 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let CEx := fresh "CEx" in
      assert (CEx : cenv mx) by (eapply cenv_munch2; [exact CE0| exact MU| apply Forall_cons; [exact CF2| apply Forall_nil]]);
      pose proof (set_shadow_cells_of_consts _ (proj1 CEx)) as SSC; clear CEx
    end.
  (* [comment removed for export] *)
  Local Ltac iso H k n C P :=
    lazymatch type of H with rw_cells _ ?m ?A ?cs =>
      let pre := eval cbn [firstn] in (firstn k cs) in
      let rest := eval cbn [skipn] in (skipn k cs) in
      let mid := eval cbn [firstn] in (firstn n rest) in
      let post := eval cbn [skipn] in (skipn n rest) in
      let o1 := eval vm_compute in (Z.of_nat (cells_size pre)) in
      let o2 := eval vm_compute in (Z.of_nat (cells_size pre + cells_size mid)) in
      let A1 := lazymatch o1 with 0 => A | _ => constr:(A + o1) end in
      let X := fresh in
      pose proof (rw_cells_iso3 m A pre mid post A1 (A + o2)
                    ltac:(first [reflexivity | cbn [cells_size csize Nat.add]; lia]) ltac:(first [reflexivity | cbn [cells_size csize Nat.add]; lia]) H) as X;
      clear H; destruct X as (H & C & P)
    end.
  (* [comment removed for export] *)
  Local Ltac uniso H C P :=
    lazymatch type of H with rw_cells _ ?m ?A ?pre =>
    lazymatch type of C with rw_cells _ _ ?Ac ?mid =>
    lazymatch type of P with rw_cells _ _ ?Ap ?post =>
      let X := fresh in
      pose proof (rw_cells_uniso3 m A pre mid post Ac Ap
                    ltac:(first [reflexivity | cbn [cells_size csize Nat.add]; lia]) ltac:(first [reflexivity | cbn [cells_size csize Nat.add]; lia]) H C P) as X;
      clear H C P; rename X into H; cbn [app] in H
    end end end.

  (* [comment removed for export] *)
  Lemma poison1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SHB : Z) (bs : list byte),
    rw_cells rsegs m SHB [CB 540 bs] -> cenv m -> const_free_ivl2 (SHB, SHB + 540) -> mem_inv rsegs m ->
    2147450880 <= SHB -> SHB + 540 <= 2^47 ->
    evt rsegs (shjunk_post 0x8716c 0x87120 sp gp tp s0 s1 s2 SHB s6 s9 s10 s11 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 18446744073709551601) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86ee4) fc None m (seg_rom rsegs)).
  Proof.
    intros until bs. intros SH CE0 CF2 MI SLO SHI.
    pose proof (munch_refl [(SHB, SHB + 540)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (first [ pose proof ((split21 _ _ _ SH)) as dR_1; dex21 dR_1 as j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21; rename dR_1 into SHC | pose proof ((split21 _ _ _ SH)) as dR_1; dand22 dR_1 as j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 SHC | destruct (split21 _ _ _ SH) as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & j16 & j17 & j18 & j19 & j20 & j21 & SHC) ]).
    clear SH. (* [comment removed for export] *) change 171%nat with (Z.to_nat 171) in SHC; change 128%nat with (Z.to_nat 128) in SHC; change 94%nat with (Z.to_nat 94) in SHC.
    iso SHC 0%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr8 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 1%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_f8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 4) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    zstep. fix_neg. (* [comment removed for export] *)
    iso SHC 2%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr37 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 3%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_f8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 192) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    iso SHC 4%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    zstep. fix_neg. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr62 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 6%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr68 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 8%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr74 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 12%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr80 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 14%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr86 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 18%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr92 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 5%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr97 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 6%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr100 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 5%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr106 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 7%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr115 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 8%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr118 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 9%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr128 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 10%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr132 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 11%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr136 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 9%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr139 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 10%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr144 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 11%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr163 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 12%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr168 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 11%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr174 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 12%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr178 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 13%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr185 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 14%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr188 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 17%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr194 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 15%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr197 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 16%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr205 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 19%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_f8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 394) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    zstep. fix_neg. (* [comment removed for export] *)
    iso SHC 20%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr232 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)

    (* [comment removed for export] *)
    apply evt_done. unfold shjunk_post.
    destruct (rw_cells_forget _ _ _ _ SHC) as [bs' SHF]. cbn [cells_size csize Nat.add] in SHF.
    hot_eexists_k16. exists bs'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SHF].
  Qed.

  (* [comment removed for export] *)
  Local Ltac subbytes H k n X :=
    lazymatch type of H with rw_cells _ ?m ?A ?cs =>
      pose proof H as X;
      rewrite <- (firstn_skipn k cs) in X;
      apply (proj1 (rw_cells_app rsegs m A (firstn k cs) (skipn k cs))) in X;
      cbn [firstn skipn] in X; apply proj2 in X;
      lazymatch type of X with rw_cells _ _ ?Ac ?cs2 =>
        rewrite <- (firstn_skipn n cs2) in X;
        apply (proj1 (rw_cells_app rsegs m Ac (firstn n cs2) (skipn n cs2))) in X;
        cbn [firstn skipn] in X; apply proj1 in X
      end;
      apply bytes_at_of_rw_cells in X;
      cbn [firstn skipn cells_bytes cbytes app cells_size csize Nat.add Z.modulo Z.pos_div_eucl] in X; rewrite ?app_nil_r in X; simpl_ofnat_in X;
      repeat match type of X with context [?a + ?x + ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (x + y) in replace (a + x + y) with (a + v) in X by lia end
    end.

  (* [comment removed for export] *)
  Lemma unpoison : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SHB : Z) (bs : list byte),
    rw_cells rsegs m SHB [CB 540 bs] -> cenv m -> const_free_ivl2 (SHB, SHB + 540) -> mem_inv rsegs m ->
    2147450880 <= SHB -> SHB + 540 <= 2^47 ->
    evt rsegs (unpoison_post sp gp tp s0 s1 s2 SHB s6 s7 s9 s10 s11 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + 394)) (Z_to_bv 64 (SHB + 192)) s6 s7 (Z_to_bv 64 (SHB + 4)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8716c) fc None m (seg_rom rsegs)).
  Proof.
    intros until bs. intros SH CE0 CF2 MI SLO SHI.
    pose proof (munch_refl [(SHB, SHB + 540)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (first [ pose proof ((split21 _ _ _ SH)) as dR_2; dex21 dR_2 as j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21; rename dR_2 into SHC | pose proof ((split21 _ _ _ SH)) as dR_2; dand22 dR_2 as j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 SHC | destruct (split21 _ _ _ SH) as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & j16 & j17 & j18 & j19 & j20 & j21 & SHC) ]).
    clear SH. (* [comment removed for export] *) change 171%nat with (Z.to_nat 171) in SHC; change 128%nat with (Z.to_nat 128) in SHC; change 94%nat with (Z.to_nat 94) in SHC.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 1%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_00_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 4) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 3%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_00_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 192) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    iso SHC 5%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 13%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 20%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 13%nat 6%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 21%nat 6%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 29%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 21%nat 7%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 31%nat 6%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 55%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 61%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 63%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    uniso SHC SHX SHP. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 68%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_00_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 394) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    subbytes SHC 1%nat 1%nat Z1. subbytes SHC 3%nat 1%nat Z2. subbytes SHC 5%nat 7%nat Z3. subbytes SHC 13%nat 7%nat Z4. subbytes SHC 21%nat 9%nat Z5. subbytes SHC 31%nat 23%nat Z6. subbytes SHC 55%nat 5%nat Z7. subbytes SHC 61%nat 1%nat Z8. subbytes SHC 63%nat 4%nat Z9. subbytes SHC 68%nat 1%nat Z10.
    apply evt_done. unfold unpoison_post.
    destruct (rw_cells_forget _ _ _ _ SHC) as [bs' SHF]. cbn [cells_size csize Nat.add] in SHF.
    hot_eexists_k16. exists bs'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact SHF|].
    unfold hsh_zero, zb.
    split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|]. split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9| exact Z10].
  Qed.

  (* [comment removed for export] *)
  Lemma poison2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SHB : Z) (bs : list byte),
    rw_cells rsegs m SHB [CB 540 bs] -> cenv m -> const_free_ivl2 (SHB, SHB + 540) -> mem_inv rsegs m ->
    2147450880 <= SHB -> SHB + 540 <= 2^47 ->
    evt rsegs (shjunk_post 0x875e8 0x875e8 sp gp tp s0 s1 s2 SHB s6 s9 s10 s11 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + 394)) (Z_to_bv 64 (SHB + 192)) s6 (Z_to_bv 64 18446744073709551608)
                 (Z_to_bv 64 (SHB + 4)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x874e4) fc None m (seg_rom rsegs)).
  Proof.
    intros until bs. intros SH CE0 CF2 MI SLO SHI.
    pose proof (munch_refl [(SHB, SHB + 540)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (first [ pose proof ((split21 _ _ _ SH)) as dR_3; dex21 dR_3 as j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21; rename dR_3 into SHC | pose proof ((split21 _ _ _ SH)) as dR_3; dand22 dR_3 as j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 SHC | destruct (split21 _ _ _ SH) as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & j16 & j17 & j18 & j19 & j20 & j21 & SHC) ]).
    clear SH. (* [comment removed for export] *) change 171%nat with (Z.to_nat 171) in SHC; change 128%nat with (Z.to_nat 128) in SHC; change 94%nat with (Z.to_nat 94) in SHC.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 19%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_f8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 394) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    iso SHC 17%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr13 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 13%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr18 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 15%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr21 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 11%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr25 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 13%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr29 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 11%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr35 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 9%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr40 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 11%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr59 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 9%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr65 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 7%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr69 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 9%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr73 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 5%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr78 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 7%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr85 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    iso SHC 5%nat 1%nat SHX SHP. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    sb1. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    apply rw_cells_forget1 in SHX; destruct SHX as [jr93 SHX]; cbn [cells_size csize Nat.add] in SHX. uniso SHC SHX SHP. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 3%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_f8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 192) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    iso SHC 1%nat 1%nat SHX SHP.
    sscells CE0 MU CF2.
    icall (set_shadow_f8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _) by (rewrite ?unsigned_lit by lia; first [exact SHX | exact SSC | assumption]).
    try clear SHX. clear SSC. lazymatch goal with X : rw_cells _ ?mx (SHB + 4) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHX end.
    uniso SHC SHX SHP.

    (* [comment removed for export] *)
    apply evt_done. unfold shjunk_post.
    destruct (rw_cells_forget _ _ _ _ SHC) as [bs' SHF]. cbn [cells_size csize Nat.add] in SHF.
    hot_eexists_k16. exists bs'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SHF].
  Qed.
End S.
End A_Ha5zr.


Module A_Haqjq.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpwd0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_World A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_WSmsm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_WSmsm.A_HKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Ha0ng.A_Ha5zr.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac icall_consts_in H ::= unfold shjunk_post in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Lemma stack_shadow_again {Clg : Ceiling} : forall (v v' : mem) SB N lo hi K,
  stack_shadow LPA v SB N lo hi -> bytes_at rsegs v' SB (zeros K) -> K = Z.to_nat N -> stack_shadow LPA v' SB N lo hi.
Proof. intros v v' SB N lo hi K (B & R) ZB ->. split; [exact ZB| exact R]. Qed.

(* [comment removed for export] *)
Lemma cframe_dropV {Clg : Ceiling} {AI : AsanAlloc LPA} : forall (o o' : Z -> Prop) (xsp win : Z) (V X N : Z -> Prop) (v v' : mem),
  cframe LPA o o' xsp win (fun a => V a \/ X a) N v v' ->
  (forall a, X a -> o a \/ (v (Z_to_bv 64 a) = None /\ ~ in_image LPA a)) ->
  cframe LPA o o' xsp win V N v v'.
Proof.
  (intros o o' xsp win V X N v v'; (first [ intro dR_8; dand3 dR_8 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros HX). split; [| split; [exact C2|]].
  - intros a Ha NO VIS NW NE NV. apply C1; try assumption. intros [Y|Y]; [exact (NV Y)|].
    destruct (HX a Y) as [O|[Nn Ni]]; [exact (NO O)|]. destruct VIS as [U|U]; [exact (U Nn)| exact (Ni U)].
  - intros a Ha NW NE Na. destruct (C3 a Ha NW NE Na) as [O|[[Y|Y]|Z]]; [left; exact O| right; left; exact Y| | right; right; exact Z].
    destruct (HX a Y) as [O|Z]; [left; exact O| right; right; exact Z].
Qed.

(* [comment removed for export] *)
Definition HBSSV (a : Z) : Prop := (vi_bss_vsc VIA <= a < vi_bss_vsc VIA + 8) \/ (vi_bss_cp VIA <= a < vi_bss_cp VIA + 8).
(* [comment removed for export] *)
Definition HV (ff : Z) (a : Z) : Prop := HBSSV a \/ frm ff HCLASS a.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (data : Z) (inp : list byte) (SB N : Z) (T : TSet).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPLO : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis MI00 : mem_inv rsegs (aview A0 m0).
  Hypothesis ST00 : stk rsegs (aview A0 m0) (bv_unsigned sp - LIB_STACK) (bv_unsigned sp).
  Hypothesis STKSH00 : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64).
  Hypothesis FR00 : forall ff, a_frame A0 ff = None.
  Hypothesis LEN : Z.of_nat (length inp) < NMAX.
  Hypothesis INP : length inp <> 0%nat -> data <> 0 /\ a_live A0 data = Some (Z.of_nat (length inp)) /\ bytes_at rsegs (aview A0 m0) data inp.
  Hypothesis BUD : a_livebytes A0 + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A0 + LIB_NLIVE <= NLIVE_MAX.
  Hypothesis SECC : LIB_SECC (Z.of_nat (length inp)) <= a_seccred A0.
  Hypothesis PRIMC : LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model) (A' : AS),
      alib_post sp m0 md0 A0 inp SB N m' md' A' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj TP (conj SP16 (conj SPLO (conj SPHI (conj AINV00 (conj MI00 (conj ST00 (conj STKSH00 (conj FR00 (conj LEN (conj INP (conj BUD
      (conj SECC (conj PRIMC K)))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    pose proof (zr_word ra) as RAR; unfold inr64 in RAR;
    unfold LIB_STACK in *.

  (* [comment removed for export] *)
  Definition SAVE : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP data"] Lemma harness_exit : forall (Ak : AS) (mk : mem) (mdk : Model) (v : mem) (ff : Z) (age : nat) (d : Z) (Nk : Z -> Prop)
      (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (jsp hdr bs : list byte),
    let sp1 := bv_unsigned sp + -192 - d in let SHB := sh ff in
    let WX := [(bv_unsigned sp - LIB_STACK, bv_unsigned sp); (SHB, SHB + 540); (ff, ff + 24)] in
    ainv Ak mk mdk -> amd_frame md0 mdk ->
    munch WX (aview Ak mk) v -> wmono rsegs (aview Ak mk) v -> client_fp LPA Ak (aview Ak mk) WX -> mem_inv rsegs v ->
    a_frame Ak ff = Some (HCLASS, age) -> ff <> 0 ->
    (forall g, g <> ff -> a_frame Ak g = None) ->
    (forall p n, a_live A0 p = Some n -> a_live Ak p = Some n) ->
    a_livebytes Ak = a_livebytes A0 -> a_nlive Ak = a_nlive A0 -> a_tinycred Ak = a_tinycred A0 ->
    a_seccred A0 - LIB_SECC (Z.of_nat (length inp)) <= a_seccred Ak <= a_seccred A0 ->
    a_primcred A0 - LIB_PRIM (Z.of_nat (length inp)) <= a_primcred Ak <= a_primcred A0 ->   (* [comment removed for export] *)
    0 <= d <= 16 -> sp1 mod 16 = 0 ->
    stk rsegs v (bv_unsigned sp - LIB_STACK) sp1 ->
    rw_cells rsegs v sp1 [CB 88 jsp] ->
    stk rsegs v (sp1 + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs v (bv_unsigned sp + -104) SAVE ->
    rw_cells rsegs v SHB [CB 540 bs] ->
    rw_cells rsegs v ff [CB 24 hdr] ->
    stack_shadow LPA (aview Ak mk) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned Ak) (bv_unsigned sp) LIB_STACK (HV ff) Nk (aview A0 m0) (aview Ak mk) ->
    (forall a, frm ff HCLASS a -> owned A0 a \/ (aview A0 m0 (Z_to_bv 64 a) = None /\ ~ in_image LPA a)) ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull Ak) (alhull Ak) (aeager Ak) mk mdk T)
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ff) (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + 394)) (Z_to_bv 64 (SHB + 192)) (Z_to_bv 64 ff)
                 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 (SHB + 4)) xs9 xs10 xs11 xt3 xt4 xt5 xt6)   (* [comment removed for export] *)
            F (Z_to_bv 64 0x874e4) fc None v (seg_rom rsegs)).
  Proof.
    touch_all. intros until bs. cbv zeta. intros AINVk MDFk MU WM CFP MI FFk FFNZ FRk LIVEk LBk NLk TCk SCk PCk D0 AL16 STlo SPILL STpad SAV SHC FFH STKSHk CF0k FRM0.
    prelims.
    pose proof (as_minv LPA Ak _ _ AINVk) as [_ MHk].
    (* [comment removed for export] *)
    (first [ pose proof ((fframe_geom LPA Ak mk mdk ff HCLASS age AINVk FFk)) as dR_1; dand5 dR_1 as _ FS FLO FHI _ | destruct (fframe_geom LPA Ak mk mdk ff HCLASS age AINVk FFk) as (_ & FS & FLO & FHI & _) ]).
    rewrite fsize7 in FS, FHI. change (Z.min 8192 4096) with 4096 in FS.
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_2; dex2 dR_2 as ix sx; rename dR_2 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_2; dand3 dR_2 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    pose proof (cenv_intro Ak mk mdk AINVk) as CEk.
    assert (CF3 : Forall const_free_ivl3 [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)]).
    { repeat (apply Forall_cons); try apply Forall_nil.
      - apply const_free_ivl3_high. cbn [fst]. keeplia SPLO ACV.
      - apply (const_free_ivl3_frame_shadow ff 8192 540 FLO); clear; [lia| change ((8192 + 7) / 8) with 1024; lia].
      - apply (const_free_ivl3_app ff 8192); [exact FLO| clear; lia| clear; lia]. }
    assert (CEv : cenv v) by (eapply cenv_munch3; [exact CEk| exact MU| exact CF3]).
    pose proof (app_shadow_const_free2 LPA ff 8192 540 FLO eq_refl eq_refl ltac:(clear; lia) ltac:(clear; change ((8192 + 7) / 8) with 1024; lia)) as CF2.
    (* [comment removed for export] *)
    icall (poison2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v (sh ff) bs)
      by (first [exact SHC | exact CEv | exact CF2 | exact MI | keeplia FB | keeplia FB]).
    clear CEv.
    lazymatch goal with X : rw_cells _ ?mx (sh ff) [CB 540 ?b] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHC2; rename mx into v2 end.
    (* [comment removed for export] *)
    zstep. zstep. try rewrite (sx32_small 1172321806) by (clear; lia). zstep.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (keeplia FB); exact (FFNZ KZ)|]. clear KZ.
    zstep. zstep. try rewrite (sx32_small 4320) by (clear; lia). zstep. zstep.
    (* [comment removed for export] *)
    astop AINVk MU WM CFP.
    lazymatch goal with AIq : ainv Ak ?mq ?mdq, SBq : same_but_materialized mdk ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa; rename mq into m1; rename mdq into md1 end.
    lazymatch goal with MIq : mem_inv _ (aview Ak m1) |- _ => rename MIq into MIa end.
    assert (MPW : mapped (aview Ak m1) (bv_unsigned sp + -192 - d - ASTK) ASTK)
      by (unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact STlo | keeplia SPLO ACV | keeplia SPLO D0 ACV | keeplia D0]).
    eapply (sfree7_acall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 Ak ff age T);
      [ exact AINVa | exact MIa | reflexivity | reflexivity | exact FFk | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
      | rewrite unsigned_lit by (clear; lia); reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold ASTK; keeplia SPLO D0 ACV
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact MPW | ].
    clear MPW.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 md2 AINV2 MI2 MDF2 FR2.
    rewrite unsigned_lit in FR2 by (keeplia SPR D0 SPLO ACV).
    pose proof (as_minv LPA _ _ _ AINV2) as [_ MH2].
    assert (CFs : cframe LPA (owned Ak) (owned (a_release Ak ff)) (bv_unsigned sp + -192 - d) ASTK (frm ff HCLASS) nowhere (aview Ak m1) (aview (a_release Ak ff) m2))
      by (apply cframe_of_frame_ok; exact FR2).
    unfold ASTK in CFs.
    (* [comment removed for export] *)
    lazymatch type of CFs with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA Ak (a_release Ak ff) xsp win V Nn ma mb CFs (bv_unsigned sp + -104)) in SAV;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) Ak _ _ ma (bv_unsigned sp + -104) 104 AINVa ltac:(keeplia SPLO ACV) ltac:(keeplia SPR)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SAV ltac:(off_image_solve LPA)))
       | unfold SAVE; cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; unfold frm in X; rewrite fsize7 in X; change (8192 / 8) with 1024 in X; keeplia Hi X FB SPLO ACV] ];
      apply (rw_cells_ccall LPA Ak (a_release Ak ff) xsp win V Nn ma mb CFs (bv_unsigned sp + -192 - d)) in SPILL;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) Ak _ _ ma (bv_unsigned sp + -192 - d) 88 AINVa ltac:(keeplia SPLO ACV D0) ltac:(keeplia SPR D0)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SPILL ltac:(off_image_solve LPA)))
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; unfold frm in X; rewrite fsize7 in X; change (8192 / 8) with 1024 in X; keeplia Hi X FB SPLO ACV D0] ];
      apply (stk_ccall_any Ak (a_release Ak ff) _ _ ma mb xsp win V Nn _ _ AINVa CFs) in STlo; [| keeplia SPLO ACV | intros a Ha X; unfold frm in X; rewrite fsize7 in X; change (8192 / 8) with 1024 in X; keeplia Ha X FB SPLO ACV];
      apply (stk_ccall_any Ak (a_release Ak ff) _ _ ma mb xsp win V Nn _ _ AINVa CFs) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; unfold frm in X; rewrite fsize7 in X; change (8192 / 8) with 1024 in X; keeplia Ha X FB SPLO ACV D0];
      assert (STKSH2 : stack_shadow LPA mb SB N (bv_unsigned sp - 12288) (bv_unsigned sp + 64));
      [ (first [ pose proof (STKSHk) as dR_3; dand6 dR_3 as SSB SSN SSL SSH SSC SST | pose proof STKSHk as (SSB & SSN & SSL & SSH & SSC & SST) ]); unfold kHighMemBeg in SST;
        pose proof sh_ceiling_ge as SHC8;
        assert (SSBa : bytes_at rsegs ma SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
          by (eapply (bytes_at_munch LPA); [exact SSB| exact MU| rewrite repeat_length, Z2Nat.id by exact SSN; intros a__ Ha__; cbn; keeplia Ha__ SSC SST SHC8 SPLO ACV FB]);
        pose proof (stack_shadow_again _ _ SB N _ _ _ STKSHk SSBa eq_refl) as SSa;
        pose proof (crange_stack_shadow (Clg:=Clg) LPA Ak _ _ SB N _ _ AINVa SSa ltac:(keeplia SPLO ACV)) as CRS;
        eapply stack_shadow_again; [exact STKSHk| | reflexivity];
        apply (bytes_at_ccall LPA Ak (a_release Ak ff) xsp win V Nn ma mb CFs SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN; split; [keeplia SSC SST SHC8 SPLO ACV D0| intros i Hi X; unfold frm in X; rewrite fsize7 in X; change (8192 / 8) with 1024 in X; keeplia Hi X FB SSC SST SHC8 SPLO ACV]
        | exact SSBa ]
      | ]
    end.
    (* [comment removed for export] *)
    ago AINV2. fold_cl_segs.
    replace (ret_pc (Z_to_bv 64 0x87608)) with (Z_to_bv 64 0x87608) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    zstep. zstep. zstep.
    try replace (bv_unsigned sp + -192) with (bv_unsigned sp + -104 + -88) by lia.
    unfold SAVE in SAV.
    do 13 zstep. zstep.
    try replace (bv_unsigned sp + -104 + -88 + 192) with (bv_unsigned sp) by lia. try replace (bv_unsigned sp + -192 + 192) with (bv_unsigned sp) by lia.
    try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    astop0 AINV2.
    lazymatch goal with AIq : ainv _ ?mq ?mdq, SBq : same_but_materialized md2 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINV3; rename SBq into SBM3; rename mq into m3; rename mdq into md3 end.
    (* [comment removed for export] *)
    release_frame SPILL STlo (bv_unsigned sp + -192 - d + 88).
    pose proof (stk_merge rsegs _ _ _ _ STlo STpad ltac:(keeplia D0 SPLO ACV)) as STm. clear STlo STpad.
    release_frame SAV STm (bv_unsigned sp).
    (first [ pose proof ((as_release_spec LPA Ak m1 md1 ff HCLASS age AINVa FFk)) as dR_4; dand11 dR_4 as RN RO RL RLB RTC RSC RPC RNL RH RE ROW | destruct (as_release_spec LPA Ak m1 md1 ff HCLASS age AINVa FFk) as (RN & RO & RL & RLB & RTC & RSC & RPC & RNL & RH & RE & ROW) ]).
    (* [comment removed for export] *)
    assert (MPF : mapped (aview (a_release Ak ff) m3) (bv_unsigned sp - 12288) 12288)
      by (eapply (stk_mapped (L:=LPA)); [exact STm | keeplia SPLO ACV | clear; lia | clear; lia]).
    assert (CFX : cframe LPA (owned Ak) (owned (a_release Ak ff)) (bv_unsigned sp) 12288 (HV ff) nowhere (aview Ak mk) (aview (a_release Ak ff) m3)).
    { eapply (cframe_extend LPA (owned Ak) (owned (a_release Ak ff)) (bv_unsigned sp + -192 - d) 8192 (bv_unsigned sp) 12288
                (frm ff HCLASS) (HV ff) nowhere nowhere (aview Ak mk) (aview Ak m1) (aview (a_release Ak ff) m3) (aview (a_release Ak ff) m3) _ []);
        [ exact MU
        | intros a Ha NO; cbn [outside] in NO; unfold HV, frm; rewrite fsize7; change (8192 / 8) with 1024; keeplia Ha NO FB D0
        | exact CFs | keeplia D0 | keeplia D0 SPR
        | intros a X; unfold HV; right; exact X
        | intros a X; destruct X
        | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | exact MPF ]. }
    pose proof (cframe_seq LPA (owned A0) (owned Ak) (owned (a_release Ak ff)) (bv_unsigned sp) 12288 12288 12288 (HV ff) Nk (HV ff) nowhere (HV ff) nowhere
                  (aview A0 m0) (aview Ak mk) (aview (a_release Ak ff) m3) CF0k CFX ltac:(clear; lia) ltac:(clear; lia) MPF
                  ltac:(intros a X; exact X) ltac:(intros a X; right; exact X) ltac:(intros a X; destruct X)) as CFA.
    unfold HV in CFA. apply (cframe_dropV _ _ _ _ HBSSV (frm ff HCLASS) nowhere _ _) in CFA; [| exact FRM0].
    clear CFX CFs CF0k.
    (* [comment removed for export] *)
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 md3 (a_release Ak ff)).
    split.
    - exact AINV3.
    - exact MI2.
    - eapply amd_frame_trans; [exact MDFk|]. eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMa| exact MHk]|].
      eapply amd_frame_trans; [exact MDF2|]. apply amd_frame_sbm; [exact SBM3| exact MH2].
    - intros p n Hp. rewrite RL. exact (LIVEk p n Hp).
    - intros p n i LP Hi. (first [ dand3 CFA as C1 _ _ | destruct CFA as (C1 & _ & _) ]).
      (first [ pose proof ((as_live_ok LPA A0 m0 md0 p n AINV00 LP)) as dR_6; dand8 dR_6 as N0 ALp PLO PHI IMG MP NOW _ | destruct (as_live_ok LPA A0 m0 md0 p n AINV00 LP) as (N0 & ALp & PLO & PHI & IMG & MP & NOW & _) ]).
      (first [ pose proof ((app_facts LPA p n PLO)) as dR_7; dand3 dR_7 as (P4 & _ & _) OFF _ | pose proof (app_facts LPA p n PLO) as ((P4 & _ & _) & OFF & _) ]). unfold off_image in OFF. cbn [cl_image_lo cl_image_hi LPA] in OFF.
      apply (C1 (p + i)); [ keeplia P4 PHI Hi ACV N0 OFF | apply NOW; exact Hi
        | left; change (aview_of (ahull A0) m0) with (aview A0 m0) in MP; apply MP; exact Hi
        | keeplia P4 PHI Hi SPLO ACV | rewrite ERRNOA_eq; unfold ERRNOA; keeplia P4 OFF Hi N0
        | unfold HBSSV; cbn [vi_bss_vsc vi_bss_cp VIA]; keeplia P4 OFF Hi N0 ].
    - intros g. destruct (Z.eq_dec g ff) as [->|NE]; [rewrite RN, FR00; reflexivity| rewrite (RO g NE), (FRk g NE), FR00; reflexivity].
    - rewrite RLB, RNL, RTC, LBk, NLk, TCk. split; [reflexivity| split; reflexivity].
    - rewrite RSC. exact SCk.
    - rewrite RPC. exact PCk.   (* [comment removed for export] *)
    - exact STm.
    - exact STKSH2.
    - apply rw_errno_any.
    - cbn [vi_bss_vsc VIA]. apply rw_C8_any; [clear; lia| clear; lia| vm_compute; reflexivity| vm_compute; reflexivity].
    - cbn [vi_bss_cp VIA]. apply rw_C8_any; [clear; lia| clear; lia| vm_compute; reflexivity| vm_compute; reflexivity].
    - exact CFA.
  Qed.
End S.
End A_Haqjq.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_WSmsm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_WSmsm.A_HKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Ha0ng.A_Ha5zr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Ha0ng.A_Haqjq.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (data : Z) (inp : list byte) (SB N : Z) (T : TSet).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPLO : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis MI00 : mem_inv rsegs (aview A0 m0).
  Hypothesis ST00 : stk rsegs (aview A0 m0) (bv_unsigned sp - LIB_STACK) (bv_unsigned sp).
  Hypothesis STKSH00 : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64).
  Hypothesis FR00 : forall ff, a_frame A0 ff = None.
  Hypothesis LEN : Z.of_nat (length inp) < NMAX.
  Hypothesis INP : length inp <> 0%nat -> data <> 0 /\ a_live A0 data = Some (Z.of_nat (length inp)) /\ bytes_at rsegs (aview A0 m0) data inp.
  Hypothesis BUD : a_livebytes A0 + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A0 + LIB_NLIVE <= NLIVE_MAX.
  Hypothesis SECC : LIB_SECC (Z.of_nat (length inp)) <= a_seccred A0.
  Hypothesis PRIMC : LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model) (A' : AS),
      alib_post sp m0 md0 A0 inp SB N m' md' A' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj TP (conj SP16 (conj SPLO (conj SPHI (conj AINV00 (conj MI00 (conj ST00 (conj STKSH00 (conj FR00 (conj LEN (conj INP (conj BUD
      (conj SECC (conj PRIMC K)))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    pose proof (zr_word ra) as RAR; unfold inr64 in RAR;
    unfold LIB_STACK in *.

  Local Ltac pose_exit :=
    pose proof (harness_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 data inp SB N T
                  TP SP16 SPLO SPHI AINV00 MI00 ST00 STKSH00 FR00 LEN INP BUD SECC PRIMC K) as harness_exit'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP data"] Lemma seg_T : forall (Ak : AS) (mk : mem) (mdk : Model) (E : option (Z * Z)) (ff : Z) (age : nat) (d : Z) (Nk : Z -> Prop)
      (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs4 xs5 xs8 xs9 xs11 xt3 xt4 xt5 xt6 : word) (j32 j32b hdr bs : list byte),
    let sp1 := bv_unsigned sp + -192 - d in let SHB := sh ff in let H := HENV ff in
    ainv Ak mk mdk -> mem_inv rsegs (aview Ak mk) -> amd_frame md0 mdk ->
    a_frame Ak ff = Some (HCLASS, age) -> ff <> 0 ->
    (forall g, g <> ff -> a_frame Ak g = None) ->
    match E with
    | None => ws0_obj LPA H (aview Ak mk) /\ (forall p n, a_live A0 p = Some n -> a_live Ak p = Some n) /\ a_livebytes Ak = a_livebytes A0 /\ a_nlive Ak = a_nlive A0
    | Some (wa, vep) => ws1_obj LPA H Ak (aview Ak mk) wa vep /\ a_live A0 wa = None /\ a_live A0 vep = None /\
                        (forall p n, a_live A0 p = Some n -> a_live Ak p = Some n) /\
                        a_livebytes Ak = a_livebytes A0 + 352 /\ a_nlive Ak = a_nlive A0 + 2 /\
                        (forall a, newblk wa 40 a \/ newblk vep 312 a -> Nk a)
    end ->
    glob_ok LPA VIA H (aview Ak mk) -> hshadow LPA H (aview Ak mk) ->
    a_tinycred Ak = a_tinycred A0 ->
    a_seccred A0 - LIB_SECC (Z.of_nat (length inp)) <= a_seccred Ak <= a_seccred A0 ->
    a_primcred A0 - LIB_PRIM (Z.of_nat (length inp)) <= a_primcred Ak <= a_primcred A0 ->   (* [comment removed for export] *)
    0 <= d <= 16 -> sp1 mod 16 = 0 ->
    stk rsegs (aview Ak mk) (bv_unsigned sp - LIB_STACK) sp1 ->
    (* [comment removed for export] *)
    rw_cells rsegs (aview Ak mk) sp1 [CB 40 j32; C8 (Z_to_bv 64 (SHB + 192)); C8 (Z_to_bv 64 (SHB + 4)); C8 (Z_to_bv 64 (SHB + 394)); CB 24 j32b] ->
    stk rsegs (aview Ak mk) (sp1 + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs (aview Ak mk) (bv_unsigned sp + -104) (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells rsegs (aview Ak mk) SHB [CB 540 bs] ->
    rw_cells rsegs (aview Ak mk) ff [CB 24 hdr] ->
    stack_shadow LPA (aview Ak mk) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned Ak) (bv_unsigned sp) LIB_STACK (HV ff) Nk (aview A0 m0) (aview Ak mk) ->
    (forall a, frm ff HCLASS a -> owned A0 a \/ (aview A0 m0 (Z_to_bv 64 a) = None /\ ~ in_image LPA a)) ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull Ak) (alhull Ak) (aeager Ak) mk mdk T)
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ff) (Z_to_bv 64 SHB) xs4 xs5 (Z_to_bv 64 ff)
                 (Z_to_bv 64 18446744073709551608) xs8 xs9 (Z_to_bv 64 (h_ws H)) xs11 xt3 xt4 xt5 xt6)   (* [comment removed for export] *)
            F (Z_to_bv 64 0x874cc) fc None (aview Ak mk) (seg_rom rsegs)).
  Proof.
    touch_all. intros until bs. cbv zeta. intros AINVk MIk MDFk FFk FFNZ FRk HE GLOBk HSHk TCk SCk PCk D0 AL16 STlo SPILL STpad SAV SHC FFH STKSHk CF0k FRM0.
    pose_exit. prelims.
    pose proof (as_minv LPA Ak _ _ AINVk) as [_ MHk].
    (first [ pose proof ((fframe_geom LPA Ak mk mdk ff HCLASS age AINVk FFk)) as dR_1; dand5 dR_1 as _ FS FLO FHI _ | destruct (fframe_geom LPA Ak mk mdk ff HCLASS age AINVk FFk) as (_ & FS & FLO & FHI & _) ]).
    rewrite fsize7 in FS, FHI. change (Z.min 8192 4096) with 4096 in FS.
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_2; dex2 dR_2 as ix sx; rename dR_2 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_2; dand3 dR_2 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    assert (HFk : hframe LPA Ak (HENV ff)) by (exists age; exact FFk).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    astop0 AINVk.
    lazymatch goal with AIq : ainv Ak ?mq ?mdq, SBq : same_but_materialized mdk ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa; rename mq into m1; rename mdq into md1 end.
    lazymatch goal with MIq : mem_inv _ (aview Ak m1) |- _ => rename MIq into MIa end.
    assert (STKSHr : stack_shadow LPA (aview Ak m1) SB N (bv_unsigned sp + -192 - d - WSROLLBACK_STACK - 64) (bv_unsigned sp + -192 - d + 64))
      by (eapply (stack_shadow_sub LPA); [exact STKSHk| unfold_stacks; keeplia D0| keeplia D0| keeplia SPLO ACV]).
    eapply (WS_Rollback_ok (HENV ff) E (bv_unsigned sp - 12288) SB N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 Ak T);
      [ exact AINVa | exact MIa | reflexivity | reflexivity
      | destruct E as [[wa vep]|]; [exact (proj1 HE)| exact (proj1 HE)]
      | exact GLOBk | exact HSHk | exact HFk | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact STlo
      | keeplia SPLO ACV
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold_stacks; keeplia SPLO D0 ACV
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact STKSHr | ].
    clear STKSHr.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A2 m2 md2. cbv zeta.
    intros AINV2 MI2 MDF2 FRS2 TC2 SC2 PC2 ST2 GLOB2 HSH2 WS2 LIVE2 CF2.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST2, CF2 by (keeplia SPR D0 SPLO ACV). unfold WSROLLBACK_STACK, WSRESET_STACK, WSAFREE_STACK, ASTK in CF2.
    replace (ret_pc (Z_to_bv 64 0x874d8)) with (Z_to_bv 64 0x874d8) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
    assert (FF2 : a_frame A2 ff = Some (HCLASS, age)) by (rewrite (FRS2 ff); exact FFk).
    (* [comment removed for export] *)
    lazymatch type of CF2 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      assert (VOUT : forall a, (sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24 \/ bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ SB <= a < SB + N) -> ~ V a)
    end.
    { (first [ pose proof (STKSHk) as dR_3; dand6 dR_3 as _ SSN SSL SSH SSC SST | pose proof STKSHk as (_ & SSN & SSL & SSH & SSC & SST) ]). unfold kHighMemBeg in SST. pose proof sh_ceiling_ge as SHC8.
      intros a Ha X. unfold h_ws, h_wsbuf in X. cbn [h_ff] in X.
      destruct E as [[wa vep]|].
      - destruct HE as (WS1 & _). (first [ dex2 WS1 as id pad; dand7 WS1 as _ _ _ _ LWA _ LVEP | dand9 WS1 as id pad _ _ _ _ LWA _ LVEP | destruct WS1 as (id & pad & _ & _ & _ & _ & LWA & _ & LVEP) ]).
        (first [ pose proof ((live_geomP LPA Ak mk mdk wa 40 AINVk LWA)) as dR_5; dand5 dR_5 as _ _ WAlo WAhi _ | pose proof (live_geomP LPA Ak mk mdk wa 40 AINVk LWA) as (_ & _ & WAlo & WAhi & _) ]). unfold kHighMemBeg in WAlo. all_app_facts.
        (first [ pose proof ((live_geomP LPA Ak mk mdk vep 312 AINVk LVEP)) as dR_6; dand5 dR_6 as _ _ VPlo VPhi _ | pose proof (live_geomP LPA Ak mk mdk vep 312 AINVk LVEP) as (_ & _ & VPlo & VPhi & _) ]). unfold kHighMemBeg in VPlo. all_app_facts.
        pose proof (as_frame_blk_disjoint LPA Ak mk mdk ff HCLASS age wa 40 AINVk FFk LWA) as DJW. rewrite fsize7 in DJW.
        pose proof (as_frame_blk_disjoint LPA Ak mk mdk ff HCLASS age vep 312 AINVk FFk LVEP) as DJV. rewrite fsize7 in DJV.
        pose proof (sh_boundL (Clg:=Clg) wa 40 ltac:(keeplia WAlo) ltac:(clear; lia) ltac:(exact WAhi)) as SHW. rewrite SHMAX_val in SHW. change ((40 + 7) / 8) with 5 in SHW.
        pose proof (sh_boundL (Clg:=Clg) vep 312 ltac:(keeplia VPlo) ltac:(clear; lia) ltac:(exact VPhi)) as SHV. rewrite SHMAX_val in SHV. change ((312 + 7) / 8) with 39 in SHV.
        unfold newblk, blk in X. change ((40 + 7) / 8) with 5 in X. change ((312 + 7) / 8) with 39 in X.
        keep_bundles; try (generalize alloc_ceiling_val); clear - Ha X FB SPLO DJW DJV WAlo WAhi VPlo VPhi SHW SHV SSC SST SHC8; intros;
        try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; unfold sh, kShadowOffset in *; Z.div_mod_to_equations; lia.
      - keeplia Ha X FB SPLO ACV SSC SST SHC8. }
    lazymatch type of CF2 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA Ak A2 xsp win V Nn ma mb CF2 (bv_unsigned sp + -104)) in SAV;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) Ak _ _ ma (bv_unsigned sp + -104) 104 AINVa ltac:(keeplia SPLO ACV) ltac:(keeplia SPR)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SAV ltac:(off_image_solve LPA)))
       | unfold SAVE; cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; refine (VOUT _ _ X); keeplia Hi] ];
      apply (rw_cells_ccall LPA Ak A2 xsp win V Nn ma mb CF2 (bv_unsigned sp + -192 - d)) in SPILL;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) Ak _ _ ma (bv_unsigned sp + -192 - d) 88 AINVa ltac:(keeplia SPLO ACV D0) ltac:(keeplia SPR D0)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SPILL ltac:(off_image_solve LPA)))
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; refine (VOUT _ _ X); keeplia Hi D0] ];
      apply (rw_cells_ccall LPA Ak A2 xsp win V Nn ma mb CF2 (sh ff)) in SHC;
      [| eapply crange_fshadow; [exact AINVa| exact FFk| clear; lia| rewrite fsize7; change (8192 / 8) with 1024; cbn [Cells.cells_size Cells.csize Nat.add length]; clear; lia| cbn; clear; lia]
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia FB SPLO ACV D0| intros i Hi X; refine (VOUT _ _ X); keeplia Hi] ];
      apply (rw_cells_ccall LPA Ak A2 xsp win V Nn ma mb CF2 ff) in FFH;
      [| eapply crange_fframe; [exact AINVa| exact FFk| clear; lia| rewrite fsize7; cbn [Cells.cells_size Cells.csize Nat.add length]; clear; lia| cbn; clear; lia]
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia FB SPLO ACV D0| intros i Hi X; refine (VOUT _ _ X); keeplia Hi] ];
      apply (stk_ccall_any Ak A2 _ _ ma mb xsp win V Nn _ _ AINVa CF2) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; refine (VOUT _ _ X); keeplia Ha D0];
      assert (STKSH2 : stack_shadow LPA mb SB N (bv_unsigned sp - 12288) (bv_unsigned sp + 64));
      [ (first [ pose proof (STKSHk) as dR_7; dand6 dR_7 as SSB SSN SSL SSH SSC SST | pose proof STKSHk as (SSB & SSN & SSL & SSH & SSC & SST) ]);
        pose proof (crange_stack_shadow (Clg:=Clg) LPA Ak _ _ SB N _ _ AINVa STKSHk ltac:(keeplia SPLO ACV)) as CRS;
        eapply stack_shadow_again; [exact STKSHk| | reflexivity];
        apply (bytes_at_ccall LPA Ak A2 xsp win V Nn ma mb CF2 SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN; split;
          [ unfold kHighMemBeg in SST; pose proof sh_ceiling_ge as SHC8; keeplia SSC SST SHC8 SPLO ACV D0
          | intros i Hi X; refine (VOUT _ _ X); keeplia Hi]
        | exact SSB ]
      | ]
    end.
    (* [comment removed for export] *)
    assert (MP2 : mapped (aview A2 m2) (bv_unsigned sp - 12288) 12288).
    { pose proof (stk_release rsegs _ _ _ _ ST2 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
    lazymatch type of CF2 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      pose proof (cframe_reframe LPA (owned Ak) (owned A2) xsp win (bv_unsigned sp) 12288 V Nn ma mb CF2 ltac:(keeplia D0) ltac:(keeplia D0 SPR) MP2) as CF2';
      assert (V2N : forall a, V a -> Nk a \/ HV ff a)
        by (intros a X; destruct X as [X|[X|X]];
            [ right; right; left; unfold h_ws in X; cbn [h_ff] in X; rewrite fsize7; keeplia X
            | right; right; left; unfold h_wsbuf in X; cbn [h_ff] in X; rewrite fsize7; keeplia X
            | destruct E as [[wa vep]|]; [left; (first [ dand7 HE as _ _ _ _ _ _ HN | destruct HE as (_ & _ & _ & _ & _ & _ & HN) ]); exact (HN a X)| destruct X] ]);
      pose proof (cframe_seq LPA (owned A0) (owned Ak) (owned A2) (bv_unsigned sp) 12288 12288 12288 (HV ff) Nk V Nn (HV ff) Nk
                  (aview A0 m0) ma mb CF0k CF2' ltac:(clear; lia) ltac:(clear; lia) MP2 ltac:(intros a X; exact X) V2N ltac:(intros a X; left; exact X)) as CF02;
      clear V2N
    end.
    clear CF2' CF0k.
    (* [comment removed for export] *)
    ago AINV2. fold_cl_segs.
    zstep. zstep. zstep.
    destruct (rw_cells_forget rsegs _ _ _ SPILL) as [jsp SPILL']. cbn [cells_size csize Nat.add] in SPILL'. clear SPILL.
    assert (CFP : client_fp LPA A2 (aview A2 m2) [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)]).
    { cbn. split; [left; split; [keeplia SPLO ACV| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - 12288)) with 12288 by (clear; lia); exact MP2]]|].
      split; [right; right; right; exists ff, HCLASS, age; split; [exact FF2| rewrite fsize7; change (8192 / 8) with 1024; clear; lia]|].
      split; [right; right; left; exists ff, HCLASS, age; split; [exact FF2| rewrite fsize7; clear; lia]| exact I]. }
    unfold LIB_STACK in harness_exit'.
    eapply (harness_exit' A2 m2 md2 (aview A2 m2) ff age d Nk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jsp hdr bs);
      [ exact AINV2 | eapply amd_frame_trans; [exact MDFk| eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMa| exact MHk]| exact MDF2]]
      | apply munch_refl | apply wmono_refl | exact CFP | exact MI2 | exact FF2 | exact FFNZ
      | intros g NE; rewrite (FRS2 g); exact (FRk g NE)
      | intros p n Hp; destruct E as [[wa vep]|];
        [ (first [ dand5 HE as _ A0W A0V LV _ | destruct HE as (_ & A0W & A0V & LV & _) ]); (first [ dand4 LIVE2 as DW DV LV2 _ | destruct LIVE2 as (DW & DV & LV2 & _) ]);
          rewrite (LV2 p); [exact (LV p n Hp)| intros ->; rewrite A0W in Hp; discriminate Hp| intros ->; rewrite A0V in Hp; discriminate Hp]
        | (first [ dand3 HE as _ LV _ | destruct HE as (_ & LV & _) ]); destruct LIVE2 as (LV2 & _); rewrite (LV2 p); exact (LV p n Hp) ]
      | destruct E as [[wa vep]|]; [(first [ dand6 HE as _ _ _ _ LB _ | destruct HE as (_ & _ & _ & _ & LB & _) ]); (first [ dand5 LIVE2 as _ _ _ LB2 _ | destruct LIVE2 as (_ & _ & _ & LB2 & _) ]); rewrite LB2, LB; clear; lia
                                   | (first [ dand4 HE as _ _ LB _ | destruct HE as (_ & _ & LB & _) ]); (first [ dand3 LIVE2 as _ LB2 _ | destruct LIVE2 as (_ & LB2 & _) ]); rewrite LB2; exact LB]
      | destruct E as [[wa vep]|]; [(first [ dand7 HE as _ _ _ _ _ NL _ | destruct HE as (_ & _ & _ & _ & _ & NL & _) ]); (first [ dand5 LIVE2 as _ _ _ _ NL2 | destruct LIVE2 as (_ & _ & _ & _ & NL2) ]); rewrite NL2, NL; clear; lia
                                   | (first [ dand4 HE as _ _ _ NL | destruct HE as (_ & _ & _ & NL) ]); (first [ dand3 LIVE2 as _ _ NL2 | destruct LIVE2 as (_ & _ & NL2) ]); rewrite NL2; exact NL]
      | rewrite TC2; exact TCk
      | rewrite SC2; exact SCk
      | rewrite PC2; exact PCk (* [comment removed for export] *)
      | exact D0 | exact AL16 | exact ST2 | exact SPILL' | exact STpad | exact SAV | exact SHC | exact FFH | exact STKSH2 | exact CF02 | exact FRM0 ].
  Qed.
End S.
