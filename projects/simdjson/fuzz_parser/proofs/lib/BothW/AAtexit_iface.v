(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw DrvAgree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ATX_FIN : Z := 0x66ea40.    (* [comment removed for export] *)
Definition ATX_LOCK : Z := 0x66ea44.   (* [comment removed for export] *)
Definition ATX_SLOT : Z := 0x66ea48.   (* [comment removed for export] *)
Definition ATX_HEAD : Z := 0x66ea50.   (* [comment removed for export] *)
Definition ATX_BUILTIN : Z := 0x66ea58.  (* [comment removed for export] *)
Definition ATX_F : Z := 0x66ea60.
Definition ATX_A : Z := 0x66eb60.

Definition atexit_cells (fs args : list word) (n : Z) (m : mem) : Prop :=
  rw_cells bsegs m ATX_FIN [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m ATX_LOCK [C4 z64] /\ rw_cells bsegs m ATX_SLOT [C4 (Z_to_bv 64 n)]
  /\ rw_cells bsegs m ATX_HEAD [C8 (Z_to_bv 64 ATX_BUILTIN)] /\ rw_cells bsegs m ATX_BUILTIN [C8 z64]
  /\ rw_cells bsegs m ATX_F (map C8 fs) /\ rw_cells bsegs m ATX_A (map C8 args)
  /\ length fs = 32%nat /\ length args = 32%nat.

Definition ATEXIT (tbl : list (Z * Z)) (m : mem) : Prop :=
  exists fj aj : list word,
    atexit_cells (map (fun e => Z_to_bv 64 (fst e)) (rev tbl) ++ fj) (map (fun e => Z_to_bv 64 (snd e)) (rev tbl) ++ aj) (Z.of_nat (length tbl)) m.

(* [comment removed for export] *)
Definition TBL_MAIN : list (Z * Z) := [(0xfa580, 0x84bc0)].
Definition TBL_RUN (f a : Z) : list (Z * Z) := (f, a) :: TBL_MAIN.
Definition AATEXIT : Z := 0xfa4bc.
Definition ACALL_THUNK : Z := 0xfa580.
Definition AXHOOK : Z := 0x95588.
Definition AIN_CB : Z := 0x64dcd4.
Definition TBL_REG : list (Z * Z) := (0xfa580, 0x95588) :: TBL_MAIN.

(* [comment removed for export] *)
Lemma cells_size_map_C8' : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma ATEXIT_transport : forall tbl mx my,
  (forall A cs, 0x66ea40 <= A -> A + Z.of_nat (cells_size cs) <= 0x66ec60 -> rw_cells bsegs mx A cs -> rw_cells bsegs my A cs) ->
  ATEXIT tbl mx -> ATEXIT tbl my.
Proof.
  intros tbl mx my T (fj & aj & C1' & C2 & C3 & C4' & C5 & C6 & C7 & L1 & L2). exists fj, aj.
  unfold atexit_cells, ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
  split; [apply T; [lia| cbn; lia| exact C1']|]. split; [apply T; [lia| cbn; lia| exact C2]|]. split; [apply T; [lia| cbn; lia| exact C3]|].
  split; [apply T; [lia| cbn; lia| exact C4']|]. split; [apply T; [lia| cbn; lia| exact C5]|].
  split; [apply T; [lia| rewrite cells_size_map_C8', L1; lia| exact C6]|]. split; [apply T; [lia| rewrite cells_size_map_C8', L2; lia| exact C7]|].
  split; assumption.
Qed.
Lemma ATEXIT_magree : forall (P : Z -> Prop) tbl mx my, ATEXIT tbl mx -> magree bsegs P mx my -> (forall a, 0x66ea40 <= a < 0x66ec60 -> P a) -> ATEXIT tbl my.
Proof.
  intros P tbl mx my AT AG HP. eapply ATEXIT_transport; [| exact AT]. intros A cs HA HB RW.
  eapply rw_cells_magree; [exact AG| exact RW|]. intros a Ha. apply HP. lia.
Qed.
Lemma atx_disjoint_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.
Lemma ATEXIT_munch : forall W tbl mx my, ATEXIT tbl mx -> munch W mx my -> wmono bsegs mx my -> disjoint_from W 0x66ea40 544 -> ATEXIT tbl my.
Proof.
  intros W tbl mx my AT MU WM DJ. eapply ATEXIT_transport; [| exact AT]. intros A cs HA HB RW.
  eapply rw_cells_transport; [exact RW| exact MU| exact WM|]. eapply atx_disjoint_sub; [exact DJ| lia| lia| lia].
Qed.

Definition aincb (cb : Z) (m : mem) : Prop := rw_cells bsegs m 0x64dcd4 [C1 (Z_to_bv 8 cb)].
Definition aincb_addr (a : Z) : Prop := 0x64dcd4 <= a < 0x64dcd5.
Lemma aincb_magree : forall (P : Z -> Prop) cb m m',
  magree bsegs P m m' -> (forall a, aincb_addr a -> P a) -> aincb cb m -> aincb cb m'.
Proof. intros P cb m m' AG HP A. unfold aincb in *. eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold aincb_addr; cbn in Ha; lia]. Qed.
Lemma aincb_munch : forall W cb m m',
  munch W m m' -> wmono bsegs m m' -> (forall a, aincb_addr a -> outside W a) -> aincb cb m -> aincb cb m'.
Proof. intros W cb m m' MU WM HW. apply (aincb_magree _ _ _ _ (magree_of_munch bsegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha. Qed.
Lemma aincb_addr_range : forall a, aincb_addr a -> a = 0x64dcd4.
Proof. intros a Ha. unfold aincb_addr in Ha. lia. Qed.

Definition ATXS (tbl : list (Z * Z)) (m : mem) : Prop := ATEXIT tbl m /\ aincb 0 m /\ (tbl = TBL_MAIN \/ tbl = TBL_REG).
Definition atxs_addr (a : Z) : Prop := (0x66ea40 <= a < 0x66ec60) \/ aincb_addr a.
Lemma ATXS_magree : forall (P : Z -> Prop) tbl mx my, ATXS tbl mx -> magree bsegs P mx my -> (forall a, atxs_addr a -> P a) -> ATXS tbl my.
Proof.
  intros P tbl mx my (AT & CB & TB) AG HP. split; [| split; [| exact TB]].
  - eapply ATEXIT_magree; [exact AT| exact AG|]. intros a Ha. apply HP. left. exact Ha.
  - eapply aincb_magree; [exact AG| | exact CB]. intros a Ha. apply HP. right. exact Ha.
Qed.
End CANSEC1.

Local Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Local Ltac hstep := sort_lits; zstep; fix_lit_store.
Local Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Local Ltac astep := hstep; try (first [if_true | if_false]).
Local Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Local Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
Local Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
Definition atx_hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (atx_hidden T) in H end.
Local Ltac unhide H := unfold atx_hidden in H.

Section CANSEC2. Context {rc : runConstT}.
Definition AATEXIT_STACK : Z := 48.

Definition atexit1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x66ea48, 0x66ea4c); (0x66ea68, 0x66ea70); (0x66eb68, 0x66eb70)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ATEXIT TBL_REG m'.

Lemma atexit1_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x66ec80 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ATEXIT TBL_MAIN m ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AXHOOK ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (atexit1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AATEXIT) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST LIBC ATX MI -> LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  destruct ATX as (fj & aj & FIN & ALK & SLOT & HEAD & NEXT & FF & AA & LF & LA).
  unfold ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
  unfold TBL_MAIN in FF, AA, SLOT, LF, LA. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FF, AA, SLOT, LF, LA.
  destruct fj as [|f1 fj]; [cbn in LF; lia|]. destruct aj as [|g1 aj]; [cbn in LA; lia|].
  cbn [length] in LF, LA. cbn [map] in FF, AA. change (Z.of_nat 1) with 1%Z in SLOT.
  change (C8 (Z_to_bv 64 0xfa580) :: C8 f1 :: map C8 fj) with ([C8 (Z_to_bv 64 0xfa580); C8 f1] ++ map C8 fj) in FF.
  change (C8 (Z_to_bv 64 0x84bc0) :: C8 g1 :: map C8 aj) with ([C8 (Z_to_bv 64 0x84bc0); C8 g1] ++ map C8 aj) in AA.
  apply (proj1 (rw_cells_app bsegs m _ _ _)) in FF. destruct FF as [FF FFR].
  apply (proj1 (rw_cells_app bsegs m _ _ _)) in AA. destruct AA as [AA AAR].
  match type of FFR with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in FFR end.
  match type of AAR with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in AAR end.
  pose proof (cells_size_map_C8' fj) as SZF. pose proof (cells_size_map_C8' aj) as SZA.
  hide FFR. hide AAR.
  unfold AXHOOK, AATEXIT.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x66ea48, 0x66ea4c); (0x66ea68, 0x66ea70); (0x66eb68, 0x66eb70)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x109250%Z.
  hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep. hstep.
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  hstep. astep.
  hstep. nlit. hstep. astep.
  steps_to 0x1094d8%Z.
  hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
  hstep. do 5 hstep.
  release_frame FR ST (bv_unsigned sp)%Z.
  hstep. hstep.
  unfold atexit1_post. apply evtF_done.
  do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  unhide FFR. unhide AAR.
  lazymatch type of MU with munch _ _ ?m' =>
    pose proof (rw_cells_transport bsegs _ m m' _ _ FFR MU WM ltac:(rewrite SZF; cbn [disjoint_from]; lia)) as FFR';
    pose proof (rw_cells_transport bsegs _ m m' _ _ AAR MU WM ltac:(rewrite SZA; cbn [disjoint_from]; lia)) as AAR';
    clear FFR AAR
  end.
  exists fj, aj. unfold atexit_cells, TBL_REG, TBL_MAIN, ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A.
  cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat match goal with |- _ /\ _ => split end; try hyp_by_addr.
  - change (C8 (Z_to_bv 64 0xfa580) :: C8 (Z_to_bv 64 0xfa580) :: map C8 fj)
      with ([C8 (Z_to_bv 64 0xfa580); C8 (Z_to_bv 64 0xfa580)] ++ map C8 fj).
    apply (proj2 (rw_cells_app bsegs _ _ _ _)). split; [hyp_by_addr|].
    match goal with |- rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' end. hyp_by_addr.
  - change (C8 (Z_to_bv 64 0x84bc0) :: C8 (Z_to_bv 64 0x95588) :: map C8 aj)
      with ([C8 (Z_to_bv 64 0x84bc0); C8 (Z_to_bv 64 0x95588)] ++ map C8 aj).
    apply (proj2 (rw_cells_app bsegs _ _ _ _)). split; [hyp_by_addr|].
    match goal with |- rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' end. hyp_by_addr.
  - cbn [length]. lia.
  - cbn [length]. lia.
Qed.
End CANSEC2.
