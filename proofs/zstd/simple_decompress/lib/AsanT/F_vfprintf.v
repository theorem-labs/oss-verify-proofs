(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import Stdio_kit F_syscalls StdioFiles MonadF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_printf_iface.

From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
  [C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Lemma file_cells_g : forall flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
  file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail
  = gfile_cells flags 0 0 0xbc1e8 wend wpos wbase writefn 0xbc32c buf bufsize fd mode (Z_to_bv 64 0xffffffff) lbf ++ [C4 z64; CB 80 tail].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_g_stmt : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
    rw_cells bsegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv bsegs m ->
    rng RNG (bv_unsigned a0) 148 ->
    evtF bsegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ rw_cells bsegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xbcca8) fc None m (seg_rom bsegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
  unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI RFP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold gfile_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem towrite_proof : towrite_stmt.
Proof.
  unfold towrite_stmt. intros until tail. intros FC NOWR B0 BHI BS0 MI RFP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | let t := type of H in idtac "FC:" t; fail] end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arg_ok_vf : forall Fp B BS RNG m m' lo sp sp' ap w a,
  arg_ok Fp B BS RNG m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono bsegs m m' ->
  appW [(lo, sp); (Fp, Fp + 232)] -> arg_ok Fp B BS RNG m' lo sp' ap w a.
Proof.
  intros Fp B BS RNG m m' lo sp sp' ap w a H Hsp MU WM AW. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & D5 & RG & r & RC & IR & RR). exists slack.
  split; [|repeat (split; [first [assumption | lia]|])].
  - eapply bytes_at_transport; [exact BY | exact MU |].
    cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
  - exists r. split; [| split; [exact IR | exact RR]]. eapply rclean_transport; [exact RC | exact MU | exact WM | exact AW].
Qed.
Lemma args_ok_vf : forall Fp B BS RNG m m' lo sp sp' ap ws args,
  args_ok Fp B BS RNG m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono bsegs m m' ->
  appW [(lo, sp); (Fp, Fp + 232)] -> args_ok Fp B BS RNG m' lo sp' ap ws args.
Proof.
  intros Fp B BS RNG m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU WM AW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells bsegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
  rw_cells bsegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post [[Hwf Hb] Hw] WF.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
End CANSEC1.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Section CANSEC2. Context {rc : runConstT}.
Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells bsegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
End CANSEC2.
