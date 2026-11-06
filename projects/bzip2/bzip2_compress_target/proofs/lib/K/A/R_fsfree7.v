(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_intalloc F_memset R_setshadow R_poison.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr R_fsfree6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memset.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_ok.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fsfree6.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.



Definition sf7_entry : Z := 0x3e4b0.

Definition sf7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB pos lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a0' : word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sf_W 7 FSB pos (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u8arr bsegs m' (fl_base FSB 7 + pos) [Z_to_bv 8 0].

Lemma stack_free_7_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB pos lo size : Z) (b0 : byte) (junkS : list byte),
  0 <= pos < 128 -> 0 < size <= 8192 -> size mod 8 = 0 ->
  u8arr bsegs m (fl_base FSB 7 + pos) [b0] ->
  rw_cells bsegs m (frame_addr FSB 7 pos + 8184) [C8 (Z_to_bv 64 (fl_base FSB 7 + pos))] ->
  rw_cells bsegs m (shad (frame_addr FSB 7 pos)) [CB 1024 junkS] ->
  m2s_cells m -> ps_cells m -> FSB_ok2 FSB -> 0x7fff00000000 <= lo -> FSB + kFakeStackSize <= lo ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  evt bsegs (sf7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (frame_addr FSB 7 pos)) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sf7_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until junkS. intros Hpos Hsz Hsz8 FLG LAST SHm M2S PS FSOK HLO FSL ST LO SPH MI.
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. unfold frame_addr, fsz, fl_base, flags_off in *.
  change (7 * 2 ^ 20) with 7340032 in *. change (64 * 2 ^ 7) with 8192 in *. change (7 * 2 ^ 17) with 917504 in SHm.
  change (8192 / 8) with 1024 in SHm. change (32768 - 2 ^ (15 - 7)) with 32512 in *.
  replace (FSB + 36864 + 7340032 + pos * 8192) with (FSB + 7376896 + pos * 8192) in * by lia.
  replace (FSB + 4096 + 32512) with (FSB + 36608) in * by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 917504 + pos * 1024) with (F8 + pos * 1024 + 2148372992) in SHm by (unfold SHB; lia).
  assert (PA : ps_args_ok (FSB + 7376896 + pos * 8192) size).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [|split; [exact Hsz8 | lia]]|lia].
    rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hq8 : 0 <= size / 8 <= 1024) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  set (k8 := Z.to_nat (size / 8)) in *.
  pose proof (rw_cells_split_CB bsegs m _ [] 1024%nat junkS [] [k8; (1024 - k8)%nat] SHm ltac:(cbn [sum_nat]; unfold k8; lia)) as SHs.
  cbn [app mk_CB_cells] in SHs. clear SHm.
  apply (rw_cells_app2 m _ [CB k8 (firstn k8 junkS)] [CB (1024 - k8) (firstn (1024 - k8) (skipn k8 junkS))]) in SHs. destruct SHs as [SHa SHb].
  cbn [cells_size csize Nat.add] in SHb. rewrite Nat.add_0_r in SHb. unfold k8 in SHb at 1. rewrite Z2Nat.id in SHb by lia.
  destruct M2S as (M2a & M2b & M2c).
  unfold sf7_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(FSB + 36608 + pos, FSB + 36608 + pos + 1); (F8 + pos * 1024 + 2148372992, F8 + pos * 1024 + 2148372992 + 1024);
                          (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 32%nat ST.
  zhide.
  do 6 zstep.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8one_store_ok mm (FSB + 36608 + pos) b0 FLG) as SOK;
    pose proof (u8one_write mm (FSB + 36608 + pos) b0 (Z_to_bv 8 0) FLG) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear FLG. store_done.
  zstep. zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 7376896 + pos * 8192) = F8 + pos * 1024 + 2148372992).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  clear M2a M2b M2c.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm end.
  rewrite <- ESH in SHa.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192) size 245 lo (firstn k8 junkS)).
  1: exact PA.
  1: lia.
  1: left; lia.
  1: exact SHa.
  1: exact PSm.
  all: try lia; try assumption; try (unfold kHighShadowEnd; lia).
  apply evt_done. unfold sf7_post.
  do 15 eexists. eexists.
  split; [reflexivity|].
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  split.
  { replace (sf_W 7 FSB pos (bv_unsigned sp)) with
      [(FSB + 36608 + pos, FSB + 36608 + pos + 1); (F8 + pos * 1024 + 2148372992, F8 + pos * 1024 + 2148372992 + 1024);
       (bv_unsigned sp - 64, bv_unsigned sp)]; [exact MU|].
    unfold sf_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (7 * 2 ^ 20) with 7340032. change (64 * 2 ^ 7) with 8192. change (7 * 2 ^ 17) with 917504.
    change (8192 / 8) with 1024. change (32768 - 2 ^ (15 - 7)) with 32512.
    repeat (f_equal; try lia). }
  split; [exact WM|]. split; [assumption|]. split; [assumption|].
  replace (fl_base FSB 7 + pos) with (FSB + 36608 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FL2.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import R_intalloc F_memset R_setshadow R_poison.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr R_fsfree6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.



Definition sf7_entry : Z := 0x3e5c8.

Definition sf7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB pos lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a0' : word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sf_W 7 FSB pos (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u8arr asegs m' (fl_base FSB 7 + pos) [Z_to_bv 8 0].

Lemma stack_free_7_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB pos lo size : Z) (b0 : byte) (junkS : list byte),
  0 <= pos < 128 -> 0 < size <= 8192 -> size mod 8 = 0 ->
  u8arr asegs m (fl_base FSB 7 + pos) [b0] ->
  rw_cells asegs m (frame_addr FSB 7 pos + 8184) [C8 (Z_to_bv 64 (fl_base FSB 7 + pos))] ->
  rw_cells asegs m (shad (frame_addr FSB 7 pos)) [CB 1024 junkS] ->
  m2s_cells m -> ps_cells m -> FSB_ok2 FSB -> 0x7fff00000000 <= lo -> FSB + kFakeStackSize <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (sf7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (frame_addr FSB 7 pos)) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sf7_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junkS. intros Hpos Hsz Hsz8 FLG LAST SHm M2S PS FSOK HLO FSL ST LO SPH MI.
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. unfold frame_addr, fsz, fl_base, flags_off in *.
  change (7 * 2 ^ 20) with 7340032 in *. change (64 * 2 ^ 7) with 8192 in *. change (7 * 2 ^ 17) with 917504 in SHm.
  change (8192 / 8) with 1024 in SHm. change (32768 - 2 ^ (15 - 7)) with 32512 in *.
  replace (FSB + 36864 + 7340032 + pos * 8192) with (FSB + 7376896 + pos * 8192) in * by lia.
  replace (FSB + 4096 + 32512) with (FSB + 36608) in * by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 917504 + pos * 1024) with (F8 + pos * 1024 + 2148372992) in SHm by (unfold SHB; lia).
  assert (PA : ps_args_ok (FSB + 7376896 + pos * 8192) size).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [|split; [exact Hsz8 | lia]]|lia].
    rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hq8 : 0 <= size / 8 <= 1024) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  set (k8 := Z.to_nat (size / 8)) in *.
  pose proof (rw_cells_split_CB asegs m _ [] 1024%nat junkS [] [k8; (1024 - k8)%nat] SHm ltac:(cbn [sum_nat]; unfold k8; lia)) as SHs.
  cbn [app mk_CB_cells] in SHs. clear SHm.
  apply (rw_cells_app2 m _ [CB k8 (firstn k8 junkS)] [CB (1024 - k8) (firstn (1024 - k8) (skipn k8 junkS))]) in SHs. destruct SHs as [SHa SHb].
  cbn [cells_size csize Nat.add] in SHb. rewrite Nat.add_0_r in SHb. unfold k8 in SHb at 1. rewrite Z2Nat.id in SHb by lia.
  destruct M2S as (M2a & M2b & M2c).
  unfold sf7_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(FSB + 36608 + pos, FSB + 36608 + pos + 1); (F8 + pos * 1024 + 2148372992, F8 + pos * 1024 + 2148372992 + 1024);
                          (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  zhide.
  do 6 zstep.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8one_store_ok mm (FSB + 36608 + pos) b0 FLG) as SOK;
    pose proof (u8one_write mm (FSB + 36608 + pos) b0 (Z_to_bv 8 0) FLG) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear FLG. store_done.
  zstep. zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 7376896 + pos * 8192) = F8 + pos * 1024 + 2148372992).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  clear M2a M2b M2c.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm end.
  rewrite <- ESH in SHa.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192) size 245 lo (firstn k8 junkS)).
  1: exact PA.
  1: lia.
  1: left; lia.
  1: exact SHa.
  1: exact PSm.
  all: try lia; try assumption; try (unfold kHighShadowEnd; lia).
  apply evt_done. unfold sf7_post.
  do 15 eexists. eexists.
  split; [reflexivity|].
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  split.
  { replace (sf_W 7 FSB pos (bv_unsigned sp)) with
      [(FSB + 36608 + pos, FSB + 36608 + pos + 1); (F8 + pos * 1024 + 2148372992, F8 + pos * 1024 + 2148372992 + 1024);
       (bv_unsigned sp - 64, bv_unsigned sp)]; [exact MU|].
    unfold sf_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (7 * 2 ^ 20) with 7340032. change (64 * 2 ^ 7) with 8192. change (7 * 2 ^ 17) with 917504.
    change (8192 / 8) with 1024. change (32768 - 2 ^ (15 - 7)) with 32512.
    repeat (f_equal; try lia). }
  split; [exact WM|]. split; [assumption|]. split; [assumption|].
  replace (fl_base FSB 7 + pos) with (FSB + 36608 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FL2.
Qed.
