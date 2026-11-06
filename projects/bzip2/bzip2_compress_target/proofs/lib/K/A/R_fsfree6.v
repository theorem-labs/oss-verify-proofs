(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_ok.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__.
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
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_na H A a
    | H : ro_cells segs m ?A _ |- _ => zidle_na H A a
    | H : u8arr segs m ?A _ |- _ => zidle_na H A a
    | H : u32arr segs m ?A _ |- _ => zidle_na H A a
    | H : u64arr segs m ?A _ |- _ => zidle_na H A a
    | H : bytes_at segs m ?A _ |- _ => zidle_na H A a
    | H : u8ro segs m ?A _ |- _ => zidle_na H A a
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


(* [comment removed for export] *)
Lemma u8one_store_ok : forall (m : mem) A b, u8arr bsegs m A [b] -> store_ok bsegs m (wa A) 1 = true.
Proof. intros m A b H. apply (u8arr_store_ok bsegs m A [b] 0 (wa A) H); [cbn; lia | f_equal; lia]. Qed.
Lemma u8one_write : forall (m : mem) A b v, u8arr bsegs m A [b] -> u8arr bsegs (write_to_mem m (wa A) [v]) A [v].
Proof.
  intros m A b v H. pose proof (u8arr_write bsegs m A [b] 0 v H ltac:(cbn; lia)) as X.
  replace (A + 0) with A in X by lia. exact X.
Qed.

Definition sf6_entry : Z := 0x3e2ec.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sf_W (c FSB pos usp : Z) : list (Z * Z) :=
  [(fl_base FSB c + pos, fl_base FSB c + pos + 1); (shad (frame_addr FSB c pos), shad (frame_addr FSB c pos) + fsz c / 8); (usp - 64, usp)].

Definition sf6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB pos lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a0' : word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sf_W 6 FSB pos (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u8arr bsegs m' (fl_base FSB 6 + pos) [Z_to_bv 8 0].

Lemma stack_free_6_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB pos lo : Z) (b0 : byte) (junkF junkS : list byte),
  0 <= pos < 256 ->
  u8arr bsegs m (fl_base FSB 6 + pos) [b0] ->
  rw_cells bsegs m (frame_addr FSB 6 pos) [CB 4088 junkF; C8 (Z_to_bv 64 (fl_base FSB 6 + pos))] ->
  rw_cells bsegs m (shad (frame_addr FSB 6 pos)) [CB 512 junkS] ->
  m2s_cells m -> FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  evt bsegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (frame_addr FSB 6 pos)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sf6_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until junkS. intros Hpos FLG LAST SHm M2S FSOK HLO FSL ST LO SPH MI.
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. unfold frame_addr, fsz, fl_base, flags_off in *.
  change (6 * 2 ^ 20) with 6291456 in *. change (64 * 2 ^ 6) with 4096 in *. change (6 * 2 ^ 17) with 786432 in SHm.
  change (4096 / 8) with 512 in SHm. change (32768 - 2 ^ (15 - 6)) with 32256 in *.
  replace (FSB + 36864 + 6291456 + pos * 4096) with (FSB + 6328320 + pos * 4096) in * by lia.
  replace (FSB + 4096 + 32256) with (FSB + 36352) in * by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 786432 + pos * 512) with (F8 + pos * 512 + 2148241920) in SHm by (unfold SHB; lia).
  destruct M2S as (M2a & M2b & M2c).
  unfold sf6_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(FSB + 36352 + pos, FSB + 36352 + pos + 1); (F8 + pos * 512 + 2148241920, F8 + pos * 512 + 2148241920 + 512);
                          (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zhide.
  do 3 zstep.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8one_store_ok mm (FSB + 36352 + pos) b0 FLG) as SOK;
    pose proof (u8one_write mm (FSB + 36352 + pos) b0 (Z_to_bv 8 0) FLG) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear FLG. store_done.
  zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 6328320 + pos * 4096)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 6328320 + pos * 4096) = F8 + pos * 512 + 2148241920).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 6328320 + pos * 4096) with ((F8 + 791040 + pos * 512) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite ESH. clear M2a M2b M2c.
  do 3 zstep.
  zidle_begin_at (F8 + pos * 512 + 2148241920)%Z 512%Z MUz WMz.
  do 63 (lstep; zstep; zstep; ifT).
  lstep. zstep. zstep. ifF.
  zidle_end MUz WMz.
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold sf6_post.
  do 15 eexists. eexists.
  split; [reflexivity|].
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  split.
  { replace (sf_W 6 FSB pos (bv_unsigned sp)) with
      [(FSB + 36352 + pos, FSB + 36352 + pos + 1); (F8 + pos * 512 + 2148241920, F8 + pos * 512 + 2148241920 + 512);
       (bv_unsigned sp - 64, bv_unsigned sp)]; [exact MU|].
    unfold sf_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (6 * 2 ^ 20) with 6291456. change (64 * 2 ^ 6) with 4096. change (6 * 2 ^ 17) with 786432.
    change (4096 / 8) with 512. change (32768 - 2 ^ (15 - 6)) with 32256.
    repeat (f_equal; try lia). }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  replace (fl_base FSB 6 + pos) with (FSB + 36352 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FL2.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr.
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
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_na H A a
    | H : ro_cells segs m ?A _ |- _ => zidle_na H A a
    | H : u8arr segs m ?A _ |- _ => zidle_na H A a
    | H : u32arr segs m ?A _ |- _ => zidle_na H A a
    | H : u64arr segs m ?A _ |- _ => zidle_na H A a
    | H : bytes_at segs m ?A _ |- _ => zidle_na H A a
    | H : u8ro segs m ?A _ |- _ => zidle_na H A a
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


(* [comment removed for export] *)
Lemma u8one_store_ok : forall (m : mem) A b, u8arr asegs m A [b] -> store_ok asegs m (wa A) 1 = true.
Proof. intros m A b H. apply (u8arr_store_ok asegs m A [b] 0 (wa A) H); [cbn; lia | f_equal; lia]. Qed.
Lemma u8one_write : forall (m : mem) A b v, u8arr asegs m A [b] -> u8arr asegs (write_to_mem m (wa A) [v]) A [v].
Proof.
  intros m A b v H. pose proof (u8arr_write asegs m A [b] 0 v H ltac:(cbn; lia)) as X.
  replace (A + 0) with A in X by lia. exact X.
Qed.

Definition sf6_entry : Z := 0x3e404.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sf_W (c FSB pos usp : Z) : list (Z * Z) :=
  [(fl_base FSB c + pos, fl_base FSB c + pos + 1); (shad (frame_addr FSB c pos), shad (frame_addr FSB c pos) + fsz c / 8); (usp - 64, usp)].

Definition sf6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB pos lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a0' : word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sf_W 6 FSB pos (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u8arr asegs m' (fl_base FSB 6 + pos) [Z_to_bv 8 0].

Lemma stack_free_6_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB pos lo : Z) (b0 : byte) (junkF junkS : list byte),
  0 <= pos < 256 ->
  u8arr asegs m (fl_base FSB 6 + pos) [b0] ->
  rw_cells asegs m (frame_addr FSB 6 pos) [CB 4088 junkF; C8 (Z_to_bv 64 (fl_base FSB 6 + pos))] ->
  rw_cells asegs m (shad (frame_addr FSB 6 pos)) [CB 512 junkS] ->
  m2s_cells m -> FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (frame_addr FSB 6 pos)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sf6_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junkS. intros Hpos FLG LAST SHm M2S FSOK HLO FSL ST LO SPH MI.
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. unfold frame_addr, fsz, fl_base, flags_off in *.
  change (6 * 2 ^ 20) with 6291456 in *. change (64 * 2 ^ 6) with 4096 in *. change (6 * 2 ^ 17) with 786432 in SHm.
  change (4096 / 8) with 512 in SHm. change (32768 - 2 ^ (15 - 6)) with 32256 in *.
  replace (FSB + 36864 + 6291456 + pos * 4096) with (FSB + 6328320 + pos * 4096) in * by lia.
  replace (FSB + 4096 + 32256) with (FSB + 36352) in * by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 786432 + pos * 512) with (F8 + pos * 512 + 2148241920) in SHm by (unfold SHB; lia).
  destruct M2S as (M2a & M2b & M2c).
  unfold sf6_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(FSB + 36352 + pos, FSB + 36352 + pos + 1); (F8 + pos * 512 + 2148241920, F8 + pos * 512 + 2148241920 + 512);
                          (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  zhide.
  do 3 zstep.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8one_store_ok mm (FSB + 36352 + pos) b0 FLG) as SOK;
    pose proof (u8one_write mm (FSB + 36352 + pos) b0 (Z_to_bv 8 0) FLG) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear FLG. store_done.
  zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 6328320 + pos * 4096)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 6328320 + pos * 4096) = F8 + pos * 512 + 2148241920).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 6328320 + pos * 4096) with ((F8 + 791040 + pos * 512) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite ESH. clear M2a M2b M2c.
  do 3 zstep.
  zidle_begin_at (F8 + pos * 512 + 2148241920)%Z 512%Z MUz WMz.
  do 63 (lstep; zstep; zstep; ifT).
  lstep. zstep. zstep. ifF.
  zidle_end MUz WMz.
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold sf6_post.
  do 15 eexists. eexists.
  split; [reflexivity|].
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  split.
  { replace (sf_W 6 FSB pos (bv_unsigned sp)) with
      [(FSB + 36352 + pos, FSB + 36352 + pos + 1); (F8 + pos * 512 + 2148241920, F8 + pos * 512 + 2148241920 + 512);
       (bv_unsigned sp - 64, bv_unsigned sp)]; [exact MU|].
    unfold sf_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (6 * 2 ^ 20) with 6291456. change (64 * 2 ^ 6) with 4096. change (6 * 2 ^ 17) with 786432.
    change (4096 / 8) with 512. change (32768 - 2 ^ (15 - 6)) with 32256.
    repeat (f_equal; try lia). }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  replace (fl_base FSB 6 + pos) with (FSB + 36352 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FL2.
Qed.
