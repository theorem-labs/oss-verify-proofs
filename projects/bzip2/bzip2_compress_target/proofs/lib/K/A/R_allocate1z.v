(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA Arr Walk Image.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Malloc Require MallocKit_AB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_thread R_cache_defs R_prim_defs R_leaves R_rzlog R_depot_defs R_asan_defs R_allocate1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr Walk Image.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_leaves.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_rzlog.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_asan_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_allocate1.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


(* [comment removed for export] *)
Definition allocate_p1_post_cf5 (cf : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n n5 B T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x32bb0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n5) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
                  (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x36da4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ (exists j, rw_cells bsegs m' (bv_unsigned sp + -128) [CB 8 j])
    /\ alloc_frame_cf (Z_to_bv 64 cf) m' (bv_unsigned sp + -128) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk bsegs m' lo (bv_unsigned sp + -128).

(* [comment removed for export] *)
Lemma allocate_p1_spec_cf0 : forall (cf : Z) ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B TCX T lo : Z),
  (0 <= cf <= 1)%Z -> (0 < B < 2^63)%Z ->
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells bsegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T < 2^63)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (0x62b000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (allocate_p1_post_cf5 cf ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 0 B T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 0) (Z_to_bv 64 8) (Z_to_bv 64 B)
             (Z_to_bv 64 1) (Z_to_bv 64 cf) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hcf HB AI RS MX RZ TC HTCX HTCXl HT ST HLO HIMG HSP MI. unfold allocate_entry.
  destruct TC as [(KI & K & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  unfold g_asan_inited, g_rss_limit_exceeded, INST, g_instance in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 120%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle1 AI. zidle1 RS. zidle1 MX. zidle1 RZ. zidle1 KI. zidle1 K. zidle1 TS. zidle1 T0. zidle1 TT.
  do 21 zstep.
  zidle_end_m m.
  call (asan_inited_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep.
  call (rss_limit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep. ifF.
  ro_debruijn MI.
  zstep. zstep. ifT.
  do 3 zstep. ifT.
  do 3 zstep. ifF.
  do 9 zstep. fold_reg 11%Z.
  do 6 zstep. ifT.
  do 4 zstep. ifF.
  zstep. zstep. zstep; fix_lit_store. zstep; fix_lit_store.
  (* [comment removed for export] *)
  zstep. ifF. do 2 zstep.
  do 6 zstep.
  sp_facts.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 5 zstep.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 7%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  (* [comment removed for export] *)
  zstep. ifF. zstep. zstep. ifF. do 3 zstep. ifF. zstep.
  do 9 zstep.
  (* [comment removed for export] *)
  zstep. dIf_closed.
  do 15 zstep.
  dIf_closed. zstep. dIf_closed.
  do 2 zstep. dIf_closed.
  zstep.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [assumption| split; [assumption| split; assumption]]| assumption]. }
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 2 zstep. ifF.
  do 5 zstep.
  finish.
  - eexists. eassumption.
  - unfold alloc_frame_cf. replace (bv_unsigned sp + -128 + 8)%Z with (bv_unsigned sp + -120)%Z by lia. eassumption.
Qed.

(* [comment removed for export] *)
Definition allocate_p1_post5 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n n5 B T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x32bb0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n5) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
                  (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x36da4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ (exists j, rw_cells bsegs m' (bv_unsigned sp + -128) [CB 8 j])
    /\ alloc_frame m' (bv_unsigned sp + -128) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk bsegs m' lo (bv_unsigned sp + -128).

Lemma allocate_p1_spec0 : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B TCX T lo : Z),
  (0 < B < 2^63)%Z ->
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells bsegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T < 2^63)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (0x62b000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (allocate_p1_post5 ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 0 B T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 0) (Z_to_bv 64 8) (Z_to_bv 64 B)
             (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros. eapply evt_mono; [eapply (allocate_p1_spec_cf0 1); try eassumption; lia|].
  intros ms' P. unfold allocate_p1_post_cf5 in P. unfold allocate_p1_post5, alloc_frame. exact P.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr Walk Image.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout R_small R_thread R_cache_defs R_prim_defs R_leaves R_rzlog
  R_sizeclass R_depot_defs R_asan_defs R_allocate1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


(* [comment removed for export] *)
Definition allocate_p1_post_cf5 (cf : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n n5 B T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x32cc8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n5) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
                  (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x36ebc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists j, rw_cells asegs m' (bv_unsigned sp + -128) [CB 8 j])
    /\ alloc_frame_cf (Z_to_bv 64 cf) m' (bv_unsigned sp + -128) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk asegs m' lo (bv_unsigned sp + -128).

(* [comment removed for export] *)
Lemma allocate_p1_spec_cf0 : forall (cf : Z) ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B TCX T lo : Z),
  (0 <= cf <= 1)%Z -> (0 < B < 2^63)%Z ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] -> rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T < 2^63)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (0x61e000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_p1_post_cf5 cf ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 0 B T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 0) (Z_to_bv 64 8) (Z_to_bv 64 B)
             (Z_to_bv 64 1) (Z_to_bv 64 cf) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hcf HB AI RS MX RZ TC HTCX HTCXl HT ST HLO HIMG HSP MI. unfold allocate_entry.
  destruct TC as [(KI & K & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  unfold g_asan_inited, g_rss_limit_exceeded, INST, g_instance in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 120%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle1 AI. zidle1 RS. zidle1 MX. zidle1 RZ. zidle1 KI. zidle1 K. zidle1 TS. zidle1 T0. zidle1 TT.
  do 21 zstep.
  zidle_end_m m.
  call (asan_inited_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep.
  call (rss_limit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep. ifF.
  ro_debruijn MI.
  zstep. zstep. ifT.
  do 3 zstep. ifT.
  do 3 zstep. ifF.
  do 9 zstep. fold_reg 11%Z.
  do 6 zstep. ifT.
  do 4 zstep. ifF.
  zstep. zstep. zstep; fix_lit_store. zstep; fix_lit_store.
  (* [comment removed for export] *)
  zstep. ifF. do 2 zstep.
  do 6 zstep.
  sp_facts.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 5 zstep.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 7%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  (* [comment removed for export] *)
  zstep. ifF. zstep. zstep. ifF. do 3 zstep. ifF. zstep.
  do 9 zstep.
  (* [comment removed for export] *)
  zstep. dIf_closed.
  do 15 zstep.
  dIf_closed. zstep. dIf_closed.
  do 2 zstep. dIf_closed.
  zstep.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [assumption| split; [assumption| split; assumption]]| assumption]. }
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 2 zstep. ifF.
  do 5 zstep.
  finish.
  - eexists. eassumption.
  - unfold alloc_frame_cf. replace (bv_unsigned sp + -128 + 8)%Z with (bv_unsigned sp + -120)%Z by lia. eassumption.
Qed.

(* [comment removed for export] *)
Definition allocate_p1_post5 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n n5 B T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x32cc8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n5) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
                  (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x36ebc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists j, rw_cells asegs m' (bv_unsigned sp + -128) [CB 8 j])
    /\ alloc_frame m' (bv_unsigned sp + -128) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk asegs m' lo (bv_unsigned sp + -128).

Lemma allocate_p1_spec0 : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B TCX T lo : Z),
  (0 < B < 2^63)%Z ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] -> rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T < 2^63)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (0x61e000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_p1_post5 ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 0 B T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 0) (Z_to_bv 64 8) (Z_to_bv 64 B)
             (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros. eapply evt_mono; [eapply (allocate_p1_spec_cf0 1); try eassumption; lia|].
  intros ms' P. unfold allocate_p1_post_cf5 in P. unfold allocate_p1_post5, alloc_frame. exact P.
Qed.
