(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_libiface I_lift X_atexit L_hkit L_harn_defs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
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
Definition hz_frame (z0 : cell) (j8 : list byte) (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [z0; CB 24 j8; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma hz_wA0 : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 128 -> 0x7fff7f800000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 z0 : word) (j8 : list byte),
      ms = entry_st (Z_to_bv 64 0x81374) (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
             (Z_to_bv 64 64) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 u3 u4 u5 u6
             F fc (e_stack_malloc 0) m1
      /\ munch [(usp - 128, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -128)
      /\ rw_cells bsegs m1 (usp + -128) (hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO LOS SPH S32 CC MI.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_fuzz, e_stack_malloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return, hz_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 128 _ [] [8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  zhide.
  do 15 lstep.
  lstep. rewrite (land_m32 (usp + -128)) by lia. replace (32 * ((usp + -128) / 32)) with (usp + -128) by (Z.div_mod_to_equations; lia).
  do 6 xstep.
  (* [comment removed for export] *)
  clear G1 G3.
  xsteps_to 0x3dc94%Z.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma hz_wA16 : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 144 -> 0x7fff7f800000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 z0 : word) (jg j8 : list byte),
      ms = entry_st (Z_to_bv 64 0x81374) (Z_to_bv 64 (usp + -144)) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -144))
             (Z_to_bv 64 64) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 u3 u4 u5 u6
             F fc (e_stack_malloc 0) m1
      /\ munch [(usp - 144, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -144)
      /\ rw_cells bsegs m1 (usp + -144) (CB 16 jg :: hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO LOS SPH S32 CC MI.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_fuzz, e_stack_malloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return, hz_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 144, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 144%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 144 _ [] [16; 8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  zhide.
  do 15 lstep.
  lstep. rewrite (land_m32 (usp + -128)) by lia. replace (32 * ((usp + -128) / 32)) with (usp + -144) by (Z.div_mod_to_equations; lia).
  do 6 xstep.
  clear G1 G3.
  xsteps_to 0x3dc94%Z.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_libiface I_lift X_atexit
  L_hkit L_harn_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
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
Definition hz_frame (z0 : cell) (j8 : list byte) (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [z0; CB 24 j8; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma hz_wA0 : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 128 -> 0x7fff7f800000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 z0 : word) (j8 : list byte),
      ms = entry_st (Z_to_bv 64 0x81928) (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
             (Z_to_bv 64 64) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 u3 u4 u5 u6
             F fc (e_stack_malloc 0) m1
      /\ munch [(usp - 128, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -128)
      /\ rw_cells asegs m1 (usp + -128) (hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO LOS SPH S32 CC MI.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_fuzz, e_stack_malloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return, hz_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  zhide.
  do 15 lstep.
  lstep. rewrite (land_m32 (usp + -128)) by lia. replace (32 * ((usp + -128) / 32)) with (usp + -128) by (Z.div_mod_to_equations; lia).
  do 6 xstep.
  (* [comment removed for export] *)
  clear G1 G3.
  xsteps_to 0x3ddac%Z.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma hz_wA16 : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 144 -> 0x7fff7f800000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 z0 : word) (jg j8 : list byte),
      ms = entry_st (Z_to_bv 64 0x81928) (Z_to_bv 64 (usp + -144)) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -144))
             (Z_to_bv 64 64) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 u3 u4 u5 u6
             F fc (e_stack_malloc 0) m1
      /\ munch [(usp - 144, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -144)
      /\ rw_cells asegs m1 (usp + -144) (CB 16 jg :: hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO LOS SPH S32 CC MI.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_fuzz, e_stack_malloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return, hz_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 144, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 144%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 144 _ [] [16; 8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  zhide.
  do 15 lstep.
  lstep. rewrite (land_m32 (usp + -128)) by lia. replace (32 * ((usp + -128) / 32)) with (usp + -144) by (Z.div_mod_to_equations; lia).
  do 6 xstep.
  clear G1 G3.
  xsteps_to 0x3ddac%Z.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.
