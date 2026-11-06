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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_merge Printf_lib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_cache_defs.
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
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hz_wE : forall (usp spa Fr d n zb ob dlv : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x62b000 <= Fr -> Fr + 64 < 2^47 -> 0 <= n < 2^26 -> 0 <= ob < 2^64 -> 0 <= dlv < 2^31 ->
  rw_cells bsegs m (Fr + 32) [C4 (Z_to_bv 64 dlv)] -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = entry_st (Z_to_bv 64 RA_B2BD) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 ob)
             (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 zb) (Z_to_bv 64 dlv) (Z_to_bv 64 (n mod 2)) (Z_to_bv 64 0) a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) (Z_to_bv 64 ob) (Z_to_bv 64 (Fr + 48))
             (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_b2bd m)
    (MS (mkR (Z_to_bv 64 0x814c8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 ob) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x814c8)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH N0 OB DL NZC MI.
  unfold entry_st, e_b2bd, RA_B2BD in *.
  replace (ret_pc (Z_to_bv 64 0x814c8)) with (Z_to_bv 64 0x814c8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 7 lstep.
  rewrite Printf_lib.sx32_lit by lia. replace (Z.land n 1) with (n mod 2) by (rewrite (Z.land_ones n 1) by lia; reflexivity).
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hz_ret (pc : Z) (usp spa Fr d n zb : Z) (a0 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
     F (ret_pc (Z_to_bv 64 pc)) fc None m (seg_rom bsegs).
Definition hz_call (ra entry : Z) (usp spa Fr d n zb : Z) (a0 a1 a2 : word) (gp tp t0 t1 t2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem) : machine_state :=
  entry_st (Z_to_bv 64 ra) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6
           F fc entry m.

(* [comment removed for export] *)
Lemma rc_nonzero : forall rc, rc <> 0 /\ -9 <= rc <= 4 -> bv_eqb (Z_to_bv 64 rc) z64 = false.
Proof.
  intros rc [RC0 RC]. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned z64) with 0.
  destruct (Z_lt_le_dec rc 0) as [N|N].
  - replace (Z_to_bv 64 rc) with (Z_to_bv 64 (rc + 2^64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
    rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma hz_wF_err : forall (usp spa Fr d n zb ob rc : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  (rc <> 0 /\ -9 <= rc <= 4) -> 0 <= zb < 2^64 ->
  evt bsegs (eq (hz_call 0x8150c e_free usp spa Fr d n zb (Z_to_bv 64 zb) a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m))
    (hz_ret RA_B2BD usp spa Fr d n zb (Z_to_bv 64 rc) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros RC ZB. unfold hz_ret, hz_call, entry_st, e_free, RA_B2BD.
  replace (ret_pc (Z_to_bv 64 0x814e4)) with (Z_to_bv 64 0x814e4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. rewrite (rc_nonzero rc RC). cbv iota beta delta [negb].
  lstep. lstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wF : forall (usp spa Fr d n zb ob : Z) (j7 : list byte) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x62b000 <= Fr -> Fr + 64 < 2^47 -> 0 <= n < 2^26 -> rw_cells bsegs m (Fr + 48) [C4 (Z_to_bv 64 n); CB 4 j7] -> mem_inv bsegs m ->
  evt bsegs (eq (hz_call 0x81500 e_memcmp usp spa Fr d n zb (Z_to_bv 64 d) (Z_to_bv 64 ob) (Z_to_bv 64 n) gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m))
    (hz_ret RA_B2BD usp spa Fr d n zb (Z_to_bv 64 0) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH N0 NOUT MI. unfold hz_ret, hz_call, entry_st, e_memcmp, RA_B2BD.
  replace (ret_pc (Z_to_bv 64 0x814e4)) with (Z_to_bv 64 0x814e4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. if_false. lstep. rewrite OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__.zx32_small by lia.
  lstep. if_false. lstep. lstep. lstep. lstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wG : forall (usp spa Fr d n zb ob : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= zb < 2^64 ->
  evt bsegs (eq (hz_call 0x8150c e_free usp spa Fr d n zb (Z_to_bv 64 zb) a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m))
    (hz_ret 0x81500 usp spa Fr d n zb (Z_to_bv 64 0) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros ZB. unfold hz_ret, hz_call, entry_st, e_free.
  replace (ret_pc (Z_to_bv 64 0x81500)) with (Z_to_bv 64 0x81500) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. if_false. lstep. lstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wH : forall (usp spa Fr d n zb : Z) (a0 s7 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt bsegs (eq (hz_call 0x81514 e_free usp spa Fr d n zb s7 a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 F fc m))
    (hz_ret 0x8150c usp spa Fr d n zb a0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. unfold hz_ret, hz_call, entry_st, e_free.
  replace (ret_pc (Z_to_bv 64 0x8150c)) with (Z_to_bv 64 0x8150c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. lstep. apply evt_done. reflexivity.
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

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_merge Printf_lib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_cache_defs.

(* [comment removed for export] *)
Lemma hz_wE : forall (usp spa Fr d n zb ob dlv : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x61e000 <= Fr -> Fr + 64 < 2^47 -> 0 <= n < 2^26 -> 0 <= ob < 2^64 -> 0 <= dlv < 2^31 ->
  rw_cells asegs m (Fr + 32) [C4 (Z_to_bv 64 dlv)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = entry_st (Z_to_bv 64 RA_B2BD) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 ob)
             (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 zb) (Z_to_bv 64 dlv) (Z_to_bv 64 (n mod 2)) (Z_to_bv 64 0) a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) (Z_to_bv 64 ob) (Z_to_bv 64 (Fr + 48))
             (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_b2bd m)
    (MS (mkR (Z_to_bv 64 0x81a7c) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 ob) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x81a7c)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH N0 OB DL NZC MI.
  unfold entry_st, e_b2bd, RA_B2BD in *.
  replace (ret_pc (Z_to_bv 64 0x81a7c)) with (Z_to_bv 64 0x81a7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 7 lstep.
  rewrite Printf_lib.sx32_lit by lia. replace (Z.land n 1) with (n mod 2) by (rewrite (Z.land_ones n 1) by lia; reflexivity).
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hz_ret (pc : Z) (usp spa Fr d n zb : Z) (a0 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
     F (ret_pc (Z_to_bv 64 pc)) fc None m (seg_rom asegs).
Definition hz_call (ra entry : Z) (usp spa Fr d n zb : Z) (a0 a1 a2 : word) (gp tp t0 t1 t2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem) : machine_state :=
  entry_st (Z_to_bv 64 ra) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6
           F fc entry m.

(* [comment removed for export] *)
Lemma rc_nonzero : forall rc, rc <> 0 /\ -9 <= rc <= 4 -> bv_eqb (Z_to_bv 64 rc) z64 = false.
Proof.
  intros rc [RC0 RC]. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned z64) with 0.
  destruct (Z_lt_le_dec rc 0) as [N|N].
  - replace (Z_to_bv 64 rc) with (Z_to_bv 64 (rc + 2^64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
    rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma hz_wF_err : forall (usp spa Fr d n zb ob rc : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  (rc <> 0 /\ -9 <= rc <= 4) -> 0 <= zb < 2^64 ->
  evt asegs (eq (hz_call 0x81ac0 e_free usp spa Fr d n zb (Z_to_bv 64 zb) a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m))
    (hz_ret RA_B2BD usp spa Fr d n zb (Z_to_bv 64 rc) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros RC ZB. unfold hz_ret, hz_call, entry_st, e_free, RA_B2BD.
  replace (ret_pc (Z_to_bv 64 0x81a98)) with (Z_to_bv 64 0x81a98) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. rewrite (rc_nonzero rc RC). cbv iota beta delta [negb].
  lstep. lstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wF : forall (usp spa Fr d n zb ob : Z) (j7 : list byte) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x61e000 <= Fr -> Fr + 64 < 2^47 -> 0 <= n < 2^26 -> rw_cells asegs m (Fr + 48) [C4 (Z_to_bv 64 n); CB 4 j7] -> mem_inv asegs m ->
  evt asegs (eq (hz_call 0x81ab4 e_memcmp usp spa Fr d n zb (Z_to_bv 64 d) (Z_to_bv 64 ob) (Z_to_bv 64 n) gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m))
    (hz_ret RA_B2BD usp spa Fr d n zb (Z_to_bv 64 0) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH N0 NOUT MI. unfold hz_ret, hz_call, entry_st, e_memcmp, RA_B2BD.
  replace (ret_pc (Z_to_bv 64 0x81a98)) with (Z_to_bv 64 0x81a98) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. if_false. lstep. rewrite R_cache_defs.zx32_small by lia.
  lstep. if_false. lstep. lstep. lstep. lstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wG : forall (usp spa Fr d n zb ob : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= zb < 2^64 ->
  evt asegs (eq (hz_call 0x81ac0 e_free usp spa Fr d n zb (Z_to_bv 64 zb) a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m))
    (hz_ret 0x81ab4 usp spa Fr d n zb (Z_to_bv 64 0) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros ZB. unfold hz_ret, hz_call, entry_st, e_free.
  replace (ret_pc (Z_to_bv 64 0x81ab4)) with (Z_to_bv 64 0x81ab4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. if_false. lstep. lstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hz_wH : forall (usp spa Fr d n zb : Z) (a0 s7 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt asegs (eq (hz_call 0x81ac8 e_free usp spa Fr d n zb s7 a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 F fc m))
    (hz_ret 0x81ac0 usp spa Fr d n zb a0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. unfold hz_ret, hz_call, entry_st, e_free.
  replace (ret_pc (Z_to_bv 64 0x81ac0)) with (Z_to_bv 64 0x81ac0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lstep. lstep. apply evt_done. reflexivity.
Qed.
