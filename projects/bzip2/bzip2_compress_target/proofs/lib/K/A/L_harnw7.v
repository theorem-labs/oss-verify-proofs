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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_harnw1 L_harnw2 L_harnw5 L_harnw6.
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

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw5.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw6.TwinB__.
Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.
Ltac ls := lstep; try sb_fix.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hz_wJ1 : forall (usp spa Fr : Z) (h0 a0 s3 s4 s5 s6 s7 s8 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x62b000 <= Fr -> Fr mod 64 = 0 -> (Fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr) -> Fr + 64 < 2^47 ->
  rw_cells bsegs m Fr [C8 h0] -> rw_cells bsegs m (shad Fr) hz_sh0 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a0' : word),
      ms = MS (mkR (Z_to_bv 64 0x81514) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0' a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x81554) fc None m' (seg_rom bsegs)
      /\ munch [(Fr, Fr + 8); (shad Fr, shad Fr + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (shad Fr) hz_sh5)
    (MS (mkR (Z_to_bv 64 0x81514) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x81514)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 F64 FSEG FH HDR SHF MI.
  unfold hz_sh0, hz_sh5 in *. cbn [repeat] in *.
  unfold shad, SHB in *.
  pose proof (munch_refl [(Fr, Fr + 8); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  replace (ret_pc (Z_to_bv 64 0x81514)) with (Z_to_bv 64 0x81514) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SEPH : Fr + 64 <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 8 <= Fr) by (Z.div_mod_to_equations; lia).
  assert (EUF : bv_unsigned (Z_to_bv 64 Fr) = Fr) by (apply unsigned_lit; lia).
  zhide.
  lstep. ls. ls. lstep. lstep. lstep.
  lstep. if_false.
  lstep. ls. ls. ls. ls. ls. ls. ls. ls.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [replace (Fr / 8 + 2147450888) with (Fr / 8 + 2147450880 + 8) by lia; exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

(* [comment removed for export] *)
Lemma hz_wJ2 : forall (usp spa Fr fl : Z) (a0 s3 s4 s5 s6 s7 s8 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x62b000 <= Fr -> Fr + 64 < 2^47 -> 0 < fl -> fl + 1 <= 2^47 ->
  ro_cells bsegs m (Fr + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR (Z_to_bv 64 0x81514) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x81580) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR (Z_to_bv 64 0x81514) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81554) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH FL0 FLH LAST FLG MI.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EUF : bv_unsigned (Z_to_bv 64 Fr) = Fr) by (apply unsigned_lit; lia).
  zhide.
  lstep. ls. lstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; assumption.
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

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import L_harnw1 L_harnw2 L_harnw5 L_harnw6.
Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.
Ltac ls := lstep; try sb_fix.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hz_wJ1 : forall (usp spa Fr : Z) (h0 a0 s3 s4 s5 s6 s7 s8 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x61e000 <= Fr -> Fr mod 64 = 0 -> (Fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr) -> Fr + 64 < 2^47 ->
  rw_cells asegs m Fr [C8 h0] -> rw_cells asegs m (shad Fr) hz_sh0 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (a0' : word),
      ms = MS (mkR (Z_to_bv 64 0x81ac8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0' a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x81b08) fc None m' (seg_rom asegs)
      /\ munch [(Fr, Fr + 8); (shad Fr, shad Fr + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (shad Fr) hz_sh5)
    (MS (mkR (Z_to_bv 64 0x81ac8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x81ac8)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 F64 FSEG FH HDR SHF MI.
  unfold hz_sh0, hz_sh5 in *. cbn [repeat] in *.
  unfold shad, SHB in *.
  pose proof (munch_refl [(Fr, Fr + 8); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  replace (ret_pc (Z_to_bv 64 0x81ac8)) with (Z_to_bv 64 0x81ac8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SEPH : Fr + 64 <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 8 <= Fr) by (Z.div_mod_to_equations; lia).
  assert (EUF : bv_unsigned (Z_to_bv 64 Fr) = Fr) by (apply unsigned_lit; lia).
  zhide.
  lstep. ls. ls. lstep. lstep. lstep.
  lstep. if_false.
  lstep. ls. ls. ls. ls. ls. ls. ls. ls.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [replace (Fr / 8 + 2147450888) with (Fr / 8 + 2147450880 + 8) by lia; exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

(* [comment removed for export] *)
Lemma hz_wJ2 : forall (usp spa Fr fl : Z) (a0 s3 s4 s5 s6 s7 s8 : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x61e000 <= Fr -> Fr + 64 < 2^47 -> 0 < fl -> fl + 1 <= 2^47 ->
  ro_cells asegs m (Fr + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
      ms = MS (mkR (Z_to_bv 64 0x81ac8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x81b34) fc None m' (seg_rom asegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR (Z_to_bv 64 0x81ac8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81b08) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH FL0 FLH LAST FLG MI.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EUF : bv_unsigned (Z_to_bv 64 Fr) = Fr) by (apply unsigned_lit; lia).
  zhide.
  lstep. ls. lstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.
