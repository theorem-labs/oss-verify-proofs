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

Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.
Ltac ls := lstep; try sb_fix.

(* [comment removed for export] *)
Lemma div100_regK : forall len, 0 <= len < 2 ^ 32 ->
  ((len ≫ 2 * 2951479051793528259) ≫ 64 mod 18446744073709551616) ≫ 2 = len / 100.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change 2951479051793528259 with M100.
  assert (B : 0 <= len / 2 ^ 2 * M100 / 2 ^ 64 < 2 ^ 64).
  { unfold M100. split; [apply Z.div_pos; [| lia]; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
    apply Z.div_lt_upper_bound; [lia|]. assert (len / 2 ^ 2 < 2 ^ 30) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos len (2 ^ 2) ltac:(lia) ltac:(lia)). nia. }
  rewrite Z.mod_small by exact B. change (2 ^ 2) with 4. apply div100_magic. exact H.
Qed.

(* [comment removed for export] *)
Definition hz_sh0 : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13))].

Lemma hz_wB : forall (usp spa Fr d n : Z) (jh js jsl : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x62b000 <= Fr -> Fr mod 64 = 0 -> (Fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr) -> Fr + 64 < 2^47 -> 0x7fff7f800000 <= spa < 2^63 -> 0 <= usp < 2^63 ->
  (Fr + 64 <= spa \/ spa + 32 <= Fr) -> 0 <= d < 2^64 -> 0 <= n < 2^26 ->
  rw_cells bsegs m Fr [CB 56 jh] -> rw_cells bsegs m (shad Fr) [CB 8 js] -> rw_cells bsegs m (spa + 24) [CB 8 jsl] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (h0 h1 h2 a1' a2' a3' a4' a5' : word) (j3 j5 j6 : list byte),
      ms = entry_st (Z_to_bv 64 0x81434) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 (nZ_of n))
             a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d)
             (Z_to_bv 64 (Fr + 32)) s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_malloc m'
      /\ munch [(Fr, Fr + 56); (shad Fr, shad Fr + 8); (spa + 24, spa + 32)] m m' /\ wmono bsegs m m'
      /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' Fr [C8 h0; C8 h1; C8 h2; CB 8 j3; C4 (Z_to_bv 64 (nZ_of n)); CB 12 j5; CB 8 j6]
      /\ rw_cells bsegs m' (shad Fr) hz_sh0 /\ rw_cells bsegs m' (spa + 24) [C8 (Z_to_bv 64 Fr)])
    (MS (mkR (Z_to_bv 64 0x81374) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 Fr) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 0x81374)) fc None m
        (seg_rom bsegs)).
Proof.
  intros until m. intros F0 F64 FSEG FH SPA USP SEPS D0 N0 HDR SHF SLOT MI.
  unfold entry_st, e_malloc, hz_sh0 in *.
  unfold shad, SHB in *.
  pose proof (munch_refl [(Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8); (spa + 24, spa + 32)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  replace (ret_pc (Z_to_bv 64 0x81374)) with (Z_to_bv 64 0x81374) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (EUF : bv_unsigned (Z_to_bv 64 Fr) = Fr) by (apply unsigned_lit; lia).
  assert (E3 : Fr ≫ 3 = Fr / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SEPH : Fr + 64 <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 8 <= Fr) by (Z.div_mod_to_equations; lia).
  assert (SEPS2 : Fr / 8 + 2147450880 + 8 <= spa) by (Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 12; 8]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app] in HDR.
  zhide.
  lstep. lstep. lstep. lstep. if_true.
  do 5 lstep. lstep. rewrite E3. do 10 lstep. lstep. ls. ls. ls. ls. lstep. lstep. ls. ls. ls. ls.
  do 5 lstep.
  rewrite (div100_regK n) by lia. replace (n + n / 100 + 600) with (nZ_of n) by (unfold nZ_of; lia).
  lstep. lstep. lstep. lstep.
  assert (NZB : 0 <= nZ_of n < 4294967296) by (unfold nZ_of; Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (nZ_of n) 18446744073709551616) by lia. rewrite (Z.mod_small (nZ_of n) 4294967296) by lia.
  apply evt_done. do 12 eexists. split; [reflexivity|].
  split; [replace (Fr / 8 + 2147450888) with (Fr / 8 + 2147450880 + 8) by lia; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; assumption.
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

Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.
Ltac ls := lstep; try sb_fix.

(* [comment removed for export] *)
Lemma div100_regK : forall len, 0 <= len < 2 ^ 32 ->
  ((len ≫ 2 * 2951479051793528259) ≫ 64 mod 18446744073709551616) ≫ 2 = len / 100.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change 2951479051793528259 with M100.
  assert (B : 0 <= len / 2 ^ 2 * M100 / 2 ^ 64 < 2 ^ 64).
  { unfold M100. split; [apply Z.div_pos; [| lia]; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
    apply Z.div_lt_upper_bound; [lia|]. assert (len / 2 ^ 2 < 2 ^ 30) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos len (2 ^ 2) ltac:(lia) ltac:(lia)). nia. }
  rewrite Z.mod_small by exact B. change (2 ^ 2) with 4. apply div100_magic. exact H.
Qed.

(* [comment removed for export] *)
Definition hz_sh0 : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13))].

Lemma hz_wB : forall (usp spa Fr d n : Z) (jh js jsl : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x61e000 <= Fr -> Fr mod 64 = 0 -> (Fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr) -> Fr + 64 < 2^47 -> 0x7fff7f800000 <= spa < 2^63 -> 0 <= usp < 2^63 ->
  (Fr + 64 <= spa \/ spa + 32 <= Fr) -> 0 <= d < 2^64 -> 0 <= n < 2^26 ->
  rw_cells asegs m Fr [CB 56 jh] -> rw_cells asegs m (shad Fr) [CB 8 js] -> rw_cells asegs m (spa + 24) [CB 8 jsl] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (h0 h1 h2 a1' a2' a3' a4' a5' : word) (j3 j5 j6 : list byte),
      ms = entry_st (Z_to_bv 64 0x819e8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 (nZ_of n))
             a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d)
             (Z_to_bv 64 (Fr + 32)) s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) s11 t3 t4 t5 t6 F fc e_malloc m'
      /\ munch [(Fr, Fr + 56); (shad Fr, shad Fr + 8); (spa + 24, spa + 32)] m m' /\ wmono asegs m m'
      /\ mem_inv asegs m'
      /\ rw_cells asegs m' Fr [C8 h0; C8 h1; C8 h2; CB 8 j3; C4 (Z_to_bv 64 (nZ_of n)); CB 12 j5; CB 8 j6]
      /\ rw_cells asegs m' (shad Fr) hz_sh0 /\ rw_cells asegs m' (spa + 24) [C8 (Z_to_bv 64 Fr)])
    (MS (mkR (Z_to_bv 64 0x81928) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 Fr) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 0x81928)) fc None m
        (seg_rom asegs)).
Proof.
  intros until m. intros F0 F64 FSEG FH SPA USP SEPS D0 N0 HDR SHF SLOT MI.
  unfold entry_st, e_malloc, hz_sh0 in *.
  unfold shad, SHB in *.
  pose proof (munch_refl [(Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8); (spa + 24, spa + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  replace (ret_pc (Z_to_bv 64 0x81928)) with (Z_to_bv 64 0x81928) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (EUF : bv_unsigned (Z_to_bv 64 Fr) = Fr) by (apply unsigned_lit; lia).
  assert (E3 : Fr ≫ 3 = Fr / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SEPH : Fr + 64 <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 8 <= Fr) by (Z.div_mod_to_equations; lia).
  assert (SEPS2 : Fr / 8 + 2147450880 + 8 <= spa) by (Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB asegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 12; 8]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app] in HDR.
  zhide.
  lstep. lstep. lstep. lstep. if_true.
  do 5 lstep. lstep. rewrite E3. do 10 lstep. lstep. ls. ls. ls. ls. lstep. lstep. ls. ls. ls. ls.
  do 5 lstep.
  rewrite (div100_regK n) by lia. replace (n + n / 100 + 600) with (nZ_of n) by (unfold nZ_of; lia).
  lstep. lstep. lstep. lstep.
  assert (NZB : 0 <= nZ_of n < 4294967296) by (unfold nZ_of; Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (nZ_of n) 18446744073709551616) by lia. rewrite (Z.mod_small (nZ_of n) 4294967296) by lia.
  apply evt_done. do 12 eexists. split; [reflexivity|].
  split; [replace (Fr / 8 + 2147450888) with (Fr / 8 + 2147450880 + 8) by lia; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; assumption.
Qed.
