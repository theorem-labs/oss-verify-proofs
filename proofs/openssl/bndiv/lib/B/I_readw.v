(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread I_consts RT_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
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
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
(* [comment removed for export] *)
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.

(* [comment removed for export] *)
Lemma read_walkA : forall (sp fd count : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo sp -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 -> 0 <= fd < 2^32 -> 0 <= count <= 65536 ->
  rw_cells bsegs m 0x5e3d40 [C8 (Z_to_bv 64 0x56a398)] -> rw_cells bsegs m 0x6a46d8 [C1 (Z_to_bv 8 1)] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) junk junk1,
      ms' = MSsvc (mkR (Z_to_bv 64 0x56a3c0) (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 g_read_stage)
                       (Z_to_bv 64 fd) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x564150) (Z_to_bv 64 63) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2144, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (sp + -2128) [CB 2080 junk]
      /\ rw_cells bsegs m' (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m' (sp + -2144) [CB 8 junk1; C8 (Z_to_bv 64 0x1aa4dc)]
      /\ stk bsegs m' lo (sp + -2144))
    (entry_st ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_read m).
Proof.
  intros until lo. intros ST LO0 LO UT Hfd Hcnt RR AI MI.
  unfold entry_st, e_read, g_read_stage. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp - 2144, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST. rename FR into FRt.
  carve_frame 2080%nat ST. rename FR into FRb.
  zidle_beginz sp 2128%Z MUz1 WMz1.
  zhide.
  do 14 step.
  zidle_end MUz1 WMz1.
  carve_frame 16%nat ST. rename FR into FRa.
  step. step. change (Z_to_le_bytes 8 1746112) with (le8 (Z_to_bv 64 1746112)). mem_after_store.
  step.
  do 6 step. if_false.
  do 4 step.
  release_frame FRa ST (sp + -2128).
  do 7 step.
  carve_frame 16%nat ST. rename FR into FRr.
  step. step. change (Z_to_le_bytes 8 1746140) with (le8 (Z_to_bv 64 1746140)). mem_after_store.
  do 7 step.
  do 9 step.
  step_ecall.
  do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact FRb|]. split; [exact FRt|]. split; [exact FRr| exact ST].
Qed.

(* [comment removed for export] *)
Lemma read_walkB_eof : forall (sp fd count : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) junk junk1,
  stk bsegs m lo (sp + -2144) -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 -> 0 <= fd < 2^32 -> 0 <= count <= 65536 ->
  rw_cells bsegs m (sp + -2144) [CB 8 junk1; C8 (Z_to_bv 64 0x1aa4dc)] ->
  rw_cells bsegs m (sp + -2128) [CB 2080 junk] ->
  rw_cells bsegs m (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
                 /\ stk bsegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x56a3c0) (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 g_read_stage)
             (Z_to_bv 64 0) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x564154) fc None m (seg_rom bsegs)).
Proof.
  intros until junk1. intros ST LO0 LO UT Hfd Hcnt FRr FRb FRt MI.
  unfold g_read_stage. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zhide.
  do 4 step.
  do 3 step. if_true.
  step.
  step. if_false.
  step. if_true.
  release_frame FRr ST (sp + -2128).
  release_frame FRb ST (sp + -48).
  do 9 step.
  release_frame FRt ST sp.
  apply evt_done. split; [| exact ST].
  do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_walkB_err : forall (sp fd count e : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) junk junk1 (errv : word),
  stk bsegs m lo (sp + -2144) -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 -> 0 <= fd < 2^32 -> 0 <= count <= 65536 ->
  1 <= e <= 4095 ->
  rw_cells bsegs m 0xbdadac [C4 errv] ->
  rw_cells bsegs m (sp + -2144) [CB 8 junk1; C8 (Z_to_bv 64 0x1aa4dc)] ->
  rw_cells bsegs m (sp + -2128) [CB 2080 junk] ->
  rw_cells bsegs m (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem),
                 (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 0xbdae50) t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs))
                 /\ munch [(sp + -2144, sp); (0xbdadac, 0xbdadb0)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ rw_cells bsegs m' 0xbdadac [C4 (Z_to_bv 64 e)]
                 /\ stk bsegs m' lo sp)
    (MS (mkR (Z_to_bv 64 0x56a3c0) (Z_to_bv 64 (sp + -2144)) gp (Z_to_bv 64 0xbdae50) t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 g_read_stage)
             (Z_to_bv 64 (- e)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x564154) fc None m (seg_rom bsegs)).
Proof.
  intros until errv. intros ST LO0 LO UT Hfd Hcnt He ERR FRr FRb FRt MI.
  unfold g_read_stage. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp + -2144, sp); (0xbdadac, 0xbdadb0)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EE : bv_unsigned (Z_to_bv 64 (- e)) = 2^64 - e) by (rewrite unsigned_lit_wrap; Z.div_mod_to_equations; lia).
  zhide.
  do 4 step.
  do 3 step.
  assert (C1 : bv_ltu (Z_to_bv 64 (- e)) (Z_to_bv 64 (-4095)) = false).
  { unfold bv_ltu. rewrite EE, (unsigned_lit_wrap (-4095)). change ((-4095) mod 2^64) with 18446744073709547521. apply Z.ltb_ge. lia. }
  rewrite C1; cbv iota.
  release_frame FRr ST (sp + -2128).
  carve_frame 16%nat ST. rename FR into FRs.
  step. step. change (Z_to_le_bytes 8 1746140) with (le8 (Z_to_bv 64 1746140)). mem_after_store.
  step.
  step. rewrite EE.
  assert (ES : bv_swrap 32 (2^64 - e + 0) = - e).
  { rewrite Z.add_0_r. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
    replace (2^64 - e + 2^31) with ((2^31 - e) + 2^32 * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  do 4 step.
  do 6 step.
  release_frame FRs ST (sp + -2128).
  step. if_false.
  step. if_true.
  release_frame FRb ST (sp + -48).
  do 9 step.
  release_frame FRt ST sp.
  apply evt_done. eexists. split.
  { do 14 eexists. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  rewrite negw_errno in ERR by lia. replace (2^64 - (2^64 - e)) with e in ERR by lia.
  split; [exact ERR| exact ST].
Qed.
