(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

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

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Lemma open_walkA : forall (sp path : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z) (g : word),
  stk bsegs m lo sp -> SEGTOP_A <= lo -> lo + 128 <= sp -> sp < 2^64 ->
  ro_cells bsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] -> ro_cells bsegs m SSP_GUARD [C8 g] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : word -> option byte) junk,
      ms' = MSsvc (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD)
                       (Z_to_bv 64 (-100)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16185c) (Z_to_bv 64 56) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 96, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (sp + -96) [CB 16 junk; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
      /\ stk bsegs m' lo (sp + -96))
    (entry_st ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_open m).
Proof.
  intros until g. intros ST LO0 LO UT G1 G2 MI.
  unfold entry_st, e_open. pose proof ST as (STa & STb & _). unfold GOT_SSP, SSP_GUARD in G1, G2. unfold SEGTOP_A in LO0.
  pose proof (munch_refl [(sp - 96, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 96%nat ST.
  zhide.
  do 17 step.
  step. if_false.
  do 3 step. if_false.
  do 10 step.
  do 8 step.
  step_ecall.
  do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact FR| exact ST].
Qed.

Lemma open_walkB_ok : forall (sp path fd : Z) (ra gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z) (g : word) junk,
  stk bsegs m lo (sp + -96) -> SEGTOP_A <= lo -> lo + 128 <= sp -> sp < 2^64 -> 0 <= fd < 2^31 ->
  rw_cells bsegs m (sp + -96) [CB 16 junk; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  ro_cells bsegs m SSP_GUARD [C8 g] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F',
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 fd) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc None m (seg_rom bsegs))
                 /\ stk bsegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD)
             (Z_to_bv 64 fd) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161860) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST LO0 LO UT Hfd FR G2 MI.
  pose proof ST as (STa & STb & _). unfold SSP_GUARD in *. unfold SEGTOP_A in LO0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (sp + -96)) = sp + -96) by (rewrite unsigned_lit by lia; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 fd) = fd) by (apply unsigned_lit; lia).
  assert (ES : bv_swrap 32 (bv_unsigned (Z_to_bv 64 fd) + 0) = fd).
  { rewrite EF, Z.add_0_r. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. }
  zhide.
  step. step. step. step. if_true.
  do 5 step. rewrite ES. if_true.
  do 3 step. step. if_false.
  do 6 step.
  release_frame FR ST sp.
  apply evt_done. split; [| replace (sp + -96 + 96) with sp in ST by lia; exact ST].
  rewrite ES. do 15 eexists. reflexivity.
Qed.

Lemma open_walkB_err : forall (sp path e : Z) (ra gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z) (g errv : word) junk,
  stk bsegs m lo (sp + -96) -> SEGTOP_A <= lo -> lo + 128 <= sp -> sp < 2^64 -> 1 <= e <= 4095 ->
  rw_cells bsegs m (sp + -96) [CB 16 junk; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  ro_cells bsegs m SSP_GUARD [C8 g] -> rw_cells bsegs m (bv_unsigned tp + -164) [C4 errv] ->
  164 <= bv_unsigned tp -> bv_unsigned tp + -164 + 4 <= 0x6cb3a8 ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
                 (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F',
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc None m' (seg_rom bsegs))
                 /\ munch [(sp + -112, sp + -96); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
                 /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ rw_cells bsegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 e)]
                 /\ stk bsegs m' lo sp)
    (MS (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD)
             (Z_to_bv 64 (- e)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161860) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST LO0 LO UT He FR G2 ERR TP TPB MI.
  pose proof ST as (STa & STb & _). unfold SSP_GUARD in *. unfold SEGTOP_A in LO0.
  pose proof (munch_refl [(sp + -112, sp + -96); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (sp + -96)) = sp + -96) by (apply unsigned_lit; lia).
  assert (EE : bv_unsigned (Z_to_bv 64 (- e)) = 2^64 - e) by (rewrite unsigned_lit_wrap; Z.div_mod_to_equations; lia).
  assert (ES : bv_swrap 32 (2^64 - e + 0) = - e).
  { rewrite Z.add_0_r. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
    replace (2^64 - e + 2^31) with ((2^31 - e) + 2^32 * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  zhide.
  step. step. step. step. if_true.
  step. rewrite EE, ES.
  assert (EE' : bv_unsigned (Z_to_bv 64 (- e)) = 2^64 - e) by exact EE.
  do 4 step. if_false.
  carve_frame 16%nat ST.
  step. step. change (Z_to_le_bytes 8 1375020) with (le8 (Z_to_bv 64 1375020)). mem_after_store.
  step. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
  do 6 step.
  do 5 step.
  release_frame FR0 ST (sp + -96).
  do 3 step. if_false.
  do 6 step.
  release_frame FR ST sp.
  apply evt_done. eexists. split.
  { do 15 eexists. reflexivity. }
  split; [intros x Hx; apply MU; cbn [outside] in *; intuition lia|]. split; [exact WM|]. split; [exact MI|].
  rewrite EE, negw_errno in ERR by lia. replace (2^64 - (2^64 - e)) with e in ERR by lia.
  split; [exact ERR| exact ST].
Qed.
