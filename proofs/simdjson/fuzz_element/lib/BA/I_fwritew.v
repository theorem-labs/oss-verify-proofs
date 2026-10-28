(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_readw2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.

Lemma fwrite_walkA : forall (sp sa len errp : Z) (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 ->
  0 <= sa < 2^64 -> 0 <= len < 2^64 -> 0 <= errp < 2^64 ->
  rw_cells asegs m 0x16c0a0 [C8 (Z_to_bv 64 0x153924)] -> rw_cells asegs m 0x174918 [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) junk,
      ms' = MS (mkR (Z_to_bv 64 0x6ee9c) (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 len)
                    (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1) (Z_to_bv 64 errp) (Z_to_bv 64 0x153924) a5 a6 a7
                    (Z_to_bv 64 sa) (Z_to_bv 64 errp) (Z_to_bv 64 1) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x153924) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2144, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -2128) [CB 2072 junk]
      /\ rw_cells asegs m' (sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs m' lo (sp + -2128))
    (entry_st ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1) (Z_to_bv 64 errp)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m).
Proof.
  intros until lo. intros ST LO0 LO UT Hsa Hlen Herr RF AI MI.
  unfold entry_st, e_fwrite. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp - 2144, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 56%nat ST. rename FR into FRt.
  carve_frame 2072%nat ST. rename FR into FRb.
  zhide.
  do 16 step.
  carve_frame 16%nat ST. rename FR into FRa.
  step. step. change (Z_to_le_bytes 8 454268) with (le8 (Z_to_bv 64 454268)). mem_after_store.
  step.
  do 6 step. if_false.
  do 4 step.
  release_frame FRa ST (sp + -2128).
  do 8 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact FRb|]. split; [exact FRt| exact ST].
Qed.

Lemma qcw_lit1 : forall len, 1 <= len <= 64 ->
  Z.land (bv_unsigned (Z_to_bv 64 (2147450880 + bv_unsigned (Z_to_bv 64 (138566 + len + -1)) ≫ 3))) 18446744073709551608
  = if len <=? 58 then 2147468200 else 2147468208.
Proof.
  intros len Hl. rewrite (unsigned_lit (138566 + len + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  rewrite unsigned_lit by (split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]| Z.div_mod_to_equations; lia]).
  rewrite I_readw2.land_m8 by (split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]| Z.div_mod_to_equations; lia]).
  destruct (Z.leb_spec len 58); Z.div_mod_to_equations; lia.
Qed.

Lemma qcw_lit2 : forall len, 1 <= len <= 64 ->
  Z.land (bv_unsigned (Z_to_bv 64 (2147450880 + bv_unsigned (Z_to_bv 64 (91041 + len + -1)) ≫ 3))) 18446744073709551608
  = if len <=? 31 then 2147462256 else 2147462264.
Proof.
  intros len Hl. rewrite (unsigned_lit (91041 + len + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  rewrite unsigned_lit by (split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]| Z.div_mod_to_equations; lia]).
  rewrite I_readw2.land_m8 by (split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]| Z.div_mod_to_equations; lia]).
  destruct (Z.leb_spec len 31); Z.div_mod_to_equations; lia.
Qed.

Lemma fwrite_walkB : forall (sp sa len errp : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) junk,
  stk asegs m lo (sp + -2128) -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 ->
  (sa = 0x21d46 \/ sa = 0x163a1) -> 1 <= len <= 64 -> 0 <= errp < 2^64 ->
  m2s_cells m ->
  ro_cells asegs m 0x7fffac70 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x7fffc3a8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (sp + -2128) [CB 2072 junk] ->
  rw_cells asegs m (sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x6ee9c) (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 len)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 sa) (Z_to_bv 64 errp) (Z_to_bv 64 1) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6ee9c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST LO0 LO UT Hsa Hlen Herr (GOT & SHC & HM) W2 W1 FRb FRt MI.
  unfold SHB in *. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUl : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  destruct Hsa as [-> | ->].
  - step. if_false.
    zhide.
    step. if_false.
    do 5 step. rewrite EUl, Z.mul_1_l. if_false.
    do 3 step.
    assert (C2 : bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (len + -65)) = true)
      by (unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
    rewrite C2; cbv iota beta delta [negb].
    do 12 step.
    rewrite (qcw_lit1 len Hlen).
    destruct (Z.leb_spec len 58) as [H9|H9].
    + step. step. step. if_false.
      release_frame FRb ST (sp + -56).
      do 10 step.
      release_frame FRt ST sp.
      apply evt_done. split; [| exact ST]. do 14 eexists. reflexivity.
    + step. step. step. if_false.
      release_frame FRb ST (sp + -56).
      do 10 step.
      release_frame FRt ST sp.
      apply evt_done. split; [| exact ST]. do 14 eexists. reflexivity.
  - step. if_false.
    step. if_false.
    do 5 step. rewrite EUl, Z.mul_1_l. if_false.
    do 3 step.
    assert (C2 : bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (len + -65)) = true)
      by (unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
    rewrite C2; cbv iota beta delta [negb].
    do 12 step.
    rewrite (qcw_lit2 len Hlen).
    destruct (Z.leb_spec len 31) as [H1|H1].
    + step. step. step. if_false.
      release_frame FRb ST (sp + -56).
      do 10 step.
      release_frame FRt ST sp.
      apply evt_done. split; [| exact ST]. do 14 eexists. reflexivity.
    + step. step. step. if_false.
      release_frame FRb ST (sp + -56).
      do 10 step.
      release_frame FRt ST sp.
      apply evt_done. split; [| exact ST]. do 14 eexists. reflexivity.
Qed.
