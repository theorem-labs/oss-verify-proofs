(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_cache_defs.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition refill_entry : Z := 0x19fc1c.
Definition refill_retB : Z := 0x19fc5c.
Definition gfa_entry : Z := 0x19fd1c.

(* [comment removed for export] *)
Definition refill_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T c P n lo : Z) (W : list (Z * Z)) (m : mem) (K : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 refill_retB) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 n)
                  (Z_to_bv 64 INST) (Z_to_bv 64 (cstats T)) (Z_to_bv 64 c) (Z_to_bv 64 (P + 16)) (Z_to_bv 64 n) a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 gfa_entry) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp - 32)
    /\ K m'.

Lemma refill_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T c cnt mc cs lo : Z),
  (1 <= c <= 31)%Z ->
  pc_cells m (pc_addr T c) cnt mc cs -> (0 <= cnt < 2^31)%Z -> (1 <= mc < 2^31)%Z -> (0 <= cs < 2^63)%Z ->
  T_ok ACEIL T ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (refill_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T c (pc_addr T c) (mc / 2) lo
               [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m (fun m' => pc_cells m' (pc_addr T c) cnt mc cs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (pc_addr T c)) (Z_to_bv 64 INST) (Z_to_bv 64 c)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hc PC Hcnt Hmc Hcs HT ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cacheT, cstats, INST, refill_entry, g_instance in *.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  zhide.
  do 7 zstep. rewrite (sx32_small_A mc) by lia. zstep. ifF.
  do 8 zstep. rewrite (srliw1_small mc) by lia.
  finish; unfold pc_cells; try rewrite <- EP; try eassumption.
Qed.

(* [comment removed for export] *)
Definition refill_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P n mc cs lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(P, P + 4); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pc_cells m' P n mc cs
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma refill_B_spec : forall ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o : word) (junk : list byte) (ACEIL T c P n cnt mc cs lo : Z),
  (1 <= c <= 31)%Z -> P = pc_addr T c ->
  pc_cells m P cnt mc cs -> (0 <= cnt < 2^31)%Z -> (0 <= n < 2^31)%Z -> (0 <= mc < 2^31)%Z -> (0 <= cs < 2^63)%Z ->
  T_ok ACEIL T ->
  rw_cells asegs m (bv_unsigned sp - 32) [CB 8 junk; C8 s1o; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 32) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (refill_B_post ra sp gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n mc cs lo m)
    (MS (mkR (Z_to_bv 64 refill_retB) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 n)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 refill_retB) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hc EP PC Hcnt Hn Hmc Hcs HT FR ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, refill_retB in *.
  pose proof (munch_refl [(P, P + 4); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zhide.
  zstep. ifF.
  do 6 zstep.
  replace (bv_unsigned sp - 32 + 32)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
