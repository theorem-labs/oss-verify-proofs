(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
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
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition rel_entry : Z := 0x1e1114.
Definition flush_entry : Z := 0x1c3d9c.
Definition g_got_pagesize_cached : Z := 0x5a9218.     (* [comment removed for export] *)
Definition g_got_sealed : Z := 0x5a9278.             (* [comment removed for export] *)
Definition g_PageSizeCached : Z := 0x701ae0.

(* [comment removed for export] *)
Definition rel_cells (m : mem) : Prop :=
  rw_cells ctasegs m g_got_pagesize_cached [C8 (Z_to_bv 64 g_PageSizeCached)]
  /\ rw_cells ctasegs m g_got_sealed [C8 (Z_to_bv 64 1)]
  /\ rw_cells ctasegs m g_PageSizeCached [C8 (Z_to_bv 64 4096)].

Definition pbeg (SA : Z) : Z := ((SA + 4095) / 4096 * 4096)%Z.
Definition pend (SE : Z) : Z := (SE / 4096 * 4096)%Z.

Lemma pbeg_facts : forall x, (0 <= x)%Z -> (x <= pbeg x < x + 4096 /\ pbeg x mod 4096 = 0)%Z.
Proof.
  intros x Hx. unfold pbeg. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)).
  split; [lia | apply Z.mod_mul; lia].
Qed.

Lemma pend_facts : forall x, (0 <= x)%Z -> (x - 4096 < pend x <= x /\ pend x mod 4096 = 0)%Z.
Proof.
  intros x Hx. unfold pend. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  split; [lia | apply Z.mod_mul; lia].
Qed.

(* [comment removed for export] *)
Lemma land_pg : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x / 4096 * 4096)%Z.
Proof.
  intros x Hx. change 18446744073709547520%Z with (Z.land (Z.lnot (Z.ones 12)) (Z.ones 64)).
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia. rewrite Z.mod_small by lia.
  rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition madv_ecall : Z := 0x1d6868.

Definition madv_regs (ra sp gp tp t0 t1 t2 s0 s1 : word) (PB PE : Z) (a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    : bvmap 5 word :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PB) (Z_to_bv 64 (PE - PB)) (Z_to_bv 64 4) (Z_to_bv 64 4) a4 a5 a6
      (Z_to_bv 64 233) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition relA_post (K : mem -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (PB PE lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (madv_regs ra sp gp tp t0' t1' t2' s0 s1 PB PE a4' a5' a6' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ K m'.

(* [comment removed for export] *)
Lemma rel_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B E lo : Z),
  rel_cells m -> (0 <= B < 2^62)%Z -> (0 <= E < 2^62)%Z -> (pbeg B < pend E)%Z ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (relA_post rel_cells ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (pbeg B) (pend E) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 E) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rel_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros (G1 & G2 & G3) HB HE HPE ST HLO HLOH MI.
  pose proof (pbeg_facts B ltac:(lia)) as (PB1 & PB2). pose proof (pend_facts E ltac:(lia)) as (PE1 & PE2).
  unfold kHighShadowEnd, rel_entry, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 32%nat ST.
  zidle_begin sp 32%Z MUz WMz.
  do 4 zstep.
  zidle_end MUz WMz.
  do 7 zstep. ifT.
  do 3 zstep. ifF.
  do 6 zstep.
  rewrite !land_pg by lia.
  change ((B + 4095) / 4096 * 4096)%Z with (pbeg B). change (E / 4096 * 4096)%Z with (pend E).
  ifF.
  do 8 zstep.
  try (replace (bv_unsigned sp + -32 + 32)%Z with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  do 3 zstep. ifF.
  do 2 zstep. ifT.
  zstep.
  step_ecall.
  unfold relA_post, madv_regs. do 11 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma flush_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P SZ lo : Z),
  m2s_cells m -> rel_cells m ->
  addr_in_mem P -> addr_in_mem (P + SZ) -> (0 <= SZ)%Z ->
  (pbeg (shad P) < pend (shad (P + SZ)))%Z ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (relA_post (fun m' => m2s_cells m' /\ rel_cells m') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (pbeg (shad P)) (pend (shad (P + SZ))) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 flush_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros M2S REL HP1 HP2 HSZ HPE ST HLO HLOH MI.
  pose proof M2S as (M1 & M2 & M3). pose proof REL as (G1 & G2 & G3).
  assert (HPr : (0 <= P < 2^47 /\ 0 <= P + SZ < 2^47)%Z)
    by (unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP1, HP2; lia).
  assert (SHr : (0 <= shad P < 2^62 /\ 0 <= shad (P + SZ) < 2^62)%Z).
  { unfold shad, SHB. pose proof (Z.div_pos P 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (P + SZ) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound P 8 (2^47) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (P + SZ) 8 (2^47) ltac:(lia) ltac:(lia)). lia. }
  unfold kHighShadowEnd, flush_entry, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  clear M2S REL.
  carve_frame 32%nat ST.
  zidle_begin_rw sp 32%Z MUz WMz.
  do 4 zstep.
  do 4 zstep.
  zidle_end MUz WMz.
  call (m2s_53700_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ P).
  1:{ reflexivity. }
  1:{ exact HP1. }
  1:{ split; [exact M1|split; [exact M2|exact M3]]. }
  1:{ assumption. }
  do 3 zstep.
  call (m2s_53700_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (P + SZ)%Z).
  1:{ f_equal. lia. }
  1:{ exact HP2. }
  1:{ split; [exact M1|split; [exact M2|exact M3]]. }
  1:{ assumption. }
  do 8 zstep.
  try (replace (bv_unsigned sp + -32 + 32)%Z with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
  release_frame FR ST (bv_unsigned sp).
  call (rel_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (shad P) (shad (P + SZ)) lo).
  1:{ split; [exact G1|split; [exact G2|exact G3]]. }
  all: try eassumption.
  all: try lia.
  apply evt_done. unfold relA_post in *. do 11 eexists.
  split; [reflexivity|].
  repeat (split; [eassumption|]).
  split; [unfold m2s_cells; repeat (split; [assumption|]); assumption | assumption].
Qed.
