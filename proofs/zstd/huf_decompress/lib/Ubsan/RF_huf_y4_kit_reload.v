From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition PHUF_RELOAD : Z := 0x1a794.

Definition y4_bd (c bc p S : Z) (pad : list byte) : list cell :=
  [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 bc); CB 4 pad; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].

Definition y4_reload_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (BD S bc p : Z) (pad : list byte) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) (m' : fmem) (c' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ 0 <= c' < 2^64 /\ rw_cells usegs m' BD (y4_bd c' (bc mod 8) (p - bc / 8) S pad).

Definition y4_reload_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (BD S n c bc p : Z) (pad sqb : list byte),
  mem_inv usegs m -> rw_cells usegs m BD (y4_bd c bc p S pad) -> BD mod 8 = 0 ->
  bytes_at usegs m S sqb -> zlen sqb = n ->
  0 < BD -> BD + 40 <= 2^47 -> 0 < S -> S + n <= 2^47 -> (BD + 40 <= S \/ S + n <= BD) ->
  0 <= bc <= 64 -> S + 8 <= p -> p <= S + n - 8 ->
  evt usegs (y4_reload_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BD S bc p pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_RELOAD) fc None m (seg_rom usegs)).

Ltac stepw stop := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a834) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      try (match goal with E1 : bv_unsigned (zx32 _) = _, E2 : Z.shiftr _ 3 = _, E3 : _ mod 2 ^ 3 = _ |- _ =>
             rewrite ?E1, ?E2, ?E3 end); zstep end).
Ltac land7 := repeat match goal with H : context [Z.land ?x 7] |- _ =>
  change 7 with (Z.ones 3) in H; rewrite Z.land_ones in H by lia end.
Ltac nrm U :=
  try (unfold zx32 in U);
  repeat (rewrite unsigned_lit in U by lia);
  repeat match type of U with context [(8 * ?q + ?r) mod 2 ^ 32] =>
    rewrite (Z.mod_small (8 * q + r) (2 ^ 32)) in U by lia end;
  repeat (rewrite Z.shiftr_div_pow2 in U by lia);
  try (change (2 ^ 3) with 8 in U);
  repeat match type of U with context [(8 * ?q + ?r) / 8] =>
    replace ((8 * q + r) / 8) with q in U by (first [apply Z.div_unique with r | symmetry; apply Z.div_unique with r]; lia) end;
  repeat match type of U with context [Z.b2z (?a <? ?b)] =>
    let E := fresh "E" in revert U; destruct (Z.ltb_spec a b) as [E|E]; intro U end;
  repeat match goal with E : Z.lxor ?a ?b < 1 |- _ =>
    assert (a = b) by (apply Z.lxor_eq; assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia); lia); clear E end;
  repeat match type of U with context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b;
    let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in U end;
  try (cbv [Z.b2z] in U);
  repeat match type of U with context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b;
    let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in U end.
Ltac brk := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
  let U := fresh "U" in if_cases U; zify_cond U; land7; try (exfalso; lia); nrm U end.

Lemma y4_zx : forall q r, 0 <= q <= 8 -> 0 <= r <= 7 -> bv_unsigned (zx32 (Z_to_bv 64 (8 * q + r))) = 8 * q + r.
Proof.
  intros q r Q R. unfold zx32. rewrite (unsigned_lit (8 * q + r)) by lia.
  rewrite (Z.mod_small (8 * q + r)) by lia. apply unsigned_lit; lia.
Qed.

Lemma y4_sh : forall q r, 0 <= q -> 0 <= r <= 7 -> Z.shiftr (8 * q + r) 3 = q.
Proof.
  intros q r Q R. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  symmetry. apply (Z.div_unique (8 * q + r) 8 q r); lia.
Qed.

Lemma y4_md : forall q r, 0 <= q -> 0 <= r <= 7 -> (8 * q + r) mod 2 ^ 3 = r.
Proof.
  intros q r Q R. change (2 ^ 3) with 8. symmetry. apply (Z.mod_unique (8 * q + r) 8 q r); lia.
Qed.

Lemma y4_rd1 : forall m S sqb k, bytes_at usegs m S sqb -> 0 <= k < zlen sqb ->
  exists b, ov_read_bytes usegs m (wa (S + k)) 1 = Some [b].
Proof.
  intros m S sqb k H K.
  pose proof (bytes_at_ov_read usegs m S sqb (Z.to_nat k) 1 H ltac:(lia)) as R.
  rewrite Z2Nat.id in R by lia.
  destruct (skipn (Z.to_nat k) sqb) as [|b l] eqn:E.
  - exfalso. apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn in E. lia.
  - exists b. rewrite R. reflexivity.
Qed.

Theorem y4_reload_proof : y4_reload_stmt.
Proof.
  unfold y4_reload_stmt, PHUF_RELOAD.
  intros until sqb. intros MI HBD BDA SQB SL R1 R2 R3 R4 DJ RB RP1 RP2.
  unfold y4_bd in HBD.
  pose proof (munch_refl [(BD, BD + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  stepw 0.
  assert (QR : exists q r d, bc = 8 * q + r /\ p = S + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
    by (exists (bc / 8), (bc mod 8), (p - S); lia).
  destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
  pose proof (y4_zx q r ltac:(lia) ltac:(lia)) as EZX.
  pose proof (y4_sh q r ltac:(lia) ltac:(lia)) as ESH.
  pose proof (y4_md q r ltac:(lia) ltac:(lia)) as EMD.
  repeat (stepw 0x1a7d4; brk; try (exfalso; lia)).
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a7d4) _ _ ?mg _) =>
    destruct (y4_rd1 mg S sqb (d - q + 0) SQB ltac:(lia)) as (b0 & B0);
    destruct (y4_rd1 mg S sqb (d - q + 1) SQB ltac:(lia)) as (b1 & B1);
    destruct (y4_rd1 mg S sqb (d - q + 2) SQB ltac:(lia)) as (b2 & B2);
    destruct (y4_rd1 mg S sqb (d - q + 3) SQB ltac:(lia)) as (b3 & B3);
    destruct (y4_rd1 mg S sqb (d - q + 4) SQB ltac:(lia)) as (b4 & B4);
    destruct (y4_rd1 mg S sqb (d - q + 5) SQB ltac:(lia)) as (b5 & B5);
    destruct (y4_rd1 mg S sqb (d - q + 6) SQB ltac:(lia)) as (b6 & B6);
    destruct (y4_rd1 mg S sqb (d - q + 7) SQB ltac:(lia)) as (b7 & B7)
  | |- _ => idtac end.
  all: repeat (stepw 0; brk; try (exfalso; lia)).
  all: stepw 0.
  all: apply evt_done; unfold y4_reload_post, y4_bd.
  all: repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: replace ((8 * q + r) / 8) with q by (apply (Z.div_unique (8 * q + r) 8 q r); lia).
  all: replace ((8 * q + r) mod 8) with r by (apply (Z.mod_unique (8 * q + r) 8 q r); lia).
  all: rewrite EMD in *.
  all: lazymatch goal with H : rw_cells usegs _ _ (C8 (Z_to_bv 64 ?cc) :: _) |- _ =>
    rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 cc)) in H;
    pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 cc)) as RG; unfold bv_modulus in RG; cbn in RG;
    split; [ | exact H ]; lia end.
Qed.
