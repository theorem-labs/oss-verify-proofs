(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim ATacA ACells APrimLem APrimPop.
Import ListNotations.
Open Scope Z_scope.

Lemma lxor_ones64' : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  assert (E : 18446744073709551615 - x = (Z.lnot x) mod 2^64).
  { unfold Z.lnot. replace (Z.pred (- x)) with ((18446744073709551615 - x) + (-1) * 2^64) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [LT|GE].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia. apply Bool.xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    assert (B1 : Z.testbit x i = false). { destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia]. }
    assert (B2 : Z.testbit 18446744073709551615 i = false). { apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite B1, B2. reflexivity.
Qed.

Lemma fill_addr : forall A t i, 0 <= i < 2^60 -> 0 <= t - 1 - i -> 0 <= A -> A + 4 * t < 2^63 ->
  Z_to_bv 64 (A + 4 * t + Z.shiftl (Z.lxor i 18446744073709551615) 2) = Z_to_bv 64 (A + 4 * (t - 1 - i)).
Proof.
  intros A t i Hi Ht HA HB. rewrite lxor_ones64' by lia. rewrite Z.shiftl_mul_pow2 by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  replace (A + 4 * t + (18446744073709551615 - i) * 2 ^ 2) with ((A + 4 * (t - 1 - i)) + 4 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma upd_at_length : forall {X} (l1 l2 : list X) (x v : X), upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. intros X l1. induction l1 as [|y l1 IH]; intros l2 x v; [reflexivity|]. cbn. f_equal. apply IH. Qed.

Lemma firstn_S_nth : forall {X} (l : list X) n (d : X), (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros X l. induction l as [|y l IH]; intros n d Hn; cbn in Hn; [lia|]. destruct n; [reflexivity|].
  cbn. f_equal. apply IH. lia.
Qed.

Section FILL.
  Context {HC : HasCeiling}.
  Variables (AL : alayout).
  Hypothesis AO : alayout_ok AL.
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q c au total cnt : Z) (ws0 : list word) (ms : mem).
  Notation FA := (fa_base AL c).
  Notation SZ := (class_size c).

  Definition cval (j : nat) : Z := (au + Z.of_nat j * SZ) / 16.

  Definition LF (i : nat) : list word :=
    firstn (Z.to_nat total - i) ws0 ++ map wz (rev (map cval (seq 0 i))) ++ skipn (Z.to_nat total) ws0.

  #[using="Type"] Lemma LF_length : forall i, (i <= Z.to_nat total)%nat -> (Z.to_nat total <= length ws0)%nat -> length (LF i) = length ws0.
  Proof. intros i Hi Ht. unfold LF. rewrite !length_app, length_firstn, length_map, length_rev, length_map, length_seq, length_skipn. lia. Qed.

  #[using="Type"] Lemma LF_step : forall i, (i < Z.to_nat total)%nat -> (Z.to_nat total <= length ws0)%nat ->
    upd (LF i) (Z.to_nat (total - 1 - Z.of_nat i)) (wz (cval i)) = LF (S i).
  Proof.
    intros i Hi Ht. unfold LF.
    replace (Z.to_nat total - i)%nat with (S (Z.to_nat total - S i)) by lia.
    rewrite (firstn_S_nth ws0 (Z.to_nat total - S i) (wz 0)) by lia. rewrite <- app_assoc. cbn [app].
    replace (Z.to_nat (total - 1 - Z.of_nat i)) with (length (firstn (Z.to_nat total - S i) ws0)) by (rewrite length_firstn; lia).
    rewrite upd_at_length. f_equal. rewrite seq_S, map_app, rev_app_distr. cbn [map rev app]. reflexivity.
  Qed.

  #[using="Type"] Lemma LF_0 : LF 0%nat = ws0.
  Proof. unfold LF. cbn [seq map rev]. rewrite Nat.sub_0_r. cbn [app]. apply firstn_skipn. Qed.

  #[using="Type"] Lemma LF_firstn : forall (nf n : nat), (nf + n = Z.to_nat total)%nat -> (Z.to_nat total <= length ws0)%nat ->
    firstn (nf + n) (LF n) = firstn nf ws0 ++ map wz (carve au SZ n).
  Proof.
    intros nf n Hn Ht. unfold LF. replace (Z.to_nat total - n)%nat with nf by lia.
    assert (LA : length (firstn nf ws0) = nf) by (rewrite length_firstn; lia).
    assert (LB : length (map wz (rev (map cval (seq 0 n)))) = n) by (rewrite length_map, length_rev, length_map, length_seq; lia).
    rewrite <- LA at 1. rewrite firstn_app_2. f_equal.
    rewrite <- (Nat.add_0_r n) at 1. rewrite <- LB at 1. rewrite firstn_app_2. cbn [firstn]. rewrite app_nil_r.
    unfold carve, cval. reflexivity.
  Qed.

  #[using="HC AO"] Lemma pop_fill : forall (K : nat) (i : Z) (mm : mem) (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ch a1v : Z),
    Z.to_nat (cnt - i) = K -> 0 <= i < cnt -> cnt <= total -> (Z.to_nat total <= length ws0)%nat -> 4 * Z.of_nat (length ws0) <= K_FA_SIZE ->
    1 <= c <= 31 -> 0 <= au -> au + cnt * SZ <= FA_OFF -> ch = au + i * SZ -> a1v = FA + 4 * total ->
    u32arr asegs mm FA (LF (Z.to_nat i)) ->
    munch [(FA + 4 * (total - cnt), FA + 4 * total)] ms mm -> wmono asegs ms mm -> mem_inv asegs mm ->
    evt asegs (fun ms' => exists x14' x15' m', ms' =
          MS (mkR x1 (wz (q - 64)) gp tp x5 x6 x7 x8 x9 (wz cnt) (wz a1v) (wz (au + cnt * SZ)) (wz au) x14' x15' x16 x17
                  s2 (wz cnt) s4 (wz SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz 0x38a2c) fc None m' (seg_rom asegs)
          /\ munch [(FA + 4 * (total - cnt), FA + 4 * total)] ms m' /\ wmono asegs ms m' /\ mem_inv asegs m'
          /\ u32arr asegs m' FA (LF (Z.to_nat cnt)))
      (MS (mkR x1 (wz (q - 64)) gp tp x5 x6 x7 x8 x9 (wz i) (wz a1v) (wz ch) (wz au) x14 x15 x16 x17
               s2 (wz cnt) s4 (wz SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz 0x38a0c) fc None mm (seg_rom asegs)).
  Proof.
    induction K as [|K IH]; intros i mm x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ch a1v HK Hi CT TL WSB Hc AU0 AUB -> -> FAA MU WM MI; [lia|].
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    pose proof (region_range AL c Hc) as RR. pose proof (class_size_pos c Hc) as CS.
    assert (Hfa : FA = region AL c + FA_OFF) by reflexivity.
    pose proof (u32arr_bound asegs _ _ _ FAA) as B1. rewrite LF_length in B1 by lia.
    assert (ISZ : 0 <= i * SZ /\ i * SZ + SZ <= cnt * SZ).
    { split; [apply Z.mul_nonneg_nonneg; lia|]. replace (i * SZ + SZ) with ((i + 1) * SZ) by lia. apply Z.mul_le_mono_nonneg_r; lia. }
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa.
    zstep.
    replace (Z.shiftr (au + i * SZ) 4) with (cval (Z.to_nat i))
      by (unfold cval; rewrite Z2Nat.id, Z.shiftr_div_pow2 by lia; reflexivity).
    zstep.
    zstep.
    zstep.
    zstep.
    rewrite (fill_addr faa total i) by lia.
    pose proof (u32arr_store_ok asegs mm faa _ (total - 1 - i) (wa (faa + 4 * (total - 1 - i))) FAA ltac:(rewrite LF_length; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u32arr_write asegs mx faa _ (total - 1 - i) (wz (cval (Z.to_nat i))) FAA ltac:(rewrite LF_length; lia)) as FAA2 end.
    replace (total - 1 - i) with (total - 1 - Z.of_nat (Z.to_nat i)) in FAA2 at 2 by lia.
    rewrite LF_step in FAA2 by lia.
    clear FAA. store_done. rename FAA2 into FAA.
    zstep.
    zstep. if_cases KB; zify_cond KB.
    - replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in FAA by lia.
      eapply (IH (i + 1)); try eassumption; try lia.
    - apply evt_done. replace (i + 1) with cnt by lia. replace (S (Z.to_nat i)) with (Z.to_nat cnt) in FAA by lia.
      replace (au + i * SZ + SZ) with (au + cnt * SZ) by lia.
      eexists _, _, _. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End FILL.
