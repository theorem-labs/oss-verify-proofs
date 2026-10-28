(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac RegsEquiv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memset F_memcpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xs_full El_xs_core El_xs_sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Notation GETCTX_FSD := 0xbf1b0%Z (only parsing).
Notation JUMPTO_FLD := 0xbf030%Z (only parsing).
Notation MEMSET := 0xd0c68%Z (only parsing).
Notation MEMCPY := 0xd06e8%Z (only parsing).

Definition fpcells (F : bvmap 5 word) : list cell :=
  map (fun i => C8 (reg_get F (Z_to_bv 5 (Z.of_nat i)))) (seq 0 32).

Section FPBLK.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Notation R := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Notation A := (bv_unsigned a0).

  Lemma getctx_fsd_walk : forall junk,
    rw_cells usegs m (A + 256) [CB 256 junk] -> mem_inv usegs m -> (A + 512 <= 2 ^ 64)%Z ->
    evt usegs (fun ms' => exists m',
        ms' = MS R F (Z_to_bv 64 (GETCTX_FSD + 128)) fc None m' (seg_rom usegs)
        /\ munch [(A + 256, A + 512)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' (A + 256) (fpcells F))
      (MS R F (Z_to_bv 64 GETCTX_FSD) fc None m (seg_rom usegs)).
  Proof.
    intros junk DST MI HB.
    pose proof (munch_refl [(A + 256, A + 512)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 32 zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact DST.
  Qed.

  Lemma jumpto_fld_walk :
    ro_cells usegs m (A + 256) (fpcells F) -> (A + 512 <= 2 ^ 64)%Z ->
    evt usegs (fun ms' => exists F',
        ms' = MS R F' (Z_to_bv 64 (JUMPTO_FLD + 128)) fc None m (seg_rom usegs)
        /\ (forall r : reg, reg_get F' r = reg_get F r))
      (MS R F (Z_to_bv 64 JUMPTO_FLD) fc None m (seg_rom usegs)).
  Proof.
    intros SRC HB. unfold fpcells in SRC. cbn [map seq Z.of_nat Pos.of_succ_nat Pos.succ] in SRC.
    do 32 zstep.
    apply evt_done. eexists. split; [reflexivity|].
    intros r. rewrite !RegsEquiv.reg_get_set. reg_cases r; reflexivity.
  Qed.
End FPBLK.

Lemma set_contract_P : set_contract usegs MEMSET.
Proof.
  unfold set_contract. intros. eapply evt_mono; [eapply (memset_spec ra sp gp tp); eassumption|]. intros ms' P. exact P.
Qed.

Lemma cpy_contract_P : cpy_contract usegs MEMCPY.
Proof.
  unfold cpy_contract. intros. eapply evt_mono; [eapply (memcpy_spec ra sp gp tp); eassumption|]. intros ms' P. exact P.
Qed.

Lemma cb8_first : forall (g : nat -> word) n k, (0 < n)%nat ->
  firstn 8 (cells_bytes (map (fun j => C8 (g j)) (seq k n))) = le8 (g k).
Proof.
  intros g n k Hn. destruct n as [|n]; [lia|]. cbn [seq map cells_bytes cbytes].
  rewrite firstn_app. rewrite Mem.length_le8. replace (8 - 8)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  apply firstn_all2. rewrite Mem.length_le8. lia.
Qed.
Lemma cb8_skip : forall (g : nat -> word) i n k, (i <= n)%nat ->
  skipn (8 * i) (cells_bytes (map (fun j => C8 (g j)) (seq k n))) = cells_bytes (map (fun j => C8 (g j)) (seq (k + i) (n - i))).
Proof.
  intros g i. induction i as [|i IH]; intros n k Hi.
  - rewrite Nat.mul_0_r, Nat.add_0_r, Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [seq map cells_bytes cbytes]. replace (8 * S i)%nat with (8 + 8 * i)%nat by lia.
    rewrite skipn_app. rewrite Mem.length_le8. replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia.
    rewrite skipn_all2 by (rewrite Mem.length_le8; lia). cbn [app].
    replace (k + S i)%nat with (S k + i)%nat by lia. apply IH. lia.
Qed.
Lemma cb8_length : forall (g : nat -> word) n k, length (cells_bytes (map (fun j => C8 (g j)) (seq k n))) = (8 * n)%nat.
Proof.
  intros g n. induction n as [|n IH]; intros k; [reflexivity|]. cbn [seq map cells_bytes cbytes]. rewrite length_app, IH. rewrite Mem.length_le8. lia.
Qed.
Lemma cb8_wf : forall (g : nat -> word) n k, cells_wf (map (fun j => C8 (g j)) (seq k n)).
Proof. intros g n. induction n as [|n IH]; intros k; [exact I|]. cbn. split; [exact I| apply IH]. Qed.

Lemma fpcells_read : forall m A F i, (i < 32)%nat ->
  cells_at usegs m A (fpcells F) ->
  rdn usegs m (Z_to_bv 64 (A + 8 * Z.of_nat i)) 8 = Some (fle8 F i).
Proof.
  intros m A F i Hi [WF BA].
  pose proof (Mem.bytes_at_rdn usegs m A _ (8 * i) 8 BA) as X. unfold fpcells in X. rewrite cb8_length in X. specialize (X ltac:(lia)).
  rewrite rdn_common in X. unfold wa in X. replace (A + Z.of_nat (8 * i)) with (A + 8 * Z.of_nat i) in X by lia. rewrite X. f_equal.
  rewrite cb8_skip by lia. rewrite cb8_first by lia. unfold fle8, Mem.le8. rewrite Nat.add_0_l. reflexivity.
Qed.

Lemma bytes_at_of_rdn : forall n m a bs,
  OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Common.PropExec.rdn usegs m (wa a) n = Some bs -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> bytes_at usegs m a bs.
Proof.
  induction n as [|n IH]; intros m a bs Hr Ha Hn.
  - cbn in Hr. injection Hr as <-. apply Mem.bytes_at_nil. lia.
  - rewrite Mem.rdn_unfold in Hr.
    destruct (mrd usegs m (wa a)) as [b|] eqn:Hb; [|discriminate].
    destruct (OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Common.PropExec.rdn usegs m (wa a + 1)%bv n) as [r|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    change (b :: r) with ([b] ++ r). apply (proj2 (Mem.bytes_at_app usegs m a [b] r)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. exact Hb.
    + cbn [length Z.of_nat Pos.of_succ_nat]. destruct n as [|n'].
      * cbn in Hr'. injection Hr' as <-. apply Mem.bytes_at_nil. lia.
      * apply IH; [| lia| lia]. rewrite <- Hr'. f_equal. unfold wa. apply bv_eq.
        rewrite u_add1 by (rewrite unsigned_lit; lia). rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma fsd_contract_P : fsd_contract usegs GETCTX_FSD.
Proof.
  unfold fsd_contract. intros R F fc m junk HFR RWC HB MI.
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  destruct (reg_get_mkR_1_10_11_12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (_ & G10 & _ & _).
  rewrite G10 in RWC, HB. replace (reg_get (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (Z_to_bv 5 10)) with x10 by (symmetry; exact G10).
  eapply evt_mono; [apply (getctx_fsd_walk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m junk RWC MI HB)|].
  intros ms' (m' & -> & MU & WM & MI' & RW'). exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  intros i Hi. replace (bv_unsigned x10 + 256 + 8 * Z.of_nat i) with ((bv_unsigned x10 + 256) + 8 * Z.of_nat i) by lia.
  apply fpcells_read; [exact Hi|]. exact (proj1 RW').
Qed.

Lemma fld_contract_P : fld_contract usegs JUMPTO_FLD.
Proof.
  unfold fld_contract. intros R F fc m HFR HB HRD.
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  destruct (reg_get_mkR_1_10_11_12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (_ & G10 & _ & _).
  rewrite G10 in HB, HRD. replace (reg_get (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (Z_to_bv 5 10)) with x10 by (symmetry; exact G10).
  assert (SRC : ro_cells usegs m (bv_unsigned x10 + 256) (fpcells F)).
  { split; [apply cb8_wf|]. unfold fpcells.
    assert (GEN : forall cnt k, (k + cnt <= 32)%nat ->
              bytes_at usegs m (bv_unsigned x10 + 256 + 8 * Z.of_nat k) (cells_bytes (map (fun j => C8 (reg_get F (Z_to_bv 5 (Z.of_nat j)))) (seq k cnt)))).
    { induction cnt as [|c IH]; intros k Hk.
      - cbn. apply Mem.bytes_at_nil. pose proof (u64_range x10). lia.
      - cbn [seq map cells_bytes cbytes]. apply (proj2 (Mem.bytes_at_app usegs m _ _ _)). split.
        + apply (bytes_at_of_rdn 8). 2,3: pose proof (u64_range x10); lia.
          rewrite rdn_common. unfold wa. exact (HRD k ltac:(lia)).
        + rewrite Mem.length_le8. replace (bv_unsigned x10 + 256 + 8 * Z.of_nat k + Z.of_nat 8) with (bv_unsigned x10 + 256 + 8 * Z.of_nat (S k)) by lia.
          apply IH. lia. }
    pose proof (GEN 32%nat 0%nat ltac:(lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X. }
  exact (jumpto_fld_walk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SRC HB).
Qed.

Definition xautoP (t : itab) := xauto usegs t MEMSET MEMCPY GETCTX_FSD JUMPTO_FLD.
Theorem xauto_soundP : forall t, itab_sound usegs t ->
  forall fc W RW ENDPC fuel k ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  xautoP t W RW ENDPC fuel k ss = Some ss' ->
  CIX usegs fc E W RW m0 base ss ms -> node_ok usegs fc ss ss' E W RW m0 base ms.
Proof.
  intros t Ht. exact (xauto_sound usegs t Ht MEMSET MEMCPY GETCTX_FSD JUMPTO_FLD set_contract_P cpy_contract_P fsd_contract_P fld_contract_P).
Qed.
