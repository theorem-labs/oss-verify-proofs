(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import DgBaseU.
Set Default Proof Mode "Classic".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DG.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Local Notation SP0 := (DgBaseU.SP0 sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis LENR : (4096 <= lenp /\ lenp + 4 <= 2^47)%Z.
Hypothesis KPR : (4096 <= kp /\ kp + 4 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 64 \/ SP0 + 8 <= buf)%Z.
Hypothesis SEP_L : (lenp + 4 <= SP0 - 64 \/ SP0 + 8 <= lenp)%Z.
Hypothesis SEP_K : (kp + 4 <= SP0 - 64 \/ SP0 + 8 <= kp)%Z.
Hypothesis SEP_BL : (buf + 21 <= lenp \/ lenp + 4 <= buf)%Z.
Hypothesis SEP_BK : (buf + 21 <= kp \/ kp + 4 <= buf)%Z.
Hypothesis SEP_LK : (lenp + 4 <= kp \/ kp + 4 <= lenp)%Z.
Hypothesis LA : (lenp mod 4 = 0)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Local Notation DG_W := (DgBaseU.DG_W sp buf lenp kp).
Local Notation dg_post := (DgBaseU.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgBaseU.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 m0 buf lenp kp).
Local Notation dg_ret' := (DgBaseU.dg_ret' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA).
Ltac dg_mem_tac := unfold DgBaseU.dg_mem, DgBaseU.DG_W; dg_conjs; try eassumption; try (rewrite ?upd_length; assumption).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgBaseU.DG_W in MU.

Lemma dg_rw1_loop : forall (n : nat) (len D U r tk Ks kappa : Z) t0' t1' t2' s0' a3' a5' t3' t4' t6' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 3)%Z -> (0 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (r < D)%Z -> (D < 2 ^ 64)%Z -> (r + tk <= U)%Z -> (U < 2 ^ 64)%Z -> (1 <= tk)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' (Z_to_bv 64 r)
                                  (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 tk) a3' (Z_to_bv 64 (len + -1 + buf)) a5' (Z_to_bv 64 1) (Z_to_bv 64 0)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' (Z_to_bv 64 1) t6')
                              F (Z_to_bv 64 0x4501c) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA.
  induction n as [n IH] using lt_wf_ind.
  intros len D U r tk Ks kappa t0' t1' t2' s0' a3' a5' t3' t4' t6' s2' s3' s4' s5' s6' m bs Hn DM Hlen Hk Hr0 HrD HD HrU HU Htk.
  pose proof DM as DM0. destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  assert (IDX : dg_idx buf (len + -1)) by exact I.
  dg_xstep. dg_solve 8%nat [0x4501c; 0x450ec]%Z.
  all: first
    [ dg_at [0x450ec]%Z; eapply (dg_ret' _ len kappa Ks); [ dg_mem_tac | lia | lia | dg_b01 ]
    | dg_at [0x4501c]%Z; eapply (IH (Z.to_nat (D - (r + tk))) ltac:(lia) len D U (r + tk)%Z tk Ks kappa);
      [ reflexivity | dg_mem_tac | lia | lia | lia | lia | lia | lia | lia | lia ] ].
Qed.

Lemma dg_rw1_entry : forall (len D U r dv kc s Ks : Z) t2' s0' a2' a5' t3' t6' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (1 <= len <= 3)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z -> (56 <= s <= 59)%Z ->
  (0 <= r < U)%Z -> (U < 2 ^ 64)%Z -> (0 <= D < 2 ^ 64)%Z -> (dv = 1 \/ dv = 10 \/ dv = 100)%Z -> (2 <= kc <= 4)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) t2' s0' (Z_to_bv 64 r)
                                  (Z_to_bv 64 D) (Z_to_bv 64 U) a2' (Z_to_bv 64 1) (Z_to_bv 64 dv) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' (Z_to_bv 64 kc) (Z_to_bv 64 1) t6')
                              F (Z_to_bv 64 0x44fb4) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA.
  intros len D U r dv kc s Ks t2' s0' a2' a5' t3' t6' s2' s3' s4' s5' s6' m bs DM Hlen HKs Hs Hr HU HD Hdv Hkc.
  destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  assert (Hs4 : s = 56%Z \/ s = 57%Z \/ s = 58%Z \/ s = 59%Z) by lia.
  destruct Hs4 as [-> | [-> | [-> | ->]]]; destruct Hdv as [-> | [-> | ->]].
  all: dg_solve 8%nat [0x4501c; 0x450ec]%Z.
  all: first
    [ dg_at [0x450ec]%Z; eapply (dg_ret' _ len (kc - 2) Ks); [ dg_mem_tac | lia | lia | dg_b01 ]
    | dg_at [0x4501c]%Z; eapply (dg_rw1_loop _ len D U r _ Ks (kc - 2)%Z);
      [ reflexivity | dg_mem_tac | lia | lia | lia | lia | lia | lia | lia | lia ] ].
Qed.

End DG.
