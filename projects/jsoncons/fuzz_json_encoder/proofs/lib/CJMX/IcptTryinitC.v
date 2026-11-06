(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm4RegionPoisoned Pm4RegionPoisoned Pm4StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrXfer BrMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMX Require Import BrCanon ShZero IcptCells IcptMemcpyC IcptMemcpyZ IcptMemsetZ.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma keeps_cs_of_but128 : forall R R', Pm4RegionPoisoned.keeps_but [1; 2; 8]%bv R R' ->
  getr R' 1 = getr R 1 -> getr R' 2 = getr R 2 -> getr R' 8 = getr R 8 -> keeps_cs R R'.
Proof.
  intros R R' KB E1 E2 E8 r Hr.
  destruct (decide (r = 1%bv)) as [->|N1]; [exact E1|].
  destruct (decide (r = 2%bv)) as [->|N2]; [exact E2|].
  destruct (decide (r = 8%bv)) as [->|N8]; [exact E8|].
  apply KB; [exact Hr|]. cbn [In]. intuition congruence.
Qed.

Section TI.
Variable K : Z.
Variables ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable q : Z.
Notation sp := (Z_to_bv 64 q).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.

Notation R0 := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

Definition tryinit_postZ : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - K, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (q - K) q.

Hypothesis MI : mem_inv rsegs m.
Hypothesis HK : (16 <= K)%Z.
Hypothesis ST : stk rsegs m (q - K) q.
Hypothesis HQ : (0x1000000 + K <= q < 2^64)%Z.
Hypothesis Hret : ret_ok ra.
Hypothesis HAI : ai_byte m.

Lemma uqt : bv_unsigned (Z_to_bv 64 q) = q.  Proof. apply unsigned_lit. lia. Qed.

Theorem tryinit_callZ :
  evt rsegs tryinit_postZ (MS R0 F (Z_to_bv 64 0x89690) fc None m (seg_rom rsegs)).
Proof.
  pose (fx := mkFP F fc).
  assert (Hok : store_ok rsegs m (Z_to_bv 64 (q - 16)) 16%nat = true).
  { destruct ST as (S0 & S1 & SH).
    assert (WR : wr_at rsegs m (q - 16) 16).
    { split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (SH (q - 16 + i)%Z ltac:(lia))). }
    replace (Z_to_bv 64 (q - 16)) with (wa (q - 16 + 0)) by (unfold wa; f_equal; lia).
    apply (wr_at_store_ok rsegs m (q - 16) 16 0 16 WR); lia. }
  destruct (@Pm4StrlenIcpt.tryinit_fast_run fx R0 m (seg_rom rsegs) ra q eq_refl eq_refl Hret ltac:(lia) ltac:(lia) Hok HAI)
    as (regs' & RUN & E10 & E2 & E8 & E1 & KB).
  assert (EPC : Z_to_bv 64 0x89690 = (0x89690 : word)) by (apply bv_eq; reflexivity).
  rewrite EPC.
  set (Mj := wbytes (wbytes m (Z_to_bv 64 (q - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (q - 16)) (word_to_le_bytes 8 (getr R0 8))) in RUN.
  change (CatSim.msteps rsegs (MS R0 F (0x89690 : word) fc None m (seg_rom rsegs)) (MS regs' F ra fc None Mj (seg_rom rsegs))) in RUN.
  eapply evt_of_cat_run; [apply rcanon_mkR | exact RUN | ].
  assert (U8 : bv_unsigned (Z_to_bv 64 (q - 8)) = (q - 8)%Z) by (apply unsigned_lit; lia).
  assert (U16 : bv_unsigned (Z_to_bv 64 (q - 16)) = (q - 16)%Z) by (apply unsigned_lit; lia).
  assert (OUT : forall x : word, (bv_unsigned x < q - 16 \/ q <= bv_unsigned x)%Z -> Mj x = m x).
  { intros x Hx. unfold Mj. rewrite wbytes_out; [| rewrite length_N_to_le_bytes, U16; cbn [Z.of_nat Pos.to_nat]; lia | rewrite length_N_to_le_bytes, U16; cbn [Z.of_nat Pos.to_nat]; lia].
    rewrite wbytes_out; [reflexivity | rewrite length_N_to_le_bytes, U8; cbn [Z.of_nat Pos.to_nat]; lia | rewrite length_N_to_le_bytes, U8; cbn [Z.of_nat Pos.to_nat]; lia]. }
  assert (GR : forall x, m x <> None -> Mj x <> None) by (intros x Hx; unfold Mj; apply IcptMemcpyZ.wbytes_grows, IcptMemcpyZ.wbytes_grows, Hx).
  assert (WM : wmono rsegs m Mj) by (apply wmono_of_grows; exact GR).
  assert (MU : munch [(q - K, q)]%Z m Mj).
  { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & _). apply OUT. lia. }
  assert (KCS : keeps_cs R0 regs') by (apply keeps_cs_of_but128; [exact KB | rewrite E1; reflexivity | rewrite E2; reflexivity | rewrite E8; reflexivity]).
  exists (getr regs' 5), (getr regs' 6), (getr regs' 7), (getr regs' 11), (getr regs' 12), (getr regs' 13), (getr regs' 14), (getr regs' 15),
         (getr regs' 16), (getr regs' 17), (getr regs' 28), (getr regs' 29), (getr regs' 30), (getr regs' 31), Mj.
  split.
  { rewrite (ret_pc_of_ok ra Hret). unfold canon_regs. rewrite E1, E2, E10.
    assert (K3 : getr regs' 3 = gp) by (rewrite (KCS 3%bv) by in_cs; reflexivity).
    assert (K4 : getr regs' 4 = tp) by (rewrite (KCS 4%bv) by in_cs; reflexivity).
    assert (K8 : getr regs' 8 = s0) by (rewrite (KCS 8%bv) by in_cs; reflexivity).
    assert (K9 : getr regs' 9 = s1) by (rewrite (KCS 9%bv) by in_cs; reflexivity).
    assert (K18 : getr regs' 18 = s2) by (rewrite (KCS 18%bv) by in_cs; reflexivity).
    assert (K19 : getr regs' 19 = s3) by (rewrite (KCS 19%bv) by in_cs; reflexivity).
    assert (K20 : getr regs' 20 = s4) by (rewrite (KCS 20%bv) by in_cs; reflexivity).
    assert (K21 : getr regs' 21 = s5) by (rewrite (KCS 21%bv) by in_cs; reflexivity).
    assert (K22 : getr regs' 22 = s6) by (rewrite (KCS 22%bv) by in_cs; reflexivity).
    assert (K23 : getr regs' 23 = s7) by (rewrite (KCS 23%bv) by in_cs; reflexivity).
    assert (K24 : getr regs' 24 = s8) by (rewrite (KCS 24%bv) by in_cs; reflexivity).
    assert (K25 : getr regs' 25 = s9) by (rewrite (KCS 25%bv) by in_cs; reflexivity).
    assert (K26 : getr regs' 26 = s10) by (rewrite (KCS 26%bv) by in_cs; reflexivity).
    assert (K27 : getr regs' 27 = s11) by (rewrite (KCS 27%bv) by in_cs; reflexivity).
    rewrite K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. reflexivity. }
  split; [exact MU|]. split; [exact WM|].
  split.
  { intros x b Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (q - 16)) as [Fl|Fl]; [rewrite OUT in Hx by lia; exact (MI _ _ Hx)|].
    destruct (Z.lt_ge_cases (bv_unsigned x) q) as [Fh|Fh]; [|rewrite OUT in Hx by lia; exact (MI _ _ Hx)].
    destruct ST as (_ & _ & SH). destruct (SH (bv_unsigned x) ltac:(lia)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
    destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x W Ex). }
  { destruct ST as (S0 & S1 & SH). split; [lia|]. split; [lia|]. intros a Ha. destruct (SH a Ha) as [W (b & Hb)]. split.
    - apply WM, W.
    - unfold mrd in *. destruct (m (wa a)) as [b0|] eqn:Ea.
      + destruct (Mj (wa a)) as [b1|] eqn:Eb; [exists b1; reflexivity|]. exfalso. apply (GR (wa a)); [rewrite Ea; discriminate| exact Eb].
      + destruct (Mj (wa a)) as [b1|]; [exists b1; reflexivity| exists b; exact Hb]. }
Qed.
End TI.
