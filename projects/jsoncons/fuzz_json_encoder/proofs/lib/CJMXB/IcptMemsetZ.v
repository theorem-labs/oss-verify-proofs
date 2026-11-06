(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5RegionPoisoned Pm5AsanMemset Pm5AsanMemcpy Pm5MemsetIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrXfer BrMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import BrCanon ShZero IcptMemcpyC IcptMemcpyZ IcptMemsetC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F5 Require Import F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma ret_pc_of_ok : forall ra, ret_ok ra -> ret_pc ra = ra.
Proof.
  intros ra Hret.
  assert (He : (bv_unsigned ra mod 2 = 0)%Z).
  { pose proof Hret as H. unfold ret_ok, v_jalr, jalr_tgtZ in H. apply (f_equal (@bv_unsigned 64)) in H. rewrite Z_to_bv_unsigned in H.
    rewrite <- H. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 * 2^63)%Z.
    rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. rewrite Z.mod_mod by lia. apply land_m2_mod2. }
  rewrite <- (Z_to_bv_bv_unsigned ra). apply ret_pc_even; [apply bv_unsigned_in_range | exact He].
Qed.

Section MSZ.
Variable K : Z.
Variables ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable q : Z.
Notation sp := (Z_to_bv 64 q).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables (D C N : Z) (junk : list byte).

Definition icpt_memset_postZ : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - K, q); (D, D + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))]
    /\ stk rsegs m' (q - K) q.

Hypothesis DST : rw_cells rsegs m D [CB (Z.to_nat N) junk].
Hypothesis MI : mem_inv rsegs m.
Hypothesis HK : (2216 <= K)%Z.
Hypothesis ST : stk rsegs m (q - K) q.
Hypothesis HQ : (0x10007fff8000 + K <= q <= 0x7fffffffff00)%Z.
Hypothesis HD : (0 <= D < 2^64)%Z.
Hypothesis HC : (0 <= C < 2^64)%Z.
Hypothesis HN : (0 <= N <= 2^40)%Z.
Hypothesis AD : app D N.
Hypothesis ZD : 0 < N -> zsh m D (D + N).
Hypothesis HDJ : (0 < N -> D + N <= q - K \/ q <= D)%Z.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : Pm5RegionPoisoned.rt_layout_globs m.
Hypothesis HI : Pm5AsanMemset.ms_icpt_globs m.

Lemma uDs : bv_unsigned (Z_to_bv 64 D) = D.  Proof. apply unsigned_lit. exact HD. Qed.
Lemma uNs : bv_unsigned (Z_to_bv 64 N) = N.  Proof. apply unsigned_lit. lia. Qed.
Lemma uqs : bv_unsigned (Z_to_bv 64 q) = q.  Proof. apply unsigned_lit. lia. Qed.

Theorem icpt_memset_callZ :
  evt rsegs icpt_memset_postZ
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x80b04) fc None m (seg_rom rsegs)).
Proof.
  destruct DST as [[DW DB] DWR]. cbn [cells_size csize Nat.add] in DWR. rewrite Nat.add_0_r in DWR.
  assert (Dn : (Z.of_nat (Z.to_nat N) = N)%Z) by lia.
  rewrite Dn in DWR.
  assert (HDN : (D + N <= 0x7fffffffff00)%Z) by (destruct AD as [[A1 A2]|[A1 A2]]; lia).
  assert (Hdst : store_ok rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 D))) (Z.to_nat (bv_unsigned (Z_to_bv 64 N))) = true).
  { rewrite uDs, uNs. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia). apply (wr_at_store_ok rsegs m D N 0 (Z.to_nat N) DWR); lia. }
  assert (Hok : store_ok rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 q) - 2216)) 2216%nat = true).
  { rewrite uqs. destruct ST as (S0 & S1 & SH).
    assert (WR : wr_at rsegs m (q - 2216) 2216).
    { split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (SH (q - 2216 + i)%Z ltac:(lia))). }
    replace (Z_to_bv 64 (q - 2216)) with (wa (q - 2216 + 0)) by (unfold wa; f_equal; lia).
    apply (wr_at_store_ok rsegs m (q - 2216) 2216 0 2216 WR); lia. }

  assert (Hl : (0 < N)%Z -> (lDs (Z_to_bv 64 D) (Z_to_bv 64 N) + 8 <= bv_unsigned (Z_to_bv 64 q) - 2216)%Z).
  { intros Hp. unfold lDs, Pm5RegionPoisoned.SB. rewrite uDs, uNs, uqs.
    assert (Ha : (D + N <= 0x7fffffffff00)%Z) by (destruct AD as [[A1 A2]|[A1 A2]]; lia).
    pose proof (Z.div_le_mono (D + N - 1) 0x7fffffffff00 8 ltac:(lia) ltac:(lia)) as Hdv. change (0x7fffffffff00 / 8)%Z with 17592186044384%Z in Hdv. lia. }
  assert (HZP : (0 < N)%Z -> _ ) by (intros Hp; exact (zsh_porta rsegs m D N (ZD Hp) Hp AD)).
  eapply evt_mono.
  { apply (icpt_memset_call_raw ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m 0%Z).
    - rewrite uNs. exact HN.
    - rewrite uDs, uNs. apply app_in_app8; [exact AD | lia].
    - rewrite uqs. lia.
    - destruct (Z.lt_ge_cases 0 N) as [Hp|Hp]; [exact (Hl Hp)|].
      unfold lDs, Pm5RegionPoisoned.SB. rewrite uDs, uNs, uqs.
      assert (Hdv : ((D + N - 1) / 8 <= D / 8)%Z) by (apply Z.div_le_mono; lia).
      assert (Ha : (D <= 0x7fffffffff00)%Z) by (destruct AD as [[A1 A2]|[A1 A2]]; lia).
      pose proof (Z.div_le_mono D 0x7fffffffff00 8 ltac:(lia) ltac:(lia)) as Hdv2. change (0x7fffffffff00 / 8)%Z with 17592186044384%Z in Hdv2.
      pose proof (Z.div_pos (D + N - 1 + 1) 8). lia.
    - rewrite uDs, uNs, uqs. intros Hp. destruct (HDJ Hp); [left|right]; lia.
    - exact Hok.
    - exact Hdst.
    - exact Hret.
    - exact HG.
    - exact HI.
    - intros Hp. rewrite uNs in Hp. unfold fDs, lDs. rewrite uDs, uNs. exact (proj1 (HZP Hp)).
    - intros Hp. rewrite uNs in Hp. unfold lDs. rewrite uDs, uNs. exact (proj1 (proj2 (HZP Hp))).
    - left; reflexivity.
    - intros Hp. rewrite uNs in Hp. unfold fDs, lDs. rewrite uDs, uNs. exact (proj2 (proj2 (HZP (proj1 Hp)))). }
  intros ms' (regs' & Mj & -> & E10 & E2 & E1 & KCS & OUT & GR).
  rewrite uDs in E10. rewrite uqs in OUT.
  set (vs := repeat (cbyte (Z_to_bv 64 C)) (Z.to_nat (bv_unsigned (Z_to_bv 64 N)))).
  set (m' := wbytes Mj (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 D))) vs).
  assert (Lvs : Z.of_nat (length vs) = N) by (unfold vs; rewrite repeat_length, uNs; exact Dn).
  assert (Hnw : (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 D))) + Z.of_nat (length vs) < 2^64)%Z)
    by (rewrite !uDs, Lvs; destruct AD as [[A1 A2]|[A1 A2]]; lia).
  assert (GR' : forall x, m x <> None -> m' x <> None) by (intros x Hx; apply wbytes_grows, GR, Hx).
  assert (WM : wmono rsegs m m') by (apply wmono_of_grows; exact GR').
  assert (OUTD : forall x : word, (bv_unsigned x < D \/ D + N <= bv_unsigned x)%Z -> m' x = Mj x).
  { intros x Hx. apply wbytes_out; [lia | rewrite !uDs, Lvs; exact Hx]. }
  assert (MU : munch [(q - K, q); (D, D + N)]%Z m m').
  { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
    rewrite OUTD by lia. apply OUT. lia. }
  assert (CV : cbyte (Z_to_bv 64 C) = Z_to_bv 8 (C mod 256)).
  { unfold cbyte. rewrite (unsigned_lit C) by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 8)%Z with 256%Z. rewrite Z.mod_mod by lia. reflexivity. }
  exists (getr regs' 5), (getr regs' 6), (getr regs' 7), (getr regs' 11), (getr regs' 12), (getr regs' 13), (getr regs' 14), (getr regs' 15),
         (getr regs' 16), (getr regs' 17), (getr regs' 28), (getr regs' 29), (getr regs' 30), (getr regs' 31), m'.
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
    rewrite K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold m'. rewrite uDs. reflexivity. }
  split; [exact MU|]. split; [exact WM|].
  split.
  {
    intros x b Hx. destruct (Z.lt_ge_cases (bv_unsigned x) D) as [Hlo|Hlo];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (D + N)) as [Hhi|Hhi]].
    - rewrite OUTD in Hx by lia.
      destruct (Z.lt_ge_cases (bv_unsigned x) (q - 2216)) as [Fl|Fl]; [rewrite OUT in Hx by lia; exact (MI _ _ Hx)|].
      destruct (Z.lt_ge_cases (bv_unsigned x) q) as [Fh|Fh]; [|rewrite OUT in Hx by lia; exact (MI _ _ Hx)].
      destruct ST as (_ & _ & SH). destruct (SH (bv_unsigned x) ltac:(lia)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
      destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x W Ex).
    - destruct DWR as (_ & _ & DWH). specialize (DWH (bv_unsigned x - D)%Z ltac:(lia)).
      replace (wa (D + (bv_unsigned x - D))) with x in DWH by (unfold wa; apply bv_eq; rewrite Z_to_bv_unsigned; replace (D + (bv_unsigned x - D))%Z with (bv_unsigned x) by lia; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
      destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x DWH Ex).
    - rewrite OUTD in Hx by lia.
      destruct (Z.lt_ge_cases (bv_unsigned x) (q - 2216)) as [Fl|Fl]; [rewrite OUT in Hx by lia; exact (MI _ _ Hx)|].
      destruct (Z.lt_ge_cases (bv_unsigned x) q) as [Fh|Fh]; [|rewrite OUT in Hx by lia; exact (MI _ _ Hx)].
      destruct ST as (_ & _ & SH). destruct (SH (bv_unsigned x) ltac:(lia)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
      destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x W Ex). }
  split.
  {
    split; [split|].
    - cbn. split; [rewrite repeat_length; reflexivity|exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite repeat_length; lia|].
      intros i Hi. rewrite repeat_length in Hi. unfold mrd. unfold m'.
      replace (wa (D + Z.of_nat i)) with (wa (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 D))) + Z.of_nat i)) by (rewrite !uDs; reflexivity).
      rewrite wbytes_in by (try (rewrite <- Lvs in Hi; unfold vs in *; rewrite repeat_length in *; lia); exact Hnw).
      unfold vs. rewrite uNs, CV. rewrite nth_error_repeat by lia. reflexivity.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Dn. eapply wr_at_wmono; [exact DWR | exact WM]. }
  {
    destruct ST as (S0 & S1 & SH). split; [lia|]. split; [lia|]. intros a Ha. destruct (SH a Ha) as [W (b & Hb)]. split.
    - apply WM, W.
    - unfold mrd in *. destruct (m (wa a)) as [b0|] eqn:Ea.
      + destruct (m' (wa a)) as [b1|] eqn:Eb; [exists b1; reflexivity|]. exfalso. apply (GR' (wa a)); [rewrite Ea; discriminate| exact Eb].
      + destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity| exists b; exact Hb]. }
Qed.
End MSZ.
