(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5RegionPoisoned Pm5AsanMemcpy Pm5MemcpyIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrXfer BrMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import BrCanon IcptMemcpyC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F5 Require Import F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma wbytes_in : forall bs m (addr : word) i, (i < length bs)%nat -> (bv_unsigned addr + Z.of_nat (length bs) < 2^64)%Z ->
  wbytes m addr bs (wa (bv_unsigned addr + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b rest IH]; intros m addr i Hi Hnw; [cbn in Hi; lia|].
  cbn [length] in *. destruct i as [|i].
  - cbn [wbytes nth_error]. rewrite wbytes_below.
    + cbv beta. replace (wa (bv_unsigned addr + Z.of_nat 0)) with addr.
      * rewrite bv_eqb_refl. reflexivity.
      * unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [Z.of_nat]. rewrite Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
    + pose proof (bv_unsigned_in_range 64 addr). unfold bv_modulus in *.
      rewrite (u_add1 addr) by lia. lia.
    + rewrite wa_unsigned by (pose proof (bv_unsigned_in_range 64 addr); unfold bv_modulus in *; lia).
      pose proof (bv_unsigned_in_range 64 addr). unfold bv_modulus in *. rewrite (u_add1 addr) by lia. lia.
  - cbn [wbytes nth_error].
    pose proof (bv_unsigned_in_range 64 addr) as Ra. unfold bv_modulus in Ra.
    assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z) by (apply u_add1; lia).
    replace (wa (bv_unsigned addr + Z.of_nat (S i))) with (wa (bv_unsigned (addr + 1) + Z.of_nat i)) by (rewrite Hu1; f_equal; lia).
    apply IH; [lia | rewrite Hu1; lia].
Qed.

Lemma wbytes_out : forall bs m (addr : word) x, (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  intros bs m addr x Hnw [Hlt|Hge]; [apply wbytes_below; assumption | apply wbytes_above; exact Hge].
Qed.

Lemma wbytes_grows : forall bs m addr x, m x <> None -> wbytes m addr bs x <> None.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hx; [exact Hx|].
  cbn [wbytes]. apply IH. cbv beta. destruct (bv_eqb x addr); [discriminate|exact Hx].
Qed.

Ltac in_cs := unfold callee_saved; cbn [In]; repeat first [ left; reflexivity | right ].

Section MZ.
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable q : Z.
Notation sp := (Z_to_bv 64 q).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables (D : Z) (src junk : list byte) (kS kD : Z).

Notation S := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Notation s := q.

Definition icpt_memcpy_postZ : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(s - 2232, s); (D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) src]
    /\ bytes_at rsegs m' S src
    /\ stk rsegs m' (s - 2232) s.

Hypothesis SRC : bytes_at rsegs m S src.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis DST : rw_cells rsegs m D [CB (Z.to_nat n) junk].
Hypothesis HD : (0 <= D < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Hypothesis MI : mem_inv rsegs m.
Hypothesis ST : stk rsegs m (s - 2232) s.

Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis HappS : Pm5AsanMemcpy.in_app8 S n.
Hypothesis HappD : Pm5AsanMemcpy.in_app8 D n.
Hypothesis Hs : (0x1000000 <= s - 2232)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshS : (lS a1 a2 + 8 <= s - 2232)%Z.
Hypothesis HshD : (lD (Z_to_bv 64 D) a2 + 8 <= s - 2232)%Z.
Hypothesis HdjS : (0 < n -> S + n <= s - 2232 \/ s <= S)%Z.
Hypothesis HdjD : (0 < n -> D + n <= s - 2232 \/ s <= D)%Z.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : Pm5RegionPoisoned.rt_layout_globs m.
Hypothesis HI : Pm5AsanMemcpy.mc_icpt_globs m.
Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS a1 <= bv_unsigned x < lS a1 a2)%Z -> m x = Some (Z_to_bv 8 0).
Hypothesis HLS : (0 < n)%Z -> m (Z_to_bv 64 (lS a1 a2)) = Some (Z_to_bv 8 kS).
Hypothesis HkS : kS = 0%Z \/ ((S + n - 1) mod 8 < kS <= 7)%Z.
Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn rsegs m (Z_to_bv 64 (fS a1 - fS a1 mod 8)) 8%nat = Some w0 /\ rdn rsegs m (Z_to_bv 64 (lS a1 a2 - lS a1 a2 mod 8)) 8%nat = Some w1.
Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD (Z_to_bv 64 D) <= bv_unsigned x < lD (Z_to_bv 64 D) a2)%Z -> m x = Some (Z_to_bv 8 0).
Hypothesis HLD : (0 < n)%Z -> m (Z_to_bv 64 (lD (Z_to_bv 64 D) a2)) = Some (Z_to_bv 8 kD).
Hypothesis HkD : kD = 0%Z \/ ((D + n - 1) mod 8 < kD <= 7)%Z.
Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn rsegs m (Z_to_bv 64 (fD (Z_to_bv 64 D) - fD (Z_to_bv 64 D) mod 8)) 8%nat = Some w0 /\
                                                rdn rsegs m (Z_to_bv 64 (lD (Z_to_bv 64 D) a2 - lD (Z_to_bv 64 D) a2 mod 8)) 8%nat = Some w1.

Lemma uD : bv_unsigned (Z_to_bv 64 D) = D.
Proof. apply unsigned_lit. exact HD. Qed.
Lemma uq : bv_unsigned (Z_to_bv 64 q) = q.
Proof. apply unsigned_lit. destruct Hs. lia. Qed.

Lemma land_m2_mod2 : forall x, (Z.land x (-2) mod 2 = 0)%Z.
Proof. intros x. rewrite <- Z.bit0_mod. rewrite Z.land_spec. rewrite Bool.andb_false_r. reflexivity. Qed.

Lemma ret_pc_ok : ret_pc ra = ra.
Proof.
  assert (He : (bv_unsigned ra mod 2 = 0)%Z).
  { pose proof Hret as H. unfold ret_ok, v_jalr, jalr_tgtZ in H. apply (f_equal (@bv_unsigned 64)) in H. rewrite Z_to_bv_unsigned in H.
    rewrite <- H. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 * 2^63)%Z.
    rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. rewrite Z.mod_mod by lia. apply land_m2_mod2. }
  rewrite <- (Z_to_bv_bv_unsigned ra). apply ret_pc_even; [apply bv_unsigned_in_range | exact He].
Qed.

Theorem icpt_memcpy_callZ :
  evt rsegs icpt_memcpy_postZ
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x80b0c) fc None m (seg_rom rsegs)).
Proof.

  destruct DST as [[DW DB] DWR]. cbn [cells_size csize Nat.add] in DWR. rewrite Nat.add_0_r in DWR.
  assert (Dn : (Z.of_nat (Z.to_nat n) = n)%Z) by (pose proof (bv_unsigned_in_range 64 a2); lia).
  rewrite Dn in DWR.
  assert (Hdst : store_ok rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 D))) (Z.to_nat n) = true).
  { rewrite uD. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia). apply (wr_at_store_ok rsegs m D n 0 (Z.to_nat n) DWR); lia. }
  assert (Hsrc : rdn rsegs m (Z_to_bv 64 S) (Z.to_nat n) = Some src).
  { replace (Z_to_bv 64 S) with (wa (S + Z.of_nat 0)) by (unfold wa; f_equal; lia).
    rewrite (bytes_at_rdn rsegs m S src 0 (Z.to_nat n) SRC) by lia. rewrite skipn_O, firstn_all2 by lia. reflexivity. }
  assert (Hok : store_ok rsegs m (Z_to_bv 64 (s - 2232)) 2232%nat = true).
  { destruct ST as (S0 & S1 & SH).
    assert (WR : wr_at rsegs m (s - 2232) 2232).
    { split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (SH (s - 2232 + i)%Z ltac:(lia))). }
    replace (Z_to_bv 64 (s - 2232)) with (wa (s - 2232 + 0)) by (unfold wa; f_equal; lia).
    apply (wr_at_store_ok rsegs m (s - 2232) 2232 0 2232 WR); lia. }
  eapply evt_mono.
  { exact (icpt_memcpy_call_raw ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m src kS kD Hn HappS ltac:(rewrite uD; exact HappD) ltac:(rewrite uq; exact Hs) ltac:(rewrite uq; exact HshS)
              ltac:(rewrite uq; exact HshD) ltac:(rewrite uq; exact HdjS) ltac:(rewrite uD, uq; exact HdjD)
              ltac:(rewrite uD; lia) ltac:(rewrite uq; exact Hok) Hdst Hsrc Hret HG HI HZS HLS HkS HWS HZD HLD ltac:(rewrite uD; exact HkD) HWD). }
  intros ms' (regs' & Mj & -> & E10 & E2 & E1 & KCS & OUT & GR).
  rewrite uD in E10. rewrite uq in OUT.
  set (m' := wbytes Mj (Z_to_bv 64 D) src).
  assert (Lsrc : Z.of_nat (length src) = n) by (rewrite LEN; exact Dn).
  assert (Hnw : (bv_unsigned (Z_to_bv 64 D) + Z.of_nat (length src) < 2^64)%Z) by (rewrite uD, Lsrc; unfold Pm5AsanMemcpy.in_app8, Pm5RegionPoisoned.LOWEND, Pm5RegionPoisoned.HIGHEND in HappD; lia).
  assert (GR' : forall x, m x <> None -> m' x <> None) by (intros x Hx; apply wbytes_grows, GR, Hx).
  assert (WM : wmono rsegs m m') by (apply wmono_of_grows; exact GR').
  assert (OUTD : forall x : word, (bv_unsigned x < D \/ D + n <= bv_unsigned x)%Z -> m' x = Mj x).
  { intros x Hx. apply wbytes_out; [lia | rewrite uD, Lsrc; exact Hx]. }
  assert (MU : munch [(s - 2232, s); (D, D + n)]%Z m m').
  { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
    rewrite OUTD by lia. apply OUT. lia. }
  exists (getr regs' 5), (getr regs' 6), (getr regs' 7), (getr regs' 11), (getr regs' 12), (getr regs' 13), (getr regs' 14), (getr regs' 15),
         (getr regs' 16), (getr regs' 17), (getr regs' 28), (getr regs' 29), (getr regs' 30), (getr regs' 31), m'.
  split.
  { rewrite ret_pc_ok. unfold canon_regs. rewrite E1, E2, E10.
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
    rewrite K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold m'. rewrite uD. reflexivity. }
  split; [exact MU|]. split; [exact WM|].
  split.
  {
    intros x b Hx. destruct (Z.lt_ge_cases (bv_unsigned x) D) as [Hlo|Hlo];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (D + n)) as [Hhi|Hhi]].
    - rewrite OUTD in Hx by lia.
      destruct (Z.lt_ge_cases (bv_unsigned x) (s - 2232)) as [Fl|Fl]; [rewrite OUT in Hx by lia; exact (MI _ _ Hx)|].
      destruct (Z.lt_ge_cases (bv_unsigned x) s) as [Fh|Fh]; [|rewrite OUT in Hx by lia; exact (MI _ _ Hx)].
      destruct ST as (_ & _ & SH). destruct (SH (bv_unsigned x) ltac:(lia)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
      destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x W Ex).
    - destruct DWR as (_ & _ & DWH). specialize (DWH (bv_unsigned x - D)%Z ltac:(lia)).
      replace (wa (D + (bv_unsigned x - D))) with x in DWH by (unfold wa; apply bv_eq; rewrite Z_to_bv_unsigned; replace (D + (bv_unsigned x - D))%Z with (bv_unsigned x) by lia; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
      destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x DWH Ex).
    - rewrite OUTD in Hx by lia.
      destruct (Z.lt_ge_cases (bv_unsigned x) (s - 2232)) as [Fl|Fl]; [rewrite OUT in Hx by lia; exact (MI _ _ Hx)|].
      destruct (Z.lt_ge_cases (bv_unsigned x) s) as [Fh|Fh]; [|rewrite OUT in Hx by lia; exact (MI _ _ Hx)].
      destruct ST as (_ & _ & SH). destruct (SH (bv_unsigned x) ltac:(lia)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
      destruct (m x) eqn:Ex; [exact (MI _ _ Ex)|]. exact (wview_not_ro rsegs m x W Ex). }
  split.
  {
    split; [split|].
    - cbn. split; [exact LEN|exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [pose proof Hnw as Hnw'; rewrite uD in Hnw'; lia|].
      intros i Hi. unfold mrd. unfold m'.
      replace (wa (D + Z.of_nat i)) with (wa (bv_unsigned (Z_to_bv 64 D) + Z.of_nat i)) by (rewrite uD; reflexivity).
      rewrite wbytes_in by (try exact Hi; exact Hnw).
      destruct (nth_error src i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Dn. eapply wr_at_wmono; [exact DWR | exact WM]. }
  split.
  {
    eapply bytes_at_agree; [exact SRC|]. intros x Hx. rewrite Lsrc in Hx.
    assert (Ux : bv_unsigned (wa x) = x) by (apply wa_unsigned; destruct SRC as (S0 & S1 & _); rewrite Lsrc in S1; lia).
    rewrite OUTD by (rewrite Ux; lia). apply OUT. rewrite Ux. destruct (Z.lt_ge_cases 0 n) as [Hp|Hp].
    - specialize (HdjS Hp). lia.
    - lia. }
  {
    destruct ST as (S0 & S1 & SH). split; [lia|]. split; [lia|]. intros a Ha. destruct (SH a Ha) as [W (b & Hb)]. split.
    - apply WM, W.
    - unfold mrd in *. destruct (m (wa a)) as [b0|] eqn:Ea.
      + destruct (m' (wa a)) as [b1|] eqn:Eb; [exists b1; reflexivity|]. exfalso. apply (GR' (wa a)); [rewrite Ea; discriminate| exact Eb].
      + destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity| exists b; exact Hb]. }
Qed.
End MZ.
