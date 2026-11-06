(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_gates F_rip M_sspdefs M_inet_pton_A M_inet_pton_C.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition inetq_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (A : Z) (N : nat) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (outs : list byte),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (A, A + Z.of_nat N)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)]
    /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ u8arr asegs m' A outs /\ length outs = N
    /\ (r = 0 \/ r = 1).

Lemma inet_pton_callq : forall ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (af S A : Z) (str ojunk : list byte) (N : nat) (canary : word) (lo : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> rw_cells asegs m A [CB N ojunk] ->
  ((af = 2 /\ 4 <= Z.of_nat N) \/ (af = 10 /\ N = 16%nat)) ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  stk asegs m lo q -> lo <= q - 80 - 2224 ->
  icpt_env m -> 0x10007fff8000 <= lo -> q <= 2^47 ->
  accessible m lo (q - lo) -> sh_readable m lo (q - lo) ->
  cwin A (Z.of_nat N) -> 0x609000 <= A -> A + Z.of_nat N <= lo -> 0x609000 <= S -> S + Z.of_nat (length str) + 1 <= lo ->
  (A + Z.of_nat N <= S \/ S + Z.of_nat (length str) + 1 <= A) ->
  mem_inv asegs m ->
  evt asegs (inetq_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str A N canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz af) (wz S) (wz A) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x9a630) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros STR OUT AF GOT GUARD ST LO IE KLO QH ACK RDK AWIN A1 A2 S1 S2 SEP MI.
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; destruct ST as (L0 & _); lia).
  assert (UA : bv_unsigned (wz A) = A) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
  assert (UF : bv_unsigned (wz af) = af) by (apply unsigned_lit; lia).
  unfold got_ssp, ssp_guard in *.
  eapply evt_mono.
  { eapply (inet_pton_spec ra (wz q) gp tp t0 t1 t2 s0 s1 (wz af) (wz S) (wz A)) with (str := str) (ojunk := ojunk) (N := N) (canary := canary) (lo := lo);
      rewrite ?UQ, ?UA, ?US, ?UF; unfold got_ssp, ssp_guard; first [ eassumption | lia ]. }
  intros ms' P. unfold inet_pton_post in P. rewrite ?UQ, ?UA, ?US in P. exact P.
Qed.

Definition inet_tpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q.

Section Tail.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (A sz lo : Z) (jk0 : list byte).
  Notation SAVES := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis FRM : rw_cells asegs m (q + -2160) (CB 2080 jk0 :: SAVES).
  Hypothesis ST : stk asegs m lo (q + -2160).
  Hypothesis LO : lo <= q - 2160 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis SZ : 1 <= sz <= 64.
  Hypothesis WINA : cwin A sz.
  Hypothesis WINA2 : A + sz < 2^47.
  Hypothesis ACCA : accessible m A sz.
  Hypothesis RDA : sh_readable m A sz.

  Notation TPOST := (inet_tpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="LO KLO Q64 WINA WINA2"] Lemma BL : 0 <= A /\ A + sz < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2240 /\ 17594333495296 <= lo.
  Proof. destruct WINA as [_ W]. lia. Qed.

  #[using="A sz jk0 MI FRM ST LO KLO Q64 WINA WINA2"] Lemma LX1 : forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x49d9c) fc None m (seg_rom asegs)).
  Proof.
    intros. pose proof BL as BL0. pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof FRM as FR. pose proof ST as ST1.
    do 14 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="jk0 MI FRM ST LO KLO Q64 IE WINA WINA2 ACCA"] Lemma LWL : forall (j : nat) (cur : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    Z.to_nat (sh (A + sz - 1) - cur) = j -> sh A <= cur < sh (A + sz - 1) ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz A) (wz sz) (wz cur) (wz (2147450880 + Z.shiftr (A + sz + -1) 3)) (wz 0) x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4a074) fc None m (seg_rom asegs)).
  Proof.
    intros j. pose proof BL as BL0. pose proof (ie_shadow _ IE) as (GOT1 & SHB1).
    induction j as [|j IH]; intros until x31; intros Hj Hc; [exfalso; lia|].
    assert (SL : sh (A + sz - 1) = 2147450880 + Z.shiftr (A + sz + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (A + sz + -1) with (A + sz - 1) by lia; lia).
    pose proof (sh_div8 (A + sz - 1)) as D1.
    pose proof (ov_read1_mrd m cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero m A sz cur ACCA ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX1.
  Qed.

  #[using="jk0 MI FRM ST LO KLO Q64 IE SZ WINA WINA2 ACCA"] Lemma LWS : forall x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz A) (wz sz) (wz (2147450880 + Z.shiftr A 3)) (wz (2147450880 + Z.shiftr (A + sz + -1) 3)) (wz (A + sz + -1)) x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4a058) fc None m (seg_rom asegs)).
  Proof.
    intros. pose proof BL as BL0. pose proof (ie_shadow _ IE) as (GOT1 & SHB1).
    destruct (acc_byte_rd m A sz (A + sz + -1) ACCA ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((A + sz + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (A + sz + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX1.
    - eapply LWL; [reflexivity |].
      rewrite !shiftr3_div in *. replace (A + sz - 1) with (A + sz + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= A / 8 < 2^44 /\ 0 <= (A + sz + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      try (change 18446744073709551615 with (Z.ones 64) in K6; rewrite ?Z.land_ones in K6 by lia).
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="jk0 MI FRM ST LO KLO Q64 IE SZ WINA WINA2 ACCA RDA"] Lemma LB : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz A) (wz sz) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x49d48) fc None m (seg_rom asegs)).
  Proof.
    intros. pose proof BL as BL0. pose proof (ie_shadow _ IE) as (GOT1 & SHB1).
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. clear - K2 SZ.
      replace ((sz + -65) mod 18446744073709551616) with (sz + -65 + 18446744073709551616) in K2 by (apply (Z.mod_unique _ _ (-1)); lia). lia. }
    do 11 zstep.
    probe8_regx 14%Z RDA A w1 P1. probe8_regx 15%Z RDA (A + sz + -1) w2 P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    - eapply LWS.
    - eapply LX1.
  Qed.
End Tail.

Definition iinet_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (A : Z) (N : nat) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (outs : list byte),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (A, A + Z.of_nat N)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ (accessible m' lo (q - lo) /\ sh_readable m' lo (q - lo))
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ rw_cells asegs m' A [CB N outs]
    /\ (r = 0 \/ r = 1).

Lemma inet_pton_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (af S A : Z) (str ojunk : list byte) (N : nat) (canary : word) (lo : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> rw_cells asegs m A [CB N ojunk] ->
  ((af = 2 /\ 4 <= Z.of_nat N) \/ (af = 10 /\ N = 16%nat)) ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  accessible m A (Z.of_nat N) -> sh_readable m A (Z.of_nat N) -> cwin A (Z.of_nat N) ->
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2160 - 80 - 2224 -> q <= 2^47 ->
  accessible m lo (q - lo) -> sh_readable m lo (q - lo) ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= lo -> 0x609000 <= A -> A + Z.of_nat N <= lo ->
  (A + Z.of_nat N <= S \/ S + Z.of_nat (length str) + 1 <= A) ->
  mem_inv asegs m -> a0 = wz af -> a1 = wz S -> a2 = wz A ->
  evt asegs (iinet_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str A N canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_inet_pton) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros STR OUT AF GOT GUARD ACCA RDA WINA IE ST KLO LO QH ACK RDK S1 S2 A1 A2 SEP MI -> -> ->.
  unfold A0_inet_pton. unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(lo, q); (A, A + Z.of_nat N)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 2160) by lia.
  assert (SAFE : env_band_safe [(lo, q); (A, A + Z.of_nat N)]) by (repeat (constructor; [cbn; lia|]); constructor).
  assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q); (A, A + Z.of_nat N)] s)
    by (intros s Hs; destruct WINA as [_ WA]; cbn [outside]; lia).
  assert (CWK : cwin lo (q - lo)) by (unfold cwin; lia).
  carve_frame 2160%nat ST.
  zstep. do 13 zstep. do 3 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (icpt_env_frame _ m m1 IE MU WM SAFE) as IE1 end.
  call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch _ m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_frame _ m m1 IE MU' WM' SAFE) as IE1;
      assert (ACK1 : accessible m1 lo (q - lo)) by (eapply accessible_munch; [exact ACK| exact MU'| exact CWK| intros s Hs; apply HO; lia]);
      assert (RDK1 : sh_readable m1 lo (q - lo)) by (eapply sh_readable_munch; [exact RDK| exact MU'| exact CWK| exact HO])
    end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_flags _ IE1) as FL1. pose proof (ie_real_lib _ IE1) as (_ & _ & RL1 & _).
  unfold env_cf in CF1. unfold env_flags in FL1.
  zstep. lit_branch.
  do 5 zstep. cbv beta. zsimp. zstep. lit_branch.
  do 6 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply inet_pton_callq with (lo := lo) (af := af) (S := S) (A := A) (str := str) (ojunk := ojunk) (N := N) (canary := canary);
      first [ eassumption | lia
            | (eapply accessible_sub; [exact ACK1| lia| lia]) | (eapply sh_readable_sub; [exact RDK1| lia| lia| lia]) | idtac ]
    | post_call asegs mm ] end.
  match goal with H : ?rr = 0 \/ ?rr = 1 |- _ => rename rr into r; rename H into HR end.
  match goal with H : u8arr asegs _ A ?oo, HL : length ?oo = N |- _ => rename oo into outs; rename H into OUTA; rename HL into LOUT end.
  clear IE1 ACK1 RDK1 CF1 FL1 RL1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU' : munch _ m mm, WM' : wmono asegs m mm |- _ =>
      pose proof (icpt_env_frame _ m mm IE MU' WM' SAFE) as IE2;
      assert (ACK2 : accessible mm lo (q - lo)) by (eapply accessible_munch; [exact ACK| exact MU'| exact CWK| intros s Hs; apply HO; lia]);
      assert (RDK2 : sh_readable mm lo (q - lo)) by (eapply sh_readable_munch; [exact RDK| exact MU'| exact CWK| exact HO]);
      assert (ACA2 : accessible mm A (Z.of_nat N)) by (eapply accessible_munch; [exact ACCA| exact MU'| exact WINA| intros s Hs; apply HO; lia]);
      assert (RDA2 : sh_readable mm A (Z.of_nat N)) by (eapply sh_readable_munch; [exact RDA| exact MU'| exact WINA| exact HO])
    end end.
  assert (OUTC : exists oo, rw_cells asegs _ A [CB N oo]) by (eexists; rewrite <- LOUT; apply rw_cells_of_u8arr; exact OUTA).
  zstep. zstep. destruct HR as [-> | ->]; lit_branch.
  -
    destruct OUTC as [oo OUTC].
    do 13 zstep.
    match goal with H : stk asegs _ lo (q + -2160) |- _ => release_frame FR H q end.
    finish.
    + exact OUTC.
    + left; reflexivity.
  -
    zstep. zstep.
    destruct OUTC as [oo OUTC].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CONT : forall sz, (sz = 4 \/ sz = 16) -> sz <= Z.of_nat N ->
      forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31,
      evt asegs (iinet_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str A N canary lo m)
        (MS (mkR y1 (wz (q + -2160)) gp tp y5 y6 y7 (wz q) (wz A) (wz sz) y11 y12 y13 y14 y15 y16 y17
                 y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
            F (wz 0x49d48) fc None mm (seg_rom asegs))) end.
    { intros sz HSZ HSN. intros.
      eapply evt_mono.
      { eapply (LB ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc _ A sz lo); try eassumption; try lia.
        - destruct WINA as [_ WA]. split; lia.
        - eapply accessible_sub; [exact ACA2| lia| lia].
        - eapply sh_readable_sub; [exact RDA2| lia| lia| lia]. }
      intros ms' Q. unfold inet_tpost in Q. unfold iinet_post.
      destruct Q as (y0' & y1' & y2' & y3' & y4' & y5' & y6' & y7' & y8' & y9' & y10' & y11' & y12' & y13' & m' & EQ & MU' & WM' & MI' & ST').
      exists y0', y1', y2', y3', y4', y5', y6', y7', y8', y9', y10', y11', y12', y13', m', 1, oo.
      assert (MUT : munch [(lo, q); (A, A + Z.of_nat N)] m m')
        by (eapply munch_trans; [eassumption|]; eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia).
      split; [exact EQ|]. split; [exact MUT|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact ST'|].
      split. { split; [eapply accessible_munch; [exact ACK| exact MUT| exact CWK| intros s Hs; apply HO; lia]
                      | eapply sh_readable_munch; [exact RDK| exact MUT| exact CWK| exact HO]]. }
      split. { eapply bytes_at_transport; [eassumption| exact MU'| rewrite length_app; cbn [length disjoint_from]; lia]. }
      split. { eapply rw_cells_transport; [eassumption| exact MU'| exact WM'| unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      split. { eapply rw_cells_transport; [eassumption| exact MU'| exact WM'| unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      split. { eapply rw_cells_transport; [exact OUTC| exact MU'| exact WM'| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      right; reflexivity. }
    destruct AF as [[-> HN] | [-> HN]].
    + zstep. zstep. lit_branch. zstep. zstep. eapply (CONT 4); [left; reflexivity| lia].
    + zstep. zstep. lit_branch. do 4 zstep. eapply (CONT 16); [right; reflexivity| lia].
Qed.
