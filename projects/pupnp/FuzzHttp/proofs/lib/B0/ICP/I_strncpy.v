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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_gates F_rip M_strnlen M_stpncpy.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition strncpyq_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ u8arr asegs m' D (stpn_result str (Z.to_nat n))
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Lemma strncpy_callq : forall ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D S n : Z) (str slack bs : list byte) (lo : Z),
  u8arr asegs m D bs -> length bs = Z.to_nat n ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  stk asegs m lo q -> lo <= q - 32 - 2224 -> q < 2^64 ->
  (D + n <= S \/ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D) ->
  D + n <= lo -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo -> 0 <= S -> 0 <= n ->
  mem_inv asegs m ->
  icpt_env m -> 0x10007fff8000 <= lo -> 0x147000 <= D ->
  accessible m D n -> sh_readable m D n -> cwin D n -> D + n < 2^47 -> n <= 2^43 ->
  evt asegs (strncpyq_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n str slack lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xa32f4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros DST LBS SRC NONUL PAD ST LO Q64 SEP SEPD SEPS S0 N0 MI IE KLO DBAND ACCD RDD WIND WD2 NSZ.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app in BS. cbn [length] in BS.
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; destruct ST as (L0 & _); lia).
  assert (UD : bv_unsigned (wz D) = D) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (wz n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strncpy_spec ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz n)) with (str := str) (slack := slack) (bs := bs) (lo := lo);
      rewrite ?UQ, ?UD, ?US, ?UN; first [ eassumption | lia ]. }
  intros ms' P. unfold strncpy_post in P. rewrite ?UQ, ?UD, ?US, ?UN in P. exact P.
Qed.

Definition istrncpy_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ u8arr asegs m' D (stpn_result str (Z.to_nat n))
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n lo : Z) (str slack dbs : list byte).
  Notation LEN := (Z.of_nat (length str)).
  Notation FULL := (str ++ Z_to_bv 8 0 :: slack).
  Notation FS := (Z.min n (LEN + 1)).
  Notation SAVES := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 2160 - 2256.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis RSC : rw_cells asegs m 0xacba8 [C8 (wz 0xa32f4)].
  Hypothesis DST : u8arr asegs m D dbs.
  Hypothesis DLEN : length dbs = Z.to_nat n.
  Hypothesis RN : 0 <= n < 2^31.
  Hypothesis SRC : bytes_at asegs m S FULL.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : (- (S + LEN + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis SEP : D + n <= S \/ S + LEN + 1 + Z.of_nat (length slack) <= D.
  Hypothesis SEPD : D + n <= lo.
  Hypothesis SEPS : S + LEN + 1 + Z.of_nat (length slack) <= lo.
  Hypothesis DBAND : 0x147000 <= D.
  Hypothesis SPOS : 0 < S.
  Hypothesis WINS : cwin S FS.   Hypothesis WINS2 : S + FS < 2^47.
  Hypothesis ACCS : accessible m S FS.   Hypothesis RDS : sh_readable m S FS.
  Hypothesis WIND : cwin D n.    Hypothesis WIND2 : D + n < 2^47.
  Hypothesis ACCD : accessible m D n.    Hypothesis RDD : sh_readable m D n.

  Notation APOST := (istrncpy_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n str slack lo m).
  Notation W := [(lo, q); (D, D + n)].

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2160) (CB 2080 jk :: SAVES))
    /\ stk asegs mc lo (q + -2160)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ u8arr asegs mc D dbs /\ bytes_at asegs mc S FULL
    /\ rw_cells asegs mc 0xacba8 [C8 (wz 0xa32f4)].
  Definition INV (mc : mem) : Prop := INVX mc /\ icpt_env mc.

  #[using="slack dbs LO KLO Q64 DLEN RN DBAND SPOS WINS2 WIND WIND2"] Lemma BL : 0 <= D /\ 0 < S /\ 0 <= n < 2^31 /\ 0 <= FS <= n /\ FS <= LEN + 1 /\ D + n < 2^47 /\ S + FS < 2^47 /\ 0 <= lo /\ q < 2^64
             /\ lo <= q - 4416 /\ 17594333495296 <= lo.
  Proof. destruct WIND as [_ W1]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & DST1 & SRC1 & RSC1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & IEc); invx_open IX;
    pose proof (ie_shadow _ IEc) as (GOT1 & SHB1); pose proof (ie_layout _ IEc) as (LG1 & LC1).

  #[using="LO KLO Q64 DLEN RN DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma facts : forall mc, INVX mc ->
    accessible mc S FS /\ sh_readable mc S FS /\ accessible mc D n /\ sh_readable mc D n.
  Proof.
    intros mc IV. invx_open IV. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [eapply accessible_munch; [exact ACCS| exact MU1| exact WINS| intros s Hs; apply HO; lia]|].
    split; [eapply sh_readable_munch; [exact RDS| exact MU1| exact WINS| exact HO]|].
    split; [eapply accessible_munch; [exact ACCD| exact MU1| exact WIND| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RDD| exact MU1| exact WIND| exact HO].
  Qed.

  #[using="LO KLO Q64 DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LX : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz S) (wz D) x20 x21 x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4bfe8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (_ & _ & ACD1 & RDD1). inv_open IV.
    apply (munch_weaken _ [(D, D + n); (lo, q)]) in MU1; [| unfold sub_fp; cbn [outside]; intros; lia].
    do 5 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply strncpy_callq with (lo := lo) (D := D) (S := S) (n := n) (str := str) (slack := slack) (bs := dbs);
        first [ eassumption | lia | idtac ]
      | post_call asegs mm ] end.
    do 13 zstep.
    lazymatch goal with H : stk asegs ?mm lo (q + -2160), FRH : rw_cells asegs ?mm (q + -2160) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => release_frame FRH H q end.
    finish.
    eapply munch_weaken; [| eassumption]. unfold sub_fp; cbn [outside]; intros; lia.
  Qed.

  #[using="LO KLO Q64 DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LWLd : forall mc (j : nat) (cur : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x24 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    Z.to_nat (sh (D + n - 1) - cur) = j -> sh D <= cur < sh (D + n - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) (wz cur) (wz (2147450880 + Z.shiftr (D + n + -1) 3)) (wz 0) x13 x14 x15 x16 x17
               (wz S) (wz D) x20 x21 x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c2c0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hj Hc. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (_ & _ & ACD1 & RDD1). inv_open IV.
    revert cur x13 Hj Hc. induction j as [|j IH]; intros cur x13 Hj Hc; [exfalso; lia|].
    assert (SL : sh (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (D + n + -1) with (D + n - 1) by lia; lia).
    pose proof (sh_div8 (D + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc D n cur ACD1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; exact IV0.
  Qed.

  #[using="LO KLO Q64 DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LWSd : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x24 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) (wz (2147450880 + Z.shiftr D 3)) (wz (2147450880 + Z.shiftr (D + n + -1) 3)) (wz (D + n + -1)) x13 x14 x15 x16 x17
               (wz S) (wz D) x20 x21 x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c2a4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (_ & _ & ACD1 & RDD1). inv_open IV.
    destruct (acc_byte_rd mc D n (D + n + -1) ACD1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((D + n + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (D + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; exact IV0.
    - eapply LWLd; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (D + n - 1) with (D + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= D / 8 < 2^44 /\ 0 <= (D + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      try (change 18446744073709551615 with (Z.ones 64) in K6; rewrite ?Z.land_ones in K6 by lia).
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 IE DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LBd : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz S) (wz D) x20 x21 x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4bf98) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (_ & _ & ACD1 & RDD1). inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      assert (N65 : 64 < n) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIND as [_ W9]; unfold rwin; lia | exact ACD1 | lia |].
      zstep. lit_branch.
      eapply LX. split.
      + unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
      + match goal with MU' : munch [(lo, q)] m ?mm, WM' : wmono asegs m ?mm |- icpt_env ?mm => eapply icpt_env_stack; [exact IE| exact MU'| exact WM'| lia] end.
    -
      assert (N1 : 1 <= n <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_regx 13%Z RDD1 D w1 P1. probe8_regx 14%Z RDD1 (D + n + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSd; eassumption.
      + eapply LX; exact IV0.
  Qed.

  #[using="LO KLO Q64 IE DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LWLs : forall mc (j : nat) (cur : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x24 x28 x29 x30 x31,
    INV mc -> 1 <= FS <= 64 ->
    Z.to_nat (sh (S + FS - 1) - cur) = j -> sh S <= cur < sh (S + FS - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) (wz cur) (wz (2147450880 + Z.shiftr (S + FS + -1) 3)) (wz 0) x13 x14 x15 x16 x17
               (wz S) (wz D) (wz FS) x21 x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c1f8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hj Hc. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (ACS1 & RDS1 & _ & _). inv_open IV.
    revert cur x13 Hj Hc. induction j as [|j IH]; intros cur x13 Hj Hc; [exfalso; lia|].
    assert (SL : sh (S + FS - 1) = 2147450880 + Z.shiftr (S + FS + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (S + FS + -1) with (S + FS - 1) by lia; lia).
    pose proof (sh_div8 (S + FS - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S FS cur ACS1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LBd; exact IV0.
  Qed.

  #[using="LO KLO Q64 IE DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LWSs : forall mc x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x22 x24 x28 x29 x30 x31,
    INV mc -> 1 <= FS <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) (wz (2147450880 + Z.shiftr S 3)) (wz (2147450880 + Z.shiftr (S + FS + -1) 3)) x12 x13 x14 x15 x16 x17
               (wz S) (wz D) (wz FS) (wz (S + FS + -1)) x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c1dc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (ACS1 & RDS1 & _ & _). inv_open IV.
    destruct (acc_byte_rd mc S FS (S + FS + -1) ACS1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((S + FS + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (S + FS + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LBd; exact IV0.
    - eapply LWLs; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (S + FS - 1) with (S + FS + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= S / 8 < 2^44 /\ 0 <= (S + FS + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      try (change 18446744073709551615 with (Z.ones 64) in K6; rewrite ?Z.land_ones in K6 by lia).
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 IE DLEN RN NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma LBs : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz S) (wz D) (wz FS) (wz (S + FS)) x22 (wz 0xacb88) x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4bf4c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts mc (proj1 IV)) as (ACS1 & RDS1 & _ & _). inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LBd; exact IV0. }
      assert (N65 : 64 < FS) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WINS as [_ W9]; unfold rwin; lia | exact ACS1 | lia |].
      zstep. lit_branch.
      eapply LBd. split.
      + unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
      + match goal with MU' : munch [(lo, q)] m ?mm, WM' : wmono asegs m ?mm |- icpt_env ?mm => eapply icpt_env_stack; [exact IE| exact MU'| exact WM'| lia] end.
    -
      assert (N1 : 1 <= FS <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 10 zstep.
      probe8_regx 12%Z RDS1 S w1 P1. probe8_regx 13%Z RDS1 (S + FS + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSs; eassumption.
      + eapply LBd; exact IV0.
  Qed.

  #[using="RN NONUL SPOS"] Lemma fs_snl : snl_sz S n FULL = FS.
  Proof. rewrite snl_sz_min by lia. rewrite (strnlen_res_cstr S n str slack NONUL). lia. Qed.

  #[using="dbs MI ST LO KLO Q64 IE RSC DST DLEN RN SRC NONUL PAD SEP SEPD SEPS DBAND SPOS WINS WINS2 ACCS RDS WIND WIND2 ACCD RDD"] Lemma istrncpy_body : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, a0 = wz D -> a1 = wz S -> a2 = wz n ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_strncpy) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros -> -> ->. unfold A0_strncpy. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2160) by lia.
    pose proof ST as ST0. ihide DST. ihide SRC. ihide RSC.
    carve_frame 2160%nat ST0.
    zstep. do 13 zstep. do 3 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
    call ensure_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
    clear IE1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1;
        assert (DST1 : u8arr asegs m1 D dbs) by (iunhide DST; eapply u8arr_transport; [exact DST| exact MU'| exact WM'| cbn [disjoint_from]; lia]);
        assert (SRC1 : bytes_at asegs m1 S FULL) by (iunhide SRC; eapply bytes_at_transport; [exact SRC| exact MU'| rewrite length_app; cbn [length disjoint_from]; lia]);
        assert (RSC1 : rw_cells asegs m1 0xacba8 [C8 (wz 0xa32f4)]) by (iunhide RSC; eapply rw_cells_transport; [exact RSC| exact MU'| exact WM'| cbn [disjoint_from cells_size csize Nat.add]; lia])
      end end.
    pose proof (ie_cf _ IE1) as CF1. pose proof (ie_aflags _ IE1) as AF1. pose proof (ie_real_str _ IE1) as (_ & _ & RS1).
    unfold env_cf in CF1. unfold env_aflags in AF1.
    do 5 zstep. zstep. lit_branch.
    zstep. zstep. lit_branch.
    do 3 zstep.
    assert (IV : INV _) by (split; [unfold INVX; split; [eexists; eassumption|]; repeat (split; [eassumption|]); assumption | exact IE1]).
    destruct (facts _ (proj1 IV)) as (ACS1 & RDS1 & _ & _).
    pose proof fs_snl as ESZ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply strnlen_a_spec with (lo := lo) (P := S) (n := n) (buf := FULL);
        rewrite ?ESZ;
        first [ eassumption | exact (memchr_ok_cstr S n str slack NONUL PAD) | reflexivity | (rewrite length_app; cbn [length]; lia) | lia | idtac ]
      | post_call asegs mm ] end.
    rewrite (strnlen_res_cstr S n str slack NONUL).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (IV2 : INV mm) end.
    { split; [unfold INVX; split; [eexists; eassumption|]; repeat (split; [eassumption|]); assumption |].
      match goal with MU' : munch [(lo, q)] m ?mm, WM' : wmono asegs m ?mm |- icpt_env ?mm => eapply icpt_env_stack; [exact IE| exact MU'| exact WM'| lia] end. }
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CONT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y24 y28 y29 y30 y31,
      evt asegs APOST
        (MS (mkR y1 (wz (q + -2160)) gp tp y5 y6 y7 (wz q) (wz n) y10 y11 y12 y13 y14 y15 y16 y17
                 (wz S) (wz D) (wz FS) y21 y22 (wz 0xacb88) y24 s9 s10 s11 y28 y29 y30 y31)
            F (wz 0x4bf34) fc None mm (seg_rom asegs))) end.
    { intros. do 4 zstep. zstep. if_cases KO1; zify_cond KO1.
      - eapply LBs; exact IV2.
      - zstep. if_cases KO2; zify_cond KO2. { exfalso. lia. }
        eapply LBs; exact IV2. }
    if_cases KM; zify_cond KM.
    - replace (Z_to_bv 64 n) with (Z_to_bv 64 FS) at 2 by (f_equal; lia).
      eapply CONT.
    - zstep. replace (LEN `min` n + 1) with FS by lia.
      eapply CONT.
  Qed.
End Proofs.

Lemma strncpy_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n : Z) (str slack dbs : list byte) (lo : Z),
  u8arr asegs m D dbs -> length dbs = Z.to_nat n -> 0 <= n < 2^31 ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  accessible m S (Z.min n (Z.of_nat (length str) + 1)) -> sh_readable m S (Z.min n (Z.of_nat (length str) + 1)) ->
  cwin S (Z.min n (Z.of_nat (length str) + 1)) -> S + Z.min n (Z.of_nat (length str) + 1) < 2^47 ->
  accessible m D n -> sh_readable m D n -> cwin D n -> D + n < 2^47 ->
  icpt_env m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2160 - 2256 -> q < 2^64 ->
  0x147000 <= D -> D + n <= lo -> 0 < S -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo ->
  (D + n <= S \/ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D) ->
  mem_inv asegs m -> a0 = wz D -> a1 = wz S -> a2 = wz n ->
  evt asegs (istrncpy_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n str slack lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strncpy) fc None m (seg_rom asegs)).
Proof.
  intros. eapply istrncpy_body with (dbs := dbs); try eassumption.
  match goal with IE : icpt_env _ |- _ => exact (ie_real_lib2 _ IE) end.
Qed.
