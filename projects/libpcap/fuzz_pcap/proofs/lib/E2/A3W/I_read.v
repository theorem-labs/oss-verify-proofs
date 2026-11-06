(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
(* [comment removed for export] *)
Local Ltac zify_lts K ::=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (first [ solve [ clear; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]);
  zify_bool K.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
(* [comment removed for export] *)
Local Ltac solve_acc_shadow H ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        first [ solve [ zify_prune; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]
      end
  end.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
(* [comment removed for export] *)
Local Lemma rw_cells_app_fr : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1))%Z cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (nd_pre WR 3%nat; intros HA HN HW; nd_post).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition read_i_entry := 0x463c4%Z.

(* [comment removed for export] *)
Definition read_i_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z).
  Notation B := (bv_unsigned a1).
  Notation W := [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (errno_addr tp, errno_addr tp + 4)]%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_read m.
  Hypothesis DST : rw_cells asegs m B [CB (Z.to_nat count) junk].
  Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
  Hypothesis A0 : a0 = Z_to_bv 64 fd.
  Hypothesis A2 : a2 = Z_to_bv 64 count.
  Hypothesis FD : (3 <= fd < 2^32)%Z.
  Hypothesis CNT : (1 <= count <= 16777216)%Z.
  (* [comment removed for export] *)
  Hypothesis BHI : (0x603000 <= B \/ (0x5d0c50 <= B /\ B + count <= 0x603000))%Z.      (* [comment removed for export] *)
  Hypothesis SEPD : (B + count <= lo)%Z.                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (ke ks kb : Z).
  Hypothesis SEPE : (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1514)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (B + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= B + (1 - kb) * 18446744073709551616))%Z.
  Hypothesis TP : (164 <= bv_unsigned tp)%Z.
  Hypothesis APPD : app_blk B (B + count).
  Hypothesis UDST : unpoisoned m B (B + count).
  Hypothesis R2 : (RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (errno_addr tp) 4.
  Hypothesis RD : rng RNG B count.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m).

  (* [comment removed for export] *)
  Definition INV2 (bs : list byte) (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2128)
    /\ munch W m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_read mc
    /\ unpoisoned mc B (B + count)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
    /\ rw_cells asegs mc (errno_addr tp) [C4 errv]
    /\ (length bs <= Z.to_nat count)%nat.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 1 <= count <= 16777216
     /\ 0x5d0c50 <= B /\ B + count <= lo /\ B + count + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr B 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
     /\ (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1514)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (B + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= B + (1 - kb) * 18446744073709551616)))%Z.

  #[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed.

  Ltac acc_facts Bf ::= pose proof BND_ok as Bf; unfold BND, KHIGH, KEND in Bf.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 1 <= count <= 16777216 /\ 0x5d0c50 <= B /\ B + count <= lo
     /\ B + count + 8 <= 2^47 /\ 0 <= Z.shiftr B 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
     /\ (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1514)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (B + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= B + (1 - kb) * 18446744073709551616)))%Z.
  #[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    (nd_pre H 15%nat; intros (jk & FR) ST1 MU1 WM1 MI1 GOT1 SHB1 INI1 LAY1 REAL1 UD1 WR21 BUF1 ERR1 LENB; nd_post).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let Bl := fresh "BL" in pose proof BL_ok as Bl; unfold BL in Bl;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in ERR; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.

  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2"] Lemma inv2_of : forall bs mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2128) ->
    munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_read mc ->
    rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] ->
    rw_cells asegs mc (errno_addr tp) [C4 errv] -> (length bs <= Z.to_nat count)%nat ->
    INV2 bs mc.
  Proof.
    intros bs mc jk FR ST1 MU1 WM1 MI1 G1 G3 G4 G5 G6 BUF1 ERR1 LENB. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : (shad (B + count - 1) + 1 <= 17594333495296 /\ 2147450880 <= shad B /\
                  (B + count <= shad B \/ shad (B + count - 1) + 1 <= B))%Z).
    { pose proof APPD as [_ AD]. unfold KLOW, KHIGH, KEND in AD. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD R2 RSTK"] Lemma LX : forall bs mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x46474) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 9 zstep.
    release_frame FR ST1 (bv_unsigned sp). unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD R2 RSTK RSH2"] Lemma LSL : forall bs mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    Z.to_nat (shad (B + Z.of_nat (length bs) - 1) - c) = k -> (shad B <= c < shad (B + Z.of_nat (length bs) - 1))%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x465d8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (B + Z.of_nat (length bs) - 1) = 2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)%Z)
      by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc B (B + count) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD R2 RSTK RSH2"] Lemma LSS : forall bs mc x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 (2147450880 + Z.shiftr B 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3))
               (Z_to_bv 64 (B + Z.of_nat (length bs) + -1)) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x465bc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    pose proof (shad_mono B (B + Z.of_nat (length bs) - 1) ltac:(lia)) as SM2.
    (nd_pre (unpoisoned_check_rd asegs mc B (B + count) (B + Z.of_nat (length bs) + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(Z.div_mod_to_equations; lia)) 3%nat; intros b2 RD2 CK2; nd_post).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((B + Z.of_nat (length bs) + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LSL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Definition LC__stmt : Prop := forall bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x46414) fc None mc (seg_rom asegs)).
  Section Zd1.   (* [comment removed for export] *)
  Variable bs : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 0).
  Variable mc : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 1).
  Variable x1 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 2).
  Variable x5 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 3).
  Variable x6 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 4).
  Variable x7 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 5).
  Variable x11 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 6).
  Variable x12 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 7).
  Variable x13 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 8).
  Variable x14 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 9).
  Variable x15 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 10).
  Variable x16 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 11).
  Variable x17 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 12).
  Variable x18 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 13).
  Variable x19 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 14).
  Variable x28 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 15).
  Variable x29 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 16).
  Variable x30 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 17).
  Variable x31 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 18).
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2 RI RSTK RSH2"] Lemma LC__body : ltac:(let T := type of (fun (h : LC__stmt) => h bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (bs, (mc, (x1, (x5, (x6, (x7, (x11, (x12, (x13, (x14, (x15, (x16, (x17, (x18, (x19, (x28, (x29, (x30, x31))))))))))))))))))) as _.
 intros IV. prep IV.
    assert (Rr : (0 <= Z.of_nat (length bs) <= count)%Z) by lia.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. if_cases KZ; zify_lts KZ.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (R1' : (1 <= Z.of_nat (length bs))%Z) by lia.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      do 4 zstep.
      unfold sf_hide in DST. (* [comment removed for export] *)
      pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; eapply app_blk_sub; [exact APPD | lia | lia | lia]
        | zsimp; eapply unpoisoned_sub; [exact UD1 | lia | lia]
        | zsimp; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 3 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv2_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (Z.of_nat (length bs) <= 64)%Z) by (clear - K2 Rr R1' BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 B WR21 ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (B + Z.of_nat (length bs) + -1) WR21
                  ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LSS; [eassumption | lia].
      + eapply LX; eassumption.
  Qed.
  End Zd1.
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2 RI RSTK RSH2"] Lemma LC : ltac:(let t := eval cbv delta [LC__stmt] in LC__stmt in exact t).
  Proof. exact LC__body. Qed.

  (* [comment removed for export] *)
  #[using="RLO2 RHI2 MI ST LO KLO GOT SHB INI LAY REAL DST ERR A0 A2 FD CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2 RI RSTK RERR RD RSH2"] Lemma read_i_body :
    implA asegs ASHM RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
          (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x463c4) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    pose proof DST as DST0. change (?P) with (sf_hide P) in DST. pose proof ERR as ERR0. change (?P) with (sf_hide P) in ERR.
    rewrite A0, A2.
    iprefix.
    carve_frame 2128%nat ST0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk0] =>
      apply (rw_cells_split_CB asegs m _ [] 2128 jk0 [] [2080%nat; 48%nat]) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR;
      set (jk1 := firstn 2080 jk0) in FR; set (jk2 := firstn 48 (skipn 2080 jk0)) in FR; clearbody jk1 jk2; clear jk0 end.
    change [CB 2080 jk1; CB 48 jk2] with ([CB 2080 jk1] ++ [CB 48 jk2]) in FR.
    apply rw_cells_app_fr in FR. destruct FR as [FR FR2].
    change (Z.of_nat (cells_size [CB 2080 jk1])) with 2080%Z in FR2.
    replace (bv_unsigned sp + -2128 + 2080)%Z with (bv_unsigned sp + -48)%Z in FR2 by lia.
    do 9 zstep. do 3 zstep. zstep.
    call_sp tryinit_spec; [ assumption | exact ST0 | lia | unfold KHIGH; lia | assumption | eapply rng_sub'; [exact RSTK | lia] | ].
    do 6 zstep. zstep.
    name_sp sp (-2128)%Z.
    Local Ltac usp := match goal with H : bv_unsigned _ = (bv_unsigned sp + -2128)%Z |- _ => rewrite H end.
    icallk read_spec;
      [ usp; eassumption | eassumption | eassumption | assumption | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia
      | usp; eapply rng_sub'; [exact RSTK | lia] | ].
    ipost asegs. unname_sp.
    lazymatch goal with P : context [match ?a with RdErr _ => _ | RdData _ => _ end] |- _ => rename P into RP end.
    lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -2128) [CB 2080 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -48) ?cs |- _ =>
      assert (FRJ : rw_cells asegs mm (bv_unsigned sp + -2128) ([CB 2080 j] ++ cs))
        by (apply rw_cells_app_fr; split; [exact H1 | change (Z.of_nat (cells_size [CB 2080 j])) with 2080%Z;
                                                     replace (bv_unsigned sp + -2128 + 2080)%Z with (bv_unsigned sp + -48)%Z by lia; exact H2]);
      cbn [app] in FRJ; clear H1 H2; rename FRJ into FR end.
    destruct ans as [e|bs]; cbn [read_ret].
    - (* [comment removed for export] *)
      (nd_pre RP 3%nat; intros BUFe ERRe He; nd_post).
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
      zstep. if_cases KZ; zify_lts KZ. 2:{ exfalso. clear - KZ. lia. }
      do 9 zstep.
      lazymatch goal with ST2 : stk asegs _ lo _ |- _ => release_frame FR ST2 (bv_unsigned sp) end.
      unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish; lia.
    - (* [comment removed for export] *)
      (nd_pre RP 3%nat; intros BUF1 ERR1 LENB; nd_post).
      eapply LC. eapply inv2_of; try eassumption.
  Qed.
End Proofs.

#[using="Type"] Lemma read_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z) (ke ks kb : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_read m ->
  rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (0x603000 <= bv_unsigned a1 \/ (0x5d0c50 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= 0x603000))%Z -> (bv_unsigned a1 + count <= lo)%Z ->
  (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1514)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (bv_unsigned a1 + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= bv_unsigned a1 + (1 - kb) * 18446744073709551616))%Z -> (164 <= bv_unsigned tp)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + count) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + count) ->
  (RLO2 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (errno_addr tp) 4 -> rng RNG (bv_unsigned a1) count ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  implA asegs ASHM RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x463c4) fc None m (seg_rom asegs)).
Proof. intros. eapply read_i_body; eassumption. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
(* [comment removed for export] *)
Local Ltac zify_lts K ::=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (first [ solve [ clear; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]);
  zify_bool K.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
(* [comment removed for export] *)
Local Ltac solve_acc_shadow H ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        first [ solve [ zify_prune; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]
      end
  end.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
(* [comment removed for export] *)
Local Lemma rw_cells_app_fr : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1))%Z cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (nd_pre WR 3%nat; intros HA HN HW; nd_post).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition read_i_entry := 0x4642c%Z.

(* [comment removed for export] *)
Definition read_i_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z).
  Notation B := (bv_unsigned a1).
  Notation W := [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (errno_addr tp, errno_addr tp + 4)]%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_read m.
  Hypothesis DST : rw_cells asegs m B [CB (Z.to_nat count) junk].
  Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
  Hypothesis A0 : a0 = Z_to_bv 64 fd.
  Hypothesis A2 : a2 = Z_to_bv 64 count.
  Hypothesis FD : (3 <= fd < 2^32)%Z.
  Hypothesis CNT : (1 <= count <= 16777216)%Z.
  (* [comment removed for export] *)
  Hypothesis BHI : (0x604000 <= B \/ (0x5d1050 <= B /\ B + count <= 0x604000))%Z.      (* [comment removed for export] *)
  Hypothesis SEPD : (B + count <= lo)%Z.                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (ke ks kb : Z).
  Hypothesis SEPE : (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1914)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (B + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= B + (1 - kb) * 18446744073709551616))%Z.
  Hypothesis TP : (164 <= bv_unsigned tp)%Z.
  Hypothesis APPD : app_blk B (B + count).
  Hypothesis UDST : unpoisoned m B (B + count).
  Hypothesis R2 : (RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (errno_addr tp) 4.
  Hypothesis RD : rng RNG B count.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m).

  (* [comment removed for export] *)
  Definition INV2 (bs : list byte) (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2128)
    /\ munch W m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_read mc
    /\ unpoisoned mc B (B + count)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
    /\ rw_cells asegs mc (errno_addr tp) [C4 errv]
    /\ (length bs <= Z.to_nat count)%nat.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 1 <= count <= 16777216
     /\ 0x5d1050 <= B /\ B + count <= lo /\ B + count + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr B 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
     /\ (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1914)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (B + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= B + (1 - kb) * 18446744073709551616)))%Z.

  #[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed.

  Ltac acc_facts Bf ::= pose proof BND_ok as Bf; unfold BND, KHIGH, KEND in Bf.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 1 <= count <= 16777216 /\ 0x5d1050 <= B /\ B + count <= lo
     /\ B + count + 8 <= 2^47 /\ 0 <= Z.shiftr B 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
     /\ (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1914)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (B + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= B + (1 - kb) * 18446744073709551616)))%Z.
  #[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    (nd_pre H 15%nat; intros (jk & FR) ST1 MU1 WM1 MI1 GOT1 SHB1 INI1 LAY1 REAL1 UD1 WR21 BUF1 ERR1 LENB; nd_post).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let Bl := fresh "BL" in pose proof BL_ok as Bl; unfold BL in Bl;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in ERR; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.

  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2"] Lemma inv2_of : forall bs mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2128) ->
    munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_read mc ->
    rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] ->
    rw_cells asegs mc (errno_addr tp) [C4 errv] -> (length bs <= Z.to_nat count)%nat ->
    INV2 bs mc.
  Proof.
    intros bs mc jk FR ST1 MU1 WM1 MI1 G1 G3 G4 G5 G6 BUF1 ERR1 LENB. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : (shad (B + count - 1) + 1 <= 17594333495296 /\ 2147450880 <= shad B /\
                  (B + count <= shad B \/ shad (B + count - 1) + 1 <= B))%Z).
    { pose proof APPD as [_ AD]. unfold KLOW, KHIGH, KEND in AD. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD R2 RSTK"] Lemma LX : forall bs mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x464dc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 9 zstep.
    release_frame FR ST1 (bv_unsigned sp). unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD R2 RSTK RSH2"] Lemma LSL : forall bs mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    Z.to_nat (shad (B + Z.of_nat (length bs) - 1) - c) = k -> (shad B <= c < shad (B + Z.of_nat (length bs) - 1))%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x46640) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (B + Z.of_nat (length bs) - 1) = 2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)%Z)
      by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc B (B + count) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD R2 RSTK RSH2"] Lemma LSS : forall bs mc x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 (2147450880 + Z.shiftr B 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3))
               (Z_to_bv 64 (B + Z.of_nat (length bs) + -1)) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x46624) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    pose proof (shad_mono B (B + Z.of_nat (length bs) - 1) ltac:(lia)) as SM2.
    (nd_pre (unpoisoned_check_rd asegs mc B (B + count) (B + Z.of_nat (length bs) + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(Z.div_mod_to_equations; lia)) 3%nat; intros b2 RD2 CK2; nd_post).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((B + Z.of_nat (length bs) + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LSL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Definition LC__stmt : Prop := forall bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4647c) fc None mc (seg_rom asegs)).
  Section Zd1.   (* [comment removed for export] *)
  Variable bs : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 0).
  Variable mc : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 1).
  Variable x1 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 2).
  Variable x5 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 3).
  Variable x6 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 4).
  Variable x7 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 5).
  Variable x11 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 6).
  Variable x12 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 7).
  Variable x13 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 8).
  Variable x14 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 9).
  Variable x15 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 10).
  Variable x16 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 11).
  Variable x17 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 12).
  Variable x18 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 13).
  Variable x19 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 14).
  Variable x28 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 15).
  Variable x29 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 16).
  Variable x30 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 17).
  Variable x31 : ltac2:(SecDietF.SzSecF.ty 'LC__stmt 18).
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2 RI RSTK RSH2"] Lemma LC__body : ltac:(let T := type of (fun (h : LC__stmt) => h bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (bs, (mc, (x1, (x5, (x6, (x7, (x11, (x12, (x13, (x14, (x15, (x16, (x17, (x18, (x19, (x28, (x29, (x30, x31))))))))))))))))))) as _.
 intros IV. prep IV.
    assert (Rr : (0 <= Z.of_nat (length bs) <= count)%Z) by lia.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. if_cases KZ; zify_lts KZ.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (R1' : (1 <= Z.of_nat (length bs))%Z) by lia.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      do 4 zstep.
      unfold sf_hide in DST. (* [comment removed for export] *)
      pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; eapply app_blk_sub; [exact APPD | lia | lia | lia]
        | zsimp; eapply unpoisoned_sub; [exact UD1 | lia | lia]
        | zsimp; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 3 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv2_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (Z.of_nat (length bs) <= 64)%Z) by (clear - K2 Rr R1' BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 B WR21 ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (B + Z.of_nat (length bs) + -1) WR21
                  ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LSS; [eassumption | lia].
      + eapply LX; eassumption.
  Qed.
  End Zd1.
  #[using="ST LO KLO CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2 RI RSTK RSH2"] Lemma LC : ltac:(let t := eval cbv delta [LC__stmt] in LC__stmt in exact t).
  Proof. exact LC__body. Qed.

  (* [comment removed for export] *)
  #[using="RLO2 RHI2 MI ST LO KLO GOT SHB INI LAY REAL DST ERR A0 A2 FD CNT BHI SEPD ke ks kb SEPE APPD UDST R2 WR2 RI RSTK RERR RD RSH2"] Lemma read_i_body :
    implA asegs ASHM RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
          (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x4642c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    pose proof DST as DST0. change (?P) with (sf_hide P) in DST. pose proof ERR as ERR0. change (?P) with (sf_hide P) in ERR.
    rewrite A0, A2.
    iprefix.
    carve_frame 2128%nat ST0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk0] =>
      apply (rw_cells_split_CB asegs m _ [] 2128 jk0 [] [2080%nat; 48%nat]) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR;
      set (jk1 := firstn 2080 jk0) in FR; set (jk2 := firstn 48 (skipn 2080 jk0)) in FR; clearbody jk1 jk2; clear jk0 end.
    change [CB 2080 jk1; CB 48 jk2] with ([CB 2080 jk1] ++ [CB 48 jk2]) in FR.
    apply rw_cells_app_fr in FR. destruct FR as [FR FR2].
    change (Z.of_nat (cells_size [CB 2080 jk1])) with 2080%Z in FR2.
    replace (bv_unsigned sp + -2128 + 2080)%Z with (bv_unsigned sp + -48)%Z in FR2 by lia.
    do 9 zstep. do 3 zstep. zstep.
    call_sp tryinit_spec; [ assumption | exact ST0 | lia | unfold KHIGH; lia | assumption | eapply rng_sub'; [exact RSTK | lia] | ].
    do 6 zstep. zstep.
    name_sp sp (-2128)%Z.
    Local Ltac usp := match goal with H : bv_unsigned _ = (bv_unsigned sp + -2128)%Z |- _ => rewrite H end.
    icallk read_spec;
      [ usp; eassumption | eassumption | eassumption | assumption | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia
      | usp; eapply rng_sub'; [exact RSTK | lia] | ].
    ipost asegs. unname_sp.
    lazymatch goal with P : context [match ?a with RdErr _ => _ | RdData _ => _ end] |- _ => rename P into RP end.
    lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -2128) [CB 2080 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -48) ?cs |- _ =>
      assert (FRJ : rw_cells asegs mm (bv_unsigned sp + -2128) ([CB 2080 j] ++ cs))
        by (apply rw_cells_app_fr; split; [exact H1 | change (Z.of_nat (cells_size [CB 2080 j])) with 2080%Z;
                                                     replace (bv_unsigned sp + -2128 + 2080)%Z with (bv_unsigned sp + -48)%Z by lia; exact H2]);
      cbn [app] in FRJ; clear H1 H2; rename FRJ into FR end.
    destruct ans as [e|bs]; cbn [read_ret].
    - (* [comment removed for export] *)
      (nd_pre RP 3%nat; intros BUFe ERRe He; nd_post).
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
      zstep. if_cases KZ; zify_lts KZ. 2:{ exfalso. clear - KZ. lia. }
      do 9 zstep.
      lazymatch goal with ST2 : stk asegs _ lo _ |- _ => release_frame FR ST2 (bv_unsigned sp) end.
      unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish; lia.
    - (* [comment removed for export] *)
      (nd_pre RP 3%nat; intros BUF1 ERR1 LENB; nd_post).
      eapply LC. eapply inv2_of; try eassumption.
  Qed.
End Proofs.

#[using="Type"] Lemma read_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z) (ke ks kb : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_read m ->
  rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (0x604000 <= bv_unsigned a1 \/ (0x5d1050 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= 0x604000))%Z -> (bv_unsigned a1 + count <= lo)%Z ->
  (4096 <= errno_addr tp /\ errno_addr tp + 4 <= lo /\ (0 <= ke <= 1 /\ 0 <= ks <= 1 /\ 0 <= kb <= 1)
     /\ (ke = 0 /\ errno_addr tp = 0x5e1914)
     /\ (errno_addr tp + 4 <= 0x7fff7000 + ks * 18446744073709551616 /\ 0x10007fff8000 * ks <= errno_addr tp)
     /\ (bv_unsigned a1 + count <= errno_addr tp + kb * 18446744073709551616 /\ errno_addr tp + 4 <= bv_unsigned a1 + (1 - kb) * 18446744073709551616))%Z -> (164 <= bv_unsigned tp)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + count) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + count) ->
  (RLO2 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (errno_addr tp) 4 -> rng RNG (bv_unsigned a1) count ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  implA asegs ASHM RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x4642c) fc None m (seg_rom asegs)).
Proof. intros. eapply read_i_body; eassumption. Qed.
End CANSEC1.
End TwB.
