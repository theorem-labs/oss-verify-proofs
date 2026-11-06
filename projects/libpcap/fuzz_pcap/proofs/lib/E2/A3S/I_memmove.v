(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells ShadowTac F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[2072%nat] => let t1 := context C[Z.to_nat 2072] in natfold_term t1
  | context C[2144%nat] => let t1 := context C[Z.to_nat 2144] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [2072%nat] |- _ => natfold_hyp nfH
  | nfH : context [2144%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [2072%nat] => natfold_concl
  | |- context [2144%nat] => natfold_concl
  | |- _ => idtac
  end.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition mmv (k n : nat) (bs : list byte) : list byte := firstn n (skipn k bs) ++ skipn n bs.
Lemma mmv_length : forall k n bs, length bs = (k + n)%nat -> length (mmv k n bs) = (k + n)%nat.
Proof. all: natfold_lits. intros k n bs L. unfold mmv. rewrite length_app, length_firstn, !length_skipn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition imemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (k n : nat) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (k + n) (mmv k n bs)].

Section Memmove.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k n : nat) (bs : list byte).
  Notation D := (bv_unsigned a0).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis REG : rw_cells asegs m D [CB (k + n) bs].
  Hypothesis HK : (1 <= k)%nat.
  Hypothesis A1 : a1 = Z_to_bv 64 (D + Z.of_nat k).
  Hypothesis A2 : a2 = Z_to_bv 64 (Z.of_nat n).
  Hypothesis SMALL : (D + Z.of_nat (k + n) < 2^63)%Z.
  Hypothesis RR : rng RNG D (Z.of_nat (k + n)).
  Notation POST := (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D k n bs m).

  (* [comment removed for export] *)
  #[using="REG HK SMALL RR"] Lemma imemmove_loop : forall (c : nat) (i : Z) (mc : word -> option byte) (cur : list byte) (x11 x13 x14 : word),
    x11 = Z_to_bv 64 (D + Z.of_nat k + i) -> x13 = Z_to_bv 64 (D + i) ->
    Z.to_nat (Z.of_nat n - i) = c -> (0 <= i < Z.of_nat n)%Z ->
    u8arr asegs mc D cur -> length cur = (k + n)%nat ->
    (forall j, (j < Z.to_nat i)%nat -> nth_error cur j = nth_error bs (k + j)) ->
    (forall j, (Z.to_nat i <= j)%nat -> nth_error cur j = nth_error bs j) ->
    munch [(D, D + Z.of_nat n)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 (Z_to_bv 64 (D + Z.of_nat n)) x13 x14 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67a50) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    pose proof (rw_cells_bound _ _ _ _ REG) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LBS : length bs = (k + n)%nat) by (destruct REG as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    induction c as [|c IH]; intros i mc cur x11 x13 x14 -> -> Hc Hi ARR LCUR DONE REST MU WM MI1; [exfalso; lia|].
    destruct (nth_error bs (k + Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (NBc : nth_error cur (Z.to_nat (Z.of_nat k + i)) = Some b).
    { replace (Z.to_nat (Z.of_nat k + i)) with (k + Z.to_nat i)%nat by lia. rewrite REST by lia. exact NB. }
    pose proof (u8arr_read asegs mc D cur (Z.of_nat k + i) b (wa (D + Z.of_nat k + i)) ARR NBc ltac:(lia) ltac:(f_equal; lia)) as RDb.
    zstep. cbv beta.
    pose proof (u8arr_store_ok asegs mc D cur i (wa (D + i)) ARR ltac:(rewrite LCUR; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write asegs mc D cur i b ARR ltac:(rewrite LCUR; lia)) as ARR'.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    store_done.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - eapply (IH (i + 1)%Z); [f_equal; lia | f_equal; lia | lia | lia | exact ARR' | rewrite Arr.upd_length; exact LCUR | | | assumption | assumption | assumption].
      + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LCUR; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
      + intros j Hj. rewrite Arr.nth_error_upd_other by lia. apply REST. lia.
    - zstep. zstep.
      assert (E : upd cur (Z.to_nat i) b = mmv k n bs).
      { assert (EI : Z.to_nat i = (n - 1)%nat) by lia.
        apply nth_error_ext. intros j. unfold mmv.
        destruct (Nat.lt_ge_cases j n) as [LT|GE].
        - rewrite nth_error_app1 by (rewrite length_firstn, length_skipn; lia).
          rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact LT). rewrite nth_error_skipn.
          destruct (Nat.eq_dec j (Z.to_nat i)).
          + subst j. rewrite Arr.nth_error_upd_same by (rewrite LCUR; lia). symmetry; exact NB.
          + rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
        - rewrite nth_error_app2 by (rewrite length_firstn, length_skipn; lia).
          rewrite length_firstn, length_skipn. replace (Nat.min n (length bs - k)) with n by lia.
          rewrite nth_error_skipn. replace (n + (j - n))%nat with j by lia.
          rewrite Arr.nth_error_upd_other by lia. apply REST. lia. }
      rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. rewrite mmv_length in ARR' by exact LBS. finish.
  Qed.

  #[using="MI REG HK A1 A2 SMALL RR"] Lemma imemmove_body : (1 <= Z.of_nat n < 2^62)%Z ->
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x67a40) fc None m (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros N1. pose proof (rw_cells_bound _ _ _ _ REG) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (munch_refl [(D, D + Z.of_nat n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. subst a1 a2.
    zstep. if_cases K; zify_cond K. { exfalso. revert K HK DB SMALL. clear. intros. Z.div_mod_to_equations. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2 N1. clear. intros. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    eapply (imemmove_loop n 0 m bs); try assumption; try lia.
    - f_equal; lia.
    - rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
    - eapply u8arr_of_rw_cells. exact REG.
    - destruct REG as [[WF _] _]. cbn in WF. exact (proj1 WF).
    - intros j Hj. reflexivity.
  Qed.
End Memmove.

(* [comment removed for export] *)
#[using="Type"] Lemma imemmove_spec : forall (k n : nat) (bs : list byte) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m -> rw_cells asegs m (bv_unsigned a0) [CB (k + n) bs] -> (1 <= k)%nat ->
  a1 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat k) -> a2 = Z_to_bv 64 (Z.of_nat n) ->
  (bv_unsigned a0 + Z.of_nat (k + n) < 2^63)%Z -> rng RNG (bv_unsigned a0) (Z.of_nat (k + n)) -> (1 <= Z.of_nat n < 2^62)%Z ->
  evtF asegs RNG (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) k n bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a40) fc None m (seg_rom asegs)).
Proof. all: natfold_lits. intros. eapply imemmove_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Definition memmove_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (k nn : nat) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat nn)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (k + nn) (mmv k nn bs)].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (k nn : nat) (bs : list byte) (RLO RHI : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REG : rw_cells asegs m D [CB (k + nn) bs].
  Hypothesis HK : (1 <= k)%nat.
  Hypothesis ES : S = (D + Z.of_nat k)%Z.
  Hypothesis EN : n = Z.of_nat nn.
  Hypothesis N64 : (1 <= n <= 64)%Z.
  Hypothesis SEPR : (D + Z.of_nat (k + nn) <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APP : app_blk D (D + Z.of_nat (k + nn)).
  Hypothesis UNP : unpoisoned m D (D + Z.of_nat (k + nn)).
  Hypothesis NSZ : (Z.of_nat (k + nn) <= 2^40)%Z.
  Hypothesis R1 : (RLO <= D /\ D + Z.of_nat (k + nn) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RR : rng RNG D (Z.of_nat (k + nn)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (memmove_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k nn bs lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc
    /\ unpoisoned mc S (S + n) /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= S /\ S + n + 8 <= KEND /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + n - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ shad RLO <= shad D /\ shad (D + n - 1) + 1 <= shad RHI
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + n <= RHI /\ RLO <= D /\ D + n <= RHI
     /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.

  #[using="m k nn ST LO KLO HK ES EN N64 SEPR APP NSZ R1"] Lemma BND_ok : BND.
  Proof. all: natfold_lits.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APP as [LEA AA]. unfold KLOW, KHIGH, KEND in *.
    pose proof R1 as R1'. pose proof ES as ES'. pose proof EN as EN'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    clear - Rn L0 LO KLO NSZ LEA AA R1' ES' EN' HK N64. Z.div_mod_to_equations. nia.
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= S /\ S + n + 8 <= 2^47 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44 /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + n - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296
     /\ shad RLO <= shad D /\ shad (D + n - 1) + 1 <= shad RHI /\ 1 <= n <= 64)%Z.
  #[using="m k nn ST LO KLO HK ES EN N64 SEPR APP NSZ R1"] Lemma BL_ok : BL. Proof. all: natfold_lits. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & US1 & UD1 & WR11).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in REG; change (?P) with (sf_hide P) in SEPR;
    change (?P) with (sf_hide P) in R1;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="k nn ST LO KLO HK ES EN N64 SEPR APP UNP NSZ R1 WR1"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc ->
    INV mc.
  Proof. all: natfold_lits.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    assert (USRC : unpoisoned m S (S + n)) by (eapply unpoisoned_sub; [exact UNP | lia | lia]).
    assert (UDST : unpoisoned m D (D + n)) by (eapply unpoisoned_sub; [exact UNP | lia | lia]).
    split. { eapply unpoisoned_munch; [exact USRC | exact MU1 |]. cbn [disjoint_from]. pose proof (SS S (S + n)%Z). lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RSTK RR"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55414) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    assert (REG1 : rw_cells asegs mc D [CB (k + nn) bs]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact REG | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    unfold sf_hide in SEPR.
    apply (munch_weaken _ [(bv_unsigned sp + -2240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat nn)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 WR11.
    assert (EA1 : a1 = Z_to_bv 64 (D + Z.of_nat k)) by (rewrite <- ES; symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA2 : a2 = Z_to_bv 64 (Z.of_nat nn)) by (rewrite <- EN; symmetry; apply Z_to_bv_bv_unsigned).
    zstep.
    call (imemmove_spec k nn bs); [exact MI1 | exact REG1 | exact HK | exact EA1 | exact EA2 | lia | lia |].
    do 12 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RSTK RR RSH1"] Lemma LWL : forall mc (cnt : nat) (c : Z) x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    Z.to_nat (shad (D + n - 1) - c) = cnt -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55680) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV Hk Hc. prep IV.
    revert c x16 Hk Hc. induction cnt as [|cnt IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RSTK RR RSH1"] Lemma LWS : forall mc x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55664) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    destruct (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LWL; [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LW : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x553c8) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. clear - K2 BL0. Z.div_mod_to_equations; lia. }
    do 11 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
    unfold sf_hide in R1.
    destruct (shadow_probe8 asegs mc RLO RHI D WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
    destruct (shadow_probe8 asegs mc RLO RHI (D + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
    unfold ASHOFF in P1, P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    + eapply LWS; eassumption.
    + eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LRL : forall mc (cnt : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    Z.to_nat (shad (S + n - 1) - c) = cnt -> (shad S <= c < shad (S + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 (Z_to_bv 64 (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55580) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV Hk Hc. prep IV.
    revert c x16 Hk Hc. induction cnt as [|cnt IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + n) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LW; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LRS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 (S + n + -1)) x16 x17
               x18 x19 (Z_to_bv 64 (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55564) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + n) (S + n + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LW; eassumption.
    - eapply LRL; [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LR : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55370) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. clear - K2 BL0. Z.div_mod_to_equations; lia. }
    do 11 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
    unfold sf_hide in R1.
    destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
    destruct (shadow_probe8 asegs mc RLO RHI (S + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
    unfold ASHOFF in P1, P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    + eapply LRS; eassumption.
    + eapply LW; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="RLO RHI MI ST LO KLO GOT RIC SHB INI LAY REG HK ES EN N64 SEPR APP UNP NSZ R1 WR1 RI RSTK RR RSH1"] Lemma memmove_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55330) fc None m (seg_rom asegs)).
  Proof. all: natfold_lits.
    pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in SEPR; change (?P) with (sf_hide P) in R1;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    (* [comment removed for export] *)
    change (?P) with (sf_hide P) in REG.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    change (?P) with (sf_hide P) in WR1.
    carve_frame (Z.to_nat 2144) ST0.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs m ?A [CB (Z.to_nat 2144) ?j] |- _ =>
        apply (rw_cells_split_CB asegs m A [] (Z.to_nat 2144) j [] [Z.to_nat 2072; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs m ?A (CB (Z.to_nat 2072) ?j0 :: ?hi) |- _ =>
        apply (proj1 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.rw_cells_app asegs m A [CB (Z.to_nat 2072) j0] hi)) in FRx;
        destruct FRx as [FRlo FRhi]; cbn [cells_size csize Nat.add] in FRhi;
        lazymatch type of FRhi with rw_cells _ _ ?nfA _ => replace nfA with (bv_unsigned sp + -72)%Z in FRhi by lia end
    end.
    do 12 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    lazymatch goal with
    | FRlo : rw_cells asegs ?mm ?A [CB (Z.to_nat 2072) ?j0], FRhi : rw_cells asegs ?mm (bv_unsigned sp + -72) ?hi |- _ =>
        assert (FRm : rw_cells asegs mm A ([CB (Z.to_nat 2072) j0] ++ hi))
          by (apply (proj2 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.rw_cells_app asegs mm A [CB (Z.to_nat 2072) j0] hi)); split;
              [exact FRlo | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?nfA _ => replace nfA with (bv_unsigned sp + -72)%Z by lia end; exact FRhi]);
        cbn [app] in FRm; clear FRlo FRhi
    end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV m1) by (eapply inv_of; eassumption) end.
    eapply LR; exact IV.
  Qed.
End Proofs.

#[using="Type"] Lemma memmove_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (k nn : nat) (bs : list byte) (RLO RHI : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m ->
  rw_cells asegs m (bv_unsigned a0) [CB (k + nn) bs] -> (1 <= k)%nat ->
  bv_unsigned a1 = (bv_unsigned a0 + Z.of_nat k)%Z -> bv_unsigned a2 = Z.of_nat nn -> (1 <= bv_unsigned a2 <= 64)%Z ->
  (bv_unsigned a0 + Z.of_nat (k + nn) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (k + nn)) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (k + nn)) ->
  (Z.of_nat (k + nn) <= 2^40)%Z ->
  (RLO <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat (k + nn) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a0) (Z.of_nat (k + nn)) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (memmove_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k nn bs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55330) fc None m (seg_rom asegs)).
Proof. all: natfold_lits. intros. eapply memmove_i_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memmove_postw (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (k nn : nat) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q); (D, D + Z.of_nat nn)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' D [CB (k + nn) (mmv k nn bs)].

#[using="Type"] Lemma memmove_wb_spec : forall (k nn : nat) (bs : list byte) RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D : Z) (lo : Z),
  rw_cells asegs m D [CB (k + nn) bs] -> (1 <= k)%nat -> (1 <= Z.of_nat nn <= 64)%Z ->
  mem_inv asegs m ->
  (0 <= q < 2^64)%Z -> (0 <= D)%Z -> (D + Z.of_nat (k + nn) < 2^64)%Z ->
  stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> sobj RNG m D (D + Z.of_nat (k + nn)) ->
  (D + Z.of_nat (k + nn) <= lo \/ q <= D)%Z ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG D (Z.of_nat (k + nn)) ->
  evtF asegs RNG (memmove_postw ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D k nn bs lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (Z.of_nat nn)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5495c) fc None m (seg_rom asegs)).
Proof. all: natfold_lits.
  intros until lo. intros REG HK HN MI Hq HD HDN ST LO KH ENV (AB & U & N40 & RLO & RHI & HU & WR & RSH) SEP RIMG RSTK RD.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 (D + Z.of_nat k)) = (D + Z.of_nat k)%Z) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 (Z.of_nat nn)) = Z.of_nat nn) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(q - 2240, q); (D, D + Z.of_nat nn)]%Z m) as MU.
  pose proof (ie_got _ ENV) as E1. pose proof (ie_ric _ ENV) as E2. pose proof (ie_shb _ ENV) as E3.
  pose proof (ie_ini _ ENV) as E4. pose proof (ie_lay _ ENV) as E5.
  step.
  eapply evtF_mono.
  { eapply (memmove_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (Z.of_nat nn)))
      with (k := k) (nn := nn) (bs := bs) (RLO := RLO) (RHI := RHI);
      rewrite ?Eq, ?Ed, ?Es, ?En; try eassumption; try lia. }
  intros ms' P. unfold memmove_i_post in P. all: natfold_lits. rewrite !Eq, !Ed in P. unfold memmove_postw. all: natfold_lits. exact P.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition mmv (k n : nat) (bs : list byte) : list byte := firstn n (skipn k bs) ++ skipn n bs.
Lemma mmv_length : forall k n bs, length bs = (k + n)%nat -> length (mmv k n bs) = (k + n)%nat.
Proof. all: natfold_lits. intros k n bs L. unfold mmv. rewrite length_app, length_firstn, !length_skipn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition imemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (k n : nat) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (k + n) (mmv k n bs)].

Section Memmove.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k n : nat) (bs : list byte).
  Notation D := (bv_unsigned a0).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis REG : rw_cells asegs m D [CB (k + n) bs].
  Hypothesis HK : (1 <= k)%nat.
  Hypothesis A1 : a1 = Z_to_bv 64 (D + Z.of_nat k).
  Hypothesis A2 : a2 = Z_to_bv 64 (Z.of_nat n).
  Hypothesis SMALL : (D + Z.of_nat (k + n) < 2^63)%Z.
  Hypothesis RR : rng RNG D (Z.of_nat (k + n)).
  Notation POST := (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D k n bs m).

  (* [comment removed for export] *)
  #[using="REG HK SMALL RR"] Lemma imemmove_loop : forall (c : nat) (i : Z) (mc : word -> option byte) (cur : list byte) (x11 x13 x14 : word),
    x11 = Z_to_bv 64 (D + Z.of_nat k + i) -> x13 = Z_to_bv 64 (D + i) ->
    Z.to_nat (Z.of_nat n - i) = c -> (0 <= i < Z.of_nat n)%Z ->
    u8arr asegs mc D cur -> length cur = (k + n)%nat ->
    (forall j, (j < Z.to_nat i)%nat -> nth_error cur j = nth_error bs (k + j)) ->
    (forall j, (Z.to_nat i <= j)%nat -> nth_error cur j = nth_error bs j) ->
    munch [(D, D + Z.of_nat n)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 (Z_to_bv 64 (D + Z.of_nat n)) x13 x14 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67ab8) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    pose proof (rw_cells_bound _ _ _ _ REG) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LBS : length bs = (k + n)%nat) by (destruct REG as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    induction c as [|c IH]; intros i mc cur x11 x13 x14 -> -> Hc Hi ARR LCUR DONE REST MU WM MI1; [exfalso; lia|].
    destruct (nth_error bs (k + Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (NBc : nth_error cur (Z.to_nat (Z.of_nat k + i)) = Some b).
    { replace (Z.to_nat (Z.of_nat k + i)) with (k + Z.to_nat i)%nat by lia. rewrite REST by lia. exact NB. }
    pose proof (u8arr_read asegs mc D cur (Z.of_nat k + i) b (wa (D + Z.of_nat k + i)) ARR NBc ltac:(lia) ltac:(f_equal; lia)) as RDb.
    zstep. cbv beta.
    pose proof (u8arr_store_ok asegs mc D cur i (wa (D + i)) ARR ltac:(rewrite LCUR; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write asegs mc D cur i b ARR ltac:(rewrite LCUR; lia)) as ARR'.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    store_done.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - eapply (IH (i + 1)%Z); [f_equal; lia | f_equal; lia | lia | lia | exact ARR' | rewrite Arr.upd_length; exact LCUR | | | assumption | assumption | assumption].
      + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LCUR; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
      + intros j Hj. rewrite Arr.nth_error_upd_other by lia. apply REST. lia.
    - zstep. zstep.
      assert (E : upd cur (Z.to_nat i) b = mmv k n bs).
      { assert (EI : Z.to_nat i = (n - 1)%nat) by lia.
        apply nth_error_ext. intros j. unfold mmv.
        destruct (Nat.lt_ge_cases j n) as [LT|GE].
        - rewrite nth_error_app1 by (rewrite length_firstn, length_skipn; lia).
          rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact LT). rewrite nth_error_skipn.
          destruct (Nat.eq_dec j (Z.to_nat i)).
          + subst j. rewrite Arr.nth_error_upd_same by (rewrite LCUR; lia). symmetry; exact NB.
          + rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
        - rewrite nth_error_app2 by (rewrite length_firstn, length_skipn; lia).
          rewrite length_firstn, length_skipn. replace (Nat.min n (length bs - k)) with n by lia.
          rewrite nth_error_skipn. replace (n + (j - n))%nat with j by lia.
          rewrite Arr.nth_error_upd_other by lia. apply REST. lia. }
      rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. rewrite mmv_length in ARR' by exact LBS. finish.
  Qed.

  #[using="MI REG HK A1 A2 SMALL RR"] Lemma imemmove_body : (1 <= Z.of_nat n < 2^62)%Z ->
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x67aa8) fc None m (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros N1. pose proof (rw_cells_bound _ _ _ _ REG) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (munch_refl [(D, D + Z.of_nat n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. subst a1 a2.
    zstep. if_cases K; zify_cond K. { exfalso. revert K HK DB SMALL. clear. intros. Z.div_mod_to_equations. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2 N1. clear. intros. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    eapply (imemmove_loop n 0 m bs); try assumption; try lia.
    - f_equal; lia.
    - rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
    - eapply u8arr_of_rw_cells. exact REG.
    - destruct REG as [[WF _] _]. cbn in WF. exact (proj1 WF).
    - intros j Hj. reflexivity.
  Qed.
End Memmove.

(* [comment removed for export] *)
#[using="Type"] Lemma imemmove_spec : forall (k n : nat) (bs : list byte) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m -> rw_cells asegs m (bv_unsigned a0) [CB (k + n) bs] -> (1 <= k)%nat ->
  a1 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat k) -> a2 = Z_to_bv 64 (Z.of_nat n) ->
  (bv_unsigned a0 + Z.of_nat (k + n) < 2^63)%Z -> rng RNG (bv_unsigned a0) (Z.of_nat (k + n)) -> (1 <= Z.of_nat n < 2^62)%Z ->
  evtF asegs RNG (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) k n bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67aa8) fc None m (seg_rom asegs)).
Proof. all: natfold_lits. intros. eapply imemmove_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Definition memmove_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (k nn : nat) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat nn)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (k + nn) (mmv k nn bs)].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (k nn : nat) (bs : list byte) (RLO RHI : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REG : rw_cells asegs m D [CB (k + nn) bs].
  Hypothesis HK : (1 <= k)%nat.
  Hypothesis ES : S = (D + Z.of_nat k)%Z.
  Hypothesis EN : n = Z.of_nat nn.
  Hypothesis N64 : (1 <= n <= 64)%Z.
  Hypothesis SEPR : (D + Z.of_nat (k + nn) <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APP : app_blk D (D + Z.of_nat (k + nn)).
  Hypothesis UNP : unpoisoned m D (D + Z.of_nat (k + nn)).
  Hypothesis NSZ : (Z.of_nat (k + nn) <= 2^40)%Z.
  Hypothesis R1 : (RLO <= D /\ D + Z.of_nat (k + nn) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RR : rng RNG D (Z.of_nat (k + nn)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (memmove_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k nn bs lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc
    /\ unpoisoned mc S (S + n) /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= S /\ S + n + 8 <= KEND /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + n - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ shad RLO <= shad D /\ shad (D + n - 1) + 1 <= shad RHI
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + n <= RHI /\ RLO <= D /\ D + n <= RHI
     /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.

  #[using="m k nn ST LO KLO HK ES EN N64 SEPR APP NSZ R1"] Lemma BND_ok : BND.
  Proof. all: natfold_lits.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APP as [LEA AA]. unfold KLOW, KHIGH, KEND in *.
    pose proof R1 as R1'. pose proof ES as ES'. pose proof EN as EN'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    clear - Rn L0 LO KLO NSZ LEA AA R1' ES' EN' HK N64. Z.div_mod_to_equations. nia.
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= S /\ S + n + 8 <= 2^47 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44 /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + n - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296
     /\ shad RLO <= shad D /\ shad (D + n - 1) + 1 <= shad RHI /\ 1 <= n <= 64)%Z.
  #[using="m k nn ST LO KLO HK ES EN N64 SEPR APP NSZ R1"] Lemma BL_ok : BL. Proof. all: natfold_lits. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & US1 & UD1 & WR11).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in REG; change (?P) with (sf_hide P) in SEPR;
    change (?P) with (sf_hide P) in R1;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="k nn ST LO KLO HK ES EN N64 SEPR APP UNP NSZ R1 WR1"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc ->
    INV mc.
  Proof. all: natfold_lits.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    assert (USRC : unpoisoned m S (S + n)) by (eapply unpoisoned_sub; [exact UNP | lia | lia]).
    assert (UDST : unpoisoned m D (D + n)) by (eapply unpoisoned_sub; [exact UNP | lia | lia]).
    split. { eapply unpoisoned_munch; [exact USRC | exact MU1 |]. cbn [disjoint_from]. pose proof (SS S (S + n)%Z). lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RSTK RR"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5547c) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    assert (REG1 : rw_cells asegs mc D [CB (k + nn) bs]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact REG | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    unfold sf_hide in SEPR.
    apply (munch_weaken _ [(bv_unsigned sp + -2240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat nn)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 WR11.
    assert (EA1 : a1 = Z_to_bv 64 (D + Z.of_nat k)) by (rewrite <- ES; symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA2 : a2 = Z_to_bv 64 (Z.of_nat nn)) by (rewrite <- EN; symmetry; apply Z_to_bv_bv_unsigned).
    zstep.
    call (imemmove_spec k nn bs); [exact MI1 | exact REG1 | exact HK | exact EA1 | exact EA2 | lia | lia |].
    do 12 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RSTK RR RSH1"] Lemma LWL : forall mc (cnt : nat) (c : Z) x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    Z.to_nat (shad (D + n - 1) - c) = cnt -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x556e8) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV Hk Hc. prep IV.
    revert c x16 Hk Hc. induction cnt as [|cnt IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RSTK RR RSH1"] Lemma LWS : forall mc x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x556cc) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    destruct (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LWL; [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LW : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55430) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. clear - K2 BL0. Z.div_mod_to_equations; lia. }
    do 11 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
    unfold sf_hide in R1.
    destruct (shadow_probe8 asegs mc RLO RHI D WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
    destruct (shadow_probe8 asegs mc RLO RHI (D + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
    unfold ASHOFF in P1, P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    + eapply LWS; eassumption.
    + eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LRL : forall mc (cnt : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    Z.to_nat (shad (S + n - 1) - c) = cnt -> (shad S <= c < shad (S + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 (Z_to_bv 64 (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x555e8) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV Hk Hc. prep IV.
    revert c x16 Hk Hc. induction cnt as [|cnt IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + n) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LW; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LRS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 (S + n + -1)) x16 x17
               x18 x19 (Z_to_bv 64 (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x555cc) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + n) (S + n + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LW; eassumption.
    - eapply LRL; [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO REG HK ES EN N64 SEPR APP NSZ R1 RI RSTK RR RSH1"] Lemma LR : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x553d8) fc None mc (seg_rom asegs)).
  Proof. all: natfold_lits.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. clear - K2 BL0. Z.div_mod_to_equations; lia. }
    do 11 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
    unfold sf_hide in R1.
    destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
    destruct (shadow_probe8 asegs mc RLO RHI (S + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
    unfold ASHOFF in P1, P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    + eapply LRS; eassumption.
    + eapply LW; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="RLO RHI MI ST LO KLO GOT RIC SHB INI LAY REG HK ES EN N64 SEPR APP UNP NSZ R1 WR1 RI RSTK RR RSH1"] Lemma memmove_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55398) fc None m (seg_rom asegs)).
  Proof. all: natfold_lits.
    pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in SEPR; change (?P) with (sf_hide P) in R1;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    (* [comment removed for export] *)
    change (?P) with (sf_hide P) in REG.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    change (?P) with (sf_hide P) in WR1.
    carve_frame (Z.to_nat 2144) ST0.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs m ?A [CB (Z.to_nat 2144) ?j] |- _ =>
        apply (rw_cells_split_CB asegs m A [] (Z.to_nat 2144) j [] [Z.to_nat 2072; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs m ?A (CB (Z.to_nat 2072) ?j0 :: ?hi) |- _ =>
        apply (proj1 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.rw_cells_app asegs m A [CB (Z.to_nat 2072) j0] hi)) in FRx;
        destruct FRx as [FRlo FRhi]; cbn [cells_size csize Nat.add] in FRhi;
        lazymatch type of FRhi with rw_cells _ _ ?nfA _ => replace nfA with (bv_unsigned sp + -72)%Z in FRhi by lia end
    end.
    do 12 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    lazymatch goal with
    | FRlo : rw_cells asegs ?mm ?A [CB (Z.to_nat 2072) ?j0], FRhi : rw_cells asegs ?mm (bv_unsigned sp + -72) ?hi |- _ =>
        assert (FRm : rw_cells asegs mm A ([CB (Z.to_nat 2072) j0] ++ hi))
          by (apply (proj2 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.rw_cells_app asegs mm A [CB (Z.to_nat 2072) j0] hi)); split;
              [exact FRlo | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?nfA _ => replace nfA with (bv_unsigned sp + -72)%Z by lia end; exact FRhi]);
        cbn [app] in FRm; clear FRlo FRhi
    end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV m1) by (eapply inv_of; eassumption) end.
    eapply LR; exact IV.
  Qed.
End Proofs.

#[using="Type"] Lemma memmove_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (k nn : nat) (bs : list byte) (RLO RHI : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m ->
  rw_cells asegs m (bv_unsigned a0) [CB (k + nn) bs] -> (1 <= k)%nat ->
  bv_unsigned a1 = (bv_unsigned a0 + Z.of_nat k)%Z -> bv_unsigned a2 = Z.of_nat nn -> (1 <= bv_unsigned a2 <= 64)%Z ->
  (bv_unsigned a0 + Z.of_nat (k + nn) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (k + nn)) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (k + nn)) ->
  (Z.of_nat (k + nn) <= 2^40)%Z ->
  (RLO <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat (k + nn) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a0) (Z.of_nat (k + nn)) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (memmove_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k nn bs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55398) fc None m (seg_rom asegs)).
Proof. all: natfold_lits. intros. eapply memmove_i_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memmove_postw (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (k nn : nat) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q); (D, D + Z.of_nat nn)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' D [CB (k + nn) (mmv k nn bs)].

#[using="Type"] Lemma memmove_wb_spec : forall (k nn : nat) (bs : list byte) RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D : Z) (lo : Z),
  rw_cells asegs m D [CB (k + nn) bs] -> (1 <= k)%nat -> (1 <= Z.of_nat nn <= 64)%Z ->
  mem_inv asegs m ->
  (0 <= q < 2^64)%Z -> (0 <= D)%Z -> (D + Z.of_nat (k + nn) < 2^64)%Z ->
  stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> sobj RNG m D (D + Z.of_nat (k + nn)) ->
  (D + Z.of_nat (k + nn) <= lo \/ q <= D)%Z ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG D (Z.of_nat (k + nn)) ->
  evtF asegs RNG (memmove_postw ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D k nn bs lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (Z.of_nat nn)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x549c4) fc None m (seg_rom asegs)).
Proof. all: natfold_lits.
  intros until lo. intros REG HK HN MI Hq HD HDN ST LO KH ENV (AB & U & N40 & RLO & RHI & HU & WR & RSH) SEP RIMG RSTK RD.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 (D + Z.of_nat k)) = (D + Z.of_nat k)%Z) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 (Z.of_nat nn)) = Z.of_nat nn) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(q - 2240, q); (D, D + Z.of_nat nn)]%Z m) as MU.
  pose proof (ie_got _ ENV) as E1. pose proof (ie_ric _ ENV) as E2. pose proof (ie_shb _ ENV) as E3.
  pose proof (ie_ini _ ENV) as E4. pose proof (ie_lay _ ENV) as E5.
  step.
  eapply evtF_mono.
  { eapply (memmove_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + Z.of_nat k)) (Z_to_bv 64 (Z.of_nat nn)))
      with (k := k) (nn := nn) (bs := bs) (RLO := RLO) (RHI := RHI);
      rewrite ?Eq, ?Ed, ?Es, ?En; try eassumption; try lia. }
  intros ms' P. unfold memmove_i_post in P. all: natfold_lits. rewrite !Eq, !Ed in P. unfold memmove_postw. all: natfold_lits. exact P.
Qed.
End CANSEC1.
End TwB.
