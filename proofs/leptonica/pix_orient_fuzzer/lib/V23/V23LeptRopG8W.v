(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptRop2Segs V23LeptRopGSpec V23LeptRopG8Segs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_g8 : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition rg8_inv (B Mi : word -> option byte) (datad nd : Z) : Prop :=
  (forall x : word, (bv_unsigned x < datad \/ datad + nd <= bv_unsigned x)%Z -> Mi x = B x) /\ mem_grows B Mi.

Lemma rg8_inv_refl : forall B datad nd, rg8_inv B B datad nd.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma rg8_inv_trans : forall B M1 M2 datad nd, rg8_inv B M1 datad nd -> rg8_inv M1 M2 datad nd -> rg8_inv B M2 datad nd.
Proof.
  intros B M1 M2 datad nd [E1 G1] [E2 G2]. split.
  - intros x Hx. rewrite (E2 x Hx). apply E1, Hx.
  - eapply mem_grows_trans; eassumption.
Qed.

Lemma rg8_inv_store : forall B Mi datad nd (a : Z) (bs : list byte),
  rg8_inv B Mi datad nd -> (0 <= datad)%Z -> (datad + nd <= 2 ^ 64)%Z -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + nd)%Z ->
  rg8_inv B (wbytes Mi (Z_to_bv 64 a) bs) datad nd.
Proof.
  intros B Mi datad nd a bs [HI HG] H0 H1 Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
  cbn [length] in Hb. split.
  - intros x Hx. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
  - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
Qed.

Lemma rg8_sok : forall B Mi (base RS a : Z) (n : nat), mem_grows B Mi ->
  store_ok SEGS B (Z_to_bv 64 base) (Z.to_nat RS) = true -> (0 <= base)%Z -> (base + RS <= 2 ^ 64)%Z ->
  (base <= a)%Z -> (a + Z.of_nat n <= base + RS)%Z -> store_ok SEGS Mi (Z_to_bv 64 a) n = true.
Proof.
  intros B Mi base RS a n HG SOK H0 H1 Ha Hn. eapply store_ok_mono; [exact HG|].
  destruct n as [|n']; [reflexivity|].
  eapply (store_ok_sub SEGS B (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
Qed.

Lemma rg8_rd : forall B Mi (base RS a : Z) (n : nat), mem_grows B Mi ->
  store_ok SEGS B (Z_to_bv 64 base) (Z.to_nat RS) = true -> (0 <= base)%Z -> (base + RS <= 2 ^ 64)%Z ->
  (base <= a)%Z -> (a + Z.of_nat n <= base + RS)%Z ->
  exists bs, rdn SEGS Mi (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros B Mi base RS a n HG SOK H0 H1 Ha Hn.
  apply (store_ok_rdn SEGS Mi n (Z_to_bv 64 a) wr_readable_g8).
  eapply rg8_sok; eassumption.
Qed.

Lemma rg8_cell : forall B Mi (datad nd s a : Z) (n : nat) bs, rg8_inv B Mi datad nd -> disj_apart datad nd (s - 240) 240 ->
  (0 <= s - 240)%Z -> (s < 2 ^ 64)%Z -> (s - 240 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  rdn SEGS B (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
Proof.
  intros B Mi datad nd s a n bs [HI _] FR H0 H1 Ha Hn HM. use_apart FR. rewrite <- HM.
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
Qed.

Ltac agr AG := match goal with |- getr _ ?r = _ => rewrite (AG r ltac:(notin_list)); assumption end.

Section RopGen8W.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (s datad nd datas ns dh swpl dwpl sls : Z).
Hypothesis Hs : (250000 <= s /\ s + 64 < 2 ^ 64)%Z.
Hypothesis Hd : (4096 <= datad /\ 0 < nd /\ datad + nd + 2 ^ 27 <= 2 ^ 64 /\ datad mod 4 = 0)%Z.
Hypothesis Hsr : (4096 <= datas /\ 0 < ns /\ datas + ns + 2 ^ 27 <= 2 ^ 64 /\ datas mod 4 = 0)%Z.
Hypothesis FR : disj_apart datad nd (s - 240) 240.
Hypothesis Hdim : (1 <= dh < 2 ^ 24 /\ 0 <= swpl < 2 ^ 24 /\ 0 <= dwpl < 2 ^ 24 /\ 1 <= sls <= 31)%Z.

Section FLoop.
Variables (B : word -> option byte) (psf pdf : Z) (f6 f7 : bool) (nm : word).
Hypothesis SOKd : store_ok SEGS B (Z_to_bv 64 datad) (Z.to_nat nd) = true.
Hypothesis SOKs : store_ok SEGS B (Z_to_bv 64 datas) (Z.to_nat ns) = true.
Hypothesis Cz : rdn SEGS B (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Hypothesis Cnm : rdn SEGS B (Z_to_bv 64 (s - 240)) 8 = Some (word_to_le_bytes 8 nm).
Hypothesis Hal : (psf mod 4 = 0 /\ pdf mod 4 = 0)%Z.
Hypothesis Hrow : forall i, (0 <= i < dh)%Z ->
  (datad <= pdf + 4 * dwpl * i /\ pdf + 4 * dwpl * i + 4 <= datad + nd /\
   datas <= psf + 4 * swpl * i /\ psf + 4 * swpl * i + 4 + (if f6 && negb f7 then 4 else 0) <= datas + ns)%Z.

Definition rg8_fregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 15 = Z_to_bv 64 psf /\ getr regs 11 = Z_to_bv 64 (4 * swpl * j) /\
  getr regs 25 = Z_to_bv 64 (pdf + 4 * dwpl * j) /\ getr regs 16 = Z_to_bv 64 (pdf + 4 * dwpl * j) /\
  getr regs 28 = Z_to_bv 64 (- (dh - j)) /\ getr regs 27 = Z_to_bv 64 (4 * swpl) /\ getr regs 7 = Z_to_bv 64 (4 * dwpl) /\
  getr regs 20 = Z_to_bv 64 (psf + 4 * swpl) /\ getr regs 19 = Z_to_bv 64 (if f6 then 1 else 0) /\
  getr regs 24 = Z_to_bv 64 (if f7 then 1 else 0) /\ getr regs 13 = Z_to_bv 64 1 /\ getr regs 23 = Z_to_bv 64 0 /\
  getr regs 9 = Z_to_bv 64 0 /\ getr regs 1 = Z_to_bv 64 31 /\ getr regs 30 = Z_to_bv 64 sls /\
  getr regs 8 = Z_to_bv 64 (32 - sls) /\ getr regs 22 = Z_to_bv 64 32.

Lemma rg8wF_bs1 : forall Mi j, rg8_inv B Mi datad nd -> (0 <= j < dh)%Z ->
  exists bs1, (f6 = true -> f7 = false -> psf + 4 * swpl * j + 8 < 2 ^ 64 /\
    rdn SEGS Mi (Z_to_bv 64 (psf + 4 * swpl * j + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z.
Proof.
  intros Mi j HI Hj. pose proof Hsr as HS. pose proof Hdim as HM.
  pose proof (Hrow j Hj) as (R1 & R2 & R3 & R4).
  destruct (f6 && negb f7) eqn:E.
  - try rewrite E in R4. cbv beta iota in R4.
    destruct (rg8_rd B Mi datas ns (psf + 4 * swpl * j + 4) 4 (proj2 HI) SOKs ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bs1 & RB & LB).
    exists bs1. intros _ _. split; [lia | split; assumption].
  - exists []. intros E6 E7. rewrite E6, E7 in E. cbn in E. discriminate E.
Qed.

(* [comment removed for export] *)
Lemma rg8_F_W : forall (k : nat) regs Mi j, (0 <= j)%Z -> (j + Z.of_nat k = dh - 1)%Z ->
  rg8_inv B Mi datad nd -> rg8_fregs regs j ->
  exists regs' M',
    msteps SEGS (mkst regs RG8_F Mi rom) (mkst regs' RG8_X1 M' rom)
    /\ rg8_inv B M' datad nd
    /\ regs_agree (fun r => In r [11; 12; 16; 17; 21; 25; 26; 28]%list) regs regs'.
Proof.
  pose proof Hd as HD. pose proof Hsr as HS. pose proof Hdim as HM. pose proof Hs as HSS. pose proof FR as FRd. use_apart FRd.
  induction k as [|k IH]; intros regs Mi j Hj Hk HI FG;
    assert (Hj' : (0 <= j < dh)%Z) by lia;
    pose proof (Hrow j Hj') as (R1 & R2 & R3 & R4);
    assert (R4' : (psf + 4 * swpl * j + 4 <= datas + ns)%Z) by (destruct (f6 && negb f7); lia);
    assert (Hoff : (0 <= 4 * swpl * j)%Z) by nia;
    assert (Hpd : (0 <= 4 * dwpl * j)%Z) by nia;
    pose proof (Hrow 0 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4);
    rewrite !Z.mul_0_r, !Z.add_0_r in Q1, Q2, Q3, Q4;
    pose proof FG as (F2 & F15 & F11 & F25 & F16 & F28 & F27 & F7 & F20 & F19 & F24 & F13 & F23 & F9 & F1 & F30 & F8 & F22);
    destruct (rg8_rd B Mi datas ns (psf + 4 * swpl * j) 4 (proj2 HI) SOKs ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(destruct (f6 && negb f7); change (Z.of_nat 4) with 4%Z; lia)) as (bs0 & RS0 & LS0);
    destruct (rg8wF_bs1 Mi j HI Hj') as (bs1 & B1);
    destruct (rg8_rd B Mi datad nd (pdf + 4 * dwpl * j) 4 (proj2 HI) SOKd ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bd & RD & LD);
    pose proof (rg8_sok B Mi datad nd (pdf + 4 * dwpl * j) 4 (proj2 HI) SOKd ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 4) with 4%Z; lia)) as SOK;
    pose proof (rg8_cell B Mi datad nd s (s - 120) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cz) as Cz1;
    pose proof (rg8_cell B Mi datad nd s (s - 240) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cnm) as Cnm1.
  - destruct (rg8_F rom f6 f7 true regs Mi s psf (4 * swpl * j) (pdf + 4 * dwpl * j) (4 * swpl) (4 * dwpl) (dh - j) sls nm bs0 bs1 bd
                ltac:(lia) ltac:(lia) ltac:(lia) Hoff ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) (ltac:(lia) : (dh - j = 1)%Z) ltac:(lia)
                RS0 LS0 B1 RD LD SOK Cz1 Cnm1 F2 F15 F11 F25 F16 F28 F27 F7 F20 F19 F24 F13 F23 F9 F1 F30 F8 F22)
      as (r1 & wv & S1 & E11 & E25 & E16 & E28 & AG1).
    exists r1, (wbytes Mi (Z_to_bv 64 (pdf + 4 * dwpl * j)) (word_to_le_bytes 4 wv)).
    split; [exact S1 | split; [| exact AG1]].
    apply rg8_inv_store; [exact HI | lia | lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 4) with 4%Z; lia].
  - destruct (rg8_F rom f6 f7 false regs Mi s psf (4 * swpl * j) (pdf + 4 * dwpl * j) (4 * swpl) (4 * dwpl) (dh - j) sls nm bs0 bs1 bd
                ltac:(lia) ltac:(lia) ltac:(lia) Hoff ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) (ltac:(lia) : (1 < dh - j)%Z) ltac:(lia)
                RS0 LS0 B1 RD LD SOK Cz1 Cnm1 F2 F15 F11 F25 F16 F28 F27 F7 F20 F19 F24 F13 F23 F9 F1 F30 F8 F22)
      as (r1 & wv & S1 & E11 & E25 & E16 & E28 & AG1).
    assert (HI1 : rg8_inv B (wbytes Mi (Z_to_bv 64 (pdf + 4 * dwpl * j)) (word_to_le_bytes 4 wv)) datad nd)
      by (apply rg8_inv_store; [exact HI | lia | lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 4) with 4%Z; lia]).
    assert (FG1 : rg8_fregs r1 (j + 1)).
    { unfold rg8_fregs. repeat split; try agr AG1.
      - rewrite E11. f_equal. ring.
      - rewrite E25. f_equal. ring.
      - rewrite E16. f_equal. ring.
      - rewrite E28. f_equal. ring. }
    destruct (IH r1 _ (j + 1)%Z ltac:(lia) ltac:(lia) HI1 FG1) as (r2 & Mb & S2 & HI2 & AG2).
    exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2] |].
    split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]].
Qed.
End FLoop.

Section LLoop.
Variables (B : word -> option byte) (psl pdl : Z) (f3 : bool) (mk : word).
Hypothesis SOKd : store_ok SEGS B (Z_to_bv 64 datad) (Z.to_nat nd) = true.
Hypothesis SOKs : store_ok SEGS B (Z_to_bv 64 datas) (Z.to_nat ns) = true.
Hypothesis Cz : rdn SEGS B (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Hypothesis Cpsl : rdn SEGS B (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)).
Hypothesis Cmk : rdn SEGS B (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk).
Hypothesis Hal : (psl mod 4 = 0 /\ pdl mod 4 = 0)%Z.
Hypothesis Hrow : forall i, (0 <= i < dh)%Z ->
  (datad <= pdl + 4 * dwpl * i /\ pdl + 4 * dwpl * i + 4 <= datad + nd /\
   datas <= psl + 4 * swpl * i /\ psl + 4 * swpl * i + 4 + (if f3 then 0 else 4) <= datas + ns)%Z.

Definition rg8_lregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 11 = Z_to_bv 64 (4 * swpl * j) /\
  getr regs 10 = Z_to_bv 64 (pdl + 4 * dwpl * j) /\ getr regs 20 = Z_to_bv 64 (pdl + 4 * dwpl * j) /\
  getr regs 9 = Z_to_bv 64 (- (dh - j)) /\ getr regs 5 = Z_to_bv 64 (if f3 then 1 else 0) /\
  getr regs 17 = Z_to_bv 64 0 /\ getr regs 14 = Z_to_bv 64 0 /\ getr regs 7 = Z_to_bv 64 18446744073709551611 /\
  getr regs 19 = Z_to_bv 64 31 /\ getr regs 16 = Z_to_bv 64 32 /\ getr regs 28 = Z_to_bv 64 (psl + 4 * swpl) /\
  getr regs 15 = Z_to_bv 64 (4 * dwpl) /\ getr regs 6 = Z_to_bv 64 (4 * swpl) /\
  getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

(* [comment removed for export] *)
Lemma rg8_L_W : forall (k : nat) regs Mi j, (0 <= j)%Z -> (j + Z.of_nat k = dh - 1)%Z ->
  rg8_inv B Mi datad nd -> rg8_lregs regs j ->
  exists regs' M',
    msteps SEGS (mkst regs RG8_L Mi rom) (mkst regs' RG_E M' rom)
    /\ rg8_inv B M' datad nd
    /\ regs_agree (fun r => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
Proof.
  pose proof Hd as HD. pose proof Hsr as HS. pose proof Hs as HSS. pose proof FR as FR'. unfold disj_apart in FR'.
  pose proof Hdim as (Hdh & Hsw & Hdw & Hsl).
  assert (Hf34 : (0 <= (if f3 then 0 else 4))%Z) by (case f3; cbv iota; lia).
  pose proof (Hrow 0 ltac:(lia)) as HR0.
  induction k as [|k IH]; intros regs Mi j Hj Hk HI LR;
    assert (Hjd : (0 <= j < dh)%Z) by lia;
    pose proof (Hrow j Hjd) as HR;
    pose proof LR as (L2 & L11 & L10 & L20 & L9 & L5 & L17 & L14 & L7 & L19 & L16 & L28 & L15 & L6 & L30 & L8);
    assert (Hoff : (0 <= 4 * swpl * j)%Z) by (apply Z.mul_nonneg_nonneg; lia);
    assert (Hdoff : (0 <= 4 * dwpl * j)%Z) by (apply Z.mul_nonneg_nonneg; lia);
    destruct (rg8_rd B Mi datas ns (psl + 4 * swpl * j) 4 (proj2 HI) SOKs ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bs0 & R0 & L0);
    assert (R1e : exists bs1, (f3 = false -> psl + 4 * swpl * j + 8 < 2 ^ 64 /\
                    rdn SEGS Mi (Z_to_bv 64 (psl + 4 * swpl * j + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z)
      by (case_eq f3; intros Ef;
          [ exists []; intros E; discriminate E
          | rewrite Ef in HR; change (if false then 0 else 4)%Z with 4%Z in HR;
            destruct (rg8_rd B Mi datas ns (psl + 4 * swpl * j + 4) 4 (proj2 HI) SOKs ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bs1 & Rb & Lb);
            exists bs1; intros _; split; [lia | split; [exact Rb | exact Lb]] ]);
    destruct R1e as (bs1 & R1);
    destruct (rg8_rd B Mi datad nd (pdl + 4 * dwpl * j) 4 (proj2 HI) SOKd ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bd & RD & LD);
    pose proof (rg8_sok B Mi datad nd (pdl + 4 * dwpl * j) 4 (proj2 HI) SOKd ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 4) with 4%Z; lia)) as SOK;
    pose proof (rg8_cell B Mi datad nd s (s - 136) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cpsl) as Cpsl';
    pose proof (rg8_cell B Mi datad nd s (s - 144) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cmk) as Cmk';
    pose proof (rg8_cell B Mi datad nd s (s - 120) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cz) as Cz'.
  - destruct (rg8_L rom f3 true regs Mi s psl (4 * swpl * j) (pdl + 4 * dwpl * j) (4 * swpl) (4 * dwpl) (dh - j) sls mk bs0 bs1 bd
                ltac:(lia) ltac:(lia) ltac:(lia) Hoff ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) (ltac:(lia) : (dh - j = 1)%Z) ltac:(lia)
                R0 L0 R1 RD LD SOK Cpsl' Cmk' Cz' L2 L11 L10 L20 L9 L5 L17 L14 L7 L19 L16 L28 L15 L6 L30 L8)
      as (r1 & wv & S1 & E11 & E10 & E20 & E9 & AG1).
    exists r1, (wbytes Mi (Z_to_bv 64 (pdl + 4 * dwpl * j)) (word_to_le_bytes 4 wv)).
    split; [exact S1 | split; [| exact AG1]].
    apply rg8_inv_store; [exact HI | lia | lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 4) with 4%Z; lia].
  - destruct (rg8_L rom f3 false regs Mi s psl (4 * swpl * j) (pdl + 4 * dwpl * j) (4 * swpl) (4 * dwpl) (dh - j) sls mk bs0 bs1 bd
                ltac:(lia) ltac:(lia) ltac:(lia) Hoff ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) (ltac:(lia) : (1 < dh - j)%Z) ltac:(lia)
                R0 L0 R1 RD LD SOK Cpsl' Cmk' Cz' L2 L11 L10 L20 L9 L5 L17 L14 L7 L19 L16 L28 L15 L6 L30 L8)
      as (r1 & wv & S1 & E11 & E10 & E20 & E9 & AG1).
    assert (HI1 : rg8_inv B (wbytes Mi (Z_to_bv 64 (pdl + 4 * dwpl * j)) (word_to_le_bytes 4 wv)) datad nd)
      by (apply rg8_inv_store; [exact HI | lia | lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 4) with 4%Z; lia]).
    assert (LR1 : rg8_lregs r1 (j + 1)).
    { unfold rg8_lregs. repeat split; try agr AG1.
      all: first [rewrite E11 | rewrite E10 | rewrite E20 | rewrite E9]; f_equal; first [lia | ring]. }
    destruct (IH r1 _ (j + 1)%Z ltac:(lia) ltac:(lia) HI1 LR1) as (r2 & Mb & S2 & HI2 & AG2).
    exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2] |].
    split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]].
Qed.
End LLoop.

Section MLoop.
Variables (B : word -> option byte) (psF pdF nfw : Z).
Hypothesis SOKd : store_ok SEGS B (Z_to_bv 64 datad) (Z.to_nat nd) = true.
Hypothesis SOKs : store_ok SEGS B (Z_to_bv 64 datas) (Z.to_nat ns) = true.
Hypothesis Cz : rdn SEGS B (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Hypothesis Cdh : rdn SEGS B (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
Hypothesis Cnfw : rdn SEGS B (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)).
Hypothesis C208 : rdn SEGS B (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)).
Hypothesis C224 : rdn SEGS B (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)).
Hypothesis Hnfw : (1 <= nfw < 2 ^ 26)%Z.
Hypothesis Hal : (psF mod 4 = 0 /\ pdF mod 4 = 0)%Z.
Hypothesis Hrow : forall i, (0 <= i < dh)%Z ->
  (datad <= pdF + 4 * dwpl * i /\ pdF + 4 * dwpl * i + 4 * nfw <= datad + nd /\
   datas <= psF + 4 * swpl * i /\ psF + 4 * swpl * i + 4 * nfw + 4 <= datas + ns)%Z.

Definition rg8_mregs (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 240) /\
  getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) /\ getr regs 22 = Z_to_bv 64 (psF + 4 * swpl * i) /\
  getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) /\ getr regs 24 = Z_to_bv 64 (pdF + 4 * dwpl * i) /\
  getr regs 11 = Z_to_bv 64 i /\
  getr regs 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs 7 = Z_to_bv 64 (4 * swpl) /\ getr regs 23 = Z_to_bv 64 0 /\
  getr regs 20 = Z_to_bv 64 (4 * nfw) /\ getr regs 25 = Z_to_bv 64 32 /\
  getr regs 26 = Z_to_bv 64 18446744073709551611 /\ getr regs 1 = Z_to_bv 64 31 /\
  getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

Definition rg8_iregs (regs : bvmap 5 word) (i w : Z) : Prop :=
  rg8_mregs regs i /\ getr regs 19 = Z_to_bv 64 (4 * w) /\ getr regs 16 = Z_to_bv 64 1 /\
  getr regs 28 = Z_to_bv 64 1 /\ getr regs 9 = Z_to_bv 64 1 /\ getr regs 21 = Z_to_bv 64 1.

(* [comment removed for export] *)
Lemma rg8_I_W : forall (k : nat) regs Mi i w, (0 <= i < dh)%Z -> (0 <= w)%Z -> (w + Z.of_nat k = nfw - 1)%Z ->
  rg8_inv B Mi datad nd -> rg8_iregs regs i w ->
  exists regs' M',
    msteps SEGS (mkst regs RG8_I Mi rom) (mkst regs' RG8_T2 M' rom)
    /\ rg8_inv B M' datad nd
    /\ regs_agree (fun r => In r [12; 15; 17; 19; 27]%list) regs regs'.
Proof.
  pose proof Hd as HD. pose proof Hsr as HS. pose proof Hdim as HM. pose proof Hs as HSS. pose proof Hnfw as HN.
  induction k as [|k IH]; intros regs Mi i w Hi Hw Hk HI IR;
    pose proof (Hrow i Hi) as HR;
    destruct IR as (MR & I19 & I16 & I28 & I9 & I21);
    pose proof MR as (M2 & M6 & M22 & M18 & M24 & M11 & M5 & M7 & M23 & M20 & M25 & M26 & M1 & M30 & M8);
    destruct (rg8_rd B Mi datas ns (psF + 4 * swpl * i + 4 * w) 4 (proj2 HI) SOKs ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bs0 & R0 & L0);
    destruct (rg8_rd B Mi datas ns (psF + 4 * swpl * i + 4 * w + 4) 4 (proj2 HI) SOKs ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bs1 & R1 & L1);
    destruct (rg8_rd B Mi datad nd (pdF + 4 * dwpl * i + 4 * w) 4 (proj2 HI) SOKd ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(change (Z.of_nat 4) with 4%Z; lia)) as (bd & RD & LD);
    pose proof (rg8_sok B Mi datad nd (pdF + 4 * dwpl * i + 4 * w) 4 (proj2 HI) SOKd ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 4) with 4%Z; lia)) as SOK.
  - destruct (rg8_I rom true regs Mi (psF + 4 * swpl * i) (pdF + 4 * dwpl * i) (4 * w) (4 * nfw) sls bs0 bs1 bd
                ltac:(lia) ltac:(lia) (ltac:(lia) : (4 * w + 4 = 4 * nfw)%Z) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) R0 L0 R1 L1 RD LD SOK M22 M6 M24 M18 I19 M20 I16 I28 I9 I21 M25 M26 M1 M30 M8)
      as (r1 & wv & S1 & E19 & AG1).
    exists r1, (wbytes Mi (Z_to_bv 64 (pdF + 4 * dwpl * i + 4 * w)) (word_to_le_bytes 4 wv)).
    split; [exact S1 | split; [| exact AG1]].
    apply rg8_inv_store; [exact HI | lia | lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 4) with 4%Z; lia].
  - destruct (rg8_I rom false regs Mi (psF + 4 * swpl * i) (pdF + 4 * dwpl * i) (4 * w) (4 * nfw) sls bs0 bs1 bd
                ltac:(lia) ltac:(lia) (ltac:(lia) : (4 * w + 4 < 4 * nfw)%Z) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) R0 L0 R1 L1 RD LD SOK M22 M6 M24 M18 I19 M20 I16 I28 I9 I21 M25 M26 M1 M30 M8)
      as (r1 & wv & S1 & E19 & AG1).
    assert (HI1 : rg8_inv B (wbytes Mi (Z_to_bv 64 (pdF + 4 * dwpl * i + 4 * w)) (word_to_le_bytes 4 wv)) datad nd)
      by (apply rg8_inv_store; [exact HI | lia | lia | lia | rewrite length_N_to_le_bytes; change (Z.of_nat 4) with 4%Z; lia]).
    assert (IR1 : rg8_iregs r1 i (w + 1)).
    { unfold rg8_iregs, rg8_mregs. repeat split; try agr AG1. rewrite E19. f_equal. lia. }
    destruct (IH r1 _ i (w + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 IR1) as (r2 & Mb & S2 & HI2 & AG2).
    exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2] |].
    split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]].
Qed.


(* [comment removed for export] *)
Lemma rg8_G_W : forall (k : nat) regs Mi i, (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z ->
  rg8_inv B Mi datad nd -> rg8_mregs regs i ->
  exists regs' M',
    msteps SEGS (mkst regs RG8_H2 Mi rom) (mkst regs' RG8_X2 M' rom)
    /\ rg8_inv B M' datad nd
    /\ regs_agree (fun r => In r [6; 9; 11; 12; 15; 16; 17; 18; 19; 21; 22; 24; 27; 28]%list) regs regs'.
Proof.
  pose proof Hd as HD. pose proof Hsr as HS. pose proof Hdim as HM. pose proof Hs as HSS. pose proof Hnfw as HN.
  assert (MA : forall r r' i', regs_agree (fun x => In x [9; 12; 15; 16; 17; 19; 21; 27; 28]%list) r r' ->
                 rg8_mregs r i' -> rg8_mregs r' i').
  { intros r r' i' AG (X2 & X6 & X22 & X18 & X24 & X11 & X5 & X7 & X23 & X20 & X25 & X26 & X1 & X30 & X8).
    unfold rg8_mregs. repeat split; agr AG. }
  induction k as [|k IH]; intros regs Mi i Hi Hk HI MR;
    assert (Hi' : (0 <= i < dh)%Z) by lia;
    pose proof (Hrow i Hi') as HR;
    pose proof MR as (M2 & M6 & M22 & M18 & M24 & M11 & M5 & M7 & M23 & M20 & M25 & M26 & M1 & M30 & M8);
    destruct (rg8_H2 rom regs Mi s nfw (psF + 4 * swpl * i) (pdF + 4 * dwpl * i) ltac:(lia) ltac:(lia) Hnfw ltac:(lia) ltac:(lia)
                (rg8_cell B Mi datad nd s (s - 128) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(change (Z.of_nat 8) with 8%Z; lia) Cnfw)
                (rg8_cell B Mi datad nd s (s - 208) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(change (Z.of_nat 8) with 8%Z; lia) C208)
                (rg8_cell B Mi datad nd s (s - 224) 8 _ HI FR ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(change (Z.of_nat 8) with 8%Z; lia) C224)
                M2 M6 M18) as (r1 & S1 & B19 & B16 & B28 & B9 & B21 & AG1);
    assert (IR1 : rg8_iregs r1 i 0)
      by (unfold rg8_iregs; split; [apply (MA regs r1 i); [regs_agree_weaken AG1 | exact MR]
                                   | split; [rewrite B19; reflexivity | repeat split; assumption]]);
    destruct (rg8_I_W (Z.to_nat (nfw - 1)) r1 Mi i 0 Hi' ltac:(lia) ltac:(lia) HI IR1) as (r2 & Ma & S2 & HI2 & AG2);
    assert (MR2 : rg8_mregs r2 i)
      by (apply (MA regs r2 i); [eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2] | exact MR]);
    destruct MR2 as (N2 & N6 & N22 & N18 & N24 & N11 & N5 & N7 & N23 & N20 & N25 & N26 & N1 & N30 & N8);
    pose proof (rg8_cell B Ma datad nd s (s - 120) 8 _ HI2 FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cz) as CZ;
    pose proof (rg8_cell B Ma datad nd s (s - 112) 8 _ HI2 FR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(change (Z.of_nat 8) with 8%Z; lia) Cdh) as CDH.
  - destruct (rg8_T2 rom true r2 Ma s i dh (4 * dwpl) (4 * swpl) (psF + 4 * swpl * i) (pdF + 4 * dwpl * i)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (ltac:(lia) : (i + 1 = dh)%Z) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CZ CDH N2 N11 N5 N7 N6 N22 N18 N24 N23)
      as (r3 & S3 & E11 & E6 & E22 & E18 & E24 & AG3).
    exists r3, Ma. split; [| split; [exact HI2 |]].
    + eapply msteps_trans; [exact S1 |]. eapply msteps_trans; [exact S2 | exact S3].
    + eapply regs_agree_trans; [regs_agree_weaken AG1 |].
      eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  - destruct (rg8_T2 rom false r2 Ma s i dh (4 * dwpl) (4 * swpl) (psF + 4 * swpl * i) (pdF + 4 * dwpl * i)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (ltac:(lia) : (i + 1 < dh)%Z) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CZ CDH N2 N11 N5 N7 N6 N22 N18 N24 N23)
      as (r3 & S3 & E11 & E6 & E22 & E18 & E24 & AG3).
    assert (MR3 : rg8_mregs r3 (i + 1)).
    { unfold rg8_mregs. repeat split; try agr AG3;
        first [rewrite E6 | rewrite E22 | rewrite E18 | rewrite E24 | rewrite E11]; first [reflexivity | f_equal; ring]. }
    destruct (IH r3 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI2 MR3) as (r4 & Mb & S4 & HI4 & AG4).
    exists r4, Mb. split; [| split; [exact HI4 |]].
    + eapply msteps_trans; [exact S1 |]. eapply msteps_trans; [exact S2 |]. eapply msteps_trans; [exact S3 | exact S4].
    + eapply regs_agree_trans; [regs_agree_weaken AG1 |].
      eapply regs_agree_trans; [regs_agree_weaken AG2 |].
      eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4].
Qed.
End MLoop.
End RopGen8W.

Definition rg8_w1 (s z : Z) : Prop := (z < s - 240 \/ s - 232 <= z)%Z.

Definition rg8_w3 (s z : Z) : Prop :=
  ((z < s - 240 \/ s - 232 <= z) /\ (z < s - 224 \/ s - 216 <= z) /\ (z < s - 208 \/ s - 200 <= z))%Z.

Definition rg8_fx (P : Z -> Prop) (M0 M : word -> option byte) (datad nd : Z) : Prop :=
  (forall x : word, (bv_unsigned x < datad \/ datad + nd <= bv_unsigned x)%Z -> P (bv_unsigned x) -> M x = M0 x) /\ mem_grows M0 M.

Lemma rg8_fx_refl : forall P M datad nd, rg8_fx P M M datad nd.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma rg8_fx_inv : forall P M0 M M' datad nd, rg8_fx P M0 M datad nd -> rg8_inv M M' datad nd -> rg8_fx P M0 M' datad nd.
Proof.
  intros P M0 M M' datad nd [E1 G1] [E2 G2]. split.
  - intros x Hx Hy. rewrite (E2 x Hx). apply E1; assumption.
  - eapply mem_grows_trans; eassumption.
Qed.

Lemma rg8_fx_weak : forall (P Q : Z -> Prop) M0 M datad nd, rg8_fx P M0 M datad nd -> (forall z, Q z -> P z) ->
  rg8_fx Q M0 M datad nd.
Proof. intros P Q M0 M datad nd [E G] HQ. split; [intros x Hx Hy; apply E; [exact Hx | apply HQ, Hy] | exact G]. Qed.

Lemma rg8_fx_wb : forall (P : Z -> Prop) M0 M datad nd (a : Z) (v : word), rg8_fx P M0 M datad nd ->
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (forall z, P z -> z < a \/ a + 8 <= z)%Z ->
  rg8_fx P M0 (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 v)) datad nd.
Proof.
  intros P M0 M datad nd a v [E G] H0 H1 HP. split.
  - intros x Hx Hy. specialize (HP _ Hy).
    rewrite MemSplit.wbytes_outside by (rewrite length_N_to_le_bytes, u_Z2bv by lia; change (Z.of_nat 8) with 8%Z; lia).
    apply E; assumption.
  - eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.

Lemma rg8_fx_rd8 : forall (P : Z -> Prop) M0 M s datad nd (a : Z) bs, rg8_fx P M0 M datad nd -> disj_apart datad nd (s - 240) 240 ->
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (s - 240 <= a)%Z -> (a + 8 <= s)%Z -> (forall z, a <= z < a + 8 -> P z)%Z ->
  rdn SEGS M0 (Z_to_bv 64 a) 8 = Some bs -> rdn SEGS M (Z_to_bv 64 a) 8 = Some bs.
Proof.
  intros P M0 M s datad nd a bs [E _] FR H0 H1 Ha Hn HP HM. use_apart FR. rewrite <- HM.
  apply rdn_ext; rewrite u_Z2bv by lia; change (Z.of_nat 8) with 8%Z; [lia |].
  intros x Hx. apply E; [lia | apply HP; lia].
Qed.

Lemma rg8_fx_rows : forall (P : Z -> Prop) M0 M s datad nd dh, rg8_fx P M0 M datad nd -> disj_apart datad nd (s - 240) 240 ->
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (forall z, s - 200 <= z < s - 152 -> P z)%Z -> rg_rows M0 s dh -> rg_rows M s dh.
Proof.
  intros P M0 M s datad nd dh FX FR H0 H1 HP (c28 & c30 & c38 & c40 & c48 & c50 & R1 & R2 & R3 & R4 & R5 & R6 & RB).
  exists c28, c30, c38, c40, c48, c50.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ RB))))));
    (eapply (rg8_fx_rd8 P M0 M s datad nd); [exact FX | exact FR | lia | lia | lia | lia | intros z Hz; apply HP; lia | eassumption]).
Qed.

Lemma rg8_fx_rg_inv : forall (P : Z -> Prop) MB M s datad nd, rg8_fx P MB M datad nd ->
  (forall z, z < s - 240 \/ s - 112 <= z -> P z)%Z -> rg_inv MB M s datad nd.
Proof.
  intros P MB M s datad nd [E G] HP. split; [intros x Hx Hy; apply E; [exact Hx | apply HP, Hy] | exact G].
Qed.

Lemma rg8_rd_wb8 : forall M (a b : Z) (v w : word), (0 <= a)%Z -> (0 <= b)%Z -> (a + 8 <= 2 ^ 64)%Z -> (b + 8 <= 2 ^ 64)%Z ->
  (b + 8 <= a \/ a + 8 <= b)%Z ->
  rdn SEGS (wbytes (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (Z_to_bv 64 b) (word_to_le_bytes 8 w)) (Z_to_bv 64 a) 8
  = Some (word_to_le_bytes 8 v).
Proof.
  intros M a b v w H0 H1 H2 H3 H4.
  rewrite <- (rdn_wbytes_hit8 SEGS M (Z_to_bv 64 a) v) by (rewrite u_Z2bv by lia; lia).
  apply rdn_ext; rewrite u_Z2bv by lia; change (Z.of_nat 8) with 8%Z; [lia |].
  intros x Hx.
  rewrite MemSplit.wbytes_outside by (rewrite length_N_to_le_bytes, u_Z2bv by lia; change (Z.of_nat 8) with 8%Z; lia).
  reflexivity.
Qed.

Ltac pw := intros; unfold rg8_w1, rg8_w3 in *; lia.

Ltac agrs := repeat match goal with
  | AG : regs_agree _ _ ?r1 |- getr ?r1 ?x = _ => rewrite (AG x ltac:(notin_list))
  end; assumption.

Ltac rg8_cp FX FR M P a C nm :=
  pose proof (rg8_fx_rd8 P _ M _ _ _ a _ FX FR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw) C) as nm.

Section RopGen8T.
Context {fx : FPState}.

(* [comment removed for export] *)
Theorem rg8_loops_W : rg_loops_spec RG8_S1.
Proof.
  intros MB rom s datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl fw f6 f7 nofull nolast f3 regs
    BLK GEO CELLS REGS.
  destruct BLK as (Hs & Hd & Hsr & SOKd & SOKs & SOKf & FR).
  destruct GEO as (Hdim0 & (Hdx1 & Hdx2) & Hnf & GF & GM & GL).
  destruct CELLS as (C216 & C208 & C152 & C120 & C112 & CROW & C224 & C128 & C232 & C136 & C144).
  destruct REGS as (R2 & R1 & R14 & R30 & R8 & RF & RM & RL).
  pose proof Hs as (Hs1 & Hs2). pose proof Hd as (Hd1 & Hd2 & Hd3 & Hd4). pose proof Hsr as (Hr1 & Hr2 & Hr3 & Hr4).
  pose proof Hdim0 as (Hdh & Hsw & Hdw & Hsl & Hnfw).
  pose proof (conj Hdh (conj Hsw (conj Hdw Hsl))) as Hdim.
  assert (SF : forall M (a : Z) (n : nat), mem_grows MB M -> (s - 240 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
                 store_ok SEGS M (Z_to_bv 64 a) n = true)
    by (intros M a n G Ha Hn; exact (rg8_sok MB M (s - 240) 240 a n G SOKf ltac:(lia) ltac:(lia) Ha ltac:(lia))).
  destruct (rg8_S1 rom fw f6 f7 regs MB s dxb psf pdf swpl dwpl dh
              ltac:(lia) ltac:(lia) ltac:(lia) Hdx2 ltac:(lia) ltac:(lia) R1 R2 R14
              (SF MB (s - 240)%Z 8%nat (mem_grows_refl MB) ltac:(lia) ltac:(change (Z.of_nat 8) with 8%Z; lia))
              ltac:(intros FW; destruct (GF FW) as ((Ha1 & Ha2) & GR); destruct (GR 0%Z ltac:(lia)) as (X1 & X2 & X3 & X4);
                    assert (X5 : (psf + 4 * swpl * 0 + 4 <= datas + ns)%Z) by (destruct (f6 && negb f7); lia);
                    destruct (RF FW) as (Q15 & Q25 & Q26);
                    refine (conj _ (conj _ (conj Ha1 (conj Ha2 (conj Hdh (conj Q15 (conj Q25 (conj Q26
                      (conj (C224 FW) (conj C152 (CROW (or_introl FW)))))))))))); lia))
    as (r1 & ST1 & EF & AG1).
  assert (P1 : exists r2 m2, msteps SEGS (mkst regs RG8_S1 MB rom) (mkst r2 RG8_X1 m2 rom) /\ rg8_fx (rg8_w1 s) MB m2 datad nd /\
                 regs_agree (fun r => In r [1; 5; 7; 9; 11; 12; 13; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs r2).
  { destruct fw.
    - destruct (EF eq_refl) as (F11 & F20 & F27 & F7 & F16 & F28 & F9 & F19 & F24 & F13 & F23 & F1 & F22).
      destruct (GF eq_refl) as (Hal & GR). destruct (RF eq_refl) as (Q15 & Q25 & Q26).
      pose (nm := v_xor (getr regs 31) (Z_to_bv 64 (-1))).
      pose (m1 := wbytes MB (Z_to_bv 64 (s - 240)) (word_to_le_bytes 8 nm)).
      assert (FX1 : rg8_fx (rg8_w1 s) MB m1 datad nd)
        by exact (rg8_fx_wb (rg8_w1 s) MB MB datad nd (s - 240) nm (rg8_fx_refl _ MB datad nd) ltac:(lia) ltac:(lia) ltac:(pw)).
      pose proof (proj2 FX1) as G1.
      rg8_cp FX1 FR m1 (rg8_w1 s) (s - 120)%Z C120 Cz1.
      assert (Cnm1 : rdn SEGS m1 (Z_to_bv 64 (s - 240)) 8 = Some (word_to_le_bytes 8 nm))
        by (apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia).
      destruct (rg8_F_W rom s datad nd datas ns dh swpl dwpl sls Hs Hd Hsr FR Hdim m1 psf pdf f6 f7 nm
                  (store_ok_mono _ _ _ _ _ G1 SOKd) (store_ok_mono _ _ _ _ _ G1 SOKs) Cz1 Cnm1 GR
                  (Z.to_nat (dh - 1)) r1 m1 0%Z ltac:(lia) ltac:(lia) (rg8_inv_refl m1 datad nd)
                  ltac:(unfold rg8_fregs; rewrite ?Z.mul_0_r, ?Z.add_0_r, ?Z.sub_0_r; repeat split; first [assumption | agrs]))
        as (r2 & m2 & ST2 & HI2 & AG2).
      exists r2, m2. split; [eapply msteps_trans; [exact ST1 | exact ST2] |].
      split; [exact (rg8_fx_inv _ _ _ _ _ _ FX1 HI2) |].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    - exists r1, MB. split; [exact ST1 |]. split; [apply rg8_fx_refl |]. regs_agree_weaken AG1. }
  destruct P1 as (r2 & m2 & ST2 & FX2 & AG2).
  pose proof (proj2 FX2) as G2.
  rg8_cp FX2 FR m2 (rg8_w1 s) (s - 208)%Z C208 D208.
  destruct (rg8_X1 rom nofull r2 m2 s psF pdF nfw swpl dwpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) D208
              (SF m2 (s - 208)%Z 8%nat G2 ltac:(lia) ltac:(change (Z.of_nat 8) with 8%Z; lia))
              (SF m2 (s - 224)%Z 8%nat G2 ltac:(lia) ltac:(change (Z.of_nat 8) with 8%Z; lia))
              ltac:(agrs) ltac:(agrs)
              ltac:(intros NF; destruct (GM NF) as ((Hm1 & Hm2) & GRm); destruct (GRm 0%Z ltac:(lia)) as (Y1 & Y2 & Y3 & Y4);
                    destruct (RM NF) as (Q6 & Q18);
                    rg8_cp FX2 FR m2 (rg8_w1 s) (s - 152)%Z C152 D152; rg8_cp FX2 FR m2 (rg8_w1 s) (s - 128)%Z (C128 NF) D128;
                    refine (conj _ (conj _ (conj Hm1 (conj Hm2 (conj _ (conj _ (conj D152 D128))))))); [lia | lia | agrs | agrs]))
    as (r3 & ST3 & EX & AG3).
  assert (P2 : exists r4 m4, msteps SEGS (mkst regs RG8_S1 MB rom) (mkst r4 RG8_X2 m4 rom) /\ rg8_fx (rg8_w3 s) MB m4 datad nd /\
                 regs_agree (fun r => In r [1; 5; 6; 7; 9; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs r4).
  { destruct nofull.
    - exists r3, m2. split; [eapply msteps_trans; [exact ST2 | exact ST3] |].
      split; [exact (rg8_fx_weak _ (rg8_w3 s) _ _ _ _ FX2 ltac:(pw)) |].
      eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
    - destruct (EX eq_refl) as (X11 & X5 & X7 & X20 & X23 & X25 & X26 & X15 & X12 & X1' & X22 & X24).
      destruct (GM eq_refl) as (Hal & GRm). destruct (RM eq_refl) as (Q6 & Q18).
      pose (m3 := wbytes (wbytes m2 (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                    (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 1))).
      assert (FX3 : rg8_fx (rg8_w3 s) MB m3 datad nd)
        by exact (rg8_fx_wb _ _ _ _ _ (s - 224) (Z_to_bv 64 1)
                    (rg8_fx_wb _ _ _ _ _ (s - 208) (Z_to_bv 64 1) (rg8_fx_weak _ (rg8_w3 s) _ _ _ _ FX2 ltac:(pw))
                       ltac:(lia) ltac:(lia) ltac:(pw))
                    ltac:(lia) ltac:(lia) ltac:(pw)).
      pose proof (proj2 FX3) as G3.
      rg8_cp FX3 FR m3 (rg8_w3 s) (s - 120)%Z C120 Cz3.
      rg8_cp FX3 FR m3 (rg8_w3 s) (s - 112)%Z C112 Cdh3.
      rg8_cp FX3 FR m3 (rg8_w3 s) (s - 128)%Z (C128 eq_refl) Cnfw3.
      assert (C2243 : rdn SEGS m3 (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)))
        by (apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia).
      pose proof (rg8_rd_wb8 m2 (s - 208) (s - 224) (Z_to_bv 64 1) (Z_to_bv 64 1)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as C2083.
      destruct (rg8_G_W rom s datad nd datas ns dh swpl dwpl sls Hs Hd Hsr FR Hdim m3 psF pdF nfw
                  (store_ok_mono _ _ _ _ _ G3 SOKd) (store_ok_mono _ _ _ _ _ G3 SOKs) Cz3 Cdh3 Cnfw3 C2083 C2243
                  ltac:(specialize (Hnf eq_refl); lia) GRm
                  (Z.to_nat (dh - 1)) r3 m3 0%Z ltac:(lia) ltac:(lia) (rg8_inv_refl m3 datad nd)
                  ltac:(unfold rg8_mregs; rewrite ?Z.mul_0_r, ?Z.add_0_r; repeat split; first [assumption | agrs]))
        as (r4 & m4 & ST4 & HI4 & AG4).
      exists r4, m4. split; [eapply msteps_trans; [exact ST2 |]; eapply msteps_trans; [exact ST3 | exact ST4] |].
      split; [exact (rg8_fx_inv _ _ _ _ _ _ FX3 HI4) |].
      eapply regs_agree_trans; [regs_agree_weaken AG2 |].
      eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4]. }
  destruct P2 as (r4 & m4 & ST4 & FX4 & AG4).
  pose proof (proj2 FX4) as G4.
  rg8_cp FX4 FR m4 (rg8_w3 s) (s - 216)%Z C216 D216.
  destruct (rg8_X2 rom nolast f3 r4 m4 s psl pdl swpl dwpl dh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) D216 ltac:(agrs) ltac:(agrs)
              ltac:(intros NL; destruct (GL NL) as ((Hl1 & Hl2) & GRl); destruct (GRl 0%Z ltac:(lia)) as (Z1 & Z2 & Z3 & Z4);
                    assert (Z5 : (psl + 4 * swpl * 0 + 4 <= datas + ns)%Z) by (destruct f3; lia);
                    pose proof (RL NL) as Q10; destruct (C144 NL) as (mk & Cmk);
                    rg8_cp FX4 FR m4 (rg8_w3 s) (s - 136)%Z (C136 NL) D136; rg8_cp FX4 FR m4 (rg8_w3 s) (s - 232)%Z (C232 NL) D232;
                    rg8_cp FX4 FR m4 (rg8_w3 s) (s - 152)%Z C152 D152; rg8_cp FX4 FR m4 (rg8_w3 s) (s - 144)%Z Cmk D144;
                    refine (conj _ (conj _ (conj Hl1 (conj Hl2 (conj Hdh (conj _ (conj D136 (conj D232 (conj D152
                              (conj (ex_intro _ mk D144) _))))))))));
                    [lia | lia | agrs
                    | exact (rg8_fx_rows _ _ _ _ _ _ dh FX4 FR ltac:(lia) ltac:(lia) ltac:(pw) (CROW (or_intror NL)))]))
    as (r5 & ST5 & EX2 & AG5).
  destruct nolast.
  - exists r5, m4. split; [eapply msteps_trans; [exact ST4 | exact ST5] |].
    split; [exact (rg8_fx_rg_inv (rg8_w3 s) MB m4 s datad nd FX4 ltac:(pw)) |].
    split; [agrs |].
    eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5].
  - destruct (EX2 eq_refl) as (L11 & L15 & L6 & L17 & L9 & L16 & L5 & L14 & L7 & L28 & L19 & L20).
    destruct (GL eq_refl) as (Hal & GRl). destruct (C144 eq_refl) as (mk & Cmk). pose proof (RL eq_refl) as Q10.
    rg8_cp FX4 FR m4 (rg8_w3 s) (s - 120)%Z C120 Cz4.
    rg8_cp FX4 FR m4 (rg8_w3 s) (s - 136)%Z (C136 eq_refl) Cpsl4.
    rg8_cp FX4 FR m4 (rg8_w3 s) (s - 144)%Z Cmk Cmk4.
    destruct (rg8_L_W rom s datad nd datas ns dh swpl dwpl sls Hs Hd Hsr FR Hdim m4 psl pdl f3 mk
                (store_ok_mono _ _ _ _ _ G4 SOKd) (store_ok_mono _ _ _ _ _ G4 SOKs) Cz4 Cpsl4 Cmk4 GRl
                (Z.to_nat (dh - 1)) r5 m4 0%Z ltac:(lia) ltac:(lia) (rg8_inv_refl m4 datad nd)
                ltac:(unfold rg8_lregs; rewrite ?Z.mul_0_r, ?Z.add_0_r, ?Z.sub_0_r; repeat split; first [assumption | agrs]))
      as (r6 & m6 & ST6 & HI6 & AG6).
    exists r6, m6. split; [eapply msteps_trans; [exact ST4 |]; eapply msteps_trans; [exact ST5 | exact ST6] |].
    split; [exact (rg8_fx_rg_inv (rg8_w3 s) MB m6 s datad nd (rg8_fx_inv _ _ _ _ _ _ FX4 HI6) ltac:(pw)) |].
    split; [agrs |].
    eapply regs_agree_trans; [regs_agree_weaken AG4 |].
    eapply regs_agree_trans; [regs_agree_weaken AG5 | regs_agree_weaken AG6].
Qed.

End RopGen8T.
