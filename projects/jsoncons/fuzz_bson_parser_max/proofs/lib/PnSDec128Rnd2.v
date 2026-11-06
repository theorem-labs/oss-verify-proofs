(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3 Bs0PlanKit PmStep PmKeep PnDecFacts PnMemW PnSDec128Defs PnSDec128RP PnSDec128Rnd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDRN2.
Import PNSDRN.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Call.

Variables (R0 : bvmap 5 word) (S first sigma e V r : Z).
Hypothesis Fr : 0 <= r < 2 ^ 47.
Hypothesis FS : 140735332483312 <= S <= 140737488355328.
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432.
Hypothesis Fe : 0 <= e <= 16383.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FV : 0 <= V < 2 ^ 113.

Abbreviation saves := (PNSDD.saves R0 S r).
Abbreviation MI := (PNSDD.MI R0 S first r).
Abbreviation cell := (PNSDD.cell S).
Abbreviation digs := (PNSDD.digs S V).
Abbreviation zers := (PNSDD.zers S).
Abbreviation RR := (PNSDRN.RR R0 S first sigma e).
Abbreviation ufacts := (PNSDRN.ufacts R0 S).
Abbreviation MI_xfer := (PNSDD.MI_xfer R0 S first r FS).
Abbreviation cell_xfer := (PNSDD.cell_xfer S FS).
Abbreviation limbs := (PNSDRN.limbs R0 S first sigma e r Fr FS F16 Ffirst Fdj Fe Fsig).
(* [comment removed for export] *)
Definition VV (k : Z) (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => sigma | 40%nat => k | 50%nat => e
  | 60%nat => r | 61%nat => bv_unsigned (getr R0 (reg 8)) | 62%nat => bv_unsigned (getr R0 (reg 9)) | 63%nat => bv_unsigned (getr R0 (reg 18))
  | 64%nat => bv_unsigned (getr R0 (reg 19)) | 65%nat => bv_unsigned (getr R0 (reg 20)) | 66%nat => bv_unsigned (getr R0 (reg 21))
  | 67%nat => bv_unsigned (getr R0 (reg 22)) | 68%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reload fx R M k rr D0 D1 :
  RR R k -> getr R (reg 29) = Z_to_bv 64 k -> getr R (reg 20) = Z_to_bv 64 rr ->
  0 <= k <= 3 -> 0 <= rr < 1000000000 -> 0 <= D0 < 2 ^ 64 -> 0 <= D1 < 2 ^ 64 -> MI M ->
  L5.u64_at RSEGS M (S - 240) D0 -> L5.u64_at RSEGS M (S - 232) D1 ->
  exists fx' R',
    RR R' k /\ getr R' (reg 29) = Z_to_bv 64 k /\ getr R' (reg 20) = Z_to_bv 64 rr /\ getr R' (reg 19) = getr R (reg 19)
    /\ bv_unsigned (getr R' (reg 12)) = D0 / 4294967296 /\ getr R' (reg 30) = Z_to_bv 64 D0 /\ getr R' (reg 31) = Z_to_bv 64 D1
    /\ ((rr = 0 /\ msteps RSEGS (st fx R 0x37be8 M) (st fx' R' 0x37c2c M))
        \/ (1 <= rr /\ msteps RSEGS (st fx R 0x37be8 M) (st fx' R' 0x37bfc M) /\ getr R' (reg 21) = Z_to_bv 64 (S - 184 + 36 * k))).
Proof.
  intros RRk G29 G20 Hk Hrr HD0 HD1 MIM C0 C1.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RRk as (G2 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G13 & G14 & G15 & G16 & G17 & G18 & G28 & G3 & G4 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDRP.dkRM_conc fx R M (fun i => match i with 46%nat => D0 | 47%nat => D1 | 48%nat => rr | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRM_conc fx R M (fun i => match i with 46%nat => D0 | 47%nat => D1 | 48%nat => rr | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A12 & A30 & A31 & Hz) | (MS1 & KS1 & A12 & A21 & A30 & A31 & Hnz) ]).
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    exists fx1, R1. split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact A12|]. split; [exact A30|]. split; [exact A31|].
    left. split; [clear -Hz Hrr; rewrite Z.mod_small in Hz by lia; lia| exact MS1].
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    exists fx1, R1. split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact A12|]. split; [exact A30|]. split; [exact A31|].
    right. split; [clear -Hnz Hrr; rewrite Z.mod_small in Hnz by lia; lia|]. split; [exact MS1| PMK.sc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rdig (rr m : Z) : Z := (rr / 10 ^ (8 - m)) mod 10.
Lemma rdS rr j m : 0 <= rr < 1000000000 -> Z.of_nat j = 8 - m -> PNDF.Dz (PNDF.Qn j rr) = rdig rr m.
Proof. intros H E. unfold rdig. rewrite <- E. apply PNDF.cellS_val. clear -H; lia. Qed.
Lemma rd0 rr : 0 <= rr < 1000000000 -> PNDF.Qn 8 rr = rdig rr 0.
Proof. intros H. unfold rdig. replace (8 - 0) with 8 by (clear; lia). apply PNDF.cell0_val. clear -H; lia. Qed.
Lemma nine9 (P : Z -> Prop) : P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> forall m, 0 <= m <= 8 -> P m.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 m Hm.
  assert (D : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8) by (clear -Hm; lia).
  destruct D as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; assumption.
Qed.
Lemma rd8 rr : 0 <= rr < 1000000000 -> PNDF.Dz rr = rdig rr 8.
Proof. intros H. apply (rdS rr 0 8 H eq_refl). Qed.
(* [comment removed for export] *)
Lemma Qz_fold x : ((((4294967296 * x) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368 = PNDF.Qz x. Proof. reflexivity. Qed.
Lemma Dz_fold x : ((x + ((18446744073709551606 * PNDF.Qz x) mod 2 ^ 64)) mod 2 ^ 64) = PNDF.Dz x. Proof. reflexivity. Qed.
Lemma Qz_rr x : PNDF.Qz x = PNDF.Qz (PNDF.Qn 0 x). Proof. reflexivity. Qed.
Lemma QzQn j x : PNDF.Qz (PNDF.Qn j x) = PNDF.Qn (Datatypes.S j) x. Proof. reflexivity. Qed.
Local Ltac cget D k m j rr Hrr :=
  lazymatch type of D with L5.u32_at _ ?Mx ?a _ =>
    replace a with (S - 216 + 4 * (9 * k + m)) in D by (clear; lia);
    rewrite !Qz_fold in D; rewrite ?Dz_fold in D; rewrite ?(Qz_rr rr) in D; rewrite ?QzQn in D;
    first [ rewrite (rdS rr j m Hrr eq_refl) in D | rewrite (rd0 rr Hrr) in D | rewrite (rd8 rr Hrr) in D ];
    lazymatch type of D with L5.u32_at _ _ _ ?v => change (PNSDD.cell S Mx (9 * k + m) v) in D end end.

Lemma digits fx R M k rr :
  RR R k -> getr R (reg 29) = Z_to_bv 64 k -> getr R (reg 20) = Z_to_bv 64 rr -> getr R (reg 21) = Z_to_bv 64 (S - 184 + 36 * k) ->
  getr R (reg 19) = Z_to_bv 64 (S - 220 + 36 * k) ->
  0 <= k <= 3 -> 1 <= rr < 1000000000 -> MI M ->
  exists fx' R' M', msteps RSEGS (st fx R 0x37bfc M) (st fx' R' 0x37c2c M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 216 + 36 * k <= a < S - 216 + 36 * k + 36) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RR R' k /\ getr R' (reg 29) = Z_to_bv 64 k /\ getr R' (reg 12) = getr R (reg 12) /\ getr R' (reg 30) = getr R (reg 30)
    /\ getr R' (reg 31) = getr R (reg 31) /\ MI M'
    /\ (forall m, 0 <= m <= 8 -> cell M' (9 * k + m) (rdig rr m)).
Proof.
  intros RRk G29 G20 G21 G19 Hk Hrr MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  assert (Hrr' : 0 <= rr < 1000000000) by (clear -Hrr; lia).
  destruct RRk as (G2 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G13 & G14 & G15 & G16 & G17 & G18 & G28 & G3 & G4 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (HK : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by (clear -Hk; lia).
  destruct HK as [-> |[-> |[-> | ->]]].
  - (let T := type of (PNSDRP.dkRD0_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 0 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRD0_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 0 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A20 & A21 & A22 & A23 & D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)); PMK.pvz_clrT.
    cget D0 0 0 8%nat rr Hrr'. cget D1 0 1 7%nat rr Hrr'. cget D2 0 2 6%nat rr Hrr'. cget D3 0 3 5%nat rr Hrr'. cget D4 0 4 4%nat rr Hrr'.
    cget D5 0 5 3%nat rr Hrr'. cget D6 0 6 2%nat rr Hrr'. cget D7 0 7 1%nat rr Hrr'. cget D8 0 8 0%nat rr Hrr'.
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split. { apply (MI_xfer M M1 MIM MG1). intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    apply nine9; assumption.
  - (let T := type of (PNSDRP.dkRD1_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 1 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRD1_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 1 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A20 & A21 & A22 & A23 & D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)); PMK.pvz_clrT.
    cget D0 1 0 8%nat rr Hrr'. cget D1 1 1 7%nat rr Hrr'. cget D2 1 2 6%nat rr Hrr'. cget D3 1 3 5%nat rr Hrr'. cget D4 1 4 4%nat rr Hrr'.
    cget D5 1 5 3%nat rr Hrr'. cget D6 1 6 2%nat rr Hrr'. cget D7 1 7 1%nat rr Hrr'. cget D8 1 8 0%nat rr Hrr'.
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split. { apply (MI_xfer M M1 MIM MG1). intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    apply nine9; assumption.
  - (let T := type of (PNSDRP.dkRD2_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 2 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRD2_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 2 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A20 & A21 & A22 & A23 & D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)); PMK.pvz_clrT.
    cget D0 2 0 8%nat rr Hrr'. cget D1 2 1 7%nat rr Hrr'. cget D2 2 2 6%nat rr Hrr'. cget D3 2 3 5%nat rr Hrr'. cget D4 2 4 4%nat rr Hrr'.
    cget D5 2 5 3%nat rr Hrr'. cget D6 2 6 2%nat rr Hrr'. cget D7 2 7 1%nat rr Hrr'. cget D8 2 8 0%nat rr Hrr'.
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split. { apply (MI_xfer M M1 MIM MG1). intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    apply nine9; assumption.
  - (let T := type of (PNSDRP.dkRD3_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 3 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRD3_conc fx R M (fun i => match i with 48%nat => rr | _ => VV 3 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A20 & A21 & A22 & A23 & D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)); PMK.pvz_clrT.
    cget D0 3 0 8%nat rr Hrr'. cget D1 3 1 7%nat rr Hrr'. cget D2 3 2 6%nat rr Hrr'. cget D3 3 3 5%nat rr Hrr'. cget D4 3 4 4%nat rr Hrr'.
    cget D5 3 5 3%nat rr Hrr'. cget D6 3 6 2%nat rr Hrr'. cget D7 3 7 1%nat rr Hrr'. cget D8 3 8 0%nat rr Hrr'.
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split. { apply (MI_xfer M M1 MIM MG1). intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
    apply nine9; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail fx R M k c :
  RR R k -> getr R (reg 29) = Z_to_bv 64 k -> 0 <= k <= 3 -> cell M 0 c -> 0 <= c <= 9 -> MI M ->
  exists fx' R',
    PNSDD.RB R0 S first sigma R' /\ getr R' (reg 10) = Z_to_bv 64 e /\ getr R' (reg 11) = Z_to_bv 64 (e - 6176)
    /\ getr R' (reg 30) = getr R (reg 30) /\ getr R' (reg 31) = getr R (reg 31)
    /\ ((k = 0 /\ msteps RSEGS (st fx R 0x37c2c M) (st fx' R' 0x37c40 M) /\ getr R' (reg 12) = Z_to_bv 64 c)
        \/ (1 <= k /\ msteps RSEGS (st fx R 0x37c2c M) (st fx' R' 0x37b84 M) /\ RR R' (k - 1) /\ getr R' (reg 19) = Z_to_bv 64 (k - 1)
             /\ getr R' (reg 12) = getr R (reg 12))).
Proof.
  intros RRk G29 Hk C0 Hc MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RRk as (G2 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G13 & G14 & G15 & G16 & G17 & G18 & G28 & G3 & G4 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof C0 as C0'. unfold PNSDD.cell in C0'. replace (S - 216 + 4 * 0) with (S - 216) in C0' by (clear; lia).
  (let T := type of (PNSDRP.dkRT_conc fx R M (fun i => match i with 51%nat => c | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRT_conc fx R M (fun i => match i with 51%nat => c | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A12 & A13 & A15 & A19 & Hz) | (MS1 & KS1 & A13 & A15 & A19 & Hnz) ]).
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    exists fx1, R1. split. { unfold PNSDD.RB. repeat apply conj; PMK.sc. } do 4 (split; [PMK.sc|]).
    left. split; [clear -Hz Hk; rewrite Z.mod_small in Hz by lia; lia|]. split; [exact MS1| exact A12].
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    exists fx1, R1. split. { unfold PNSDD.RB. repeat apply conj; PMK.sc. } do 4 (split; [PMK.sc|]).
    right. split; [clear -Hnz Hk; rewrite Z.mod_small in Hnz by lia; lia|]. split; [exact MS1|].
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. }
    split; PMK.sc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p0 (W : Z) : Z := W / 2 ^ 96.
Definition p1 (W : Z) : Z := (W / 2 ^ 64) mod 2 ^ 32.
Definition p2 (W : Z) : Z := (W / 2 ^ 32) mod 2 ^ 32.
Definition p3 (W : Z) : Z := W mod 2 ^ 32.
Lemma parts_val W : 0 <= W < 2 ^ 113 ->
  W = p0 W * 2 ^ 96 + p1 W * 2 ^ 64 + p2 W * 2 ^ 32 + p3 W /\ 0 <= p0 W < 2 ^ 17 /\ 0 <= p1 W < 2 ^ 32 /\ 0 <= p2 W < 2 ^ 32 /\ 0 <= p3 W < 2 ^ 32.
Proof.
  intros HW. unfold p0, p1, p2, p3.
  pose proof (Z.div_mod W (2 ^ 32) ltac:(clear; lia)) as E1. pose proof (Z.mod_pos_bound W (2 ^ 32) ltac:(clear; lia)) as B1.
  pose proof (Z.div_mod (W / 2 ^ 32) (2 ^ 32) ltac:(clear; lia)) as E2. pose proof (Z.mod_pos_bound (W / 2 ^ 32) (2 ^ 32) ltac:(clear; lia)) as B2.
  pose proof (Z.div_mod (W / 2 ^ 64) (2 ^ 32) ltac:(clear; lia)) as E3. pose proof (Z.mod_pos_bound (W / 2 ^ 64) (2 ^ 32) ltac:(clear; lia)) as B3.
  rewrite (Z.div_div W (2 ^ 32) (2 ^ 32)) in E2 by (clear; lia). change (2 ^ 32 * 2 ^ 32) with (2 ^ 64) in E2.
  rewrite (Z.div_div W (2 ^ 64) (2 ^ 32)) in E3 by (clear; lia). change (2 ^ 64 * 2 ^ 32) with (2 ^ 96) in E3.
  assert (B4 : 0 <= W / 2 ^ 96 < 2 ^ 17).
  { split; [apply Z.div_pos; clear -HW; lia|]. apply Z.div_lt_upper_bound; [clear; lia|]. change (2 ^ 96 * 2 ^ 17) with (2 ^ 113). clear -HW; lia. }
  assert (B5 : 0 <= W / 2 ^ 64) by (apply Z.div_pos; clear -HW; lia). assert (B6 : 0 <= W / 2 ^ 32) by (apply Z.div_pos; clear -HW; lia).
  clear -HW E1 B1 E2 B2 E3 B3 B4 B5 B6. repeat split; lia.
Qed.
Lemma limb_uniq Q q0 q1 q2 q3 : Q = q0 * 2 ^ 96 + q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3 ->
  0 <= q0 < 2 ^ 32 -> 0 <= q1 < 2 ^ 32 -> 0 <= q2 < 2 ^ 32 -> 0 <= q3 < 2 ^ 32 -> p0 Q = q0 /\ p1 Q = q1 /\ p2 Q = q2 /\ p3 Q = q3.
Proof.
  intros -> H0 H1 H2 H3. unfold p0, p1, p2, p3. repeat split.
  - replace (q0 * 2 ^ 96 + q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3) with ((q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3) + q0 * 2 ^ 96) by (clear; lia).
    rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -H1 H2 H3; lia). clear; lia.
  - replace (q0 * 2 ^ 96 + q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3) with ((q2 * 2 ^ 32 + q3) + (q1 + q0 * 2 ^ 32) * 2 ^ 64) by (clear; lia).
    rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -H2 H3; lia). rewrite Z.add_0_l. rewrite Z.mod_add by (clear; lia).
    apply Z.mod_small. clear -H1; lia.
  - replace (q0 * 2 ^ 96 + q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3) with (q3 + (q2 + (q1 + q0 * 2 ^ 32) * 2 ^ 32) * 2 ^ 32) by (clear; lia).
    rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -H3; lia). rewrite Z.add_0_l. rewrite Z.mod_add by (clear; lia).
    apply Z.mod_small. clear -H2; lia.
  - replace (q0 * 2 ^ 96 + q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3) with (q3 + (q2 + (q1 + q0 * 2 ^ 32) * 2 ^ 32) * 2 ^ 32) by (clear; lia).
    rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -H3; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma headfork fx R M k W :
  RR R k -> getr R (reg 19) = Z_to_bv 64 k -> 0 <= k <= 3 -> 0 <= W < 2 ^ 113 ->
  bv_unsigned (getr R (reg 30)) mod 2 ^ 32 = p0 W -> bv_unsigned (getr R (reg 12)) mod 2 ^ 32 = p1 W ->
  getr R (reg 31) = Z_to_bv 64 (p2 W + 4294967296 * p3 W) -> MI M ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 224) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ RR R' k /\ getr R' (reg 29) = Z_to_bv 64 k
    /\ ((W = 0 /\ msteps RSEGS (st fx R 0x37b84 M) (st fx' R' 0x37c2c M') /\ getr R' (reg 12) = Z_to_bv 64 0 /\ getr R' (reg 31) = Z_to_bv 64 0
           /\ bv_unsigned (getr R' (reg 30)) = 0)
        \/ (0 < W /\ msteps RSEGS (st fx R 0x37b84 M) (st fx' R' 0x37bbc M') /\ getr R' (reg 12) = Z_to_bv 64 (S - 240)
           /\ getr R' (reg 19) = Z_to_bv 64 (S - 220 + 36 * k) /\ getr R' (reg 20) = Z_to_bv 64 0
           /\ L5.u32_at RSEGS M' (S - 240) (p0 W) /\ L5.u32_at RSEGS M' (S - 236) (p1 W) /\ L5.u32_at RSEGS M' (S - 232) (p2 W)
           /\ L5.u32_at RSEGS M' (S - 228) (p3 W))).
Proof.
  intros RRk G19 Hk HW H30 H12 G31 MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof (parts_val W HW) as (EW & B0 & B1 & B2 & B3).
  set (q0 := p0 W) in *. set (q1 := p1 W) in *. set (q2 := p2 W) in *. set (q3 := p3 W) in *. clearbody q0 q1 q2 q3.
  set (u30 := bv_unsigned (getr R (reg 30))) in *. set (u12 := bv_unsigned (getr R (reg 12))) in *.
  pose proof (bv_unsigned_in_range _ (getr R (reg 30))) as R30. pose proof (bv_unsigned_in_range _ (getr R (reg 12))) as R12.
  unfold bv_modulus in R30, R12. fold u30 in R30. fold u12 in R12.
  assert (G30 : getr R (reg 30) = Z_to_bv 64 u30) by (apply PNSDRN.to_bv_of_unsigned; reflexivity).
  assert (G12 : getr R (reg 12) = Z_to_bv 64 u12) by (apply PNSDRN.to_bv_of_unsigned; reflexivity).
  clearbody u30 u12.
  set (D1 := q2 + 4294967296 * q3) in *. set (D0 := q0 + 4294967296 * q1).
  assert (HD1 : 0 <= D1 < 2 ^ 64) by (subst D1; clear -B2 B3; lia). assert (HD0 : 0 <= D0 < 2 ^ 64) by (subst D0; clear -B0 B1; lia).
  destruct RRk as (G2 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G13 & G14 & G15 & G16 & G17 & G18 & G28 & G3 & G4 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDRP.dkRH_conc fx R M (fun i => match i with 41%nat => u30 | 42%nat => D1 | 43%nat => u12 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRH_conc fx R M (fun i => match i with 41%nat => u30 | 42%nat => D1 | 43%nat => u12 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A12 & A29 & A30 & C232 & C240)); PMK.pvz_clrT.
  rewrite (PNDF.dword0_val u12 u30) in A12, A30, C240 by (clear -R30 R12; lia).
  rewrite H30, H12 in A12, A30, C240. fold D0 in A12, A30, C240.
  pose proof (MI_xfer M M1 MIM MG1 ltac:(intros a Ha Hn; apply (FZ1 a Ha); clear -Hn; lia)) as MI1.
  pose proof MI1 as (WRf1 & WR11 & IC1 & (T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19)).
  pose proof (PNDF.lor_bound D0 D1 64 ltac:(clear; lia) HD0 HD1) as HL.
  assert (G30' : getr R1 (reg 30) = Z_to_bv 64 (Z.lor D0 D1)) by (apply PNSDRN.to_bv_of_unsigned; exact A30).
  (let T := type of (PNSDRP.dkRF_conc fx1 R1 M1 (fun i => match i with 44%nat => Z.lor D0 D1 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkRF_conc fx1 R1 M1 (fun i => match i with 44%nat => Z.lor D0 D1 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & [ (MS2 & KS2 & B12 & B31 & Hz) | (MS2 & KS2 & B12 & B19 & B20 & Hnz) ]).
  - assert (EM : M2 = M1) by (apply functional_extensionality; exact FW2). subst M2.
    rewrite Z.sub_0_r, Z.mod_small in Hz by exact HL.
    assert (HZ : Z.lor D0 D1 = 0) by (clear -Hz HL; lia).
    subst D0 D1. apply (PNDF.parts_zero_iff q0 q1 q2 q3) in HZ; [| clear -B0; lia| exact B1| exact B2| exact B3].
    exists fx2, R2, M1. split; [exact MG1|]. split; [intros a Ha Hn; apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact MI1|].
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. } split; [PMK.sc|].
    left. split; [clear -HZ EW; lia|]. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
    split; [exact B12|]. split; [exact B31|].
    rewrite (KS2 30%nat) by PMK.inl. rewrite A30. apply Z.lor_eq_0_iff. clear -HZ B0 B1 B2 B3; lia.
  - assert (EM : M2 = M1) by (apply functional_extensionality; exact FW2). subst M2.
    rewrite Z.sub_0_r, Z.mod_small in Hnz by exact HL.
    assert (HZ : W <> 0).
    { intros HW0. subst D0 D1. pose proof (proj2 (PNDF.parts_zero_iff q0 q1 q2 q3 ltac:(clear -B0; lia) B1 B2 B3) ltac:(clear -HW0 EW; lia)) as X.
      clear -X Hnz; lia. }
    exists fx2, R2, M1. split; [exact MG1|]. split; [intros a Ha Hn; apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact MI1|].
    split. { unfold PNSDRN.RR. repeat apply conj; PMK.sc. } split; [PMK.sc|].
    right. split; [clear -HZ HW; lia|]. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
    split; [exact B12|]. split; [PMK.sc|]. split; [exact B20|].
    assert (X0 : L5.u32_at RSEGS M1 (S - 240) (D0 mod 2 ^ 32)) by (apply (PNMW.u32_of_u64_lo RSEGS M1 (S - 240) D0); [clear -FS; lia| clear -FS; lia| exact HD0| exact C240]).
    assert (X1 : L5.u32_at RSEGS M1 (S - 240 + 4) (D0 / 2 ^ 32)) by (apply (PNMW.u32_of_u64_hi RSEGS M1 (S - 240) D0); [clear -FS; lia| clear -FS; lia| exact HD0| exact C240]).
    assert (X2 : L5.u32_at RSEGS M1 (S - 232) (D1 mod 2 ^ 32)) by (apply (PNMW.u32_of_u64_lo RSEGS M1 (S - 232) D1); [clear -FS; lia| clear -FS; lia| exact HD1| exact C232]).
    assert (X3 : L5.u32_at RSEGS M1 (S - 232 + 4) (D1 / 2 ^ 32)) by (apply (PNMW.u32_of_u64_hi RSEGS M1 (S - 232) D1); [clear -FS; lia| clear -FS; lia| exact HD1| exact C232]).
    replace (D0 mod 2 ^ 32) with q0 in X0.
    2:{ subst D0. replace (q0 + 4294967296 * q1) with (q0 + q1 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear -B0; lia. }
    replace (D0 / 2 ^ 32) with q1 in X1.
    2:{ subst D0. replace (q0 + 4294967296 * q1) with (q0 + q1 * 2 ^ 32) by (clear; lia). rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -B0; lia). clear; lia. }
    replace (D1 mod 2 ^ 32) with q2 in X2.
    2:{ subst D1. replace (q2 + 4294967296 * q3) with (q2 + q3 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear -B2; lia. }
    replace (D1 / 2 ^ 32) with q3 in X3.
    2:{ subst D1. replace (q2 + 4294967296 * q3) with (q2 + q3 * 2 ^ 32) by (clear; lia). rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -B2; lia). clear; lia. }
    replace (S - 240 + 4) with (S - 236) in X1 by (clear; lia). replace (S - 232 + 4) with (S - 228) in X3 by (clear; lia).
    split; [exact X0|]. split; [exact X1|]. split; [exact X2| exact X3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma divide fx R M k W :
  RR R k -> getr R (reg 29) = Z_to_bv 64 k -> getr R (reg 12) = Z_to_bv 64 (S - 240) -> getr R (reg 20) = Z_to_bv 64 0 ->
  0 <= k <= 3 -> 0 <= W < 2 ^ 113 -> MI M ->
  L5.u32_at RSEGS M (S - 240) (p0 W) -> L5.u32_at RSEGS M (S - 236) (p1 W) -> L5.u32_at RSEGS M (S - 232) (p2 W) -> L5.u32_at RSEGS M (S - 228) (p3 W) ->
  exists fx' R' M' Q rr, msteps RSEGS (st fx R 0x37bbc M) (st fx' R' 0x37be8 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 224) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RR R' k /\ getr R' (reg 29) = Z_to_bv 64 k /\ getr R' (reg 19) = getr R (reg 19) /\ MI M'
    /\ getr R' (reg 20) = Z_to_bv 64 rr /\ 0 <= rr < 1000000000 /\ Q = W / 1000000000 /\ rr = W mod 1000000000 /\ 0 <= Q < 2 ^ 113
    /\ 0 <= p0 Q + 4294967296 * p1 Q < 2 ^ 64 /\ 0 <= p2 Q + 4294967296 * p3 Q < 2 ^ 64
    /\ (p0 Q + 4294967296 * p1 Q) mod 2 ^ 32 = p0 Q /\ (p0 Q + 4294967296 * p1 Q) / 4294967296 = p1 Q
    /\ L5.u64_at RSEGS M' (S - 240) (p0 Q + 4294967296 * p1 Q) /\ L5.u64_at RSEGS M' (S - 232) (p2 Q + 4294967296 * p3 Q).
Proof.
  intros RRk G29 G12 G20 Hk HW MIM C0 C1 C2 C3.
  pose proof (parts_val W HW) as (EW & B0 & B1 & B2 & B3).
  destruct (limbs fx R M k (p0 W) (p1 W) (p2 W) (p3 W) RRk G29 G12 G20 Hk ltac:(clear -B0; lia) B1 B2 B3 MIM C0 C1 C2 C3)
    as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & RR2 & B29 & B20 & B19 & MI2 & D0 & D1 & D2 & D3).
  pose proof (PNDF.ldiv4 (p0 W) (p1 W) (p2 W) (p3 W) ltac:(clear -B0; lia) B1 B2 B3) as LD. cbn zeta in LD.
  destruct LD as (EQ & Hr3 & Hq0 & Hq1 & Hq2 & Hq3 & _).
  eexists fx2, R2, M2, _, _. split; [exact MS2|]. split; [exact MG2|]. split; [exact FZ2|]. split; [exact RR2|]. split; [exact B29|]. split; [exact B19|].
  split; [exact MI2|]. split; [exact B20|]. split; [exact Hr3|].
  match type of EQ with _ = 1000000000 * ?Qt + ?rt =>
    pose proof (limb_uniq Qt _ _ _ _ eq_refl Hq0 Hq1 Hq2 Hq3) as (U0 & U1 & U2 & U3);
    assert (HQ : Qt = W / 1000000000) by (apply (Z.div_unique_pos W 1000000000 Qt rt); [exact Hr3| clear -EW EQ; lia]);
    assert (HR : rt = W mod 1000000000) by (apply (Z.mod_unique_pos W 1000000000 Qt rt); [exact Hr3| clear -EW EQ; lia])
  end.
  split; [exact HQ|]. split; [exact HR|].
  split. { rewrite HQ. split; [apply Z.div_pos; clear -HW; lia|]. apply Z.div_lt_upper_bound; [clear; lia|]. clear -HW; lia. }
  rewrite U0, U1, U2, U3.
  split; [clear -Hq0 Hq1; lia|]. split; [clear -Hq2 Hq3; lia|].
  split. { match goal with |- (?a + 4294967296 * ?b) mod _ = _ => replace (a + 4294967296 * b) with (a + b * 2 ^ 32) by (clear; lia) end.
           rewrite Z.mod_add by (clear; lia). apply Z.mod_small. exact Hq0. }
  split. { match goal with |- (?a + 4294967296 * ?b) / _ = _ => replace (a + 4294967296 * b) with (a + b * 4294967296) by (clear; lia) end.
           rewrite Z.div_add by (clear; lia). rewrite Z.div_small by exact Hq0. clear; lia. }
  split.
  - match goal with |- L5.u64_at _ _ _ (?a + 4294967296 * ?b) => apply (PNMW.u64_of_u32x2 RSEGS M2 (S - 240) a b) end;
      [clear -FS; lia| clear -FS; lia| exact Hq0| exact Hq1| exact D0| replace (S - 240 + 4) with (S - 236) by (clear; lia); exact D1].
  - match goal with |- L5.u64_at _ _ _ (?a + 4294967296 * ?b) => apply (PNMW.u64_of_u32x2 RSEGS M2 (S - 232) a b) end;
      [clear -FS; lia| clear -FS; lia| exact Hq2| exact Hq3| exact D2| replace (S - 232 + 4) with (S - 228) by (clear; lia); exact D3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wk (k : Z) : Z := V / 1000000000 ^ (3 - k).
Lemma Wk3 : Wk 3 = V.
Proof. unfold Wk. replace (3 - 3) with 0 by (clear; lia). rewrite Z.pow_0_r. apply Z.div_1_r. Qed.
Lemma Wk_range k : 0 <= k <= 3 -> 0 <= Wk k <= V.
Proof.
  intros Hk. unfold Wk. assert (P : 0 < 1000000000 ^ (3 - k)) by (apply Z.pow_pos_nonneg; clear -Hk; lia).
  split; [apply Z.div_pos; clear -P FV; lia|]. apply Z.div_le_upper_bound; [exact P|]. clear -P FV; nia.
Qed.
Lemma Wk_step k : 1 <= k <= 3 -> Wk (k - 1) = Wk k / 1000000000.
Proof.
  intros Hk. unfold Wk. replace (3 - (k - 1)) with ((3 - k) + 1) by (clear; lia). rewrite Z.pow_add_r by (clear -Hk; lia). rewrite Z.pow_1_r.
  assert (P : 0 < 1000000000 ^ (3 - k)) by (apply Z.pow_pos_nonneg; clear -Hk; lia). rewrite Z.div_div by (clear -P; lia). reflexivity.
Qed.
Lemma bvu_small z : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. clear -Hz. cbn. lia. Qed.

Definition HD (R : bvmap 5 word) (M : word -> option byte) (k : Z) : Prop :=
  RR R k /\ getr R (reg 19) = Z_to_bv 64 k
  /\ bv_unsigned (getr R (reg 30)) mod 2 ^ 32 = p0 (Wk k) /\ bv_unsigned (getr R (reg 12)) mod 2 ^ 32 = p1 (Wk k)
  /\ getr R (reg 31) = Z_to_bv 64 (p2 (Wk k) + 4294967296 * p3 (Wk k))
  /\ MI M /\ digs M (k + 1) /\ zers M (k + 1).

(* [comment removed for export] *)
Lemma finish fx R M k Q :
  RR R k -> getr R (reg 29) = Z_to_bv 64 k -> 0 <= k <= 3 -> MI M -> digs M k -> zers M k ->
  bv_unsigned (getr R (reg 30)) mod 2 ^ 32 = p0 Q -> bv_unsigned (getr R (reg 12)) mod 2 ^ 32 = p1 Q ->
  getr R (reg 31) = Z_to_bv 64 (p2 Q + 4294967296 * p3 Q) -> Q = Wk k / 1000000000 ->
  exists fx' R',
    (k = 0 /\ msteps RSEGS (st fx R 0x37c2c M) (st fx' R' 0x37c40 M) /\ PNSDD.RB R0 S first sigma R'
       /\ getr R' (reg 10) = Z_to_bv 64 e /\ getr R' (reg 11) = Z_to_bv 64 (e - 6176) /\ getr R' (reg 12) = Z_to_bv 64 (PNDF.dg V 0))
    \/ (1 <= k /\ msteps RSEGS (st fx R 0x37c2c M) (st fx' R' 0x37b84 M) /\ HD R' M (k - 1)).
Proof.
  intros RRk G29 Hk MIM DG ZR H30 H12 G31 HQ.
  destruct (Z.eq_dec k 0) as [K0 | K1].
  - pose proof (PNDF.dg_range V 0) as Hc.
    assert (C0 : cell M 0 (PNDF.dg V 0)) by (apply DG; clear -K0; lia).
    destruct (tail fx R M k (PNDF.dg V 0) RRk G29 Hk C0 Hc MIM) as (fx1 & R1 & RB1 & A10 & A11 & A30 & A31 & [(_ & MS1 & A12) | (K1 & _)]); [| exfalso; clear -K0 K1; lia].
    exists fx1, R1. left. split; [exact K0|]. split; [exact MS1|]. split; [exact RB1|]. split; [exact A10|]. split; [exact A11| exact A12].
  - assert (C0 : cell M 0 0) by (apply ZR; clear -K1 Hk; lia).
    destruct (tail fx R M k 0 RRk G29 Hk C0 ltac:(clear; lia) MIM) as (fx1 & R1 & RB1 & A10 & A11 & A30 & A31 & [(K0 & _) | (_ & MS1 & RR1 & A19 & A12)]); [exfalso; clear -K0 K1; lia|].
    exists fx1, R1. right. split; [clear -K1 Hk; lia|]. split; [exact MS1|].
    unfold HD. rewrite (Wk_step k) by (clear -K1 Hk; lia). rewrite <- HQ. rewrite A30, A12, A31.
    split; [exact RR1|]. split; [exact A19|]. split; [exact H30|]. split; [exact H12|]. split; [exact G31|]. split; [exact MIM|].
    replace (k - 1 + 1) with k by (clear; lia). split; [exact DG| exact ZR].
Qed.

Lemma round_step fx R M k : 0 <= k <= 3 -> HD R M k ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M'
    /\ ((k = 0 /\ msteps RSEGS (st fx R 0x37b84 M) (st fx' R' 0x37c40 M') /\ PNSDD.RB R0 S first sigma R'
           /\ getr R' (reg 10) = Z_to_bv 64 e /\ getr R' (reg 11) = Z_to_bv 64 (e - 6176) /\ getr R' (reg 12) = Z_to_bv 64 (PNDF.dg V 0) /\ digs M' 0)
        \/ (1 <= k /\ msteps RSEGS (st fx R 0x37b84 M) (st fx' R' 0x37b84 M') /\ HD R' M' (k - 1))).
Proof.
  intros Hk (RRk & G19 & H30 & H12 & G31 & MIM & DG & ZR).
  pose proof (Wk_range k Hk) as HWk.
  assert (HW : 0 <= Wk k < 2 ^ 113) by (clear -HWk FV; lia).
  destruct (headfork fx R M k (Wk k) RRk G19 Hk HW H30 H12 G31 MIM)
    as (fx1 & R1 & M1 & MG1 & FZ1 & MI1 & RR1 & A29 & [(W0 & MS1 & A12 & A31 & A30) | (Wp & MS1 & A12 & A19 & A20 & C0 & C1 & C2 & C3)]).
  - (* [comment removed for export] *)
    assert (ZR1 : zers M1 (k + 1)).
    { intros i Hi. apply (cell_xfer M M1 _ i 0 FZ1); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia| exact (ZR i Hi)]. }
    assert (DG1 : digs M1 k).
    { intros i Hi. destruct (Z_lt_le_dec i (9 * (k + 1))) as [LT | GE].
      - replace i with (9 * k + (i - 9 * k)) by (clear; lia). rewrite (PNDF.dg_W_zero V k (i - 9 * k)); [| clear -FV; lia| exact Hk| clear -Hi LT; lia| exact W0].
        replace (9 * k + (i - 9 * k)) with i by (clear; lia). apply ZR1. clear -Hi LT Hk; lia.
      - apply (cell_xfer M M1 _ i _ FZ1); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia| ]. apply DG. clear -Hi GE; lia. }
    assert (ZR1' : zers M1 k) by (intros i Hi; apply ZR1; clear -Hi Hk; lia).
    assert (P30 : bv_unsigned (getr R1 (reg 30)) mod 2 ^ 32 = p0 0) by (rewrite A30; reflexivity).
    assert (P12 : bv_unsigned (getr R1 (reg 12)) mod 2 ^ 32 = p1 0) by (rewrite A12; reflexivity).
    assert (P31 : getr R1 (reg 31) = Z_to_bv 64 (p2 0 + 4294967296 * p3 0)) by (rewrite A31; reflexivity).
    assert (HQ : 0 = Wk k / 1000000000) by (rewrite W0; reflexivity).
    destruct (finish fx1 R1 M1 k 0 RR1 A29 Hk MI1 DG1 ZR1' P30 P12 P31 HQ) as (fx2 & R2 & [(K0 & MS2 & RB2 & B10 & B11 & B12) | (K1 & MS2 & HD2)]).
    + exists fx2, R2, M1. split; [exact MG1|]. split; [intros a Ha Hn; apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact MI1|].
      left. split; [exact K0|]. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. subst k. split; [exact RB2|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12| exact DG1].
    + exists fx2, R2, M1. split; [exact MG1|]. split; [intros a Ha Hn; apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact MI1|].
      right. split; [exact K1|]. split; [eapply msteps_trans; [exact MS1| exact MS2]| exact HD2].
  - (* [comment removed for export] *)
    destruct (divide fx1 R1 M1 k (Wk k) RR1 A29 A12 A20 Hk HW MI1 C0 C1 C2 C3)
      as (fx2 & R2 & M2 & Q & rr & MS2 & MG2 & FZ2 & RR2 & B29 & B19 & MI2 & B20 & Hrr & HQ & HR & HQr & HE0 & HE1 & M0 & Dv1 & X0 & X1).
    (* [comment removed for export] *)
    assert (ZR2 : zers M2 (k + 1)).
    { intros i Hi. apply (cell_xfer M1 M2 _ i 0 FZ2); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia|].
      apply (cell_xfer M M1 _ i 0 FZ1); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia| exact (ZR i Hi)]. }
    assert (DG2 : digs M2 (k + 1)).
    { intros i Hi. apply (cell_xfer M1 M2 _ i _ FZ2); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia|].
      apply (cell_xfer M M1 _ i _ FZ1); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia| exact (DG i Hi)]. }
    destruct (reload fx2 R2 M2 k rr (p0 Q + 4294967296 * p1 Q) (p2 Q + 4294967296 * p3 Q) RR2 B29 B20 Hk Hrr HE0 HE1 MI2 X0 X1)
      as (fx3 & R3 & RR3 & C29 & C20 & C19 & C12 & C30 & C31 & [(Rz & MS3) | (Rnz & MS3 & C21)]).
    + (* [comment removed for export] *)
      assert (DG3 : digs M2 k).
      { intros i Hi. destruct (Z_lt_le_dec i (9 * (k + 1))) as [LT | GE]; [| apply DG2; clear -Hi GE; lia].
        replace i with (9 * k + (i - 9 * k)) by (clear; lia).
        rewrite (PNDF.dg_round_zero V k (i - 9 * k)); [| clear -FV; lia| exact Hk| clear -Hi LT; lia| unfold Wk in HR; rewrite <- HR; exact Rz].
        replace (9 * k + (i - 9 * k)) with i by (clear; lia). apply ZR2. clear -Hi LT Hk; lia. }
      assert (ZR3 : zers M2 k) by (intros i Hi; apply ZR2; clear -Hi Hk; lia).
      assert (P30 : bv_unsigned (getr R3 (reg 30)) mod 2 ^ 32 = p0 Q) by (rewrite C30, (bvu_small _ HE0); exact M0).
      assert (P12 : bv_unsigned (getr R3 (reg 12)) mod 2 ^ 32 = p1 Q) by (rewrite C12, Dv1; apply Z.mod_small; apply (proj1 (proj2 (proj2 (parts_val Q HQr))))).
      destruct (finish fx3 R3 M2 k Q RR3 C29 Hk MI2 DG3 ZR3 P30 P12 C31 HQ) as (fx4 & R4 & [(K0 & MS4 & RB4 & B10 & B11 & B12) | (K1 & MS4 & HD4)]).
      * exists fx4, R4, M2. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact MI2|].
        left. split; [exact K0|]. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
        subst k. split; [exact RB4|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12| exact DG3].
      * exists fx4, R4, M2. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact MI2|].
        right. split; [exact K1|]. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]| exact HD4].
    + (* [comment removed for export] *)
      assert (Hrr' : 1 <= rr < 1000000000) by (clear -Rnz Hrr; lia).
      assert (C19' : getr R3 (reg 19) = Z_to_bv 64 (S - 220 + 36 * k)) by (rewrite C19, B19; exact A19).
      destruct (digits fx3 R3 M2 k rr RR3 C29 C20 C21 C19' Hk Hrr' MI2)
        as (fx4 & R4 & M4 & MS4 & MG4 & FZ4 & RR4 & D29 & D12 & D30 & D31 & MI4 & CELLS).
      assert (DG4 : digs M4 k).
      { intros i Hi. destruct (Z_lt_le_dec i (9 * (k + 1))) as [LT | GE].
        - replace i with (9 * k + (i - 9 * k)) by (clear; lia).
          rewrite <- (PNDF.dg_round V k (i - 9 * k)); [| clear -FV; lia| exact Hk| clear -Hi LT; lia].
          unfold Wk in HR. rewrite <- HR. apply (CELLS (i - 9 * k)). clear -Hi LT Hk; lia.
        - apply (cell_xfer M2 M4 _ i _ FZ4); [intros a Ha; clear -Ha Hi GE; lia| clear -Hi Hk; lia|]. apply DG2. clear -Hi GE; lia. }
      assert (ZR4 : zers M4 k).
      { intros i Hi. apply (cell_xfer M2 M4 _ i 0 FZ4); [intros a Ha; clear -Ha Hi Hk; lia| clear -Hi Hk; lia|]. apply ZR2. clear -Hi Hk; lia. }
      assert (P30 : bv_unsigned (getr R4 (reg 30)) mod 2 ^ 32 = p0 Q) by (rewrite D30, C30, (bvu_small _ HE0); exact M0).
      assert (P12 : bv_unsigned (getr R4 (reg 12)) mod 2 ^ 32 = p1 Q) by (rewrite D12, C12, Dv1; apply Z.mod_small; apply (proj1 (proj2 (proj2 (parts_val Q HQr))))).
      assert (P31 : getr R4 (reg 31) = Z_to_bv 64 (p2 Q + 4294967296 * p3 Q)) by (rewrite D31; exact C31).
      destruct (finish fx4 R4 M4 k Q RR4 D29 Hk MI4 DG4 ZR4 P30 P12 P31 HQ) as (fx5 & R5 & [(K0 & MS5 & RB5 & B10 & B11 & B12) | (K1 & MS5 & HD5)]).
      * exists fx5, R5, M4. split; [intros a Ha; apply MG4; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; rewrite (FZ4 a Ha) by (clear -Hn Hk; lia); rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|].
        split; [exact MI4|].
        left. split; [exact K0|].
        split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MS5]]]]|].
        subst k. split; [exact RB5|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12| exact DG4].
      * exists fx5, R5, M4. split; [intros a Ha; apply MG4; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; rewrite (FZ4 a Ha) by (clear -Hn Hk; lia); rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|].
        split; [exact MI4|].
        right. split; [exact K1|].
        split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MS5]]]]| exact HD5].
Qed.

End Call.
End PNSDRN2.
