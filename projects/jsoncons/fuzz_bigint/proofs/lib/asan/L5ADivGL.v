(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ADDq L5ASubMul L5ADivPG2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGL.
Import L5A. Import L5CA. Import L5SA. Import L5ADIVPG2.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section LOOP.
Variables (E to Dr Dq Dd d n l sdl : Z).
Local Notation SPA := (E - 352).
Local Notation SBZ := 2147450880.

(* [comment removed for export] *)
Definition FP (a : Z) : Prop :=
  SPA - 80 <= a < SPA \/ E - 328 <= a < E - 312 \/ E - 184 <= a < E - 176 \/ Dr <= a < Dr + 8 * (n + 1) \/ Dq <= a < Dq + 8 * (n - l).
Definition lagree (M0 Mk : word -> option byte) : Prop :=
  mem_grows M0 Mk /\ forall a, 0 <= a < 2 ^ 64 -> ~ FP a -> Mk (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Lemma lagree_refl M0 : lagree M0 M0. Proof. split. apply mem_grows_refl. intros; reflexivity. Qed.
Lemma lagree_trans M0 M1 M2 : lagree M0 M1 -> lagree M1 M2 -> lagree M0 M2.
Proof. intros [G1 A1] [G2 A2]. split. eapply mem_grows_trans; eassumption. intros a Ha Hn. rewrite A2 by assumption. apply A1; assumption. Qed.
(* [comment removed for export] *)
Definition FPI (a : Z) : Prop :=
  SPA - 80 <= a < SPA \/ False \/ E - 184 <= a < E - 176 \/ Dr <= a < Dr + 8 * (n + 1) \/ Dq <= a < Dq + 8 * (n - l).
Definition lagreeI (M0 Mk : word -> option byte) : Prop :=
  mem_grows M0 Mk /\ forall a, 0 <= a < 2 ^ 64 -> ~ FPI a -> Mk (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Lemma lagreeI_trans M0 M1 M2 : lagreeI M0 M1 -> lagreeI M1 M2 -> lagreeI M0 M2.
Proof. intros [G1 A1] [G2 A2]. split. eapply mem_grows_trans; eassumption. intros a Ha Hn. rewrite A2 by assumption. apply A1; assumption. Qed.
Lemma lagree_of_I M0 Mk : lagreeI M0 Mk -> lagree M0 Mk.
Proof.
  intros [G1 A1]. split. exact G1. intros a Ha Hn. apply A1. exact Ha. intros X. apply Hn. unfold FP. unfold FPI in X.
  destruct X as [X|[X|X]]. left; exact X. destruct X. right; right; exact X.
Qed.

Definition nsh (x lx : Z) : Prop := 2147446784 + 17592186048512 <= x \/ x + lx <= 2147446784.
Definition oim (x lx : Z) : Prop := x + lx <= 65536 \/ 6500352 <= x.

(* [comment removed for export] *)
Record lctx (M : word -> option byte) : Prop := LCTX {
  lc_E : 140735332487680 <= E <= 140737488355328;
  lc_EA : E mod 32 = 0;
  lc_n : 0 <= l /\ l <= 298 /\ 0 <= n <= 299;
  lc_fw : L5.writable RSEGS M (SPA - 80) (352 + 80);
  lc_fd : L5.defined M (SPA - 80) (352 + 80);
  lc_st : L5.img_clear M 860160 880640 /\ L5.u64_at RSEGS M 908088 2147450880 /\ L5.u32_at RSEGS M 908096 1;
  lc_sl : L5.u64_at RSEGS M (E - 232) l;
  lc_sdd : L5.u64_at RSEGS M (E - 224) Dd;
  lc_sdl : L5.u64_at RSEGS M (E - 216) (l + 1);
  lc_ssb : L5.u64_at RSEGS M (E - 200) 2147450880;
  lc_sto : L5.u64_at RSEGS M (E - 208) to;
  lc_to : 0 <= to < 2 ^ 64;
  lc_r : 4096 <= Dr /\ Dr + 8 * (n + 1) <= 140737488351232 /\ Dr mod 8 = 0 /\ nsh Dr (8 * (n + 1)) /\ oim Dr (8 * (n + 1));
  lc_rw : L5.writable RSEGS M Dr (8 * (n + 1));
  lc_rd : L5.defined M Dr (8 * (n + 1));
  lc_rz : L5KA.zeros_at M (Dr / 8 + 2147450880) (n + 1);
  lc_q : 4096 <= Dq /\ Dq + 8 * (n - l) <= 140737488351232 /\ Dq mod 8 = 0 /\ nsh Dq (8 * (n - l)) /\ oim Dq (8 * (n - l));
  lc_qw : L5.writable RSEGS M Dq (8 * (n - l));
  lc_qz : L5KA.zeros_at M (Dq / 8 + 2147450880) (n - l);
  lc_d : 4096 <= Dd /\ Dd + 8 * (l + 1) <= 140737488351232 /\ Dd mod 8 = 0 /\ nsh Dd (8 * (l + 1));
  lc_dd : L5.defined M Dd (8 * (l + 1));
  lc_dz : L5KA.zeros_at M (Dd / 8 + 2147450880) (l + 1);
  lc_dv : L5.u64_at RSEGS M (Dd + 8 * l) d /\ 2 ^ 63 <= d < 2 ^ 64;
  lc_sd : sdl = (Dd + 8 * l) / 8 + 2147450880;
  lc_qc : L5KA.zeros_at M ((E - 184) / 8 + 2147450880) 1;
  lc_ap : (Dr + 8 * (n + 1) <= Dq \/ Dq + 8 * (n - l) <= Dr) /\ (Dr + 8 * (n + 1) <= Dd \/ Dd + 8 * (l + 1) <= Dr) /\ (Dq + 8 * (n - l) <= Dd \/ Dd + 8 * (l + 1) <= Dq)
          /\ Dr + 8 * (n + 1) <= SPA - 80 /\ Dq + 8 * (n - l) <= SPA - 80 /\ Dd + 8 * (l + 1) <= SPA - 80 }.

Lemma sh_not_FP M : lctx M -> forall a, 2147450880 <= a < 17594333495296 -> ~ FP a.
Proof.
  intros C a Ha. pose proof (lc_E _ C) as ER. pose proof (lc_r _ C) as (_ & _ & _ & NR & _). pose proof (lc_q _ C) as (_ & _ & _ & NQ & _). pose proof (lc_n _ C) as NL.
  unfold FP, nsh in *. intros [X|[X|[X|[X|X]]]]; clear - X Ha ER NR NQ NL; lia.
Qed.
Lemma img_not_FP M : lctx M -> forall a, 65536 <= a < 6500352 -> ~ FP a.
Proof.
  intros C a Ha. pose proof (lc_E _ C) as ER. pose proof (lc_r _ C) as (_ & _ & _ & _ & NR). pose proof (lc_q _ C) as (_ & _ & _ & _ & NQ). pose proof (lc_n _ C) as NL.
  unfold FP, oim in *. intros [X|[X|[X|[X|X]]]]; clear - X Ha ER NR NQ NL; lia.
Qed.
Lemma u64_keep M0 Mk a v : lagree M0 Mk -> (forall i, a <= i < a + 8 -> ~ FP i) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M0 a v -> L5.u64_at RSEGS Mk a v.
Proof. intros [_ AG] NF H0 H1 Hu. eapply L5C.u64_at_agree. 4: exact Hu. 2: exact H0. 2: exact H1. intros j Hj. apply AG. lia. apply NF. exact Hj. Qed.
Lemma zeros_keep M0 Mk a m : lctx M0 -> lagree M0 Mk -> 2147450880 <= a -> a + m <= 17594333495296 -> L5KA.zeros_at M0 a m -> L5KA.zeros_at Mk a m.
Proof. intros C [_ AG] H0 H1 Hz. apply (L5KA.zeros_at_agree1 M0 Mk a m). 2: exact Hz. intros i Hi. apply AG. lia. apply (sh_not_FP M0 C). lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lctx_keep M0 Mk : lctx M0 -> lagree M0 Mk -> lctx Mk.
Proof.
  intros C LA. pose proof LA as [MG AG]. destruct C as [ER EA NL FW FD (IMG & S1 & S2) SL SDD SDL SSB STO TOR RR RW RD RZ QR QW QZ DR DD DZ (DV & DVR) SD QC AP].
  pose proof (LCTX M0 ER EA NL FW FD (conj IMG (conj S1 S2)) SL SDD SDL SSB STO TOR RR RW RD RZ QR QW QZ DR DD DZ (conj DV DVR) SD QC AP) as C.
  assert (FRM : forall a, SPA <= a < E -> ~ (E - 328 <= a < E - 312) -> ~ (E - 184 <= a < E - 176) -> ~ FP a).
  { intros a Ha N1 N2. unfold FP. destruct AP as (_ & _ & _ & A4 & A5 & _). clear - Ha N1 N2 A4 A5 NL. lia. }
  constructor; try assumption.
  - eapply L5.writable_grows; eassumption.
  - eapply L5.defined_grows; eassumption.
  - split. { intros i Hi. rewrite AG. apply IMG. exact Hi. lia. apply (img_not_FP M0 C). lia. }
    split. apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply (img_not_FP M0 C). lia. lia. lia. exact S1.
    unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M0 Mk 4 908096 ltac:(lia) ltac:(cbn; lia)). exact S2. intros i Hi. apply AG. cbn in Hi; lia. apply (img_not_FP M0 C). cbn in Hi; lia.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact SL.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact SDD.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact SDL.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact SSB.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact STO.
  - eapply L5.writable_grows; eassumption.
  - eapply L5.defined_grows; eassumption.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact RZ. destruct RR as (R1 & R2 & _). lia. destruct RR as (R1 & R2 & _). lia.
  - eapply L5.writable_grows; eassumption.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact QZ. destruct QR as (R1 & R2 & _). lia. destruct QR as (R1 & R2 & _). lia.
  - eapply L5.defined_grows; eassumption.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact DZ. destruct DR as (R1 & R2 & _). lia. destruct DR as (R1 & R2 & _). lia.
  - split. 2: exact DVR. apply (u64_keep M0 Mk _ _ LA). 4: exact DV. 2: destruct DR as (R1 & R2 & _); lia. 2: destruct DR as (R1 & R2 & _); lia.
    intros i Hi. unfold FP. destruct AP as (_ & A2 & A3 & _ & _ & A6). destruct DR as (R1 & R2 & _). clear - Hi A2 A3 A6 NL ER R1 R2. lia.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact QC. lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hregs (R0 Rk : bvmap 5 word) (k : Z) : Prop :=
  getr Rk (reg 2) = Z_to_bv 64 SPA /\ getr Rk (reg 8) = Z_to_bv 64 E /\ getr Rk (reg 9) = Z_to_bv 64 SPA /\
  getr Rk (reg 3) = getr R0 (reg 3) /\ getr Rk (reg 4) = getr R0 (reg 4) /\
  getr Rk (reg 18) = Z_to_bv 64 to /\ getr Rk (reg 19) = Z_to_bv 64 (Dr - 8 * (n - k)) /\ getr Rk (reg 20) = Z_to_bv 64 (Dr - 8 * (l + 1) - 8 * (n - k)) /\
  getr Rk (reg 21) = Z_to_bv 64 (8 * n) /\ getr Rk (reg 22) = Z_to_bv 64 k /\ getr Rk (reg 23) = Z_to_bv 64 (Dr - 8 * (n - k)) /\ getr Rk (reg 24) = Z_to_bv 64 d /\
  getr Rk (reg 25) = Z_to_bv 64 (Dq - 8 * (l + 1) - 8 * (n - k)) /\ getr Rk (reg 26) = Z_to_bv 64 2147450880 /\ getr Rk (reg 27) = Z_to_bv 64 (Dq - 8 * (l + 1) - 8 * (n - k)).
Definition kept5 (R0 R' : bvmap 5 word) : Prop :=
  getr R' (reg 2) = Z_to_bv 64 SPA /\ getr R' (reg 8) = Z_to_bv 64 E /\ getr R' (reg 9) = Z_to_bv 64 SPA /\ getr R' (reg 3) = getr R0 (reg 3) /\ getr R' (reg 4) = getr R0 (reg 4).

Local Ltac rg H := rewrite H; f_equal; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma div8 x j : x mod 8 = 0 -> (x + 8 * j) / 8 = x / 8 + j /\ x / 8 * 8 = x.
Proof. intros H. split; lia. Qed.
Lemma al8 x j : x mod 8 = 0 -> (x + 8 * j) mod 8 = 0. Proof. intros H. lia. Qed.
Lemma e32 : E mod 32 = 0 -> (E - 352) mod 16 = 0 /\ (E - 184) mod 8 = 0 /\ (E - 184) / 8 * 8 = E - 184. Proof. intros H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma giter (fx : FPState) R0 Rk Mk k : lctx Mk -> hregs R0 Rk k -> l < k <= n ->
  exists (fx' : FPState) R' M', lagreeI Mk M' /\
    ((k - l = 1 /\ msteps RSEGS (st fx Rk 0x9294c Mk) (st fx' R' 0x929e8 M') /\ kept5 R0 R')
     \/ (2 <= k - l /\ msteps RSEGS (st fx Rk 0x9294c Mk) (st fx' R' 0x9294c M') /\ hregs R0 R' (k - 1))).
Proof.
  intros C (h2 & h8 & h9 & h3 & h4 & h18 & h19 & h20 & h21 & h22 & h23 & h24 & h25 & h26 & h27) Hk.
  pose proof C as [ER EA NL FW FD (IMG & S1 & S2) SL SDD SDL SSB STO TOR (RR1 & RR2 & RR8 & RNS & ROI) RW RD RZ (QR1 & QR2 & QR8 & QNS & QOI) QW QZ (DR1 & DR2 & DR8 & DNS) DD DZ (DV & DVR) SD QC (AP1 & AP2 & AP3 & AP4 & AP5 & AP6)].
  unfold nsh, oim in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by lia. destruct ER' as [ER' ERG].
  assert (EAL : aligned E 32) by exact EA.
  assert (FW352 : L5.writable RSEGS Mk (E - 352) 352). { eapply L5.writable_sub. exact FW. lia. lia. }
  set (A := Dr + 8 * (k - 1)).
  assert (AR : 4096 <= A <= 140737488355312 /\ 0 <= A < 2 ^ 64) by (clear - RR1 RR2 Hk NL; subst A; lia). destruct AR as [AR ARG].
  assert (AAL : aligned A 8) by (unfold aligned; subst A; apply al8; exact RR8).
  pose proof (div8 Dr (k - 1) RR8) as [AD8 DR8']. fold A in AD8.
  assert (DRB : 0 <= Dr / 8 /\ Dr / 8 <= 17592186043904) by (clear - DR8' RR1 RR2 NL; lia).
  assert (ANS : 2147446784 + 17592186048512 <= A \/ A + 16 <= 2147446784) by (clear - RNS Hk NL; subst A; lia).
  assert (AZ : L5KA.zeros_at Mk (A / 8 + 2147450880) 2). { eapply L5KA.zeros_at_sub. exact RZ. rewrite AD8; lia. rewrite AD8; lia. }
  assert (AF1 : E - 352 + 352 <= A \/ A + 16 <= E - 352) by (clear - AP4 Hk NL; subst A; lia).
  assert (AF2 : E - 352 + 352 <= A / 8 + 2147450880 \/ A / 8 + 2147450880 + 2 <= E - 352) by (rewrite AD8; clear - DRB ER Hk NL; lia).
  assert (AF3 : A + 16 <= A / 8 + 2147450880 \/ A / 8 + 2147450880 + 2 <= A) by (rewrite AD8; clear - DR8' DRB RNS RR1 RR2 Hk NL; subst A; lia).
  destruct (defined_word Mk A ltac:(eapply L5.defined_sub; [exact RD | subst A; lia | subst A; lia]) ltac:(lia) ltac:(lia)) as (w1 & W1R & W1).
  destruct (defined_word Mk (A + 8) ltac:(eapply L5.defined_sub; [exact RD | subst A; lia | subst A; lia]) ltac:(lia) ltac:(lia)) as (w2 & W2R & W2).
  assert (DRG : 0 <= d < 2 ^ 64 /\ 0 <= 8 * n < 2 ^ 64) by lia. destruct DRG as [DRG N8R].
  (* [comment removed for export] *)
  pose proof (v5GLa_conc fx Rk Mk (fun j => match j with 2%nat => E | 33%nat => to | 58%nat => U Rk 1 | 75%nat => d | 76%nat => w2 | 77%nat => w1 | 79%nat => 8 * n | 82%nat => A | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rg h19) | (rg h23) ]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & aEQ & (aMS & aKS & aR1 & aR10 & aR11 & aR12 & aR13)).
  assert (EM1 : M1 = Mk) by (apply mem_eq_of_agree; exact aEQ). subst M1.
  (* [comment removed for export] *)
  destruct (L5ADDQ.ddq_runA fx1 R1 Mk d 600460 aR13 DVR aR1 ltac:(split; [lia | reflexivity])) as (fx2 & R2 & M2 & dMS & dKS & dRP & EM2). subst M2.
  set (q := U R2 10). assert (QRG : 0 <= q <= 18446744073709551615) by (subst q; pose proof (UR R2 10); lia).
  (* [comment removed for export] *)
  set (s4v := Dr - 8 * (l + 1) - 8 * (n - k)).
  assert (S4R : 0 <= s4v < 2 ^ 64 /\ 0 <= Dd < 2 ^ 64 /\ 0 <= l + 1 < 2 ^ 64) by (subst s4v; lia). destruct S4R as (S4R & DDR & L1R).
  pose proof (v5GLb_conc fx2 R2 Mk (fun j => match j with 2%nat => E | 33%nat => to | 58%nat => U R2 1 | 64%nat => l + 1 | 65%nat => Dd | 78%nat => q | 79%nat => 8 * n | 85%nat => s4v | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (dKS 2%nat) by inl; rk) | (rewrite (dKS 8%nat) by inl; rk) | (rewrite (dKS 9%nat) by inl; rk) | (rewrite (dKS 18%nat) by inl; rk)
                      | (rewrite (dKS 20%nat) by inl; rk) | (rewrite (dKS 21%nat) by inl; rk) ]).
  destruct P as (fx3 & R3 & M3 & MG3 & _ & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR14 & bQ)).
  assert (LA3 : lagreeI Mk M3). { split. exact MG3. intros a Ha Hn. apply bFZ. exact Ha. intros X. apply Hn. unfold FPI. right; right; left. lia. }
  pose proof (lctx_keep Mk M3 C (lagree_of_I _ _ LA3)) as C3.
  pose proof C3 as [_ _ _ FW3 FD3 (IMG3 & S13 & S23) SL3 SDD3 SDL3 SSB3 STO3 _ _ RW3 RD3 RZ3 _ QW3 QZ3 _ DD3 DZ3 (DV3 & _) _ QC3 _].
  (* [comment removed for export] *)
  set (a := Dr + 8 * (k - l - 1)). set (n' := Z.to_nat (l + 1)).
  assert (N'E : Z.of_nat n' = l + 1) by (subst n'; apply Z2Nat.id; clear - NL; lia).
  pose proof (div8 Dr (k - l - 1) RR8) as [AD8a _]. fold a in AD8a.
  pose proof (div8 Dd 0 DR8) as [_ DD8'].
  pose proof (e32 EA) as (SP16 & QA8 & QAD).
  assert (SMC : L5ASM.smctxA M3 SPA a Dd (E - 184) n').
  { constructor.
    - split. clear - ER; lia. exact SP16.
    - eapply L5.writable_sub. exact FW3. clear; lia. clear; lia.
    - split. exact IMG3. split. exact S13. exact S23.
    - clear - N'E NL. lia.
    - split. subst a; clear - RR1 RR2 Hk NL; lia. split. subst a; apply al8; exact RR8.
      split. unfold L5ASM.notshadow. rewrite N'E. subst a; clear - RNS Hk NL; lia. unfold L5ASM.offimg. rewrite N'E. subst a; clear - ROI Hk NL; lia.
    - rewrite N'E. eapply L5.writable_sub. exact RW3. subst a; clear - Hk NL; lia. subst a; clear - Hk NL; lia.
    - rewrite N'E. eapply L5.defined_sub. exact RD3. subst a; clear - Hk NL; lia. subst a; clear - Hk NL; lia.
    - rewrite N'E. eapply L5KA.zeros_at_sub. exact RZ3. rewrite AD8a; clear - Hk NL; lia. rewrite AD8a; clear - Hk NL; lia.
    - split. clear - DR1 DR2 NL; lia. split. exact DR8. unfold L5ASM.notshadow. rewrite N'E. clear - DNS; lia.
    - rewrite N'E. exact DD3.
    - rewrite N'E. exact DZ3.
    - split. clear - ER; lia. split. exact QA8. split. unfold L5ASM.notshadow. clear - ER; lia. unfold L5ASM.offimg. clear - ER; lia.
    - eapply L5.writable_sub. exact FW3. clear; lia. clear; lia.
    - eapply L5.defined_sub. exact FD3. clear; lia. clear; lia.
    - exact QC3.
    - unfold L5ASM.apart. rewrite N'E. subst a; clear - AP4 Hk NL; lia.
    - unfold L5ASM.apart. rewrite N'E. clear - AP6 NL; lia.
    - unfold L5ASM.apart. clear; lia.
    - unfold L5ASM.apart. rewrite N'E. subst a; clear - AP2 Hk NL; lia.
    - unfold L5ASM.apart. rewrite N'E. subst a; clear - AP4 Hk NL; lia.
    - unfold L5ASM.apart. rewrite N'E. clear - AP6 NL; lia. }
  assert (R3_2 : getr R3 (reg 2) = Z_to_bv 64 SPA). { rewrite (bKS 2%nat) by inl. rewrite (dKS 2%nat) by inl. rewrite (aKS 2%nat) by inl. exact h2. }
  destruct (L5ASM.submul_runA fx3 R3 M3 SPA a Dd (E - 184) 600488 n' R3_2 ltac:(rg bR11) bR12 ltac:(rewrite N'E; exact bR13) bR14 bR1 ltac:(split; [clear; lia | reflexivity]) SMC)
    as (fx4 & R4 & M4 & sMS & sKS & sRP & _ & sAG & MG4).
  assert (LA4 : lagreeI M3 M4).
  { split. exact MG4. intros x Hx Hn. apply sAG. exact Hx.
    - intros X. apply Hn. unfold FPI. left. exact X.
    - intros X. apply Hn. unfold FPI. right; right; right; left. rewrite N'E in X. subst a. clear - X Hk NL. lia.
    - intros X. apply Hn. unfold FPI. right; right; left. clear - X; lia. }
  pose proof (lctx_keep M3 M4 C3 (lagree_of_I _ _ LA4)) as C4.
  pose proof C4 as [_ _ _ FW4 FD4 (IMG4 & S14 & S24) SL4 _ _ _ _ _ _ _ _ _ _ QW4 QZ4 _ _ _ _ _ _ _].
  (* [comment removed for export] *)
  set (qs := Dq + 8 * (k - l - 1)).
  pose proof (div8 Dq (k - l - 1) QR8) as [QD8 DQ8']. fold qs in QD8.
  assert (DQB : 0 <= Dq / 8 /\ Dq / 8 <= 17592186043904) by (clear - DQ8' QR1 QR2 NL Hk; lia).
  assert (QSR : 4096 <= qs <= 140737488355320 /\ 0 <= qs < 2 ^ 64) by (subst qs; clear - QR1 QR2 Hk NL; lia). destruct QSR as [QSR QSRG].
  assert (QSAL : aligned qs 8) by (unfold aligned; subst qs; apply al8; exact QR8).
  assert (QSNS : 2147446784 + 17592186048512 <= qs \/ qs + 8 <= 2147446784) by (subst qs; clear - QNS Hk NL; lia).
  assert (QSZ : L5KA.zeros_at M4 (qs / 8 + 2147450880) 1). { eapply L5KA.zeros_at_sub. exact QZ4. rewrite QD8; clear - Hk; lia. rewrite QD8; clear - Hk; lia. }
  assert (QF1 : E - 352 + 352 <= qs \/ qs + 8 <= E - 352) by (subst qs; clear - AP5 Hk NL; lia).
  assert (QF2 : E - 352 + 352 <= qs / 8 + 2147450880 \/ qs / 8 + 2147450880 + 1 <= E - 352) by (rewrite QD8; clear - DQB ER Hk NL; lia).
  assert (QF3 : qs + 8 <= qs / 8 + 2147450880 \/ qs / 8 + 2147450880 + 1 <= qs) by (rewrite QD8; clear - DQ8' DQB QNS QR1 QR2 Hk NL; subst qs; lia).
  assert (QSW : L5.writable RSEGS M4 qs 8). { eapply L5.writable_sub. exact QW4. subst qs; clear - Hk; lia. subst qs; clear - Hk; lia. }
  destruct (defined_word M4 (E - 184) ltac:(eapply L5.defined_sub; [exact FD4 | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia)) as (q4 & Q4R & Q4).
  assert (FW352' : L5.writable RSEGS M4 (E - 352) 352). { eapply L5.writable_sub. exact FW4. clear; lia. clear; lia. }
  set (s3v := Dr - 8 * (n - k)). set (s9v := Dq - 8 * (l + 1) - 8 * (n - k)).
  assert (VR : 0 <= s3v <= 18446744073709551615 /\ 0 <= s4v <= 18446744073709551615 /\ 0 <= 8 * n <= 18446744073709551615 /\ 1 <= k <= 134217727 /\ 0 <= l <= 134217727
               /\ 0 <= q4 <= 18446744073709551615) by (subst s3v s4v; clear - RR1 RR2 Hk NL Q4R; lia).
  destruct VR as (V1 & V2 & V3 & V4 & V5 & V6).
  assert (K19 : getr R4 (reg 19) = Z_to_bv 64 s3v). { rewrite (sKS 19%nat) by inl. rewrite (bKS 19%nat) by inl. rewrite (dKS 19%nat) by inl. rewrite (aKS 19%nat) by inl. exact h19. }
  assert (K20 : getr R4 (reg 20) = Z_to_bv 64 s4v). { rewrite (sKS 20%nat) by inl. rewrite (bKS 20%nat) by inl. rewrite (dKS 20%nat) by inl. rewrite (aKS 20%nat) by inl. exact h20. }
  assert (K21 : getr R4 (reg 21) = Z_to_bv 64 (8 * n)). { rewrite (sKS 21%nat) by inl. rewrite (bKS 21%nat) by inl. rewrite (dKS 21%nat) by inl. rewrite (aKS 21%nat) by inl. exact h21. }
  assert (K22 : getr R4 (reg 22) = Z_to_bv 64 k). { rewrite (sKS 22%nat) by inl. rewrite (bKS 22%nat) by inl. rewrite (dKS 22%nat) by inl. rewrite (aKS 22%nat) by inl. exact h22. }
  assert (K23 : getr R4 (reg 23) = Z_to_bv 64 s3v). { rewrite (sKS 23%nat) by inl. rewrite (bKS 23%nat) by inl. rewrite (dKS 23%nat) by inl. rewrite (aKS 23%nat) by inl. exact h23. }
  assert (K25 : getr R4 (reg 25) = Z_to_bv 64 (-1 * (8 * n) + qs)). { rewrite (sKS 25%nat) by inl. rewrite (bKS 25%nat) by inl. rewrite (dKS 25%nat) by inl. rewrite (aKS 25%nat) by inl. rewrite h25. f_equal. subst qs. clear; lia. }
  assert (K27 : getr R4 (reg 27) = Z_to_bv 64 (-1 * (8 * n) + qs)). { rewrite (sKS 27%nat) by inl. rewrite (bKS 27%nat) by inl. rewrite (dKS 27%nat) by inl. rewrite (aKS 27%nat) by inl. rewrite h27. f_equal. subst qs. clear; lia. }
  assert (K26 : getr R4 (reg 26) = Z_to_bv 64 2147450880). { rewrite (sKS 26%nat) by inl. rewrite (bKS 26%nat) by inl. rewrite (dKS 26%nat) by inl. rewrite (aKS 26%nat) by inl. exact h26. }
  assert (K2 : getr R4 (reg 2) = Z_to_bv 64 (E - 352)). { rewrite (sKS 2%nat) by inl. exact R3_2. }
  assert (K8 : getr R4 (reg 8) = Z_to_bv 64 E). { rewrite (sKS 8%nat) by inl. rewrite (bKS 8%nat) by inl. rewrite (dKS 8%nat) by inl. rewrite (aKS 8%nat) by inl. exact h8. }
  assert (K9 : getr R4 (reg 9) = Z_to_bv 64 (E - 352)). { rewrite (sKS 9%nat) by inl. rewrite (bKS 9%nat) by inl. rewrite (dKS 9%nat) by inl. rewrite (aKS 9%nat) by inl. exact h9. }
  assert (K3 : getr R4 (reg 3) = getr R0 (reg 3)). { rewrite (sKS 3%nat) by inl. rewrite (bKS 3%nat) by inl. rewrite (dKS 3%nat) by inl. rewrite (aKS 3%nat) by inl. exact h3. }
  assert (K4 : getr R4 (reg 4) = getr R0 (reg 4)). { rewrite (sKS 4%nat) by inl. rewrite (bKS 4%nat) by inl. rewrite (dKS 4%nat) by inl. rewrite (aKS 4%nat) by inl. exact h4. }
  assert (K18 : getr R4 (reg 18) = Z_to_bv 64 to). { rewrite (sKS 18%nat) by inl. rewrite (bKS 18%nat) by inl. rewrite (dKS 18%nat) by inl. rewrite (aKS 18%nat) by inl. exact h18. }
  assert (K24 : getr R4 (reg 24) = Z_to_bv 64 d). { rewrite (sKS 24%nat) by inl. rewrite (bKS 24%nat) by inl. rewrite (dKS 24%nat) by inl. rewrite (aKS 24%nat) by inl. exact h24. }
  destruct (Z.eq_dec (k - l) 1) as [KL1|KL1].
  - (* [comment removed for export] *)
    assert (KLR : 1 <= k - l <= 1) by (clear - KL1; lia).
    pose proof (v5GLcl_conc fx4 R4 M4 (fun j => match j with 2%nat => E | 58%nat => U R4 1 | 70%nat => s3v | 73%nat => k | 74%nat => l | 78%nat => q4 | 79%nat => 8 * n | 83%nat => s3v | 84%nat => qs | 85%nat => s4v | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx5 & R5 & M5 & MG5 & _ & cFZ & (cMS & cKS & _)).
    assert (LA5 : lagreeI M4 M5). { split. exact MG5. intros x Hx Hn. apply cFZ. exact Hx. intros X. apply Hn. unfold FPI. right; right; right; right. subst qs. clear - X Hk NL. lia. }
    exists fx5, R5, M5. split. { eapply lagreeI_trans. exact LA3. eapply lagreeI_trans. exact LA4. exact LA5. }
    left. split. exact KL1. split. { eapply msteps_trans. exact aMS. eapply msteps_trans. exact dMS. eapply msteps_trans. exact bMS. eapply msteps_trans. exact sMS. exact cMS. }
    unfold kept5. rewrite (cKS 2%nat), (cKS 8%nat), (cKS 9%nat), (cKS 3%nat), (cKS 4%nat) by inl. repeat split; assumption.
  - (* [comment removed for export] *)
    assert (KLR : 2 <= k - l <= 134217728) by (clear - KL1 Hk NL; lia).
    pose proof (v5GLcm_conc fx4 R4 M4 (fun j => match j with 2%nat => E | 58%nat => U R4 1 | 70%nat => s3v | 73%nat => k | 74%nat => l | 78%nat => q4 | 79%nat => 8 * n | 83%nat => s3v | 84%nat => qs | 85%nat => s4v | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx5 & R5 & M5 & MG5 & _ & cFZ & (cMS & cKS & c10 & c11 & c19 & c20 & c22 & c23 & c25 & c27 & _)).
    assert (LA5 : lagreeI M4 M5). { split. exact MG5. intros x Hx Hn. apply cFZ. exact Hx. intros X. apply Hn. unfold FPI. right; right; right; right. subst qs. clear - X Hk NL. lia. }
    exists fx5, R5, M5. split. { eapply lagreeI_trans. exact LA3. eapply lagreeI_trans. exact LA4. exact LA5. }
    right. split. clear - KLR; lia. split. { eapply msteps_trans. exact aMS. eapply msteps_trans. exact dMS. eapply msteps_trans. exact bMS. eapply msteps_trans. exact sMS. exact cMS. }
    unfold hregs. rewrite (cKS 2%nat), (cKS 8%nat), (cKS 9%nat), (cKS 3%nat), (cKS 4%nat), (cKS 18%nat), (cKS 21%nat), (cKS 24%nat), (cKS 26%nat) by inl.
    split. exact K2. split. exact K8. split. exact K9. split. exact K3. split. exact K4. split. exact K18.
    split. { rewrite c19. f_equal. subst s3v. clear; lia. } split. { rewrite c20. f_equal. subst s4v. clear; lia. } split. exact K21.
    split. { rewrite c22. reflexivity. } split. { rewrite c23. f_equal. subst s3v. clear; lia. } split. exact K24.
    split. { rewrite c25. f_equal. subst qs. clear; lia. } split. exact K26. rewrite c27. f_equal. subst qs. clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gloop_iter (j : nat) : forall (fx : FPState) R0 Rk Mk k, k = l + 1 + Z.of_nat j -> k <= n -> lctx Mk -> hregs R0 Rk k ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx Rk 0x9294c Mk) (st fx' R' 0x929e8 M') /\ lagreeI Mk M' /\ kept5 R0 R'.
Proof.
  induction j as [|j IH]; intros fx R0 Rk Mk k Hk Hn C HR.
  - destruct (giter fx R0 Rk Mk k C HR ltac:(clear - Hk Hn; lia)) as (fx' & R' & M' & LA & [(E1 & MS & K5)|(E2 & _)]).
    + exists fx', R', M'. split. exact MS. split. exact LA. exact K5.
    + exfalso. clear - Hk E2. lia.
  - destruct (giter fx R0 Rk Mk k C HR ltac:(clear - Hk Hn; lia)) as (fx1 & R1 & M1 & LA & [(E1 & _)|(E2 & MS & HR')]).
    + exfalso. clear - Hk E1. lia.
    + destruct (IH fx1 R0 R1 M1 (k - 1) ltac:(clear - Hk; lia) ltac:(clear - Hn; lia) (lctx_keep Mk M1 C (lagree_of_I _ _ LA)) HR') as (fx' & R' & M' & MS' & LA' & K5).
      exists fx', R', M'. split. eapply msteps_trans. exact MS. exact MS'. split. eapply lagreeI_trans. exact LA. exact LA'. exact K5.
Qed.

Definition eregs (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 SPA /\ getr R (reg 8) = Z_to_bv 64 E /\ getr R (reg 9) = Z_to_bv 64 SPA /\
  getr R (reg 19) = Z_to_bv 64 Dr /\ getr R (reg 20) = Z_to_bv 64 Dq /\ getr R (reg 21) = Z_to_bv 64 sdl /\ getr R (reg 22) = Z_to_bv 64 n /\ getr R (reg 24) = Z_to_bv 64 (Dd + 8 * l).

Theorem gloop_run (fx : FPState) R M0 : lctx M0 -> eregs R ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R 0x9290c M0) (st fx' R' 0x929e8 M') /\ lagree M0 M' /\ kept5 R R'
    /\ L5.u64_at RSEGS M' (E - 328) (U R 18) /\ L5.u64_at RSEGS M' (E - 320) (U R 26).
Proof.
  intros C (e2 & e8 & e9 & e19 & e20 & e21 & e22 & e24).
  pose proof C as [ER EA NL FW FD (IMG & S1 & S2) SL SDD SDL SSB STO TOR (RR1 & RR2 & RR8 & RNS & ROI) RW RD RZ (QR1 & QR2 & QR8 & QNS & QOI) QW QZ (DR1 & DR2 & DR8 & DNS) DD DZ (DV & DVR) SD QC (AP1 & AP2 & AP3 & AP4 & AP5 & AP6)].
  unfold nsh, oim in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - ER; lia). destruct ER' as [ER' ERG].
  assert (EAL : aligned E 32) by exact EA.
  assert (FW352 : L5.writable RSEGS M0 (E - 352) 352). { eapply L5.writable_sub. exact FW. clear; lia. clear; lia. }
  set (dl := Dd + 8 * l).
  pose proof (div8 Dd l DR8) as [DL8 DD8']. fold dl in DL8.
  assert (DDB : 0 <= Dd / 8 /\ Dd / 8 <= 17592186043904) by (clear - DD8' DR1 DR2 NL; lia).
  assert (SDE : sdl = dl / 8 + 2147450880) by exact SD.
  assert (DLR : 4096 <= dl <= 140737488355320 /\ 0 <= dl < 2 ^ 64) by (subst dl; clear - DR1 DR2 NL; lia). destruct DLR as [DLR DLRG].
  assert (DLAL : aligned dl 8) by (unfold aligned; subst dl; apply al8; exact DR8).
  assert (DLNS : 2147446784 + 17592186048512 <= dl \/ dl + 8 <= 2147446784) by (subst dl; clear - DNS NL; lia).
  assert (DLZ : L5KA.zeros_at M0 (dl / 8 + 2147450880) 1). { eapply L5KA.zeros_at_sub. exact DZ. rewrite DL8; clear - NL; lia. rewrite DL8; clear - NL; lia. }
  assert (DLZ' : L5KA.zeros_at M0 sdl 1) by (rewrite SDE; exact DLZ).
  assert (SDR : 2147450880 <= sdl <= 17594333495295 /\ 0 <= sdl < 2 ^ 64) by (rewrite SDE, DL8; clear - DDB NL; lia). destruct SDR as [SDR SDRG].
  assert (SDF : E - 352 + 352 <= sdl \/ sdl + 1 <= E - 352) by (clear - SDR ER; lia).
  assert (DF1 : E - 352 + 352 <= dl \/ dl + 8 <= E - 352) by (subst dl; clear - AP6 NL; lia).
  assert (DF2 : E - 352 + 352 <= dl / 8 + 2147450880 \/ dl / 8 + 2147450880 + 1 <= E - 352) by (rewrite DL8; clear - DDB ER NL; lia).
  assert (DF3 : dl + 8 <= dl / 8 + 2147450880 \/ dl / 8 + 2147450880 + 1 <= dl) by (rewrite DL8; clear - DD8' DDB DNS DR1 DR2 NL; subst dl; lia).
  assert (VR : 0 <= Dr <= 18446744073709551615 /\ 0 <= Dq <= 18446744073709551615 /\ 0 <= n <= 134217727 /\ 0 <= l <= 134217727 /\ 0 <= d <= 18446744073709551615 /\ 0 <= l + 1 <= 18446744073709551615
               /\ 0 <= to <= 18446744073709551615 /\ 0 <= Dr < 2 ^ 64 /\ 0 <= Dq < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= l < 2 ^ 64 /\ 0 <= d < 2 ^ 64 /\ 0 <= l + 1 < 2 ^ 64)
    by (clear - RR1 RR2 QR1 QR2 NL DVR TOR; lia).
  destruct VR as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V1' & V2' & V3' & V4' & V5' & V6').
  assert (J18 : 0 <= U R 18 <= 18446744073709551615 /\ 0 <= U R 26 <= 18446744073709551615) by (pose proof (UR R 18); pose proof (UR R 26); lia). destruct J18 as [J18 J26].
  destruct (Z_le_gt_dec n l) as [NLE|NGT].
  - (* [comment removed for export] *)
    assert (REL : 0 <= l - n <= 134217728) by (clear - NLE NL; lia).
    pose proof (v5G9x_conc fx R M0 (fun j => match j with 2%nat => E | 58%nat => U R 1 | 68%nat => Dq | 70%nat => Dr | 73%nat => n | 74%nat => l | 80%nat => dl | 81%nat => sdl | 87%nat => U R 18 | 89%nat => U R 26 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & xFZ & (xMS & xKS & _ & xC0 & xC1)).
    exists fx1, R1, M1. split. exact xMS.
    split. { split. exact MG1. intros a Ha Hn. apply xFZ. exact Ha. intros X. apply Hn. unfold FP. right; left. clear - X; lia. intros X. apply Hn. unfold FP. right; left. clear - X; lia. }
    split. { unfold kept5. rewrite (xKS 2%nat), (xKS 8%nat), (xKS 9%nat), (xKS 3%nat), (xKS 4%nat) by inl. repeat split; first [assumption | reflexivity]. }
    split. exact xC0. exact xC1.
  - (* [comment removed for export] *)
    assert (REL : 1 <= n - l <= 134217728) by (clear - NGT NL; lia).
    pose proof (v5G9l_conc fx R M0 (fun j => match j with 2%nat => E | 33%nat => to | 58%nat => U R 1 | 64%nat => l + 1 | 68%nat => Dq | 70%nat => Dr | 73%nat => n | 74%nat => l | 75%nat => d | 80%nat => dl | 81%nat => sdl | 87%nat => U R 18 | 89%nat => U R 26 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & lFZ & (lMS & lKS & l10 & l18 & l20 & l21 & l23 & l24 & l25 & l26 & l27 & lC0 & lC1)).
    assert (LA1 : lagree M0 M1). { split. exact MG1. intros a Ha Hn. apply lFZ. exact Ha. intros X. apply Hn. unfold FP. right; left. clear - X; lia. intros X. apply Hn. unfold FP. right; left. clear - X; lia. }
    assert (HR1 : hregs R R1 n).
    { unfold hregs. rewrite (lKS 2%nat), (lKS 8%nat), (lKS 9%nat), (lKS 3%nat), (lKS 4%nat), (lKS 19%nat), (lKS 22%nat) by inl.
      split. exact e2. split. exact e8. split. exact e9. split. reflexivity. split. reflexivity. split. exact l18.
      split. { rewrite e19. f_equal. clear; lia. } split. { rewrite l20. f_equal. clear; lia. } split. exact l21. split. exact e22.
      split. { rewrite l23. f_equal. clear; lia. } split. exact l24. split. { rewrite l25. f_equal. clear; lia. } split. exact l26. rewrite l27. f_equal. clear; lia. }
    destruct (gloop_iter (Z.to_nat (n - l - 1)) fx1 R R1 M1 n ltac:(rewrite Z2Nat.id by (clear - NGT; lia); clear; lia) ltac:(clear; lia) (lctx_keep M0 M1 C LA1) HR1)
      as (fx' & R' & M' & MS' & LA' & K5).
    exists fx', R', M'. split. eapply msteps_trans. exact lMS. exact MS'. split. eapply lagree_trans. exact LA1. exact (lagree_of_I _ _ LA'). split. exact K5.
    destruct LA' as [_ AGI].
    assert (NI : forall i, E - 328 <= i < E - 312 -> ~ FPI i). { intros i Hi. unfold FPI. clear - Hi ER RR1 RR2 QR1 QR2 AP4 AP5 NL. intros [X|[X|[X|[X|X]]]]; lia. }
    split.
    + eapply L5C.u64_at_agree. 4: exact lC0. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply AGI. clear - Hi ER; lia. apply NI. clear - Hi; lia.
    + eapply L5C.u64_at_agree. 4: exact lC1. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply AGI. clear - Hi ER; lia. apply NI. clear - Hi; lia.
Qed.
End LOOP.
End SCFG_1.
End L5ADVGL.
