(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BDDq L5BSubMul L5BDivPG2.
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
Variables (E to Dr Dq Dd d n l : Z).
Local Notation SPA := (E - 384).
Local Notation SBZ := 2147450880.

(* [comment removed for export] *)
Definition FP (a : Z) : Prop :=
  SPA - 96 <= a < SPA \/ False \/ E - 248 <= a < E - 240 \/ Dr <= a < Dr + 8 * (n + 1) \/ Dq <= a < Dq + 8 * (n - l).
Definition lagree (M0 Mk : word -> option byte) : Prop :=
  mem_grows M0 Mk /\ forall a, 0 <= a < 2 ^ 64 -> ~ FP a -> Mk (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Lemma lagree_refl M0 : lagree M0 M0. Proof. split. apply mem_grows_refl. intros; reflexivity. Qed.
Lemma lagree_trans M0 M1 M2 : lagree M0 M1 -> lagree M1 M2 -> lagree M0 M2.
Proof. intros [G1 A1] [G2 A2]. split. eapply mem_grows_trans; eassumption. intros a Ha Hn. rewrite A2 by assumption. apply A1; assumption. Qed.

Definition nsh (x lx : Z) : Prop := 2147446784 + 17592186048512 <= x \/ x + lx <= 2147446784.
Definition oim (x lx : Z) : Prop := x + lx <= 65536 \/ 6504448 <= x.

(* [comment removed for export] *)
Record lctx (M : word -> option byte) : Prop := LCTX {
  lc_E : 140735332487680 <= E <= 140737488355328;
  lc_EA : E mod 32 = 0;
  lc_n : 0 <= l /\ l <= 298 /\ 0 <= n <= 299;
  lc_fw : L5.writable RSEGS M (SPA - 96) (384 + 96);
  lc_fd : L5.defined M (SPA - 96) (384 + 96);
  lc_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  lc_sdl : L5.u64_at RSEGS M (E - 272) (l + 1);
  lc_sto : L5.u64_at RSEGS M (E - 264) to;
  lc_vr : L5.u64_at RSEGS M (E - 240) Dr;
  lc_vq : L5.u64_at RSEGS M (E - 136) Dq;
  lc_vd : L5.u64_at RSEGS M (E - 120) Dd;
  lc_fz : L5KA.zeros_at M ((E - 384) / 8 + 2147450880) 48;
  lc_to : 0 <= to < 2 ^ 64;
  lc_r : 4096 <= Dr /\ Dr + 8 * (n + 1) <= 140737479966720 /\ Dr mod 8 = 0 /\ nsh Dr (8 * (n + 1)) /\ oim Dr (8 * (n + 1));
  lc_rw : L5.writable RSEGS M Dr (8 * (n + 1));
  lc_rd : L5.defined M Dr (8 * (n + 1));
  lc_rz : L5KA.zeros_at M (Dr / 8 + 2147450880) (n + 1);
  lc_q : 4096 <= Dq /\ Dq + 8 * (n - l) <= 140737479966720 /\ Dq mod 8 = 0 /\ nsh Dq (8 * (n - l)) /\ oim Dq (8 * (n - l));
  lc_qw : L5.writable RSEGS M Dq (8 * (n - l));
  lc_qz : L5KA.zeros_at M (Dq / 8 + 2147450880) (n - l);
  lc_d : 4096 <= Dd /\ Dd + 8 * (l + 1) <= 140737479966720 /\ Dd mod 8 = 0 /\ nsh Dd (8 * (l + 1));
  lc_dd : L5.defined M Dd (8 * (l + 1));
  lc_dz : L5KA.zeros_at M (Dd / 8 + 2147450880) (l + 1);
  lc_dv : L5.u64_at RSEGS M (Dd + 8 * l) d /\ 2 ^ 63 <= d < 2 ^ 64;
  lc_ap : (Dr + 8 * (n + 1) <= Dq \/ Dq + 8 * (n - l) <= Dr) /\ (Dr + 8 * (n + 1) <= Dd \/ Dd + 8 * (l + 1) <= Dr) /\ (Dq + 8 * (n - l) <= Dd \/ Dd + 8 * (l + 1) <= Dq)
          /\ Dr + 8 * (n + 1) <= SPA - 96 /\ Dq + 8 * (n - l) <= SPA - 96 /\ Dd + 8 * (l + 1) <= SPA - 96 }.

Lemma sh_not_FP M : lctx M -> forall a, 2147450880 <= a < 17594333495296 -> ~ FP a.
Proof.
  intros C a Ha. pose proof (lc_E _ C) as ER. pose proof (lc_r _ C) as (_ & _ & _ & NR & _). pose proof (lc_q _ C) as (_ & _ & _ & NQ & _). pose proof (lc_n _ C) as NL.
  unfold FP, nsh in *. intros [X|[X|[X|[X|X]]]]; [ | destruct X | | | ]; clear - X Ha ER NR NQ NL; lia.
Qed.
Lemma img_not_FP M : lctx M -> forall a, 65536 <= a < 6504448 -> ~ FP a.
Proof.
  intros C a Ha. pose proof (lc_E _ C) as ER. pose proof (lc_r _ C) as (_ & _ & _ & _ & NR). pose proof (lc_q _ C) as (_ & _ & _ & _ & NQ). pose proof (lc_n _ C) as NL.
  unfold FP, oim in *. intros [X|[X|[X|[X|X]]]]; [ | destruct X | | | ]; clear - X Ha ER NR NQ NL; lia.
Qed.
Lemma u64_keep M0 Mk a v : lagree M0 Mk -> (forall i, a <= i < a + 8 -> ~ FP i) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M0 a v -> L5.u64_at RSEGS Mk a v.
Proof. intros [_ AG] NF H0 H1 Hu. eapply L5C.u64_at_agree. 4: exact Hu. 2: exact H0. 2: exact H1. intros j Hj. apply AG. lia. apply NF. exact Hj. Qed.
Lemma zeros_keep M0 Mk a m : lctx M0 -> lagree M0 Mk -> 2147450880 <= a -> a + m <= 17594333495296 -> L5KA.zeros_at M0 a m -> L5KA.zeros_at Mk a m.
Proof. intros C [_ AG] H0 H1 Hz. apply (L5KA.zeros_at_agree1 M0 Mk a m). 2: exact Hz. intros i Hi. apply AG. lia. apply (sh_not_FP M0 C). lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lctx_keep M0 Mk : lctx M0 -> lagree M0 Mk -> lctx Mk.
Proof.
  intros C LA. pose proof LA as [MG AG]. destruct C as [ER EA NL FW FD (IMG & S1 & S2) SDL STO VR VQ VD FZ TOR RR RW RD RZ QR QW QZ DR DD DZ (DV & DVR) AP].
  pose proof (LCTX M0 ER EA NL FW FD (conj IMG (conj S1 S2)) SDL STO VR VQ VD FZ TOR RR RW RD RZ QR QW QZ DR DD DZ (conj DV DVR) AP) as C.
  assert (FRM : forall a, SPA <= a < E -> ~ (E - 248 <= a < E - 240) -> ~ FP a).
  { intros a Ha N2. unfold FP. destruct AP as (_ & _ & _ & A4 & A5 & _). clear - Ha N2 A4 A5 NL. lia. }
  constructor; try assumption.
  - eapply L5.writable_grows; eassumption.
  - eapply L5.defined_grows; eassumption.
  - split. { intros i Hi. rewrite AG. apply IMG. exact Hi. lia. apply (img_not_FP M0 C). lia. }
    split. apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply (img_not_FP M0 C). lia. lia. lia. exact S1.
    unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M0 Mk 4 911168 ltac:(lia) ltac:(cbn; lia)). exact S2. intros i Hi. apply AG. cbn in Hi; lia. apply (img_not_FP M0 C). cbn in Hi; lia.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact SDL.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact STO.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact VR.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact VQ.
  - apply (u64_keep M0 Mk _ _ LA). intros i Hi. apply FRM; lia. lia. lia. exact VD.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact FZ. lia. lia.
  - eapply L5.writable_grows; eassumption.
  - eapply L5.defined_grows; eassumption.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact RZ. destruct RR as (R1 & R2 & _). lia. destruct RR as (R1 & R2 & _). lia.
  - eapply L5.writable_grows; eassumption.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact QZ. destruct QR as (R1 & R2 & _). lia. destruct QR as (R1 & R2 & _). lia.
  - eapply L5.defined_grows; eassumption.
  - apply (zeros_keep M0 Mk _ _ C LA). 3: exact DZ. destruct DR as (R1 & R2 & _). lia. destruct DR as (R1 & R2 & _). lia.
  - split. 2: exact DVR. apply (u64_keep M0 Mk _ _ LA). 4: exact DV. 2: destruct DR as (R1 & R2 & _); lia. 2: destruct DR as (R1 & R2 & _); lia.
    intros i Hi. unfold FP. destruct AP as (_ & A2 & A3 & _ & _ & A6). destruct DR as (R1 & R2 & _). clear - Hi A2 A3 A6 NL ER R1 R2. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hregs (R0 Rk : bvmap 5 word) (k : Z) : Prop :=
  getr Rk (reg 2) = Z_to_bv 64 SPA /\ getr Rk (reg 8) = Z_to_bv 64 E /\ getr Rk (reg 9) = Z_to_bv 64 SPA /\
  getr Rk (reg 3) = getr R0 (reg 3) /\ getr Rk (reg 4) = getr R0 (reg 4) /\
  getr Rk (reg 18) = getr R0 (reg 18) /\ getr Rk (reg 19) = Z_to_bv 64 k /\ getr Rk (reg 21) = Z_to_bv 64 ((-1) * l + 1152921504606846975) /\
  getr Rk (reg 23) = Z_to_bv 64 2147450880 /\ getr Rk (reg 24) = Z_to_bv 64 (8 * (k - l - 1)) /\ getr Rk (reg 25) = Z_to_bv 64 ((-1) * l - 1) /\
  getr Rk (reg 26) = Z_to_bv 64 d /\ getr Rk (reg 27) = Z_to_bv 64 l.
Definition kept5 (R0 R' : bvmap 5 word) : Prop :=
  getr R' (reg 2) = Z_to_bv 64 SPA /\ getr R' (reg 8) = Z_to_bv 64 E /\ getr R' (reg 9) = Z_to_bv 64 SPA /\ getr R' (reg 3) = getr R0 (reg 3) /\ getr R' (reg 4) = getr R0 (reg 4).
(* [comment removed for export] *)
Definition kept7 (R0 R' : bvmap 5 word) : Prop :=
  kept5 R0 R' /\ getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 23) = Z_to_bv 64 2147450880.

Local Ltac rg H := rewrite H; f_equal; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma div8 x j : x mod 8 = 0 -> (x + 8 * j) / 8 = x / 8 + j /\ x / 8 * 8 = x.
Proof. intros H. split; lia. Qed.
Lemma al8 x j : x mod 8 = 0 -> (x + 8 * j) mod 8 = 0. Proof. intros H. lia. Qed.
Lemma e32 : E mod 32 = 0 -> (E - 384) mod 16 = 0 /\ (E - 248) mod 8 = 0 /\ (E - 248) / 8 = (E - 384) / 8 + 17 /\ (E - 240) / 8 = (E - 384) / 8 + 18 /\ (E - 136) / 8 = (E - 384) / 8 + 31
  /\ (E - 120) / 8 = (E - 384) / 8 + 33 /\ (E - 384) / 8 * 8 = E - 384.
Proof. intros H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma la_slot Mk M1 : mem_grows Mk M1 -> (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (E - 392 <= i < E - 392 + 8) -> M1 (Z_to_bv 64 i) = Mk (Z_to_bv 64 i)) -> lagree Mk M1.
Proof. intros MG FZ. split. exact MG. intros a Ha Hn. apply FZ. exact Ha. intros X. apply Hn. unfold FP. left. clear - X; lia. Qed.

Lemma giter (fx : FPState) R0 Rk Mk k : lctx Mk -> hregs R0 Rk k -> l < k <= n ->
  exists (fx' : FPState) R' M', lagree Mk M' /\
    ((k - l = 1 /\ msteps RSEGS (st fx Rk 0x93394 Mk) (st fx' R' 0x93458 M') /\ kept7 R0 R')
     \/ (2 <= k - l /\ msteps RSEGS (st fx Rk 0x93394 Mk) (st fx' R' 0x93394 M') /\ hregs R0 R' (k - 1))).
Proof.
  intros C (h2 & h8 & h9 & h3 & h4 & h18 & h19 & h21 & h23 & h24 & h25 & h26 & h27) Hk.
  pose proof C as [ER EA NL FW FD (IMG & S1 & S2) SDL STO VR VQ VD FZ TOR (RR1 & RR2 & RR8 & RNS & ROI) RW RD RZ (QR1 & QR2 & QR8 & QNS & QOI) QW QZ (DR1 & DR2 & DR8 & DNS) DD DZ (DV & DVR) (AP1 & AP2 & AP3 & AP4 & AP5 & AP6)].
  unfold nsh, oim in *.
  assert (ER' : 140735332487632 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64 /\ 140735332487616 <= E <= 140737488355328) by lia. destruct ER' as (ER' & ERG & ER'').
  assert (EAL : aligned E 32) by exact EA.
  pose proof (e32 EA) as (SP16 & QA8 & QAD & VRD & VQD & VDD & SPD).
  assert (SPB : 17591916560912 <= (E - 384) / 8 /\ (E - 384) / 8 + 48 <= 17592186044416) by (clear - SPD ER; lia).
  assert (FW400 : L5.writable RSEGS Mk (E - 400) 400). { eapply L5.writable_sub. exact FW. lia. lia. }
  assert (VZR : L5KA.zeros_at Mk ((E - 240) / 8 + 2147450880) 1). { rewrite VRD. eapply L5KA.zeros_at_sub. exact FZ. clear; lia. clear; lia. }
  set (A := Dr + 8 * k).
  pose proof (div8 Dr 0 RR8) as [_ DR8'].
  assert (DRB : 0 <= Dr / 8 /\ Dr / 8 <= 17592186043904) by (clear - DR8' RR1 RR2 NL; lia).
  assert (RCAP : 1 <= n + 1 <= 134217728 /\ 1 <= n + 1 - k <= 134217728 /\ 1 <= k <= 134217727 /\ 0 <= n + 1 < 2 ^ 64 /\ 0 <= k < 2 ^ 64) by (clear - Hk NL; lia).
  destruct RCAP as (RC1 & RC2 & RC3 & RC4 & RC5).
  destruct (defined_word Mk (A - 8) ltac:(eapply L5.defined_sub; [exact RD | subst A; lia | subst A; lia]) ltac:(subst A; lia) ltac:(subst A; lia)) as (w1 & W1R & W1).
  destruct (defined_word Mk A ltac:(eapply L5.defined_sub; [exact RD | subst A; lia | subst A; lia]) ltac:(subst A; lia) ltac:(subst A; lia)) as (w2 & W2R & W2).
  subst A.
  assert (DRG : 0 <= d < 2 ^ 64 /\ 0 <= Dr < 2 ^ 64 /\ 0 <= Dq < 2 ^ 64 /\ 0 <= Dd < 2 ^ 64) by lia. destruct DRG as (DRG & DrG & DqG & DdG).
  assert (RF1 : Dr + 8 * (n + 1) <= Dr / 8 + 2147450880 \/ Dr / 8 + 2147450880 + (n + 1) <= Dr) by (clear - DR8' DRB RNS RR1 RR2 NL; lia).
  assert (RF2 : E - 400 + 400 <= Dr \/ Dr + 8 * (n + 1) <= E - 400) by (clear - AP4; lia).
  assert (RF3 : E - 400 + 400 <= Dr / 8 + 2147450880 \/ Dr / 8 + 2147450880 + (n + 1) <= E - 400) by (clear - DRB ER NL; lia).
  assert (RF4 : 4104 <= Dr + 8 * (n + 1) <= 140737479966720) by (clear - RR1 RR2 NL; lia).
  (* [comment removed for export] *)
  pose proof (v5GLa_conc fx Rk Mk (fun j => match j with 2%nat => E | 33%nat => to | 58%nat => U Rk 1 | 70%nat => Dr | 71%nat => n + 1 | 73%nat => k | 75%nat => d | 76%nat => w2 | 77%nat => w1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & aFZ & (aMS & aKS & aR1 & aR10 & aR11 & aR12 & aR13 & _ & aR20 & aR22 & _)).
  pose proof (la_slot Mk M1 MG1 aFZ) as LA1.
  pose proof (lctx_keep Mk M1 C LA1) as C1.
  (* [comment removed for export] *)
  destruct (L5ADDQ.ddq_runA fx1 R1 M1 d 603112 aR13 DVR aR1 ltac:(split; [lia | reflexivity])) as (fx2 & R2 & M2 & dMS & dKS & dRP & EM2). subst M2.
  set (q := U R2 10). assert (QRG : 0 <= q <= 18446744073709551615) by (subst q; pose proof (UR R2 10); lia).
  (* [comment removed for export] *)
  pose proof C1 as [_ _ _ FW1 FD1 (IMG1 & S11 & S21) SDL1 STO1 VR1 VQ1 VD1 FZ1 _ _ RW1 RD1 RZ1 _ QW1 QZ1 _ DD1 DZ1 (DV1 & _) _].
  assert (FW384 : L5.writable RSEGS M1 (E - 384) 384). { eapply L5.writable_sub. exact FW1. lia. lia. }
  assert (JR : 0 <= k - l - 1 <= 134217727 /\ 0 <= l <= 134217727 /\ 0 <= k - l - 1 < 2 ^ 64 /\ 0 <= l < 2 ^ 64 /\ 4096 <= Dr <= 140737488355328 /\ 0 <= Dd <= 18446744073709551615
               /\ 0 <= to <= 18446744073709551615) by (clear - Hk NL RR1 RR2 DR1 DR2 TOR; lia).
  destruct JR as (JR1 & JR2 & JR3 & JR4 & JR5 & JR6 & JR7).
  assert (DRAL : aligned Dr 8) by exact RR8.
  pose proof (v5GLb_conc fx2 R2 M1 (fun j => match j with 2%nat => E | 33%nat => to | 58%nat => U R2 1 | 65%nat => Dd | 70%nat => Dr | 73%nat => k | 74%nat => l | 78%nat => q | 80%nat => k - l - 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (dKS 2%nat) by inl; rk) | (rewrite (dKS 8%nat) by inl; rk) | (rewrite (dKS 9%nat) by inl; rk) | (rewrite (dKS 18%nat) by inl; rk)
                      | (rewrite (dKS 19%nat) by inl; rk) | (rewrite (dKS 21%nat) by inl; rk) | (rewrite (dKS 23%nat) by inl; rk) | (rewrite (dKS 24%nat) by inl; rk) | (rewrite (dKS 25%nat) by inl; rk) ]).
  destruct P as (fx3 & R3 & M3 & MG3 & _ & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR14 & bR19 & bQ)).
  assert (LA3 : lagree M1 M3). { split. exact MG3. intros a Ha Hn. apply bFZ. exact Ha. intros X. apply Hn. unfold FP. right; right; left. lia. }
  pose proof (lctx_keep M1 M3 C1 LA3) as C3.
  pose proof C3 as [_ _ _ FW3 FD3 (IMG3 & S13 & S23) _ _ _ _ _ FZ3 _ _ RW3 RD3 RZ3 _ _ _ _ DD3 DZ3 _ _].
  (* [comment removed for export] *)
  set (a := Dr + 8 * (k - l - 1)). set (n' := Z.to_nat (l + 1)).
  assert (N'E : Z.of_nat n' = l + 1) by (subst n'; apply Z2Nat.id; clear - NL; lia).
  pose proof (div8 Dr (k - l - 1) RR8) as [AD8a _]. fold a in AD8a.
  assert (SMC : L5ASM.smctxA M3 SPA a Dd (E - 248) n').
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
    - rewrite QAD. eapply L5KA.zeros_at_sub. exact FZ3. clear; lia. clear; lia.
    - unfold L5ASM.apart. rewrite N'E. subst a; clear - AP4 Hk NL; lia.
    - unfold L5ASM.apart. rewrite N'E. clear - AP6 NL; lia.
    - unfold L5ASM.apart. clear; lia.
    - unfold L5ASM.apart. rewrite N'E. subst a; clear - AP2 Hk NL; lia.
    - unfold L5ASM.apart. rewrite N'E. subst a; clear - AP4 Hk NL; lia.
    - unfold L5ASM.apart. rewrite N'E. clear - AP6 NL; lia. }
  assert (R3_2 : getr R3 (reg 2) = Z_to_bv 64 SPA). { rewrite (bKS 2%nat) by inl. rewrite (dKS 2%nat) by inl. rewrite (aKS 2%nat) by inl. exact h2. }
  destruct (L5ASM.submul_runA fx3 R3 M3 SPA a Dd (E - 248) 603176 n' R3_2 ltac:(rg bR11) bR12 ltac:(rewrite N'E; exact bR13) bR14 bR1 ltac:(split; [clear; lia | reflexivity]) SMC)
    as (fx4 & R4 & M4 & sMS & sKS & sRP & _ & sAG & MG4).
  assert (LA4 : lagree M3 M4).
  { split. exact MG4. intros x Hx Hn. apply sAG. exact Hx.
    - intros X. apply Hn. unfold FP. left. exact X.
    - intros X. apply Hn. unfold FP. right; right; right; left. rewrite N'E in X. subst a. clear - X Hk NL. lia.
    - intros X. apply Hn. unfold FP. right; right; left. clear - X; lia. }
  pose proof (lctx_keep M3 M4 C3 LA4) as C4.
  pose proof C4 as [_ _ _ FW4 FD4 (IMG4 & S14 & S24) _ _ _ VQ4 _ FZ4 _ _ _ _ _ _ QW4 QZ4 _ _ _ _ _].
  (* [comment removed for export] *)
  pose proof (div8 Dq 0 QR8) as [_ DQ8'].
  assert (DQB : 0 <= Dq / 8 /\ Dq / 8 <= 17592186043904) by (clear - DQ8' QR1 QR2 NL Hk; lia).
  assert (QCAP : 1 <= n - l <= 134217728 /\ 1 <= n - l - (k - l - 1) <= 134217728 /\ 0 <= n - l < 2 ^ 64 /\ 4096 <= Dq <= 140737488355328) by (clear - Hk NL QR1 QR2; lia).
  destruct QCAP as (QC1 & QC2 & QC3 & QC4).
  assert (DQAL : aligned Dq 8) by exact QR8.
  assert (QF1 : Dq + 8 * (n - l) <= Dq / 8 + 2147450880 \/ Dq / 8 + 2147450880 + (n - l) <= Dq) by (clear - DQ8' DQB QNS QR1 QR2 NL Hk; lia).
  assert (QF2 : E - 400 + 400 <= Dq \/ Dq + 8 * (n - l) <= E - 400) by (clear - AP5; lia).
  assert (QF3 : E - 400 + 400 <= Dq / 8 + 2147450880 \/ Dq / 8 + 2147450880 + (n - l) <= E - 400) by (clear - DQB ER NL Hk; lia).
  assert (QF4 : 4104 <= Dq + 8 * (n - l) <= 140737479966720) by (clear - QR1 QR2 NL Hk; lia).
  assert (QF5 : 65536 + 6438912 <= Dq \/ Dq + 8 * (n - l) <= 65536) by (clear - QOI; lia).
  assert (VZQ : L5KA.zeros_at M4 ((E - 136) / 8 + 2147450880) 1). { rewrite VQD. eapply L5KA.zeros_at_sub. exact FZ4. clear; lia. clear; lia. }
  destruct (defined_word M4 (E - 248) ltac:(eapply L5.defined_sub; [exact FD4 | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia)) as (q4 & Q4R & Q4).
  assert (FW400' : L5.writable RSEGS M4 (E - 400) 400). { eapply L5.writable_sub. exact FW4. clear; lia. clear; lia. }
  assert (V6 : 0 <= q4 <= 18446744073709551615) by (clear - Q4R; lia).
  assert (K19 : getr R4 (reg 19) = Z_to_bv 64 (k - l - 1)). { rewrite (sKS 19%nat) by inl. exact bR19. }
  assert (K22 : getr R4 (reg 22) = Z_to_bv 64 (k - 1)). { rewrite (sKS 22%nat) by inl. rewrite (bKS 22%nat) by inl. rewrite (dKS 22%nat) by inl. exact aR22. }
  assert (K24 : getr R4 (reg 24) = Z_to_bv 64 (8 * (k - l - 1))). { rewrite (sKS 24%nat) by inl. rewrite (bKS 24%nat) by inl. rewrite (dKS 24%nat) by inl. rewrite (aKS 24%nat) by inl. exact h24. }
  assert (K27 : getr R4 (reg 27) = Z_to_bv 64 l). { rewrite (sKS 27%nat) by inl. rewrite (bKS 27%nat) by inl. rewrite (dKS 27%nat) by inl. rewrite (aKS 27%nat) by inl. exact h27. }
  assert (K2 : getr R4 (reg 2) = Z_to_bv 64 (E - 384)). { rewrite (sKS 2%nat) by inl. exact R3_2. }
  assert (K8 : getr R4 (reg 8) = Z_to_bv 64 E). { rewrite (sKS 8%nat) by inl. rewrite (bKS 8%nat) by inl. rewrite (dKS 8%nat) by inl. rewrite (aKS 8%nat) by inl. exact h8. }
  assert (K9 : getr R4 (reg 9) = Z_to_bv 64 (E - 384)). { rewrite (sKS 9%nat) by inl. rewrite (bKS 9%nat) by inl. rewrite (dKS 9%nat) by inl. rewrite (aKS 9%nat) by inl. exact h9. }
  assert (K3 : getr R4 (reg 3) = getr R0 (reg 3)). { rewrite (sKS 3%nat) by inl. rewrite (bKS 3%nat) by inl. rewrite (dKS 3%nat) by inl. rewrite (aKS 3%nat) by inl. exact h3. }
  assert (K4 : getr R4 (reg 4) = getr R0 (reg 4)). { rewrite (sKS 4%nat) by inl. rewrite (bKS 4%nat) by inl. rewrite (dKS 4%nat) by inl. rewrite (aKS 4%nat) by inl. exact h4. }
  assert (K18 : getr R4 (reg 18) = getr R0 (reg 18)). { rewrite (sKS 18%nat) by inl. rewrite (bKS 18%nat) by inl. rewrite (dKS 18%nat) by inl. rewrite (aKS 18%nat) by inl. exact h18. }
  assert (K21 : getr R4 (reg 21) = Z_to_bv 64 ((-1) * l + 1152921504606846975)). { rewrite (sKS 21%nat) by inl. rewrite (bKS 21%nat) by inl. rewrite (dKS 21%nat) by inl. rewrite (aKS 21%nat) by inl. exact h21. }
  assert (K23 : getr R4 (reg 23) = Z_to_bv 64 2147450880). { rewrite (sKS 23%nat) by inl. rewrite (bKS 23%nat) by inl. rewrite (dKS 23%nat) by inl. rewrite (aKS 23%nat) by inl. exact h23. }
  assert (K25 : getr R4 (reg 25) = Z_to_bv 64 ((-1) * l - 1)). { rewrite (sKS 25%nat) by inl. rewrite (bKS 25%nat) by inl. rewrite (dKS 25%nat) by inl. rewrite (aKS 25%nat) by inl. exact h25. }
  assert (K26 : getr R4 (reg 26) = Z_to_bv 64 d). { rewrite (sKS 26%nat) by inl. rewrite (bKS 26%nat) by inl. rewrite (dKS 26%nat) by inl. rewrite (aKS 26%nat) by inl. exact h26. }
  destruct (Z.eq_dec (k - l) 1) as [KL1|KL1].
  - (* [comment removed for export] *)
    assert (KLR : 1 <= k - l <= 1) by (clear - KL1; lia).
    pose proof (v5GLcl_conc fx4 R4 M4 (fun j => match j with 2%nat => E | 58%nat => U R4 1 | 68%nat => Dq | 69%nat => n - l | 73%nat => k | 74%nat => l | 78%nat => q4 | 80%nat => k - l - 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx5 & R5 & M5 & MG5 & _ & cFZ & (cMS & cKS & _)).
    assert (LA5 : lagree M4 M5).
    { split. exact MG5. intros x Hx Hn. apply cFZ. exact Hx. intros X. apply Hn. unfold FP. right; right; right; right. clear - X Hk NL. lia. intros X. apply Hn. unfold FP. left. clear - X; lia. }
    exists fx5, R5, M5. split. { eapply lagree_trans. exact LA1. eapply lagree_trans. exact LA3. eapply lagree_trans. exact LA4. exact LA5. }
    left. split. exact KL1. split. { eapply msteps_trans. exact aMS. eapply msteps_trans. exact dMS. eapply msteps_trans. exact bMS. eapply msteps_trans. exact sMS. exact cMS. }
    unfold kept7, kept5. rewrite (cKS 2%nat), (cKS 8%nat), (cKS 9%nat), (cKS 3%nat), (cKS 4%nat), (cKS 18%nat), (cKS 23%nat) by inl. repeat split; assumption.
  - (* [comment removed for export] *)
    assert (KLR : 2 <= k - l <= 134217728) by (clear - KL1 Hk NL; lia).
    pose proof (v5GLcm_conc fx4 R4 M4 (fun j => match j with 2%nat => E | 58%nat => U R4 1 | 68%nat => Dq | 69%nat => n - l | 73%nat => k | 74%nat => l | 78%nat => q4 | 80%nat => k - l - 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx5 & R5 & M5 & MG5 & _ & cFZ & (cMS & cKS & _ & _ & _ & _ & _ & _ & c19 & _ & c24 & _)).
    assert (LA5 : lagree M4 M5).
    { split. exact MG5. intros x Hx Hn. apply cFZ. exact Hx. intros X. apply Hn. unfold FP. right; right; right; right. clear - X Hk NL. lia. intros X. apply Hn. unfold FP. left. clear - X; lia. }
    exists fx5, R5, M5. split. { eapply lagree_trans. exact LA1. eapply lagree_trans. exact LA3. eapply lagree_trans. exact LA4. exact LA5. }
    right. split. clear - KLR; lia. split. { eapply msteps_trans. exact aMS. eapply msteps_trans. exact dMS. eapply msteps_trans. exact bMS. eapply msteps_trans. exact sMS. exact cMS. }
    unfold hregs. rewrite (cKS 2%nat), (cKS 8%nat), (cKS 9%nat), (cKS 3%nat), (cKS 4%nat), (cKS 18%nat), (cKS 21%nat), (cKS 23%nat), (cKS 25%nat), (cKS 26%nat), (cKS 27%nat) by inl.
    split. exact K2. split. exact K8. split. exact K9. split. exact K3. split. exact K4. split. exact K18.
    split. { rewrite c19. reflexivity. } split. exact K21. split. exact K23.
    split. { rewrite c24. f_equal. clear; lia. } split. exact K25. split. exact K26. exact K27.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gloop_iter (j : nat) : forall (fx : FPState) R0 Rk Mk k, k = l + 1 + Z.of_nat j -> k <= n -> lctx Mk -> hregs R0 Rk k ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx Rk 0x93394 Mk) (st fx' R' 0x93458 M') /\ lagree Mk M' /\ kept7 R0 R'.
Proof.
  induction j as [|j IH]; intros fx R0 Rk Mk k Hk Hn C HR.
  - destruct (giter fx R0 Rk Mk k C HR ltac:(clear - Hk Hn; lia)) as (fx' & R' & M' & LA & [(E1 & MS & K5)|(E2 & _)]).
    + exists fx', R', M'. split. exact MS. split. exact LA. exact K5.
    + exfalso. clear - Hk E2. lia.
  - destruct (giter fx R0 Rk Mk k C HR ltac:(clear - Hk Hn; lia)) as (fx1 & R1 & M1 & LA & [(E1 & _)|(E2 & MS & HR')]).
    + exfalso. clear - Hk E1. lia.
    + destruct (IH fx1 R0 R1 M1 (k - 1) ltac:(clear - Hk; lia) ltac:(clear - Hn; lia) (lctx_keep Mk M1 C LA) HR') as (fx' & R' & M' & MS' & LA' & K5).
      exists fx', R', M'. split. eapply msteps_trans. exact MS. exact MS'. split. eapply lagree_trans. exact LA. exact LA'. exact K5.
Qed.

Definition eregs (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 SPA /\ getr R (reg 8) = Z_to_bv 64 E /\ getr R (reg 9) = Z_to_bv 64 SPA /\
  getr R (reg 19) = Z_to_bv 64 n /\ getr R (reg 23) = Z_to_bv 64 2147450880 /\ getr R (reg 27) = Z_to_bv 64 l.

Theorem gloop_run (fx : FPState) R M0 : lctx M0 -> eregs R ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R 0x93350 M0) (st fx' R' 0x93458 M') /\ lagree M0 M' /\ kept5 R R'
    /\ getr R' (reg 18) = getr R (reg 18) /\ getr R' (reg 23) = Z_to_bv 64 2147450880.
Proof.
  intros C (e2 & e8 & e9 & e19 & e23 & e27).
  pose proof C as [ER EA NL FW FD (IMG & S1 & S2) SDL STO VR VQ VD FZ TOR (RR1 & RR2 & RR8 & RNS & ROI) RW RD RZ (QR1 & QR2 & QR8 & QNS & QOI) QW QZ (DR1 & DR2 & DR8 & DNS) DD DZ (DV & DVR) (AP1 & AP2 & AP3 & AP4 & AP5 & AP6)].
  unfold nsh, oim in *.
  assert (ER' : 140735332487632 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - ER; lia). destruct ER' as [ER' ERG].
  assert (EAL : aligned E 32) by exact EA.
  pose proof (e32 EA) as (SP16 & QA8 & QAD & VRD & VQD & VDD & SPD).
  assert (SPB : 17591916560912 <= (E - 384) / 8 /\ (E - 384) / 8 + 48 <= 17592186044416) by (clear - SPD ER; lia).
  assert (FW400 : L5.writable RSEGS M0 (E - 400) 400). { eapply L5.writable_sub. exact FW. clear; lia. clear; lia. }
  assert (VZD : L5KA.zeros_at M0 ((E - 120) / 8 + 2147450880) 1). { rewrite VDD. eapply L5KA.zeros_at_sub. exact FZ. clear; lia. clear; lia. }
  pose proof (div8 Dd 0 DR8) as [_ DD8'].
  assert (DDB : 0 <= Dd / 8 /\ Dd / 8 <= 17592186043904) by (clear - DD8' DR1 DR2 NL; lia).
  assert (DDAL : aligned Dd 8) by exact DR8.
  assert (VR0 : 0 <= n <= 134217727 /\ 0 <= l <= 134217727 /\ 0 <= d <= 18446744073709551615 /\ 1 <= l + 1 <= 134217728 /\ 1 <= l + 1 - l <= 134217728 /\ 4096 <= Dd <= 140737488355328
               /\ 0 <= Dd < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= l < 2 ^ 64 /\ 0 <= d < 2 ^ 64 /\ 0 <= l + 1 < 2 ^ 64)
    by (clear - DR1 DR2 NL DVR; lia).
  destruct VR0 as (V3 & V4 & V5 & V6 & V7 & V8 & V1' & V3' & V4' & V5' & V6').
  assert (DF1 : Dd + 8 * (l + 1) <= Dd / 8 + 2147450880 \/ Dd / 8 + 2147450880 + (l + 1) <= Dd) by (clear - DD8' DDB DNS DR1 DR2 NL; lia).
  assert (DF2 : E - 400 + 400 <= Dd \/ Dd + 8 * (l + 1) <= E - 400) by (clear - AP6; lia).
  assert (DF3 : E - 400 + 400 <= Dd / 8 + 2147450880 \/ Dd / 8 + 2147450880 + (l + 1) <= E - 400) by (clear - DDB ER NL; lia).
  assert (DF4 : 4104 <= 8 * (l + 1) + Dd <= 140737479966720) by (clear - DR1 DR2 NL; lia).
  destruct (Z_le_gt_dec n l) as [NLE|NGT].
  - (* [comment removed for export] *)
    assert (REL : 0 <= l - n <= 134217728) by (clear - NLE NL; lia).
    pose proof (v5G9x_conc fx R M0 (fun j => match j with 2%nat => E | 58%nat => U R 1 | 64%nat => l + 1 | 65%nat => Dd | 73%nat => n | 74%nat => l | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & xFZ & (xMS & xKS & _)).
    exists fx1, R1, M1. split. exact xMS.
    split. { apply la_slot. exact MG1. exact xFZ. }
    split. { unfold kept5. rewrite (xKS 2%nat), (xKS 8%nat), (xKS 9%nat), (xKS 3%nat), (xKS 4%nat) by inl. repeat split; first [assumption | reflexivity]. }
    rewrite (xKS 18%nat), (xKS 23%nat) by inl. split. reflexivity. exact e23.
  - (* [comment removed for export] *)
    assert (REL : 1 <= n - l <= 134217728) by (clear - NGT NL; lia).
    pose proof (v5G9l_conc fx R M0 (fun j => match j with 2%nat => E | 58%nat => U R 1 | 64%nat => l + 1 | 65%nat => Dd | 73%nat => n | 74%nat => l | 75%nat => d | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & lFZ & (lMS & lKS & _ & _ & _ & _ & _ & _ & l21 & l24 & l25 & l26 & _)).
    pose proof (la_slot M0 M1 MG1 lFZ) as LA1.
    assert (HR1 : hregs R R1 n).
    { unfold hregs. rewrite (lKS 2%nat), (lKS 8%nat), (lKS 9%nat), (lKS 3%nat), (lKS 4%nat), (lKS 18%nat), (lKS 19%nat), (lKS 23%nat), (lKS 27%nat) by inl.
      split. exact e2. split. exact e8. split. exact e9. split. reflexivity. split. reflexivity. split. reflexivity. split. exact e19.
      split. exact l21. split. exact e23. split. { rewrite l24. f_equal. clear; lia. } split. exact l25. split. exact l26. exact e27. }
    destruct (gloop_iter (Z.to_nat (n - l - 1)) fx1 R R1 M1 n ltac:(rewrite Z2Nat.id by (clear - NGT; lia); clear; lia) ltac:(clear; lia) (lctx_keep M0 M1 C LA1) HR1)
      as (fx' & R' & M' & MS' & LA' & (K5 & K18 & K23)).
    exists fx', R', M'. split. eapply msteps_trans. exact lMS. exact MS'. split. eapply lagree_trans. exact LA1. exact LA'. split. exact K5. split; assumption.
Qed.
End LOOP.
End SCFG_1.
End L5ADVGL.
