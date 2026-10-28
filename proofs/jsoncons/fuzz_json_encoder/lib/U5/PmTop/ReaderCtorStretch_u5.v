(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_rctor_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module RCT.
Definition R_INIT : Z := 0x46cf0.      Definition R_LOC : Z := 0x46d2c.       Definition R_NEW : Z := 0x46c74.       Definition R_RSV : Z := 0x46ac4.
Definition R_VRSV : Z := 0x46af4.      Definition R_PUSH : Z := 0x46b04.      Definition RET : Z := 0x3ab54.
Definition RA_N : Z := 0x46c34.        Definition RA_S : Z := 0x4660c.        Definition RA_P : Z := 0x46634.        Definition RA_C : Z := 0x3aaf0.     (* [comment removed for export] *)
Definition OPT_VT : Z := 0xc4640.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition W : Z := 304.   Definition DC : Z := 352.   Definition DS : Z := 384.   Definition DN : Z := 416.   Definition DP : Z := 448.   Definition DEEP : Z := 480.
End RCT.

Module RCS.
Module G := Cut_rctor_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_rc : CL.is_ret_at RSEGS RCT.RET. Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Fixpoint cells64 (M : mem) (l : list (Z * Z)) : Prop := match l with [] => True | (a, v) :: r => L5.u64_at RSEGS M a v /\ cells64 M r end.
Lemma cells64_x : forall (K : Z -> Prop) (M M' : mem) l, TK.samem K M M' -> (forall av, In av l -> 0 <= fst av < 2 ^ 63 /\ forall i, fst av <= i < fst av + 8 -> K i) -> cells64 M l -> cells64 M' l.
Proof.
  intros K M M' l AG. induction l as [|[a v] r IH]; intros H C; [exact I|]. destruct C as [C1 C2]. split.
  - destruct (H (a, v) (or_introl eq_refl)) as [Q1 Q2]. cbn [fst] in Q1, Q2. exact (TK.u64_samem K M M' a v AG Q1 Q2 C1).
  - apply IH; [intros av Hav; apply H; right; exact Hav | exact C2].
Qed.
(* [comment removed for export] *)
Lemma cells64_win : forall (K : Z -> Prop) (M M' : mem) l lo hi, TK.samem K M M' -> 0 <= lo -> hi < 2 ^ 63 -> (forall i, lo <= i < hi -> K i) ->
  (forall av, In av l -> lo <= fst av /\ fst av + 8 <= hi) -> cells64 M l -> cells64 M' l.
Proof. intros K M M' l lo hi AG Hlo Hhi HK HW. apply (cells64_x K M M' l AG). intros av Hav. destruct (HW av Hav) as [Q1 Q2]. split; [lia | intros i Hi; apply HK; lia]. Qed.

(* [comment removed for export] *)
Definition u16_at (M : mem) (a z : Z) : Prop := rdn RSEGS M (Z_to_bv 64 a) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 z)).
Definition zeros (M : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Lemma kword16_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 2 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z -> u16_at M A z -> kentry_ok RSEGS E M (KWord a 2 v).
Proof.
  intros E M a v A z Ha H0 H4 Hv Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 2)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.
Lemma zeros_of_u64 : forall (M : mem) a, 0 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8 -> L5.u64_at RSEGS M a 0 -> zeros M a 8.
Proof.
  intros M a Ha Hn HD Hu i Hi.
  assert (L8 : length (word_to_le_bytes 8 (Z_to_bv 64 0)) = 8%nat) by (vm_compute; reflexivity).
  assert (HB : L5.bytes_at RSEGS M a (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 0)))).
  { apply L5C.rdn_bytes_at; [exact Ha | rewrite L8; cbn; lia | rewrite L8; exact Hu]. }
  pose proof (HB (Z.to_nat i) ltac:(rewrite length_map, L8; lia)) as H8.
  rewrite Z2Nat.id in H8 by lia.
  assert (NTH : forall k, (k < 8)%nat -> nth k (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 0))) 0 = 0).
  { intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
  rewrite (NTH (Z.to_nat i) ltac:(lia)) in H8. unfold L5.u8_at in H8. cbn [rdn] in H8.
  pose proof (HD i Hi) as HN. destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:EM; [|contradiction].
  injection H8 as Hb. rewrite Hb. reflexivity.
Qed.
Lemma zeros_app : forall (M : mem) a n m, 0 <= n -> 0 <= m -> zeros M a n -> zeros M (a + n) m -> zeros M a (n + m).
Proof.
  intros M a n m Hn Hm Z1 Z2 i Hi. destruct (Z.lt_ge_cases i n) as [Hl|Hg]; [apply Z1; lia|].
  replace (a + i) with (a + n + (i - n)) by lia. apply Z2. lia.
Qed.
Lemma zeros48_of_u64 : forall (M : mem) a, 0 <= a -> a + 48 <= 2 ^ 64 -> L5.defined M a 48 ->
  L5.u64_at RSEGS M a 0 -> L5.u64_at RSEGS M (a + 8) 0 -> L5.u64_at RSEGS M (a + 16) 0 -> L5.u64_at RSEGS M (a + 24) 0 ->
  L5.u64_at RSEGS M (a + 32) 0 -> L5.u64_at RSEGS M (a + 40) 0 -> zeros M a 48.
Proof.
  intros M a Ha Hn HD C0 C1 C2 C3 C4 C5.
  assert (D8 : forall j, 0 <= j -> j + 8 <= 48 -> L5.defined M (a + j) 8) by (intros j Hj Hj8 i Hi; replace (a + j + i) with (a + (j + i)) by lia; apply HD; lia).
  pose proof (zeros_of_u64 M a ltac:(lia) ltac:(lia) ltac:(replace a with (a + 0) at 1 by lia; apply D8; lia) C0) as Z0.
  pose proof (zeros_of_u64 M (a + 8) ltac:(lia) ltac:(lia) ltac:(apply D8; lia) C1) as Z1.
  pose proof (zeros_of_u64 M (a + 16) ltac:(lia) ltac:(lia) ltac:(apply D8; lia) C2) as Z2.
  pose proof (zeros_of_u64 M (a + 24) ltac:(lia) ltac:(lia) ltac:(apply D8; lia) C3) as Z3.
  pose proof (zeros_of_u64 M (a + 32) ltac:(lia) ltac:(lia) ltac:(apply D8; lia) C4) as Z4.
  pose proof (zeros_of_u64 M (a + 40) ltac:(lia) ltac:(lia) ltac:(apply D8; lia) C5) as Z5.
  replace 48 with (8 + (8 + (8 + (8 + (8 + 8))))) by lia.
  apply zeros_app; [lia | lia | exact Z0 |]. apply zeros_app; [lia | lia | exact Z1 |].
  replace (a + 8 + 8) with (a + 16) by lia. apply zeros_app; [lia | lia | exact Z2 |].
  replace (a + 16 + 8) with (a + 24) by lia. apply zeros_app; [lia | lia | exact Z3 |].
  replace (a + 24 + 8) with (a + 32) by lia. apply zeros_app; [lia | lia | exact Z4 |].
  replace (a + 32 + 8) with (a + 40) by lia. exact Z5.
Qed.
Lemma u16_of_u8s : forall (M : mem) a, 0 <= a -> a + 2 <= 2 ^ 64 -> L5.u8_at RSEGS M a 0 -> L5.u8_at RSEGS M (a + 1) 1 -> u16_at M a 256.
Proof.
  intros M a Ha Hn H0 H1. unfold u16_at.
  assert (HB : L5.bytes_at RSEGS M a [0; 1]).
  { intros i Hi. cbn [length] in Hi. destruct i as [|[|i]]; [rewrite Z.add_0_r; exact H0 | change (a + Z.of_nat 1) with (a + 1); exact H1 | lia]. }
  pose proof (L5C.bytes_at_rdn RSEGS M [0; 1] a Ha ltac:(cbn; lia) HB) as R. cbn [length map] in R. rewrite R. f_equal.
  vm_compute. repeat (first [reflexivity | apply bv_eq; vm_compute; reflexivity | f_equal]).
Qed.
Lemma kword16_elim : forall E (M : mem) a v A z, kentry_ok RSEGS E M (KWord a 2 v) -> estart E a = A -> bv_unsigned (edenot E v) = z -> u16_at M A z.
Proof. intros E M a v A z (_ & Hfl & Hr) Ha Hz. unfold u16_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr. rewrite <- Hz, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma u16_samem : forall (K : Z -> Prop) M M' a v, TK.samem K M M' -> 0 <= a < 2 ^ 63 -> (forall i, a <= i < a + 2 -> K i) -> u16_at M a v -> u16_at M' a v.
Proof. intros K M M' a v H Ha HK Hu. unfold u16_at in *. rewrite (TK.rdn_samem K M M' a 2 H) by (first [cbn; lia | intros i Hi; apply HK; cbn in Hi; lia]). exact Hu. Qed.
Lemma kzero_intro : forall E (M : mem) a n A N, estart E a = A -> elenZ E n = N -> 0 <= A -> A + N <= 2 ^ 64 -> A < 2 ^ 64 -> 0 <= N -> zeros M A N -> kentry_ok RSEGS E M (KZero a n).
Proof. intros E M a n A N Ha Hn H0 H1 H2 H3 Hz. cbn [kentry_ok]. rewrite Ha, Hn. split; [unfold flat; rewrite Ha; lia | exact Hz]. Qed.
Lemma kzero_elim : forall E (M : mem) a n A N, kentry_ok RSEGS E M (KZero a n) -> estart E a = A -> elenZ E n = N -> zeros M A N.
Proof. intros E M a n A N [_ Hz] <- <-. exact Hz. Qed.
Lemma zeros_samem : forall (K : Z -> Prop) M M' a n, TK.samem K M M' -> 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> K i) -> zeros M a n -> zeros M' a n.
Proof. intros K M M' a n H Ha Hn HK Hz i Hi. rewrite (H (a + i)) by (first [lia | apply HK; lia]). apply Hz. exact Hi. Qed.
Lemma zeros_sub : forall (M : mem) a n a' n', zeros M a n -> a <= a' -> a' + n' <= a + n -> zeros M a' n'.
Proof. intros M a n a' n' Hz H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Hz. lia. Qed.
Lemma zeros_u8 : forall (M : mem) a n i, zeros M a n -> 0 <= i < n -> L5.u8_at RSEGS M (a + i) 0.
Proof. intros M a n i Hz Hi. unfold L5.u8_at. cbn [rdn]. rewrite (Hz i Hi). reflexivity. Qed.
Lemma zeros_u64 : forall (M : mem) a n i, zeros M a n -> 0 <= i -> i + 8 <= n -> L5.u64_at RSEGS M (a + i) 0.
Proof.
  intros M a n i Hz H0 H8. set (A := a + i). assert (H : forall j, 0 <= j < 8 -> M (Z_to_bv 64 (A + j)) = Some (Z_to_bv 8 0)) by (intros j Hj; unfold A; replace (a + i + j) with (a + (i + j)) by lia; apply Hz; lia).
  unfold L5.u64_at. cbn [rdn]. rewrite !L5C.add1_lit.
  pose proof (H 0 ltac:(lia)) as X0. rewrite Z.add_0_r in X0.
  replace (A + 1 + 1) with (A + 2) by lia. replace (A + 2 + 1) with (A + 3) by lia. replace (A + 3 + 1) with (A + 4) by lia. replace (A + 4 + 1) with (A + 5) by lia.
  replace (A + 5 + 1) with (A + 6) by lia. replace (A + 6 + 1) with (A + 7) by lia.
  rewrite X0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)), (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Definition opts_at (M : mem) (O : Z) : Prop :=
  L5.u64_at RSEGS M O RCT.OPT_VT /\ L5.u32_at RSEGS M (O + 8) 0x10100 /\ L5.u64_at RSEGS M (O + 16) PML.VT_FUNC /\ L5.u64_at RSEGS M (O + 48) (O + 16) /\ u16_at M (O + 72) 0 /\
  zeros M (O + 80) 144 /\ L5.u32_at RSEGS M (O + 224) 1024.
Lemma opts_at_x : forall (K : Z -> Prop) (M M' : mem) O, TK.samem K M M' -> 0 <= O < 2 ^ 62 -> (forall i, O <= i < O + 232 -> K i) -> opts_at M O -> opts_at M' O.
Proof.
  intros K M M' O AG HO HK (C0 & C8 & C16 & C48 & C72 & CZ & C224). unfold opts_at.
  split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C0]|]. split; [apply (TK.u32_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C8]|].
  split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C16]|]. split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C48]|].
  split; [apply (u16_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C72]|]. split; [apply (zeros_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply HK; lia | exact CZ]|].
  apply (TK.u32_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C224].
Qed.

(* [comment removed for export] *)
Definition wframe (sp rav : Z) (R0 : bvmap 5 word) : list (Z * Z) :=
  [(sp - 8, rav); (sp - 16, bv_unsigned (getr R0 8%bv)); (sp - 24, bv_unsigned (getr R0 9%bv)); (sp - 32, bv_unsigned (getr R0 18%bv)); (sp - 40, bv_unsigned (getr R0 19%bv));
   (sp - 48, bv_unsigned (getr R0 20%bv)); (sp - 56, bv_unsigned (getr R0 21%bv)); (sp - 64, bv_unsigned (getr R0 22%bv))].
Definition cframe (sp c0 c1 c2 c3 : Z) : list (Z * Z) := [(sp - 312, RCT.RA_C); (sp - 320, c0); (sp - 328, c1); (sp - 336, c2); (sp - 344, c3)].
Definition sframe (sp R g : Z) : list (Z * Z) := [(sp - 360, RCT.RA_S); (sp - 368, R); (sp - 376, g); (sp - 384, sp - 304)].
Definition nframe (sp R : Z) : list (Z * Z) := [(sp - 392, RCT.RA_N); (sp - 400, R + 8); (sp - 408, R)].
Definition pframe (sp p0 p1 p2 p3 p5 p6 p7 : Z) : list (Z * Z) :=
  [(sp - 360, RCT.RA_P); (sp - 368, p0); (sp - 376, p1); (sp - 384, p2); (sp - 392, p3); (sp - 400, sp - 288); (sp - 408, p5); (sp - 416, p6); (sp - 424, p7)].
Definition same_s06 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\ getr R' 21%bv = getr R0 21%bv /\
  getr R' 22%bv = getr R0 22%bv.
(* [comment removed for export] *)
Definition KO7 : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.
Definition KO8 : list nat := [3; 4; 24; 25; 26; 27]%nat.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition KE1 (sp1 R : Z) (a : Z) : Prop := ~ (sp1 - 416 <= a < sp1) /\ ~ (R + 8 <= a < R + 24) /\ ~ (R + 88 <= a < R + 96) /\ ~ (R + 136 <= a < R + 144).

(* [comment removed for export] *)
Lemma s_rc_entry : forall (fx : FPState) R M model K sp1 Rr IS V rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 Rr -> getr R 11%bv = Z_to_bv 64 IS -> getr R 12%bv = Z_to_bv 64 V ->
  2 ^ 40 <= Rr <= 2 ^ 47 - 592 -> 0 <= IS < 2 ^ 64 -> 0 <= V < 2 ^ 64 -> PML.img_ro M -> L5.defined M (sp1 - 416) 416 -> L5.defined M Rr 592 -> sp1 <= Rr ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 416) -> getr R' 1%bv = Z_to_bv 64 RCT.R_INIT -> getr R' 10%bv = Z_to_bv 64 (Rr + 88) -> getr R' 11%bv = Z_to_bv 64 (Rr + 24) ->
      getr R' 8%bv = Z_to_bv 64 (Rr + 8) -> getr R' 18%bv = Z_to_bv 64 IS -> getr R' 19%bv = Z_to_bv 64 V -> getr R' 20%bv = Z_to_bv 64 (sp1 - 288) ->
      cells64 M' (wframe sp1 rav R) -> opts_at M' (sp1 - 304) -> cells64 M' (cframe sp1 (bv_unsigned (getr R 13%bv)) V IS Rr) -> cells64 M' (sframe sp1 Rr (bv_unsigned (getr R 13%bv))) ->
      cells64 M' (nframe sp1 Rr) -> TK.keepsR KO7 R R' -> TK.samem (KE1 sp1 Rr) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_IOSB_INIT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_READER_CTOR M model) K.
Proof.
  intros fx R M model K sp1 Rr IS V rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 H12 HR HIS HV RO DF DR J1 Kinit.
  change PML.PC_READER_CTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (12%bv : reg) H12. ck_reg E (1%bv : reg) H1.
    pose proof (bv_unsigned_in_range _ (getr R 13%bv)) as G13. change (bv_modulus 64) with (2 ^ 64) in G13.
    assert (U13 : bv_unsigned (ev E 45) = bv_unsigned (getr R 13%bv)) by (change 45%nat with (32 + ridx (13%bv : reg))%nat; subst E; rewrite CK.hvB_reg; reflexivity).
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE1 sp1 Rr) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kinit fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold RCT.R_INIT; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (18%bv : reg)
      | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | | | | | | ck_keeps HLF Hag64 KO7 | exact FRM | exact MG].
    + unfold wframe. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)
        | ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg) | ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg) | ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg) | ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg)
        | ck_saved HLF Hag64 (-64) 54%nat (22%bv : reg)].
    + unfold opts_at, RCT.OPT_VT, PML.VT_FUNC. repeat split.
      * ck_cell64 HLF (EVar 2) (-304) (ELit 804416). reflexivity.
      * replace (sp1 - 304 + 8) with (sp1 - 296) by lia. ck_cell32 HLF (EVar 2) (-296) (ELit 65792). reflexivity.
      * replace (sp1 - 304 + 16) with (sp1 - 288) by lia. ck_cell64 HLF (EVar 2) (-288) (ELit 804528). reflexivity.
      * replace (sp1 - 304 + 48) with (sp1 - 256) by lia. replace (sp1 - 304 + 16) with (sp1 - 288) by lia. ck_cell64 HLF (EVar 2) (-256) (EAlu ALU_ADD (EVar 2) (ELit (-288))). ck_vlin.
      * replace (sp1 - 304 + 72) with (sp1 - 232) by lia. eapply kword16_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EVar 2) (-232)) 2 (ELit 0)) HLF); vm_compute; reflexivity | ev_start | reflexivity].
      * replace (sp1 - 304 + 80) with (sp1 - 224) by lia. eapply kzero_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 2) (-224)) (ELit 144)) HLF); vm_compute; reflexivity | ev_start | reflexivity].
      * replace (sp1 - 304 + 224) with (sp1 - 80) by lia. ck_cell32 HLF (EVar 2) (-80) (ELit 1024). reflexivity.
    + unfold cframe, RCT.RA_C. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-312) (ELit 240368); reflexivity | ck_cell64 HLF (EVar 2) (-320) (EVar 45); ck_atom | ck_cell64 HLF (EVar 2) (-328) (EVar 44); ck_atom
        | ck_cell64 HLF (EVar 2) (-336) (EVar 43); ck_atom | ck_cell64 HLF (EVar 2) (-344) (EVar 42); ck_atom].
    + unfold sframe, RCT.RA_S. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-360) (ELit 288268); reflexivity | ck_cell64 HLF (EVar 2) (-368) (EVar 42); ck_atom | ck_cell64 HLF (EVar 2) (-376) (EVar 45); ck_atom
        | ck_cell64 HLF (EVar 2) (-384) (EAlu ALU_ADD (EVar 2) (ELit (-304))); ck_vlin].
    + unfold nframe, RCT.RA_N. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-392) (ELit 289844); reflexivity | ck_cell64 HLF (EVar 2) (-400) (EAlu ALU_ADD (EVar 42) (ELit 8)); ck_vlin
        | ck_cell64 HLF (EVar 2) (-408) (EVar 42); ck_atom].
Qed.

Definition KE2 (R : Z) (a : Z) : Prop := ~ (R + 224 <= a < R + 236) /\ ~ (R + 88 <= a < R + 96) /\ ~ (R + 8 <= a < R + 16) /\ ~ (R + 24 <= a < R + 32).

(* [comment removed for export] *)
Lemma s_rc_r_init : forall (fx : FPState) R M model K sp1 Rr,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 416) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 (Rr + 8) ->
  2 ^ 40 <= Rr <= 2 ^ 47 - 592 -> PML.img_ro M -> L5.defined M Rr 592 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 416) -> getr R' 1%bv = Z_to_bv 64 RCT.R_LOC -> getr R' 10%bv = Z_to_bv 64 (Rr + 32) ->
      TK.keepsR CK.CSR R R' -> TK.samem (KE2 Rr) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RCT.R_INIT M model) K.
Proof.
  intros fx R M model K sp1 Rr Hh Hl Hfp H2 [Hsp Hal] H8 HR RO DR Kloc.
  change RCT.R_INIT with (CC.cp_pc G.cp1).
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-416) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8.
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE2 Rr) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kloc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold RCT.R_LOC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact MG].
Qed.

Definition KE3 (R : Z) (a : Z) : Prop := ~ (R + 40 <= a < R + 88) /\ ~ (R + 24 <= a < R + 32) /\ ~ (R + 240 <= a < R + 296).
Definition KS3 : list nat := [3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition KC4 : list nat := [3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Lemma s_rc_r_loc : forall (fx : FPState) R M model K sp1 Rr IS rb,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 416) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 (Rr + 8) -> getr R 18%bv = Z_to_bv 64 IS ->
  2 ^ 40 <= Rr <= 2 ^ 47 - 592 -> 2 ^ 40 <= IS <= 2 ^ 47 - 272 -> 0 <= rb < 2 ^ 64 -> sp1 <= Rr -> (Rr + 592 <= IS \/ IS + 272 <= Rr) ->
  cells64 M (nframe sp1 Rr) -> PML.img_ro M -> L5.defined M Rr 592 -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u64_at RSEGS M (IS + 160) rb -> IS mod 8 = 0 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 384) -> getr R' 1%bv = Z_to_bv 64 RCT.R_NEW -> getr R' 10%bv = Z_to_bv 64 16384 -> getr R' 9%bv = Z_to_bv 64 Rr ->
      TK.keepsR KS3 R R' -> L5.u64_at RSEGS M' (Rr + 240) IS -> L5.u64_at RSEGS M' (Rr + 248) rb -> L5.u64_at RSEGS M' (Rr + 272) 16384 -> L5.u64_at RSEGS M' (Rr + 288) 0 ->
      TK.samem (KE3 Rr) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPNEW M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RCT.R_LOC M model) K.
Proof.
  intros fx R M model K sp1 Rr IS rb Hh Hl Hfp H2 [Hsp Hal] H8 H18 HR HIS Hrb J1 APT NF RO DR CI0 CI160 ISAL Knew.
  change RCT.R_LOC with (CC.cp_pc G.cp2). unfold nframe, RCT.RA_N in NF. cbn [cells64] in NF. destruct NF as (N1 & N2 & N3 & _). unfold PML.VT_ISS in CI0.
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (-416) [rb] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (18%bv : reg) H18. ck_gh E 0%nat rb.
    unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 392) 289844 N1. + ck_kw64 (sp1 - 400) (Rr + 8) N2. + ck_kw64 (sp1 - 408) Rr N3.
    + e_range. + e_range. + tk_kimg RO. + ck_kw64 IS 818632 CI0. + ck_kw64 (IS + 160) rb CI160.
    + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj. + e_disj. + e_align ISAL.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (18%bv : reg) H18. ck_gh E 0%nat rb.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE3 Rr) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Knew fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold RCT.R_NEW; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (9%bv : reg) | ck_keeps HLF Hag64 KS3 | | | | | exact FRM | exact MG].
    + replace (Rr + 240) with (Rr + 8 + 232) by lia. ck_cell64 HLF (EVar 40) 232 (EVar 50). ck_atom.
    + replace (Rr + 248) with (Rr + 8 + 240) by lia. ck_cell64 HLF (EVar 40) 240 (EVar 64). ck_atom.
    + replace (Rr + 272) with (Rr + 8 + 264) by lia. ck_cell64 HLF (EVar 40) 264 (ELit 16384). reflexivity.
    + replace (Rr + 288) with (Rr + 8 + 280) by lia. ck_cell64 HLF (EVar 40) 280 (ELit 0). reflexivity.
Qed.

(* [comment removed for export] *)
Definition pcells (M : mem) (P : Z) : Prop :=
  L5.u64_at RSEGS M P PML.VT_PARSER /\ L5.u32_at RSEGS M (P + 8) 1024 /\ L5.u8_at RSEGS M (P + 12) 0 /\ L5.u8_at RSEGS M (P + 13) 1 /\ u16_at M (P + 14) 256 /\
  L5.u8_at RSEGS M (P + 16) 0 /\ L5.u8_at RSEGS M (P + 17) 0 /\ L5.u8_at RSEGS M (P + 18) 0 /\ (forall j, 0 <= j < 9 -> L5.u64_at RSEGS M (P + 24 + 8 * j) 0) /\
  L5.u64_at RSEGS M (P + 96) PML.VT_FUNC /\ L5.u64_at RSEGS M (P + 128) (P + 96) /\ L5.u64_at RSEGS M (P + 144) 0 /\ zeros M (P + 168) 40 /\
  L5.u32_at RSEGS M (P + 208) 16777217 /\ u16_at M (P + 212) 0 /\ L5.u32_at RSEGS M (P + 216) 0 /\ zeros M (P + 224) 48.
Definition KE4 (sp1 R : Z) (a : Z) : Prop := ~ (sp1 - 480 <= a < sp1 - 352) /\ ~ (R + 264 <= a < R + 272) /\ ~ (R + 280 <= a < R + 288) /\ ~ (R + 296 <= a < R + 592).

(* [comment removed for export] *)
Lemma s_rc_r_new : forall (fx : FPState) R M model K sp1 Rr V ch g,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 384) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 ch -> getr R 9%bv = Z_to_bv 64 Rr ->
  getr R 19%bv = Z_to_bv 64 V -> getr R 20%bv = Z_to_bv 64 (sp1 - 288) -> 2 ^ 40 <= Rr <= 2 ^ 47 - 592 -> 0 <= V < 2 ^ 64 -> 0 <= ch < 2 ^ 64 -> 0 <= g < 2 ^ 64 -> sp1 <= Rr ->
  cells64 M (sframe sp1 Rr g) -> opts_at M (sp1 - 304) -> PML.img_ro M -> L5.defined M Rr 592 -> L5.defined M (sp1 - 480) 128 -> Rr mod 8 = 0 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 448) -> getr R' 1%bv = Z_to_bv 64 RCT.R_RSV -> getr R' 10%bv = Z_to_bv 64 (Rr + 544) -> getr R' 11%bv = Z_to_bv 64 256 ->
      getr R' 19%bv = Z_to_bv 64 (sp1 - 304) -> getr R' 23%bv = Z_to_bv 64 (Rr + 568) -> TK.keepsR KO8 R R' ->
      cells64 M' (pframe sp1 Rr g (sp1 - 304) V (bv_unsigned (getr R 21%bv)) (bv_unsigned (getr R 22%bv)) (bv_unsigned (getr R 23%bv))) ->
      L5.u64_at RSEGS M' (Rr + 264) ch -> L5.u64_at RSEGS M' (Rr + 280) ch -> L5.u8_at RSEGS M' (Rr + 296) 1 -> L5.u64_at RSEGS M' (Rr + 304) PML.VT_DEFVIS -> L5.u64_at RSEGS M' (Rr + 312) V ->
      pcells M' (Rr + 320) -> TK.samem (KE4 sp1 Rr) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_STR_RESERVE M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RCT.R_NEW M model) K.
Proof.
  intros fx R M model K sp1 Rr V ch g Hh Hl Hfp H2 [Hsp Hal] H10 H9 H19 H20 HR HV Hch Hg J1 SF (O0 & O8 & O16 & O48 & O72 & OZ & O224) RO DR DF RAL Krsv.
  change RCT.R_NEW with (CC.cp_pc G.cp3). unfold sframe, RCT.RA_S in SF. cbn [cells64] in SF. destruct SF as (S1 & S2 & S3 & S4 & _). unfold RCT.OPT_VT, PML.VT_FUNC in *.
  replace (sp1 - 304 + 8) with (sp1 - 296) in O8 by lia. replace (sp1 - 304 + 16) with (sp1 - 288) in * by lia. replace (sp1 - 304 + 48) with (sp1 - 256) in O48 by lia.
  replace (sp1 - 304 + 72) with (sp1 - 232) in O72 by lia. replace (sp1 - 304 + 80) with (sp1 - 224) in OZ by lia. replace (sp1 - 304 + 224) with (sp1 - 80) in O224 by lia.
  ck_open FPM G.cp3 (G.plans 3%nat _ eq_refl) (-384) [g] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (9%bv : reg) H9. ck_gh E 0%nat g.
    unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 360) 288268 S1. + ck_kw64 (sp1 - 368) Rr S2. + ck_kw64 (sp1 - 376) g S3. + ck_kw64 (sp1 - 384) (sp1 - 304) S4.
    + e_wr.
    + ck_kw64 (sp1 - 304) 804416 O0. + ck_kw32 (sp1 - 296) 65792 O8. + ck_kw64 (sp1 - 288) 804528 O16. + ck_kw64 (sp1 - 256) (sp1 - 288) O48.
    + eapply kword16_intro with (A := sp1 - 232) (z := 0); [ev_start | lia | lia | reflexivity | exact O72].
    + eapply kzero_intro with (A := sp1 - 224) (N := 144); [ev_start | reflexivity | lia | lia | lia | lia | exact OZ].
    + ck_kw32 (sp1 - 80) 1024 O224.
    + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj. + e_align RAL.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (9%bv : reg) H9. ck_reg E (10%bv : reg) H10. ck_reg E (19%bv : reg) H19. ck_reg E (20%bv : reg) H20. ck_gh E 0%nat g.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE4 sp1 Rr) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Krsv fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold RCT.R_RSV; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (23%bv : reg)
      | ck_keeps HLF Hag64 KO8 | | | | | | | | exact FRM | exact MG].
    + unfold pframe, RCT.RA_P. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-360) (ELit 288308); reflexivity | ck_cell64 HLF (EVar 2) (-368) (EVar 41); ck_atom | ck_cell64 HLF (EVar 2) (-376) (EVar 64); ck_atom
        | ck_cell64 HLF (EVar 2) (-384) (EAlu ALU_ADD (EVar 2) (ELit (-304))); ck_vlin | ck_cell64 HLF (EVar 2) (-392) (EVar 51); ck_atom | ck_cell64 HLF (EVar 2) (-400) (EVar 52); ck_atom
        | ck_saved HLF Hag64 (-408) 53%nat (21%bv : reg) | ck_saved HLF Hag64 (-416) 54%nat (22%bv : reg) | ck_saved HLF Hag64 (-424) 55%nat (23%bv : reg)].
    + ck_cell64 HLF (EVar 41) 264 (EVar 42). ck_atom.
    + ck_cell64 HLF (EVar 41) 280 (EVar 42). ck_atom.
    + ck_cell8 HLF (EVar 41) 296 (ELit 1). reflexivity.
    + unfold PML.VT_DEFVIS. ck_cell64 HLF (EVar 41) 304 (ELit 804824). reflexivity.
    + ck_cell64 HLF (EVar 41) 312 (EVar 51). ck_atom.
    + unfold pcells, PML.VT_PARSER, PML.VT_FUNC.
      split; [replace (Rr + 320) with (Rr + 320) by lia; ck_cell64 HLF (EVar 41) 320 (ELit 803024); reflexivity|].
      split; [replace (Rr + 320 + 8) with (Rr + 328) by lia; ck_cell32 HLF (EVar 41) 328 (ELit 1024); reflexivity|].
      split; [replace (Rr + 320 + 12) with (Rr + 332) by lia; ck_cell8 HLF (EVar 41) 332 (ELit 0); reflexivity|].
      split; [replace (Rr + 320 + 13) with (Rr + 333) by lia; ck_cell8 HLF (EVar 41) 333 (ELit 1); reflexivity|].
      split; [replace (Rr + 320 + 14) with (Rr + 334) by lia; apply u16_of_u8s; [lia | lia | ck_cell8 HLF (EVar 41) 334 (ELit 0); reflexivity | replace (Rr + 334 + 1) with (Rr + 335) by lia; ck_cell8 HLF (EVar 41) 335 (ELit 1); reflexivity]|].
      split; [replace (Rr + 320 + 16) with (Rr + 336) by lia; ck_cell8 HLF (EVar 41) 336 (ELit 0); reflexivity|].
      split; [replace (Rr + 320 + 17) with (Rr + 337) by lia; ck_cell8 HLF (EVar 41) 337 (ELit 0); reflexivity|].
      split; [replace (Rr + 320 + 18) with (Rr + 338) by lia; ck_cell8 HLF (EVar 41) 338 (ELit 0); reflexivity|].
      split.
      { intros j Hj. assert (JJ : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
        destruct JJ as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
        - replace (Rr + 320 + 24 + 8 * 0) with (Rr + 344) by lia. ck_cell64 HLF (EVar 41) 344 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 1) with (Rr + 352) by lia. ck_cell64 HLF (EVar 41) 352 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 2) with (Rr + 360) by lia. ck_cell64 HLF (EVar 41) 360 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 3) with (Rr + 368) by lia. ck_cell64 HLF (EVar 41) 368 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 4) with (Rr + 376) by lia. ck_cell64 HLF (EVar 41) 376 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 5) with (Rr + 384) by lia. ck_cell64 HLF (EVar 41) 384 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 6) with (Rr + 392) by lia. ck_cell64 HLF (EVar 41) 392 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 7) with (Rr + 400) by lia. ck_cell64 HLF (EVar 41) 400 (ELit 0). reflexivity.
        - replace (Rr + 320 + 24 + 8 * 8) with (Rr + 408) by lia. ck_cell64 HLF (EVar 41) 408 (ELit 0). reflexivity. }
      split; [replace (Rr + 320 + 96) with (Rr + 416) by lia; ck_cell64 HLF (EVar 41) 416 (ELit 804528); reflexivity|].
      split; [replace (Rr + 320 + 128) with (Rr + 448) by lia; replace (Rr + 320 + 96) with (Rr + 416) by lia; ck_cell64 HLF (EVar 41) 448 (EAlu ALU_ADD (EVar 41) (ELit 416)); ck_vlin|].
      split; [replace (Rr + 320 + 144) with (Rr + 464) by lia; ck_cell64 HLF (EVar 41) 464 (ELit 0); reflexivity|].
      split; [replace (Rr + 320 + 168) with (Rr + 488) by lia; eapply kzero_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 41) 488) (ELit 40)) HLF); vm_compute; reflexivity | ev_start | reflexivity]|].
      split; [replace (Rr + 320 + 208) with (Rr + 528) by lia; ck_cell32 HLF (EVar 41) 528 (ELit 16777217); reflexivity|].
      split; [replace (Rr + 320 + 212) with (Rr + 532) by lia; eapply kword16_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EVar 41) 532) 2 (ELit 0)) HLF); vm_compute; reflexivity | ev_start | reflexivity]|].
      split; [replace (Rr + 320 + 216) with (Rr + 536) by lia; ck_cell32 HLF (EVar 41) 536 (ELit 0); reflexivity|].
      replace (Rr + 320 + 224) with (Rr + 544) by lia. apply zeros48_of_u64; [lia | lia | apply (L5.defined_grows M M' (Rr + 544) 48 MG); intros i Hi; replace (Rr + 544 + i) with (Rr + (544 + i)) by lia; apply DR; lia | | | | | |].
      * ck_cell64 HLF (EVar 41) 544 (ELit 0). reflexivity.
      * replace (Rr + 544 + 8) with (Rr + 552) by lia. ck_cell64 HLF (EVar 41) 552 (ELit 0). reflexivity.
      * replace (Rr + 544 + 16) with (Rr + 560) by lia. ck_cell64 HLF (EVar 41) 560 (ELit 0). reflexivity.
      * replace (Rr + 544 + 24) with (Rr + 568) by lia. ck_cell64 HLF (EVar 41) 568 (ELit 0). reflexivity.
      * replace (Rr + 544 + 32) with (Rr + 576) by lia. ck_cell64 HLF (EVar 41) 576 (ELit 0). reflexivity.
      * replace (Rr + 544 + 40) with (Rr + 584) by lia. ck_cell64 HLF (EVar 41) 584 (ELit 0). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma s_rc_r_rsv : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 448) -> CK.spok sp1 -> 2 ^ 40 + 304 <= sp1 -> getr R 19%bv = Z_to_bv 64 (sp1 - 304) ->
  L5.u64_at RSEGS M (sp1 - 304) RCT.OPT_VT -> L5.u32_at RSEGS M (sp1 - 304 + 224) 1024 -> PML.img_ro M ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 448) -> getr R' 1%bv = Z_to_bv 64 RCT.R_VRSV -> getr R' 10%bv = getr R 23%bv -> getr R' 11%bv = Z_to_bv 64 66 ->
      TK.keepsR KC4 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_VEC_RESERVE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RCT.R_RSV M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] Hlo H20 O0 O224 RO Kv.
  change RCT.R_RSV with (CC.cp_pc G.cp4). unfold RCT.OPT_VT in O0.
  ck_open FPM G.cp4 (G.plans 4%nat _ eq_refl) (-448) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (19%bv : reg) H20.
    unfold know_ok, G.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + tk_kimg RO. + ck_kw64 (sp1 - 304) 804416 O0. + ck_kw32 (sp1 - 304 + 224) 1024 O224.
    + eapply CL5.kalign_intro; [lin_eval; rw_atoms; reflexivity | lia | lia | Z.div_mod_to_equations; lia].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (19%bv : reg) H20.
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kv fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | unfold RCT.R_VRSV; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (23%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 KC4].
Qed.

(* [comment removed for export] *)
Lemma s_rc_r_vrsv : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 448) -> CK.spok sp1 -> L5.defined M (sp1 - 433) 1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 448) -> getr R' 1%bv = Z_to_bv 64 RCT.R_PUSH -> getr R' 10%bv = getr R 23%bv -> getr R' 11%bv = Z_to_bv 64 (sp1 - 433) ->
      TK.keepsR CK.CSR R R' -> L5.u8_at RSEGS M' (sp1 - 433) 0 -> TK.samem (fun a => ~ (sp1 - 433 <= a < sp1 - 432)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_VEC_PUSH M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RCT.R_VRSV M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] DX Kp.
  change RCT.R_VRSV with (CC.cp_pc G.cp5).
  ck_open FPM G.cp5 (G.plans 5%nat _ eq_refl) (-448) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - unfold know_ok, G.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 433 <= a < sp1 - 432)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kp fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold RCT.R_PUSH; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (23%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 CK.CSR
      | | exact FRM | exact MG].
    ck_cell8 HLF (EVar 2) (-433) (ELit 0). reflexivity.
Qed.

Definition KE7 (sp1 : Z) (a : Z) : Prop := ~ (sp1 - 320 <= a < sp1 - 296) /\ ~ (sp1 - 240 <= a < sp1 - 232).

(* [comment removed for export] *)
Lemma s_rc_r_push : forall (fx : FPState) R M model K sp1 rav R0 p0 p1 p2 p3 p5 p6 p7 c0 c1 c2 c3,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 448) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= p0 < 2 ^ 64 -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> 0 <= p3 < 2 ^ 64 -> 0 <= p5 < 2 ^ 64 -> 0 <= p6 < 2 ^ 64 -> 0 <= p7 < 2 ^ 64 ->
  0 <= c0 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= c2 < 2 ^ 64 -> 0 <= c3 < 2 ^ 64 ->
  cells64 M (pframe sp1 p0 p1 p2 p3 p5 p6 p7) -> cells64 M (cframe sp1 c0 c1 c2 c3) -> cells64 M (wframe sp1 rav R0) ->
  L5.u64_at RSEGS M (sp1 - 288) PML.VT_FUNC -> L5.u64_at RSEGS M (sp1 - 256) (sp1 - 288) -> zeros M (sp1 - 224) 144 -> PML.img_ro M -> L5.defined M (sp1 - 320) 24 -> L5.defined M (sp1 - 240) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s06 R0 R' -> getr R' 23%bv = Z_to_bv 64 p7 -> TK.keepsR KO8 R R' -> TK.samem (KE7 sp1) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RCT.R_PUSH M model) K.
Proof.
  intros fx R M model K sp1 rav R0 p0 p1 p2 p3 p5 p6 p7 c0 c1 c2 c3 Hh Hl Hfp H2 [Hsp Hal] Hra Hp0 Hp1 Hp2 Hp3 Hp5 Hp6 Hp7 Hc0 Hc1 Hc2 Hc3 PF CF WF O16 O48 OZ RO D1 D2 Kret.
  change RCT.R_PUSH with (CC.cp_pc G.cp6). unfold PML.VT_FUNC in O16.
  unfold pframe, RCT.RA_P in PF. cbn [cells64] in PF. destruct PF as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _).
  unfold cframe, RCT.RA_C in CF. cbn [cells64] in CF. destruct CF as (C1 & C2 & C3 & C4 & C5 & _).
  unfold wframe in WF. cbn [cells64] in WF. destruct WF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  set (gl := [p0; p1; p2; p3; p5; p6; p7; c0; c1; c2; c3; rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv);
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv)]).
  ck_open FPM G.cp6 (G.plans 6%nat _ eq_refl) (-448) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat p0. ck_gh E 1%nat p1. ck_gh E 2%nat p2. ck_gh E 3%nat p3. ck_gh E 4%nat p5. ck_gh E 5%nat p6. ck_gh E 6%nat p7. ck_gh E 7%nat c0. ck_gh E 8%nat c1. ck_gh E 9%nat c2. ck_gh E 10%nat c3.
    ck_gh E 11%nat rav. ck_gh E 12%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 13%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 14%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 15%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 16%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 17%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 18%nat (bv_unsigned (getr R0 22%bv)).
    unfold know_ok, G.cp6. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 360) 288308 P1. + ck_kw64 (sp1 - 368) p0 P2. + ck_kw64 (sp1 - 376) p1 P3. + ck_kw64 (sp1 - 384) p2 P4. + ck_kw64 (sp1 - 392) p3 P5. + ck_kw64 (sp1 - 400) (sp1 - 288) P6.
    + ck_kw64 (sp1 - 408) p5 P7. + ck_kw64 (sp1 - 416) p6 P8. + ck_kw64 (sp1 - 424) p7 P9.
    + ck_kw64 (sp1 - 312) 240368 C1. + ck_kw64 (sp1 - 320) c0 C2. + ck_kw64 (sp1 - 328) c1 C3. + ck_kw64 (sp1 - 336) c2 C4. + ck_kw64 (sp1 - 344) c3 C5.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8.
    + e_wr. + ck_kw64 (sp1 - 288) 804528 O16. + ck_kw64 (sp1 - 256) (sp1 - 288) O48.
    + eapply kzero_intro with (A := sp1 - 224) (N := 144); [ev_start | reflexivity | lia | lia | lia | lia | exact OZ].
    + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 19)%nat) by (change 19%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp6) with 83%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE7 sp1) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 11%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_rc Hh Hl R1 Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | tk_reg HLF (23%bv : reg); exact (GH 6%nat _ eq_refl) | ck_keeps HLF Hag64 KO8 | exact FRM | exact MG].
    unfold same_s06. repeat split.
    + tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 12%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 13%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 14%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 15%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 16%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 17%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (22%bv : reg). etransitivity; [exact (GH 18%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
Qed.
End S.
End RCS.
