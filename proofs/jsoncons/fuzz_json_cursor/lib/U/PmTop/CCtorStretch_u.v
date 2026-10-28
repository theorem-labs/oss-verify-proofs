(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_cctor_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CCT.
Definition R_INIT : Z := 0x41820.      Definition R_LOC : Z := 0x4185c.       Definition R_NEW : Z := 0x417a4.       Definition R_RSV : Z := 0x41560.
Definition R_VRSV : Z := 0x41590.      Definition R_PUSH : Z := 0x415a0.      Definition R_SYSCAT : Z := 0x40f30.    Definition R_RN : Z := 0x40f44.
Definition R_SETEC2 : Z := 0x40f58.    Definition RET : Z := 0x39be8.
Definition RA_N : Z := 0x41764.        Definition RA_S : Z := 0x40ec8.        Definition RA_P : Z := 0x40ee4.        Definition RA_C : Z := 0x39b88.
Definition OPT_VT : Z := 0xbddb0.      Definition OPT_VT2 : Z := 0xbddd8.
End CCT.

Module CCS.
Module G := Cut_cctor_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_cc : CL.is_ret_at RSEGS CCT.RET. Proof. CL.solve_is_ret. Qed.

Fixpoint cells64 (M : mem) (l : list (Z * Z)) : Prop := match l with [] => True | (a, v) :: r => L5.u64_at RSEGS M a v /\ cells64 M r end.
Lemma cells64_x : forall (K : Z -> Prop) (M M' : mem) l, TK.samem K M M' -> (forall av, In av l -> 0 <= fst av < 2 ^ 63 /\ forall i, fst av <= i < fst av + 8 -> K i) -> cells64 M l -> cells64 M' l.
Proof.
  intros K M M' l AG. induction l as [|[a v] r IH]; intros H C; [exact I|]. destruct C as [C1 C2]. split.
  - destruct (H (a, v) (or_introl eq_refl)) as [Q1 Q2]. cbn [fst] in Q1, Q2. exact (TK.u64_samem K M M' a v AG Q1 Q2 C1).
  - apply IH; [intros av Hav; apply H; right; exact Hav | exact C2].
Qed.

Lemma cells64_win : forall (K : Z -> Prop) (M M' : mem) l lo hi, TK.samem K M M' -> 0 <= lo -> hi < 2 ^ 63 -> (forall i, lo <= i < hi -> K i) ->
  (forall av, In av l -> lo <= fst av /\ fst av + 8 <= hi) -> cells64 M l -> cells64 M' l.
Proof. intros K M M' l lo hi AG Hlo Hhi HK HW. apply (cells64_x K M M' l AG). intros av Hav. destruct (HW av Hav) as [Q1 Q2]. split; [lia | intros i Hi; apply HK; lia]. Qed.

Definition u16_at (M : mem) (a z : Z) : Prop := rdn RSEGS M (Z_to_bv 64 a) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 z)).
Definition zeros (M : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Lemma kword16_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 2 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z -> u16_at M A z -> kentry_ok RSEGS E M (KWord a 2 v).
Proof.
  intros E M a v A z Ha H0 H4 Hv Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 2)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
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
Lemma rdn_def_nth : forall (M : mem) (n : nat) a bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hr Hd i Hi; [lia|].
  cbn [rdn] in Hr. rewrite (L5C.add1_lit a) in Hr. pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (M (Z_to_bv 64 a)) as [b0|] eqn:EM; [|contradiction].
  destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:ER; [|discriminate]. injection Hr as <-.
  destruct i as [|i]; [cbn [nth Z.of_nat]; rewrite Z.add_0_r; exact EM|].
  cbn [nth]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest ER); [|lia].
  intros j Hj. replace (a + 1 + j) with (a + (1 + j)) by lia. apply Hd. lia.
Qed.
Lemma zeros8_of_u64 : forall (M : mem) a, L5.u64_at RSEGS M a 0 -> L5.defined M a 8 -> zeros M a 8.
Proof.
  intros M a Hu Hd i Hi. unfold L5.u64_at in Hu.
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (rdn_def_nth M 8 a _ Hu Hd (Z.to_nat i) ltac:(lia)). f_equal.
  assert (Hc : (Z.to_nat i < 8)%nat) by lia. revert Hc. generalize (Z.to_nat i). intros k Hk.
  do 8 (destruct k as [|k]; [apply bv_eq; reflexivity|]). lia.
Qed.
Lemma zeros48_of_u64 : forall (M : mem) a, L5.defined M a 48 ->
  L5.u64_at RSEGS M a 0 -> L5.u64_at RSEGS M (a + 8) 0 -> L5.u64_at RSEGS M (a + 16) 0 -> L5.u64_at RSEGS M (a + 24) 0 ->
  L5.u64_at RSEGS M (a + 32) 0 -> L5.u64_at RSEGS M (a + 40) 0 -> zeros M a 48.
Proof.
  intros M a D Z0 Z1 Z2 Z3 Z4 Z5 i Hi.
  assert (Q : forall k, 0 <= k -> k + 8 <= 48 -> L5.u64_at RSEGS M (a + k) 0 -> forall j, 0 <= j < 8 -> M (Z_to_bv 64 (a + k + j)) = Some (Z_to_bv 8 0)).
  { intros k Hk0 Hk1 Hu j Hj. apply (zeros8_of_u64 M (a + k) Hu); [|exact Hj]. intros t Ht. replace (a + k + t) with (a + (k + t)) by lia. apply D. lia. }
  rewrite <- (Z.add_0_r a) in Z0.
  assert (C6 : 0 <= i < 8 \/ 8 <= i < 16 \/ 16 <= i < 24 \/ 24 <= i < 32 \/ 32 <= i < 40 \/ 40 <= i < 48) by lia.
  destruct C6 as [X|[X|[X|[X|[X|X]]]]];
    [ replace (a + i) with (a + 0 + (i - 0)) by lia; apply (Q 0); [lia | lia | exact Z0 | lia]
    | replace (a + i) with (a + 8 + (i - 8)) by lia; apply (Q 8); [lia | lia | exact Z1 | lia]
    | replace (a + i) with (a + 16 + (i - 16)) by lia; apply (Q 16); [lia | lia | exact Z2 | lia]
    | replace (a + i) with (a + 24 + (i - 24)) by lia; apply (Q 24); [lia | lia | exact Z3 | lia]
    | replace (a + i) with (a + 32 + (i - 32)) by lia; apply (Q 32); [lia | lia | exact Z4 | lia]
    | replace (a + i) with (a + 40 + (i - 40)) by lia; apply (Q 40); [lia | lia | exact Z5 | lia] ].
Qed.
Lemma u16_of_u8s : forall (M : mem) a, L5.u8_at RSEGS M a 0 -> L5.u8_at RSEGS M (a + 1) 1 -> u16_at M a 256.
Proof.
  intros M a H0 H1. unfold u16_at, L5.u8_at in *. cbn [rdn] in *. rewrite L5C.add1_lit.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|]; [|discriminate H0].
  destruct (match M (Z_to_bv 64 (a + 1)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + 1)) end) as [b1|]; [|discriminate H1].
  cbv beta iota in H0, H1 |- *. injection H0 as E0. injection H1 as E1. subst b0 b1.
  f_equal. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity.
Qed.

Definition opts_at (M : mem) (O : Z) : Prop :=
  L5.u64_at RSEGS M O CCT.OPT_VT /\ L5.u32_at RSEGS M (O + 8) 0x10100 /\ L5.u64_at RSEGS M (O + 16) PML.VT_FUNC /\ L5.u64_at RSEGS M (O + 48) (O + 16) /\ u16_at M (O + 72) 0 /\
  zeros M (O + 80) 144 /\ L5.u32_at RSEGS M (O + 224) 1024.
Lemma opts_at_x : forall (K : Z -> Prop) (M M' : mem) O, TK.samem K M M' -> 0 <= O < 2 ^ 62 -> (forall i, O <= i < O + 232 -> K i) -> opts_at M O -> opts_at M' O.
Proof.
  intros K M M' O AG HO HK (C0 & C8 & C16 & C48 & C72 & CZ & C224). unfold opts_at.
  split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C0]|]. split; [apply (TK.u32_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C8]|].
  split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C16]|]. split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C48]|].
  split; [apply (u16_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C72]|]. split; [apply (zeros_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply HK; lia | exact CZ]|].
  apply (TK.u32_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C224].
Qed.

Definition wframe (sp rav : Z) (R0 : bvmap 5 word) : list (Z * Z) :=
  [(sp - 8, rav); (sp - 16, bv_unsigned (getr R0 8%bv)); (sp - 24, bv_unsigned (getr R0 9%bv)); (sp - 32, bv_unsigned (getr R0 18%bv)); (sp - 40, bv_unsigned (getr R0 19%bv));
   (sp - 48, bv_unsigned (getr R0 20%bv)); (sp - 56, bv_unsigned (getr R0 21%bv))].

Definition cframe (sp C IS E s6 : Z) : list (Z * Z) :=
  [(sp - 312, CCT.RA_C); (sp - 320, E); (sp - 328, IS); (sp - 336, C); (sp - 344, sp - 288); (sp - 352, CCT.OPT_VT); (sp - 360, CCT.OPT_VT2); (sp - 368, s6)].
Definition sframe (sp C g : Z) : list (Z * Z) := [(sp - 408, CCT.RA_S); (sp - 416, g); (sp - 424, C); (sp - 432, C + 8)].
Definition nframe (sp C : Z) : list (Z * Z) := [(sp - 440, CCT.RA_N); (sp - 448, C + 16); (sp - 456, C + 8)].
Definition pframe (sp C p0 p6 p7 : Z) : list (Z * Z) :=
  [(sp - 408, CCT.RA_P); (sp - 416, p0); (sp - 424, C); (sp - 432, C + 8); (sp - 440, C + 320); (sp - 448, sp - 304); (sp - 456, p6); (sp - 464, 1); (sp - 472, p7)].
Definition same_s05 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\
  getr R' 21%bv = getr R0 21%bv.

Definition KO7 : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.
Definition KO8 : list nat := [3; 4; 24; 25; 26; 27]%nat.
Definition KO4 : list nat := [3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition hv_slot_s (off : Z) (spins : list (nat * Z)) (q : nat) : expr :=
  if Nat.eqb q 2 then (if Z.eqb off 0 then EVar 2 else EAlu ALU_ADD (EVar 2) (ELit off))
  else match List.find (fun p => Nat.eqb (fst p) q) spins with Some p => EAlu ALU_ADD (EVar 2) (ELit (snd p)) | None => EVar (32 + q) end.
Definition hv_shape_s (sr : list expr) (off : Z) (spins : list (nat * Z)) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (hv_slot_s off spins q)) (seq 1 31).
Lemma regs_ok_hvB_s : forall sr off spins sp0 R gl bl,
  hv_shape_s sr off spins = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) spins -> 0 <= sp0 + z < 2 ^ 64 /\ getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 (sp0 + z)) ->
  regs_ok (CK.hvB sp0 R gl bl) sr R.
Proof.
  intros sr off spins sp0 R gl bl Hsh Hsp Hspo H2 Hpins. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold hv_shape_s in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold hv_slot_s. destruct (Nat.eqb (ridx r) 2) eqn:E2.
  - apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
    destruct (Z.eqb_spec off 0) as [->|Hne].
    + cbn [edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
    + cbn [edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
  - destruct (find (fun p => Nat.eqb (fst p) (ridx r)) spins) as [[q z]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb].
      destruct (Hpins _ _ Hin) as (Hz & Hr). rewrite TK.add_lit by lia. rewrite <- Hr, ridx_roundtrip. reflexivity.
    + cbn [edenot]. symmetry. apply CK.hvB_reg.
Qed.

Lemma u64_u32_lo : forall (M : mem) a v c, 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 32 -> L5.u64_at RSEGS M a v -> L5.u32_at RSEGS M a c -> v mod 2 ^ 32 = c.
Proof.
  intros M a v c Hv Hc H8 H4. unfold L5.u64_at, L5.u32_at in *.
  pose proof (SeqExec.rdn_firstn RSEGS M 8 (Z_to_bv 64 a) _ 4 H8 ltac:(lia)) as X0. rewrite H4 in X0.
  assert (X : word_to_le_bytes 4 (Z_to_bv 64 c) = firstn 4 (word_to_le_bytes 8 (Z_to_bv 64 v))) by congruence. clear X0.
  unfold word_to_le_bytes in X. rewrite !u64_of_Z in X by lia.
  change (firstn 4 (Z_to_le_bytes 8 v)) with (Z_to_le_bytes 4 v) in X.
  apply (f_equal bytes_le_to_Z) in X. rewrite !bytes_le_to_Z_of_le_bytes in X by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X.
  rewrite (Z.mod_small c) in X by lia. lia.
Qed.
Lemma u32_of_u64 : forall (M : mem) a v, 0 <= v < 2 ^ 64 -> L5.u64_at RSEGS M a v -> L5.u32_at RSEGS M a (v mod 2 ^ 32).
Proof.
  intros M a v Hv H8. unfold L5.u64_at, L5.u32_at in *.
  rewrite (SeqExec.rdn_firstn RSEGS M 8 (Z_to_bv 64 a) _ 4 H8 ltac:(lia)). f_equal.
  unfold word_to_le_bytes. rewrite !u64_of_Z by (pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)); lia).
  change (firstn 4 (Z_to_le_bytes 8 v)) with (Z_to_le_bytes 4 v).
  pose proof (APSX.Z_to_le_bytes_of_bytes (Z_to_le_bytes 4 v)) as X. rewrite length_Z_to_le_bytes in X. rewrite bytes_le_to_Z_of_le_bytes in X by lia.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X. symmetry. exact X.
Qed.
Lemma ext_s32_mod : forall x c, 0 <= x < 2 ^ 64 -> x mod 2 ^ 32 = c -> 0 <= c < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 x) = Z_to_bv 64 c.
Proof.
  intros x c Hx Hm Hc. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite Z.div_1_r, Hm. f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31). change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac ck_open_s FPM cp plans off gl bl spn sp0 R M fx model K Hh Hl Hfp H2 Hpins :=
  let E := fresh "E" in set (E := CK.hvB sp0 R gl bl);
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply CK.hvB_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (regs_ok_hvB_s _ off spn); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins] | | ].
Lemma al8_lin : forall a v k, a mod 8 = 0 -> v = a + k * 8 -> v mod 8 = 0.
Proof. intros a v k Ha ->. rewrite Z.mod_add by lia. exact Ha. Qed.
Lemma al16_8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a H. pose proof (Z.div_mod a 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (16 * (a / 16)) with (0 + (2 * (a / 16)) * 8) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
Ltac e_al8 H k := eapply CL5.kalign_intro; [lin_eval; rw_atoms; reflexivity | lia | lia | rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l; apply (al8_lin _ _ k H); lia].

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition KE1 (sp1 C : Z) (a : Z) : Prop :=
  ~ (sp1 - 512 <= a < sp1) /\ ~ (C <= a < C + 8) /\ ~ (C + 648 <= a < C + 656) /\ ~ (C + 16 <= a < C + 32) /\ ~ (C + 96 <= a < C + 104) /\ ~ (C + 144 <= a < C + 152).

Lemma s_cc_entry : forall (fx : FPState) R M model K sp1 C IS E rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 C -> getr R 11%bv = Z_to_bv 64 IS -> getr R 12%bv = Z_to_bv 64 E ->
  2 ^ 40 <= C <= 2 ^ 47 - 656 -> 0 <= IS < 2 ^ 64 -> 0 <= E < 2 ^ 64 -> PML.img_ro M -> L5.defined M (sp1 - 512) 512 -> L5.defined M C 656 -> sp1 <= C ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 464) -> getr R' 1%bv = Z_to_bv 64 CCT.R_INIT -> getr R' 10%bv = Z_to_bv 64 (C + 96) ->
      getr R' 11%bv = Z_to_bv 64 (C + 32) -> getr R' 8%bv = Z_to_bv 64 (C + 16) -> getr R' 18%bv = Z_to_bv 64 IS -> getr R' 19%bv = Z_to_bv 64 (sp1 - 288) -> getr R' 20%bv = Z_to_bv 64 (sp1 - 304) ->
      cells64 M' (wframe sp1 rav R) -> opts_at M' (sp1 - 304) -> cells64 M' (cframe sp1 C IS E (bv_unsigned (getr R 22%bv))) -> cells64 M' (sframe sp1 C E) ->
      cells64 M' (nframe sp1 C) -> L5.u64_at RSEGS M' C PMCS.VT_CURSOR -> L5.u64_at RSEGS M' (C + 648) PMCS.VT_CURSOR_SER ->
      TK.keepsR KO7 R R' -> TK.samem (KE1 sp1 C) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_IOSB_INIT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_CURSOR_CTOR M model) K.
Proof.
  intros fx R M model K sp1 C IS E rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 H12 HC HIS HE RO DF DC J1 Kinit.
  change PMCS.PC_CURSOR_CTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E0 (10%bv : reg) H10.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (10%bv : reg) H10. ck_reg E0 (11%bv : reg) H11. ck_reg E0 (12%bv : reg) H12. ck_reg E0 (1%bv : reg) H1.
    pose proof (bv_unsigned_in_range _ (getr R 22%bv)) as G22. change (bv_modulus 64) with (2 ^ 64) in G22.
    assert (U22 : bv_unsigned (ev E0 54) = bv_unsigned (getr R 22%bv)) by (change 54%nat with (32 + ridx (22%bv : reg))%nat; subst E0; rewrite CK.hvB_reg; reflexivity).
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE1 sp1 C) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4 & Hk5 & Hk6); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kinit fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_INIT; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (18%bv : reg)
      | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | | | | | | | | ck_keeps HLF Hag64 KO7 | exact FRM | exact MG].
    + unfold wframe. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg)
        | ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg) | ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg) | ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg) | ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg)].
    + unfold opts_at, CCT.OPT_VT, PML.VT_FUNC. repeat split.
      * ck_cell64 HLF (EVar 2) (-304) (ELit 777648). reflexivity.
      * replace (sp1 - 304 + 8) with (sp1 - 296) by lia. ck_cell32 HLF (EVar 2) (-296) (ELit 65792). reflexivity.
      * replace (sp1 - 304 + 16) with (sp1 - 288) by lia. ck_cell64 HLF (EVar 2) (-288) (ELit 777808). reflexivity.
      * replace (sp1 - 304 + 48) with (sp1 - 256) by lia. replace (sp1 - 304 + 16) with (sp1 - 288) by lia. ck_cell64 HLF (EVar 2) (-256) (EAlu ALU_ADD (EVar 2) (ELit (-288))). ck_vlin.
      * replace (sp1 - 304 + 72) with (sp1 - 232) by lia. eapply kword16_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EVar 2) (-232)) 2 (ELit 0)) HLF); vm_compute; reflexivity | ev_start | reflexivity].
      * replace (sp1 - 304 + 80) with (sp1 - 224) by lia. eapply kzero_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 2) (-224)) (ELit 144)) HLF); vm_compute; reflexivity | ev_start | reflexivity].
      * replace (sp1 - 304 + 224) with (sp1 - 80) by lia. ck_cell32 HLF (EVar 2) (-80) (ELit 1024). reflexivity.
    + unfold cframe, CCT.RA_C, CCT.OPT_VT, CCT.OPT_VT2. cbn [cells64]. repeat split;
        [ck_cell64 HLF (EVar 2) (-312) (ELit 236424); reflexivity | ck_cell64 HLF (EVar 2) (-320) (EVar 44); ck_atom | ck_cell64 HLF (EVar 2) (-328) (EVar 43); ck_atom
        | ck_cell64 HLF (EVar 2) (-336) (EVar 42); ck_atom | ck_cell64 HLF (EVar 2) (-344) (EAlu ALU_ADD (EVar 2) (ELit (-288))); ck_vlin
        | ck_cell64 HLF (EVar 2) (-352) (ELit 777648); reflexivity | ck_cell64 HLF (EVar 2) (-360) (ELit 777688); reflexivity | ck_cell64 HLF (EVar 2) (-368) (EVar 54); ck_atom].
    + unfold sframe, CCT.RA_S. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-408) (ELit 265928); reflexivity | ck_cell64 HLF (EVar 2) (-416) (EVar 44); ck_atom
        | ck_cell64 HLF (EVar 2) (-424) (EVar 42); ck_atom | ck_cell64 HLF (EVar 2) (-432) (EAlu ALU_ADD (EVar 42) (ELit 8)); ck_vlin].
    + unfold nframe, CCT.RA_N. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-440) (ELit 268132); reflexivity | ck_cell64 HLF (EVar 2) (-448) (EAlu ALU_ADD (EVar 42) (ELit 16)); ck_vlin
        | ck_cell64 HLF (EVar 2) (-456) (EAlu ALU_ADD (EVar 42) (ELit 8)); ck_vlin].
    + unfold PMCS.VT_CURSOR. replace C with (C + 0) by lia. ck_cell64 HLF (EVar 42) 0 (ELit 776480). reflexivity.
    + unfold PMCS.VT_CURSOR_SER. ck_cell64 HLF (EVar 42) 648 (ELit 776696). reflexivity.
Qed.

Definition KE2 (C : Z) (a : Z) : Prop := ~ (C + 232 <= a < C + 244) /\ ~ (C + 96 <= a < C + 104) /\ ~ (C + 16 <= a < C + 24) /\ ~ (C + 32 <= a < C + 40).

Lemma s_r_init : forall (fx : FPState) R M model K sp1 C,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 464) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 (C + 16) ->
  2 ^ 40 <= C <= 2 ^ 47 - 656 -> PML.img_ro M -> L5.defined M C 656 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 464) -> getr R' 1%bv = Z_to_bv 64 CCT.R_LOC -> getr R' 10%bv = Z_to_bv 64 (C + 40) ->
      TK.keepsR CK.CSR R R' -> TK.samem (KE2 C) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_INIT M model) K.
Proof.
  intros fx R M model K sp1 C Hh Hl Hfp H2 [Hsp Hal] H8 HC RO DC Kloc.
  change CCT.R_INIT with (CC.cp_pc G.cp1).
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-464) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8.
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE2 C) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kloc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_LOC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact MG].
Qed.

Definition KE3 (C : Z) (a : Z) : Prop := ~ (C + 48 <= a < C + 96) /\ ~ (C + 32 <= a < C + 40) /\ ~ (C + 248 <= a < C + 304).
Definition KS3 : list nat := [3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma s_r_loc : forall (fx : FPState) R M model K sp1 C IS rb,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 464) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 (C + 16) -> getr R 18%bv = Z_to_bv 64 IS ->
  2 ^ 40 <= C <= 2 ^ 47 - 656 -> 2 ^ 40 <= IS <= 2 ^ 47 - 272 -> IS mod 8 = 0 -> 0 <= rb < 2 ^ 64 -> sp1 <= C -> (C + 656 <= IS \/ IS + 272 <= C) ->
  cells64 M (nframe sp1 C) -> PML.img_ro M -> L5.defined M C 656 -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u64_at RSEGS M (IS + 160) rb ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 432) -> getr R' 1%bv = Z_to_bv 64 CCT.R_NEW -> getr R' 10%bv = Z_to_bv 64 16384 -> getr R' 9%bv = Z_to_bv 64 (C + 8) ->
      TK.keepsR KS3 R R' -> L5.u64_at RSEGS M' (C + 248) IS -> L5.u64_at RSEGS M' (C + 256) rb -> L5.u64_at RSEGS M' (C + 280) 16384 -> L5.u64_at RSEGS M' (C + 296) 0 ->
      TK.samem (KE3 C) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPNEW M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_LOC M model) K.
Proof.
  intros fx R M model K sp1 C IS rb Hh Hl Hfp H2 [Hsp Hal] H8 H18 HC HIS HISa Hrb J1 APT NF RO DC CI0 CI160 Knew.
  change CCT.R_LOC with (CC.cp_pc G.cp2). unfold nframe, CCT.RA_N in NF. cbn [cells64] in NF. destruct NF as (N1 & N2 & N3 & _). unfold PML.VT_ISS in CI0.
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (-464) [rb] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (18%bv : reg) H18. ck_gh E 0%nat rb.
    unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 440) 268132 N1. + ck_kw64 (sp1 - 448) (C + 16) N2. + ck_kw64 (sp1 - 456) (C + 8) N3.
    + e_range. + e_range. + tk_kimg RO. + ck_kw64 IS 792064 CI0. + ck_kw64 (IS + 160) rb CI160.
    + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj. + e_disj. + e_al8 HISa 0.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (18%bv : reg) H18. ck_gh E 0%nat rb.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE3 C) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Knew fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_NEW; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (9%bv : reg) | ck_keeps HLF Hag64 KS3 | | | | | exact FRM | exact MG].
    + replace (C + 248) with (C + 16 + 232) by lia. ck_cell64 HLF (EVar 40) 232 (EVar 50). ck_atom.
    + replace (C + 256) with (C + 16 + 240) by lia. ck_cell64 HLF (EVar 40) 240 (EVar 64). ck_atom.
    + replace (C + 280) with (C + 16 + 264) by lia. ck_cell64 HLF (EVar 40) 264 (ELit 16384). reflexivity.
    + replace (C + 296) with (C + 16 + 280) by lia. ck_cell64 HLF (EVar 40) 280 (ELit 0). reflexivity.
Qed.

Definition pcells (M : mem) (P : Z) : Prop :=
  L5.u64_at RSEGS M P PML.VT_PARSER /\ L5.u32_at RSEGS M (P + 8) 1024 /\ L5.u8_at RSEGS M (P + 12) 0 /\ L5.u8_at RSEGS M (P + 13) 1 /\ u16_at M (P + 14) 256 /\
  L5.u8_at RSEGS M (P + 16) 0 /\ L5.u8_at RSEGS M (P + 17) 0 /\ L5.u8_at RSEGS M (P + 18) 0 /\ (forall j, 0 <= j < 9 -> L5.u64_at RSEGS M (P + 24 + 8 * j) 0) /\
  L5.u64_at RSEGS M (P + 96) PML.VT_FUNC /\ L5.u64_at RSEGS M (P + 128) (P + 96) /\ L5.u64_at RSEGS M (P + 144) 0 /\ zeros M (P + 168) 40 /\
  L5.u32_at RSEGS M (P + 208) 16777217 /\ u16_at M (P + 212) 0 /\ L5.u32_at RSEGS M (P + 216) 0 /\ zeros M (P + 224) 48.
Definition KE4 (sp1 C : Z) (a : Z) : Prop :=
  ~ (sp1 - 528 <= a < sp1 - 400) /\ ~ (C + 272 <= a < C + 280) /\ ~ (C + 288 <= a < C + 296) /\ ~ (C + 304 <= a < C + 305) /\ ~ (C + 320 <= a < C + 592).

Lemma s_r_new : forall (fx : FPState) R M model K sp1 C ch g,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 432) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 ch -> getr R 9%bv = Z_to_bv 64 (C + 8) ->
  getr R 20%bv = Z_to_bv 64 (sp1 - 304) -> 2 ^ 40 <= C <= 2 ^ 47 - 656 -> C mod 8 = 0 -> 0 <= ch < 2 ^ 64 -> 0 <= g < 2 ^ 64 -> sp1 <= C ->
  cells64 M (sframe sp1 C g) -> opts_at M (sp1 - 304) -> PML.img_ro M -> L5.defined M C 656 -> L5.defined M (sp1 - 528) 128 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 496) -> getr R' 1%bv = Z_to_bv 64 CCT.R_RSV -> getr R' 10%bv = Z_to_bv 64 (C + 544) -> getr R' 11%bv = Z_to_bv 64 256 ->
      getr R' 19%bv = Z_to_bv 64 (sp1 - 304) -> getr R' 23%bv = Z_to_bv 64 (C + 568) -> TK.keepsR KO8 R R' ->
      cells64 M' (pframe sp1 C g (bv_unsigned (getr R 21%bv)) (bv_unsigned (getr R 23%bv))) ->
      L5.u64_at RSEGS M' (C + 272) ch -> L5.u64_at RSEGS M' (C + 288) ch -> L5.u8_at RSEGS M' (C + 304) 1 ->
      pcells M' (C + 320) -> TK.samem (KE4 sp1 C) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_STR_RESERVE M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_NEW M model) K.
Proof.
  intros fx R M model K sp1 C ch g Hh Hl Hfp H2 [Hsp Hal] H10 H9 H20 HC HCa Hch Hg J1 SF (O0 & O8 & O16 & O48 & O72 & OZ & O224) RO DC DF Krsv.
  change CCT.R_NEW with (CC.cp_pc G.cp3). unfold sframe, CCT.RA_S in SF. cbn [cells64] in SF. destruct SF as (S1 & S2 & S3 & S4 & _). unfold CCT.OPT_VT, PML.VT_FUNC in *.
  replace (sp1 - 304 + 8) with (sp1 - 296) in O8 by lia. replace (sp1 - 304 + 16) with (sp1 - 288) in * by lia. replace (sp1 - 304 + 48) with (sp1 - 256) in O48 by lia.
  replace (sp1 - 304 + 72) with (sp1 - 232) in O72 by lia. replace (sp1 - 304 + 80) with (sp1 - 224) in OZ by lia. replace (sp1 - 304 + 224) with (sp1 - 80) in O224 by lia.
  ck_open_s FPM G.cp3 (G.plans 3%nat _ eq_refl) (-432) [g] (fun _ : nat => @nil byte) [(20%nat, -304)] sp1 R M fx model K Hh Hl Hfp H2
    ltac:(let q := fresh in let z := fresh in let X := fresh in intros q z [X|[]]; injection X as <- <-; split; [lia | exact H20]).
  - ck_reg E (9%bv : reg) H9. ck_gh E 0%nat g.
    unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 408) 265928 S1. + ck_kw64 (sp1 - 416) g S2. + ck_kw64 (sp1 - 424) C S3. + ck_kw64 (sp1 - 432) (C + 8) S4.
    + e_wr.
    + ck_kw64 (sp1 - 304) 777648 O0. + ck_kw32 (sp1 - 296) 65792 O8. + ck_kw64 (sp1 - 288) 777808 O16. + ck_kw64 (sp1 - 256) (sp1 - 288) O48.
    + eapply kword16_intro with (A := sp1 - 232) (z := 0); [ev_start | lia | lia | reflexivity | exact O72].
    + eapply kzero_intro with (A := sp1 - 224) (N := 144); [ev_start | reflexivity | lia | lia | lia | lia | exact OZ].
    + ck_kw32 (sp1 - 80) 1024 O224.
    + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj. + e_al8 HCa 1.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (9%bv : reg) H9. ck_reg E (10%bv : reg) H10. ck_gh E 0%nat g.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE4 sp1 C) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4 & Hk5); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Krsv fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_RSV; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (23%bv : reg)
      | ck_keeps HLF Hag64 KO8 | | | | | | exact FRM | exact MG].
    + unfold pframe, CCT.RA_P. cbn [cells64]. repeat split; [ck_cell64 HLF (EVar 2) (-408) (ELit 265956); reflexivity | ck_cell64 HLF (EVar 2) (-416) (EVar 64); ck_atom
        | ck_cell64 HLF (EVar 2) (-424) (EAlu ALU_ADD (EVar 41) (ELit (-8))); ck_vlin | ck_cell64 HLF (EVar 2) (-432) (EVar 41); ck_atom
        | ck_cell64 HLF (EVar 2) (-440) (EAlu ALU_ADD (EVar 41) (ELit 312)); ck_vlin | ck_cell64 HLF (EVar 2) (-448) (EAlu ALU_ADD (EVar 2) (ELit (-304))); ck_vlin
        | ck_saved HLF Hag64 (-456) 53%nat (21%bv : reg) | ck_cell64 HLF (EVar 2) (-464) (ELit 1); reflexivity | ck_saved HLF Hag64 (-472) 55%nat (23%bv : reg)].
    + ck_cell64 HLF (EVar 41) 264 (EVar 42). ck_atom.
    + ck_cell64 HLF (EVar 41) 280 (EVar 42). ck_atom.
    + ck_cell8 HLF (EVar 41) 296 (ELit 1). reflexivity.
    + unfold pcells, PML.VT_PARSER, PML.VT_FUNC.
      split; [ck_cell64 HLF (EVar 41) 312 (ELit 776856); reflexivity|].
      split; [ck_cell32 HLF (EVar 41) 320 (ELit 1024); reflexivity|].
      split; [ck_cell8 HLF (EVar 41) 324 (ELit 0); reflexivity|].
      split; [ck_cell8 HLF (EVar 41) 325 (ELit 1); reflexivity|].
      split; [apply u16_of_u8s; [ck_cell8 HLF (EVar 41) 326 (ELit 0); reflexivity | ck_cell8 HLF (EVar 41) 327 (ELit 1); reflexivity]|].
      split; [ck_cell8 HLF (EVar 41) 328 (ELit 0); reflexivity|].
      split; [ck_cell8 HLF (EVar 41) 329 (ELit 0); reflexivity|].
      split; [ck_cell8 HLF (EVar 41) 330 (ELit 0); reflexivity|].
      split.
      { intros j Hj. assert (JJ : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
        destruct JJ as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
        - ck_cell64 HLF (EVar 41) 336 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 344 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 352 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 360 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 368 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 376 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 384 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 392 (ELit 0). reflexivity.
        - ck_cell64 HLF (EVar 41) 400 (ELit 0). reflexivity. }
      split; [ck_cell64 HLF (EVar 41) 408 (ELit 777808); reflexivity|].
      split; [ck_cell64 HLF (EVar 41) 440 (EAlu ALU_ADD (EVar 41) (ELit 408)); ck_vlin|].
      split; [ck_cell64 HLF (EVar 41) 456 (ELit 0); reflexivity|].
      split; [eapply kzero_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 41) 480) (ELit 40)) HLF); vm_compute; reflexivity | ev_start | reflexivity]|].
      split; [ck_cell32 HLF (EVar 41) 520 (ELit 16777217); reflexivity|].
      split; [eapply kword16_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA (EVar 41) 524) 2 (ELit 0)) HLF); vm_compute; reflexivity | ev_start | reflexivity]|].
      split; [ck_cell32 HLF (EVar 41) 528 (ELit 0); reflexivity|].
      apply zeros48_of_u64; [apply (L5.defined_grows _ _ _ _ MG); eapply (L5.defined_sub _ _ _ _ _ DC); lia
        | ck_cell64 HLF (EVar 41) 536 (ELit 0); reflexivity | ck_cell64 HLF (EVar 41) 544 (ELit 0); reflexivity | ck_cell64 HLF (EVar 41) 552 (ELit 0); reflexivity
        | ck_cell64 HLF (EVar 41) 560 (ELit 0); reflexivity | ck_cell64 HLF (EVar 41) 568 (ELit 0); reflexivity | ck_cell64 HLF (EVar 41) 576 (ELit 0); reflexivity].
Qed.

Lemma s_r_rsv : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 496) -> CK.spok sp1 -> 2 ^ 40 + 304 <= sp1 -> getr R 19%bv = Z_to_bv 64 (sp1 - 304) ->
  L5.u64_at RSEGS M (sp1 - 304) CCT.OPT_VT -> L5.u32_at RSEGS M (sp1 - 304 + 224) 1024 -> PML.img_ro M ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 496) -> getr R' 1%bv = Z_to_bv 64 CCT.R_VRSV -> getr R' 10%bv = getr R 23%bv -> getr R' 11%bv = Z_to_bv 64 66 ->
      TK.keepsR KO4 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_VEC_RESERVE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_RSV M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] Hlo H19 O0 O224 RO Kv.
  change CCT.R_RSV with (CC.cp_pc G.cp4). unfold CCT.OPT_VT in O0. pose proof (al16_8 sp1 Hal) as Hsp8.
  ck_open FPM G.cp4 (G.plans 4%nat _ eq_refl) (-496) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (19%bv : reg) H19.
    unfold know_ok, G.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + tk_kimg RO. + ck_kw64 (sp1 - 304) 777648 O0. + ck_kw32 (sp1 - 304 + 224) 1024 O224. + e_al8 Hsp8 (-38).
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (19%bv : reg) H19.
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kv fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_VRSV; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (23%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 KO4].
Qed.

Lemma s_r_vrsv : forall (fx : FPState) R M model K sp1,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 496) -> CK.spok sp1 -> L5.defined M (sp1 - 481) 1 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 496) -> getr R' 1%bv = Z_to_bv 64 CCT.R_PUSH -> getr R' 10%bv = getr R 23%bv -> getr R' 11%bv = Z_to_bv 64 (sp1 - 481) ->
      TK.keepsR CK.CSR R R' -> L5.u8_at RSEGS M' (sp1 - 481) 0 -> TK.samem (fun a => ~ (sp1 - 481 <= a < sp1 - 480)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_VEC_PUSH M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_VRSV M model) K.
Proof.
  intros fx R M model K sp1 Hh Hl Hfp H2 [Hsp Hal] DX Kp.
  change CCT.R_VRSV with (CC.cp_pc G.cp5).
  ck_open FPM G.cp5 (G.plans 5%nat _ eq_refl) (-496) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - unfold know_ok, G.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 481 <= a < sp1 - 480)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kp fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_PUSH; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (23%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 CK.CSR
      | | exact FRM | exact MG].
    ck_cell8 HLF (EVar 2) (-481) (ELit 0). reflexivity.
Qed.

Definition KE6 (sp1 C : Z) (a : Z) : Prop := ~ (C + 533 <= a < C + 534) /\ ~ (C + 592 <= a < C + 641) /\ ~ (sp1 - 384 <= a < sp1 - 380).

Lemma s_r_push : forall (fx : FPState) R M model K sp1 C p0 p6 p7,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 496) -> CK.spok sp1 ->
  2 ^ 40 <= C <= 2 ^ 47 - 656 -> sp1 <= C -> 0 <= p0 < 2 ^ 64 -> 0 <= p6 < 2 ^ 64 -> 0 <= p7 < 2 ^ 64 ->
  cells64 M (pframe sp1 C p0 p6 p7) -> L5.u8_at RSEGS M (C + 532) 0 -> L5.defined M C 656 -> L5.defined M (sp1 - 384) 4 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 400) -> getr R' 1%bv = Z_to_bv 64 CCT.R_SYSCAT ->
      getr R' 8%bv = Z_to_bv 64 p0 -> getr R' 9%bv = Z_to_bv 64 C -> getr R' 18%bv = Z_to_bv 64 (C + 8) -> getr R' 19%bv = Z_to_bv 64 (C + 320) -> getr R' 20%bv = Z_to_bv 64 (C + 592) ->
      getr R' 21%bv = Z_to_bv 64 p6 -> getr R' 22%bv = Z_to_bv 64 1 -> getr R' 23%bv = Z_to_bv 64 p7 -> TK.keepsR KO8 R R' ->
      L5.u32_at RSEGS M' (sp1 - 384) 0 -> L5.u8_at RSEGS M' (C + 640) 0 -> L5.u8_at RSEGS M' (C + 533) 1 -> L5.u64_at RSEGS M' (C + 592) PML.VT_VISITOR ->
      L5.u64_at RSEGS M' (C + 600) 4 -> L5.u8_at RSEGS M' (C + 608) 0 -> L5.u64_at RSEGS M' (C + 616) 0 -> L5.u64_at RSEGS M' (C + 624) 0 -> L5.u64_at RSEGS M' (C + 632) 0 ->
      TK.samem (KE6 sp1 C) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SYSTEM_CATEGORY M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_PUSH M model) K.
Proof.
  intros fx R M model K sp1 C p0 p6 p7 Hh Hl Hfp H2 [Hsp Hal] HC J1 Hp0 Hp6 Hp7 PF D532 DC D384 Ksys.
  change CCT.R_PUSH with (CC.cp_pc G.cp6). unfold pframe, CCT.RA_P in PF. cbn [cells64] in PF. destruct PF as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _).
  ck_open FPM G.cp6 (G.plans 6%nat _ eq_refl) (-496) [p0; C; p6; p7] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat p0. ck_gh E 1%nat C. ck_gh E 2%nat p6. ck_gh E 3%nat p7.
    unfold know_ok, G.cp6. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 408) 265956 P1. + ck_kw64 (sp1 - 416) p0 P2. + ck_kw64 (sp1 - 424) C P3. + ck_kw64 (sp1 - 432) (C + 8) P4.
    + ck_kw64 (sp1 - 440) (C + 320) P5. + ck_kw64 (sp1 - 448) (sp1 - 304) P6. + ck_kw64 (sp1 - 456) p6 P7. + ck_kw64 (sp1 - 464) 1 P8. + ck_kw64 (sp1 - 472) p7 P9.
    + e_range. + ck_kw8 (C + 532) 0 D532. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_gh E 0%nat p0. ck_gh E 1%nat C. ck_gh E 2%nat p6. ck_gh E 3%nat p7.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE6 sp1 C) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Ksys fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_SYSCAT; tk_lin HLF (1%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg)
      | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | tk_lin HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg) | ck_keeps HLF Hag64 KO8
      | | | | | | | | | | exact FRM | exact MG].
    + ck_cell32 HLF (EVar 2) (-384) (ELit 0). reflexivity.
    + ck_cell8 HLF (EVar 65) 640 (ELit 0). reflexivity.
    + ck_cell8 HLF (EVar 65) 533 (ELit 1). reflexivity.
    + unfold PML.VT_VISITOR. ck_cell64 HLF (EVar 65) 592 (ELit 778104). reflexivity.
    + ck_cell64 HLF (EVar 65) 600 (ELit 4). reflexivity.
    + ck_cell8 HLF (EVar 65) 608 (ELit 0). reflexivity.
    + ck_cell64 HLF (EVar 65) 616 (ELit 0). reflexivity.
    + ck_cell64 HLF (EVar 65) 624 (ELit 0). reflexivity.
    + ck_cell64 HLF (EVar 65) 632 (ELit 0). reflexivity.
Qed.

Lemma s_r_syscat : forall (fx : FPState) R M model K sp1 cat,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 400) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 cat -> 0 <= cat < 2 ^ 64 ->
  L5.defined M (sp1 - 376) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 400) -> getr R' 1%bv = Z_to_bv 64 CCT.R_RN -> getr R' 10%bv = getr R 9%bv -> getr R' 11%bv = getr R 20%bv ->
      getr R' 12%bv = Z_to_bv 64 (sp1 - 384) -> TK.keepsR CK.CSR R R' -> L5.u64_at RSEGS M' (sp1 - 376) cat ->
      TK.samem (fun a => ~ (sp1 - 376 <= a < sp1 - 368)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_READ_NEXT_C M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_SYSCAT M model) K.
Proof.
  intros fx R M model K sp1 cat Hh Hl Hfp H2 [Hsp Hal] H10 Hcat DX Krn.
  change CCT.R_SYSCAT with (CC.cp_pc G.cp7).
  ck_open FPM G.cp7 (G.plans 7%nat _ eq_refl) (-400) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - unfold know_ok, G.cp7. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 376 <= a < sp1 - 368)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Krn fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_RN; tk_lin HLF (1%bv : reg) | ck_keep HLF Hag64 (10%bv : reg) (9%bv : reg) | ck_keep HLF Hag64 (11%bv : reg) (20%bv : reg)
      | tk_lin HLF (12%bv : reg) | ck_keeps HLF Hag64 CK.CSR | | exact FRM | exact MG].
    ck_cell64 HLF (EVar 2) (-376) (EVar 42). ck_atom.
Qed.

Definition KE8 (sp1 : Z) (a : Z) : Prop := ~ (sp1 - 320 <= a < sp1 - 296) /\ ~ (sp1 - 240 <= a < sp1 - 232).
Lemma nth_gl : forall (gl : list Z) j z, nth_error gl j = Some z -> (j < length gl)%nat.
Proof. intros gl j z H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma s_r_rn : forall (fx : FPState) R M model K sp1 rav R0 C IS E s6 code,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 400) -> CK.spok sp1 -> L5.ra_ok rav ->
  0 <= C < 2 ^ 64 -> 0 <= IS < 2 ^ 64 -> 0 <= E < 2 ^ 64 -> 0 <= s6 < 2 ^ 64 -> 0 <= code < 2 ^ 31 ->
  L5.u32_at RSEGS M (sp1 - 384) code -> cells64 M (wframe sp1 rav R0) -> cells64 M (cframe sp1 C IS E s6) ->
  L5.u64_at RSEGS M (sp1 - 288) PML.VT_FUNC -> L5.u64_at RSEGS M (sp1 - 256) (sp1 - 288) -> zeros M (sp1 - 224) 144 -> PML.img_ro M -> L5.defined M (sp1 - 400) 400 ->
  (code = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s05 R0 R' -> getr R' 22%bv = Z_to_bv 64 s6 -> TK.keepsR KO7 R R' ->
      TK.samem (KE8 sp1) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (code <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 400) -> getr R' 1%bv = Z_to_bv 64 CCT.R_SETEC2 ->
      getr R' 10%bv = Z_to_bv 64 (sp1 - 400) -> getr R' 11%bv = Z_to_bv 64 1 -> TK.keepsR CK.CSR R R' -> TK.samem (KE8 sp1) M M' -> mem_grows M M' ->
      L5.u64_at RSEGS M' (sp1 - 312) CCT.RA_C -> L5.u64_at RSEGS M' (sp1 - 320) E ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_SET_EC2 M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_RN M model) K.
Proof.
  intros fx R M model K sp1 rav R0 C IS E s6 code Hh Hl Hfp H2 [Hsp Hal] Hra HC HIS HE Hs6 Hcode CO WF CF O16 O48 OZ RO D400 Kret Kset.
  change CCT.R_RN with (CC.cp_pc G.cp8). unfold PML.VT_FUNC in O16.
  unfold cframe, CCT.RA_C, CCT.OPT_VT, CCT.OPT_VT2 in CF. cbn [cells64] in CF. destruct CF as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
  unfold wframe in WF. cbn [cells64] in WF. destruct WF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21.
  set (gl := [code; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv);
              bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 21%bv); 0; 0; 0; E; IS; C; s6]).
  ck_open FPM G.cp8 (G.plans 8%nat _ eq_refl) (-400) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E0 0%nat code. ck_gh E0 20%nat rav. ck_gh E0 21%nat (bv_unsigned (getr R0 8%bv)). ck_gh E0 22%nat (bv_unsigned (getr R0 9%bv)). ck_gh E0 23%nat (bv_unsigned (getr R0 18%bv)).
    ck_gh E0 24%nat (bv_unsigned (getr R0 19%bv)). ck_gh E0 25%nat (bv_unsigned (getr R0 20%bv)). ck_gh E0 26%nat (bv_unsigned (getr R0 21%bv)).
    ck_gh E0 30%nat E. ck_gh E0 31%nat IS. ck_gh E0 32%nat C. ck_gh E0 33%nat s6.
    unfold know_ok, G.cp8. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw32 (sp1 - 384) code CO.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 312) 236424 C1. + ck_kw64 (sp1 - 320) E C2. + ck_kw64 (sp1 - 328) IS C3. + ck_kw64 (sp1 - 336) C C4. + ck_kw64 (sp1 - 344) (sp1 - 288) C5.
    + ck_kw64 (sp1 - 360) 777688 C7. + ck_kw64 (sp1 - 352) 777648 C6. + ck_kw64 (sp1 - 368) s6 C8.
    + e_wr. + ck_kw64 (sp1 - 288) 777808 O16. + ck_kw64 (sp1 - 256) (sp1 - 288) O48.
    + eapply kzero_intro with (A := sp1 - 224) (N := 144); [ev_start | reflexivity | lia | lia | lia | lia | exact OZ].
    + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 34%nat in Hj8. change (CC.cp_nx G.cp8) with 104%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_gh E0 0%nat code. ck_gh E0 30%nat E.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE8 sp1) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k; discriminate Hnth]].
    +
      ck_probes HLF PF. destruct PF as (PF & _). ck_w2z PF. rewrite (RK.ext_s32 code Hcode) in PF. apply RK.w_inj in PF; [|lia|lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 20%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_cc Hh Hl R1 Hra).
      apply (Kret PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | tk_reg HLF (22%bv : reg); exact (GH 33%nat _ eq_refl) | ck_keeps HLF Hag64 KO7 | exact FRM | exact MG].
      unfold same_s05. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 21%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 22%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 23%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 24%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 25%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 26%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    +
      ck_probes HLF PF. destruct PF as (PF & _). ck_w2z PF. rewrite (RK.ext_s32 code Hcode) in PF. apply RK.w_neq in PF.
      apply (Kset PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold CCT.R_SETEC2; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 CK.CSR
        | exact FRM | exact MG | |].
      * ck_cell64 HLF (EVar 2) (-312) (ELit 236424). reflexivity.
      * ck_cell64 HLF (EVar 2) (-320) (EVar 94). ck_atom.
Qed.

Definition KE9 (sp1 C E : Z) (a : Z) : Prop := ~ (sp1 - 400 <= a < sp1) /\ ~ (C + 640 <= a < C + 641) /\ ~ (E <= a < E + 16).

Lemma s_r_setec2 : forall (fx : FPState) R M model K sp1 rav R0 C IS E s6 v64 cat tv64 tcat code tcode dnb e0 e8,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 400) -> getr R 8%bv = Z_to_bv 64 E -> getr R 9%bv = Z_to_bv 64 C ->
  CK.spok sp1 -> L5.ra_ok rav ->
  2 ^ 40 <= C <= 2 ^ 47 - 656 -> 2 ^ 40 <= E <= 2 ^ 47 - 16 -> sp1 <= C -> sp1 <= E -> (C + 656 <= E \/ E + 16 <= C) ->
  0 <= IS < 2 ^ 64 -> 0 <= s6 < 2 ^ 64 -> 0 <= v64 < 2 ^ 64 -> 0 <= cat < 2 ^ 64 -> 0 <= tv64 < 2 ^ 64 -> 0 <= tcat < 2 ^ 64 ->
  0 <= dnb < 256 -> 0 <= e0 < 2 ^ 64 -> 0 <= e8 < 2 ^ 64 ->
  v64 mod 2 ^ 32 = code -> 0 <= code < 2 ^ 31 -> tv64 mod 2 ^ 32 = tcode -> 0 <= tcode < 2 ^ 31 ->
  1 <= cat <= 2 ^ 40 -> cat mod 8 = 0 -> 1 <= tcat <= 2 ^ 40 -> tcat mod 8 = 0 ->
  L5.u64_at RSEGS M (sp1 - 384) v64 -> L5.u64_at RSEGS M (sp1 - 376) cat -> L5.u64_at RSEGS M (sp1 - 400) tv64 -> L5.u64_at RSEGS M (sp1 - 392) tcat ->
  L5.u8_at RSEGS M (C + 640) dnb -> L5.u64_at RSEGS M E e0 -> L5.u64_at RSEGS M (E + 8) e8 ->
  cells64 M (wframe sp1 rav R0) -> cells64 M (cframe sp1 C IS E s6) ->
  L5.u64_at RSEGS M (sp1 - 288) PML.VT_FUNC -> L5.u64_at RSEGS M (sp1 - 256) (sp1 - 288) -> zeros M (sp1 - 224) 144 -> PML.img_ro M -> L5.defined M (sp1 - 400) 400 ->
  L5.defined M C 656 -> L5.defined M E 16 ->
  ((code = tcode /\ cat = tcat) -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s05 R0 R' -> getr R' 22%bv = Z_to_bv 64 s6 ->
      TK.keepsR KO7 R R' -> L5.u8_at RSEGS M' (C + 640) 1 -> L5.u64_at RSEGS M' E e0 -> L5.u64_at RSEGS M' (E + 8) e8 -> TK.samem (KE9 sp1 C E) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (~ (code = tcode /\ cat = tcat) -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s05 R0 R' -> getr R' 22%bv = Z_to_bv 64 s6 ->
      TK.keepsR KO7 R R' -> L5.u64_at RSEGS M' E v64 -> L5.u64_at RSEGS M' (E + 8) cat -> L5.u8_at RSEGS M' (C + 640) dnb -> TK.samem (KE9 sp1 C E) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CCT.R_SETEC2 M model) K.
Proof.
  intros fx R M model K sp1 rav R0 C IS E s6 v64 cat tv64 tcat code tcode dnb e0 e8 Hh Hl Hfp H2 H8 H9 [Hsp Hal] Hra HC HE J1 J2 J3 HIS Hs6 Hv Hcat Htv Htcat Hdnb He0 He8 Hm Hc Htm Htc Hcr Hca Htr Hta
    L0 L1 L2 L3 D640 E0c E8c WF CF O16 O48 OZ RO D400 DC DE Kdone Kcopy.
  change CCT.R_SETEC2 with (CC.cp_pc G.cp9). unfold PML.VT_FUNC in O16.
  unfold cframe, CCT.RA_C, CCT.OPT_VT, CCT.OPT_VT2 in CF. cbn [cells64] in CF. destruct CF as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
  unfold wframe in WF. cbn [cells64] in WF. destruct WF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21.
  set (gl := [v64; cat; tv64; tcat; dnb; e0; e8; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv);
              bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 21%bv); 0; 0; 0; E; IS; C; s6]).
  ck_open FPM G.cp9 (G.plans 9%nat _ eq_refl) (-400) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E0 (8%bv : reg) H8. ck_reg E0 (9%bv : reg) H9.
    ck_gh E0 0%nat v64. ck_gh E0 1%nat cat. ck_gh E0 2%nat tv64. ck_gh E0 3%nat tcat. ck_gh E0 4%nat dnb. ck_gh E0 5%nat e0. ck_gh E0 6%nat e8.
    ck_gh E0 20%nat rav. ck_gh E0 21%nat (bv_unsigned (getr R0 8%bv)). ck_gh E0 22%nat (bv_unsigned (getr R0 9%bv)). ck_gh E0 23%nat (bv_unsigned (getr R0 18%bv)).
    ck_gh E0 24%nat (bv_unsigned (getr R0 19%bv)). ck_gh E0 25%nat (bv_unsigned (getr R0 20%bv)). ck_gh E0 26%nat (bv_unsigned (getr R0 21%bv)).
    ck_gh E0 30%nat E. ck_gh E0 31%nat IS. ck_gh E0 32%nat C. ck_gh E0 33%nat s6.
    unfold know_ok, G.cp9. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 384) v64 L0. + ck_kw64 (sp1 - 376) cat L1. + ck_kw64 (sp1 - 400) tv64 L2. + ck_kw64 (sp1 - 392) tcat L3.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 312) 236424 C1. + ck_kw64 (sp1 - 320) E C2. + ck_kw64 (sp1 - 328) IS C3. + ck_kw64 (sp1 - 336) C C4. + ck_kw64 (sp1 - 344) (sp1 - 288) C5.
    + ck_kw64 (sp1 - 360) 777688 C7. + ck_kw64 (sp1 - 352) 777648 C6. + ck_kw64 (sp1 - 368) s6 C8.
    + e_wr. + ck_kw64 (sp1 - 288) 777808 O16. + ck_kw64 (sp1 - 256) (sp1 - 288) O48.
    + eapply kzero_intro with (A := sp1 - 224) (N := 144); [ev_start | reflexivity | lia | lia | lia | lia | exact OZ].
    + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_range. + e_range.
    + ck_kw8 (C + 640) dnb D640. + e_wr. + ck_kw64 E e0 E0c. + ck_kw64 (E + 8) e8 E8c. + e_wr.
    + e_disj. + e_disj. + e_disj. + e_range. + e_al8 Hca 0. + e_range. + e_al8 Hta 0.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. pose proof (nth_gl gl j z Hj) as Hj8. change (length gl) with 34%nat in Hj8. change (CC.cp_nx G.cp9) with 104%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E0 (8%bv : reg) H8. ck_reg E0 (9%bv : reg) H9.
    ck_gh E0 0%nat v64. ck_gh E0 1%nat cat. ck_gh E0 2%nat tv64. ck_gh E0 3%nat tcat. ck_gh E0 4%nat dnb. ck_gh E0 5%nat e0. ck_gh E0 6%nat e8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE9 sp1 C E) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k as [|k]; [injection Hnth as <- | destruct k; discriminate Hnth]]].
    all: assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 20%nat _ eq_refl)).
    all: assert (SS : same_s05 R0 R') by (unfold same_s05; repeat split;
           [ tk_reg HLF (8%bv : reg); etransitivity; [exact (GH 21%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]
           | tk_reg HLF (9%bv : reg); etransitivity; [exact (GH 22%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]
           | tk_reg HLF (18%bv : reg); etransitivity; [exact (GH 23%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]
           | tk_reg HLF (19%bv : reg); etransitivity; [exact (GH 24%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]
           | tk_reg HLF (20%bv : reg); etransitivity; [exact (GH 25%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]
           | tk_reg HLF (21%bv : reg); etransitivity; [exact (GH 26%nat _ eq_refl) | apply Z_to_bv_bv_unsigned] ]).
    all: assert (S6 : getr R' 22%bv = Z_to_bv 64 s6) by (tk_reg HLF (22%bv : reg); exact (GH 33%nat _ eq_refl)).
    all: assert (S2 : getr R' 2%bv = Z_to_bv 64 sp1) by (tk_lin HLF (2%bv : reg)).
    all: assert (KO : TK.keepsR KO7 R R') by (ck_keeps HLF Hag64 KO7).
    all: apply (CK.ret_leaf fx' R' _ M' model K rav ret_cc Hh Hl R1 Hra).
    +
      ck_probes HLF PF. destruct PF as (PFa & PFb & _). ck_w2z PFa. ck_w2z PFb.
      rewrite (ext_s32_mod v64 code Hv Hm Hc), (ext_s32_mod tv64 tcode Htv Htm Htc) in PFa. apply RK.w_inj in PFa; [|lia|lia]. apply RK.w_inj in PFb; [|lia|lia].
      apply (Kdone (conj PFa PFb) fx' R' M' Hfp' S2 SS S6 KO); [| | |exact FRM | exact MG].
      * ck_cell8 HLF (EVar 41) 640 (ELit 1). reflexivity.
      * replace E with (E + 0) by lia. ck_cell64 HLF (EVar 40) 0 (EVar 69). ck_atom.
      * ck_cell64 HLF (EVar 40) 8 (EVar 70). ck_atom.
    +
      ck_probes HLF PF. destruct PF as (PFa & _). ck_w2z PFa.
      rewrite (ext_s32_mod v64 code Hv Hm Hc), (ext_s32_mod tv64 tcode Htv Htm Htc) in PFa. apply RK.w_neq in PFa.
      apply (Kcopy (fun X => PFa (proj1 X)) fx' R' M' Hfp' S2 SS S6 KO); [| | | exact FRM | exact MG].
      * replace E with (E + 0) by lia. ck_cell64 HLF (EVar 40) 0 (EVar 64). ck_atom.
      * ck_cell64 HLF (EVar 40) 8 (EVar 65). ck_atom.
      * ck_cell8 HLF (EVar 41) 640 (EVar 68). ck_atom.
    +
      ck_probes HLF PF. destruct PF as (PFb & _). ck_w2z PFb. apply RK.w_neq in PFb.
      apply (Kcopy (fun X => PFb (proj2 X)) fx' R' M' Hfp' S2 SS S6 KO); [| | | exact FRM | exact MG].
      * replace E with (E + 0) by lia. ck_cell64 HLF (EVar 40) 0 (EVar 64). ck_atom.
      * ck_cell64 HLF (EVar 40) 8 (EVar 65). ck_atom.
      * ck_cell8 HLF (EVar 41) 640 (EVar 68). ck_atom.
Qed.

End S.
End CCS.
