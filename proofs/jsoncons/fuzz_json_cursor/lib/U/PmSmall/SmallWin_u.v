(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeAt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPW.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Definition rng_in (cells : list kentry) (e : expr) (lo hi : Z) : bool := match CX.range3 cells e with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end.
Definition rng_is (cells : list kentry) (e : expr) (v : Z) : bool := rng_in cells e v v.
Lemma rng_in_sound : forall E (M : mem) cells e lo hi, know_ok RSEGS E M cells -> rng_in cells e lo hi = true -> lo <= uv E e <= hi.
Proof.
  intros E M cells e lo hi HK H. unfold rng_in in H. destruct (CX.range3 cells e) as [[l h]|] eqn:Hr; [|discriminate]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (CX.range3_sound RSEGS E M cells e l h HK Hr) as X. unfold PB.uv. lia.
Qed.
Lemma rng_is_sound : forall E (M : mem) cells e v, know_ok RSEGS E M cells -> rng_is cells e v = true -> uv E e = v.
Proof. intros E M cells e v HK H. pose proof (rng_in_sound E M cells e v v HK H). lia. Qed.

Lemma mod64_zero : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> (x - y) mod 2 ^ 64 = 0 -> x = y.
Proof. intros x y Hx Hy H. destruct (Z_lt_dec (x - y) 0) as [N|N]; [rewrite PB3.mod_neg64 in H by lia; lia | rewrite Z.mod_small in H by lia; lia]. Qed.

Lemma win_pos : forall seg wlen c lo, 0 <= seg -> 0 <= wlen <= 16384 -> seg + wlen < 2 ^ 63 -> 0 <= c < 2 ^ 64 -> 0 <= lo ->
  lo <= (c - seg) mod 2 ^ 64 <= 16384 -> (seg + wlen - c) mod 2 ^ 64 <= 16384 -> seg + lo <= c <= seg + wlen.
Proof.
  intros seg wlen c lo Hs Hw Hsw Hc Hlo H1 H2.
  destruct (Z_lt_dec (c - seg) 0) as [N1|N1]; [rewrite PB3.mod_neg64 in H1 by lia; lia|]. rewrite Z.mod_small in H1 by lia.
  destruct (Z_lt_dec (seg + wlen - c) 0) as [N2|N2]; [rewrite PB3.mod_neg64 in H2 by lia; lia|]. lia.
Qed.

Definition named_at (cells : list kentry) (cur : expr) : option (saddr * expr * Z * Z) :=
  match find (fun X => match X with KWord a 1 _ => rng_is cells (APC.esub (APC.eaddz (a_base a) (a_off a)) cur) 0 | _ => false end) cells with
  | Some (KWord a 1 v) => match CX.range3 cells v with
                          | Some (lo, hi) => if (Z.leb 0 lo && Z.leb hi 255)%bool then Some (a, v, lo, hi) else None
                          | None => None end
  | _ => None
  end.
Lemma named_sound : forall E (M : mem) cells cur a v lo hi, know_ok RSEGS E M cells -> named_at cells cur = Some (a, v, lo, hi) ->
  L5.u8_at RSEGS M (uv E cur) (uv E v) /\ lo <= uv E v <= hi /\ 0 <= lo /\ hi <= 255.
Proof.
  intros E M cells cur a v lo hi HK H. unfold named_at in H.
  destruct (find _ cells) as [X|] eqn:Hf; [|discriminate]. apply find_some in Hf as [Hin Hrg].
  destruct X as [a0 w v0| | | | | | | | |]; try discriminate. destruct w as [|[|w]]; try discriminate.
  destruct (CX.range3 cells v0) as [[l h]|] eqn:Hr; [|discriminate]. destruct (Z.leb 0 l && Z.leb h 255)%bool eqn:Hb; [|discriminate]. injection H as -> -> -> ->.
  apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  pose proof (CX.range3_sound RSEGS E M cells v lo hi HK Hr) as Hv. fold (uv E v) in Hv.
  pose proof (rng_is_sound E M cells _ 0 HK Hrg) as H0. rewrite PB.uv_esub, PB.uv_eaddz in H0.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HC. cbn [kentry_ok] in HC. destruct HC as (_ & Hfl & Hrd).
  pose proof Hfl as (F0 & F1 & _ & F3). unfold estart in F0, F1, F3. fold (uv E (a_base a)) in F0, F1, F3.
  rewrite (Z.mod_small (uv E (a_base a) + a_off a)) in H0 by lia.
  pose proof (mod64_zero (uv E (a_base a) + a_off a) (uv E cur) ltac:(lia) (PB.uv_range E cur) H0) as Heq.
  split; [|lia]. unfold L5.u8_at. rewrite <- Heq.
  assert (Had : adenot E a = Z_to_bv 64 (uv E (a_base a) + a_off a)).
  { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E a)), (flat_u E a _ Hfl). reflexivity. }
  rewrite <- Had, Hrd. apply f_equal.
  assert (Hev : edenot E v = Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (uv E v)))).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. unfold PB.uv. symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hev. apply CX.wle1_byte.
Qed.
Lemma u8_inj : forall (M : mem) a b1 b2, L5.u8_at RSEGS M a b1 -> L5.u8_at RSEGS M a b2 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> b1 = b2.
Proof.
  intros M a b1 b2 H1 H2 R1 R2. unfold L5.u8_at in H1, H2. rewrite H1 in H2. assert (H3 : Z_to_bv 8 b1 = Z_to_bv 8 b2) by congruence. clear H2. apply (f_equal bv_unsigned) in H3. rename H3 into H2.
  rewrite !Z_to_bv_unsigned in H2. unfold bv_wrap in H2. change (bv_modulus 8) with 256 in H2. rewrite !Z.mod_small in H2 by lia. exact H2.
Qed.
Lemma u8_frame : forall (M1 M' : mem) a b, M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a) -> L5.u8_at RSEGS M1 a b -> L5.u8_at RSEGS M' a b.
Proof. intros M1 M' a b H H1. unfold L5.u8_at in *. cbn [rdn] in *. unfold rd1 in *. rewrite H. exact H1. Qed.

Definition sltu0 (v : expr) (c : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB v (ELit c)) (ELit 1)) 0 0.
Definition ne_chk (cells : list kentry) (v : expr) (lo hi c : Z) : bool := (PB.has cells (sltu0 v c) || Z.ltb hi c || Z.ltb c lo)%bool.
Lemma ne_chk_sound : forall E (M : mem) cells v lo hi c, know_ok RSEGS E M cells -> ne_chk cells v lo hi c = true -> lo <= uv E v <= hi -> 0 <= c < 2 ^ 64 -> uv E v <> c.
Proof.
  intros E M cells v lo hi c HK H Hv Hc. unfold ne_chk in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - pose proof (PB.has_ok E M _ _ HK H) as Q. unfold sltu0 in Q. cbn [kentry_ok] in Q. apply SPA.sltu_sub_ne; [|exact Hc]. unfold PB.uv. lia.
  - apply Z.ltb_lt in H. lia.
  - apply Z.ltb_lt in H. lia.
Qed.

Definition sltu1 (e : expr) (c : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB e (ELit c)) (ELit 1)) 1 1.
Lemma sltu_sub_eq : forall Ex x c, uv Ex (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1)) = 1 -> 0 <= c < 2 ^ 64 -> uv Ex x = c.
Proof.
  intros Ex x c H Hc. unfold PB.uv in H. cbn [edenot] in H. rewrite u_sltu64, u_sub64 in H. cbn [edenot] in H. rewrite u_lit64 in H. unfold two64 in H.
  rewrite (Z.mod_small c) in H by lia. change (bv_unsigned (Z_to_bv 64 1)) with 1 in H.
  destruct (Z.ltb_spec ((bv_unsigned (edenot Ex x) - c) mod 2 ^ 64) 1) as [Q|Q]; [|discriminate H].
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot Ex x) - c) (2 ^ 64) ltac:(lia)) as B.
  apply (mod64_zero (uv Ex x) c (PB.uv_range Ex x) Hc). unfold PB.uv. lia.
Qed.
Definition eq_chk (cells : list kentry) (e : expr) (c : Z) : bool := (rng_is cells e c || PB.has cells (sltu1 e c))%bool.
Lemma eq_chk_sound : forall E (M : mem) cells e c, know_ok RSEGS E M cells -> eq_chk cells e c = true -> 0 <= c < 2 ^ 64 -> uv E e = c.
Proof.
  intros E M cells e c HK H Hc. unfold eq_chk in H. apply orb_prop in H as [H|H]; [exact (rng_is_sound E M cells e c HK H)|].
  pose proof (PB.has_ok E M _ _ HK H) as Q. unfold sltu1 in Q. cbn [kentry_ok] in Q. apply sltu_sub_eq; [|exact Hc]. unfold PB.uv. lia.
Qed.

Definition nonws_chk (cells : list kentry) (v : expr) (lo hi : Z) : bool := forallb (ne_chk cells v lo hi) [9; 10; 13; 32].
Lemma nonws_sound : forall E (M : mem) cells v lo hi, know_ok RSEGS E M cells -> nonws_chk cells v lo hi = true -> lo <= uv E v <= hi -> ~ In (uv E v) [9; 10; 13; 32].
Proof.
  intros E M cells v lo hi HK H Hv Hin. unfold nonws_chk in H. rewrite forallb_forall in H.
  assert (Hc : 0 <= uv E v < 2 ^ 64) by (cbn [In] in Hin; lia).
  exact (ne_chk_sound E M cells v lo hi (uv E v) HK (H _ Hin) Hv Hc eq_refl).
Qed.
End SPW.
