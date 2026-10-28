(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PropExec CatExec SeqExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section RwSem.
Variable segs : list Segment.

Definition fldw (m : word -> option byte) (a : Z) (k : nat) (w : word) : Prop :=
  PropExec.rdn segs m (Z_to_bv 64 a) k = Some (word_to_le_bytes k w).

Lemma rw_adenot : forall E (a : saddr) (z : Z), estart E a = z -> 0 <= z < 2 ^ 64 -> adenot E a = Z_to_bv 64 z.
Proof. intros E a z Hs Hz. unfold adenot, PropExec.v_addi. unfold estart in Hs. rewrite Hs. reflexivity. Qed.

Lemma rw_kword_fld : forall E m (sa : saddr) (w : nat) (e : expr) (a v : Z),
  fld segs m a w v -> estart E sa = a -> 0 <= a < 2 ^ 64 -> a + Z.of_nat w <= 2 ^ 64 -> (w <= 8)%nat ->
  edenot E e = Z_to_bv 64 v -> kentry_ok segs E m (KWord sa w e).
Proof.
  intros E m sa w e a v HF Hs H0 H1 Hw He. cbn [kentry_ok]. split; [exact Hw|]. split.
  - unfold flat. rewrite Hs. lia.
  - rewrite (rw_adenot E sa a Hs ltac:(lia)), He. exact HF.
Qed.

Lemma rw_kword_fldw : forall E m (sa : saddr) (w : nat) (e : expr) (a : Z) (x : word),
  fldw m a w x -> estart E sa = a -> 0 <= a < 2 ^ 64 -> a + Z.of_nat w <= 2 ^ 64 -> (w <= 8)%nat ->
  edenot E e = x -> kentry_ok segs E m (KWord sa w e).
Proof.
  intros E m sa w e a x HF Hs H0 H1 Hw He. cbn [kentry_ok]. split; [exact Hw|]. split.
  - unfold flat. rewrite Hs. lia.
  - rewrite (rw_adenot E sa a Hs ltac:(lia)), He. exact HF.
Qed.

Lemma rw_kwr : forall E m (sa : saddr) (en : expr) (a n : Z),
  wr_at segs m a n -> estart E sa = a -> elenZ E en = n -> 0 < n ->
  kentry_ok segs E m (KWr sa en).
Proof.
  intros E m sa en a n HW Hs Hn Hpos. pose proof HW as (HA & HAn & _). cbn [kentry_ok].
  split; [unfold flat; lia|]. intros d mm Hd Hdm.
  rewrite Hs. apply (wr_at_store_ok segs m a n); [exact HW | lia | lia].
Qed.

Lemma rw_wr_at_of_stk : forall m lo hi, stk segs m lo hi -> wr_at segs m lo (hi - lo).
Proof.
  intros m lo hi (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
  exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma rw_wr_at_sub : forall m a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n -> wr_at segs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma rw_wbytes_eq : forall bs m a, CatExec.wbytes m a bs = write_to_mem m a bs.
Proof. induction bs as [|b bs IH]; intros m a; [reflexivity|]. cbn [CatExec.wbytes write_to_mem]. apply IH. Qed.

Lemma rw_wmono : forall E M log, wmono segs M (mem_denot E M log).
Proof.
  intros E M log. induction log as [|[a w v] rest IH]; cbn [mem_denot]; [apply wmono_refl|].
  rewrite rw_wbytes_eq. apply wmono_write. exact IH.
Qed.

Lemma rw_munch : forall W E M log,
  log_flat E log ->
  Forall (fun se => inside W (estart E (e_addr se)) (Z.of_nat (e_width se))) log ->
  munch W M (mem_denot E M log).
Proof.
  intros W E M log. induction log as [|[a w v] rest IH]; intros Hf Hin; cbn [mem_denot]; [apply munch_refl|].
  cbn [log_flat] in Hf. destruct Hf as (Hw & Hfl & Hf). inversion Hin as [|? ? Hin0 Hin1]; subst. cbn [e_addr e_width] in Hin0.
  rewrite rw_wbytes_eq.
  pose proof (flat_u E a (Z.of_nat w) Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  replace (adenot E a) with (wa (estart E a))
    by (apply bv_eq; rewrite Hu; unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
  apply munch_write; [exact (IH Hf Hin1) | lia | |].
  - rewrite CatExec.length_N_to_le_bytes. lia.
  - rewrite CatExec.length_N_to_le_bytes. exact Hin0.
Qed.

Lemma rw_log_flat_mid : forall E pre (a : saddr) (w : nat) (v : expr) post,
  log_flat E (pre ++ SE a w v :: post) -> (w <= 8)%nat /\ flat E a (Z.of_nat w).
Proof.
  intros E pre a w v post Hf.
  induction pre as [|[x y z] pre IH]; cbn [app log_flat] in Hf; [exact (conj (proj1 Hf) (proj1 (proj2 Hf))) | exact (IH (proj2 (proj2 Hf)))].
Qed.

Lemma rw_rdn_hit : forall E M pre (a : saddr) (w : nat) (v : expr) post,
  log_flat E (pre ++ SE a w v :: post) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) pre ->
  PropExec.rdn segs (mem_denot E M (pre ++ SE a w v :: post)) (adenot E a) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E M pre a w v post. induction pre as [|[a' w' v'] pre IH]; intros Hf Hd.
  - cbn [app mem_denot]. cbn [log_flat] in Hf. destruct Hf as (_ & Hfl & _).
    pose proof (flat_u E a (Z.of_nat w) Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    pose proof (SeqExec.rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E M post) (adenot E a)) as K.
    rewrite CatExec.length_N_to_le_bytes in K. apply K. rewrite Hu. lia.
  - cbn [app mem_denot]. cbn [app log_flat] in Hf. destruct Hf as (Hw' & Hfl' & Hf).
    inversion Hd as [|? ? Hd0 Hd1]; subst. cbn [e_addr e_width] in Hd0.
    pose proof (flat_u E a' (Z.of_nat w') Hfl') as Hu'. destruct Hfl' as (F1 & F2 & F3 & F4).
    pose proof (rw_log_flat_mid E pre a w v post Hf) as (_ & Hfa).
    pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. destruct Hfa as (G1 & G2 & G3 & G4).
    rewrite CatExec.rdn_wbytes_out.
    + exact (IH Hf Hd1).
    + rewrite Hu, Hu', CatExec.length_N_to_le_bytes. lia.
    + rewrite Hu. lia.
    + rewrite Hu', CatExec.length_N_to_le_bytes. lia.
Qed.

Lemma rw_fld_post : forall E M log (k : nat) (a : saddr) (w : nat) (v : expr) (A V : Z),
  log_flat E log -> nth_error log k = Some (SE a w v) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) (firstn k log) ->
  estart E a = A -> edenot E v = Z_to_bv 64 V ->
  fld segs (mem_denot E M log) A w V.
Proof.
  intros E M log k a w v A V Hf Hk Hd Hs Hv.
  pose proof (nth_error_split log k Hk) as (pre & post & Hl & Hlen). subst log. subst k.
  rewrite firstn_app, firstn_all, Nat.sub_diag in Hd. cbn [firstn] in Hd. rewrite app_nil_r in Hd.
  pose proof (rw_log_flat_mid E pre a w v post Hf) as (_ & Hfa).
  pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. destruct Hfa as (G1 & G2 & G3 & G4).
  unfold fld. rewrite <- (rw_adenot E a A Hs ltac:(lia)), <- Hv. apply rw_rdn_hit; assumption.
Qed.

Lemma rw_fldw_post : forall E M log (k : nat) (a : saddr) (w : nat) (v : expr) (A : Z) (X : word),
  log_flat E log -> nth_error log k = Some (SE a w v) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) (firstn k log) ->
  estart E a = A -> edenot E v = X ->
  fldw (mem_denot E M log) A w X.
Proof.
  intros E M log k a w v A X Hf Hk Hd Hs Hv.
  pose proof (nth_error_split log k Hk) as (pre & post & Hl & Hlen). subst log. subst k.
  rewrite firstn_app, firstn_all, Nat.sub_diag in Hd. cbn [firstn] in Hd. rewrite app_nil_r in Hd.
  pose proof (rw_log_flat_mid E pre a w v post Hf) as (_ & Hfa).
  pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. destruct Hfa as (G1 & G2 & G3 & G4).
  unfold fldw. rewrite <- (rw_adenot E a A Hs ltac:(lia)), <- Hv. apply rw_rdn_hit; assumption.
Qed.

End RwSem.

Definition sh0w (segs : list Segment) (shbase : Z) (m : word -> option byte) (x : Z) : Prop :=
  PropExec.rdn segs m (Z_to_bv 64 (x / 8 + shbase)) 1 = Some [Z_to_bv 8 0].

Lemma rw_kword_sh0 : forall segs shbase E m (e : expr) (x : Z),
  sh0w segs shbase m x -> edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= shbase -> x / 8 + shbase + 1 <= 2 ^ 64 ->
  kentry_ok segs E m (KWord (SA (EAlu ALU_SRL e (ELit 3)) shbase) 1 (ELit 0)).
Proof.
  intros segs shbase E m e x HS He Hx Hb Hr. apply (rw_kword_fld segs E m _ 1 _ (x / 8 + shbase) 0).
  - unfold fld. exact HS.
  - unfold estart. cbn [a_base a_off edenot]. rewrite He. cbn [alu64 alu].
    rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !PropExec.bv_wrap64_mod.
    rewrite (Z.mod_small x) by lia.
    replace (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3 by (vm_compute; reflexivity).
    rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
  - cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - lia.
  - reflexivity.
Qed.


Ltac rw_estartB := unfold estart; cbn [a_base a_off]; evs; wnormB; rewrite ?u64_of_Z by dlia; dlia.
Ltac rw_elenB := unfold elenZ; evs; rewrite ?u64_of_Z by dlia; dlia.
