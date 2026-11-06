(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 136 of its 173 lines of code are new or changed and 32 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma tq_le_nth : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal.
  rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma tq_le_len : forall n z, length (Z_to_le_bytes n z) = n.
Proof. induction n as [|n IH]; intros z; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma tq_byte32 : forall a b i, 0 <= i < 4 -> a mod 2 ^ 32 = b mod 2 ^ 32 ->
  Z_to_bv 8 (Z.shiftr a (8 * i)) = Z_to_bv 8 (Z.shiftr b (8 * i)).
Proof.
intros a b i Hi Hab. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
apply Z.bits_inj'. intros n Hn.
destruct (Z.lt_ge_cases n 8) as [Hl | Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite <- (Z.mod_pow2_bits_low a 32 (n + 8 * i)) by lia. rewrite Hab. apply Z.mod_pow2_bits_low. lia.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma tq_inc32 : forall d, 0 <= d < 2 ^ 32 ->
  bv_unsigned (alu64 ALU_ADD (sext 64 (bv_extract 0 32 (Z_to_bv 64 d))) (Z_to_bv 64 1)) mod 2 ^ 32 = (d + 1) mod 2 ^ 32.
Proof.
intros d Hd. rewrite sext64_lit, alu64_add_lit, Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2 ^ 64).
unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
change (bv_wrap 64 d) with (d mod 2 ^ 64). rewrite (Z.mod_small d (2 ^ 64)) by lia.
change (bv_wrap 32 d) with (d mod 2 ^ 32). rewrite (Z.mod_small d (2 ^ 32)) by lia.
unfold bv_swrap. change (bv_wrap 32 ?x) with (x mod 2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite Z.mod_mod_divide by (exists (2 ^ 32); reflexivity).
replace ((d + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31 + 1) with ((d + 2 ^ 31) mod 2 ^ 32 + (1 - 2 ^ 31)) by lia.
rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tq_hdr_same : forall E m (Tc : list byte) b, YP09.region_ok SEGS E m R_hdr ->
  ed E 0 = Tc -> base_val E (Some 8%nat) = b ->
  forall i, 384 <= i < 400 -> mbyte SEGS m (b + i) = nth_error Tc (Z.to_nat i).
Proof.
intros E m Tc b Hreg Hed Hb i Hi. unfold R_hdr in Hreg.
rewrite (region_bytes E m 8 384 400 384 400 _ b (DTC.sub Tc 384 16) Hreg Hb ltac:(vm_compute; reflexivity)) by
  (first [ lia
         | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|]; intros k Hk; rewrite Hed;
           rewrite nth_error_sub by lia; f_equal; lia ]).
rewrite nth_error_sub by lia. f_equal. lia.
Qed.
Lemma tq_hdr_store : forall E m (v : sv) o w (Tc : list byte) b,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some 8%nat) 384 400 384 400
    [YP09.mkChunk o (CVal 4 v); YP09.mkChunk 384 (CData 0 384 (o - 384)); YP09.mkChunk (o + 4) (CData 0 (o + 4) (396 - o))]) ->
  (o = 388 \/ o = 392) -> length Tc = 400%nat -> ed E 0 = Tc -> base_val E (Some 8%nat) = b ->
  bv_unsigned (sv_denot E v) mod 2 ^ 32 = w mod 2 ^ 32 ->
  forall i, 384 <= i < 400 -> mbyte SEGS m (b + i) = nth_error (DTC.upd Tc o (Z_to_le_bytes 4 w)) (Z.to_nat i).
Proof.
intros E m v o w Tc b Hreg Ho HL Hed Hb Hv i Hi.
assert (HLu : Z.of_nat (length (Z_to_le_bytes 4 w)) = 4) by (rewrite tq_le_len; reflexivity).
destruct Ho as [-> | ->];
(lazymatch goal with |- _ = nth_error ?L _ =>
 rewrite (region_bytes E m 8 384 400 384 400 _ b (DTC.sub L 384 16) Hreg Hb ltac:(vm_compute; reflexivity)) by
  (first
   [ lia
   | repeat apply Forall_cons; try apply Forall_nil;
     [ intros k Hk; cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off YP09.cbyte Z.of_N] in Hk |- *;
       rewrite nth_error_sub by lia;
       lazymatch goal with |- _ = nth_error _ (Z.to_nat 384 + Z.to_nat (?o + k - 384))%nat =>
         replace (Z.to_nat 384 + Z.to_nat (o + k - 384))%nat with (Z.to_nat (o + k)) by lia;
         rewrite TM.upd_nth_in by lia;
         replace (Z.to_nat (o + k - o)) with (Z.to_nat k) by lia end;
       rewrite tq_le_nth by lia; unfold YP09.byte_of_word; f_equal; rewrite Z2Nat.id by lia;
       apply tq_byte32; [lia | exact Hv]
     | apply cagree_cdata; [lia|]; intros k Hk; rewrite Hed; rewrite nth_error_sub by lia;
       lazymatch goal with |- nth_error _ (Z.to_nat ?s) = nth_error _ (Z.to_nat 384 + ?x)%nat =>
         replace (Z.to_nat 384 + x)%nat with (Z.to_nat s) by lia end;
       rewrite TM.upd_nth_out by lia; reflexivity
     | apply cagree_cdata; [lia|]; intros k Hk; rewrite Hed; rewrite nth_error_sub by lia;
       lazymatch goal with |- nth_error _ (Z.to_nat ?s) = nth_error _ (Z.to_nat 384 + ?x)%nat =>
         replace (Z.to_nat 384 + x)%nat with (Z.to_nat s) by lia end;
       rewrite TM.upd_nth_out by lia; reflexivity ] ]) end;
 rewrite nth_error_sub by lia; f_equal; lia).
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUNTO := paj_run_to B LAWS.
Lemma seg_seq : forall c, SegRet B c -> SegSeq B c.
Proof.
intros c HRet regs1 m1 md1 Tc so ret HP HM Hso H18 H10 Hmod.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ. pose proof (tm_Tl _ _ _ _ _ _ HM) as HTl.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
assert (B8 : base_val (tobs_env c regs1 Tc 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
pose proof (tobs_regs_ok c regs1 Tc 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 Tc 0) as HEI.
assert (Hsq : 0 <= DTC.seq_of Tc < 2 ^ 32).
{ pose proof (data_word_range (tobs_env c regs1 Tc 0) 0 392 4 ltac:(cbn; lia)) as R.
  change (data_word _ 0 392 4) with (DTC.seq_of Tc) in R. change (2 ^ (8 * Z.of_N 4) - 1) with (2 ^ 32 - 1) in R. lia. }
assert (HL' : length (DTC.upd Tc 392 (Z_to_le_bytes 4 (DTC.seq_of Tc + 1))) = 400%nat)
  by (rewrite RDO.upd_len; [exact HTl | lia | rewrite tq_le_len, HTl; cbn; lia]).
unfold cfgB.
destruct Hso as [-> | ->];
(lazymatch type of H18 with _ = w64 (ts c - ?sv) =>
  destruct (tobs_enter B c regs1 m1 md1 Tc 0x55d0 false 0 sv HP HM ltac:(first [left; reflexivity | right; reflexivity]) H18
    ltac:(discriminate)) as [HS SHOK] end;
paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x55f0;
[ exact (tobs_awr B c _ false _ 0 HP B8 ltac:(discriminate))
| pmkst HS;
  assert (RG : forall q : Z, In q [2; 3; 4; 8; 9; 10; 18; 20; 21; 22; 24; 27] ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q))
  by (intros q Hq; cbn in Hq;
      repeat (destruct Hq as [<- | Hq];
        [ eapply (tobs_reg_same c regs1 Tc 0 _ _ _ _ _ HS HR0);
          [ vm_compute; reflexivity | vm_compute; reflexivity
          | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ] |]);
      destruct Hq);
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg; cbn [ms_mem restrict] in Hreg;
  assert (HM2 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1)
    (DTC.upd Tc 392 (Z_to_le_bytes 4 (DTC.seq_of Tc + 1))));
  [ apply (tobs_exit_run B LAWS c regs1 m1 md1 Tc (tobs_env c regs1 Tc 0) false _ 0 (ms_regs ms) (ms_mem ms) _ _ HP HM B8
      ltac:(discriminate) HFr HG HJ HL');
    [ intros i Hi Hn _; apply TM.upd_nth_out; rewrite ?tq_le_len; lia
    | intros i Hi; apply (tq_hdr_store _ _ _ 392 _ Tc (tt c) Hreg (or_intror eq_refl) HTl eq_refl B8); [|exact Hi];
      cbn [sv_denot]; change (data_word _ 0 392 4) with (DTC.seq_of Tc); apply tq_inc32; exact Hsq
    | discriminate
    | intros q Hq; apply RG; cbn in Hq |- *; tauto ]
  | lazymatch type of H18 with _ = w64 (ts c - ?sv) =>
      exact (HRet (ms_regs ms) (ms_mem ms) _ _ sv ret HP HM2 ltac:(first [left; reflexivity | right; reflexivity])
        (eq_trans (RG 18 ltac:(cbn; lia)) H18) (eq_trans (RG 10 ltac:(cbn; lia)) H10) Hmod) end ] ]).
Qed.
End h.
End f.
End d.
