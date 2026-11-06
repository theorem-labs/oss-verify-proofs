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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsBase BigFactsOps BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5AChk L5BChkAs0 L5ArithSpecsB0 L5ParseSpecsBB0 L5BDetailP L5BDetailK L5BDetailH Bo0_code_8e368_8f368
     AsanPlanCore AsanPlanSound Bo0PlanKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADM.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5ADTP. Import L5ADK. Import L5ADH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nwe_le2 (n : nat) : (n <= 38)%nat -> (num_words_est n <= 2)%nat.
Proof.
  intros H. unfold num_words_est. destruct (Nat.ltb_spec n 10) as [LT|GE]. lia.
  assert (B1: Z.of_nat n * 3402 / 1024 < 127) by (apply Z.div_lt_upper_bound; lia).
  assert (B0: 0 <= Z.of_nat n * 3402 / 1024) by (apply Z.div_pos; lia).
  assert (B2: (Z.of_nat n * 3402 / 1024 + 1 + 63) / 64 < 3) by (apply Z.div_lt_upper_bound; lia).
  assert (B3: 0 <= (Z.of_nat n * 3402 / 1024 + 1 + 63) / 64) by (apply Z.div_pos; lia). lia.
Qed.
Lemma nwe_ge3 (n : nat) : (39 <= n)%nat -> (3 <= num_words_est n)%nat.
Proof.
  intros H. unfold num_words_est. destruct (Nat.ltb_spec n 10) as [LT|GE]. lia.
  assert (B1: 129 <= Z.of_nat n * 3402 / 1024) by (apply Z.div_le_lower_bound; lia).
  assert (B2: 3 <= (Z.of_nat n * 3402 / 1024 + 1 + 63) / 64) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma est_eval (m : nat) : (10 <= m)%nat -> (3402 * Z.of_nat m / 1024 + 64) / 64 = Z.of_nat (num_words_est m).
Proof.
  intros Hm. unfold num_words_est. replace (m <? 10)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  rewrite Z2Nat.id. 2:{ apply Z.div_pos. 2: lia. pose proof (Z.div_pos (Z.of_nat m * 3402) 1024 ltac:(lia) ltac:(lia)). lia. }
  replace (Z.of_nat m * 3402) with (3402 * Z.of_nat m) by lia. f_equal. lia.
Qed.
Lemma est_small (m : nat) : (m <= 9)%nat -> Z.of_nat (num_words_est m) = 1.
Proof. intros Hm. unfold num_words_est. replace (m <? 10)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.

Lemma dec_acc_shift acc cs : dec_acc acc cs = acc * 10 ^ Z.of_nat (length cs) + dec_acc 0 cs.
Proof.
  revert acc. induction cs as [|c t IH]; intros acc.
  - cbn. lia.
  - cbn [dec_acc length]. rewrite (IH (acc * 10 + (c - 48))), (IH (0 * 10 + (c - 48))). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma dec_zero_all cs : digits_ok cs -> dec cs = 0 -> Forall (fun c => c = 48) cs.
Proof.
  induction cs as [|c t IH]; intros D Z0. constructor.
  unfold digits_ok in D. inversion D; subst. unfold dec in Z0. cbn [dec_acc] in Z0. rewrite dec_acc_shift in Z0.
  pose proof (dec_bound t (all_digits_Forall t ltac:(assumption))) as B. unfold dec in B.
  pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length t)) ltac:(lia) ltac:(lia)).
  assert (c = 48) by nia. constructor. assumption. apply IH. assumption. unfold dec. nia.
Qed.
Lemma dec_pos_of_nonzero ds (z : nat) : digits_ok ds -> (z < length ds)%nat -> nth z ds 0 <> 48 -> 0 < dec ds.
Proof.
  intros D Hz NZ. pose proof (dec_bound ds (all_digits_Forall ds D)) as B.
  destruct (Z.eq_dec (dec ds) 0) as [E|NE]. 2: lia. exfalso. apply NZ.
  pose proof (dec_zero_all ds D E) as AZ. exact (proj1 (Forall_nth _ _) AZ z 0 Hz).
Qed.
Lemma pow10_le (j m : nat) : (j <= m)%nat -> 10 ^ Z.of_nat j <= 10 ^ Z.of_nat m.
Proof. intros H. apply Z.pow_le_mono_r; lia. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma round_upZ_mono a b : 0 <= a <= b -> L5CSA.round_up a <= L5CSA.round_up b.
Proof. intros H. unfold L5CSA.round_up. pose proof (Z.div_le_mono a b 8 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma round_upZ_2 a : 0 <= a <= 2 -> L5CSA.round_up a = 8.
Proof. intros H. unfold L5CSA.round_up. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma setbit_fbW dyn : (Z.land (fbW dyn) 18446744073709551613 + 2) mod 2 ^ 64 = fbN dyn true.
Proof. destruct dyn; reflexivity. Qed.

(* [comment removed for export] *)
Definition fbWj (j : Z) (dyn : bool) : Z := Z.land j 252 + (if dyn then 1 else 0).
Definition fbNj (j : Z) (dyn ng : bool) : Z := if ng then Z.lor (fbWj j dyn) 2 else fbWj j dyn.
Lemma fbj_all (P : Z -> bool) : forallb (fun i => P (Z.of_nat i)) (seq 0 256) = true -> forall j, 0 <= j < 256 -> P j = true.
Proof. intros H j Hj. rewrite forallb_forall in H. specialize (H (Z.to_nat j)). rewrite Z2Nat.id in H by lia. apply H. apply in_seq. lia. Qed.
Lemma fbNj_land2 j dyn ng : 0 <= j < 256 -> Z.land (fbNj j dyn ng) 2 = if ng then 2 else 0.
Proof. intros Hj. destruct dyn, ng; unfold fbNj, fbWj; apply Z.eqb_eq; revert j Hj; apply fbj_all; vm_compute; reflexivity. Qed.
Lemma fbNj_range j dyn ng : 0 <= j < 256 -> 0 <= fbNj j dyn ng <= 255.
Proof. intros Hj. assert (X : ((0 <=? fbNj j dyn ng) && (fbNj j dyn ng <=? 255))%bool = true) by (destruct dyn, ng; unfold fbNj, fbWj; revert j Hj; apply fbj_all; vm_compute; reflexivity).
  apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2. lia. Qed.
Lemma fbNj_bit0 j dyn ng : 0 <= j < 256 -> Z.testbit (fbNj j dyn ng) 0 = dyn.
Proof. intros Hj. destruct dyn, ng; unfold fbNj, fbWj; apply Bool.eqb_prop; revert j Hj; apply fbj_all; vm_compute; reflexivity. Qed.
Lemma fbWj_lor1 j : 0 <= j < 256 -> Z.lor (fbWj j false) 1 = fbWj j true.
Proof. intros Hj. unfold fbWj; apply Z.eqb_eq; revert j Hj; apply fbj_all; vm_compute; reflexivity. Qed.
Lemma fbNj_bit1 j dyn : 0 <= j < 256 -> Z.testbit (fbWj j dyn) 1 = false.
Proof. intros Hj. destruct dyn; unfold fbWj; apply Bool.eqb_prop; revert j Hj; apply fbj_all; vm_compute; reflexivity. Qed.
Lemma fbWj_div4 j : 0 <= j < 256 -> 4 * (j / 4) = fbWj j false.
Proof. intros Hj. unfold fbWj; apply Z.eqb_eq; revert j Hj; apply fbj_all; vm_compute; reflexivity. Qed.
Lemma zbv_notp p : Z_to_bv 64 ((-1) * p - 1) = Z_to_bv 64 (18446744073709551615 - p).
Proof.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (18446744073709551615 - p) with ((-1) * p - 1 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma setbit_fbWj j dyn : 0 <= j < 256 -> (Z.land (fbWj j dyn) 18446744073709551613 + 2) mod 2 ^ 64 = fbNj j dyn true.
Proof. intros Hj. destruct dyn; unfold fbNj, fbWj; apply Z.eqb_eq; revert j Hj; apply fbj_all; vm_compute; reflexivity. Qed.
Lemma assign_fb_resj fb fbv (ng : bool) (n : nat) (grown : bool) :
  0 <= fb < 256 -> Z.land fb 3 = 0 -> (1 <= n)%nat -> (grown = true <-> (3 <= n)%nat) -> Z.land fbv 2 = (if ng then 2 else 0) ->
  assign_fb fb fbv n grown = res_fb fb n ng.
Proof.
  intros Hfb H3 Hn HG HL2. destruct (fb3_facts fb Hfb H3) as (F1 & F2 & F3 & F4 & F5 & F6 & _ & _ & _ & _ & F11).
  unfold assign_fb, res_fb. replace (Nat.eqb n 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (1 <=? n)%nat with true by (symmetry; apply Nat.leb_le; lia). rewrite HL2.
  destruct grown.
  - replace (3 <=? n)%nat with true by (symmetry; apply Nat.leb_le; apply HG; reflexivity). rewrite F2. destruct ng; cbn [andb]; lia.
  - replace (3 <=? n)%nat with false. 2: { symmetry. apply Nat.leb_gt. destruct (Nat.lt_ge_cases n 3). lia. exfalso. pose proof (proj2 HG ltac:(lia)). discriminate. }
    rewrite F1. destruct ng; cbn [andb]; lia.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis Hres : reserve_spec L ar HI.
Hypothesis Hmul : L5ASB.mul10_specB L ar HI.
Hypothesis Hadd : L5ASB.addd_specB L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.

Section MAIN.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
          (p o sp r fb : Z) (neg : bool) (s : list Z) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis CTX : mctx L ar IL HI R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2.
Variable jv : Z.                      (* [comment removed for export] *)
Hypothesis JVR : 0 <= jv < 256.
Local Notation fbW := (fbWj jv).
Local Notation fbN := (fbNj jv).
Local Notation fbN_land2 := (fun dyn ng => fbNj_land2 jv dyn ng JVR).
Local Notation fbN_bit0 := (fun dyn ng => fbNj_bit0 jv dyn ng JVR).
Local Notation fbN_range := (fun dyn ng => fbNj_range jv dyn ng JVR).
Local Notation setbit_fbW := (fun dyn => setbit_fbWj jv dyn JVR).
Local Notation sb := (sp - 16).
Local Notation n := (Z.of_nat (length s)).
Local Notation negz := (if neg then 1 else 0).
Local Notation FF' := ((F, 2, sp - 16 - 192 + 32) :: FF).
Local Abbreviation binv := (L5ADH.binv L ar HI R M model LB FF LK A sp neg F).
Local Abbreviation rinv := (L5ADH.rinv R sp F).
Local Abbreviation Wret := (L5ADH.Wret F fl).
Local Abbreviation binv_model := (L5ADH.binv_model L ar HI R M model LB FF LK A sp neg F).
Local Abbreviation binv_piece := (L5ADH.binv_piece L ar IL HI R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2 CTX).
Local Abbreviation binv_mem := (L5ADH.binv_mem L ar C IL HI HIok R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2 CTX).
Local Abbreviation binv_callee := (L5ADH.binv_callee L ar C IL HI HIok R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2 CTX).
Local Abbreviation vis_facts := (L5ADH.vis_facts L ar C IL HI LY HIok R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2 CTX).
Local Abbreviation exit_path := (L5ADH.exit_path L ar C IL HI LY HIok R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2 CTX Hdel).
Local Abbreviation apure := (L5ADH.apure L ar C HI LY HIok).
Local Abbreviation stksh_now := (L5ADH.stksh_now L ar C IL HI HIok R M model K LB FF LK cr A p o sp r fb neg s F fl LK2 M2 model2 CTX).
Ltac open_ctx CTX :=
  destruct CTX as [HK RA UR1 G2 G4 LEN HVN CRD SLO SHI SPT SA32 SA16 SPR FFR FFRS HH BIG FB3 AOB SZ BYTES BR SRC APART PRG OR OBIG FS1 FS2 FAPP FCEIL FAPART FBLK LKI2
                   FLP FLNC FLA HH2 FLC FR F32 F8 FBIG FLR FLBIG SF SFSH SFL OF OFSH OFL FQ31 NCF NCS SSH KONT].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vb (dyn : bool) (sto : L5.bstore) (ws : list Z) : L5.bigobj := L5.BO (fbW dyn) (length ws) sto.
Definition vobj (Mc : word -> option byte) (BX : list (Z * Z)) (crc : credit) (dyn : bool) (sto : L5.bstore) (ws : list Z) (V : Z) : Prop :=
  L5.big_at RSEGS Mc (F + 96) (vb dyn sto ws) /\ L5C.obj_limbs RSEGS Mc (vb dyn sto ws) ws /\ shadow_zero Mc (F + 96) 4 /\
  (L5.u64_at RSEGS Mc (sb - 160) o /\ L5.u64_at RSEGS Mc (sb - 176) (F + 112)) /\
  L5.limbs_val ws = V /\ length ws = nwords V /\ 0 <= V /\
  (dyn = false -> (exists v0 v1, sto = L5.BInl v0 v1) /\ BX = [] /\ crc = cr /\ (length s <= 38)%nat) /\
  (dyn = true -> exists q cap, sto = L5.BDyn cap q /\ BX = [(q, 8 * cap)] /\ crc = adebit L cr (vblk (length s)) /\ 8 * cap = vblk (length s) /\
                 (forall V', 0 <= V' < 10 ^ n -> Z.of_nat (nwords V') + 1 <= cap /\ L5CSA.round_up (Z.of_nat (nwords V')) <= cap)).
Lemma vb_dyn dyn sto ws : L5.bo_dyn (vb dyn sto ws) = dyn. Proof. unfold L5.bo_dyn, vb. cbn [L5.bo_fb]. exact (fbNj_bit0 jv dyn false JVR). Qed.
Lemma vb_neg dyn sto ws : L5.bo_neg (vb dyn sto ws) = false. Proof. unfold L5.bo_neg, vb. cbn [L5.bo_fb]. exact (fbNj_bit1 jv dyn JVR). Qed.

(* [comment removed for export] *)
Lemma blk_not_client q nq Mc Vc LKc crc Ac a : ri_inv HI ((q, nq) :: LB) FF' LKc crc Ac Mc Vc -> q <= a < q + nq -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a.
Proof.
  intros HHc Ha. pose proof CTX as CTX'. open_ctx CTX'. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & _).
  destruct (WB (q, nq) (or_introl eq_refl)) as (BR0 & _ & _ & _ & BA & BF & _). cbn [fst snd] in *. rewrite lb_remove_head in BA.
  apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp L5PSB.DETAIL_SCRB q nq a HH SPT BR0 BA).
  - eapply fframes_apart_incl. exact BF. intros g Hg. apply in_or_app. left. right. exact Hg.
  - exact Ha.
Qed.

(* [comment removed for export] *)
Lemma callee_pre W BX Mc modelc LKc crc Ac SCRc : binv W BX Mc modelc LKc crc Ac -> 0 <= SCRc <= 4656 ->
  astk ar Mc (sb - 192) SCRc /\ ffr FF' LKc 5 /\ ffrs FF' (sb - 192) /\ (sb - 192) mod 32 = 0.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9) HS. pose proof CTX as CTX'. open_ctx CTX'.
  split. { replace (sb - 192) with (sp - 208) by (clear; lia). apply (astk_sub ar Mc Mc sp L5PSB.DETAIL_SCRB 208 SCRc B6 (mem_grows_refl Mc)).
           clear; lia. clear - HS; lia. rewrite DSCR_EQ; clear - HS; lia. replace (sp - 208) with (sb - 192) by (clear; lia). exact SA16. }
  split. { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
           assert (ND : NoDup (map ff_addr (FF' ++ LKc))). { clear - WF. decompose [and] WF. assumption. }
           apply (proj1 (ffrk_1 FF' LKc 5)). apply (ffrk_push_other 1 FF LK LKc (F, 2, sb - 192 + 32) 5). cbn [ff_class fst snd]. clear; lia.
           apply (proj2 (ffrk_1 FF LK 5)). exact FFR. exact B5. exact ND. }
  split. { apply (ffrs_push FF sp). exact FFRS. clear; lia. clear; lia. }
  clear - SA32. unfold aligned in SA32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arith_step pc SCRa dd (VAL : list Z -> Z -> Z) y (Hop : L5ASB.arith_spec_atB pc SCRa dd VAL y L ar HI)
      (fx : FPState) Rc Mc modelc BX LKc crc Ac dyn sto ws V ret :
  0 <= SCRa <= 4656 -> SCRa mod 8 = 0 -> dd <= 5 ->
  binv [] BX Mc modelc LKc crc Ac -> vobj Mc BX crc dyn sto ws V -> rinv Rc ->
  0 <= V < 10 ^ n -> 0 <= VAL ws y < 10 ^ n ->
  getr Rc (reg 10) = Z_to_bv 64 (F + 96) -> getr Rc (reg 11) = Z_to_bv 64 y -> getr Rc (reg 1) = Z_to_bv 64 ret -> L5.ra_ok ret ->
  (forall (fx' : FPState) R' M' model' BX' LK' cr' A' dyn' sto' ws',
      binv [] BX' M' model' LK' cr' A' -> vobj M' BX' cr' dyn' sto' ws' (VAL ws y) -> regs_preserved Rc R' ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' ret M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros HS HS8 HD BI VO RI VR VR' G10 G11 G1 RAr KS.
  destruct (callee_pre [] BX Mc modelc LKc crc Ac SCRa BI HS) as (ASTKc & FFRc & FFRSc & A32c).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof VO as (VB & VL & VSZ & VSP & VV & VN & V0 & VI & VD).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  pose proof CTX as CTX'. open_ctx CTX'.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WFB & _).
  assert (NWB : (nwords V <= 260)%nat). { pose proof (nwords_bound V (length s) VR). pose proof (num_words_est_4999 (length s) LEN). clear - H H0. lia. }
  assert (AOV : aobj FF' (F + 96) 32).
  { exists (F, 2, sb - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 2) with 256. split. clear; lia. split. clear; lia.
    clear - F8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (DATA : forall k, 0 <= k -> (dyn = true -> k <= 8 * (Z.of_nat (nwords V) + 1)) -> (dyn = false -> k <= 16) ->
             L5.bo_data (F + 96) (vb dyn sto ws) + k <= ahl_ceil ar
             /\ (forall a, L5.bo_data (F + 96) (vb dyn sto ws) <= a < L5.bo_data (F + 96) (vb dyn sto ws) + k ->
                   ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32) /\ a < ahl_ceil ar)).
  { intros k Hk KD KI. destruct dyn.
    - destruct (VD eq_refl) as (q & cap & -> & EBX & _ & _ & CAPOK). subst BX. cbn [L5.bo_data L5.bo_st vb].
      destruct (WFB (q, 8 * cap) (or_introl eq_refl)) as ((Q0 & _ & _ & _ & Q4 & (_ & Q5 & _)) & _). cbn [fst snd] in *.
      specialize (KD eq_refl). destruct (CAPOK V VR) as [CK _]. unfold BIGSHADOW_LO, BIGSHADOW_HI in Q5.
      split. clear - KD CK Q4; lia. intros a Ha. split. apply (blk_not_client q (8 * cap) Mc _ LKc crc Ac a B1). clear - Ha KD CK; lia.
      split. clear - Ha KD CK Q5 Q0 FR F8. unfold SB. lia. clear - Ha KD CK Q4; lia.
    - destruct (VI eq_refl) as ((v0 & v1 & ->) & _). cbn [L5.bo_data L5.bo_st vb]. specialize (KI eq_refl).
      split. clear - KI FCEIL; lia. intros a Ha. split. apply (NCF a). left. clear - Ha KI; lia.
      split. clear - Ha KI FR FBIG. unfold SB. lia. clear - Ha KI FCEIL; lia. }
  apply (Hop fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac (F + 96) (sb - 192) ret (vb dyn sto ws) ws B1 B2 HK).
  - rewrite r10. exact G10.
  - rewrite r11. exact G11.
  - cbn [vb L5.bo_len]. rewrite VN. clear - NWB. lia.
  - rewrite vb_dyn. intros Hd. subst dyn. destruct (VD eq_refl) as (q & cap & -> & _ & _ & _ & CAPOK). cbn [vb L5.bo_len L5.bo_cap L5.bo_st].
    rewrite VN. exact (proj1 (CAPOK V VR)).
  - rewrite vb_dyn. intros Hd _. subst dyn. destruct (VI eq_refl) as (_ & _ & -> & M38).
    replace 64 with (vblk (length s)). exact (proj1 CRD). unfold vblk. replace (length s <? 39)%nat with true by (symmetry; apply Nat.ltb_lt; clear - M38; lia). reflexivity.
  - rewrite r1. exact G1.
  - exact RAr.
  - rewrite r2. exact G2'.
  - exact A32c.
  - rewrite r4, G4'. exact G4.
  - exact ASTKc.
  - apply (stksh_now BX Mc modelc LKc crc Ac (sb - 192 - SCRa) BI). rewrite DSCR_EQ. clear - HS; lia. clear - HS8 SA32. unfold aligned in SA32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    eapply ffr_le. exact FFRc. exact HD.
  - exact FFRSc.
  - exact VB.
  - exact VL.
  - apply vb_neg.
  - exact AOV.
  - exact VSZ.
  - cbn [vb L5.bo_st]. intros cap q E. destruct dyn.
    + destruct (VD eq_refl) as (q' & cap' & E' & -> & _). rewrite E' in E. injection E as <- <-. left; reflexivity.
    + destruct (VI eq_refl) as ((v0 & v1 & E') & _). rewrite E' in E. discriminate E.
  - intros fx' R' M' model' g LB' cr' LK' A' POST RT IA AM ILK HH'.
    destruct POST as (RP & R10 & ws' & st' & LV & RED & LEN' & OB' & OL' & G). cbn [L5.bo_fb L5.bo_len vb] in LEN', OB', OL'.
    pose proof OL' as (_ & OF' & _).
    assert (LN : length ws' = nwords (VAL ws y)) by (apply length_nwords; assumption).
    (* [comment removed for export] *)
    assert (KEEP : forall Wc, ahpres L ar (BX ++ LB) FF' (sb - 192) SCRa Wc Mc M' ->
               (forall rr, In rr Wc -> fst rr + snd rr <= ahl_ceil ar /\ forall a, L5.in_rng rr a -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32)) ->
               shadow_zero M' (F + 96) 4 /\ (L5.u64_at RSEGS M' (sb - 160) o /\ L5.u64_at RSEGS M' (sb - 176) (F + 112))).
    { intros Wc AH HW. split.
      - intros j Hj. unfold byte_at. rewrite (proj1 AH). apply VSZ. exact Hj.
        split. unfold S, SB. clear - Hj FR. pose proof (Z.div_pos (F + 96) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (F + 96) (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
        split. apply (fframe_shadow_client L ar (BX ++ LB) FF' (sb - 192) SCRa F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S.
        rewrite (proj1 FQ31). clear - Hj F8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        intros rr Hr X. destruct (HW rr Hr) as (_ & HX). destruct (HX _ X) as (_ & NS). apply NS. unfold S. clear - Hj F8. lia.
      - split.
        + eapply L5C.u64_at_agree. 4: exact (proj1 VSP). 2: clear - SPR; lia. 2: clear - SPR; lia. intros i Hi.
          apply (stack_callee L ar (BX ++ LB) FF' (sb - 192) SCRa Wc Mc M' i AH). intros rr Hr. exact (proj1 (HW rr Hr)). clear - Hi SPR; lia. clear - Hi SLO SHI SPT; lia. clear - Hi; lia.
        + eapply L5C.u64_at_agree. 4: exact (proj2 VSP). 2: clear - SPR; lia. 2: clear - SPR; lia. intros i Hi.
          apply (stack_callee L ar (BX ++ LB) FF' (sb - 192) SCRa Wc Mc M' i AH). intros rr Hr. exact (proj1 (HW rr Hr)). clear - Hi SPR; lia. clear - Hi SLO SHI SPT; lia. clear - Hi; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct g as [|gq gc].
    + (* [comment removed for export] *)
      destruct G as (DD & ELB & ECR & ST & AH). subst LB' cr'. rewrite vb_dyn in DD. cbn [vb L5.bo_len L5.bo_st] in DD, ST, AH.
      destruct (DATA (8 * (Z.of_nat (length ws) + 1)) ltac:(clear; lia) ltac:(intros _; rewrite VN; clear; lia)
                  ltac:(intros E; destruct DD as [DD|DD]; [rewrite E in DD; discriminate DD | clear - DD; lia])) as (DC & DN).
      assert (HW : forall rr, In rr [(F + 96, 32); (L5.bo_data (F + 96) (vb dyn sto ws), 8 * (Z.of_nat (length ws) + 1))] ->
                 fst rr + snd rr <= ahl_ceil ar /\ forall a, L5.in_rng rr a -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32)).
      { intros rr [<-|[<-|[]]]; cbn [fst snd]; unfold L5.in_rng; cbn [fst snd].
        - split. clear - FCEIL; lia. intros a Ha. split. apply (NCF a). left; clear - Ha; lia. clear - Ha FR FBIG. unfold SB. lia.
        - split. exact DC. intros a Ha. destruct (DN a Ha) as (X1 & X2 & _). split; assumption. }
      destruct (KEEP _ AH HW) as (VSZ' & VSP').
      apply (KS fx' R' M' model' BX LK' crc A' dyn st' ws').
      * apply (binv_callee [] [] BX BX BX Mc modelc LKc crc Ac M' model' LK' crc A' SCRa _ BI AH HH' AM RT IA ILK HS).
        -- intros rr Hr. exact (proj1 (HW rr Hr)).
        -- intros a Hc _ rr Hr X. exact (proj1 (proj2 (HW rr Hr) a X) Hc).
        -- intros a X. exact X.
      * unfold vobj, vb. split. exact OB'. split. exact OL'. split. exact VSZ'. split. exact VSP'. split. exact LV. split. exact LN. split. clear - VR'; lia.
        split.
        -- intros Hd. subst dyn. destruct (VI eq_refl) as ((v0 & v1 & ->) & X1 & X2 & X3). destruct st' as [w0 w1|c q]; [|destruct ST].
           split. exists w0, w1; reflexivity. split. exact X1. split. exact X2. exact X3.
        -- intros Hd. subst dyn. destruct (VD eq_refl) as (q & cap & -> & X1 & X2 & X3 & X4). destruct st' as [w0 w1|c q']; [destruct ST|]. destruct ST as [-> ->].
           exists q, cap. split. reflexivity. split. exact X1. split. exact X2. split. exact X3. exact X4.
      * exact RP.
    + (* [comment removed for export] *)
      destruct G as (DD & L2 & EC & EST & ELB & ECR & FB & AH). rewrite vb_dyn in DD. subst dyn gc st' LB' cr'.
      destruct (VI eq_refl) as (_ & -> & -> & M38). cbn [app] in *.
      assert (HW : forall rr, In rr [(F + 96, 32)] ->
                 fst rr + snd rr <= ahl_ceil ar /\ forall a, L5.in_rng rr a -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32)).
      { intros rr [<-|[]]; cbn [fst snd]; unfold L5.in_rng; cbn [fst snd].
        split. clear - FCEIL; lia. intros a Ha. split. apply (NCF a). left; clear - Ha; lia. clear - Ha FR FBIG. unfold SB. lia. }
      destruct (KEEP _ AH HW) as (VSZ' & VSP').
      assert (V64 : vblk (length s) = 64). { unfold vblk. replace (length s <? 39)%nat with true by (symmetry; apply Nat.ltb_lt; clear - M38; lia). reflexivity. }
      apply (KS fx' R' M' model' [(gq, 64)] LK' (adebit L cr 64) A' true (L5.BDyn 8 gq) ws').
      * apply (binv_callee [] [] [] [] [(gq, 64)] Mc modelc LKc cr Ac M' model' LK' (adebit L cr 64) A' SCRa _ BI AH HH' AM RT IA ILK HS).
        -- intros rr Hr. exact (proj1 (HW rr Hr)).
        -- intros a Hc _ rr Hr X. exact (proj1 (proj2 (HW rr Hr) a X) Hc).
        -- intros a X. exact X.
      * unfold vobj, vb. rewrite (fbWj_lor1 jv JVR) in OB', OL'.
        split. exact OB'. split. exact OL'. split. exact VSZ'. split. exact VSP'. split. exact LV. split. exact LN. split. clear - VR'; lia.
        split. intros X; discriminate X. intros _. exists gq, 8. rewrite V64. split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity.
        intros V' HV'. pose proof (nwords_le2 V' (length s) M38 HV') as N2. split. clear - N2; lia.
        rewrite (round_upZ_2 (Z.of_nat (nwords V'))) by (clear - N2; lia). clear; lia.
      * exact RP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma src_facts BX Mc modelc LKc crc Ac : binv [] BX Mc modelc LKc crc Ac ->
  L5.bytes_at RSEGS (mrestrict (ahid Ac modelc) Mc) p s /\ aacc (mrestrict (ahid Ac modelc) Mc) p n.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). pose proof CTX as CTX'. open_ctx CTX'.
  assert (BY : L5.bytes_at RSEGS Mc p s). { apply (ek_bytes L ar C IL LY ILY LB FF sp L5PSB.DETAIL_SCRB M Mc p s B7 SRC). clear - PRG; lia. clear - PRG; lia. exact BYTES. }
  assert (SRCc : asrc IL (BX ++ LB) FF' Mc p n).
  { apply (ek_src L ar C IL HI LY HIok LB FF LK cr A sp L5PSB.DETAIL_SCRB M model Mc (BX ++ LB) FF' p n HH B7 SRC). apply incl_appr. apply incl_refl. apply incl_tl. apply incl_refl. }
  pose proof (asrc_vis L ar C IL HI LY ILY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc p n B1 SRCc) as PVIS.
  split.
  - eapply L5C.bytes_at_agree. 4: exact BY. 2: clear - PRG; lia. 2: clear - PRG; lia. intros i Hi. apply mrestrict_visible. replace i with (p + (i - p)) by (clear; lia). apply PVIS. clear - Hi; lia.
  - apply (aacc_vis (ahid Ac modelc) Mc p n). apply (asrc_aacc L ar C IL HI ILY HIok ICok (BX ++ LB) FF' LKc crc Ac Mc _ p n B1 SRCc).
    intros a Ha. apply (asrc_shadow_vis L ar C IL HI LY ILY HIok ICok (BX ++ LB) FF' LKc crc Ac Mc modelc p n a B1 SRCc Ha).
Qed.

(* [comment removed for export] *)
Definition lregs (Rc : bvmap 5 word) (j rem idx : nat) : Prop :=
  getr Rc (reg 10) = Z_to_bv 64 ((p + Z.of_nat j) / 8 + 2147450880) /\ getr Rc (reg 18) = Z_to_bv 64 (18446744073709551615 - p) /\
  getr Rc (reg 19) = Z_to_bv 64 9 /\ getr Rc (reg 20) = Z_to_bv 64 (Z.of_nat idx) /\
  getr Rc (reg 22) = Z_to_bv 64 (p + Z.of_nat j) /\ getr Rc (reg 23) = Z_to_bv 64 (p + Z.of_nat j) /\ getr Rc (reg 24) = Z_to_bv 64 (F + 96) /\
  getr Rc (reg 27) = Z_to_bv 64 (Z.of_nat rem).

Lemma credit_after (dyn : bool) crc : (dyn = false -> crc = cr) -> (dyn = true -> crc = adebit L cr (vblk (length s))) -> credit_le (parse_debit L cr (length s)) crc.
Proof.
  intros VI VD. unfold parse_debit. destruct dyn.
  - rewrite (VD eq_refl). apply adebit_le. exact LY2. apply vblk_pos.
  - rewrite (VI eq_refl). eapply credit_le_trans. apply adebit_le. exact LY2. apply vblk_pos. apply adebit_le. exact LY2. apply vblk_pos.
Qed.

(* [comment removed for export] *)
Lemma err_path (fx : FPState) Rc Mc modelc BX LKc crc Ac dyn sto ws V (j rem idx : nat) :
  (j < length s)%nat -> (nth j s 0 < 48 \/ 57 < nth j s 0) ->
  binv [] BX Mc modelc LKc crc Ac -> vobj Mc BX crc dyn sto ws V -> rinv Rc -> lregs Rc j rem idx -> (rem <= 4999)%nat -> (idx <= 4999)%nat ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8f024 Mc modelc) K.
Proof.
  intros Hj ND BI VO RI (L10 & L18 & L19 & L20 & L22 & L23 & L24 & L27) HREM HIDX.
  destruct (src_facts BX Mc modelc LKc crc Ac BI) as (BYv & ACCv).
  destruct (vis_facts [] BX Mc modelc LKc crc Ac BI) as ((W176 & IMGC & CSB & CUAR) & _).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  pose proof CTX as CTX'. open_ctx CTX'. destruct SPR as [SPR0 SPR1].
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  set (cur := p + Z.of_nat j) in *. set (c := nth j s 0) in *.
  assert (CR : 4096 <= cur /\ cur + 1 <= p + n) by (subst cur; clear - PRG Hj; lia).
  assert (CB : 0 <= c < 256). { subst c. rewrite Forall_forall in BR. apply BR. apply nth_In. exact Hj. }
  assert (Bc : L5.u8_at RSEGS MV cur c) by (apply BYv; exact Hj).
  destruct (L5ACHK0.chk_8ecd0 fx Rc MV cur ltac:(unfold S, SB; exact L10) L23 ltac:(clear - CR PRG; lia) ltac:(eapply aacc_sub; [exact ACCv | clear - CR; lia | clear - CR; lia]))
    as (R1 & MS1 & K1).
  assert (J2 : getr R1 (reg 2) = Z_to_bv 64 (sb - 192)) by (rewrite K1 by (clear; lia); exact G2').
  assert (J8 : getr R1 (reg 8) = Z_to_bv 64 (sb + 16)) by (rewrite K1 by (clear; lia); exact G8).
  assert (J9 : getr R1 (reg 9) = Z_to_bv 64 (sb - 192)) by (rewrite K1 by (clear; lia); exact G9).
  assert (J18 : getr R1 (reg 18) = Z_to_bv 64 (18446744073709551615 - p)) by (rewrite K1 by (clear; lia); exact L18).
  assert (J19 : getr R1 (reg 19) = Z_to_bv 64 9) by (rewrite K1 by (clear; lia); exact L19).
  assert (J20 : getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat idx)) by (rewrite K1 by (clear; lia); exact L20).
  assert (J21 : getr R1 (reg 21) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite K1 by (clear; lia); exact G21).
  assert (J22 : getr R1 (reg 22) = Z_to_bv 64 cur) by (rewrite K1 by (clear; lia); exact L22).
  assert (J23 : getr R1 (reg 23) = Z_to_bv 64 cur) by (rewrite K1 by (clear; lia); exact L23).
  assert (J24 : getr R1 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite K1 by (clear; lia); exact L24).
  assert (J26 : getr R1 (reg 26) = Z_to_bv 64 2147450880) by (rewrite K1 by (clear; lia); exact G26).
  assert (J27 : getr R1 (reg 27) = Z_to_bv 64 (Z.of_nat rem)) by (rewrite K1 by (clear; lia); exact L27).
  assert (HV55 : 4096 <= cur <= 140737488355327) by (clear - CR PRG; lia).
  assert (HV57 : 0 <= Z.of_nat rem < 2 ^ 64) by (clear - HREM; lia).
  assert (HV64 : 0 <= 18446744073709551615 - p < 2 ^ 64) by (clear - PRG; lia).
  assert (HV65 : 0 <= Z.of_nat idx < 2 ^ 64) by (clear - HIDX; lia).
  assert (EX : exists fx2 R2 M2v, msteps RSEGS (st fx R1 0x8f02c MV) (st fx2 R2 0x8f09c M2v) /\ mem_grows MV M2v
             /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sb - 136 <= i < sb - 136 + 8) -> M2v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
             /\ rinv R2 /\ getr R2 (reg 20) = Z_to_bv 64 22 /\ getr R2 (reg 24) = Z_to_bv 64 (F + 96)).
  { assert (RI1 : rinv R1). { apply (rinv_keep R sp F Rc R1 RI). intros k Hk. apply K1. unfold RIDX in Hk. cbn [In] in Hk. clear - Hk. lia. unfold RIDX in Hk. cbn [In] in Hk. clear - Hk; lia. unfold RIDX in Hk. cbn [In] in Hk. clear - Hk; lia. }
    destruct ND as [LT|GT].
    - assert (C47 : 0 <= c <= 47) by (clear - CB LT; lia).
      pose proof (dtD1l_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 57%nat => Z.of_nat rem | 58%nat => U R1 1 | 59%nat => U R1 10 | 60%nat => U R1 11
                                                  | 64%nat => 18446744073709551615 - p | 65%nat => Z.of_nat idx | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx2 & R2 & M2' & MG2 & FR2 & FZ2 & (MS2 & KS2 & Q10 & Q20 & Q25 & QC)).
      exists fx2, R2, M2'. split. exact MS2. split. exact MG2. split. exact FZ2. split. apply (rinv_ks R sp F R1 R2 KS_dtD1l RI1 KS2). vm_compute; reflexivity.
      split. exact Q20. rewrite (KS2 24%nat) by inl. exact J24.
    - assert (C58 : 58 <= c <= 255) by (clear - CB GT; lia).
      pose proof (dtD1h_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 57%nat => Z.of_nat rem | 58%nat => U R1 1 | 59%nat => U R1 10 | 60%nat => U R1 11
                                                  | 64%nat => 18446744073709551615 - p | 65%nat => Z.of_nat idx | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx2 & R2 & M2' & MG2 & FR2 & FZ2 & (MS2 & KS2 & Q10 & Q20 & Q25 & QC)).
      exists fx2, R2, M2'. split. exact MS2. split. exact MG2. split. exact FZ2. split. apply (rinv_ks R sp F R1 R2 KS_dtD1h RI1 KS2). vm_compute; reflexivity.
      split. exact Q20. rewrite (KS2 24%nat) by inl. exact J24. }
  destruct EX as (fx2 & R2 & M2v & MS2 & MG2 & FZ2 & RI2 & Q20 & Q24).
  set (Wp := fun a => sb - 136 <= a < sb - 128).
  apply (apiece L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8f024 R2 0x8f09c M2v Wp K B1 B2 (msteps_trans _ _ _ _ MS1 MS2) MG2).
  { intros a Ha Hna. apply FZ2. exact Ha. clear - Hna; subst Wp; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  pose proof (binv_piece [] BX Mc modelc LKc crc Ac M1 model1 Wp BI HH1 AM1 RT1 MGM1 FRM1
                ltac:(intros a Wa; subst Wp; cbn beta in Wa; left; right; exact Wa)) as BI1.
  pose proof VO as (VB & _ & _ & (_ & VC176) & _ & _ & _ & VI & VD).
  assert (VB1 : L5.big_at RSEGS M1 (F + 96) (vb dyn sto ws)).
  { eapply L5C.big_at_agree. 4: exact VB. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply FRM1. clear - Hi FR; lia. subst Wp; cbn beta. clear - Hi SF; lia. }
  apply (exit_path [] BX [] fx2 R2 M1 model1 LKc crc Ac (fbW dyn) (length ws) sto 22 BI1 RI2 Q24 Q20 ltac:(clear; lia) VB1).
  { destruct dyn.
    - destruct (VD eq_refl) as (q & cap & -> & -> & _). split. left; reflexivity. split. apply lb_remove_head.
      eapply L5C.u64_at_agree. 4: exact VC176. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi. apply FRM1. clear - Hi SPR1; lia. subst Wp; cbn beta. clear - Hi; lia.
    - destruct (VI eq_refl) as ((v0 & v1 & ->) & -> & _). reflexivity. }
  intros fxf Rf Mf modelf LKf Af RPf R11f AGf AHf RTf IAf AMf ILKf HHf.
  apply (KONT fxf Rf Mf modelf LB crc LKf Af).
  - split. exact RPf. right. split. { right. apply (not_digits_ok s j c Hj eq_refl). exact ND. }
    split. rewrite r11. exact R11f.
    split. reflexivity.
    split. { eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply (proj1 AHf). split. clear - Hi OR; lia.
             split. apply (obj_client L ar LB FF sp L5PSB.DETAIL_SCRB o 32 i AOB Hi). intros rr []. }
    split. { apply (credit_after dyn crc). intros E. exact (proj1 (proj2 (proj2 (VI E)))). intros E. destruct (VD E) as (q & cap & _ & _ & X & _). exact X. } exact AHf.
  - exact RTf.
  - exact IAf.
  - exact AMf.
  - exact ILKf.
  - exact HHf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma round_upZ_gt a : 0 <= a -> a < L5CSA.round_up a.
Proof. intros H. unfold L5CSA.round_up. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma assign_exit (fx : FPState) Rc Mc modelc BX LKc crc Ac dyn sto ws (z : nat) :
  digits_ok s -> (z < length s)%nat -> nth z s 0 <> 48 ->
  binv [] BX Mc modelc LKc crc Ac -> rinv Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (F + 96) -> getr Rc (reg 1) = Z_to_bv 64 585880 -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) ->
  L5.u64_at RSEGS Mc (sb - 176) (F + 112) ->
  L5.big_at RSEGS Mc (F + 96) (L5.BO (fbN dyn neg) (length ws) sto) -> L5C.obj_limbs RSEGS Mc (L5.BO (fbN dyn neg) (length ws) sto) ws ->
  shadow_zero Mc (F + 96) 4 ->
  L5.limbs_val ws = dec s -> length ws = nwords (dec s) ->
  (dyn = false -> (exists v0 v1, sto = L5.BInl v0 v1) /\ BX = [] /\ crc = cr /\ (length s <= 38)%nat) ->
  (dyn = true -> exists q cap, sto = L5.BDyn cap q /\ BX = [(q, 8 * cap)] /\ crc = adebit L cr (vblk (length s)) /\ 8 * cap = vblk (length s) /\
                 (forall V', 0 <= V' < 10 ^ n -> Z.of_nat (nwords V') + 1 <= cap /\ L5CSA.round_up (Z.of_nat (nwords V')) <= cap)) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc ASSIGN Mc modelc) K.
Proof.
  intros DOK Hz NZ BI RI G10 G11 G1 G24 VC176 VB VL VSZ VV VN VI VD.
  destruct (callee_pre [] BX Mc modelc LKc crc Ac ASSIGN_SCR BI ltac:(rewrite ASG_EQ; clear; lia)) as (ASTKc & FFRc & FFRSc & A32c).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  pose proof CTX as CTX'. open_ctx CTX'.
  set (V := dec s) in *.
  assert (VR : 0 <= V < 10 ^ n). { subst V. apply dec_bound. apply all_digits_Forall. exact DOK. }
  assert (VPOS : 0 < V) by (apply (dec_pos_of_nonzero s z DOK Hz NZ)).
  assert (N1 : (1 <= nwords V)%nat) by (apply nwords_pos; exact VPOS).
  assert (NWB : (nwords V <= 260)%nat). { pose proof (nwords_bound V (length s) VR). pose proof (num_words_est_4999 (length s) LEN). clear - H H0. lia. }
  destruct (ek_obj L ar C HI LY HIok LB FF LK cr A sp L5PSB.DETAIL_SCRB M model Mc o HH B7 AOB) as [OEQ OSH].
  assert (BIGc : L5.big_at RSEGS Mc o (L5.BO fb 0 (L5.BInl 0 0))).
  { eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply OEQ. exact Hi. }
  assert (SZc : shadow_zero Mc o 4). { intros j Hj. unfold byte_at. rewrite OSH by exact Hj. apply SZ. exact Hj. }
  assert (AOV : aobj FF' (F + 96) 32).
  { exists (F, 2, sb - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 2) with 256. split. clear; lia. split. clear; lia.
    clear - F8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FBO : Z.testbit fb 0 = false). { destruct BIG as (_ & _ & _ & BT & _). cbn [L5.bo_st L5.bo_fb] in BT. exact BT. }
  assert (FBR : 0 <= fb < 256). { destruct BIG as (_ & X & _). cbn [L5.bo_fb] in X. exact X. }
  apply (Hasg fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac o (F + 96) (sb - 192) 585880 (L5.BO fb 0 (L5.BInl 0 0)) (L5.BO (fbN dyn neg) (length ws) sto) ws B1 B2 HK).
  - rewrite r10. exact G10.
  - rewrite r11. exact G11.
  - cbn [L5.bo_len]. rewrite VN. clear - NWB. lia.
  - intros X. exfalso. unfold L5.bo_dyn in X; cbn [L5.bo_fb] in X. rewrite FBO in X. discriminate X.
  - cbn [L5.bo_len]. intros H3 _. destruct dyn.
    + destruct (VD eq_refl) as (q & cap & _ & _ & -> & E8 & CAPOK). apply (acredit_ok_le L _ (vblk (length s))). exact LY2. exact (proj2 CRD).
      rewrite VN. rewrite <- E8. destruct (CAPOK V VR) as [_ X]. clear - X. lia.
    + exfalso. destruct (VI eq_refl) as ((v0 & v1 & ->) & _). destruct VB as (_ & _ & _ & (_ & _ & _ & X & _)). cbn [L5.bo_len] in X. clear - X H3. lia.
  - rewrite r1. exact G1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact G2'.
  - exact A32c.
  - rewrite r4, G4'. exact G4.
  - exact ASTKc.
  - eapply ffr_le. exact FFRc. clear; lia.
  - exact FFRSc.
  - exact BIGc.
  - apply aobj_cons. exact AOB.
  - exact SZc.
  - exact VB.
  - exact VL.
  - exact AOV.
  - exact VSZ.
  - intros cap q X. discriminate X.
  - cbn [L5.bo_st]. intros cap q E. destruct dyn.
    + destruct (VD eq_refl) as (q' & cap' & E' & -> & _). rewrite E' in E. injection E as <- <-. left; reflexivity.
    + destruct (VI eq_refl) as ((v0 & v1 & E') & _). rewrite E' in E. discriminate E.
  - clear - OF. lia.
  - intros c q c' q' X. discriminate X.
  - intros fx8 R8 M8 model8 g LB8 cr8 LK8 A8 POST RT8 IA8 AM8 LKI8 HH8.
    destruct POST as (RP8 & R8_10 & G). cbn [L5.bo_len L5.bo_fb L5.bo_st] in G.
    (* [comment removed for export] *)
    assert (TAIL : forall (BX8 BXf : list (Z * Z)) (st8 : L5.bstore) (grown : bool) (Wc : list L5.range),
        ri_inv HI (BX8 ++ LB) FF' LK8 cr8 A8 M8 (vml_of model8) ->
        ahpres L ar (BX ++ LB) FF' (sb - 192) ASSIGN_SCR Wc Mc M8 ->
        (forall rr, In rr Wc -> o <= fst rr /\ fst rr + snd rr <= o + 32) ->
        L5.big_at RSEGS M8 o (L5.BO (assign_fb fb (fbN dyn neg) (length ws) grown) (length ws) st8) ->
        L5C.obj_limbs RSEGS M8 (L5.BO (assign_fb fb (fbN dyn neg) (length ws) grown) (length ws) st8) ws ->
        (grown = true <-> (3 <= length ws)%nat) ->
        match st8 with L5.BInl _ _ => BXf = [] | L5.BDyn c8 q8 => c8 = L5CSA.round_up (Z.of_nat (length ws)) /\ BXf = [(q8, 8 * c8)] /\ (3 <= length ws)%nat end ->
        match sto with L5.BInl _ _ => BXf = BX8 | L5.BDyn cap q => In (q, 8 * cap) (BX8 ++ LB) /\ lb_remove q (BX8 ++ LB) = BXf ++ LB end ->
        credit_le (parse_debit L cr (length s)) cr8 ->
        srealizes RSEGS SCFG (cfg (fx:=fx8) R8 585880 M8 model8) K).
    { intros BX8 BXf st8 grown Wc HH8' AH8 HWc OB8 OL8 HG HST HSTO HCR.
      assert (BI8 : binv [(o, 32)] BX8 M8 model8 LK8 cr8 A8).
      { apply (binv_callee [] [(o, 32)] BX BX BX8 Mc modelc LKc crc Ac M8 model8 LK8 cr8 A8 ASSIGN_SCR Wc BI AH8 HH8' AM8 RT8 IA8 LKI8).
        - rewrite ASG_EQ; clear; lia.
        - intros rr Hr. destruct (HWc rr Hr) as [X1 X2]. clear - X2 OR. lia.
        - intros a _ Ho rr Hr X. apply (Ho (o, 32)). left; reflexivity. destruct (HWc rr Hr) as [X1 X2]. unfold L5.in_rng in X |- *. cbn [fst snd]. clear - X X1 X2. lia.
        - intros a _ rr []. }
      assert (RI8 : rinv R8) by (apply (rinv_pres R sp F Rc R8 RI RP8)).
      (* [comment removed for export] *)
      assert (VB8 : L5.big_at RSEGS M8 (F + 96) (L5.BO (fbN dyn neg) (length ws) sto)).
      { eapply L5C.big_at_agree. 4: exact VB. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply (proj1 AH8). split. clear - Hi FR; lia.
        split. apply (fframe_client L ar (BX ++ LB) FF' (sb - 192) ASSIGN_SCR F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Hi; lia.
        intros rr Hr X. destruct (HWc rr Hr) as [X1 X2]. unfold L5.in_rng in X. clear - X X1 X2 Hi OF. lia. }
      (* [comment removed for export] *)
      assert (VC8 : L5.u64_at RSEGS M8 (sb - 176) (F + 112)).
      { eapply L5C.u64_at_agree. 4: exact VC176. 2: clear - SPR; lia. 2: clear - SPR; lia. intros i Hi.
        apply (stack_callee L ar (BX ++ LB) FF' (sb - 192) ASSIGN_SCR Wc Mc M8 i AH8). intros rr Hr. destruct (HWc rr Hr) as [X1 X2]. clear - X2 OR; lia. clear - Hi SPR; lia. clear - Hi SLO SHI SPT SPR; lia. clear - Hi; lia. }
      assert (H24 : getr R8 (reg 24) = Z_to_bv 64 (F + 96)). { rewrite (cs_of_preserved Rc R8 24 RP8) by inl. exact G24. }
      (* [comment removed for export] *)
      destruct (vis_facts [(o, 32)] BX8 M8 model8 LK8 cr8 A8 BI8) as ((W176 & IMGC & CSB & CUAR) & _).
      pose proof BI8 as (C1 & C2 & _).
      pose proof RI8 as (H2' & H8 & H9 & H21 & H26 & H3 & H4').
      destruct SPR as [SPR0 SPR1].
      set (MV8 := mrestrict (ahid A8 model8) M8) in *.
      pose proof (dtS2_conc fx8 R8 MV8 (fun k => match k with 2%nat => sb | 40%nat => F | 58%nat => U R8 1 | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx9 & R9 & M9' & _ & FR9 & _ & (MS9 & KS9 & Q20)).
      assert (E9 : M9' = MV8) by (apply mem_eq_of_agree; intros a Ha; apply FR9). subst M9'.
      apply (apure (BX8 ++ LB) FF' LK8 cr8 A8 M8 model8 fx8 fx9 R8 585880 R9 0x8f09c K C1 C2 MS9).
      intros model9 HH9 AM9 RT9 AH9.
      pose proof (binv_model [(o, 32)] BX8 M8 model8 LK8 cr8 A8 model9 BI8 HH9 AM9 RT9) as BI9.
      assert (RI9 : rinv R9). { apply (rinv_ks R sp F R8 R9 KS_dtS2 RI8 KS9). vm_compute; reflexivity. }
      assert (Q24 : getr R9 (reg 24) = Z_to_bv 64 (F + 96)). { rewrite (KS9 24%nat) by inl. exact H24. }
      apply (exit_path [(o, 32)] BX8 BXf fx9 R9 M8 model9 LK8 cr8 A8 (fbN dyn neg) (length ws) sto 0 BI9 RI9 Q24 Q20 ltac:(clear; lia) VB8
               ltac:(destruct sto; [exact HSTO | exact (conj (proj1 HSTO) (conj (proj2 HSTO) VC8))])).
      intros fxf Rf Mf modelf LKf Af RPf R11f AGf AHf RTf IAf AMf ILKf HHf.
      (* [comment removed for export] *)
      assert (OAG : L5C.agree_on M8 Mf o 32).
      { intros i Hi. apply AGf. clear - Hi OR; lia. apply (obj_client L ar (BXf ++ LB) FF' (sb - 192) OPDEL_SCR o 32 i). apply aobj_cons. exact AOB. exact Hi.
        unfold L5ADH.Wret. clear - Hi OF OFSH OFL. unfold SB in *. lia. }
      apply (KONT fxf Rf Mf modelf (BXf ++ LB) cr8 LKf Af).
      - split. exact RPf. left. split. clear - HVN; lia. split. exact DOK. split. rewrite r11. exact R11f.
        unfold parse_post. fold V. cbv zeta. rewrite <- VN.
        assert (WSE : ws = wlist V (length ws)). { rewrite VN. apply ws_is_wlist. exact (proj1 (proj2 VL)). exact VV. exact VN. }
        rewrite <- WSE.
        assert (RFB : assign_fb fb (fbN dyn neg) (length ws) grown = res_fb fb (length ws) neg).
        { apply assign_fb_resj. exact FBR. exact FB3. rewrite VN; exact N1. exact HG. exact (fbN_land2 dyn neg). }
        rewrite RFB in OB8, OL8.
        exists st8. split. { eapply L5C.big_at_agree. 4: exact OB8. 2: clear - OR; lia. 2: clear - OR; lia. exact OAG. }
        split. { apply (obj_limbs_reflag M8 Mf (res_fb fb (length ws) neg) (res_fb fb (length ws) neg) (length ws) st8 ws OL8).
                 intros c8 q8 E8. subst st8. destruct HST as (EC8 & EBXf & _).
                 destruct (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BXf LB HHf eq_refl (q8, 8 * c8) ltac:(rewrite EBXf; left; reflexivity)) as ((Q0 & _ & _ & _ & Q4 & (_ & Q5 & Q6)) & QFS).
                 cbn [fst snd] in *. unfold BIGSHADOW_LO, BIGSHADOW_HI in Q5.
                 assert (LE8 : Z.of_nat (length ws) <= c8). { rewrite EC8. pose proof (round_upZ_gt (Z.of_nat (length ws)) ltac:(clear; lia)). clear - H. lia. }
                 split. 2:{ clear - Q0 Q6 LE8. lia. }
                 intros i Hi. apply AGf. clear - Hi Q0 Q6 LE8; lia.
                 apply (block_client L ar (BXf ++ LB) FF' (sb - 192) OPDEL_SCR q8 (8 * c8) i). rewrite EBXf. left; reflexivity. clear - Hi LE8; lia.
                 unfold L5ADH.Wret. clear - Hi LE8 Q0 Q5 QFS FS1 FS2 FLP FR F8. unfold SB, FS_BYTES in *. lia. }
        split. { destruct st8 as [u0 u1|c8 q8].
                 - subst BXf. split. destruct OB8 as (_ & _ & _ & (_ & _ & _ & X & _)). cbn [L5.bo_len] in X. exact X. reflexivity.
                 - destruct HST as (EC8 & EBXf & HL3). subst BXf. split. exact HL3. split. exact EC8. split. reflexivity.
                   apply (afresh_of_inv L ar C HI HIok q8 (8 * c8) LB FF LKf cr8 Af Mf _ HHf). }
        split. exact HCR. exact AHf.
      - exact RTf.
      - exact IAf.
      - exact AMf.
      - exact ILKf.
      - exact HHf. }
    destruct g as [|gq gc].
    + (* [comment removed for export] *)
      destruct G as (DD & -> & -> & (st8 & OB8 & OL8 & ST8) & AH8). cbn [L5.bo_data L5.bo_st] in AH8.
      assert (N2 : (length ws <= 2)%nat). { destruct DD as [DD|DD]. exfalso. unfold L5.bo_dyn in DD; cbn [L5.bo_fb] in DD. rewrite FBO in DD. discriminate DD. exact DD. }
      destruct st8 as [u0 u1|c8 q8]. 2:{ exfalso. exact ST8. }
      apply (TAIL BX [] (L5.BInl u0 u1) false _ HH8 AH8).
      * intros rr [<-|[<-|[]]]; cbn [fst snd]; clear - N2; lia.
      * exact OB8.
      * exact OL8.
      * split. intros X; discriminate X. intros X. exfalso. clear - X N2. lia.
      * reflexivity.
      * destruct dyn.
        -- destruct (VD eq_refl) as (q & cap & -> & -> & _). split. left; reflexivity. apply lb_remove_head.
        -- destruct (VI eq_refl) as ((v0 & v1 & ->) & -> & _). reflexivity.
      * apply (credit_after dyn crc). intros E. exact (proj1 (proj2 (proj2 (VI E)))). intros E. destruct (VD E) as (q & cap & _ & _ & X & _). exact X.
    + (* [comment removed for export] *)
      destruct G as (DD & HL3 & EC & ELB & ECR & FRESH & OB8 & OL8 & AH8). subst LB8 cr8.
      destruct dyn. 2:{ exfalso. destruct (VI eq_refl) as ((v0 & v1 & ->) & _). destruct VB as (_ & _ & _ & (_ & _ & _ & X & _)). cbn [L5.bo_len] in X. clear - X HL3. lia. }
      destruct (VD eq_refl) as (q & cap & -> & -> & -> & E8 & CAPOK).
      assert (NEQ : gq <> q).
      { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH8) as WF8. assert (ND : NoDup (map fst ((gq, 8 * gc) :: [(q, 8 * cap)] ++ LB))). { clear - WF8. decompose [and] WF8. assumption. }
        cbn [map fst app] in ND. inversion ND as [|x l NI _]. subst. intros E. apply NI. rewrite E. constructor. }
      apply (TAIL ((gq, 8 * gc) :: [(q, 8 * cap)]) [(gq, 8 * gc)] (L5.BDyn gc gq) true [(o, 32)] HH8 AH8).
      * intros rr [<-|[]]; cbn [fst snd]; clear; lia.
      * exact OB8.
      * exact OL8.
      * split. intros _. exact HL3. intros _. reflexivity.
      * split. exact EC. split. reflexivity. exact HL3.
      * split. right; left; reflexivity. cbn [app]. rewrite lb_remove_skip by exact NEQ. rewrite lb_remove_head. reflexivity.
      * unfold parse_debit. apply adebit_le_amount. exact LY2. rewrite <- E8, EC, VN. destruct (CAPOK V VR) as [_ X]. clear - X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin_path (fx : FPState) Rc Mc modelc BX LKc crc Ac dyn sto ws (z : nat) :
  digits_ok s -> (z < length s)%nat -> nth z s 0 <> 48 ->
  binv [] BX Mc modelc LKc crc Ac -> vobj Mc BX crc dyn sto ws (dec s) -> rinv Rc -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8f078 Mc modelc) K.
Proof.
  intros DOK Hz NZ BI VO RI G24.
  destruct (vis_facts [] BX Mc modelc LKc crc Ac BI) as ((W176 & IMGC & CSB & CUAR) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (_ & _ & FV & SV)).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof VO as (VB & VL & VSZ & VSP & VV & VN & V0 & VI & VD).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  pose proof CTX as CTX'. open_ctx CTX'. destruct SPR as [SPR0 SPR1].
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OWNv as (_ & (S112 & S144 & S152 & S168) & _).
  assert (VSPv : L5.u64_at RSEGS MV (sb - 160) o).
  { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (sb - 160) o ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - SPR1; lia) ltac:(clear - SPR1; lia))). exact (proj1 VSP). }
  assert (VU8 : L5.u8_at RSEGS Mc (F + 96) (fbW dyn)) by exact (proj1 VB).
  assert (VU8v : L5.u8_at RSEGS MV (F + 96) (fbW dyn)).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 96) (fbW dyn) ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact VU8. }
  assert (FWR : 0 <= fbW dyn <= 255 /\ 0 <= fbW dyn < 2 ^ 64) by (pose proof (fbN_range dyn false) as X; unfold fbNj in X; clear - X; lia).
  assert (OR0 : 0 <= o < 2 ^ 64) by (clear - OR; lia).
  destruct (Bool.bool_dec neg true) as [EN|EN].
  - (* [comment removed for export] *)
    rewrite EN in S168.
    pose proof (dtSn_conc fx Rc MV (fun k => match k with 2%nat => sb | 36%nat => o | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fbW dyn | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & sFR & sFZ & (sMS & sKS & sR1 & sR10 & sR11 & sU8 & _)).
    rewrite setbit_fbW in sU8.
    set (Wp := fun a => F + 96 <= a < F + 97).
    apply (apiece L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8f078 R1 ASSIGN M1v Wp K B1 B2 sMS MG1).
    { intros a Ha Hna. apply sFZ. exact Ha. clear - Hna; subst Wp; cbn beta in Hna; lia. }
    { intros a Ha Wa. subst Wp; cbn beta in Wa. split. apply (fframe_client L ar (BX ++ LB) _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia. clear - Wa FR; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    pose proof (binv_piece [] BX Mc modelc LKc crc Ac M1 model1 Wp BI HH1 AM1 RT1 MGM1 FRM1 ltac:(intros a Wa; subst Wp; cbn beta in Wa; right; left; clear - Wa; lia)) as BI1.
    assert (U81 : L5.u8_at RSEGS M1 (F + 96) (fbN dyn true)).
    { apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F + 96) (fbN dyn true) ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
      rewrite VIS1. exact sU8. }
    assert (AG1 : forall a, ~ (F + 96 <= a < F + 97) -> 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Hn Ha. apply FRM1. exact Ha. exact Hn. }
    apply (assign_exit fx1 R1 M1 model1 BX LKc crc Ac dyn sto ws z DOK Hz NZ BI1).
    + apply (rinv_ks R sp F Rc R1 KS_dtSn RI sKS). vm_compute; reflexivity.
    + exact sR10.
    + exact sR11.
    + exact sR1.
    + rewrite (sKS 24%nat) by inl. exact G24.
    + eapply L5C.u64_at_agree. 4: exact (proj2 VSP). 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi. apply AG1. clear - Hi SF; lia. clear - Hi SPR1; lia.
    + rewrite EN. apply (big_at_reflag Mc M1 (F + 96) (fbW dyn) (fbN dyn true) (length ws) sto VB U81).
      * pose proof (fbN_range dyn true). clear - H; lia.
      * rewrite fbN_bit0. symmetry. exact (fbN_bit0 dyn false).
      * intros i Hi. apply AG1. clear - Hi; lia. clear - Hi FR; lia.
      * clear - FR; lia.
      * clear - FR; lia.
    + rewrite EN. apply (obj_limbs_reflag Mc M1 (fbW dyn) (fbN dyn true) (length ws) sto ws VL).
      intros cap q E. destruct dyn. 2:{ exfalso. destruct (VI eq_refl) as ((v0 & v1 & E') & _). rewrite E' in E. discriminate E. }
      destruct (VD eq_refl) as (q' & cap' & E' & EBX & _ & _ & CAPOK). rewrite E' in E. injection E as <- <-.
      destruct (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LB B1 eq_refl (q', 8 * cap') ltac:(rewrite EBX; left; reflexivity)) as ((Q0 & _ & _ & _ & Q4 & (_ & _ & Q6)) & QFS). cbn [fst snd] in *.
      assert (VRc : 0 <= dec s < 10 ^ n). { apply dec_bound. apply all_digits_Forall. exact DOK. }
      destruct (CAPOK (dec s) VRc) as [CK _]. rewrite <- VN in CK.
      split. 2:{ clear - Q0 Q6 CK. lia. }
      intros i Hi. apply AG1. clear - Hi CK QFS FS1 FS2. lia. clear - Hi CK Q0 Q6; lia.
    + intros j Hj. unfold byte_at. rewrite AG1. apply VSZ. exact Hj. unfold S, SB. clear - Hj FR FBIG F8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      unfold S, SB. clear - Hj FR F8. lia.
    + exact VV.
    + exact VN.
    + exact VI.
    + exact VD.
  - (* [comment removed for export] *)
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply Bool.not_true_is_false in EN. rewrite EN in S168.
    pose proof (dtSp_conc fx Rc MV (fun k => match k with 2%nat => sb | 36%nat => o | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & sFR & _ & (sMS & sKS & sR1 & sR10 & sR11)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply sFR). subst M1v.
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8f078 R1 ASSIGN K B1 B2 sMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (binv_model [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (assign_exit fx1 R1 Mc model1 BX LKc crc Ac dyn sto ws z DOK Hz NZ BI1).
    + apply (rinv_ks R sp F Rc R1 KS_dtSp RI sKS). vm_compute; reflexivity.
    + exact sR10.
    + exact sR11.
    + exact sR1.
    + rewrite (sKS 24%nat) by inl. exact G24.
    + exact (proj2 VSP).
    + rewrite EN. exact VB.
    + rewrite EN. exact VL.
    + exact VSZ.
    + exact VV.
    + exact VN.
    + exact VI.
    + exact VD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digit_loop (z : nat) : (z < length s)%nat -> nth z s 0 <> 48 ->
  forall (rem j idx : nat) (fx : FPState) Rc Mc modelc BX LKc crc Ac dyn sto ws,
  (j + rem = length s)%nat -> (1 <= rem)%nat -> (idx <= j)%nat -> digits_ok (firstn j s) ->
  binv [] BX Mc modelc LKc crc Ac -> vobj Mc BX crc dyn sto ws (dec (firstn j s)) -> rinv Rc -> lregs Rc j rem idx ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8f024 Mc modelc) K.
Proof.
  intros Hz NZ. induction rem as [|rem IH]; intros j idx fx Rc Mc modelc BX LKc crc Ac dyn sto ws EJ HR HIJ DOKj BI VO RI LR. { exfalso. clear - HR. lia. }
  assert (JL : (j < length s)%nat) by (clear - EJ; lia).
  pose proof CTX as CTX'. open_ctx CTX'. destruct SPR as [SPR0 SPR1].
  set (c := nth j s 0).
  assert (CB : 0 <= c < 256). { subst c. rewrite Forall_forall in BR. apply BR. apply nth_In. exact JL. }
  assert (HREM : (Datatypes.S rem <= 4999)%nat) by (clear - EJ LEN; lia).
  assert (HIDX : (idx <= 4999)%nat) by (clear - EJ LEN HIJ; lia).
  destruct (Z_lt_le_dec c 48) as [LT|GE]. { apply (err_path fx Rc Mc modelc BX LKc crc Ac dyn sto ws _ j (Datatypes.S rem) idx JL (or_introl LT) BI VO RI LR HREM HIDX). }
  destruct (Z_lt_le_dec 57 c) as [GT|LE]. { apply (err_path fx Rc Mc modelc BX LKc crc Ac dyn sto ws _ j (Datatypes.S rem) idx JL (or_intror GT) BI VO RI LR HREM HIDX). }
  (* [comment removed for export] *)
  assert (DIG : 48 <= c <= 57) by (clear - GE LE; lia).
  set (V := dec (firstn j s)) in *.
  pose proof (firstn_digits_bound s j ltac:(clear - JL; lia) DOKj) as VBj. fold V in VBj.
  pose proof (pow10_le (Datatypes.S j) (length s) ltac:(clear - JL; lia)) as PJ. rewrite Nat2Z.inj_succ, Z.pow_succ_r in PJ by (clear; lia).
  assert (V'EQ : dec (firstn (Datatypes.S j) s) = 10 * V + (c - 48)) by (subst V c; apply dec_firstn_S; exact JL).
  assert (VR : 0 <= V < 10 ^ n) by (clear - VBj PJ; lia).
  assert (B10 : 0 <= 10 * V < 10 ^ n) by (clear - VBj PJ; lia).
  assert (B10d : 0 <= 10 * V + (c - 48) < 10 ^ n) by (clear - VBj PJ DIG; lia).
  destruct LR as (L10 & L18 & L19 & L20 & L22 & L23 & L24 & L27).
  destruct (src_facts BX Mc modelc LKc crc Ac BI) as (BYv & ACCv).
  destruct (vis_facts [] BX Mc modelc LKc crc Ac BI) as ((W176 & IMGC & CSB & CUAR) & _).
  pose proof BI as (B1 & B2 & _).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  set (cur := p + Z.of_nat j) in *.
  set (GG := 18446744073709551615 - p) in *.
  assert (CR : 4096 <= cur /\ cur + 1 <= p + n) by (subst cur; clear - PRG JL; lia).
  assert (Bc : L5.u8_at RSEGS MV cur c) by (apply BYv; exact JL).
  destruct (L5ACHK0.chk_8ecd0 fx Rc MV cur ltac:(unfold S, SB; exact L10) L23 ltac:(clear - CR PRG; lia) ltac:(eapply aacc_sub; [exact ACCv | clear - CR; lia | clear - CR; lia]))
    as (R1 & MS1 & K1).
  assert (RI1 : rinv R1). { apply (rinv_keep R sp F Rc R1 RI). intros k Hk. unfold RIDX in Hk. cbn [In] in Hk. apply K1; clear - Hk; lia. }
  pose proof RI1 as (J2 & J8 & J9 & J21 & J26 & _ & _).
  assert (J18 : getr R1 (reg 18) = Z_to_bv 64 GG) by (rewrite K1 by (clear; lia); exact L18).
  assert (J19 : getr R1 (reg 19) = Z_to_bv 64 9) by (rewrite K1 by (clear; lia); exact L19).
  assert (J20 : getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat idx)) by (rewrite K1 by (clear; lia); exact L20).
  assert (J22 : getr R1 (reg 22) = Z_to_bv 64 cur) by (rewrite K1 by (clear; lia); exact L22).
  assert (J23 : getr R1 (reg 23) = Z_to_bv 64 cur) by (rewrite K1 by (clear; lia); exact L23).
  assert (J24 : getr R1 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite K1 by (clear; lia); exact L24).
  assert (J27 : getr R1 (reg 27) = Z_to_bv 64 (Z.of_nat (Datatypes.S rem))) by (rewrite K1 by (clear; lia); exact L27).
  assert (HV55 : 4096 <= cur <= 140737488355327) by (clear - CR PRG; lia).
  assert (HV57 : 0 <= Z.of_nat (Datatypes.S rem) < 2 ^ 64) by (clear - HREM; lia).
  assert (HV64 : 0 <= GG < 2 ^ 64) by (subst GG; clear - PRG; lia).
  assert (HV65 : 0 <= Z.of_nat idx < 2 ^ 64) by (clear - HIDX; lia).
  pose proof (dtD1g_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 57%nat => Z.of_nat (Datatypes.S rem) | 58%nat => U R1 1 | 59%nat => U R1 10 | 60%nat => U R1 11
                                              | 64%nat => GG | 65%nat => Z.of_nat idx | _ => 0 end)) as P.
  cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2' & _ & FR2 & _ & (MS2 & KS2 & Q1 & Q10 & Q11 & Q25)).
  assert (E2 : M2' = MV) by (apply mem_eq_of_agree; intros a Ha; apply FR2). subst M2'.
  apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8f024 R2 MUL10 K B1 B2 (msteps_trans _ _ _ _ MS1 MS2)).
  intros model2' HH2' AM2' RT2' AH2'.
  pose proof (binv_model [] BX Mc modelc LKc crc Ac model2' BI HH2' AM2' RT2') as BI2.
  assert (RI2 : rinv R2). { apply (rinv_ks R sp F R1 R2 KS_dtD1g RI1 KS2). vm_compute; reflexivity. }
  assert (S18 : getr R2 (reg 18) = Z_to_bv 64 GG) by (rewrite (KS2 18%nat) by inl; exact J18).
  assert (S19 : getr R2 (reg 19) = Z_to_bv 64 9) by (rewrite (KS2 19%nat) by inl; exact J19).
  assert (S20 : getr R2 (reg 20) = Z_to_bv 64 (Z.of_nat idx)) by (rewrite (KS2 20%nat) by inl; exact J20).
  assert (S22 : getr R2 (reg 22) = Z_to_bv 64 cur) by (rewrite (KS2 22%nat) by inl; exact J22).
  assert (S23 : getr R2 (reg 23) = Z_to_bv 64 cur) by (rewrite (KS2 23%nat) by inl; exact J23).
  assert (S24 : getr R2 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (KS2 24%nat) by inl; exact J24).
  assert (S27 : getr R2 (reg 27) = Z_to_bv 64 (Z.of_nat (Datatypes.S rem))) by (rewrite (KS2 27%nat) by inl; exact J27).
  clear W176 IMGC CSB CUAR BYv ACCv Bc MS1 MS2 FR2 K1 KS2 J2 J8 J9 J21 J26 J18 J19 J20 J22 J23 J24 J27 B1 B2 G2' G8 G9 G21 G26 G3 G4'.
  clear MV.
  pose proof VO as (_ & _ & _ & _ & VV & _).
  (* [comment removed for export] *)
  apply (arith_step MUL10 L5ASB.MUL10_SCRB 4 (fun ws _ => 10 * L5.limbs_val ws) 10 Hmul fx2 R2 Mc model2' BX LKc crc Ac dyn sto ws V 585796
           ltac:(rewrite MUL_EQ; clear; lia) ltac:(reflexivity) ltac:(clear; lia) BI2 VO RI2 VR ltac:(cbn beta; rewrite VV; exact B10) Q10 Q11 Q1 ltac:(split; [clear; lia | reflexivity])).
  cbn beta. rewrite VV.
  intros fx3 R3 M3 model3 BX3 LK3 cr3 A3 dyn3 sto3 ws3 BI3 VO3 RP3.
  assert (RI3 : rinv R3) by (apply (rinv_pres R sp F R2 R3 RI2 RP3)).
  assert (T18 : getr R3 (reg 18) = Z_to_bv 64 GG) by (rewrite (cs_of_preserved R2 R3 18 RP3) by inl; exact S18).
  assert (T19 : getr R3 (reg 19) = Z_to_bv 64 9) by (rewrite (cs_of_preserved R2 R3 19 RP3) by inl; exact S19).
  assert (T20 : getr R3 (reg 20) = Z_to_bv 64 (Z.of_nat idx)) by (rewrite (cs_of_preserved R2 R3 20 RP3) by inl; exact S20).
  assert (T22 : getr R3 (reg 22) = Z_to_bv 64 cur) by (rewrite (cs_of_preserved R2 R3 22 RP3) by inl; exact S22).
  assert (T23 : getr R3 (reg 23) = Z_to_bv 64 cur) by (rewrite (cs_of_preserved R2 R3 23 RP3) by inl; exact S23).
  assert (T24 : getr R3 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R2 R3 24 RP3) by inl; exact S24).
  assert (T25 : getr R3 (reg 25) = Z_to_bv 64 (c - 48)) by (rewrite (cs_of_preserved R2 R3 25 RP3) by inl; exact Q25).
  assert (T27 : getr R3 (reg 27) = Z_to_bv 64 (Z.of_nat (Datatypes.S rem))) by (rewrite (cs_of_preserved R2 R3 27 RP3) by inl; exact S27).
  clear S18 S19 S20 S22 S23 S24 S27 Q1 Q10 Q11 Q25 BI2 RI2 VO VV BI RI.
  (* [comment removed for export] *)
  destruct (vis_facts [] BX3 M3 model3 LK3 cr3 A3 BI3) as ((W176 & IMGC & CSB & CUAR) & _).
  pose proof BI3 as (B1 & B2 & _).
  pose proof RI3 as (G2' & G8 & G9 & G21 & G26 & _ & _).
  set (MV3 := mrestrict (ahid A3 model3) M3) in *.
  assert (HV56 : 0 <= c - 48 < 2 ^ 64) by (clear - DIG; lia).
  pose proof (dtD2_conc fx3 R3 MV3 (fun k => match k with 2%nat => sb | 40%nat => F | 56%nat => c - 48 | 58%nat => U R3 1 | _ => 0 end)) as P.
  cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx4 & R4 & M4' & _ & FR4 & _ & (MS4 & KS4 & Q1 & Q10 & Q11)).
  assert (E4 : M4' = MV3) by (apply mem_eq_of_agree; intros a Ha; apply FR4). subst M4'.
  apply (apure (BX3 ++ LB) FF' LK3 cr3 A3 M3 model3 fx3 fx4 R3 585796 R4 ADDD K B1 B2 MS4).
  intros model4 HH4 AM4 RT4 AH4.
  pose proof (binv_model [] BX3 M3 model3 LK3 cr3 A3 model4 BI3 HH4 AM4 RT4) as BI4.
  assert (RI4 : rinv R4). { apply (rinv_ks R sp F R3 R4 KS_dtD2 RI3 KS4). vm_compute; reflexivity. }
  assert (S18 : getr R4 (reg 18) = Z_to_bv 64 GG) by (rewrite (KS4 18%nat) by inl; exact T18).
  assert (S19 : getr R4 (reg 19) = Z_to_bv 64 9) by (rewrite (KS4 19%nat) by inl; exact T19).
  assert (S20 : getr R4 (reg 20) = Z_to_bv 64 (Z.of_nat idx)) by (rewrite (KS4 20%nat) by inl; exact T20).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 cur) by (rewrite (KS4 22%nat) by inl; exact T22).
  assert (S23 : getr R4 (reg 23) = Z_to_bv 64 cur) by (rewrite (KS4 23%nat) by inl; exact T23).
  assert (S24 : getr R4 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (KS4 24%nat) by inl; exact T24).
  assert (S27 : getr R4 (reg 27) = Z_to_bv 64 (Z.of_nat (Datatypes.S rem))) by (rewrite (KS4 27%nat) by inl; exact T27).
  clear W176 IMGC CSB CUAR MS4 FR4 KS4 B1 B2 G2' G8 G9 G21 G26 T18 T19 T20 T22 T23 T24 T25 T27. clear MV3.
  pose proof VO3 as (_ & _ & _ & _ & VV3 & _).
  (* [comment removed for export] *)
  apply (arith_step ADDD L5ASB.ADDD_SCRB 5 (fun ws d => L5.limbs_val ws + d) (c - 48) (Hadd (c - 48) ltac:(clear - DIG; lia)) fx4 R4 M3 model4 BX3 LK3 cr3 A3 dyn3 sto3 ws3 (10 * V) 585808
           ltac:(rewrite ADD_EQ; clear; lia) ltac:(reflexivity) ltac:(clear; lia) BI4 VO3 RI4 B10 ltac:(cbn beta; rewrite VV3; exact B10d) Q10 Q11 Q1 ltac:(split; [clear; lia | reflexivity])).
  cbn beta. rewrite VV3. rewrite <- V'EQ.
  intros fx5 R5 M5 model5 BX5 LK5 cr5 A5 dyn5 sto5 ws5 BI5 VO5 RP5.
  assert (RI5 : rinv R5) by (apply (rinv_pres R sp F R4 R5 RI4 RP5)).
  assert (T18 : getr R5 (reg 18) = Z_to_bv 64 GG) by (rewrite (cs_of_preserved R4 R5 18 RP5) by inl; exact S18).
  assert (T19 : getr R5 (reg 19) = Z_to_bv 64 9) by (rewrite (cs_of_preserved R4 R5 19 RP5) by inl; exact S19).
  assert (T20 : getr R5 (reg 20) = Z_to_bv 64 (Z.of_nat idx)) by (rewrite (cs_of_preserved R4 R5 20 RP5) by inl; exact S20).
  assert (T22 : getr R5 (reg 22) = Z_to_bv 64 cur) by (rewrite (cs_of_preserved R4 R5 22 RP5) by inl; exact S22).
  assert (T23 : getr R5 (reg 23) = Z_to_bv 64 cur) by (rewrite (cs_of_preserved R4 R5 23 RP5) by inl; exact S23).
  assert (T24 : getr R5 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R4 R5 24 RP5) by inl; exact S24).
  assert (T27 : getr R5 (reg 27) = Z_to_bv 64 (Z.of_nat (Datatypes.S rem))) by (rewrite (cs_of_preserved R4 R5 27 RP5) by inl; exact S27).
  clear S18 S19 S20 S22 S23 S24 S27 Q1 Q10 Q11 BI4 RI4 VO3 VV3 BI3 RI3.
  (* [comment removed for export] *)
  destruct (vis_facts [] BX5 M5 model5 LK5 cr5 A5 BI5) as ((W176 & IMGC & CSB & CUAR) & _).
  pose proof BI5 as (B1 & B2 & _).
  pose proof RI5 as (G2' & G8 & G9 & G21 & G26 & _ & _).
  set (MV5 := mrestrict (ahid A5 model5) M5) in *.
  assert (DOKS : digits_ok (firstn (Datatypes.S j) s)) by (apply digits_ok_S; [exact JL | exact DOKj | exact DIG]).
  assert (HV55' : 4096 <= cur <= 140737488355326) by (clear - CR PRG; lia).
  assert (GK1 : 9223372036854775808 <= GG <= 18446744073709551615) by (subst GG; clear - PRG; lia).
  assert (GK2 : 0 <= Z.of_nat idx <= 67108863) by (clear - HIDX; lia).
  destruct rem as [|rem'].
  - (* [comment removed for export] *)
    change (Z.of_nat 1) with 1 in T27.
    pose proof (dtD3l_conc fx5 R5 MV5 (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 58%nat => U R5 1 | 64%nat => GG | 65%nat => Z.of_nat idx | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx6 & R6 & M6' & _ & FR6 & _ & (MS6 & KS6 & _)).
    assert (E6 : M6' = MV5) by (apply mem_eq_of_agree; intros a Ha; apply FR6). subst M6'.
    apply (apure (BX5 ++ LB) FF' LK5 cr5 A5 M5 model5 fx5 fx6 R5 585808 R6 0x8f078 K B1 B2 MS6).
    intros model6 HH6 AM6 RT6 AH6.
    pose proof (binv_model [] BX5 M5 model5 LK5 cr5 A5 model6 BI5 HH6 AM6 RT6) as BI6.
    assert (EJS : Datatypes.S j = length s) by (clear - EJ; lia).
    rewrite EJS in VO5, DOKS. rewrite dec_firstn_all in VO5. rewrite firstn_all in DOKS.
    apply (fin_path fx6 R6 M5 model6 BX5 LK5 cr5 A5 dyn5 sto5 ws5 z DOKS Hz NZ BI6 VO5).
    apply (rinv_ks R sp F R5 R6 KS_dtD3l RI5 KS6). vm_compute; reflexivity.
    rewrite (KS6 24%nat) by inl. exact T24.
  - (* [comment removed for export] *)
    assert (HV57' : 2 <= Z.of_nat (Datatypes.S (Datatypes.S rem')) <= 67108863) by (clear - HREM; lia).
    pose proof (dtD3m_conc fx5 R5 MV5 (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 57%nat => Z.of_nat (Datatypes.S (Datatypes.S rem')) | 58%nat => U R5 1
                                                 | 64%nat => GG | 65%nat => Z.of_nat idx | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx6 & R6 & M6' & _ & FR6 & _ & (MS6 & KS6 & Q10 & Q20 & Q22 & Q23 & Q27)).
    assert (E6 : M6' = MV5) by (apply mem_eq_of_agree; intros a Ha; apply FR6). subst M6'.
    apply (apure (BX5 ++ LB) FF' LK5 cr5 A5 M5 model5 fx5 fx6 R5 585808 R6 0x8f024 K B1 B2 MS6).
    intros model6 HH6 AM6 RT6 AH6.
    pose proof (binv_model [] BX5 M5 model5 LK5 cr5 A5 model6 BI5 HH6 AM6 RT6) as BI6.
    apply (IH (Datatypes.S j) (Datatypes.S idx) fx6 R6 M5 model6 BX5 LK5 cr5 A5 dyn5 sto5 ws5 ltac:(clear - EJ; lia) ltac:(clear; lia) ltac:(clear - HIJ; lia) DOKS BI6 VO5).
    + apply (rinv_ks R sp F R5 R6 KS_dtD3m RI5 KS6). vm_compute; reflexivity.
    + unfold lregs. replace (p + Z.of_nat (Datatypes.S j)) with (cur + 1) by (subst cur; clear; lia).
      split. exact Q10. split. { rewrite (KS6 18%nat) by inl. exact T18. } split. { rewrite (KS6 19%nat) by inl. exact T19. }
      split. { rewrite Q20. f_equal. clear; lia. } split. exact Q22. split. exact Q23. split. { rewrite (KS6 24%nat) by inl. exact T24. }
      rewrite Q27. f_equal. clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main_path (fx : FPState) Rc Mc modelc LKc Ac (z : nat) :
  (z < length s)%nat -> nth z s 0 <> 48 ->
  binv [] [] Mc modelc LKc cr Ac -> rinv Rc ->
  getr Rc (reg 11) = Z_to_bv 64 (p + Z.of_nat z) -> getr Rc (reg 22) = Z_to_bv 64 p -> getr Rc (reg 23) = Z_to_bv 64 n -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) ->
  L5.u64_at RSEGS Mc (sb - 136) (p + n) -> L5.u64_at RSEGS Mc (sb - 160) o -> L5.u8_at RSEGS Mc (F + 96) jv ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8eee8 Mc modelc) K.
Proof.
  intros Hz NZ BI RI G11 G22 G23 G24 ENDC OSP JVB.
  assert (FW0 : Z.testbit (fbW false) 0 = false) by exact (fbN_bit0 false false).
  assert (FWR0 : 0 <= fbW false < 256) by (pose proof (fbN_range false false) as X; unfold fbNj in X; clear - X; lia).
  destruct (vis_facts [] [] Mc modelc LKc cr Ac BI) as ((W176 & IMGC & CSB & CUAR) & _ & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (_ & _ & FV & SV)).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  pose proof CTX as CTX'. open_ctx CTX'. destruct SPR as [SPR0 SPR1].
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  set (est := Z.of_nat (num_words_est (length s))).
  assert (ESTR : 1 <= est <= 260).
  { subst est. pose proof (num_words_est_4999 (length s) LEN). split. 2: clear - H; lia.
    destruct (Nat.lt_ge_cases (length s) 10) as [LT|GE]. rewrite est_small by (clear - LT; lia). clear; lia.
    rewrite <- est_eval by exact GE. apply Z.div_le_lower_bound. clear; lia. pose proof (Z.div_pos (3402 * n) 1024 ltac:(clear; lia) ltac:(clear; lia)). clear - H0. lia. }
  assert (OR0 : 0 <= o < 2 ^ 64) by (clear - OR; lia).
  assert (HZ : 0 <= Z.of_nat z < n) by (clear - Hz; lia).
  assert (HV55 : 4096 <= p + Z.of_nat z <= 140737479966720 /\ 0 <= p + Z.of_nat z < 2 ^ 64) by (clear - PRG HZ; lia). destruct HV55 as [HV55 HV55r].
  assert (HV57 : 1 <= n - Z.of_nat z <= 67108863 /\ 0 <= n - Z.of_nat z < 2 ^ 64) by (clear - HVN HZ; lia). destruct HV57 as [HV57 HV57r].
  assert (NR : 0 <= n < 2 ^ 64) by (clear - HVN; lia).
  assert (VISa : forall a k, (sb - 192 <= a /\ a + k <= sb + 16) \/ (F <= a /\ a + k <= F + 256) -> avis (ahid Ac modelc) a k).
  { intros a k [X|X]. eapply avis_sub. exact SV. clear - X; lia. clear - X; lia. eapply avis_sub. exact FV. clear - X; lia. clear - X; lia. }
  assert (ENDv : L5.u64_at RSEGS MV (sb - 136) (p + Z.of_nat z + (n - Z.of_nat z))).
  { replace (p + Z.of_nat z + (n - Z.of_nat z)) with (p + n) by (clear; lia).
    apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (sb - 136) (p + n) (VISa (sb - 136) 8 ltac:(left; clear; lia)) ltac:(clear - SPR1; lia) ltac:(clear - SPR1; lia))). exact ENDC. }
  assert (JVv : L5.u8_at RSEGS MV (F + 96) jv).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 96) jv (VISa (F + 96) 1 ltac:(right; clear; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact JVB. }
  assert (JVR' : 0 <= jv <= 255 /\ 0 <= jv < 2 ^ 64) by (clear - JVR; lia). destruct JVR' as [JVR1 JVR2].
  (* [comment removed for export] *)
  assert (EX : exists fx1 R1 M1v, msteps RSEGS (st fx Rc 0x8eee8 MV) (st fx1 R1 0x5e7f0 M1v) /\ mem_grows MV M1v
             /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F + 96 <= i < F + 96 + 1) -> ~ (F / 8 + 2147450892 <= i < F / 8 + 2147450892 + 4) ->
                   M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
             /\ rinv R1 /\ getr R1 (reg 22) = Z_to_bv 64 p /\ getr R1 (reg 23) = Z_to_bv 64 n /\ getr R1 (reg 24) = Z_to_bv 64 (F + 96)
             /\ getr R1 (reg 1) = Z_to_bv 64 585700 /\ getr R1 (reg 10) = Z_to_bv 64 (F + 104) /\ getr R1 (reg 11) = Z_to_bv 64 0 /\ getr R1 (reg 12) = Z_to_bv 64 16
             /\ getr R1 (reg 18) = Z_to_bv 64 (F + 112) /\ getr R1 (reg 25) = Z_to_bv 64 est
             /\ L5.u8_at RSEGS M1v (F + 96) (fbW false)
             /\ (L5.u8_at RSEGS M1v (F / 8 + 2147450895) 0 /\ L5.u8_at RSEGS M1v (F / 8 + 2147450894) 0 /\ L5.u8_at RSEGS M1v (F / 8 + 2147450893) 0 /\ L5.u8_at RSEGS M1v (F / 8 + 2147450892) 0)).
  { destruct (Z_le_gt_dec n 9) as [SM|BG].
    - assert (HV34 : 1 <= n <= 9) by (clear - HVN SM; lia).
      pose proof (dtQS_conc fx Rc MV (fun k => match k with 2%nat => sb | 34%nat => n | 40%nat => F | 41%nat => fl | 55%nat => p + Z.of_nat z | 57%nat => n - Z.of_nat z | 58%nat => U Rc 1 | 60%nat => jv | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & qR12 & qR18 & qR25 & qU8 & qS3 & qS2 & qS1 & qS0 & _)).
      exists fx1, R1, M1v. split. exact qMS. split. exact MG1. split. exact qFZ.
      split. apply (rinv_ks R sp F Rc R1 KS_dtQS RI qKS). vm_compute; reflexivity.
      split. rewrite (qKS 22%nat) by inl. exact G22. split. rewrite (qKS 23%nat) by inl. exact G23. split. rewrite (qKS 24%nat) by inl. exact G24.
      split. exact qR1. split. exact qR10. split. exact qR11. split. exact qR12. split. exact qR18.
      split. { rewrite qR25. f_equal. subst est. symmetry. apply est_small. clear - SM; lia. }
      split. { rewrite <- (fbWj_div4 jv JVR). exact qU8. } split. exact qS3. split. exact qS2. split. exact qS1. exact qS0.
    - assert (HV34 : 10 <= n <= 67108863) by (clear - HVN BG; lia).
      pose proof (dtQL_conc fx Rc MV (fun k => match k with 2%nat => sb | 34%nat => n | 40%nat => F | 41%nat => fl | 55%nat => p + Z.of_nat z | 57%nat => n - Z.of_nat z | 58%nat => U Rc 1 | 60%nat => jv | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & qR12 & qR18 & qR25 & qU8 & qS3 & qS2 & qS1 & qS0 & _)).
      exists fx1, R1, M1v. split. exact qMS. split. exact MG1. split. exact qFZ.
      split. apply (rinv_ks R sp F Rc R1 KS_dtQL RI qKS). vm_compute; reflexivity.
      split. rewrite (qKS 22%nat) by inl. exact G22. split. rewrite (qKS 23%nat) by inl. exact G23. split. rewrite (qKS 24%nat) by inl. exact G24.
      split. exact qR1. split. exact qR10. split. exact qR11. split. exact qR12. split. exact qR18.
      split. { rewrite qR25. f_equal. subst est. apply est_eval. clear - BG; lia. }
      split. { rewrite <- (fbWj_div4 jv JVR). exact qU8. } split. exact qS3. split. exact qS2. split. exact qS1. exact qS0. }
  destruct EX as (fx1 & R1 & M1v & qMS & MG1 & qFZ & RI1 & Q22 & Q23 & Q24 & qR1 & qR10 & qR11 & qR12 & qR18 & qR25 & qU8 & (qS3 & qS2 & qS1 & qS0)).
  set (Wp := fun a => F + 96 <= a < F + 97 \/ F / 8 + SB + 12 <= a < F / 8 + SB + 16).
  apply (apiece L ar C HI LY HIok ([] ++ LB) FF' LKc cr Ac Mc modelc fx fx1 Rc 0x8eee8 R1 0x5e7f0 M1v Wp K B1 B2 qMS MG1).
  { intros a Ha Hna. apply qFZ. exact Ha. all: clear - Hna; subst Wp; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - split. apply (fframe_client L ar _ _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia. clear - Wa FR; lia.
    - split. apply (fframe_shadow_client L ar _ _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. rewrite (proj1 FQ31). clear - Wa. unfold SB in *. lia.
      clear - Wa FR; unfold SB in Wa; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  pose proof (binv_piece [] [] Mc modelc LKc cr Ac M1 model1 Wp BI HH1 AM1 RT1 MGM1 FRM1
                ltac:(intros a Wa; subst Wp; cbn beta in Wa; destruct Wa as [Wa|Wa]; [right; left; clear - Wa; lia | right; right; clear - Wa; lia])) as BI1.
  pose proof BI1 as (C1 & C2 & _ & _ & _ & C6 & _).
  (* [comment removed for export] *)
  assert (VU1 : L5.u8_at RSEGS M1 (F + 96) (fbW false)).
  { apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F + 96) (fbW false) (VISa (F + 96) 1 ltac:(right; clear; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). rewrite VIS1. exact qU8. }
  assert (VSP1 : L5.u64_at RSEGS M1 (sb - 160) o).
  { eapply L5C.u64_at_agree. 4: exact OSP. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi. apply FRM1. clear - Hi SPR1; lia. subst Wp; cbn beta. clear - Hi SF SFSH; unfold SB in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH12 : (F + 96) / 8 = F / 8 + 12 /\ (F + 96) mod 8 = 0) by (clear - F8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (vis_facts [] [] M1 model1 LKc cr Ac BI1) as (_ & (_ & _ & FSD1) & _ & _).
  assert (SHV1 : forall a, F / 8 + SB <= a < F / 8 + SB + 32 -> ahid Ac model1 (Z_to_bv 64 a) = false).
  { intros a Ha. pose proof (vis_pack L ar C HI LY HIok _ FF' LKc cr Ac M1 model1 HH1) as (_ & _ & _ & _ & _ & _ & VFSSH & _).
    replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH (F / 8 + SB) 32). 2: clear - Ha; lia.
    intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VZ1 : shadow_zero M1 (F + 96) 4).
  { intros j Hj. unfold byte_at, S. rewrite (proj1 FSH12).
    assert (X : L5.u8_at RSEGS M1v (F / 8 + 12 + SB + j) 0).
    { assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|[J|J]]]; subst j; gmem. }
    rewrite EQ1. apply (byte_of_u8 M1v _ 0 X). right. clear - Hj FR F8; unfold SB; lia. clear - Hj FR F8; unfold SB; lia.
    rewrite <- AH1. apply SHV1. clear - Hj; lia. }
  (* [comment removed for export] *)
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  pose proof RI1 as (H2' & H8 & H9 & H21 & H26 & H3 & H4').
  assert (U25 : bv_unsigned (getr R1 2%bv) = sb - 192). { rewrite r2, H2'. apply L5.unsigned_lit. clear - SPR1; lia. }
  eapply (MS fx1 R1 M1 model1 ([] ++ LB) FF' LKc cr Ac (F + 104) 0 16 K); clear MS.
  { split. exact C1. split. exact (proj1 C2). split. exact (proj2 C2).
    split. rewrite r10. exact qR10. split. rewrite r12. exact qR12. split. clear; lia.
    split. rewrite r4, H4'. exact G4. split. rewrite r1, qR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U25. replace (sb - 192) with (sp - 208) by (clear; lia).
             apply (astack_ok_of_astk L ar C LY M1 M1 sp L5PSB.DETAIL_SCRB 208 2560 C6 (mem_grows_refl M1)). clear; lia. clear; lia. rewrite DSCR_EQ; clear; lia.
             replace (sp - 208) with (sb - 192) by (clear; lia). exact SA16. }
    split. { eapply aacc_of_zero. exact VZ1. exact (proj2 FSH12). clear - FR; lia. clear; lia. clear; lia. }
    split. { intros i Hi. rewrite U25. apply (fframe_client L ar _ _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Hi; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M1 (F + 104) 16). 2: clear - FR; lia. 2: clear - FR; lia. 2: exact Hi. 2: exact Hm.
             pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & WF1 & _).
             pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WF1 _ (or_introl eq_refl))))))) as FD. cbn [ff_addr ff_class fst snd] in FD. change (ff_bytes 2) with 256 in FD.
             intros j Hj. replace (F + 104 + j) with (F + (104 + j)) by (clear; lia). apply FD. clear - Hj; lia. }
    split. exact HK. apply (app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ (F + 104) 16 C1). clear - FS1; lia. pose proof FS2 as FS2'. change (ff_bytes 2) with 256 in FS2'. clear - FS2'; lia. }
  { rewrite r11. exact qR11. }
  intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U25 in PRES6, SDEF6. rewrite r1, qR1.
  assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 C2). }
  assert (BI6 : binv [] [] M6 model6 LKc cr Ac).
  { apply (binv_mem [] [] M1 model1 LKc cr Ac M6 model6 (fun a => F + 104 <= a < F + 104 + 16) BI1 HH6 (conj Hh6 MI6) RT6 PRES6).
    - intros a Ha. apply SDEF6. clear - Ha; lia.
    - intros a Da. destruct (ZB (a - (F + 104)) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (F + 104 + (a - (F + 104))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    - intros a. destruct (rng_dec a (F + 104) (F + 104 + 16)); [left|right]; assumption.
    - intros a Da. clear - Da; lia. }
  assert (RI6 : rinv R6) by (apply (rinv_pres R sp F R1 R6 RI1 RP6)).
  assert (FCL6 : forall a, F + 32 <= a < F + 248 -> aclient L ar ([] ++ LB) FF' (sb - 192) 2560 a).
  { intros a Ha. apply (fframe_client L ar _ _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Ha; lia. }
  assert (VU6 : L5.u8_at RSEGS M6 (F + 96) (fbW false)).
  { eapply L5C.u8_at_agree. 4: exact VU1. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply PRES6. clear - Hi FR; lia. apply FCL6. clear - Hi; lia. clear - Hi; lia. }
  assert (Z6 : L5KA.zeros_at M6 (F + 104) 16). { intros i Hi. destruct (ZB i Hi) as (v & Ev & Bv). subst v. exact Bv. }
  assert (VW8 : L5.u64_at RSEGS M6 (F + 104) 0 /\ L5.u64_at RSEGS M6 (F + 112) 0).
  { split.
    - apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia.
    - apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia. }
  assert (VZ6 : shadow_zero M6 (F + 96) 4).
  { intros j Hj. unfold byte_at. rewrite PRES6. apply VZ1. exact Hj. unfold S, SB. rewrite (proj1 FSH12). clear - Hj FR; lia.
    apply (fframe_shadow_client L ar _ _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. rewrite (proj1 FSH12), (proj1 FQ31). clear - Hj; lia.
    unfold S. rewrite (proj1 FSH12). clear - Hj FR FBIG; unfold SB; lia. }
  assert (VSP6 : L5.u64_at RSEGS M6 (sb - 160) o).
  { eapply L5C.u64_at_agree. 4: exact VSP1. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi. apply PRES6. clear - Hi SPR1; lia.
    apply stack_client. clear - Hi SLO SHI SPT; lia. clear - Hi; lia. clear - Hi FR FCEIL SLO; lia. }
  (* [comment removed for export] *)
  assert (S18 : getr R6 (reg 18) = Z_to_bv 64 (F + 112)) by (rewrite (cs_of_preserved R1 R6 18 RP6) by inl; exact qR18).
  assert (S22 : getr R6 (reg 22) = Z_to_bv 64 p) by (rewrite (cs_of_preserved R1 R6 22 RP6) by inl; exact Q22).
  assert (S23 : getr R6 (reg 23) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R1 R6 23 RP6) by inl; exact Q23).
  assert (S24 : getr R6 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R1 R6 24 RP6) by inl; exact Q24).
  assert (S25 : getr R6 (reg 25) = Z_to_bv 64 est) by (rewrite (cs_of_preserved R1 R6 25 RP6) by inl; exact qR25).
  clear W176 IMGC CSB CUAR FDEFv FWv FSHWv FLCv FLWv FV SV qMS MG1 qFZ qU8 qS3 qS2 qS1 qS0 VISa FRM1 EQ1 VIS1 MGM1 SHV1 VZ1 VU1 VSP1 PRES6 SDEF6 ZB Z6 FCL6 ENDv JVv ENDC OSP JVB
        G2' G8 G9 G21 G26 G3 G4' H2' H8 H9 H21 H26 H3 H4' G11 G22 G23 G24 Q22 Q23 Q24 qR1 qR10 qR11 qR12 qR18 qR25 B1 B2 B3 B4 B5 B6 B7 B8 B9 C1 C2 C6 FSD1 BI BI1 RI RI1.
  clear MV.
  destruct (vis_facts [] [] M6 model6 LKc cr Ac BI6) as ((W176 & IMGC & CSB & CUAR) & _ & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (_ & _ & FV & SV)).
  pose proof BI6 as (B1 & B2 & _).
  pose proof RI6 as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  set (MV6 := mrestrict (ahid Ac model6) M6) in *.
  assert (ESTR' : 0 <= est < 2 ^ 64) by (clear - ESTR; lia).
  pose proof (dtR2_conc fx1 R6 MV6 (fun k => match k with 2%nat => sb | 40%nat => F | 41%nat => fl | 58%nat => U R6 1 | 63%nat => est | _ => 0 end)) as P.
  cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx7 & R7 & M7v & MG7 & FR7 & FZ7 & (MS7 & KS7 & Q1 & Q10 & Q11 & rC120 & rC176 & _)).
  set (Wq := fun a => sb - 176 <= a < sb - 168 \/ F + 120 <= a < F + 128).
  apply (apiece L ar C HI LY HIok ([] ++ LB) FF' LKc cr Ac M6 model6 fx1 fx7 R6 585700 R7 RESERVE M7v Wq K B1 B2 MS7 MG7).
  { intros a Ha Hna. apply FZ7. exact Ha. all: clear - Hna; subst Wq; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst Wq; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
    - split. apply (fframe_client L ar _ _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia. clear - Wa FR; lia. }
  intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
  pose proof (binv_piece [] [] M6 model6 LKc cr Ac M7 model7 Wq BI6 HH7 AM7 RT7 MGM7 FRM7
                ltac:(intros a Wa; subst Wq; cbn beta in Wa; destruct Wa as [Wa|Wa]; [left; left; exact Wa | right; left; clear - Wa; lia])) as BI7.
  assert (VISb : forall a k, (sb - 192 <= a /\ a + k <= sb + 16) \/ (F <= a /\ a + k <= F + 256) -> avis (ahid Ac model6) a k).
  { intros a k [X|X]. eapply avis_sub. exact SV. clear - X; lia. clear - X; lia. eapply avis_sub. exact FV. clear - X; lia. clear - X; lia. }
  assert (VC7 : L5.u64_at RSEGS M7 (sb - 176) (F + 112)).
  { apply (proj1 (u64_at_vis (ahid Ac model6) M7 (sb - 176) (F + 112) (VISb (sb - 176) 8 ltac:(left; clear; lia)) ltac:(clear - SPR1; lia) ltac:(clear - SPR1; lia))). rewrite VIS7. exact rC176. }
  assert (VD7 : L5.u64_at RSEGS M7 (F + 120) 0).
  { apply (proj1 (u64_at_vis (ahid Ac model6) M7 (F + 120) 0 (VISb (F + 120) 8 ltac:(right; clear; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). rewrite VIS7. exact rC120. }
  assert (AG7 : forall i, 0 <= i < 2 ^ 64 -> ~ (sb - 176 <= i < sb - 168) -> ~ (F + 120 <= i < F + 128) -> M7 (Z_to_bv 64 i) = M6 (Z_to_bv 64 i)).
  { intros i Hi N1 N2. apply FRM7. exact Hi. subst Wq; cbn beta. clear - N1 N2; lia. }
  assert (VBIG7 : L5.big_at RSEGS M7 (F + 96) (L5.BO (fbW false) 0 (L5.BInl 0 0))).
  { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. change (Z.of_nat 0) with 0.
    split. { eapply L5C.u8_at_agree. 4: exact VU6. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply AG7. clear - Hi FR; lia. clear - Hi SF; lia. clear - Hi; lia. }
    split. exact FWR0.
    split. { replace (F + 96 + 8) with (F + 104) by (clear; lia). eapply L5C.u64_at_agree. 4: exact (proj1 VW8). 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply AG7. clear - Hi FR; lia. clear - Hi SF; lia. clear - Hi; lia. }
    split. exact FW0.
    split. { replace (F + 96 + 16) with (F + 112) by (clear; lia). eapply L5C.u64_at_agree. 4: exact (proj2 VW8). 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply AG7. clear - Hi FR; lia. clear - Hi SF; lia. clear - Hi; lia. }
    split. { replace (F + 96 + 24) with (F + 120) by (clear; lia). exact VD7. }
    split. clear; lia. split; clear; lia. }
  assert (VZ7 : shadow_zero M7 (F + 96) 4).
  { intros j Hj. unfold byte_at. rewrite AG7. apply VZ6. exact Hj. unfold S, SB. rewrite (proj1 FSH12). clear - Hj FR; lia.
    unfold S, SB. rewrite (proj1 FSH12). clear - Hj SFSH; unfold SB in SFSH; lia. unfold S, SB. rewrite (proj1 FSH12). clear - Hj FR FBIG; lia. }
  assert (VSP7 : L5.u64_at RSEGS M7 (sb - 160) o).
  { eapply L5C.u64_at_agree. 4: exact VSP6. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi. apply AG7. clear - Hi SPR1; lia. clear - Hi; lia. clear - Hi SF; lia. }
  assert (RI7 : rinv R7). { apply (rinv_ks R sp F R6 R7 KS_dtR2 RI6 KS7). vm_compute; reflexivity. }
  assert (T22 : getr R7 (reg 22) = Z_to_bv 64 p) by (rewrite (KS7 22%nat) by inl; exact S22).
  assert (T23 : getr R7 (reg 23) = Z_to_bv 64 n) by (rewrite (KS7 23%nat) by inl; exact S23).
  assert (T24 : getr R7 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (KS7 24%nat) by inl; exact S24).
  destruct (callee_pre [] [] M7 model7 LKc cr Ac RESERVE_SCR BI7 ltac:(rewrite RSV_EQ; clear; lia)) as (ASTKc & FFRc & FFRSc & A32c).
  assert (AOV : aobj FF' (F + 96) 32).
  { exists (F, 2, sb - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 2) with 256. split. clear; lia. split. clear; lia. exact (proj2 FSH12). }
  pose proof RI7 as (I2 & _ & _ & _ & _ & _ & I4).
  pose proof BI7 as (D1' & D2' & _).
  (* [comment removed for export] *)
  apply (Hres fx7 R7 M7 model7 K ([] ++ LB) FF' LKc cr Ac (F + 96) est (sb - 192) 585728 (L5.BO (fbW false) 0 (L5.BInl 0 0)) D1' D2' HK).
  - rewrite r10. exact Q10.
  - rewrite r11. exact Q11.
  - clear - ESTR. lia.
  - intros X. exfalso. unfold L5.bo_dyn in X; cbn [L5.bo_fb] in X. rewrite FW0 in X. discriminate X.
  - intros _ H3. assert (M39 : (39 <= length s)%nat). { destruct (Nat.lt_ge_cases (length s) 39) as [LT|GE]. 2: exact GE. exfalso. pose proof (nwe_le2 (length s) ltac:(clear - LT; lia)). subst est. clear - H H3. lia. }
    replace (8 * round_up est) with (vblk (length s)). exact (proj1 CRD). unfold vblk. replace (length s <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; exact M39). reflexivity.
  - rewrite r1. exact Q1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact I2.
  - exact A32c.
  - rewrite r4, I4. exact G4.
  - exact ASTKc.
  - eapply ffr_le. exact FFRc. clear; lia.
  - exact FFRSc.
  - exact VBIG7.
  - exact AOV.
  - exact VZ7.
  - intros fx8 R8 M8 model8 g LB8 cr8 LK8 A8 POST RT8 IA8 AM8 LKI8 HH8.
    destruct POST as (RP8 & G).
    assert (RI8 : rinv R8) by (apply (rinv_pres R sp F R7 R8 RI7 RP8)).
    assert (U22 : getr R8 (reg 22) = Z_to_bv 64 p) by (rewrite (cs_of_preserved R7 R8 22 RP8) by inl; exact T22).
    assert (U23 : getr R8 (reg 23) = Z_to_bv 64 n) by (rewrite (cs_of_preserved R7 R8 23 RP8) by inl; exact T23).
    assert (U24 : getr R8 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R7 R8 24 RP8) by inl; exact T24).
    (* [comment removed for export] *)
    assert (LOOP : forall BX8 dyn8 sto8, binv [] BX8 M8 model8 LK8 cr8 A8 -> vobj M8 BX8 cr8 dyn8 sto8 [] 0 ->
               srealizes RSEGS SCFG (cfg (fx:=fx8) R8 585728 M8 model8) K).
    { intros BX8 dyn8 sto8 BI8 VO8.
      destruct (vis_facts [] BX8 M8 model8 LK8 cr8 A8 BI8) as ((X176 & XMGC & XSB & XUAR) & _).
      pose proof BI8 as (D1 & D2 & _).
      pose proof RI8 as (J2 & J8 & J9 & J21 & J26 & _ & _).
      set (MV8 := mrestrict (ahid A8 model8) M8) in *.
      assert (HVN' : 1 <= n <= 67108863) by (clear - HVN; lia).
      assert (PR0 : 0 <= p < 2 ^ 64) by (clear - PRG; lia).
      pose proof (dtR3_conc fx8 R8 MV8 (fun k => match k with 2%nat => sb | 33%nat => p | 34%nat => n | 40%nat => F | 58%nat => U R8 1 | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx9 & R9 & M9' & _ & FR9 & _ & (MS9 & KS9 & W18 & W19 & W20 & W23 & W27)).
      assert (E9 : M9' = MV8) by (apply mem_eq_of_agree; intros a Ha; apply FR9). subst M9'.
      rewrite zbv_notp in W18.
      (* [comment removed for export] *)
      assert (RI9 : rinv R9). { apply (rinv_ks R sp F R8 R9 KS_dtR3 RI8 KS9). vm_compute; reflexivity. }
      pose proof RI9 as (K2 & K8 & K9 & K21 & K26 & _ & _).
      assert (K24 : getr R9 (reg 24) = Z_to_bv 64 (F + 96)) by (rewrite (KS9 24%nat) by inl; exact U24).
      assert (K22 : getr R9 (reg 22) = Z_to_bv 64 p) by (rewrite (KS9 22%nat) by inl; exact U22).
      assert (GK1 : 9223372036854775808 <= 18446744073709551615 - p <= 18446744073709551615 /\ 0 <= 18446744073709551615 - p < 2 ^ 64) by (clear - PRG; lia). destruct GK1 as [GK1 GK1r].
      assert (HV55p : 4096 <= p <= 140737488355326) by (clear - PRG; lia).
      pose proof (dtR4_conc fx9 R9 MV8 (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => p | 58%nat => U R9 1 | 64%nat => 18446744073709551615 - p | 65%nat => 0 | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx10 & R10 & M10' & _ & FR10 & _ & (MS10 & KS10 & X10)).
      assert (E10 : M10' = MV8) by (apply mem_eq_of_agree; intros a Ha; apply FR10). subst M10'.
      apply (apure (BX8 ++ LB) FF' LK8 cr8 A8 M8 model8 fx8 fx10 R8 585728 R10 0x8f024 K D1 D2 (msteps_trans _ _ _ _ MS9 MS10)).
      intros model9 HH9 AM9 RT9 AH9.
      pose proof (binv_model [] BX8 M8 model8 LK8 cr8 A8 model9 BI8 HH9 AM9 RT9) as BI9.
      apply (digit_loop z Hz NZ (length s) 0%nat 0%nat fx10 R10 M8 model9 BX8 LK8 cr8 A8 dyn8 sto8 [] ltac:(clear; lia) ltac:(clear - HVN; lia) ltac:(clear; lia) ltac:(constructor) BI9 VO8).
      - apply (rinv_ks R sp F R9 R10 KS_dtR4 RI9 KS10). vm_compute; reflexivity.
      - unfold lregs. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. split. exact X10. split. { rewrite (KS10 18%nat) by inl. exact W18. }
        split. { rewrite (KS10 19%nat) by inl. exact W19. } split. { rewrite (KS10 20%nat) by inl. exact W20. }
        split. { rewrite (KS10 22%nat) by inl. exact K22. } split. { rewrite (KS10 23%nat) by inl. exact W23. }
        split. { rewrite (KS10 24%nat) by inl. exact K24. } rewrite (KS10 27%nat) by inl. exact W27. }
    destruct g as [|gq gc].
    + (* [comment removed for export] *)
      destruct G as (DD & -> & -> & OB8 & AH8).
      assert (E2 : est <= 2). { destruct DD as [DD|DD]. exfalso. unfold L5.bo_dyn in DD; cbn [L5.bo_fb] in DD. rewrite FW0 in DD. discriminate DD. exact DD. }
      apply (LOOP [] false (L5.BInl 0 0)).
      * apply (binv_callee [] [] [] [] [] M7 model7 LKc cr Ac M8 model8 LK8 cr A8 RESERVE_SCR [] BI7 AH8 HH8 AM8 RT8 IA8 LKI8).
        -- rewrite RSV_EQ; clear; lia.
        -- intros rr [].
        -- intros a _ _ rr [].
        -- intros a X. exact X.
      * unfold vobj, vb. cbn [length]. split. exact OB8. split. { unfold L5C.obj_limbs; cbn. repeat split. constructor. }
        split. { intros j Hj. unfold byte_at. rewrite (proj1 AH8). apply VZ7. exact Hj. split. unfold S, SB. rewrite (proj1 FSH12). clear - Hj FR; lia.
                 split. apply (fframe_shadow_client L ar _ _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. rewrite (proj1 FSH12), (proj1 FQ31). clear - Hj; lia.
                 intros rr []. }
        split. { split.
                 - eapply L5C.u64_at_agree. 4: exact VSP7. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi.
                   apply (stack_callee L ar _ FF' (sb - 192) RESERVE_SCR [] M7 M8 i AH8). intros rr []. clear - Hi SPR1; lia. clear - Hi SLO SHI SPT; lia. clear - Hi; lia.
                 - eapply L5C.u64_at_agree. 4: exact VC7. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi.
                   apply (stack_callee L ar _ FF' (sb - 192) RESERVE_SCR [] M7 M8 i AH8). intros rr []. clear - Hi SPR1; lia. clear - Hi SLO SHI SPT; lia. clear - Hi; lia. }
        split. reflexivity. split. reflexivity. split. clear; lia.
        split. { intros _. split. exists 0, 0; reflexivity. split. reflexivity. split. reflexivity.
                 destruct (Nat.lt_ge_cases (length s) 39) as [LT|GE]. clear - LT; lia. exfalso. pose proof (nwe_ge3 (length s) GE). subst est. clear - H E2. lia. }
        intros X. discriminate X.
    + (* [comment removed for export] *)
      destruct G as (DD & H3 & EC & -> & -> & FRESH & _ & OB8 & AH8). cbn [L5.bo_fb L5.bo_len] in OB8. rewrite (fbWj_lor1 jv JVR) in OB8.
      assert (M39 : (39 <= length s)%nat). { destruct (Nat.lt_ge_cases (length s) 39) as [LT|GE]. 2: exact GE. exfalso. pose proof (nwe_le2 (length s) ltac:(clear - LT; lia)). subst est. clear - H H3. lia. }
      assert (VBK : vblk (length s) = 8 * gc). { unfold vblk. replace (length s <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; exact M39). rewrite EC. reflexivity. }
      assert (HW : forall rr, In rr [(F + 96, 32)] -> fst rr + snd rr <= ahl_ceil ar /\ forall a, L5.in_rng rr a -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32)).
      { intros rr [<-|[]]; cbn [fst snd]; unfold L5.in_rng; cbn [fst snd].
        split. clear - FCEIL; lia. intros a Ha. split. apply (NCF a). left; clear - Ha; lia. clear - Ha FR FBIG. unfold SB. lia. }
      apply (LOOP [(gq, 8 * gc)] true (L5.BDyn gc gq)).
      * apply (binv_callee [] [] [] [] [(gq, 8 * gc)] M7 model7 LKc cr Ac M8 model8 LK8 (adebit L cr (8 * gc)) A8 RESERVE_SCR [(F + 96, 32)] BI7 AH8 HH8 AM8 RT8 IA8 LKI8).
        -- rewrite RSV_EQ; clear; lia.
        -- intros rr Hr. exact (proj1 (HW rr Hr)).
        -- intros a Hc _ rr Hr X. exact (proj1 (proj2 (HW rr Hr) a X) Hc).
        -- intros a X. exact X.
      * unfold vobj, vb. cbn [length]. split. exact OB8.
        split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st length]. split. reflexivity. split. constructor. intros i Hi. exfalso. cbn in Hi. clear - Hi. lia. }
        split. { intros j Hj. unfold byte_at. rewrite (proj1 AH8). apply VZ7. exact Hj. split. unfold S, SB. rewrite (proj1 FSH12). clear - Hj FR; lia.
                 split. apply (fframe_shadow_client L ar _ _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. rewrite (proj1 FSH12), (proj1 FQ31). clear - Hj; lia.
                 intros rr Hr X. destruct (HW rr Hr) as (_ & HX). destruct (HX _ X) as (_ & NS). apply NS. unfold S. rewrite (proj1 FSH12). clear - Hj. lia. }
        split. { split.
                 - eapply L5C.u64_at_agree. 4: exact VSP7. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi.
                   apply (stack_callee L ar _ FF' (sb - 192) RESERVE_SCR _ M7 M8 i AH8). intros rr Hr. exact (proj1 (HW rr Hr)). clear - Hi SPR1; lia. clear - Hi SLO SHI SPT; lia. clear - Hi; lia.
                 - eapply L5C.u64_at_agree. 4: exact VC7. 2: clear - SPR1; lia. 2: clear - SPR1; lia. intros i Hi.
                   apply (stack_callee L ar _ FF' (sb - 192) RESERVE_SCR _ M7 M8 i AH8). intros rr Hr. exact (proj1 (HW rr Hr)). clear - Hi SPR1; lia. clear - Hi SLO SHI SPT; lia. clear - Hi; lia. }
        split. reflexivity. split. reflexivity. split. clear; lia.
        split. intros X; discriminate X.
        intros _. exists gq, gc. split. reflexivity. split. reflexivity. split. rewrite VBK; reflexivity. split. symmetry; exact VBK.
        intros V' HV'. rewrite EC. subst est. rewrite round_up_Z. split. apply cap_reserve_ok. exact HV'.
        rewrite <- round_up_Z. apply round_upZ_mono. pose proof (nwords_bound V' (length s) HV'). clear - H. lia.
Qed.

End MAIN.
End WithIface.
End SCFG_1.
End L5ADM.
