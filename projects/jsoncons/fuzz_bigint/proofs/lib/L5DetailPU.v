(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_201fc_21084 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU BigZskipUb0
     BigModel BigFactsBase BigFactsOps BigFactsRun BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseArith L5ParseKit L5ParseSpecsU L5DetailAU ZskipAllU L5DetailZU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5DETPU.
Import L5CSU L5PSU L5DAU L5DETZU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition DRET : Z := 0x21080.      (* [comment removed for export] *)
Definition ZHEAD : Z := 0x20f00.     (* [comment removed for export] *)
Definition ZBR : Z := 0x20f14.       (* [comment removed for export] *)
Definition DL_HEAD : Z := 0x20fd4.
Definition DL_EXIT : Z := 0x2100c.
Definition DL_ERR : Z := 0x21084.
Ltac uscr := unfold DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_detail fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R DRET M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M DRET W_21080 r F_21080 eq_refl D_21080 H1 Hr He). Qed.

Lemma br_20ddc fx R M :
  msteps RSEGS (st fx R ZBR M) (st fx R (if branch_taken BC_EQ (getr R (reg 10)) (getr R (reg 8)) then 0x20f28 else 0x20f18) M).
Proof.
  rewrite <- L5CoreKit.L5K.rl10, <- L5CoreKit.L5K.rl8.
  apply (@BDQU.br_site fx M R ZBR 0x20f28 (0x20f14%bv : word) _ BC_EQ 10 8 _ eq_refl F_20f14 eq_refl D_20f14). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land3_bits fb : 0 <= fb -> Z.land fb 3 = 0 -> Z.testbit fb 0 = false /\ Z.testbit fb 1 = false.
Proof.
  intros Hfb H. split.
  - apply (f_equal (fun x => Z.testbit x 0)) in H. rewrite Z.land_spec in H. change (Z.testbit 3 0) with true in H. rewrite Bool.andb_true_r in H. rewrite H. reflexivity.
  - apply (f_equal (fun x => Z.testbit x 1)) in H. rewrite Z.land_spec in H. change (Z.testbit 3 1) with true in H. rewrite Bool.andb_true_r in H. rewrite H. reflexivity.
Qed.
Lemma lit_of_word (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma wrange (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. Qed.
Lemma ra_ok_lit z : 0 <= z < 2 ^ 47 -> z mod 2 = 0 -> L5.ra_ok z.
Proof. intros; split; assumption. Qed.

Lemma mod16_8 sp k : sp mod 16 = 0 -> (sp + 8 * k) mod 8 = 0.
Proof.
  intros H. apply Z.mod_divide in H. 2: lia. destruct H as [q Hq]. subst sp.
  replace (q * 16 + 8 * k) with ((q * 2 + k) * 8) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma big_at_zero M a : L5.u8_at RSEGS M a 0 -> L5.u64_at RSEGS M (a + 8) 0 -> L5.u64_at RSEGS M (a + 16) 0 -> L5.u64_at RSEGS M (a + 24) 0 ->
  L5.big_at RSEGS M a (L5.BO 0 0 (L5.BInl 0 0)).
Proof. intros H0 H8 H16 H24. unfold L5.big_at; cbn. repeat split; try assumption; try lia; reflexivity. Qed.
Lemma obj_limbs_zero M : L5C.obj_limbs RSEGS M (L5.BO 0 0 (L5.BInl 0 0)) [].
Proof. unfold L5C.obj_limbs; cbn. repeat split. constructor. Qed.

(* [comment removed for export] *)
Lemma limbs_val_val ws : L5.limbs_val ws = val ws.
Proof. induction ws as [|w t IH]. reflexivity. cbn [L5.limbs_val val]. rewrite IH, M_val. reflexivity. Qed.
Lemma words_ok_of_Forall ws : Forall (fun w => 0 <= w < 2 ^ 64) ws -> words_ok ws.
Proof. intros H. unfold words_ok. eapply Forall_impl. 2: exact H. intros a Ha. cbn beta in Ha. unfold wordZ. rewrite M_val. lia. Qed.
Lemma reduced_ws_of ws : L5CSU.reduced ws -> reduced_ws ws.
Proof. intros H. apply reduced_ws_intro. intros NE. destruct H as [H|H]. congruence. unfold nth_w. exact H. Qed.
Lemma length_nwords ws V : Forall (fun w => 0 <= w < 2 ^ 64) ws -> L5CSU.reduced ws -> L5.limbs_val ws = V -> length ws = nwords V.
Proof.
  intros HF HR HV. rewrite <- HV, limbs_val_val. apply reduced_length_nwords. apply words_ok_of_Forall. exact HF. apply reduced_ws_of. exact HR.
Qed.
Lemma limbs_val_nonneg ws : Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= L5.limbs_val ws.
Proof. induction ws as [|w t IH]; intros H. cbn; lia. inversion H; subst. cbn [L5.limbs_val]. specialize (IH ltac:(assumption)). lia. Qed.
(* [comment removed for export] *)
Lemma nwords_le2 V (n : nat) : (n <= 38)%nat -> 0 <= V < 10 ^ Z.of_nat n -> (nwords V <= 2)%nat.
Proof.
  intros Hn HV. apply (proj2 (nwords_le_iff V 2 ltac:(lia))). rewrite Mpow_nat. change (2 ^ (64 * Z.of_nat 2)) with (2 ^ 128).
  eapply Z.lt_le_trans. apply (proj2 HV). eapply Z.le_trans. apply (Z.pow_le_mono_r 10 (Z.of_nat n) 38). lia. lia.
  cbn. lia.
Qed.
(* [comment removed for export] *)
Lemma cap_reserve_ok V (n : nat) : 0 <= V < 10 ^ Z.of_nat n -> Z.of_nat (nwords V) + 1 <= Z.of_nat (BigModel.round_up (num_words_est n)).
Proof.
  intros HV. pose proof (nwords_bound V n HV). pose proof (round_up_ge_S (num_words_est n)). lia.
Qed.

(* [comment removed for export] *)
Lemma segs_below : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) 0x92000) RSEGS = true.
Proof. vm_compute. reflexivity. Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Hres : reserve_spec L HI.
Hypothesis Hmul : mul10_spec L HI.
Hypothesis Hadd : addd_spec L HI.
Hypothesis Hasg : assign_spec L HI.
Hypothesis Hdel : opdel_sized_spec L HI.
(* [comment removed for export] *)
Hypothesis KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.

Lemma credit_le_refl c : credit_le c c. Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold credit_le. lia. Qed.
Lemma credit_le_trans a b c : credit_le a b -> credit_le b c -> credit_le a c. Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold credit_le. lia. Qed.
Lemma credit_le_debit c n : 0 <= n -> credit_le (debit L c n) c.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. intros Hn. unfold credit_le, debit. cbn. lia. Qed.
Lemma debit_mono c c' n : credit_le c c' -> credit_le (debit L c n) (debit L c' n).
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold credit_le, debit. cbn. lia. Qed.
Lemma debit_le_amount c n n' : n' <= n -> credit_le (debit L c n) (debit L c n').
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold credit_le, debit. cbn. lia. Qed.
Lemma vblk_pos m : 0 <= vblk m.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold vblk. destruct (m <? 39)%nat. lia. pose proof (round_up_ge_S (num_words_est m)). lia. Qed.
Lemma parse_debit_le c m : credit_le (parse_debit L c m) c.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold parse_debit. eapply credit_le_trans. apply credit_le_debit. apply vblk_pos. apply credit_le_debit. apply vblk_pos. Qed.

Lemma IMGLO : 0 <= hl_img_lo L <= hl_img_hi L. Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma IMGHI : hl_img_hi L <= 0x7fff7f800000. Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. rewrite (ly_img_hi L LY). lia. Qed.
Lemma ERR : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L. Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. rewrite (ly_errno L LY), (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma SEGSB : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) (hl_img_hi L)) RSEGS = true.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. rewrite (ly_img_hi L LY). exact segs_below. Qed.
Lemma ERRNO_LO : hl_errno L + 4 <= hl_img_hi L. Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. rewrite (ly_errno L LY), (ly_img_hi L LY). lia. Qed.

(* [comment removed for export] *)
Lemma fb3_facts fb : 0 <= fb < 256 -> Z.land fb 3 = 0 ->
  Z.land fb 253 = fb /\ Z.land (Z.lor fb 1) 253 = fb + 1 /\ Z.lor fb 0 = fb /\ Z.lor fb 2 = fb + 2 /\ Z.lor (fb + 1) 0 = fb + 1 /\ Z.lor (fb + 1) 2 = fb + 1 + 2
  /\ Z.testbit fb 0 = false /\ Z.testbit (fb + 1) 0 = true /\ Z.testbit (fb + 2) 0 = false /\ Z.testbit (fb + 1 + 2) 0 = true /\ Z.lor fb 1 = fb + 1.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS.
  intros Hfb H3.
  pose proof (L5CoreKit.L5K.byte_cases (fun fb => implb (Z.land fb 3 =? 0)
     ((Z.land fb 253 =? fb) && (Z.land (Z.lor fb 1) 253 =? fb + 1) && (Z.lor fb 0 =? fb) && (Z.lor fb 2 =? fb + 2) && (Z.lor (fb + 1) 0 =? fb + 1) && (Z.lor (fb + 1) 2 =? fb + 1 + 2)
      && negb (Z.testbit fb 0) && Z.testbit (fb + 1) 0 && negb (Z.testbit (fb + 2) 0) && Z.testbit (fb + 1 + 2) 0 && (Z.lor fb 1 =? fb + 1))%bool)
     ltac:(vm_compute; reflexivity) fb Hfb) as X. cbn beta in X.
  rewrite (proj2 (Z.eqb_eq _ _) H3) in X. cbn [implb] in X.
  repeat (apply andb_prop in X; destruct X as [X ?Y]).
  repeat split; try (apply Z.eqb_eq; assumption).
  - destruct (Z.testbit fb 0); [discriminate|reflexivity].
  - assumption.
  - destruct (Z.testbit (fb + 2) 0); [discriminate|reflexivity].
  - assumption.
Qed.

(* [comment removed for export] *)
Definition fbW (dyn : bool) : Z := if dyn then 1 else 0.
Definition fbN (dyn ng : bool) : Z := if ng then Z.lor (fbW dyn) 2 else fbW dyn.
Lemma fbN_land1 dyn ng : Z.land (fbN dyn ng) 1 = fbW dyn.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. destruct dyn, ng; reflexivity. Qed.
Lemma fbN_land2 dyn ng : Z.land (fbN dyn ng) 2 = if ng then 2 else 0.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. destruct dyn, ng; reflexivity. Qed.
Lemma fbN_range dyn ng : 0 <= fbN dyn ng <= 3.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. destruct dyn, ng; vm_compute; split; discriminate. Qed.
Lemma fbN_bit0 dyn ng : Z.testbit (fbN dyn ng) 0 = dyn.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. destruct dyn, ng; reflexivity. Qed.

Lemma assign_fb_res fb dyn ng (n : nat) (grown : bool) :
  0 <= fb < 256 -> Z.land fb 3 = 0 -> (1 <= n)%nat -> (grown = true <-> (3 <= n)%nat) ->
  assign_fb fb (fbN dyn ng) n grown = res_fb fb n ng.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS.
  intros Hfb H3 Hn HG. destruct (fb3_facts fb Hfb H3) as (F1 & F2 & F3 & F4 & F5 & F6 & _ & _ & _ & _ & F11).
  unfold assign_fb, res_fb. replace (Nat.eqb n 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (1 <=? n)%nat with true by (symmetry; apply Nat.leb_le; lia). rewrite fbN_land2.
  destruct grown.
  - replace (3 <=? n)%nat with true by (symmetry; apply Nat.leb_le; apply HG; reflexivity). rewrite F2. destruct ng; cbn [andb]; lia.
  - replace (3 <=? n)%nat with false. 2: { symmetry. apply Nat.leb_gt. destruct (Nat.lt_ge_cases n 3). lia. exfalso. pose proof (proj2 HG ltac:(lia)). discriminate. }
    rewrite F1. destruct ng; cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
Lemma big_at_reflag M M' a f f' (n : nat) st :
  L5.big_at RSEGS M a (L5.BO f n st) -> L5.u8_at RSEGS M' a f' -> 0 <= f' < 256 -> Z.testbit f' 0 = Z.testbit f 0 ->
  L5C.agree_on M M' (a + 8) 24 -> 0 <= a -> a + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M' a (L5.BO f' n st).
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS.
  intros (B1 & B2 & B3 & B4) U Hf' T0 AG Ha Hn. unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in B3, B4.
  split. exact U. split. exact Hf'.
  split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact B3. }
  rewrite T0. destruct st as [v0 v1|cap q].
  - destruct B4 as (C1 & C2 & C3 & C4). split. exact C1.
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C2. }
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C3. }
    exact C4.
  - destruct B4 as (C1 & C2 & C3 & C4). split. exact C1.
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C2. }
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C3. }
    exact C4.
Qed.

(* [comment removed for export] *)
Lemma obj_limbs_reflag M M' f f' (n : nat) st ws :
  L5C.obj_limbs RSEGS M (L5.BO f n st) ws ->
  (forall cap q, st = L5.BDyn cap q -> L5C.agree_on M M' q (8 * Z.of_nat (length ws)) /\ 0 <= q /\ q + 8 * Z.of_nat (length ws) <= 2 ^ 64) ->
  L5C.obj_limbs RSEGS M' (L5.BO f' n st) ws.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS.
  intros (L1 & L2 & L3) HQ. unfold L5C.obj_limbs; cbn [L5.bo_len L5.bo_st]. cbn [L5.bo_len L5.bo_st] in L1, L3.
  split. exact L1. split. exact L2. destruct st as [v0 v1|cap q]. exact L3.
  destruct (HQ cap q eq_refl) as (AG & Q0 & Q1). eapply (L5C.limbs_at_agree RSEGS M M'). exact AG. exact Q0. exact Q1. exact L3.
Qed.

(* [comment removed for export] *)
Lemma hpres_defined LBx spx scr W Ma Mb : L5C.hpres L LBx spx scr W Ma Mb -> L5.defined Mb (spx - scr) scr.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. intros HPx. exact (proj1 (proj2 HPx)). Qed.
Lemma credit_ok_le c n n' : credit_ok L c n -> n' <= n -> credit_ok L c n'.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS. unfold credit_ok. lia. Qed.
Lemma round_up_Z (n : nat) : round_up (Z.of_nat n) = Z.of_nat (BigModel.round_up n).
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS.
  unfold round_up. rewrite BigFactsOps.round_up_eq. rewrite Nat2Z.inj_mul, Nat2Z.inj_add, Nat2Z.inj_div. lia.
Qed.
(* [comment removed for export] *)
Lemma ws_is_wlist ws V : Forall (fun w => 0 <= w < 2 ^ 64) ws -> L5.limbs_val ws = V -> length ws = nwords V -> ws = wlist V (nwords V).
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS.
  intros HF HV HL. rewrite <- HL. rewrite <- HV, limbs_val_val. symmetry. apply wlist_val. apply words_ok_of_Forall. exact HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CTX.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit).
Variables (p o sp r fb : Z) (neg : bool) (ds : list Z).
Let m : Z := Z.of_nat (length ds).
Let negz : Z := if neg then 1 else 0.
Let o' : Z := sp - 112.                      (* [comment removed for export] *)
Hypothesis HK0 : K [].
Hypothesis MOK0 : model_ok model0.
Hypothesis RA : L5.ra_ok r.
Hypothesis H0_1 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis H0_2 : getr R0 (reg 2) = Z_to_bv 64 sp.
Hypothesis H0_4 : getr R0 (reg 4) = Z_to_bv 64 TP.
Hypothesis Hlen : (1 <= length ds <= 4999)%nat.
Hypothesis A16 : sp mod 16 = 0.
Hypothesis SLO : hl_sptop L - 2 ^ 23 + DETAIL_SCR <= sp.    (* [comment removed for export] *)
Hypothesis SHI : sp <= hl_sptop L.
Hypothesis STOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.   (* [comment removed for export] *)
Hypothesis Hfb : 0 <= fb < 256.
Hypothesis Hfb3 : Z.land fb 3 = 0.
Hypothesis Ao : o mod 8 = 0.
Hypothesis Olo : sp <= o.
Hypothesis Ohi : o + 32 <= hl_sptop L.
Hypothesis DSR : Forall (fun c => 0 <= c < 256) ds.
Hypothesis Plo : 4096 <= p.
Hypothesis Phi : p + m <= 2 ^ 47.
Hypothesis DAT : digits_at L LB sp p (length ds).
Hypothesis APO : p + m <= o \/ o + 32 <= p.
Hypothesis CRED : parse_credit L cr (length ds).
Hypothesis LBWF : L5PK.lb_wf L LB.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    detail_post L LB cr M0 M' R0 R' o sp fb neg ds LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' r M' model') K.

(* [comment removed for export] *)
Definition regsK (R : bvmap 5 word) : Prop := forall i, In i [3; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i).
Definition frameK (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) r /\
  L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\
  L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\
  L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20))) /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\
  L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22))) /\ L5.u64_at RSEGS M (sp - 72) (bv_unsigned (getr R0 (reg 23))) /\
  L5.u64_at RSEGS M (sp - 80) (bv_unsigned (getr R0 (reg 24))).

Lemma frameK_agree M M' : frameK M -> L5C.agree_on M M' (sp - 80) 80 -> frameK M'.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10) AG. uscr.
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [ | | | eassumption]; [eapply L5C.agree_on_sub; [exact AG| lia | lia] | lia | lia]).
Qed.

(* [comment removed for export] *)
Definition vb (dyn : bool) (st : L5.bstore) (ws : list Z) : L5.bigobj := L5.BO (if dyn then 1 else 0) (length ws) st.
Definition vobj (M : word -> option byte) (LBc : list (Z * Z)) (crc : credit) (dyn : bool) (st : L5.bstore) (ws : list Z) (V : Z) : Prop :=
  L5.big_at RSEGS M o' (vb dyn st ws) /\ L5C.obj_limbs RSEGS M (vb dyn st ws) ws /\ L5.limbs_val ws = V /\ length ws = nwords V /\ 0 <= V /\
  (dyn = false -> (exists v0 v1, st = L5.BInl v0 v1) /\ LBc = LB /\ crc = cr /\ (length ds <= 38)%nat) /\
  (dyn = true -> exists A cap, st = L5.BDyn cap A /\ LBc = (A, 8 * cap) :: LB /\ crc = debit L cr (vblk (length ds)) /\ 8 * cap = vblk (length ds) /\
                 L5PK.fresh_rng L LB A (8 * cap) /\ A mod 16 = 0 /\
                 (forall V', 0 <= V' < 10 ^ m -> Z.of_nat (nwords V') + 1 <= cap)).

Lemma vb_dyn dyn st ws : L5.bo_dyn (vb dyn st ws) = dyn.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT. unfold vb, L5.bo_dyn; cbn. destruct dyn; reflexivity. Qed.
Lemma vb_neg dyn st ws : L5.bo_neg (vb dyn st ws) = false.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT. unfold vb, L5.bo_neg; cbn. destruct dyn; reflexivity. Qed.

(* [comment removed for export] *)
Lemma vobj_step M M' Ra Rb LBc crc dyn st ws V V' g LB' cr' SCR :
  vobj M LBc crc dyn st ws V ->
  arith_post L LBc crc M M' Ra Rb o' (sp - 112) SCR (vb dyn st ws) V' g LB' cr' ->
  0 <= V' < 10 ^ m ->
  exists dyn' st' ws',
    vobj M' LB' cr' dyn' st' ws' V' /\ regs_preserved Ra Rb /\ getr Rb (reg 10) = Z_to_bv 64 o' /\ (length ws' <= length ws + 1)%nat /\
    ( (g = Same /\ dyn' = dyn /\ LB' = LBc /\ cr' = crc /\ (dyn = true \/ (length ws <= 1)%nat) /\
         L5C.hpres L LBc (sp - 112) SCR [(o', 32); (L5.bo_data o' (vb dyn st ws), 8 * (Z.of_nat (length ws) + 1))] M M')
      \/ (exists A', dyn = false /\ dyn' = true /\ st' = L5.BDyn 8 A' /\ g = Grown A' 8 /\ LB' = (A', 64) :: LBc /\ cr' = debit L crc 64 /\ LBc = LB /\ crc = cr /\
          L5C.fresh_block L LBc M' A' 64 /\ L5C.hpres L LBc (sp - 112) SCR [(o', 32)] M M') ).
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros VO AP HV'. destruct VO as (VB & VL & VV & VN & V0 & VI & VD).
  destruct AP as (RP & RA0 & ws' & st' & LV & RED & LEN & OB' & OL' & G). cbn [L5.bo_fb L5.bo_len L5.bo_st vb] in LEN, OB', OL', G.
  pose proof OL' as (OLen & OF & OS). cbn [L5.bo_len L5.bo_st] in OLen, OF, OS.
  assert (LN: length ws' = nwords V') by (apply length_nwords; assumption).
  destruct g as [|An capn].
  - destruct G as (DD & ELB & ECR & ST & HP). rewrite vb_dyn in DD.
    exists dyn, st', ws'. split.
    2: { split. exact RP. split. rewrite <- L5CoreKit.L5K.rl10. exact RA0. split. lia. left.
         split. reflexivity. split. reflexivity. split. exact ELB. split. exact ECR. split. { cbn [L5.bo_len] in DD. exact DD. } exact HP. }
    unfold vobj, vb. cbn [L5.bo_fb L5.bo_len L5.bo_st].
    split. exact OB'. split. exact OL'. split. exact LV. split. exact LN. split. lia. split.
    + intros Hd. subst dyn. destruct (VI eq_refl) as ((v0 & v1 & EST) & X1 & X2 & X3). subst st. rewrite ELB, ECR.
      destruct st' as [w0 w1|c q]; [|destruct ST]. split. exists w0, w1; reflexivity. split. exact X1. split. exact X2. exact X3.
    + intros Hd. subst dyn. destruct (VD eq_refl) as (A & cap & EST & X1 & X2 & X3 & X4 & X5 & X7). subst st. rewrite ELB, ECR.
      destruct st' as [w0 w1|c q]; [destruct ST|]. destruct ST as [-> ->].
      exists A, cap. split. reflexivity. split. exact X1. split. exact X2. split. exact X3. split. exact X4. split. exact X5. exact X7.
  - destruct G as (DD & L2 & EC & EST & ELB & ECR & FB & HP). rewrite vb_dyn in DD. subst dyn capn st'.
    destruct (VI eq_refl) as (_ & X1 & X2 & X3). subst LBc crc.
    exists true, (L5.BDyn 8 An), ws'. split.
    2: { split. exact RP. split. rewrite <- L5CoreKit.L5K.rl10. exact RA0. split. cbn in LEN |- *. lia. right. exists An.
         split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity. split. exact ELB. split. exact ECR.
         split. reflexivity. split. reflexivity. split. exact FB. exact HP. }
    unfold vobj, vb. cbn [L5.bo_fb L5.bo_len L5.bo_st]. change (Z.lor 0 1) with 1 in OB', OL'.
    split. exact OB'. split. exact OL'. split. exact LV. split. exact LN. split. lia. split.
    + intros Hd. discriminate Hd.
    + intros _. assert (V64: vblk (length ds) = 64). { unfold vblk. replace (length ds <? 39)%nat with true. reflexivity. symmetry. apply Nat.ltb_lt. lia. }
      exists An, 8. rewrite V64, ELB, ECR. split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity.
      destruct FB as (BR & BA & BD). destruct BR as (B0 & B1 & B2 & B3 & B4).
      split. { split. exact B0. split. exact B1. split. lia. exact BA. } split. exact B2.
      intros W HW. change 8 with (Z.of_nat 2 + 1 + 5). pose proof (nwords_le2 W (length ds) ltac:(lia) HW). lia.
Qed.

(* [comment removed for export] *)
Definition dinvG (p18 r20 c21 : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
           (dyn : bool) (sto : L5.bstore) (ws : list Z) (V : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 o' /\ getr R (reg 4) = Z_to_bv 64 TP /\ getr R (reg 18) = Z_to_bv 64 p18 /\
  getr R (reg 20) = Z_to_bv 64 r20 /\ getr R (reg 23) = Z_to_bv 64 9 /\ getr R (reg 9) = Z_to_bv 64 o /\
  getr R (reg 19) = Z_to_bv 64 negz /\ getr R (reg 8) = Z_to_bv 64 (p + m) /\
  getr R (reg 21) = Z_to_bv 64 c21 /\ getr R (reg 22) = Z_to_bv 64 (2 ^ 64 - 1 - p) /\ regsK R /\
  frameK M /\ vobj M LBc crc dyn sto ws V /\
  L5.bytes_at RSEGS M p ds /\ L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) /\ L5.writable RSEGS M o 32 /\
  hi_heap HI LBc crc M (m_vmmaps model) /\ model_ok model /\ model_but_vm model0 model /\
  L5C.hpres L LB sp DETAIL_SCR [] M0 M.
Definition dinv (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
           (dyn : bool) (sto : L5.bstore) (ws : list Z) (j : nat) : Prop :=
  dinvG (p + Z.of_nat j) (m - Z.of_nat j) (Z.of_nat j) R M model LBc crc dyn sto ws (dec (firstn j ds)).

Lemma vblk_bound : 0 < vblk (length ds) <= 8 * 268.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  unfold vblk. destruct (length ds <? 39)%nat. lia.
  pose proof (num_words_est_4999 (length ds) ltac:(lia)). pose proof (round_up_le (num_words_est (length ds))). pose proof (round_up_gt (num_words_est (length ds))). lia.
Qed.

Lemma hpres_nil_o M : L5C.hpres L LB sp DETAIL_SCR [] M0 M -> L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT. intros (P & D & WD). split. 2: { split. exact D. exact WD. } intros a (Ha & CA & NE & OW). apply P. split. exact Ha. split. exact CA. split. exact NE. apply L5C.outside_nil. Qed.

Lemma not_digits_ok Kb c : (Kb < length ds)%nat -> nth Kb ds 0 = c -> (c < 48 \/ 57 < c) -> ~ digits_ok ds.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT. intros HK Hc Hrg D. unfold digits_ok in D. pose proof (proj1 (Forall_nth _ _) D Kb 0 HK) as X. cbn beta in X. lia. Qed.

(* [comment removed for export] *)
Lemma err_path (fx : FPState) R M model LBc crc dyn st ws V (pj : Z) :
  getr R (reg 2) = Z_to_bv 64 o' -> getr R (reg 4) = Z_to_bv 64 TP -> getr R (reg 18) = Z_to_bv 64 pj -> 0 <= pj <= 2 ^ 48 ->
  regsK R -> frameK M -> vobj M LBc crc dyn st ws V ->
  L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) ->
  hi_heap HI LBc crc M (m_vmmaps model) -> model_ok model -> model_but_vm model0 model ->
  L5C.hpres L LB sp DETAIL_SCR [] M0 M ->
  ~ digits_ok ds ->
  srealizes RSEGS SCFG (cfg R DL_ERR M model) K.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros H2 H4 H18 Hpj RK FK VO OB HH MOK MBV HP ND.
  pose proof MOK as (Mh & Ml & Mm). pose proof RA as [Hr He]. pose proof SLO as SLO'. pose proof (proj1 (proj2 HP)) as DEF. uscr.
  assert (WR112: L5.writable RSEGS M (sp - 112) 112).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct FK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  pose proof (wrange (getr R0 (reg 8))) as W8. pose proof (wrange (getr R0 (reg 9))) as W9. pose proof (wrange (getr R0 (reg 18))) as W18.
  pose proof (wrange (getr R0 (reg 19))) as W19. pose proof (wrange (getr R0 (reg 20))) as W20. pose proof (wrange (getr R0 (reg 21))) as W21.
  pose proof (wrange (getr R0 (reg 22))) as W22. pose proof (wrange (getr R0 (reg 23))) as W23. pose proof (wrange (getr R0 (reg 24))) as W24.
  destruct VO as (VB & VL & VV & VN & V0 & VI & VD). cbn [L5.bo_fb L5.bo_len L5.bo_st vb] in VB, VL.
  destruct VB as (Vfb & _ & V8 & VS).
  (* [comment removed for export] *)
  assert (TAIL: forall (fx1 : FPState) R1 M1 model1 LB1 cr1,
     getr R1 (reg 2) = Z_to_bv 64 o' -> getr R1 (reg 4) = Z_to_bv 64 TP -> getr R1 (reg 9) = Z_to_bv 64 22 -> (exists x8, getr R1 (reg 8) = Z_to_bv 64 x8 /\ 0 <= x8 < 2 ^ 64) ->
     regsK R1 -> frameK M1 -> L5.writable RSEGS M1 (sp - 112) 112 ->
     L5.big_at RSEGS M1 o (L5.BO fb 0 (L5.BInl 0 0)) ->
     hi_heap HI LB1 cr1 M1 (m_vmmaps model1) -> model_ok model1 -> model_but_vm model0 model1 ->
     LB1 = LB -> credit_le (parse_debit L cr (length ds)) cr1 ->
     L5C.hpres L LB sp DETAIL_SCR [] M0 M1 ->
     srealizes RSEGS SCFG (cfg R1 0x2104c M1 model1) K).
  { intros fx1 R1 M1 model1 LB1 cr1 Q2 Q4 Q9 (x8 & Q8 & X8) RK1 FK1 WR1 OB1 HH1 MOK1 MBV1 -> CR1 HP1.
    pose proof MOK1 as (Mh1 & Ml1 & Mm1). destruct FK1 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
    destruct (pa11u_conc fx1 R1 M1 sp x8 22 r (bv_unsigned (getr R0 (reg 8))) (bv_unsigned (getr R0 (reg 9)))
                (bv_unsigned (getr R0 (reg 18))) (bv_unsigned (getr R0 (reg 19))) (bv_unsigned (getr R0 (reg 20))) (bv_unsigned (getr R0 (reg 21)))
                (bv_unsigned (getr R0 (reg 22))) (bv_unsigned (getr R0 (reg 23))) (bv_unsigned (getr R0 (reg 24)))
                Q2 Q8 Q9 ltac:(lia) X8 ltac:(lia) ltac:(lia) W8 W9 W18 W19 W20 W21 W22 W23 W24 ltac:(lia) A16
                D1 D2 D3 D4 D5 D6 D7 D8 D9 D10)
      as (fx2 & R2 & M2 & MS2 & K2 & R2_1 & R2_2 & R2_8 & R2_9 & R2_10 & R2_11 & R2_18 & R2_19 & R2_20 & R2_21 & R2_22 & R2_23 & R2_24 & FR2 & GR2).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh1. exact Ml1.
    { eapply msteps_trans. exact MS2. apply ret_detail. exact R2_1. exact Hr. exact He. }
    apply (KONT fx2 R2 M2 model1 LB cr1).
    - split.
      { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|Hi]. { rewrite R2_2, H0_2. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite (K2 3%nat) by (apply L5KP.In_of_existsb; reflexivity). apply (RK1 3%nat). cbn; tauto. }
        destruct Hi as [<-|Hi]. { rewrite (K2 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite Q4, H0_4. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R2_8. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_9. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_18. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_19. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_20. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_21. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_22. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_23. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R2_24. apply lit_of_word. }
        assert (G: forall j, In j [25; 26; 27]%nat -> getr R2 (reg j) = getr R0 (reg j)).
        { intros j Hj. assert (A2: In j KS_A11) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
          assert (AK: In j [3; 25; 26; 27]%nat) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
          rewrite (K2 j A2). apply (RK1 j AK). }
        apply G. L5CoreKit.L5K.inlist Hi. }
      right. split. right. exact ND. split. rewrite L5CoreKit.L5K.rl11. exact R2_11.
      split. reflexivity. split.
      { eapply (L5C.big_at_agree RSEGS M1 M2). intros i Hi. apply FR2. lia. lia. exact OB1. }
      split. exact CR1.
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M1 M2 []). exact LBWF. uscr; lia. exact HP1.
      intros x Hx. apply FR2. exact GR2. constructor.
    - exact MBV1.
    - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr1 M1 M2 (m_vmmaps model1) []). exact HIok. exact HH1. exact (ly_ro L LY). lia.
      intros x Hx. apply FR2. exact GR2. constructor. }
  destruct dyn.
  - (* [comment removed for export] *)
    destruct (VD eq_refl) as (A & cap & EST & ELB & ECR & ECAP & FRESH & AAL & CAPOK). clear VI. subst st.
    destruct VS as (Vb0 & V16 & V24 & Vlen & Vcap & Aq & QLO & QHI & HAP). destruct FRESH as (F0 & F1 & F2 & F3).
    pose proof vblk_bound as VBB. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in F1.
    assert (X1: 0 <= sp < 2 ^ 64) by lia. assert (X2: 0 <= A < 2 ^ 64) by lia. assert (X3: 0 <= cap < 2 ^ 64) by lia.
    assert (X4: 140735332483184 <= sp <= 140737488355328) by lia. assert (X5: 0 <= 1 <= 255) by lia. assert (X6: 1 <= Z.land 1 1 <= 1) by (change (Z.land 1 1) with 1; lia).
    assert (X7: L5.u64_at RSEGS M (sp - 88) A) by (replace (sp - 88) with (sp - 112 + 24) by lia; exact V24).
    assert (X8: 4096 <= A <= 140737488355327) by lia.
    assert (X9: L5.u64_at RSEGS M (sp - 96) cap) by (replace (sp - 96) with (sp - 112 + 16) by lia; exact V16).
    assert (X10: 1 <= cap <= 134217728) by lia. assert (X0: 0 <= 1 < 2 ^ 64) by lia.
    destruct (pa12du_conc fx R M sp pj 1 A cap H2 H18 X1 Hpj X0 X2 X3 X4 A16 Vfb X5 X6 X7 X8 X9 X10)
      as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & FR1 & GR1).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold DL_ERR. exact MS1. }
    assert (EQM: forall a, M1 a = M a) by (intros a; apply FR1).
    eapply (Hdel fx1 R1 M1 model K LBc crc A (8 * cap) (sp - 112) 0x2104c).
    + eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LBc crc M M1 (m_vmmaps model) []). exact HIok. exact HH. exact (ly_ro L LY). lia.
      intros x Hx. apply FR1. exact GR1. constructor.
    + exact MOK. + exact HK0.
    + rewrite ELB. left. reflexivity.
    + rewrite L5CoreKit.L5K.rl10. exact R1_10.
    + rewrite L5CoreKit.L5K.rl1. exact R1_1.
    + apply ra_ok_lit. lia. reflexivity.
    + rewrite L5CoreKit.L5K.rl2. exact R1_2.
    + rewrite L5CoreKit.L5K.rl4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
    + uscr. split. { replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
      split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR1. eapply L5.defined_sub. exact DEF. lia. lia.
    + intros fx2 R2 M2 model2 RP HP2 MBV2 HH2.
      assert (RM: lb_remove A LBc = LB). { rewrite ELB. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
      rewrite RM in HP2, HH2.
      assert (AG2: forall a n, sp - 112 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n).
      { intros a n Ha Hn. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP2. uscr; lia. uscr; lia. lia. lia.
        intros i Hi. apply L5C.outside_nil. }
      assert (AG02: forall a n, sp - 112 <= a -> a + n <= sp -> L5C.agree_on M M2 a n).
      { intros a n Ha Hn. eapply L5C.agree_on_trans. 2: apply AG2; lia. intros i Hi. apply FR1. }
      pose proof (RP 2%bv ltac:(cbn; tauto)) as P2. pose proof (RP 8%bv ltac:(cbn; tauto)) as P8. pose proof (RP 9%bv ltac:(cbn; tauto)) as P9.
      pose proof (RP 4%bv ltac:(cbn; tauto)) as P4.
      rewrite L5CoreKit.L5K.rl2 in P2. rewrite L5CoreKit.L5K.rl8 in P8. rewrite L5CoreKit.L5K.rl9 in P9. rewrite L5CoreKit.L5K.rl4 in P4.
      apply (TAIL fx2 R2 M2 model2 LB crc).
      * rewrite P2. exact R1_2.
      * rewrite P4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
      * rewrite P9. exact R1_9.
      * exists pj. split. rewrite P8. exact R1_8. lia.
      * intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
        rewrite (K1 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi).
      * apply (frameK_agree M M2). repeat split; assumption. apply AG02; lia.
      * eapply (L5C.writable_agree RSEGS M M2). apply AG02; lia. lia. lia. exact WR112.
      * eapply (L5C.big_at_agree RSEGS M M2). eapply L5C.agree_on_trans. intros i Hi; apply FR1.
        eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP2. uscr; lia. uscr; lia. lia. lia. intros i Hi; apply L5C.outside_nil. lia. lia. exact OB.
      * exact HH2. * destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]].
      * eapply L5C.model_but_vm_trans. exact MBV. exact MBV2.
      * reflexivity.
      * rewrite ECR. unfold parse_debit. apply credit_le_debit. apply vblk_pos.
      * (* [comment removed for export] *)
        assert (HP1: L5C.hpres L LB sp DETAIL_SCR [] M0 M1).
        { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M M1 []). exact LBWF. uscr; lia. exact HP. intros x Hx. apply FR1. exact GR1. constructor. }
        eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp DETAIL_SCR [] (sp - 112) OPDEL_SCR [] M0 M1 M2). exact LBWF. uscr; lia. lia. exact HP1. exact HP2. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia. constructor.
  - (* [comment removed for export] *)
    destruct (VI eq_refl) as (_ & ELB & ECR & M38). clear VD.
    assert (X1: 0 <= sp < 2 ^ 64) by lia. assert (X0: 0 <= 0 < 2 ^ 64) by lia.
    assert (X4: 140735332483184 <= sp <= 140737488355328) by lia. assert (X5: 0 <= 0 <= 255) by lia. assert (X6: 0 <= Z.land 0 1 <= 0) by (change (Z.land 0 1) with 0; lia).
    destruct (pa12iu_conc fx R M sp pj 0 H2 H18 X1 Hpj X0 X4 A16 Vfb X5 X6)
      as (fx1 & R1 & M1 & MS1 & K1 & R1_2 & R1_8 & R1_9 & FR1 & GR1).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold DL_ERR. exact MS1. }
    assert (AG1: forall a n, L5C.agree_on M M1 a n) by (intros a n i Hi; apply FR1).
    rewrite ECR in HH. apply (TAIL fx1 R1 M1 model LB cr).
    + exact R1_2.
    + rewrite (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
    + exact R1_9.
    + exists pj. split. exact R1_8. lia.
    + intros i Hi. rewrite (K1 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi).
    + apply (frameK_agree M M1). repeat split; assumption. apply AG1.
    + eapply (L5C.writable_agree RSEGS M M1). apply AG1. lia. lia. exact WR112.
    + eapply (L5C.big_at_agree RSEGS M M1). apply AG1. lia. lia. exact OB.
    + rewrite <- ELB. eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LBc cr M M1 (m_vmmaps model) []). exact HIok. exact HH. exact (ly_ro L LY). lia.
      intros x Hx. apply FR1. exact GR1. constructor.
    + exact MOK. + exact MBV. + reflexivity.
    + apply parse_debit_le.
    + eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M M1 []). exact LBWF. uscr; lia. exact HP. intros x Hx. apply FR1. exact GR1. constructor.
Qed.

(* [comment removed for export] *)
Lemma vobj_agree M M' LBc crc dyn sto ws V : vobj M LBc crc dyn sto ws V -> (forall a k, L5C.agree_on M M' a k) -> vobj M' LBc crc dyn sto ws V.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros (VB & VL & VV & VN & V0 & VI & VD) AG. split. { eapply (L5C.big_at_agree RSEGS M M'). apply AG. uscr; lia. lia. exact VB. }
  split. { eapply (obj_limbs_reflag M M'). exact VL. intros cap q E. split. apply AG.
           destruct dyn. destruct (VD eq_refl) as (A & cap' & EST & _ & _ & ECAP & FR & _). rewrite EST in E. injection E as <- <-. destruct FR as (F0 & F1 & F2 & F3).
           pose proof IMGLO. pose proof vblk_bound. destruct VB as (_ & _ & _ & VS). cbn [L5.bo_st vb] in VS. rewrite EST in VS. destruct VS as (_ & _ & _ & X4 & _). cbn [L5.bo_len vb] in X4. lia.
           destruct (VI eq_refl) as ((v0 & v1 & EST) & _). rewrite EST in E. discriminate E. }
  split. exact VV. split. exact VN. split. exact V0. split. exact VI. exact VD.
Qed.

Lemma pow10_le_m (j : nat) : (j <= length ds)%nat -> 10 ^ Z.of_nat j <= 10 ^ m.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT. intros Hj. try subst m. apply Z.pow_le_mono_r. lia. lia. Qed.
Lemma firstn_digits_bound (j : nat) : (j <= length ds)%nat -> digits_ok (firstn j ds) -> 0 <= dec (firstn j ds) < 10 ^ Z.of_nat j.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros Hj D. pose proof (dec_bound (firstn j ds) (all_digits_Forall _ D)) as B. rewrite length_firstn, Nat.min_l in B by lia. exact B.
Qed.
Lemma digits_ok_S (j : nat) : (j < length ds)%nat -> digits_ok (firstn j ds) -> 48 <= nth j ds 0 <= 57 -> digits_ok (firstn (S j) ds).
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros Hj D C. unfold digits_ok. rewrite (firstn_S_nth ds j Hj). apply Forall_app. split. exact D. constructor. exact C. constructor.
Qed.

(* [comment removed for export] *)
Lemma digits_outside W' : Forall (L5PK.wr_ok L LB sp DETAIL_SCR []) W' -> forall i, p <= i < p + m -> L5.outside W' i.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros WF i Hi rg Hrg IN. pose proof (proj1 (Forall_forall _ _) WF rg Hrg) as WR. pose proof SLO as SLO'. uscr.
  destruct DAT as [Z0|DAT']. { try subst m. lia. }
  inversion WR; subst; unfold L5.in_rng in IN; cbn [fst snd] in IN.
  - destruct DAT' as [(A & k & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]; [pose proof (LBWF (A, k) Hin) as (W0 & W1 & W2); cbn in W0, W1, W2; try subst m; lia| try subst m; lia | try subst m; lia].
  - destruct H.
  - destruct H as (F0 & F1 & F2 & F3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in F1.
    destruct DAT' as [(A' & k & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]. pose proof (F3 (A', k) Hin) as BA. cbn in BA. try subst m. lia. try subst m; lia. try subst m; lia.
  - lia.
  - (* [comment removed for export] *)
    pose proof (ly_errno L LY) as EQE. pose proof (ly_img_hi L LY) as EQH.
    pose proof (ly_img_lo L LY) as EQL.
    destruct DAT' as [(A' & k & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]; [pose proof (LBWF (A', k) Hin) as (W0 & W1 & W2); cbn in W0, W1, W2; try subst m; lia| try subst m; lia | try subst m; lia].
Qed.
Lemma digits_agree LB' sp' scr' W' M1 M2 :
  L5C.hpres L LB' sp' scr' W' M1 M2 -> L5PK.lb_sub LB LB' -> 0 <= scr' -> hl_sptop L - 2 ^ 23 + scr' <= sp' -> sp' <= sp ->
  Forall (L5PK.wr_ok L LB sp DETAIL_SCR []) W' -> L5C.agree_on M1 M2 p m.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros HP' SUB Hscr Hsp' Hle WF. pose proof (digits_outside W' WF) as HO.
  destruct DAT as [Z0|[(A & k & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. { exfalso. lia. }
  - pose proof (LBWF (A, k) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2.
    eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP'. apply SUB. exact Hin. lia. exact W1. exact W2. exact HA. try subst m; exact HAk. exact HO.
  - eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP'. lia. lia. lia. try subst m; lia. exact HO.
  - eapply (L5PK.agree_call_static L IMGHI STOP ERR IMGLO). exact HP'. rewrite (ly_img_lo L LY); lia. rewrite (ly_img_hi L LY); try subst m; lia.
    intros i Hi HS. pose proof (ly_static L LY i HS). try subst m; lia. left. rewrite (ly_errno L LY); try subst m; lia. exact HO.
Qed.
Lemma bytes_agree M1 M2 : L5C.agree_on M1 M2 p m -> L5.bytes_at RSEGS M1 p ds -> L5.bytes_at RSEGS M2 p ds.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT. intros AG BY. eapply (L5C.bytes_at_agree RSEGS M1 M2). exact AG. lia. try subst m; lia. exact BY. Qed.

(* [comment removed for export] *)
Lemma digit_step (fx : FPState) R M model LBc crc dyn sto ws (j : nat) :
  (j < length ds)%nat -> 48 <= nth j ds 0 <= 57 -> digits_ok (firstn j ds) ->
  dinv R M model LBc crc dyn sto ws j ->
  (forall (fx' : FPState) R' M' model' LBc' crc' dyn' sto' ws',
      dinvG (p + Z.of_nat j) (m - Z.of_nat j) (Z.of_nat j) R' M' model' LBc' crc' dyn' sto' ws' (dec (firstn (S j) ds)) ->
      srealizes RSEGS SCFG (cfg R' 0x20ffc M' model') K) ->
  srealizes RSEGS SCFG (cfg R DL_HEAD M model) K.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros Hj DIG DOKj DI KD.
  destruct DI as (H2 & H4 & H18 & H20 & H23 & H9 & H19 & H8 & HJ & HNP & RK & FK & VO & BY & OB & WO & HH & MOK & MBV & HP).
  pose proof MOK as (Mh & Ml & Mm). pose proof RA as [Hr He]. pose proof SLO as SLO'. pose proof (hpres_defined _ _ _ _ _ _ HP) as DEF. uscr.
  set (V := dec (firstn j ds)) in *. set (c := nth j ds 0) in *.
  pose proof (firstn_digits_bound j ltac:(lia) DOKj) as VBj. change (dec (firstn j ds)) with V in VBj.
  pose proof (pow10_le_m (S j) ltac:(lia)) as PJ. rewrite Nat2Z.inj_succ, Z.pow_succ_r in PJ by lia.
  assert (V'EQ: dec (firstn (S j) ds) = 10 * V + (c - 48)) by (subst V c; apply dec_firstn_S; exact Hj).
  assert (B10: 0 <= 10 * V < 10 ^ m) by lia.
  assert (B10d: 0 <= 10 * V + (c - 48) < 10 ^ m) by lia.
  pose proof VO as (VB & VL & VV & VN & V0 & VI & VD).
  (* [comment removed for export] *)
  assert (Uc: L5.u8_at RSEGS M (p + Z.of_nat j) c) by (apply BY; exact Hj).
  pose proof (proj1 (Forall_nth _ _) DSR j 0 Hj) as CR. cbn beta in CR. change (nth j ds 0) with c in CR.
  (* [comment removed for export] *)
  destruct (pa6u_conc fx R M sp (p + Z.of_nat j) (Z.of_nat j) (2 ^ 64 - 1 - p) c H2 H18 HJ HNP H23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) Uc DIG ltac:(lia) ltac:(lia))
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_21 & R1_22 & R1_24 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold DL_HEAD. exact MS1. }
  assert (AG1: forall a k, L5C.agree_on M M1 a k) by (intros a k i Hi; apply FR1).
  assert (HP1: L5C.hpres L LB sp DETAIL_SCR [] M0 M1).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M M1 []). exact LBWF. uscr; lia. exact HP. intros x Hx. apply FR1. exact GR1. constructor. }
  pose proof (hpres_defined _ _ _ _ _ _ HP1) as DEF1.
  (* [comment removed for export] *)
  eapply (Hmul fx1 R1 M1 model K LBc crc (sp - 112) (sp - 112) 135152 (vb dyn sto ws) ws).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LBc crc M M1 (m_vmmaps model) []). exact HIok. exact HH. exact (ly_ro L LY). lia.
    intros x Hx. apply FR1. exact GR1. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11. exact R1_11.
  - cbn [vb L5.bo_len]. rewrite VN. pose proof (nwords_bound_le V j (length ds) VBj ltac:(lia)). pose proof (num_words_est_4999 (length ds) ltac:(lia)). lia.
  - rewrite vb_dyn. intros Hd. subst dyn. destruct (VD eq_refl) as (A & cap & EST & _ & _ & _ & _ & _ & CAPOK). subst sto. cbn [vb L5.bo_len L5.bo_cap L5.bo_st].
    rewrite VN. apply CAPOK. pose proof (pow10_le_m j ltac:(lia)). lia.
  - rewrite vb_dyn. intros Hd _. subst dyn. destruct (VI eq_refl) as (_ & ELB & ECR & M38). rewrite ECR.
    replace 64 with (vblk (length ds)). exact (proj1 CRED). unfold vblk. replace (length ds <? 39)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  - rewrite L5CoreKit.L5K.rl1. exact R1_1.
  - apply ra_ok_lit. lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R1_2.
  - rewrite L5CoreKit.L5K.rl4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - split. { replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_sub. exact DEF1. lia. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). apply AG1. lia. lia. exact VB.
  - eapply (obj_limbs_reflag M M1). exact VL. intros cap q E. split. apply AG1.
    pose proof (vobj_agree M M1 LBc crc dyn sto ws V VO AG1) as (_ & VL1 & _). destruct VL1 as (_ & _ & L3). cbn [L5.bo_st vb] in L3. rewrite E in L3.
    destruct VB as (_ & _ & _ & VS). cbn [L5.bo_st vb] in VS. rewrite E in VS. destruct VS as (_ & _ & _ & X4 & X5 & X6 & X7 & X8). cbn [L5.bo_len vb] in X4. lia.
  - apply vb_neg.
  - replace (sp - 112) with (sp + 8 * (-14)) by lia. apply mod16_8. exact A16.
  - lia.
  - lia.
  - eapply L5.writable_grows. exact GR1. eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia.
  - cbn [L5.bo_st vb]. intros cap q E. destruct dyn. destruct (VD eq_refl) as (A & cap' & EST & ELB & _). rewrite EST in E. injection E as <- <-. rewrite ELB. left; reflexivity.
    destruct (VI eq_refl) as ((v0 & v1 & EST) & _). rewrite EST in E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 AP MBV2 HH2.
    rewrite VV in AP.
    pose proof (vobj_agree M M1 LBc crc dyn sto ws V VO AG1) as VO1.
    destruct (vobj_step M1 M2 R1 R2 LBc crc dyn sto ws V (10 * V) g LB2 cr2 MUL10_SCR VO1 AP B10) as (dyn1 & sto1 & ws1 & VO2 & RP & R2_10 & LEN1 & GG).
    assert (MOK2: model_ok model2).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]]. }
    pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (MBV02: model_but_vm model0 model2) by (eapply L5C.model_but_vm_trans; [exact MBV| exact MBV2]).
    (* [comment removed for export] *)
    assert (GC: exists W', L5C.hpres L LBc (sp - 112) MUL10_SCR W' M1 M2 /\ (forall i, sp - 80 <= i -> L5.outside W' i) /\ (forall i, i < sp - 112 -> ~ (exists A k, In (A, k) LBc /\ A <= i < A + k) -> L5.outside W' i)
                       /\ Forall (L5PK.wr_ok L LB sp DETAIL_SCR []) W' /\ L5PK.lb_sub LBc LB2 /\ L5PK.lb_sub LB LBc).
    { assert (SUBc: L5PK.lb_sub LB LBc).
      { destruct dyn. destruct (VD eq_refl) as (A & cap & _ & -> & _). apply L5PK.lb_sub_cons. destruct (VI eq_refl) as (_ & -> & _). apply L5PK.lb_sub_refl. }
      destruct GG as [(-> & -> & -> & -> & DD & HPm)|(A' & Hd & -> & -> & -> & -> & -> & ELB & ECR & FB' & HPm)].
      - eexists. split. exact HPm.
        destruct dyn.
        + destruct (VD eq_refl) as (A & cap & EST & ELB & ECR & ECAP & FRESH & AAL & CAPOK). subst sto. cbn [L5.bo_data L5.bo_st L5.bo_len vb].
          destruct FRESH as (F0 & F1 & F2 & F3). pose proof vblk_bound. pose proof (CAPOK V ltac:(pose proof (pow10_le_m j ltac:(lia)); lia)) as CK. rewrite <- VN in CK.
          split. { intros i Hi r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
          split. { intros i Hi NB r' [<-|[<-|[]]]; unfold L5.in_rng; cbn. lia. intros Hin. apply NB. exists A, (8 * cap). split. rewrite ELB. left; reflexivity. lia. }
          split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. eapply L5PK.wr_fresh. exact (conj F0 (conj F1 (conj F2 F3))). lia. lia. constructor. }
          split. apply L5PK.lb_sub_refl. exact SUBc.
        + destruct (VI eq_refl) as ((v0 & v1 & EST) & ELB & ECR & M38). subst sto. cbn [L5.bo_data L5.bo_st L5.bo_len vb].
          assert (X4: (length ws <= 1)%nat) by (destruct DD as [DD|DD]; [discriminate DD| exact DD]).
          split. { intros i Hi r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
          split. { intros i Hi NB r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
          split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
          split. apply L5PK.lb_sub_refl. exact SUBc.
      - exists [(sp - 112, 32)]. split. exact HPm.
        split. { intros i Hi r' [<-|[]]; unfold L5.in_rng; cbn; lia. }
        split. { intros i Hi NB r' [<-|[]]; unfold L5.in_rng; cbn; lia. }
        split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
        split. rewrite ELB. apply L5PK.lb_sub_cons. exact SUBc. }
    destruct GC as (W' & HPm & WO1 & WO2 & WF' & SUB2 & SUBc).
    assert (AG2s: forall a k, sp - 80 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M1 M2 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPm. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply WO1. lia. }
    assert (HP2: L5C.hpres L LB sp DETAIL_SCR [] M0 M2).
    { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LBc sp DETAIL_SCR [] (sp - 112) MUL10_SCR W' M0 M1 M2). exact LBWF. uscr; lia. lia. exact HP1. exact HPm. exact SUBc. uscr; lia. lia. uscr; lia. exact WF'. }
    pose proof (hpres_defined _ _ _ _ _ _ HP2) as DEF2.
    assert (FK2: frameK M2). { revert FK. unfold frameK. intros FK. repeat split; (eapply (L5C.u64_at_agree RSEGS M M2); [eapply L5C.agree_on_trans; [apply AG1| apply AG2s; lia] | lia | lia | apply FK]). }
    destruct FK2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
    pose proof (RP 2%bv ltac:(cbn; tauto)) as P2. pose proof (RP 24%bv ltac:(cbn; tauto)) as P24. pose proof (RP 4%bv ltac:(cbn; tauto)) as P4.
    rewrite L5CoreKit.L5K.rl2 in P2. rewrite L5CoreKit.L5K.rl24 in P24. rewrite L5CoreKit.L5K.rl4 in P4.
    assert (R2_2: getr R2 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite P2; exact R1_2).
    assert (R2_24: getr R2 (reg 24) = Z_to_bv 64 c) by (rewrite P24; exact R1_24).
    assert (R2_4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite P4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4. }
    assert (RS2: forall i, In i [8; 9; 18; 19; 20; 21; 22; 23]%nat -> getr R2 (reg i) = getr R (reg i)).
    { intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
      apply K1. pose proof Hi as H'; L5CoreKit.L5K.inlist H'. }
    assert (RK2: regsK R2).
    { intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
      rewrite (K1 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi). }
    (* [comment removed for export] *)
    destruct (pa7u_conc fx2 R2 M2 sp c R2_2 R2_24 ltac:(lia) ltac:(lia) ltac:(lia) A16 DIG)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_10 & R3_11 & FR3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
    assert (AG3: forall a k, L5C.agree_on M2 M3 a k) by (intros a k i Hi; apply FR3).
    pose proof (vobj_agree M2 M3 LB2 cr2 dyn1 sto1 ws1 (10 * V) VO2 AG3) as VO3.
    pose proof VO3 as (VB3 & VL3 & VV3 & VN3 & V03 & VI3 & VD3).
    assert (HP3: L5C.hpres L LB sp DETAIL_SCR [] M0 M3).
    { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M2 M3 []). exact LBWF. uscr; lia. exact HP2. intros x Hx. apply FR3. exact GR3. constructor. }
    pose proof (hpres_defined _ _ _ _ _ _ HP3) as DEF3.
    assert (LBWF2: L5PK.lb_wf L LB2) by (eapply (L5PK.lb_wf_of_heap L HI); [exact HIok | exact HH2]).
    (* [comment removed for export] *)
    eapply (Hadd fx3 R3 M3 model2 K LB2 cr2 (sp - 112) (c - 48) (sp - 112) 135164 (vb dyn1 sto1 ws1) ws1).
    + eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia.
      intros x Hx. apply FR3. exact GR3. constructor.
    + exact MOK2.
    + exact HK0.
    + rewrite L5CoreKit.L5K.rl10. exact R3_10.
    + rewrite L5CoreKit.L5K.rl11. exact R3_11.
    + lia.
    + cbn [vb L5.bo_len]. rewrite VN3. pose proof (nwords_bound (10 * V) (length ds) B10). pose proof (num_words_est_4999 (length ds) ltac:(lia)). lia.
    + rewrite vb_dyn. intros Hd. subst dyn1. destruct (VD3 eq_refl) as (A & cap & EST & _ & _ & _ & _ & _ & CAPOK). subst sto1. cbn [vb L5.bo_len L5.bo_cap L5.bo_st].
      rewrite VN3. apply CAPOK. exact B10.
    + rewrite vb_dyn. intros Hd _. subst dyn1. destruct (VI3 eq_refl) as (_ & ELB & ECR & M38). rewrite ECR.
      replace 64 with (vblk (length ds)). exact (proj1 CRED). unfold vblk. replace (length ds <? 39)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
    + rewrite L5CoreKit.L5K.rl1. exact R3_1.
    + apply ra_ok_lit. lia. reflexivity.
    + rewrite L5CoreKit.L5K.rl2. exact R3_2.
    + rewrite L5CoreKit.L5K.rl4, (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_4.
    + split. { replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
      uscr. split. lia. split. lia. split. lia. eapply L5.defined_sub. exact DEF3. lia. lia.
    + exact VB3.
    + exact VL3.
    + apply vb_neg.
    + replace (sp - 112) with (sp + 8 * (-14)) by lia. apply mod16_8. exact A16.
    + lia.
    + lia.
    + eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF3| uscr; lia | uscr; lia] | uscr; lia | uscr; lia].
    + cbn [L5.bo_st vb]. intros cap q E. destruct dyn1. destruct (VD3 eq_refl) as (A & cap' & EST & ELB & _). rewrite EST in E. injection E as <- <-. rewrite ELB. left; reflexivity.
      destruct (VI3 eq_refl) as ((v0 & v1 & EST) & _). rewrite EST in E. discriminate E.
    + (* [comment removed for export] *)
      intros fx4 R4 M4 model4 g' LB4 cr4 AP4 MBV4 HH4.
      rewrite VV3 in AP4.
      destruct (vobj_step M3 M4 R3 R4 LB2 cr2 dyn1 sto1 ws1 (10 * V) (10 * V + (c - 48)) g' LB4 cr4 ADDD_SCR VO3 AP4 B10d) as (dyn4 & sto4 & ws4 & VO4 & RP4 & R4_10 & LEN4 & GG4).
      assert (MOK4: model_ok model4).
      { destruct MOK2 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV4); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV4); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV4); exact Y3]]. }
      assert (GC4: exists W', L5C.hpres L LB2 (sp - 112) ADDD_SCR W' M3 M4 /\ (forall i, sp - 80 <= i -> L5.outside W' i)
                          /\ Forall (L5PK.wr_ok L LB sp DETAIL_SCR []) W' /\ L5PK.lb_sub LB LB2).
      { assert (SUB2': L5PK.lb_sub LB LB2) by (eapply L5PK.lb_sub_trans; [exact SUBc| exact SUB2]).
        destruct GG4 as [(-> & -> & -> & -> & DD & HPa)|(A' & Hd & -> & -> & -> & -> & -> & ELB & ECR & FB' & HPa)].
        - eexists. split. exact HPa.
          destruct dyn1.
          * destruct (VD3 eq_refl) as (A & cap & EST & ELB & ECR & ECAP & FRESH & AAL & CAPOK). subst sto1. cbn [L5.bo_data L5.bo_st L5.bo_len vb].
            destruct FRESH as (F0 & F1 & F2 & F3). pose proof vblk_bound. pose proof (CAPOK (10 * V) B10) as CK. rewrite <- VN3 in CK.
            split. { intros i Hi r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
            split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. eapply L5PK.wr_fresh. exact (conj F0 (conj F1 (conj F2 F3))). lia. lia. constructor. }
            exact SUB2'.
          * destruct (VI3 eq_refl) as ((v0 & v1 & EST) & ELB & ECR & M38). subst sto1. cbn [L5.bo_data L5.bo_st L5.bo_len vb].
            assert (X4: (length ws1 <= 1)%nat) by (destruct DD as [DD|DD]; [discriminate DD| exact DD]).
            split. { intros i Hi r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
            split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
            exact SUB2'.
        - exists [(sp - 112, 32)]. split. exact HPa.
          split. { intros i Hi r' [<-|[]]; unfold L5.in_rng; cbn; lia. }
          split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
          exact SUB2'. }
      destruct GC4 as (W4 & HPa & WO4 & WF4 & SUB2').
      assert (AG4s: forall a k, sp - 80 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M3 M4 a k).
      { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPa. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply WO4. lia. }
      assert (AG24: forall a k, sp - 80 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M2 M4 a k).
      { intros a k Ha Hk. eapply L5C.agree_on_trans. apply AG3. apply AG4s; lia. }
      pose proof (RP4 2%bv ltac:(cbn; tauto)) as T2. pose proof (RP4 4%bv ltac:(cbn; tauto)) as T4.
      rewrite L5CoreKit.L5K.rl2 in T2. rewrite L5CoreKit.L5K.rl4 in T4.
      apply (KD fx4 R4 M4 model4 LB4 cr4 dyn4 sto4 ws4). rewrite V'EQ.
      split. { rewrite T2. exact R3_2. }
      split. { rewrite T4, (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_4. }
      assert (RS4: forall i, In i [8; 9; 18; 19; 20; 21; 22; 23]%nat -> getr R4 (reg i) = getr R (reg i)).
      { intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R3 R4 i RP4) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
        rewrite (K3 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply RS2. exact Hi. }
      split. { rewrite (RS4 18%nat) by (cbn; tauto). exact H18. }
      split. { rewrite (RS4 20%nat) by (cbn; tauto). exact H20. }
      split. { rewrite (RS4 23%nat) by (cbn; tauto). exact H23. }
      split. { rewrite (RS4 9%nat) by (cbn; tauto). exact H9. }
      split. { rewrite (RS4 19%nat) by (cbn; tauto). exact H19. }
      split. { rewrite (RS4 8%nat) by (cbn; tauto). exact H8. }
      split. { rewrite (RS4 21%nat) by (cbn; tauto). exact HJ. }
      split. { rewrite (RS4 22%nat) by (cbn; tauto). exact HNP. }
      split. { intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R3 R4 i RP4) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
               rewrite (K3 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK2 i Hi). }
      split. { unfold frameK. repeat split; (eapply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; lia | lia | lia | assumption]). }
      split. exact VO4.
      split. { apply (bytes_agree M3 M4). apply (digits_agree LB2 (sp - 112) ADDD_SCR W4 M3 M4 HPa SUB2' ltac:(uscr; lia) ltac:(uscr; lia) ltac:(lia) WF4).
               apply (bytes_agree M2 M3). apply AG3. apply (bytes_agree M1 M2). apply (digits_agree LBc (sp - 112) MUL10_SCR W' M1 M2 HPm SUBc ltac:(uscr; lia) ltac:(uscr; lia) ltac:(lia) WF').
               apply (bytes_agree M M1). apply AG1. exact BY. }
      split. { eapply (L5C.big_at_agree RSEGS M2 M4). apply AG24; lia. lia. lia. eapply (L5C.big_at_agree RSEGS M M2). eapply L5C.agree_on_trans. apply AG1. apply AG2s; lia. lia. lia. exact OB. }
      split. { eapply (L5C.writable_agree RSEGS M2 M4). apply AG24; lia. lia. lia. eapply (L5C.writable_agree RSEGS M M2). eapply L5C.agree_on_trans. apply AG1. apply AG2s; lia. lia. lia. exact WO. }
      split. exact HH4. split. exact MOK4. split. { eapply L5C.model_but_vm_trans. exact MBV02. exact MBV4. }
      eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB2 sp DETAIL_SCR [] (sp - 112) ADDD_SCR W4 M0 M3 M4). exact LBWF. uscr; lia. lia. exact HP3. exact HPa. exact SUB2'. uscr; lia. lia. uscr; lia. exact WF4.
Qed.

(* [comment removed for export] *)
End CTX.
End WithHeap.
End SCFG_1.
End L5DETPU.
