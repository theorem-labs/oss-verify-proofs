(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5KnA_u Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmLayout PmModel PmModelFacts PmStatics PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics PnKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u
     PnCertKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnMemW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSStrCstr_u PnSDec128Defs_u PnSDec128EP_u PnSDec128AP_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDENT.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation AD := PnLayoutS_u.ADDR_S.

Lemma wseg_infg : wseg_ok RSEGS (Z_to_bv 64 820640) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_nang : wseg_ok RSEGS (Z_to_bv 64 820672) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_info : wseg_ok RSEGS (Z_to_bv 64 820616) (Z.to_nat 24) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_nano : wseg_ok RSEGS (Z_to_bv 64 820648) (Z.to_nat 24) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_atexit : wseg_ok RSEGS (Z_to_bv 64 958472) (Z.to_nat 544) = true. Proof. vm_compute. reflexivity. Qed.

Lemma PNSDSPC_mod16 S0 : S0 mod 16 = 0 -> (S0 - 256) mod 16 = 0.
Proof. intros H. replace (S0 - 256) with (S0 + (-16) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.
(* [comment removed for export] *)
Lemma slt_sign (ev : nat -> word) (bl : nat -> list byte) hi :
  0 <= hi < 2 ^ 64 -> ev 37%nat = Z_to_bv 64 hi ->
  bv_unsigned (AX2.edenot (AX2.Env ev bl) (AX2.EAlu Instr.ALU_SLT (AX2.EVar 37) (AX2.ELit 0))) = (if Z.leb (2 ^ 63) hi then 1 else 0).
Proof.
  intros Hhi E. cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div]. rewrite E. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
  rewrite (Z.mod_small (0 + 2 ^ 63)) by (clear; lia).
  destruct (Z.leb_spec (2 ^ 63) hi) as [G|L].
  - replace ((hi + 2 ^ 63) mod 2 ^ 64) with (hi + 2 ^ 63 - 2 ^ 64).
    2:{ replace (hi + 2 ^ 63) with ((hi + 2 ^ 63 - 2 ^ 64) + 1 * 2 ^ 64) at 2 by (clear; lia). rewrite Z.mod_add by (clear; lia). rewrite Z.mod_small by (clear -G Hhi; lia). reflexivity. }
    destruct (Z.ltb_spec (hi + 2 ^ 63 - 2 ^ 64 - 2 ^ 63) (0 + 2 ^ 63 - 2 ^ 63)) as [X|X]; [reflexivity| exfalso; clear -X G Hhi; lia].
  - rewrite (Z.mod_small (hi + 2 ^ 63)) by (clear -L Hhi; lia).
    destruct (Z.ltb_spec (hi + 2 ^ 63 - 2 ^ 63) (0 + 2 ^ 63 - 2 ^ 63)) as [X|X]; [exfalso; clear -X L Hhi; lia| reflexivity].
Qed.

Section Ent.
Variables (R0 : bvmap 5 word) (S first vp hi lo r : Z) (ax : PNST.bax).
Let u8 := bv_unsigned (getr R0 (reg 8)).
Let u9 := bv_unsigned (getr R0 (reg 9)).
Let u18 := bv_unsigned (getr R0 (reg 18)).
Let u19 := bv_unsigned (getr R0 (reg 19)).
Let u20 := bv_unsigned (getr R0 (reg 20)).
Let u21 := bv_unsigned (getr R0 (reg 21)).
Let u22 := bv_unsigned (getr R0 (reg 22)).
Let u23 := bv_unsigned (getr R0 (reg 23)).
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 first.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (first + 42).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 vp.
Hypothesis A2 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis A1 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis Fr : 0 <= r < 2 ^ 47.
Hypothesis FS : 140735332483408 <= S <= 140737488355328.     (* [comment removed for export] *)
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fimg : first + 42 <= 65536 \/ 962560 <= first.      (* [comment removed for export] *)
Hypothesis Fdj : S - 336 + 336 <= first \/ first + 42 <= S - 336.
Hypothesis Fvp : 4096 <= vp <= 140737488355312.
Hypothesis Fvp8 : vp mod 8 = 0.
Hypothesis FvS : S <= vp.
Hypothesis Fvf : first + 42 <= vp \/ vp + 16 <= first.
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.

Abbreviation MI := (PNSDD.MI R0 S first r).
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 35%nat => vp | 36%nat => lo | 37%nat => hi
  | 60%nat => r | 61%nat => u8 | 62%nat => u9 | 63%nat => u18 | 64%nat => u19 | 65%nat => u20 | 66%nat => u21 | 67%nat => u22 | 68%nat => u23 | _ => 0 end.

Lemma ufacts : 0 <= u8 < 2 ^ 64 /\ 0 <= u9 < 2 ^ 64 /\ 0 <= u18 < 2 ^ 64 /\ 0 <= u19 < 2 ^ 64 /\ 0 <= u20 < 2 ^ 64 /\ 0 <= u21 < 2 ^ 64
  /\ 0 <= u22 < 2 ^ 64 /\ 0 <= u23 < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 8))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 9))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 18))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 19))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 20))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 21))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 22))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 23))).
  unfold bv_modulus in *. subst u8 u9 u18 u19 u20 u21 u22 u23. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition ent_post fx (M : word -> option byte) fx' R' M' (sigma : Z) : Prop :=
  mem_grows M M' /\ msteps RSEGS (st fx R0 0x38a78 M) (st fx' R' 0x38afc M')
  /\ PNSDD.stJ R0 S first sigma vp R' /\ (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R0 (reg k))
  /\ MI M' /\ (PNSDD.zers S M' 4 /\ L5.defined M' (S - 216) 144) /\ PNSDD.vp_at M' vp lo hi
  /\ PMST.base_ok RSEGS AD M' /\ PNST.berr_ok RSEGS AD AN M' (PNST.bax_add_dec ax)
  /\ 0 <= sigma <= 1 /\ (2 ^ 63 <= hi <-> sigma = 1)
  /\ PNSDD.agree_but (fun a => S - 336 <= a < S \/ (first <= a < first + 1) \/ (PNST.bax_dec ax = false /\ PMK.inW (PNST.dec_W AD AN) a)) M M'.

(* [comment removed for export] *)
Lemma zers_of_zeros M : L5KA.zeros_at M (S - 216) 144 -> PNSDD.zers S M 4.
Proof.
  intros Z0 i Hi. unfold PNSDD.cell. apply (PNMW.u32_of_zeros RSEGS M (S - 216) 144); [exact Z0| clear -Hi; lia| clear -Hi; lia| clear -FS; lia| clear -FS; lia].
Qed.

Local Ltac x8 FZ C := apply (L5C.u8_at_agree RSEGS _ _ _ _ ltac:(intros i Hi; apply FZ; revert Hi; clear -FS Ffirst Fimg Fvp Fvf FvS; intros Hi; lia) ltac:(clear; lia) ltac:(clear; lia) C).
Local Ltac x64 FZ C := apply (L5C.u64_at_agree RSEGS _ _ _ _ ltac:(intros i Hi; apply FZ; revert Hi; clear -FS Ffirst Fimg Fvp Fvf FvS; intros Hi; lia) ltac:(clear -FS Fvp; lia) ltac:(clear -FS Fvp; lia) C).
Local Ltac x32 FZ C := apply (PNMW.u32_at_agree RSEGS _ _ _ _ ltac:(intros i Hi; apply FZ; revert Hi; clear -FS Ffirst Fimg Fvp Fvf FvS; intros Hi; lia) ltac:(clear; lia) ltac:(clear; lia) C).
Local Ltac xcl FZ C := apply (PMKP.clear_agree _ _ _ _ ltac:(intros i Hi; apply FZ; revert Hi; clear -FS Ffirst Fimg Fvp Fvf FvS; intros Hi; lia) C).

(* [comment removed for export] *)
Lemma base_keep (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> (S - 336 <= a < S) \/ (first <= a < first + 42) \/ (820616 <= a < 820680) \/ (958472 <= a < 959016)) ->
  PMST.base_ok RSEGS AD M -> PMST.base_ok RSEGS AD M'.
Proof.
  intros FZ PW (IC & (c & Hc & CAN) & NL & LL). cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in *.
  assert (FZ' : forall a, 0 <= a < 2 ^ 64 -> ~ ((S - 336 <= a < S) \/ (first <= a < first + 42) \/ (820616 <= a < 820680) \/ (958472 <= a < 959016)) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. apply PW. exact X. }
  unfold PMST.base_ok. cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S].
  assert (AG : forall a n, (a + n <= S - 336 \/ S <= a) -> (a + n <= first \/ first + 42 <= a) -> (a + n <= 820616 \/ 820680 <= a) -> (a + n <= 958472 \/ 959016 <= a) ->
                0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M' a n).
  { intros a n H1 H2 H3 H4 Ha Hn i Hi. apply FZ'; [clear -Hi Ha Hn; lia| clear -Hi H1 H2 H3 H4; lia]. }
  split; [apply (PMKP.clear_agree M M'); [apply AG; clear -FS Ffirst Fimg; lia| exact IC]|].
  split; [exists c; split; [exact Hc| apply (L5C.u64_at_agree RSEGS M M'); [apply AG; clear -FS Ffirst Fimg; lia| clear; lia| clear; lia| exact CAN]]|].
  split; [apply (PMKP.clear_agree M M'); [apply AG; clear -FS Ffirst Fimg; lia| exact NL]| apply (PMKP.clear_agree M M'); [apply AG; clear -FS Ffirst Fimg; lia| exact LL]].
Qed.
Lemma berr_keep (M M' : word -> option byte) (P : Z -> Prop) bx :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, P a -> (S - 336 <= a < S) \/ (first <= a < first + 42)) ->
  PNST.berr_ok RSEGS AD AN M bx -> PNST.berr_ok RSEGS AD AN M' bx.
Proof.
  intros FZ PW ERR. apply (PNKP.berr_agree RSEGS AD AN PNRS.addrs_wf_B M M'); [| exact ERR].
  intros a Ha D. apply FZ; [exact Ha|]. intros X. apply PW in X. unfold PNKP.edep, PNL.pn_d128_foot in D. cbn in D.
  destruct D as [D|[D|(iv & Hin & D)]]; [clear -X D Ffirst Fimg FS; lia| clear -X D Ffirst Fimg FS; lia|].
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in D; clear -X D Ffirst Fimg FS; lia.
Qed.

(* [comment removed for export] *)
Lemma warm fx M :
  PNST.bax_dec ax = true ->
  L5.writable RSEGS M (S - 336) 336 -> L5.writable RSEGS M first 42 -> PNSDD.vp_at M vp lo hi ->
  PMST.base_ok RSEGS AD M -> PNST.berr_ok RSEGS AD AN M ax ->
  exists fx' R' M' sigma, ent_post fx M fx' R' M' sigma.
Proof.
  intros ED WRF WR1 (VLO & VHI) BASE ERR.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof BASE as (IC & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IC.
  pose proof ERR as (EG & EDEC & EA). rewrite ED in EDEC.
  pose proof EDEC as (G1 & G2 & (BI & DI) & (BN & DN)). unfold PNST.sso_lit in BI, DI, BN, DN.
  cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in G1, G2, DI, BI, DN, BN.
  assert (WRf : L5.writable RSEGS M (S - 256) 256) by (apply (L5.writable_sub RSEGS M (S - 336) 336 _ _ WRF); clear; lia).
  (let T := type of (PNSDAP.dkA_conc fx R0 M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkA_conc fx R0 M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  assert (EADD : PNST.bax_add_dec ax = ax) by (apply PNST.bax_add_dec_id; exact ED).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & B2 & B8 & B9 & B10 & B18 & B19 & SGN & ZR & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9)
                                                  | (MS1 & KS1 & B2 & B8 & B9 & B10 & B18 & B19 & MINUS & SGN & ZR & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) ]).
  - exists fx1, R1, M1, 0. rewrite (slt_sign _ _ hi Fhi eq_refl) in SGN.
    assert (Hs : hi < 2 ^ 63) by (destruct (Z.leb_spec (2 ^ 63) hi); [exfalso; clear -SGN; lia| assumption]). clear SGN.
    assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((S - 240 <= a < S) \/ (first <= a < first + 1)) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; clear -X; lia| intros X; apply N; right; clear -X; lia]. }
    assert (AG : forall a n, (a + n <= S - 240 \/ S <= a) -> (a + n <= first \/ first + 1 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n).
    { intros a n H1 H2 Ha Hn i Hi. apply FZ; [clear -Hi Ha Hn; lia| clear -Hi H1 H2; lia]. }
    unfold ent_post. rewrite EADD.
    split; [exact MG1|]. split; [exact MS1|].
    split. { unfold PNSDD.stJ, PNSDD.RB. rewrite ?(KS1 3%nat), ?(KS1 4%nat), ?(KS1 24%nat), ?(KS1 25%nat), ?(KS1 26%nat), ?(KS1 27%nat) by PMK.inl.
             repeat apply conj; first [exact B2 | exact B9 | exact B8 | exact B18 | rewrite B9; f_equal; clear; lia | reflexivity | exact B19]. }
    split; [intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
    split. { split; [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WRf)|]. split; [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WR1)|].
             split; [apply (PMKP.clear_agree M M1); [apply AG; clear -FS Ffirst Fimg; lia| exact IC]|].
             unfold PNSDD.saves. rewrite A1, L5.unsigned_lit in C9 by (clear -Fr; lia).
             split; [exact C9|]. split; [exact C8|]. split; [exact C7|]. split; [exact C6|]. split; [exact C5|]. split; [exact C4|]. split; [exact C3|]. split; [exact C2| exact C1]. }
    split; [split; [apply zers_of_zeros; exact ZR| exact (L5KA.zeros_at_defined _ _ _ ZR)]|].
    split; [split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; clear -FS FvS Fvf Fvp; lia| clear -Fvp; lia| clear -Fvp; lia| assumption])|].
    split; [apply (base_keep M M1 _ FZ); [intros a Ha; clear -Ha; lia| exact BASE]|].
    split; [apply (berr_keep M M1 _ _ FZ); [intros a Ha; clear -Ha; lia| exact ERR]|].
    split; [clear; lia|]. split; [split; intros X; exfalso; clear -X Hs; lia|].
    intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. destruct X as [X|X]; [left; clear -X; lia| right; left; exact X].
  - exists fx1, R1, M1, 1. rewrite (slt_sign _ _ hi Fhi eq_refl) in SGN.
    assert (Hs : 2 ^ 63 <= hi) by (destruct (Z.leb_spec (2 ^ 63) hi); [assumption| exfalso; clear -SGN; lia]). clear SGN.
    assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((S - 240 <= a < S) \/ (first <= a < first + 1)) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; clear -X; lia| intros X; apply N; right; clear -X; lia]. }
    assert (AG : forall a n, (a + n <= S - 240 \/ S <= a) -> (a + n <= first \/ first + 1 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n).
    { intros a n H1 H2 Ha Hn i Hi. apply FZ; [clear -Hi Ha Hn; lia| clear -Hi H1 H2; lia]. }
    unfold ent_post. rewrite EADD.
    split; [exact MG1|]. split; [exact MS1|].
    split. { unfold PNSDD.stJ, PNSDD.RB. rewrite ?(KS1 3%nat), ?(KS1 4%nat), ?(KS1 24%nat), ?(KS1 25%nat), ?(KS1 26%nat), ?(KS1 27%nat) by PMK.inl.
             repeat apply conj; first [exact B2 | exact B9 | exact B8 | exact B18 | rewrite B9; f_equal; clear; lia | reflexivity | exact B19]. }
    split; [intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
    split. { split; [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WRf)|]. split; [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WR1)|].
             split; [apply (PMKP.clear_agree M M1); [apply AG; clear -FS Ffirst Fimg; lia| exact IC]|].
             unfold PNSDD.saves. rewrite A1, L5.unsigned_lit in C9 by (clear -Fr; lia).
             split; [exact C9|]. split; [exact C8|]. split; [exact C7|]. split; [exact C6|]. split; [exact C5|]. split; [exact C4|]. split; [exact C3|]. split; [exact C2| exact C1]. }
    split; [split; [apply zers_of_zeros; exact ZR| exact (L5KA.zeros_at_defined _ _ _ ZR)]|].
    split; [split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; clear -FS FvS Fvf Fvp; lia| clear -Fvp; lia| clear -Fvp; lia| assumption])|].
    split; [apply (base_keep M M1 _ FZ); [intros a Ha; clear -Ha; lia| exact BASE]|].
    split; [apply (berr_keep M M1 _ _ FZ); [intros a Ha; clear -Ha; lia| exact ERR]|].
    split; [clear; lia|]. split; [split; intros X; [reflexivity| exact Hs]|].
    intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. destruct X as [X|X]; [left; clear -X; lia| right; left; exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma slots_xfer (M M' : word -> option byte) l : forall i,
  (forall a, 958472 <= a < 959016 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> 0 <= i -> i + Z.of_nat (length l) <= 32 ->
  PNST.slots_at RSEGS M 958472 i l -> PNST.slots_at RSEGS M' 958472 i l.
Proof.
  induction l as [|[f a] t IH]; intros i AG Hi Hl SL; [exact I|]. cbn [length] in Hl.
  destruct SL as (F & A & SL'). cbn [PNST.slots_at].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [intros j Hj; apply AG; clear -Hj Hi Hl; lia| clear -Hi; lia| clear -Hi Hl; lia| exact F]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [intros j Hj; apply AG; clear -Hj Hi Hl; lia| clear -Hi; lia| clear -Hi Hl; lia| exact A]|].
  apply IH; [exact AG| clear -Hi; lia| clear -Hl; lia| exact SL'].
Qed.
Lemma batexit_xfer (M M' : word -> option byte) bx :
  (forall a, 958472 <= a < 959016 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PNST.batexit_st RSEGS AD AN M bx -> PNST.batexit_st RSEGS AD AN M' bx.
Proof.
  intros AG. unfold PNST.batexit_st. cbv zeta. cbn [pa_atexit AD PnLayoutS_u.ADDR_S].
  (* [comment removed for export] *)
  assert (LEN : Z.of_nat (length (PNST.bax_drv AN :: PNST.bax_list AD AN bx)) <= 4) by (destruct bx; cbn; clear; lia).
  assert (LEN1 : 1 <= Z.of_nat (length (PNST.bax_drv AN :: PNST.bax_list AD AN bx))) by (cbn [length]; clear; lia).
  assert (CL : forall p q, 958472 <= p -> q <= 959016 -> L5.img_clear M p q -> L5.img_clear M' p q).
  { intros p q H1 H2 C i Hi. rewrite AG; [apply C; exact Hi| clear -Hi H1 H2; lia]. }
  intros (C1 & S1 & C2 & H & C3 & SL & C4 & C5).
  split; [apply CL; [clear; lia| clear; lia| exact C1]|].
  split; [apply (PNMW.u32_at_agree RSEGS M M'); [intros j Hj; apply AG; clear -Hj; lia| clear; lia| clear; lia| exact S1]|].
  split; [apply CL; [clear; lia| clear; lia| exact C2]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [intros j Hj; apply AG; clear -Hj; lia| clear; lia| clear; lia| exact H]|].
  split; [apply CL; [clear; lia| clear; lia| exact C3]|].
  split; [apply (slots_xfer M M' (PNST.bax_drv AN :: PNST.bax_list AD AN bx) 0 AG); [clear; lia| clear -LEN; lia| exact SL]|].
  split; (apply CL; [clear -LEN LEN1; lia| clear -LEN LEN1; lia| assumption]).
Qed.
Lemma bax_cat_add_dec bx : PNST.bax_cat (PNST.bax_add_dec bx) = PNST.bax_cat bx.
Proof. destruct bx; reflexivity. Qed.

(* [comment removed for export] *)
Definition cmw (a : Z) : Prop := (S - 336 <= a < S - 240) \/ (820640 <= a < 820680) \/ (958472 <= a < 959016).

Lemma cold_mid fx2 R2 M2 :
  PNST.bax_dec ax = false ->
  getr R2 (reg 2) = Z_to_bv 64 (S - 256) -> getr R2 (reg 8) = Z_to_bv 64 (first + 42) -> getr R2 (reg 18) = Z_to_bv 64 first -> getr R2 (reg 19) = Z_to_bv 64 vp ->
  (forall k, In k [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr R0 (reg k)) ->
  L5.writable RSEGS M2 (S - 336) 336 -> L5.img_clear M2 65536 754672 -> L5.img_clear M2 959059 959060 -> L5.img_clear M2 820672 820680 ->
  PNST.batexit_st RSEGS AD AN M2 ax ->
  exists fx5 R5 M5, msteps RSEGS (st fx2 R2 0x391c4 M2) (st fx5 R5 0x38acc M5) /\ mem_grows M2 M5
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ cmw a -> M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))
    /\ getr R5 (reg 2) = Z_to_bv 64 (S - 256) /\ getr R5 (reg 8) = Z_to_bv 64 (first + 42) /\ getr R5 (reg 18) = Z_to_bv 64 first /\ getr R5 (reg 19) = Z_to_bv 64 vp
    /\ (forall k, In k [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R0 (reg k))
    /\ L5.u8_at RSEGS M5 820640 1 /\ L5.u8_at RSEGS M5 820672 1 /\ PNSSC.sso M5 820648 3 /\ PNST.batexit_st RSEGS AD AN M5 (PNST.bax_add_dec ax).
Proof.
  intros ED G2 G8 G18 G19 GK WRF IC NL CG2 EA.
  pose proof (PMCK.writable_img M2 958472 544 wseg_atexit ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as WAT.
  pose proof (PMCK.writable_img M2 820672 8 wseg_nang ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as WNG.
  pose proof (PMCK.writable_img M2 820640 8 wseg_infg ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as WIG.
  (* [comment removed for export] *)
  assert (STEP3 : exists fx3 R3 M3, mem_grows M2 M3
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ cmw i -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
    /\ msteps RSEGS (st fx2 R2 0x391c4 M2) (st fx3 R3 0x37f44 M3)
    /\ (forall k, In k [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k) = getr R2 (reg k))
    /\ getr R3 (reg 1) = Z_to_bv 64 0x39218 /\ getr R3 (reg 10) = Z_to_bv 64 820648 /\ getr R3 (reg 11) = Z_to_bv 64 73575
    /\ L5.u8_at RSEGS M3 820640 1
    /\ (L5.img_clear M3 958472 958480 /\ L5.img_clear M3 958484 958488 /\ L5.u64_at RSEGS M3 958488 958496 /\ L5.img_clear M3 958496 958504)
    /\ L5.u64_at RSEGS M3 958504 634268 /\ L5.u64_at RSEGS M3 958760 214692
    /\ (   (ax = PNST.AX0 /\ L5.u32_at RSEGS M3 958480 2 /\ L5.u64_at RSEGS M3 958512 361520 /\ L5.u64_at RSEGS M3 958768 820616
                         /\ L5.img_clear M3 958520 958760 /\ L5.img_clear M3 958776 959016)
        \/ (ax = PNST.AXc /\ L5.u32_at RSEGS M3 958480 3 /\ L5.u64_at RSEGS M3 958512 (pa_errcat_dtor AD) /\ L5.u64_at RSEGS M3 958768 (pa_errcat_obj AD)
                         /\ L5.u64_at RSEGS M3 958520 361520 /\ L5.u64_at RSEGS M3 958776 820616
                         /\ L5.img_clear M3 958528 958760 /\ L5.img_clear M3 958784 959016))).
  { unfold PNST.batexit_st in EA. cbv zeta in EA.
    destruct ax; cbn in ED; try discriminate ED; clear ED;
      cbn [PNST.bax_list length Z.of_nat Pos.of_succ_nat Pos.succ pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S PNST.slots_at PNST.bax_drv PNL.pn_drv_call PNL.pn_drv_guard fst snd Z.mul Z.add] in EA.
    - (* [comment removed for export] *)
      destruct EA as (X0 & XN & X12 & XH & X24 & (DF0 & DA0 & _) & XCF & XCA).
      (let T := type of (PNSDEP.dkC20_conc fx2 R2 M2 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDEP.dkC20_conc fx2 R2 M2 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
      destruct P as (fx3 & R3 & M3 & MG3 & FW3 & FZ3 & MS3 & KS3 & B1 & B10 & B11 & B12 & B13 & GN2 & GI1b & GI1 & CNT & SA1 & SF1 & HD).
      exists fx3, R3, M3. split; [exact MG3|].
      split. { intros i Hi N. apply FZ3; [exact Hi| | | | | | |]; intros X; apply N; unfold cmw; clear -X; lia. }
      split; [exact MS3|]. split; [intros k Hk; apply KS3; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact B1|]. split; [exact B10|]. split; [exact B11|]. split; [exact GI1|].
      assert (AG3 : forall a n, 958472 <= a -> a + n <= 959016 -> (a + n <= 958480 \/ (958484 <= a /\ a + n <= 958488) \/ (958496 <= a /\ a + n <= 958512) \/ (958520 <= a /\ a + n <= 958768) \/ 958776 <= a) ->
                    L5C.agree_on M2 M3 a n).
      { intros a n H1 H2 H3 i Hi. apply FZ3; [clear -Hi H1 H2; lia| | | | | | |]; clear -Hi H1 H2 H3 FS; lia. }
      split. { split; [apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia| exact X0]|]. split; [apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia| exact X12]|].
               split; [exact HD| apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia| exact X24]]. }
      split; [apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; clear; lia| clear; lia| clear; lia| exact DF0]|].
      split; [apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; clear; lia| clear; lia| clear; lia| exact DA0]|].
      left. split; [reflexivity|]. split; [exact CNT|].
      split; [exact SF1|]. split; [exact SA1|].
      split; (apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia|]); [|].
      + intros i Hi. apply XCF. clear -Hi. lia.
      + intros i Hi. apply XCA. clear -Hi. lia.
    - (* [comment removed for export] *)
      destruct EA as (X0 & XN & X12 & XH & X24 & (DF0 & DA0 & XF0 & XA0 & _) & XCF & XCA).
      (let T := type of (PNSDEP.dkC2c_conc fx2 R2 M2 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDEP.dkC2c_conc fx2 R2 M2 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
      destruct P as (fx3 & R3 & M3 & MG3 & FW3 & FZ3 & MS3 & KS3 & B1 & B10 & B11 & B12 & B13 & GN2 & GI1b & GI1 & CNT & SA2 & SF2 & HD).
      exists fx3, R3, M3. split; [exact MG3|].
      split. { intros i Hi N. apply FZ3; [exact Hi| | | | | | |]; intros X; apply N; unfold cmw; clear -X; lia. }
      split; [exact MS3|]. split; [intros k Hk; apply KS3; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact B1|]. split; [exact B10|]. split; [exact B11|]. split; [exact GI1|].
      assert (AG3 : forall a n, 958472 <= a -> a + n <= 959016 -> (a + n <= 958480 \/ (958484 <= a /\ a + n <= 958488) \/ (958496 <= a /\ a + n <= 958520) \/ (958528 <= a /\ a + n <= 958776) \/ 958784 <= a) ->
                    L5C.agree_on M2 M3 a n).
      { intros a n H1 H2 H3 i Hi. apply FZ3; [clear -Hi H1 H2; lia| | | | | | |]; clear -Hi H1 H2 H3 FS; lia. }
      split. { split; [apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia| exact X0]|]. split; [apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia| exact X12]|].
               split; [exact HD| apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia| exact X24]]. }
      split; [apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; clear; lia| clear; lia| clear; lia| exact DF0]|].
      split; [apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; clear; lia| clear; lia| clear; lia| exact DA0]|].
      right. split; [reflexivity|]. split; [exact CNT|].
      split; [apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; clear; lia| clear; lia| clear; lia| exact XF0]|].
      split; [apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; clear; lia| clear; lia| clear; lia| exact XA0]|].
      split; [exact SF2|]. split; [exact SA2|].
      split; (apply (PMKP.clear_agree M2 M3); [apply AG3; clear; lia|]); [|].
      + intros i Hi. apply XCF. clear -Hi. lia.
      + intros i Hi. apply XCA. clear -Hi. lia. }
  destruct STEP3 as (fx3 & R3 & M3 & MG3 & FZ3 & MS3 & KS3 & B1 & B10 & B11 & GI1 & (X0 & X12 & XH & X24) & DF0 & DA0 & SHAPE).
  (* [comment removed for export] *)
  assert (IC3 : L5.img_clear M3 65536 754672) by (apply (PMKP.clear_agree M2 M3); [intros i Hi; apply FZ3; [clear -Hi; lia| unfold cmw; clear -Hi FS; lia]| exact IC]).
  destruct (PNSSC.str_cstr_lit false fx3 R3 M3 (S - 256) 820648 0x39218 B10 B11 B1 ltac:(rewrite (KS3 2%nat) by PMK.inl; exact G2)
              ltac:(split; [clear; lia| reflexivity]) ltac:(clear -FS; lia) (PNSDSPC_mod16 _ F16)
              ltac:(apply (L5.writable_sub RSEGS M3 (S - 336) 336); [exact (L5.writable_grows RSEGS M2 M3 _ _ MG3 WRF)| clear; lia| clear; lia])
              ltac:(clear; lia) ltac:(apply (L5.writable_grows RSEGS M2 M3 _ _ MG3); apply (PMCK.writable_img M2 820648 24 wseg_nano); clear; lia)
              ltac:(right; clear -FS; lia) IC3)
    as (fx4 & R4 & M4 & MS4 & MG4 & FZ4 & SSO4 & E4 & KS4).
  cbn [PNSSC.len] in SSO4.
  (* [comment removed for export] *)
  assert (IC4 : L5.img_clear M4 65536 754672) by (apply (PMKP.clear_agree M3 M4); [intros i Hi; apply FZ4; clear -Hi FS; lia| exact IC3]).
  assert (NL4 : L5.img_clear M4 959059 959060).
  { apply (PMKP.clear_agree M3 M4); [intros i Hi; apply FZ4; clear -Hi FS; lia|].
    apply (PMKP.clear_agree M2 M3); [intros i Hi; apply FZ3; [clear -Hi; lia| unfold cmw; clear -Hi FS; lia]| exact NL]. }
  assert (AG34 : forall a n, (a + n <= S - 304 \/ S - 256 <= a) -> (a + n <= 820648 \/ 820672 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M3 M4 a n).
  { intros a n H1 H2 Ha Hn i Hi. apply FZ4; [clear -Hi Ha Hn; lia| clear -Hi H1; lia| clear -Hi H2; lia]. }
  assert (GI14 : L5.u8_at RSEGS M4 820640 1) by (apply (L5C.u8_at_agree RSEGS M3 M4); [apply AG34; clear -FS; lia| clear; lia| clear; lia| exact GI1]).
  assert (STEP5 : exists fx5 R5 M5, mem_grows M4 M5
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ cmw i -> M5 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i))
    /\ msteps RSEGS (st fx4 R4 0x39218 M4) (st fx5 R5 0x38acc M5)
    /\ (forall k, In k [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R4 (reg k))
    /\ L5.u8_at RSEGS M5 820672 1 /\ PNST.batexit_st RSEGS AD AN M5 (PNST.bax_add_dec ax)
    /\ L5.u8_at RSEGS M5 820640 1 /\ PNSSC.sso M5 820648 3).
  { destruct SHAPE as [(-> & CNT & SF1 & SA1 & XCF & XCA)|(-> & CNT & XF1 & XA1 & SF2 & SA2 & XCF & XCA)].
    - (let T := type of (PNSDEP.dkC30_conc fx4 R4 M4 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDEP.dkC30_conc fx4 R4 M4 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS4 _) by PMK.inl; rewrite (KS3 _) by PMK.inl; PMK.sc
                             | exact (L5.writable_grows RSEGS M2 M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) WRF)
                             | exact (L5.writable_grows RSEGS M2 M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) WAT)
                             | exact (L5.writable_grows RSEGS M2 M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) WNG)
                             | apply (PMKP.clear_agree M3 M4); [apply AG34; clear -FS; lia| assumption]
                             | apply (PNMW.u32_at_agree RSEGS M3 M4); [apply AG34; clear -FS; lia| clear; lia| clear; lia| assumption]
                             | apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG34; clear -FS; lia| clear; lia| clear; lia| assumption] ])).
      destruct P as (fx5 & R5 & M5 & MG5 & FW5 & FZ5 & MS5 & KS5 & _ & _ & _ & _ & _ & GN1b & GN1 & CNT3 & SAn & SFn & HD5).
      exists fx5, R5, M5. split; [exact MG5|].
      split. { intros i Hi N. apply FZ5; [exact Hi| | | | | |]; intros X; apply N; unfold cmw; clear -X; lia. }
      split; [exact MS5|]. split; [intros k Hk; apply KS5; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|]. split; [exact GN1|].
      split; cycle 1.
      { split; [apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply FZ5; clear -Hi FS; lia| clear; lia| clear; lia| exact GI14]|].
        destruct SSO4 as (SB & SD). split; [| exact (L5.defined_grows M4 M5 _ _ MG5 SD)].
        apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply FZ5; clear -Hi FS; lia| clear; lia| clear; lia| exact SB]. }
      assert (AG35 : forall a n, (a + n <= S - 336 \/ S - 240 <= a) -> (a + n <= 820648 \/ 820674 <= a) ->
                (a + n <= 958480 \/ (958484 <= a /\ a + n <= 958488) \/ (958496 <= a /\ a + n <= 958520) \/ (958528 <= a /\ a + n <= 958776) \/ 958784 <= a) ->
                0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M3 M5 a n).
      { intros a n H1 H2 H3 Ha Hn i Hi. rewrite (FZ5 i) by (clear -Hi Ha Hn H1 H2 H3 FS; lia). apply FZ4; clear -Hi Ha Hn H1 H2; lia. }
      unfold PNST.batexit_st. cbv zeta.
      cbn [PNST.bax_add_dec PNST.bax_list length Z.of_nat Pos.of_succ_nat Pos.succ pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S PNST.slots_at PNST.bax_drv PNL.pn_drv_call PNL.pn_drv_guard fst snd Z.mul Z.add].
      split; [apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia| exact X0]|]. split; [exact CNT3|].
      split; [apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia| exact X12]|]. split; [exact HD5|].
      split; [apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia| exact X24]|].
      split. { split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact DF0]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact DA0]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact SF1]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact SA1]|].
               split; [exact SFn|]. split; [exact SAn| exact I]. }
      split; (apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia|]); [intros i Hi; apply XCF; clear -Hi; lia| intros i Hi; apply XCA; clear -Hi; lia].
    - (let T := type of (PNSDEP.dkC3c_conc fx4 R4 M4 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDEP.dkC3c_conc fx4 R4 M4 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS4 _) by PMK.inl; rewrite (KS3 _) by PMK.inl; PMK.sc
                             | exact (L5.writable_grows RSEGS M2 M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) WRF)
                             | exact (L5.writable_grows RSEGS M2 M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) WAT)
                             | exact (L5.writable_grows RSEGS M2 M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) WNG)
                             | apply (PMKP.clear_agree M3 M4); [apply AG34; clear -FS; lia| assumption]
                             | apply (PNMW.u32_at_agree RSEGS M3 M4); [apply AG34; clear -FS; lia| clear; lia| clear; lia| assumption]
                             | apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG34; clear -FS; lia| clear; lia| clear; lia| assumption] ])).
      destruct P as (fx5 & R5 & M5 & MG5 & FW5 & FZ5 & MS5 & KS5 & _ & _ & _ & _ & _ & GN1b & GN1 & CNT4 & SA3 & SF3 & HD5).
      exists fx5, R5, M5. split; [exact MG5|].
      split. { intros i Hi N. apply FZ5; [exact Hi| | | | | |]; intros X; apply N; unfold cmw; clear -X; lia. }
      split; [exact MS5|]. split; [intros k Hk; apply KS5; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|]. split; [exact GN1|].
      split; cycle 1.
      { split; [apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply FZ5; clear -Hi FS; lia| clear; lia| clear; lia| exact GI14]|].
        destruct SSO4 as (SB & SD). split; [| exact (L5.defined_grows M4 M5 _ _ MG5 SD)].
        apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply FZ5; clear -Hi FS; lia| clear; lia| clear; lia| exact SB]. }
      assert (AG35 : forall a n, (a + n <= S - 336 \/ S - 240 <= a) -> (a + n <= 820648 \/ 820674 <= a) ->
                (a + n <= 958480 \/ (958484 <= a /\ a + n <= 958488) \/ (958496 <= a /\ a + n <= 958528) \/ (958536 <= a /\ a + n <= 958784) \/ 958792 <= a) ->
                0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M3 M5 a n).
      { intros a n H1 H2 H3 Ha Hn i Hi. rewrite (FZ5 i) by (clear -Hi Ha Hn H1 H2 H3 FS; lia). apply FZ4; clear -Hi Ha Hn H1 H2; lia. }
      unfold PNST.batexit_st. cbv zeta.
      cbn [PNST.bax_add_dec PNST.bax_list length Z.of_nat Pos.of_succ_nat Pos.succ pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S PNST.slots_at PNST.bax_drv PNL.pn_drv_call PNL.pn_drv_guard fst snd Z.mul Z.add].
      cbn [pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S] in XF1, XA1.
      split; [apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia| exact X0]|]. split; [exact CNT4|].
      split; [apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia| exact X12]|]. split; [exact HD5|].
      split; [apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia| exact X24]|].
      split. { split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact DF0]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact DA0]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact XF1]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact XA1]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact SF2]|].
               split; [apply (L5C.u64_at_agree RSEGS M3 M5); [apply AG35; clear -FS; lia| clear; lia| clear; lia| exact SA2]|].
               split; [exact SF3|]. split; [exact SA3| exact I]. }
      split; (apply (PMKP.clear_agree M3 M5); [apply AG35; clear -FS; lia|]); [intros i Hi; apply XCF; clear -Hi; lia| intros i Hi; apply XCA; clear -Hi; lia]. }
  destruct STEP5 as (fx5 & R5 & M5 & MG5 & FZ5 & MS5 & KS5 & GN1 & AT5 & GI5 & SSO5).
  exists fx5, R5, M5.
  split. { eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4| exact MS5]. }
  split; [exact (mem_grows_trans _ _ _ MG3 (mem_grows_trans _ _ _ MG4 MG5))|].
  split. { intros a Ha N. rewrite (FZ5 a Ha N). rewrite (FZ4 a Ha) by (unfold cmw in N; clear -N; intros X; apply N; lia). apply FZ3; [exact Ha| exact N]. }
  split; [rewrite (KS5 2%nat) by PMK.inl; exact E4|].
  split; [rewrite (KS5 8%nat), (KS4 8%nat), (KS3 8%nat) by PMK.inl; exact G8|].
  split; [rewrite (KS5 18%nat), (KS4 18%nat), (KS3 18%nat) by PMK.inl; exact G18|].
  split; [rewrite (KS5 19%nat), (KS4 19%nat), (KS3 19%nat) by PMK.inl; exact G19|].
  split. { intros k Hk. rewrite (KS5 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS4 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
           rewrite (KS3 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply GK. exact Hk. }
  split; [exact GI5|]. split; [exact GN1|]. split; [exact SSO5| exact AT5].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cold fx M :
  PNST.bax_dec ax = false ->
  L5.writable RSEGS M (S - 336) 336 -> L5.writable RSEGS M first 42 -> PNSDD.vp_at M vp lo hi ->
  PMST.base_ok RSEGS AD M -> PNST.berr_ok RSEGS AD AN M ax ->
  exists fx' R' M' sigma, ent_post fx M fx' R' M' sigma.
Proof.
  intros ED WRF WR1 (VLO & VHI) BASE ERR.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof BASE as (IC & _ & NL & _). cbn [pa_rw_lo pa_need_locks AD PnLayoutS_u.ADDR_S] in IC, NL.
  pose proof ERR as (EG & EDEC & EA). rewrite ED in EDEC.
  pose proof EDEC as (CG1 & CG2 & CO1 & CO2). cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.add] in CG1, CG2, CO1, CO2.
  assert (WRf : L5.writable RSEGS M (S - 256) 256) by (apply (L5.writable_sub RSEGS M (S - 336) 336 _ _ WRF); clear; lia).
  pose proof (PMCK.writable_img M 820672 8 wseg_nang ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as WNG.
  pose proof (PMCK.writable_img M 820640 8 wseg_infg ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as WIG.
  (let T := type of (PNSDEP.dkC1_conc fx R0 M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDEP.dkC1_conc fx R0 M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & B1 & B2 & B8 & B10 & B11 & B12 & B18 & B19 & GP & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  assert (AG1 : forall a n, (a + n <= S - 240 \/ S <= a) -> (a + n <= 820640 \/ 820642 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n).
  { intros a n H1 H2 Ha Hn i Hi. apply FZ1; [clear -Hi Ha Hn; lia| clear -Hi H1; lia| clear -Hi H2; lia]. }
  (* [comment removed for export] *)
  assert (IC1 : L5.img_clear M1 65536 754672) by (apply (PMKP.clear_agree M M1); [apply AG1; clear -FS; lia| exact IC]).
  destruct (PNSSC.str_cstr_lit true fx1 R1 M1 (S - 256) 820616 0x391c4 B10 B11 B1 B2
              ltac:(split; [clear; lia| reflexivity]) ltac:(clear -FS; lia) (PNSDSPC_mod16 _ F16)
              ltac:(apply (L5.writable_sub RSEGS M1 (S - 336) 336); [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WRF)| clear; lia| clear; lia])
              ltac:(clear; lia) ltac:(apply (L5.writable_grows RSEGS M M1 _ _ MG1); apply (PMCK.writable_img M 820616 24 wseg_info); clear; lia)
              ltac:(right; clear -FS; lia) IC1)
    as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SSO2 & E2 & KS2).
  cbn [PNSSC.len] in SSO2.
  assert (AG2 : forall a n, (a + n <= S - 304 \/ S - 256 <= a) -> (a + n <= 820616 \/ 820640 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 Ha Hn i Hi. apply FZ2; [clear -Hi Ha Hn; lia| clear -Hi H1; lia| clear -Hi H2; lia]. }
  (* [comment removed for export] *)
  destruct (cold_mid fx2 R2 M2 ED E2 ltac:(rewrite (KS2 8%nat) by PMK.inl; exact B8) ltac:(rewrite (KS2 18%nat) by PMK.inl; exact B18) ltac:(rewrite (KS2 19%nat) by PMK.inl; exact B19)
              ltac:(intros k Hk; rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto); apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto)
              (L5.writable_grows RSEGS M M2 _ _ (mem_grows_trans _ _ _ MG1 MG2) WRF)
              ltac:(apply (PMKP.clear_agree M1 M2); [apply AG2; clear -FS; lia| exact IC1])
              ltac:(apply (PMKP.clear_agree M1 M2); [apply AG2; clear -FS; lia|]; apply (PMKP.clear_agree M M1); [apply AG1; clear -FS; lia| exact NL])
              ltac:(apply (PMKP.clear_agree M1 M2); [apply AG2; clear -FS; lia|]; apply (PMKP.clear_agree M M1); [apply AG1; clear -FS; lia| exact CG2])
              ltac:(apply (batexit_xfer M1 M2); [intros a Ha; apply FZ2; clear -Ha FS; lia|]; apply (batexit_xfer M M1); [intros a Ha; apply FZ1; clear -Ha FS; lia| exact EA]))
    as (fx5 & R5 & M5 & MS5 & MG5 & FZ5 & Q2 & Q8 & Q18 & Q19 & QK & GI5 & GN5 & SSO5 & AT5).
  (* [comment removed for export] *)
  assert (AG5 : forall a n, (a + n <= S - 336 \/ S - 240 <= a) -> (a + n <= 820640 \/ 820680 <= a) -> (a + n <= 958472 \/ 959016 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M2 M5 a n).
  { intros a n H1 H2 H3 Ha Hn i Hi. apply FZ5; [clear -Hi Ha Hn; lia| unfold cmw; clear -Hi H1 H2 H3; lia]. }
  assert (IC5 : L5.img_clear M5 65536 754672).
  { apply (PMKP.clear_agree M2 M5); [apply AG5; clear -FS; lia|]. apply (PMKP.clear_agree M1 M2); [apply AG2; clear -FS; lia| exact IC1]. }
  assert (VLO5 : L5.u64_at RSEGS M5 vp lo).
  { apply (L5C.u64_at_agree RSEGS M2 M5); [apply AG5; clear -FS FvS Fvp; lia| clear -Fvp; lia| clear -Fvp; lia|].
    apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; clear -FS FvS Fvp; lia| clear -Fvp; lia| clear -Fvp; lia|].
    apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; clear -FS FvS Fvp; lia| clear -Fvp; lia| clear -Fvp; lia| exact VLO]. }
  assert (VHI5 : L5.u64_at RSEGS M5 (vp + 8) hi).
  { apply (L5C.u64_at_agree RSEGS M2 M5); [apply AG5; clear -FS FvS Fvp; lia| clear -Fvp; lia| clear -Fvp; lia|].
    apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; clear -FS FvS Fvp; lia| clear -Fvp; lia| clear -Fvp; lia|].
    apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; clear -FS FvS Fvp; lia| clear -Fvp; lia| clear -Fvp; lia| exact VHI]. }
  (let T := type of (PNSDEP.dkA2_conc fx5 R5 M5 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDEP.dkA2_conc fx5 R5 M5 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | apply (L5.writable_sub RSEGS M5 (S - 256) 256); [exact (L5.writable_grows RSEGS M M5 _ _ (mem_grows_trans _ _ _ MG1 (mem_grows_trans _ _ _ MG2 MG5)) WRf)| clear; lia| clear; lia]
                         | exact (L5.writable_grows RSEGS M M5 _ _ (mem_grows_trans _ _ _ MG1 (mem_grows_trans _ _ _ MG2 MG5)) WR1) ])).
  (* [comment removed for export] *)
  assert (FIN : forall fx6 R6 (M6 : word -> option byte) sigma,
            mem_grows M5 M6 ->
            (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 216 <= i < S - 216 + 144) -> ~ (first + 0 <= i < first + 0 + 1) -> M6 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i)) ->
            msteps RSEGS (st fx5 R5 0x38acc M5) (st fx6 R6 0x38afc M6) ->
            (forall k, In k [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg k) = getr R5 (reg k)) ->
            getr R6 (reg 9) = Z_to_bv 64 (first + sigma) ->
            L5KA.zeros_at M6 (S - 216) 144 -> 0 <= sigma <= 1 -> (2 ^ 63 <= hi <-> sigma = 1) ->
            exists fx' R' M' sigma', ent_post fx M fx' R' M' sigma').
  { intros fx6 R6 M6 sigma MG6 FZ6 MS6 KS6 B9 ZR Hs1 Hs2.
    assert (AG6 : forall a n, (a + n <= S - 216 \/ S - 72 <= a) -> (a + n <= first \/ first + 1 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M5 M6 a n).
    { intros a n H1 H2 Ha Hn i Hi. apply FZ6; [clear -Hi Ha Hn; lia| clear -Hi H1; lia| clear -Hi H2; lia]. }
    assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((S - 336 <= a < S) \/ (first <= a < first + 1) \/ (820616 <= a < 820680) \/ (958472 <= a < 959016)) ->
                 M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. rewrite (FZ6 a Ha) by (clear -N; intros X; apply N; lia). rewrite (FZ5 a Ha) by (unfold cmw; clear -N; intros X; apply N; lia).
      rewrite (FZ2 a Ha) by (clear -N; intros X; apply N; lia). apply FZ1; [exact Ha| clear -N; intros X; apply N; lia| clear -N; intros X; apply N; lia]. }
    exists fx6, R6, M6, sigma. unfold ent_post.
    split; [exact (mem_grows_trans _ _ _ MG1 (mem_grows_trans _ _ _ MG2 (mem_grows_trans _ _ _ MG5 MG6)))|].
    split. { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS5| exact MS6]. }
    split. { unfold PNSDD.stJ, PNSDD.RB.
             rewrite (KS6 2%nat), (KS6 3%nat), (KS6 4%nat), (KS6 18%nat), (KS6 8%nat), (KS6 24%nat), (KS6 25%nat), (KS6 26%nat), (KS6 27%nat), (KS6 19%nat) by PMK.inl.
             rewrite (QK 3%nat), (QK 4%nat), (QK 24%nat), (QK 25%nat), (QK 26%nat), (QK 27%nat) by PMK.inl.
             repeat apply conj; first [exact Q2 | reflexivity | exact Q18 | exact Q8 | exact B9 | exact Q19]. }
    split; [intros k Hk; rewrite (KS6 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto); apply QK; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
    split. { split; [exact (L5.writable_grows RSEGS M M6 _ _ (mem_grows_trans _ _ _ MG1 (mem_grows_trans _ _ _ MG2 (mem_grows_trans _ _ _ MG5 MG6))) WRf)|].
             split; [exact (L5.writable_grows RSEGS M M6 _ _ (mem_grows_trans _ _ _ MG1 (mem_grows_trans _ _ _ MG2 (mem_grows_trans _ _ _ MG5 MG6))) WR1)|].
             split; [apply (PMKP.clear_agree M5 M6); [apply AG6; clear -FS Ffirst Fimg; lia| exact IC5]|].
             unfold PNSDD.saves. rewrite A1, L5.unsigned_lit in C9 by (clear -Fr; lia).
             repeat lazymatch goal with
             | |- _ /\ _ => split
             | |- L5.u64_at _ M6 ?a _ =>
                 apply (L5C.u64_at_agree RSEGS M5 M6); [apply AG6; clear -FS Fdj; lia| clear -FS; lia| clear -FS; lia|];
                 apply (L5C.u64_at_agree RSEGS M2 M5); [apply AG5; clear -FS Fdj; lia| clear -FS; lia| clear -FS; lia|];
                 apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; clear -FS Fdj; lia| clear -FS; lia| clear -FS; lia| assumption]
             end. }
    split; [split; [apply zers_of_zeros; exact ZR| exact (L5KA.zeros_at_defined _ _ _ ZR)]|].
    split; [split; (apply (L5C.u64_at_agree RSEGS M5 M6); [apply AG6; clear -FS FvS Fvf Fvp; lia| clear -Fvp; lia| clear -Fvp; lia| assumption])|].
    split; [apply (base_keep M M6 _ FZ); [intros a Ha; destruct Ha as [X|[X|[X|X]]]; clear -X; lia| exact BASE]|].
    split.
    { (* [comment removed for export] *)
      split; [| split].
      - rewrite bax_cat_add_dec. destruct (PNST.bax_cat ax); cbn [pa_errcat_guard AD PnLayoutS_u.ADDR_S] in EG |- *.
        + apply (L5C.u8_at_agree RSEGS M M6); [intros i Hi; apply FZ; clear -Hi FS Ffirst Fimg; lia| clear; lia| clear; lia| exact EG].
        + apply (PMKP.clear_agree M M6); [intros i Hi; apply FZ; clear -Hi FS Ffirst Fimg; lia| exact EG].
      - rewrite PNST.bax_dec_add. unfold PNST.bdec_ok, PNST.sso_lit. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add].
        destruct SSO2 as (IB & ID). destruct SSO5 as (NB & ND).
        split; [apply (L5C.u8_at_agree RSEGS M5 M6); [apply AG6; clear -FS Ffirst Fimg; lia| clear; lia| clear; lia| exact GI5]|].
        split; [apply (L5C.u8_at_agree RSEGS M5 M6); [apply AG6; clear -FS Ffirst Fimg; lia| clear; lia| clear; lia| exact GN5]|].
        split.
        + split; [| exact (L5.defined_grows M2 M6 _ _ (mem_grows_trans _ _ _ MG5 MG6) ID)].
          apply (L5C.u8_at_agree RSEGS M5 M6); [apply AG6; clear -FS Ffirst Fimg; lia| clear; lia| clear; lia|].
          apply (L5C.u8_at_agree RSEGS M2 M5); [apply AG5; clear -FS; lia| clear; lia| clear; lia| exact IB].
        + split; [| exact (L5.defined_grows M5 M6 _ _ MG6 ND)].
          apply (L5C.u8_at_agree RSEGS M5 M6); [apply AG6; clear -FS Ffirst Fimg; lia| clear; lia| clear; lia| exact NB].
      - apply (batexit_xfer M5 M6); [intros a Ha; apply FZ6; clear -Ha FS Ffirst Fimg; lia| exact AT5]. }
    split; [exact Hs1|]. split; [exact Hs2|].
    intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. destruct X as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| right; right| right; right].
    + split; [exact ED|]. unfold PMK.inW, PNST.dec_W. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S pa_atexit AD PnLayoutS_u.ADDR_S].
      destruct (Z_lt_le_dec a 820640) as [L1|G1]; [destruct (Z_lt_le_dec a 820616) as [L0|G0]; [exfalso; clear -X L0; lia|]|].
      * exists (820616, 24). split; [cbn; tauto| unfold L5.in_rng; cbn [fst snd]; clear -G0 L1; lia].
      * destruct (Z_lt_le_dec a 820648) as [L2|G2]; [exists (820640, 8); split; [cbn; tauto| unfold L5.in_rng; cbn [fst snd]; clear -G1 L2; lia]|].
        destruct (Z_lt_le_dec a 820672) as [L3|G3]; [exists (820648, 24); split; [cbn; tauto| unfold L5.in_rng; cbn [fst snd]; clear -G2 L3; lia]|].
        exists (820672, 8). split; [cbn; tauto| unfold L5.in_rng; cbn [fst snd]; clear -G3 X; lia].
    + split; [exact ED|]. exists (958472, 544). split; [cbn; tauto| unfold L5.in_rng; cbn [fst snd]; clear -X; lia]. }
  destruct P as (fx6 & R6 & M6 & MG6 & FW6 & FZ6 & [ (MS6 & KS6 & B9 & B10' & SGN & ZR) | (MS6 & KS6 & B9 & B10' & MINUS & SGN & ZR) ]);
    rewrite (slt_sign _ _ hi Fhi eq_refl) in SGN.
  - apply (FIN fx6 R6 M6 0 MG6 FZ6 MS6); [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| rewrite B9; f_equal; clear; lia| exact ZR| clear; lia|].
    destruct (Z.leb_spec (2 ^ 63) hi); [exfalso; clear -SGN; lia|]. split; intros X; exfalso; clear -X H; lia.
  - apply (FIN fx6 R6 M6 1 MG6 FZ6 MS6); [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact B9| exact ZR| clear; lia|].
    destruct (Z.leb_spec (2 ^ 63) hi); [| exfalso; clear -SGN; lia]. split; intros X; [reflexivity| exact H].
Qed.

(* [comment removed for export] *)
Theorem entry fx M :
  L5.writable RSEGS M (S - 336) 336 -> L5.writable RSEGS M first 42 -> PNSDD.vp_at M vp lo hi ->
  PMST.base_ok RSEGS AD M -> PNST.berr_ok RSEGS AD AN M ax ->
  exists fx' R' M' sigma, ent_post fx M fx' R' M' sigma.
Proof.
  destruct (PNST.bax_dec ax) eqn:ED; [apply warm| apply cold]; exact ED.
Qed.

End Ent.
End PNSDENT.
