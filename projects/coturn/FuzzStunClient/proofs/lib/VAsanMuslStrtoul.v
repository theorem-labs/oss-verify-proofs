(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanMemcpyBase AsanMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanMuslStrLib VAsanMuslTolower VAsanMuslStrtoul_code.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation W8 v := (word_to_le_bytes 8 v).
Definition MAXW : word := Z_to_bv 64 18446744073709551615.   (* [comment removed for export] *)
Definition TABA : Z := 0x237c0.                             (* [comment removed for export] *)
Definition C10A : Z := 0x10330.                             (* [comment removed for export] *)
Definition GOTA : Z := 0xabb08.                             (* [comment removed for export] *)
Definition strtoul_clob : list reg := [10; 11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Definition isdig (c : Z) : bool := ((48 <=? c) && (c <=? 57))%Z.
Definition issp (c : Z) : bool := (((9 <=? c) && (c <=? 13)) || (c =? 32))%Z.
Definition issign (c : Z) : bool := ((c =? 43) || (c =? 45))%Z.
(* [comment removed for export] *)
Definition stopper (c : Z) : Prop := isdig c = false /\ issp c = false /\ issign c = false.

(* [comment removed for export] *)
Definition TABLE : list byte := Eval vm_compute in
  match rdn SEGS (fun _ => None) (Z_to_bv 64 TABA) 257 with Some l => l | None => [] end.
Lemma TABLE_len : length TABLE = 257%nat. Proof. reflexivity. Qed.
Lemma rd_TABLE_img : rdn SEGS (fun _ => None) (Z_to_bv 64 TABA) 257 = Some TABLE.
Proof. vm_compute. reflexivity. Qed.
Definition TAB (c : Z) : byte := nth (Z.to_nat (c + 1)) TABLE B0.
(* [comment removed for export] *)
Lemma TAB_dig : forall c, (0 <= c < 256)%Z -> (bv_unsigned (TAB c) <? 10)%Z = isdig c.
Proof.
  intros c Hc.
  assert (H : forallb (fun n : nat => Bool.eqb (bv_unsigned (nth (S n) TABLE B0) <? 10)%Z (isdig (Z.of_nat n))) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  pose proof (ZStores.forallb_In _ _ (Z.to_nat c) H ltac:(apply in_seq; lia)) as E. cbn beta in E.
  apply Bool.eqb_prop in E. unfold TAB. replace (Z.to_nat (c + 1)) with (S (Z.to_nat c)) by lia.
  rewrite Z2Nat.id in E by lia. exact E.
Qed.

(* [comment removed for export] *)
Definition C10 : Z := 0x199999999999999a.   (* [comment removed for export] *)
Lemma rd_C10_img : exists bs, rdn SEGS (fun _ => None) (Z_to_bv 64 C10A) 8 = Some bs
                             /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 C10).
Proof. eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dig_cond : forall c : byte,
  c_ltu (Z_to_bv 64 9) (v_addiw (Z_to_bv 64 (bv_unsigned c)) (-48)) = negb (isdig (bv_unsigned c)).
Proof.
  intros c. pose proof (u8_range c) as Hc. unfold c_ltu, bv_ltu, v_addiw, isdig.
  rewrite (u_Z2bv (bv_unsigned c)) by lia. rewrite (u_Z2bv 9) by lia.
  rewrite (bv_swrap_small 32 (bv_unsigned c + -48)) by (rewrite half_modulus_32; lia).
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (bv_unsigned c + -48)) with ((bv_unsigned c + -48) mod 2 ^ 64)%Z.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct (Z_lt_le_dec (bv_unsigned c) 48) as [Hl|Hl].
  - replace ((bv_unsigned c + -48) mod 2 ^ 64)%Z with (2 ^ 64 + (bv_unsigned c - 48))%Z.
    2:{ symmetry. replace (bv_unsigned c + -48)%Z with ((2 ^ 64 + (bv_unsigned c - 48)) + (-1) * 2 ^ 64)%Z by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    replace (48 <=? bv_unsigned c)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb negb].
    apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia.
    replace (48 <=? bv_unsigned c)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z_lt_le_dec 57 (bv_unsigned c)) as [Hh|Hh].
    + replace (bv_unsigned c <=? 57)%Z with false by (symmetry; apply Z.leb_gt; lia). apply Z.ltb_lt. lia.
    + replace (bv_unsigned c <=? 57)%Z with true by (symmetry; apply Z.leb_le; lia). apply Z.ltb_ge. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma sp_cond1 : forall c : byte,
  c_ltu (v_addi (Z_to_bv 64 (bv_unsigned c)) (-9)) (Z_to_bv 64 5) = ((9 <=? bv_unsigned c) && (bv_unsigned c <=? 13))%Z.
Proof.
  intros c. pose proof (u8_range c) as Hc. unfold c_ltu, bv_ltu, v_addi.
  rewrite (u_Z2bv (bv_unsigned c)) by lia. rewrite (u_Z2bv 5) by lia.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (bv_unsigned c + -9)) with ((bv_unsigned c + -9) mod 2 ^ 64)%Z.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct (Z_lt_le_dec (bv_unsigned c) 9) as [Hl|Hl].
  - replace ((bv_unsigned c + -9) mod 2 ^ 64)%Z with (2 ^ 64 + (bv_unsigned c - 9))%Z.
    2:{ symmetry. replace (bv_unsigned c + -9)%Z with ((2 ^ 64 + (bv_unsigned c - 9)) + (-1) * 2 ^ 64)%Z by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    replace (9 <=? bv_unsigned c)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    apply Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia.
    replace (9 <=? bv_unsigned c)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z_lt_le_dec 13 (bv_unsigned c)) as [Hh|Hh].
    + replace (bv_unsigned c <=? 13)%Z with false by (symmetry; apply Z.leb_gt; lia). apply Z.ltb_ge. lia.
    + replace (bv_unsigned c <=? 13)%Z with true by (symmetry; apply Z.leb_le; lia). apply Z.ltb_lt. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma sp_cond2 : forall c : byte, c_eq (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 32) = (bv_unsigned c =? 32)%Z.
Proof. intros c. pose proof (u8_range c). unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma eq_lit : forall (c : byte) k, (0 <= k < 256)%Z -> c_eq (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 k) = (bv_unsigned c =? k)%Z.
Proof. intros c k Hk. pose proof (u8_range c). unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Ltac stepand F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].
Lemma v_and_0_l : forall x : word, v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Section ST.
  Variable mem : word -> option byte.
  Variables s sp tp G CAN : word.          (* [comment removed for export] *)
  Variable str : list byte.                (* [comment removed for export] *)
  Variable A : Z.                          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variables ret s0e s1e s2e s3e s4e s5e s6e s7e s8e : word.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation utp := (bv_unsigned tp).
  #[local] Notation L := (Z.of_nat (length str)).
  #[local] Notation SLOT k := (Z_to_bv 64 (bv_unsigned sp - k)).
  #[local] Notation ERR := (Z_to_bv 64 (bv_unsigned tp - 164)).
  Definition B_ (j : Z) : byte := nth (Z.to_nat j) str B0.

  (* [comment removed for export] *)
  Record stH : Prop := STH {
    Hstr  : rdn SEGS mem s (length str) = Some str;
    HA    : (0 <= A < L)%Z;
    Hstop : stopper (bv_unsigned (B_ A));
    Hnws  : (bv_unsigned s + L < 2 ^ 64 - 8)%Z;
    Hstk  : store_ok SEGS mem (SLOT 368) 368 = true;
    Hsp   : (368 <= usp)%Z /\ (usp < 2 ^ 64)%Z;
    Hsp_ro : (0x27468 <= usp - 368)%Z;                       (* [comment removed for export] *)
    Hsp_str : (usp <= bv_unsigned s \/ bv_unsigned s + L <= usp - 368)%Z;
    Herr  : store_ok SEGS mem ERR 4 = true;
    Htp   : (0x27468 + 164 <= utp)%Z;                         (* [comment removed for export] *)
    Herr_stk : (utp - 164 + 4 <= usp - 368 \/ usp <= utp - 164)%Z;
    Herr_str : (utp - 164 + 4 <= bv_unsigned s \/ bv_unsigned s + L <= utp - 164)%Z;
    Hgot  : rdn SEGS mem (Z_to_bv 64 GOTA) 8 = Some (W8 G);
    Hgot_stk : (GOTA + 8 <= usp - 368)%Z;
    Hcan  : rdn SEGS mem G 8 = Some (W8 CAN);
    HG_stk : (bv_unsigned G + 8 <= usp - 368 \/ usp <= bv_unsigned G)%Z;
    HG_err : (bv_unsigned G + 8 <= utp - 164 \/ utp - 164 + 4 <= bv_unsigned G)%Z;
    HG_nw : (bv_unsigned G + 8 < 2 ^ 64)%Z;
    Hro   : forall x, (C10A <= x < C10A + 8 \/ TABA <= x < TABA + 257)%Z -> mem (Z_to_bv 64 x) = None }.
  Hypothesis HOK : stH.

  (* [comment removed for export] *)
  Definition SLOTS : list (Z * word) :=
    [(8%Z, ret); (16%Z, s0e); (24%Z, s1e); (32%Z, s2e); (40%Z, s3e); (48%Z, CAN);
     (296%Z, (0xa3fa8 : word)); (304%Z, Z_to_bv 64 0); (312%Z, s); (320%Z, Z_to_bv 64 10); (328%Z, G);
     (336%Z, s4e); (344%Z, s5e); (352%Z, s6e); (360%Z, s7e); (368%Z, s8e)].

  (* [comment removed for export] *)
  Definition INV2 (m : word -> option byte) : Prop :=
    (forall k v, In (k, v) SLOTS -> rdn SEGS m (SLOT k) 8 = Some (W8 v))
    /\ rdn SEGS m G 8 = Some (W8 CAN)
    /\ store_ok SEGS m (SLOT 368) 368 = true
    /\ store_ok SEGS m ERR 4 = true
    /\ frame_mod mem m [(SLOT 368, 368%Z); (ERR, 4%Z)].

  (* [comment removed for export] *)
  Definition INV (m : word -> option byte) (i : Z) : Prop :=
    INV2 m
    /\ rdn SEGS m (SLOT 272) 8 = Some (W8 (at_ s i))         (* [comment removed for export] *)
    /\ rdn SEGS m (SLOT 96) 8 = Some (W8 MAXW)                (* [comment removed for export] *)
    /\ rdn SEGS m (SLOT 88) 8 = Some (W8 (Z_to_bv 64 0))      (* [comment removed for export] *)
    /\ rdn SEGS m (SLOT 192) 8 = Some (W8 s)                  (* [comment removed for export] *)
    /\ rdn SEGS m (SLOT 264) 8 = Some (W8 MAXW)               (* [comment removed for export] *)
    /\ rdn SEGS m s (length str) = Some str
    /\ (forall x, (C10A <= x < C10A + 8 \/ TABA <= x < TABA + 257)%Z -> m (Z_to_bv 64 x) = None).

  #[using="Type"] Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  #[using="Type"] Lemma slots_k : forall k v, In (k, v) SLOTS -> (8 <= k <= 368)%Z.
  Proof.
    intros k v Hin. assert (H : In k (map fst SLOTS)) by (apply in_map_iff; exists (k, v); auto).
    cbn [SLOTS map fst In] in H. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition miss_slots (a : Z) (n : Z) : Prop :=
    forall k v, In (k, v) SLOTS -> (a + n <= usp - k \/ usp - k + 8 <= a)%Z.

  #[using="str A HOK"] Lemma INV2_store : forall m (a : Z) (bs : list byte),
    INV2 m ->
    (0 <= a)%Z -> (a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
    miss_slots a (Z.of_nat (length bs)) ->
    ((usp - 368 <= a /\ a + Z.of_nat (length bs) <= usp) \/ (a = utp - 164 /\ length bs = 4%nat))%Z ->
    INV2 (wbytes m (Z_to_bv 64 a) bs).
  Proof.
    intros m a bs (S1 & S2 & S3 & S4 & S5) Ha Hnw Hmiss Hwhere.
    destruct HOK. pose proof (u64_range G). pose proof (u64_range tp). pose proof (u64_range sp).
    split; [|split; [|split; [|split]]].
    - intros k v Hin. pose proof (slots_k k v Hin). pose proof (Hmiss k v Hin).
      rewrite rdn_wbytes_out; [apply S1; exact Hin | u_norm; (ltac2:(LK.k [@Hwhere; @HA0; @Hsp_ro0; @Htp0; @H2; @Hnw; @Hnws0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @HG_nw0; @H0; @H1; @Ha; @H3]); lia) | u_norm; (ltac2:(LK.k [@Hwhere; @HA0; @Hsp_ro0; @Htp0; @H2; @Hnw; @Hnws0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @HG_nw0; @H0; @H1; @Ha; @H3]); lia) | u_norm; (ltac2:(LK.k [@Hwhere; @HA0; @Hsp_ro0; @Htp0; @H2; @Hnw; @Hnws0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @HG_nw0; @H0; @H1; @Ha; @H3]); lia)].
    - rewrite rdn_wbytes_out; [exact S2 | u_norm; lia | lia | u_norm; lia].
    - eapply store_ok_mono; [apply wbytes_grows | exact S3].
    - eapply store_ok_mono; [apply wbytes_grows | exact S4].
    - eapply frame_mod_trans_same; [exact S5|]. split; [|apply wbytes_grows].
      intros x (O1 & O2 & _). unfold in_rng in O1, O2. revert O1 O2. u_norm. intros O1 O2.
      apply MemSplit.wbytes_outside; u_norm; (ltac2:(LK.k [@Ha; @Hwhere; @Hnw; @HA0; @Hnws0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @HG_nw0; @H0; @H1; @O1; @O2]); lia).
  Qed.

  #[using="A HOK"] Lemma INV_rpos : forall m i j, INV m i -> (0 <= j)%Z -> (bv_unsigned s + j < 2 ^ 64)%Z ->
    INV (wbytes m (SLOT 272) (W8 (at_ s j))) j.
  Proof.
    intros m i j (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro) Hj Hjw.
    pose proof HOK as K; destruct K. pose proof (u64_range s).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - apply INV2_store; try assumption; rewrite ?lenW8; try lia.
      intros k v Hin.
      assert (HK : In k (map fst SLOTS)) by (apply in_map_iff; exists (k, v); auto).
      cbn [SLOTS map fst In] in HK. lia.
    - apply rdn_wbytes_hit8. u_norm. lia.
    - rewrite rdn_wbytes_out; [exact Rse | rewrite lenW8; u_norm; lia | u_norm; lia | rewrite lenW8; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rsl | rewrite lenW8; u_norm; lia | u_norm; lia | rewrite lenW8; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rb | rewrite lenW8; u_norm; lia | u_norm; lia | rewrite lenW8; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rre | rewrite lenW8; u_norm; lia | u_norm; lia | rewrite lenW8; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rs | rewrite lenW8; u_norm; lia | lia | rewrite lenW8; u_norm; lia].
    - intros x Hx. pose proof Hx as Hx'. unfold C10A, TABA in Hx'.
      rewrite MemSplit.wbytes_outside; [apply Rro; exact Hx | rewrite lenW8; u_norm; lia | rewrite lenW8; u_norm; lia].
  Qed.

  #[using="Type"] Lemma rd_str : forall m i j, INV m i -> (0 <= j < L)%Z -> rdn SEGS m (at_ s j) 1 = Some [B_ j].
  Proof.
    intros m i j (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro) Hj. unfold B_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_nth1 SEGS m s (length str)); [exact Rs | lia].
  Qed.

  #[using="Type"] Lemma rd_tab : forall m i (c : Z), INV m i -> (0 <= c < 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (TABA + c + 1)) 1 = Some [TAB c].
  Proof.
    intros m i c (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro) Hc. unfold TAB.
    rewrite (rdn_ext SEGS 1 m (fun _ => None)).
    - replace (Z_to_bv 64 (TABA + c + 1)) with (at_ (Z_to_bv 64 TABA) (Z.of_nat (Z.to_nat (c + 1))))
        by (unfold at_, TABA; u_norm; f_equal; lia).
      apply (rdn_nth1 SEGS _ _ 257%nat); [exact rd_TABLE_img | lia].
    - unfold TABA. u_norm. lia.
    - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Rro. revert Hx. unfold TABA. u_norm. lia.
  Qed.

  #[using="Type"] Lemma rd_c10 : forall m i, INV m i ->
    exists bs, rdn SEGS m (Z_to_bv 64 C10A) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 C10).
  Proof.
    intros m i (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro).
    destruct rd_C10_img as (bs & R & E). exists bs. split; [|exact E].
    rewrite (rdn_ext SEGS 8 m (fun _ => None)); [exact R | unfold C10A; u_norm; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Rro. revert Hx. unfold C10A. u_norm. lia.
  Qed.

  #[using="Type"] Lemma rd_slot : forall m k v, INV2 m -> In (k, v) SLOTS -> rdn SEGS m (SLOT k) 8 = Some (W8 v).
  Proof. intros m k v (S1 & _) Hin. apply S1. exact Hin. Qed.

  Ltac in_slots := unfold SLOTS; in_list.

  (* [comment removed for export] *)
  Ltac mld F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; rewrite ?v_addi_0;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              first [constr_eq a c | replace a with c by (unfold v_addi, GOTA; u_norm; first [f_equal; lia | apply bv_eq; u_norm; lia])] end end;
          exact RD
        | first [apply bytes_le_to_Z_8 | reflexivity] ]
      | step_simpl]; vnorm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="str A HOK"] Lemma epi_run : forall regs m (res : word),
    INV2 m -> ret_ok ret -> getr regs 2 = SLOT 368 -> getr regs 8 = res ->
    exists r,
      msteps SEGS (mkst regs (0xa3ac4 : word) m rom) (mkst r ret m rom)
      /\ getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ret /\ getr r 8 = s0e /\ getr r 9 = s1e
      /\ getr r 18 = s2e /\ getr r 19 = s3e /\ getr r 20 = s4e /\ getr r 21 = s5e /\ getr r 22 = s6e
      /\ getr r 23 = s7e /\ getr r 24 = s8e
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24]%list) regs r.
  Proof.
    intros regs m res HI2 Hret H2 H8.
    pose proof HOK as K; destruct K. pose proof (u64_range G).
    pose proof HI2 as (S1 & SG & _).
    eexists. split.
    - stepn F_a3ac4 D_a3ac4.                                        (* [comment removed for export] *)
      mld F_a3ac8 D_a3ac8 (0xa3fa8 : word) (rd_slot m 296 _ HI2 ltac:(in_slots)).   (* [comment removed for export] *)
      mld F_a3acc D_a3acc (Z_to_bv 64 0) (rd_slot m 304 _ HI2 ltac:(in_slots)).      (* [comment removed for export] *)
      mld F_a3ad0 D_a3ad0 s (rd_slot m 312 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_a3ad4 D_a3ad4 (Z_to_bv 64 10) (rd_slot m 320 _ HI2 ltac:(in_slots)).     (* [comment removed for export] *)
      mld F_a3ad8 D_a3ad8 G (rd_slot m 328 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_a3adc D_a3adc s4e (rd_slot m 336 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_a3ae0 D_a3ae0 s5e (rd_slot m 344 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_a3ae4 D_a3ae4 s6e (rd_slot m 352 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_a3ae8 D_a3ae8 s7e (rd_slot m 360 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_a3aec D_a3aec s8e (rd_slot m 368 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      stepiv F_a3af0 D_a3af0 (SLOT 288) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).  (* [comment removed for export] *)
      stepret F_a3af4 D_a3af4 (0xa3fa8 : word) ltac:(reflexivity).                   (* [comment removed for export] *)
      stepb_tk F_a3fa8 D_a3fa8 ltac:(cond_compute).                                  (* [comment removed for export] *)
      mld F_a3fc8 D_a3fc8 CAN SG.                                                     (* [comment removed for export] *)
      mld F_a3fcc D_a3fcc CAN (rd_slot m 48 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      stepb_ft F_a3fd0 D_a3fd0 ltac:(unfold c_eq; apply bv_eqb_refl).                (* [comment removed for export] *)
      mld F_a3fd4 D_a3fd4 ret (rd_slot m 8 _ HI2 ltac:(in_slots)).                   (* [comment removed for export] *)
      mld F_a3fd8 D_a3fd8 s0e (rd_slot m 16 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_a3fdc D_a3fdc s1e (rd_slot m 24 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_a3fe0 D_a3fe0 s2e (rd_slot m 32 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_a3fe4 D_a3fe4 s3e (rd_slot m 40 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      stepiv F_a3fe8 D_a3fe8 sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
      stepret F_a3fec D_a3fec ret ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition BIG : list reg := [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24]%list.

  Definition POSTF (regs0 r : bvmap 5 word) (m' : word -> option byte) : Prop :=
    INV2 m' /\ getr r 2 = sp /\ getr r 1 = ret /\ getr r 8 = s0e /\ getr r 9 = s1e
    /\ getr r 18 = s2e /\ getr r 19 = s3e /\ getr r 20 = s4e /\ getr r 21 = s5e /\ getr r 22 = s6e
    /\ getr r 23 = s7e /\ getr r 24 = s8e
    /\ regs_agree (fun x => In x BIG) regs0 r.

  (* [comment removed for export] *)
  #[using="Type"] Lemma I_2 : forall m i, INV m i -> INV2 m. Proof. intros m i H; exact (proj1 H). Qed.
  #[using="Type"] Lemma I_rpos : forall m i, INV m i -> rdn SEGS m (SLOT 272) 8 = Some (W8 (at_ s i)).
  Proof. intros m i H. exact (proj1 (proj2 H)). Qed.
  #[using="Type"] Lemma I_shend : forall m i, INV m i -> rdn SEGS m (SLOT 96) 8 = Some (W8 MAXW).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 H))). Qed.
  #[using="Type"] Lemma I_shlim : forall m i, INV m i -> rdn SEGS m (SLOT 88) 8 = Some (W8 (Z_to_bv 64 0)).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
  #[using="Type"] Lemma I_buf : forall m i, INV m i -> rdn SEGS m (SLOT 192) 8 = Some (W8 s).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
  #[using="Type"] Lemma I_rend : forall m i, INV m i -> rdn SEGS m (SLOT 264) 8 = Some (W8 MAXW).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
  #[using="Type"] Lemma I_ok : forall m i, INV m i -> store_ok SEGS m (SLOT 368) 368 = true.
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj1 H)))). Qed.
  #[using="Type"] Lemma I_okE : forall m i, INV m i -> store_ok SEGS m ERR 4 = true.
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 (proj1 H))))). Qed.

  #[using="Type"] Lemma neq_max : forall i, (0 <= bv_unsigned s + i < 2 ^ 64 - 1)%Z -> c_eq (at_ s i) MAXW = false.
  Proof.
    intros i Hi. unfold c_eq, bv_eqb, MAXW. rewrite at_u by lia. rewrite u_Z2bv by lia. apply Z.eqb_neq. lia.
  Qed.
  #[using="Type"] Lemma ltu_max_false : forall y : word, c_ltu MAXW y = false.
  Proof. intros y. pose proof (u64_range y). unfold c_ltu, bv_ltu, MAXW. rewrite u_Z2bv by lia. apply Z.ltb_ge. lia. Qed.
  #[using="Type"] Lemma lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
  Proof. vm_compute. reflexivity. Qed.

  Ltac okstk HI :=
    eapply (store_ok_sub SEGS _ (SLOT 368) _ 368 8);
      [u_norm; lia | exact (I_ok _ _ HI) | u_norm; lia | u_norm; cbn; lia].

  (* [comment removed for export] *)
  Ltac getc F1 D1 F2 D2 F3 D3 F4 D4 F5 D5 F6 D6 HI HI1 i :=
    mld F1 D1 (at_ s i) (I_rpos _ _ HI);
    mld F2 D2 MAXW (I_shend _ _ HI);
    stepb_ft F3 D3 ltac:(rwH; apply neq_max; lia);
    stepn F4 D4;
    (chain_step; [reflexivity
      | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i + 1));
        [exact F5 | reflexivity | exact D5
        | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
        | gres; rwH; rewrite at_addi; reflexivity
        | okstk HI ]
      | step_simpl]);
    (chain_step; [reflexivity
      | eapply step_lbu;
        [exact F6 | reflexivity | exact D6
        | gres; imm_norm; rwH; rewrite ?v_addi_0; apply (rd_str _ _ _ HI1); lia ]
      | step_simpl]); vnorm.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
               try (unfold v_addi; u_norm; f_equal; lia).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="str A HOK"] Lemma d68_run : forall regs0 regs m,
    INV2 m -> ret_ok ret -> getr regs 2 = SLOT 368 ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3a10 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m HI2 Hret H2 AG.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3ac4 : word) m rom)
             (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + stepn F_a3a10 D_a3a10.             (* [comment removed for export] *)
        stepn F_a3a14 D_a3a14.             (* [comment removed for export] *)
        stepn F_a3a18 D_a3a18.             (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - cbv beta. intros r1 (R2 & AG1).
      destruct (epi_run r1 m (getr r1 8) HI2 Hret R2 eq_refl) as (r2 & RUN & _ & P).
      exists r2, m. split; [exact RUN|]. split; [exact HI2|].
      decompose [and] P. repeat split; try assumption.
      eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_mono; [|eassumption].
      unfold BIG. cbn [In]. intros x HH. decompose [or] HH; subst; auto 30.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="A HOK"] Lemma done_run : forall regs0 regs m i,
    INV m i -> (1 <= i)%Z -> (bv_unsigned s + i < 2 ^ 64 - 1)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa39f8 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i HI Hi Hiw Hret H2 H9 H8 AG.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i - 1) HI ltac:(lia) ltac:(lia)) as HI1.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3a10 : word) (wbytes m (SLOT 272) (W8 (at_ s (i - 1)))) rom)
             (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    2:{ cbv beta. intros r1 (R2 & AG1). apply (d68_run regs0 r1); try assumption. exact (I_2 _ _ HI1). }
    destruct (c_ltu (getr regs 19) MAXW) eqn:CY.
    - eexists. split.
      + mld F_a39f8 D_a39f8 (Z_to_bv 64 0) (I_shlim _ _ HI).      (* [comment removed for export] *)
        stepb_ft F_a39fc D_a39fc ltac:(exact lts_0_0).             (* [comment removed for export] *)
        mld F_a3a00 D_a3a00 (at_ s i) (I_rpos _ _ HI).              (* [comment removed for export] *)
        stepn F_a3a04 D_a3a04.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i - 1));
            [exact F_a3a08 | reflexivity | exact D_a3a08
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepb_ft F_a3a0c D_a3a0c ltac:(rwH; exact CY).              (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - eexists. split.
      + mld F_a39f8 D_a39f8 (Z_to_bv 64 0) (I_shlim _ _ HI).
        stepb_ft F_a39fc D_a39fc ltac:(exact lts_0_0).
        mld F_a3a00 D_a3a00 (at_ s i) (I_rpos _ _ HI).
        stepn F_a3a04 D_a3a04.
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i - 1));
            [exact F_a3a08 | reflexivity | exact D_a3a08
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI ]
          | step_simpl].
        stepb_tk F_a3a0c D_a3a0c ltac:(rwH; exact CY).              (* [comment removed for export] *)
        stepn F_a3a7c D_a3a7c.                                      (* [comment removed for export] *)
        stepb_tk F_a3a80 D_a3a80 ltac:(rwH; cond_compute).         (* [comment removed for export] *)
        stepb_tk F_a3a9c D_a3a9c ltac:(rwH; apply ltu_max_false). (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
  Qed.

  #[local] Notation W4 v := (word_to_le_bytes 4 v).
  #[using="Type"] Lemma lenW4 : forall v : word, length (W4 v) = 4%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  #[using="A HOK"] Lemma INV_err : forall m i (v : word), INV m i -> INV (wbytes m ERR (W4 v)) i.
  Proof.
    intros m i v (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro).
    pose proof HOK as K; destruct K. pose proof (u64_range s). pose proof (u64_range tp).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - apply INV2_store; try assumption; rewrite ?lenW4; try lia.
      intros k v' Hin. pose proof (slots_k k v' Hin). lia.
    - rewrite rdn_wbytes_out; [exact Rr | rewrite lenW4; u_norm; lia | u_norm; lia | rewrite lenW4; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rse | rewrite lenW4; u_norm; lia | u_norm; lia | rewrite lenW4; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rsl | rewrite lenW4; u_norm; lia | u_norm; lia | rewrite lenW4; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rb | rewrite lenW4; u_norm; lia | u_norm; lia | rewrite lenW4; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rre | rewrite lenW4; u_norm; lia | u_norm; lia | rewrite lenW4; u_norm; lia].
    - rewrite rdn_wbytes_out; [exact Rs | rewrite lenW4; u_norm; lia | lia | rewrite lenW4; u_norm; lia].
    - intros x Hx. pose proof Hx as Hx'. unfold C10A, TABA in Hx'.
      rewrite MemSplit.wbytes_outside; [apply Rro; exact Hx | rewrite lenW4; u_norm; lia | rewrite lenW4; u_norm; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tab_cond : forall c : byte,
    c_ltu (Z_to_bv 64 (bv_unsigned (TAB (bv_unsigned c)))) (Z_to_bv 64 10) = isdig (bv_unsigned c).
  Proof.
    intros c. pose proof (u8_range c). pose proof (u8_range (TAB (bv_unsigned c))).
    unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. apply TAB_dig. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma tab_addr : forall c : byte,
    v_addi (v_add (Z_to_bv 64 TABA) (Z_to_bv 64 (bv_unsigned c))) 1 = Z_to_bv 64 (TABA + bv_unsigned c + 1).
  Proof.
    intros c. pose proof (u8_range c). unfold v_addi, v_add, TABA. unorm. reflexivity || (f_equal; lia).
  Qed.

  Ltac mtab F D HI :=
    chain_step; [reflexivity
      | eapply step_lbu;
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; rewrite tab_addr; apply (rd_tab _ _ _ HI); apply u8_range ]
      | step_simpl]; vnorm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma skip_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 21 = Z_to_bv 64 TABA -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3a30 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs m i Hcnt HI Hi Hret H2 H9 H8 H18 H21 H4 AG.
    pose proof HOK as K; destruct K.
    pose proof (u64_range s) as Hs. pose proof (u64_range tp) as Htpr.
    pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
    pose proof (u8_range (B_ i)) as U.
    destruct (isdig (bv_unsigned (B_ i))) eqn:DG.
    - (* [comment removed for export] *)
      assert (HiA : (i < A)%Z).
      { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (D & _ & _). rewrite D in DG. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3a30 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 21 = Z_to_bv 64 TABA /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3a30 D_a3a30 F_a3a34 D_a3a34 F_a3a38 D_a3a38 F_a3a3c D_a3a3c F_a3a40 D_a3a40 F_a3a44 D_a3a44 HI HI1 i.
          stepn F_a3a48 D_a3a48.                                  (* [comment removed for export] *)
          mtab F_a3a4c D_a3a4c HI1.                               (* [comment removed for export] *)
          stepb_tk F_a3a50 D_a3a50 ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R21 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      pose proof (INV_err _ _ (Z_to_bv 64 34) HI1) as HI2e.
      pose proof (INV_rpos _ _ i HI2e ltac:(lia) ltac:(lia)) as HI3.
      eapply (runs_trans_km SEGS _
               (fun r => mkst r (0xa3a10 : word)
                  (wbytes (wbytes (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) ERR (W4 (Z_to_bv 64 34))) (SLOT 272) (W8 (at_ s i))) rom)
               (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      2:{ cbv beta. intros r1 (R2 & AG1). apply (d68_run regs0 r1); try assumption. exact (I_2 _ _ HI3). }
      eexists. split.
      + getc F_a3a30 D_a3a30 F_a3a34 D_a3a34 F_a3a38 D_a3a38 F_a3a3c D_a3a3c F_a3a40 D_a3a40 F_a3a44 D_a3a44 HI HI1 i.
        stepn F_a3a48 D_a3a48.                                    (* [comment removed for export] *)
        mtab F_a3a4c D_a3a4c HI1.                                 (* [comment removed for export] *)
        stepb_ft F_a3a50 D_a3a50 ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
        stepn F_a3a54 D_a3a54.                                    (* [comment removed for export] *)
        stepn F_9a5f8 D_9a5f8.                                    (* [comment removed for export] *)
        stepn F_9a5fc D_9a5fc.                                    (* [comment removed for export] *)
        stepret F_9a600 D_9a600 (0xa3a58 : word) ltac:(apply bv_eq; vm_compute; reflexivity).
        stepn F_a3a58 D_a3a58.                                    (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := ERR) (v := Z_to_bv 64 34);
            [exact F_a3a5c | reflexivity | exact D_a3a5c
            | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | exact (I_okE _ _ HI1) ]
          | step_simpl].                                          (* [comment removed for export] *)
        stepn F_a3a60 D_a3a60.                                    (* [comment removed for export] *)
        stepn F_a3a64 D_a3a64.                                    (* [comment removed for export] *)
        stepn F_a3a68 D_a3a68.                                    (* [comment removed for export] *)
        stepn F_a3a6c D_a3a6c.                                    (* [comment removed for export] *)
        mld F_a3a70 D_a3a70 (Z_to_bv 64 0) (I_shlim _ _ HI2e).   (* [comment removed for export] *)
        stepb_tk F_a3a74 D_a3a74 ltac:(exact lts_0_0).           (* [comment removed for export] *)
        mld F_a3a00 D_a3a00 (at_ s (i + 1)) (I_rpos _ _ HI2e).   (* [comment removed for export] *)
        stepn F_a3a04 D_a3a04.                                    (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s i);
            [exact F_a3a08 | reflexivity | exact D_a3a08
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI2e ]
          | step_simpl].                                          (* [comment removed for export] *)
        stepb_tk F_a3a0c D_a3a0c ltac:(rwH; apply ltu_max_false).   (* [comment removed for export] *)
        stepn F_a3a7c D_a3a7c.                                    (* [comment removed for export] *)
        stepb_tk F_a3a80 D_a3a80 ltac:(rwH; cond_compute).       (* [comment removed for export] *)
        stepb_tk F_a3a9c D_a3a9c ltac:(rwH; apply ltu_max_false). (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma ovf_run : forall regs0 regs m i (c : byte),
    INV m i -> (0 <= i <= A)%Z -> isdig (bv_unsigned c) = true -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa39e4 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi DG Hret H2 H9 H8 H18 H10 H4 AG.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3a30 : word) m rom)
             (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                       /\ getr r 21 = Z_to_bv 64 TABA /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + stepn F_a39e4 D_a39e4.                                    (* [comment removed for export] *)
        stepn F_a39e8 D_a39e8.                                    (* [comment removed for export] *)
        stepn F_a39ec D_a39ec.                                    (* [comment removed for export] *)
        mtab F_a39f0 D_a39f0 HI.                                  (* [comment removed for export] *)
        stepb_tk F_a39f4 D_a39f4 ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - cbv beta. intros r1 (R2 & R9 & R8' & R18 & R21 & R4 & AG1).
      apply (skip_run (Z.to_nat (A - i)) regs0 r1 m i); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma loop2_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 22 = Z_to_bv 64 C10 -> getr regs 23 = Z_to_bv 64 9 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3748 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs m i Hcnt HI Hi Hret H2 H9 H8 H22 H23 H4 AG.
    pose proof HOK as K; destruct K.
    pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
    pose proof (u8_range (B_ i)) as U.
    destruct (isdig (bv_unsigned (B_ i))) eqn:DG.
    2:{ (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa39f8 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      - eexists. split.
        + getc F_a3748 D_a3748 F_a374c D_a374c F_a3750 D_a3750 F_a3754 D_a3754 F_a3758 D_a3758 F_a375c D_a375c HI HI1 i.
          stepn F_a3760 D_a3760.                                  (* [comment removed for export] *)
          stepn F_a3764 D_a3764.                                  (* [comment removed for export] *)
          stepb_ft F_a3768 D_a3768 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_a376c D_a376c.                                  (* [comment removed for export] *)
          stepn F_a39d8 D_a39d8.                                  (* [comment removed for export] *)
          stepb_tk F_a39dc D_a39dc ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      - cbv beta. intros r1 (R2 & R9 & R8' & AG1).
        apply (done_run regs0 r1 _ (i + 1)); try assumption; lia. }
    assert (HiA : (i < A)%Z).
    { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (D & _ & _). rewrite D in DG. discriminate. }
    destruct (c_ltu (v_add (getr regs 24) (getr regs 21)) (Z_to_bv 64 C10)) eqn:CY.
    - (* [comment removed for export] *)
      destruct (c_ltu (v_xori (v_addiw (Z_to_bv 64 (bv_unsigned (B_ i))) (-48)) (-1))
                      (v_mul (v_add (getr regs 24) (getr regs 21)) (Z_to_bv 64 10))) eqn:CZ.
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa39e4 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                           /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                           /\ regs_agree (fun x => In x BIG) regs0 r)
                 (fun r m' => mkst r ret m' rom)).
        * eexists. split.
          -- getc F_a3748 D_a3748 F_a374c D_a374c F_a3750 D_a3750 F_a3754 D_a3754 F_a3758 D_a3758 F_a375c D_a375c HI HI1 i.
             stepn F_a3760 D_a3760.                               (* [comment removed for export] *)
             stepn F_a3764 D_a3764.                               (* [comment removed for export] *)
             stepb_tk F_a3768 D_a3768 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
             stepb_ft F_a3784 D_a3784 ltac:(rwH; exact CY).       (* [comment removed for export] *)
             stepn F_a3788 D_a3788.                               (* [comment removed for export] *)
             stepn F_a378c D_a378c.                               (* [comment removed for export] *)
             stepn F_a3790 D_a3790.                               (* [comment removed for export] *)
             stepb_ft F_a3794 D_a3794 ltac:(rwH; exact CZ).       (* [comment removed for export] *)
             stepn F_a3798 D_a3798.                               (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
          apply (ovf_run regs0 r1 _ (i + 1) (B_ i)); try assumption; lia.
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3748 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 22 = Z_to_bv 64 C10
                           /\ getr r 23 = Z_to_bv 64 9 /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
                 (fun r m' => mkst r ret m' rom)).
        * eexists. split.
          -- getc F_a3748 D_a3748 F_a374c D_a374c F_a3750 D_a3750 F_a3754 D_a3754 F_a3758 D_a3758 F_a375c D_a375c HI HI1 i.
             stepn F_a3760 D_a3760.
             stepn F_a3764 D_a3764.
             stepb_tk F_a3768 D_a3768 ltac:(rwH; rewrite dig_cond, DG; reflexivity).
             stepb_ft F_a3784 D_a3784 ltac:(rwH; exact CY).
             stepn F_a3788 D_a3788.
             stepn F_a378c D_a378c.
             stepn F_a3790 D_a3790.
             stepb_tk F_a3794 D_a3794 ltac:(rwH; exact CZ).       (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R22 & R23 & R4 & AG1).
          apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa39e4 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3748 D_a3748 F_a374c D_a374c F_a3750 D_a3750 F_a3754 D_a3754 F_a3758 D_a3758 F_a375c D_a375c HI HI1 i.
          stepn F_a3760 D_a3760.
          stepn F_a3764 D_a3764.
          stepb_tk F_a3768 D_a3768 ltac:(rwH; rewrite dig_cond, DG; reflexivity).
          stepb_tk F_a3784 D_a3784 ltac:(rwH; exact CY).          (* [comment removed for export] *)
          stepn F_a39d8 D_a39d8.                                  (* [comment removed for export] *)
          stepb_ft F_a39dc D_a39dc ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_a39e0 D_a39e0.                                  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (ovf_run regs0 r1 _ (i + 1) (B_ i)); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma loop1_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 9 -> getr regs 22 = Z_to_bv 64 10 -> getr regs 23 = Z_to_bv 64 0x19999999 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3700 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs m i Hcnt HI Hi Hret H2 H9 H8 H18 H22 H23 H4 AG.
    pose proof HOK as K; destruct K.
    pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
    pose proof (u8_range (B_ i)) as U.
    destruct (isdig (bv_unsigned (B_ i))) eqn:DG.
    2:{ (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa39f8 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      - eexists. split.
        + getc F_a3700 D_a3700 F_a3704 D_a3704 F_a3708 D_a3708 F_a370c D_a370c F_a3710 D_a3710 F_a3714 D_a3714 HI HI1 i.
          stepn F_a3718 D_a3718.                                  (* [comment removed for export] *)
          stepn F_a371c D_a371c.                                  (* [comment removed for export] *)
          stepn F_a3720 D_a3720.                                  (* [comment removed for export] *)
          stepb_ft F_a3724 D_a3724 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_a3728 D_a3728.                                  (* [comment removed for export] *)
          stepn F_a372c D_a372c.                                  (* [comment removed for export] *)
          stepb_tk F_a3730 D_a3730 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      - cbv beta. intros r1 (R2 & R9 & R8' & AG1).
        apply (done_run regs0 r1 _ (i + 1)); try assumption; lia. }
    assert (HiA : (i < A)%Z).
    { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (D & _ & _). rewrite D in DG. discriminate. }
    destruct (c_ltu (v_addw (v_mul (getr regs 19) (Z_to_bv 64 10)) (getr regs 21)) (Z_to_bv 64 0x19999999)) eqn:CX.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3700 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 9
                         /\ getr r 22 = Z_to_bv 64 10 /\ getr r 23 = Z_to_bv 64 0x19999999 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3700 D_a3700 F_a3704 D_a3704 F_a3708 D_a3708 F_a370c D_a370c F_a3710 D_a3710 F_a3714 D_a3714 HI HI1 i.
          stepn F_a3718 D_a3718.
          stepn F_a371c D_a371c.
          stepn F_a3720 D_a3720.
          stepb_tk F_a3724 D_a3724 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepb_ft F_a36fc D_a36fc ltac:(rwH; exact CX).          (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R22 & R23 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      destruct (rd_c10 _ _ HI1) as (bsC & RC & EC).
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3748 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 22 = Z_to_bv 64 C10
                         /\ getr r 23 = Z_to_bv 64 9 /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3700 D_a3700 F_a3704 D_a3704 F_a3708 D_a3708 F_a370c D_a370c F_a3710 D_a3710 F_a3714 D_a3714 HI HI1 i.
          stepn F_a3718 D_a3718.
          stepn F_a371c D_a371c.
          stepn F_a3720 D_a3720.
          stepb_tk F_a3724 D_a3724 ltac:(rwH; rewrite dig_cond, DG; reflexivity).
          stepb_tk F_a36fc D_a36fc ltac:(rwH; exact CX).          (* [comment removed for export] *)
          stepn F_a3728 D_a3728.
          stepn F_a372c D_a372c.
          stepb_ft F_a3730 D_a3730 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_a3734 D_a3734.                                  (* [comment removed for export] *)
          chain_step; [reflexivity
            | eapply step_ld with (v := Z_to_bv 64 C10);
              [exact F_a3738 | reflexivity | exact D_a3738
              | gres; imm_norm;
                lazymatch goal with |- rdn _ _ ?a _ = _ =>
                  lazymatch type of RC with rdn _ _ ?c _ = _ =>
                    replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
                exact RC
              | exact EC ]
            | step_simpl]; vnorm.                                   (* [comment removed for export] *)
          stepn F_a373c D_a373c.                                  (* [comment removed for export] *)
          stepn F_a3740 D_a3740.                                  (* [comment removed for export] *)
          stepn F_a3744 D_a3744.                                  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R22 & R23 & R4 & AG1).
        apply (loop2_run (Z.to_nat (A - (i + 1))) regs0 r1 _ (i + 1)%Z); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma dig_run : forall regs0 regs m i (c : byte),
    INV m i -> (0 <= i <= A)%Z -> isdig (bv_unsigned c) = true -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa36bc : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi DG Hret H2 H9 H8 H18 H10 H4 AG. pose proof (u8_range c).
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3700 : word) m rom)
             (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 9
                       /\ getr r 22 = Z_to_bv 64 10 /\ getr r 23 = Z_to_bv 64 0x19999999 /\ getr r 4 = tp
                       /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + stepn F_a36bc D_a36bc.                                    (* [comment removed for export] *)
        stepb_ft F_a36c0 D_a36c0 ltac:(rwH; cond_compute).         (* [comment removed for export] *)
        stepn F_a36c4 D_a36c4.                                    (* [comment removed for export] *)
        stepn F_a36c8 D_a36c8.                                    (* [comment removed for export] *)
        stepn F_a36cc D_a36cc.                                    (* [comment removed for export] *)
        stepb_ft F_a36d0 D_a36d0 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
        stepn F_a36d4 D_a36d4.                                    (* [comment removed for export] *)
        stepn F_a36d8 D_a36d8.                                    (* [comment removed for export] *)
        stepn F_a36dc D_a36dc.                                    (* [comment removed for export] *)
        stepn F_a36e0 D_a36e0.                                    (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - cbv beta. intros r1 (R2 & R9 & R8' & R18 & R22 & R23 & R4 & AG1).
      pose proof HOK as K; destruct K.
      apply (loop1_run (Z.to_nat (A - i)) regs0 r1 m i); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac okfr1 HI := eapply store_ok_mono; [apply wbytes_grows|]; okstk HI.
  Ltac okfr2 HI := eapply store_ok_mono; [apply wbytes_grows|]; okfr1 HI.
  Ltac okfr3 HI := eapply store_ok_mono; [apply wbytes_grows|]; okfr2 HI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma einval_run : forall regs0 regs m i,
    INV m i -> (1 <= i <= A + 1)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3670 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i HI Hi Hret H2 H9 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs. pose proof (u64_range tp) as Htpr.
    pose proof (INV_rpos m i (i - 1) HI ltac:(lia) ltac:(lia)) as HI1.
    set (m1 := wbytes m (SLOT 272) (W8 (at_ s (i - 1)))) in HI1.
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _
             (fun r => mkst r (0xa3ac4 : word)
                (wbytes (wbytes (wbytes (wbytes m1 (SLOT 88) (W8 (Z_to_bv 64 0))) (SLOT 80) (W8 (v_sub s (at_ s (i - 1)))))
                           (SLOT 96) (W8 MAXW)) ERR (W4 (Z_to_bv 64 22))) rom)
             (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + mld F_a3670 D_a3670 (Z_to_bv 64 0) (I_shlim _ _ HI).      (* [comment removed for export] *)
        stepb_ft F_a3674 D_a3674 ltac:(exact lts_0_0).             (* [comment removed for export] *)
        mld F_a3678 D_a3678 (at_ s i) (I_rpos _ _ HI).              (* [comment removed for export] *)
        stepn F_a367c D_a367c.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i - 1));
            [exact F_a3680 | reflexivity | exact D_a3680
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI ]
          | step_simpl].                                            (* [comment removed for export] *)
        fold m1.
        stepn F_a3684 D_a3684.                                      (* [comment removed for export] *)
        stepn F_a3688 D_a3688.                                      (* [comment removed for export] *)
        stepn F_a368c D_a368c.                                      (* [comment removed for export] *)
        mld F_a3420 D_a3420 (at_ s (i - 1)) (I_rpos _ _ HI1).      (* [comment removed for export] *)
        mld F_a3424 D_a3424 MAXW (I_rend _ _ HI1).                  (* [comment removed for export] *)
        mld F_a3428 D_a3428 s (I_buf _ _ HI1).                      (* [comment removed for export] *)
        stepn F_a342c D_a342c.                                      (* [comment removed for export] *)
        stepn F_a3430 D_a3430.                                      (* [comment removed for export] *)
        stepn F_a3434 D_a3434.                                      (* [comment removed for export] *)
        stepand F_a3438 D_a3438 (Z_to_bv 64 0) ltac:(gres; rwH; apply v_and_0_l).   (* [comment removed for export] *)
        stepn F_a343c D_a343c.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 88) (v := Z_to_bv 64 0);
            [exact F_a3440 | reflexivity | exact D_a3440
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | okstk HI1 ]
          | step_simpl].                                            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 80);
            [exact F_a3444 | reflexivity | exact D_a3444
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | okfr1 HI1 ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepb_tk F_a3448 D_a3448 ltac:(cond_compute).              (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 96) (v := MAXW);
            [exact F_a3450 | reflexivity | exact D_a3450
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | okfr2 HI1 ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepret F_a3454 D_a3454 (0xa3690 : word) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
        stepn F_a3690 D_a3690.                                      (* [comment removed for export] *)
        stepn F_9a5f8 D_9a5f8.                                      (* [comment removed for export] *)
        stepn F_9a5fc D_9a5fc.                                      (* [comment removed for export] *)
        stepret F_9a600 D_9a600 (0xa3694 : word) ltac:(apply bv_eq; vm_compute; reflexivity).
        stepn F_a3694 D_a3694.                                      (* [comment removed for export] *)
        stepn F_a3698 D_a3698.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := ERR) (v := Z_to_bv 64 22);
            [exact F_a369c | reflexivity | exact D_a369c
            | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | do 3 (eapply store_ok_mono; [apply wbytes_grows|]); exact (I_okE _ _ HI1) ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepn F_a36a0 D_a36a0.                                      (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - cbv beta. intros r1 (R2 & AG1).
      assert (HI2f : INV2 (wbytes (wbytes (wbytes (wbytes m1 (SLOT 88) (W8 (Z_to_bv 64 0))) (SLOT 80) (W8 (v_sub s (at_ s (i - 1)))))
                           (SLOT 96) (W8 MAXW)) ERR (W4 (Z_to_bv 64 22)))).
      { pose proof (I_2 _ _ HI1) as B.
        assert (MS : forall a, (a = 88 \/ a = 80 \/ a = 96)%Z -> miss_slots (usp - a) 8).
        { intros a Ha k v Hin. assert (HK : In k (map fst SLOTS)) by (apply in_map_iff; exists (k, v); auto).
          cbn [SLOTS map fst In] in HK. (ltac2:(LK.k [@HA0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @Ha; @HK]); lia). }
        apply INV2_store; rewrite ?lenW4; try lia; [| intros k v Hin; pose proof (slots_k k v Hin); lia].
        apply INV2_store; rewrite ?lenW8; try lia; [| apply MS; lia].
        apply INV2_store; rewrite ?lenW8; try lia; [| apply MS; lia].
        apply INV2_store; rewrite ?lenW8; try lia; [| apply MS; lia].
        exact B. }
      destruct (epi_run r1 _ (getr r1 8) HI2f Hret R2 eq_refl) as (r2 & RUN & _ & P).
      eexists r2, _. split; [exact RUN|]. split; [exact HI2f|].
      decompose [and] P. repeat split; try assumption.
      eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_mono; [|eassumption].
      unfold BIG. cbn [In]. intros x HH. decompose [or] HH; subst; auto 30.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma dispatch_run : forall regs0 regs m i (c : byte),
    INV m i -> (1 <= i <= A + 1)%Z -> c = B_ (i - 1) -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3654 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi Hc Hret H2 H9 H8 H18 H10 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u8_range c) as U.
    destruct (isdig (bv_unsigned c)) eqn:DG.
    - (* [comment removed for export] *)
      assert (HiA : (i - 1 < A)%Z).
      { destruct (Z.eq_dec (i - 1) A) as [E|]; [|lia]. destruct Hstop0 as (D & _ & _).
        rewrite <- E, <- Hc in D. rewrite D in DG. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa36bc : word) m rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * stepb_tk F_a3654 D_a3654 ltac:(rwH; cond_compute).      (* [comment removed for export] *)
          stepn F_a365c D_a365c.                                  (* [comment removed for export] *)
          stepn F_a3660 D_a3660.                                  (* [comment removed for export] *)
          stepn F_a3664 D_a3664.                                  (* [comment removed for export] *)
          mtab F_a3668 D_a3668 HI.                                (* [comment removed for export] *)
          stepb_tk F_a366c D_a366c ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (dig_run regs0 r1 m i c); try assumption; lia.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3670 : word) m rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * stepb_tk F_a3654 D_a3654 ltac:(rwH; cond_compute).
          stepn F_a365c D_a365c.
          stepn F_a3660 D_a3660.
          stepn F_a3664 D_a3664.
          mtab F_a3668 D_a3668 HI.
          stepb_ft F_a366c D_a366c ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R4 & AG1).
        apply (einval_run regs0 r1 m i); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma sign_run : forall regs0 regs m i (c : byte),
    INV m i -> (1 <= i <= A + 1)%Z -> c = B_ (i - 1) -> issp (bv_unsigned c) = false -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa35ac : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi Hc Hsp' Hret H2 H9 H8 H18 H10 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u8_range c) as U. pose proof (u64_range s) as Hs.
    destruct (issign (bv_unsigned c)) eqn:SG.
    - (* [comment removed for export] *)
      assert (HiA : (i - 1 < A)%Z).
      { destruct (Z.eq_dec (i - 1) A) as [E|]; [|lia]. destruct Hstop0 as (_ & _ & D).
        rewrite <- E, <- Hc in D. rewrite D in SG. discriminate. }
      pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3654 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      2:{ cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
          apply (dispatch_run regs0 r1 _ (i + 1) (B_ i)); try assumption; try lia. f_equal; lia. }
      (* [comment removed for export] *)
      assert (TAIL : forall regs1,
        getr regs1 2 = SLOT 368 -> getr regs1 9 = SLOT 280 -> getr regs1 8 = MAXW ->
        getr regs1 18 = Z_to_bv 64 10 -> getr regs1 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs1 4 = tp ->
        regs_agree (fun x => In x BIG) regs0 regs1 ->
        exists r1, msteps SEGS (mkst regs1 (0xa35bc : word) m rom) (mkst r1 (0xa3654 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
          /\ (getr r1 2 = SLOT 368 /\ getr r1 9 = SLOT 280 /\ getr r1 8 = MAXW /\ getr r1 18 = Z_to_bv 64 10
              /\ getr r1 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r1 4 = tp
              /\ regs_agree (fun x => In x BIG) regs0 r1)).
      { intros regs1 Q2 Q9 Q8 Q18 Q10 Q4 QAG. clear H2 H9 H8 H18 H10 H4 AG.
        eexists. split.
        - mld F_a35bc D_a35bc (at_ s i) (I_rpos _ _ HI).           (* [comment removed for export] *)
          mld F_a35c0 D_a35c0 MAXW (I_shend _ _ HI).               (* [comment removed for export] *)
          stepn F_a35c4 D_a35c4.                                    (* [comment removed for export] *)
          stepn F_a35c8 D_a35c8.                                    (* [comment removed for export] *)
          stepn F_a35cc D_a35cc.                                    (* [comment removed for export] *)
          stepb_ft F_a35d0 D_a35d0 ltac:(rwH; apply neq_max; lia). (* [comment removed for export] *)
          stepn F_a35d4 D_a35d4.                                    (* [comment removed for export] *)
          chain_step; [reflexivity
            | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i + 1));
              [exact F_a35d8 | reflexivity | exact D_a35d8
              | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
              | gres; rwH; rewrite at_addi; reflexivity
              | okstk HI ]
            | step_simpl].                                          (* [comment removed for export] *)
          chain_step; [reflexivity
            | eapply step_lbu;
              [exact F_a35dc | reflexivity | exact D_a35dc
              | gres; imm_norm; rwH; rewrite ?v_addi_0; apply (rd_str _ _ _ HI1); lia ]
            | step_simpl]; vnorm.                                   (* [comment removed for export] *)
          stepn F_a35e0 D_a35e0.                                    (* [comment removed for export] *)
          stepb_ft F_a35e4 D_a35e4 ltac:(rwH; cond_compute).       (* [comment removed for export] *)
          stepn F_a35e8 D_a35e8.                                    (* [comment removed for export] *)
          apply mst_refl.
        - post. eapply regs_agree_trans; [exact QAG|]. unfold BIG. solve_regs_agree. }
      destruct (Z.eqb_spec (bv_unsigned c) 45) as [E45|N45].
      + eapply (runs_trans SEGS _ (fun r => mkst r (0xa35bc : word) m rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                           /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)).
        * eexists. split.
          -- stepn F_a35ac D_a35ac.                                 (* [comment removed for export] *)
             stepb_tk F_a35b0 D_a35b0 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_eq; exact E45).   (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1). apply TAIL; assumption.
      + assert (E43 : bv_unsigned c = 43%Z).
        { unfold issign in SG. apply orb_true_iff in SG as [SG|SG]; apply Z.eqb_eq in SG; lia. }
        eapply (runs_trans SEGS _ (fun r => mkst r (0xa35bc : word) m rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                           /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)).
        * eexists. split.
          -- stepn F_a35ac D_a35ac.                                 (* [comment removed for export] *)
             stepb_ft F_a35b0 D_a35b0 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_neq; exact N45).  (* [comment removed for export] *)
             stepn F_a35b4 D_a35b4.                                 (* [comment removed for export] *)
             stepb_ft F_a35b8 D_a35b8 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_eq; exact E43).   (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1). apply TAIL; assumption.
    - (* [comment removed for export] *)
      assert (N45 : bv_unsigned c <> 45%Z).
      { intros E. unfold issign in SG. rewrite E in SG. discriminate. }
      assert (N43 : bv_unsigned c <> 43%Z).
      { intros E. unfold issign in SG. rewrite E in SG. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3654 : word) m rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * stepn F_a35ac D_a35ac.                                    (* [comment removed for export] *)
          stepb_ft F_a35b0 D_a35b0 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_neq; exact N45).
          stepn F_a35b4 D_a35b4.                                    (* [comment removed for export] *)
          stepb_tk F_a35b8 D_a35b8 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_neq; exact N43).  (* [comment removed for export] *)
          stepn F_a35ec D_a35ec.                                    (* [comment removed for export] *)
          stepn F_a35f0 D_a35f0.                                    (* [comment removed for export] *)
          stepb_ft F_a35f4 D_a35f4 ltac:(rwH; cond_compute).         (* [comment removed for export] *)
          stepn F_a35f8 D_a35f8.                                    (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (dispatch_run regs0 r1 m i c); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma ws_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 20 = Z_to_bv 64 5 -> getr regs 21 = Z_to_bv 64 32 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0xa3588 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs m i Hcnt HI Hi Hret H2 H9 H8 H18 H20 H21 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
    pose proof (u8_range (B_ i)) as U.
    destruct ((9 <=? bv_unsigned (B_ i)) && (bv_unsigned (B_ i) <=? 13))%Z eqn:SP1;
      [| destruct (bv_unsigned (B_ i) =? 32)%Z eqn:SP2].
    - (* [comment removed for export] *)
      assert (HiA : (i < A)%Z).
      { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (_ & D & _). unfold issp in D.
        rewrite SP1 in D. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3588 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3588 D_a3588 F_a358c D_a358c F_a3590 D_a3590 F_a3594 D_a3594 F_a3598 D_a3598 F_a359c D_a359c HI HI1 i.
          stepn F_a35a0 D_a35a0.                                  (* [comment removed for export] *)
          stepb_tk F_a35a4 D_a35a4 ltac:(rwH; rewrite sp_cond1; exact SP1).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R20 & R21 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      assert (HiA : (i < A)%Z).
      { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (_ & D & _). unfold issp in D.
        rewrite SP1, SP2 in D. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3588 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3588 D_a3588 F_a358c D_a358c F_a3590 D_a3590 F_a3594 D_a3594 F_a3598 D_a3598 F_a359c D_a359c HI HI1 i.
          stepn F_a35a0 D_a35a0.
          stepb_ft F_a35a4 D_a35a4 ltac:(rwH; rewrite sp_cond1; exact SP1).   (* [comment removed for export] *)
          stepb_tk F_a35a8 D_a35a8 ltac:(rwH; rewrite sp_cond2; exact SP2).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R20 & R21 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:((ltac2:(LK.k [@Hcnt; @Hi; @HA0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @SP2; @HiA]); lia)) regs0 r1 _ (i + 1)%Z); try assumption; (ltac2:(LK.k [@Hcnt; @Hi; @HA0; @Hsp_str0; @Herr_stk0; @Herr_str0; @HG_stk0; @HG_err0; @SP2; @HiA]); lia).
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa35ac : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_a3588 D_a3588 F_a358c D_a358c F_a3590 D_a3590 F_a3594 D_a3594 F_a3598 D_a3598 F_a359c D_a359c HI HI1 i.
          stepn F_a35a0 D_a35a0.
          stepb_ft F_a35a4 D_a35a4 ltac:(rwH; rewrite sp_cond1; exact SP1).
          stepb_ft F_a35a8 D_a35a8 ltac:(rwH; rewrite sp_cond2; exact SP2).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (sign_run regs0 r1 _ (i + 1) (B_ i)); try assumption; try lia.
        * f_equal. lia.
        * unfold issp. rewrite SP1, SP2. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint apply_stores (m : word -> option byte) (l : list (Z * word)) : word -> option byte :=
    match l with
    | [] => m
    | (k, v) :: l' => apply_stores (wbytes m (SLOT k) (W8 v)) l'
    end.
  Fixpoint distinctb (l : list Z) : bool :=
    match l with [] => true | k :: t => negb (existsb (Z.eqb k) t) && distinctb t end.
  Definition sepb (l : list Z) : bool :=
    forallb (fun k1 => forallb (fun k2 => (k1 =? k2) || (k1 + 8 <=? k2) || (k2 + 8 <=? k1))%Z l) l.
  Definition inb (l : list Z) : bool := forallb (fun k => (8 <=? k) && (k <=? 368))%Z l.

  #[using="mem s tp G CAN str A HOK"] Lemma as_rdn_sep : forall l m (a : word) n,
    inb (map fst l) = true ->
    (forall k, In k (map fst l) -> (bv_unsigned a + Z.of_nat n <= usp - k \/ usp - k + 8 <= bv_unsigned a)%Z) ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    rdn SEGS (apply_stores m l) a n = rdn SEGS m a n.
  Proof.
    pose proof HOK as K; destruct K.
    induction l as [|[k v] l IH]; intros m a n Hinb Hsep Hnw; [reflexivity|].
    cbn [apply_stores]. cbn [map fst inb forallb] in Hinb. apply andb_true_iff in Hinb as [Hk Hinb].
    apply andb_true_iff in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
    rewrite IH; [| exact Hinb | intros k' Hk'; apply Hsep; right; exact Hk' | exact Hnw].
    pose proof (Hsep k (or_introl eq_refl)).
    apply rdn_wbytes_out; rewrite ?lenW8; u_norm; lia.
  Qed.

  #[using="mem s tp G CAN str A HOK"] Lemma as_slot : forall l m k v,
    inb (map fst l) = true -> sepb (map fst l) = true -> distinctb (map fst l) = true ->
    In (k, v) l -> rdn SEGS (apply_stores m l) (SLOT k) 8 = Some (W8 v).
  Proof.
    pose proof HOK as K; destruct K.
    induction l as [|[k1 v1] l IH]; intros m k v Hinb Hsep Hdis Hin; [destruct Hin|].
    cbn [map fst] in Hinb, Hsep, Hdis. pose proof Hinb as Hinb0.
    cbn [inb forallb] in Hinb. apply andb_true_iff in Hinb as [Hk Hinb].
    apply andb_true_iff in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
    cbn [distinctb] in Hdis. apply andb_true_iff in Hdis as [Hnot Hdis]. apply negb_true_iff in Hnot.
    assert (Hsep' : sepb (map fst l) = true).
    { unfold sepb. apply forallb_forall. intros x Hx. apply forallb_forall. intros y Hy.
      unfold sepb in Hsep. pose proof (ZStores.forallb_In _ _ x Hsep (or_intror Hx)) as E. cbn beta in E.
      exact (ZStores.forallb_In _ _ y E (or_intror Hy)). }
    cbn [apply_stores]. destruct Hin as [E|Hin].
    - injection E as <- <-.
      rewrite as_rdn_sep; [| exact Hinb | | u_norm; lia].
      + apply rdn_wbytes_hit8. u_norm. lia.
      + intros k' Hk'. pose proof (ZStores.forallb_In _ _ k1 Hsep (or_introl eq_refl)) as E. cbn beta in E.
        pose proof (ZStores.forallb_In _ _ k' E (or_intror Hk')) as E2. cbn beta in E2.
        pose proof (ZStores.forallb_In _ _ k' Hinb Hk') as B. cbn beta in B.
        apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
        assert (k1 <> k') by (intros ->; pose proof (ZStores.existsb_false_forall _ _ Hnot k' Hk') as X; cbn beta in X; rewrite Z.eqb_refl in X; discriminate).
        rewrite !orb_true_iff, Z.eqb_eq, !Z.leb_le in E2. u_norm. lia.
    - apply IH; assumption.
  Qed.

  #[using="mem s tp G CAN str A HOK"] Lemma as_out : forall l m (x : word),
    inb (map fst l) = true ->
    (bv_unsigned x < usp - 368 \/ usp <= bv_unsigned x)%Z -> apply_stores m l x = m x.
  Proof.
    pose proof HOK as K; destruct K.
    induction l as [|[k v] l IH]; intros m x Hinb Hx; [reflexivity|].
    cbn [apply_stores]. cbn [map fst inb forallb] in Hinb. apply andb_true_iff in Hinb as [Hk Hinb].
    apply andb_true_iff in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
    rewrite IH by assumption. apply MemSplit.wbytes_outside; rewrite lenW8; u_norm; lia.
  Qed.

  #[using="Type"] Lemma as_grows : forall l m, mem_grows m (apply_stores m l).
  Proof.
    induction l as [|[k v] l IH]; intros m; [apply mem_grows_refl|].
    cbn [apply_stores]. eapply mem_grows_trans; [apply wbytes_grows | apply IH].
  Qed.

  (* [comment removed for export] *)
  Definition L0 : list (Z * word) :=
    [(8%Z, ret); (16%Z, s0e); (24%Z, s1e); (32%Z, s2e); (40%Z, s3e); (48%Z, CAN);
     (192%Z, s); (272%Z, s); (264%Z, MAXW); (88%Z, Z_to_bv 64 0); (80%Z, Z_to_bv 64 0); (96%Z, MAXW);
     (296%Z, (0xa3fa8 : word)); (304%Z, Z_to_bv 64 0); (312%Z, s); (320%Z, Z_to_bv 64 10); (328%Z, G);
     (336%Z, s4e); (344%Z, s5e); (352%Z, s6e); (360%Z, s7e); (368%Z, s8e)].
  Definition MB0 : word -> option byte := apply_stores mem L0.

  #[using="Type"] Lemma L0_inb : inb (map fst L0) = true. Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma L0_sep : sepb (map fst L0) = true. Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma L0_dis : distinctb (map fst L0) = true. Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma L0_keys : forall k, In k (map fst L0) -> (8 <= k <= 368)%Z.
  Proof. intros k Hk. pose proof (ZStores.forallb_In _ _ k L0_inb Hk) as B. cbn beta in B.
    apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia. Qed.

  #[using="tp str A HOK"] Lemma slot_MB0 : forall k v, In (k, v) L0 -> rdn SEGS MB0 (SLOT k) 8 = Some (W8 v).
  Proof. intros k v Hin. unfold MB0. apply as_slot; [apply L0_inb | apply L0_sep | apply L0_dis | exact Hin]. Qed.

  #[using="A HOK"] Lemma INV_MB0 : INV MB0 0.
  Proof.
    pose proof HOK as K; destruct K. pose proof (u64_range s). pose proof (u64_range G). pose proof (u64_range tp).
    assert (OUT : forall (a : word) n, (bv_unsigned a + Z.of_nat n <= usp - 368 \/ usp <= bv_unsigned a)%Z ->
                  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z -> rdn SEGS MB0 a n = rdn SEGS mem a n).
    { intros a n Ha Hnw. unfold MB0. apply as_rdn_sep; [apply L0_inb | | exact Hnw].
      intros k Hk. pose proof (L0_keys k Hk). lia. }
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - split; [|split; [|split; [|split]]].
      + intros k v Hin. apply slot_MB0. unfold SLOTS in Hin. cbn [In] in Hin.
        decompose [or] Hin; try contradiction;
          match goal with H : (_, _) = (k, v) |- _ => injection H as <- <- end; unfold L0; in_list.
      + rewrite OUT; [exact Hcan0 | lia | lia].
      + unfold MB0. eapply store_ok_mono; [apply as_grows | exact Hstk0].
      + unfold MB0. eapply store_ok_mono; [apply as_grows | exact Herr0].
      + split; [| unfold MB0; apply as_grows].
        intros x (O1 & O2 & _). unfold in_rng in O1. revert O1. u_norm. intros O1.
        unfold MB0. apply as_out; [apply L0_inb | lia].
    - rewrite at_0. apply slot_MB0. unfold L0; in_list.
    - apply slot_MB0. unfold L0; in_list.
    - apply slot_MB0. unfold L0; in_list.
    - apply slot_MB0. unfold L0; in_list.
    - apply slot_MB0. unfold L0; in_list.
    - rewrite OUT; [exact Hstr0 | lia | lia].
    - intros x Hx. pose proof Hx as Hx'. unfold C10A, TABA in Hx'. unfold MB0. rewrite as_out; [apply Hro0; exact Hx | apply L0_inb | u_norm; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition L5 : list (Z * word) := Eval cbn in firstn 5 L0.
  Definition L9 : list (Z * word) := Eval cbn in firstn 9 L0.

  #[using="s tp CAN str A HOK"] Lemma rd5_got : rdn SEGS (apply_stores mem L5) (Z_to_bv 64 GOTA) 8 = Some (W8 G).
  Proof.
    pose proof HOK as K; destruct K. rewrite as_rdn_sep; [exact Hgot0 | vm_compute; reflexivity | | unfold GOTA; u_norm; lia].
    intros k Hk. cbn [L5 map fst In] in Hk. unfold GOTA in *. u_norm. lia.
  Qed.
  #[using="s tp str A HOK"] Lemma rd5_can : rdn SEGS (apply_stores mem L5) G 8 = Some (W8 CAN).
  Proof.
    pose proof HOK as K; destruct K. pose proof (u64_range G). rewrite as_rdn_sep; [exact Hcan0 | vm_compute; reflexivity | | lia].
    intros k Hk. cbn [L5 map fst In] in Hk. lia.
  Qed.
  #[using="tp G str A HOK"] Lemma rd9 : forall k v, In (k, v) L9 -> rdn SEGS (apply_stores mem L9) (SLOT k) 8 = Some (W8 v).
  Proof. intros k v Hin. apply as_slot; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hin]. Qed.

  Ltac okm :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub SEGS mem (SLOT 368) _ 368 8); [u_norm; lia | exact (Hstk HOK) | u_norm; lia | u_norm; cbn; lia].
  (* [comment removed for export] *)
  Ltac msd F D k vv :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := SLOT k) (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
        | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
        | okm ]
      | step_simpl].

  #[using="str A HOK"] Lemma p1_run : forall regs,
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 4 = tp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 10 ->
    getr regs 8 = s0e -> getr regs 9 = s1e -> getr regs 18 = s2e -> getr regs 19 = s3e -> getr regs 20 = s4e ->
    getr regs 21 = s5e -> getr regs 22 = s6e -> getr regs 23 = s7e -> getr regs 24 = s8e ->
    exists r,
      msteps SEGS (mkst regs (0xa3f44 : word) mem rom) (mkst r (0xa3588 : word) MB0 rom)
      /\ getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
      /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
      /\ regs_agree (fun x => In x BIG) regs r.
  Proof.
    intros regs H1 H2 H4 H10 H11 H12 H8 H9 H18 H19 H20 H21 H22 H23 H24.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs. pose proof (u64_range G) as HGr.
    eexists. split.
    - stepiv F_a3f44 D_a3f44 (SLOT 288) ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
      msd F_a3f48 D_a3f48 8%Z ret.                                  (* [comment removed for export] *)
      msd F_a3f4c D_a3f4c 16%Z s0e.                                 (* [comment removed for export] *)
      msd F_a3f50 D_a3f50 24%Z s1e.                                 (* [comment removed for export] *)
      msd F_a3f54 D_a3f54 32%Z s2e.                                 (* [comment removed for export] *)
      msd F_a3f58 D_a3f58 40%Z s3e.                                 (* [comment removed for export] *)
      stepn F_a3f5c D_a3f5c.                                        (* [comment removed for export] *)
      stepn F_a3f60 D_a3f60.                                        (* [comment removed for export] *)
      stepn F_a3f64 D_a3f64.                                        (* [comment removed for export] *)
      stepn F_a3f68 D_a3f68.                                        (* [comment removed for export] *)
      mld F_a3f6c D_a3f6c G rd5_got.                                (* [comment removed for export] *)
      mld F_a3f70 D_a3f70 CAN rd5_can.                              (* [comment removed for export] *)
      msd F_a3f74 D_a3f74 48%Z CAN.                                 (* [comment removed for export] *)
      stepn F_a3f78 D_a3f78.                                        (* [comment removed for export] *)
      msd F_a3f7c D_a3f7c 192%Z s.                                  (* [comment removed for export] *)
      msd F_a3f80 D_a3f80 272%Z s.                                  (* [comment removed for export] *)
      msd F_a3f84 D_a3f84 264%Z MAXW.                               (* [comment removed for export] *)
      stepiv F_a3f88 D_a3f88 (SLOT 280) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).   (* [comment removed for export] *)
      stepn F_a3f8c D_a3f8c.                                        (* [comment removed for export] *)
      stepn F_a3f90 D_a3f90.                                        (* [comment removed for export] *)
      mld F_a3420 D_a3420 s (rd9 272 s ltac:(unfold L9; in_list)).          (* [comment removed for export] *)
      mld F_a3424 D_a3424 MAXW (rd9 264 MAXW ltac:(unfold L9; in_list)).    (* [comment removed for export] *)
      mld F_a3428 D_a3428 s (rd9 192 s ltac:(unfold L9; in_list)).          (* [comment removed for export] *)
      stepn F_a342c D_a342c.                                        (* [comment removed for export] *)
      stepn F_a3430 D_a3430.                                        (* [comment removed for export] *)
      stepn F_a3434 D_a3434.                                        (* [comment removed for export] *)
      stepand F_a3438 D_a3438 (Z_to_bv 64 0) ltac:(gres; rwH; apply v_and_0_l).   (* [comment removed for export] *)
      stepiv F_a343c D_a343c (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sub; f_equal; lia).   (* [comment removed for export] *)
      msd F_a3440 D_a3440 88%Z (Z_to_bv 64 0).                     (* [comment removed for export] *)
      msd F_a3444 D_a3444 80%Z (Z_to_bv 64 0).                     (* [comment removed for export] *)
      stepb_tk F_a3448 D_a3448 ltac:(cond_compute).                (* [comment removed for export] *)
      msd F_a3450 D_a3450 96%Z MAXW.                                (* [comment removed for export] *)
      stepret F_a3454 D_a3454 (0xa3f94 : word) ltac:(apply bv_eq; vm_compute; reflexivity).
      stepiv F_a3f94 D_a3f94 (SLOT 280) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).   (* [comment removed for export] *)
      stepn F_a3f98 D_a3f98.                                        (* [comment removed for export] *)
      stepn F_a3f9c D_a3f9c.                                        (* [comment removed for export] *)
      stepn F_a3fa0 D_a3fa0.                                        (* [comment removed for export] *)
      stepn F_a3fa4 D_a3fa4.                                        (* [comment removed for export] *)
      stepiv F_a3520 D_a3520 (SLOT 368) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).  (* [comment removed for export] *)
      msd F_a3524 D_a3524 296%Z (0xa3fa8 : word).                   (* [comment removed for export] *)
      msd F_a3528 D_a3528 304%Z (Z_to_bv 64 0).                     (* [comment removed for export] *)
      msd F_a352c D_a352c 312%Z s.                                  (* [comment removed for export] *)
      msd F_a3530 D_a3530 320%Z (Z_to_bv 64 10).                    (* [comment removed for export] *)
      msd F_a3534 D_a3534 328%Z G.                                  (* [comment removed for export] *)
      msd F_a3538 D_a3538 336%Z s4e.                                (* [comment removed for export] *)
      msd F_a353c D_a353c 344%Z s5e.                                (* [comment removed for export] *)
      msd F_a3540 D_a3540 352%Z s6e.                                (* [comment removed for export] *)
      msd F_a3544 D_a3544 360%Z s7e.                                (* [comment removed for export] *)
      msd F_a3548 D_a3548 368%Z s8e.                                (* [comment removed for export] *)
      stepn F_a354c D_a354c.                                        (* [comment removed for export] *)
      stepn F_a3550 D_a3550.                                        (* [comment removed for export] *)
      stepb_ft F_a3554 D_a3554 ltac:(rwH; cond_compute).             (* [comment removed for export] *)
      stepn F_a3558 D_a3558.                                        (* [comment removed for export] *)
      stepn F_a355c D_a355c.                                        (* [comment removed for export] *)
      stepb_ft F_a3560 D_a3560 ltac:(rwH; cond_compute).             (* [comment removed for export] *)
      stepn F_a3564 D_a3564.                                        (* [comment removed for export] *)
      stepn F_a3568 D_a3568.                                        (* [comment removed for export] *)
      stepn F_a356c D_a356c.                                        (* [comment removed for export] *)
      stepn F_a3570 D_a3570.                                        (* [comment removed for export] *)
      stepn F_a3574 D_a3574.                                        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. unfold BIG. solve_regs_agree.
  Qed.

  #[using="str A HOK"] Theorem strtoul_run : forall regs,
    ret_ok ret ->
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 4 = tp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 10 ->
    getr regs 8 = s0e -> getr regs 9 = s1e -> getr regs 18 = s2e -> getr regs 19 = s3e -> getr regs 20 = s4e ->
    getr regs 21 = s5e -> getr regs 22 = s6e -> getr regs 23 = s7e -> getr regs 24 = s8e ->
    exists r m', msteps SEGS (mkst regs (0xa3f44 : word) mem rom) (mkst r ret m' rom) /\ POSTF regs r m'.
  Proof.
    intros regs Hret H1 H2 H4 H10 H11 H12 H8 H9 H18 H19 H20 H21 H22 H23 H24.
    pose proof HOK as K; destruct K.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3588 : word) MB0 rom)
             (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                       /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
                       /\ regs_agree (fun x => In x BIG) regs r)
             (fun r m' => mkst r ret m' rom)).
    - apply p1_run; assumption.
    - cbv beta. intros r1 (R2 & R9 & R8 & R18 & R20 & R21 & R4 & AG1).
      apply (ws_run (Z.to_nat A) regs r1 MB0 0); try assumption; try lia. apply INV_MB0.
  Qed.
End ST.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ref_strtoul : forall mem (s sp tp G CAN : word) (str : list byte) (A : Z) rom regs (ret : word),
  stH mem s sp tp G CAN str A ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 4 = tp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 10 ->
  exists regs' mem',
    msteps SEGS (mkst regs (0xa3f44 : word) mem rom) (mkst regs' ret mem' rom)
    /\ regs_agree (fun x => In x strtoul_clob) regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 368), 368%Z); (Z_to_bv 64 (bv_unsigned tp - 164), 4%Z)].
Proof.
  intros mem s sp tp G CAN str A rom regs ret HOK Hret H1 H2 H4 H10 H11 H12.
  destruct (strtoul_run mem s sp tp G CAN str A rom ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
              (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) HOK regs Hret H1 H2 H4 H10 H11 H12
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (r & m' & RUN & P).
  destruct P as (HI2 & R2 & R1 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & AG).
  exists r, m'. split; [exact RUN|]. split.
  - assert (AG' : regs_agree (fun x => In x ([1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24] ++ strtoul_clob)%list) regs r).
    { eapply regs_agree_mono; [|exact AG]. unfold BIG, strtoul_clob. cbn [In app]. intros x Hx. tauto. }
    cbn [app] in AG'.
    apply (regs_agree_drop _ 24); [|exact R24]. apply (regs_agree_drop _ 23); [|exact R23].
    apply (regs_agree_drop _ 22); [|exact R22]. apply (regs_agree_drop _ 21); [|exact R21].
    apply (regs_agree_drop _ 20); [|exact R20]. apply (regs_agree_drop _ 19); [|exact R19].
    apply (regs_agree_drop _ 18); [|exact R18]. apply (regs_agree_drop _ 9); [|exact R9].
    apply (regs_agree_drop _ 8); [|exact R8]. apply (regs_agree_drop _ 2); [|rewrite H2; exact R2].
    apply (regs_agree_drop _ 1); [|rewrite H1; exact R1].
    eapply regs_agree_mono; [|exact AG']. cbn [In]. intros x Hx. tauto.
  - exact (proj2 (proj2 (proj2 (proj2 HI2)))).
Qed.

