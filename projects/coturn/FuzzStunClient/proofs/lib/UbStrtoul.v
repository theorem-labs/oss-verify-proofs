(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase RefStrLib UbMemchr UbTolower Ub_code_1b104_1c2fc Ub_code_225f0_235f0 Ub_code_235f0_245f0 .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation W8 v := (word_to_le_bytes 8 v).
Definition MAXW : word := Z_to_bv 64 18446744073709551615.   (* [comment removed for export] *)
Definition TABA : Z := 0x1146c.                             (* [comment removed for export] *)
Definition C10A : Z := 0x10570.                             (* [comment removed for export] *)
Definition GOTA : Z := 0x257a0.                             (* [comment removed for export] *)
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
    Hsp_ro : (0x11574 <= usp - 368)%Z;                       (* [comment removed for export] *)
    Hsp_str : (usp <= bv_unsigned s \/ bv_unsigned s + L <= usp - 368)%Z;
    Herr  : store_ok SEGS mem ERR 4 = true;
    Htp   : (0x11574 + 164 <= utp)%Z;                         (* [comment removed for export] *)
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
     (296%Z, (0x2399c : word)); (304%Z, Z_to_bv 64 0); (312%Z, s); (320%Z, Z_to_bv 64 10); (328%Z, G);
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

  Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  Lemma slots_k : forall k v, In (k, v) SLOTS -> (8 <= k <= 368)%Z.
  Proof.
    intros k v Hin. assert (H : In k (map fst SLOTS)) by (apply in_map_iff; exists (k, v); auto).
    cbn [SLOTS map fst In] in H. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition miss_slots (a : Z) (n : Z) : Prop :=
    forall k v, In (k, v) SLOTS -> (a + n <= usp - k \/ usp - k + 8 <= a)%Z.

  Lemma INV2_store : forall m (a : Z) (bs : list byte),
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
      rewrite rdn_wbytes_out; [apply S1; exact Hin | u_norm; lia | u_norm; lia | u_norm; lia].
    - rewrite rdn_wbytes_out; [exact S2 | u_norm; lia | lia | u_norm; lia].
    - eapply store_ok_mono; [apply wbytes_grows | exact S3].
    - eapply store_ok_mono; [apply wbytes_grows | exact S4].
    - eapply frame_mod_trans_same; [exact S5|]. split; [|apply wbytes_grows].
      intros x (O1 & O2 & _). unfold in_rng in O1, O2. revert O1 O2. u_norm. intros O1 O2.
      apply MemSplit.wbytes_outside; u_norm; lia.
  Qed.

  Lemma INV_rpos : forall m i j, INV m i -> (0 <= j)%Z -> (bv_unsigned s + j < 2 ^ 64)%Z ->
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

  Lemma rd_str : forall m i j, INV m i -> (0 <= j < L)%Z -> rdn SEGS m (at_ s j) 1 = Some [B_ j].
  Proof.
    intros m i j (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro) Hj. unfold B_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_nth1 SEGS m s (length str)); [exact Rs | lia].
  Qed.

  Lemma rd_tab : forall m i (c : Z), INV m i -> (0 <= c < 256)%Z ->
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

  Lemma rd_c10 : forall m i, INV m i ->
    exists bs, rdn SEGS m (Z_to_bv 64 C10A) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 C10).
  Proof.
    intros m i (HI2 & Rr & Rse & Rsl & Rb & Rre & Rs & Rro).
    destruct rd_C10_img as (bs & R & E). exists bs. split; [|exact E].
    rewrite (rdn_ext SEGS 8 m (fun _ => None)); [exact R | unfold C10A; u_norm; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Rro. revert Hx. unfold C10A. u_norm. lia.
  Qed.

  Lemma rd_slot : forall m k v, INV2 m -> In (k, v) SLOTS -> rdn SEGS m (SLOT k) 8 = Some (W8 v).
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
  Lemma epi_run : forall regs m (res : word),
    INV2 m -> ret_ok ret -> getr regs 2 = SLOT 368 -> getr regs 8 = res ->
    exists r,
      msteps SEGS (mkst regs (0x23904 : word) m rom) (mkst r ret m rom)
      /\ getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ret /\ getr r 8 = s0e /\ getr r 9 = s1e
      /\ getr r 18 = s2e /\ getr r 19 = s3e /\ getr r 20 = s4e /\ getr r 21 = s5e /\ getr r 22 = s6e
      /\ getr r 23 = s7e /\ getr r 24 = s8e
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24]%list) regs r.
  Proof.
    intros regs m res HI2 Hret H2 H8.
    pose proof HOK as K; destruct K. pose proof (u64_range G).
    pose proof HI2 as (S1 & SG & _).
    eexists. split.
    - stepn F_23904 D_23904.                                        (* [comment removed for export] *)
      mld F_23908 D_23908 (0x2399c : word) (rd_slot m 296 _ HI2 ltac:(in_slots)).   (* [comment removed for export] *)
      mld F_2390c D_2390c (Z_to_bv 64 0) (rd_slot m 304 _ HI2 ltac:(in_slots)).      (* [comment removed for export] *)
      mld F_23910 D_23910 s (rd_slot m 312 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_23914 D_23914 (Z_to_bv 64 10) (rd_slot m 320 _ HI2 ltac:(in_slots)).     (* [comment removed for export] *)
      mld F_23918 D_23918 G (rd_slot m 328 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_2391c D_2391c s4e (rd_slot m 336 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_23920 D_23920 s5e (rd_slot m 344 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_23924 D_23924 s6e (rd_slot m 352 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_23928 D_23928 s7e (rd_slot m 360 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      mld F_2392c D_2392c s8e (rd_slot m 368 _ HI2 ltac:(in_slots)).                (* [comment removed for export] *)
      stepiv F_23930 D_23930 (SLOT 288) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).  (* [comment removed for export] *)
      stepret F_23934 D_23934 (0x2399c : word) ltac:(reflexivity).                   (* [comment removed for export] *)
      stepb_tk F_2399c D_2399c ltac:(cond_compute).                                  (* [comment removed for export] *)
      mld F_239bc D_239bc CAN SG.                                                     (* [comment removed for export] *)
      mld F_239c0 D_239c0 CAN (rd_slot m 48 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      stepb_ft F_239c4 D_239c4 ltac:(unfold c_eq; apply bv_eqb_refl).                (* [comment removed for export] *)
      mld F_239c8 D_239c8 ret (rd_slot m 8 _ HI2 ltac:(in_slots)).                   (* [comment removed for export] *)
      mld F_239cc D_239cc s0e (rd_slot m 16 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_239d0 D_239d0 s1e (rd_slot m 24 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_239d4 D_239d4 s2e (rd_slot m 32 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      mld F_239d8 D_239d8 s3e (rd_slot m 40 _ HI2 ltac:(in_slots)).                  (* [comment removed for export] *)
      stepiv F_239dc D_239dc sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
      stepret F_239e0 D_239e0 ret ltac:(reflexivity).
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
  Lemma I_2 : forall m i, INV m i -> INV2 m. Proof. intros m i H; exact (proj1 H). Qed.
  Lemma I_rpos : forall m i, INV m i -> rdn SEGS m (SLOT 272) 8 = Some (W8 (at_ s i)).
  Proof. intros m i H. exact (proj1 (proj2 H)). Qed.
  Lemma I_shend : forall m i, INV m i -> rdn SEGS m (SLOT 96) 8 = Some (W8 MAXW).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 H))). Qed.
  Lemma I_shlim : forall m i, INV m i -> rdn SEGS m (SLOT 88) 8 = Some (W8 (Z_to_bv 64 0)).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
  Lemma I_buf : forall m i, INV m i -> rdn SEGS m (SLOT 192) 8 = Some (W8 s).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
  Lemma I_rend : forall m i, INV m i -> rdn SEGS m (SLOT 264) 8 = Some (W8 MAXW).
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
  Lemma I_ok : forall m i, INV m i -> store_ok SEGS m (SLOT 368) 368 = true.
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj1 H)))). Qed.
  Lemma I_okE : forall m i, INV m i -> store_ok SEGS m ERR 4 = true.
  Proof. intros m i H. exact (proj1 (proj2 (proj2 (proj2 (proj1 H))))). Qed.

  Lemma neq_max : forall i, (0 <= bv_unsigned s + i < 2 ^ 64 - 1)%Z -> c_eq (at_ s i) MAXW = false.
  Proof.
    intros i Hi. unfold c_eq, bv_eqb, MAXW. rewrite at_u by lia. rewrite u_Z2bv by lia. apply Z.eqb_neq. lia.
  Qed.
  Lemma ltu_max_false : forall y : word, c_ltu MAXW y = false.
  Proof. intros y. pose proof (u64_range y). unfold c_ltu, bv_ltu, MAXW. rewrite u_Z2bv by lia. apply Z.ltb_ge. lia. Qed.
  Lemma lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
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
  Lemma d68_run : forall regs0 regs m,
    INV2 m -> ret_ok ret -> getr regs 2 = SLOT 368 ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23850 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m HI2 Hret H2 AG.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23904 : word) m rom)
             (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + stepn F_23850 D_23850.             (* [comment removed for export] *)
        stepn F_23854 D_23854.             (* [comment removed for export] *)
        stepn F_23858 D_23858.             (* [comment removed for export] *)
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
  Lemma done_run : forall regs0 regs m i,
    INV m i -> (1 <= i)%Z -> (bv_unsigned s + i < 2 ^ 64 - 1)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23838 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i HI Hi Hiw Hret H2 H9 H8 AG.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i - 1) HI ltac:(lia) ltac:(lia)) as HI1.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23850 : word) (wbytes m (SLOT 272) (W8 (at_ s (i - 1)))) rom)
             (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    2:{ cbv beta. intros r1 (R2 & AG1). apply (d68_run regs0 r1); try assumption. exact (I_2 _ _ HI1). }
    destruct (c_ltu (getr regs 19) MAXW) eqn:CY.
    - eexists. split.
      + mld F_23838 D_23838 (Z_to_bv 64 0) (I_shlim _ _ HI).      (* [comment removed for export] *)
        stepb_ft F_2383c D_2383c ltac:(exact lts_0_0).             (* [comment removed for export] *)
        mld F_23840 D_23840 (at_ s i) (I_rpos _ _ HI).              (* [comment removed for export] *)
        stepn F_23844 D_23844.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i - 1));
            [exact F_23848 | reflexivity | exact D_23848
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepb_ft F_2384c D_2384c ltac:(rwH; exact CY).              (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - eexists. split.
      + mld F_23838 D_23838 (Z_to_bv 64 0) (I_shlim _ _ HI).
        stepb_ft F_2383c D_2383c ltac:(exact lts_0_0).
        mld F_23840 D_23840 (at_ s i) (I_rpos _ _ HI).
        stepn F_23844 D_23844.
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i - 1));
            [exact F_23848 | reflexivity | exact D_23848
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI ]
          | step_simpl].
        stepb_tk F_2384c D_2384c ltac:(rwH; exact CY).              (* [comment removed for export] *)
        stepn F_238bc D_238bc.                                      (* [comment removed for export] *)
        stepb_tk F_238c0 D_238c0 ltac:(rwH; cond_compute).         (* [comment removed for export] *)
        stepb_tk F_238dc D_238dc ltac:(rwH; apply ltu_max_false). (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
  Qed.

  #[local] Notation W4 v := (word_to_le_bytes 4 v).
  Lemma lenW4 : forall v : word, length (W4 v) = 4%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  Lemma INV_err : forall m i (v : word), INV m i -> INV (wbytes m ERR (W4 v)) i.
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
  Lemma tab_cond : forall c : byte,
    c_ltu (Z_to_bv 64 (bv_unsigned (TAB (bv_unsigned c)))) (Z_to_bv 64 10) = isdig (bv_unsigned c).
  Proof.
    intros c. pose proof (u8_range c). pose proof (u8_range (TAB (bv_unsigned c))).
    unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. apply TAB_dig. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma tab_addr : forall c : byte,
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
  Lemma skip_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 21 = Z_to_bv 64 TABA -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23870 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
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
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23870 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 21 = Z_to_bv 64 TABA /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_23870 D_23870 F_23874 D_23874 F_23878 D_23878 F_2387c D_2387c F_23880 D_23880 F_23884 D_23884 HI HI1 i.
          stepn F_23888 D_23888.                                  (* [comment removed for export] *)
          mtab F_2388c D_2388c HI1.                               (* [comment removed for export] *)
          stepb_tk F_23890 D_23890 ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R21 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      pose proof (INV_err _ _ (Z_to_bv 64 34) HI1) as HI2e.
      pose proof (INV_rpos _ _ i HI2e ltac:(lia) ltac:(lia)) as HI3.
      eapply (runs_trans_km SEGS _
               (fun r => mkst r (0x23850 : word)
                  (wbytes (wbytes (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) ERR (W4 (Z_to_bv 64 34))) (SLOT 272) (W8 (at_ s i))) rom)
               (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      2:{ cbv beta. intros r1 (R2 & AG1). apply (d68_run regs0 r1); try assumption. exact (I_2 _ _ HI3). }
      eexists. split.
      + getc F_23870 D_23870 F_23874 D_23874 F_23878 D_23878 F_2387c D_2387c F_23880 D_23880 F_23884 D_23884 HI HI1 i.
        stepn F_23888 D_23888.                                    (* [comment removed for export] *)
        mtab F_2388c D_2388c HI1.                                 (* [comment removed for export] *)
        stepb_ft F_23890 D_23890 ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
        stepn F_23894 D_23894.                                    (* [comment removed for export] *)
        stepn F_1bd58 D_1bd58.                                    (* [comment removed for export] *)
        stepn F_1bd5c D_1bd5c.                                    (* [comment removed for export] *)
        stepret F_1bd60 D_1bd60 (0x23898 : word) ltac:(apply bv_eq; vm_compute; reflexivity).
        stepn F_23898 D_23898.                                    (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := ERR) (v := Z_to_bv 64 34);
            [exact F_2389c | reflexivity | exact D_2389c
            | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | exact (I_okE _ _ HI1) ]
          | step_simpl].                                          (* [comment removed for export] *)
        stepn F_238a0 D_238a0.                                    (* [comment removed for export] *)
        stepn F_238a4 D_238a4.                                    (* [comment removed for export] *)
        stepn F_238a8 D_238a8.                                    (* [comment removed for export] *)
        stepn F_238ac D_238ac.                                    (* [comment removed for export] *)
        mld F_238b0 D_238b0 (Z_to_bv 64 0) (I_shlim _ _ HI2e).   (* [comment removed for export] *)
        stepb_tk F_238b4 D_238b4 ltac:(exact lts_0_0).           (* [comment removed for export] *)
        mld F_23840 D_23840 (at_ s (i + 1)) (I_rpos _ _ HI2e).   (* [comment removed for export] *)
        stepn F_23844 D_23844.                                    (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s i);
            [exact F_23848 | reflexivity | exact D_23848
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI2e ]
          | step_simpl].                                          (* [comment removed for export] *)
        stepb_tk F_2384c D_2384c ltac:(rwH; apply ltu_max_false).   (* [comment removed for export] *)
        stepn F_238bc D_238bc.                                    (* [comment removed for export] *)
        stepb_tk F_238c0 D_238c0 ltac:(rwH; cond_compute).       (* [comment removed for export] *)
        stepb_tk F_238dc D_238dc ltac:(rwH; apply ltu_max_false). (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ovf_run : forall regs0 regs m i (c : byte),
    INV m i -> (0 <= i <= A)%Z -> isdig (bv_unsigned c) = true -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23824 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi DG Hret H2 H9 H8 H18 H10 H4 AG.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23870 : word) m rom)
             (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                       /\ getr r 21 = Z_to_bv 64 TABA /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + stepn F_23824 D_23824.                                    (* [comment removed for export] *)
        stepn F_23828 D_23828.                                    (* [comment removed for export] *)
        stepn F_2382c D_2382c.                                    (* [comment removed for export] *)
        mtab F_23830 D_23830 HI.                                  (* [comment removed for export] *)
        stepb_tk F_23834 D_23834 ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - cbv beta. intros r1 (R2 & R9 & R8' & R18 & R21 & R4 & AG1).
      apply (skip_run (Z.to_nat (A - i)) regs0 r1 m i); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop2_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 22 = Z_to_bv 64 C10 -> getr regs 23 = Z_to_bv 64 9 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23588 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs m i Hcnt HI Hi Hret H2 H9 H8 H22 H23 H4 AG.
    pose proof HOK as K; destruct K.
    pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
    pose proof (u8_range (B_ i)) as U.
    destruct (isdig (bv_unsigned (B_ i))) eqn:DG.
    2:{ (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23838 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      - eexists. split.
        + getc F_23588 D_23588 F_2358c D_2358c F_23590 D_23590 F_23594 D_23594 F_23598 D_23598 F_2359c D_2359c HI HI1 i.
          stepn F_235a0 D_235a0.                                  (* [comment removed for export] *)
          stepn F_235a4 D_235a4.                                  (* [comment removed for export] *)
          stepb_ft F_235a8 D_235a8 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_235ac D_235ac.                                  (* [comment removed for export] *)
          stepn F_23818 D_23818.                                  (* [comment removed for export] *)
          stepb_tk F_2381c D_2381c ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
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
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23824 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                           /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                           /\ regs_agree (fun x => In x BIG) regs0 r)
                 (fun r m' => mkst r ret m' rom)).
        * eexists. split.
          -- getc F_23588 D_23588 F_2358c D_2358c F_23590 D_23590 F_23594 D_23594 F_23598 D_23598 F_2359c D_2359c HI HI1 i.
             stepn F_235a0 D_235a0.                               (* [comment removed for export] *)
             stepn F_235a4 D_235a4.                               (* [comment removed for export] *)
             stepb_tk F_235a8 D_235a8 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
             stepb_ft F_235c4 D_235c4 ltac:(rwH; exact CY).       (* [comment removed for export] *)
             stepn F_235c8 D_235c8.                               (* [comment removed for export] *)
             stepn F_235cc D_235cc.                               (* [comment removed for export] *)
             stepn F_235d0 D_235d0.                               (* [comment removed for export] *)
             stepb_ft F_235d4 D_235d4 ltac:(rwH; exact CZ).       (* [comment removed for export] *)
             stepn F_235d8 D_235d8.                               (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
          apply (ovf_run regs0 r1 _ (i + 1) (B_ i)); try assumption; lia.
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23588 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 22 = Z_to_bv 64 C10
                           /\ getr r 23 = Z_to_bv 64 9 /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
                 (fun r m' => mkst r ret m' rom)).
        * eexists. split.
          -- getc F_23588 D_23588 F_2358c D_2358c F_23590 D_23590 F_23594 D_23594 F_23598 D_23598 F_2359c D_2359c HI HI1 i.
             stepn F_235a0 D_235a0.
             stepn F_235a4 D_235a4.
             stepb_tk F_235a8 D_235a8 ltac:(rwH; rewrite dig_cond, DG; reflexivity).
             stepb_ft F_235c4 D_235c4 ltac:(rwH; exact CY).
             stepn F_235c8 D_235c8.
             stepn F_235cc D_235cc.
             stepn F_235d0 D_235d0.
             stepb_tk F_235d4 D_235d4 ltac:(rwH; exact CZ).       (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R22 & R23 & R4 & AG1).
          apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23824 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_23588 D_23588 F_2358c D_2358c F_23590 D_23590 F_23594 D_23594 F_23598 D_23598 F_2359c D_2359c HI HI1 i.
          stepn F_235a0 D_235a0.
          stepn F_235a4 D_235a4.
          stepb_tk F_235a8 D_235a8 ltac:(rwH; rewrite dig_cond, DG; reflexivity).
          stepb_tk F_235c4 D_235c4 ltac:(rwH; exact CY).          (* [comment removed for export] *)
          stepn F_23818 D_23818.                                  (* [comment removed for export] *)
          stepb_ft F_2381c D_2381c ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_23820 D_23820.                                  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (ovf_run regs0 r1 _ (i + 1) (B_ i)); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop1_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 9 -> getr regs 22 = Z_to_bv 64 10 -> getr regs 23 = Z_to_bv 64 0x19999999 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23540 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs m i Hcnt HI Hi Hret H2 H9 H8 H18 H22 H23 H4 AG.
    pose proof HOK as K; destruct K.
    pose proof (u64_range s) as Hs.
    pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
    pose proof (u8_range (B_ i)) as U.
    destruct (isdig (bv_unsigned (B_ i))) eqn:DG.
    2:{ (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23838 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      - eexists. split.
        + getc F_23540 D_23540 F_23544 D_23544 F_23548 D_23548 F_2354c D_2354c F_23550 D_23550 F_23554 D_23554 HI HI1 i.
          stepn F_23558 D_23558.                                  (* [comment removed for export] *)
          stepn F_2355c D_2355c.                                  (* [comment removed for export] *)
          stepn F_23560 D_23560.                                  (* [comment removed for export] *)
          stepb_ft F_23564 D_23564 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_23568 D_23568.                                  (* [comment removed for export] *)
          stepn F_2356c D_2356c.                                  (* [comment removed for export] *)
          stepb_tk F_23570 D_23570 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      - cbv beta. intros r1 (R2 & R9 & R8' & AG1).
        apply (done_run regs0 r1 _ (i + 1)); try assumption; lia. }
    assert (HiA : (i < A)%Z).
    { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (D & _ & _). rewrite D in DG. discriminate. }
    destruct (c_ltu (v_addw (v_mul (getr regs 19) (Z_to_bv 64 10)) (getr regs 21)) (Z_to_bv 64 0x19999999)) eqn:CX.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23540 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 9
                         /\ getr r 22 = Z_to_bv 64 10 /\ getr r 23 = Z_to_bv 64 0x19999999 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_23540 D_23540 F_23544 D_23544 F_23548 D_23548 F_2354c D_2354c F_23550 D_23550 F_23554 D_23554 HI HI1 i.
          stepn F_23558 D_23558.
          stepn F_2355c D_2355c.
          stepn F_23560 D_23560.
          stepb_tk F_23564 D_23564 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepb_ft F_2353c D_2353c ltac:(rwH; exact CX).          (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R22 & R23 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      destruct (rd_c10 _ _ HI1) as (bsC & RC & EC).
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23588 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 22 = Z_to_bv 64 C10
                         /\ getr r 23 = Z_to_bv 64 9 /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_23540 D_23540 F_23544 D_23544 F_23548 D_23548 F_2354c D_2354c F_23550 D_23550 F_23554 D_23554 HI HI1 i.
          stepn F_23558 D_23558.
          stepn F_2355c D_2355c.
          stepn F_23560 D_23560.
          stepb_tk F_23564 D_23564 ltac:(rwH; rewrite dig_cond, DG; reflexivity).
          stepb_tk F_2353c D_2353c ltac:(rwH; exact CX).          (* [comment removed for export] *)
          stepn F_23568 D_23568.
          stepn F_2356c D_2356c.
          stepb_ft F_23570 D_23570 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
          stepn F_23574 D_23574.                                  (* [comment removed for export] *)
          chain_step; [reflexivity
            | eapply step_ld with (v := Z_to_bv 64 C10);
              [exact F_23578 | reflexivity | exact D_23578
              | gres; imm_norm;
                lazymatch goal with |- rdn _ _ ?a _ = _ =>
                  lazymatch type of RC with rdn _ _ ?c _ = _ =>
                    replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
                exact RC
              | exact EC ]
            | step_simpl]; vnorm.                                   (* [comment removed for export] *)
          stepn F_2357c D_2357c.                                  (* [comment removed for export] *)
          stepn F_23580 D_23580.                                  (* [comment removed for export] *)
          stepn F_23584 D_23584.                                  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R22 & R23 & R4 & AG1).
        apply (loop2_run (Z.to_nat (A - (i + 1))) regs0 r1 _ (i + 1)%Z); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dig_run : forall regs0 regs m i (c : byte),
    INV m i -> (0 <= i <= A)%Z -> isdig (bv_unsigned c) = true -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x234fc : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi DG Hret H2 H9 H8 H18 H10 H4 AG. pose proof (u8_range c).
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23540 : word) m rom)
             (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 9
                       /\ getr r 22 = Z_to_bv 64 10 /\ getr r 23 = Z_to_bv 64 0x19999999 /\ getr r 4 = tp
                       /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + stepn F_234fc D_234fc.                                    (* [comment removed for export] *)
        stepb_ft F_23500 D_23500 ltac:(rwH; cond_compute).         (* [comment removed for export] *)
        stepn F_23504 D_23504.                                    (* [comment removed for export] *)
        stepn F_23508 D_23508.                                    (* [comment removed for export] *)
        stepn F_2350c D_2350c.                                    (* [comment removed for export] *)
        stepb_ft F_23510 D_23510 ltac:(rwH; rewrite dig_cond, DG; reflexivity).   (* [comment removed for export] *)
        stepn F_23514 D_23514.                                    (* [comment removed for export] *)
        stepn F_23518 D_23518.                                    (* [comment removed for export] *)
        stepn F_2351c D_2351c.                                    (* [comment removed for export] *)
        stepn F_23520 D_23520.                                    (* [comment removed for export] *)
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
  Lemma einval_run : forall regs0 regs m i,
    INV m i -> (1 <= i <= A + 1)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x234b0 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i HI Hi Hret H2 H9 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs. pose proof (u64_range tp) as Htpr.
    pose proof (INV_rpos m i (i - 1) HI ltac:(lia) ltac:(lia)) as HI1.
    set (m1 := wbytes m (SLOT 272) (W8 (at_ s (i - 1)))) in HI1.
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _
             (fun r => mkst r (0x23904 : word)
                (wbytes (wbytes (wbytes (wbytes m1 (SLOT 88) (W8 (Z_to_bv 64 0))) (SLOT 80) (W8 (v_sub s (at_ s (i - 1)))))
                           (SLOT 96) (W8 MAXW)) ERR (W4 (Z_to_bv 64 22))) rom)
             (fun r => getr r 2 = SLOT 368 /\ regs_agree (fun x => In x BIG) regs0 r)
             (fun r m' => mkst r ret m' rom)).
    - eexists. split.
      + mld F_234b0 D_234b0 (Z_to_bv 64 0) (I_shlim _ _ HI).      (* [comment removed for export] *)
        stepb_ft F_234b4 D_234b4 ltac:(exact lts_0_0).             (* [comment removed for export] *)
        mld F_234b8 D_234b8 (at_ s i) (I_rpos _ _ HI).              (* [comment removed for export] *)
        stepn F_234bc D_234bc.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i - 1));
            [exact F_234c0 | reflexivity | exact D_234c0
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; rewrite at_addi; f_equal; lia
            | okstk HI ]
          | step_simpl].                                            (* [comment removed for export] *)
        fold m1.
        stepn F_234c4 D_234c4.                                      (* [comment removed for export] *)
        stepn F_234c8 D_234c8.                                      (* [comment removed for export] *)
        stepn F_234cc D_234cc.                                      (* [comment removed for export] *)
        mld F_23260 D_23260 (at_ s (i - 1)) (I_rpos _ _ HI1).      (* [comment removed for export] *)
        mld F_23264 D_23264 MAXW (I_rend _ _ HI1).                  (* [comment removed for export] *)
        mld F_23268 D_23268 s (I_buf _ _ HI1).                      (* [comment removed for export] *)
        stepn F_2326c D_2326c.                                      (* [comment removed for export] *)
        stepn F_23270 D_23270.                                      (* [comment removed for export] *)
        stepn F_23274 D_23274.                                      (* [comment removed for export] *)
        stepand F_23278 D_23278 (Z_to_bv 64 0) ltac:(gres; rwH; apply v_and_0_l).   (* [comment removed for export] *)
        stepn F_2327c D_2327c.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 88) (v := Z_to_bv 64 0);
            [exact F_23280 | reflexivity | exact D_23280
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | okstk HI1 ]
          | step_simpl].                                            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 80);
            [exact F_23284 | reflexivity | exact D_23284
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | okfr1 HI1 ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepb_tk F_23288 D_23288 ltac:(cond_compute).              (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := SLOT 96) (v := MAXW);
            [exact F_23290 | reflexivity | exact D_23290
            | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | okfr2 HI1 ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepret F_23294 D_23294 (0x234d0 : word) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
        stepn F_234d0 D_234d0.                                      (* [comment removed for export] *)
        stepn F_1bd58 D_1bd58.                                      (* [comment removed for export] *)
        stepn F_1bd5c D_1bd5c.                                      (* [comment removed for export] *)
        stepret F_1bd60 D_1bd60 (0x234d4 : word) ltac:(apply bv_eq; vm_compute; reflexivity).
        stepn F_234d4 D_234d4.                                      (* [comment removed for export] *)
        stepn F_234d8 D_234d8.                                      (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := ERR) (v := Z_to_bv 64 22);
            [exact F_234dc | reflexivity | exact D_234dc
            | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi; u_norm; f_equal; lia
            | gres; rwH; reflexivity
            | do 3 (eapply store_ok_mono; [apply wbytes_grows|]); exact (I_okE _ _ HI1) ]
          | step_simpl].                                            (* [comment removed for export] *)
        stepn F_234e0 D_234e0.                                      (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact H2|]. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
    - cbv beta. intros r1 (R2 & AG1).
      assert (HI2f : INV2 (wbytes (wbytes (wbytes (wbytes m1 (SLOT 88) (W8 (Z_to_bv 64 0))) (SLOT 80) (W8 (v_sub s (at_ s (i - 1)))))
                           (SLOT 96) (W8 MAXW)) ERR (W4 (Z_to_bv 64 22)))).
      { pose proof (I_2 _ _ HI1) as B.
        assert (MS : forall a, (a = 88 \/ a = 80 \/ a = 96)%Z -> miss_slots (usp - a) 8).
        { intros a Ha k v Hin. assert (HK : In k (map fst SLOTS)) by (apply in_map_iff; exists (k, v); auto).
          cbn [SLOTS map fst In] in HK. lia. }
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
  Lemma dispatch_run : forall regs0 regs m i (c : byte),
    INV m i -> (1 <= i <= A + 1)%Z -> c = B_ (i - 1) -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x23494 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi Hc Hret H2 H9 H8 H18 H10 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u8_range c) as U.
    destruct (isdig (bv_unsigned c)) eqn:DG.
    - (* [comment removed for export] *)
      assert (HiA : (i - 1 < A)%Z).
      { destruct (Z.eq_dec (i - 1) A) as [E|]; [|lia]. destruct Hstop0 as (D & _ & _).
        rewrite <- E, <- Hc in D. rewrite D in DG. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x234fc : word) m rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * stepb_tk F_23494 D_23494 ltac:(rwH; cond_compute).      (* [comment removed for export] *)
          stepn F_2349c D_2349c.                                  (* [comment removed for export] *)
          stepn F_234a0 D_234a0.                                  (* [comment removed for export] *)
          stepn F_234a4 D_234a4.                                  (* [comment removed for export] *)
          mtab F_234a8 D_234a8 HI.                                (* [comment removed for export] *)
          stepb_tk F_234ac D_234ac ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (dig_run regs0 r1 m i c); try assumption; lia.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x234b0 : word) m rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * stepb_tk F_23494 D_23494 ltac:(rwH; cond_compute).
          stepn F_2349c D_2349c.
          stepn F_234a0 D_234a0.
          stepn F_234a4 D_234a4.
          mtab F_234a8 D_234a8 HI.
          stepb_ft F_234ac D_234ac ltac:(rwH; rewrite tab_cond; exact DG).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R4 & AG1).
        apply (einval_run regs0 r1 m i); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sign_run : forall regs0 regs m i (c : byte),
    INV m i -> (1 <= i <= A + 1)%Z -> c = B_ (i - 1) -> issp (bv_unsigned c) = false -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 10 = Z_to_bv 64 (bv_unsigned c) -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x233ec : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
  Proof.
    intros regs0 regs m i c HI Hi Hc Hsp' Hret H2 H9 H8 H18 H10 H4 AG.
    pose proof HOK as K; destruct K. pose proof (u8_range c) as U. pose proof (u64_range s) as Hs.
    destruct (issign (bv_unsigned c)) eqn:SG.
    - (* [comment removed for export] *)
      assert (HiA : (i - 1 < A)%Z).
      { destruct (Z.eq_dec (i - 1) A) as [E|]; [|lia]. destruct Hstop0 as (_ & _ & D).
        rewrite <- E, <- Hc in D. rewrite D in SG. discriminate. }
      pose proof (INV_rpos m i (i + 1) HI ltac:(lia) ltac:(lia)) as HI1.
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23494 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
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
        exists r1, msteps SEGS (mkst regs1 (0x233fc : word) m rom) (mkst r1 (0x23494 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
          /\ (getr r1 2 = SLOT 368 /\ getr r1 9 = SLOT 280 /\ getr r1 8 = MAXW /\ getr r1 18 = Z_to_bv 64 10
              /\ getr r1 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r1 4 = tp
              /\ regs_agree (fun x => In x BIG) regs0 r1)).
      { intros regs1 Q2 Q9 Q8 Q18 Q10 Q4 QAG. clear H2 H9 H8 H18 H10 H4 AG.
        eexists. split.
        - mld F_233fc D_233fc (at_ s i) (I_rpos _ _ HI).           (* [comment removed for export] *)
          mld F_23400 D_23400 MAXW (I_shend _ _ HI).               (* [comment removed for export] *)
          stepn F_23404 D_23404.                                    (* [comment removed for export] *)
          stepn F_23408 D_23408.                                    (* [comment removed for export] *)
          stepn F_2340c D_2340c.                                    (* [comment removed for export] *)
          stepb_ft F_23410 D_23410 ltac:(rwH; apply neq_max; lia). (* [comment removed for export] *)
          stepn F_23414 D_23414.                                    (* [comment removed for export] *)
          chain_step; [reflexivity
            | eapply step_sd_at with (a := SLOT 272) (v := at_ s (i + 1));
              [exact F_23418 | reflexivity | exact D_23418
              | gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia
              | gres; rwH; rewrite at_addi; reflexivity
              | okstk HI ]
            | step_simpl].                                          (* [comment removed for export] *)
          chain_step; [reflexivity
            | eapply step_lbu;
              [exact F_2341c | reflexivity | exact D_2341c
              | gres; imm_norm; rwH; rewrite ?v_addi_0; apply (rd_str _ _ _ HI1); lia ]
            | step_simpl]; vnorm.                                   (* [comment removed for export] *)
          stepn F_23420 D_23420.                                    (* [comment removed for export] *)
          stepb_ft F_23424 D_23424 ltac:(rwH; cond_compute).       (* [comment removed for export] *)
          stepn F_23428 D_23428.                                    (* [comment removed for export] *)
          apply mst_refl.
        - post. eapply regs_agree_trans; [exact QAG|]. unfold BIG. solve_regs_agree. }
      destruct (Z.eqb_spec (bv_unsigned c) 45) as [E45|N45].
      + eapply (runs_trans SEGS _ (fun r => mkst r (0x233fc : word) m rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                           /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)).
        * eexists. split.
          -- stepn F_233ec D_233ec.                                 (* [comment removed for export] *)
             stepb_tk F_233f0 D_233f0 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_eq; exact E45).   (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1). apply TAIL; assumption.
      + assert (E43 : bv_unsigned c = 43%Z).
        { unfold issign in SG. apply orb_true_iff in SG as [SG|SG]; apply Z.eqb_eq in SG; lia. }
        eapply (runs_trans SEGS _ (fun r => mkst r (0x233fc : word) m rom)
                 (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                           /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp /\ regs_agree (fun x => In x BIG) regs0 r)).
        * eexists. split.
          -- stepn F_233ec D_233ec.                                 (* [comment removed for export] *)
             stepb_ft F_233f0 D_233f0 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_neq; exact N45).  (* [comment removed for export] *)
             stepn F_233f4 D_233f4.                                 (* [comment removed for export] *)
             stepb_ft F_233f8 D_233f8 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_eq; exact E43).   (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1). apply TAIL; assumption.
    - (* [comment removed for export] *)
      assert (N45 : bv_unsigned c <> 45%Z).
      { intros E. unfold issign in SG. rewrite E in SG. discriminate. }
      assert (N43 : bv_unsigned c <> 43%Z).
      { intros E. unfold issign in SG. rewrite E in SG. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23494 : word) m rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned c) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * stepn F_233ec D_233ec.                                    (* [comment removed for export] *)
          stepb_ft F_233f0 D_233f0 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_neq; exact N45).
          stepn F_233f4 D_233f4.                                    (* [comment removed for export] *)
          stepb_tk F_233f8 D_233f8 ltac:(rwH; rewrite eq_lit by lia; apply Z.eqb_neq; exact N43).  (* [comment removed for export] *)
          stepn F_2342c D_2342c.                                    (* [comment removed for export] *)
          stepn F_23430 D_23430.                                    (* [comment removed for export] *)
          stepb_ft F_23434 D_23434 ltac:(rwH; cond_compute).         (* [comment removed for export] *)
          stepn F_23438 D_23438.                                    (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R10 & R4 & AG1).
        apply (dispatch_run regs0 r1 m i c); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ws_run : forall (cnt : nat) regs0 regs m i,
    (Z.of_nat cnt = A - i)%Z -> INV m i -> (0 <= i <= A)%Z -> ret_ok ret ->
    getr regs 2 = SLOT 368 -> getr regs 9 = SLOT 280 -> getr regs 8 = MAXW ->
    getr regs 18 = Z_to_bv 64 10 -> getr regs 20 = Z_to_bv 64 5 -> getr regs 21 = Z_to_bv 64 32 -> getr regs 4 = tp ->
    regs_agree (fun x => In x BIG) regs0 regs ->
    exists r m', msteps SEGS (mkst regs (0x233c8 : word) m rom) (mkst r ret m' rom) /\ POSTF regs0 r m'.
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
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x233c8 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_233c8 D_233c8 F_233cc D_233cc F_233d0 D_233d0 F_233d4 D_233d4 F_233d8 D_233d8 F_233dc D_233dc HI HI1 i.
          stepn F_233e0 D_233e0.                                  (* [comment removed for export] *)
          stepb_tk F_233e4 D_233e4 ltac:(rwH; rewrite sp_cond1; exact SP1).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R20 & R21 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      assert (HiA : (i < A)%Z).
      { destruct (Z.eq_dec i A) as [->|]; [|lia]. destruct Hstop0 as (_ & D & _). unfold issp in D.
        rewrite SP1, SP2 in D. discriminate. }
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x233c8 : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_233c8 D_233c8 F_233cc D_233cc F_233d0 D_233d0 F_233d4 D_233d4 F_233d8 D_233d8 F_233dc D_233dc HI HI1 i.
          stepn F_233e0 D_233e0.
          stepb_ft F_233e4 D_233e4 ltac:(rwH; rewrite sp_cond1; exact SP1).   (* [comment removed for export] *)
          stepb_tk F_233e8 D_233e8 ltac:(rwH; rewrite sp_cond2; exact SP2).   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold BIG. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R9 & R8' & R18 & R20 & R21 & R4 & AG1).
        apply (IH (Z.to_nat (A - (i + 1))) ltac:(lia) regs0 r1 _ (i + 1)%Z); try assumption; lia.
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x233ec : word) (wbytes m (SLOT 272) (W8 (at_ s (i + 1)))) rom)
               (fun r => getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
                         /\ getr r 10 = Z_to_bv 64 (bv_unsigned (B_ i)) /\ getr r 4 = tp
                         /\ regs_agree (fun x => In x BIG) regs0 r)
               (fun r m' => mkst r ret m' rom)).
      + eexists. split.
        * getc F_233c8 D_233c8 F_233cc D_233cc F_233d0 D_233d0 F_233d4 D_233d4 F_233d8 D_233d8 F_233dc D_233dc HI HI1 i.
          stepn F_233e0 D_233e0.
          stepb_ft F_233e4 D_233e4 ltac:(rwH; rewrite sp_cond1; exact SP1).
          stepb_ft F_233e8 D_233e8 ltac:(rwH; rewrite sp_cond2; exact SP2).   (* [comment removed for export] *)
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

  Lemma as_rdn_sep : forall l m (a : word) n,
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

  Lemma as_slot : forall l m k v,
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

  Lemma as_out : forall l m (x : word),
    inb (map fst l) = true ->
    (bv_unsigned x < usp - 368 \/ usp <= bv_unsigned x)%Z -> apply_stores m l x = m x.
  Proof.
    pose proof HOK as K; destruct K.
    induction l as [|[k v] l IH]; intros m x Hinb Hx; [reflexivity|].
    cbn [apply_stores]. cbn [map fst inb forallb] in Hinb. apply andb_true_iff in Hinb as [Hk Hinb].
    apply andb_true_iff in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
    rewrite IH by assumption. apply MemSplit.wbytes_outside; rewrite lenW8; u_norm; lia.
  Qed.

  Lemma as_grows : forall l m, mem_grows m (apply_stores m l).
  Proof.
    induction l as [|[k v] l IH]; intros m; [apply mem_grows_refl|].
    cbn [apply_stores]. eapply mem_grows_trans; [apply wbytes_grows | apply IH].
  Qed.

  (* [comment removed for export] *)
  Definition L0 : list (Z * word) :=
    [(8%Z, ret); (16%Z, s0e); (24%Z, s1e); (32%Z, s2e); (40%Z, s3e); (48%Z, CAN);
     (192%Z, s); (272%Z, s); (264%Z, MAXW); (88%Z, Z_to_bv 64 0); (80%Z, Z_to_bv 64 0); (96%Z, MAXW);
     (296%Z, (0x2399c : word)); (304%Z, Z_to_bv 64 0); (312%Z, s); (320%Z, Z_to_bv 64 10); (328%Z, G);
     (336%Z, s4e); (344%Z, s5e); (352%Z, s6e); (360%Z, s7e); (368%Z, s8e)].
  Definition MB0 : word -> option byte := apply_stores mem L0.

  Lemma L0_inb : inb (map fst L0) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma L0_sep : sepb (map fst L0) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma L0_dis : distinctb (map fst L0) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma L0_keys : forall k, In k (map fst L0) -> (8 <= k <= 368)%Z.
  Proof. intros k Hk. pose proof (ZStores.forallb_In _ _ k L0_inb Hk) as B. cbn beta in B.
    apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia. Qed.

  Lemma slot_MB0 : forall k v, In (k, v) L0 -> rdn SEGS MB0 (SLOT k) 8 = Some (W8 v).
  Proof. intros k v Hin. unfold MB0. apply as_slot; [apply L0_inb | apply L0_sep | apply L0_dis | exact Hin]. Qed.

  Lemma INV_MB0 : INV MB0 0.
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

  Lemma rd5_got : rdn SEGS (apply_stores mem L5) (Z_to_bv 64 GOTA) 8 = Some (W8 G).
  Proof.
    pose proof HOK as K; destruct K. rewrite as_rdn_sep; [exact Hgot0 | vm_compute; reflexivity | | unfold GOTA; u_norm; lia].
    intros k Hk. cbn [L5 map fst In] in Hk. unfold GOTA in *. u_norm. lia.
  Qed.
  Lemma rd5_can : rdn SEGS (apply_stores mem L5) G 8 = Some (W8 CAN).
  Proof.
    pose proof HOK as K; destruct K. pose proof (u64_range G). rewrite as_rdn_sep; [exact Hcan0 | vm_compute; reflexivity | | lia].
    intros k Hk. cbn [L5 map fst In] in Hk. lia.
  Qed.
  Lemma rd9 : forall k v, In (k, v) L9 -> rdn SEGS (apply_stores mem L9) (SLOT k) 8 = Some (W8 v).
  Proof. intros k v Hin. apply as_slot; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hin]. Qed.

  Ltac okm :=
    (try store_ok_peel_fast1; repeat (eapply store_ok_mono; [apply wbytes_grows|]));
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

  Lemma p1_run : forall regs,
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 4 = tp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 10 ->
    getr regs 8 = s0e -> getr regs 9 = s1e -> getr regs 18 = s2e -> getr regs 19 = s3e -> getr regs 20 = s4e ->
    getr regs 21 = s5e -> getr regs 22 = s6e -> getr regs 23 = s7e -> getr regs 24 = s8e ->
    exists r,
      msteps SEGS (mkst regs (0x23938 : word) mem rom) (mkst r (0x233c8 : word) MB0 rom)
      /\ getr r 2 = SLOT 368 /\ getr r 9 = SLOT 280 /\ getr r 8 = MAXW /\ getr r 18 = Z_to_bv 64 10
      /\ getr r 20 = Z_to_bv 64 5 /\ getr r 21 = Z_to_bv 64 32 /\ getr r 4 = tp
      /\ regs_agree (fun x => In x BIG) regs r.
  Proof.
    intros regs H1 H2 H4 H10 H11 H12 H8 H9 H18 H19 H20 H21 H22 H23 H24.
    pose proof HOK as K; destruct K. pose proof (u64_range s) as Hs. pose proof (u64_range G) as HGr.
    eexists. split.
    - stepiv F_23938 D_23938 (SLOT 288) ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
      msd F_2393c D_2393c 8%Z ret.                                  (* [comment removed for export] *)
      msd F_23940 D_23940 16%Z s0e.                                 (* [comment removed for export] *)
      msd F_23944 D_23944 24%Z s1e.                                 (* [comment removed for export] *)
      msd F_23948 D_23948 32%Z s2e.                                 (* [comment removed for export] *)
      msd F_2394c D_2394c 40%Z s3e.                                 (* [comment removed for export] *)
      stepn F_23950 D_23950.                                        (* [comment removed for export] *)
      stepn F_23954 D_23954.                                        (* [comment removed for export] *)
      stepn F_23958 D_23958.                                        (* [comment removed for export] *)
      stepn F_2395c D_2395c.                                        (* [comment removed for export] *)
      mld F_23960 D_23960 G rd5_got.                                (* [comment removed for export] *)
      mld F_23964 D_23964 CAN rd5_can.                              (* [comment removed for export] *)
      msd F_23968 D_23968 48%Z CAN.                                 (* [comment removed for export] *)
      stepn F_2396c D_2396c.                                        (* [comment removed for export] *)
      msd F_23970 D_23970 192%Z s.                                  (* [comment removed for export] *)
      msd F_23974 D_23974 272%Z s.                                  (* [comment removed for export] *)
      msd F_23978 D_23978 264%Z MAXW.                               (* [comment removed for export] *)
      stepiv F_2397c D_2397c (SLOT 280) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).   (* [comment removed for export] *)
      stepn F_23980 D_23980.                                        (* [comment removed for export] *)
      stepn F_23984 D_23984.                                        (* [comment removed for export] *)
      mld F_23260 D_23260 s (rd9 272 s ltac:(unfold L9; in_list)).          (* [comment removed for export] *)
      mld F_23264 D_23264 MAXW (rd9 264 MAXW ltac:(unfold L9; in_list)).    (* [comment removed for export] *)
      mld F_23268 D_23268 s (rd9 192 s ltac:(unfold L9; in_list)).          (* [comment removed for export] *)
      stepn F_2326c D_2326c.                                        (* [comment removed for export] *)
      stepn F_23270 D_23270.                                        (* [comment removed for export] *)
      stepn F_23274 D_23274.                                        (* [comment removed for export] *)
      stepand F_23278 D_23278 (Z_to_bv 64 0) ltac:(gres; rwH; apply v_and_0_l).   (* [comment removed for export] *)
      stepiv F_2327c D_2327c (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sub; f_equal; lia).   (* [comment removed for export] *)
      msd F_23280 D_23280 88%Z (Z_to_bv 64 0).                     (* [comment removed for export] *)
      msd F_23284 D_23284 80%Z (Z_to_bv 64 0).                     (* [comment removed for export] *)
      stepb_tk F_23288 D_23288 ltac:(cond_compute).                (* [comment removed for export] *)
      msd F_23290 D_23290 96%Z MAXW.                                (* [comment removed for export] *)
      stepret F_23294 D_23294 (0x23988 : word) ltac:(apply bv_eq; vm_compute; reflexivity).
      stepiv F_23988 D_23988 (SLOT 280) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).   (* [comment removed for export] *)
      stepn F_2398c D_2398c.                                        (* [comment removed for export] *)
      stepn F_23990 D_23990.                                        (* [comment removed for export] *)
      stepn F_23994 D_23994.                                        (* [comment removed for export] *)
      stepn F_23998 D_23998.                                        (* [comment removed for export] *)
      stepiv F_23360 D_23360 (SLOT 368) ltac:(gres; imm_norm; rwH; unfold v_addi; u_norm; f_equal; lia).  (* [comment removed for export] *)
      msd F_23364 D_23364 296%Z (0x2399c : word).                   (* [comment removed for export] *)
      msd F_23368 D_23368 304%Z (Z_to_bv 64 0).                     (* [comment removed for export] *)
      msd F_2336c D_2336c 312%Z s.                                  (* [comment removed for export] *)
      msd F_23370 D_23370 320%Z (Z_to_bv 64 10).                    (* [comment removed for export] *)
      msd F_23374 D_23374 328%Z G.                                  (* [comment removed for export] *)
      msd F_23378 D_23378 336%Z s4e.                                (* [comment removed for export] *)
      msd F_2337c D_2337c 344%Z s5e.                                (* [comment removed for export] *)
      msd F_23380 D_23380 352%Z s6e.                                (* [comment removed for export] *)
      msd F_23384 D_23384 360%Z s7e.                                (* [comment removed for export] *)
      msd F_23388 D_23388 368%Z s8e.                                (* [comment removed for export] *)
      stepn F_2338c D_2338c.                                        (* [comment removed for export] *)
      stepn F_23390 D_23390.                                        (* [comment removed for export] *)
      stepb_ft F_23394 D_23394 ltac:(rwH; cond_compute).             (* [comment removed for export] *)
      stepn F_23398 D_23398.                                        (* [comment removed for export] *)
      stepn F_2339c D_2339c.                                        (* [comment removed for export] *)
      stepb_ft F_233a0 D_233a0 ltac:(rwH; cond_compute).             (* [comment removed for export] *)
      stepn F_233a4 D_233a4.                                        (* [comment removed for export] *)
      stepn F_233a8 D_233a8.                                        (* [comment removed for export] *)
      stepn F_233ac D_233ac.                                        (* [comment removed for export] *)
      stepn F_233b0 D_233b0.                                        (* [comment removed for export] *)
      stepn F_233b4 D_233b4.                                        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. unfold BIG. solve_regs_agree.
  Qed.

  Theorem strtoul_run : forall regs,
    ret_ok ret ->
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 4 = tp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 10 ->
    getr regs 8 = s0e -> getr regs 9 = s1e -> getr regs 18 = s2e -> getr regs 19 = s3e -> getr regs 20 = s4e ->
    getr regs 21 = s5e -> getr regs 22 = s6e -> getr regs 23 = s7e -> getr regs 24 = s8e ->
    exists r m', msteps SEGS (mkst regs (0x23938 : word) mem rom) (mkst r ret m' rom) /\ POSTF regs r m'.
  Proof.
    intros regs Hret H1 H2 H4 H10 H11 H12 H8 H9 H18 H19 H20 H21 H22 H23 H24.
    pose proof HOK as K; destruct K.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x233c8 : word) MB0 rom)
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
    msteps SEGS (mkst regs (0x23938 : word) mem rom) (mkst regs' ret mem' rom)
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

