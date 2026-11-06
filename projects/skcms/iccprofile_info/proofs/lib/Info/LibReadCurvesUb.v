(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibWP1Spec LibWP2Spec LibRodata LibFrame LibFPLib LibTagsCall LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfKc.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac perf_el3_core := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs;
  first [ Zify.zify_post_hook; xlia zchecker | zify_saturate; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook; xlia zchecker ].
Local Ltac perf_el3_clear_all := clear.  (* [comment removed for export] *)
Local Ltac perf_el3_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif perf_el3_has_var then perf_el3_core
  else first [ solve [perf_el3_clear_all; perf_el3_core] | perf_el3_core ].

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zext32_idiom : forall x : word, (bv_unsigned x < 4294967296)%Z ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) x) (Z_to_bv 64 32) = x.
Proof.
  intros x Hx. pose proof (u64_range x). apply bv_eq. rewrite u_srl64, u_mul64, !u_small by lia.
  change (32 mod 64)%Z with 32%Z. change (2 ^ 32)%Z with 4294967296%Z.
  rewrite Z.mod_small by lia. rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma srlw2_val : forall v : Z, (0 <= v <= 4294967292)%Z ->
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 (alu64 ALU_ADD (Z_to_bv 64 v) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 2))) : word)
  = ((v + 3) / 4)%Z.
Proof.
  intros v Hv.
  assert (Ha : bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 v) (Z_to_bv 64 3)) = (v + 3)%Z).
  { rewrite u_add64, !u_small by lia. apply Z.mod_small. lia. }
  rewrite (u_srlw_small _ _ 2); [ | rewrite u_small by lia; reflexivity | rewrite Ha; lia | ].
  - rewrite Ha. reflexivity.
  - rewrite Ha. change (2 ^ (2 mod 32))%Z with 4%Z. apply Z.div_lt_upper_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma newoff_val : forall (x12 : word) (v : Z), (bv_unsigned x12 < 4294967296)%Z -> (0 <= v <= 4294967292)%Z ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) x12) (Z_to_bv 64 32))
     (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (alu64 ALU_ADD (Z_to_bv 64 v) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 2))))))
  = (bv_unsigned x12 + 4 * ((v + 3) / 4))%Z.
Proof.
  intros x12 v Hx Hv. pose proof (u64_range x12).
  assert (Hq : (0 <= (v + 3) / 4 < 1073741824)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite u_add64, u_mul64, srlw2_val, zext32_idiom by lia. rewrite !u_small by lia.
  rewrite (Z.mod_small (4 * _)) by lia. apply Z.mod_small. lia.
Qed.

Lemma u_srl32 : forall w : word, bv_unsigned (alu64 ALU_SRL w (Z_to_bv 64 32)) = (bv_unsigned w / 4294967296)%Z.
Proof. intros. rewrite u_srl64, u_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sext32_ge : forall x : word, (bv_unsigned x < 4294967296)%Z ->
  (bv_unsigned x <= bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) : word))%Z.
Proof.
  intros x Hx. pose proof (u64_range x). rewrite w_addw. unfold v_addw. rewrite u_lit64a.
  rewrite (u_small 0) by lia. rewrite Z.add_0_r. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
  destruct (Z_lt_le_dec (bv_unsigned x) 2147483648).
  - rewrite (Z.mod_small (_ + _)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((bv_unsigned x + 2147483648) mod 4294967296)%Z with (bv_unsigned x + 2147483648 - 1 * 4294967296)%Z.
    + replace ((bv_unsigned x + 2147483648 - 1 * 4294967296 - 2147483648))%Z with ((bv_unsigned x  + 18446744069414584320) + (-1) * 2 ^ 64)%Z by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
    + rewrite <- (Z_mod_plus_full (bv_unsigned x + 2147483648) (-1) 4294967296).
      symmetry. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma xori_sltu : forall a b : word, exists r : Z,
  alu64 ALU_XOR (alu64 ALU_SLTU a b) (Z_to_bv 64 1) = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z /\
  (r = 1%Z <-> (bv_unsigned b <= bv_unsigned a)%Z).
Proof.
  intros a b.
  destruct (bv_unsigned a <? bv_unsigned b)%Z eqn:Hlt.
  - exists 0%Z. split; [|apply Z.ltb_lt in Hlt; lia]. apply bv_eq. rewrite u_xor64, u_sltu64, !u_small by lia. rewrite Hlt. reflexivity.
  - exists 1%Z. split; [|apply Z.ltb_ge in Hlt; lia]. apply bv_eq. rewrite u_xor64, u_sltu64, !u_small by lia. rewrite Hlt. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nullness_ok : forall buf w : word, (0 < bv_unsigned buf)%Z -> (bv_unsigned buf + bv_unsigned w < 2 ^ 64)%Z ->
  negb (bv_unsigned (alu64 ALU_XOR (Z_to_bv 64 1) (alu64 ALU_SLTU (Z_to_bv 64 0) (alu64 ALU_ADD buf w))) =? 0)%Z = false.
Proof.
  intros buf w Hb Hw. pose proof (u64_range buf). pose proof (u64_range w).
  rewrite u_xor64, u_sltu64, u_add64, !u_small by lia. rewrite Z.mod_small by lia.
  replace (0 <? bv_unsigned buf + bv_unsigned w)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma not_idiom : forall Cw : word,
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) Cw) (Z_to_bv 64 (-1)) = alu64 ALU_XOR Cw (Z_to_bv 64 (-1)).
Proof.
  intros Cw. pose proof (mkXor_denot (Env (vals_ev [Cw]) (blobs_ev [])) (EVar 0) (ELit (-1))) as H.
  change (mkXor (EVar 0) (ELit (-1))) with (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 0)) (ELit (-1))) in H.
  cbn [edenot] in H. exact H.
Qed.

Section Proof.
  Hypothesis Hrc : read_curve_contract SEGS wp1_infoub.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp buf C offw data : word) (size k len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = buf.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 size.
  Hypothesis H12 : getr regs 12 = offw.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 k.
  Hypothesis H14 : getr regs 14 = C.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hwc : (0 < k -> writable SEGS mem (bv_unsigned C) (32 * k))%Z.
  Hypothesis Hcal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hcend : (0 < k -> bv_unsigned C + 32 * k <= 2 ^ 64)%Z.
  Hypothesis Hal16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hwst : writable SEGS mem (bv_unsigned sp - 128) 128.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis Hd_sc : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 * k <= bv_unsigned sp - 128)%Z.
  Hypothesis Hd_dc : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 * k <= bv_unsigned data)%Z.
  Hypothesis Hd_ds : (bv_unsigned data + len <= bv_unsigned sp - 128 \/ bv_unsigned sp <= bv_unsigned data)%Z.

  #[local] Abbreviation fp0 := (fp_regs (FPState:=FPI)).

  Definition BIG : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 128), 128%Z); (C, (32 * k)%Z)].

  (* [comment removed for export] *)
  Definition QP (FPI' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept fp0 (fp_regs (FPState:=FPI')) /\
    (frame_mod mem mem' BIG /\
     exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z /\
       (r = 1%Z -> forall i, (0 <= i < k)%Z -> curve_ok SEGS mem' data len (bv_unsigned C + 32 * i))).
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem', st' = mkst (FP:=FPI') regs' ret mem' rom /\ QP FPI' regs' mem'.

  (* [comment removed for export] *)
  Definition MEMH (M : word -> option byte) : Prop :=
    cell64 SEGS M (bv_unsigned sp - 8) ret /\ cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8) /\
    cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9) /\ cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18) /\
    cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19) /\ cell64 SEGS M (bv_unsigned sp - 48) (getr regs 20) /\
    cell64 SEGS M (bv_unsigned sp - 56) (getr regs 21) /\ cell64 SEGS M (bv_unsigned sp - 64) (getr regs 22) /\
    cell64 SEGS M (bv_unsigned sp - 72) (getr regs 23) /\ cell64 SEGS M (bv_unsigned sp - 80) (getr regs 24) /\
    cell64 SEGS M (bv_unsigned sp - 88) (getr regs 25) /\
    frame_mod mem M BIG.

  (* [comment removed for export] *)
  Definition REGH (j : Z) (FPI' : FPState) (R : bvmap 5 word) : Prop :=
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 96) /\ getr R 8 = C /\
    getr R 9 = Z_to_bv 64 size /\ getr R 11 = Z_to_bv 64 (j + 1) /\
    (bv_unsigned (getr R 12) <= size)%Z /\ getr R 18 = buf /\ getr R 19 = Z_to_bv 64 (32 * j) /\
    getr R 20 = alu64 ALU_XOR C (Z_to_bv 64 (-1)) /\ getr R 21 = Z_to_bv 64 1 /\ getr R 22 = Z_to_bv 64 k /\
    getr R 23 = Z_to_bv 64 4294967293 /\
    (forall r, In r [3; 4; 26; 27]%bv -> getr R r = getr regs r) /\
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get fp0 r).

  Definition HINV (j : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    REGH j FPI' R /\ MEMH M /\ (0 <= j < k)%Z /\
    (forall i, (0 <= i < j)%Z -> curve_ok SEGS M data len (bv_unsigned C + 32 * i)).

  (* [comment removed for export] *)
  #[local] Abbreviation VALS R FR j :=
    (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ fjunk_vals fp0 ++ [Z_to_bv 64 (bv_unsigned C + 32 * j)]).

  Definition SRH : list expr :=
    [ELit 0; EVar 1; EAlu ALU_ADD (EVar 66) (ELit (-96)); EVar 67; EVar 68; EVar 5; EVar 6; EVar 7;
     EVar 78; EVar 75; EVar 10; EVar 11; EVar 12; EVar 13;
     EVar 14; EVar 15; EVar 16; EVar 17; EVar 74; EVar 19; EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 78)) (ELit (-1)); ELit 1;
     EVar 77; ELit 4294967293; EVar 24; EVar 25; EVar 90; EVar 91; EVar 28; EVar 29; EVar 30; EVar 31].
  Definition SFH : list expr :=
    [EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 104; EVar 105;
     EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 49; EVar 114; EVar 115; EVar 116;
     EVar 117; EVar 118; EVar 119; EVar 120; EVar 121; EVar 122; EVar 123; EVar 60; EVar 61; EVar 62; EVar 63].

  Definition KNH : list kentry :=
    [KAlign (EVar 66) 16; KAlign (EVar 78) 8; KRange (EVar 77) 1 4; KRange (EVar 11) 1 4;
     KRange (EVar 74) 1 140737488355328;
     KWord (SA (EVar 66) (-8)) 8 (EVar 65); KWord (SA (EVar 66) (-16)) 8 (EVar 72);
     KWord (SA (EVar 66) (-24)) 8 (EVar 73); KWord (SA (EVar 66) (-32)) 8 (EVar 82);
     KWord (SA (EVar 66) (-40)) 8 (EVar 83); KWord (SA (EVar 66) (-48)) 8 (EVar 84);
     KWord (SA (EVar 66) (-56)) 8 (EVar 85); KWord (SA (EVar 66) (-64)) 8 (EVar 86);
     KWord (SA (EVar 66) (-72)) 8 (EVar 87); KWord (SA (EVar 66) (-80)) 8 (EVar 88);
     KWord (SA (EVar 66) (-88)) 8 (EVar 89);
     KWr (SA (EVar 66) (-128)) 128;
     KDisj (SA (EVar 66) (-128)) 128 (SA (EVar 128) 0) 32].

  Lemma pack : forall (j : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte),
    HINV j FPI' R M ->
    let E := Env (vals_ev (VALS R (fp_regs (FPState:=FPI')) j)) (blobs_ev [bs]) in
    regs_ok E SRH R /\ fregs_ok E SFH (fp_regs (FPState:=FPI')) /\ know_ok SEGS E M KNH /\
    regs_ok E (sr_vars 64) regs /\ fregs_ok E (sfr_vars 96) fp0.
  Proof using H10 H11 H13 H14 Hal16 Hcal Hd_dc Hd_ds Hd_sc Hdok Hin Hk Hra Hsp Hwc Hwst.
    intros j FPI' R M ((R2 & R8 & R9 & R11 & R12 & R18 & R19 & R20 & R21 & R22 & R23 & RK & FK) &
                       (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & Mfr) & Hj & Hcurves) E.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr. pose proof (u64_range buf) as Hbufr.
    pose proof (u64_range data) as Hdr.
    pose proof (writable_frame SEGS mem M BIG _ _ Mfr Hwst) as (W1 & W2 & W3 & W4).
    pose proof Hin as (I1 & I2 & I3). pose proof Hdok as (D1 & D2 & D3 & D4 & D5).
    pose proof (Hwc ltac:(lia)) as (V1 & V2 & V3 & V4).
    clear Hcurves Mfr.
    unfold cell64, cell in *.
    split; [|split; [|split; [|split]]].
    - replace SRH with (sr_upds (sr_vars 0)
        [(2, EAlu ALU_ADD (EVar 66) (ELit (-96))); (8, EVar 78); (9, EVar 75); (18, EVar 74);
         (20, mkXor (EVar 78) (ELit (-1))); (21, ELit 1); (22, EVar 77);
         (23, ELit 4294967293); (3, EVar 67); (4, EVar 68); (26, EVar 90); (27, EVar 91)]%bv) by (vm_compute; reflexivity).
      apply regs_ok_pins; [exact (regs_ok_vars [] R _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?mkXor_denot; cbn [edenot]; ev_simpl E; rewrite_getr; rewrite ?alu_add_lit;
                                  first [ reflexivity | apply RK; in_lit | f_equal; lia ] |]).
      apply Forall_nil.
    - replace SFH with (sr_upds (sfr_vars 32)
        [(8, EVar 104); (9, EVar 105); (18, EVar 114); (19, EVar 115); (20, EVar 116);
         (21, EVar 117); (22, EVar 118); (23, EVar 119); (24, EVar 120); (25, EVar 121); (26, EVar 122); (27, EVar 123)]%bv)
        by (vm_compute; reflexivity).
      apply fregs_ok_pins; [exact (fregs_ok_vars (junk_vals R) (fp_regs (FPState:=FPI')) _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; apply FK; in_lit |]).
      apply Forall_nil.
    - unfold KNH.
      constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal16]|].
      constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite H14; exact Hcal]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite H13, u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite R11, u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite H10; lia|].
      Ltac kw E0 H := eapply (kword_intro SEGS _ _ (EVar 66) sp _ _ _ _);
                      [cbn [edenot]; ev_simpl E0; assumption | cbn [edenot]; ev_simpl E0; reflexivity | lia | lia | lia | lia |
                       lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                         lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by lia; rewrite_getr; exact H end end].
      constructor; [kw E M1|]. constructor; [kw E M2|]. constructor; [kw E M3|]. constructor; [kw E M4|].
      constructor; [kw E M5|]. constructor; [kw E M6|]. constructor; [kw E M7|]. constructor; [kw E M8|].
      constructor; [kw E M9|]. constructor; [kw E M10|]. constructor; [kw E M11|].
      constructor; [apply (kwr_intro SEGS E M (EVar 66) sp (-128) 128);
                    [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                     replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp - 128)%Z by lia; exact W4]|].
      constructor; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp, u_small by lia; lia|].
      constructor.
    - exact (regs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI'))) regs
               (fjunk_vals fp0 ++ [Z_to_bv 64 (bv_unsigned C + 32 * j)]) (blobs_ev [bs])).
    - exact (fregs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI')) ++ junk_vals regs) fp0
               [Z_to_bv 64 (bv_unsigned C + 32 * j)] (blobs_ev [bs])).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.
  Ltac kcell_auto HK b k n H :=
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with Some ?v => kcell HK b k n v H end end.

  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by lia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | f_equal; lia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.

  (* [comment removed for export] *)
  Lemma memh_facts : forall M, (0 < k)%Z -> frame_mod mem M BIG ->
    data_ok M data len bs /\ rodata_clear M 0x103ec 0x10490 /\
    writable SEGS M (bv_unsigned sp - 128) 128 /\ writable SEGS M (bv_unsigned C) (32 * k).
  Proof using Hd_dc Hd_ds Hdok Hro Hwc Hwst.
    intros M Hk0 Hfr. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range data).
    destruct Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hwst as (W1 & W2 & W3 & W4). pose proof (Hwc Hk0) as HwcK.
    split; [eapply data_ok_frame; [exact Hfr | exact (conj D1 (conj D2 (conj D3 (conj D4 D5)))) | unfold BIG; solve_apart]|].
    split.
    { pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) Hwst Hro).
      pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) HwcK Hro).
      eapply rodata_clear_frame; [exact Hfr | exact Hro | lia | lia | unfold BIG; solve_apart]. }
    split; [eapply writable_frame; [exact Hfr | exact Hwst]|].
    eapply writable_frame; [exact Hfr | exact HwcK].
  Qed.

  (* [comment removed for export] *)
  Lemma pre_at : forall (M : word -> option byte) (I : FPState) (R' : bvmap 5 word) (j off : Z),
    (0 <= j < k)%Z -> (0 <= off <= size)%Z ->
    data_ok M data len bs -> rodata_clear M 0x103ec 0x10490 ->
    writable SEGS M (bv_unsigned sp - 128) 128 -> writable SEGS M (bv_unsigned C) (32 * k) ->
    getr R' 2 = Z_to_bv 64 (bv_unsigned sp - 96) ->
    getr R' 10 = Z_to_bv 64 (bv_unsigned buf + off) ->
    getr R' 11 = Z_to_bv 64 (size - off) ->
    getr R' 12 = Z_to_bv 64 (bv_unsigned C + 32 * j) ->
    getr R' 13 = Z_to_bv 64 (bv_unsigned sp - 92) ->
    rcurve_pre SEGS wp1_infoub data len bs (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 (bv_unsigned buf + off))
       (Z_to_bv 64 (bv_unsigned C + 32 * j)) (Z_to_bv 64 (bv_unsigned sp - 92)) (size - off) I R' M.
  Proof using Hal16 Hcal Hd_dc Hd_ds Hd_sc Hin.
    intros M I R' j off Hj Hoff MD MRO MW MWC R2 R10 R11 R12 R13.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr. pose proof (u64_range data) as Hdr.
    pose proof (u64_range buf) as Hbufr.
    destruct MD as (D1 & D2 & D3 & D4 & D5). destruct Hin as (I1 & I2 & I3).
    pose proof MW as (W1 & W2 & W3 & W4). pose proof MWC as (V1 & V2 & V3 & V4).
    unfold rcurve_pre. cbv zeta. cbn [w1_rcurve_d w1_ro_lo w1_ro_hi wp1_infoub].
    rewrite !u_small by lia.
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [exact (conj D1 (conj D2 (conj D3 (conj D4 D5))))|].
    split; [lia|].
    split; [unfold inDATA; lia|].
    split; [eapply writable_sub; [exact MWC|lia|lia|lia]|].
    split; [replace (bv_unsigned C + 32 * j)%Z with (bv_unsigned C + (4 * j) * 8)%Z by lia;
            rewrite Z_mod_plus_full; exact Hcal|].
    split; [apply mod_sub_multiple; [lia | exact Hal16 | reflexivity]|].
    split; [eapply writable_sub; [exact MW|lia|lia|lia]|].
    split; [exact MRO|].
    split; [lia|]. split; [lia|]. split; [lia|].
    right.
    split; [eapply writable_sub; [exact MW|lia|lia|lia]|].
    split; [clear -Hal16 Hspr; apply mod_sub_multiple; [lia | | reflexivity]; apply (Z.mod_divide _ 4); [lia|];
            apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (4*q)%Z; lia |].
    lia.
  Qed.

  Ltac post_regs_rc HR0 HF0 Mq :=
    lazymatch goal with
    | HR : regs_ok ?E1 ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?I) |- _ =>
        lift_id HR0 HR; lift_id HF0 HF;
        exists I, R2, Mq; split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|];
        lazymatch type of HR0 with id (regs_ok _ ?sr0 _) =>
          split; [exact (regs_same_on E1 sr0 sr regs R2 abi_kept HR0 HR ltac:(vm_compute; reflexivity))|] end;
        lazymatch type of HF0 with id (fregs_ok _ ?sfr0 _) =>
          split; [exact (fregs_same_on E1 sfr0 sfr fp0 _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|] end
    end.

  (* [comment removed for export] *)
  Ltac fin_fail HR0 HF0 HFR :=
    run_fp 40%nat (@nil Z) noscr true; subst_triv; fin_ret;
    lazymatch goal with |- Q (@mkst _ _ _ ?Mq _) =>
      post_regs_rc HR0 HF0 Mq;
      split; [exact HFR|]; exists 0%Z;
      split; [lazymatch goal with HR : regs_ok _ _ _ |- _ => regv HR (10%bv:reg); reflexivity end|];
      split; [lia|]; intros; exfalso; lia
    end.

  (* [comment removed for export] *)
  Ltac fin_exit HR0 HF0 HFR Hcv Hok R11 a b jj :=
    run_fp 40%nat (@nil Z) noscr true; subst_triv; fin_ret;
    lazymatch goal with |- Q (@mkst _ _ _ ?Mq _) =>
      post_regs_rc HR0 HF0 Mq;
      split; [exact HFR|];
      lazymatch goal with HR : regs_ok _ _ _ |- _ =>
        let r := fresh "r" in let Hr := fresh "Hr" in let Hr01 := fresh "Hr01" in let Hriff := fresh "Hriff" in
        destruct (xori_sltu a b) as (r & Hr & Hr01 & Hriff);
        exists r; split; [regv HR (10%bv:reg); exact Hr|]; split; [exact Hr01|];
        let Hi := fresh "Hi" in
        intros -> i Hi; rewrite R11, H13, !u_small in Hriff by lia;
        destruct (Z_lt_le_dec i jj); [apply Hcv; lia | replace i with jj by lia; exact Hok]
      end
    end.

  Lemma iter : forall (n : nat) (j : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte),
    (k - 1 - j < Z.of_nat n)%Z -> HINV j FPI' R M ->
    runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x1697c) M rom) Q.
  Proof using H10 H11 H13 H14 Hal16 Hcal Hcend Hd_dc Hd_ds Hd_sc Hdok Hin Hk Hra Hrc Hret Hro Hsize Hsp Hwc Hwst.
    induction n as [|n IH]; intros j FPI' R M Hn HI.
    { exfalso. destruct HI as (_ & _ & Hj & _). lia. }
    pose proof (pack j FPI' R M HI) as (HR & HF & HK & H64 & H96).
    pose proof (H64 : id _) as HR0. pose proof (H96 : id _) as HF0. clear H64 H96.
    destruct HI as ((R2 & R8 & R9 & R11 & R12 & R18 & R19 & R20 & R21 & R22 & R23 & RK & FK) &
                    (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & Mfr) & Hj & Hcurves).
    pose proof (memh_facts M ltac:(lia) Mfr) as (MD & MRO & MW & MWC).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr. pose proof (u64_range data) as Hdr.
    pose proof (u64_range buf) as Hbufr. pose proof (u64_range (getr R 12)) as H12r.
    pose proof MD as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof MW as (W1 & W2 & W3 & W4).
    assert (Hoff : (0 <= bv_unsigned (getr R 12) <= size)%Z) by lia.
    assert (HuC1 : bv_unsigned (Z_to_bv 64 (bv_unsigned C + 32 * j)) = (bv_unsigned C + 32 * j)%Z) by (apply u_small; lia).
    assert (Hu19 : bv_unsigned (Z_to_bv 64 (32 * j)) = (32 * j)%Z) by (apply u_small; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    run_fp 30%nat [0x1463c%Z] (dirs [false; false; false]) true
      by (rewrite ?zext32_idiom by lia; first [lia | apply nullness_ok; lia | mod2_split; apply Z.ltb_ge; lia]). subst M0. clear HLF.
    eapply rt_call.
    { eapply (Hrc data len bs _ _ _ _ (size - bv_unsigned (getr R 12))%Z FPI0 R0 M rom (Z_to_bv 64 0x169b4));
      [ regv HR (1%bv:reg); reflexivity
      | apply ret_ok_even; rewrite u_small by lia; reflexivity
      | apply (pre_at M FPI0 R0 j (bv_unsigned (getr R 12)) Hj Hoff MD MRO MW MWC) ].
      - regv_lin HR (2%bv:reg). rewrite Hsp. f_equal. lia.
      - regv HR (10%bv:reg). rewrite zext32_idiom by lia. rewrite H10. apply bv_eq.
        rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity.
      - regv HR (11%bv:reg). symmetry. apply Z_to_bv_lit. apply u_subw_small; [lia|]. rewrite H11, u_small by lia. reflexivity.
      - regv HR (12%bv:reg). rewrite H14, R19. apply bv_eq. rewrite u_add64, Hu19, u_small by lia. rewrite Z.mod_small by lia. lia.
      - regv_lin HR (13%bv:reg). rewrite Hsp. f_equal. lia. }
    cbv beta. intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hpost).
    unfold rcurve_post in Hpost. cbv zeta in Hpost. cbn [w1_rcurve_d wp1_infoub] in Hpost.
    destruct Hpost as (Hfr & r1 & Hr1 & Hr01 & Hok1 & Hpres & Hcs).
    rewrite !(u_small (bv_unsigned sp - 92)) in Hcs by lia.
    rewrite !(u_small (bv_unsigned sp - 92)) in Hfr by lia.
    rewrite !(u_small (bv_unsigned sp - 96)) in Hfr by lia.
    destruct (Z.eq_dec (bv_unsigned sp - 92) 0) as [Habs|Hne]; [exfalso; clear -Habs W1; lia|].
    specialize (Hcs Hne).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    know_frame HK Hfr [(SA (EVar 66) (-128)%Z, 32%Z); (SA (EVar 128) 0%Z, 32%Z); (SA (EVar 66) (-92)%Z, 4%Z)].
    { rewrite Hsp. unfold v_addi. rewrite HuC1.
      replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp - 96 - 32)%Z by lia.
      replace (bv_unsigned C + 32 * j + 0)%Z with (bv_unsigned C + 32 * j)%Z by lia.
      replace (bv_unsigned sp + -92)%Z with (bv_unsigned sp - 92)%Z by lia. reflexivity. }
    assert (HFR2 : frame_mod mem mq1 BIG).
    { eapply frame_mod_trans_same; [exact Mfr|]. eapply frame_mod_of_covered; [|exact Hfr]. unfold BIG. solve_covered. }
    (* [comment removed for export] *)
    assert (Hcurves1 : forall i, (0 <= i < j)%Z -> curve_ok SEGS mq1 data len (bv_unsigned C + 32 * i)).
    { intros i Hi. eapply curve_ok_frame; [exact Hfr | exact (Hcurves i Hi) | lia | lia | solve_apart]. }
    clear Hcurves Hpres.
    destruct Hr01 as [-> | ->].
    - (* [comment removed for export] *)
      add_krange (EVar 139) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      clear Hcs Hok1. fin_fail HR0 HF0 HFR2.
    - specialize (Hok1 eq_refl). rewrite HuC1 in Hok1.
      add_krange (EVar 139) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      destruct (Hcs eq_refl) as [v [Hv32 Hv]]. unfold cell in Hv. clear Hcs.
      env_extend [Z_to_bv 64 v].
      lazymatch type of HK with know_ok _ ?E1 _ ?kn1 =>
        assert (HK1 : know_ok SEGS E1 mq1 (KRange (EVar 193) 0 4294967295 :: KWord (SA (EVar 66) (-92)) 4 (EVar 193) :: kn1));
        [ constructor; [apply krange_intro; cbn [edenot]; ev_simpl E1; rewrite u_small by lia; lia|];
          constructor; [eapply (kword_intro SEGS E1 mq1 (EVar 66) sp (-92) 4 (EVar 193) (Z_to_bv 64 v)); cbn [edenot]; ev_simpl E1;
                          first [exact Hsp | reflexivity | lia
                                | replace (bv_unsigned sp + -92)%Z with (bv_unsigned sp - 92)%Z by lia; exact Hv] | exact HK]
        | clear HK; rename HK1 into HK ] end.
      (* [comment removed for export] *)
      run_fp 40%nat (@nil Z) noscr true. subst M0.
      branch_case as Hb1; [clear Hb1; fin_fail HR0 HF0 HFR2|].
      lazymatch type of HK with know_ok _ ?E1 _ _ => br_simpl_in E1 Hb1 end.
      assert (Hv3 : (v <= 4294967292)%Z) by (rewrite !Z.mod_small in Hb1 by lia; apply Z.ltb_lt in Hb1; lia). clear Hb1.
      add_krange (EVar 193) 0%Z 4294967292%Z by (rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 40%nat (@nil Z) noscr true. subst M0.
      branch_case as Hb2; [clear Hb2; fin_fail HR0 HF0 HFR2|].
      lazymatch type of HK with know_ok _ ?E1 _ _ => br_simpl_in E1 Hb2 end.
      rewrite u_srl32, newoff_val, (Z.mod_small 0), Z.eqb_eq in Hb2 by lia.
      pose proof (Z.div_small_iff (bv_unsigned (getr R 12) + 4 * ((v + 3) / 4)) 4294967296 ltac:(lia)) as Hdz.
      assert (Hq : (0 <= (v + 3) / 4)%Z) by (apply Z.div_pos; lia).
      assert (Hno : (bv_unsigned (getr R 12) + 4 * ((v + 3) / 4) < 4294967296)%Z) by (apply Hdz in Hb2; lia).
      clear Hdz Hb2.
      (* [comment removed for export] *)
      run_fp 40%nat (@nil Z) noscr true. subst M0.
      branch_case as Hb3; [clear Hb3; fin_exit HR0 HF0 HFR2 Hcurves1 Hok1 R11 (getr R 11) (getr regs 13) j|].
      lazymatch type of HK with know_ok _ ?E1 _ _ => br_simpl_in E1 Hb3 end.
      apply Z.ltb_ge in Hb3. rewrite H11, u_small in Hb3 by lia.
      match type of Hb3 with (bv_unsigned (sext 64 (alu32 ALU_ADD (low32 ?w) _)) <= size)%Z =>
        pose proof (sext32_ge w ltac:(rewrite newoff_val by lia; lia)) as Hge; rewrite newoff_val in Hge by lia end.
      assert (Hnew : (bv_unsigned (getr R 12) + 4 * ((v + 3) / 4) <= size)%Z) by lia. clear Hge Hb3.
      (* [comment removed for export] *)
      run_fp 40%nat [0x1697c%Z] noscr true. subst M0.
      branch_case as Hb4; [clear Hb4; fin_exit HR0 HF0 HFR2 Hcurves1 Hok1 R11 (getr R 11) (getr regs 13) j|].
      lazymatch type of HK with know_ok _ ?E1 _ _ => br_simpl_in E1 Hb4 end.
      rewrite R11, H13, !u_small in Hb4 by lia.
      run_fp 40%nat [0x1697c%Z] noscr true. subst M0.
      apply Z.ltb_lt in Hb4.
      apply (IH (j + 1)%Z); [lia|].
      lift_id HR0 HR. lift_id HF0 HF.
      split; [|split; [|split; [lia|]]].
      + unfold REGH.
        split; [regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia|].
        split; [regv HR (8%bv:reg); exact H14|].
        split; [regv HR (9%bv:reg); exact H11|].
        split; [regv HR (11%bv:reg); rewrite R11, alu_add_lit, u_small by lia; f_equal; lia|].
        split; [regv HR (12%bv:reg); rewrite newoff_val by lia; exact Hnew|].
        split; [regv HR (18%bv:reg); exact H10|].
        split; [regv HR (19%bv:reg); rewrite R19, alu_add_lit, Hu19; f_equal; lia|].
        split; [regv HR (20%bv:reg); rewrite H14; apply not_idiom|].
        split; [regv HR (21%bv:reg); reflexivity|].
        split; [regv HR (22%bv:reg); exact H13|].
        split; [regv HR (23%bv:reg); reflexivity|].
        lazymatch goal with HR' : regs_ok ?E1 ?sr ?R', HF' : fregs_ok _ ?sfr (@fp_regs ?I) |- _ =>
          lazymatch type of HR0 with id (regs_ok _ ?sr0 _) =>
            split; [exact (regs_same_on E1 sr0 sr regs R' [3; 4; 26; 27]%bv HR0 HR' ltac:(vm_compute; reflexivity))|] end;
          lazymatch type of HF0 with id (fregs_ok _ ?sfr0 _) =>
            exact (fregs_same_on E1 sfr0 sfr fp0 _ abi_fkept HF0 HF' ltac:(vm_compute; reflexivity)) end
        end.
      + unfold MEMH.
        Ltac mcell Hfr H := eapply cell64_frame; [exact Hfr | exact H | lia | lia | solve_apart].
        split; [mcell Hfr M1|]. split; [mcell Hfr M2|]. split; [mcell Hfr M3|]. split; [mcell Hfr M4|].
        split; [mcell Hfr M5|]. split; [mcell Hfr M6|]. split; [mcell Hfr M7|]. split; [mcell Hfr M8|].
        split; [mcell Hfr M9|]. split; [mcell Hfr M10|]. split; [mcell Hfr M11|].
        exact HFR2.
      + intros i Hi. destruct (Z_lt_le_dec i j); [apply Hcurves1; lia | replace i with j by lia; exact Hok1].
  Qed.

  (* [comment removed for export] *)
  Lemma sltiu1_val : forall x : word, exists r : Z,
    alu64 ALU_SLTU x (Z_to_bv 64 1) = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z /\ (r = 1%Z <-> bv_unsigned x = 0%Z).
  Proof using C sp.
    intros x. pose proof (u64_range x). rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite (u_small 1) by lia.
    destruct (bv_unsigned x <? 1)%Z eqn:Hlt.
    - exists 1%Z. split; [reflexivity|]. apply Z.ltb_lt in Hlt. lia.
    - exists 0%Z. split; [reflexivity|]. apply Z.ltb_ge in Hlt. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac fin_pro HR0 HF0 HFR :=
    run_fp 40%nat (@nil Z) noscr true; subst_triv; fin_ret;
    lazymatch goal with |- Q (@mkst _ _ _ ?Mq _) =>
      post_regs_rc HR0 HF0 Mq;
      split; [exact HFR|];
      lazymatch goal with HR : regs_ok _ _ _ |- _ =>
        let r := fresh "r" in let Hr := fresh "Hr" in let Hr01 := fresh "Hr01" in let Hriff := fresh "Hriff" in
        destruct (sltiu1_val (getr regs 13)) as (r & Hr & Hr01 & Hriff);
        exists r; split; [regv HR (10%bv:reg); exact Hr|]; split; [exact Hr01|];
        let Hi := fresh "Hi" in
        intros -> i Hi; exfalso; rewrite H13, u_small in Hriff by lia; lia
      end
    end.

  Lemma sltu0_pos : forall x : word, (0 < bv_unsigned x)%Z -> alu64 ALU_SLTU (Z_to_bv 64 0) x = Z_to_bv 64 1.
  Proof using C sp.
    intros x Hx. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite (u_small 0) by lia.
    replace (0 <? bv_unsigned x)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Theorem body : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x16914) mem rom) Q.
  Proof using H10 H11 H12 H13 H14 Hal16 Hcal Hcend Hd_dc Hd_ds Hd_sc Hdok Hin Hk Hra Hrc Hret Hro Hsize Hsp Hwc Hwst.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr. pose proof (u64_range data) as Hdr.
    pose proof (u64_range buf) as Hbufr. pose proof (u64_range offw) as Hoffr.
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof Hwst as (W1 & W2 & W3 & W4).
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals fp0 ++ [])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp0) by exact (fregs_ok_vars (junk_vals regs) fp0 _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    assert (HK : know_ok SEGS E mem [KAlign (EVar 2) 16; KRange (EVar 13) 0 4; KRange (EVar 11) 0 4294967295;
                                    KRange (EVar 2) 128 (2^64 - 1); KWr (SA (EVar 2) (-128)) 128]).
    { constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal16]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite H13, u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite H11, u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; lia|].
      constructor; [apply (kwr_intro SEGS E mem (EVar 2) sp (-128) 128);
                    [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                     replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp - 128)%Z by lia; exact W4]|].
      constructor. }
    run_fp 60%nat [0x1697c%Z] noscr true.
    lazymatch goal with EQM : ?M1 = mem_denot _ mem _ |- _ =>
      assert (HFRP : frame_mod mem M1 BIG)
        by (rewrite EQM; eapply frame_mod_of_covered;
              [| frame_of_log [(SA (EVar 2) (-96)%Z, 96%Z)] ltac:(rewrite Hsp)];
            unfold BIG, v_addi, covered; apply Forall_cons;
              [cbn [fst snd]; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia| apply Forall_nil])
    end.
    (* [comment removed for export] *)
    branch_case as Hc1; [clear Hc1; fin_pro HR0 HF0 HFRP|].
    br_simpl_in E Hc1. apply Z.ltb_ge in Hc1. rewrite H11, H12, u_small in Hc1 by lia.
    (* [comment removed for export] *)
    branch_case as Hc2; [fin_pro HR0 HF0 HFRP|].
    br_simpl_in E Hc2. rewrite H13, !u_small, ?Z.mod_small in Hc2 by lia.
    run_fp 60%nat [0x1697c%Z] noscr true.
    subst M0. apply Z.eqb_neq in Hc2.
    apply (iter (Z.to_nat k) 0); [lia|].
    lift_id HR0 HR. lift_id HF0 HF.
    split; [|split; [|split; [lia| intros i Hi; exfalso; lia]]].
    + unfold REGH.
      split; [regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia|].
      split; [regv HR (8%bv:reg); exact H14|].
      split; [regv HR (9%bv:reg); exact H11|].
      split; [regv HR (11%bv:reg); reflexivity|].
      split; [regv HR (12%bv:reg); rewrite H12; exact Hc1|].
      split; [regv HR (18%bv:reg); exact H10|].
      split; [regv HR (19%bv:reg); reflexivity|].
      split; [regv HR (20%bv:reg); rewrite H14; apply not_idiom|].
      split; [regv HR (21%bv:reg); rewrite H10; apply sltu0_pos; lia|].
      split; [regv HR (22%bv:reg); exact H13|].
      split; [regv HR (23%bv:reg); reflexivity|].
      lazymatch goal with HR' : regs_ok ?E1 ?sr ?R', HF' : fregs_ok _ ?sfr (@fp_regs ?I) |- _ =>
        lazymatch type of HR0 with id (regs_ok _ ?sr0 _) =>
          split; [exact (regs_same_on E1 sr0 sr regs R' [3; 4; 26; 27]%bv HR0 HR' ltac:(vm_compute; reflexivity))|] end;
        lazymatch type of HF0 with id (fregs_ok _ ?sfr0 _) =>
          exact (fregs_same_on E1 sfr0 sfr fp0 _ abi_fkept HF0 HF' ltac:(vm_compute; reflexivity)) end
      end.
    + unfold MEMH, cell64, cell.
      kcell_auto HK (EVar 2) (-8)%Z 8%nat M1. kcell_auto HK (EVar 2) (-16)%Z 8%nat M2.
      kcell_auto HK (EVar 2) (-24)%Z 8%nat M3. kcell_auto HK (EVar 2) (-32)%Z 8%nat M4.
      kcell_auto HK (EVar 2) (-40)%Z 8%nat M5. kcell_auto HK (EVar 2) (-48)%Z 8%nat M6.
      kcell_auto HK (EVar 2) (-56)%Z 8%nat M7. kcell_auto HK (EVar 2) (-64)%Z 8%nat M8.
      kcell_auto HK (EVar 2) (-72)%Z 8%nat M9. kcell_auto HK (EVar 2) (-80)%Z 8%nat M10.
      kcell_auto HK (EVar 2) (-88)%Z 8%nat M11.
      Ltac mc H := lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                     lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by lia; rewrite_getr; exact H end end.
      split; [mc M1|]. split; [mc M2|]. split; [mc M3|]. split; [mc M4|].
      split; [mc M5|]. split; [mc M6|]. split; [mc M7|]. split; [mc M8|].
      split; [mc M9|]. split; [mc M10|]. split; [mc M11|].
      exact HFRP.
  Qed.

End Proof.

Theorem read_curves_Ub_ok : read_curve_contract SEGS wp1_infoub -> read_curves_contract SEGS wp2_infoub.
Proof.
  intros Hrc data len bs sp buf C size offw k FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & H10 & H11 & H12 & H13 & H14 & Hdok & Hsize & Hin & Hk & Hwc & Hcal & Hcend & Hal16 & Hwst & Hro & Hd_sc & Hd_dc & Hd_ds).
  cbn [w_rcurves_d w_ro_lo w_ro_hi wp2_infoub] in *.
  destruct (body Hrc FPI regs mem rom ret sp buf C offw data size k len bs Hra Hret Hsp H10 H11 H12 H13 H14 Hdok Hsize Hin Hk
              Hwc Hcal Hcend Hal16 Hwst Hro Hd_sc Hd_dc Hd_ds)
    as (st1 & Hms & (FPI1 & regs1 & mem1 & Hst & Hk1 & Hk2 & Hfr & Hr)).
  subst st1.
  exists FPI1, regs1, mem1. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  split; [| exact Hr].
  unfold BIG in Hfr. rewrite Z_to_bv_bv_unsigned. exact Hfr.
Qed.
