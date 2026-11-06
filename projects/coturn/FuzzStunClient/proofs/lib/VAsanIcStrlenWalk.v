(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanMemcpyBase AsanMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanTls_code VAsanIcStrlen_code VAsanMemsetWalk VAsanTlsWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMuslStrlen.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_63f74 : v_addi (0x442f4 : word) 4 = Z_to_bv 64 0x442f8. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_63f7c : v_addi (0x442fc : word) 4 = Z_to_bv 64 0x44300. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_63f90 : v_addi (0x44310 : word) 4 = (0x44314 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_64114 : v_addi (0x44494 : word) 4 = (0x44498 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_63f94 : ret_ok (0x44314 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_64118 : ret_ok (0x44498 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma jalr_strlen : v_jalr (Z_to_bv 64 0xa47fc) 0 = (0xa47fc : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_63f74 : v_jalr (Z_to_bv 64 0x442f8) 0 = (0x442f8 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_63f7c : v_jalr (Z_to_bv 64 0x44300) 0 = (0x44300 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Definition ISL_FRAME : Z := 2216.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition isl_cells (m : word -> option byte) : Prop :=
  cells m
  /\ rdn SEGS m (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xacb88 0xa47fc                                     (* [comment removed for export] *)
  /\ cell m 0xaae70 0x145128                                     (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0x145223) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ AsanMemchr.rodata_clear m.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Record islH (mem : word -> option byte) (s usp : Z) (buf : list byte) (K : Z) : Prop := {
  is_buf  : rdn SEGS mem (Z_to_bv 64 s) (length buf) = Some buf;
  is_span : (VAsanMuslStrlen.strlen_span s K <= Z.of_nat (length buf))%Z;
  is_nw   : (s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  is_s    : (0 <= s)%Z;
  is_K    : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z;
  is_zero_K : bv_unsigned (VAsanMuslStrlen.b_ buf K) = 0%Z;
  is_rng  : (s + K + 1 <= kLowEnd)%Z \/ (kHighBeg <= s /\ s + K + 1 <= kHighEnd)%Z;
  is_sp   : (SB + ISL_FRAME + 8 <= usp < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  is_sap  : (usp <= s \/ s + Z.of_nat (length buf) <= usp - ISL_FRAME)%Z;
  is_shd  : (SB + (s + K) / 8 + 8 < usp - ISL_FRAME)%Z;
  (* [comment removed for export] *)
  is_zg   : forall g, (s / 8 <= g < (s + K) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  is_last : exists b1 : byte, mem (Z_to_bv 64 (SB + (s + K) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((s + K) mod 8 < bv_unsigned b1 < 8)%Z);
  (* [comment removed for export] *)
  is_words : forall a, ((SB + s / 8) / 8 * 8 <= a)%Z -> (a <= (SB + (s + K) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
               exists w : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w);
  is_stk  : forall a, (usp - ISL_FRAME <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  is_cel  : isl_cells mem
}.

(* [comment removed for export] *)
Definition isl_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.
(* [comment removed for export] *)
Definition ekeep (r : reg) : bool :=
  (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21 || bv_eqb r 22)%bool.

Section ISL.
  Variables (mem rom : word -> option byte) (s usp : Z) (buf : list byte) (K : Z).
  Hypothesis H : islH mem s usp buf K.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 s.

  Let Hs := is_s _ _ _ _ _ H.
  Let HK := is_K _ _ _ _ _ H.
  #[using="mem s buf K H"] Lemma Hsp : (0x7fff8000 + 2224 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (is_sp _ _ _ _ _ H). unfold ISL_FRAME, SB in *. lia. Qed.
  #[using="mem usp buf K H Hs"] Lemma Hs64 : (0 <= s < 2 ^ 64)%Z.
  Proof. pose proof (is_nw _ _ _ _ _ H). pose proof (is_s _ _ _ _ _ H). lia. Qed.
  #[using="mem usp buf H HK"] Lemma HK64 : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z /\ (s + K + 1 < 2 ^ 47)%Z.
  Proof. pose proof (is_K _ _ _ _ _ H). pose proof (is_rng _ _ _ _ _ H). unfold kLowEnd, kHighBeg, kHighEnd in *. lia. Qed.

  (* [comment removed for export] *)
  Definition p8 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 64%Z (getr regs0 22) (w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
      (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem))))))).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.
  (* [comment removed for export] *)
  Ltac adr c := match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with c by lia end.

  (* [comment removed for export] *)
  Definition sfr (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - ISL_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x)
    /\ (forall x : word, (usp - 64 <= bv_unsigned x < usp)%Z -> m x = p8 x)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true)
    /\ (forall x, mem x <> None -> m x <> None).

  #[using="s buf K H"] Lemma p8_out : forall x : word, (bv_unsigned x < usp - 64 \/ usp <= bv_unsigned x)%Z -> p8 x = mem x.
  Proof.
    intros x [Hx|Hx]; unfold p8; pose proof Hsp.
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  #[using="s buf K H"] Lemma sfr_p8 : sfr p8.
  Proof.
    split; [|split; [intros; reflexivity|split]].
    - intros x Hx. apply p8_out. unfold ISL_FRAME in Hx. lia.
    - intros x Hx. unfold p8. repeat apply store_ok1_wbytes. exact Hx.
    - intros x Hx. unfold p8. repeat apply wbytes_keep. exact Hx.
  Qed.
  (* [comment removed for export] *)
  #[using="s buf K H"] Lemma sfr_w8 : forall m (a : Z) (v : word), sfr m -> (usp - ISL_FRAME <= a)%Z -> (a + 8 <= usp - 64)%Z ->
    sfr (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    intros m a v (F1 & F2 & F3 & F4) Ha Hb. pose proof Hsp. unfold ISL_FRAME in *. split; [|split; [|split]].
    - intros x Hx. rewrite <- (F1 x Hx). unfold ISL_FRAME in Hx. destruct Hx as [Hx|Hx].
      + apply wbytes_below; len8; rewrite ?zbv_u by lia; lia.
      + apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. rewrite <- (F2 x Hx). apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. apply store_ok1_wbytes. apply F3. exact Hx.
    - intros x Hx. apply wbytes_keep. apply F4. exact Hx.
  Qed.
  #[using="s buf K H"] Lemma sfr_rp : forall m (rra s0 s1 s2 s3 s4 s5 : word), sfr m -> sfr (rp_frame m (usp - 2144) rra s0 s1 s2 s3 s4 s5).
  Proof. intros. unfold rp_frame. repeat (apply sfr_w8; [|unfold ISL_FRAME; lia|lia]). assumption. Qed.

  #[using="Type"] Lemma sfr_below : forall m (x : word), sfr m -> (bv_unsigned x < usp - ISL_FRAME)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. exact (F1 x (or_introl Hx)). Qed.
  #[using="s buf K H"] Lemma rdn_sfr_below : forall m (a : Z) k, sfr m -> (0 <= a)%Z -> (a + Z.of_nat k <= usp - ISL_FRAME)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k F Ha Hk. pose proof Hsp. unfold ISL_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply (sfr_below m x F). unfold ISL_FRAME. lia.
  Qed.
  #[using="s buf K H"] Lemma rdn_sfr_out : forall m (a : Z) k, sfr m -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= usp - ISL_FRAME \/ usp <= a)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k (F1 & _) Ha Hk Hap. pose proof Hsp. unfold ISL_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply F1. lia.
  Qed.
  #[using="s buf K H"] Lemma cells_sfr : forall m, sfr m -> isl_cells m.
  Proof.
    intros m F. pose proof (is_cel _ _ _ _ _ H) as (C & C1 & C2 & C3 & C4 & C5). pose proof Hsp. pose proof SB_val. unfold ISL_FRAME in *.
    unfold isl_cells, cells, cell in *. rewrite !(rdn_sfr_below m) by (first [exact F | cbn; unfold ISL_FRAME; lia]).
    split; [exact C|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    intros i Hi. rewrite (sfr_below m); [exact (C5 i Hi)|exact F|rewrite zbv_u by lia; unfold ISL_FRAME; lia].
  Qed.
  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp; unfold p8;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
  #[using="s buf K H"] Lemma rd_ra : rdn SEGS p8 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).              Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s0 : rdn SEGS p8 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)).  Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s1 : rdn SEGS p8 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)).  Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s2 : rdn SEGS p8 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s3 : rdn SEGS p8 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s4 : rdn SEGS p8 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s5 : rdn SEGS p8 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_s6 : rdn SEGS p8 (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 (getr regs0 22)). Proof. rd_slot. Qed.
  #[using="s buf K H"] Lemma rd_sfr_slot : forall m (a : Z) v, sfr m -> (usp - 64 <= a)%Z -> (a + 8 <= usp)%Z ->
    rdn SEGS p8 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).
  Proof.
    intros m a v (_ & F2 & _) Ha Hb R. pose proof Hsp. rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx. apply F2. lia.
  Qed.

  #[using="s buf K H"] Lemma stk8 : forall m a, sfr m -> (usp - ISL_FRAME <= a)%Z -> (a + 8 <= usp)%Z -> store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a (_ & _ & F3 & _) H1 H2. unfold ISL_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F3. apply (is_stk _ _ _ _ _ H). unfold ISL_FRAME. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p9 : word -> option byte :=
    wbytes (wbytes p8 (Z_to_bv 64 (usp - 2152)) (word_to_le_bytes 8 (Z_to_bv 64 0x44300)))
           (Z_to_bv 64 (usp - 2160)) (word_to_le_bytes 8 (Z_to_bv 64 usp)).
  #[using="s buf K H"] Lemma sfr_p9 : sfr p9.
  Proof. unfold p9. apply sfr_w8; [apply sfr_w8; [exact sfr_p8|unfold ISL_FRAME; lia|lia]|unfold ISL_FRAME; lia|lia]. Qed.

  Ltac msd F D a v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                 | apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold p9, p8; repeat apply store_ok1_wbytes;
                   apply (is_stk _ _ _ _ _ H); unfold ISL_FRAME; lia ]).


  (* [comment removed for export] *)
  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r : reg, isl_clob r = false -> ekeep r = false -> getr regs r = getr regs0 r.
  Ltac keep_tac Hr He := repeat (rewrite getr_other by (intros ->; cbn in Hr, He; first [discriminate Hr | discriminate He])).

  #[using="buf K H H01 H02 H010 Hs"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x442c4 : word) mem rom) (mkst regs (0x44300 : word) p9 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 2144) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 18 = Z_to_bv 64 s
      /\ getr regs 10 = Z_to_bv 64 1 /\ keep regs.
  Proof.
    pose proof Hsp. pose proof Hs64. pose proof (cells_sfr p8 sfr_p8) as (_ & AI & _).
    assert (AI9 : rdn SEGS p9 (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_sfr p9 sfr_p9))).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_442c4 eq_refl D_442c4)). rewrite H02. zn.
      msd F_442c8 D_442c8 (usp - 8)%Z ra H02.
      msd F_442cc D_442cc (usp - 16)%Z (getr regs0 8) H02.
      msd F_442d0 D_442d0 (usp - 24)%Z (getr regs0 9) H02.
      msd F_442d4 D_442d4 (usp - 32)%Z (getr regs0 18) H02.
      msd F_442d8 D_442d8 (usp - 40)%Z (getr regs0 19) H02.
      msd F_442dc D_442dc (usp - 48)%Z (getr regs0 20) H02.
      msd F_442e0 D_442e0 (usp - 56)%Z (getr regs0 21) H02.
      msd F_442e4 D_442e4 (usp - 64)%Z (getr regs0 22) H02.
      change (wbytes _ _ _) with p8.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_442e8 eq_refl D_442e8)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_442ec eq_refl D_442ec)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_442f0 eq_refl D_442f0)). gr. rewrite H010. zn. rewrite ?Z.add_0_r.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_442f4 eq_refl D_442f4)). rewrite lit_63f74.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3f30) F_5af30 eq_refl D_5af30);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5af34 eq_refl D_5af34);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI).
      rewrite v_lb_1.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5af38 eq_refl D_5af38)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5af3c eq_refl D_5af3c)). gr. zn.
      mstep ltac:(exact (step_sltiu _ _ _ _ _ _ _ _ _ F_5af40 eq_refl D_5af40)). gr.
      replace (v_sltiu (Z_to_bv 64 (1 + -1)) 1) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x442f8) F_5af44 eq_refl D_5af44); gr; reflexivity |].
      imm_norm. rewrite ret_63f74.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_442f8 eq_refl D_442f8); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_442fc eq_refl D_442fc)). rewrite lit_63f7c.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be40 eq_refl D_5be40)). gr. zn.
      msd F_5be44 D_5be44 (usp - 2152)%Z (Z_to_bv 64 0x44300) H02.
      msd F_5be48 D_5be48 (usp - 2160)%Z (Z_to_bv 64 usp) H02.
      change (wbytes _ _ _) with p9.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3e4c) F_5be4c eq_refl D_5be4c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be50 eq_refl D_5be50)). gr. zn.
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5be54 eq_refl D_5be54);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI9).
      rewrite v_lb_1.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be58 eq_refl D_5be58)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5be5c eq_refl D_5be5c)).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5be60 eq_refl D_5be60); gr; br_eq).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0x44300) F_5be64 eq_refl D_5be64);
                   [ gr; imm_norm; zn; adr (usp - 2152)%Z;
                     unfold p9; rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia| len8; rewrite !zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia]
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 usp) F_5be68 eq_refl D_5be68);
                   [ gr; imm_norm; zn; adr (usp - 2160)%Z;
                     unfold p9; apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be6c eq_refl D_5be6c)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x44300) F_5be70 eq_refl D_5be70); gr; reflexivity |].
      imm_norm. rewrite ret_63f7c. replace (usp - 2144 + -16 + 16)%Z with (usp - 2144)%Z by lia.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr He. keep_tac Hr He. reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma strlen_clob_isl : forall r : reg, isl_clob r = false -> ~ In r VAsanMuslStrlen.strlen_clob.
  Proof.
    intros r Hr Hin. unfold VAsanMuslStrlen.strlen_clob in Hin. cbn in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; discriminate Hr|]). exact Hin.
  Qed.

  #[using="H Hs HK"] Lemma slH_p9 : VAsanMuslStrlen.slH p9 (Z_to_bv 64 s) buf K.
  Proof.
    pose proof Hsp. pose proof Hs64. pose proof (is_nw _ _ _ _ _ H). pose proof (is_sap _ _ _ _ _ H) as AP.
    pose proof (cells_sfr p9 sfr_p9) as (_ & _ & _ & _ & _ & RO).
    constructor; rewrite ?zbv_u by lia.
    - rewrite (rdn_sfr_out p9); [exact (is_buf _ _ _ _ _ H) | exact sfr_p9 | lia | lia | unfold ISL_FRAME in *; lia].
    - exact (is_span _ _ _ _ _ H).
    - lia.
    - exact (proj1 HK).
    - exact (is_zero_K _ _ _ _ _ H).
    - exact RO.
  Qed.

  #[using="H Hs HK"] Lemma blk_S : forall regs,
    keep regs -> getr regs 18 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 1 ->
    getr regs 2 = Z_to_bv 64 (usp - 2144) -> getr regs 8 = Z_to_bv 64 usp ->
    exists regs' (i : Z),
      msteps SEGS (mkst regs (0x44300 : word) p9 rom) (mkst regs' (0x44314 : word) p9 rom)
      /\ (0 <= i <= K)%Z /\ bv_unsigned (VAsanMuslStrlen.b_ buf i) = 0%Z
      /\ (forall j, (0 <= j < i)%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf j) <> 0%Z)
      /\ getr regs' 10 = Z_to_bv 64 i /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 s
      /\ getr regs' 2 = Z_to_bv 64 (usp - 2144) /\ getr regs' 8 = Z_to_bv 64 usp /\ keep regs'.
  Proof.
    intros regs HKp H18 H10 H2 H8. pose proof Hsp. pose proof Hs64.
    pose proof (cells_sfr p9 sfr_p9) as (_ & _ & RL & _).
    evar (rr : bvmap 5 word).
    edestruct (VAsanMuslStrlen.ref_strlen p9 (Z_to_bv 64 s) buf K rom slH_p9 rr (0x44314 : word) ret_ok_63f94)
      as (r1 & i & M1 & K1 & Hi & Zi & NZi & R10); cycle -1.
    { exists r1, i. split; [|split; [exact Hi|split; [exact Zi|split; [exact NZi|split; [exact R10|]]]]].
      - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xad300) F_44300 eq_refl D_44300);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_44304 D_44304 0xa47fc%Z RL H18.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44308 eq_refl D_44308)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4430c eq_refl D_4430c)). gr. rewrite H18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa47fc) F_44310 eq_refl D_44310);
                     [reflexivity | gr; reflexivity]).
        rewrite ?lit_63f90.
        match goal with |- msteps _ (mkst ?r ?pc ?mm ?ro) _ =>
          replace pc with (0xa47fc : word) by (apply bv_eq; vm_compute; reflexivity) end.
        subst rr. exact M1.
      - assert (K9 : getr r1 9 = getr rr 9).
        { apply K1. intros X. cbn in X. repeat (destruct X as [X|X]; [discriminate X|]). exact X. }
        assert (K18 : getr r1 18 = getr rr 18).
        { apply K1. intros X. cbn in X. repeat (destruct X as [X|X]; [discriminate X|]). exact X. }
        assert (K2 : getr r1 2 = getr rr 2).
        { apply K1. intros X. cbn in X. repeat (destruct X as [X|X]; [discriminate X|]). exact X. }
        assert (K8 : getr r1 8 = getr rr 8).
        { apply K1. intros X. cbn in X. repeat (destruct X as [X|X]; [discriminate X|]). exact X. }
        rewrite K9, K18, K2, K8. subst rr. gr. split; [reflexivity|]. split; [exact H18|]. split; [exact H2|]. split; [exact H8|].
        intros r Hr He. rewrite (K1 r (strlen_clob_isl r Hr)). keep_tac Hr He. apply HKp; assumption. }
    all: subst rr; gr; try reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="buf H Hs HK"] Lemma blk_T : forall regs (i : Z), (0 <= i <= K)%Z -> keep regs ->
    getr regs 9 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 i -> getr regs 18 = Z_to_bv 64 s -> getr regs 8 = Z_to_bv 64 usp ->
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    exists regs',
      msteps SEGS (mkst regs (0x44314 : word) p9 rom) (mkst regs' (0x44340 : word) p9 rom)
      /\ getr regs' 9 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 64 /\ getr regs' 10 = Z_to_bv 64 i
      /\ getr regs' 18 = Z_to_bv 64 s /\ getr regs' 2 = Z_to_bv 64 (usp - 2144) /\ getr regs' 8 = Z_to_bv 64 usp
      /\ keep regs'.
  Proof.
    intros regs i Hi HKp H9 H10 H18 H8 H2. pose proof Hsp. pose proof Hs64. pose proof HK64 as (HK0 & HK1 & HK2).
    pose proof (cells_sfr p9 sfr_p9) as (_ & _ & _ & G1 & IS & _).
    eexists. split.
    - mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44314 eq_refl D_44314); gr; rewrite ?H9, ?getr_zero; br_eq).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab318) F_44318 eq_refl D_44318);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_4431c D_4431c 0x145128%Z G1 H8.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_44320 eq_refl D_44320);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; first [exact IS | adr 0x145223%Z; exact IS]).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44324 eq_refl D_44324); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44328 eq_refl D_44328)). gr. rewrite H10. zn.
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_4432c eq_refl D_4432c)). gr. rewrite H18. rewrite v_not_zbv by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44330 eq_refl D_44330)). gr. rewrite H8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44334 eq_refl D_44334)). gr. zn.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_44338 eq_refl D_44338); gr; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4433c eq_refl D_4433c)). rewrite getr_zero. zn.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try assumption.
      intros r Hr He. keep_tac Hr He. apply HKp; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp buf H Hs HK"] Lemma last_i : forall i, (0 <= i <= K)%Z ->
    exists b1 : byte, mem (Z_to_bv 64 (SB + (s + i) / 8)) = Some b1
                      /\ (bv_unsigned b1 = 0%Z \/ ((s + i) mod 8 < bv_unsigned b1 < 8)%Z).
  Proof.
    intros i Hi. pose proof Hs64.
    pose proof (Z.div_le_mono (s + i) (s + K) 8 ltac:(lia) ltac:(lia)) as LE.
    destruct (Z.lt_ge_cases ((s + i) / 8) ((s + K) / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      apply (is_zg _ _ _ _ _ H). split; [apply Z.div_le_mono; lia|exact LT].
    - assert (E : ((s + i) / 8 = (s + K) / 8)%Z) by lia.
      destruct (is_last _ _ _ _ _ H) as (b1 & M & B). exists b1. rewrite E. split; [exact M|].
      destruct B as [B|B]; [left; exact B|right].
      pose proof (Z.div_mod (s + i) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + i) 8 ltac:(lia)).
      pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). lia.
  Qed.
  #[using="usp buf H Hs"] Lemma zero_i : forall i g, (0 <= i <= K)%Z -> (s / 8 <= g < (s + i) / 8)%Z ->
    mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
  Proof.
    intros i g Hi Hg. pose proof Hs64. pose proof (Z.div_le_mono (s + i) (s + K) 8 ltac:(lia) ltac:(lia)).
    apply (is_zg _ _ _ _ _ H). lia.
  Qed.
  #[using="mem buf H Hs HK"] Lemma qfacts : forall i, (0 <= i <= K)%Z ->
    (8 * (s / 8) <= s < 8 * (s / 8) + 8)%Z /\ (8 * ((s + i) / 8) <= s + i < 8 * ((s + i) / 8) + 8)%Z
    /\ ((s + i) mod 8 = s + i - 8 * ((s + i) / 8))%Z
    /\ (SB + (s + i) / 8 + 8 < usp - 2216)%Z /\ (s / 8 <= (s + i) / 8 <= (s + K) / 8)%Z /\ SB = 0x7fff8000%Z
    /\ (s + K + 1 < 2 ^ 47)%Z.
  Proof.
    intros i Hi. pose proof (is_shd _ _ _ _ _ H) as Hshd. unfold ISL_FRAME in Hshd. pose proof SB_val. pose proof Hs64.
    pose proof HK64 as (HK0 & HK1 & HK2).
    pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
    pose proof (Z.div_mod (s + i) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + i) 8 ltac:(lia)).
    pose proof (Z.div_le_mono s (s + i) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (s + i) (s + K) 8 ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="buf H Hs HK"] Lemma blk_Q1 : forall regs m (i : Z), sfr m -> (0 <= i <= K)%Z -> (i <= 63)%Z -> keep regs ->
    getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 64 -> getr regs 18 = Z_to_bv 64 s ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x44340 : word) m rom) (mkst regs' (0x44378 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (SB + s / 8) /\ getr regs' 12 = Z_to_bv 64 (SB + (s + i) / 8)
      /\ getr regs' 13 = Z_to_bv 64 (s + i) /\ getr regs' 14 = w /\ getr regs' 10 = Z_to_bv 64 i
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m i F Hi Hi63 HKp H10 H11 H18. pose proof Hsp as HU. pose proof Hs64.
    destruct (qfacts i Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
    pose proof (Z.div_mod (SB + s / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + s / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + (s + i) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (s + i) / 8) 8 ltac:(lia)).
    pose proof (Z.div_le_mono (SB + s / 8) (SB + (s + i) / 8) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (SB + (s + i) / 8) (SB + (s + K) / 8) 8 ltac:(lia) ltac:(lia)).
    destruct (is_words _ _ _ _ _ H ((SB + s / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @H1; @H3; @H4; @H5; @H6]); lia)) ltac:((ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @H1; @H3; @H4; @H5; @H6]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w1 W1].
    destruct (is_words _ _ _ _ _ H ((SB + (s + i) / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:((ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w2 W2].
    assert (W1c : cell m ((SB + s / 8) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISL_FRAME; (ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @H1; @H2; @Dshd]); lia)]). exact W1. }
    assert (W2c : cell m ((SB + (s + i) / 8) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISL_FRAME; (ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @H3; @H4; @Dshd]); lia)]). exact W2. }
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_44340 eq_refl D_44340); gr; rewrite ?H10, ?H11; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab344) F_44344 eq_refl D_44344);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_44348 D_44348 0xb35f8%Z C1 H18.
      mld F_4434c D_4434c SB C2 H18.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_44350 eq_refl D_44350)). gr. rewrite H10, H18, v_add_zbv by lia.
      replace (i + s)%Z with (s + i)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_44354 eq_refl D_44354)). gr. rewrite H18, (v_srli_3 s) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_44358 eq_refl D_44358)). gr. rewrite (v_srli_3 (s + i)) by (ltac2:(LK.k [@Hs; @Hi; @H0; @D0; @D1; @D01; @HSB; @HsK]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_4435c eq_refl D_4435c)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hs; @HSB; @HK; @Hi; @D0; @HsK]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_44360 eq_refl D_44360)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hs; @HSB; @Hi; @H0; @D0; @D1; @DM; @D01; @HsK]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44364 eq_refl D_44364)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hs; @HK; @Hi; @H0; @D0; @D1; @D01; @HSB; @HsK]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44368 eq_refl D_44368)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hs; @Hi; @H0; @D1; @DM; @D01; @HSB; @HsK]); lia).
      mld F_4436c D_4436c (bv_unsigned w1) W1c H18.
      mld F_44370 D_44370 (bv_unsigned w2) W2c H18.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_44374 eq_refl D_44374)). gr.
      apply mst_refl.
    - gr. repeat split; try reflexivity; try assumption.
      intros r Hr He. keep_tac Hr He. apply HKp; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="buf H Hs HK"] Lemma blk_Q2a : forall regs m (i : Z), sfr m -> (0 <= i <= K)%Z -> keep regs ->
    getr regs 12 = Z_to_bv 64 (SB + (s + i) / 8) -> getr regs 13 = Z_to_bv 64 (s + i) -> getr regs 10 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x44454 : word) m rom) (mkst regs' (0x44470 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 i
      /\ getr regs' 11 = getr regs 11 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m i F Hi HKp H12 H13 H10. pose proof Hsp as HU. pose proof Hs64.
    destruct (qfacts i Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK).
    destruct (last_i i Hi) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (s + i) / 8)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISL_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
      + mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44454 eq_refl D_44454)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_44458 eq_refl D_44458);
                     gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_4445c eq_refl D_4445c)). gr. rewrite H13, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44460 eq_refl D_44460)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_44464 eq_refl D_44464)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44468 eq_refl D_44468)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_4446c eq_refl D_4446c)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + gr. apply (f_equal (Z_to_bv 64)). lia.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
    - eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
      + mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44454 eq_refl D_44454)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_44458 eq_refl D_44458);
                     gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_4445c eq_refl D_4445c)). gr. rewrite H13, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44460 eq_refl D_44460)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_44464 eq_refl D_44464)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44468 eq_refl D_44468)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_4446c eq_refl D_4446c)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + gr. apply (f_equal (Z_to_bv 64)). lia.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="buf H Hs HK"] Lemma q_loop : forall (n : nat) regs m (i g : Z), sfr m -> (0 <= i <= K)%Z -> keep regs ->
    getr regs 11 = Z_to_bv 64 (SB + g) -> getr regs 12 = Z_to_bv 64 (SB + (s + i) / 8) -> getr regs 10 = Z_to_bv 64 0 ->
    (s / 8 <= g < (s + i) / 8)%Z -> Z.of_nat n = ((s + i) / 8 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x44474 : word) m rom) (mkst regs' (0x44484 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 21 = getr regs 21
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    pose proof Hsp as HU. pose proof Hs64.
    induction n as [|n IH]; intros regs m i g F Hi HKp H11 H12 H10 Hg Hn; [lia|].
    destruct (qfacts i Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK).
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISL_FRAME; lia]).
      apply (zero_i i); lia. }
    destruct (Z.eq_dec (g + 1) ((s + i) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_44474 eq_refl D_44474);
                     gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44478 eq_refl D_44478)). gr. rewrite H11. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_4447c eq_refl D_4447c)). gr. rewrite H10, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_44480 eq_refl D_44480); gr; rewrite ?H12; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m i (g + 1)%Z F Hi) as (r2 & M2 & R10 & R21 & R2 & R8 & R9 & R18 & K2); cycle -1.
      { exists r2. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_44474 eq_refl D_44474);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44478 eq_refl D_44478)). gr. rewrite H11. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_4447c eq_refl D_4447c)). gr. rewrite H10, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44480 eq_refl D_44480); gr; rewrite ?H12; br_eq).
          subst rr. exact M2.
        + exact R10.
        + rewrite R21. subst rr. gr. reflexivity.
        + rewrite R2. subst rr. gr. reflexivity.
        + rewrite R8. subst rr. gr. reflexivity.
        + rewrite R9. subst rr. gr. reflexivity.
        + rewrite R18. subst rr. gr. reflexivity.
        + exact K2. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      { intros r Hr He. keep_tac Hr He. apply HKp; assumption. }
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="buf H Hs HK"] Lemma blk_Q2b : forall regs m (i : Z), sfr m -> (0 <= i <= K)%Z -> keep regs ->
    getr regs 11 = Z_to_bv 64 (SB + s / 8) -> getr regs 12 = Z_to_bv 64 (SB + (s + i) / 8) -> getr regs 10 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x44470 : word) m rom) (mkst regs' (0x4437c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 i
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m i F Hi HKp H11 H12 H10 H21. pose proof Hsp as HU. pose proof Hs64.
    destruct (qfacts i Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec (s / 8) ((s + i) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_44470 eq_refl D_44470); gr; rewrite ?H11, ?H12; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44484 eq_refl D_44484)). gr. rewrite H10, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44488 eq_refl D_44488); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44550 eq_refl D_44550)). gr. rewrite H21. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44554 eq_refl D_44554)).
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
    - evar (rr : bvmap 5 word).
      edestruct (q_loop (Z.to_nat ((s + i) / 8 - s / 8)) rr m i (s / 8) F Hi) as (r2 & M2 & R10 & R21 & R2 & R8 & R9 & R18 & K2); cycle -1.
      { eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_44470 eq_refl D_44470); gr; rewrite ?H11, ?H12; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44484 eq_refl D_44484)). rewrite R10, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44488 eq_refl D_44488); gr; rewrite ?getr_zero; br_eq).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44550 eq_refl D_44550)). gr. rewrite R21. subst rr. gr. rewrite H21. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44554 eq_refl D_44554)).
          apply mst_refl.
        + gr. reflexivity.
        + gr. rewrite R2. subst rr. reflexivity.
        + gr. rewrite R8. subst rr. reflexivity.
        + gr. rewrite R9. subst rr. reflexivity.
        + gr. rewrite R18. subst rr. reflexivity.
        + intros r Hr He. keep_tac Hr He. apply K2; assumption. }
      all: subst rr; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="buf H Hs HK"] Lemma rp_pre : forall m (i : Z) b1, sfr m -> (64 <= i <= K)%Z ->
    mem (Z_to_bv 64 (SB + (s + i) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((s + i) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH m s (i + 1) (usp - 2144) b1.
  Proof.
    intros m i b1 F Hi L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof Hs64. pose proof HK64 as (HK0 & HK1 & HK2).
    destruct (qfacts i ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK).
    pose proof F as (F1 & F2 & F3 & F4).
    replace (s + (i + 1) - 1)%Z with (s + i)%Z by lia.
    constructor; rewrite ?Z.add_assoc; replace (s + i + 1 - 1)%Z with (s + i)%Z by lia.
    - lia.
    - lia.
    - pose proof (is_rng _ _ _ _ _ H). lia.
    - lia.
    - lia.
    - intros g Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISL_FRAME; lia]). apply (zero_i i); lia.
    - rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISL_FRAME; lia]). exact L1.
    - exact Hb1.
    - intros a Ha. apply F3. apply (is_stk _ _ _ _ _ H). unfold ISL_FRAME. lia.
    - exact (proj1 (cells_sfr m F)).
  Qed.

  #[using="Type"] Lemma rp_clob_isl : forall r : reg, isl_clob r = false -> rp_clob r = false.
  Proof.
    intros r Hr. unfold isl_clob in Hr. unfold rp_clob.
    repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
    repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
  Qed.

  #[using="buf H Hs HK"] Lemma blk_L : forall regs m (i : Z), sfr m -> (0 <= i <= K)%Z -> (64 <= i)%Z -> keep regs ->
    getr regs 9 = Z_to_bv 64 (i + 1) -> getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 64 ->
    getr regs 18 = Z_to_bv 64 s -> getr regs 2 = Z_to_bv 64 (usp - 2144) -> getr regs 8 = Z_to_bv 64 usp ->
    exists regs' m',
      msteps SEGS (mkst regs (0x44340 : word) m rom) (mkst regs' (0x4437c : word) m' rom)
      /\ sfr m'
      /\ getr regs' 10 = Z_to_bv 64 i /\ getr regs' 2 = Z_to_bv 64 (usp - 2144)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m i F Hi Hi64 HKp H9 H10 H11 H18 H2 H8. pose proof Hsp. pose proof Hs64. pose proof HK64 as (HK0 & HK1 & HK2).
    destruct (last_i i Hi) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom s (i + 1) (usp - 2144) b1 (rp_pre m i b1 F ltac:(lia) L1 Hb1) rr (0x44498 : word) ret_ok_64118)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_44340 eq_refl D_44340); gr; rewrite ?H10, ?H11; br_lt).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44444 eq_refl D_44444)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44448 eq_refl D_44448); gr; rewrite ?H9, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4448c eq_refl D_4448c)). gr. rewrite H18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44490 eq_refl D_44490)). gr. rewrite H9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_44494 eq_refl D_44494)). rewrite lit_64114.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44498 eq_refl D_44498); gr; rewrite ?R10, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44550 eq_refl D_44550)). gr.
        rewrite (K1 21) by reflexivity. subst rr. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44554 eq_refl D_44554)).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - subst rr. gr. reflexivity.
      - subst rr. gr. exact R2.
      - subst rr. gr. rewrite (K1 8) by reflexivity. gr. reflexivity.
      - subst rr. gr. rewrite (K1 9) by reflexivity. gr. reflexivity.
      - subst rr. gr. rewrite (K1 18) by reflexivity. gr. reflexivity.
      - subst rr. intros r Hr He. keep_tac Hr He. rewrite (K1 r (rp_clob_isl r Hr)). keep_tac Hr He. apply HKp; assumption. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  #[using="s buf K H Hret"] Lemma blk_E : forall regs mF,
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    (forall a, (usp - 64 <= a)%Z -> (a + 8 <= usp)%Z -> rdn SEGS mF (Z_to_bv 64 a) 8 = rdn SEGS p8 (Z_to_bv 64 a) 8) ->
    exists regs',
      msteps SEGS (mkst regs (0x4437c : word) mF rom) (mkst regs' ra mF rom)
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22 /\ getr regs' 10 = getr regs 10
      /\ (forall r, ekeep r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs mF H2 HF. pose proof Hsp.
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18.
    pose proof rd_s3 as RD19. pose proof rd_s4 as RD20. pose proof rd_s5 as RD21. pose proof rd_s6 as RD22.
    rewrite <- HF in RD1 by lia. rewrite <- HF in RD8 by lia. rewrite <- HF in RD9 by lia. rewrite <- HF in RD18 by lia.
    rewrite <- HF in RD19 by lia. rewrite <- HF in RD20 by lia. rewrite <- HF in RD21 by lia. rewrite <- HF in RD22 by lia.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4437c eq_refl D_4437c)). rewrite H2. zn.
      mld2 F_44380 D_44380 ra RD1 H2.
      mld2 F_44384 D_44384 (getr regs0 8) RD8 H2.
      mld2 F_44388 D_44388 (getr regs0 9) RD9 H2.
      mld2 F_4438c D_4438c (getr regs0 18) RD18 H2.
      mld2 F_44390 D_44390 (getr regs0 19) RD19 H2.
      mld2 F_44394 D_44394 (getr regs0 20) RD20 H2.
      mld2 F_44398 D_44398 (getr regs0 21) RD21 H2.
      mld2 F_4439c D_4439c (getr regs0 22) RD22 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_443a0 eq_refl D_443a0)). gr. zn.
      replace (usp - 2144 + 112 + 2032)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_443a4 eq_refl D_443a4); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r He. unfold ekeep in He.
      repeat (rewrite getr_other by (intros ->; cbn in He; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="s H Hret H01 H02 H010 Hs HK"] Theorem isl_body :
    exists regs' (i : Z) m',
      msteps SEGS (mkst regs0 (0x442c4 : word) mem rom) (mkst regs' ra m' rom)
      /\ (0 <= i <= K)%Z /\ bv_unsigned (VAsanMuslStrlen.b_ buf i) = 0%Z
      /\ (forall j, (0 <= j < i)%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf j) <> 0%Z)
      /\ getr regs' 10 = Z_to_bv 64 i /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, isl_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - ISL_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
  Proof.
    pose proof Hsp as HU.
    destruct blk_P as (q1 & MP & P2 & P8 & P18 & P10 & PK).
    destruct (blk_S q1 PK P18 P10 P2 P8) as (q2 & i & MS & Hi & Zi & NZi & S10 & S9 & S18 & S2 & S8 & SK).
    destruct (blk_T q2 i Hi SK S9 S10 S18 S8 S2) as (q3 & MT & T9 & T11 & T10 & T18 & T2 & T8 & TK).
    (* [comment removed for export] *)
    assert (TAIL : forall q mX, sfr mX -> keep q ->
      getr q 10 = Z_to_bv 64 i -> getr q 2 = Z_to_bv 64 (usp - 2144) ->
      msteps SEGS (mkst regs0 (0x442c4 : word) mem rom) (mkst q (0x4437c : word) mX rom) ->
      exists regs' (i : Z) m',
        msteps SEGS (mkst regs0 (0x442c4 : word) mem rom) (mkst regs' ra m' rom)
        /\ (0 <= i <= K)%Z /\ bv_unsigned (VAsanMuslStrlen.b_ buf i) = 0%Z
        /\ (forall j, (0 <= j < i)%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf j) <> 0%Z)
        /\ getr regs' 10 = Z_to_bv 64 i /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, isl_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - ISL_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true)).
    { intros q mX F QK Q10 Q2 MQ. pose proof F as (F1 & F2 & F3 & F4).
      destruct (blk_E q mX Q2) as (q6 & M6 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E10 & EK).
      { intros a Ha1 Ha2. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx.
        apply F2. lia. }
      exists q6, i, mX. split; [eapply msteps_trans; [exact MQ | exact M6] |].
      split; [exact Hi|]. split; [exact Zi|]. split; [exact NZi|].
      split; [rewrite E10; exact Q10|]. split; [exact E2|]. split; [exact E1|].
      split; [|split; [exact F1 | split; [exact F4 | exact F3]]].
      intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite E1; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite E2; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact E8|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact E9|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact E18|].
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact E19|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact E20|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact E21|].
      destruct (bv_eq_dec _ r 22) as [-> | N22]; [exact E22|].
      assert (He : ekeep r = false).
      { unfold ekeep. rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8), (bv_eqb_neq _ _ N9),
          (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N22). reflexivity. }
      rewrite (EK r He). apply QK; assumption. }
    destruct (Z.lt_ge_cases i 64) as [Hsmall | Hbig].
    - (* [comment removed for export] *)
      destruct (blk_Q1 q3 p9 i sfr_p9 Hi ltac:(lia) TK T10 T11 T18) as (q4 & w & M4 & A11 & A12 & A13 & A14 & A10 & A2 & A8 & A9 & A18 & AK).
      pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
      destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
      + apply (TAIL q4 p9 sfr_p9 AK A10); [rewrite A2; exact T2|].
        eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MT|].
        eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_44378 eq_refl D_44378); gr; rewrite ?A14, ?getr_zero; br_eq).
        apply mst_refl.
      + assert (NZu : bv_unsigned w <> 0%Z).
        { intros E0. apply NZ. rewrite <- (zbv_self w), E0. reflexivity. }
        destruct (blk_Q2a q4 p9 i sfr_p9 Hi AK A12 A13 A10) as (q5 & M5 & B10 & B21 & B11 & B12 & B2 & B8 & B9 & B18 & BK).
        destruct (blk_Q2b q5 p9 i sfr_p9 Hi BK) as (q6 & M6 & C10 & C2 & C8 & C9 & C18 & CK);
          [rewrite B11; exact A11 | rewrite B12; exact A12 | exact B10 | exact B21 |].
        apply (TAIL q6 p9 sfr_p9 CK C10); [rewrite C2, B2, A2; exact T2|].
        eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MT|].
        eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44378 eq_refl D_44378); gr; rewrite ?A14, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M5|]. exact M6.
    - (* [comment removed for export] *)
      destruct (blk_L q3 p9 i sfr_p9 Hi Hbig TK T9 T10 T11 T18 T2 T8) as (q4 & m4 & M4 & F4 & L10 & L2 & L8 & L9 & L18 & LK).
      apply (TAIL q4 m4 F4 LK L10 L2).
      eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MT|]. exact M4.
  Qed.
End ISL.

(* [comment removed for export] *)
Theorem isl_run :
  forall (mem rom : word -> option byte) (s usp : Z) (buf : list byte) (K : Z),
  islH mem s usp buf K ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 s ->
  exists regs' (i : Z) m',
    msteps SEGS (mkst regs (0x44230 : word) mem rom) (mkst regs' ra m' rom)
    /\ (0 <= i <= K)%Z /\ bv_unsigned (VAsanMuslStrlen.b_ buf i) = 0%Z
    /\ (forall j, (0 <= j < i)%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf j) <> 0%Z)
    /\ getr regs' 10 = Z_to_bv 64 i /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, isl_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - ISL_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
Proof.
  intros mem rom s usp buf K H regs ra Hret H1 H2 H10.
  destruct (isl_body mem rom s usp buf K H regs ra Hret H1 H2 H10) as (regs' & i & m' & M & REST).
  exists regs', i, m'. split; [|exact REST].
  mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44230 eq_refl D_44230)).
  exact M.
Qed.
