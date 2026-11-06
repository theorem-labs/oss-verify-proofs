(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothTls_code.
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
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma step_fence : forall segs regs pc mem rom w fm pr sc rd rs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence fm pr sc rd rs, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w fm pr sc rd rs HF HE HD. step_pipeline HF HE HD. rewrite ?b_npc4; reflexivity. Qed.

Lemma wbytes_agree : forall bs m1 m2 (a x : word), m1 x = m2 x -> wbytes m1 a bs x = wbytes m2 a bs x.
Proof.
  induction bs as [|b bs IH]; intros m1 m2 a x Hx; cbn [wbytes]; [exact Hx|].
  apply IH. cbv beta. destruct (bv_eqb x a); [reflexivity|exact Hx].
Qed.
Lemma wbytes_keep : forall bs m (a x : word), m x <> None -> wbytes m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x Hx; cbn [wbytes]; [exact Hx|].
  apply IH. cbv beta. destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Definition TP : Z := 0x5e4bb0.          (* [comment removed for export] *)
Definition A_DESC : Z := 0xaa198.      (* [comment removed for export] *)
Definition TLS_FRAME : Z := 176.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition tcells (m : word -> option byte) : Prop :=
     rdn SEGS m (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]                 (* [comment removed for export] *)
  /\ cell m 0xab268 0xa33dc                                                (* [comment removed for export] *)
  /\ cell m 0xaa198 1 /\ cell m 0xaa1a0 0xfffffffffffff800                 (* [comment removed for export] *)
  /\ cell m 0x5e4ba8 0x5e4bd0 /\ cell m 0x5e4bd8 0x5e53b0                    (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0xb1420) 1 = Some [Z_to_bv 8 1]                 (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0xb1424) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))  (* [comment removed for export] *)
  /\ cell m 0x5e4b58 0x605f58                                                (* [comment removed for export] *)
  /\ cell m 0xa94a8 0x1436e8 /\ rdn SEGS m (Z_to_bv 64 0x143771) 1 = Some [Z_to_bv 8 1]   (* [comment removed for export] *)
  /\ cell m 0xa9508 0x141658 /\ rdn SEGS m (Z_to_bv 64 0x141658) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))  (* [comment removed for export] *)
  /\ cell m 0xaa1a8 0x8.                                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Record tlsH (mem : word -> option byte) (S ctx thr db beg : Z) (a2v a3v : word) : Prop := {
  t_S     : (0x10007fff8000 <= S - TLS_FRAME)%Z /\ (S < 2 ^ 64)%Z;
  t_stk   : forall a, (S - TLS_FRAME <= a < S)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  t_cells : tcells mem;
  t_ctx   : cell mem 0x605f58 ctx;
  t_ctxb  : (0 < ctx)%Z /\ (ctx + 160 <= 2 ^ 64)%Z;
  t_thr   : cell mem (ctx + 152) thr;
  t_thrb  : (0 < thr)%Z /\ (thr + 64 <= 2 ^ 64)%Z;
  t_a2    : rdn SEGS mem (Z_to_bv 64 (thr + 48)) 8 = Some (word_to_le_bytes 8 a2v);
  t_a3    : rdn SEGS mem (Z_to_bv 64 (thr + 56)) 8 = Some (word_to_le_bytes 8 a3v);
  t_db    : cell mem (TP + 8) db;
  t_dbb   : (0 < db)%Z /\ (db + 32 <= 2 ^ 64)%Z;
  t_beg   : cell mem (db + 24) beg;
  t_begb  : (0 < beg < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  t_ap1   : (ctx + 160 <= S - TLS_FRAME \/ S <= ctx + 152)%Z;
  t_ap2   : (thr + 64 <= S - TLS_FRAME \/ S <= thr + 48)%Z;
  t_ap3   : (db + 32 <= S - TLS_FRAME \/ S <= db + 24)%Z
}.

(* [comment removed for export] *)
Definition tls_clob (r : reg) : bool := (bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13)%bool.

Section TLS.
  Variables (mem rom : word -> option byte) (S ctx thr db beg : Z) (a2v a3v : word).
  Hypothesis H : tlsH mem S ctx thr db beg a2v a3v.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 S.
  Hypothesis H04 : getr regs0 4 = Z_to_bv 64 TP.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 A_DESC.

  #[using="mem ctx thr db beg a2v a3v H"] Lemma HS : (0x10007fff8000 + 176 <= S < 2 ^ 64)%Z.
  Proof. pose proof (t_S _ _ _ _ _ _ _ _ H). unfold TLS_FRAME in *. lia. Qed.

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.

  (* [comment removed for export] *)
  Definition fr_mem (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < S - TLS_FRAME \/ S <= bv_unsigned x)%Z -> m x = mem x)
    /\ (forall x, mem x <> None -> m x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true).

  #[using="Type"] Lemma fr_mem_refl : fr_mem mem.
  Proof. split; [intros; reflexivity|]. split; auto. Qed.

  #[using="ctx thr db beg a2v a3v H"] Lemma fr_mem_w8 : forall m a v, fr_mem m -> (S - TLS_FRAME <= a)%Z -> (a + 8 <= S)%Z ->
    fr_mem (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    intros m a v (F1 & F2 & F3) Ha Hb. pose proof HS. unfold fr_mem, TLS_FRAME in *. split; [|split].
    - intros x Hx. rewrite <- (F1 x Hx). destruct Hx as [Hx|Hx].
      + apply wbytes_below; len8; rewrite ?zbv_u by lia; lia.
      + apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. apply wbytes_keep. apply F2. exact Hx.
    - intros x Hx. apply store_ok1_wbytes. apply F3. exact Hx.
  Qed.

  (* [comment removed for export] *)
  #[using="ctx thr db beg a2v a3v H"] Lemma rdn_fr : forall m (a : Z) k, fr_mem m -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= S - TLS_FRAME \/ S <= a)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k (F1 & _) Ha Hk Hap. pose proof HS. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply F1. unfold TLS_FRAME in *. lia.
  Qed.

  #[using="ctx thr db beg a2v a3v H"] Lemma tcells_fr : forall m, fr_mem m -> tcells m.
  Proof.
    intros m F. pose proof (t_cells _ _ _ _ _ _ _ _ H) as C. pose proof HS. unfold tcells, cell in *.
    rewrite !(rdn_fr m) by (first [exact F | cbn; unfold TLS_FRAME; lia]). exact C.
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma sym_fr : forall m, fr_mem m ->
       cell m 0x605f58 ctx /\ cell m (ctx + 152) thr
    /\ rdn SEGS m (Z_to_bv 64 (thr + 48)) 8 = Some (word_to_le_bytes 8 a2v)
    /\ rdn SEGS m (Z_to_bv 64 (thr + 56)) 8 = Some (word_to_le_bytes 8 a3v)
    /\ cell m (TP + 8) db /\ cell m (db + 24) beg.
  Proof.
    intros m F. pose proof HS. unfold cell, TP.
    pose proof (t_ctxb _ _ _ _ _ _ _ _ H). pose proof (t_thrb _ _ _ _ _ _ _ _ H). pose proof (t_dbb _ _ _ _ _ _ _ _ H).
    pose proof (t_ap1 _ _ _ _ _ _ _ _ H). pose proof (t_ap2 _ _ _ _ _ _ _ _ H). pose proof (t_ap3 _ _ _ _ _ _ _ _ H).
    unfold TLS_FRAME in *.
    rewrite !(rdn_fr m) by (first [exact F | cbn; unfold TLS_FRAME; lia]).
    pose proof (t_ctx _ _ _ _ _ _ _ _ H) as X1. pose proof (t_thr _ _ _ _ _ _ _ _ H) as X2.
    pose proof (t_a2 _ _ _ _ _ _ _ _ H) as X3. pose proof (t_a3 _ _ _ _ _ _ _ _ H) as X4.
    pose proof (t_db _ _ _ _ _ _ _ _ H) as X5. pose proof (t_beg _ _ _ _ _ _ _ _ H) as X6.
    unfold cell, TP in *. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Fixpoint fm (l : list (Z * word)) : word -> option byte :=
    match l with
    | [] => mem
    | (o, v) :: t => wbytes (fm t) (Z_to_bv 64 (S - o)) (word_to_le_bytes 8 v)
    end.
  Definition off_ok (o : Z) : bool := ((8 <=? o) && (o <=? TLS_FRAME))%Z.
  Fixpoint fm_rd (l : list (Z * word)) (o : Z) : option word :=
    match l with
    | [] => None
    | (o', v) :: t => if (o' =? o)%Z then Some v
                      else if ((o' + 8 <=? o) || (o + 8 <=? o'))%Z then fm_rd t o else None
    end.

  #[using="ctx thr db beg a2v a3v H"] Lemma fm_fr : forall l, forallb (fun p => off_ok (fst p)) l = true -> fr_mem (fm l).
  Proof.
    induction l as [|[o v] t IH]; intros Hl; [apply fr_mem_refl|].
    cbn [forallb fst] in Hl. apply andb_prop in Hl as [Ho Ht]. unfold off_ok in Ho.
    apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2. unfold TLS_FRAME in *.
    cbn [fm]. apply fr_mem_w8; [apply IH; exact Ht| unfold TLS_FRAME; lia | lia].
  Qed.

  #[using="ctx thr db beg a2v a3v H"] Lemma fm_rd_sound : forall l o v,
    forallb (fun p => off_ok (fst p)) l = true -> off_ok o = true -> fm_rd l o = Some v ->
    rdn SEGS (fm l) (Z_to_bv 64 (S - o)) 8 = Some (word_to_le_bytes 8 v).
  Proof.
    pose proof HS as HSS. unfold TLS_FRAME in *.
    induction l as [|[o' v'] t IH]; intros o v Hl Ho Hr; [discriminate|].
    cbn [forallb fst] in Hl. apply andb_prop in Hl as [Ho' Ht]. unfold off_ok in Ho, Ho'.
    apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
    apply andb_prop in Ho' as [Ho3 Ho4]. apply Z.leb_le in Ho3. apply Z.leb_le in Ho4. unfold TLS_FRAME in *.
    cbn [fm_rd] in Hr. cbn [fm].
    destruct (Z.eqb_spec o' o) as [->|NE].
    - injection Hr as ->. apply rdn_wbytes_hit8. rewrite zbv_u by lia. lia.
    - destruct ((o' + 8 <=? o) || (o + 8 <=? o'))%Z eqn:D; [|discriminate].
      rewrite rdn_wbytes_out; [apply IH; auto; unfold off_ok, TLS_FRAME; rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.leb_le _ _)) by lia; reflexivity| | |];
        len8; rewrite ?zbv_u by lia; try lia;
      apply orb_prop in D; destruct D as [D|D]; apply Z.leb_le in D; lia.
  Qed.

  #[using="ctx thr db beg a2v a3v H"] Lemma stk8 : forall m a, fr_mem m -> (S - TLS_FRAME <= a)%Z -> (a + 8 <= S)%Z ->
    store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a (_ & _ & F3) H1 H2. pose proof HS. unfold TLS_FRAME in *. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F3. apply (t_stk _ _ _ _ _ _ _ _ H). unfold TLS_FRAME. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac msd F D o v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (S - o)) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption]
                 | apply stk8; [apply fm_fr; reflexivity | unfold TLS_FRAME; lia | lia] ]);
    lazymatch goal with |- msteps _ (mkst _ _ (wbytes (fm ?l) _ _) _) _ =>
      change (wbytes (fm l) (Z_to_bv 64 (S - o)) (word_to_le_bytes 8 v)) with (fm ((o, v) :: l)) end.

  (* [comment removed for export] *)
  Ltac mldf F D o Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ _ F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ => replace a with (S - o)%Z by lia end;
                   apply fm_rd_sound; reflexivity
                 | apply bytes_le_to_Z_8 ]).

  Ltac wz T V := progress (replace T with (Z_to_bv 64 V) by (apply bv_eq; vm_compute; reflexivity)).
  #[using="Type"] Lemma lit_983ec : v_addi (0x48bb8 : word) 4 = Z_to_bv 64 0x48bbc. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma lit_98400 : v_addi (0x48bcc : word) 4 = Z_to_bv 64 0x48bd0. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma lit_9840c : v_addi (0x48bd8 : word) 4 = Z_to_bv 64 0x48bdc. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma lit_98430 : v_addi (0x48bfc : word) 4 = Z_to_bv 64 0x48c00. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma lit_dc5e8 : v_addi (0x5e638 : word) 4 = Z_to_bv 64 0x5e63c. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma v_lb_1 : v_lb (Z_to_bv 8 1) = Z_to_bv 64 1. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma v_lw_0 : v_lw (Z_to_bv 64 0) = Z_to_bv 64 0. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma jalr_tga : v_jalr (Z_to_bv 64 0xa33dc) 0 = (0xa33dc : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma ret_983ec : v_jalr (Z_to_bv 64 0x48bbc) 0 = (0x48bbc : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma ret_98400 : v_jalr (Z_to_bv 64 0x48bd0) 0 = (0x48bd0 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma ret_9840c : v_jalr (Z_to_bv 64 0x48bdc) 0 = (0x48bdc : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma ret_98430 : v_jalr (Z_to_bv 64 0x48c00) 0 = (0x48c00 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma ret_dc5e8 : v_jalr (Z_to_bv 64 0x5e63c) 0 = (0x5e63c : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  #[using="Type"] Lemma bytes4_0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0).
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition lA : list (Z * word) := [(32, getr regs0 18); (24, getr regs0 9); (16, getr regs0 8); (8, ra)]%Z.
  Definition a_clob (r : reg) : bool := (bv_eqb r 2 || bv_eqb r 8)%bool.

  #[using="ctx thr db beg a2v a3v H H01 H02 H010"] Lemma blk_A :
    exists regs,
      msteps SEGS (mkst regs0 (0x4427c : word) mem rom) (mkst regs (0x48bb8 : word) (fm lA) rom)
      /\ getr regs 2 = Z_to_bv 64 (S - 32) /\ getr regs 8 = Z_to_bv 64 A_DESC
      /\ (forall r, a_clob r = false -> getr regs r = getr regs0 r).
  Proof.
    pose proof HS. pose proof H010 as HA0. unfold A_DESC in HA0.
    eexists. split.
    - change mem with (fm []).
      mstep ltac:(eapply (step_jal_x0 _ _ _ _ _ _ _ F_4427c eq_refl D_4427c)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48ba0 eq_refl D_48ba0)). rewrite H02. zn.
      msd F_48ba4 D_48ba4 8%Z ra H02.
      msd F_48ba8 D_48ba8 16%Z (getr regs0 8) H02.
      msd F_48bac D_48bac 24%Z (getr regs0 9) H02.
      msd F_48bb0 D_48bb0 32%Z (getr regs0 18) H02.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48bb4 eq_refl D_48bb4)). gr. rewrite HA0. zn. rewrite ?Z.add_0_r.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr. unfold a_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition lB : list (Z * word) := ((48, Z_to_bv 64 A_DESC) :: (40, Z_to_bv 64 0x48bbc) :: lA)%Z.
  Definition b_clob (r : reg) : bool := (bv_eqb r 1 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 18 || bv_eqb r 2 || bv_eqb r 8)%bool.

  #[using="ctx thr db beg a2v a3v H"] Lemma blk_B : forall regs,
    getr regs 2 = Z_to_bv 64 (S - 32) -> getr regs 8 = Z_to_bv 64 A_DESC ->
    exists regs',
      msteps SEGS (mkst regs (0x48bb8 : word) (fm lA) rom) (mkst regs' (0xa33dc : word) (fm lB) rom)
      /\ getr regs' 2 = Z_to_bv 64 (S - 32) /\ getr regs' 8 = Z_to_bv 64 A_DESC
      /\ getr regs' 10 = Z_to_bv 64 A_DESC /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 1 = Z_to_bv 64 0x48bd0
      /\ (forall r, b_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H2 H8. pose proof HS. pose proof (tcells_fr (fm lB) ltac:(apply fm_fr; reflexivity)) as (C1 & C2 & _).
    eexists. split.
    - mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_48bb8 eq_refl D_48bb8)). rewrite lit_983ec.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be30 eq_refl D_5be30)). gr. rewrite H2. zn.
      msd F_5be34 D_5be34 40%Z (Z_to_bv 64 0x48bbc) H2.
      msd F_5be38 D_5be38 48%Z (Z_to_bv 64 A_DESC) H2.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb2e3c) F_5be3c eq_refl D_5be3c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be40 eq_refl D_5be40)). gr. zn.
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5be44 eq_refl D_5be44);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact C1).
      rewrite v_lb_1.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be48 eq_refl D_5be48)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5be4c eq_refl D_5be4c)).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5be50 eq_refl D_5be50); gr; br_eq).
      mldf F_5be54 D_5be54 40%Z H2.
      mldf F_5be58 D_5be58 48%Z H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be5c eq_refl D_5be5c)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x48bbc) F_5be60 eq_refl D_5be60); gr; reflexivity |].
      imm_norm. rewrite ret_983ec.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaabbc) F_48bbc eq_refl D_48bbc);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_48bc0 D_48bc0 0xa33dc%Z C2 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48bc4 eq_refl D_48bc4)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48bc8 eq_refl D_48bc8)). gr. zn.
      mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa33dc) F_48bcc eq_refl D_48bcc);
                   [reflexivity | gr; reflexivity]).
      rewrite ?lit_98400, ?jalr_tga. apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr. unfold b_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition c_clob (r : reg) : bool := (bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12)%bool.

  #[using="ctx thr db beg a2v a3v H"] Lemma blk_C : forall regs m,
    fr_mem m -> getr regs 4 = Z_to_bv 64 TP -> getr regs 10 = Z_to_bv 64 A_DESC -> getr regs 1 = Z_to_bv 64 0x48bd0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa33dc : word) m rom) (mkst regs' (0x48bd0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 TP
      /\ (forall r, c_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m FR H4 H10 H1. pose proof HS. pose proof (tcells_fr m FR) as (_ & _ & C3 & C4 & C5 & C6 & _). unfold TP, A_DESC in *.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a33dc eq_refl D_a33dc)). gr. rewrite H4. zn.
      mld F_a33e0 D_a33e0 1%Z C3 H10.
      mld F_a33e4 D_a33e4 0x5e4bd0%Z C5 H4.
      mld F_a33e8 D_a33e8 0xfffffffffffff800%Z C4 H10.
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_a33ec eq_refl D_a33ec)). gr. imm_norm.
      wz (v_slli (Z_to_bv 64 1) 3) 8%Z.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_a33f0 eq_refl D_a33f0)). gr. rewrite v_add_zbv by lia.
      mld F_a33f4 D_a33f4 0x5e53b0%Z C6 H4.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_a33f8 eq_refl D_a33f8)). gr. rewrite v_add_zbv by lia.
      wz (Z_to_bv 64 (18446744073709549568 + 6181808)) 0x5e4bb0%Z.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x48bd0) F_a33fc eq_refl D_a33fc); gr; exact H1 |].
      imm_norm. rewrite ret_98400. apply mst_refl.
    - gr. split; [reflexivity|].
      intros r Hr. unfold c_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition lC : list (Z * word) := ((40, Z_to_bv 64 0x48bdc) :: lB)%Z.
  Definition d_clob (r : reg) : bool := (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13)%bool.

  #[using="ctx thr db beg H"] Lemma blk_D : forall regs,
    getr regs 2 = Z_to_bv 64 (S - 32) -> getr regs 4 = Z_to_bv 64 TP -> getr regs 8 = Z_to_bv 64 A_DESC ->
    getr regs 10 = Z_to_bv 64 TP -> getr regs 18 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x48bd0 : word) (fm lB) rom) (mkst regs' (0x6bd44 : word) (fm lC) rom)
      /\ getr regs' 2 = Z_to_bv 64 (S - 32) /\ getr regs' 9 = Z_to_bv 64 TP
      /\ getr regs' 10 = Z_to_bv 64 A_DESC /\ getr regs' 11 = Z_to_bv 64 TP
      /\ getr regs' 12 = a2v /\ getr regs' 13 = a3v /\ getr regs' 1 = Z_to_bv 64 0x48c00
      /\ (forall r, d_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H2 H4 H8 H10 H18. pose proof HS. unfold TP, A_DESC in *.
    pose proof (t_ctxb _ _ _ _ _ _ _ _ H). pose proof (t_thrb _ _ _ _ _ _ _ _ H).
    assert (FC : fr_mem (fm lC)) by (apply fm_fr; reflexivity).
    pose proof (tcells_fr (fm lC) FC) as (_ & _ & _ & _ & _ & _ & C7 & C8 & C9 & _).
    pose proof (sym_fr (fm lC) FC) as (Y1 & Y2 & Y3 & Y4 & _). unfold TP in *.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48bd0 eq_refl D_48bd0)). gr. rewrite H10. zn.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_48bd4 eq_refl D_48bd4); gr; rewrite H18, getr_zero; br_eq).
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_48bd8 eq_refl D_48bd8)). rewrite lit_9840c.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5e630 eq_refl D_5e630)). gr. rewrite H2. zn.
      msd F_5e634 D_5e634 40%Z (Z_to_bv 64 0x48bdc) H2.
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_5e638 eq_refl D_5e638)). rewrite lit_dc5e8.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb117c) F_5717c eq_refl D_5717c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_57180 eq_refl D_57180)). gr. zn.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_57184 eq_refl D_57184);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact C7).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_57188 eq_refl D_57188); gr; rewrite getr_zero; br_eq).
      mstep ltac:(eapply (@step_lw _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) F_5718c eq_refl D_5718c);
                   [gr; imm_norm; zn; exact C8 | exact bytes4_0]).
      rewrite v_lw_0.
      mstep ltac:(eapply (step_jal_x0 _ _ _ _ _ _ _ F_57190 eq_refl D_57190)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a46cc eq_refl D_a46cc)). gr. rewrite H4. zn.
      mld F_a46d0 D_a46d0 0x605f58%Z C9 H4.
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_a46d4 eq_refl D_a46d4)). gr. imm_norm.
      wz (v_slli (Z_to_bv 64 0) 32) 0%Z.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_a46d8 eq_refl D_a46d8)). gr. imm_norm.
      wz (v_srli (Z_to_bv 64 0) 29) 0%Z.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_a46dc eq_refl D_a46dc)). gr. rewrite v_add_zbv by lia.
      mld F_a46e0 D_a46e0 ctx Y1 H4.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5e63c) F_a46e4 eq_refl D_a46e4); gr; reflexivity |].
      imm_norm. rewrite ret_dc5e8.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_5e63c eq_refl D_5e63c); gr; rewrite getr_zero; br_eq).
      mld F_5e640 D_5e640 thr Y2 H4.
      mldf F_5e644 D_5e644 40%Z H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5e648 eq_refl D_5e648)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x48bdc) F_5e64c eq_refl D_5e64c); gr; reflexivity |].
      imm_norm. rewrite ret_9840c.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_48bdc eq_refl D_48bdc); gr; rewrite getr_zero; br_eq).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ a2v F_48be0 eq_refl D_48be0);
                   [ gr; imm_norm; zn; exact Y3 | apply bytes_le_to_Z_8 ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ a3v F_48be4 eq_refl D_48be4);
                   [ gr; imm_norm; zn; exact Y4 | apply bytes_le_to_Z_8 ]).
      mstep ltac:(eapply (step_jal_x0 _ _ _ _ _ _ _ F_48be8 eq_refl D_48be8)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48bf4 eq_refl D_48bf4)). gr. rewrite H8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48bf8 eq_refl D_48bf8)). gr. zn.
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_48bfc eq_refl D_48bfc)). rewrite lit_98430.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr. unfold d_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition lD (regs : bvmap 5 word) : list (Z * word) :=
    ((152, a3v) :: (160, a2v)
     :: (136, getr regs 27) :: (128, getr regs 26) :: (120, getr regs 25) :: (112, getr regs 24)
     :: (104, getr regs 23) :: (96, getr regs 22) :: (88, getr regs 21) :: (80, getr regs 20)
     :: (72, getr regs 19) :: (64, getr regs 18) :: (56, getr regs 9) :: (48, getr regs 8)
     :: (40, getr regs 1) :: lC)%Z.

  Definition e_clob (r : reg) : bool :=
    (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11
     || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21 || bv_eqb r 22 || bv_eqb r 23
     || bv_eqb r 24 || bv_eqb r 25 || bv_eqb r 26 || bv_eqb r 27)%bool.

  #[using="ctx thr db beg H"] Lemma blk_E : forall regs,
    getr regs 2 = Z_to_bv 64 (S - 32) -> getr regs 4 = Z_to_bv 64 TP -> getr regs 10 = Z_to_bv 64 A_DESC ->
    getr regs 12 = a2v -> getr regs 13 = a3v -> getr regs 1 = Z_to_bv 64 0x48c00 ->
    exists regs',
      msteps SEGS (mkst regs (0x6bd44 : word) (fm lC) rom) (mkst regs' (0x48c00 : word) (fm (lD regs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (S - 32) /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 1 = getr regs 1 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
      /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26
      /\ getr regs' 27 = getr regs 27
      /\ (forall r, e_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H2 H4 H10 H12 H13 H1. pose proof HS. unfold TP, A_DESC in *.
    pose proof (t_dbb _ _ _ _ _ _ _ _ H). pose proof (t_begb _ _ _ _ _ _ _ _ H).
    (* [comment removed for export] *)
    set (lP := ((136, getr regs 27) :: (128, getr regs 26) :: (120, getr regs 25) :: (112, getr regs 24)
     :: (104, getr regs 23) :: (96, getr regs 22) :: (88, getr regs 21) :: (80, getr regs 20)
     :: (72, getr regs 19) :: (64, getr regs 18) :: (56, getr regs 9) :: (48, getr regs 8)
     :: (40, getr regs 1) :: lC)%Z).
    assert (FP : fr_mem (fm lP)) by (apply fm_fr; reflexivity).
    pose proof (tcells_fr (fm lP) FP) as (_ & _ & P3 & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & P13 & P14).
    pose proof (sym_fr (fm lP) FP) as (_ & _ & _ & _ & P5 & P6). unfold TP in P5.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bd44 eq_refl D_6bd44)). rewrite H2. zn.
      msd F_6bd48 D_6bd48 40%Z (getr regs 1) H2.
      msd F_6bd4c D_6bd4c 48%Z (getr regs 8) H2.
      msd F_6bd50 D_6bd50 56%Z (getr regs 9) H2.
      msd F_6bd54 D_6bd54 64%Z (getr regs 18) H2.
      msd F_6bd58 D_6bd58 72%Z (getr regs 19) H2.
      msd F_6bd5c D_6bd5c 80%Z (getr regs 20) H2.
      msd F_6bd60 D_6bd60 88%Z (getr regs 21) H2.
      msd F_6bd64 D_6bd64 96%Z (getr regs 22) H2.
      msd F_6bd68 D_6bd68 104%Z (getr regs 23) H2.
      msd F_6bd6c D_6bd6c 112%Z (getr regs 24) H2.
      msd F_6bd70 D_6bd70 120%Z (getr regs 25) H2.
      msd F_6bd74 D_6bd74 128%Z (getr regs 26) H2.
      msd F_6bd78 D_6bd78 136%Z (getr regs 27) H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bd7c eq_refl D_6bd7c)). gr.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa8d80) F_6bd80 eq_refl D_6bd80);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_6bd84 D_6bd84 0x1436e8%Z P10 H2.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_6bd88 eq_refl D_6bd88);
                   gr; imm_norm; zn; exact P11).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_6bd8c eq_refl D_6bd8c); gr; rewrite getr_zero; br_eq).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bd90 eq_refl D_6bd90)). gr. rewrite H10. zn.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa8d94) F_6bd94 eq_refl D_6bd94);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_6bd98 D_6bd98 0x141658%Z P12 H2.
      mld F_6bd9c D_6bd9c 1%Z P3 H2.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9da0) F_6bda0 eq_refl D_6bda0);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(eapply (@step_lw _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) F_6bda4 eq_refl D_6bda4);
                   [gr; imm_norm; zn; rewrite ?Z.add_0_r; exact P13 | exact bytes4_0]).
      rewrite v_lw_0.
      mld F_6bda8 D_6bda8 0x8%Z P14 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bdac eq_refl D_6bdac)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_6bdb0 eq_refl D_6bdb0)). gr. rewrite H4, v_add_zbv by lia.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_6bdb4 eq_refl D_6bdb4); gr; br_lt).
      mld F_6bdb8 D_6bdb8 db P5 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bdbc eq_refl D_6bdbc)). rewrite getr_zero, k_m1_val.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_6bdc0 eq_refl D_6bdc0)).
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_6bdc4 eq_refl D_6bdc4); gr; br_eq).
      mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_6bdc8 eq_refl D_6bdc8); gr; rewrite getr_zero; br_eq).
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_6be4c eq_refl D_6be4c); gr; rewrite getr_zero; br_eq).
      subst lP.
      msd F_6be50 D_6be50 160%Z a2v H2.
      msd F_6be54 D_6be54 152%Z a3v H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6be58 eq_refl D_6be58)). rewrite getr_zero. zn.
      mstep ltac:(eapply (step_bltu_tk _ _ _ _ _ _ _ _ _ F_6be5c eq_refl D_6be5c); gr; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bf0c eq_refl D_6bf0c)). gr. zn.
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_6bf10 eq_refl D_6bf10)). gr. imm_norm.
      wz (v_slli (Z_to_bv 64 1) 4) 16%Z.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_6bf14 eq_refl D_6bf14)). gr. rewrite v_add_zbv by lia.
      pose proof (sym_fr (fm (lD regs)) ltac:(apply fm_fr; reflexivity)) as (_ & _ & _ & _ & _ & Q6).
      mld F_6bf18 D_6bf18 beg Q6 H2.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_6bf1c eq_refl D_6bf1c); gr; rewrite getr_zero; br_eq).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bf20 eq_refl D_6bf20)). rewrite getr_zero. zn.
      mldf F_6bf24 D_6bf24 40%Z H2.
      mldf F_6bf28 D_6bf28 48%Z H2.
      mldf F_6bf2c D_6bf2c 56%Z H2.
      mldf F_6bf30 D_6bf30 64%Z H2.
      mldf F_6bf34 D_6bf34 72%Z H2.
      mldf F_6bf38 D_6bf38 80%Z H2.
      mldf F_6bf3c D_6bf3c 88%Z H2.
      mldf F_6bf40 D_6bf40 96%Z H2.
      mldf F_6bf44 D_6bf44 104%Z H2.
      mldf F_6bf48 D_6bf48 112%Z H2.
      mldf F_6bf4c D_6bf4c 120%Z H2.
      mldf F_6bf50 D_6bf50 128%Z H2.
      mldf F_6bf54 D_6bf54 136%Z H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6bf58 eq_refl D_6bf58)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x48c00) F_6bf5c eq_refl D_6bf5c); gr; exact H1 |].
      imm_norm. rewrite ret_98430. apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr. unfold e_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition f_clob (r : reg) : bool := (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 18)%bool.

  #[using="ctx thr db beg H Hret"] Lemma blk_F : forall regs rr,
    getr regs 2 = Z_to_bv 64 (S - 32) -> getr regs 9 = Z_to_bv 64 TP ->
    exists regs',
      msteps SEGS (mkst regs (0x48c00 : word) (fm (lD rr)) rom) (mkst regs' ra (fm (lD rr)) rom)
      /\ getr regs' 2 = Z_to_bv 64 S /\ getr regs' 10 = Z_to_bv 64 TP /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ (forall r, f_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs rr H2 H9. pose proof HS. unfold TP in *.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48c00 eq_refl D_48c00)). gr. rewrite H9. zn.
      mldf F_48c04 D_48c04 8%Z H2.
      mldf F_48c08 D_48c08 16%Z H2.
      mldf F_48c0c D_48c0c 24%Z H2.
      mldf F_48c10 D_48c10 32%Z H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_48c14 eq_refl D_48c14)). gr. rewrite H2. zn.
      replace (S - 32 + 32)%Z with S by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_48c18 eq_refl D_48c18); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr. unfold f_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ctx thr db beg a2v a3v H Hret H01 H02 H04 H010"] Theorem tls_AM :
    exists regs' m',
      msteps SEGS (mkst regs0 (0x4427c : word) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 TP /\ getr regs' 2 = Z_to_bv 64 S /\ getr regs' 1 = ra
      /\ (forall r, tls_clob r = false -> getr regs' r = getr regs0 r)
      /\ fr_mem m'.
  Proof.
    pose proof HS as HU.
    destruct blk_A as (q1 & M1 & A2 & A8 & AK).
    assert (A4 : getr q1 4 = Z_to_bv 64 TP) by (rewrite AK by reflexivity; exact H04).
    destruct (blk_B q1 A2 A8) as (q2 & M2 & B2 & B8 & B10 & B18 & B1 & BK).
    assert (B4 : getr q2 4 = Z_to_bv 64 TP) by (rewrite BK by reflexivity; exact A4).
    destruct (blk_C q2 (fm lB) ltac:(apply fm_fr; reflexivity) B4 B10 B1) as (q3 & M3 & C10 & CK).
    assert (C2 : getr q3 2 = Z_to_bv 64 (S - 32)) by (rewrite CK by reflexivity; exact B2).
    assert (C4 : getr q3 4 = Z_to_bv 64 TP) by (rewrite CK by reflexivity; exact B4).
    assert (C8 : getr q3 8 = Z_to_bv 64 A_DESC) by (rewrite CK by reflexivity; exact B8).
    assert (C18 : getr q3 18 = Z_to_bv 64 1) by (rewrite CK by reflexivity; exact B18).
    destruct (blk_D q3 C2 C4 C8 C10 C18) as (q4 & M4 & D2 & D9 & D10 & D11 & D12 & D13 & D1 & DK).
    assert (D4 : getr q4 4 = Z_to_bv 64 TP) by (rewrite DK by reflexivity; exact C4).
    destruct (blk_E q4 D2 D4 D10 D12 D13 D1) as (q5 & M5 & E2 & E10 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & EK).
    assert (E9' : getr q5 9 = Z_to_bv 64 TP) by (rewrite E9; exact D9).
    destruct (blk_F q5 q4 E2 E9') as (q6 & M6 & F2 & F10 & F1 & F8 & F9 & F18 & FK).
    exists q6, (fm (lD q4)). split; [|split; [exact F10|split; [exact F2|split; [exact F1|split; [|apply fm_fr; reflexivity]]]]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
      eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. exact M6.
    - intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite F1; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite F2; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact F8|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact F9|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact F18|].
      assert (G : forall k : reg, (k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) ->
                  getr q6 k = getr regs0 k).
      { intros k Hk.
        assert (EE : getr q5 k = getr q4 k) by (destruct Hk as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; assumption).
        rewrite FK by (destruct Hk as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; reflexivity).
        rewrite EE. rewrite DK, CK, BK, AK by (destruct Hk as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; reflexivity).
        reflexivity. }
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 22) as [-> | N22]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 23) as [-> | N23]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 24) as [-> | N24]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 25) as [-> | N25]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 26) as [-> | N26]; [apply G; tauto|].
      destruct (bv_eq_dec _ r 27) as [-> | N27]; [apply G; tauto|].
      unfold tls_clob in Hr.
      apply orb_false_iff in Hr as [Hr T13]. apply orb_false_iff in Hr as [Hr T12]. apply orb_false_iff in Hr as [T10 T11].
      assert (NE : forall k : reg, r <> k -> bv_eqb r k = false) by (intros k Hk; apply bv_eqb_neq; exact Hk).
      pose proof (NE _ N1) as T1. pose proof (NE _ N2) as T2. pose proof (NE _ N8) as T8. pose proof (NE _ N9) as T9.
      pose proof (NE _ N18) as T18. pose proof (NE _ N19) as T19. pose proof (NE _ N20) as T20. pose proof (NE _ N21) as T21.
      pose proof (NE _ N22) as T22. pose proof (NE _ N23) as T23. pose proof (NE _ N24) as T24. pose proof (NE _ N25) as T25.
      pose proof (NE _ N26) as T26. pose proof (NE _ N27) as T27.
      rewrite FK by (unfold f_clob; rewrite ?T1, ?T2, ?T8, ?T9, ?T10, ?T18; reflexivity).
      rewrite EK by (unfold e_clob; rewrite ?T1, ?T2, ?T8, ?T9, ?T10, ?T11, ?T18, ?T19, ?T20, ?T21, ?T22, ?T23, ?T24, ?T25, ?T26, ?T27; reflexivity).
      rewrite DK by (unfold d_clob; rewrite ?T1, ?T2, ?T9, ?T10, ?T11, ?T12, ?T13; reflexivity).
      rewrite CK by (unfold c_clob; rewrite ?T10, ?T11, ?T12; reflexivity).
      rewrite BK by (unfold b_clob; rewrite ?T1, ?T10, ?T11, ?T18, ?T2, ?T8; reflexivity).
      rewrite AK by (unfold a_clob; rewrite ?T2, ?T8; reflexivity).
      reflexivity.
  Qed.
End TLS.

(* [comment removed for export] *)
Theorem tls_run :
  forall (mem rom : word -> option byte) (S ctx thr db beg : Z) (a2v a3v : word),
  tlsH mem S ctx thr db beg a2v a3v ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 TP ->
  getr regs 10 = Z_to_bv 64 A_DESC ->
  exists regs' m',
    msteps SEGS (mkst regs (0x4427c : word) mem rom) (mkst regs' ra m' rom)
    /\ getr regs' 10 = Z_to_bv 64 TP /\ getr regs' 2 = Z_to_bv 64 S /\ getr regs' 1 = ra
    /\ (forall r, tls_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < S - TLS_FRAME \/ S <= bv_unsigned x)%Z -> m' x = mem x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
Proof.
  intros mem rom S ctx thr db beg a2v a3v H regs ra Hret H1 H2 H4 H10.
  destruct (tls_AM mem rom S ctx thr db beg a2v a3v H regs ra Hret H1 H2 H4 H10) as (regs' & m' & M & R10 & R2 & R1 & RK & (F1 & F2 & F3)).
  exists regs', m'. repeat split; auto.
Qed.
