(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ARep AHeapP ARepExt FsKit AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFake_cnt AFake_gcP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_sm0P. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_sm1P. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_sm2P. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_sm0PB. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_sm1PB. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_sm2PB. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFake_hnrP AFake_relP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm1g. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_ahnr F_adepot ARepQ ARepQP ASec AInstance AInstanceM AInstanceF AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Notation AHg g := (AHEAP_P (AHI (gb:=g))).

Definition rdb (m : amem) (a : Z) : byte := match m (wa a) with Some b => b | None => Z_to_bv 8 0 end.
Definition rs_word (m : amem) (F : Z) : word := le_bytes_to_word (map (fun i => rdb m (F + 24 + Z.of_nat i)) (seq 0 8)).
Definition rs_mem (m : amem) (F : Z) : Z := bv_unsigned (rs_word m F).

Lemma rs_mem_range : forall m F, 0 <= rs_mem m F < 2^64.
Proof. intros m F. unfold rs_mem. pose proof (bv_unsigned_in_range 64 (rs_word m F)) as R. unfold bv_modulus in R. lia. Qed.

Lemma rs_mem_cells : forall m F, wr_at asegs m (F + 24) 8 -> 0x62f000 <= F + 24 ->
  rw_cells asegs m (F + 24) [C8 (Z_to_bv 64 (rs_mem m F))].
Proof.
  intros m F W LO. pose proof (no_image_asan (F + 24) (F + 24 + 8) LO) as NI.
  unfold rs_mem. rewrite Z_to_bv_bv_unsigned.
  split; [| cbn [cells_size csize Nat.add]; exact W].
  split; [cbn; auto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  unfold rs_word. rewrite le8_of_bytes by (rewrite length_map, length_seq; reflexivity).
  destruct W as (W0 & W1 & W2). split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (mrd_no_image asegs m (F + 24) (F + 24 + 8) (F + 24 + Z.of_nat i) NI ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct (wr_at_some asegs m (F + 24) 8 (Z.of_nat i) (conj W0 (conj W1 W2)) NI ltac:(lia)) as [b Hb].
  rewrite Hb. symmetry. rewrite nth_error_map.
  replace (nth_error (seq 0 8) i) with (Some i).
  2:{ clear - Hi. do 8 (destruct i as [|i]; [reflexivity|]). lia. }
  cbn [option_map]. unfold rdb. rewrite Hb. reflexivity.
Qed.

Lemma afakeU_block : forall g L RNG st LB m c F n, AHg g L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  0 <= c < FK_NCLS /\ n = fk_fsize c /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP /\ 64 <= n
  /\ wr_at asegs m F n /\ wr_at asegs m (shad F) (shlen n).
Proof.
  intros g L RNG st LB m c F n AH Hb. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LB m c F n HFK Hb) as (C0 & EN & NP & F64 & FLO & FHI & BK & TOP & _).
  destruct HFK as (G & _ & _ & _ & _ & DC1 & DC2 & _). destruct G as (G1 & G2 & G3 & _).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI, FK_NCLS in *.
  assert (N64 : exists q, n = 64 * q /\ 1 <= q).
  { exists (2 ^ c). subst n. unfold fk_fsize. rewrite Z.pow_add_r by lia. split; [reflexivity|]. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)). lia. }
  destruct N64 as (q & EQ & Q1).
  split; [lia|]. split; [exact EN|]. split; [exact F64|]. split; [exact BK|]. split; [exact TOP|]. split; [lia|].
  assert (DCW : forall A k, dc_at m A k -> 0 <= k -> wr_at asegs m A k).
  { intros A k [bs H] Hk. apply (rw_cells_wr_at asegs m A _ k H). cbn [cells_size csize Nat.add]. lia. }
  split.
  - apply DCW; [| lia]. apply (dc_sub m (al_fake L + 4096) (11571200 - 4096)); [exact DC1| lia| lia| lia].
  - assert (SH : shad (al_fake L) <= shad F /\ shad F + shlen n <= shad (al_fake L) + shlen 11571200 /\ 0 <= shlen n).
    { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - F64 G1 FLO FHI EQ Q1 GL1. Z.div_mod_to_equations. lia. }
    apply DCW; [| lia]. apply (dc_sub m (shad (al_fake L)) (shlen 11571200)); [exact DC2| lia| lia| lia].
Qed.

Lemma rs_of_mem : forall g L RNG st LB m, AHg g L RNG st LB m ->
  forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rs_mem m F < 2^64 /\ rw_cells asegs m (F + 24) [C8 (Z_to_bv 64 (rs_mem m F))].
Proof.
  intros g L RNG st LB m AH c F n Hb. split; [apply rs_mem_range|].
  destruct (afakeU_block g L RNG st LB m c F n AH Hb) as (_ & _ & _ & BK & _ & N64 & WR & _).
  apply rs_mem_cells.
  - apply (Shadow.wr_at_sub asegs m F n (F + 24) 8 WR); lia.
  - unfold ablk, AIMG_HI in BK. lia.
Qed.

Lemma nth_error_ext_len8 : forall (l1 l2 : list byte), (forall i, (i < 8)%nat -> nth_error l1 i = nth_error l2 i) -> length l1 = 8%nat -> length l2 = 8%nat -> l1 = l2.
Proof.
  intros l1 l2 H L1 L2. apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [LT|GE]; [exact (H i LT)|].
  rewrite (proj2 (nth_error_None l1 i)) by lia. rewrite (proj2 (nth_error_None l2 i)) by lia. reflexivity.
Qed.

Lemma rs_mem_of_bytes : forall m F (rs : word), bytes_at asegs m (F + 24) (le8 rs) -> 0x62f000 <= F + 24 -> rs_mem m F = bv_unsigned rs.
Proof.
  intros m F rs (B0 & B1 & B) LO. pose proof (no_image_asan (F + 24) (F + 24 + 8) LO) as NI. rewrite length_le8 in B1.
  unfold rs_mem, rs_word. f_equal. transitivity (le_bytes_to_word (le8 rs)); [| apply le_bytes_to_word_le8]. f_equal.
  apply nth_error_ext_len8; [| rewrite length_map, length_seq; reflexivity| apply length_le8]. intros i Hi. rewrite nth_error_map.
  replace (nth_error (seq 0 8) i) with (Some i) by (clear - Hi; do 8 (destruct i as [|i]; [reflexivity|]); lia).
  cbn [option_map]. specialize (B i ltac:(rewrite length_le8; exact Hi)).
  rewrite (mrd_no_image asegs m (F + 24) (F + 24 + 8) (F + 24 + Z.of_nat i) NI ltac:(lia) ltac:(lia) ltac:(lia)) in B.
  unfold rdb. rewrite B. destruct (nth_error (le8 rs) i) as [b|] eqn:E; [reflexivity|].
  exfalso. apply nth_error_None in E. rewrite length_le8 in E. lia.
Qed.

Definition fk_live (L : alayout) (m : amem) (sp : word) (b : ablock) : Prop :=
  AFake_gcP.fk_dead (rs_mem m) (al_bot L) (bv_unsigned sp) b = false.

Lemma fk_live_heap : forall L m sp p A n, fk_live L m sp (HB p A n).
Proof. intros. reflexivity. Qed.
Lemma fk_live_of_rs : forall L m sp c F n (rs : word), bytes_at asegs m (F + 24) (le8 rs) -> 0x62f000 <= F + 24 ->
  bv_unsigned sp <= bv_unsigned rs -> fk_live L m sp (mkABlock (ABFake c) F n).
Proof.
  intros L m sp c F n rs BA LO LE. unfold fk_live, AFake_gcP.fk_dead. cbn [ab_kind ab_addr]. rewrite (rs_mem_of_bytes m F rs BA LO).
  apply andb_false_iff. right. apply Z.ltb_ge. exact LE.
Qed.

Definition smU_post (c n : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (LBk : list ablock) (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres aci_I LBk (bv_unsigned sp) m m'
    /\ AHEAPu L RNG st (mkABlock (ABFake c) F n :: LBk) m'
    /\ (forall b, In b LBk -> In b LB) /\ (forall b, In b LB -> fk_live L m sp b -> In b LBk)
    /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) (Z.to_nat (n / 64)))
    /\ rng RNG F n /\ rng RNG (shad F) (n / 8)
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Definition smU_stmt (c n nfr entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAPu L RNG st LB m ->
  Z.of_nat (fk_count c LB) < nfr ->
  (forall c' F n', In (mkABlock (ABFake c') F n') LB -> c' <= 2) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (smU_post c n L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Ltac smU_arm_A TH :=
  intros until lo; intros [g AH] NOTFULL CLS MI ST BOT LO SPT TP RSTK RIMG FRNG;
  destruct g;
  [ | lazymatch type of AH with
      | AHEAP_P _ _ _ _ ?LB0 _ =>
        eapply evtF_mono;
        [ eapply (TH rc ov false adepot_iface AQUAR ASEC_of (AH_laws (gb:=false)) aci_I aci_ok1); try eassumption; reflexivity
        | let ms' := fresh "ms'" in
          intros ms' (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & j0 & j1 & j2 & junk
                      & E & MI' & ST' & PR & AH' & F64 & BK & TOP & FRM & SHD & R1 & R2 & RSW);
          exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', LB0, j0, j1, j2, junk;
          split; [exact E|]; split; [exact MI'|]; split; [exact ST'|]; split; [exact PR|];
          split; [exists false; exact AH'|]; split; [intros b Hb; exact Hb|]; split; [intros b Hb _; exact Hb|];
          split; [first [exact F64 | (clear - F64; Z.div_mod_to_equations; lia)]|]; split; [exact BK|]; split; [exact TOP|]; split; [exact FRM|]; split; [exact SHD|];
          split; [exact R1|]; split; [exact R2| exact RSW] ]
      end ].

Ltac smU_arm_B TH :=
  lazymatch goal with
  | AH : AHEAP_P _ ?L0 _ _ ?LB0 ?m0 |- evtF _ _ (smU_post _ _ _ _ _ ?sp0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
    eapply evtF_mono;
    [ eapply (TH rc ov adepot_iface AQUAR ASEC_of (AH_laws (gb:=true)) aci_I aci_ok1) with (rsf := rs_mem m0); try eassumption;
      eapply rs_of_mem; eassumption
    | let ms' := fresh "ms'" in
      intros ms' (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & j0 & j1 & j2 & junk
                  & E & MI' & ST' & PR & AH' & F64 & BK & TOP & FRM & SHD & R1 & R2 & RSW);
      exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m',
             (AFake_gcP.fk_kept LB0 (rs_mem m0) (al_bot L0) (bv_unsigned sp0)), j0, j1, j2, junk;
      split; [exact E|]; split; [exact MI'|]; split; [exact ST'|]; split; [exact PR|];
      split; [exists false; exact AH'|];
      split; [intros b Hb; exact (proj1 (proj1 (AFake_gcP.fk_kept_In _ _ _ _ b) Hb))|];
      split; [intros b Hb LV; apply (AFake_gcP.fk_kept_In _ _ _ _ b); split; [exact Hb| exact LV]|];
      split; [first [exact F64 | (clear - F64; Z.div_mod_to_equations; lia)]|]; split; [exact BK|]; split; [exact TOP|]; split; [exact FRM|]; split; [exact SHD|];
      split; [exact R1|]; split; [exact R2| exact RSW] ]
  end.

Theorem AHU_stack_malloc_0 : smU_stmt 0 64 16384 ASTKMALLOC0.
Proof. unfold smU_stmt. smU_arm_A @stack_malloc_0_GA. smU_arm_B @stack_malloc_0_GB. Qed.
Theorem AHU_stack_malloc_1 : smU_stmt 1 128 8192 ASTKMALLOC1.
Proof. unfold smU_stmt. smU_arm_A @stack_malloc_1_GA. smU_arm_B @stack_malloc_1_GB. Qed.
Theorem AHU_stack_malloc_2 : smU_stmt 2 256 4096 ASTKMALLOC2.
Proof. unfold smU_stmt. smU_arm_A @stack_malloc_2_GA. smU_arm_B @stack_malloc_2_GB. Qed.

Definition hnrU_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ AHEAPu L RNG st LB m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr aci_I LB (bv_unsigned sp) a ->
          ~ (shad (hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None))
    /\ rw_cells asegs m' (shad (hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - hnr_bottom sp))))].

Theorem AHU_hnr : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAPu L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HNR_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (shad (hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  rng RNG (shad (hnr_bottom sp)) (shlen (al_top L - hnr_bottom sp)) ->
  evtF asegs RNG (hnrU_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHNR) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros [g AH] MI ST BOT LO SPT TP SHW RSTK RIMG FRNG RSH.
  eapply evtF_mono.
  - eapply (hnr_P adepot_iface AQUAR ASEC_of g (AH_laws (gb:=g)) aci_I aci_ok1); eassumption.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & AH' & PR & Z0).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists true; exact AH'|]. split; [exact PR| exact Z0].
Qed.

Theorem AHU_fake_release : forall L RNG st LB m c F n,
  AHEAPu L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  AHEAPu L RNG st (fk_rel c F LB) (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m c F n [g AH] Hb. exists g.
  exact (fake_release_G (gb:=g) adepot_iface AQUAR ASEC_of (AH_laws (gb:=g)) L RNG st LB m c F n AH Hb).
Qed.

Lemma fflagU_facts : forall L RNG st LB m c F n, AHEAPu L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  al_fake L + 4096 <= fflag L c F < al_fake L + 36864 /\ al_fake L + 36864 <= F /\ wr_at asegs m (fflag L c F) 1.
Proof.
  intros L RNG st LB m c F n [g AH] Hb. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LB m c F n HFK Hb) as (C0 & EN & NP & F64 & FLO & FHI & BK & TOP & pos & Hp & HF & EF & FR).
  split; [exact FR|]. split; [exact FLO|].
  destruct HFK as (G & _ & _ & _ & _ & DC1 & _).
  assert (DCW : forall A k, dc_at m A k -> 0 <= k -> wr_at asegs m A k).
  { intros A k [bs H] Hk. apply (rw_cells_wr_at asegs m A _ k H). cbn [cells_size csize Nat.add]. lia. }
  apply DCW; [| lia]. apply (dc_sub m (al_fake L + 4096) (11571200 - 4096)); [exact DC1| lia| lia| lia].
Qed.

Lemma fakeU_obj : forall L RNG st LB m, AHEAPu L RNG st LB m -> ablk (al_fake L) (al_fake L + 11571200).
Proof.
  intros L RNG st LB m [g AH]. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct HFK as (G & _). destruct G as (G1 & G2 & _). exact G2.
Qed.
Lemma fakeU_frame_lo : forall L RNG st LB m c F n, AHEAPu L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  al_fake L + 36864 <= F /\ F + n <= al_fake L + 11571200 /\ n = fk_fsize c /\ 0 <= c.
Proof.
  intros L RNG st LB m c F n [g AH] Hb. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LB m c F n HFK Hb) as (C0 & EN & NP & F64 & FLO & FHI & _). unfold FAKESZ in FHI. repeat split; [exact FLO| exact FHI| exact EN| lia].
Qed.
Lemma heapU_off_fake : forall L RNG st LB m p A n, AHEAPu L RNG st LB m -> In (HB p A n) LB ->
  A + n <= al_fake L \/ al_fake L + 11571200 <= A.
Proof. intros L RNG st LB m p A n [g AH] Hb. exact (AHEAP_P_hb_fake _ L RNG st LB m p A n AH Hb). Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import RtCells.TwinB AProto.TwinB ABase.TwinB ABytes.TwinB AMalloc_iface.TwinB ARep.TwinB AHeapP.TwinB ARepExt.TwinB FsKit.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AFake_cnt.TwinB AFake_gcP.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_sm0P.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_sm1P.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_sm2P.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_sm0PB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_sm1PB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_sm2PB. Import AFake_hnrP.TwinB AFake_relP.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm1g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2. Import F_ahnr.TwinB F_adepot.TwinB ARepQ.TwinB ARepQP.TwinB ASec.TwinB AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB AInstanceU.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Notation AHg g := (AHEAP_P (AHI (gb:=g))).

Definition rdb (m : amem) (a : Z) : byte := match m (wa a) with Some b => b | None => Z_to_bv 8 0 end.
Definition rs_word (m : amem) (F : Z) : word := le_bytes_to_word (map (fun i => rdb m (F + 24 + Z.of_nat i)) (seq 0 8)).
Definition rs_mem (m : amem) (F : Z) : Z := bv_unsigned (rs_word m F).

Lemma rs_mem_range : forall m F, 0 <= rs_mem m F < 2^64.
Proof. intros m F. unfold rs_mem. pose proof (bv_unsigned_in_range 64 (rs_word m F)) as R. unfold bv_modulus in R. lia. Qed.

Lemma rs_mem_cells : forall m F, wr_at bsegs m (F + 24) 8 -> 0x631000 <= F + 24 ->
  rw_cells bsegs m (F + 24) [C8 (Z_to_bv 64 (rs_mem m F))].
Proof.
  intros m F W LO. pose proof (no_image_asan (F + 24) (F + 24 + 8) LO) as NI.
  unfold rs_mem. rewrite Z_to_bv_bv_unsigned.
  split; [| cbn [cells_size csize Nat.add]; exact W].
  split; [cbn; auto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  unfold rs_word. rewrite le8_of_bytes by (rewrite length_map, length_seq; reflexivity).
  destruct W as (W0 & W1 & W2). split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (mrd_no_image bsegs m (F + 24) (F + 24 + 8) (F + 24 + Z.of_nat i) NI ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct (wr_at_some bsegs m (F + 24) 8 (Z.of_nat i) (conj W0 (conj W1 W2)) NI ltac:(lia)) as [b Hb].
  rewrite Hb. symmetry. rewrite nth_error_map.
  replace (nth_error (seq 0 8) i) with (Some i).
  2:{ clear - Hi. do 8 (destruct i as [|i]; [reflexivity|]). lia. }
  cbn [option_map]. unfold rdb. rewrite Hb. reflexivity.
Qed.

Lemma afakeU_block : forall g L RNG st LB m c F n, AHg g L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  0 <= c < FK_NCLS /\ n = fk_fsize c /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP /\ 64 <= n
  /\ wr_at bsegs m F n /\ wr_at bsegs m (shad F) (shlen n).
Proof.
  intros g L RNG st LB m c F n AH Hb. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LB m c F n HFK Hb) as (C0 & EN & NP & F64 & FLO & FHI & BK & TOP & _).
  destruct HFK as (G & _ & _ & _ & _ & DC1 & DC2 & _). destruct G as (G1 & G2 & G3 & _).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI, FK_NCLS in *.
  assert (N64 : exists q, n = 64 * q /\ 1 <= q).
  { exists (2 ^ c). subst n. unfold fk_fsize. rewrite Z.pow_add_r by lia. split; [reflexivity|]. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)). lia. }
  destruct N64 as (q & EQ & Q1).
  split; [lia|]. split; [exact EN|]. split; [exact F64|]. split; [exact BK|]. split; [exact TOP|]. split; [lia|].
  assert (DCW : forall A k, dc_at m A k -> 0 <= k -> wr_at bsegs m A k).
  { intros A k [bs H] Hk. apply (rw_cells_wr_at bsegs m A _ k H). cbn [cells_size csize Nat.add]. lia. }
  split.
  - apply DCW; [| lia]. apply (dc_sub m (al_fake L + 4096) (11571200 - 4096)); [exact DC1| lia| lia| lia].
  - assert (SH : shad (al_fake L) <= shad F /\ shad F + shlen n <= shad (al_fake L) + shlen 11571200 /\ 0 <= shlen n).
    { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - F64 G1 FLO FHI EQ Q1 GL1. Z.div_mod_to_equations. lia. }
    apply DCW; [| lia]. apply (dc_sub m (shad (al_fake L)) (shlen 11571200)); [exact DC2| lia| lia| lia].
Qed.

Lemma rs_of_mem : forall g L RNG st LB m, AHg g L RNG st LB m ->
  forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rs_mem m F < 2^64 /\ rw_cells bsegs m (F + 24) [C8 (Z_to_bv 64 (rs_mem m F))].
Proof.
  intros g L RNG st LB m AH c F n Hb. split; [apply rs_mem_range|].
  destruct (afakeU_block g L RNG st LB m c F n AH Hb) as (_ & _ & _ & BK & _ & N64 & WR & _).
  apply rs_mem_cells.
  - apply (Shadow.wr_at_sub bsegs m F n (F + 24) 8 WR); lia.
  - unfold ablk, AIMG_HI in BK. lia.
Qed.

Lemma nth_error_ext_len8 : forall (l1 l2 : list byte), (forall i, (i < 8)%nat -> nth_error l1 i = nth_error l2 i) -> length l1 = 8%nat -> length l2 = 8%nat -> l1 = l2.
Proof.
  intros l1 l2 H L1 L2. apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [LT|GE]; [exact (H i LT)|].
  rewrite (proj2 (nth_error_None l1 i)) by lia. rewrite (proj2 (nth_error_None l2 i)) by lia. reflexivity.
Qed.

Lemma rs_mem_of_bytes : forall m F (rs : word), bytes_at bsegs m (F + 24) (le8 rs) -> 0x631000 <= F + 24 -> rs_mem m F = bv_unsigned rs.
Proof.
  intros m F rs (B0 & B1 & B) LO. pose proof (no_image_asan (F + 24) (F + 24 + 8) LO) as NI. rewrite length_le8 in B1.
  unfold rs_mem, rs_word. f_equal. transitivity (le_bytes_to_word (le8 rs)); [| apply le_bytes_to_word_le8]. f_equal.
  apply nth_error_ext_len8; [| rewrite length_map, length_seq; reflexivity| apply length_le8]. intros i Hi. rewrite nth_error_map.
  replace (nth_error (seq 0 8) i) with (Some i) by (clear - Hi; do 8 (destruct i as [|i]; [reflexivity|]); lia).
  cbn [option_map]. specialize (B i ltac:(rewrite length_le8; exact Hi)).
  rewrite (mrd_no_image bsegs m (F + 24) (F + 24 + 8) (F + 24 + Z.of_nat i) NI ltac:(lia) ltac:(lia) ltac:(lia)) in B.
  unfold rdb. rewrite B. destruct (nth_error (le8 rs) i) as [b|] eqn:E; [reflexivity|].
  exfalso. apply nth_error_None in E. rewrite length_le8 in E. lia.
Qed.

Definition fk_live (L : alayout) (m : amem) (sp : word) (b : ablock) : Prop :=
  AFake_gcP.TwinB.fk_dead (rs_mem m) (al_bot L) (bv_unsigned sp) b = false.

Lemma fk_live_heap : forall L m sp p A n, fk_live L m sp (HB p A n).
Proof. intros. reflexivity. Qed.
Lemma fk_live_of_rs : forall L m sp c F n (rs : word), bytes_at bsegs m (F + 24) (le8 rs) -> 0x631000 <= F + 24 ->
  bv_unsigned sp <= bv_unsigned rs -> fk_live L m sp (mkABlock (ABFake c) F n).
Proof.
  intros L m sp c F n rs BA LO LE. unfold fk_live, AFake_gcP.TwinB.fk_dead. cbn [ab_kind ab_addr]. rewrite (rs_mem_of_bytes m F rs BA LO).
  apply andb_false_iff. right. apply Z.ltb_ge. exact LE.
Qed.

Definition smU_post (c n : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (LBk : list ablock) (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres aci_I LBk (bv_unsigned sp) m m'
    /\ AHEAPu L RNG st (mkABlock (ABFake c) F n :: LBk) m'
    /\ (forall b, In b LBk -> In b LB) /\ (forall b, In b LB -> fk_live L m sp b -> In b LBk)
    /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) (Z.to_nat (n / 64)))
    /\ rng RNG F n /\ rng RNG (shad F) (n / 8)
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Definition smU_stmt (c n nfr entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAPu L RNG st LB m ->
  Z.of_nat (fk_count c LB) < nfr ->
  (forall c' F n', In (mkABlock (ABFake c') F n') LB -> c' <= 2) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (smU_post c n L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Ltac smU_arm_A TH :=
  intros until lo; intros [g AH] NOTFULL CLS MI ST BOT LO SPT TP RSTK RIMG FRNG;
  destruct g;
  [ | lazymatch type of AH with
      | AHEAP_P _ _ _ _ ?LB0 _ =>
        eapply evtF_mono;
        [ eapply (TH rc ov false adepot_iface AQUAR ASEC_of (AH_laws (gb:=false)) aci_I aci_ok1); try eassumption; reflexivity
        | let ms' := fresh "ms'" in
          intros ms' (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & j0 & j1 & j2 & junk
                      & E & MI' & ST' & PR & AH' & F64 & BK & TOP & FRM & SHD & R1 & R2 & RSW);
          exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', LB0, j0, j1, j2, junk;
          split; [exact E|]; split; [exact MI'|]; split; [exact ST'|]; split; [exact PR|];
          split; [exists false; exact AH'|]; split; [intros b Hb; exact Hb|]; split; [intros b Hb _; exact Hb|];
          split; [first [exact F64 | (clear - F64; Z.div_mod_to_equations; lia)]|]; split; [exact BK|]; split; [exact TOP|]; split; [exact FRM|]; split; [exact SHD|];
          split; [exact R1|]; split; [exact R2| exact RSW] ]
      end ].

Ltac smU_arm_B TH :=
  lazymatch goal with
  | AH : AHEAP_P _ ?L0 _ _ ?LB0 ?m0 |- evtF _ _ (smU_post _ _ _ _ _ ?sp0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
    eapply evtF_mono;
    [ eapply (TH rc ov adepot_iface AQUAR ASEC_of (AH_laws (gb:=true)) aci_I aci_ok1) with (rsf := rs_mem m0); try eassumption;
      eapply rs_of_mem; eassumption
    | let ms' := fresh "ms'" in
      intros ms' (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & j0 & j1 & j2 & junk
                  & E & MI' & ST' & PR & AH' & F64 & BK & TOP & FRM & SHD & R1 & R2 & RSW);
      exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m',
             (AFake_gcP.TwinB.fk_kept LB0 (rs_mem m0) (al_bot L0) (bv_unsigned sp0)), j0, j1, j2, junk;
      split; [exact E|]; split; [exact MI'|]; split; [exact ST'|]; split; [exact PR|];
      split; [exists false; exact AH'|];
      split; [intros b Hb; exact (proj1 (proj1 (AFake_gcP.TwinB.fk_kept_In _ _ _ _ b) Hb))|];
      split; [intros b Hb LV; apply (AFake_gcP.TwinB.fk_kept_In _ _ _ _ b); split; [exact Hb| exact LV]|];
      split; [first [exact F64 | (clear - F64; Z.div_mod_to_equations; lia)]|]; split; [exact BK|]; split; [exact TOP|]; split; [exact FRM|]; split; [exact SHD|];
      split; [exact R1|]; split; [exact R2| exact RSW] ]
  end.

Theorem AHU_stack_malloc_0 : smU_stmt 0 64 16384 ASTKMALLOC0.
Proof. unfold smU_stmt. smU_arm_A @stack_malloc_0_GA. smU_arm_B @stack_malloc_0_GB. Qed.
Theorem AHU_stack_malloc_1 : smU_stmt 1 128 8192 ASTKMALLOC1.
Proof. unfold smU_stmt. smU_arm_A @stack_malloc_1_GA. smU_arm_B @stack_malloc_1_GB. Qed.
Theorem AHU_stack_malloc_2 : smU_stmt 2 256 4096 ASTKMALLOC2.
Proof. unfold smU_stmt. smU_arm_A @stack_malloc_2_GA. smU_arm_B @stack_malloc_2_GB. Qed.

Definition hnrU_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AHEAPu L RNG st LB m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr aci_I LB (bv_unsigned sp) a ->
          ~ (shad (hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None))
    /\ rw_cells bsegs m' (shad (hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - hnr_bottom sp))))].

Theorem AHU_hnr : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAPu L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HNR_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m (shad (hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  rng RNG (shad (hnr_bottom sp)) (shlen (al_top L - hnr_bottom sp)) ->
  evtF bsegs RNG (hnrU_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHNR) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros [g AH] MI ST BOT LO SPT TP SHW RSTK RIMG FRNG RSH.
  eapply evtF_mono.
  - eapply (hnr_P adepot_iface AQUAR ASEC_of g (AH_laws (gb:=g)) aci_I aci_ok1); eassumption.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & AH' & PR & Z0).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists true; exact AH'|]. split; [exact PR| exact Z0].
Qed.

Theorem AHU_fake_release : forall L RNG st LB m c F n,
  AHEAPu L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  AHEAPu L RNG st (fk_rel c F LB) (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m c F n [g AH] Hb. exists g.
  exact (fake_release_G (gb:=g) adepot_iface AQUAR ASEC_of (AH_laws (gb:=g)) L RNG st LB m c F n AH Hb).
Qed.

Lemma fflagU_facts : forall L RNG st LB m c F n, AHEAPu L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  al_fake L + 4096 <= fflag L c F < al_fake L + 36864 /\ al_fake L + 36864 <= F /\ wr_at bsegs m (fflag L c F) 1.
Proof.
  intros L RNG st LB m c F n [g AH] Hb. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LB m c F n HFK Hb) as (C0 & EN & NP & F64 & FLO & FHI & BK & TOP & pos & Hp & HF & EF & FR).
  split; [exact FR|]. split; [exact FLO|].
  destruct HFK as (G & _ & _ & _ & _ & DC1 & _).
  assert (DCW : forall A k, dc_at m A k -> 0 <= k -> wr_at bsegs m A k).
  { intros A k [bs H] Hk. apply (rw_cells_wr_at bsegs m A _ k H). cbn [cells_size csize Nat.add]. lia. }
  apply DCW; [| lia]. apply (dc_sub m (al_fake L + 4096) (11571200 - 4096)); [exact DC1| lia| lia| lia].
Qed.

Lemma fakeU_obj : forall L RNG st LB m, AHEAPu L RNG st LB m -> ablk (al_fake L) (al_fake L + 11571200).
Proof.
  intros L RNG st LB m [g AH]. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct HFK as (G & _). destruct G as (G1 & G2 & _). exact G2.
Qed.
Lemma fakeU_frame_lo : forall L RNG st LB m c F n, AHEAPu L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  al_fake L + 36864 <= F /\ F + n <= al_fake L + 11571200 /\ n = fk_fsize c /\ 0 <= c.
Proof.
  intros L RNG st LB m c F n [g AH] Hb. destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LB m c F n HFK Hb) as (C0 & EN & NP & F64 & FLO & FHI & _). unfold FAKESZ in FHI. repeat split; [exact FLO| exact FHI| exact EN| lia].
Qed.
Lemma heapU_off_fake : forall L RNG st LB m p A n, AHEAPu L RNG st LB m -> In (HB p A n) LB ->
  A + n <= al_fake L \/ al_fake L + 11571200 <= A.
Proof. intros L RNG st LB m p A n [g AH] Hb. exact (AHEAP_P_hb_fake _ L RNG st LB m p A n AH Hb). Qed.
End CANSEC1.
End TwinB.
