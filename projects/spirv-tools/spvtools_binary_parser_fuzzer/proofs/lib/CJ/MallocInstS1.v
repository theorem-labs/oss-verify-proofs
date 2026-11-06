(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes NodesMM NodesInv Decode Arr MState Mem Cells Frame Exec RegsEquiv ImplEqv ImplBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require PropExec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog MSafe KInv KLink KLinkC MI_Cnt LB_Sum LB_Logic LB_Kernel LB_Inv LB_StmtA LB_Raw LB_Alloc LB_Count MPos Path PathQ PathCfg PathQCfg CtxMono MFail MRefuse.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocBlocks MallocHINV Malloc_iface MallocFacts_A MTight.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require Import RMallocRep RImage RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec RBridge.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim ShapeAlg SRealizes ShapeUpto SeqExec Hoare RefMemcpyLib LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Instance mng_auxv_off : auxv_mode := AuxvMode False.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Record mstateA : Type := MKA {
  a_s : PState;
  a_LB : list block;
  a_P : Z -> Z;
  a_big : Z
}.

Definition a_live (A : mstateA) : list (Z * Z) := map (fun b => (blk_addr b, blk_size b)) (a_LB A).
Definition a_X (A : mstateA) : list (bptr * Z) := map (fun b => (blk_id b, blk_size b)) (a_LB A).

Definition BIGUNIT : Z := mng_round_big MNG_BIG.
Definition a_PL (A : mstateA) : Z -> Z := fun c => if c =? 63 then a_big A / BIGUNIT + 1 else a_P A c.

Definition a_owned (A : mstateA) (a : Z) : Prop := rowned (a_LB A) a.

Definition a_room (A : mstateA) (n : Z) : Prop :=
  (0 <= n < MNG_BIG /\
   count_class_f mng_size_class MNG_BIG (a_live A) (mng_size_class n) + 1 <= a_P A (mng_size_class n) /\
   count_class_f mng_size_class MNG_BIG (a_live A) (mng_size_class n + 1) + 1 <= a_P A (mng_size_class n + 1))
  \/ (MNG_BIG <= n <= MNG_NMAX /\ big_bytes_f mng_round_big MNG_BIG (a_live A) + mng_round_big n <= a_big A).

Definition caps_ok (PL : Z -> Z) (big : Z) (NR RBY : Z) : Prop :=
  exists SMAX ETOT,
    0 <= SMAX /\ 0 <= NR /\ 0 <= RBY /\ 0 <= big
    /\ NMETA PL <= SMAX /\ NE PL + Z.of_nat (MALLOC_DEPTH + 0) <= ETOT
    /\ (forall n, 0 <= n <= MNG_NMAX -> GAPOK n SMAX ETOT NR RBY)
    /\ PHI PL + big + BIGUNIT <= LBUDGET
    /\ (forall c, 0 <= PL c).

Definition kpart (s : PState) (X : list (bptr * Z)) (PL : Z -> Z) (NR RBY : Z) (h : VmMaps) : Prop :=
  (forall mo, m_vmmaps mo = h -> mstd' mo -> OWN (map fst X) GT s mo /\ QI X PL s mo)
  /\ LBUDGET <= vm_limit h /\ RSV NR RBY h.

Definition in_gotb (a : word) : bool := (RGOT_SSP <=? bv_unsigned a) && (bv_unsigned a <? RGOT_SSP + 8).
Definition got_clear (M : LibIface.mem) : LibIface.mem := fun a => if in_gotb a then None else M a.

Definition a_inv (A : mstateA) (M : LibIface.mem) (mo : Model) : Prop :=
  RHEAP (a_s A) (a_LB A) (got_clear M)
  /\ c_init_done (ctx (ps_m (a_s A))) = 1
  /\ m_vm_lazy mo = []
  /\ exists NR RBY, kpart (a_s A) (a_X A) (a_PL A) NR RBY (m_vmmaps mo) /\ caps_ok (a_PL A) (a_big A) NR RBY.

Definition a_invX (A : mstateA) (M : LibIface.mem) (mo : Model) : Prop :=
  RHEAP (a_s A) (a_LB A) (got_clear M)
  /\ m_vm_lazy mo = []
  /\ exists NR RBY, kpart (a_s A) (a_X A) (a_PL A) NR RBY (m_vmmaps mo) /\ caps_ok (a_PL A) (a_big A) NR RBY.

Lemma a_inv_X A M mo : a_inv A M mo -> a_invX A M mo /\ c_init_done (ctx (ps_m (a_s A))) = 1.
Proof. intros (H1 & H2 & H3 & H4). repeat split; assumption. Qed.

Definition mng_static_cells : list (Z * list Z) :=
  [(RNEED_LOCKS, [0]); (RSSP_GUARD, map bv_unsigned (le8 (wz rr_canary))); (RPAGE_SIZE, [0;16;0;0;0;0;0;0])].

Definition a_may_fail (A : mstateA) (n : Z) : Prop := MNG_BIG <= n \/ refuses (a_s A) n \/ refuses_small (ps_m (a_s A)) n.

Lemma L_big_pos : 0 < MNG_BIG <= MNG_NMAX.
Proof. unfold MNG_BIG, MNG_NMAX, LIB_NMAX. lia. Qed.

Lemma L_nmax_bound : MNG_NMAX < 2 ^ 40.
Proof. unfold MNG_NMAX, LIB_NMAX. lia. Qed.

Lemma mng_round_up_pg_spec x : x <= mng_round_up_pg x < x + 4096 /\ mng_round_up_pg x mod 4096 = 0.
Proof.
  unfold mng_round_up_pg, MNG_PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  change 4096 with (2 ^ 12). Z.div_mod_to_equations. nia.
Qed.

Lemma L_round_big_mono : forall n m, 0 <= n <= m -> mng_round_big n <= mng_round_big m.
Proof.
  intros n m H. unfold mng_round_big. pose proof (mng_round_up_pg_spec (n + MNG_IB + MNG_UNIT)). pose proof (mng_round_up_pg_spec (m + MNG_IB + MNG_UNIT)).
  Z.div_mod_to_equations. nia.
Qed.

Lemma L_round_big_nonneg : forall n, 0 <= n -> 0 <= mng_round_big n.
Proof. intros n H. unfold mng_round_big. pose proof (mng_round_up_pg_spec (n + MNG_IB + MNG_UNIT)). unfold MNG_IB, MNG_UNIT in *. lia. Qed.

Lemma mng_size_class_eq n : mng_size_class n = size_to_class n.
Proof. reflexivity. Qed.

Lemma L_size_class_range : forall n, 0 <= n < MNG_BIG -> 0 <= mng_size_class n < 63.
Proof.
  intros n Hn. rewrite mng_size_class_eq. pose proof (size_to_class_ok n ltac:(unfold MNG_BIG, MMAP_THRESHOLD in *; lia)). lia.
Qed.

Lemma L_room_small : forall A M mo n, a_inv A M mo -> 0 <= n < MNG_BIG ->
  count_class_f mng_size_class MNG_BIG (a_live A) (mng_size_class n) + 1 <= a_P A (mng_size_class n) ->
  count_class_f mng_size_class MNG_BIG (a_live A) (mng_size_class n + 1) + 1 <= a_P A (mng_size_class n + 1) ->
  a_room A n.
Proof. intros A M mo n _ Hn H1 H2. left. auto. Qed.

Lemma L_room_big : forall A M mo n, a_inv A M mo -> MNG_BIG <= n <= MNG_NMAX ->
  big_bytes_f mng_round_big MNG_BIG (a_live A) + mng_round_big n <= a_big A -> a_room A n.
Proof. intros A M mo n _ Hn H. right. auto. Qed.

Lemma L_mstd : forall A M mo, a_inv A M mo -> m_vm_lazy mo = [].
Proof. intros A M mo (_ & _ & H & _). exact H. Qed.

Lemma in_live_block A p n : In (p, n) (a_live A) -> exists b, In b (a_LB A) /\ blk_addr b = p /\ blk_size b = n.
Proof. unfold a_live. intros H. apply in_map_iff in H. destruct H as (b & E & Hb). exists b. inversion E; subst. auto. Qed.

Lemma got_clear_off (M : LibIface.mem) (a : word) : ~ (RGOT_SSP <= bv_unsigned a < RGOT_SSP + 8) -> got_clear M a = M a.
Proof.
  intros H. unfold got_clear, in_gotb. destruct (Z.leb_spec RGOT_SSP (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) (RGOT_SSP + 8)); cbn; try reflexivity. lia.
Qed.
Lemma got_clear_on (M : LibIface.mem) (a : word) : RGOT_SSP <= bv_unsigned a < RGOT_SSP + 8 -> got_clear M a = None.
Proof.
  intros H. unfold got_clear, in_gotb. destruct (Z.leb_spec RGOT_SSP (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) (RGOT_SSP + 8)); cbn; try reflexivity; lia.
Qed.

Lemma in_ranges_img a : in_ranges (ly_img L) a <-> RIMG_LO <= a < RIMG_HI.
Proof.
  unfold in_ranges, RIMG_LO, RIMG_HI. cbn. split.
  - intros (lo & hi & [E|[]] & H). injection E as <- <-. exact H.
  - intros H. exists 0x10000, 0x122000. auto.
Qed.
Lemma in_ranges_rw a : in_ranges (ly_rw L) a <-> RRW_LO <= a < RIMG_HI.
Proof.
  unfold in_ranges, RRW_LO, RIMG_HI. cbn. split.
  - intros (lo & hi & [E|[]] & H). injection E as <- <-. exact H.
  - intros H. exists 0xee000, 0x122000. auto.
Qed.

Lemma L_live_block : forall A M mo p n, a_inv A M mo -> In (p, n) (a_live A) ->
  0 <= n /\ p mod 16 = 0 /\ 0 < p /\ p + n <= alloc_ceiling
  /\ (forall a, p <= a < p + n -> ~ a_owned A a /\ ~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) <> None).
Proof.
  intros A M mo p n (HH & _) Hin. destruct (in_live_block A p n Hin) as (b & Hb & <- & <-).
  destruct (RHEAP_block_range _ _ _ b HH Hb) as (P1 & P2 & P3 & P4 & P5).
  repeat split; try lia.
  - intros [ST|(_ & _ & NB)].
    + pose proof (mng_static_img a ST). unfold RRW_LO, RIMG_LO, RIMG_HI in *. lia.
    + apply NB. exists b. split; [exact Hb| lia].
  - rewrite in_ranges_img. lia.
  - pose proof (RHEAP_block_bytes _ _ _ b a HH Hb ltac:(lia)) as X. unfold wa in X.
    rewrite got_clear_off in X; [exact X|]. rewrite unsigned_lit by (pose proof ac_bounds_lit as ?ACBL; lia).
    unfold RGOT_SSP, RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma L_live_nodup : forall A M mo, a_inv A M mo -> List.NoDup (map fst (a_live A)).
Proof.
  intros A M mo (HH & _). unfold a_live. rewrite map_map. cbn [fst]. exact (RHEAP_addr_nodup _ _ _ HH).
Qed.

Lemma L_live_disjoint : forall A M mo p n q k, a_inv A M mo ->
  In (p, n) (a_live A) -> In (q, k) (a_live A) -> p <> q -> p + n <= q \/ q + k <= p.
Proof.
  intros A M mo p n q k (HH & _) H1 H2 NE.
  destruct (in_live_block A p n H1) as (b1 & Hb1 & <- & <-). destruct (in_live_block A q k H2) as (b2 & Hb2 & <- & <-).
  exact (RHEAP_blocks_disjoint _ _ _ b1 b2 HH Hb1 Hb2 NE).
Qed.

Lemma L_owned_not_img_ro : forall A M mo a, a_inv A M mo -> a_owned A a -> in_ranges (ly_rw L) a \/ ~ in_ranges (ly_img L) a.
Proof.
  intros A M mo a _ [ST|(OFF & _ & _)].
  - left. rewrite in_ranges_rw. exact (mng_static_img a ST).
  - right. rewrite in_ranges_img. lia.
Qed.

Lemma L_owned_below_ceiling : forall A M mo a, a_inv A M mo -> a_owned A a -> ~ in_ranges (ly_img L) a -> 0 < a < alloc_ceiling.
Proof.
  intros A M mo a _ [ST|(OFF & R & _)] NI; [| exact R].
  exfalso. apply NI. rewrite in_ranges_img. pose proof (mng_static_img a ST). unfold RRW_LO, RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma L_frame : forall A M M' mo mo', a_inv A M mo ->
  (forall a : word, a_owned A (bv_unsigned a) -> M' a = M a) ->
  (forall a : word, M a <> None -> M' a <> None) ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> a_inv A M' mo'.
Proof.
  intros A M M' mo mo' (HH & HI & HL & HK) OW DEF EV EL. split; [| split; [exact HI| split; [rewrite EL; exact HL| rewrite EV; exact HK]]].
  apply (RHEAP_frame_pw _ _ (got_clear M) (got_clear M') HH).
  - intros a Ha. unfold got_clear. destruct (in_gotb (wa a)); [reflexivity|]. apply OW.
    unfold wa. rewrite unsigned_lit; [exact Ha|]. destruct Ha as [ST|(_ & R & _)]; [pose proof (mng_static_img a ST); unfold RRW_LO, RIMG_HI in *; lia| pose proof ac_bounds_lit as ?ACBL; lia].
  - intros a Ha. apply got_clear_on. exact Ha.
  - apply wmono_of_def. intros a. unfold got_clear. destruct (in_gotb a); [auto| apply DEF].
Qed.

Lemma wa_add_Z : forall (a : word) i, 0 <= i -> (a + Z_to_bv 64 i)%bv = wa (bv_unsigned a + i).
Proof. intros a i Hi. rewrite <- (Z2Nat.id i) at 1 2 by lia. apply wa_add_nat. Qed.

Lemma rdn_ext_range segs (m m' : LibIface.mem) : forall n (a : word),
  (forall i, 0 <= i < Z.of_nat n -> m' (a + Z_to_bv 64 i)%bv = m (a + Z_to_bv 64 i)%bv) ->
  rdn segs m' a n = rdn segs m a n.
Proof.
  induction n as [|n IH]; intros a H; [reflexivity|]. cbn [rdn].
  pose proof (H 0 ltac:(lia)) as H0.
  replace (bv_add a (Z_to_bv 64 0)) with a in H0 by (rewrite wa_add_Z by lia; rewrite Z.add_0_r; unfold wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  rewrite H0. rewrite (IH (bv_add a (Z_to_bv 64 1))); [reflexivity|].
  intros i Hi. specialize (H (i + 1) ltac:(lia)).
  replace (bv_add (bv_add a (Z_to_bv 64 1)) (Z_to_bv 64 i)) with (bv_add a (Z_to_bv 64 (i + 1))); [exact H|].
  rewrite !wa_add_Z by lia. unfold wa. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma bytes_eq_of_unsigned : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma L_static_cells : forall A M mo a bs, a_inv A M mo -> In (a, bs) mng_static_cells ->
  rdn SEGS M (Z_to_bv 64 a) (length bs) = Some (map (Z_to_bv 8) bs).
Proof.
  intros A M mo a bs ((st & LB0 & _ & _ & MR & _) & _) Hin.
  pose proof MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  assert (RD : forall A0 c, rw_cells rsegs (got_clear M) A0 [c] -> 0 <= A0 -> A0 + Z.of_nat (csize c) <= RIMG_HI ->
               (A0 + Z.of_nat (csize c) <= RGOT_SSP \/ RGOT_SSP + 8 <= A0) ->
               rdn SEGS M (Z_to_bv 64 A0) (csize c) = Some (cbytes c)).
  { intros A0 c RW HA0 HA1 HA2. rewrite <- PropExec.ov_rdn. change SEGS with rsegs.
    pose proof (rw_cells_read rsegs (got_clear M) A0 [c] 0 c RW eq_refl) as X. rewrite Z.add_0_r in X. unfold wa in X.
    rewrite CJ.Lib.PropExec.ov_rdn in X |- *. rewrite <- X. symmetry. apply rdn_ext_range.
    intros i Hi. apply got_clear_off. rewrite wa_add_Z by lia. unfold wa. unfold RIMG_HI in HA1.
    rewrite (unsigned_lit A0) by lia. rewrite unsigned_lit by lia. lia. }
  assert (HG : rdn SEGS M (Z_to_bv 64 RSSP_GUARD) (length (map bv_unsigned (le8 (wz rr_canary))))
               = Some (map (Z_to_bv 8) (map bv_unsigned (le8 (wz rr_canary))))).
  { rewrite length_map, length_le8, map_map. rewrite (map_ext _ (fun x => x)) by (intros x; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range). rewrite map_id.
    exact (RD RSSP_GUARD (C8 (wz rr_canary)) G5 ltac:(unfold RSSP_GUARD; lia) ltac:(unfold RSSP_GUARD, RIMG_HI; cbn; lia) ltac:(unfold RSSP_GUARD, RGOT_SSP; cbn; lia)). }
  unfold mng_static_cells in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
  - exact (RD RNEED_LOCKS (C1 (b8 0)) G2 ltac:(unfold RNEED_LOCKS; lia) ltac:(unfold RNEED_LOCKS, RIMG_HI; cbn; lia) ltac:(unfold RNEED_LOCKS, RGOT_SSP; cbn; lia)).
  - exact HG.
  - rewrite (RD RPAGE_SIZE (C8 (wz 4096)) G3 ltac:(unfold RPAGE_SIZE; lia) ltac:(unfold RPAGE_SIZE, RIMG_HI; cbn; lia) ltac:(unfold RPAGE_SIZE, RGOT_SSP; cbn; lia)).
    f_equal. apply bytes_eq_of_unsigned. vm_compute. reflexivity.
Qed.

Lemma L_static_cells_owned : forall A M mo a bs i, a_inv A M mo -> In (a, bs) mng_static_cells ->
  0 <= i < Z.of_nat (length bs) -> a_owned A (a + i).
Proof.
  intros A M mo a bs i _ Hin Hi. left. unfold mng_static.
  unfold mng_static_cells in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; rewrite ?length_map, ?length_le8 in Hi; cbn in Hi; lia.
Qed.

Lemma img_ro_clear_num (M : LibIface.mem) : img_ro_clear L M ->
  forall w : word, RIMG_LO <= bv_unsigned w < RIMG_HI -> ~ (RRW_LO <= bv_unsigned w < RIMG_HI) -> M w = None.
Proof. intros H w H1 H2. apply H; [rewrite in_ranges_img; exact H1| rewrite in_ranges_rw; exact H2]. Qed.

Lemma got_clear_id (M : LibIface.mem) : img_ro_clear L M -> forall a, got_clear M a = M a.
Proof.
  intros H a. unfold got_clear. destruct (in_gotb a) eqn:E; [| reflexivity].
  unfold in_gotb in E. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  symmetry. apply (img_ro_clear_num M H); unfold RGOT_SSP, RIMG_LO, RIMG_HI, RRW_LO in *; lia.
Qed.

Lemma a_invX_call A M mo : a_invX A M mo -> mstd mo -> img_ro_clear L M ->
  RHEAP (a_s A) (a_LB A) M /\ mem_inv rsegs M
  /\ exists NR RBY, OWN (map fst (a_X A)) GT (a_s A) mo /\ QI (a_X A) (a_PL A) (a_s A) mo
     /\ LBUDGET <= vm_limit (m_vmmaps mo) /\ RSV NR RBY (m_vmmaps mo) /\ caps_ok (a_PL A) (a_big A) NR RBY.
Proof.
  intros (HH & HL & (NR & RBY & (KP & LIM & HR) & CO)) [Hh Hl Hm Hc] RO.
  split; [| split].
  - apply (RHEAP_frame_pw _ _ (got_clear M) M HH).
    + intros a _. symmetry. apply got_clear_id. exact RO.
    + intros a Ha. apply (img_ro_clear_num M RO); unfold RGOT_SSP, RIMG_LO, RIMG_HI, RRW_LO in *; lia.
    + intros x. unfold wview. rewrite (got_clear_id M RO). exact (fun H => H).
  - apply mem_inv_of_clear. apply img_ro_clear_num. exact RO.
  - exists NR, RBY. destruct (KP mo eq_refl ltac:(split; [exact Hh| split; [exact Hl| split; [exact Hm| exact Hc]]])) as [HO HQ]. auto 10.
Qed.

Lemma a_inv_call A M mo : a_inv A M mo -> mstd mo -> img_ro_clear L M ->
  RHEAP (a_s A) (a_LB A) M /\ c_init_done (ctx (ps_m (a_s A))) = 1 /\ mem_inv rsegs M
  /\ exists NR RBY, OWN (map fst (a_X A)) GT (a_s A) mo /\ QI (a_X A) (a_PL A) (a_s A) mo
     /\ LBUDGET <= vm_limit (m_vmmaps mo) /\ RSV NR RBY (m_vmmaps mo) /\ caps_ok (a_PL A) (a_big A) NR RBY.
Proof.
  intros AI SM RO. destruct (a_inv_X A M mo AI) as [AX HI]. destruct (a_invX_call A M mo AX SM RO) as (H1 & H2 & H3). auto.
Qed.

Lemma twf_twl_conj {R} B : forall (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf t mo P -> twl B t mo Q -> twf t mo (fun r mo' => P r mo' /\ Q r mo').
Proof.
  induction t as [r|n k IH]; intros mo P Q HT HL; cbn in *.
  - auto.
  - destruct HT as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hn. apply IH; [eapply Hk; exact Hn|]. apply (proj2 (HL rsp mo' evs Hn)).
Qed.

Lemma raw_free_tpath_elim p s mo u s'' mo' :
  tpath nstep (raw_free p s) mo [] (Exc.Ok (u, s'')) mo' ->
  exists cs' s', tpath nstep (membed (cfree (ps_m s) (Some (fst p))) s) mo [] (Exc.Ok (cs', s')) mo' /\ s'' = set_m cs' s'.
Proof.
  intros Hp. unfold raw_free, mbind, mget in Hp. rewrite ebind_ret_ok in Hp. cbn [fst snd] in Hp.
  apply (proj1 (tpath_ebind _ _ _ _ _ _ _ _)) in Hp. destruct Hp as [[_ E]|(tr1 & [cs' s'] & mo1 & tr2 & H1 & H2 & Etr)]; [discriminate E|].
  destruct tr1; [| discriminate Etr]. destruct tr2; [| discriminate Etr]. cbn in H2. destruct H2 as (E1 & -> & _).
  exists cs', s'. split; [exact H1|]. inversion E1; subst. reflexivity.
Qed.

Lemma ret_pc_of_ret_ok ret : 0 <= ret < 2 ^ 64 -> ret_ok (Z_to_bv 64 ret) -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret.
Proof.
  intros Hr RK. apply ret_pc_even; [exact Hr|].
  unfold ret_ok, v_jalr, jalr_tgtZ in RK. apply (f_equal bv_unsigned) in RK. rewrite (unsigned_lit ret) in RK by lia.
  rewrite Z.add_0_r in RK. rewrite Z_to_bv_unsigned in RK.
  assert (E : Z.testbit (bv_wrap 64 (Z.land ret (-2))) 0 = Z.testbit ret 0) by (rewrite RK; reflexivity).
  unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E. rewrite <- Z.land_ones in E by lia.
  rewrite Z.land_spec, Z.land_spec in E. change (Z.testbit (-2) 0) with false in E. rewrite andb_false_r in E. cbn [andb] in E.
  rewrite Z.bit0_odd in E. rewrite Zmod_odd. rewrite <- E. reflexivity.
Qed.

Lemma mkst_MS (fx : FPState) R pc M : @mkst fx R pc M (seg_rom SEGS) = MS R (@fp_regs fx) pc (@fp_csr fx) None M (CJ.Lib.PropExec.seg_rom rsegs).
Proof. reflexivity. Qed.

Lemma getr_reg_get R (k : reg) : is_x0 k = false -> getr R k = reg_get R k.
Proof. intros Hk. unfold getr. rewrite CJ.Lib.PropExec.bv_eqb0_is_x0, Hk. reflexivity. Qed.

Lemma leaf_state (fx : FPState) R (x y : machine_state) R' pc' m' :
  ms_eqv y x -> y = MS R' (@fp_regs fx) pc' (@fp_csr fx) None m' (CJ.Lib.PropExec.seg_rom rsegs) ->
  (forall k : reg, In k callee_saved -> reg_get R' k = getr R k) ->
  x = @mkst fx (ms_regs x) pc' m' (seg_rom SEGS) /\ kept R (ms_regs x) /\ (forall k, is_x0 k = false -> getr (ms_regs x) k = reg_get R' k).
Proof.
  intros EQ -> CS. destruct x as [xr xf xpc xsvc xrv xfc xm xro]. destruct EQ as (ER & EF & EP & ES & EV & EC & EM & EO). cbn in *. subst.
  split; [reflexivity|]. split.
  - intros k Hk. assert (NZ : is_x0 k = false) by (cbn in Hk; destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; reflexivity).
    rewrite (getr_reg_get xr k NZ), <- (ER k NZ). apply CS. exact Hk.
  - intros k Hk. rewrite (getr_reg_get xr k Hk). symmetry. apply ER. exact Hk.
Qed.

Lemma twf_with_path {R} : forall (t : itree node R) mo (P : R -> Model -> Prop),
  twf t mo P -> twf t mo (fun r mo' => P r mo' /\ tpath nstep t mo [] r mo').
Proof.
  induction t as [r|n k IH]; intros mo P HT; cbn in HT |- *.
  - split; [exact HT| auto].
  - destruct HT as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hn.
    pose proof (nstep_evs_nil _ _ _ _ _ Hn) as ->.
    eapply twf_mono; [apply IH; eapply Hk; exact Hn|]. cbn beta. intros r mo1 [HP Hp]. split; [exact HP|].
    exists rsp, mo', [], []. auto.
Qed.

Lemma OWN_G_switch X G G' s mo : OWN X G s mo -> G' s mo -> OWN X G' s mo.
Proof. intros [A [B _]] HG. split; [exact A| split; [exact B| exact HG]]. Qed.

Definition GV (mo0 : Model) : PState -> Model -> Prop := fun _ mo => vm_only mo0 mo.
Lemma frame_ok_GV mo0 : frame_ok (GV mo0).
Proof. intros s s' mo mo' _ _ V H. unfold GV in *. eapply vm_only_trans; [exact H| exact V]. Qed.

Lemma kpart_intro s X PL NR RBY mo :
  OWN (map fst X) GT s mo -> QI X PL s mo -> LBUDGET <= vm_limit (m_vmmaps mo) -> RSV NR RBY (m_vmmaps mo) ->
  kpart s X PL NR RBY (m_vmmaps mo).
Proof.
  intros HO HQ LIM HR. split; [| split; [exact LIM| exact HR]].
  intros mo' EV (Hh & Hl & Hm & _).
  assert (KT : forall L pbrk, KL L pbrk mo -> KL L pbrk mo').
  { intros L0 pbrk HK. apply (KL_vm_eq L0 pbrk mo mo' HK); [split; assumption| exact Hh| rewrite EV; reflexivity ..]. }
  split.
  - destruct HO as [(L0 & HC & HK & HI) [ND _]]. split; [| split; [exact ND| exact I]]. exists L0. split; [exact HC|]. split; [apply KT; exact HK| exact HI].
  - destruct HQ as [(st & L0 & BL & LS & E & INV & SI & HAQ & HK & HLI & HP) HB]. split; [| exact HB].
    exists st, L0, BL, LS. repeat (split; [assumption|]). split; [apply KT; exact HK|]. split; [| exact HP].
    destruct HLI as [L1 L2]. split; [rewrite EV; exact L1| unfold nmaps in *; rewrite EV; exact L2].
Qed.

Theorem L_free_gen (LP : mstate -> Prop) : forall (fx : FPState) (A : mstateA) R M mo (p n sp ret : Z) (K : TSet),
  a_inv A M mo -> mstd mo -> img_ro_clear L M ->
  call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
  (p = 0 /\ n = 0 \/ In (p, n) (a_live A)) ->
  alloc_ceiling + MNG_MALLOC_STACK <= sp ->
  stack_room SEGS M sp MNG_MALLOC_STACK ->
  (forall a, zwin (sp - MNG_MALLOC_STACK) sp a -> ~ a_owned A a) ->
  LP (ps_m (a_s A)) ->
  (forall slot g idx, (s_slots (ps_m (a_s A))) !! slot = Some (g, idx) -> lall LP (cfree (ps_m (a_s A)) (Some slot))) ->
  (forall A' R' M' mo', a_inv A' M' mo' -> LP (ps_m (a_s A')) -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
      kept R R' -> live_del p (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
      (forall a, a_owned A' a -> a_owned A a \/ (p <= a < p + n)) ->
      frame_eq (fun a => a_owned A a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
      (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win L (bv_unsigned a)) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mo') K) ->
  srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (ly_free L)) M (seg_rom SEGS)) mo) K.
Proof.
  intros fx A R M mo p n sp ret K AI SM RO CR A0 HP SPC SR SOW LP0 HLP HK.
  pose proof (a_inv_call A M mo AI SM RO) as (HH & INIT & MI & NR & RBY & HO & HQ & LIM & HRSV & CO).
  destruct CR as [Cra Cret Cretr Csp Csp16 Csphi Cgp Ctp]. pose proof SM as [Sh Sl Sm Sc].
  pose proof SPC as SP0. unfold MNG_MALLOC_STACK in SP0; pose proof ac_bounds_lit as ?ACBL.
  rewrite (getr_reg_get R 1%bv eq_refl) in Cra. rewrite (getr_reg_get R 2%bv eq_refl) in Csp. rewrite (getr_reg_get R 3%bv eq_refl) in Cgp.
  rewrite (getr_reg_get R 4%bv eq_refl) in Ctp. rewrite (getr_reg_get R 10%bv eq_refl) in A0. cbn [ly_tp ly_gp L] in Ctp, Cgp.
  destruct HP as [[-> ->]|HIN].
  -
    pose proof (rfree_null_spec (reg_get R 1%bv) (reg_get R 2%bv) (reg_get R 3%bv) (reg_get R 4%bv) (reg_get R 5%bv) (reg_get R 6%bv) (reg_get R 7%bv)
      (reg_get R 8%bv) (reg_get R 9%bv) (reg_get R 10%bv) (reg_get R 11%bv) (reg_get R 12%bv) (reg_get R 13%bv) (reg_get R 14%bv) (reg_get R 15%bv)
      (reg_get R 16%bv) (reg_get R 17%bv) (reg_get R 18%bv) (reg_get R 19%bv) (reg_get R 20%bv) (reg_get R 21%bv) (reg_get R 22%bv) (reg_get R 23%bv)
      (reg_get R 24%bv) (reg_get R 25%bv) (reg_get R 26%bv) (reg_get R 27%bv) (reg_get R 28%bv) (reg_get R 29%bv) (reg_get R 30%bv) (reg_get R 31%bv)
      (@fp_regs fx) (@fp_csr fx) M A0) as EV.
    match type of EV with evt _ _ ?ms =>
      assert (EQV : ms_eqv ms (@mkst fx R (Z_to_bv 64 (ly_free L)) M (seg_rom SEGS))) end.
    { rewrite mkst_MS. apply ms_eqv_sym. apply (MS_eqv_mkR R). }
    pose proof (evt_eqv rsegs _ _ _ EQV EV) as EV2. clear EV EQV. cbv beta in EV2.
    apply (srz_evt rsegs _ _ mo K Sh Sl EV2). intros x (y & Ey & EQy).
    destruct (leaf_state fx R x y _ _ M EQy Ey) as (Ex & KEPT & _).
    { intros k Hk. cbn in Hk.
      destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
        first [exact (eq_sym Cra) | exact (eq_sym Csp) | exact (eq_sym Cgp) | exact (eq_sym Ctp) | reflexivity]. }
    rewrite Ex. rewrite Cra, (ret_pc_of_ret_ok ret Cretr Cret).
    apply (HK A (ms_regs x) M mo AI LP0 SM eq_refl eq_refl KEPT).
    + intros q k. split; [| intros [H _]; exact H]. intros H. split; [exact H|].
      destruct (L_live_block A M mo q k AI H) as (_ & _ & P0 & _). lia.
    + reflexivity.
    + reflexivity.
    + intros a Ha. left. exact Ha.
    + intros w _. reflexivity.
    + intros w Hw. left. exact Hw.
  - destruct (in_live_block A p n HIN) as (b & Hb & Ep & En).
    set (lo := sp - MNG_MALLOC_STACK).
    assert (STK : stk rsegs M lo sp).
    { replace sp with (lo + Z.of_nat (Z.to_nat MNG_MALLOC_STACK)) by (subst lo; unfold MNG_MALLOC_STACK; lia).
      apply stk_of_store_ok; [exact SR| subst lo; unfold MNG_MALLOC_STACK in *; lia| subst lo; unfold MNG_MALLOC_STACK; lia| subst lo; unfold RIMG_HI, MNG_MALLOC_STACK in *; lia]. }
    destruct (errno_cell_any M) as [errv ERR].
    destruct b as [[pid pA] pn]. cbn [blk_addr blk_size blk_id fst snd] in Ep, En. subst pA pn.
    pose proof (rfree_spec_proof (reg_get R 1%bv) (reg_get R 2%bv) (reg_get R 3%bv) (reg_get R 4%bv) (reg_get R 5%bv) (reg_get R 6%bv) (reg_get R 7%bv)
      (reg_get R 8%bv) (reg_get R 9%bv) (reg_get R 10%bv) (reg_get R 11%bv) (reg_get R 12%bv) (reg_get R 13%bv) (reg_get R 14%bv) (reg_get R 15%bv)
      (reg_get R 16%bv) (reg_get R 17%bv) (reg_get R 18%bv) (reg_get R 19%bv) (reg_get R 20%bv) (reg_get R 21%bv) (reg_get R 22%bv) (reg_get R 23%bv)
      (reg_get R 24%bv) (reg_get R 25%bv) (reg_get R 26%bv) (reg_get R 27%bv) (reg_get R 28%bv) (reg_get R 29%bv) (reg_get R 30%bv) (reg_get R 31%bv)
      (@fp_regs fx) (@fp_csr fx) M (a_s A) (a_LB A) pid p n lo sp errv HH Hb) as IMPL.
    rewrite Csp, Ctp, A0 in IMPL. rewrite !unsigned_lit in IMPL by (unfold RATP; lia).
    specialize (IMPL ltac:(split; [pose proof ac_bounds_lit as ?ACBL; lia| intros []]) ltac:(lia) STK ltac:(subst lo; unfold MNG_MALLOC_STACK in *; pose proof ac_bounds_lit as ?ACBL; lia)
                     ltac:(subst lo; unfold MNG_MALLOC_STACK, RFREE_STACK; lia)).
    specialize (IMPL ltac:(exact ERR) MI eq_refl eq_refl).

    unfold implM in IMPL.
    match type of IMPL with impl _ _ _ _ ?ms =>
      assert (EQV : ms_eqv ms (@mkst fx R (Z_to_bv 64 (ly_free L)) M (seg_rom SEGS))) end.
    { rewrite mkst_MS. rewrite <- Csp, <- Ctp, <- A0. apply ms_eqv_sym. apply (MS_eqv_mkR R). }
    pose proof (impl_eqv rsegs _ _ _ _ IMPL EQV) as IM2. clear IMPL EQV. cbv beta in IM2.

    set (LB' := lb_remove pid (a_LB A)). set (A' := fun s' => MKA s' LB' (a_P A) (a_big A)).
    pose proof (lb_remove_perm_cons (a_LB A) (pid, p, n) (RHEAP_blocks_nodup_proof _ _ _ HH) Hb) as PERM. cbn [blk_id fst] in PERM. fold LB' in PERM.
    assert (HO' : OWN (pid :: map blk_id LB') (GV mo) (a_s A) mo).
    { eapply OWN_G_switch; [| apply vm_only_refl]. eapply OWN_perm; [| exact HO]. unfold a_X. rewrite map_map. cbn [fst].
      change (pid :: map blk_id LB') with (map blk_id ((pid, p, n) :: LB')). apply Permutation_map. exact PERM. }
    assert (HQ' : QI ((pid, n) :: a_X (A' (a_s A))) (a_PL A) (a_s A) mo).
    { eapply QI_perm; [| exact HQ]. unfold a_X. cbn [a_LB A'].
      change ((pid, n) :: map _ LB') with (map (fun b : block => (blk_id b, blk_size b)) ((pid, p, n) :: LB')). apply Permutation_map. exact PERM. }
    pose proof (raw_free_spec_c (map blk_id LB') (GV mo) pid (frame_ok_GV mo) (a_s A) mo HO') as TW1.
    pose proof (raw_free_LQ (a_X (A' (a_s A))) (a_PL A) pid n (a_s A) mo HQ') as TW2.
    pose proof (twf_with_path _ _ _ (twf_twl_conj LBUDGET _ _ _ _ TW1 TW2)) as TW. clear TW1 TW2. cbv beta in TW.

    match type of IM2 with impl _ _ _ ?Q _ => match type of TW with twf _ _ ?P =>
      assert (LEAF : forall r ms' mo', Q r ms' -> P r mo' -> mstd' mo' -> srealizes SEGS (mkCfg ms' mo') K) end end.
    { intros r ms' mo' HQr HPr SM'. destruct r as [|[[] s'']]; [exact (False_ind _ (proj1 (proj1 HPr)))|].
      cbn [epost fst snd] in HQr. destruct HPr as [[HO2 HQ2] PATH].
      destruct HQr as (y & POST & EQy).
      destruct POST as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & Ey & MI' & ST' & ERR' & AUX' & HPRES & FR & Efa & Eso & RH').

      destruct (raw_free_tpath_elim _ _ _ _ _ _ PATH) as (cs' & s' & PM & Es'').
      destruct (tpath_membed_follow _ _ _ _ _ _ PM) as [ans Hf].
      pose proof (cfree_leaf_rel _ _ _ _ Hf) as [RELi _]. unfold cinit in RELi. cbn [s_ctx] in RELi.
      assert (LPl : LP cs').
      { unfold cfree in Hf |- *. destruct ((s_slots (ps_m (a_s A))) !! (fst pid)) as [[g0 idx0]|] eqn:ESL; [| cbn in Hf; discriminate Hf].
        specialize (HLP (fst pid) g0 idx0 ESL). unfold cfree in HLP. rewrite ESL in HLP. exact (lall_follow _ _ _ _ HLP Hf). }
      pose proof (tpath_vm_const _ _ _ _ _ PATH) as [VL VR].

      destruct (leaf_state fx R ms' y _ _ m' EQy Ey) as (Ems' & KEPT & REGS).
      { intros k Hk. cbn in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
          first [exact (eq_sym Cra) | exact (eq_sym Csp) | exact (eq_sym Cgp) | exact (eq_sym Ctp) | reflexivity]. }
      rewrite Ems'. rewrite Cra, (ret_pc_of_ret_ok ret Cretr Cret).
      rewrite !unsigned_lit in ST', FR, HPRES by lia.
      assert (NDid : List.NoDup (map blk_id (a_LB A))) by exact (RHEAP_blocks_nodup_proof _ _ _ HH).

      assert (IDP : forall b', In b' (a_LB A) -> blk_id b' = pid -> b' = (pid, p, n)).
      { intros b' Hb' E. apply (nodup_map_inj blk_id (a_LB A) b' (pid, p, n) NDid Hb' Hb). exact E. }
      assert (ADP : forall b', In b' (a_LB A) -> blk_addr b' = p -> b' = (pid, p, n)).
      { intros b' Hb' E. apply (RHEAP_block_addr_inj _ _ _ b' (pid, p, n) HH Hb' Hb). exact E. }
      assert (OWN' : forall a, rowned LB' a -> rowned (a_LB A) a \/ p <= a < p + n).
      { intros a [ST|(O1 & O2 & O3)]; [left; left; exact ST|].
        destruct (in_blockb (a_LB A) a) eqn:IB.
        - apply in_blockb_spec in IB. destruct IB as (b' & Hb' & Hab). right.
          destruct (bptr_eqb (blk_id b') pid) eqn:E.
          + apply bptr_eqb_eq in E. rewrite (IDP b' Hb' E) in Hab. cbn in Hab. exact Hab.
          + exfalso. apply O3. exists b'. split; [| exact Hab]. apply In_lb_remove. split; [exact Hb'|]. intros E'. rewrite E', (proj2 (bptr_eqb_eq _ _) eq_refl) in E. discriminate.
        - left. right. split; [exact O1|]. split; [exact O2|]. intros IBP. apply in_blockb_spec in IBP. congruence. }
      apply (HK (A' s'') (ms_regs ms') m' mo').
      -   split; [| split; [| split]].
        + cbn [a_s a_LB A']. apply (RHEAP_frame_pw _ _ m' (got_clear m') RH').
          * intros a Ha. apply got_clear_off. unfold wa.
            destruct Ha as [ST|(O1 & O2 & _)]; [pose proof (mng_static_img a ST)|]; rewrite unsigned_lit by (unfold RRW_LO, RIMG_HI in *; pose proof ac_bounds_lit as ?ACBL; lia);
              unfold RGOT_SSP, RRW_LO, RIMG_LO, RIMG_HI in *; lia.
          * intros a Ha. apply got_clear_on. exact Ha.
          * intros x Hx. unfold wview in Hx |- *. unfold got_clear. destruct (in_gotb x) eqn:E; [| exact Hx].
            unfold in_gotb in E. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
            pose proof (got_wview_any (fun _ => None) (bv_unsigned x) ltac:(lia)) as G. unfold wview, wa in G. rewrite Z_to_bv_bv_unsigned in G. exact G.
        + cbn [a_s A']. rewrite Es''. cbn [ps_m set_m]. unfold ctx in *. lia.
        + destruct SM' as (_ & Sl' & _). exact Sl'.
        + exists NR, RBY. split; [| exact CO]. cbn [a_s a_X a_PL a_big A'].
          apply kpart_intro.
          * eapply OWN_G_switch; [| exact I]. unfold a_X. cbn [a_LB]. rewrite map_map. cbn [fst]. exact HO2.
          * exact HQ2.
          * rewrite VL. exact LIM.
          * unfold RSV in *. rewrite VR. exact HRSV.
      - cbn [a_s A']. rewrite Es''. exact LPl.
      - destruct SM' as (Sh' & Sl' & Sm' & Sc'). split; assumption.
      - apply vm_only_fs. exact (OWN_G _ _ _ _ HO2).
      - apply vm_only_fds. exact (OWN_G _ _ _ _ HO2).
      - exact KEPT.
      -   intros q k. unfold a_live. cbn [a_LB A']. rewrite !in_map_iff. split.
        + intros (b' & E & Hb'). apply In_lb_remove in Hb'. destruct Hb' as [Hb' NE]. split; [exists b'; auto|].
          intros ->. apply NE. inversion E; subst. rewrite (ADP b' Hb' eq_refl). reflexivity.
        + intros [(b' & E & Hb') NE]. exists b'. split; [exact E|]. apply In_lb_remove. split; [exact Hb'|].
          intros Eid. apply NE. pose proof (IDP b' Hb' Eid) as Eb. rewrite Eb in E. cbn in E. congruence.
      - reflexivity.
      - reflexivity.
      - exact OWN'.
      -   intros w Hw. pose proof (bv_unsigned_in_range 64 w) as Wr. unfold bv_modulus in Wr.
        destruct (rframe_cases _ _ _ _ _ (bv_unsigned w) FR ltac:(lia)) as [[E _]|[X|[X|[X|X]]]].
        + unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
        + exfalso. apply Hw. right; right; left. subst lo. exact X.
        + exfalso. apply Hw. right; right; right. unfold errno_win, zwin. cbn [ly_tp ly_errno_off L]. unfold RERRNO in X. lia.
        + exfalso. apply Hw. left. left. unfold mng_static, RMLOCK, RCTX in *. lia.
        + exfalso. apply Hw. destruct (OWN' (bv_unsigned w) (or_intror X)) as [O|O]; [left; exact O| right; left; exact O].
      -   intros w Hw. pose proof (bv_unsigned_in_range 64 w) as Wr. unfold bv_modulus in Wr.
        destruct (rframe_cases _ _ _ _ _ (bv_unsigned w) FR ltac:(lia)) as [[E _]|[X|[X|[X|X]]]].
        + left. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. exact Hw.
        + left. destruct ST' as (_ & _ & STa). destruct (STa (bv_unsigned w) ltac:(subst lo; lia)) as [W1 _].
          rewrite ref_wview_overlay in W1 by (unfold wa; rewrite Z_to_bv_bv_unsigned; subst lo; unfold MNG_MALLOC_STACK in *; pose proof ac_bounds_lit as ?ACBL; lia).
          unfold wa in W1. rewrite Z_to_bv_bv_unsigned in W1. exact W1.
        + right; right; right. unfold errno_win, zwin. cbn [ly_tp ly_errno_off L]. unfold RERRNO in X. lia.
        + right; left. left. unfold mng_static, RMLOCK, RCTX in *. lia.
        + right. destruct (OWN' (bv_unsigned w) (or_intror X)) as [O|O]; [left; exact O| right; left; exact O].
    }

    assert (MSTD : mstd' mo) by (split; [exact Sh| split; [exact Sl| split; [exact Sm| exact Sc]]]).
    eapply srz_conseq.
    { apply (srz_impl rsegs _ _ _ _ _ (fun _ _ => K) IM2 TW MSTD LEAF). }
    apply tset_eq_const.
    + intros r mo' _. apply t_eq_refl.
    + destruct (twf_cfg_leaf_exists _ _ _ (twf_twf_cfg _ _ _ TW) (fun nd mo1 Hs => nstep_exists nd mo1 Hs)) as (r & mo' & Hp & _).
      exists r, mo'. exact Hp.
    + destruct (twf_leaf_exists _ _ _ TW) as (r & mo' & Hp & HPr).
      destruct (impl_tpath_leaf rsegs _ _ _ _ _ _ _ IM2 Hp) as [ms' HQr].
      pose proof (tpath_mstd' _ _ _ _ _ MSTD Hp) as SM'.
      exact (srealizes_nonempty _ _ _ (LEAF r ms' mo' HQr HPr SM')).
Qed.

Lemma cfree_lall_true cs slot : lall (fun _ : mstate => True) (cfree cs slot).
Proof. destruct (cfree_tok 0 cs slot) as (LA & _ & _). eapply lall_mono; [| exact LA]. intros; exact I. Qed.

Theorem L_free : forall (fx : FPState) (A : mstateA) R M mo (p n sp ret : Z) (K : TSet),
  a_inv A M mo -> mstd mo -> img_ro_clear L M ->
  call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
  (p = 0 /\ n = 0 \/ In (p, n) (a_live A)) ->
  alloc_ceiling + MNG_MALLOC_STACK <= sp ->
  stack_room SEGS M sp MNG_MALLOC_STACK ->
  (forall a, zwin (sp - MNG_MALLOC_STACK) sp a -> ~ a_owned A a) ->
  (forall A' R' M' mo', a_inv A' M' mo' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
      kept R R' -> live_del p (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
      (forall a, a_owned A' a -> a_owned A a \/ (p <= a < p + n)) ->
      frame_eq (fun a => a_owned A a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
      (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win L (bv_unsigned a)) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mo') K) ->
  srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (ly_free L)) M (seg_rom SEGS)) mo) K.
Proof.
  intros fx A R M mo p n sp ret K AI SM RO CR A0 HP SPC SR SOW HK.
  apply (L_free_gen (fun _ => True) fx A R M mo p n sp ret K AI SM RO CR A0 HP SPC SR SOW I).
  - intros. apply cfree_lall_true.
  - intros A' R' M' mo' H1 _. apply HK. exact H1.
Qed.

Lemma LRX_live A c : LRX (a_X A) c = count_class_f mng_size_class MNG_BIG (a_live A) c.
Proof.
  unfold LRX, a_X, a_live. induction (a_LB A) as [|b LB IH]; [reflexivity|].
  cbn [map count_class_f]. rewrite zcount_cons, IH. cbn [snd]. rewrite mng_size_class_eq. unfold MNG_BIG, MMAP_THRESHOLD.
  destruct (Z.leb_spec 131052 (blk_size b)); destruct (Z.ltb_spec (blk_size b) 131052); cbn [negb andb]; try lia; reflexivity.
Qed.

Lemma bigb_round n : bigb n = if MNG_BIG <=? n then mng_round_big n else 0.
Proof. unfold bigb, mng_round_big, mng_round_up_pg, round_up_pg, MNG_BIG, MMAP_THRESHOLD, MNG_IB, MNG_UNIT, IB, UNIT, MNG_PGSZ, PGSZ. reflexivity. Qed.

Lemma R63X_live A : R63X (a_X A) = big_bytes_f mng_round_big MNG_BIG (a_live A).
Proof.
  unfold a_X, a_live. induction (a_LB A) as [|b LB IH]; [reflexivity|].
  cbn [map big_bytes_f]. change (map (fun b0 : block => (blk_id b0, blk_size b0)) LB) with (a_X (MKA (a_s A) LB (a_P A) (a_big A))) in *.
  rewrite R63X_cons. cbn [a_LB] in IH. rewrite IH. rewrite bigb_round. reflexivity.
Qed.

Lemma n63X_cons q n X : n63X ((q, n) :: X) = (if MMAP_THRESHOLD <=? n then 1 else 0) + n63X X.
Proof. unfold n63X. rewrite zcount_cons. reflexivity. Qed.

Lemma BIGUNIT_val : BIGUNIT = 131072.
Proof. vm_compute. reflexivity. Qed.

Lemma bigb_ge n : MNG_BIG <= n -> BIGUNIT <= bigb n.
Proof.
  intros H. rewrite bigb_round. destruct (Z.leb_spec MNG_BIG n); [| lia]. unfold BIGUNIT. apply L_round_big_mono. unfold MNG_BIG in *. lia.
Qed.

Lemma n63X_R63X X : n63X X * BIGUNIT <= R63X X /\ 0 <= n63X X.
Proof.
  induction X as [|[q n] X IH].
  { rewrite BIGUNIT_val. unfold n63X, R63X. rewrite zcount_nil. cbn. lia. }
  rewrite n63X_cons, R63X_cons. rewrite BIGUNIT_val in *. pose proof (bigb_nonneg n).
  destruct (Z.leb_spec MMAP_THRESHOLD n); [| lia].
  pose proof (bigb_ge n ltac:(unfold MNG_BIG, MMAP_THRESHOLD in *; lia)). rewrite BIGUNIT_val in *. lia.
Qed.

Lemma room_to_LB A mo NR RBY n : QI (a_X A) (a_PL A) (a_s A) mo -> caps_ok (a_PL A) (a_big A) NR RBY -> a_room A n ->
  ROOMX (a_X A) (a_PL A) n /\ PHI (a_PL A) + R63X (a_X A) + bigb n <= LBUDGET /\ 0 <= n <= MNG_NMAX.
Proof.
  intros [_ HB] (SMAX & ETOT & _ & _ & _ & B0 & _ & _ & _ & CAPB & P0) HR.
  pose proof L_big_pos as BP. pose proof (n63X_R63X (a_X A)) as [NR63 N0].
  unfold ROOMX, a_PL in *. cbn [Z.eqb Pos.eqb] in *. rewrite BIGUNIT_val in *. destruct HR as [(Hn & C1 & C2)|(Hn & CB)].
  - rewrite <- LRX_live in C1. change mng_size_class with size_to_class in C1.
    pose proof (L_size_class_range n Hn) as SC. change mng_size_class with size_to_class in SC.
    destruct (Z.eqb_spec (size_to_class n) 63); [lia|].
    split; [split; [intros _; exact C1| intros X; unfold MNG_BIG, MMAP_THRESHOLD in *; lia]|].
    rewrite bigb_round. destruct (Z.leb_spec MNG_BIG n); [lia|]. lia.
  - rewrite <- R63X_live in CB. rewrite bigb_round. destruct (Z.leb_spec MNG_BIG n); [| lia].
    pose proof (bigb_ge n ltac:(lia)) as BG. rewrite bigb_round, BIGUNIT_val in BG. destruct (Z.leb_spec MNG_BIG n); [| lia].
    split; [split; [intros X; unfold MNG_BIG, MMAP_THRESHOLD in *; lia| intros _]|].
    + enough (n63X (a_X A) + 1 <= a_big A / 131072) by lia. apply Z.div_le_lower_bound; lia.
    + lia.
Qed.

Lemma cmalloc_init_kept cs n : c_init_done (s_ctx cs) = 1 ->
  lall (fun r => True /\ c_init_done (s_ctx (fst r)) = 1) (cmalloc cs n).
Proof.
  intros HI. destruct (cmalloc_tok n cs ltac:(right; exact HI)) as (LA & _ & _).
  eapply lall_mono; [| exact LA]. intros [st r] [HR _]. cbn [fst] in *. split; [exact I|]. unfold cinit in *. lia.
Qed.

Section MALLOC.
Variable AUXM : auxv_mode.
Variable LP : mstate -> Prop.
Variables (fx : FPState) (A : mstateA) (R : bvmap 5 word) (M : LibIface.mem) (mo : Model) (n sp ret : Z) (Ksucc : TSet).
Hypothesis AI : a_invX A M mo.
Hypothesis IMODE : c_init_done (ctx (ps_m (a_s A))) = 1 \/ @AUXAVAIL AUXM.
Hypothesis AUXF : @AUXAVAIL AUXM -> rauxv_full M sp rr_secret.
Hypothesis HLP : lall (fun r => LP (fst r) /\ c_init_done (s_ctx (fst r)) = 1) (cmalloc (ps_m (a_s A)) n).
Hypothesis SM : mstd mo.
Hypothesis RO : img_ro_clear L M.
Hypothesis CR : call_regs L R sp ret.
Hypothesis A0 : getr R 10%bv = Z_to_bv 64 n.
Hypothesis HN : 0 <= n <= MNG_NMAX.
Hypothesis SPC : alloc_ceiling + MNG_MALLOC_STACK <= sp.
Hypothesis SR : stack_room SEGS M sp MNG_MALLOC_STACK.
Hypothesis SOW : forall a, zwin (sp - MNG_MALLOC_STACK) sp a -> ~ a_owned A a.
Hypothesis ROOM : a_room A n.
Hypothesis KS : forall A' R' M' mo' (p : Z),
  a_inv A' M' mo' -> LP (ps_m (a_s A')) -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
  kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
  live_add p n (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
  (forall a, a_owned A' a -> a_owned A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
  frame_eq (fun a => a_owned A' a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
  (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
  srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mo') Ksucc.

Definition KL : Exc.exc (option bptr * PState) -> Model -> TSet := fun _ _ => Ksucc.
Definition good (r : Exc.exc (option bptr * PState)) : bool :=
  match r with Exc.Ok (Some _, _) => true | _ => false end.

Lemma malloc_core :
  srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (ly_malloc L)) M (seg_rom SEGS)) mo) (tset (raw_malloc n (a_s A)) mo KL)
  /\ (exists r mo', tpath nstep_cfg (raw_malloc n (a_s A)) mo [] r mo')
  /\ Ksucc [].
Proof.
  pose proof (a_invX_call A M mo AI SM RO) as (HH & MI & NR & RBY & HO & HQ & LIM & HRSV & CO).
  destruct CR as [Cra Cret Cretr Csp Csp16 Csphi Cgp Ctp]. pose proof SM as [Sh Sl Sm Sc].
  pose proof SPC as SP0. unfold MNG_MALLOC_STACK in SP0; pose proof ac_bounds_lit as ?ACBL.
  pose proof A0 as A0'.
  rewrite (getr_reg_get R 1%bv eq_refl) in Cra. rewrite (getr_reg_get R 2%bv eq_refl) in Csp. rewrite (getr_reg_get R 3%bv eq_refl) in Cgp.
  rewrite (getr_reg_get R 4%bv eq_refl) in Ctp. rewrite (getr_reg_get R 10%bv eq_refl) in A0'. cbn [ly_tp ly_gp L] in Ctp, Cgp.
  destruct (room_to_LB A mo NR RBY n HQ CO ROOM) as (HRX & HB & _).
  set (lo := sp - MNG_MALLOC_STACK).
  assert (STK : stk rsegs M lo sp).
  { replace sp with (lo + Z.of_nat (Z.to_nat MNG_MALLOC_STACK)) by (subst lo; unfold MNG_MALLOC_STACK; lia).
    apply stk_of_store_ok; [exact SR| subst lo; unfold MNG_MALLOC_STACK in *; lia| subst lo; unfold MNG_MALLOC_STACK; lia| subst lo; unfold RIMG_HI, MNG_MALLOC_STACK in *; lia]. }
  destruct (errno_cell_any M) as [errv ERR].
  pose proof (@rmalloc_spec _ _ AUXM (reg_get R 1%bv) (reg_get R 2%bv) (reg_get R 3%bv) (reg_get R 4%bv) (reg_get R 5%bv) (reg_get R 6%bv) (reg_get R 7%bv)
    (reg_get R 8%bv) (reg_get R 9%bv) (reg_get R 10%bv) (reg_get R 11%bv) (reg_get R 12%bv) (reg_get R 13%bv) (reg_get R 14%bv) (reg_get R 15%bv)
    (reg_get R 16%bv) (reg_get R 17%bv) (reg_get R 18%bv) (reg_get R 19%bv) (reg_get R 20%bv) (reg_get R 21%bv) (reg_get R 22%bv) (reg_get R 23%bv)
    (reg_get R 24%bv) (reg_get R 25%bv) (reg_get R 26%bv) (reg_get R 27%bv) (reg_get R 28%bv) (reg_get R 29%bv) (reg_get R 30%bv) (reg_get R 31%bv)
    (@fp_regs fx) (@fp_csr fx) M (a_s A) (a_LB A) n lo sp errv HH IMODE) as IMPL.
  rewrite Csp, Ctp, A0' in IMPL. rewrite !unsigned_lit in IMPL by (unfold RATP; lia).
  specialize (IMPL ltac:(split; [pose proof ac_bounds_lit as ?ACBL; lia| exact AUXF]) ltac:(lia) STK ltac:(subst lo; unfold MNG_MALLOC_STACK in *; pose proof ac_bounds_lit as ?ACBL; lia)
                   ltac:(subst lo; unfold MNG_MALLOC_STACK, RMALLOC_STACK; lia)).
  specialize (IMPL ltac:(exact ERR) MI eq_refl eq_refl ltac:(unfold MNG_NMAX, LIB_NMAX in HN; lia)).
  unfold implM in IMPL.
  match type of IMPL with impl _ _ _ _ ?ms =>
    assert (EQV : ms_eqv ms (@mkst fx R (Z_to_bv 64 (ly_malloc L)) M (seg_rom SEGS))) end.
  { rewrite mkst_MS. rewrite <- Csp, <- Ctp, <- A0'. apply ms_eqv_sym. apply (MS_eqv_mkR R). }
  pose proof (impl_eqv rsegs _ _ _ _ IMPL EQV) as IM2. clear IMPL EQV. cbv beta in IM2.

  assert (HO' : OWN (map blk_id (a_LB A)) (GV mo) (a_s A) mo).
  { eapply OWN_G_switch; [| apply vm_only_refl]. unfold a_X in HO. rewrite map_map in HO. exact HO. }
  pose proof (raw_malloc_spec_c (map blk_id (a_LB A)) (GV mo) n (frame_ok_GV mo) (proj1 HN) (a_s A) mo HO') as TW1.
  pose proof (raw_malloc_LQ (a_X A) (a_PL A) n (proj1 HN) (a_s A) mo (conj HQ (conj HRX HB))) as TW2.
  pose proof (twf_with_path _ _ _ (twf_twl_conj LBUDGET _ _ _ _ TW1 TW2)) as TW. clear TW1 TW2. cbv beta in TW.
  assert (NDid : List.NoDup (map blk_id (a_LB A))) by exact (RHEAP_blocks_nodup_proof _ _ _ HH).

  assert (ALLSUCC : forall r mo', tpath nstep_cfg (raw_malloc n (a_s A)) mo [] r mo' -> good r = true).
  { intros r mo' Hp. pose proof (twf_tpath _ _ _ _ _ _ TW (tpath_cfg_sub _ _ _ _ _ Hp)) as HPr. cbv beta in HPr.
    destruct r as [|[[pb|] s'']]; [exact (False_ind _ (proj1 (proj1 HPr))) | reflexivity |]. exfalso.
    destruct CO as (SMAX & ETOT & SMAX0 & NR0 & RBY0 & B0 & HSM & HET & HGAP & CAPB & P0).
    exact (raw_malloc_all_succ (a_PL A) SMAX ETOT NR RBY MNG_NMAX SMAX0 RBY0 HSM HET ltac:(unfold MNG_NMAX, LIB_NMAX; lia) HGAP
             (a_X A) n (a_s A) mo HQ HRX HB HN LIM HRSV None s'' mo' Hp eq_refl). }
  pose proof (twf_cfg_with_path _ _ _ (fun r _ => good r = true) (twf_twf_cfg _ _ _ TW) ALLSUCC) as TWC. cbv beta in TWC.

  match type of IM2 with impl _ _ _ ?Q _ => match type of TWC with twf_cfg _ _ ?P =>
    assert (LEAF : forall r ms' mo', Q r ms' -> P r mo' -> mstd' mo' -> srealizes SEGS (mkCfg ms' mo') (KL r mo')) end end.
  { intros r ms' mo' HQr [HPr Hgood] SM'. destruct r as [|[rp s'']]; [exact (False_ind _ (proj1 (proj1 HPr)))|].
    cbn [epost fst snd] in HQr. destruct HPr as [[HO2 HQ2] PATH]. cbn [fst snd] in HO2, HQ2.
    destruct HQr as (y & POST & EQy).
    destruct POST as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & errv' & Ey & MI' & ST' & ERR' & AUX' & HPRES & FR & Efa & Eso & RES).
    rewrite !unsigned_lit in ST', FR, HPRES by lia.

    destruct (raw_malloc_tpath_elim _ _ _ _ _ _ PATH) as (cs' & p0 & s' & PM & Es'' & Erp).
    destruct (tpath_membed_follow _ _ _ _ _ _ PM) as [ans Hf].
    pose proof (lall_follow _ _ _ _ HLP Hf) as [LPl INITl]. cbn [fst] in LPl, INITl.
    pose proof (tpath_vm_const _ _ _ _ _ PATH) as [VL VR].

    destruct (leaf_state fx R ms' y _ _ m' EQy Ey) as (Ems' & KEPT & REGS).
    { intros k Hk. cbn in Hk.
      destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
        first [exact (eq_sym Cra) | exact (eq_sym Csp) | exact (eq_sym Cgp) | exact (eq_sym Ctp) | reflexivity]. }
    rewrite Ems'. rewrite Cra, (ret_pc_of_ret_ok ret Cretr Cret).
    assert (RA0 : getr (ms_regs ms') 10%bv = wa0) by (rewrite (REGS 10%bv eq_refl); reflexivity).
    assert (GOTW : wmono rsegs m' (got_clear m')).
    { intros x Hx. unfold wview in Hx |- *. unfold got_clear. destruct (in_gotb x) eqn:E; [| exact Hx].
      unfold in_gotb in E. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      pose proof (got_wview_any (fun _ => None) (bv_unsigned x) ltac:(lia)) as G. unfold wview, wa in G. rewrite Z_to_bv_bv_unsigned in G. exact G. }
    assert (RHG : forall sx LBx, RHEAP sx LBx m' -> RHEAP sx LBx (got_clear m')).
    { intros sx LBx RHx. apply (RHEAP_frame_pw _ _ m' (got_clear m') RHx); [| intros a Ha; apply got_clear_on; exact Ha| exact GOTW].
      intros a Ha. apply got_clear_off. unfold wa.
      destruct Ha as [ST|(O1 & O2 & _)]; [pose proof (mng_static_img a ST)|]; rewrite unsigned_lit by (unfold RRW_LO, RIMG_HI in *; pose proof ac_bounds_lit as ?ACBL; lia);
        unfold RGOT_SSP, RRW_LO, RIMG_LO, RIMG_HI in *; lia. }
    assert (DEF : forall LBx (w : word), (forall a, in_block (a_LB A) a -> in_block LBx a) -> rframe LBx lo sp M m' ->
              M w <> None -> m' w <> None \/ a_owned A (bv_unsigned w) \/ errno_win L (bv_unsigned w)).
    { intros LBx w SUB FRx Hw. pose proof (bv_unsigned_in_range 64 w) as Wr. unfold bv_modulus in Wr.
      destruct (rframe_cases _ _ _ _ _ (bv_unsigned w) FRx ltac:(lia)) as [[E _]|[X|[X|[X|(X1 & X2 & X3)]]]].
      + left. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. exact Hw.
      + left. destruct ST' as (_ & _ & STa). destruct (STa (bv_unsigned w) ltac:(subst lo; lia)) as [W1 _].
        rewrite ref_wview_overlay in W1 by (unfold wa; rewrite Z_to_bv_bv_unsigned; subst lo; unfold MNG_MALLOC_STACK in *; pose proof ac_bounds_lit as ?ACBL; lia).
        unfold wa in W1. rewrite Z_to_bv_bv_unsigned in W1. exact W1.
      + right; right. unfold errno_win, zwin. cbn [ly_tp ly_errno_off L]. unfold RERRNO in X. lia.
      + right; left. left. unfold mng_static, RMLOCK, RCTX in *. lia.
      + right; left. right. split; [exact X1|]. split; [exact X2|]. intros IB. apply X3. apply SUB. exact IB. }
    destruct rp as [pb|].
    -
      destruct RES as (Addr & junk & Ea0 & BR & RH' & UCH & _). subst wa0.
      set (A' := MKA s'' ((pb, Addr, n) :: a_LB A) (a_P A) (a_big A)).
      destruct BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      assert (OWN' : forall a, rowned ((pb, Addr, n) :: a_LB A) a -> rowned (a_LB A) a).
      { intros a [ST|(O1 & O2 & O3)]; [left; exact ST| right]. split; [exact O1|]. split; [exact O2|].
        intros (b' & Hb' & Hab). apply O3. exists b'. split; [right; exact Hb'| exact Hab]. }
      apply (KS A' (ms_regs ms') m' mo' Addr).
      + split; [| split; [| split]].
        * exact (RHG _ _ RH').
        * cbn [a_s A']. rewrite Es''. cbn [ps_m set_m]. exact INITl.
        * destruct SM' as (_ & Sl' & _). exact Sl'.
        * exists NR, RBY. split; [| exact CO]. cbn [a_s a_X a_PL a_big A']. apply kpart_intro.
          -- eapply OWN_G_switch; [| exact I]. unfold a_X. cbn [a_LB map fst]. rewrite map_map. cbn [fst]. exact (proj1 HO2).
          -- unfold a_X. cbn [a_LB map]. exact (proj1 HQ2).
          -- rewrite VL. exact LIM.
          -- unfold RSV in *. rewrite VR. exact HRSV.
      + cbn [a_s A']. rewrite Es''. cbn [ps_m set_m]. exact LPl.
      + destruct SM' as (Sh' & Sl' & Sm' & Sc'). split; assumption.
      + apply vm_only_fs. exact (OWN_G _ _ _ _ (proj1 HO2)).
      + apply vm_only_fds. exact (OWN_G _ _ _ _ (proj1 HO2)).
      + exact KEPT.
      + exact RA0.
      + exact BR1.
      + split; [reflexivity|]. unfold a_live. rewrite map_map. cbn [fst].
        pose proof (RHEAP_addr_nodup _ _ _ RH') as ND. cbn [map blk_addr fst snd] in ND. inversion ND; subst. exact H1.
      + reflexivity.
      + reflexivity.
      + intros a Ha. left. exact (OWN' a Ha).
      + intros w Hw. pose proof (bv_unsigned_in_range 64 w) as Wr. unfold bv_modulus in Wr.
        destruct (rframe_cases _ _ _ _ _ (bv_unsigned w) FR ltac:(lia)) as [[E _]|[X|[X|[X|(X1 & X2 & X3)]]]].
        * unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
        * exfalso. apply Hw. right; right; left. subst lo. exact X.
        * exfalso. apply Hw. right; right; right. unfold errno_win, zwin. cbn [ly_tp ly_errno_off L]. unfold RERRNO in X. lia.
        * exfalso. apply Hw. left. left. unfold mng_static, RMLOCK, RCTX in *. lia.
        * exfalso. apply Hw. destruct (in_blockb ((pb, Addr, n) :: a_LB A) (bv_unsigned w)) eqn:IB.
          -- apply in_blockb_spec in IB. destruct IB as (b' & [<-|Hb'] & Hab); [right; left; cbn in Hab; exact Hab|].
             exfalso. apply X3. exists b'. auto.
          -- left. right. split; [exact X1|]. split; [exact X2|]. intros IBP. apply in_blockb_spec in IBP. cbn [a_LB A'] in IBP. congruence.
      + intros w Hw. apply (DEF (a_LB A) w (fun a H => H) FR Hw).
    -
      discriminate Hgood. }
  assert (MSTD : mstd' mo) by (split; [exact Sh| split; [exact Sl| split; [exact Sm| exact Sc]]]).
  split; [| split].
  - apply (srz_impl_cfg rsegs _ _ _ _ _ KL IM2 TWC MSTD LEAF).
  - destruct (twf_cfg_leaf_exists _ _ _ TWC (fun nd mo1 Hs => nstep_exists nd mo1 Hs)) as (r & mo' & Hp & _). exists r, mo'. exact Hp.
  - destruct (twf_cfg_leaf_exists _ _ _ TWC (fun nd mo1 Hs => nstep_exists nd mo1 Hs)) as (r & mo' & Hp & HPr).
    destruct (impl_tpath_leaf rsegs _ _ _ _ _ _ _ IM2 (tpath_cfg_sub _ _ _ _ _ Hp)) as [ms' HQr].
    pose proof (tpath_mstd' _ _ _ _ _ MSTD (tpath_cfg_sub _ _ _ _ _ Hp)) as SM'.
    exact (srealizes_nonempty _ _ _ (LEAF r ms' mo' HQr HPr SM')).
Qed.

Theorem L_malloc :
  srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (ly_malloc L)) M (seg_rom SEGS)) mo) Ksucc.
Proof.
  destruct malloc_core as (SRZ & (r0 & mo0 & Hp0) & Knil).
  eapply srz_conseq; [exact SRZ|]. apply tset_eq_const.
  - intros r mo' _. apply t_eq_refl.
  - exists r0, mo0. exact Hp0.
  - exact Knil.
Qed.
End MALLOC.

Section MALLOC_MI.
Variables (fx : FPState) (A : mstateA) (R : bvmap 5 word) (M : LibIface.mem) (mo : Model) (n sp ret : Z) (Ksucc : TSet).
Hypothesis AI : a_inv A M mo.
Hypothesis SM : mstd mo.
Hypothesis RO : img_ro_clear L M.
Hypothesis CR : call_regs L R sp ret.
Hypothesis A0 : getr R 10%bv = Z_to_bv 64 n.
Hypothesis HN : 0 <= n <= MNG_NMAX.
Hypothesis SPC : alloc_ceiling + MNG_MALLOC_STACK <= sp.
Hypothesis SR : stack_room SEGS M sp MNG_MALLOC_STACK.
Hypothesis ROOM : a_room A n.
Hypothesis KS : forall A' R' M' mo' (p : Z),
  a_inv A' M' mo' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
  kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
  live_add p n (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
  (forall a, a_owned A' a -> a_owned A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
  frame_eq (fun a => a_owned A' a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
  (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
  srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mo') Ksucc.

Let AX : a_invX A M mo := proj1 (a_inv_X A M mo AI).
Let INIT : c_init_done (ctx (ps_m (a_s A))) = 1 := proj2 (a_inv_X A M mo AI).
Let IMODE : c_init_done (ctx (ps_m (a_s A))) = 1 \/ @AUXAVAIL mng_auxv_off := or_introl INIT.
Let AUXF : @AUXAVAIL mng_auxv_off -> rauxv_full M sp rr_secret := fun F : False => match F with end.
Let HLP : lall (fun r => True /\ c_init_done (s_ctx (fst r)) = 1) (cmalloc (ps_m (a_s A)) n) := cmalloc_init_kept _ n INIT.

Theorem L_malloc_MI :
  srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (ly_malloc L)) M (seg_rom SEGS)) mo) Ksucc.
Proof.
  apply (L_malloc mng_auxv_off (fun _ => True) fx A R M mo n sp ret Ksucc AX IMODE AUXF HLP SM RO CR A0 HN SPC SR ROOM).
  intros A' R' M' mo' p H1 _. apply KS. exact H1.
Qed.
End MALLOC_MI.

Definition MI_S1 : MallocIface SEGS L :=
  {| AS := mstateA;
     ainv := a_inv;
     live := a_live;
     owned := a_owned;
     size_class := mng_size_class;
     BIG := MNG_BIG;
     NMAX := MNG_NMAX;
     round_big := mng_round_big;
     caps := a_P;
     bigcap := a_big;
     room_for := a_room;
     MALLOC_STACK := MNG_MALLOC_STACK;
     ai_big_pos := L_big_pos;
     ai_nmax_bound := L_nmax_bound;
     ai_round_big_mono := L_round_big_mono;
     ai_round_big_nonneg := L_round_big_nonneg;
     ai_size_class_range := L_size_class_range;
     room_small := L_room_small;
     room_big := L_room_big;
     ai_mstd := L_mstd;
     ai_live_block := L_live_block;
     ai_live_nodup := fun A M mo H => proj2 (NoDup_ListNoDup _) (L_live_nodup A M mo H);
     ai_live_disjoint := L_live_disjoint;
     ai_owned_not_img_ro := L_owned_not_img_ro;
     ai_owned_below_ceiling := L_owned_below_ceiling;
     static_cells := mng_static_cells;
     ai_static_cells := L_static_cells;
     ai_static_cells_owned := L_static_cells_owned;
     ai_frame := L_frame;
     may_fail := a_may_fail;
     may_fail_big := fun A n H => or_introl H;
     mi_malloc := fun fx A R M mo n sp ret Ks AI SM RO CR A0 HN SPC SR SOW ROOM KS =>
                    L_malloc_MI fx A R M mo n sp ret Ks AI SM RO CR A0 HN SPC SR ROOM KS;
     mi_free := L_free |}.

Lemma MI_S1_consts_ok : mi_consts_ok SEGS L MI_S1.
Proof. constructor; reflexivity. Qed.

End AC_1.
