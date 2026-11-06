(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Placement.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Iface.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require CFGA.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.

(* [comment removed for export] *)
Module SegD_cost.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "le"; "leb"; "div"; "min"; "modulo"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "sumZ"; "DEPC"; "dep_cost"; "depot_mem"; "depot_inv"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "dF"; "DG"; "dN"; "dFB"; "dFP"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "nat"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_wf.
Import ListNotations.
Open Scope Z_scope.

Lemma sumZ_firstn_S : ltac2:(tb__ "0|0|
S17S0A1S18S1eR1S16S0R2A2A2S1bS0S9SeS0S19R2A1R3A3A1S1S9SeS0R2R3A3A1SfS0R2R3Z0A4A2A3F_;Fn;Fl;").
Proof.
  induction l as [|x l IH]; intros [|n] Hn; cbn in Hn |- *; try lia.
  - unfold sumZ. cbn. destruct l; cbn; lia.
  - unfold sumZ in *. cbn. specialize (IH n ltac:(lia)). cbn in IH. rewrite IH. lia.
Qed.

Lemma sumZ_firstn_all : ltac2:(tb__ "0|0|
S17S0A1S1bS0S9SeS0S16S0R1A2R1A3A1S9R1A1A3Fl;").
Proof. intros l. rewrite firstn_all. reflexivity. Qed.

Lemma pages_prefix_bound : ltac2:(tb__ "0|6|
S11S1cS18ScR3R2A2S1dR2S16S0S13R4A1A2A2S5S10R5A1Z100000M0A2S0S3S2S1aS9SeS0R4S14R6A1A3A1A2S1S1S2S2Z8M1G0A2S6S8R4A1M2R1A2A2S15S0L_;M3S4G2R1A2Z0M4S1S1S2G1S7S10R6A1G0A2A2S1aA2Z58M5A2X15x2A2G3S4G2S1R1Z1A2A2G4S1S1aG5A2X15x2A2A2Tq;F_;F_;Fn;Fm;FG;").
Proof.
  intros G m n HM Hn q. pose proof (dm_F _ _ HM) as (F0 & _ & F32 & _). pose proof (dm_fb_len _ _ HM) as [[L1 L2] HL].
  pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MB.
  assert (FB : fblk (dF G) <= q + 1).
  { unfold fblk, q. assert ((dF G + 1048576 - 1) / 1048576 < dF G / 1048576 + 1 + 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  induction n as [|n IH].
  - change (firstn 0 (dFP G)) with (@nil Z). change (Z.of_nat 0) with 0. unfold sumZ. cbn [fold_right]. rewrite Z.min_l by lia.
    replace (0 <=? q) with true by (symmetry; apply Z.leb_le; lia). replace (0 <=? q + 1) with true by (symmetry; apply Z.leb_le; lia). unfold PG. lia.
  - specialize (IH ltac:(lia)). rewrite sumZ_firstn_S by (rewrite HL; lia). rewrite Z.mul_add_distr_l.
    destruct (dm_fp _ _ HM n ltac:(lia)) as [[P0 P1] _]. pose proof (dm_fp_hi _ _ HM n ltac:(lia)) as PH.
    destruct (Z_lt_le_dec (Z.of_nat n) q) as [C1|C1].
    +
      rewrite (Z.min_l (Z.of_nat (S n))) by lia. rewrite Z.min_l in IH by lia.
      replace (Z.of_nat (S n) <=? q) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat (S n) <=? q + 1) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat n <=? q) with true in IH by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat n <=? q + 1) with true in IH by (symmetry; apply Z.leb_le; lia).
      unfold FBPAGES, PG in *. nia.
    + destruct (Z.eq_dec (Z.of_nat n) q) as [C2|C2].
      *
        rewrite (Z.min_r (Z.of_nat (S n))) by lia. rewrite Z.min_l in IH by lia.
        replace (Z.of_nat (S n) <=? q) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat (S n) <=? q + 1) with true by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat n <=? q) with true in IH by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat n <=? q + 1) with true in IH by (symmetry; apply Z.leb_le; lia).
        rewrite C2 in PH. unfold q in PH. unfold PG in *. nia.
      *
        assert (C3 : Z.of_nat n = q + 1) by lia.
        rewrite (Z.min_r (Z.of_nat (S n))) by lia. rewrite Z.min_r in IH by lia.
        replace (Z.of_nat (S n) <=? q) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat (S n) <=? q + 1) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat n <=? q) with false in IH by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat n <=? q + 1) with true in IH by (symmetry; apply Z.leb_le; lia).
        rewrite C3 in PH. unfold q in PH. unfold PG in *. nia.
Qed.

Theorem dep_cost_bound_mem : ltac2:(tb__ "0|0|
S11S1cScR2R1A2S3SbR3A1S1S1S2Z10S12R3A1A2S2Z8S10R3A1A2A2SaA2A2F_;Fm;FG;").
Proof.
  intros G m HM. pose proof (dm_F _ _ HM) as (F0 & _ & F32 & _). pose proof (dm_N _ _ HM) as [[N1 N2] _].
  pose proof (dm_fb_len _ _ HM) as [[L1 L2] HL]. pose proof (dm_map1_len _ _ HM) as [M1 M2].
  pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MB.
  pose proof (pages_prefix_bound G m (length (dFB G)) HM ltac:(lia)) as P. cbn zeta in P.
  rewrite <- HL, sumZ_firstn_all in P. rewrite HL in P.
  unfold dep_cost, dep_pages, DEPC.
  assert (NB : NBSZ * Z.of_nat (length (dNB G)) <= 16 * dN G + 16 + NBSZ).
  { unfold nblk in M2. destruct (Z.eqb_spec (dN G + 1) 0); [lia|].
    pose proof (Z.div_mod (dN G + 1) 65536 ltac:(lia)). pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)). unfold NBSZ. nia. }
  assert (FP : PG * sumZ (dFP G) <= 8 * dF G + 2 * PG + 176).
  { pose proof (Z.le_min_r (Z.of_nat (length (dFB G))) (dF G / 1048576)) as MR.
    destruct (Z.of_nat (length (dFB G)) <=? dF G / 1048576); destruct (Z.of_nat (length (dFB G)) <=? dF G / 1048576 + 1); unfold PG in *; nia. }
  unfold PG, NBSZ in *. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Theorem dep_cost_bound : ltac2:(tb__ "0|0|
S11S20S1fS17S21Q40A1A1SdVsegs;R4R3R2R1A5S3SbR5A1S1S1S2Z10S12R5A1A2S2Z8S10R5A1A2A2SaA2A2F_;Ftp;Fmd;Frho;FG;").
Proof. intros G rho md tp [HM _]. exact (dep_cost_bound_mem G _ HM). Qed.
End WithSegs.
End SegD_cost.

(* [comment removed for export] *)
Module Ledger.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "sub"; "of_nat"; "div"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "app"; "list"; "cons"; "snd"; "bool"; "fst"; "length"; "nat"; "Some"; "nil"; "option"; "pair"; "true"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "hwN"; "hwS"; "VCAP"; "GAPF"; "GN"; "apartW"; "live_hi"; "FBMAX"; "NBMAX"; "BETA1"; "QDEPK"; "maps_disjoint"; "ranges_apart"; "NLIM"; "Q1"; "SLIM"; "ledger"; "sepZ"; "GAPC"; "N0"; "QDEPF"; "QPIECES"; "S0"; "blocks_left"; "budget_boundD"; "gapN_ok"; "gapS_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_depot"; "aa_Km"; "aa_Kf"; "aa_V"; "dN"; "aa_ptr_committed"; "dF"; "dFB"; "dNB"; "AA"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "gw_sizes"; "live_at"; "gap_weight"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "FBSZ"; "DEPC"; "NBSZ"; "dep_cost"; "NFBLK"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "acost"; "BETA_F"; "BETA_M"; "LIMIT"; "QMAX"; "QPRIM"; "U0"; "limit_ok_alloc"; "limit_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "kPtrArrayCommit"; "kUserMapSize"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "region_free"; "vm_maps"; "vm_reserved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Placement.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition BETA1 : Z := 1936.

Definition QPIECES : Z := ltac2:(tb__ "0|0|
S2Z1eS2Z2S0S57S5S57Z8A2A2A2A2").
Definition Q1 : Z := ltac2:(tb__ "0|0|
S0S0S0S0S31Z2404A2Z10000A2S2Z4S55A2A2S51A2").

Definition QDEPK : Z := 104.
Definition QDEPF : Z := 88 * 4096.

Definition budget_boundD (A : AA) : Z := ltac2:(tb__ "0|0|
S0S0S0S0S0S52S4cS3aVA;A1A1A2S2S25S0S38VA;A1S39VA;A1A2A2A2S2aA2S3cVA;A1A2S48S37VA;A1A1A2").

Lemma budgetD_closes : ltac2:(tb__ "0|0|
S1S0S0S0S0S0S2aS26A2S30A2S46A2S56A2S2Z7S55A2A2S50A2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma BETA1_M : ltac2:(tb__ "0|0|
S1S0S0S25S26A2Z8A2S4eA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma BETA1_F : ltac2:(tb__ "0|0|
S1S0S25S26A2S4dA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Q1_nonneg : 0 <= Q1.
Proof. unfold Z.le. intro H. vm_compute in H. discriminate H. Qed.
Lemma BETA1_nonneg : 0 <= BETA1.
Proof. unfold BETA1. lia. Qed.

Lemma budgetD_le_budget : ltac2:(tb__ "0|5|
S40S1S48S37R1A1M0A1S0S0S2Z10S3bG0A1A2S2Z8M1S3dG0A1A2A2S46A2A2S1S3dS37R2A1M2A1S2ZbS0S3bG2A1S49A2A2A2S1S3bS37R3A1A1S0S0S38R3A1S39R3A1A2Z1A2A2S18S1Z0M3S3cR4A1M4A2S1G4S0S2G1S38R4A1A2S56A2A2A2S1G3S38R5A1A2S1G3S39R6A1A2S1S34R7A1S41R7A1A2F_;F_;F_;F_;F_;F_;FA;").
Proof.
  intros A HC HF HN HP HKm HKf. unfold budget_boundD, budget_bound.
  pose proof budgetD_closes as CL. pose proof BETA1_M as BM. pose proof BETA1_F as BF.
  unfold QDEPK, QDEPF, NFBLK, PG in *.
  set (q1 := Q1) in *. set (qm := QMAX) in *. set (dc := DEPC) in *. set (pc := kPtrArrayCommit) in *.
  set (b1 := BETA1) in *. set (bm := BETA_M) in *. set (bf := BETA_F) in *.
  clearbody q1 qm dc pc b1 bm bf. nia.
Qed.

Definition VCAP : Z := 4 * LIMIT / 7.
Definition NBMAX : Z := 4100.
Definition FBMAX : Z := 4100.
Definition GAPF : Z := 0x10007fff8000.
Definition GAPC : Z := 0x7fff7f800000.
Definition GN : Z := 64513.
Definition N0 : Z := 2 ^ 18.
Definition S0 : Z := 2 ^ 40.
Definition NLIM : Z := ltac2:(tb__ "0|0|
S0S0S0S0S2fS24A2S23A2S5S1eS20A2A2Z1A2").
Definition SLIM : Z := ltac2:(tb__ "0|0|
S0S0S0S32S2Z2S1eA2A2S2S47S24A2A2S2S45S23A2A2").

Definition MUK : Z := 2 ^ 20.

Lemma GAPF_eq : GAPF = Placement.SHADOW_BAND_HI. Proof. reflexivity. Qed.
Lemma GAPF_eqG : GAPF = Geometry.SHADOW_BAND_HI. Proof. reflexivity. Qed.
Lemma GAPC_eq : GAPC = alloc_ceiling_lo. Proof. reflexivity. Qed.
Lemma VCAP_acost : ltac2:(tb__ "0|0|
S6S1Z0R1A2S1S4cR2A1S4fA2S1R3S1eA2F_;F_;Fx;").
Proof.
  intros x Hx H. unfold acost, ALPHA_NUM, ALPHA_DEN, VCAP, LIMIT in *.
  pose proof (Z.div_mod (7 * x + 4 - 1) 4) as D1. pose proof (Z.mod_pos_bound (7 * x + 4 - 1) 4) as M1.
  pose proof (Z.div_mod (4 * 2 ^ 39) 7) as D2. pose proof (Z.mod_pos_bound (4 * 2 ^ 39) 7) as M2. lia.
Qed.
Lemma VCAP_limit_alloc : ltac2:(tb__ "0|2|
S6S6S6S6S1Z0M0S0R4R1A2A2S1G0R4A2M1G1S53R7R6R5R4A4S1S0R8R5A2S1eA2F_;F_;F_;F_;Fn;FKf;FKm;FV;").
Proof.
  intros V Km Kf n H0 HKm HKf H. unfold limit_ok_alloc, BETA_M, BETA_F in H.
  pose proof QMAX_nonneg. pose proof U0_nonneg. apply VCAP_acost; [exact H0 |]. set (q := QMAX) in *. set (u := U0) in *. clearbody q u. nia.
Qed.
Lemma VCAP_limit_free : ltac2:(tb__ "0|1|
S6S6S6S1Z0R3A2M0G0G0S54R6R5R4A3S1R7S1eA2F_;F_;F_;F_;FKf;FKm;FV;").
Proof.
  intros V Km Kf H0 HKm HKf H. unfold limit_ok_free, BETA_M, BETA_F in H.
  pose proof QMAX_nonneg. pose proof U0_nonneg. apply VCAP_acost; [exact H0 |]. set (q := QMAX) in *. set (u := U0) in *. clearbody q u. nia.
Qed.

Definition ledger (V : VmMaps) : list (word * word) := ltac2:(tb__ "0|1|
S8S7S15Q40A1M0G0A2S5aVV;A1S59VV;A1A3").

Definition live_hi (l : list (word * word)) : list (word * word) := List.filter (live_at GAPF) l.
Definition hwN (l : list (word * word)) : Z := Z.of_nat (length (live_hi l)).
Definition hwS (l : list (word * word)) : Z := gw_sizes (live_hi l).

Lemma gap_weight_hw : ltac2:(tb__ "0|1|
S6S9S7S15Q40A1M0G0A2A1S17S6S44R2S22R1A1A2S0S1dR1A1S2S1cR1A1S0R2ZfffA2A2A2A3Fl;FnZ;").
Proof. intros nZ l. unfold hwS, hwN. apply gap_weight_sizes. Qed.
Lemma live_hi_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17G2S22S8G1R2R1A3A1S8G1S22R2A1S22R1A1A3A3Fl2;Fl1;").
Proof. intros l1 l2. unfold live_hi. apply List.filter_app. Qed.
Lemma live_hi_cons : ltac2:(tb__ "0|4|
S7S15Q40A1M0G0A2M1S9G1A1M2S17G2S22SaG1R2R1A3A1S8G1ScG2L_;S43S1fR2A2SaG1R2S11G1A1M3A3G3Xcx2S22R1A1A3A3Fl;Fe;").
Proof. intros e l. unfold live_hi. cbn [List.filter]. destruct (live_at GAPF e); reflexivity. Qed.
Lemma gw_sizes_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17S6S42S8G1R2R1A3A1S0S42R2A1S42R1A1A2A3Fl2;Fl1;").
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn -[Z.add]; [lia | rewrite IH; lia]. Qed.
Lemma gw_sizes_nonneg : ltac2:(tb__ "0|1|
S9S7S15Q40A1M0G0A2A1S1Z0S42R1A1A2Fl;").
Proof. induction l as [|[b s] l IH]; cbn -[Z.add]; [lia|]. pose proof (bv_unsigned_in_range 64 s). lia. Qed.
Lemma hwN_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17S6S1cS8G1R2R1A3A1S0S1cR2A1S1cR1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold hwN. rewrite live_hi_app, length_app. lia. Qed.
Lemma hwS_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17S6S1dS8G1R2R1A3A1S0S1dR2A1S1dR1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold hwS. rewrite live_hi_app. apply gw_sizes_app. Qed.
Lemma hwN_nonneg : ltac2:(tb__ "0|1|
S9S7S15Q40A1M0G0A2A1S1Z0S1cR1A1A2Fl;").
Proof. intros l. unfold hwN. lia. Qed.
Lemma hwS_nonneg : ltac2:(tb__ "0|1|
S9S7S15Q40A1M0G0A2A1S1Z0S1dR1A1A2Fl;").
Proof. intros l. unfold hwS. apply gw_sizes_nonneg. Qed.
Lemma hwN_cons : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0A2M1S9G1A1S17S6S1cSaG1R2R1A3A1S0ScS6L_;S43S1fR2A2Z1Z0Xcx2S1cR1A1A2A3Fl;Fe;").
Proof. intros e l. unfold hwN. rewrite live_hi_cons. rewrite length_app. destruct (live_at GAPF e); cbn [length]; lia. Qed.
Lemma hwS_cons : ltac2:(tb__ "0|3|
S7S15Q40M0A1M1G1A2M2S9G2A1S17S6S1dSaG2R2R1A3A1S0ScS6L_;S43S1fR2A2S16G0SbG1G1R2A3A2Z0Xcx2S1dR1A1A2A3Fl;Fe;").
Proof. intros [b s] l. unfold hwS. rewrite live_hi_cons. rewrite gw_sizes_app. destruct (live_at GAPF (b, s)); cbn -[Z.add]; lia. Qed.

Lemma hwN_insert_le : ltac2:(tb__ "0|5|
S9S7S15Q40A1M0G0A2M1A1M2G1G2S18S1S1cS8G1R3R1A3A1M3S1cS8G1R3SaG1R2R1A3A3A1M4A2S1G4S0G3Z1A2A2A2Fl2;Fe;Fl1;").
Proof. intros l1 e l2. rewrite !hwN_app, hwN_cons. destruct (live_at GAPF e); lia. Qed.
Lemma hwS_insert_le : ltac2:(tb__ "0|6|
S9S7S15Q40M0A1M1G1A2M2A1M3G2G3S18S1S1dS8G2R3R1A3A1M4S1dS8G2R3SaG2R2R1A3A3A1M5A2S1G5S0G4S16G0SbG1G1R2A3A2A2A2A2Fl2;Fe;Fl1;").
Proof. intros l1 e l2. rewrite !hwS_app, hwS_cons. pose proof (bv_unsigned_in_range 64 (snd e)). destruct (live_at GAPF e); lia. Qed.

Lemma hwN_insert_low : ltac2:(tb__ "0|4|
S9S7S15Q40M0A1M1G1A2M2A1M3G2G3S1S0S16G0SdG1G1R2A3A2S16G0SbG1G1R2A3A2A2S1fA2S17S6S1cS8G2R4SaG2R3R2A3A3A1S1cS8G2R4R2A3A1A3F_;Fl2;Fe;Fl1;").
Proof.
  intros l1 [b s] l2 H. rewrite !hwN_app, hwN_cons. cbn [fst snd] in H.
  unfold live_at. cbn [fst snd]. destruct (GAPF <? bv_unsigned b + bv_unsigned s) eqn:E; [apply Z.ltb_lt in E; lia | lia].
Qed.
Lemma hwS_insert_low : ltac2:(tb__ "0|4|
S9S7S15Q40M0A1M1G1A2M2A1M3G2G3S1S0S16G0SdG1G1R2A3A2S16G0SbG1G1R2A3A2A2S1fA2S17S6S1dS8G2R4SaG2R3R2A3A3A1S1dS8G2R4R2A3A1A3F_;Fl2;Fe;Fl1;").
Proof.
  intros l1 [b s] l2 H. rewrite !hwS_app, hwS_cons. cbn [fst snd] in H.
  unfold live_at. cbn [fst snd]. destruct (GAPF <? bv_unsigned b + bv_unsigned s) eqn:E; [apply Z.ltb_lt in E; lia | lia].
Qed.

Definition blocks_left (A : AA) : Z := ltac2:(tb__ "0|1|
S0S3S24S4SeS6S3fS37VA;A1M0A1A2A1A2S3S23S4SeS6S3eG0A1A2A1A2A2").
Definition gapN_ok (A : AA) (V : VmMaps) : Prop := ltac2:(tb__ "0|0|
S1S0S0S2S20S1cS2cVV;A1A1A2S3S1eS3aVA;A1A2A2S2S20S33VA;A1A2A2S2S20S29A2A2").
Definition gapS_ok (A : AA) (V : VmMaps) : Prop := ltac2:(tb__ "0|1|
S1S0S0S0S1dS2cVV;A1A1S2Z2S3S1eS3aVA;A1A2A2A2S2S47S3S24S4SeS6S3fS37VA;A1M0A1A2A1A2A2A2S2S45S3S23S4SeS6S3eG0A1A2A1A2A2A2S2bA2").
Definition gap_ok (A : AA) (V : VmMaps) : Prop := ltac2:(tb__ "0|0|
S18S35VA;VV;A2S36VA;VV;A2A2").

Lemma GN_pays_chunk : ltac2:(tb__ "0|0|
S6S6S1S20R2A2S1R2S0R3Z3007A2A2S18S1S2S20Z1A2R4A2S1R3S2Z2R4A2A2A2F_;F_;Fms;Fn;").
Proof. intros n ms Hn Hms. unfold GN in *. lia. Qed.

Lemma gap_closes : ltac2:(tb__ "0|0|
S1S0S0S0S1fS45A2S2bA2S2S29S0S45ZfffA2A2A2S2eA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition apartW (e1 e2 : word * word) : Prop := ltac2:(tb__ "0|4|
S19S1S0S16Q40M0SdS15G0A1M1G1Ve1;A3A2M2S16G0SbG1G1Ve1;A3A2A2S16G0SdG1G1Ve2;A3A2M3A2S1S0G3S16G0SbG1G1Ve2;A3A2A2G2A2A2").
Lemma apartW_sym : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0A2M1G1S21R2R1A2S21R2R3A2F_;Fe2;Fe1;").
Proof. intros e1 e2 [H|H]; [right|left]; exact H. Qed.

Fixpoint ranges_apart (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | e :: r => Forall (apartW e) r /\ ranges_apart r
  end.
Definition maps_disjoint (l : list (word * word)) : Prop := ranges_apart l.

Lemma ranges_apart_app : ltac2:(tb__ "0|4|
S9S7S15Q40A1M0G0A2M1A1M2G2S1aS28S8G1R2R1A3A1S18S28R2A1S18S28R1A1G1G1S4aG1R2R4A3M3G3S21R4R3A2F_;F_;Fe2;Fe1;A2A2A2Fl2;Fl1;").
Proof.
  induction l1 as [|e l1 IH]; intros l2; cbn.
  - split; [intros H; split; [exact I|]; split; [exact H|]; intros e1 e2 [] | intros (_ & H & _); exact H].
  - rewrite Forall_app, IH. split.
    + intros ([F1 F2] & R1 & R2 & X). split; [split; [exact F1 | exact R1]|]. split; [exact R2|].
      intros e1 e2 [<-|H1] H2; [exact (proj1 (Forall_forall _ _) F2 e2 H2) | exact (X e1 e2 H1 H2)].
    + intros ([F1 R1] & R2 & X). split; [split; [exact F1|]|].
      * apply Forall_forall. intros e2 H2. apply X; [left; reflexivity | exact H2].
      * split; [exact R1|]. split; [exact R2|]. intros e1 e2 H1 H2. apply X; [right; exact H1 | exact H2].
Qed.

Lemma maps_disjoint_insert : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G1G2S27S8G1R3R1A3A1G1S4aG1R1S8G1R5R3A3A3S21R5R2A2F_;Fe';S27S8G1R5SaG1R4R3A3A3A1F_;F_;Fl2;Fe;Fl1;").
Proof.
  intros l1 e l2 H X. unfold maps_disjoint in *. apply ranges_apart_app in H as (R1 & R2 & Y).
  apply (proj2 (ranges_apart_app l1 (e :: l2))). split; [exact R1|]. split.
  - cbn. split; [|exact R2]. apply Forall_forall. intros e' H'. apply X. apply in_or_app. right. exact H'.
  - intros e1 e2 H1 [<-|H2]; [|exact (Y e1 e2 H1 H2)]. apply apartW_sym. apply X. apply in_or_app. left. exact H1.
Qed.
Lemma maps_disjoint_in : ltac2:(tb__ "0|4|
S9S7S15Q40A1M0G0A2M1A1SfSfG1G1S27R5A1S1bS17SfR5R4A3A1S17S12G1A1M2S4bG1R7R6A3S10G1R4A2M3A3S17G2S4bG1R8R6A3G3A3S21R6R5A2F_;F_;F_;F_;Fe2;Fe1;Fj;Fi;Fl;").
Proof.
  unfold maps_disjoint. induction l as [|e l IH]; intros i j e1 e2 H Hij H1 H2.
  - destruct i; discriminate H1.
  - cbn in H. destruct H as [F R]. destruct i as [|i], j as [|j]; cbn in H1, H2.
    + lia.
    + injection H1 as <-. apply nth_error_In in H2. exact (proj1 (Forall_forall _ _) F e2 H2).
    + injection H2 as <-. apply nth_error_In in H1. apply apartW_sym. exact (proj1 (Forall_forall _ _) F e1 H1).
    + apply (IH i j e1 e2 R ltac:(lia) H1 H2).
Qed.

Lemma apart_of_region_free : ltac2:(tb__ "0|2|
S9S7S15Q40A1M0G0A2M1A1G0G0S17ScS58R3R2R1A3S14A3G1S4aG1R1R5A3S21S13G0G0R5R4A4R2A2F_;Fe;F_;Fn;Fa;Fl;").
Proof.
  intros l a n H [b s] Hin. pose proof (region_free_In l a n b s H Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; unfold apartW; cbn [fst snd]; lia.
Qed.

Definition sepZ (r1 r2 : Z * Z) : Prop := ltac2:(tb__ "0|2|
S19S1S0SdS6S6Vr1;A3M0SbS6S6Vr1;A3A2SdS6S6Vr2;A3M1A2S1S0G1SbS6S6Vr2;A3A2G0A2A2").
Lemma sepZ_sym : ltac2:(tb__ "0|1|
S7S6S6A2M0G0S2dR2R1A2S2dR2R3A2F_;Fr2;Fr1;").
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.
End Ledger.

(* [comment removed for export] *)
Module CallocArith.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.Riscv.Sem"; "mul_div"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "M_MULHU"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "div"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "eval"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "calloc_size"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Iface.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation word := (bv 64).
Local Notation U := bv_unsigned.

Lemma urange64 : ltac2:(tb__ "0|2|
S1Q40M0A1S4S8Z0S0G0R1A2M1A2SbG1SaZ2Z40A2A2A2Fx;").
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

Lemma mul_word_comm : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S3G1S2G0S6R2R1A4S2G0S6R1R2A4A3Fy;Fx;").
Proof. intros x y. apply bv_eq. rewrite !mul_val. f_equal. lia. Qed.

Lemma mulhu_val : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S3SdS0G0S2G0S7R2R1A4A2ScS9S0G0R2A2S0G0R1A2A2SaZ2Z40A2A2A3Fy;Fx;").
Proof.
  intros x y. unfold mul_div, bv_mulhuu. pose proof (urange64 x) as Hx. pose proof (urange64 y) as Hy.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (Z.of_N 64) with 64.
  rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_small. split; [apply Z.div_pos; nia|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma mulhu_zero_iff : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S5S3SdS0G0S2G0S7R2R1A4A2Z0A3SbS9S0G0R2A2S0G0R1A2A2SaZ2Z40A2A2A2Fy;Fx;").
Proof.
  intros x y. rewrite mulhu_val. pose proof (urange64 x) as Hx. pose proof (urange64 y) as Hy. split.
  - intros H. apply Z.div_small_iff in H; [|lia]. destruct H as [H|H]; lia.
  - intros H. apply Z.div_small. nia.
Qed.

Lemma mul_exact : ltac2:(tb__ "0|3|
S1Q40M0A1M1G1SbS9S0G0R2A2M2S0G0R1A2A2SaZ2Z40A2A2S3SdS0G0S2G0S6R3R2A4A2S9S0G0R3A2G2A2A3F_;Fy;Fx;").
Proof. intros x y H. rewrite mul_val. pose proof (urange64 x). pose proof (urange64 y). apply Z.mod_small. nia. Qed.

Lemma mul_pos_factors : ltac2:(tb__ "0|3|
S1Q40M0A1M1G1S8Z1M2S0G0S2G0S6R2R1A4A2A2S4S8G2S0G0R3A2A2S8G2S0G0R2A2A2A2F_;Fy;Fx;").
Proof.
  intros x y H. rewrite mul_val in H. pose proof (urange64 x) as Hx. pose proof (urange64 y) as Hy.
  destruct (Z.eq_dec (U x) 0) as [E|E]; [rewrite E in H; cbn in H; lia|].
  destruct (Z.eq_dec (U y) 0) as [E'|E']; [rewrite E', Z.mul_0_r in H; cbn in H; lia|]. lia.
Qed.

Lemma calloc_size_val : ltac2:(tb__ "0|1|
S10S3S1Q40M0A1SfR1S11A2S2G0S6SeR1PcA2SeR1PdA2A4A3Frho;").
Proof. intros rho. reflexivity. Qed.
End CallocArith.

(* [comment removed for export] *)
Module SegD_ins.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "of_nat"; "modulo"; "div"; "to_nat"; "sub"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Corelib.Init.Datatypes"; "nat"; "length"; "prod"; "pair"; "list"; "app"; "cons"; "option"; "nil"; "Some"; "fst"; "snd"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "DG"; "dNB"; "dFB"; "dN"; "dFP"; "dF"; "list_upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "STORE"; "node_addr"; "depot_mem"; "NBSZ"; "cellZ"; "ranges_disjointZ"; "FBSZ"; "G_page"; "fpage"; "G_ins"; "depot_vm"; "fblk"; "G_fblk"; "G_nblk"; "NIDS"; "DEPOT"; "DNMAX"; "FBPAGES"; "MAP1"; "dep_cost"; "sumZ"; "NFBLK"; "TABSZ"; "nblk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "IMG_HI"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins"; "ins_written"; "pw_disj"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Specif"; "sumbool"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_wf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac dc := unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.

Lemma nth_map' : forall {A B} (f : A -> B) (l : list A) i dA dB, (i < length l)%nat -> nth i (map f l) dB = f (nth i l dA).
Proof.
  intros A B f l. induction l as [|x l IH]; intros [|i] dA dB Hi; cbn in Hi |- *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma dblocks_nf_disj : ltac2:(tb__ "0|6|
S1eSfSfS1bR2S10S0S1fR3A1A2A2S1bR2S10S0S20R4A1A2A2SfSfS1bR2R1A2S1bR2S10S11S0S0A2M0S25R8A1A2A2S2bS1cG0R4S25R9A1M1S12S0S0Z0M2G2A4M3A4S1cG0R3G1G3A4A2F_;F_;Fj';Fi';ScS2S1S1cS0R5S1fR6A1G2A4M4S29A2S1cS0R4S20R6A1G2A4M5A2S2S1G5S2cA2G4A2A2F_;F_;F_;Fb;Fi;FG;").
Proof.
  intros G i b Hi Hb DD.
  assert (Hj2 : (length (dNB G) + b < length (dblocks G))%nat) by (unfold dblocks; rewrite ?length_app, !length_map; lia).
  specialize (DD i (length (dNB G) + b)%nat ltac:(lia) Hj2). unfold dblocks in DD.
  rewrite app_nth1 in DD by (rewrite length_map; exact Hi). rewrite app_nth2 in DD by (rewrite length_map; lia).
  rewrite length_map, Nat.add_comm, Nat.add_sub in DD.
  rewrite (nth_map' (fun b0 => (b0, NBSZ)) (dNB G) i 0 (0,0) Hi) in DD. rewrite (nth_map' (fun b0 => (b0, FBSZ)) (dFB G) b 0 (0,0) Hb) in DD.
  unfold ranges_disjointZ in DD. cbn [fst snd] in DD. exact DD.
Qed.

Lemma dblocks_nn_disj : ltac2:(tb__ "0|7|
S1eSfSfS1bR2S10S0S1fR3A1A2A2S1bR2S10S0S1fR4A1A2A2S1bR4R3A2SfSfS1bR2R1A2S1bR2S10S11S0S0A2M0S25R9A1A2A2S2bS1cG0R4S25RaA1M1S12S0S0Z0M2G2A4M3A4S1cG0R3G1G3A4A2F_;F_;Fj';Fi';ScS2S1S1cS0R6S1fR7A1M4G2A4M5S29A2S1cS0R5G4G2A4M6A2S2S1G6S29A2G5A2A2F_;F_;F_;F_;Fj;Fi;FG;").
Proof.
  intros G i j Hi Hj Hij DD. specialize (DD i j Hij ltac:(unfold dblocks; rewrite ?length_app, !length_map; lia)).
  unfold dblocks in DD. rewrite !app_nth1 in DD by (rewrite length_map; lia).
  rewrite (nth_map' (fun b0 => (b0, NBSZ)) (dNB G) i 0 (0,0) Hi) in DD. rewrite (nth_map' (fun b0 => (b0, NBSZ)) (dNB G) j 0 (0,0) Hj) in DD.
  unfold ranges_disjointZ in DD. cbn [fst snd] in DD. exact DD.
Qed.

Definition ins_written (G : DG) (i : Z) (b : nat) (sz S : Z) (z : Z) : Prop := ltac2:(tb__ "0|8|
ScSbS2S1S35S3Z4M0Vi;A2A2M1Vz;A2S4Vz;S1G1G0A2A2A2ScSbS2S34Vz;A2S4Vz;S1S34G0A2A2A2ScSbS2S27VG;S1S21VG;A1Z1M2A2A2M3Vz;A2S4Vz;S1G3Z10M4A2A2A2ScSbS2S26Vz;A2S4Vz;S1S26Z8M5A2A2A2ScSbS2S1S1S26Z18A2S3G4S5Vb;A1A2M6A2Vz;A2S4Vz;S1S1S26Z1cA2G6A2A2A2SbS2S1S1cS0Vb;S20VG;A1Z0A4S3G5S6VS;Z100000A2A2A2M7Vz;A2S4Vz;S1G7S3G5S1Vsz;G2A2A2A2A2A2A2A2A2A2A2").

Lemma zrange_dec : ltac2:(tb__ "0|1|
S0S0S0S49SbS2R3R1A2S4R1R2A2A2M0SdG0A1A2Fz;Fhi;Flo;").
Proof. intros. destruct (Z_le_dec lo z); [destruct (Z_lt_dec z hi); [left; lia | right; lia] | right; lia]. Qed.

Lemma ins_written_dec : ltac2:(tb__ "0|1|
S1eS0SfS0S0S0ScS46R6R5R4R3R2R1A6M0SdG0A1A2Fz;FS;Fsz;Fb;Fi;FG;").
Proof.
  intros G i b sz S z. unfold ins_written.
  destruct (zrange_dec (DEPOT + 4 * i) (DEPOT + 4 * i + 4) z); [tauto|].
  destruct (zrange_dec NIDS (NIDS + 4) z); [tauto|].
  destruct (zrange_dec (node_addr G (dN G + 1)) (node_addr G (dN G + 1) + 16) z); [tauto|].
  destruct (zrange_dec STORE (STORE + 8) z); [tauto|].
  destruct (zrange_dec (STORE + 24 + 16 * Z.of_nat b) (STORE + 28 + 16 * Z.of_nat b) z); [tauto|].
  destruct (zrange_dec (nth b (dFB G) 0 + 8 * (S mod 1048576)) (nth b (dFB G) 0 + 8 * (S mod 1048576) + 8 * (sz + 1)) z); [tauto|].
  right. tauto.
Qed.

Lemma nblk_step : ltac2:(tb__ "0|2|
S0S2Z0R1A2SaS0S3dS1R2Z1M0A2M1A1S1S7G1Z10000A2G0A2A3F_;FN;").
Proof. intros N HN. unfold nblk. destruct (Z.eqb_spec (N + 1) 0); lia. Qed.

Lemma node_addr_G_ins : ltac2:(tb__ "0|0|
S1eS0S0SaS0S27S2fR3R2A2R1A2S27R3R1A2A3Fs;FF;FG;").
Proof. reflexivity. Qed.

Lemma dblocks_G_ins : ltac2:(tb__ "0|0|
S1eS0SaS13S11S0S0A2A1S25S2fR2R1A2A1S25R2A1A3FF;FG;").
Proof. reflexivity. Qed.

Lemma nodes_disjoint : ltac2:(tb__ "0|9|
S1eS0S0SfSfS1bR2R1A2S1bR2S10S11S0S0A2M0S25R6A1A2A2S2bS1cG0R4S25R7A1M1S12S0S0Z0M2G2A4M3A4S1cG0R3G1G3A4A2F_;F_;Fj;Fi;S2G2R3A2M4G4SdSaS0R5R4A3A1S1bS8S7R6Z10000A2A1M5S10S0S1fR7A1A2A2S1bG5S10S0S1fR8A1A2A2ScS2S1S27R9R8A2M6Z10M7A2S27R9R7A2M8A2S2S1G8G7A2G6A2A2F_;F_;F_;F_;F_;F_;Fs';Fs;FG;").
Proof.
  intros G s s' DD Hs Hs' Hne Hb Hb'. unfold node_addr.
  pose proof (Z.mod_pos_bound s 65536 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound s' 65536 ltac:(lia)) as M2.
  destruct (Nat.eq_dec (Z.to_nat (s / 65536)) (Z.to_nat (s' / 65536))) as [E|NE].
  - rewrite <- E. assert (s / 65536 = s' / 65536) by (pose proof (Z.div_pos s 65536); pose proof (Z.div_pos s' 65536); lia).
    assert (s mod 65536 <> s' mod 65536).
    { intros EQ. apply Hne. rewrite (Z.div_mod s 65536), (Z.div_mod s' 65536) by lia. lia. }
    lia.
  - destruct (Nat.lt_ge_cases (Z.to_nat (s / 65536)) (Z.to_nat (s' / 65536))).
    + destruct (dblocks_nn_disj G _ _ Hb Hb' ltac:(lia) DD); unfold NBSZ in *; lia.
    + destruct (dblocks_nn_disj G _ _ Hb' Hb ltac:(lia) DD); unfold NBSZ in *; lia.
Qed.

Lemma depot_vm_G_ins : ltac2:(tb__ "0|0|
S1eS0S45S13S42Q40A1A1S30R4R2R1A3S30S2fR5R4A2R3R2A3F_;Ftp;Fmd;FF;FG;").
Proof. intros G F md tp [A B C D]. constructor; cbn [dNB dFB dFP G_ins]; assumption. Qed.

Lemma fblk_mono : ltac2:(tb__ "0|0|
S0S0SbS2Z0R2A2S2R2R1A2A2S2S31R3A1S31R2A1A2F_;Fb;Fa;").
Proof. intros a b H. unfold fblk. apply Z.div_le_mono; lia. Qed.
Lemma fblk_le_succ_div : ltac2:(tb__ "0|1|
S0S0S2Z0R2A2S2R3S3Z100000S1R2Z1M0A2A2A2S2S31R4A1S1R3G0A2A2F_;F_;Fq;FF;").
Proof. intros F q H1 H2. unfold fblk. assert ((F + 1048576 - 1) / 1048576 < q + 1 + 1) by (apply Z.div_lt_upper_bound; lia). lia. Qed.
Lemma fblk_gt_div : ltac2:(tb__ "0|0|
S0S0S2Z0R1A2S4S3Z100000R2A2R3A2S2S1R3Z1A2S31R4A1A2F_;F_;Fq;FF;").
Proof. intros F q H1 H2. unfold fblk. apply Z.div_le_lower_bound; lia. Qed.

Lemma depot_mem_insert : ltac2:(tb__ "0|c|
S1eS3eS3eS0SfS0S0S0S28R8R7A2SbS2Z1M0R6A2S2R6ZaA2A2S2S21RaA1S36A2ScSaS0R4S23RbA1M1A3SbSaS0R4S1G1S1R8G0A2A2A3S2Z100000M2S1S6G1G2A2R8A2A2A2A2SaSfR8S8S7R5G2A2A1A3S1bR9S10S0S20RdA1A2A2S4S1S6R7G2A2RbA2G2A2S2S3Z8M3S1S1S6R8G2A2RcA2G0A2A2S3S40S1cS0RbS22RfA1Z0M4A4A2A2S1bS8S7S1S21R10A1G0A2Z10000A2A1S10S0S1fR10A1A2A2SbS2G4RcA2S4RcS3cA2A2S0SdS46R13ReRfR10RcR1A6A1SaS16S42Q8A1A1R12R2A1R13R2A1A3F_;Fz;S2aR11S1S35S3Z4ReA2A2U4M5S1S21R13A1G0A2A4S2aR12S34G5S1S21R14A1G0A2A4S2aR13S27R15S1S21R15A1G0A2A2U8M6RfA4SeS0S0SbS2aR15S1S27R17S1S21R17A1M7G0A2A2M8G3A2G5R1A4SbS2G4R1A2S2R1G7A2A2A2Ll;A2S3fR15S1G8ZcA2S1G8Z10M9A2A3S2aR16S26G6S1S1R11R15A2G0A2A4S3fR17S1S1S26Z18A2S3G9S5R15A1A2MaA2S1S1S26Z1cA2GaA2A3S3fR18S1S1cS0R16S20R1aA1G4A4S3G3S6R13G2A2A2A2MbS1GbS3G3S1R17G0A2A2A2A3S28S2fR1bS1S1R14R18A2G0A2A2R19A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FS;Fh;Fi;Fb;Fsz;Fm';Fm;FG;").
Proof.
  intros G m m' sz b i h S HM Hsz HDN HS Hb Hbl Hns Hpaid HjN Hi Hsame Ctab Cnid Cnh [l [Cnl Hl]] Pst Ctf Pstc Pfr.
  destruct HM as [HN HF Hmu Hal Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfp Hfr Hfh Hdj].
  pose proof (proj1 HF) as F0.
  assert (HSge : dF G <= S <= dF G + 11) by lia.
  pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MBF.
  pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  pose proof (Z.div_mod S 1048576 ltac:(lia)) as DMS. pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DMF.
  assert (HbZ : Z.of_nat b = S / 1048576) by (subst b; rewrite Z2Nat.id by (apply Z.div_pos; lia); reflexivity).
  assert (FBL : fblk (dF G) < 4096) by (apply fblk_lt; lia).
  assert (Hb4096 : Z.of_nat b < 4096) by (pose proof (proj1 Hfl); lia).
  assert (HinN : In (nth (Z.to_nat ((dN G + 1) / 65536)) (dNB G) 0) (dNB G)) by (apply nth_In; exact HjN).
  destruct (Hnb _ HinN) as (NBal & NBlo & NBhi & NBpres).
  assert (Ena : node_addr G (dN G + 1) = nth (Z.to_nat ((dN G + 1) / 65536)) (dNB G) 0 + 16 * ((dN G + 1) mod 65536)) by reflexivity.
  assert (NAlo : IMG_HI <= node_addr G (dN G + 1) /\ node_addr G (dN G + 1) + 16 <= 140737479966720) by (rewrite Ena; unfold NBSZ in NBhi; lia).
  destruct (Hfbs (nth b (dFB G) 0) (nth_In _ _ Hbl)) as (FBal & FBlo & FBhi).

  assert (FBm : fblk (dF G) <= fblk (S + sz + 1)) by (apply fblk_mono; lia).
  assert (FB2 : S = dF G + (sz + 1) -> fblk (dF G) + 1 <= fblk (S + sz + 1)).
  { intros ES. pose proof (fblk_le_succ_div (dF G) (dF G / 1048576) ltac:(lia) ltac:(lia)) as U.
    pose proof (Z.div_pos (dF G) 1048576 ltac:(lia) ltac:(lia)) as DP.
    pose proof (fblk_gt_div (S + sz + 1) (dF G / 1048576 + 1) ltac:(lia) ltac:(lia)) as V. lia. }
  assert (Fnew : S + sz + 1 <= 11 * (dN G + 1 + fblk (S + sz + 1))) by (destruct HS as [ES|[ES SR]]; [|specialize (FB2 ES)]; lia).

  assert (UV : forall a k v, (forall j, (j < k)%nat -> ~ ins_written G i b sz S (a + Z.of_nat j)) -> cellZ m a k v -> cellZ m' a k v).
  { intros a k v Hk H j Hj. unfold cellZ, cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. rewrite (Hsame _ (Hk j Hj)). exact (H j Hj). }
  assert (PR : forall lo hi, (forall a, lo <= a < hi -> ~ ins_written G i b sz S a) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hk Hp z Hz. rewrite (Hsame z (Hk z Hz)). exact (Hp z Hz). }
  assert (FL : forall lo hi v, (forall a, lo <= a < hi -> ~ ins_written G i b sz S a) -> filled m lo hi v -> filled m' lo hi v).
  { intros lo hi v Hk Hp z Hz. rewrite (Hsame z (Hk z Hz)). exact (Hp z Hz). }

  assert (WP : forall a, ins_written G i b sz S a -> exists b0, m' a = Some b0).
  { intros a Hw. unfold ins_written in Hw.
    assert (CP : forall a0 k v, cellZ m' a0 k v -> a0 <= a < a0 + Z.of_nat k -> exists b0, m' a = Some b0).
    { intros a0 k v Hc Ha. unfold cellZ, cell_ok in Hc. cbn [c_addr c_w RtCells.c_val] in Hc. specialize (Hc (Z.to_nat (a - a0)) ltac:(first [ clear - Ha; lia | lia ])).
      replace (a0 + Z.of_nat (Z.to_nat (a - a0))) with a in Hc by (first [ clear - Ha; lia | lia ]).     eexists; exact Hc. }
    destruct Hw as [X|[X|[X|[X|[X|X]]]]].
    - eapply (CP _ 4%nat); [exact Ctab | cbn; lia].
    - eapply (CP _ 4%nat); [exact Cnid | cbn; lia].
    - destruct (Z_lt_le_dec a (node_addr G (dN G + 1) + 8)); [eapply (CP _ 8%nat); [exact Cnh | cbn; lia]|].
      destruct (Z_lt_le_dec a (node_addr G (dN G + 1) + 12)); [eapply (CP _ 4%nat); [exact Cnl | cbn; lia]|].
      apply Pst. lia.
    - eapply (CP _ 8%nat); [exact Ctf | cbn; lia].
    - apply Pstc. lia.
    - apply Pfr. lia. }
  assert (PR2 : forall lo hi, present m lo hi -> present m' lo hi).
  { intros lo hi Hp z Hz. destruct (ins_written_dec G i b sz S z) as [W|NW]; [exact (WP z W) | rewrite (Hsame z NW); exact (Hp z Hz)]. }
  unfold ins_written in UV, PR, FL, Hsame.
  unfold DNMAX in HDN. dc.
  constructor; cbn [dN dF dNB dFB dFP G_ins]; dc.
  -   split; [lia | exact Cnid].
  -   destruct HF as (F1 & F2 & F3 & F4). split; [lia|]. split; [exact Fnew|]. split; [lia|]. exact Ctf.
  -   apply UV; [|exact Hmu]. intros j Hj. lia.
  -   apply PR; [|exact Hal]. intros a Ha. lia.
  -   intros i' Hi'. destruct (Z.eq_dec i' i) as [->|Hne].
    + exists (dN G + 1). split; [exact Ctab | right; lia].
    + destruct (Htab i' Hi') as (w & Hw & Hr). exists w. split; [|lia]. apply UV; [|exact Hw]. intros j Hj. lia.
  -   rewrite nblk_step by lia. replace (dN G + 1 + 1) with (dN G + 2) by lia. unfold nblk in Hl1 |- *.
    destruct (Z.eqb_spec (dN G) 0); [lia|]. destruct (Z.eqb_spec (dN G + 1) 0); [lia|]. destruct (Z.eqb_spec (dN G + 2) 0); [lia|].
    pose proof (proj1 (Nat2Z.inj_lt _ _) HjN) as X. rewrite Z2Nat.id in X by (apply Z.div_pos; lia).
    assert ((dN G + 1) / 65536 <= (dN G + 2) / 65536) by (apply Z.div_le_mono; lia). lia.
  -   intros j Hj. apply UV; [|exact (Hm1 j Hj)]. intros j' Hj'. lia.
  -   intros b0 Hb0. destruct (Hnb b0 Hb0) as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. apply PR2. exact A4.
  -   intros s Hs. rewrite !node_addr_G_ins. destruct (Z.eq_dec s (dN G + 1)) as [->|Hne].
    + exists h, l. split; [exact Cnh|]. split; [exact Cnl | lia].
    + destruct (Hlk s ltac:(lia)) as (h0 & l0 & Hh & Hl0 & Hr). exists h0, l0.
      assert (SB : (Z.to_nat (s / 65536) < length (dNB G))%nat).
      { unfold nblk in Hl1. destruct (Z.eqb_spec (dN G) 0); [lia|].
        assert (s / 65536 <= dN G / 65536) by (apply Z.div_le_mono; lia). pose proof (Z.div_pos s 65536 ltac:(lia) ltac:(lia)). lia. }
      assert (ND : node_addr G s + 16 <= node_addr G (dN G + 1) \/ node_addr G (dN G + 1) + 16 <= node_addr G s) by (apply (nodes_disjoint G s (dN G + 1) Hdj); lia).

      pose proof (Z.mod_pos_bound s 65536 ltac:(lia)) as MS.
      destruct (Hnb _ (nth_In _ 0 SB)) as (_ & SBlo & SBhi & _). unfold NBSZ in SBhi.
      destruct (dblocks_nf_disj G _ b SB Hbl Hdj) as [NF|NF]; unfold NBSZ, FBSZ in NF;
      unfold node_addr in ND |- *; unfold node_addr in NAlo;
      (split; [apply UV; [intros j Hj; lia | exact Hh] | split; [apply UV; [intros j Hj; lia | exact Hl0] | exact Hr]]).
  -   split; [|exact (proj2 Hfl)]. pose proof (proj1 Hfl) as X.
    pose proof (fblk_le_succ_div (S + sz + 1) (Z.of_nat b) ltac:(lia) ltac:(lia)) as U.
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hbl). lia.
  -   intros b0 Hb0. destruct (Hfb b0 Hb0) as (A1 & A2 & A3 & A4).
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hb0). pose proof (proj1 Hfl).
    split; [|split; [exact A2 | split]].
    + apply UV; [|exact A1]. intros j Hj. lia.
    + apply PR2. exact A3.
    + apply UV; [|exact A4]. intros j Hj. lia.
  -   intros b0 Hb0. destruct (Hfz b0 Hb0) as (Z1 & Z2 & Z3). pose proof (proj1 (Nat2Z.inj_lt _ _) Hbl).
    split; [apply FL; [intros a Ha; lia | exact Z1]|]. split; [apply PR2; exact Z2 | apply FL; [intros a Ha; lia | exact Z3]].
  -   exact Hfbs.
  -   intros b0 Hb0. destruct (Hfp b0 Hb0) as [A1 A2]. split; [exact A1|]. apply PR2. exact A2.
  -   intros b0 Hb0. pose proof (Hfr b0 Hb0) as LO. destruct (Hfp b0 Hb0) as [[FP0 _] _].
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hb0) as B0.
    destruct (Nat.lt_trichotomy b0 b) as [LT|[->|GT]].
    +
      assert (FULL : 8 * 1048576 <= 4096 * nth b0 (dFP G) 0).
      { destruct (Z_lt_le_dec (dF G - 1048576 * Z.of_nat b0) 1048576) as [LOW|HIGH].
        -
          assert (Z.of_nat b0 = dF G / 1048576) by (destruct HS as [ES|[ES SR]]; nia).
          rewrite Z.min_l in LO by lia. destruct HS as [ES|[ES SR]]; nia.
        - rewrite Z.min_r in LO by lia. lia. }
      pose proof (Z.le_min_r (S + sz + 1 - 1048576 * Z.of_nat b0) 1048576). lia.
    +   rewrite HbZ in *. pose proof (Z.le_min_l (S + sz + 1 - 1048576 * (S / 1048576)) 1048576). lia.
    +   pose proof (Z.le_min_l (S + sz + 1 - 1048576 * Z.of_nat b0) 1048576). nia.
  -   intros b0 Hb0. pose proof (Hfh b0 Hb0). lia.
  -   exact Hdj.
Qed.

Lemma dblocks_G_page : ltac2:(tb__ "0|0|
S1eSfSaS13S11S0S0A2A1S25S2dR2R1A2A1S25R2A1A3Fb;FG;").
Proof. intros. reflexivity. Qed.
Lemma node_addr_G_page : ltac2:(tb__ "0|0|
S1eSfS0SaS0S27S2dR3R2A2R1A2S27R3R1A2A3Fs;Fb;FG;").
Proof. intros. reflexivity. Qed.
Lemma fpage_G_page : ltac2:(tb__ "0|0|
S1eSfSfS0SaS0S2eS2dR4R3A2R2R1A3S2eR4R2R1A3A3Fk;Fb';Fb;FG;").
Proof. intros. reflexivity. Qed.

Lemma sumZ_list_upd : ltac2:(tb__ "0|0|
S13S0A1SfS0S1bR2S10S0R3A2A2SaS0S3aS24S0R4R3R2A4A1S1S9S3aR4A1S1cS0R3R4Z0A4A2R2A2A3F_;Fx;Fi;Fl;").
Proof.
  induction l as [|a l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia.
  unfold sumZ in IH |- *. cbn. rewrite (IH i x) by lia. lia.
Qed.

Lemma dep_cost_G_page : ltac2:(tb__ "0|0|
S1eSfS1bR1S10S0S22R2A1A2A2SaS0S39S2dR3R2A2A1S1S39R3A1S40A2A3F_;Fb;FG;").
Proof.
  intros G b Hb. unfold dep_cost, dep_pages, G_page. cbn [dNB dFP]. rewrite sumZ_list_upd by exact Hb. lia.
Qed.

Lemma depot_mem_page : ltac2:(tb__ "0|6|
S1eS3eS3eSfS28R4R3A2S1bR2S10S0S20R5A1A2A2S4S1cS0R3S22R6A1Z0M0A4S37A2S2S3S40S1S1cS0R4S22R7A1G0A4Z1A2A2S1S1S3Z8S9S23R7A1S3Z100000S5R4A1A2A2A2S40A2Z58A2A2S0SbS2S2eR9R6S1cS0R6S22R9A1G0A4A3M1R1A2S4R1S1G1S40A2A2A2SaS16S42Q8M2A1M3A1M4R8R2A1S18G3S43G2G0A2A2A3F_;Fz;S0SdSbS2S2eRaR7S1cS0R7S22RaA1G0A4A3M5R1A2S4R1S1G5S40A2A2A2A1SaG4R9R2A1RaR2A1A3F_;Fz;S28S2dRaR7A2R8A2F_;F_;F_;F_;F_;F_;Fb;Fm';Fm;FG;").
Proof.
  intros G m m' b HM Hbl Hfp Hhi Hz Hsame.
  destruct HM as [HN HF Hmu Hal Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfpp Hfr Hfh Hdj].
  pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MB.
  set (fb := nth b (dFB G) 0) in *. set (fp := nth b (dFP G) 0) in *.
  destruct (Hfbs fb (nth_In _ _ Hbl)) as (FBal & FBlo & FBhi).
  destruct (Hfpp b Hbl) as [FPr FPpres]. fold fb fp in FPr, FPpres.
  assert (PGLO : IMG_HI <= fpage G b fp) by (unfold fpage; fold fb; unfold PG; lia).
  assert (FBL : fblk (dF G) < 4096) by (apply fblk_lt; lia).

  assert (UV : forall a k v, (forall j, (j < k)%nat -> ~ (fpage G b fp <= a + Z.of_nat j < fpage G b fp + PG)) -> cellZ m a k v -> cellZ m' a k v).
  { intros a k v Hk H j Hj. unfold cellZ, cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. rewrite (Hsame _ (Hk j Hj)). exact (H j Hj). }
  assert (PR : forall lo hi, (forall a, lo <= a < hi -> ~ (fpage G b fp <= a < fpage G b fp + PG)) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hk Hp z Hzz. rewrite (Hsame z (Hk z Hzz)). exact (Hp z Hzz). }
  assert (PR' : forall lo hi, present m lo hi -> present m' lo hi).
  { intros lo hi Hp z Hzz. destruct (zrange_dec (fpage G b fp) (fpage G b fp + PG) z) as [Hin|Hout]; [rewrite (Hz z Hin); eexists; reflexivity | rewrite (Hsame z Hout); exact (Hp z Hzz)]. }
  assert (FL : forall lo hi c, (forall a, lo <= a < hi -> ~ (fpage G b fp <= a < fpage G b fp + PG)) -> filled m lo hi c -> filled m' lo hi c).
  { intros lo hi c Hk Hp z Hzz. rewrite (Hsame z (Hk z Hzz)). exact (Hp z Hzz). }
  assert (STLO : forall a, a < IMG_HI -> ~ (fpage G b fp <= a < fpage G b fp + PG)) by (intros a Ha H; lia).

  assert (NBout : forall nb, In nb (dNB G) -> forall a, nb <= a < nb + NBSZ -> ~ (fpage G b fp <= a < fpage G b fp + PG)).
  { intros nb Hin a Ha H. destruct (In_nth _ _ 0 Hin) as (i & Hi & <-).
    pose proof (dblocks_nf_disj G i b Hi Hbl Hdj) as D. fold fb in D. unfold fpage in H. fold fb in H. unfold FBPAGES, FBSZ, NBSZ, PG in *. lia. }
  unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  constructor; cbn [dN dF dNB dFB dFP G_page]; rewrite ?node_addr_G_page, ?dblocks_G_page.
  all: unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  - split; [exact (proj1 HN)|]. apply UV; [|exact (proj2 HN)]. intros j Hj. apply STLO. lia.
  - destruct HF as (F1 & F2 & F3 & F4). repeat (split; [lia|]). apply UV; [|exact F4]. intros j Hj. apply STLO. lia.
  - apply UV; [|exact Hmu]. intros j Hj. apply STLO. lia.
  - apply PR'; exact Hal.
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [|exact Hr]. apply UV; [|exact Hw]. intros j Hj. apply STLO. lia.
  - exact Hl1.
  - intros j Hj. apply UV; [|exact (Hm1 j Hj)]. intros jj Hjj. apply STLO. lia.
  - intros nb Hin. destruct (Hnb nb Hin) as (A1 & A2 & A3 & A4). repeat (split; [assumption|]). apply PR'. exact A4.
  - intros s Hs. rewrite !node_addr_G_page. destruct (Hlk s Hs) as (h & l & C1 & C2 & C3). exists h, l.
    assert (HjN : (Z.to_nat (s / 65536) < length (dNB G))%nat).
    { pose proof (proj1 Hl1) as X. unfold nblk in X. destruct (Z.eqb_spec (dN G) 0); [lia|].
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      assert (s / 65536 <= dN G / 65536) by (apply Z.div_le_mono; lia). lia. }
    assert (OFF : forall j, 0 <= j < 16 -> ~ (fpage G b fp <= node_addr G s + j < fpage G b fp + 4096)).
    { intros j Hj. unfold node_addr. apply (NBout (nth (Z.to_nat (s / 65536)) (dNB G) 0)); [apply nth_In; exact HjN|].
      pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). lia. }
    split; [|split; [|exact C3]]; apply UV; try assumption; intros j Hj;
      [apply OFF; lia | replace (node_addr G s + 8 + Z.of_nat j) with (node_addr G s + (8 + Z.of_nat j)) by lia; apply OFF; lia].
  - rewrite length_list_upd. exact Hfl.
  - intros b' Hb'. destruct (Hfb b' Hb') as (C1 & C2 & C3 & C4). split; [apply UV; [|exact C1]; intros j Hj; apply STLO; lia|].
    split; [exact C2|]. split; [apply PR'; exact C3 | apply UV; [|exact C4]; intros j Hj; apply STLO; lia].
  - intros b' Hb'. destruct (Hfz b' Hb') as (Z1 & Z2 & Z3). split; [apply FL; [intros a Ha; apply STLO; lia | exact Z1]|].
    split; [apply PR'; exact Z2 | apply FL; [intros a Ha; apply STLO; lia | exact Z3]].
  - exact Hfbs.
  - intros b' Hb'. destruct (Nat.eq_dec b' b) as [->|Hne].
    + rewrite nth_list_upd_same by (rewrite (proj2 Hfl); exact Hbl). fold fb fp. split; [lia|].
      intros z Hzz. destruct (zrange_dec (fpage G b fp) (fpage G b fp + 4096) z) as [Hin|Hout]; [rewrite (Hz z Hin); eexists; reflexivity|].
      rewrite (Hsame z Hout). apply FPpres. unfold fpage, PG in Hout. fold fb in Hout. lia.
    + rewrite nth_list_upd_other by (intros E; apply Hne; symmetry; exact E). destruct (Hfpp b' Hb') as [X Y]. split; [exact X | apply PR'; exact Y].
  - intros b' Hb'. destruct (Nat.eq_dec b' b) as [->|Hne].
    + rewrite nth_list_upd_same by (rewrite (proj2 Hfl); exact Hbl). pose proof (Hfr b Hbl) as Y. fold fp in Y. lia.
    + rewrite nth_list_upd_other by (intros E; apply Hne; symmetry; exact E). exact (Hfr b' Hb').
  - intros b' Hb'. destruct (Nat.eq_dec b' b) as [->|Hne].
    + rewrite nth_list_upd_same by (rewrite (proj2 Hfl); exact Hbl). fold fp. lia.
    + rewrite nth_list_upd_other by (intros E; apply Hne; symmetry; exact E). exact (Hfh b' Hb').
  - exact Hdj.
Qed.

Lemma dblocks_ff_disj : ltac2:(tb__ "0|7|
S1eSfSfS1bR2S10S0S20R3A1A2A2S1bR2S10S0S20R4A1A2A2S1bR4R3A2SfSfS1bR2R1A2S1bR2S10S11S0S0A2M0S25R9A1A2A2S2bS1cG0R4S25RaA1M1S12S0S0Z0M2G2A4M3A4S1cG0R3G1G3A4A2F_;F_;Fj';Fi';ScS2S1S1cS0R6S20R7A1M4G2A4M5S2cA2S1cS0R5G4G2A4M6A2S2S1G6S2cA2G5A2A2F_;F_;F_;F_;Fj;Fi;FG;").
Proof.
  intros G i j Hi Hj Hij DD.
  specialize (DD (length (dNB G) + i)%nat (length (dNB G) + j)%nat ltac:(lia) ltac:(unfold dblocks; rewrite ?length_app, !length_map; lia)).
  unfold dblocks in DD. rewrite !app_nth2 in DD by (rewrite length_map; lia). rewrite !length_map in DD.
  replace (length (dNB G) + i - length (dNB G))%nat with i in DD by lia. replace (length (dNB G) + j - length (dNB G))%nat with j in DD by lia.
  rewrite (nth_map' (fun b0 => (b0, FBSZ)) (dFB G) i 0 (0,0) Hi) in DD. rewrite (nth_map' (fun b0 => (b0, FBSZ)) (dFB G) j 0 (0,0) Hj) in DD.
  unfold ranges_disjointZ in DD. cbn [fst snd] in DD. exact DD.
Qed.

Lemma depot_vm_page : ltac2:(tb__ "0|3|
S1eS3eS45S13S42Q40M0A1M1A1SfG1S28R6R5A2S30R7R5R4A3S1bR4S10S0S20R8A1A2A2S4S1cS0R5S22R9A1Z0M2A4S37A2SaG1R5S43G0S2eRaR6S1cS0R6S22RaA1G2A4A3A2A3S30S2dRbR7A2R9S15G1R6R8A3A3F_;F_;F_;F_;F_;Fp;Fb;Ftp;Fmd;Fm;FG;").
Proof.
  intros G m md tp b p HM [DM DL DA DT] Hbl Hfp Hp.
  pose proof (dm_fp _ _ HM b Hbl) as [FPr _]. pose proof (dm_fb_len _ _ HM) as [_ LEN].
  assert (INB : forall b' k, (b' < length (dFB G))%nat -> 0 <= k < FBPAGES -> 0 <= fpage G b' k /\ fpage G b' k + PG <= 2 ^ 64 /\ nth b' (dFB G) 0 <= fpage G b' k /\ fpage G b' k + PG <= nth b' (dFB G) 0 + FBSZ).
  { intros b' k Hb' Hk. destruct (dm_fbases _ _ HM _ (nth_In _ 0 Hb')) as (A1 & A2 & A3). unfold fpage, PG, FBPAGES, FBSZ, IMG_HI in *.
    nia. }
  constructor; cbn [dNB dFB dFP G_page]; rewrite ?dblocks_G_page; try assumption.
  intros b' k Hb' Hk. cbn [In]. rewrite !fpage_G_page. destruct (Nat.eq_dec b' b) as [->|Hne].
  - rewrite nth_list_upd_same by (rewrite LEN; exact Hbl). split.
    + intros [E|Hin]; [|apply (proj1 (DT b k Hbl Hk)) in Hin; lia].
      assert (EZ : fpage G b (nth b (dFP G) 0) = fpage G b k).
      { destruct (INB b k Hbl Hk) as (X1 & X2 & _). destruct (INB b (nth b (dFP G) 0) Hbl ltac:(lia)) as (Y1 & Y2 & _).
        rewrite <- (u64_lit (fpage G b k)) by (unfold PG in *; lia). rewrite <- (u64_lit (fpage G b (nth b (dFP G) 0))) by (unfold PG in *; lia).
        rewrite <- E, Hp. reflexivity. }
      unfold fpage, PG in EZ. nia.
    + intros Hlt. destruct (Z.eq_dec k (nth b (dFP G) 0)) as [->|Hk']; [left; exact Hp|].
      right. apply (proj2 (DT b k Hbl Hk)). lia.
  - rewrite nth_list_upd_other by (intros E; apply Hne; symmetry; exact E). split.
    + intros [E|Hin]; [|exact (proj1 (DT b' k Hb' Hk) Hin)]. exfalso.
      assert (EZ : fpage G b (nth b (dFP G) 0) = fpage G b' k).
      { destruct (INB b' k Hb' Hk) as (X1 & X2 & _). destruct (INB b (nth b (dFP G) 0) Hbl ltac:(lia)) as (Y1 & Y2 & _).
        rewrite <- (u64_lit (fpage G b' k)) by (unfold PG in *; lia). rewrite <- (u64_lit (fpage G b (nth b (dFP G) 0))) by (unfold PG in *; lia).
        rewrite <- E, Hp. reflexivity. }
      destruct (INB b' k Hb' Hk) as (_ & _ & X3 & X4). destruct (INB b (nth b (dFP G) 0) Hbl ltac:(lia)) as (_ & _ & Y3 & Y4).
      assert (D : nth b' (dFB G) 0 + FBSZ <= nth b (dFB G) 0 \/ nth b (dFB G) 0 + FBSZ <= nth b' (dFB G) 0).
      { destruct (lt_dec b' b); [exact (dblocks_ff_disj G b' b Hb' Hbl ltac:(lia) (dm_disj _ _ HM))|].
        destruct (dblocks_ff_disj G b b' Hbl Hb' ltac:(lia) (dm_disj _ _ HM)); tauto. }
      unfold PG, FBSZ in *. lia.
    + intros Hlt. right. exact (proj2 (DT b' k Hb' Hk) Hlt).
Qed.

Definition pw_disj (l : list (Z * Z)) : Prop := ltac2:(tb__ "0|3|
SfSfS1bR2R1A2S1bR2S10S11S0S0A2M0Vl;A2A2S2bS1cG0R4Vl;S12S0S0Z0M1G1A4M2A4S1cG0R3Vl;G2A4A2F_;F_;Fj;Fi;").

Lemma pw_disj_insert : ltac2:(tb__ "0|2|
S13S11S0S0A2M0A1M1G1G0S47S14G0R3R2A3A1G0S44G0R1S14G0R5R4A3A3S2bR2R4A2F_;Fx;S47S14G0R5S15G0R3R4A3A3A1F_;F_;Fy;Fl2;Fl1;").
Proof.
  intros l1 l2 y HD Hy i j Hij Hj.
  assert (SYM : forall p q, ranges_disjointZ p q -> ranges_disjointZ q p) by (intros p q; unfold ranges_disjointZ; lia).
  rewrite length_app in Hj. cbn [length] in Hj.

  assert (GET : forall k, (k < length l1 + S (length l2))%nat ->
            (k < length l1)%nat /\ nth k (l1 ++ y :: l2) (0,0) = nth k (l1 ++ l2) (0,0)
            \/ k = length l1 /\ nth k (l1 ++ y :: l2) (0,0) = y
            \/ (length l1 < k)%nat /\ nth k (l1 ++ y :: l2) (0,0) = nth (k - 1) (l1 ++ l2) (0,0)).
  { intros k Hk. destruct (lt_dec k (length l1)) as [A|A].
    - left. split; [exact A|]. rewrite !app_nth1 by lia. reflexivity.
    - destruct (Nat.eq_dec k (length l1)) as [->|B].
      + right. left. split; [reflexivity|]. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
      + right. right. split; [lia|]. rewrite !app_nth2 by lia. replace (k - length l1)%nat with (S (k - 1 - length l1)) by lia. reflexivity. }
  assert (INl : forall k, (k < length l1 + length l2)%nat -> In (nth k (l1 ++ l2) (0,0)) (l1 ++ l2)).
  { intros k Hk. apply nth_In. rewrite length_app. exact Hk. }
  destruct (GET i ltac:(lia)) as [[Ai Ei]|[[Ai Ei]|[Ai Ei]]]; destruct (GET j ltac:(lia)) as [[Aj Ej]|[[Aj Ej]|[Aj Ej]]]; rewrite Ei, Ej; try lia.
  - apply HD; [lia | rewrite length_app; lia].
  - apply Hy. apply INl. lia.
  - apply HD; [lia | rewrite length_app; lia].
  - apply SYM. apply Hy. apply INl. lia.
  - apply HD; [lia | rewrite length_app; lia].
Qed.

Lemma dblocks_G_nblk : ltac2:(tb__ "0|2|
S1eS0SaS13S11S0S0A2M0A1S25S33R2R1A2A1S14G0S1dS0G0S0S12S0S0R1S29A4M1Lb;S1fR2A1A4S15G0G1S1dS0G0S0S12S0S0R1S2cA4Lb;S20R2A1A4A3A3A3Fa;FG;").
Proof. intros. unfold dblocks, G_nblk. cbn [dNB dFB]. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity. Qed.

Lemma node_addr_G_nblk : ltac2:(tb__ "0|0|
S1eS0S0S2Z0R1A2S4S7R2Z10000A2S5S10S0S1fR4A1A2A1A2SaS0S27S33R5R4A2R3A2S27R5R3A2A3F_;F_;Fs;Fa;FG;").
Proof.
  intros G a s Hs Hlt. unfold node_addr, G_nblk. cbn [dNB]. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma depot_mem_nblk : ltac2:(tb__ "0|6|
S1eS3eS3eS0S28R4R3A2S2S21R5A1S36A2SaS0S5S10S0S1fR6A1A2A1S7S1S21R6A1Z1M0A2Z10000M1A2A3SaS0S6S1S21R7A1G0A2G1A2Z0M2A3SaS0S6R5S40A2G2A3S2S41R6A2S2S1R7S29A2Z7fffff800000A2S11S0S0A2M3S44G3R1S25RcA1A3S2bR2S12S0S0RaS29A4A2F_;Fbn;S2aRaS1S38S3Z8M4S5S10S0S1fRcA1A2A1A2A2U8R9A4S3fRbRaS1RaS29A2A3S0SdSbS2S1S38S3G4S5S10S0S1fRfA1A2A1A2A2M5R1A2S4R1S1G5G4A2A2A2A1SdSbS2RdR2A2S4R2S1RdS29A2A2A2A1SaS16S42Q8A1A1RfR3A1R10R3A1A3F_;F_;Fz;S28S33RfRcA2RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fm';Fm;FG;").
Proof.
  intros G m m' a HM HDN Hj Hmod Hal Hlo Hhi Hdisj Cslot Pblk Hsame.
  destruct HM as [HN HF Hmu Halc Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfpp Hfr Hfh Hdj].
  set (j := length (dNB G)) in *.
  assert (FBL : fblk (dF G) < 4096) by (apply fblk_lt; lia).
  assert (HjM : Z.of_nat j < MAP1N) by (unfold MAP1N, DNMAX in *; rewrite Hj; apply Z.div_lt_upper_bound; lia).

  assert (OFFs : forall z, z < MAP1 + 8 * Z.of_nat j \/ MAP1 + 8 * Z.of_nat j + 8 <= z -> z < IMG_HI -> m' z = m z).
  { intros z H1 H2. apply Hsame; unfold MAP1, IMG_HI, NBSZ in *; lia. }
  assert (OFFb : forall b0 n0 z, In (b0, n0) (dblocks G) -> b0 <= z < b0 + n0 -> IMG_HI <= b0 -> m' z = m z).
  { intros b0 n0 z Hin Hz Hb0. pose proof (Hdisj _ Hin) as D. unfold ranges_disjointZ in D. cbn [fst snd] in D. apply Hsame; unfold MAP1, MAP1N, IMG_HI, NBSZ in *; lia. }
  assert (UV : forall a0 k v, (forall jj, (jj < k)%nat -> m' (a0 + Z.of_nat jj) = m (a0 + Z.of_nat jj)) -> cellZ m a0 k v -> cellZ m' a0 k v).
  { intros a0 k v Hk H jj Hjj. unfold cellZ, cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. rewrite (Hk jj Hjj). exact (H jj Hjj). }
  assert (PR : forall lo hi, (forall z, lo <= z < hi -> m' z = m z) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hk Hp z Hzz. rewrite (Hk z Hzz). exact (Hp z Hzz). }
  assert (FL : forall lo hi c, (forall z, lo <= z < hi -> m' z = m z) -> filled m lo hi c -> filled m' lo hi c).
  { intros lo hi c Hk Hp z Hzz. rewrite (Hk z Hzz). exact (Hp z Hzz). }
  assert (INnb : forall b0, In b0 (dNB G) -> In (b0, NBSZ) (dblocks G)) by (intros b0 Hb0; unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b0; split; [reflexivity | exact Hb0]).
  assert (INfb : forall b0, In b0 (dFB G) -> In (b0, FBSZ) (dblocks G)) by (intros b0 Hb0; unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b0; split; [reflexivity | exact Hb0]).
  unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  constructor; cbn [dN dF dNB dFB dFP G_nblk].
  all: unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  - split; [exact (proj1 HN)|]. apply UV; [|exact (proj2 HN)]. intros jj Hjj. apply OFFs; lia.
  - destruct HF as (F1 & F2 & F3 & F4). repeat (split; [lia|]). apply UV; [|exact F4]. intros jj Hjj. apply OFFs; lia.
  - apply UV; [|exact Hmu]. intros jj Hjj. apply OFFs; lia.
  - apply PR; [|exact Halc]. intros z Hz. apply OFFs; lia.
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [|exact Hr]. apply UV; [|exact Hw]. intros jj Hjj. apply OFFs; lia.
  - rewrite length_app. cbn [length]. unfold nblk in *. destruct (Z.eqb_spec (dN G) 0); [lia|]. destruct (Z.eqb_spec (dN G + 1) 0); [lia|].
    fold j. pose proof (Z.div_mod (dN G) 65536 ltac:(lia)). pose proof (Z.div_mod (dN G + 1) 65536 ltac:(lia)).
    pose proof (Z.mod_pos_bound (dN G) 65536 ltac:(lia)). lia.
  - intros j' Hj'. destruct (Z.eq_dec j' (Z.of_nat j)) as [->|Hne].
    + rewrite Nat2Z.id. rewrite app_nth2 by lia. fold j. rewrite Nat.sub_diag. cbn [nth]. exact Cslot.
    + assert (E : nth (Z.to_nat j') (dNB G ++ [a]) 0 = nth (Z.to_nat j') (dNB G) 0).
      { destruct (Z_lt_le_dec j' (Z.of_nat j)); [rewrite app_nth1 by lia; reflexivity|].
        rewrite app_nth2 by lia. rewrite (nth_overflow (dNB G)) by lia. destruct (Z.to_nat j' - length (dNB G))%nat as [|k] eqn:E; [lia|]. cbn. destruct k; reflexivity. }
      rewrite E. apply UV; [|exact (Hm1 j' Hj')]. intros jj Hjj. apply OFFs; lia.
  - intros b0 Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
    + destruct (Hnb b0 Hin) as (A1 & A2 & A3 & A4). repeat (split; [assumption|]). apply PR; [|exact A4]. intros z Hz. apply (OFFb b0 1048576 z (INnb _ Hin) Hz A2).
    + split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|]. exact Pblk.
  - intros s Hs.
    assert (HsN : s / 65536 < Z.of_nat j).
    { rewrite Hj. pose proof (Z.div_mod s 65536 ltac:(lia)). pose proof (Z.div_mod (dN G + 1) 65536 ltac:(lia)). pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). nia. }
    rewrite (node_addr_G_nblk G a s) by lia.
    destruct (Hlk s Hs) as (h & l & C1 & C2 & C3). exists h, l.
    assert (HjN : (Z.to_nat (s / 65536) < length (dNB G))%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); fold j; lia).
    destruct (Hnb _ (nth_In _ 0 HjN)) as (_ & Blo & _ & _).
    assert (OFF : forall jj, 0 <= jj < 16 -> m' (node_addr G s + jj) = m (node_addr G s + jj)).
    { intros jj Hjj. unfold node_addr. apply (OFFb (nth (Z.to_nat (s / 65536)) (dNB G) 0) 1048576); [apply INnb; apply nth_In; exact HjN | | exact Blo].
      pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). lia. }
    split; [|split; [|exact C3]]; apply UV; try assumption; intros jj Hjj;
      [apply OFF; lia | replace (node_addr G s + 8 + Z.of_nat jj) with (node_addr G s + (8 + Z.of_nat jj)) by lia; apply OFF; lia].
  - exact Hfl.
  - intros b' Hb'. destruct (Hfb b' Hb') as (C1 & C2 & C3 & C4). split; [apply UV; [|exact C1]; intros jj Hjj; apply OFFs; lia|].
    split; [exact C2|]. split; [apply PR; [|exact C3]; intros z Hz; apply OFFs; lia | apply UV; [|exact C4]; intros jj Hjj; apply OFFs; lia].
  - intros b' Hb'. destruct (Hfz b' Hb') as (Z1 & Z2 & Z3). split; [apply FL; [intros z Hz; apply OFFs; lia | exact Z1]|].
    split; [apply PR; [intros z Hz; apply OFFs; lia | exact Z2] | apply FL; [intros z Hz; apply OFFs; lia | exact Z3]].
  - exact Hfbs.
  - intros b' Hb'. destruct (Hfpp b' Hb') as [X Y]. split; [exact X|]. apply PR; [|exact Y]. intros z Hz.
    destruct (Hfbs _ (nth_In _ 0 Hb')) as (_ & Blo & _). apply (OFFb (nth b' (dFB G) 0) 8388608); [apply INfb; apply nth_In; exact Hb' | lia | exact Blo].
  - exact Hfr.
  - exact Hfh.
  - rewrite dblocks_G_nblk. apply pw_disj_insert; [exact Hdj|]. intros x Hx. apply Hdisj. exact Hx.
Qed.

Lemma node_addr_G_fblk : ltac2:(tb__ "0|0|
S1eS0S0SaS0S27S32R3R2A2R1A2S27R3R1A2A3Fs;Fa;FG;").
Proof. reflexivity. Qed.
Lemma dblocks_fblk : ltac2:(tb__ "0|1|
S1eS0SaS13S11S0S0A2M0A1S25S32R2R1A2A1S14G0S25R2A1S15G0S12S0S0R1S2cA4S17G0A1A3A3A3Fa;FG;").
Proof. intros G a. unfold dblocks, G_fblk. cbn [dNB dFB]. rewrite map_app, app_assoc. reflexivity. Qed.

Lemma nth_app_cases : ltac2:(tb__ "0|2|
S13S0A1S0SfS0S1bR2S48S10S0R4A2U1A2A2ScSbS1bR3S10S0R5A2M0A2SaS0S1cS0R3S14S0R5S15S0R4S17S0A1A3A3R2A4M1S1cS0R3R5R2A4A3A2SbSaSfR3G0A3SaS0G1R4A3A2A2F_;Fd;Fk;Fa;Fl;").
Proof.
  intros l a k d Hk. destruct (lt_dec k (length l)) as [L|L]; [left; split; [exact L | apply app_nth1; exact L]|].
  right. split; [lia|]. rewrite app_nth2 by lia. replace (k - length l)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma depot_mem_fblk : ltac2:(tb__ "0|d|
S1eS3eS3eS0S0S0S10S0S20R6A1A2SfS28R7R6A2SbS2Z1M0R3A2S2R3ZaA2A2ScSaS0R5S23R9A1M1A3SbSaS0R5S1G1S1R4G0A2A2A3S2Z100000M2S1S6G1G2A2R4A2A2A2A2SaS0S5R4A1S7R6G2A2A3SaS0S6R8S40A2Z0M3A3S2S41R9A2S2S1RaS2cA2Z7fffff800000A2S11S0S0A2M4S44G4R1S25RfA1A3S2bR2S12S0S0RdS2cA4A2F_;Fbn;S2aRdS1S1S26Z10M5A2M6S3G5S5R9A1A2A2U8RcA4S3fReS1S1S26Z18A2S3G5S5RaA1A2M7A2S1S1S26Z1cA2M8G7A2A3S2aRfS1G8S3G5S5RbA1A2A2U4G3A4S3fR10S1S26Z8A2M9G6A3S0S4R1S41A2SdSbS2G9R2A2S4R2G6A2A2A1SdSbS2S1G6S3G5S5R10A1A2MaA2R3A2S4R3S1S1S26Z20A2GaA2A2A2A1SaS16S42Q8A1A1MbR15R4A1R16R4A1A3F_;F_;F_;Fz;G4S0S44G4R2S25R16A1A3SbS2S19S0S0R3A3McR2A2S4R2S1GcS1aS0S0R3A3A2A2A2SaGbR16R3A1R17R3A1A3F_;F_;Fz;Fbn;S28S32R15R12A2R13A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;Fsz;FS;Fa;Fm';Fm;FG;").
Proof.
  intros G m m' a S sz b HM Hsz HS HbS Hal Hlo Hhi Hdisj Cdat Pst Cmtx Palc OFFs OFFb.
  pose proof (proj2 (dm_fb_len _ _ HM)) as HL.
  destruct HM as [HN HF Hmu Halc Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfpp Hflo Hfh Hdj].
  pose proof (proj1 HF) as F0. assert (FBL : fblk (dF G) < 4096) by (apply fblk_lt; lia).
  pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MBF. pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DMF.
  pose proof (Z.div_mod S 1048576 ltac:(lia)) as DMS. pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MBS.
  assert (HbN : Z.of_nat b < 4096) by (unfold b; lia).

  assert (HFB : fblk (dF G) = Z.of_nat b /\ -11 <= dF G - 1048576 * Z.of_nat b <= 0).
  { pose proof (proj1 Hfl) as X. fold b in X. unfold fblk in *. destruct HS as [ES|[ES SR]].
    - subst S. assert ((dF G + 1048576 - 1) / 1048576 >= dF G / 1048576) by (apply Z_div_ge; lia). nia.
    - assert (Q : S / 1048576 = dF G / 1048576 + 1).
      { symmetry. apply (Z.div_unique_pos S 1048576 (dF G / 1048576 + 1) (dF G mod 1048576 + sz + 1 - 1048576)); lia. }
      assert ((dF G + 1048576 - 1) / 1048576 = dF G / 1048576 + 1).
      { symmetry. apply (Z.div_unique_pos _ 1048576 (dF G / 1048576 + 1) (dF G mod 1048576 - 1)); lia. }
      nia. }
  destruct HFB as [HFB HOFF].
  assert (UV : forall a0 k v, (forall jj, (jj < k)%nat -> m' (a0 + Z.of_nat jj) = m (a0 + Z.of_nat jj)) -> cellZ m a0 k v -> cellZ m' a0 k v).
  { intros a0 k v Hk H jj Hjj. unfold cellZ, cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. rewrite (Hk jj Hjj). exact (H jj Hjj). }
  assert (PR : forall lo hi, (forall z, lo <= z < hi -> m' z = m z) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hk Hp z Hzz. rewrite (Hk z Hzz). exact (Hp z Hzz). }
  assert (FL : forall lo hi c, (forall z, lo <= z < hi -> m' z = m z) -> filled m lo hi c -> filled m' lo hi c).
  { intros lo hi c Hk Hp z Hzz. rewrite (Hk z Hzz). exact (Hp z Hzz). }
  assert (INnb : forall b0, In b0 (dNB G) -> In (b0, NBSZ) (dblocks G)) by (intros b0 Hb0; unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b0; split; [reflexivity | exact Hb0]).
  assert (INfb : forall b0, In b0 (dFB G) -> In (b0, FBSZ) (dblocks G)) by (intros b0 Hb0; unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b0; split; [reflexivity | exact Hb0]).
  unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  constructor; cbn [dN dF dNB dFB dFP G_fblk].
  all: unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  - split; [exact (proj1 HN)|]. apply UV; [|exact (proj2 HN)]. intros jj Hjj. apply OFFs; lia.
  - destruct HF as (F1 & F2 & F3 & F4). repeat (split; [lia|]). apply UV; [|exact F4]. intros jj Hjj. apply OFFs; lia.
  - apply UV; [|exact Hmu]. intros jj Hjj. apply OFFs; lia.
  - exact Palc.
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [|exact Hr]. apply UV; [|exact Hw]. intros jj Hjj. apply OFFs; lia.
  - exact Hl1.
  - intros j Hj. apply UV; [|exact (Hm1 j Hj)]. intros jj Hjj. apply OFFs; lia.
  - intros b0 Hin. destruct (Hnb b0 Hin) as (A1 & A2 & A3 & A4). repeat (split; [assumption|]). apply PR; [|exact A4]. intros z Hz. apply (OFFb (b0, 1048576) z (INnb _ Hin)). cbn [fst snd]. lia.
  - intros s Hs.
    assert (HjN : (Z.to_nat (s / 65536) < length (dNB G))%nat).
    { unfold nblk in Hl1. destruct (Z.eqb_spec (dN G) 0); [lia|]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      assert (s / 65536 <= dN G / 65536) by (apply Z.div_le_mono; lia). lia. }
    rewrite !node_addr_G_fblk.
    destruct (Hlk s Hs) as (h & l & C1 & C2 & C3). exists h, l.
    assert (OFF : forall jj, 0 <= jj < 16 -> m' (node_addr G s + jj) = m (node_addr G s + jj)).
    { intros jj Hjj. unfold node_addr. apply (OFFb (nth (Z.to_nat (s / 65536)) (dNB G) 0, 1048576)); [apply INnb; apply nth_In; exact HjN|]. cbn [fst snd].
      pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). lia. }
    split; [|split; [|exact C3]]; apply UV; try assumption; intros jj Hjj;
      [apply OFF; lia | replace (node_addr G s + 8 + Z.of_nat jj) with (node_addr G s + (8 + Z.of_nat jj)) by lia; apply OFF; lia].
  - rewrite !length_app. cbn [length]. fold b. split; [lia | lia].
  - intros b0 Hb0. rewrite length_app in Hb0. cbn [length] in Hb0. fold b in Hb0.
    destruct (nth_app_cases (dFB G) a b0 0 Hb0) as [[L E]|[-> E]]; rewrite E.
    + destruct (Hfb b0 L) as (C1 & C2 & C3 & C4). pose proof (proj1 (Nat2Z.inj_lt _ _) L) as LZ. fold b in LZ.
      split; [apply UV; [|exact C1]; intros jj Hjj; apply OFFs; lia|]. split; [exact C2|].
      split; [apply PR; [|exact C3]; intros z Hz; apply OFFs; lia | apply UV; [|exact C4]; intros jj Hjj; apply OFFs; lia].
    + fold b. split; [exact Cdat|]. split; [lia|]. split; [exact Pst | exact Cmtx].
  - intros b0 Hb0. rewrite length_app in Hb0. cbn [length] in Hb0. fold b in Hb0. destruct (Hfz b0 ltac:(fold b; lia)) as (Z1 & Z2 & Z3).
    split; [apply FL; [intros z Hz; apply OFFs; lia | exact Z1]|]. split; [apply PR; [intros z Hz; apply OFFs; lia | exact Z2] | apply FL; [intros z Hz; apply OFFs; lia | exact Z3]].
  - intros b0 Hin. apply in_app_or in Hin as [Hin|[<-|[]]]; [exact (Hfbs b0 Hin)|]. split; [exact Hal|]. split; [exact Hlo | exact Hhi].
  - intros b0 Hb0. rewrite length_app in Hb0. cbn [length] in Hb0. fold b in Hb0.
    destruct (nth_app_cases (dFB G) a b0 0 Hb0) as [[L E]|[-> E]]; rewrite E.
    + rewrite app_nth1 by (rewrite HL; exact L). destruct (Hfpp b0 L) as [X Y]. split; [exact X|]. apply PR; [|exact Y]. intros z Hz.
      apply (OFFb (nth b0 (dFB G) 0, 8388608)); [apply INfb; apply nth_In; exact L | cbn [fst snd]; lia].
    + fold b. rewrite app_nth2 by (rewrite HL; lia). rewrite HL, Nat.sub_diag. cbn [nth]. split; [lia|]. rewrite Z.mul_0_r, Z.add_0_r. intros z Hz. lia.
  - intros b0 Hb0. rewrite length_app in Hb0. cbn [length] in Hb0. fold b in Hb0.
    destruct (lt_dec b0 (length (dFB G))) as [L|L].
    + rewrite app_nth1 by (rewrite HL; exact L). exact (Hflo b0 L).
    + assert (b0 = b) as -> by (unfold b; lia). rewrite app_nth2 by (rewrite HL; lia). fold b. rewrite HL. unfold b. rewrite Nat.sub_diag. cbn [nth]. fold b.
      pose proof (Z.le_min_l (dF G - 1048576 * Z.of_nat b) 1048576). lia.
  - intros b0 Hb0. rewrite length_app in Hb0. cbn [length] in Hb0. fold b in Hb0.
    destruct (lt_dec b0 (length (dFB G))) as [L|L].
    + rewrite app_nth1 by (rewrite HL; exact L). exact (Hfh b0 L).
    + assert (b0 = b) as -> by (unfold b; lia). rewrite app_nth2 by (rewrite HL; lia). rewrite HL. unfold b. rewrite Nat.sub_diag. cbn [nth]. fold b. lia.
  - rewrite dblocks_fblk. refine (pw_disj_insert (dblocks G) [] (a, _) _ _); rewrite app_nil_r; [exact Hdj | exact Hdisj].
Qed.

Lemma depot_mem_stc : ltac2:(tb__ "0|8|
S1eS3eS3eS0S28R4R3A2S2Z0R2A2S4S1R3Z1M0A2S3bA2S3fR5S1S1S26Z18A2M1S3Z10M2R4A2M3A2S1S1S26Z1cA2M4G3A2A3S3fR6S1G1S3G2S1R5G0A2A2M5A2S1G4G5A2A3S0SdSbS2S1G1S3G2R7A2M6A2R1A2S4R1S1G4G6A2A2A2A1SdSbS2S1G1S3G2S1R8G0A2A2M7A2R2A2S4R2S1G4G7A2A2A2A1SaS16S42Q8A1A1RaR3A1RbR3A1A3F_;F_;Fz;S28RaR8A2F_;F_;F_;F_;F_;F_;Fb;Fm';Fm;FG;").
Proof.
  intros G m m' b HM HbO HbN P1 P2 Hsame.
  destruct HM as [HN HF Hmu Halc Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfpp Hflo Hfh Hdj].
  pose proof (proj1 HF) as F0. assert (FBL : fblk (dF G) < 4096) by (apply fblk_lt; lia).
  assert (UV : forall a0 k v, (forall jj, (jj < k)%nat -> m' (a0 + Z.of_nat jj) = m (a0 + Z.of_nat jj)) -> cellZ m a0 k v -> cellZ m' a0 k v).
  { intros a0 k v Hk H jj Hjj. unfold cellZ, cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. rewrite (Hk jj Hjj). exact (H jj Hjj). }
  assert (PR : forall lo hi, (forall z, lo <= z < hi -> m' z = m z) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hk Hp z Hzz. rewrite (Hk z Hzz). exact (Hp z Hzz). }
  assert (FL : forall lo hi c, (forall z, lo <= z < hi -> m' z = m z) -> filled m lo hi c -> filled m' lo hi c).
  { intros lo hi c Hk Hp z Hzz. rewrite (Hk z Hzz). exact (Hp z Hzz). }

  assert (PS : forall b0, 0 <= b0 < NFBLK -> present m (STORE + 24 + 16 * b0) (STORE + 28 + 16 * b0) -> present m' (STORE + 24 + 16 * b0) (STORE + 28 + 16 * b0)).
  { intros b0 Hrg Hp. destruct (Z.eq_dec b0 b) as [->|N1]; [exact P1|]. destruct (Z.eq_dec b0 (b + 1)) as [->|N2]; [exact P2|].
    apply PR; [|exact Hp]. intros z Hz. apply Hsame; lia. }
  assert (OFF : forall z, z < STORE + 16 \/ (exists b0, STORE + 16 + 16 * b0 <= z < STORE + 24 + 16 * b0 \/ STORE + 28 + 16 * b0 <= z < STORE + 32 + 16 * b0) \/ STORE + 16 + 16 * NFBLK <= z -> m' z = m z).
  { intros z Hz. apply Hsame; [intros R | intros R]; (destruct Hz as [X|[[b0 X]|X]]; [lia | | unfold NFBLK in *; lia]); nia. }
  unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  constructor.
  all: unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG, IMG_HI in *.
  - split; [exact (proj1 HN)|]. apply UV; [|exact (proj2 HN)]. intros jj Hjj. apply OFF. right. right. lia.
  - destruct HF as (F1 & F2 & F3 & F4). repeat (split; [lia|]). apply UV; [|exact F4]. intros jj Hjj. apply OFF. left. lia.
  - apply UV; [|exact Hmu]. intros jj Hjj. apply OFF. right. right. lia.
  - apply PR; [|exact Halc]. intros z Hz. apply OFF. left. lia.
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [|exact Hr]. apply UV; [|exact Hw]. intros jj Hjj. apply OFF. right. right. lia.
  - exact Hl1.
  - intros j Hj. apply UV; [|exact (Hm1 j Hj)]. intros jj Hjj. apply OFF. right. right. lia.
  - intros b0 Hin. destruct (Hnb b0 Hin) as (A1 & A2 & A3 & A4). repeat (split; [assumption|]). apply PR; [|exact A4]. intros z Hz. apply OFF. right. right. lia.
  - intros s Hs. destruct (Hlk s Hs) as (h & l & C1 & C2 & C3). exists h, l.
    assert (HjN : (Z.to_nat (s / 65536) < length (dNB G))%nat).
    { unfold nblk in Hl1. destruct (Z.eqb_spec (dN G) 0); [lia|]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      assert (s / 65536 <= dN G / 65536) by (apply Z.div_le_mono; lia). lia. }
    destruct (Hnb _ (nth_In _ 0 HjN)) as (_ & Blo & _ & _).
    assert (OFFn : forall jj, 0 <= jj < 16 -> m' (node_addr G s + jj) = m (node_addr G s + jj)).
    { intros jj Hjj. apply OFF. right. right. unfold node_addr. pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). lia. }
    split; [|split; [|exact C3]]; apply UV; try assumption; intros jj Hjj;
      [apply OFFn; lia | replace (node_addr G s + 8 + Z.of_nat jj) with (node_addr G s + (8 + Z.of_nat jj)) by lia; apply OFFn; lia].
  - exact Hfl.
  - intros b0 Hb0. destruct (Hfb b0 Hb0) as (C1 & C2 & C3 & C4). pose proof (proj1 (Nat2Z.inj_lt _ _) Hb0) as LZ. pose proof (proj1 Hfl).
    split; [apply UV; [|exact C1]; intros jj Hjj; apply OFF; right; left; exists (Z.of_nat b0); lia|]. split; [exact C2|].
    split; [apply PS; [lia | exact C3] | apply UV; [|exact C4]; intros jj Hjj; apply OFF; right; left; exists (Z.of_nat b0); lia].
  - intros b0 Hb0. destruct (Hfz b0 Hb0) as (Z1 & Z2 & Z3).
    split; [apply FL; [intros z Hz; apply OFF; right; left; exists b0; lia | exact Z1]|].
    split; [apply PS; [lia | exact Z2] | apply FL; [intros z Hz; apply OFF; right; left; exists b0; lia | exact Z3]].
  - exact Hfbs.
  - intros b0 Hb0. destruct (Hfpp b0 Hb0) as [X Y]. split; [exact X|]. apply PR; [|exact Y]. intros z Hz.
    destruct (Hfbs _ (nth_In _ 0 Hb0)) as (_ & Blo2 & _). apply OFF. right. right. nia.
  - exact Hflo.
  - exact Hfh.
  - exact Hdj.
Qed.
End SegD_ins.

(* [comment removed for export] *)
Module CertStackFree.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "pair"; "prod"; "app"; "nat"; "None"; "false"; "true"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "sobj"; "SPUle"; "SVar"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "mkCell"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "F8"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "to_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "NW"; "cuts_sf"; "exits_sf"; "segsA"; "F_win"; "O_khigh"; "Post_sf"; "Pre_sf"; "gsv"; "shb"; "vG"; "win_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "IMG_HI"; "K_HIGH_MEM_END"; "@Corelib.Init.Logic"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.StackFree"; "F_sf"; "objs_sf"; "O_fshadow"; "f5_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "V_FL"; "mkA"; "A_globals"; "ae_ret_stack_free"; "ae_stack_free"; "flag_obj"; "flagbyte_obj"; "frame_obj"; "pre_facts"; "stack_malloc_depth"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition segsA : list Segment := Asan.M.loaded_segments.

Definition NW : positive := 200%positive.
Definition GW : positive := 160%positive.
Definition vG : positive := 150%positive.
Definition shb : sv := SLit SHADOW_OFF.

Definition gsv (e : sv) : sv := SAlu ALU_SRL e (SLit 3).

Definition khigh_cells : list (Z * nat * sv) := ltac2:(tb__ "0|4|
S0S4S4S16S6A2M0SdA2M1S3G0SdS3S16S6Zf20e0U8M2A4ScS2eA1A4S0G1S3G0SdS3S16S6Zf20e8G2A4ScZ0A1M3A4S0G1S3G0SdS3S16S6Zf20f0G2A4G3A4S1G1A1A3A3A3").
Definition O_khigh : sobj := carved (SLit 0) 0xf20e0 0xf20f8 khigh_cells.

Definition F_win (hi : bool) (e : sv) (sz : Z) : list sprop := ltac2:(tb__ "0|4|
S2SaSbA1Lhi;Vhi;S0SbSfScS2bA1Ve;A2S0SbSfVe;ScZ7fffff800000A1M0A2S0SbSfS11S1dVe;ScVsz;A1A3M1G0A2S1SbA1M2A3A3A3S0SbSfScS2dA1Ve;A2S0SbSfVe;ScS2cA1M3A2S0SbSfG1G3A2G2A3A3A3X2x2").
Definition win_hyp (hi : bool) (a len : Z) : Prop := ltac2:(tb__ "0|0|
S2OLhi;Vhi;S19S2bVa;A2S19S1aVa;Vlen;A2S2cA2X2x2").
Lemma win_hyp_cases : ltac2:(tb__ "0|0|
S16S16S31S19S1aR2R1A2S2cA2S19S2bR2A2A2S30S2S2S2aR1R4R3A3Lhi;A2F_;Flen;Fa;").
Proof. intros a len [H|H]; [exists false|exists true]; exact H. Qed.

Section StackFree.
Variable E : aentry.
Variable hi : bool.
Variable c : Z.
Let SZ : Z := fs_frame_size c.
Let NSH : Z := SZ / 8.

Definition O_fshadow (cs : list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|0|
S46S11S1dS27S10PcA1A1S28A3Z0VNSH;Vcs;A4").

Definition F_sf : list sprop := ltac2:(tb__ "0|2|
S5SbS23Vhi;S10PcA1M0VSZ;A3S5SbS0SbSfScZ1000A1S10S3bA1M1A2S0SbSfS11S1dG1ScZ1A1A3ScZ7fffff800000A1A2S1SbA1A3A3S5SbS18S29G0A2S43S44A1A3A3A3").

Definition objs_sf (flagcells : list cell) (shcells : list (Z * nat * sv)) : list sobj := ltac2:(tb__ "0|3|
S5SeS0SeS45S0SeS42S10PcA1M0Vc;A2S0SeS40G0Vc;S10S3bA1M1A3S0SeS41G1Vflagcells;A2S1SeA1M2A3A3A3A3S5SeS3dS0SeS24S0SeS38Vshcells;A1G2A3A3A3A3").

Definition Pre_sf : axst := ltac2:(tb__ "0|0|
S3cS14S3fVE;Vc;A2S34S32S13S7SdA1S37S1S12A1S1S4S4S16S6A2SdA2A1A2S36S1fS8A9S1S4SdSdA2A1A2").

Definition F5W : Z := 0xf5f5f5f5f5f5f5f5.
Fixpoint f5_cells (k : nat) : list (Z * nat * sv) :=
  match k with O => [] | S k' => (8 * Z.of_nat k', 8%nat, SLit F5W) :: f5_cells k' end.
Definition Post_sf : axst := ltac2:(tb__ "0|1|
S3cS14S3eVE;Vc;A2S33S1eA1S32S13S7SdA1S37S0S12S15ScZ0A1M0Z1G0A3S1S12A1A3S39S1cS1bVNSH;Z8A2A1A1A2S36S1fS8A9S1S4SdSdA2A1A2").
End StackFree.

Definition cuts_sf (hi : bool) (c : Z) : list axst := ltac2:(tb__ "0|0|
S0S17S26S3aVhi;Vc;A3S1S17A1A3").
Definition exits_sf (hi : bool) (c : Z) : list axst := ltac2:(tb__ "0|0|
S0S17S25S3aVhi;Vc;A3S1S17A1A3").

Lemma cert_sf5 : ltac2:(tb__ "0|1|
S2S2fS2S35S22Uc8S1S16A1S1eS20R1Z5M0A2S21R1G0A2A6S9A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cert_sf6 : ltac2:(tb__ "0|1|
S2S2fS2S35S22U190S1S16A1S1eS20R1Z6M0A2S21R1G0A2A6S9A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertStackFree.

(* [comment removed for export] *)
Module GlueMC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "sub"; "to_nat"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "cell"; "sv"; "rm"; "soff"; "eval"; "DUnknown"; "SLit"; "mkObj"; "ss_objs"; "sstate"; "valuation"; "c_width"; "c_off"; "mkSS"; "obj_holds"; "obj_range"; "ranges_disjoint"; "rom_ok"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "c_val"; "enc_bytes"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "nat"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC.WithSegs"; "gcells_in_view"; "gcells_inside"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymFrame SymEntail SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition gcells_inside (rho : valuation) (lo hi : Z) (cs : list cell) : Prop := ltac2:(tb__ "0|2|
S3aSbSbS28S1Vlo;SeVrho;S17R1A1A2M0A2S28S1S0G0S16R1A1M1A2Vhi;A2S28S1Z1G1A2S1G1Z8A2A2A2A2Lc;Vcs;A3").

Definition gcells_in_view (rho : valuation) (rdv : word -> option byte) (b : Z) (cs : list cell) : Prop := ltac2:(tb__ "0|2|
S3aSbSbS39S48R1S6S16R2A1A1A2S29S34S2cQ8M0A1M1A1Vrdv;S2bQ40S0S0Vb;SeVrho;S17R3A1A2A2S7R2A1A2A2A1S33G1S3bG1R2S27S6S16R3A1A1SfVrho;S26R3A1A2A2S2bG0Z0A2A4A2A3F_;Fj;Lc;Vcs;A3").

Lemma obj_holds_frame_gen : ltac2:(tb__ "0|5|
S15S40S2cQ40M0A1S34S2cQ8A1M1A1M2F_;ScS8S8S31SbA1S1cVsegs;R6A2S2dG0SfR8R5A2A2S8S1S4S3Z2M3Z3eA2M4A1R5A2S1R6R5A2S2R6G4A2S1Z0S0R4R8A2A2S1S0R5R8A2S3G3Z40A2A2S3fReRaR9R8A4S8S28S1RcR1A2S2R1RbA2A2S28S29S30S2fVsegs;RfS2bG0S0R9R2A2A2A3S32A3S2aG1G1S29G2S2eVsegs;R10S2bG0S0RaR3A2A2A3S33G1R1A2A3Lx;A2A2F_;Foff;S3eR10S2eVsegs;ReA2R8RaA4S19Vsegs;R11S42R10RfA2S12ReS11RdA1S11RcA1RbS10A5A4F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;Fcs;Fhi;Flo;Fbase;Fm;Fms;Frho;").
Proof using .
  intros rho ms m base lo hi cs Hrom b Hlo Hlh Hhi Hb0 Hb1 Hins Hview Hcells.
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
  rewrite !soff_lit_small by lia.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. destruct (Hview off Hoff) as [W R]. exact (wview_of_views segs m _ W R). }
  split.
  { revert Hins Hcells. induction cs as [|c t IH]; intros Hins Hcells; [constructor|].
    apply Forall_cons_iff in Hins as [(Ho1 & Ho2 & Hk) Hins'].
    apply Forall_cons_iff in Hcells as [Hcv Hcells'].
    constructor; [|apply IH; assumption].
    unfold SymState.cell_holds.
    split; [lia|]. split; [lia|].
    apply rd_bytes_of_nth.
    - rewrite enc_bytes_length. reflexivity.
    - rewrite oaddr_unsigned by lia. fold b. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. fold b. rewrite (rd_with_mem segs) by exact Hrom.
      exact (Hcv j Hj). }
  split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite (rd_with_mem segs) by exact Hrom.
  destruct (Hview off Hoff) as [_ [x Hx]]. exists x. exact Hx.
Qed.

Lemma SPA_carve_gen : ltac2:(tb__ "0|4|
S3dS15S45S31S2cQ40M0A1A1S41ScS8S8S31SbA1S9S3cVsegs;RaR8R9R7R6A6S43R9A1S14S12R7S11R6A1S11R5A1R4S10A5SaS18S22R2A1S23R2A1S1fR2A1S1eR2A1S24R2A1S35SaS13R2A1S36SaR1S37SaA1A3A3S1dR2A1R4S20R2A1A9S14S29S30S25R1A1S32A3S47S21R4A1R6A2S2dG0SfRfRbA2A2S8S1S4S3Z2M1Z3eA2M2A1RbA2S1RcRbA2S2RcG2A2S1Z0S0R4ReA2A2S1S0R5ReA2S3G1Z40A2A2S3fR15R10RfReA4S3aSaSaS1bS1aR17R1A2S38S8S8S0R8R12A2S0R8R11A2A4A2Lo';S13RcA1A3S8S28S1R13R1A2S2R1R12A2A2S28S29S30S2fVsegs;SdR19A1S2bG0S0RaR2A2A2A3S32A3S2aS2cQ8A1M3G3S29S34G3A1S2eVsegs;SdR1aA1S2bG0S0RbR3A2A2A3S33G3R1A2A3Lx;A2A2F_;Foff;S3eR18S2eVsegs;SdR18A1A2R9R11A4S46R19R18S0RaR14A2S0RaR13A2A4S3cVsegs;R1bS44R19ReA2R1aR18R17A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';To;TS;F_;Fnx;Fcs;Fhi;Flo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w base lo hi cs nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S o S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hins Hdisj Hview Hcells Hxs.
  subst S. split; [|exact Hk].
  destruct w as [tr [ms md]].
  assert (Hrom : rom_ok segs (vms md tp ms)).
  { unfold virt in Hsm. cbn in Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). }
  assert (Hor : obj_range rho o = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi]. fold b. rewrite !soff_lit_small by lia. reflexivity. }
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_extend_objs segs rho (ax_S A) tr (vms md tp ms) (vmd md) [o] nx Hsm Hwf').
    + constructor; [|constructor]. apply obj_holds_frame_gen; auto.
    + constructor; [|constructor]. rewrite Hor. exact Hdisj.
    + cbn. split; [constructor | exact I].
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hor. cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

Lemma obj_holds_frame_gsym : ltac2:(tb__ "0|4|
S15S40S2cQ40M0A1S34S2cQ8A1M1A1M2F_;ScScScS31SbA1S1cVsegs;R6A2S2dG0SfR8R5A2A2S8SeR9R5A2S8SeRaR5A2S8S1R2R1A2S2S5R2R3A2S3Z2M3Z3fA2A2S1Z0S0R5R4A2A2S1S0R6R4A2S3G3Z40A2A2S3fRfR6R5R9A4S8S28S1R8R1A2S2R1R7A2A2S28S29S30S2fVsegs;R10S2bG0S0RaR2A2A2A3S32A3S2aG1G1S29G2S2eVsegs;R11S2bG0S0RbR3A2A2A3S33G1R1A2A3Lx;A2A2F_;Foff;S3eR11S2eVsegs;RfA2R9RbA4S19Vsegs;R12S42R11R10A2S12RfReRdRcS10A5A4F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;Fcs;Fehi;Felo;Fbase;Fm;Fms;Frho;").
Proof using .
  intros rho ms m base elo ehi cs Hrom b lo hi Hlh Hw Hb0 Hb1 Hins Hview Hcells.
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b. fold lo. fold hi.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. destruct (Hview off Hoff) as [W R]. exact (wview_of_views segs m _ W R). }
  split.
  { revert Hins Hcells. induction cs as [|c t IH]; intros Hins Hcells; [constructor|].
    apply Forall_cons_iff in Hins as [(Ho1 & Ho2 & Hk) Hins'].
    apply Forall_cons_iff in Hcells as [Hcv Hcells'].
    constructor; [|apply IH; assumption].
    unfold SymState.cell_holds.
    split; [lia|]. split; [lia|].
    apply rd_bytes_of_nth.
    - rewrite enc_bytes_length. reflexivity.
    - rewrite oaddr_unsigned by lia. fold b. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. fold b. rewrite (rd_with_mem segs) by exact Hrom.
      exact (Hcv j Hj). }
  split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite (rd_with_mem segs) by exact Hrom.
  destruct (Hview off Hoff) as [_ [x Hx]]. exists x. exact Hx.
Qed.

Lemma SPA_carve_gsym : ltac2:(tb__ "0|3|
S3dS15S45S31S2cQ40M0A1A1S41ScScScS31SbA1S9S3cVsegs;RaR8R9R7R6A6S43R9A1S14S12R7R6R5R4S10A5SaS18S22R2A1S23R2A1S1fR2A1S1eR2A1S24R2A1S35SaS13R2A1S36SaR1S37SaA1A3A3S1dR2A1R4S20R2A1A9S14S29S30S25R1A1S32A3S47S21R4A1R6A2S2dG0SfRfRbA2A2S8SeR10RbA2S8SeR11RbA2S8S1R2R1A2S2S5R2R3A2S3Z2M1Z3fA2A2S1Z0S0R5R4A2A2S1S0R6R4A2S3G1Z40A2A2S3fR16R6R5RfA4S3aSaSaS1bS1aR18R1A2S38S8S8S0R9R8A2S0R9R7A2A4A2Lo';S13RdA1A3S8S28S1R9R1A2S2R1R8A2A2S28S29S30S2fVsegs;SdR1aA1S2bG0S0RbR2A2A2A3S32A3S2aS2cQ8A1M2G2S29S34G2A1S2eVsegs;SdR1bA1S2bG0S0RcR3A2A2A3S33G2R1A2A3Lx;A2A2F_;Foff;S3eR19S2eVsegs;SdR19A1A2RaR12A4S46R1aR19S0RbRaA2S0RbR9A2A4S3cVsegs;R1cS44R1aRfA2R1bR19R18A6F_;F_;F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;F_;TS';To;TS;F_;Fnx;Fcs;Fehi;Felo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w base elo ehi cs nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S o S' Hwf' Hnx b lo hi Hlh Hw63 Hlo Hhi Hins Hdisj Hview Hcells Hxs.
  subst S. split; [|exact Hk].
  destruct w as [tr [ms md]].
  assert (Hrom : rom_ok segs (vms md tp ms)).
  { unfold virt in Hsm. cbn in Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). }
  assert (Hor : obj_range rho o = (b + lo, b + hi)) by reflexivity.
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_extend_objs segs rho (ax_S A) tr (vms md tp ms) (vmd md) [o] nx Hsm Hwf').
    + constructor; [|constructor]. apply obj_holds_frame_gsym; auto.
    + constructor; [|constructor]. rewrite Hor. exact Hdisj.
    + cbn. split; [constructor | exact I].
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hor. cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.
End WithSegs.
End GlueMC.

