(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "modulo"; "div"; "sub"; "pow"; "eqb"; "to_nat"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "iff"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_maps"; "event"; "vm_init_sp"; "vm_noaccess"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "dFB"; "DG"; "dNB"; "dN"; "dF"; "dFP"; "mkDG"; "list_upd"; "@Corelib.Init.Datatypes"; "list"; "pair"; "app"; "bool"; "prod"; "cons"; "fst"; "snd"; "option"; "false"; "nil"; "length"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "STORE"; "cellZ"; "FBSZ"; "NBSZ"; "DFP"; "MAP1"; "depot_mem"; "DFPw"; "NFBLK"; "fblk"; "in_blk"; "dblocks"; "depot_vm"; "DEPOT"; "FBPAGES"; "MAP1N"; "dep_cost"; "dfp_static"; "wentry"; "G0"; "NIDS"; "NODESMU"; "TABSZ"; "dep_pages"; "droom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf.WithSegs"; "depot_inv"; "dpost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "present"; "bview"; "cell_ok"; "filled"; "mkACell"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition DEPOT : Z := 0x1d32d8.
Definition TABSZ : Z := 1048576.
Definition NIDS : Z := 0x5d32d8.
Definition NODESMU : Z := 0x5d32e0.
Definition MAP1 : Z := 0x5d32e8.
Definition MAP1N : Z := 32768.
Definition NBSZ : Z := 1048576.
Definition STORE : Z := 0x1c32c8.
Definition NFBLK : Z := 4096.
Definition FBSZ : Z := 8388608.
Definition FBPAGES : Z := 2048.
Definition DNMAX : Z := 2 ^ 28 + 1.

Definition nblk (N : Z) : Z := ltac2:(tb__ "0|1|
S28S0L_;SaVN;Z0M0A2G0S2S7VN;Z10000A2Z1A2X28x2").
Definition fblk (F : Z) : Z := ltac2:(tb__ "0|1|
S7S8S2VF;Z100000M0A2Z1A2G0A2").
Definition sumZ (l : list Z) : Z := fold_right Z.add 0 l.

Definition dblocks (G : DG) : list (Z * Z) := ltac2:(tb__ "0|1|
S27S29S0S0A2M0S5bS0G0S0S26S0S0R1S3cA4Lb;S1fVG;A1A4S5bS0G0S0S26S0S0R1S3bA4Lb;S1dVG;A1A4A3").
Definition wentry (bn : Z * Z) : word * word := ltac2:(tb__ "0|2|
S26S31Q40M0A1M1G1S32G0S2bS0S0Vbn;A3A2S32G0S2cS0S0Vbn;A3A2A4").
Definition in_dblocks (G : DG) (a : Z) : Prop := ltac2:(tb__ "0|2|
S10S29S0S0A2M0G0SdS13G0R1S44VG;A1A3SdS3S2bS0S0R1A3M1Va;A2S4Va;S2G1S2cS0S0R1A3A2A2A2A2Lbn;A2").

Definition dep_pages (G : DG) : Z := sumZ (dFP G).
Definition dep_cost (G : DG) : Z := ltac2:(tb__ "0|0|
S2S5S3cScS30S0S1fVG;A1A2A1A2S5S37S50VG;A1A2A2").

Definition DEPC : Z := NBSZ + 3 * PG.

Definition droom (G : DG) : Z := ltac2:(tb__ "0|1|
S2S37S28S0L_;SaS6S2S20VG;A1Z1A2Z10000A2Z0M0A2S3cG0X28x2A2").

Definition in_blk (bases : list Z) (sz : Z) (a : Z) : Prop := ltac2:(tb__ "0|0|
S10S0S0SdS13S0R1Vbases;A3SdS3R1Va;A2S4Va;S2R1Vsz;A2A2A2A2Lb;A2").

Definition dfp_static (a : Z) : Prop := ltac2:(tb__ "0|1|
SfSdS3S46Va;A2S4Va;S2S3eS5Z8S48A2A2A2A2SdS3S39Va;A2S4Va;S2S2S39Z10M0A2S5G0S41A2A2A2A2A2").

Definition DFP (G : DG) (a : Z) : Prop := ltac2:(tb__ "0|0|
SfS4aVa;A1SfS43S1fVG;A1S3cVa;A3S43S1dVG;A1S3bVa;A3A2A2").

Definition DFPw (G : DG) (a : Z) : Prop := ltac2:(tb__ "0|0|
SfSdS4aVa;A1SdS11SdS3S2S39Z10A2Va;A2S4Va;S2S39Z18A2A2A2A1S11SdS3S3eVa;A2S4Va;S2S3eZ8A2A2A2A1A2A2SfS43S1fVG;A1S3cVa;A3S43S1dVG;A1S3bVa;A3A2A2").

Lemma DFPw_DFP : ltac2:(tb__ "0|0|
S1eS0S40R2R1A2S3dR3R2A2F_;Fa;FG;").
Proof. intros G a [[H _]|[H|H]]; [left|right;left|right;right]; exact H. Qed.

Definition cellZ (m : bview) (a : Z) (w : nat) (v : Z) : Prop := ltac2:(tb__ "0|0|
S57Vm;S59Va;Vw;Vv;A3A2").

Definition node_addr (G : DG) (s : Z) : Z := ltac2:(tb__ "0|1|
S2S5aS0SbS7Vs;Z10000M0A2A1S1fVG;A1Z0A4S5Z10S6Vs;G0A2A2A2").
Definition fpage (G : DG) (b : nat) (k : Z) : Z := ltac2:(tb__ "0|0|
S2S5aS0Vb;S1dVG;A1Z0A4S5S37Vk;A2A2").

Definition ranges_disjointZ (p q : Z * Z) : Prop := ltac2:(tb__ "0|2|
SfS3S2S2bS0S0Vp;A3M0S2cS0S0Vp;A3A2S2bS0S0Vq;A3M1A2S3S2G1S2cS0S0Vq;A3A2G0A2A2").

Record depot_mem (G : DG) (m : bview) : Prop := mkDM {

  dm_N : 1 <= dN G < 2 ^ 31 - 1 /\ cellZ m NIDS 4 (dN G);
  dm_F : 1 <= dF G /\ dF G <= 11 * (dN G + fblk (dF G)) /\ dF G <= 2 ^ 32 - 2 ^ 21 /\ cellZ m STORE 8 (dF G);
  dm_mu : cellZ m NODESMU 4 0;
  dm_alloc : present m (STORE + 8) (STORE + 16);

  dm_tab : forall i, 0 <= i < TABSZ -> exists w, cellZ m (DEPOT + 4 * i) 4 w /\ (w = 0 \/ 1 <= w <= dN G);

  dm_map1_len : nblk (dN G) <= Z.of_nat (length (dNB G)) <= nblk (dN G + 1);
  dm_map1 : forall j, 0 <= j < MAP1N -> cellZ m (MAP1 + 8 * j) 8 (nth (Z.to_nat j) (dNB G) 0);
  dm_nb : forall b, In b (dNB G) -> b mod PG = 0 /\ IMG_HI <= b /\ b + NBSZ <= 140737479966720 /\ present m b (b + NBSZ);

  dm_link : forall s, 1 <= s <= dN G -> exists h l, cellZ m (node_addr G s) 8 h /\ cellZ m (node_addr G s + 8) 4 l /\ 0 <= l < s;

  dm_fb_len : fblk (dF G) <= Z.of_nat (length (dFB G)) <= fblk (dF G) + 1 /\ length (dFP G) = length (dFB G);
  dm_fb : forall b, (b < length (dFB G))%nat ->
            cellZ m (STORE + 16 + 16 * Z.of_nat b) 8 (nth b (dFB G) 0) /\ nth b (dFB G) 0 <> 0
            /\ present m (STORE + 24 + 16 * Z.of_nat b) (STORE + 28 + 16 * Z.of_nat b)
            /\ cellZ m (STORE + 28 + 16 * Z.of_nat b) 4 0;
  dm_fb_zero : forall b, Z.of_nat (length (dFB G)) <= b < NFBLK ->
            filled m (STORE + 16 + 16 * b) (STORE + 24 + 16 * b) 0 /\ present m (STORE + 24 + 16 * b) (STORE + 28 + 16 * b)
            /\ filled m (STORE + 28 + 16 * b) (STORE + 32 + 16 * b) 0;
  dm_fbases : forall b, In b (dFB G) -> b mod PG = 0 /\ IMG_HI <= b /\ b + FBSZ <= 140737479966720;

  dm_fp : forall b, (b < length (dFB G))%nat -> 0 <= nth b (dFP G) 0 <= FBPAGES /\ present m (nth b (dFB G) 0) (nth b (dFB G) 0 + PG * nth b (dFP G) 0);

  dm_fp_lo : forall b, (b < length (dFB G))%nat -> 8 * Z.min (dF G - 1048576 * Z.of_nat b) 1048576 <= PG * nth b (dFP G) 0;

  dm_fp_hi : forall b, (b < length (dFB G))%nat -> PG * nth b (dFP G) 0 <= 8 * (dF G - 1048576 * Z.of_nat b) + PG + 88;

  dm_disj : forall i j, (i < j)%nat -> (j < length (dblocks G))%nat -> ranges_disjointZ (nth i (dblocks G) (0,0)) (nth j (dblocks G) (0,0))
}.

Record depot_vm (G : DG) (md : Model) (tp : list word) : Prop := mkDV {

  dv_maps : forall bn, In bn (dblocks G) -> In (wentry bn) (vm_maps (m_vmmaps md));
  dv_lazy : forall b, In b (dFB G) -> In (Z_to_bv 64 b, Z_to_bv 64 FBSZ) (m_vm_lazy md);
  dv_acc : forall b j, In b (dFB G) -> 0 <= j < FBSZ -> covered (vm_noaccess (m_vmmaps md)) (b + j) = false;

  dv_tp : forall b k, (b < length (dFB G))%nat -> 0 <= k < FBPAGES -> (In (Z_to_bv 64 (fpage G b k)) tp <-> k < nth b (dFP G) 0);

  dv_top : forall bn, In bn (dblocks G) -> fst bn + snd bn <= alloc_top (m_vmmaps md);
  dv_top_range : 140735332483072 <= alloc_top (m_vmmaps md) <= 140737479966720
}.

Definition G0 (nodes0 ss0 f0 : Z) : DG := ltac2:(tb__ "0|2|
S23Z1M0Vf0;S2aS0Vnodes0;S2fS0A1M1A3S2aS0Vss0;G1A3S2aS0G0G1A3A5").

Section WithSegs.
Variable segs : list Segment.

Definition depot_inv (G : DG) (rho : valuation) (md : Model) (tp : list word) : Prop := ltac2:(tb__ "0|0|
SdS3fVG;S54Vsegs;S34Vrho;A1A2A2S45VG;Vmd;Vtp;A3A2").

Local Ltac dc := unfold DFP, dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, TABSZ, NIDS, NODESMU, NBSZ, FBSZ, FBPAGES, PG in *.

Lemma fblk_lt : ltac2:(tb__ "0|1|
S0S3Z0R1A2S3R2S8S9Z2M0Z20A2S9G0Z15A2A2A2S4S42R3A1Z1000A2F_;F_;FF;").
Proof. intros F H1 H2. unfold fblk in *. apply Z.div_lt_upper_bound; lia. Qed.

Lemma depot_mem_frame : ltac2:(tb__ "0|2|
S1eS0S2dS31Q8A1A1M0Fx;M1G1S0S3dR4R1A2SeG0R3R2A1R4R2A1A3F_;Fa;S3fR4R3A2S3fR5R3A2F_;F_;Fm';Fm;FG;").
Proof.
  intros G m m' Hm H. destruct H as [HN HF Hmu Hal Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfp Hflo Hfh Hdj].
  assert (UV : forall a k v, (forall j, (j < k)%nat -> DFP G (a + Z.of_nat j)) -> cellZ m a k v -> cellZ m' a k v).
  { intros a k v Hk H j Hj. unfold cellZ, cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. rewrite (Hm _ (Hk j Hj)). exact (H j Hj). }
  assert (PR : forall lo hi, (forall a, lo <= a < hi -> DFP G a) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hk Hp z Hz. rewrite (Hm z (Hk z Hz)). exact (Hp z Hz). }
  assert (FL : forall lo hi b, (forall a, lo <= a < hi -> DFP G a) -> filled m lo hi b -> filled m' lo hi b).
  { intros lo hi b Hk Hp z Hz. rewrite (Hm z (Hk z Hz)). exact (Hp z Hz). }
  assert (FB : fblk (dF G) < 4096) by (apply fblk_lt; lia).
  dc. constructor; dc.
  - split; [exact (proj1 HN)|]. apply UV; [|exact (proj2 HN)]. intros j Hj. left. left. dc; lia.
  - destruct HF as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. apply UV; [|exact F4]. intros j Hj. left. right. dc; lia.
  - apply UV; [|exact Hmu]. intros j Hj. left. left. dc; lia.
  - apply PR; [|exact Hal]. intros a Ha. left. right. dc; lia.
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [|exact Hr]. apply UV; [|exact Hw]. intros j Hj. left. left. dc; lia.
  - exact Hl1.
  - intros j Hj. apply UV; [|exact (Hm1 j Hj)]. intros j' Hj'. left. left. dc; lia.
  - intros b Hb. destruct (Hnb b Hb) as (A1 & A2 & A3 & A4). repeat split; try assumption.
    apply PR; [|exact A4]. intros a Ha. right. left. exists b. split; [exact Hb|]. unfold NBSZ in *. dc; lia.
  - intros s Hs. destruct (Hlk s Hs) as (h & l & Hh & Hl & Hr). exists h, l.
    assert (Hin : In (nth (Z.to_nat (s / 65536)) (dNB G) 0) (dNB G)).
    { apply nth_In. pose proof (proj1 HN). unfold nblk in Hl1.
      destruct (Z.eqb_spec (dN G) 0); [lia|].
      assert (s / 65536 <= dN G / 65536) by (apply Z.div_le_mono; lia).
      assert (0 <= s / 65536) by (apply Z.div_pos; lia). lia. }
    pose proof (Z.mod_pos_bound s 65536 ltac:(lia)) as MB.
    assert (NA : forall j, 0 <= j < 16 -> DFP G (node_addr G s + j)).
    { intros j Hj. right. left. exists (nth (Z.to_nat (s / 65536)) (dNB G) 0). split; [exact Hin|]. unfold node_addr. dc; lia. }
    split; [|split; [|exact Hr]].
    + apply UV; [|exact Hh]. intros j Hj. apply NA. lia.
    + apply UV; [|exact Hl]. intros j Hj. replace (node_addr G s + 8 + Z.of_nat j) with (node_addr G s + (8 + Z.of_nat j)) by lia. apply NA. lia.
  - exact Hfl.
  - intros b Hb. destruct (Hfb b Hb) as (A1 & A2 & A3 & A4).
    assert (BB : Z.of_nat b < fblk (dF G) + 1) by (pose proof (proj1 (Nat2Z.inj_lt _ _) Hb); lia).
    split; [|split; [exact A2 | split]].
    + apply UV; [|exact A1]. intros j Hj. left. right. dc; lia.
    + apply PR; [|exact A3]. intros a Ha. left. right. dc; lia.
    + apply UV; [|exact A4]. intros j Hj. left. right. dc; lia.
  - intros b Hb. destruct (Hfz b Hb) as (A1 & A2 & A3). split; [|split].
    + apply FL; [|exact A1]. intros a Ha. left. right. dc; lia.
    + apply PR; [|exact A2]. intros a Ha. left. right. dc; lia.
    + apply FL; [|exact A3]. intros a Ha. left. right. dc; lia.
  - exact Hfbs.
  - intros b Hb. destruct (Hfp b Hb) as (A1 & A2). split; [exact A1|]. apply PR; [|exact A2].
    intros a Ha. right. right. exists (nth b (dFB G) 0). split; [apply nth_In; exact Hb|]. unfold FBSZ, PG in *. dc; nia.
  - exact Hflo.
  - exact Hfh.
  - exact Hdj.
Qed.

Lemma fblk_nonneg : ltac2:(tb__ "0|1|
S0S3Z0M0R1A2S3G0S42R2A1A2F_;FF;").
Proof. intros F H. unfold fblk. apply Z.div_pos; lia. Qed.
Lemma fblk_ge : ltac2:(tb__ "0|0|
S0S3Z0R1A2S3R2S5Z100000S42R2A1A2A2F_;FF;").
Proof. intros F H. unfold fblk. pose proof (Z.div_mod (F + 1048576 - 1) 1048576 ltac:(lia)). pose proof (Z.mod_pos_bound (F + 1048576 - 1) 1048576 ltac:(lia)). lia. Qed.
Lemma fblk_pred_div : ltac2:(tb__ "0|1|
S0S3Z1M0R1A2SeS0S7S8R2G0A2Z100000A2S8S42R2A1G0A2A3F_;FF;").
Proof. intros F H. unfold fblk. replace (F + 1048576 - 1) with ((F - 1) + 1 * 1048576) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma dm_frames : ltac2:(tb__ "0|4|
S1eS56S3fR2R1A2S0SdS3Z0M0R1A2S4R1S21R4A1A2A2SdS5dSbS7R2Z100000M1A2A1M2S30S0S1dR5A1A2A2S3S2S5Z8M3S6R2G1A2A2G3A2S5S37S5aS0G2S22R5A1G0A4A2A2A2F_;Fi;F_;Fm;FG;").
Proof.
  intros G m HM i Hi. pose proof (dm_fb_len _ _ HM) as [[L _] _]. pose proof (dm_F _ _ HM) as (F0 & _).
  assert (Hq : 0 <= i / 1048576) by (apply Z.div_pos; lia).
  assert (Hlt : i / 1048576 <= fblk (dF G) - 1).
  { rewrite <- (fblk_pred_div (dF G)) by lia. apply Z.div_le_mono; lia. }
  assert (Hb : (Z.to_nat (i / 1048576) < length (dFB G))%nat) by lia.
  split; [exact Hb|]. pose proof (dm_fp_lo _ _ HM _ Hb) as P. rewrite Z2Nat.id in P by lia.
  pose proof (Z.div_mod i 1048576 ltac:(lia)). pose proof (Z.mod_pos_bound i 1048576 ltac:(lia)).
  assert (8 * (i mod 1048576) + 8 <= 8 * Z.min (dF G - 1048576 * (i / 1048576)) 1048576) by (apply Z.min_case_strong; intros; lia). lia.
Qed.

Lemma dm_F_NFBLK : ltac2:(tb__ "0|0|
S1eS56S3fR2R1A2S3S21R3A1S5ZbS2S20R3A1S41A2A2A2F_;Fm;FG;").
Proof.
  intros G m HM. pose proof (dm_F _ _ HM) as (F0 & F1 & F2 & _). pose proof (fblk_lt (dF G) ltac:(lia) F2). unfold NFBLK. lia.
Qed.

Lemma depot_inv_frame : ltac2:(tb__ "0|0|
S1eS35S35S15S25S31Q40A1A1S0S3dR6R1A2SeS2dS31Q8A1A1S54Vsegs;S34R5A1R2A3S54Vsegs;S34R6A1R2A3A3F_;Fa;S52R6R5R3R2A4S52R7R5R4R3A4F_;F_;Ftp;Fmd;Frho';Frho;FG;").
Proof. intros G rho rho' md tp Hm [H1 H2]. split; [eapply depot_mem_frame; eauto | exact H2]. Qed.

Lemma depot_vm_mat : ltac2:(tb__ "0|1|
S1eS15S15S25S31Q40A1M0A1SeS1cS14R2A1S14R3A1A3SeS25S29G0G0A2A1S17R3A1S17R4A1A3S45R6R5R3A3S45R7R5R4A3F_;F_;F_;Ftp;Fmd';Fmd;FG;").
Proof.
  intros G md md' tp Hm Hl [A B C D E F]. constructor.
  - intros bn Hbn. rewrite Hm. exact (A bn Hbn).
  - intros b Hb. rewrite Hl. exact (B b Hb).
  - intros b j Hb Hj. rewrite Hm. exact (C b j Hb Hj).
  - exact D.
  - intros bn Hbn. rewrite Hm. exact (E bn Hbn).
  - rewrite Hm. exact F.
Qed.

Lemma depot_inv_mat : ltac2:(tb__ "0|0|
S1eS35S15S15S25S31Q40A1A1S5eVsegs;R1R3R2A4S52R6R5R4R2A4S52R7R6R4R3A4F_;F_;Ftp;Fmd';Fmd;Frho;FG;").
Proof.
  intros G rho md md' tp ((mat' & ->) & _) [HM HV]. split; [exact HM|]. eapply depot_vm_mat; [| |exact HV]; reflexivity.
Qed.

Lemma depot_inv_bounds : ltac2:(tb__ "0|7|
S1eS35S15S25S31Q40A1A1S52R4R3R2R1A4SdSdS3Z1M0S20R5A1M1A2S4G1S8S9Z2Z1fA2G0A2A2A2SdSdS3Z0M2S21R5A1M3A2S3G3S5ZbS2G1S41A2A2A2A2SdS29S0S0A2M4S13G4R1S44R6A1A3SdS3S38S2bS0S0R2A3M5A2SdS3S2G5S2cS0S0R2A3A2S16S14R5A1A1A2SeS0S6G5S37A2G2A3A2A2F_;Fbn;SdS3Z7fff7f800000S16S14R3A1A1M6A2S3G6Z7fffff800000A2A2A2A2A2F_;Ftp;Fmd;Frho;FG;").
Proof.
  intros G rho md tp [HM HV]. split; [exact (proj1 (dm_N _ _ HM))|]. split; [pose proof (dm_F _ _ HM); pose proof (dm_F_NFBLK _ _ HM); lia|].
  split; [|exact (dv_top_range _ _ _ HV)].
  intros [b n] Hin. pose proof (dv_top _ _ _ HV _ Hin) as T. cbn [fst snd] in T.
  unfold dblocks in Hin. apply in_app_or in Hin as [Hin|Hin]; apply in_map_iff in Hin as (b' & E & Hb'); injection E as <- <-; cbn [fst snd].
  - destruct (dm_nb _ _ HM b' Hb') as (A & B & C & _). repeat split; assumption.
  - destruct (dm_fbases _ _ HM b' Hb') as (A & B & C). repeat split; assumption.
Qed.

Lemma depot_inv_ext : ltac2:(tb__ "0|b|
S1eS35S35S15S15S25S31Q40M0A1M1A1M2G2S52R7R6R4R2A4S0S3dR9R1A2SeS2dS31Q8A1A1S54Vsegs;S34R8A1R2A3S54Vsegs;S34R9A1R2A3A3F_;Fa;S29S0S0A2M3S13G3R1S44RaA1A3S13S29G1G1A2M4S4bR2A1S18S14R8A1A1M5A3S13G4S4bR3A1G5A3F_;F_;Fbn;S0S13S0R1S1dRbA1A3S13G4S26G1G1S32G0R2A2S32G0S3bA2M6A4S17R9A1M7A3S13G4S26G1G1S32G0R3A2G6A4G7A3F_;F_;Fb;S0S0S13S0R2S1dRdA1A3SdS3Z0R2A2M8S4R2S3bA2A2SeS28S5cS1bS14RcA1A1M9S2R4R3A2A2S2eA3SeS28S5cG9S2R5R4A2A2S2eA3F_;F_;F_;Fj;Fb;S0S0S13S0R2S1dReA1A3SdG8S4R2S47A2A2S12S13G1S32G0S2R4S5S37R3A2A2A2MaRaA3S13G1GaRbA3A2F_;F_;Fk;Fb;SeG1S1aS14R9A1A1S1aS14RaA1A1A3S52ReRcRaR8A4F_;F_;F_;F_;F_;F_;F_;Ftp';Ftp;Fmd';Fmd;Frho';Frho;FG;").
Proof.
  intros G rho rho' md md' tp tp' [HM HV] Hview Hmaps Hlazy Hacc Htp Hsp. split.
  - eapply depot_mem_frame; [exact Hview | exact HM].
  - destruct HV as [A B C D E F]. pose proof (alloc_top_same _ _ Hsp) as ET. constructor.
    + intros bn Hbn. apply Hmaps; [exact Hbn | exact (A bn Hbn)].
    + intros b Hb. apply Hlazy; [exact Hb | exact (B b Hb)].
    + intros b j Hb Hj. apply Hacc; [exact Hb | exact Hj | exact (C b j Hb Hj)].
    + intros b k Hb Hk. unfold fpage. rewrite (Htp (nth b (dFB G) 0) k (nth_In _ _ Hb) Hk). exact (D b k Hb Hk).
    + intros bn Hbn. rewrite ET. exact (E bn Hbn).
    + rewrite ET. exact F.
Qed.

Definition G_page (G : DG) (b : nat) : DG := ltac2:(tb__ "0|1|
S23S20VG;A1S21VG;A1S1fVG;A1S1dVG;A1S24S0S22VG;A1M0Vb;S2S5aS0Vb;G0Z0A4Z1A2A4A5").
Definition G_fblk (G : DG) (a : Z) : DG := ltac2:(tb__ "0|1|
S23S20VG;A1S21VG;A1S1fVG;A1S27S0S1dVG;A1S2aS0Va;S2fS0A1M0A3A3S27S0S22VG;A1S2aS0Z0G0A3A3A5").
Definition G_nblk (G : DG) (a : Z) : DG := ltac2:(tb__ "0|0|
S23S20VG;A1S21VG;A1S27S0S1fVG;A1S2aS0Va;S2fS0A1A3A3S1dVG;A1S22VG;A1A5").
Definition G_ins (G : DG) (dF' : Z) : DG := ltac2:(tb__ "0|0|
S23S2S20VG;A1Z1A2VdF';S1fVG;A1S1dVG;A1S22VG;A1A5").

Inductive dtrans : DG -> list word -> Model -> DG -> list word -> Model -> Prop :=

  | DT_page : forall G tp md b p,
      (b < length (dFB G))%nat -> nth b (dFP G) 0 < FBPAGES ->
      p = Z_to_bv 64 (fpage G b (nth b (dFP G) 0)) -> ~ In p tp ->
      headroom md tp >= PG ->
      dtrans G tp md (G_page G b) (p :: tp) md

  | DT_fblk : forall G tp md h' (a n : word),
      vm_maps h' = (a, n) :: vm_maps (m_vmmaps md) -> vm_noaccess h' = vm_noaccess (m_vmmaps md) ->
      vm_reserved h' = vm_reserved (m_vmmaps md) -> vm_limit h' = vm_limit (m_vmmaps md) ->
      vm_init_sp h' = vm_init_sp (m_vmmaps md) ->
      bv_unsigned n = FBSZ -> bv_unsigned a mod PG = 0 -> IMG_HI <= bv_unsigned a -> bv_unsigned a + FBSZ <= alloc_top (m_vmmaps md) ->
      region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a n = true ->
      paid (vm_add_lazy a n (with_vmmaps h' md)) tp <= paid md tp ->
      dtrans G tp md (G_fblk G (bv_unsigned a)) tp (vm_add_lazy a n (with_vmmaps h' md))

  | DT_nblk : forall G tp md h' (a n : word),
      vm_maps h' = (a, n) :: vm_maps (m_vmmaps md) -> vm_noaccess h' = vm_noaccess (m_vmmaps md) ->
      vm_reserved h' = vm_reserved (m_vmmaps md) -> vm_limit h' = vm_limit (m_vmmaps md) ->
      vm_init_sp h' = vm_init_sp (m_vmmaps md) ->
      bv_unsigned n = NBSZ -> bv_unsigned a mod PG = 0 -> IMG_HI <= bv_unsigned a -> bv_unsigned a + NBSZ <= alloc_top (m_vmmaps md) ->
      region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a n = true ->
      headroom md tp >= NBSZ -> paid (with_vmmaps h' md) tp <= paid md tp + NBSZ ->
      dtrans G tp md (G_nblk G (bv_unsigned a)) tp (with_vmmaps h' md)

  | DT_ins : forall G tp md dF',
      dF G <= dF' <= dF G + 22 -> dF' <= 11 * (dN G + 1 + NFBLK) ->
      dtrans G tp md (G_ins G dF') tp md.

Record KD_laws (K : DG -> jpredA) (n : positive) : Prop := mkKDL {

  kd_stable : forall G, stableA segs n (K G);

  kd_view : forall G rho rho' tp tr md,
      (forall i, rw rho' i = rw rho i) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ DFPw G z -> view segs (rm rho') z = view segs (rm rho) z) ->
      K G rho tp tr md -> K G rho' tp tr md;

  kd_trans : forall G tp md G' tp' md' rho tr,
      dtrans G tp md G' tp' md' -> K G rho tp tr md -> K G' rho tp' tr md';

  kd_room : forall G rho tp tr md, K G rho tp tr md -> depot_inv G rho md tp -> headroom md tp >= droom G /\ dN G <= DNMAX;

  kd_reserved : forall G rho tp tr md, K G rho tp tr md -> vm_reserved (m_vmmaps md) = segments_reserved segs;

  kd_noacc : forall G rho tp tr md a n x, K G rho tp tr md -> In (a, n) (vm_noaccess (m_vmmaps md)) ->
      bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
      exists b m, In (b, m) (vm_maps (m_vmmaps md)) /\ bv_unsigned b <= x < bv_unsigned b + bv_unsigned m;

  kd_place : forall G rho tp tr md L, K G rho tp tr md -> depot_inv G rho md tp -> (L = NBSZ \/ L = FBSZ) ->
      exists a : word, mmap_place_ok_none (Z_to_bv 64 0) md (Z_to_bv 64 L) a
}.

Definition JD (K : DG -> jpredA) (G : DG) : jpredA := ltac2:(tb__ "0|0|
S35S25S31Q40A1A1S25S19A1S15SdVK;VG;R4R3R2R1A5S52VG;R4R1R3A4A2Lmd;Ltr;Ltp;Lrho;").

Definition dpost (G G' : DG) : Prop := ltac2:(tb__ "0|5|
SdSfSeS0S20VG';A1M0S20VG;A1M1A3SeS0G0S2G1Z1A2A3A2SdSdS3S21VG;A1M2S21VG';A1M3A2S3G3S2G2Z16A2A2A2SdS10S25S0A1M4G4SeG4S1fVG';A1S27S0S1fVG;A1R1A3A3Ll;A2SdS10G4G4SeG4S1dVG';A1S27S0S1dVG;A1R1A3A3Ll;A2SdS3S49VG';A1S2S49VG;A1S51VG;A1A2A2S0S40VG;R1A2S40VG';R2A2F_;Fa;A2A2A2A2A2").

Definition JLD (K : DG -> jpredA) (G : DG) : jpostA := ltac2:(tb__ "0|5|
S35S25S31Q40M0A1M1A1M2S35G2S25S19A1S15S10S1eS1eSdVK;R1R5R4R3R2A5SdS52R1R5R2R4A4SdS53VG;R1A2SdG1S11S3dR2S33G0R1A2A2A1SeS2dS31Q8A1M3A1M4S34R7R2A2S34R9R2A2A3F_;Fa;SdS0S11S40R2R1A2A1SeG4S54Vsegs;S34R7A1R2A3S54Vsegs;S34R9A1R2A3A3F_;Fz;SdS1SeS25G3A1S36R6R1A2S36R8R1A2A3Fl;S10G2G2SeG2R5S27G1R1R7A3A3Ll;A2A2A2A2A2A2A2LG';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Lemma depot_inv_G0_intro : ltac2:(tb__ "0|12|
S0S0S0S35S15S25S31Q40M0A1M1A1S54Vsegs;S34R3A1A2S56SdS3Z1M2R5A2S3R5Z16A2A2S3aR2S4dU4M3G2A4S3aR3S39U8M4R7A4S3aR4S4eG3Z0M5A4S55R5S2S39Z8M6A2S2S39Z10M7A2M8A3S0SdS3G5R1A2M9S4R1S4fA2A2S10S0S0SdS3aR9S2S46S5Z4R3A2A2G3R1A4SfSeS0R1G5A3SeS0R1G2A3A2A2Lw;A2F_;Fi;S3aR7S3eG4RdA4S0SdS3G2R1A2MaS4R1S48A2A2S3aRaS2S3eS5G6R2A2A2G4G5A4F_;Fj;SeS0S6RfS37A2G5A3S3S38R10A2S3S2R11S3cA2S16S14RdA1A1A2S55RcR12S2R12S3cA2A3S10S0S0S3aReS2R14G7A2G4R1A4Lh;A2S3aReS2R14Z18MbA2G3G5A4S3aRfG8G4R14A4S11SeS0R15G5A3A1S55R11S2S39GbA2S2S39Z1cA2McA3S3aR12GcG3G5A4S0SdGaS4R1S41A2A2S58R15S2G8S5G7R2A2MdA2S2S2S39Z20A2GdA2G5A4F_;Fb;SeS0S6R19S37A2G5A3S3S38R1aA2S3S2R1bS3bA2S16S14R18A1A1A2S55R17R1cS2R1cS37A2A3SfS3S2R1eS3cA2R1dA2S3S2R1dS3bA2R1eA2A2SdS3Z7fff7f800000S16S14R1bA1A1MeA2S3GeZ7fffff800000A2A2S13S29G1G1A2MfS26G1G1S32G0R20A2M10S32G0S3cA2A4S18S14R1cA1A1A3S13GfS26G1G1G10S32G0S3bA2M11A4S18S14R1dA1A1A3S13GfS26G1G1S32G0R21A2G11A4S17R1eA1A3S0SdG9S4R1S3bA2A2SeS28S5cS1bS14R21A1A1S2R24R2A2A2S2eA3F_;Fj;S0SdG9S4R1S47A2A2S12S13G1S32G0S2R25S5S37R2A2A2A2R21A3SeS0R2G5A3A2F_;Fk;S52S4cR25R24R23A3R22R21R20A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tm;Ftp;Fmd;Frho;Ff0;Fss0;Fnodes0;").
Proof.
  intros nodes0 ss0 f0 rho md tp m Hf0 H1 H2 H3 H4 H5 H6 H7 N1 N2 N3 N4 [h Hh] Hl S1 S2 S3 S4 Hz F1 F2 F3 Fp Hdis TR V1 V2 V3 V4 V5.
  assert (N3' : nodes0 + NBSZ <= 140737479966720) by lia. assert (F3' : ss0 + FBSZ <= 140737479966720) by lia.
  assert (FB1 : fblk f0 = 1).
  { unfold fblk. replace (f0 + 1048576 - 1) with (1 * 1048576 + (f0 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (f0 - 1)) by lia. reflexivity. }
  split.
  - constructor; cbn [dN dF dNB dFB dFP G0 length nth Z.to_nat Z.of_nat].
    + split; [lia | exact H1].
    + split; [lia|]. split; [rewrite FB1; lia|]. split; [lia | exact H2].
    + exact H3.
    + exact H4.
    + intros i Hi. destruct (H5 i Hi) as (w & Hw & Hr). exists w. split; [exact Hw | lia].
    + vm_compute. split; discriminate.
    + intros j Hj. destruct (Z.to_nat j) as [|[|n]] eqn:E.
      * assert (j = 0) by lia. subst j. rewrite Z.mul_0_r, Z.add_0_r. exact H6.
      * apply H7. lia.
      * apply H7. lia.
    + intros b [<-|[]]. repeat split; assumption.
    + intros s Hs. assert (s = 1) by lia. subst s. exists h, 0. unfold node_addr.
      rewrite (Z.div_small 1 65536) by lia. rewrite (Z.mod_small 1 65536) by lia.
      replace (nth (Z.to_nat 0) (dNB (G0 nodes0 ss0 f0)) 0) with nodes0 by reflexivity.
      replace (nodes0 + 16 * 1) with (nodes0 + 16) by lia. replace (nodes0 + 16 + 8) with (nodes0 + 24) by lia.
      split; [exact Hh | split; [exact Hl | lia]].
    + split; [rewrite FB1; cbn; lia | reflexivity].
    + intros b Hb. assert (b = 0%nat) by (cbn in Hb; lia). subst b. cbn [nth Z.of_nat]. rewrite Z.mul_0_r, !Z.add_0_r.
      split; [exact S1|]. split; [exact S2|]. split; [exact S3 | exact S4].
    + intros b Hb. cbn in Hb. pose proof (Hz b ltac:(lia)) as F. split; [|split].
      * intros z Hzz. apply F. lia.
      * intros z Hzz. exists (Z_to_bv 8 0). apply F. lia.
      * intros z Hzz. apply F. lia.
    + intros b [<-|[]]. repeat split; assumption.
    + intros b Hb. assert (b = 0%nat) by (cbn in Hb; lia). subst b. cbn [nth]. split; [unfold FBPAGES; lia|]. rewrite Z.mul_1_r. exact Fp.
    + intros b Hb. assert (b = 0%nat) by (cbn in Hb; lia). subst b. cbn [nth Z.of_nat]. unfold PG. lia.
    + intros b Hb. assert (b = 0%nat) by (cbn in Hb; lia). subst b. cbn [nth Z.of_nat]. unfold PG. lia.
    + intros i j Hij Hj. cbn in Hj. assert (i = 0%nat /\ j = 1%nat) as [-> ->] by lia. cbn. unfold ranges_disjointZ. cbn [fst snd]. lia.
  - constructor; cbn [dN dF dNB dFB dFP G0 length nth].
    + intros bn Hbn. unfold dblocks in Hbn. cbn in Hbn. destruct Hbn as [<-|[<-|[]]]; unfold wentry; cbn [fst snd]; assumption.
    + intros b [<-|[]]. exact V3.
    + intros b j [<-|[]] Hj. apply V4. exact Hj.
    + intros b k Hb Hk. assert (b = 0%nat) by (cbn in Hb; lia). subst b. unfold fpage. cbn [nth]. rewrite (V5 k Hk). lia.
    + intros bn Hbn. unfold dblocks in Hbn. cbn in Hbn. destruct Hbn as [<-|[<-|[]]]; cbn [fst snd]; assumption.
    + exact TR.
Qed.

Lemma dpost_refl : ltac2:(tb__ "0|0|
S1eS53R1R1A2FG;").
Proof.
  intros G. unfold dpost. split; [left; reflexivity|]. split; [lia|]. split; [exists []; symmetry; apply app_nil_r|].
  split; [exists []; symmetry; apply app_nil_r|]. split; [|intros a H; exact H].
  unfold droom, PG, NBSZ. destruct ((dN G + 1) mod 65536 =? 0); lia.
Qed.

End WithSegs.

