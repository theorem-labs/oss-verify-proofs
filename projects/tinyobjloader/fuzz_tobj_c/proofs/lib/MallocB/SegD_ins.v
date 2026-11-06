(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "of_nat"; "modulo"; "div"; "to_nat"; "sub"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Corelib.Init.Datatypes"; "nat"; "length"; "prod"; "pair"; "list"; "app"; "cons"; "option"; "nil"; "Some"; "fst"; "snd"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "DG"; "dNB"; "dFB"; "dN"; "dFP"; "dF"; "list_upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "STORE"; "node_addr"; "depot_mem"; "NBSZ"; "cellZ"; "ranges_disjointZ"; "FBSZ"; "G_page"; "fpage"; "G_ins"; "depot_vm"; "fblk"; "G_fblk"; "G_nblk"; "NIDS"; "DEPOT"; "DNMAX"; "FBPAGES"; "MAP1"; "dep_cost"; "sumZ"; "NFBLK"; "TABSZ"; "nblk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "IMG_HI"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins"; "ins_written"; "pw_disj"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_wf.
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
S1eS3eS3eS0SfS0S0S0S28R8R7A2SbS2Z1M0R6A2S2R6Z1eA2A2ScS2R7ZaA2S2S21RaA1S1S4aG0A2A2A2S2S21RbA1S36A2ScSaS0R5S23RcA1M1A3SbSaS0R5S1G1S1R9G0A2A2A3S2Z100000M2S1S6G1G2A2R9A2A2A2A2SaSfR9S8S7R6G2A2A1A3S1bRaS10S0S20ReA1A2A2S4S1S6R8G2A2RcA2G2A2S2S3Z8M3S1S1S6R9G2A2RdA2G0A2A2S3S40S1cS0RcS22R10A1Z0M4A4A2A2S1bS8S7S1S21R11A1G0A2Z10000A2A1S10S0S1fR11A1A2A2SbS2G4RdA2S4RdS3cA2A2S0SdS46R14RfR10R11RdR1A6A1SaS16S42Q8A1A1R13R2A1R14R2A1A3F_;Fz;S2aR12S1S35S3Z4RfA2A2U4M5S1S21R14A1G0A2A4S2aR13S34G5S1S21R15A1G0A2A4S2aR14S27R16S1S21R16A1G0A2A2U8M6R10A4SeS0S0SbS2aR16S1S27R18S1S21R18A1M7G0A2A2M8G3A2G5R1A4SbS2G4R1A2S2R1G7A2A2A2Ll;A2S3fR16S1G8ZcA2S1G8Z10M9A2A3S2aR17S26G6S1S1R12R16A2G0A2A4S3fR18S1S1S26Z18A2S3G9S5R16A1A2MaA2S1S1S26Z1cA2GaA2A3S3fR19S1S1cS0R17S20R1bA1G4A4S3G3S6R14G2A2A2A2MbS1GbS3G3S1R18G0A2A2A2A3S28S2fR1cS1S1R15R19A2G0A2A2R1aA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FS;Fh;Fi;Fb;Fsz;Fm';Fm;FG;").
Proof.
  intros G m m' sz b i h S HM Hsz Htol HDN HS Hb Hbl Hns Hpaid HjN Hi Hsame Ctab Cnid Cnh [l [Cnl Hl]] Pst Ctf Pstc Pfr.
  destruct HM as [HN HF Hmu Hal Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfp Hfr Hfh Hdj].
  pose proof (proj1 HF) as F0.
  assert (HSge : dF G <= S <= dF G + 31) by lia.
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
  pose proof XCAP_val as XV. assert (XK : XCAP = 20 * (KMAX + 2)) by reflexivity.
  assert (Fnew1 : S + sz + 1 <= 31 * (dN G + 1 + fblk (S + sz + 1))) by (destruct HF as (_ & (HF1 & _) & _); destruct HS as [ES|[ES SR]]; [|specialize (FB2 ES)]; lia).
  assert (Fnew2 : S + sz + 1 <= 11 * (dN G + 1) + 31 * fblk (S + sz + 1) + XCAP).
  { destruct HF as (_ & (HF1 & HF2) & _). destruct Htol as [Hn|Hk]; (destruct HS as [ES|[ES SR]]; [|specialize (FB2 ES)]); lia. }
  assert (Fnew : S + sz + 1 <= 31 * (dN G + 1 + fblk (S + sz + 1)) /\ S + sz + 1 <= 11 * (dN G + 1) + 31 * fblk (S + sz + 1) + XCAP) by exact (conj Fnew1 Fnew2).

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
S1eS3eS3eSfS28R4R3A2S1bR2S10S0S20R5A1A2A2S4S1cS0R3S22R6A1Z0M0A4S37A2S2S3S40S1S1cS0R4S22R7A1G0A4Z1A2A2S1S1S3Z8S9S23R7A1S3Z100000S5R4A1A2A2A2S40A2Zf8A2A2S0SbS2S2eR9R6S1cS0R6S22R9A1G0A4A3M1R1A2S4R1S1G1S40A2A2A2SaS16S42Q8M2A1M3A1M4R8R2A1S18G3S43G2G0A2A2A3F_;Fz;S0SdSbS2S2eRaR7S1cS0R7S22RaA1G0A4A3M5R1A2S4R1S1G5S40A2A2A2A1SaG4R9R2A1RaR2A1A3F_;Fz;S28S2dRaR7A2R8A2F_;F_;F_;F_;F_;F_;Fb;Fm';Fm;FG;").
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
S1eS3eS3eS0S0S0S10S0S20R6A1A2SfS28R7R6A2SbS2Z1M0R3A2S2R3Z1eA2A2ScSaS0R5S23R9A1M1A3SbSaS0R5S1G1S1R4G0A2A2A3S2Z100000M2S1S6G1G2A2R4A2A2A2A2SaS0S5R4A1S7R6G2A2A3SaS0S6R8S40A2Z0M3A3S2S41R9A2S2S1RaS2cA2Z7fffff800000A2S11S0S0A2M4S44G4R1S25RfA1A3S2bR2S12S0S0RdS2cA4A2F_;Fbn;S2aRdS1S1S26Z10M5A2M6S3G5S5R9A1A2A2U8RcA4S3fReS1S1S26Z18A2S3G5S5RaA1A2M7A2S1S1S26Z1cA2M8G7A2A3S2aRfS1G8S3G5S5RbA1A2A2U4G3A4S3fR10S1S26Z8A2M9G6A3S0S4R1S41A2SdSbS2G9R2A2S4R2G6A2A2A1SdSbS2S1G6S3G5S5R10A1A2MaA2R3A2S4R3S1S1S26Z20A2GaA2A2A2A1SaS16S42Q8A1A1MbR15R4A1R16R4A1A3F_;F_;F_;Fz;G4S0S44G4R2S25R16A1A3SbS2S19S0S0R3A3McR2A2S4R2S1GcS1aS0S0R3A3A2A2A2SaGbR16R3A1R17R3A1A3F_;F_;Fz;Fbn;S28S32R15R12A2R13A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;Fsz;FS;Fa;Fm';Fm;FG;").
Proof.
  intros G m m' a S sz b HM Hsz HS HbS Hal Hlo Hhi Hdisj Cdat Pst Cmtx Palc OFFs OFFb.
  pose proof (proj2 (dm_fb_len _ _ HM)) as HL.
  destruct HM as [HN HF Hmu Halc Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfpp Hflo Hfh Hdj].
  pose proof (proj1 HF) as F0. assert (FBL : fblk (dF G) < 4096) by (apply fblk_lt; lia).
  pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MBF. pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DMF.
  pose proof (Z.div_mod S 1048576 ltac:(lia)) as DMS. pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MBS.
  assert (HbN : Z.of_nat b < 4096) by (unfold b; lia).

  assert (HFB : fblk (dF G) = Z.of_nat b /\ -31 <= dF G - 1048576 * Z.of_nat b <= 0).
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
