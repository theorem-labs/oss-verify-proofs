(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "length"; "app"; "bool"; "nat"; "list"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "add"; "le"; "to_nat"; "ltb"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_cache"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_mapped_user"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "cs_empty"; "cs_n_allocated"; "cs_n_freed"; "list_upd"; "mkAA"; "mkCS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "cls_pure"; "@Corelib.Lists.ListDef"; "skipn"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drain_cs"; "drain_keep"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kFreeArrayMapSize"; "@Corelib.Init.Nat"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model PrimCredit PrimCreditLaws RefillModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition drain_keep (c : Z) (cs : class_state) : nat := ltac2:(tb__ "0|0|
S33S3S0SfVcs;A1A2SbS2aVc;A1A1A2").
Definition drain_grows (c : Z) (cs : class_state) : bool := ltac2:(tb__ "0|0|
ScS12Vcs;A1SdZ4S9S8S3S0S11Vcs;A1A2A1S2aVc;A1A2A2A2").
Definition drain_cs (c : Z) (cs : class_state) : class_state := ltac2:(tb__ "0|2|
S30Vc;Vcs;A2S6S29S14Vcs;A1S13Vcs;A1S4S0S11Vcs;A1S2cS0R1SfVcs;A1M0A3A3S5S0L_;S31Vc;Vcs;A2S9S12Vcs;A1M1S32A2G1X5x2S2dS0R1G0A3S25Vcs;A1S9S26Vcs;A1S2aVc;A1A2A7Tkeep;").
Definition drainA (A : AA) (c : Z) : AA := ltac2:(tb__ "0|2|
S28S1dVA;A1S27S10S19VA;A1M0SbVc;A1M1S2fVc;S2eS10G1G0S24A4A2A4S18VA;A1S23VA;A1S20VA;A1S1fVA;A1S22VA;A1S21VA;A1S1aVA;A1S1cVA;A1S1bVA;A1S1eVA;A1S17VA;A1S16VA;A1S15VA;A1Af").

Lemma drain_pure : ltac2:(tb__ "0|8|
S0S10S7S0A1M0S1SaZ1R3A2SaR3Z1eA2A2S2bR4R3R2A3SaS2aR5A1S8S3S0SfR4A1A2A1A2S2fR6R5A2S10S1S2bR7R1R5A3S1S2S6S3S0SfR1A1M1A2M2S30R7R6A2M3A3S1S2S0S8G2A1SeS8S3S0SfR6A1M4A2A1S2aR7A1M5A2A3S1S2S0S8S3S0S11R1A1A2A1S9S8S3S0S11R6A1A2A1G5A2A3S1S2G0S4S0G1S2cS0G3G4A3A3G4A3S1S2S0S14R1A1S14R6A1A3S1S2S0S13R1A1S13R6A1A3S1SaS12R6A1M6S12R1A1M7A2SaG7S9G6S32A2A2A2A2A2A2A2A2A2A2Tcs';F_;F_;F_;Fout;Fcs;Fc;").
Proof.
  intros c cs out Hc (P1 & P2 & P3 & P4 & P4' & P5 & P6 & P7 & P8 & P9 & P10 & P11) Hn cs'.
  destruct (kchunks_facts c Hc) as (K1 & K2 & K3). destruct (cap_facts c Hc) as (SZ & _ & _ & _ & _ & _ & FC & _).
  unfold cs', drain_cs. set (keep := drain_keep c cs). set (ca := cs_cache cs) in *. set (fa := cs_free_array cs) in *.
  assert (Hk : (keep <= length ca)%nat) by (unfold keep, drain_keep; fold ca; lia).
  assert (E : firstn keep ca ++ skipn keep ca = ca) by apply firstn_skipn.
  assert (L1 : length (firstn keep ca) = keep) by (rewrite firstn_length_le; [reflexivity | exact Hk]).
  assert (L2 : Z.of_nat (length (skipn keep ca)) = kchunks c) by (rewrite length_skipn; unfold keep, drain_keep; fold ca; lia).
  assert (PM : Permutation ((fa ++ skipn keep ca) ++ firstn keep ca ++ out) (fa ++ ca ++ out)).
  { set (sk := skipn keep ca) in *. set (fi := firstn keep ca) in *. rewrite <- app_assoc. apply Permutation_app_head.
    rewrite <- E. rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (MF : cs_mapped_free_array cs <= (if drain_grows c cs then cs_mapped_free_array cs + kFreeArrayMapSize else cs_mapped_free_array cs)
                                       <= cs_mapped_free_array cs + kFreeArrayMapSize).
  { destruct (drain_grows c cs); unfold kFreeArrayMapSize; lia. }
  cbn [cs_free_array cs_cache cs_mapped_user cs_allocated_user cs_mapped_free_array].
  split; [|split; [exact L1|]; split; [rewrite L1; unfold keep, drain_keep; fold ca; lia|]; split; [rewrite length_app; fold fa; lia|];
           split; [exact E|]; split; [reflexivity|]; split; [reflexivity | exact MF]].
  unfold cls_pure. cbn [cs_free_array cs_cache cs_mapped_user cs_allocated_user cs_mapped_free_array].
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split.
  { destruct (drain_grows c cs); [|exact P4]. unfold kFreeArrayMapSize in *. rewrite <- Z.add_mod_idemp_l by lia. rewrite P4. reflexivity. }
  split; [clear -MF P4'; lia|].
  split.
  { rewrite length_app. fold fa. unfold drain_grows. fold fa. destruct (Z.ltb_spec (cs_mapped_free_array cs) (4 * (Z.of_nat (length fa) + kchunks c))) as [LT|GE];
      [unfold kFreeArrayMapSize; fold fa in P5; clear -P5 K1 L2; lia | clear -GE L2; lia]. }
  split; [intros x Hx; apply P6; exact (Permutation_in x PM Hx)|].
  split; [exact (Permutation_NoDup (Permutation_sym PM) P7)|].
  split; [exact P8|].
  split; [rewrite P9, length_app, L1; apply f_equal; apply Nat2Z.inj; rewrite !Nat2Z.inj_add, L2; clear -Hn Hk L1 L2; pose proof (length_skipn keep ca) as LS; lia|].
  split; [exact P10|].

  unfold drain_grows. fold fa. destruct (Z.ltb_spec (cs_mapped_free_array cs) (4 * (Z.of_nat (length fa) + kchunks c))) as [LT|GE]; [|exact P11].
  assert (SL : Z.of_nat (length fa) + kchunks c <= cs_allocated_user cs / Size c).
  { rewrite P9. fold fa ca. rewrite !Nat2Z.inj_add. clear -Hn. lia. }
  assert (DM : cs_allocated_user cs / Size c <= MUCAP c / Size c) by (apply Z.div_le_mono; [clear -SZ; lia | clear -P2 P10; lia]).
  clear -LT SL DM FC. lia.
Qed.
