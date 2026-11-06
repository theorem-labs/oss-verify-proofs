(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "mul"; "of_nat"; "div"; "sub"; "ltb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Init.Datatypes"; "prod"; "list"; "app"; "bool"; "pair"; "true"; "length"; "cons"; "false"; "snd"; "fst"; "nat"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "band_covered"; "SHADOW_BAND_HI"; "ledger_split"; "SHADOW_BAND_LO"; "gap_weight"; "IMG_BAND_HI"; "IMG_BAND_LO"; "live_at"; "SHADOW_RW_HI_BEG"; "SHADOW_RW_LO_END"; "gw_sizes"; "DYN_LO"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_size"; "region_free"; "vm_maps"; "vm_reserved"; "alloc_top"; "VmMaps"; "page_round_up_Z"; "iv_overlap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "alloc_ceiling_hi"; "mmap_nZ"; "mmap_n"; "alloc_ceiling_lo"; "init_sp_ok"; "mmap_place_ok"; "mmap_place_ok_none"; "@Stdlib.Lists.List"; "In"; "filter"; "incl"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement.Gap"; "gap_at"; "scan_inv"; "@Corelib.Lists.ListDef"; "Forall"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma fg_u64_lit : ltac2:(tb__ "0|1|
S0SeS1Z0R1A2S3R1S5Z2Z40A2A2A2SfS0SbQ40M0SdG0R2A2A2R2A3F_;Fz;").
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. exact Hz.
Qed.

Lemma fg_u64_range : ltac2:(tb__ "0|2|
ScQ40M0A1SeS1Z0SbG0R1A2M1A2S3G1S5Z2Z40A2A2A2Fx;").
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.

Lemma page_multiple_eq : ltac2:(tb__ "0|1|
S0SfS0S4R1S2bA2Z0A3SfS0R2S6S8R2Z1000M0A2G0A2A3F_;Fz;").
Proof.
  intros z Hz. unfold page_size in Hz.
  pose proof (Z.div_mod z 4096 ltac:(lia)). lia.
Qed.

Lemma pg_round_up_ge : ltac2:(tb__ "0|0|
S0S1R1S31R1A1A2Fz;").
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

Lemma pg_round_up_le : ltac2:(tb__ "0|0|
S0S1S31R1A1S2R1ZfffA2A2Fz;").
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.mul_div_le (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma pg_round_up_aligned : ltac2:(tb__ "0|0|
S0SfS0S4S31R1A1S2bA2Z0A3Fz;").
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma fg_region_free_false : ltac2:(tb__ "0|2|
S13S12ScQ40A1M0G0A2M1A1G0G0SfS15S2cR3R2R1A3S1aA3S11G0G0S11G0G0SeS3aG1S16G0G0R2R1A4R6A3SfS15S32R5R4R2R1A4S17A3A2Ls;A2Lb;A2F_;Fn;Flo;Fmaps;").
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov).
    exists b', s'. split; [now right|exact Hov].
Qed.

Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_app : ltac2:(tb__ "0|3|
S0S13S12ScQ40A1M0G0A2M1A1M2G2SfS0S23R3S14G1R2R1A3A2S2S23R3R2A2S23R3R1A2A2A3Fl2;Fl1;FnZ;").
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.

Lemma gap_weight_nonneg : ltac2:(tb__ "0|2|
S0S13S12ScQ40A1M0G0A2A1S1Z0M1R2A2S1G1S23R3R2A2A2F_;Fl;FnZ;").
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

Definition live_at (c : Z) (p : word * word) : bool := ltac2:(tb__ "0|2|
SaVc;S2SbQ40M0S1cScG0A1M1G1Vp;A3A2SbG0S1bG1G1Vp;A3A2A2A2").

Lemma gap_weight_filter_le : ltac2:(tb__ "0|2|
S0S12ScQ40A1M0G0A2M1S15F_;S13G1A1S1Z0R3A2S1S23R4S3bG1R3R2A3A2S23R4R2A2A2F_;Fl;Ff;FnZ;").
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

Lemma live_weight_step : ltac2:(tb__ "0|5|
S0S13S12ScQ40M0A1M1G1A2M2A1S0S0G1G1S1Z0R6A2S1R5R4A2S3aG2S16G1G1R4R3A4R7A3SfS15S26R7S16G1G1R5R4A4A2S17A3SfS15S26R7S16G1G1R6R5A4A2S1aA3SeS1S2S23RbS3bG2S26R8A1RaA3M3A2S2S2SbG0R6A2RbA2ZfffA2A2S23RbS3bG2S26R9A1RaA3M4A2A2S3dS18G2G3A2S18G2G4A2A2A2F_;F_;F_;F_;F_;Fs;Fb;Fc';Fc;Fl;FnZ;").
Proof.
  intros nZ l. induction l as [|[b0 s0] l IH]; intros c c' b s HnZ Hcc Hin Hl Hd; [destruct Hin|].
  assert (Hsub : forall x, live_at c' x = true -> live_at c x = true).
  { intros [b1 s1] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hmono : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
                  /\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
  { clear IH Hin Hl Hd. induction l as [|[b1 s1] l IHl]; cbn; [split; [lia|lia]|].
    pose proof (bv_unsigned_in_range 64 s1).
    destruct (live_at c' (b1, s1)) eqn:E.
    - rewrite (Hsub _ E). cbn. destruct IHl. split; lia.
    - destruct (live_at c (b1, s1)); cbn; destruct IHl; split; lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hl, Hd. cbn. destruct Hmono. split; lia.
  - specialize (IH c c' b s HnZ Hcc Hin Hl Hd). destruct IH as [IH1 IH2].
    cbn. pose proof (bv_unsigned_in_range 64 s0).
    destruct (live_at c' (b0, s0)) eqn:E.
    + rewrite (Hsub _ E). cbn. split; lia.
    + destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.

Section Gap.
  Variable L : list (word * word).
  Variables nZ F C : Z.
  Hypothesis HnZ : 0 <= nZ.
  Hypothesis HFal : F mod page_size = 0.
  Hypothesis HF0 : 0 <= F.
  Hypothesis HC : C <= 2 ^ 64 - 2 ^ 32.

  Definition scan_inv (c : Z) : Prop := ltac2:(tb__ "0|1|
SeSfS0S4Vc;S2bA2Z0A3SeS1VF;Vc;A2S1S2S2Vc;VnZ;A2S23VnZ;S3bS12ScQ40A1M0G0A2S26Vc;A1VL;A3A2A2VC;A2A2A2").

  Definition gap_at (c : Z) : Prop := ltac2:(tb__ "0|1|
SeSfS0S4Vc;S2bA2Z0A3SeS1VF;Vc;A2SeS1S2Vc;VnZ;A2VC;A2SfS15S2cVL;SdQ40M0Vc;A2SdG0VnZ;A2A3S17A3A2A2A2").

  Lemma scan_ok_or_step : ltac2:(tb__ "0|3|
S0S40R1A1M0S10S3fR2A1S11S0S0SeG0S3dS18S12ScQ40A1M1G1A2M2S3bG2S26R1A1VL;A3A2S18G2S3bG2S26R3A1VL;A3A2A2A2Lc';A2A2F_;Fc;").
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (pg_round_up_ge (B + S)) as Hge.
      pose proof (pg_round_up_le (B + S)) as Hle.
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply pg_round_up_aligned|].
      split; lia.
  Qed.

  Lemma scan : ltac2:(tb__ "0|2|
S1dS0S3eS18S12ScQ40A1M0G0A2M1S3bG1S26R1A1VL;A3A2R2A2S40R2A1S11S0S0S3fR1A1Lg;A2F_;F_;Fc;Fk;").
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
      exists c. exact Hok.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
      + exists c. exact Hok.
      + apply (IH c'); [lia|exact Hinv'].
  Qed.

  Theorem free_gap_of_slack : ltac2:(tb__ "0|1|
S1S2S2VF;VnZ;A2S23VnZ;VL;A2A2VC;A2S11S0S0SeSfS0S4R1S2bA2Z0A3SeS1VF;R1A2SeS1S2R1VnZ;A2VC;A2SfS15S2cVL;SdQ40M0R1A2SdG0VnZ;A2A3S17A3A2A2A2Lg;A2F_;").
  Proof.
    intros Hslack.
    assert (Hinv : scan_inv F).
    { split; [exact HFal|]. split; [lia|].
      pose proof (gap_weight_filter_le nZ (live_at F) L HnZ). lia. }
    exact (scan _ F (le_n _) Hinv).
  Qed.
End Gap.

Lemma gap_weight_bound : ltac2:(tb__ "0|3|
S0S0S13S12ScQ40M0A1M1G1A2M2A1S1Z0R3A2S41G2G2S1SbG0S1bG1G1R1A3A2R4A2Lp;R2A3S1S23R5R3A2S6S7S18G2R3A2A1S2S2R4R5A2ZfffA2A2A2F_;F_;Fl;FN;FnZ;").
Proof.
  intros nZ N l HnZ H. induction H as [|[b s] l Hs _ IH]; cbn -[Z.of_nat]; [lia|].
  cbn in Hs. rewrite Nat2Z.inj_succ. lia.
Qed.

Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_sizes : ltac2:(tb__ "0|2|
S0S13S12ScQ40A1M0G0A2M1A1SfS0S23R2R1A2S2S29R1A1S6S7S18G1R1A2A1S2R2ZfffA2A2A2A3Fl;FnZ;").
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Theorem free_gap_of_totals : ltac2:(tb__ "0|5|
S30S0S0S0S0S1Z0M0R4A2SfS0S4R4S2bA2G0A3S1G0R5A2S1R5S9S5Z2M1Z40A2S5G1Z20A2A2A2S1S29S14S12ScQ40M2A1M3G3A2M4S2eR9A1S2dR9A1A3A1R5A2S1S2S2S2R8R9A2R6A2S6S7S18G4S14G4S2eRaA1S2dRaA1A3A2A1S2R9ZfffA2A2A2R7A2S11S0S0SeSfS0S4R1S2bA2G0A3SeS1RaR1A2SeS1S2R1RbA2R9A2SfS15S2cS14G4S2eRcA1S2dRcA1A3SdG2R1A2SdG2RbA2A3S17A3A2A2A2Lg;A2F_;F_;F_;F_;F_;F_;Ftot;FC;FF;FnZ;Fh;").
Proof.
  intros h nZ F C tot HnZ HFal HF0 HC Htot Hband.
  destruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ F C HnZ HFal HF0 HC) as (g & Hal & Hfl & Hc & Hfree).
  { rewrite gap_weight_sizes. lia. }
  exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|exact Hfree].
Qed.

Corollary free_gap_below_top : ltac2:(tb__ "0|5|
S30S0S0S0S37R4A1S1Z0M0R4A2SfS0S4R4S2bA2G0A3S1G0R5A2S1S29S14S12ScQ40M1A1M2G2A2M3S2eR8A1S2dR8A1A3A1R5A2S1S2S2S2R7R8A2R6A2S6S7S18G3S14G3S2eR9A1S2dR9A1A3A2A1S2R8ZfffA2A2A2S36A2S11S0S0SeSfS0S4R1S2bA2G0A3SeS1R9R1A2SeS1S2R1RaA2M4S36A2SeS1G4S2fRbA1A2SfS15S2cS14G3S2eRbA1S2dRbA1A3SdG1R1A2SdG1RaA2A3S17A3A2A2A2A2Lg;A2F_;F_;F_;F_;F_;F_;Ftot;FF;FnZ;Fh;").
Proof.
  intros h nZ F tot Hsp HnZ HFal HF0 Htot Hband.
  destruct (free_gap_of_totals h nZ F alloc_ceiling_lo tot HnZ HFal HF0 ltac:(unfold alloc_ceiling_lo; lia) Htot Hband)
    as (g & Hal & Hfl & Hc & Hfree).
  exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|]. split; [|exact Hfree].
  apply (alloc_top_ge_lo h); [exact Hsp | exact Hc].
Qed.

Definition ledger_split (l : list (word * word)) (K Y : Z) : Prop := ltac2:(tb__ "0|3|
ScQ40M0A1M1G1S3aS12G1G1A2S16G1G1R2R1A4Vl;A3S10S1S2SbG0R3A2M2SbG0R2A2A2VK;A2S1VY;G2A2A2F_;Fs;Fb;").

Lemma ledger_split_nil : ltac2:(tb__ "0|1|
S0S0S21S1eS12ScQ40A1M0G0A2A1R2R1A3FY;FK;").
Proof. intros K Y b s []. Qed.

Lemma ledger_split_mono : ltac2:(tb__ "0|1|
S13S12ScQ40A1M0G0A2A1S0S0S0S21R4R3R2A3S1R2R3A2S21R6R5R3A3F_;F_;FY';FY;FK;Fl;").
Proof. intros l K Y Y' H HY b s Hin. destruct (H b s Hin); [left|right]; lia. Qed.

Lemma ledger_split_cons : ltac2:(tb__ "0|4|
S13S12ScQ40M0A1M1G1A2M2A1S0S0G1G1S21R5R4R3A3S10S1S2SbG0R3A2M3SbG0R2A2A2R5A2S1R4G3A2A2S21S19G2S16G1G1R4R3A4R7A3R6R5A3F_;F_;Fs;Fb;FY;FK;Fl;").
Proof.
  intros l K Y b s H Hbs b' s' [Heq|Hin]; [injection Heq as <- <-; exact Hbs|].
  exact (H b' s' Hin).
Qed.

Lemma ledger_split_app : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2S0S0S21R4R2R1A3S21R4R3R2A3S21S14G1R6R5A3R4R3A3F_;F_;FY;FK;Fl2;Fl1;").
Proof.
  intros l1 l2 K Y H1 H2 b s Hin. apply in_app_iff in Hin as [Hin|Hin]; eauto.
Qed.

Lemma ledger_split_app_inv : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2S0S0S21S14G1R4R3A3R2R1A3SeS21R5R3R2A3S21R4R3R2A3A2F_;FY;FK;Fl2;Fl1;").
Proof.
  intros l1 l2 K Y H. split; intros b s Hin; apply H; apply in_app_iff; auto.
Qed.

Lemma ledger_split_incl : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2S0S0S21R4R2R1A3S3cG1R4R5A3S21R5R4R3A3F_;F_;FY;FK;Fl';Fl;").
Proof. intros l l' K Y H Hincl b s Hin. apply H. apply Hincl. exact Hin. Qed.

Lemma ledger_split_filter : ltac2:(tb__ "0|2|
S12ScQ40A1M0G0A2M1S15F_;S13G1A1S0S0S21R3R2R1A3S21S3bG1R5R4A3R3R2A3F_;FY;FK;Fl;Ff;").
Proof.
  intros f l K Y H. apply (ledger_split_incl l); [exact H|].
  intros x Hx. apply filter_In in Hx. tauto.
Qed.

Lemma ledger_split_window_free : ltac2:(tb__ "0|4|
S13S12ScQ40M0A1M1G1A2A1S0S0S0S1Z0M2R3A2S3G2R2A2S1S2R5S6Z2M3R3A2A2R4A2S3R5S5G3Z40A2A2S21R8R7R6A3SfS15S2cR9SdG0S9R7R6A2A2SdG0R6A2A3S17A3F_;F_;F_;F_;F_;FnZ;FY;FK;Fl;").
Proof.
  intros l K Y nZ HK HnZ HY HY64 Hsplit.
  apply region_free_intro. intros b s Hin.
  unfold iv_overlap. rewrite !fg_u64_lit by lia.
  pose proof (bv_unsigned_in_range 64 s).
  destruct (Hsplit b s Hin) as [Hlow|Hhigh].
  - apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Definition band_covered (l : list (word * word)) (lo hi : Z) : Prop := ltac2:(tb__ "0|3|
S0SeS1Vlo;R1A2S3R1Vhi;A2A2S11ScQ40M0A1M1G1S11G1G1SeS3aS12G1G1A2S16G1G1R2R1A4Vl;A3SeS1SbG0R2A2M2R4A2S3R4S2G2SbG0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fx;").

Lemma band_covered_empty : ltac2:(tb__ "0|1|
S13S12ScQ40A1M0G0A2A1S0S0S1R1R2A2S1fR4R3R2A3F_;Fhi;Flo;Fl;").
Proof. intros l lo hi H x Hx. lia. Qed.

Lemma band_covered_mono : ltac2:(tb__ "0|1|
S13S12ScQ40A1M0G0A2A1S0S0S0S0S1fR5R4R3A3S1R5R3A2S1R3R5A2S1fR8R5R4A3F_;F_;F_;Fhi';Flo';Fhi;Flo;Fl;").
Proof. intros l lo hi lo' hi' H H1 H2 x Hx. apply H. lia. Qed.

Lemma band_covered_incl : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2S0S0S1fR4R2R1A3S3cG1R5R4A3S1fR5R4R3A3F_;F_;Fhi;Flo;Fl';Fl;").
Proof.
  intros l l' lo hi H Hincl x Hx. destruct (H x Hx) as (b & s & Hin & Hbs).
  exists b, s. split; [apply Hincl; exact Hin | exact Hbs].
Qed.

Lemma band_covered_cons : ltac2:(tb__ "0|2|
S13S12ScQ40A1M0G0A2M1A1G1S0S0S1fR4R2R1A3S1fS19G1R4R5A3R3R2A3F_;Fhi;Flo;Fe;Fl;").
Proof. intros l e lo hi H. apply (band_covered_incl l); [exact H | intros x Hx; right; exact Hx]. Qed.

Lemma band_covered_app_l : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2S0S0S1fR4R2R1A3S1fS14G1R5R4A3R3R2A3F_;Fhi;Flo;Fl2;Fl1;").
Proof. intros l1 l2 lo hi H. apply (band_covered_incl l1); [exact H | intros x Hx; apply in_app_iff; left; exact Hx]. Qed.

Lemma band_covered_app_r : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2S0S0S1fR3R2R1A3S1fS14G1R5R4A3R3R2A3F_;Fhi;Flo;Fl2;Fl1;").
Proof. intros l1 l2 lo hi H. apply (band_covered_incl l2); [exact H | intros x Hx; apply in_app_iff; right; exact Hx]. Qed.

Lemma band_covered_app_cons : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2G1S0S0S1fS14G1R5R4A3R2R1A3S1fS14G1R6S19G1R4R5A3A3R3R2A3F_;Fhi;Flo;Fe;Fl2;Fl1;").
Proof.
  intros l1 l2 e lo hi H. apply (band_covered_incl (l1 ++ l2)); [exact H|].
  intros x Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx].
Qed.

Lemma band_covered_entry : ltac2:(tb__ "0|4|
S13S12ScQ40M0A1M1G1A2M2A1G1G1S3aG2S16G1G1R2R1A4R3A3S1fR4SbG0R3A2M3S2G3SbG0R2A2A2A3F_;Fs;Fb;Fl;").
Proof. intros l b s Hin x Hx. exists b, s. split; [exact Hin | exact Hx]. Qed.

Lemma band_covered_join : ltac2:(tb__ "0|1|
S13S12ScQ40A1M0G0A2A1S0S0S0S1fR4R3R2A3S1fR5R3R2A3S1fR6R5R3A3F_;F_;Fhi;Fmid;Flo;Fl;").
Proof.
  intros l lo mid hi H1 H2 x Hx.
  destruct (Z.lt_ge_cases x mid); [apply H1 | apply H2]; lia.
Qed.

Lemma band_covered_transfer : ltac2:(tb__ "0|5|
S13S12ScQ40M0A1M1G1A2M2A1M3G3S0S0S1fR4R2R1A3G1G1S0S3aG2S16G1G1R3R2A4R8A3SeS1R7R2A2S3R2R6A2A2SeS1SbG0R5A2M4R3A2S3R3S2G4SbG0R4A2A2A2A2S3aG2S16G1G1R6R5A4RaA3F_;F_;F_;Fx;Fs;Fb;S1fR5R4R3A3F_;F_;Fhi;Flo;Fl';Fl;").
Proof.
  intros l l' lo hi H HT x Hx. destruct (H x Hx) as (b & s & Hin & Hbs).
  exists b, s. split; [exact (HT b s x Hin Hx Hbs) | exact Hbs].
Qed.

Lemma band_covered_filter : ltac2:(tb__ "0|4|
S12ScQ40M0A1M1G1A2M2S15Fx;S13G2A1S0S0S1fR3R2R1A3G1G1S3aG2S16G1G1R2R1A4R6A3SfS15R8S16G1G1R3R2A4A1S1aA3S10S1S2SbG0R4A2M3SbG0R3A2A2R7A2S1R6G3A2A2F_;F_;Fs;Fb;S1fS3bG2R6R5A3R4R3A3F_;F_;Fhi;Flo;Fl;Ff;").
Proof.
  intros f l lo hi H Hf. apply (band_covered_transfer l); [exact H|].
  intros b s x Hin Hx Hbs. apply filter_In. split; [exact Hin|].
  destruct (f (b, s)) eqn:E; [reflexivity|exfalso].
  destruct (Hf b s Hin E); lia.
Qed.

Theorem grant_avoids_band : ltac2:(tb__ "0|3|
S13S12ScQ40M0A1M1G1A2A1S0S0G1G1S1fR5R4R3A3S3R5R4A2SfS15S2cR7R4R3A3S17A3S3Z0SbG0R4A2A2S10S1S2SbG0R6A2M2SbG0R5A2A2R8A2S1R7G2A2A2F_;F_;F_;F_;Fn;Fa;Fhi;Flo;Fl;").
Proof.
  intros l lo hi a n Hcov Hlh Hfree Hn.
  destruct (Z.le_gt_cases (bv_unsigned a + bv_unsigned n) lo) as [H1|H1]; [left; exact H1|].
  destruct (Z.le_gt_cases hi (bv_unsigned a)) as [H2|H2]; [right; exact H2|].
  exfalso.
  set (x := Z.max (bv_unsigned a) lo).
  assert (Hx : lo <= x < hi) by (subst x; lia).
  destruct (Hcov x Hx) as (b & s & Hin & Hbs).
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov.
  destruct Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; subst x; lia.
Qed.

Definition IMG_BAND_LO : Z := 0x10000.
Definition IMG_BAND_HI : Z := 0x646000.

Definition SHADOW_BAND_LO : Z := 0x7fff7000.
Definition SHADOW_RW_LO_END : Z := 0x8fff7000.
Definition SHADOW_RW_HI_BEG : Z := 0x2008fff7000.
Definition SHADOW_BAND_HI : Z := 0x10007fff8000.

Definition kHighMemBeg : Z := SHADOW_BAND_HI.

Definition DYN_LO : Z := IMG_BAND_HI.
Lemma DYN_LO_val : DYN_LO = 0x646000.
Proof. reflexivity. Qed.

Lemma shadow_band_covered : ltac2:(tb__ "0|5|
S13S12ScQ40M0A1M1G1A2M2A1G1G1G1G1G1G1S3aG2S16G1G1R6R5A4R7A3S3aG2S16G1G1R5R4A4R8A3S3aG2S16G1G1R4R3A4R9A3SfS0SbG0R9A2M3S22A3SfS0S2SbG0RaA2G3A2M4S28A3SfS0G3S28A3SfS0G4S27A3SfS0G3S27A3SfS0G4S20A3S1fR10S22S20A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn4;Fa4;Fn3;Fa3;Fn2;Fa2;Fl;").
Proof.
  intros l a2 n2 a3 n3 a4 n4 H2 H3 H4 E2 F2 E3 F3 E4 F4.
  apply (band_covered_join l _ SHADOW_RW_LO_END).
  { rewrite <- E2, <- F2. apply band_covered_entry. exact H2. }
  apply (band_covered_join l _ SHADOW_RW_HI_BEG).
  { rewrite <- E3, <- F3. apply band_covered_entry. exact H3. }
  rewrite <- E4, <- F4. apply band_covered_entry. exact H4.
Qed.

Theorem grant_windows : ltac2:(tb__ "0|6|
S13S12ScQ40M0A1M1G1A2A1G1G1S0S1fR4S25S24A3S1fR5S22S20A3SfS15S2cR6R5R4A3S17A3S3Z0M2SbG0R6A2A2SfS0S4SbG0R7A2M3S2bA2G2A3S3G2G3A2S1S2SbG0R9A2SbG0R8A2A2R7A2S1R8S33A2S10SeS1Z1000SbG0RbA2M4A2S1S2G4SbG0RaA2A2M5S25A2A2S10SeS1S24G4A2S1G5S22A2A2SeS1S20G4A2S1G5S33A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftop;Fn;Fa;Fl;").
Proof.
  intros l a n top Himg Hsh Hfree Ha Hal Hn Htop Hhi.
  assert (Hpg : 4096 <= bv_unsigned a).
  { pose proof (page_multiple_eq _ Hal) as E. clear Hal. lia. }
  pose proof (grant_avoids_band l _ _ a n Himg ltac:(unfold IMG_BAND_LO, IMG_BAND_HI; lia) Hfree Hn) as Wi.
  pose proof (grant_avoids_band l _ _ a n Hsh ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) Hfree Hn) as Ws.
  unfold IMG_BAND_LO, IMG_BAND_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, alloc_ceiling_hi in *.
  destruct Wi as [Wi|Wi]; [left; split; [exact Hpg | exact Wi]|].
  destruct Ws as [Ws|Ws]; [right; left; split; [exact Wi | exact Ws]|].
  right; right. split; [exact Ws | lia].
Qed.

Corollary grant_dyn_lo : ltac2:(tb__ "0|6|
S13S12ScQ40M0A1M1G1A2A1G1G1S0S1fR4S25S24A3S1fR5S22S20A3SfS15S2cR6R5R4A3S17A3S3Z0M2SbG0R6A2A2SfS0S4SbG0R7A2M3S2bA2G2A3S3Zf000G3A2S1S2SbG0R9A2SbG0R8A2A2R7A2S1R8S33A2SeS1S24SbG0RbA2M4A2SeS10S1S2G4SbG0RaA2A2M5S22A2S1S20G4A2A2S1G5S33A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftop;Fn;Fa;Fl;").
Proof.
  intros l a n top Himg Hsh Hfree Ha Hal Hn Htop Hhi.
  destruct (grant_windows l a n top Himg Hsh Hfree Ha Hal ltac:(lia) Htop Hhi) as [W|[W|W]];
    unfold IMG_BAND_LO, IMG_BAND_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, alloc_ceiling_hi in *; lia.
Qed.

Corollary grant_high_of_big : ltac2:(tb__ "0|5|
S13S12ScQ40M0A1M1G1A2A1G1G1S0S1fR4S25S24A3S1fR5S22S20A3SfS15S2cR6R5R4A3S17A3S3Z0M2SbG0R6A2A2SfS0S4SbG0R7A2M3S2bA2G2A3S1S5Z2Z1fA2G3A2S1S2SbG0R9A2SbG0R8A2A2R7A2S1R8S33A2SeS1S20SbG0RbA2M4A2S1S2G4SbG0RaA2A2S33A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftop;Fn;Fa;Fl;").
Proof.
  intros l a n top Himg Hsh Hfree Ha Hal Hn Htop Hhi.
  destruct (grant_windows l a n top Himg Hsh Hfree Ha Hal ltac:(lia) Htop Hhi) as [W|[W|W]];
    unfold IMG_BAND_LO, IMG_BAND_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, alloc_ceiling_hi in *; lia.
Qed.

Lemma sh_low_window : ltac2:(tb__ "0|1|
S0SeS1Z1000R1A2S3R1S22A2A2SeS1S2S22Z1200A2S2S8R2Z8A2Z7fff8000A2M0A2S3G0S9S28Z200A2A2A2F_;Fz;").
Proof. intros z Hz. unfold SHADOW_BAND_LO, SHADOW_RW_LO_END in *. split; [|]; Z.to_euclidean_division_equations; lia. Qed.

Lemma sh_high_window : ltac2:(tb__ "0|1|
S0SeS1S20R1A2S3R1S5Z2Z2fA2A2A2SeS1S27S2S8R2Z8A2Z7fff8000A2M0A2S3G0S20A2A2F_;Fz;").
Proof. intros z Hz. unfold SHADOW_BAND_HI, SHADOW_RW_HI_BEG in *. Z.to_euclidean_division_equations; lia. Qed.

Lemma shadow_band_below_alloc : ltac2:(tb__ "0|1|
SeS1S2S2S20S5Z2M0Z25A2A2S5G0Z20A2A2S36A2S3S33S5G0Z2fA2A2A2").
Proof. unfold SHADOW_BAND_HI, alloc_ceiling_lo, alloc_ceiling_hi. split; reflexivity || lia. Qed.

Lemma mmap_nZ_ge_len : ltac2:(tb__ "0|1|
ScQ40M0A1S1SbG0R1A2S34R1A1A2Flen;").
Proof. intros len. unfold mmap_nZ. apply pg_round_up_ge. Qed.

Lemma mmap_n_val_of_top : ltac2:(tb__ "0|2|
S30ScQ40M0A1M1G1S1S2SbG0R2A2S34R1A1A2S2fR3A1A2SfS0SbG0S35R2A1A2S34R2A1A3F_;Flen;Fa;Fh;").
Proof.
  intros h a len Htop. unfold mmap_n. apply fg_u64_lit.
  pose proof (mmap_nZ_nonneg len). pose proof (alloc_top_lt h). pose proof (fg_u64_range a).
  unfold two_pow_64 in *. lia.
Qed.

Section PlaceOk.
  Variable m : Model.
  Let h := m_vmmaps m.
  Hypothesis Hsp : init_sp_ok h.
  Hypothesis Himg : ltac2:(tb__ "0|1|
S1fS14S12ScQ40A1M0G0A2S2eVh;A1S2dVh;A1A3S25S24A3").
  Hypothesis Hsh : ltac2:(tb__ "0|1|
S1fS14S12ScQ40A1M0G0A2S2eVh;A1S2dVh;A1A3S22S20A3").

  Lemma place_windows : ltac2:(tb__ "0|7|
ScQ40M0A1M1G1SfS0S4SbG0R2A2S2bA2Z0M2A3S3G2SbG0R3A2A2S1S2SbG0R4A2S34R3A1A2S2fVh;A1M3A2SfS15S2cS14S12G1G1A2S2eVh;A1S2dVh;A1A3R5S35R4A1A3S17A3S3G2SbG0R5A2A2SeSfS0SbG0S35R6A1A2S34R6A1M4A3SeS1S2SbG0R7A2M5G4A2M6G3A2SeS1G3S33A2S10SeS1Z1000G5A2S1G6S25A2A2S10SeS1S24G5A2S1G6S22A2A2SeS1S20G5A2S1G6S33A2A2A2A2A2A2A2F_;F_;F_;F_;F_;Flen;Fa;").
  Proof using Himg Hsh Hsp.
    intros a len Hal Ha Htop Hfree Hlen.
    pose proof (mmap_n_val_of_top h a len Htop) as En.
    pose proof (alloc_top_bounds h Hsp) as [_ Hhi].
    pose proof (mmap_nZ_ge_len len) as Hge.
    split; [exact En|]. split; [exact Htop|]. split; [exact Hhi|].
    rewrite <- En.
    apply (grant_windows (vm_reserved h ++ vm_maps h) a (mmap_n len) (alloc_top h) Himg Hsh Hfree Ha Hal);
      rewrite ?En; [lia | exact Htop | exact Hhi].
  Qed.

  Lemma place_ok_windows : ltac2:(tb__ "0|6|
ScQ40M0A1M1G1G1G1S38R4R3Vm;R2R1A5S3Z0SbG0R3A2M2A2SeSfS0SbG0S35R4A1A2S34R4A1M3A3SeS1S2G2G3A2M4S2fVh;A1M5A2SeS1G5S33A2S10SeS1Z1000G2A2S1G4S25A2A2S10SeS1S24G2A2S1G4S22A2A2SeS1S20G2A2S1G4S33A2A2A2A2A2A2A2F_;F_;Fa;Flen;Fflags;Faddr;").
  Proof using Himg Hsh Hsp.
    intros addr flags len a (Hal & Ha & Htop & Hfree & _) Hlen. exact (place_windows a len Hal Ha Htop Hfree Hlen).
  Qed.

  Lemma place_ok_none_windows : ltac2:(tb__ "0|6|
ScQ40M0A1M1G1G1S39R3Vm;R2R1A4S3Z0SbG0R3A2M2A2SeSfS0SbG0S35R4A1A2S34R4A1M3A3SeS1S2G2G3A2M4S2fVh;A1M5A2SeS1G5S33A2S10SeS1Z1000G2A2S1G4S25A2A2S10SeS1S24G2A2S1G4S22A2A2SeS1S20G2A2S1G4S33A2A2A2A2A2A2A2F_;F_;Fa;Flen;Faddr;").
  Proof using Himg Hsh Hsp.
    intros addr len a (Hal & Ha & Htop & Hfree) Hlen. exact (place_windows a len Hal Ha Htop Hfree Hlen).
  Qed.

  Lemma place_dyn_lo : ltac2:(tb__ "0|6|
ScQ40M0A1M1G1SfS0S4SbG0R2A2S2bA2Z0M2A3S3G2SbG0R3A2A2S1S2SbG0R4A2S34R3A1A2S2fVh;A1M3A2SfS15S2cS14S12G1G1A2S2eVh;A1S2dVh;A1A3R5S35R4A1A3S17A3S3Zf000SbG0R5A2A2SeS1S2aSbG0R7A2M4A2SeS10S1S2G4S34R6A1A2M5S22A2S1S20G4A2A2SeS1G5G3A2S1G3S33A2A2A2A2F_;F_;F_;F_;F_;Flen;Fa;").
  Proof using Himg Hsh Hsp.
    intros a len Hal Ha Htop Hfree Hlen.
    destruct (place_windows a len Hal Ha Htop Hfree ltac:(lia)) as (En & Ht & Hhi & W).
    pose proof (mmap_nZ_ge_len len). unfold DYN_LO, IMG_BAND_LO, IMG_BAND_HI, SHADOW_BAND_LO, SHADOW_BAND_HI in *.
    destruct W as [W|[W|W]]; lia.
  Qed.

  Lemma band_covered_after_grant : ltac2:(tb__ "0|4|
S0S0ScQ40A1M0G0S1fS14S12G0G0A2M1S2eVh;A1M2S2dVh;A1M3A3R4R3A3S1fS14G1G2S19G1S16G0G0R3R2A4G3A3A3R5R4A3F_;Fn;Fa;Fhi;Flo;").
  Proof. intros lo hi a n H. apply band_covered_app_cons. exact H. Qed.
End PlaceOk.
