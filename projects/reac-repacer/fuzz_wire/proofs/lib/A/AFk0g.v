(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AFk0g.v at 88154566652a (donor image sha256 61768cf4739b), with its module paths changed and A/AB1v imported for A/AWalkFw0. *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, for a Theorem Labs lane's lib/A/AFk0.v; split agreed with a Theorem Labs lane): the ledger
   and amwf part of AD3j.AR_but_depot_grow's proof (the setup, ledger and amwf parts of the Lemma at lib/A/AD3j.v:1746),
   stated over ALedger at the walk's layout lyW instead of AR_but_depot: no exclusion list there, so the two
   new maps are covered at the grown layout (the nodes block by its static extent, the store block by its lazy zone).
   The proof is the A twin of a Theorem Labs lane's lib/B/YFk0g.v, YD3* -> AD3*.
   rule 24: proves no function (kind: ledger lemma). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AF0m AF0x AB1w AFl0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK0v YK13 YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YK0g YF0p YA0o.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import KnBlockExt.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AD3d AD3h AD3c AD3g.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AD3a AD3b AD3i AFem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AD3k AB13.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YP03 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YG0b YG08.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AD3j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac YM03.lf_lia_orig ::= Zify.zify; xlia zchecker.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The ledger after knock's first StackDepot Put, at the grown layout (both blocks mapped, the store block lazy), from
   the ledger at the walk's layout lyW (ly up to its secondary slots) and B2's post (placement, freshness of both blocks
   against every map of the Put's entry model md, whose maps are mdold's). *)
Lemma ALedger_grow : forall (B : asyms) (ly lyW : alayout) (S Sf : astate) (mdold mdf : Model) (Wc W' : world tfibsegs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (tr : list Z) (nb sb : Z) (md' : Model) (c' : config),
  AD3j.ly_core lyW = AD3j.ly_core ly -> layout_ok lyW -> ly_NB ly = 0 -> ly_SB ly = 0 -> nb <> 0 -> sb <> 0 ->
  ALedger tfibsegs lyW Sf mdold -> amwf mdold ->
  Forall (fun e => 0 <= snd e < 2 ^ 64) (sec_extents lyW Sf) -> sec_placed lyW Sf ->
  AD3j.depot_first_put_post depot_ok AD3j.as_const_g2f B Wc ly S regs mem md tr
    (AD3c.set_ly_SB (AD3g.set_ly_NB ly nb) sb) W' md' c' ->
  vm_maps (m_vmmaps md) = vm_maps (m_vmmaps mdold) ->
  m_vmmaps mdf = m_vmmaps (mmap_model (Z_to_bv 64 sb) (Z_to_bv 64 kStoreBlockSize)
                             (mmap_model (Z_to_bv 64 nb) (Z_to_bv 64 kNodesBlockSize) mdold)) ->
  m_vm_lazy mdf = (Z_to_bv 64 sb, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy mdold ->
  ALedger tfibsegs (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb) Sf mdf /\ amwf mdf.
Proof.
  intros B ly lyW S Sf mdold mdf Wc W' regs mem md tr nb sb md' c' LW LYW N0 S0 NZ SZ L AMWF SZE PL POST VMd HVM LZ.
  destruct POST as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PNB & ANB & PSB & ASB & DNS & FNB & FSB & _ & _ & _ & _
    & VNB & VSB).
  change (ly_NB (AD3c.set_ly_SB (AD3g.set_ly_NB ly nb) sb)) with nb in *.
  change (ly_SB (AD3c.set_ly_SB (AD3g.set_ly_NB ly nb) sb)) with sb in *.
  (* the walk's layout lyW is ly up to its secondary slots *)
  assert (WNB : ly_NB lyW = 0) by exact (eq_trans (f_equal ly_NB LW) N0).
  assert (WSB : ly_SB lyW = 0) by exact (eq_trans (f_equal ly_SB LW) S0).
  assert (EXTW : ext_but_NB lyW = ext_but_NB ly)
    by (change (ext_but_NB (AD3j.ly_core lyW) = ext_but_NB (AD3j.ly_core ly)); rewrite LW; reflexivity).
  assert (XW : ly_extra lyW = ly_extra ly) by exact (f_equal ly_extra LW).
  unfold AD3j.first_put_avoid in FNB, FSB. rewrite <- EXTW, <- XW in FNB, FSB.
  apply Forall_app in FNB as [FNB1 FNB]. apply Forall_app in FNB as [FNB2 _].
  apply Forall_app in FSB as [FSB1 FSB]. apply Forall_app in FSB as [FSB2 _].
  unfold ext_but_NB in FNB1, FSB1. rewrite WSB in FNB1, FSB1. cbn [Z.eqb] in FNB1, FSB1. rewrite app_nil_r in FNB1, FSB1.
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
  pose proof (YG0s.in_app_small _ _ ANB ltac:(unfold kNodesBlockSize; lia)) as NBR.
  pose proof (YG0s.in_app_small _ _ ASB ltac:(unfold kStoreBlockSize; lia)) as SBR.
  unfold kNodesBlockSize in NBR. unfold kStoreBlockSize in SBR.
  (* the final model: the entry maps plus both blocks, the store block lazy *)
  assert (VMF : vm_maps (m_vmmaps mdf) = wiv (sb, kStoreBlockSize) :: wiv (nb, kNodesBlockSize) :: vm_maps (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (NAF : vm_noaccess (m_vmmaps mdf) = vm_noaccess (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (LIMF : vm_limit (m_vmmaps mdf) = vm_limit (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (RESF : vm_reserved (m_vmmaps mdf) = vm_reserved (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (TOPF : alloc_top (m_vmmaps mdf) = alloc_top (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (ISPF : vm_init_sp (m_vmmaps mdf) = vm_init_sp (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (LZF : m_vm_lazy mdf = wiv (sb, kStoreBlockSize) :: m_vm_lazy mdold) by exact LZ.
  assert (INF : forall e, In e (vm_maps (m_vmmaps mdold)) -> In e (vm_maps (m_vmmaps mdf)))
    by (intros e He; rewrite VMF; right; right; exact He).
  assert (WNBb : bv_unsigned (w64 nb) = nb) by (apply YK0g.fg_lit; lia).
  assert (WSBb : bv_unsigned (w64 sb) = sb) by (apply YK0g.fg_lit; lia).
  assert (WKN : bv_unsigned (w64 kNodesBlockSize) = kNodesBlockSize) by (apply YK0g.fg_lit; unfold kNodesBlockSize; lia).
  assert (WKS : bv_unsigned (w64 kStoreBlockSize) = kStoreBlockSize) by (apply YK0g.fg_lit; unfold kStoreBlockSize; lia).
  assert (BSB0 : bv_unsigned (fst (wiv (sb, kStoreBlockSize))) = sb) by exact WSBb.
  assert (SSB0 : bv_unsigned (snd (wiv (sb, kStoreBlockSize))) = kStoreBlockSize) by exact WKS.
  assert (BNB0 : bv_unsigned (fst (wiv (nb, kNodesBlockSize))) = nb) by exact WNBb.
  assert (SNB0 : bv_unsigned (snd (wiv (nb, kNodesBlockSize))) = kNodesBlockSize) by exact WKN.
  destruct L as [AIMG ALIM ARES APRIM AQ AHS ASEC ACOV AEX APERM ABAND ASECX ATOP AIMGCOV ASHNA].
  pose proof AMWF as ((MW1 & MW2 & MW3 & MWP & MWSP) & MWPOS).
  (* every secondary extent of Sf is a map of the Put's entry model, so both blocks miss it *)
  assert (SECB : forall e, In e (sec_extents lyW Sf) ->
            zdisjoint (nb, kNodesBlockSize) e /\ zdisjoint (sb, kStoreBlockSize) e /\
            bv_unsigned (fst (wiv e)) = fst e /\ bv_unsigned (snd (wiv e)) = snd e).
  { intros e He. pose proof (ASEC e He) as Hm. rewrite <- VMd in Hm.
    pose proof (proj1 (Forall_forall _ _) VNB _ Hm) as D1. pose proof (proj1 (Forall_forall _ _) VSB _ Hm) as D2.
    pose proof (proj1 (Forall_forall _ _) SZE e He) as SZe. cbv beta in SZe.
    destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & IAe & _).
    destruct (YG0s.in_app_small _ _ IAe ltac:(lia)) as [IE1 IE2].
    assert (E1 : bv_unsigned (fst (wiv e)) = fst e) by (unfold wiv, w64; cbn [fst]; apply YK0g.fg_lit; lia).
    assert (E2 : bv_unsigned (snd (wiv e)) = snd e) by (unfold wiv, w64; cbn [snd]; apply YK0g.fg_lit; lia).
    cbv beta in D1, D2. rewrite E1, E2 in D1, D2. split; [exact D1|]. split; [exact D2|]. split; [exact E1 | exact E2]. }
  split.
  - constructor.
    + exact AIMG.
    + rewrite LIMF. exact ALIM.
    + rewrite RESF. exact ARES.
    + (* al_prim *)
      destruct APRIM as (pieces & PP & PI). exists pieces. split; [exact PP|]. intros p.
      change (ly_prim (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb)) with (ly_prim lyW). rewrite (PI p), VMF.
      split; [intros (Hin & H1 & H2 & H3); split; [right; right; exact Hin | tauto]|].
      intros (Hin & H1 & H2 & H3). split; [|tauto]. cbn [In] in Hin.
      pose proof (proj1 (Forall_forall _ _) FNB1 (ly_prim lyW, kPrimResvSize) ltac:(left; reflexivity)) as DP1.
      pose proof (proj1 (Forall_forall _ _) FSB1 (ly_prim lyW, kPrimResvSize) ltac:(left; reflexivity)) as DP2.
      unfold zdisjoint in DP1, DP2. cbn [fst snd] in DP1, DP2, H2, H3.
      destruct Hin as [Hin|[Hin|Hin]]; [| |exact Hin]; exfalso.
      * assert (Hf : bv_unsigned (fst (wiv (sb, kStoreBlockSize))) = bv_unsigned (fst (wiv p))) by (rewrite Hin; reflexivity).
        assert (Hs : bv_unsigned (snd (wiv (sb, kStoreBlockSize))) = bv_unsigned (snd (wiv p))) by (rewrite Hin; reflexivity).
        change (bv_unsigned (w64 sb) = bv_unsigned (w64 (fst p))) in Hf.
        change (bv_unsigned (w64 kStoreBlockSize) = bv_unsigned (w64 (snd p))) in Hs.
        pose proof (lo_high _ LYW) as HI. unfold in_high, kHighMemBeg in HI.
        rewrite WSBb, YK0g.fg_lit in Hf by (unfold kPrimResvSize in *; lia).
        rewrite WKS, YK0g.fg_lit in Hs by (unfold kPrimResvSize in *; lia).
        unfold kStoreBlockSize, kPrimResvSize in *. lia.
      * assert (Hf : bv_unsigned (fst (wiv (nb, kNodesBlockSize))) = bv_unsigned (fst (wiv p))) by (rewrite Hin; reflexivity).
        assert (Hs : bv_unsigned (snd (wiv (nb, kNodesBlockSize))) = bv_unsigned (snd (wiv p))) by (rewrite Hin; reflexivity).
        change (bv_unsigned (w64 nb) = bv_unsigned (w64 (fst p))) in Hf.
        change (bv_unsigned (w64 kNodesBlockSize) = bv_unsigned (w64 (snd p))) in Hs.
        pose proof (lo_high _ LYW) as HI. unfold in_high, kHighMemBeg in HI.
        rewrite WNBb, YK0g.fg_lit in Hf by (unfold kPrimResvSize in *; lia).
        rewrite WKN, YK0g.fg_lit in Hs by (unfold kPrimResvSize in *; lia).
        unfold kNodesBlockSize, kPrimResvSize in *. lia.
    + exact (INF _ AQ).
    + exact (INF _ AHS).
    + intros e He. exact (INF _ (ASEC e He)).
    + (* al_cover: the store block is the grown layout's lazy SB zone, the nodes block one of its static extents *)
      assert (NZG : ly_NB (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb) <> 0) by exact NZ.
      assert (SZG : ly_SB (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb) <> 0) by exact SZ.
      assert (LZS : In (sb, kStoreBlockSize) (lazy_zones (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb))).
      { unfold lazy_zones. change (ly_SB (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb)) with sb.
        rewrite (proj2 (Z.eqb_neq _ 0) SZ). apply in_or_app. left. right. right. right. left. reflexivity. }
      assert (LZN : In (nb, kNodesBlockSize) (lazy_zones (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb))).
      { unfold lazy_zones. apply in_or_app. right. apply in_or_app. right.
        rewrite (static_extents_set _ NZG SZG). change (ly_NB (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb)) with nb.
        right. right. right. right. left. reflexivity. }
      intros e He. rewrite VMF in He. destruct He as [He|[He|He]].
      * apply Exists_exists. exists (sb, kStoreBlockSize). split.
        -- apply in_app_iff. left. exact LZS.
        -- rewrite <- He. rewrite BSB0, SSB0. cbn [fst snd]. lia.
      * apply Exists_exists. exists (nb, kNodesBlockSize). split.
        -- apply in_app_iff. left. exact LZN.
        -- rewrite <- He. rewrite BNB0, SNB0. cbn [fst snd]. lia.
      * pose proof (ACOV e He) as Hc. apply Exists_exists in Hc as (z & Hz & Hcz). apply Exists_exists.
        pose proof (MWPOS e He) as Pe.
        apply in_app_iff in Hz as [Hz|Hz].
        -- destruct (AD3j.lazy_zones_grow lyW nb sb WNB WSB NZ SZ z Hz) as [Ez|Hz'].
           ++ exfalso. subst z. cbn [fst snd] in Hcz. lia.
           ++ exists z. split; [apply in_app_iff; left; exact Hz' | exact Hcz].
        -- exists z. split; [apply in_app_iff; right; exact Hz | exact Hcz].
    + (* al_eager_x *)
      assert (WFo : YK0g.model_ivs_wf mdold)
        by (split; [|split; [|split]]; [intros q Hq; exact (MW1 q Hq) | intros q Hq; exact (MW2 q Hq) |
                                        intros q Hq; exact (MW3 q Hq) | exact MWSP]).
      assert (BSB : YK0g.B (wiv (sb, kStoreBlockSize)) = sb) by exact WSBb.
      assert (SSB : YK0g.S (wiv (sb, kStoreBlockSize)) = kStoreBlockSize) by exact WKS.
      assert (BNB : YK0g.B (wiv (nb, kNodesBlockSize)) = nb) by exact WNBb.
      assert (SNB : YK0g.S (wiv (nb, kNodesBlockSize)) = kNodesBlockSize) by exact WKN.
      assert (WFf : YK0g.model_ivs_wf mdf).
      { split; [|split; [|split]].
        - intros q Hq. rewrite VMF in Hq. destruct Hq as [<-|[<-|Hq]]; [| |exact (MW1 q Hq)]; unfold YK0g.iv_wf;
            rewrite ?BSB, ?SSB, ?BNB, ?SNB; unfold kStoreBlockSize, kNodesBlockSize; lia.
        - intros q Hq. rewrite NAF in Hq. exact (MW2 q Hq).
        - intros q Hq. rewrite LZF in Hq. destruct Hq as [<-|Hq]; [|exact (MW3 q Hq)].
          unfold YK0g.iv_wf. rewrite BSB, SSB. unfold kStoreBlockSize; lia.
        - unfold YK06.init_sp_ok in *. rewrite ISPF. exact MWSP. }
      assert (NBE : nb_eager (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb) = kNodesBlockSize).
      { unfold nb_eager. change (ly_NB (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb)) with nb.
        rewrite (proj2 (Z.eqb_neq _ 0) NZ). reflexivity. }
      assert (NBW : nb_eager lyW = 0) by (unfold nb_eager; rewrite WNB; reflexivity).
      rewrite NBW in AEX. rewrite NBE.
      rewrite (YG0b.eager_used_sem _ WFf), NAF, LZF, VMF. rewrite (YG0b.eager_used_sem _ WFo) in AEX.
      change (sec_extents (AD3c.set_ly_SB (AD3g.set_ly_NB lyW nb) sb) Sf) with (sec_extents lyW Sf).
      set (na := vm_noaccess (m_vmmaps mdold)) in *. set (lz := m_vm_lazy mdold) in *.
      assert (CC : forall a l x, YK0g.covered (a :: l) x = (YK0g.in_iv a x || YK0g.covered l x)%bool) by reflexivity.
      (* the esec term: no secondary byte lies in the store block *)
      assert (ES2 : esec na (wiv (sb, kStoreBlockSize) :: lz) (sec_extents lyW Sf) = esec na lz (sec_extents lyW Sf)).
      { unfold esec. apply AD3j.sum_count_ext_on. intros q x Hq Hx. apply in_map_iff in Hq as (e & <- & He).
        destruct (SECB e He) as (_ & D2 & E1 & E2). unfold YK0g.B, YK0g.S in Hx. rewrite E1, E2 in Hx.
        rewrite !YK0g.covered_app, CC. unfold YK0g.in_iv, YK0g.in_rng. rewrite BSB, SSB.
        unfold zdisjoint in D2. cbn [fst snd] in D2.
        replace ((sb <=? x) && (x <? sb + kStoreBlockSize))%bool with false by (symmetry; apply andb_false_iff;
          destruct D2 as [D2|D2]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]).
        rewrite orb_false_l. reflexivity. }
      rewrite ES2. cbn [YK0g.sum_count].
      assert (C0 : YK0g.iv_count (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
                     (wiv (sb, kStoreBlockSize)) = 0).
      { unfold YK0g.iv_count. rewrite BSB, SSB. apply YK0g.zcount_false. intros x Hx.
        rewrite Z2Nat.id in Hx by (unfold kStoreBlockSize; lia).
        rewrite YK0g.covered_app, CC. unfold YK0g.in_iv, YK0g.in_rng. rewrite BSB, SSB.
        replace ((sb <=? x) && (x <? sb + kStoreBlockSize))%bool with true
          by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        rewrite orb_true_l, orb_true_r. reflexivity. }
      assert (C1 : YK0g.iv_count (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
                     (wiv (nb, kNodesBlockSize)) <= kNodesBlockSize).
      { unfold YK0g.iv_count. rewrite SNB.
        pose proof (YK0g.zcount_le_len (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
          (YK0g.B (wiv (nb, kNodesBlockSize))) (Z.to_nat kNodesBlockSize)) as Hc.
        rewrite Z2Nat.id in Hc by (unfold kNodesBlockSize; lia). exact Hc. }
      assert (C2 : YK0g.sum_count (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
                     (vm_maps (m_vmmaps mdold))
                   <= YK0g.sum_count (fun x => negb (YK0g.covered (na ++ lz) x)) (vm_maps (m_vmmaps mdold))).
      { apply YK0g.sum_count_mono. intros x Hx. rewrite !YK0g.covered_app in *. rewrite CC in Hx.
        apply negb_true_iff in Hx. apply negb_true_iff. apply orb_false_iff in Hx as [Hx1 Hx2].
        apply orb_false_iff in Hx2 as [_ Hx2]. rewrite Hx1, Hx2. reflexivity. }
      lia.
    + (* al_perm *)
      intros z Hz. destruct (AD3j.perm_live_grow lyW nb sb WNB WSB NZ SZ z Hz) as [->|[->|Hz']].
      * rewrite VMF. right. left. reflexivity.
      * rewrite VMF. left. reflexivity.
      * exact (INF _ (APERM z Hz')).
    + intros z Hz. exact (INF _ (ABAND z Hz)).
    + (* al_secx *)
      intros e z He Hz. destruct (AD3j.perm_maps_grow lyW nb sb WNB WSB NZ SZ z Hz) as [->|[->|Hz']].
      * exact (YG0s.zdisjoint_sym _ _ (proj1 (SECB e He))).
      * exact (YG0s.zdisjoint_sym _ _ (proj1 (proj2 (SECB e He)))).
      * exact (ASECX e z He Hz').
    + rewrite TOPF. exact ATOP.
    + exact AIMGCOV.
    + rewrite NAF. exact ASHNA.
  - (* amwf *)
    split.
    + split; [|split; [|split; [|split]]].
      * intros q Hq. rewrite VMF in Hq. destruct Hq as [<-|[<-|Hq]]; [| |exact (MW1 q Hq)];
          rewrite ?BSB0, ?SSB0, ?BNB0, ?SNB0; unfold kStoreBlockSize, kNodesBlockSize; lia.
      * intros q Hq. rewrite NAF in Hq. exact (MW2 q Hq).
      * intros q Hq. rewrite LZF in Hq. destruct Hq as [<-|Hq]; [|exact (MW3 q Hq)].
        rewrite BSB0, SSB0. unfold kStoreBlockSize; lia.
      * rewrite VMF. cbn [pairwise]. rewrite BSB0, SSB0, BNB0, SNB0.
        split; [|split; [|exact MWP]].
        -- apply Forall_cons; [cbv beta; rewrite BNB0, SNB0; unfold zdisjoint in DNS; cbn [fst snd] in DNS; lia|].
           apply Forall_forall. intros q Hq. rewrite <- VMd in Hq.
           pose proof (proj1 (Forall_forall _ _) VSB q Hq) as D. cbv beta in D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
        -- apply Forall_forall. intros q Hq. rewrite <- VMd in Hq.
           pose proof (proj1 (Forall_forall _ _) VNB q Hq) as D. cbv beta in D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
      * unfold YK06.init_sp_ok in *. rewrite ISPF. exact MWSP.
    + intros q Hq. rewrite VMF in Hq. destruct Hq as [<-|[<-|Hq]]; [| |exact (MWPOS q Hq)];
        rewrite ?SSB0, ?SNB0; unfold kStoreBlockSize, kNodesBlockSize; lia.
Qed.
End d.
