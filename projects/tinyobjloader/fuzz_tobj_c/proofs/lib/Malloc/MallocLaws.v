(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "option"; "pair"; "true"; "nat"; "list"; "app"; "cons"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "MInv"; "ma_blocks"; "ma_s"; "ma_owned"; "malloc_rel"; "MA_init"; "calloc_rel"; "free_rel"; "ma_L"; "minv_frame_stmt"; "run_init"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mconsts"; "mc_img_hi"; "mc_img_lo"; "holds"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "owned"; "topL"; "addr_of"; "mc_ctx"; "mc_errno"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "pairwise"; "byteview"; "cell_holds"; "image"; "layout"; "loc"; "ranges_disjoint"; "CTX_SIZE"; "LMem"; "WF"; "alloc_owned"; "footprint"; "layout_ok"; "loc_addr"; "ly_reg"; "mc_loc"; "mc_w"; "user_blocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "UNIT"; "st_init_done"; "PGSZ"; "sptr"; "IB"; "kreq"; "SP"; "astate"; "size_overflows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.Frame"; "static_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws"; "statics_in_image"; "lock_in_image"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfGeom MallocWfRepr MallocWfMain
  MallocLayout MallocFooter MallocFooterLemmas ImageUpd MallocCalloc NestTier MallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pairwise_map_iff {A B : Type} (R : B -> B -> Prop) (f : A -> B) (l : list A) : ltac2:(tb__ "0|0|
S6S3aVB;VR;S5aVA;VB;Vf;Vl;A4A3S3aVA;VA;VA;VR;Vf;R2A1Vf;R1A1A2Ly;Lx;Vl;A3A2").
Proof.
  induction l as [|x t IH]; cbn; [tauto|].
  split; intros [H1 H2]; split.
  - intros y Hy. apply H1. apply in_map. exact Hy.
  - apply IH. exact H2.
  - intros y Hy. apply in_map_iff in Hy as [a [<- Ha]]. apply H1. exact Ha.
  - apply IH. exact H2.
Qed.

Theorem minv_blocks_pairwise : ltac2:(tb__ "0|1|
S26S17S23Q40A1M0SfS23Q8A1A1F_;G0SdF_;S38S18R5R4R3R2R1A5S3aSeS0S0A2S40S19R5A1A3F_;Fvm;Fwok;Frd;FA;FC;").
Proof.
  intros C [s L] rd wok vm (HW & _ & _ & ((HL & _ & _) & _) & _). cbn [ma_s ma_L] in *.
  unfold ma_blocks, blocks. cbn [ma_s ma_L].
  apply pairwise_map_iff.
  pose proof (user_blocks_disjoint s L HW HL) as P.
  apply (proj1 (pairwise_map_iff ranges_disjoint (block_range L) (user_blocks s))) in P.
  exact P.
Qed.

Corollary new_block_disjoint : ltac2:(tb__ "0|3|
S26S17S23Q40A1M0SfS23Q8A1A1F_;G0SdF_;S38S13SeS0S0A2M1A1M2G2G1S18R8R7R6R5R4A5S2G2S19R8A1S14G1R4S15G1R2R3A3A3A3G1S25G1R1S14G1R6R5A3A3S40R5R2A2F_;Fx;F_;F_;Fnb;Fl2;Fl1;Fvm;Fwok;Frd;FA';FC;").
Proof.
  intros C A' rd wok vm l1 l2 nb HM E x Hx.
  pose proof (minv_blocks_pairwise C A' rd wok vm HM) as P. rewrite E in P. clear E HM.
  induction l1 as [|y t IH]; cbn in P.
  - destruct P as [P _]. apply P. exact Hx.
  - destruct P as [P1 P2]. cbn in Hx. destruct Hx as [<- | Hx].
    + specialize (P1 nb ltac:(apply in_app_iff; right; left; reflexivity)).
      unfold ranges_disjoint in *. lia.
    + apply IH; assumption.
Qed.

Lemma user_block_geom : ltac2:(tb__ "0|3|
S53S3eS4fS0S43R4A1S46R4R5A2S25SeS4fS0A2S10S4fS0R4R3A4S4bR6A1A3S4S12S12S4S0S0S1S25SeS3fS0A2S10S3fS0S42S52R2Z0M0A2A1R1A4S45R9A1A3S1S2S0SaS48R8R2A2M1S4eA2G0A3S1S7G0R6A2S1S2S0SaS35R8R7A2M2Z10A2G0A3S1S7S8G1S4cA2G2A2S7S8S8G2R6A2S50A2S8G1R1A2A2A2A2A2A2A2Llen;A2Lr;A2F_;F_;F_;Fn;Fp;FL;Fs;").
Proof.
  intros s L p n HW HL Hin.
  destruct (in_user_blocks_inv s (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & Hk & E).
  injection E as Ep En.
  apply (used_metas_usedX s g am HW) in Hg.
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hlv & Ho & Hext & _).
  exists (prid (am_mem am)), (rg_len rg).
  pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (B1 & B2 & B3).
  pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S2].
  pose proof (stride_mod16 _ _ _ _ _ _ HW Hg) as Hst16.
  pose proof (used_group_aligned [] None U0 s HW _ g am Hg (PeanoNat.Nat.le_refl _)) as Hal16.
  destruct HL as (_ & HAL & _ & _).
  split; [apply footprint_region_In; assumption|].
  split; [exact (HAL _ _ Hr Hlv)|].
  split; [subst n; exact B3|].
  subst p n. unfold addr_of, loc_addr, frame_ptr, slot_start in *.
  destruct (am_mem am) as [k o]. cbn [padd prid poff] in *.
  pose proof (HAL _ _ Hr Hlv) as Hpg.
  apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hst16; [|lia]. apply Z.mod_divide in Hpg; [|unfold PGSZ; lia].
  destruct Hal16 as [a Ha]. destruct Hst16 as [b Hb]. destruct Hpg as [q Hq].
  unfold PGSZ, UNIT, IB in *.
  split; [|lia].
  rewrite Ha, Hb, Hq.
  replace (q * 4096 + (a * 16 + (16 + b * 16 * i) + 16 * fr_off fr)) with ((q * 256 + a + 1 + b * i + fr_off fr) * 16) by lia.
  apply Z_mod_mult.
Qed.

Theorem minv_block_geom : ltac2:(tb__ "0|3|
S26S17S23Q40A1M0SfS23Q8A1A1F_;G0SdF_;S38S0S0S18R7R6R5R4R3A5S25SeS0S0A2S10S0S0R3R2A4S19R7A1A3S1S7Z0M1R3A2S1S2S0SaR4Z10A2G1A3S1S7S8S4eS4cA2R4A2S1S7S8S8R4R3A2S50A2M2S34S20R8A1A1A2S3S7G2S28R9A1A2S7S8S27R9A1S4cA2R4A2A2A2A2A2A2F_;F_;Fn;Fb;Fvm;Fwok;Frd;FA;FC;").
Proof.
  intros C [s L] rd wok vm b n (HW & _ & _ & ((HL & _ & _) & _) & HV & _ & _ & HLed & _) Hin. cbn [ma_s ma_L] in *.
  rewrite (vm_ok_top L s vm HV).
  unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin.
  apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
  destruct (user_block_geom s L p n HW HL Hin) as (r & len & Hfp & Hpg & Hn & Hal & Hlo & Hhi).
  destruct HV as (_ & _ & _ & Hcov & _).
  destruct (Hcov (SP r 0) len Hfp) as (e & He & E1 & E2).
  destruct (HLed e He) as (G1 & G2 & G3).
  unfold addr_of, loc_addr in E1, E2. cbn [prid poff] in E1, E2. rewrite Z.add_0_r in E1, E2.
  repeat split; try assumption; try lia.
Qed.

Theorem minv_block_not_owned : ltac2:(tb__ "0|1|
S26S17S23Q40A1M0SfS23Q8A1A1F_;G0SdF_;S38S0S0S18R7R6R5R4R3A5S25SeS0S0A2S10S0S0R3R2A4S19R7A1A3S0S1S7R5R1A2S9R1S8R5R4A2A2A2S5S1bRbRaR2A3A1F_;Fa;F_;F_;Fn;Fb;Fvm;Fwok;Frd;FA;FC;").
Proof.
  intros C [s L] rd wok vm b n HM Hin a Ha [Ho | Hl].
  - destruct Ho as [_ Hnu]. apply Hnu.
    unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin.
    apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    exists (p, n). split; [exact Hin|]. cbn [fst snd]. unfold addr_of in Ha. exact Ha.
  -
    pose proof (minv_block_geom C _ rd wok vm b n HM Hin) as (_ & _ & _ & _ & Gimg).
    destruct HM as (_ & _ & _ & _ & _ & HS & _).

    revert Gimg Hl Ha. generalize (mc_lock C) (mc_img_lo C) (mc_img_hi C).

Abort.

Definition lock_in_image (C : mconsts) : Prop := ltac2:(tb__ "0|1|
S1S7S28VC;A1S2eVC;A1M0A2S7S8G0Z4A2S27VC;A1A2A2").

Theorem minv_block_not_owned : ltac2:(tb__ "0|1|
S26S17S23Q40A1M0SfS23Q8A1A1F_;G0SdF_;S38S0S0S58R7A1S18R8R7R6R5R4A5S25SeS0S0A2S10S0S0R4R3A4S19R8A1A3S0S1S7R6R1A2S9R1S8R6R5A2A2A2S5S1bRcRbR2A3A1F_;Fa;F_;F_;F_;Fn;Fb;Fvm;Fwok;Frd;FA;FC;").
Proof.
  intros C [s L] rd wok vm b n HC HM Hin a Ha [Ho | Hl].
  - destruct Ho as [_ Hnu]. apply Hnu.
    unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin.
    apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    exists (p, n). split; [exact Hin|]. cbn [fst snd]. unfold addr_of in Ha. exact Ha.
  - pose proof (minv_block_geom C _ rd wok vm b n HM Hin) as (_ & _ & _ & _ & Gimg).
    unfold lock_in_image, UNIT, IB in *. lia.
Qed.

Definition statics_in_image (C : mconsts) : Prop := ltac2:(tb__ "0|4|
S0S0S1S7S28VC;A1M0R2A2S7S8R2R1A2S27VC;A1M1A2A2Ln;Llo;S0S0OFn;Flo;S1R1S2dVC;A1Z38A2S1R1S30VC;A1Z4M2A2S1R1S31VC;A1Z60A2S1R1S32VC;A1Z1bA2S1R1S2fVC;A1G2A2S1R1S2cVC;A1Z20A2S1R1S2bVC;A1Z8M3A2S1R1S2aVC;A1G3A2S1R1S2eVC;A1G2A2S1R1S36VC;A1S41A2S1R1S37VC;A1G2A2S1S7S4eG0A2S7S8G1S4cA2Z7fff7f800000A2A2A2A2A2A2A2A2A2A2A2A2A2Tinside;").

Lemma statics_in_image_P : statics_in_image C_P.
Proof. unfold statics_in_image, CTX_SIZE, PGSZ, UNIT, mc_errno. cbn. lia. Qed.
Lemma statics_in_image_U : statics_in_image C_U.
Proof. unfold statics_in_image, CTX_SIZE, PGSZ, UNIT, mc_errno. cbn. lia. Qed.

Lemma statics_below_top : ltac2:(tb__ "0|0|
S26S3eS57R2A1S7S8S27R3A1S4cA2S34R2A1A2F_;FL;FC;").
Proof. intros C L H. pose proof (topL_range L). unfold statics_in_image in H. lia. Qed.

Lemma lock_in_image_P : lock_in_image C_P. Proof. unfold lock_in_image; cbn; lia. Qed.
Lemma lock_in_image_U : lock_in_image C_U. Proof. unfold lock_in_image; cbn; lia. Qed.

Corollary minv_block_misses_statics : ltac2:(tb__ "0|1|
S26S17S23Q40A1M0SfS23Q8A1A1F_;G0SdF_;S38S0S0S57R7A1S18R8R7R6R5R4A5S25SeS0S0A2S10S0S0R4R3A4S19R8A1A3S0S0S1S7S28RcA1R2A2S7S8R2R1A2S27RcA1A2A2S3S7S8R8R7A2R3A2S7S8R3R2A2R8A2A2F_;Fk;Flo;F_;F_;F_;Fn;Fb;Fvm;Fwok;Frd;FA;FC;").
Proof.
  intros C A rd wok vm b n HS HM Hin lo k Hlk.
  pose proof (minv_block_geom C A rd wok vm b n HM Hin) as (_ & _ & _ & _ & G). unfold UNIT, IB in G. lia.
Qed.

Definition init_done_preserved_stmt : Prop := ltac2:(tb__ "0|2|
S1S17S0S13SeS51S0A2A1M0S0S17S2SdS4dS1aR5A1A1S11A3S1cR6R5R4R3R2A5S2SdS4dS1aR3A1A1S11A3M1F_;F_;FA';Fres;Ftr;Fn;FA;S1S17S0G0S17S2SdS4dS1aR4A1A1S11A3S1fR5R4R3R2A4G1F_;F_;FA';Ftr;Fb;FA;S17S0S0G0S0SdS17S2SdS4dS1aR7A1A1S11A3S1eR8R7R6R5R4R3R2A7G1F_;F_;FA';Fc;Fres;Ftr;Fn;Fm;FA;A2A2").

Definition first_malloc_init_done_stmt : Prop := ltac2:(tb__ "0|0|
S26S22S0S13SeS51S0A2A1S0S17S7Z0R4A2S2SdS54R5A1S16A3S1cS1dR8R7A2R6R5R4R3A5S2SdS4dS1aR4A1A1S11A3F_;F_;F_;FA';Fres;Ftr;Fn;Fbrk0;FC;").

Section Frame.
  Variables (C : mconsts) (s : astate) (L : layout).
  Variables (rd rd' : word -> option byte) (wok wok' : word -> bool).

  Let bv  := byteview_of rd wok.
  Let bv' := byteview_of rd' wok'.
  Let rv  := byteview_of rd (fun _ => true).
  Let rv' := byteview_of rd' (fun _ => true).

  Definition static_addr (a : Z) : Prop := ltac2:(tb__ "0|a|
S3S1S7S2dVC;A1M0Va;A2S9Va;S8G0Z38A2A2A2S3S1S7S30VC;A1M1Va;A2S9Va;S8G1Z4M2A2A2A2S3S1S7S31VC;A1M3Va;A2S9Va;S8G3Z60A2A2A2S3S1S7S32VC;A1M4Va;A2S9Va;S8G4Z1bA2A2A2S3S1S7S2fVC;A1M5Va;A2S9Va;S8G5G2A2A2A2S3S1S7S2cVC;A1M6Va;A2S9Va;S8G6Z20A2A2A2S3S1S7S2bVC;A1M7Va;A2S9Va;S8G7Z8M8A2A2A2S1S7S2aVC;A1M9Va;A2S9Va;S8G9G8A2A2A2A2A2A2A2A2A2A2").

  Hypothesis AG : ltac2:(tb__ "0|1|
S0S1S7Z0R1A2S9R1ScZ2Z40A2A2A2S3S33VC;VL;Vs;R2A4S56R2A1A2S1S2SfS23Q8A1A1Vrd';S24Q40R3A2M0A1Vrd;G0A1A3S2SdVwok';G0A1Vwok;G0A1A3A2F_;F_;Fa;").

  Lemma bv_agree : ltac2:(tb__ "0|1|
S0S1S7Z0R1A2S9R1ScZ2Z40A2A2A2S3S33VC;VL;Vs;R2A4S56R2A1A2F_;S1S2SfS0A1M0Vbv';R2A1Vbv;R2A1A3S2G0Vrv';R2A1Vrv;R2A1A3A2F_;Fa;").
  Proof using AG.
    intros a Ha. unfold bv, bv', rv, rv', byteview_of.
    destruct ((0 <=? a) && (a <? 2 ^ 64))%bool eqn:E; [|split; reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (AG a ltac:(lia) (Ha ltac:(lia))) as [R W]. rewrite R, W. split; reflexivity.
  Qed.

  Lemma holds_agree : ltac2:(tb__ "0|1|
S3bS3bS0S12S0S12S59R1R3A2S2SfS0A1R6S8R5SbR2A1A2M0A1R7G0A1A3F_;Fk;S29R6R4R3R2A4S29R6R5R4R3A4F_;F_;Fv;Fw;Fa;Fm';Fm;").
  Proof using . intros m m' a w v E H k Hk. rewrite (E k Hk). exact (H k Hk). Qed.

  Hypothesis HW : WF s.
  Hypothesis HL : layout_ok L s.

  Lemma cell_bytes_owned : ltac2:(tb__ "0|1|
S39S3S25S39R1S3dVs;A1A3S25S39R1S55Vs;A1A3A2S0S1S7S47VL;S49R3A1A2M0R1A2S9R1S8G0SbS4aR3A1A1A2A2A2S44VL;Vs;R2A3F_;Fx;F_;Fc;").
  Proof using HL HW.
    intros c Hc x Hx.
    assert (FP : exists rg, In rg (footprint s) /\ range_incl (cell_range L c) (crange L rg)).
    { destruct Hc as [Hc|Hc]; [exact (image_in_footprint s L c HW HL Hc) | exact (footer_in_footprint s L c HW HL Hc)]. }
    destruct FP as (rg & Hrg & [I1 I2]). unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2.
    split.
    - exists rg. split; [exact Hrg|]. lia.
    - intros (b & Hb & Hxb).
      assert (D : ranges_disjoint (cell_range L c) (block_range L b)).
      { destruct Hc as [Hc|Hc]; [exact (image_outside_user_blocks s L c b HW HL Hc Hb) | exact (footer_outside_user_blocks s L c b HW HL Hc Hb)]. }
      unfold ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. lia.
  Qed.

  Lemma cell_holds_agree : ltac2:(tb__ "0|0|
S39S3S25S39R1S3dVs;A1A3S25S39R1S55Vs;A1A3A2S3cVL;Vbv;R2A3S3cVL;Vbv';R3A3F_;F_;Fc;").
  Proof using AG HL HW rv rv'.
    intros c Hc H.
    assert (Hw : (0 < mc_w c)%nat).
    { destruct Hc as [Hc|Hc]; [exact (image_cell_w s c Hc) | exact (footer_cells_w s c Hc)]. }
    assert (E : forall k, (k < mc_w c)%nat ->
              bv' (loc_addr L (mc_loc c) + Z.of_nat k) = bv (loc_addr L (mc_loc c) + Z.of_nat k)).
    { intros k Hk. apply (proj1 (bv_agree _ (fun _ => or_introl (or_introl (cell_bytes_owned c Hc (loc_addr L (mc_loc c) + Z.of_nat k) ltac:(lia)))))). }
    unfold cell_holds in *. cbn zeta in *.
    destruct (mc_val c); try (intros k Hk; rewrite (E k Hk); exact (H k Hk)).
    destruct H as (b & Hb & Hm). exists b. split; [|exact Hm].
    rewrite <- Hb. rewrite <- (Z.add_0_r (loc_addr L (mc_loc c))). change 0 with (Z.of_nat 0). apply E. lia.
  Qed.
End Frame.

Theorem minv_frame : ltac2:(tb__ "0|0|
S26S21R1A1FC;").
Proof.
  intros C [s L] rd wok vm rd' wok' vm' HM AG Hmaps Hna Hbrk Hsbrk Hres Hisp Hinit.
  assert (Htop : alloc_top vm' = alloc_top vm) by (unfold alloc_top; rewrite Hisp; reflexivity).
  pose proof HM as (HW & HB & HC & ((HL & HI & HO) & HF) & HV & HS & HA & HLG & HIMG & HMW & HRCH). cbn [ma_s ma_L] in *.
  assert (AG' : forall a, 0 <= a < 2 ^ 64 -> owned C L s a \/ static_addr C a ->
            rd' (Z_to_bv 64 a) = rd (Z_to_bv 64 a) /\ wok' (Z_to_bv 64 a) = wok (Z_to_bv 64 a)).
  { intros a Ha Ho. apply (AG a Ha). unfold static_addr in Ho. unfold ma_owned. cbn [ma_s ma_L]. tauto. }
  pose proof (bv_agree C s L rd rd' wok wok' AG') as BA.
  unfold MInv. cbn [ma_s ma_L].
  split; [exact HW|]. split; [exact HB|]. split; [exact HC|].
  split.
  {   split; [split; [exact HL|split]|].
    - apply Forall_forall. intros c Hc. apply (cell_holds_agree C s L rd rd' wok wok' AG' HW HL c (or_introl Hc)).
      exact (proj1 (Forall_forall _ _) HI c Hc).
    - intros x Hx. rewrite (proj1 (BA x (fun _ => or_introl (or_introl Hx)))). exact (HO x Hx).
    - apply Forall_forall. intros c Hc. apply (cell_holds_agree C s L rd rd' wok wok' AG' HW HL c (or_intror Hc)).
      exact (proj1 (Forall_forall _ _) HF c Hc). }
  split.
  {
    unfold vm_ok in *. rewrite Hmaps, Hna, Hbrk, Hsbrk, Htop. exact HV. }
  split.
  {
    destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (gd & S9 & S10)).
    assert (RV : forall a, static_addr C a -> byteview_of rd' (fun _ => true) a = byteview_of rd (fun _ => true) a).
    { intros a Ha. exact (proj2 (BA a (fun _ => or_intror Ha))). }
    unfold statics_ok, mc_need_locks, mc_page_size, mc_auxv in *.
    split; [eapply holds_agree; [|exact S1]; intros k Hk; apply RV; unfold static_addr; lia|].
    split; [eapply holds_agree; [|exact S2]; intros k Hk; apply RV; unfold static_addr; lia|].
    split; [eapply holds_agree; [|exact S3]; intros k Hk; apply RV; unfold static_addr; lia|].
    split. { eapply holds_agree; [|exact S4]. intros k Hk. refine (proj1 (BA _ _)). intros _. left. right. lia. }
    split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S5 k Hk). }
    split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S6 k Hk). }
    split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S7 k Hk). }
    split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S8 k Hk). }
    exists gd. split.
    - eapply holds_agree; [|exact S9]. intros k Hk; apply RV; unfold static_addr; lia.
    - eapply holds_agree; [|exact S10]. intros k Hk; apply RV; unfold static_addr; lia. }
  split.
  {   intros Hf. rewrite Hinit in Hf. discriminate. }
  split.
  {   unfold ledger_ok in *. rewrite Hmaps, Htop. exact HLG. }
  split.
  {   unfold img_reserved in *. rewrite Hres. exact HIMG. }
  split.
  {   unfold maps_wf in *. rewrite Hmaps. exact HMW. }
  exact HRCH.
Qed.
