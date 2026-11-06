(* The bridge between lib/Reusable/FCiface.v (fuzz_preset's AR-parametric frame-area interface fs_iface, over a
   relation ARx with a poisoned-head argument) and lib/A/FSupoison.v (fuzz_state's ARU: cgif's AR of
   unpoison U mem, plus upoison_ok and upoisoned): ARU with the head argument ignored is an fs_iface instance,
   so fuzz_state's runtime takes preset's frame-area walks. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s YG0q YG0t YF0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSuwalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Module FSPU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (segs : list Segment) (B : asyms).

(* ------------------------------------------------------------------------------------------------ *)
(* Where a byte of U can be, and where it cannot.                                                     *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma ceil_hi : 0x7fff7f800000 <= ASAN_CEIL <= 0x7fffff800000.
Proof. exact (proj1 (@ASAN_CEIL_range rc)). Qed.

(* An address of the application memory is off the shadow range, so no user-poisoned byte sits there. *)
Lemma in_app_off : forall lo len a, in_app lo len -> lo <= a < lo + len -> 0 <= a < 2 ^ 64 /\ off_shadow a.
Proof.
intros lo len a [H0 H] Ha. pose proof ceil_hi as [C1 C2].
change (2 ^ 64) with 18446744073709551616.
unfold off_shadow, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma view_off : forall ly S U W mem md (m : word -> option byte) a, FSP.ARU segs B ly S U W mem md ->
0 <= a < 2 ^ 64 -> off_shadow a -> aview segs (w_H W) (FSP.unpoison U m) a = aview segs (w_H W) m a.
Proof. intros ly S U W mem md m a H Ha Ho. exact (aview_unp_off segs B ly S U W mem md (w_H W) m a H Ha Ho). Qed.

Lemma view_app : forall ly S U W mem md (m : word -> option byte) lo len a, FSP.ARU segs B ly S U W mem md ->
in_app lo len -> lo <= a < lo + len -> aview segs (w_H W) (FSP.unpoison U m) a = aview segs (w_H W) m a.
Proof.
intros ly S U W mem md m lo len a H IA Ha. destruct (in_app_off lo len a IA Ha) as [R O].
exact (view_off ly S U W mem md m a H R O).
Qed.

(* The side stack lives in the application memory. *)
Lemma F_in_app : forall ly S U W mem md, FSP.ARU segs B ly S U W mem md -> in_app (ly_F ly) kFakeStackSize.
Proof.
intros ly S U W mem md H.
exact (proj1 (Forall_forall _ _) (lo_app _ (am_layout _ _ _ _ (FSP.ARU_ARm segs B ly S U W mem md H)))
(ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn [In]; tauto)).
Qed.

Lemma view_F : forall ly S U W mem md (m : word -> option byte) a, FSP.ARU segs B ly S U W mem md ->
ly_F ly <= a < ly_F ly + kFakeStackSize -> aview segs (w_H W) (FSP.unpoison U m) a = aview segs (w_H W) m a.
Proof.
intros ly S U W mem md m a H Ha.
exact (view_app ly S U W mem md m (ly_F ly) kFakeStackSize a H (F_in_app ly S U W mem md H) Ha).
Qed.

(* Every byte of U is owned by the runtime, so an unowned byte is not one. *)
Lemma ush_unowned : forall ly S U W mem md a, FSP.ARU segs B ly S U W mem md -> ~ aowned B ly S a ->
FSP.in_ush U a = false.
Proof.
intros ly S U W mem md a H NO. destruct (FSP.in_ush U a) eqn:E; [|reflexivity].
exfalso. exact (NO (proj1 (FSP.ush_facts segs B ly S U W mem md a H E))).
Qed.

Lemma view_ush : forall U (W : world segs) (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> FSP.in_ush U a = false ->
aview segs (w_H W) (FSP.unpoison U m) a = aview segs (w_H W) m a.
Proof.
intros U W m a Ha E. apply FSP.aview_unpoison_out. rewrite (FSP.wz a Ha). exact E.
Qed.

Lemma apresent_move : forall ly S U W mem md a, FSP.ARU segs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
FSP.in_ush U a = false -> apresent (w_H W) (FSP.unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha E [Hh [b Hb]]. split; [exact Hh|]. exists b.
rewrite <- (FSP.unpoison_out U mem (Z_to_bv 64 a)); [exact Hb|]. rewrite (FSP.wz a Ha). exact E.
Qed.

(* A cell read at addresses where the two memories agree holds on both. *)
Lemma cell_move : forall ly (rd rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros ly rd rd' c AG HC. unfold cell_holds in HC |- *. cbv zeta in HC |- *. destruct (c_val c).
- intros k Hk. rewrite (AG (Z.of_nat k) ltac:(lia)). exact (HC k Hk).
- destruct HC as (b & H1 & H2). exists b. split; [|exact H2].
  rewrite <- (Z.add_0_r (aeval B ly (c_at c))), (AG 0 ltac:(lia)), Z.add_0_r. exact H1.
Qed.

Lemma core_in_owned : forall ly e, In e (core_extents ly) -> In e (owned_extents ly).
Proof. intros ly e H. unfold core_extents, owned_extents in H |- *. cbn [In] in H |- *. tauto. Qed.

(* The shadow bytes of a statically owned range are inside the image's shadow, and the image holds no live
   block (AR_client_img_law), so they are not user-poisoned. *)
Lemma static_shadow_ush : forall ly S U W mem md a r, AR_laws segs B -> FSP.ARU segs B ly S U W mem md ->
In r (as_owned_static B) -> shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 ->
FSP.in_ush U a = false /\ 0 <= a < 2 ^ 64.
Proof.
intros ly S U W mem md a r LAWS HU Hr Hra.
pose proof (FSP.ARU_ARm segs B ly S U W mem md HU) as M.
pose proof (FSP.ARU_AR segs B ly S U W mem md HU) as HAR.
pose proof (am_layout _ _ _ _ M) as LO.
pose proof (proj1 (Forall_forall _ _) (aso_static _ (am_syms _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)) as P1.
pose proof (Z.div_le_upper_bound (fst r) 8 (fst r) ltac:(lia) ltac:(lia)) as P2.
pose proof (Z.div_le_upper_bound (snd r + 7) 8 (snd r + 7) ltac:(lia) ltac:(lia)) as P3.
assert (RG : 0 <= a < 2 ^ 64).
{ change (2 ^ 64) with 18446744073709551616. unfold shadow_addr, SHADOW_OFF, kImgEnd in *. lia. }
split; [|exact RG].
destruct (FSP.in_ush U a) eqn:EU; [|reflexivity]. exfalso.
destruct (FSP.ush_granule B ly S U a (FSP.ARU_ok segs B ly S U W mem md HU) EU)
as (g & p & n & Hb & G8 & Gs & Gp & Gn).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [SI1 SI2].
pose proof (lo_img _ LO) as (I1 & I2 & I3 & I4).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
assert (HBG : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= g < p0 + req_size n0)
by (exists p, n; split; [exact Hb | lia]).
pose proof (proj1 (al_client_img _ _ LAWS ly S W (FSP.unpoison U mem) md g HAR (or_introl HBG))) as NI.
apply NI. unfold in_zr.
apply Z.mod_divide in G8 as [q Hq]; [|lia].
unfold shadow_addr in Gs, Hra. rewrite Hq, Z.div_mul in Gs by lia.
pose proof (Z.mul_div_le (fst r) 8 ltac:(lia)) as D1.
pose proof (Z.mul_div_le (snd r + 7) 8 ltac:(lia)) as D2.
pose proof (Z.div_le_mono 65536 (fst r) 8 ltac:(lia) ltac:(unfold kImgLo in I1; lia)) as D3.
change (65536 / 8) with 8192 in D3.
unfold kImgLo in I1. rewrite Hq. lia.
Qed.

(* A byte of a constant cell is never user-poisoned: it is an image byte, a core-structure byte, or a
   shadow byte of a global. *)
Lemma owned_core_view : forall ly S U W mem md a, AR_laws segs B -> FSP.ARU segs B ly S U W mem md ->
owned_core B ly a -> aview segs (w_H W) (FSP.unpoison U mem) a = aview segs (w_H W) mem a.
Proof.
intros ly S U W mem md a LAWS HU HO.
pose proof (FSP.ARU_ARm segs B ly S U W mem md HU) as M.
pose proof (am_layout _ _ _ _ M) as LO.
destruct HO as [E1 | [E2 | E3]].
- pose proof (owned_static_bound B a (am_syms _ _ _ _ M) E1) as [L1 L2].
  apply (view_off ly S U W mem md mem a HU);
  [change (2 ^ 64) with 18446744073709551616; unfold kImgEnd in L2; lia
  |unfold off_shadow, SHADOW_OFF, kImgEnd in *; lia].
- apply Exists_exists in E2 as (e & He & Ha). unfold in_zr in Ha.
  exact (view_app ly S U W mem md mem (fst e) (snd e) a HU
    (proj1 (Forall_forall _ _) (lo_app _ LO) e (core_in_owned ly e He)) Ha).
- apply Exists_exists in E3 as (r & Hr & Hra). unfold in_zr in Hra. cbn [fst snd] in Hra.
  destruct (static_shadow_ush ly S U W mem md a r LAWS HU Hr Hra) as [EU RG].
  exact (view_ush U W mem a RG EU).
Qed.

(* The side-stack cells all sit in the first 104 bytes of the side stack. *)
Lemma fs_cells_bound : forall S c, In c (fs_cells S) ->
exists off, c_at c = AF off /\ 0 <= off /\ off + Z.max 1 (Z.of_nat (c_w c)) <= 104.
Proof.
intros S c H. unfold fs_cells in H. destruct H as [<-|[<-|H]].
- exists 88. cbn [c_at c_w z8 c8]. split; [reflexivity | lia].
- exists 96. cbn [c_at c_w z1 c1]. split; [reflexivity | lia].
- apply in_map_iff in H as ([i v] & <- & Hin). cbn [c_at c_w z8 c8 fst snd].
  exists (8 * Z.of_nat i). split; [reflexivity|].
  apply in_combine_l, in_seq in Hin. lia.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The instance.                                                                                      *)
(* ------------------------------------------------------------------------------------------------ *)

Definition ARU_nohp (U : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
(mem : word -> option byte) (md : Model) : Prop := FSupoison.ARU segs B ly S U W mem md.

Lemma fs_iface_ARU : AR_laws segs B -> forall U, FCiface.fs_iface segs B (ARU_nohp U).
Proof.
intros LAWS U. constructor; unfold ARU_nohp.
- (* fi_hints *)
  intros ly S hp W mem md HU.
  exact (wfs_hints _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ (FSP.ARU_ARm segs B ly S U W mem md HU)))).
- (* fi_layout *)
  intros ly S hp W mem md HU. exact (am_layout _ _ _ _ (FSP.ARU_ARm segs B ly S U W mem md HU)).
- (* fi_img *)
  intros ly S hp W mem md sg HU Hsg.
  exact (al_img _ _ _ _ (proj1 (proj2 (FSP.ARU_AR segs B ly S U W mem md HU))) sg Hsg).
- (* fi_tsd *)
  intros ly S hp W mem md HU. exact (am_tsd _ _ _ _ (FSP.ARU_ARm segs B ly S U W mem md HU)).
- (* fi_const *)
  intros ly S hp W mem md HU.
  pose proof (FSP.ARU_ARm segs B ly S U W mem md HU) as M.
  apply Forall_forall. intros c Hc.
  apply (cell_move ly (aview segs (w_H W) (FSP.unpoison U mem)) (aview segs (w_H W) mem) c).
  + intros k Hk. symmetry. apply (owned_core_view ly S U W mem md _ LAWS HU).
    exact (proj1 (Forall_forall _ _) (am_const_owned _ _ _ _ M) c Hc k Hk).
  + exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) c Hc).
- (* fi_fs_cells *)
  intros ly S hp W mem md HU.
  pose proof (FSP.ARU_ARm segs B ly S U W mem md HU) as M.
  apply Forall_forall. intros c Hc.
  destruct (fs_cells_bound S c Hc) as (off & Eat & O1 & O2).
  apply (cell_move ly (aview segs (w_H W) (FSP.unpoison U mem)) (aview segs (w_H W) mem) c).
  + intros k Hk. rewrite Eat. cbn [aeval]. symmetry.
    apply (view_F ly S U W mem md mem). exact HU. unfold kFakeStackSize. lia.
  + apply (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M)).
    unfold acells. rewrite !in_app_iff. right; right; right; right; right; left. exact Hc.
- (* fi_flags *)
  intros ly S hp W mem md HU cid pos Hc Hpos.
  pose proof (FSP.ARU_ARm segs B ly S U W mem md HU) as M.
  pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
  rewrite <- (view_F ly S U W mem md mem (flag_addr ly cid pos) HU
    ltac:(unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia)).
  exact (am_flags _ _ _ _ M cid pos Hc Hpos).
- (* fi_area_F *)
  intros ly S hp W mem md HU i Hi.
  apply (aview_some_unp segs B ly S U W mem md _ HU).
  refine (proj1 (Forall_forall _ _) (am_areas _ _ _ _ (FSP.ARU_ARm segs B ly S U W mem md HU))
    (AF 0, kFakeStackSize) _ i Hi).
  unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- (* fi_area_Fsh *)
  intros ly S hp W mem md HU i Hi.
  apply (aview_some_unp segs B ly S U W mem md _ HU).
  refine (proj1 (Forall_forall _ _) (am_areas _ _ _ _ (FSP.ARU_ARm segs B ly S U W mem md HU))
    (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) _ i Hi).
  unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- (* fi_own_free_frame *)
  intros ly S hp W mem md cid pos a HU.
  exact (own_free_frame B ly S _ cid pos a (FSP.ARU_ARm segs B ly S U W mem md HU)).
- (* fi_own_free_frame_shadow *)
  intros ly S hp W mem md cid pos a HU.
  exact (own_free_frame_shadow B ly S _ cid pos a (FSP.ARU_ARm segs B ly S U W mem md HU)).
- (* fi_own_F_low *)
  intros ly S hp W mem md a HU.
  exact (own_F_low B ly S _ a (FSP.ARU_ARm segs B ly S U W mem md HU)).
- (* fi_malloc_law *)
  intros ly S hp W mem md mem' md' cid pos hint' HU Hc HP S' HW HF1 AGR VIS Ev1 Ev2 Ev3 HK.
  pose proof HU as (HAR & OK & PO).
  pose proof (FSP.ARU_ARm segs B ly S U W mem md HU) as M.
  pose proof (F_in_app ly S U W mem md HU) as FA.
  destruct (fs_probe_some _ _ _ _ _ _ (fs_frames_pos cid Hc) HP) as (h & Hh1 & Eh & Epos & NM).
  assert (Hpos : 0 <= pos < fs_frames cid)
    by (rewrite Epos; apply Z.mod_pos_bound; exact (fs_frames_pos cid Hc)).
  assert (NIN : ~ In (cid, pos) (frames S)) by (unfold frames; apply mem_pos_false; exact NM).
  pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
  pose proof (frame_off_bounds cid pos Hc Hpos) as (FO1 & FO2 & FO3 & FO4 & FO5 & FO6).
  assert (F8 : frame_addr ly cid pos mod 8 = 0).
  { unfold frame_addr. pose proof (lo_F_al _ (am_layout _ _ _ _ M)) as FAL. unfold page_aligned in FAL.
    apply Z.mod_divide in FAL as [u Hu]; [|lia]. pose proof FO3 as FO3'. apply Z.mod_divide in FO3' as [v Hv]; [|lia].
    rewrite Hu, Hv. replace (u * 4096 + v * 64) with ((u * 512 + v * 8) * 8) by lia. apply Z.mod_mul. lia. }
  assert (B8 : fs_frame_bytes cid mod 8 = 0).
  { pose proof FO5 as FO5'. apply Z.mod_divide in FO5' as [v Hv]; [|lia].
    rewrite Hv. replace (v * 64) with ((v * 8) * 8) by lia. apply Z.mod_mul. lia. }
  unfold FSP.ARU. split; [|split].
  + apply (astack_malloc_law_ok segs B ly S W (FSP.unpoison U mem) md (FSP.unpoison U mem') md' cid pos hint'
      HAR Hc HP).
    * intros k Hk.
      rewrite (view_F ly S U W mem md mem' (ly_F ly + 8 * cid + Z.of_nat k) HU
        ltac:(unfold kFakeStackSize; lia)).
      exact (HW k Hk).
    * rewrite (view_F ly S U W mem md mem' (flag_addr ly cid pos) HU
        ltac:(unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia)). exact HF1.
    * intros a Ha Hown N1 N2 N3 N4.
      destruct (FSP.in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
      -- apply FSP.aview_unpoison_in. exact Ei.
      -- rewrite (FSP.aview_unpoison_out segs (w_H W) U mem' a Ei),
           (FSP.aview_unpoison_out segs (w_H W) U mem a Ei).
         exact (AGR a Ha Hown N1 N2 N3 N4).
    * intros a Hv. destruct (FSP.in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
      -- rewrite (FSP.aview_unpoison_in segs (w_H W) U mem' mem a Ei). exact Hv.
      -- rewrite (FSP.aview_unpoison_out segs (w_H W) U mem' a Ei).
         rewrite (FSP.aview_unpoison_out segs (w_H W) U mem a Ei) in Hv. exact (VIS a Hv).
    * exact Ev1.
    * exact Ev2.
    * exact Ev3.
    * intros a Hb Hh. unfold FSP.unpoison.
      destruct (FSP.in_ush U (bv_unsigned (w64 a))); [reflexivity | exact (HK a Hb Hh)].
  + unfold FSP.upoison_ok in OK |- *. exact OK.
  + intros s Hs.
    pose proof (FSP.ush_facts segs B ly S U W mem md s HU Hs) as (Hown & SL1 & SL2).
    pose proof (FSP.ush_range segs B ly S U W mem md s HU Hs) as SR.
    assert (N1 : ~ (ly_F ly + 8 * cid <= s < ly_F ly + 8 * cid + 8)).
    { intros Hbad. destruct (in_app_off (ly_F ly) kFakeStackSize s FA ltac:(unfold kFakeStackSize; lia)) as [_ O].
      unfold off_shadow, SHADOW_OFF, kHighMemBeg in *. lia. }
    assert (N2 : s <> flag_addr ly cid pos).
    { intros Hbad. destruct (in_app_off (ly_F ly) kFakeStackSize s FA
        ltac:(unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia)) as [_ O].
      unfold off_shadow, SHADOW_OFF, kHighMemBeg in *. lia. }
    assert (N3 : ~ in_zr s (frame_addr ly cid pos, fs_frame_bytes cid)).
    { unfold in_zr. cbn [fst snd]. intros Hbad.
      destruct (in_app_off (ly_F ly) kFakeStackSize s FA
        ltac:(unfold frame_addr, kFakeFramesOff, kFakeStackSize in *; lia)) as [_ O].
      unfold off_shadow, SHADOW_OFF, kHighMemBeg in *. lia. }
    assert (N4 : ~ in_zr s (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)).
    { unfold in_zr. cbn [fst snd]. intros Hbad.
      rewrite (ush_free_frame segs B LAWS ly S U W mem md cid pos s HU Hc Hpos NIN F8 B8 Hbad) in Hs.
      discriminate Hs. }
    rewrite (AGR s SR Hown N1 N2 N3 N4). exact (PO s Hs).
- (* fi_stack *)
  intros ly S hp W mem md a HU Ha. exact (FSP.ARU_stack segs B LAWS ly S U W mem md a HU Ha).
- (* fi_frame *)
  intros ly S hp W mem md mem' md'. exact (FSP.ARU_frame segs B LAWS ly S U W mem md mem' md').
- (* fi_frames *)
  intros ly S hp W mem md cid pos HU Hin.
  destruct (al_frames _ _ LAWS ly S W (FSP.unpoison U mem) md cid pos
    (FSP.ARU_AR segs B ly S U W mem md HU) Hin) as (G1 & G2 & G3 & G4).
  split; [exact G1|]. split; [exact G2|]. split.
  + intros a Ha. destruct (G3 a Ha) as [P1 P2]. split; [|exact P2].
    destruct (in_app_off (frame_addr ly cid pos) (fs_frame_bytes cid) a G2 Ha) as [R O].
    exact (apresent_unp_off segs B ly S U W mem md (w_H W) a HU R O P1).
  + intros i Hi. destruct (G4 i Hi) as [P1 P2]. split; [|exact P2].
    apply (apresent_move ly S U W mem md _ HU);
      [|exact (ush_unowned ly S U W mem md _ HU P2) | exact P1].
    assert (FB0 : 0 <= fs_frame_bytes cid).
    { destruct (Z_le_gt_dec 0 (fs_frame_bytes cid)) as [Y|Hneg]; [exact Y|]. exfalso.
      assert (fs_frame_bytes cid / 8 <= 0) by (apply Z.div_le_upper_bound; lia). lia. }
    destruct G2 as [GA0 GA]. pose proof ceil_hi as [C1 C2].
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Q1.
    pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (frame_addr ly cid pos) ltac:(lia) ltac:(lia)) as Q2.
    pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (fs_frame_bytes cid) ltac:(lia) ltac:(lia)) as Q3.
    change (2 ^ 64) with 18446744073709551616.
    unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The pre of astack_malloc_realizes_x at ARU_nohp U is FSupoison.ecall_preU, conjunct for conjunct: ARU in
   place of AR, and the stack window present on mem instead of on unpoison U mem (the stack is above the
   shadow, so the two readings agree there). The post is FSupoisonU.astack_malloc_realizesU's post verbatim. *)
Lemma astack_malloc_realizesU_of_x : forall cid,
(forall U, FCiface.astack_malloc_realizes_x segs B (ARU_nohp U) cid) ->
FSPU.astack_malloc_realizesU segs B cid.
Proof.
intros cid H ly S U W regs mem md pos S' HPRE Hcnt Hpath.
pose proof HPRE as ((HAR & Hra & Hal & Hlo & Hhi & HpresE & Hgp & Htp) & HOK & HPO).
assert (HU : FSP.ARU segs B ly S U W mem md) by exact (conj HAR (conj HOK HPO)).
pose proof (proj1 HAR) as M.
pose proof (lo_top _ (am_layout _ _ _ _ M)) as (_ & _ & _ & T4 & _ & _ & T7).
unfold kHighMemBeg, kHighMemEnd in T4, T7.
apply (H U ly S [] W regs mem md pos S'); [|exact Hcnt | exact Hpath].
split; [exact HU|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [|split; [exact Hgp | exact Htp]].
intros a Ha. apply (apresent_unp_off segs B ly S U W mem md (w_H W) a HU);
[change (2 ^ 64) with 18446744073709551616; unfold ESTACK in *; lia
|unfold off_shadow, kHighMemBeg, ESTACK in *; lia
|exact (HpresE a Ha)].
Qed.
End a.
