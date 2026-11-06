(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem BatLeaf BatPoison ArtRuns BatCls BatDepot ArtBridge BatInv BatLift BatFsInv BatFsInvLaws.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac rok_open ROK :=
  destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
                   & Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
                   & Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb & Khi).
Ltac geo_open GEO :=
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).

(* [comment removed for export] *)
Lemma art_lazy_zone_bounds : forall FSG rn (G : art_gs FSG) a, art_run_ok rn -> art_lazy_zone FSG rn G a ->
  0x694000 <= a < rn_HI rn /\ ~ (ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES).
Proof.
  intros FSG rn G a ROK Z. rok_open ROK. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
  destruct Z as [Z|[Z|[[Z|Z] _]]].
  - clear - Z G1 Fap. unfold FS_BYTES in *. lia.
  - clear - Z Iblk Dblk Afb. unfold apart, FS_BYTES in *. lia.
  - clear - Z G4 Kspb Kend Afkb. unfold apart, FS_BYTES in *. lia.
  - clear - Z Plo Phi Afp. unfold apart, FS_BYTES in *. lia.
Qed.

(* [comment removed for export] *)
Lemma art_img_vis : forall FSG rn (G : art_gs FSG) A lazy a n, art_run_ok rn -> art_lazy_ok FSG rn G A lazy -> 0x10000 <= a -> a + n <= 0x694000 -> art_vis (mkH lazy A) a n.
Proof.
  intros FSG rn G A lazy a n ROK (LZ & _) Ha Hn x Hx. destruct (mkH lazy A x) eqn:E; [|reflexivity]. exfalso.
  unfold mkH in E. apply andb_prop in E as [E _]. pose proof (art_lazy_zone_bounds FSG rn G (U x) ROK (LZ x E)). lia.
Qed.

Section Laws.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x694000.

#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="HLhi"] Theorem art_law_lazy : rt_lazy L (rn_ar rn) HI.
Proof.
  intros LB FF LK cr A M model (G & REP & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in *.
  split; [exact (proj1 EG)|]. intros w Hw. cbv zeta. pose proof REP as (ROK & _). destruct LZ as (L1 & _).
  destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2). rewrite HLhi.
  split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2].
  intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw.
Qed.

(* [comment removed for export] *)
#[using="HLlo HLhi"] Theorem art_law_wf : HAJ.rt_wfR L (rn_ar rn) HI.
Proof.
  intros LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG).
  destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
  destruct (art_fsinv_wf_proved rn (g_fs art_fsg G) FF LK M FS) as (WF1 & WF2 & WF3 & WF4 & _ & WF6).
  destruct CRED as (CR1 & CR2 & _).
  split. { intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13).
           split. { unfold ablock_range. rewrite HLlo, HLhi. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|exact B6]. }
           split; [exact B7|]. split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|exact B12]. }
  split. { intros f Hf. destruct (WF1 f Hf) as (F1 & F2 & F3 & F4 & F5 & F6). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
           split; [clear - F4; cbn [In] in *; tauto|]. split; [exact F5|exact F6]. }
  split; [exact WF2|]. split; [exact WF3|]. split; [rewrite HLlo, HLhi; exact WF4|]. split; [exact CSA2|].
  split. { intros x (X1 & X2). apply CSA1. split; [exact X1|]. eapply Z.le_trans; [exact X2|]. unfold HeapIfaceA.S. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  split; [split; [exact CS1|exact CS2]|]. split; [split; [exact CS3|split; [exact CS5|split; [exact CS6|exact CS16]]]|]. split; [exact CS4|]. split; [exact CND|].
  split; [exact (art_fsinv_nodup_stdpp rn (g_fs art_fsg G) FF LK M FS)|]. split; [exact CR1|]. split; [exact CR2|exact WF6].
Qed.

(* [comment removed for export] *)
Definition art_cells_d4 : list (Z * Z * Z) :=
  [ (0x13d7b8, 8, HeapIfaceA.SB); (0x13d7c0, 4, 1); (0x136fe8, 8, 0x127758); (0x136f78, 8, 0x10e1f4);
    (0x134fd8, 8, 0x13d7b8);
    (0x134fe0, 8, 0x13e4a8); (0x13e4a8, 8, 0); (0x134fe8, 8, 0x13e4b0); (0x13e4b0, 8, 0);
    (0x134ff0, 8, 0x13e4a0); (0x13e4a0, 8, 0x7fffffffffff);
    (0x135b40, 8, 0x13e499); (0x13e499, 1, 1);
    (0x136fe0, 8, 0x127354);
    (0x13e498, 1, 1);
    (0x136ed8, 8, 0x128338);
    (0x671878, 8, 0x6718a0); (0x6718a8, 8, 0x672080);
    (0x13d020, 1, 1); (0x13d024, 4, 0);
    (0x671828, 8, 0x692d38);
    (0x134fc8, 8, 0x1cf2e8); (0x1cf371, 1, 1);
    (0x135028, 8, 0x1cd258); (0x1cd258, 4, 0);
    (0x135de0, 8, 8) ].
Definition art_cells_drv : list (Z * Z * Z) :=
  [ (0x1cf33c, 1, 1); (0x136e30, 8, 0x12dd58); (0x136e38, 8, 0x11e754); (0x136e60, 8, 0x124e50); (0x136e68, 8, 0x11eb6c);
    (0x136de8, 8, 0x136de8); (0x13a100, 8, 1); (0x13a150, 1, 0); (0x13afd0, 4, 1); (0x13b070, 8, 0); (0x13d01c, 1, 1);
    (0x1cf360, 8, 18446744073709551615); (0x1cf660, 1, 0); (0x135018, 8, 1);
    (0x136f90, 8, 0x127e78); (0x136e20, 8, 0x127258); (0x1cf3e3, 1, 1); (0x13afd4, 1, 0); (0x136f88, 8, 0x1160ec); (0x671890, 4, 0); (0x136e10, 8, 0x127324); (0x1cf3e6, 1, 1); (0x1cf3e7, 1, 1) ].
Definition art_statics_cells : asan_statics_cells := ASC 0x12e000 0x136000 (art_cells_d4 ++ art_cells_drv).

(* [comment removed for export] *)
Hypothesis Htp : rn_tp rn = 0x671880.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x692d38.
Hypothesis Hloff : rn_loff rn = 0x10.      (* [comment removed for export] *)

#[using="HLsegs Htp Hkey0 Htsd Hloff"] Theorem art_law_statics : rt_statics L art_statics_cells HI.
Proof.
  intros LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG). rewrite HLsegs.
  pose proof REP as (ROK & ST & TH & _). unfold art_rt_thread in TH. rewrite Htp, Hloff in TH. decompose [and] TH. clear TH.      (* [comment removed for export] *)
  assert (VIS : forall a n, 0x10000 <= a -> a + n <= 0x694000 -> art_vis (mkH (snd V) A) a n) by (intros a n; exact (art_img_vis art_fsg rn G A (snd V) a n ROK LZ)).
  assert (UP : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x694000 -> cellA (mrestrict (mkH (snd V) A) M) a n v -> cellA M a n v).
  { intros a n v Ha Hn C. apply (art_cell_vis (mkH (snd V) A) M a n v ltac:(lia) ltac:(lia) (VIS a _ Ha Hn)). exact C. }
  destruct ST as (PC & LY & T & RO & RZ & DR & TG & CS).
  unfold art_layout in LY. unfold art_tsd in T. rewrite Htp, Hkey0, Htsd in T. destruct TG as (GN & TG1 & TG2).
  decompose [and] LY. decompose [and] T. decompose [and] CS. clear LY T CS.
  split.
  - cbn [asc_got_lo asc_got_hi art_statics_cells]. intros a Ha. specialize (GN a Ha). unfold mrestrict in GN.
    rewrite (VIS a 1 ltac:(lia) ltac:(lia) (Z_to_bv 64 a) ltac:(rewrite art_u_lit by lia; lia)) in GN. exact GN.
  - cbn [asc_cells art_statics_cells art_cells_d4 art_cells_drv app].
    repeat (apply Forall_cons; [cbn [fst snd]; apply UP; [lia|cbn; lia|]; first [assumption | (unfold HeapIfaceA.SB; assumption)]|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_lb_remove_in : forall u (LB : list (Z * Z)) b, In b (lb_remove u LB) -> In b LB.
Proof. induction LB as [|x r IH]; intros b Hb; cbn in Hb; [exact Hb|]. destruct (Z.eqb (fst x) u); [right; exact Hb|]. destruct Hb as [<-|Hb]; [left; reflexivity|right; exact (IH b Hb)]. Qed.
#[using="Type"] Lemma art_lb_remove_keep : forall u (LB : list (Z * Z)) b, In b LB -> fst b <> u -> In b (lb_remove u LB).
Proof.
  induction LB as [|x r IH]; intros b Hb Hne; cbn in *; [exact Hb|]. destruct (Z.eqb_spec (fst x) u) as [E|NE].
  - destruct Hb as [<-|Hb]; [exfalso; exact (Hne E)|exact Hb].
  - destruct Hb as [<-|Hb]; [left; reflexivity|right; exact (IH b Hb Hne)].
Qed.
#[using="Type"] Lemma art_lb_remove_gone : forall u (LB : list (Z * Z)) b, List.NoDup (map fst LB) -> In b (lb_remove u LB) -> fst b <> u.
Proof.
  induction LB as [|x r IH]; intros b ND Hb; cbn in *; [destruct Hb|]. inversion ND as [|y l NI ND']; subst.
  destruct (Z.eqb_spec (fst x) u) as [E|NE].
  - intros Eb. apply NI. rewrite E, <- Eb. apply in_map. exact Hb.
  - destruct Hb as [<-|Hb]; [exact NE|exact (IH b ND' Hb)].
Qed.

#[using="Type"] Lemma art_perm_length : forall (LB LB' : list (Z * Z)), List.NoDup (map fst LB) -> List.NoDup (map fst LB') -> (forall b, In b LB <-> In b LB') -> length LB' = length LB.
Proof.
  intros LB LB' N1 N2 EQ. apply Nat.le_antisymm; apply List.NoDup_incl_length.
  - exact (List.NoDup_map_inv fst LB' N2).
  - intros b Hb. apply EQ. exact Hb.
  - exact (List.NoDup_map_inv fst LB N1).
  - intros b Hb. apply EQ. exact Hb.
Qed.

#[using="Type"] Lemma art_alloc_rep_perm : forall G LB LB' (M : word -> option byte), (forall b, In b LB <-> In b LB') -> art_alloc_rep art_fsg rn G LB M -> art_alloc_rep art_fsg rn G LB' M.
Proof.
  intros G LB LB' M EQ (ROK & ST & TH & PR & CH & SEC & QU & DEP & IA & BL & GH).
  split; [exact ROK|]. split; [exact ST|]. split; [exact TH|]. split; [exact PR|].
  split. { intros c Hc. specialize (CH c Hc). cbv zeta in *. destruct CH as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
           intros w Hw. specialize (C4 w Hw). destruct (g_st art_fsg G c w); try exact C4. destruct C4 as (I1 & REST). split; [apply EQ; exact I1|exact REST]. }
  split. { destruct SEC as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & SALL & REST). repeat (split; [assumption|]). split; [|exact REST].
           intros i s Hi. destruct (SALL i s Hi) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). repeat (split; [assumption|]). split; [|exact P10].
           destruct (sc_quar s); [exact P9|]. destruct P9 as (Q1 & Q2). split; [apply EQ; exact Q1|exact Q2]. }
  split; [exact QU|]. split; [exact DEP|]. split; [exact IA|]. split; [|exact GH].
  intros b Hb. apply BL. apply EQ. exact Hb.
Qed.

#[using="Type"] Theorem art_law_perm : rt_perm HI.
Proof.
  intros LB LB' FF FF' LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) EQB ND' EQF NDF'.
  destruct CLI as (CB & CND & CREST).
  apply NoDup_ListNoDup in ND'. apply NoDup_ListNoDup in NDF'. pose proof CND as CNDl. apply NoDup_ListNoDup in CNDl.
  assert (LEN : length LB' = length LB) by (apply art_perm_length; assumption).
  pose proof (fsinv_nodup rn (g_fs art_fsg G) FF LK M FS) as NDFL.
  assert (EQFL : forall f, In f (FF' ++ LK) <-> In f (FF ++ LK)).
  { intros f. rewrite !in_app_iff. rewrite (EQF f). tauto. }
  exists G. split; [exact (art_alloc_rep_perm G LB LB' _ EQB REP)|].
  split. { apply (art_fsinv_relist rn (g_fs art_fsg G) FF LK FF' LK M FS EQFL).
           pose proof NDFL as NDFL0. rewrite map_app in NDFL |- *. apply List.NoDup_app; [exact NDF'|exact (List.NoDup_app_remove_l _ _ NDFL)|].
           intros a Ha HaL. apply in_map_iff in Ha. destruct Ha as (f & Ef & Hf). apply EQF in Hf.
           apply in_map_iff in HaL. destruct HaL as (f2 & Ef2 & Hf2).
           apply (nodup_app_disj _ _ ff_addr FF LK f f2 NDFL0 Hf Hf2). rewrite Ef, Ef2. reflexivity. }
  split; [exact BV|].
  split. { unfold art_credit_ok, art_nret in *. rewrite LEN. exact CRED. }
  split. { split; [|split; [apply NoDup_ListNoDup; exact ND'|exact CREST]].
           intros b Hb. apply EQB in Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
           repeat (split; [assumption|]). split; [|split; [|exact B12]].
           - intros b' Hb'. apply B10. apply art_lb_remove_keep; [apply EQB; exact (art_lb_remove_in _ _ _ Hb')|exact (art_lb_remove_gone _ _ _ ND' Hb')].
           - intros f Hf. apply B11. apply EQFL. exact Hf. }
  split; [exact KN|]. split; [exact LZ|].
  destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. apply (EB b x); [apply EQB; exact Hb|exact Hx].
Qed.

#[using="Type"] Theorem art_law_small_high : rt_small_high HI.
Proof.
  intros LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) b Hb Hs.
  destruct CLI as (CB & _). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B13). unfold BIGSHADOW_HI. exact (B13 Hs).
Qed.
#[using="HLsegs"] Theorem art_law_flagptr : rt_flagptr L HI.
Proof.
  intros LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl (G & _ & FS & _) (G' & _ & FS' & _) H1 H2 C. rewrite HLsegs in *.
  exact (art_fsinv_flagptr rn (g_fs art_fsg G) (g_fs art_fsg G') FF LK FF' LK' M M' F k rs rs' fl FS FS' H1 H2 C).
Qed.

#[using="Type"] Theorem art_law_leak_frames : rt_leak_frames HI.
Proof.
  intros LB FF LK cr A M V FX (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) INC ND.
  exists G. split; [exact REP|]. split. { apply (art_fsinv_leak_proved rn (g_fs art_fsg G) FF LK M FX FS INC). apply NoDup_ListNoDup. exact ND. }
  split; [exact BV|]. split; [exact CRED|]. split; [|split; [exact KN|split; [exact LZ|exact EG]]].
  destruct CLI as (CB & CREST). split; [|exact CREST].
  intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  repeat (split; [assumption|]). split; [|exact B12].
  intros f Hf. apply B11. apply in_app_iff in Hf. apply in_app_iff. destruct Hf as [Hf|Hf].
  - left. apply sfilter_In in Hf. exact (proj2 Hf).
  - apply in_app_iff in Hf. destruct Hf as [Hf|Hf]; [left; exact (INC f Hf)|right; exact Hf].
Qed.
End Laws.
