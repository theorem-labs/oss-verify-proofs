(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCellEx_b BatAllocG_b BatInv_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFsInv_b BatFsInvLaws_b BatFsInvLaws2_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_fsinv_alloc_g : forall rn g FF LK (M M' : word -> option byte) k j (col : fframe -> bool) sp (gb : bool),
  art_fsinv rn g FF LK M -> mem_grows M M' -> 0 <= k <= 5 -> 0 <= j -> 0 <= sp -> sp <= 2 ^ 47 ->
  let fs := ar_fs (rn_ar rn) in let pos := (fg_hint g k + j) mod fs_nfr k in let F := fs_frame fs k pos in
  let LK' := List.filter (fun f => negb (col f)) LK in
  (forall f, In f FF -> col f = false) ->
  (forall f, In f (FF ++ LK') -> ~ (ff_class f = k /\ ff_addr f = F)) ->
  (forall x : word, fs_zone3 rn (U x) -> ~ fs_wr rn k pos LK col (U x) -> M' x = M x) ->
  (forall x : word, cs_zone rn (U x) -> M' x = M x) ->
  cellA M' (fs + 8 * k) 8 ((fg_hint g k + j + 1) mod 2 ^ 64) -> cellA M' (fs + 96) 1 (if gb then 1 else 0) -> cellA M' (fs_flag fs k pos) 1 1 ->
  (forall f i, In f LK -> col f = true -> fs_slot fs f i -> ~ (ff_class f = k /\ i = pos) -> cellA M' (fs_flag fs (ff_class f) i) 1 0) ->
  cellA M' (F + 24) 8 sp -> cellA M' (F + ff_bytes k - 8) 8 (fs_flag fs k pos) ->
  art_fsinv rn (FSGH (fun c => if c =? k then (fg_hint g k + j + 1) mod 2 ^ 64 else fg_hint g c) gb) ((F, k, sp + 32) :: FF) LK' M'.
Proof.
  intros rn g FF LK M M' k j col sp gb I GR Hk Hj Hsp0 Hsp47 fs pos F LK' HFFC FREE AG AGCS CH CG CF CC CRS CFP.
  pose proof (art_c_statics_keep rn M M' (fsinv_geo _ _ _ _ _ I) (fsinv_cs _ _ _ _ _ I) GR AGCS) as CS'.
  pose proof (fsinv_geo _ _ _ _ _ I) as GEO. pose proof (fsinv_frame_in _ _ _ _ _ I) as FIN. pose proof (fsinv_slot _ _ _ _ _ I) as SLOT.
  pose proof (fsinv_nodup _ _ _ _ _ I) as ND.
  destruct I as (_ & W & CTP & CT & C88 & C96 & HINT & _ & FR & FL & _). cbn zeta in *.
  pose proof GEO as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & G8 & G9 & G10 & G11 & G12). unfold FS_BYTES in *. fold fs in W, CTP, CT, C88, C96, HINT, FR, FL, FIN, SLOT, G1, G2, G3, G4, G5, G6, G7, G8.
  assert (NP : 0 < fs_nfr k) by (apply fs_nfr_pos; lia).
  assert (Hpos : 0 <= pos < fs_nfr k) by (apply Z.mod_pos_bound; exact NP).
  pose proof (fs_frame_range fs k pos ltac:(lia) Hpos) as FRG. fold F in FRG. pose proof (ff_bytes_ge64 k ltac:(lia)) as B64.
  pose proof (fs_flag_range fs k pos ltac:(lia) Hpos) as FLG.
  assert (NK : fs_nfr k <= 16384). { unfold fs_nfr. assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia. destruct Ek as [Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]; rewrite Ek; cbn; lia. }
  assert (INC' : forall f, In f (FF ++ LK') -> In f (FF ++ LK)).
  { intros f Hf. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left; exact Hf | right; apply filter_In in Hf; exact (proj1 Hf)]. }
  assert (KEEP : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall z, a <= z < a + Z.of_nat n -> fs_zone3 rn z /\ ~ fs_wr rn k pos LK col z) -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn Hb C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C]. intros x Hx. destruct (Hb (U x) Hx) as (Z3 & NW). exact (AG x Z3 NW). }
  (* [comment removed for export] *)
  assert (NWLO : forall z, (z < fs \/ fs + 11571200 <= z \/ (fs <= z < fs + 4096 /\ ~ (fs + 8 * k <= z < fs + 8 * k + 8) /\ z <> fs + 96)) -> ~ fs_wr rn k pos LK col z).
  { intros z Hz WRz. unfold fs_wr in WRz. fold fs F in WRz. destruct WRz as [X | [X | [X | [(f & i & Hf & _ & (Hi & _) & X) | [X | X]]]]]; try lia.
    destruct (SLOT f ltac:(apply in_or_app; right; exact Hf)) as (Kf & _). pose proof (fs_flag_range fs (ff_class f) i ltac:(lia) Hi) as R.
    assert (0 < fs_nfr (ff_class f) <= 16384) by (unfold fs_nfr; assert (Ek : ff_class f = 0 \/ ff_class f = 1 \/ ff_class f = 2 \/ ff_class f = 3 \/ ff_class f = 4 \/ ff_class f = 5) by lia; destruct Ek as [Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]; rewrite Ek; cbn; lia). lia. }
  unfold art_fsinv. cbn zeta. fold fs. unfold FS_BYTES. cbn [fg_hint fg_gc].
  split; [exact GEO|]. split; [eapply wr_grows; [exact GR | exact W]|].
  split. { refine (KEEP _ _ _ _ _ _ CTP); [lia | cbn; lia |]. intros z Hz. cbn in Hz. split; [unfold fs_zone3, FS_BYTES; lia | apply NWLO; lia]. }
  split. { refine (KEEP _ _ _ _ _ _ CT); [lia | cbn; lia |]. intros z Hz. cbn in Hz. split; [unfold fs_zone3, FS_BYTES; lia | apply NWLO; lia]. }
  split. { refine (KEEP _ _ _ _ _ _ C88); [lia | cbn; lia |]. intros z Hz. cbn in Hz. split; [unfold fs_zone3, FS_BYTES; fold fs; lia | apply NWLO; lia]. }
  split; [exact CG|].
  split. { intros c Hc. destruct (Z.eqb_spec c k) as [-> | NE].
           - split; [exact CH | apply Z.mod_pos_bound; lia].
           - destruct (HINT c Hc) as (C & R). split; [|exact R]. refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |].
             intros z Hz. cbn in Hz. split; [unfold fs_zone3, FS_BYTES; fold fs; lia | apply NWLO; lia]. }
  assert (EFL : FF ++ LK' = List.filter (fun f => negb (col f)) (FF ++ LK)).
  { unfold LK'. rewrite filter_app. f_equal. clear - HFFC. induction FF as [|a l IH]; [reflexivity|]. cbn. rewrite (HFFC a (or_introl eq_refl)). cbn. f_equal. apply IH. intros f Hf. apply HFFC. right. exact Hf. }
  assert (NDL : List.NoDup (map ff_addr (FF ++ LK'))) by (rewrite EFL; apply nodup_map_lfilter; exact ND).
  assert (CLS3 : forall c, 0 <= c <= 5 -> 0 < fs_nfr c <= 16384) by (intros c Hc; unfold fs_nfr; assert (Ek : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5) by lia; destruct Ek as [Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]; rewrite Ek; cbn; lia).
  (* [comment removed for export] *)
  assert (APF : forall f, In f (FF ++ LK') -> apart (ff_addr f) (ff_bytes (ff_class f)) F (ff_bytes k)).
  { intros f Hf. destruct (SLOT f (INC' f Hf)) as (Kf & i & Hi & Af). rewrite Af.
    destruct (fs_frames_apart_or_eq fs (ff_class f) i k pos ltac:(lia) ltac:(lia) Hi Hpos) as [(E1 & E2) | AP]; [|exact AP].
    exfalso. apply (FREE f Hf). split; [exact E1|]. rewrite Af, E1, E2. reflexivity. }
  split.
  { cbn [app map]. constructor; [|exact NDL]. intros X. apply in_map_iff in X as (f & Ef & Hf).
    pose proof (APF f Hf) as AP. pose proof (FIN f (INC' f Hf)) as (_ & _ & P). unfold apart in AP. assert (E : ff_addr f = F) by exact Ef. rewrite E in AP. lia. }
  split.
  { intros f Hf. cbn [app] in Hf. destruct Hf as [<- | Hf].
    - unfold ff_class, ff_addr, ff_rs. cbn [fst snd]. split; [exact Hk|]. split; [exists pos; split; [split; [exact Hpos | reflexivity] | exact CFP]|].
      split; [replace (sp + 32 - 32) with sp by ring; exact CRS | lia].
    - pose proof (INC' f Hf) as Hf0. destruct (FR f Hf0) as (K & (i & SL & CSf) & CR & RS). pose proof (FIN f Hf0) as (IN1 & IN2 & IN3).
      pose proof (ff_bytes_ge64 (ff_class f) ltac:(lia)) as Bf. pose proof (APF f Hf) as AP. unfold apart in AP.
      assert (NWF : forall z, ff_addr f <= z < ff_addr f + ff_bytes (ff_class f) -> fs_zone3 rn z /\ ~ fs_wr rn k pos LK col z).
      { intros z Hz. split; [unfold fs_zone3, FS_BYTES; fold fs; lia|]. unfold fs_wr. fold fs F. intros [X | [X | [X | [(f2 & i2 & Hf2 & _ & (Hi2 & _) & X) | [X | X]]]]]; try lia.
        destruct (SLOT f2 ltac:(apply in_or_app; right; exact Hf2)) as (K2 & _). pose proof (fs_flag_range fs (ff_class f2) i2 ltac:(lia) Hi2). pose proof (CLS3 _ K2). lia. }
      split; [exact K|]. split; [|split; [|exact RS]].
      + exists i. split; [exact SL|]. refine (KEEP _ _ _ _ _ _ CSf); [lia | cbn; lia |]. intros z Hz. cbn in Hz. apply NWF. lia.
      + refine (KEEP _ _ _ _ _ _ CR); [lia | cbn; lia |]. intros z Hz. cbn in Hz. apply NWF. lia. }
  split; [|exact CS'].
  intros c i Hc Hi. pose proof (fs_flag_range fs c i Hc Hi) as FRc.
  assert (NC2 : 2 * fs_nfr c <= 32768). { unfold fs_nfr. assert (0 < 2 ^ (14 - c) <= 2 ^ 14) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]). change (2 ^ 14) with 16384 in *. lia. }
  assert (OTHER : ~ (c = k /\ i = pos) ->
            exists b, cellA M' (fs_flag fs c i) 1 b /\ (b = 0 \/ b = 1)
                      /\ (b = 1 <-> exists f, In f (((F, k, sp + 32) :: FF) ++ LK') /\ ff_class f = c /\ ff_addr f = fs_frame fs c i)).
  { intros NE. destruct (FL c i Hc Hi) as (b & C & B01 & IFF).
    (* [comment removed for export] *)
    assert (NNEW : forall f, In f (((F, k, sp + 32) :: FF) ++ LK') -> ff_class f = c -> ff_addr f = fs_frame fs c i -> In f (FF ++ LK')).
    { intros f Hf Ec Ea. cbn [app] in Hf. destruct Hf as [<- | Hf]; [exfalso | exact Hf]. unfold ff_class, ff_addr in Ec, Ea. cbn [fst snd] in Ec, Ea. subst c.
      apply NE. split; [reflexivity|]. symmetry. apply (fs_frame_inj fs k pos i Ea). lia. }
    (* [comment removed for export] *)
    assert (NWC : (forall f, In f LK -> col f = true -> ~ (ff_class f = c /\ ff_addr f = fs_frame fs c i)) -> ~ fs_wr rn k pos LK col (fs_flag fs c i)).
    { intros NCOL. unfold fs_wr. fold fs F. intros [X | [X | [X | [(f2 & i2 & Hf2 & Cf2 & (Hi2 & Af2) & X) | [X | X]]]]]; try lia.
      - apply NE. exact (fs_flag_inj fs c i k pos Hc ltac:(lia) Hi Hpos X).
      - destruct (SLOT f2 ltac:(apply in_or_app; right; exact Hf2)) as (K2 & _).
        destruct (fs_flag_inj fs c i (ff_class f2) i2 Hc ltac:(lia) Hi Hi2 X) as (E1 & E2). apply (NCOL f2 Hf2 Cf2). split; [symmetry; exact E1|]. rewrite Af2, <- E1, <- E2. reflexivity. }
    destruct B01 as [B0 | B1].
    - (* [comment removed for export] *)
      subst b. assert (NT : ~ exists f, In f (FF ++ LK) /\ ff_class f = c /\ ff_addr f = fs_frame fs c i) by (intros X; apply IFF in X; discriminate X).
      exists 0. split; [|split; [left; reflexivity|]].
      + refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros z Hz. cbn in Hz. assert (z = fs_flag fs c i) by lia. subst z. split; [unfold fs_zone3, FS_BYTES; fold fs; lia|].
        apply NWC. intros f Hf _ (Ec & Ea). apply NT. exists f. split; [apply in_or_app; right; exact Hf | split; assumption].
      + split; [intros X; discriminate X|]. intros (f & Hf & Ec & Ea). exfalso. apply NT. exists f. split; [exact (INC' f (NNEW f Hf Ec Ea)) | split; assumption].
    - subst b. destruct (proj1 IFF eq_refl) as (f & Hf & Ec & Ea).
      assert (UNIQ : forall f', In f' (FF ++ LK) -> ff_addr f' = fs_frame fs c i -> f' = f).
      { intros f' Hf' Ea'. apply (nodup_map_inj _ _ ff_addr (FF ++ LK) f' f ND Hf' Hf). rewrite Ea, Ea'. reflexivity. }
      destruct (col f) eqn:CF1; [apply in_app_or in Hf; destruct Hf as [HfF | HfL]; [rewrite (HFFC f HfF) in CF1; discriminate CF1|]|].
      + (* [comment removed for export] *)
        exists 0. split; [|split; [left; reflexivity|]].
        * rewrite <- Ec. apply (CC f i HfL CF1); [split; [rewrite Ec; exact Hi | rewrite Ec; exact Ea] | rewrite Ec; exact NE].
        * split; [intros X; discriminate X|]. intros (f' & Hf' & Ec' & Ea'). exfalso. pose proof (NNEW f' Hf' Ec' Ea') as Hf'0.
          pose proof (UNIQ f' (INC' f' Hf'0) Ea') as ->. rewrite EFL in Hf'0. apply filter_In in Hf'0 as (_ & X). rewrite CF1 in X. discriminate X.
      + (* [comment removed for export] *)
        exists 1. split; [|split; [right; reflexivity|]].
        * refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros z Hz. cbn in Hz. assert (z = fs_flag fs c i) by lia. subst z. split; [unfold fs_zone3, FS_BYTES; fold fs; lia|].
          apply NWC. intros f2 Hf2 Cf2 (Ec2 & Ea2). pose proof (UNIQ f2 ltac:(apply in_or_app; right; exact Hf2) Ea2) as ->. rewrite CF1 in Cf2. discriminate Cf2.
        * split; [intros _|reflexivity]. exists f. split; [|split; assumption]. change (In f ((F, k, sp + 32) :: (FF ++ LK'))). apply in_cons. rewrite EFL. apply filter_In. split; [exact Hf | rewrite CF1; reflexivity]. }
  destruct (Z.eq_dec c k) as [Eck | Nck]; [destruct (Z.eq_dec i pos) as [Eip | Nip]|].
  - subst c i. exists 1. split; [exact CF|]. split; [right; reflexivity|]. split; [intros _|reflexivity].
    exists (F, k, sp + 32). split; [left; reflexivity | split; reflexivity].
  - apply OTHER. intros (_ & X). exact (Nip X).
  - apply OTHER. intros (X & _). exact (Nck X).
Qed.
