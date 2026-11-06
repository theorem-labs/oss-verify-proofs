(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Shadow MI_Read MI_Pres1 MI_Pres2.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma guard_true {R} tag (c : bool) (k bail : M R) : c = true -> guard tag c k bail = k.
Proof. intros ->. reflexivity. Qed.

Lemma size_class_28 sc : 28 <= sc < 48 -> 292 <= size_class sc.
Proof.
  intros H. unfold size_class.
  assert (E : exists n, Z.to_nat sc = (28 + n)%nat /\ (n < 20)%nat) by (exists (Z.to_nat sc - 28)%nat; lia).
  destruct E as (n & -> & Hn).
  do 20 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
Lemma guard16_arith S stride i off n q last :
  1 <= S -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off <= 255 -> 0 <= i <= last ->
  (stride = 16 * S \/ last = 0) -> (stride <= 16 * S \/ 292 <= S) ->
  S * i <= q < S * (i + 1).
Proof.
  intros HS Hq Hfit Hn Hoff Hi A B.
  destruct A as [E|L0].
  - subst stride. Local Ltac2 Set LiaHints.tbl := fun () => "0040>41329089501.13493449659.15  55931546631.1366189108153.1400000400;00K00OS2HqS2Hi2L0S4Hfit2Hn4Hoff1BS2Hq".
assert (q = S * i + off) by lia. subst q. nia.
  - assert (i = 0) by lia. subst i. assert (q = off) by lia. subst q. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma guard17_arith stride i off n q last maplen :
  16 <= stride -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off -> 0 <= i <= last ->
  16 + stride * (last + 1) <= maplen * 4096 ->
  q <= maplen * 4096 / 16 - 1.
Proof.
  intros. Local Ltac2 Set LiaHints.tbl := fun () => "0030>24890867315.1436715006380.1448684554819.1500000100200BSSS2H02H12H22H52H6".
replace (maplen * 4096 / 16) with (maplen * 256) by (rewrite <- (Z.div_mul (maplen * 256) 16) by lia; f_equal; lia).
  assert (stride * i + stride <= stride * (last + 1)) by nia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section BLOCK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variables (c : cptr) (off n : Z).
Hypothesis Hk : In ((c, off), n) BL.

Local Notation R := (MR st).

Record blk_facts (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z) : Prop := mkBF {
  bf_slot : s_slots st !! c = Some (m, i);
  bf_hosts : s_groups st !! bm = Some (mkGhdr (Some m) ai);
  bf_mem : m_mem (R m) = Some bm;
  bf_c : c = (fst bm, sstart (R m) i);
  bf_i : 0 <= i <= m_last_idx (R m);
  bf_li : m_last_idx (R m) <= 31;
  bf_ai : 0 <= ai <= m_last_idx (R m);
  bf_off : 0 <= off <= 255;
  bf_n : 0 <= n;
  bf_fit : UNIT * off + n <= get_stride (R m) - IB;
  bf_stride : UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0;
  bf_b16 : 0 <= snd bm /\ snd bm mod UNIT = 0;
  bf_notA : tbit (m_avail (R m)) i = false;
  bf_notF : tbit (m_freed (R m)) i = false;
  bf_notH : s_groups st !! c = None;
  bf_sc : (0 <= m_sizeclass (R m) < 48 /\ (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
            /\ (get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) \/ (m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0)))
          \/ m_sizeclass (R m) = 63;
  bf_top : m_maplen (R m) <> 0 -> snd bm = 0 /\ gend (R m) <= m_maplen (R m) * 4096;
  bf_maplen : 0 <= m_maplen (R m);
  bf_area : s_areas st !! a = Some ar /\ a_check ar = c_secret (s_ctx st) /\ snd a mod PGSZ = 0 /\ 0 <= ka < NSLOTS /\ m = mslot a ka;
  bf_shadow : blk_shadow_ok st ((c, off), n) m i;
  bf_hdr0 : known st (fst bm, sstart (R m) (i + 1) - IB) 0;
  bf_bytes : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256
}.

#[using="X L BL LS INV Hk"] Lemma block_facts : exists m bm i ai a ar ka, blk_facts m bm i ai a ar ka.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & Hoff & Hn & Hfit). cbn [bslot boff bsize fst snd] in Hs, Hoff, Hn, Hfit.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ec).
  pose proof Hm as [ai Hm'].
  pose proof (ig_ok _ _ _ IG _ _ _ Hm') as GO.
  pose proof (hosts_mem _ _ _ IM _ _ Hm) as Hmem.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ec.
  pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! m) as [mr|] eqn:Em; [| congruence].
  destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
  destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
  exists m, bm, i, ai, a, ar, ka.
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm), <- Ec in P.
  assert (U : In c (map bslot BL)) by (change c with (bslot ((c, off), n)); apply in_map; exact Hk).
  unfold one5 in P.
  constructor; auto.
  - pose proof (g_li _ _ _ _ _ _ GO). Local Ltac2 Set LiaHints.tbl := fun () => "0030>13573058490.5141814433747.5051906659886.5200000300700<S1HS2HiS3Hsc".
lia.
  - exact (g_ai _ _ _ _ _ _ GO).
  - exact (stride_ge _ _ _ IG _ _ Hm).
  - exact (g_align _ _ _ _ _ _ GO).
  - destruct (tbit (m_avail (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (tbit (m_freed (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. tauto.
  - destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc Hml]|(Hsc & Hli & Hml & _)]; [left| right; exact Hsc].
    destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
    split; [exact Hsc|]. split; [exact S1|].
    unfold get_stride. destruct (m_last_idx (R m) =? 0) eqn:E0; destruct (m_maplen (R m) =? 0) eqn:EM; cbn [andb negb];
      first [left; reflexivity | right; split; [apply Z.eqb_eq; exact E0| apply Z.eqb_neq; exact EM]].
  - intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r' & _ & _ & _ & Hge). auto.
  - exact (g_maplen _ _ _ _ _ _ GO).
  - exact (ish_blk _ _ ISH _ m i Hk Hs).
  - apply (ish_hdr0 _ _ ISH _ _ _ Hm). unfold cnt_of. lia.
  - intros q v Hq. eapply known_byte; [| exact Hq]. intros sh o' v' t Hsh Hc. exact (proj1 (proj1 (ish_ticks _ _ ISH _ _ Hsh) o' v' t Hc)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End BLOCK.

Section HDR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Local Notation R := (MR st).
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (R m).
Let e : Z := snd c + stride - IB.
Let res : Z := e - snd p - n.
Let q : Z := (snd p - snd bm - UNIT) / UNIT.

#[using="n bm ai a ar ka BF"] Lemma p_snd : snd p = sstart (R m) i + UNIT * off.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
#[using="st n m i ai a ar ka BF"] Lemma p_fst : fst p = fst bm.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
#[using="c off n i ai a ar ka BF"] Lemma gbase_bm : gbase (R m) = bm.
Proof. unfold gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
#[using="off n bm ai a ar ka BF"] Lemma c_snd : snd c = sstart (R m) i.
Proof. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.

#[using="n ai a ar ka BF e res"] Lemma q16 : UNIT * q = stride * i + UNIT * off /\ 0 <= q < 2^16.
Proof.
  destruct (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as (_ & _ & _ & _ & Q & _). cbn [bslot boff fst snd] in Q.
  rewrite gbase_bm in Q. subst q p. cbn [snd aadd] in *. rewrite c_snd in *. unfold sstart in *. rewrite gbase_bm in *.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. subst stride.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>24890752246.2124897143244.2233223631350.2241146381802.2255536683976.2100000100200300900:SSSS2S11HS".
replace (snd bm + UNIT + get_stride (R m) * i + UNIT * off - snd bm - UNIT) with (get_stride (R m) * i + UNIT * off) in Q |- * by lia.
  split; [| exact Q].
  unfold UNIT in *. pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). rewrite S2 in H.
  replace (get_stride (R m) * i + 16 * off) with ((get_stride (R m) / 16 * i + off) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Let SH := bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF.

#[using="st n m bm i ai a ar ka BF stride e res q"] Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  rewrite p_snd. unfold sstart. rewrite gbase_bm.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. destruct (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B1 B2]. unfold UNIT in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>24891030774.2624897143244.2732858298761.2800000400800DS2B1S2B1S2S12B11H2H0".
pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). pose proof (Z.div_mod (snd bm) 16 ltac:(lia)).
  rewrite S2 in H. rewrite B2 in H0.
  replace (snd bm + 16 + get_stride (R m) * i + 16 * off) with ((snd bm / 16 + 1 + get_stride (R m) / 16 * i + off) * 16) by lia.
  apply Z_mod_mult.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="bm i ai a ar ka BF q"] Lemma res_nonneg : 0 <= res.
Proof.
  subst res e p stride. cbn [snd aadd]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). unfold IB, UNIT in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>67275653658.20000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="n ai a ar ka BF stride e res SH"] Lemma get_meta_eq {T} (k : aptr -> Z -> Z -> M T) bail : get_meta st p k bail = k m q i.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  unfold get_meta.
  rewrite (guard_true 10) by (apply Z.eqb_eq; exact p_mod16).
  unfold rd16.
  Local Ltac2 Set LiaHints.tbl := fun () => "00<0>22999234796.4224561843857.3637252221201.3643045784683.434510990859.40 52078369397.4053624587632.3753908986357.3854384010184.3757573027061.3662501120465.3665541758487.3700000900:00;00B00G00Q00Y00`00d00e00f00kS3Hsc3H28SSS3Hsc1HS3OFFS2Q12PS2PFS2Hi3HliS3E631HS2HiSSS3RES".
rewrite (rd8_known st (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-4)) 0) by (eapply known_at; [exact K4| cbn; lia| reflexivity]).
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bm).
  { pose proof q16 as [Q1 _]. pose proof p_snd as PS. pose proof p_fst as PF. unfold sstart in PS. rewrite gbase_bm in PS.
    subst stride. unfold aadd. destruct bm as [br bo]. cbn [fst snd] in *. f_equal; [exact PF| lia]. }
  rewrite Ebase. unfold get_group. rewrite (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). cbn [g_meta].
  rewrite (land31_idx i (Z.min res 5)) by lia. fold (MR st m).
  rewrite (guard_true 11) by (rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  rewrite (guard_true 13) by (unfold testbit; rewrite (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  rewrite (guard_true 14) by (unfold testbit; rewrite (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
  rewrite (guard_true 15) by (rewrite Em, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; exact Hck).
  pose proof q16 as [Q1 _]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. fold stride in FIT.
  unfold UNIT, IB in Q1, FIT. fold stride in FIT.
  rewrite (guard_true 16).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc & Hle & Hst)| E63].
      - fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
        pose proof (size_class_bound _ Hsc) as SB.
        assert (A : stride = 16 * size_class (m_sizeclass (R m)) \/ m_last_idx (R m) = 0) by tauto.
        assert (B : stride <= 16 * size_class (m_sizeclass (R m)) \/ 292 <= size_class (m_sizeclass (R m))).
        { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
        clearbody p stride e res q. clear SH Hle Hst.
        pose proof (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0 OFF Hi A B) as [G1 G2].
        destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [|lia].
        apply Bool.andb_true_iff. split; [apply Z.leb_le; exact G1| apply Z.ltb_lt; exact G2].
      - clearbody p stride e res q. clear SH. destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [lia|]. apply Z.eqb_eq. exact E63. }
  rewrite (guard_true 17).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (Z.eqb_spec (m_maplen (R m)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE]. apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite gbase_bm, B0 in GE. fold stride in GE. unfold UNIT in GE.
      pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 _]. fold stride in S1. unfold UNIT in S1.
      clearbody p stride e res q. clear SH.
      eapply (guard17_arith stride i off n q); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; lia. }
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).

#[using="Type"] Lemma ea_fst : fst ea = fst bm. Proof. reflexivity. Qed.
#[using="off n ai a ar ka BF p res q"] Lemma ea_snd : snd ea = e.
Proof. subst ea e stride. cbn [snd aadd]. rewrite c_snd. unfold sstart. rewrite gbase_bm. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56555977517.20000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="off n ai a ar ka BF p res q"] Lemma ea_off d : snd (aadd ea d) = e + d.
Proof. pose proof ea_snd as EA. unfold aadd at 1. cbn [snd]. rewrite <- EA. reflexivity. Qed.

#[using="ai a ar ka BF e res q SH"] Lemma get_nominal_size_eq {T} (k : Z -> M T) bail : get_nominal_size st p ea k bail = k n.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof ea_snd as EA. pose proof p_fst as PF. pose proof c_snd as CS.
  assert (CF : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  assert (Hres : res = e - snd p - n) by reflexivity.
  assert (He : e = snd c + stride - IB) by reflexivity.
  assert (Hst : stride = get_stride (R m)) by reflexivity.
  assert (Hp2 : snd p = snd c + UNIT * off) by reflexivity.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ, <- CS, <- Hst in H0.
  (* [comment removed for export] *)
  assert (OFF : forall d, snd (aadd ea d) = snd c + get_stride (R m) - IB + d) by (intros d; rewrite ea_off, He, Hst; reflexivity).
  clearbody q. clear SH.
  unfold get_nominal_size.
  Local Ltac2 Set LiaHints.tbl := fun () => "00G0>11227741828.5412968552960.5418088705564.4918088844702.542517236875.49 2517606153.44 26482670641.482866932681.44 2867300427.49 32381050280.4937250131786.4237320885929.5445005441428.4845007538321.5450679163078.4853628688273.4760592686854.4963265729318.4964441408872.4965537395958.4767273982104.5467275635117.497650529638.49 00000C00M00\00k01801E01S01`01m02:02A02K02X02b02l03:03G03T03a03l04:04L04YS3RES2PF2CF3Hp23R32S2PF2CF2R5S2PF2CF4Hres2R5S2PF2CF4Hres2R5S2EA2PF2CF2R5S2EA2PF2CF2R5S2PF2CF3Hp22R5S2EA2PF2CF2R5S2EA2PF2CF2R5S2EA2PF2CF2R5S2PF2CFS2PF2CF2R5S2N02PF2CF2R5S2N02PF2CFS2PF2CF2R5S2Hi3Hli2PF2CFS2EA2PF2CF2R5S2EA2PF2CF2R5S2EA2PF2CF2R5S3RES2PF2CFS2PF2CF3Hp22R5S3RES2PF2CF3Hp22NES2EA2PF2CF2R5".
rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
  cbv beta. rewrite (shiftr5_res i (Z.min res 5)) by lia. cbv zeta.
  destruct (Z.leb_spec 5 (Z.min res 5)) as [R5|R5].
  - (* [comment removed for export] *)
    destruct (K5 ltac:(lia)) as (B0 & B1 & B2 & B3 & B5 & R32).
    rewrite (guard_true 20) by (apply Z.eqb_eq; lia).
    unfold rd32.
    rewrite (rd8_known st (aadd ea (-4)) (byte_of res 0)) by (eapply known_at; [exact B0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 1) (byte_of res 1)) by (eapply known_at; [exact B1| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 2) (byte_of res 2)) by (eapply known_at; [exact B2| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 3) (byte_of res 3)) by (eapply known_at; [exact B3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (u32_bytes res) by lia.
    rewrite (guard_true 21) by (apply Z.leb_le; lia).
    rewrite (rd8_known st (aadd ea (-5)) 0) by (eapply known_at; [exact B5| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 25) by reflexivity.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [apply Kr; lia| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
  - (* [comment removed for export] *)
    replace (Z.min res 5) with res by lia.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    assert (Kr0 : known st (fst c, snd c + get_stride (R m) - IB - res) 0).
    { destruct (Z.eq_dec res 0) as [E0|NE]; [| apply Kr; lia]. rewrite E0, Z.sub_0_r, CF, <- Hst. exact H0. }
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [exact Kr0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="n bm ai a ar ka BF stride e res q SH ea"] Lemma free_hdr_eq : free_hdr st p = SRet (Some (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st), m, i)).
Proof.
  unfold free_hdr. rewrite get_meta_eq. cbv beta zeta.
  unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
  match goal with |- get_nominal_size st p ?e ?k ?b = _ => change (get_nominal_size st p e k b) with (get_nominal_size st p ea k b) end.
  rewrite get_nominal_size_eq. reflexivity.
Qed.
End HDR.
