(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib RefReadLib FPSteps
  LibIface LibBudget LibEff MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition O_WORDS : Z := 48.  Definition O_N : Z := 56.  Definition O_DIAG : Z := 64.
Definition O_WIDX : Z := 72.  Definition O_ICOUNT : Z := 80.  Definition O_ENDIAN : Z := 88.
Definition O_FLAGS : Z := 92.  Definition O_M1 : Z := 96.  Definition O_M2 : Z := 136.
Definition O_M3 : Z := 176.  Definition O_V1 : Z := 216.  Definition O_V2 : Z := 240.  Definition O_V3 : Z := 264.
Definition PM_FRAME : Z := 880.

Section Base.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
Hypothesis HLerr_img : forall a, errno_win L a -> in_ranges (ly_img L) a.
Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

#[local] Abbreviation fld := (CRep.fld SEGS).
#[local] Abbreviation vec32 := (CRep.vec32 MI).
#[local] Abbreviation vec_opnd := (CRep.vec_opnd MI).
#[local] Abbreviation umapx := (@HRep.umapx AC SEGS L MI).

Record pmw : Type := PMW {
  w_sp   : Z;
  w_STK  : Z;
  w_ret  : Z;
  w_p    : Z;
  w_cons : Z;
  w_user : Z;
  w_diag : Z;
  w_words : Z; w_n : Z;
  w_L0   : list (Z * Z);
  w_R0   : bvmap 5 word;
  w_A0   : AS MI; w_M0 : mem; w_model0 : Model; w_s : SX ST
}.
Definition w_sp0 (w : pmw) : Z := w_sp w + PM_FRAME.

Definition junkL (w : pmw) (a : Z) : Prop :=
  0 < a < alloc_ceiling /\ ~ in_ranges (ly_img L) a /\ forall q k, In (q, k) (w_L0 w) -> ~ (q <= a < q + k).

Definition PMF (w : pmw) (a : Z) : Prop :=
  (w_p w <= a < w_p w + PARSER_SIZE) \/ junkL w a.

Definition SLOT_vals (R : bvmap 5 word) (ret : Z) : list word :=
  [getr R 27%bv; getr R 26%bv; getr R 25%bv; getr R 24%bv; getr R 23%bv; getr R 22%bv; getr R 21%bv;
   getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

Record pmc : Type := PMC {
  c_widx : Z; c_icount : Z; c_endian : Z; c_reqconv : Z;
  c_m1 : Z * Z * list (Z * (Z * Z));
  c_m2 : Z * Z * list (Z * (Z * (Z * Z * Z)));
  c_m3 : Z * Z * list (Z * (Z * Z));
  c_v1 : Z * Z * Z;
  c_v2 : Z * list Z * Z;
  c_v3 : Z * list Z * Z;
  c_tr : list (Z * Z)
}.

Definition c_blocks (c : pmc) : list (Z * Z) :=
  umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
  ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
  ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
  ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
  ++ (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))])
  ++ (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))])
  ++ c_tr c.

Record PMX (w : pmw) (A : AS MI) (M : mem) (model : Model) (c : pmc) : Prop := MKPMX {

  x_ai   : ainv MI A M model;
  x_ms   : mstd model;
  x_fs   : m_fs model = m_fs (w_model0 w);
  x_fds  : m_fds model = m_fds (w_model0 w);
  x_sx   : sx_inv ST (w_s w) M;
  x_sxh  : sx_handler_set ST (w_s w);
  x_roc  : ro_clear L M;
  x_eff  : eff MI (w_A0 w) A (w_M0 w) M (w_sp0 w - w_STK w, w_sp0 w) (PMF w);
  x_own_sx : forall a, owned MI A a -> ~ sx_region ST a;
  x_err_sx : forall a, errno_win L a -> ~ sx_region ST a;
  x_win_sx : forall a, zwin (w_sp0 w - w_STK w) (w_sp0 w) a -> ~ sx_region ST a;

  x_geo  : w_sp w mod 16 = 0 /\ alloc_ceiling + w_STK w <= w_sp0 w /\ w_sp0 w < 2 ^ 47 /\ 16384 <= w_STK w
           /\ w_sp0 w <= w_p w /\ w_p w + PARSER_SIZE <= 2 ^ 47 /\ w_p w mod 16 = 0
           /\ w_sp0 w <= w_cons w /\ w_cons w + 48 <= 2 ^ 47 /\ apart (w_p w) PARSER_SIZE (w_cons w) 48
           /\ 0 <= w_n w < 2 ^ 24
           /\ (w_words w <> 0 -> 0 < w_words w /\ w_words w mod 4 = 0 /\ w_words w + 4 * w_n w <= 2 ^ 47
                                 /\ (w_sp0 w <= w_words w \/ exists q k, In (q, k) (w_L0 w) /\ q <= w_words w /\ w_words w + 4 * w_n w <= q + k)
                                 /\ (forall a, zwin (w_words w) (w_words w + 4 * w_n w) a ->
                                       ~ zwin (w_sp0 w - w_STK w) (w_sp0 w) a /\ ~ (w_p w <= a < w_p w + PARSER_SIZE)));

  x_wdef : mdef M (w_sp0 w - w_STK w) (w_STK w);
  x_wown : forall a, zwin (w_sp0 w - w_STK w) (w_sp0 w) a -> ~ owned MI A a;
  x_slots : forall k, 1 <= k <= 13 ->
      rdn SEGS M (Z_to_bv 64 (w_sp0 w - 8 * k)) 8 = Some (word_to_le_bytes 8 (nth (Z.to_nat (13 - k)) (SLOT_vals (w_R0 w) (w_ret w)) (Z_to_bv 64 0)));

  x_pdef : mdef M (w_p w) PARSER_SIZE;
  x_cons : fld M (w_p w + 8) 8 (w_cons w);
  x_user : fld M (w_p w + 16) 8 (w_user w);
  x_hdrfn : fld M (w_p w + 24) 8 0;
  x_insfn : fld M (w_p w + 32) 8 0;
  x_hunk : fld M (w_p w + 40) 1 0;
  x_words : fld M (w_p w + O_WORDS) 8 (w_words w);
  x_n    : fld M (w_p w + O_N) 8 (w_n w);
  x_diag : fld M (w_p w + O_DIAG) 8 (w_diag w);
  x_widx : fld M (w_p w + O_WIDX) 8 (c_widx c);
  x_icount : fld M (w_p w + O_ICOUNT) 8 (c_icount c);
  x_endian : fld M (w_p w + O_ENDIAN) 4 (c_endian c);
  x_flags : fld M (w_p w + O_FLAGS) 2 (c_reqconv c);
  x_scal : 0 <= c_widx c <= w_n w /\ 0 <= c_icount c <= c_widx c /\ 0 <= c_endian c < 2 ^ 32 /\ (c_reqconv c = 0 \/ c_reqconv c = 1);
  x_consf : fld M (w_cons w + 32) 8 0;
  x_consd : mdef M (w_cons w + 32) 8;
  x_wbuf : w_words w <> 0 -> mdef M (w_words w) (4 * w_n w);

  x_m1 : umapx 24 (nval24 SEGS) A M (w_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c));
  x_m2 : umapx 32 (nval32 SEGS) A M (w_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c));
  x_m3 : umapx 24 (nval24 SEGS) A M (w_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c));
  x_v1 : vec_opnd A M (w_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c));
  x_v2 : vec32 A M (w_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c));
  x_v3 : vec32 A M (w_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c));

  x_live : Permutation (live MI A) (w_L0 w ++ c_blocks c);
  x_caps : caps MI A = lib_caps /\ bigcap MI A = LIB_BIGCAP /\ LIB_NMAX <= NMAX MI
}.

Arguments MKPMX {w A M model c}.
Arguments x_ai {w A M model c} _.
Arguments x_ms {w A M model c} _.
Arguments x_fs {w A M model c} _.
Arguments x_fds {w A M model c} _.
Arguments x_sx {w A M model c} _.
Arguments x_sxh {w A M model c} _.
Arguments x_roc {w A M model c} _.
Arguments x_eff {w A M model c} _.
Arguments x_own_sx {w A M model c} _.
Arguments x_err_sx {w A M model c} _.
Arguments x_win_sx {w A M model c} _.
Arguments x_geo {w A M model c} _.
Arguments x_wdef {w A M model c} _.
Arguments x_wown {w A M model c} _.
Arguments x_slots {w A M model c} _.
Arguments x_pdef {w A M model c} _.
Arguments x_cons {w A M model c} _.
Arguments x_user {w A M model c} _.
Arguments x_hdrfn {w A M model c} _.
Arguments x_insfn {w A M model c} _.
Arguments x_hunk {w A M model c} _.
Arguments x_words {w A M model c} _.
Arguments x_n {w A M model c} _.
Arguments x_diag {w A M model c} _.
Arguments x_widx {w A M model c} _.
Arguments x_icount {w A M model c} _.
Arguments x_endian {w A M model c} _.
Arguments x_flags {w A M model c} _.
Arguments x_scal {w A M model c} _.
Arguments x_consf {w A M model c} _.
Arguments x_consd {w A M model c} _.
Arguments x_wbuf {w A M model c} _.
Arguments x_m1 {w A M model c} _.
Arguments x_m2 {w A M model c} _.
Arguments x_m3 {w A M model c} _.
Arguments x_v1 {w A M model c} _.
Arguments x_v2 {w A M model c} _.
Arguments x_v3 {w A M model c} _.
Arguments x_live {w A M model c} _.
Arguments x_caps {w A M model c} _.

Section Facts.
  Context (w : pmw).

  Lemma pmx_img_ro_clear : forall A M model c, PMX w A M model c -> img_ro_clear L M.
  Proof using AC SEGS L MI ST w. intros A M model c X. apply img_ro_clear_of; [exact (x_roc X) |]. intros a Ha. eapply sx_relro. exact (x_sx X). exact Ha. Qed.

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC SEGS L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw|Hoff].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hoff). lia.
  Qed.
End Facts.

Section Via.
  Lemma sx_inv_via_eff : forall (s0 : SX ST) (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
    sx_inv ST s0 M -> ainv MI A M model -> eff MI A A' M M' W F ->
    (forall a, owned MI A a -> ~ sx_region ST a) -> (forall a, errno_win L a -> ~ sx_region ST a) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
    sx_inv ST s0 M'.
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros s0 A A' M M' model W F SX AI EF Hosx Hesx HF HW.
    apply (sx_frame ST s0 M M' SX). intros a Ha.
    assert (Himg : in_ranges (ly_img L) (bv_unsigned a)).
    { destruct Ha as [Hs | Hr]; [exact (HLrw_img _ (sx_region_rw ST _ Hs)) | exact (HLrelro_img _ Hr)]. }
    pose proof (HLimg_lo _ Himg) as Hlt.
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF). intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - destruct Ha as [Hs | Hr]; [exact (Hosx _ Ho Hs)|].
      destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (HLrw_relro _ Hrw Hr) | exact (Hni Himg)].
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
      + destruct Ha as [Hs | Hr]; [exact (Hosx _ Ho Hs)|].
        destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (HLrw_relro _ Hrw Hr) | exact (Hni Himg)].
      + exact (Hni Himg).
      + exact (HF _ Hf Himg).
    - destruct Hnm as (Hni & _). exact (Hni Himg).
    - exact (HF _ Hf Himg).
    - unfold W_of in Hw. lia.
    - destruct Ha as [Hs | Hr]; [exact (Hesx _ He Hs)|]. exact (HLrw_relro _ (HLerr_rw _ He) Hr).
  Qed.

  Lemma ro_clear_via_eff : forall (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
    ro_clear L M -> ainv MI A M model -> eff MI A A' M M' W F ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
    ro_clear L M'.
  Proof using AC SEGS L MI HLimg_lo HLerr_rw.
    intros A A' M M' model W F RC AI EF HF HW.
    eapply (ro_clear_frame L _ M M' RC (ef_frame _ _ _ _ _ _ _ _ _ EF)).
    intros a (Himg & Hnrw & Hnrel). pose proof (HLimg_lo _ Himg) as Hlt.
    intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
      + destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
      + exact (Hni Himg).
      + exact (HF _ Hf Himg).
    - destruct Hnm as (Hni & _). exact (Hni Himg).
    - exact (HF _ Hf Himg).
    - unfold W_of in Hw. lia.
    - exact (Hnrw (HLerr_rw _ He)).
  Qed.

  Lemma mdef_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop) a n,
    eff MI A A' M M' W F -> alloc_ceiling <= a \/ (a + n <= alloc_ceiling /\ forall i, 0 <= i < n -> ~ in_ranges (ly_img L) (a + i)) ->
    0 <= a -> a + n <= 2 ^ 64 ->
    (forall i, 0 <= i < n -> ~ owned MI A (a + i)) -> (forall i, 0 <= i < n -> ~ F (a + i)) ->
    mdef M a n -> mdef M' a n.
  Proof using AC SEGS L MI HLimg_lo HLrw_img HLerr_rw.
    intros A A' M M' W F a n EF Ha Ha0 Han Hown HF Hdef i Hi. pose proof ac_bounds_lit as Hcv.
    destruct (ef_def _ _ _ _ _ _ _ _ _ EF (a + i) ltac:(lia) (Hdef i Hi)) as [H|[H|[H|H]]];
      [exact H | exfalso; exact (Hown i Hi H) | exfalso; exact (HF i Hi H) |].
    exfalso. pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ H))).
    destruct Ha as [Ha|[Ha Hni]]; [lia | exact (Hni i Hi (HLrw_img _ (HLerr_rw _ H)))].
  Qed.

  Lemma agree_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop) (P : Z -> Prop),
    eff MI A A' M M' W F ->
    (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ owned MI A a /\ ~ owned MI A' a /\ M (Z_to_bv 64 a) <> None /\ ~ F a /\ ~ W_of W a /\ ~ errno_win L a) ->
    CRep.agree_on P M M'.
  Proof using AC SEGS L MI.
    intros A A' M M' W F P EF HP a Ha. destruct (HP a Ha) as (Hr & Ho & Ho' & Hd & Hf & Hw & He).
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
    intros [H|[H|[H|[H|[H|H]]]]]; try tauto. destruct H as (_ & _ & Hn). exact (Hd Hn).
  Qed.

  Lemma eff_drop : forall (A A' : AS MI) M M' model' (W : Z * Z) (F G : Z -> Prop),
    eff MI A A' M M' W (fun a => F a \/ G a) -> ainv MI A' M' model' ->
    (forall a, G a -> W_of W a /\ alloc_ceiling <= a) ->
    (forall a, G a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
    eff MI A A' M M' W F.
  Proof using AC SEGS L MI HLimg_lo HLrw_img.
    intros A A' M M' model' W F G E AI' HG HD. destruct E as [C B O FR D OI]. constructor.
    - exact C. - exact B.
    - intros a Ho'. destruct (O a Ho') as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | right; right; exact H |].
      exfalso. destruct (HG a H) as [_ Hc]. exact (hi_unowned A' M' model' a AI' Hc Ho').
    - intros a Hn. apply FR. intros [H|[H|[H|[[H|H]|[H|H]]]]]; apply Hn.
      + left; exact H. + right; left; exact H. + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left. exact (proj1 (HG _ H)).
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; exact H.
    - intros a Ha Hd. destruct (D a Ha Hd) as [H|[H|[[H|H]|H]]]; [left; exact H | right; left; exact H | right; right; left; exact H | left; exact (HD a H Hd) | right; right; right; exact H].
    - exact OI.
  Qed.
End Via.

Lemma Zlength_cons : forall {T : Type} (x : T) l, Zlength (x :: l) = Zlength l + 1.
Proof using. intros. unfold Zlength. cbn [length]. lia. Qed.
Lemma Zlength_nil : forall (T : Type), Zlength (@nil T) = 0.
Proof using. intros. reflexivity. Qed.

Section LiveAlg.
  Lemma perm_nodup_fst : forall (l1 l2 : list (Z * Z)), Permutation l1 l2 -> NoDup (map fst l1) -> NoDup (map fst l2).
  Proof using. intros l1 l2 P N. apply (Permutation_map fst) in P. rewrite <- P. exact N. Qed.

  Lemma nodup_fst_notin : forall (b : Z * Z) (R : list (Z * Z)), NoDup (map fst (b :: R)) -> ~ In (fst b) (map fst R).
  Proof using.
    intros b R N Hin. cbn in N. inversion N as [|x l Hn Hl]; subst. apply Hn. apply list_elem_of_In. exact Hin.
  Qed.
  Lemma nodup_fst_tail : forall (b : Z * Z) (R : list (Z * Z)), NoDup (map fst (b :: R)) -> NoDup (map fst R).
  Proof using. intros b R N. cbn in N. inversion N; assumption. Qed.

  Lemma live_del_perm : forall (p n : Z) (R lv lv1 : list (Z * Z)),
    Permutation lv ((p, n) :: R) -> NoDup (map fst lv) -> live_del p lv lv1 -> NoDup (map fst lv1) ->
    Permutation lv1 R.
  Proof using.
    intros p n R lv lv1 P N D N1.
    pose proof (perm_nodup_fst _ _ P N) as NR. pose proof (nodup_fst_notin (p, n) R NR) as Hp. cbn in Hp.
    apply live_equiv_perm; [exact N1 | exact (nodup_fst_tail _ _ NR) |].
    intros q k. rewrite (D q k). split.
    - intros [Hin Hq]. apply (Permutation_in (q, k) P) in Hin. destruct Hin as [E|Hin]; [injection E; lia | exact Hin].
    - intros Hin. split; [apply (Permutation_in (q, k) (Permutation_sym P)); right; exact Hin |].
      intros ->. apply Hp. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hin].
  Qed.

  Lemma live_add_perm : forall (p n : Z) (R lv lv' : list (Z * Z)),
    Permutation lv R -> live_add p n lv lv' -> Permutation lv' ((p, n) :: R) /\ ~ In p (map fst R).
  Proof using.
    intros p n R lv lv' P [-> Hf]. split; [apply perm_skip; exact P|].
    intros Hin. apply Hf. apply (Permutation_map fst) in P. apply (Permutation_in p (Permutation_sym P)). exact Hin.
  Qed.

  Lemma blk_xfer_small : forall (B B' R lv lv' : list (Z * Z)),
    Zlength B <= 1 -> Zlength B' <= 1 ->
    blk_xfer B B' lv lv' -> Permutation lv (B ++ R) -> NoDup (map fst lv) -> NoDup (map fst lv') ->
    Permutation lv' (B' ++ R) /\ (forall b, In b B' -> ~ In (fst b) (map fst R)).
  Proof using.
    intros B B' R lv lv' HB HB' (X1 & X2 & X3) P N N'.
    pose proof (perm_nodup_fst _ _ P N) as NB. pose proof NB as NB2. rewrite map_app in NB2.
    apply (proj1 (list_relations.list.NoDup_app _ _)) in NB2. destruct NB2 as (NBB & HX & NR).
    assert (FR : forall b, In b B' -> ~ In (fst b) (map fst R)).
    { intros b Hb Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & HxR).
      apply (X2 b x Hb); [| | exact Hx].
      - apply (Permutation_in x (Permutation_sym P)). apply in_app_iff. right. exact HxR.
      - intros HxB. apply (HX (fst x)); apply list_elem_of_In; [apply in_map_iff; exists x; split; [reflexivity | exact HxB] |].
        apply in_map_iff. exists x. split; [reflexivity | exact HxR]. }
    split; [| exact FR].
    apply live_equiv_perm; [exact N' | |].
    - destruct B' as [|b' [|? ?]]; [exact NR | | rewrite !Zlength_cons in HB'; unfold Zlength in HB'; cbn in HB'; lia].
      cbn. apply NoDup_cons_2; [| exact NR]. intros Hin. apply (FR b' ltac:(left; reflexivity)). apply list_elem_of_In in Hin. exact Hin.
    - intros q k. rewrite (X3 (q, k)). rewrite in_app_iff. split.
      + intros [Hb'|[Hlv Hnb]]; [left; exact Hb'|right].
        apply (Permutation_in (q, k) P) in Hlv. apply in_app_iff in Hlv. destruct Hlv as [Hb|Hr]; [exfalso; exact (Hnb Hb) | exact Hr].
      + intros [Hb'|Hr]; [left; exact Hb'|right]. split.
        * apply (Permutation_in (q, k) (Permutation_sym P)). apply in_app_iff. right. exact Hr.
        * intros Hb. apply (HX q); apply list_elem_of_In; [apply in_map_iff; exists (q, k); split; [reflexivity | exact Hb] |].
          apply in_map_iff. exists (q, k). split; [reflexivity | exact Hr].
  Qed.

End LiveAlg.

Section Transport.
  Context (w : pmw).

  Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> fst W' <= fst W -> snd W <= snd W' -> eff MI A A' M M' W' F.
  Proof using AC SEGS L MI.
    intros A A' M M' W W' F E H1 H2. destruct E as [C B O FR D OI]. constructor; try assumption.
    intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn.
    - left; exact H. - right; left; exact H. - right; right; left; exact H.
    - right; right; right; left; exact H.
    - right; right; right; right; left. unfold W_of in *. cbn in *. lia.
    - right; right; right; right; right. exact H.
  Qed.

  Definition cblk (c : pmc) : list (Z * Z) :=
    umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
    ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
    ++ (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))])
    ++ (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]).

  Lemma c_blocks_split : forall c, c_blocks c = cblk c ++ c_tr c.
  Proof using. intros c. unfold c_blocks, cblk. rewrite <- !app_assoc. reflexivity. Qed.

  Definition fprot (c : pmc) (a : Z) : Prop :=
    zwin (w_sp0 w - 104) (w_sp0 w) a
    \/ (w_p w <= a < w_p w + PARSER_SIZE)
    \/ (w_cons w + 32 <= a < w_cons w + 40)
    \/ (w_words w <> 0 /\ zwin (w_words w) (w_words w + 4 * w_n w) a)
    \/ (exists b, In b (cblk c) /\ fst b <= a < fst b + snd b).

  Lemma cblk_live : forall A M model c b, PMX w A M model c -> In b (cblk c) -> In b (live MI A).
  Proof using AC SEGS L MI ST w.
    intros A M model c b X Hb. pose proof (x_live X) as PL.
    apply (Permutation_in b (Permutation_sym PL)). apply in_app_iff. right.
    rewrite c_blocks_split. apply in_app_iff. left. exact Hb.
  Qed.

  Definition set_tr (c : pmc) (tr : list (Z * Z)) : pmc :=
    {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
       c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := tr |}.

  Lemma fprot_facts : forall A M model c a,
    PMX w A M model c -> fprot c a ->
    0 <= a < 2 ^ 64 /\ ~ owned MI A a /\ M (Z_to_bv 64 a) <> None /\ ~ in_ranges (ly_img L) a
    /\ (w_sp w <= a \/ a < alloc_ceiling)
    /\ (forall (A' : AS MI) M' model', ainv MI A' M' model' -> (forall b, In b (cblk c) -> In b (live MI A')) ->
          (forall b, In b (w_L0 w) -> In b (live MI A')) -> ~ owned MI A' a).
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img w.
    intros A M model c a X HP. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    unfold fprot in HP. unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    assert (HI : forall x, alloc_ceiling <= x -> ~ in_ranges (ly_img L) x) by (intros x Hx Hi; pose proof (HLimg_lo _ Hi); lia).
    destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]].
    - unfold zwin in Hs. split; [lia|]. split; [apply (x_wown X); unfold zwin, w_sp0, PM_FRAME; lia|].
      split; [| split; [apply HI; lia | split; [left; lia | intros A' M' model' AI' _ _; apply (hi_unowned A' M' model'); [exact AI'|lia]]]].
      pose proof (x_wdef X (a - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (a - (w_sp w + 880 - w_STK w))) with a in D by lia. exact D.
    - split; [lia|]. split; [apply (hi_unowned A M model); [exact AI|lia]|].
      split; [| split; [apply HI; lia | split; [left; lia | intros A' M' model' AI' _ _; apply (hi_unowned A' M' model'); [exact AI'|lia]]]].
      pose proof (x_pdef X (a - w_p w) ltac:(unfold PARSER_SIZE; lia)) as D. replace (w_p w + (a - w_p w)) with a in D by lia. exact D.
    - split; [lia|]. split; [apply (hi_unowned A M model); [exact AI|lia]|].
      split; [| split; [apply HI; lia | split; [left; lia | intros A' M' model' AI' _ _; apply (hi_unowned A' M' model'); [exact AI'|lia]]]].
      pose proof (x_consd X (a - (w_cons w + 32)) ltac:(lia)) as D. replace (w_cons w + 32 + (a - (w_cons w + 32))) with a in D by lia. exact D.
    - destruct (Gw Hwz) as (W0 & W4 & Whi & Wpl & Wdj). unfold zwin in Hwd.
      assert (D : M (Z_to_bv 64 a) <> None).
      { pose proof (x_wbuf X Hwz (a - w_words w) ltac:(lia)) as D. replace (w_words w + (a - w_words w)) with a in D by lia. exact D. }
      destruct Wpl as [Whi2|(q & k & Hqk & Hq1 & Hq2)].
      + unfold w_sp0, PM_FRAME in Whi2. split; [lia|]. split; [apply (hi_unowned A M model); [exact AI|lia]|]. split; [exact D|].
        split; [apply HI; lia | split; [left; lia | intros A' M' model' AI' _ _; apply (hi_unowned A' M' model'); [exact AI'|lia]]].
      + assert (HinA : In (q, k) (live MI A)).
        { apply (Permutation_in (q, k) (Permutation_sym (x_live X))). apply in_app_iff. left. exact Hqk. }
        destruct (ai_live_block MI A M model q k AI HinA) as (_ & _ & Hq0 & Hqc & Hpay).
        destruct (Hpay a ltac:(lia)) as (Hno & Hni & _).
        split; [lia|]. split; [exact Hno|]. split; [exact D|]. split; [exact Hni|]. split; [right; lia|].
        intros A' M' model' AI' _ HL0. destruct (ai_live_block MI A' M' model' q k AI' (HL0 _ Hqk)) as (_ & _ & _ & _ & Hpay').
        exact (proj1 (Hpay' a ltac:(lia))).
    - assert (HinA : In b (live MI A)) by (eapply cblk_live; [exact X | exact Hb]).
      destruct b as [q k]. cbn in Hab.
      destruct (ai_live_block MI A M model q k AI HinA) as (_ & _ & Hq0 & Hqc & Hpay).
      destruct (Hpay a ltac:(lia)) as (Hno & Hni & Hd).
      split; [lia|]. split; [exact Hno|]. split; [exact Hd|]. split; [exact Hni|]. split; [right; lia|].
      intros A' M' model' AI' HK _. destruct (ai_live_block MI A' M' model' q k AI' (HK _ Hb)) as (_ & _ & _ & _ & Hpay').
      exact (proj1 (Hpay' a ltac:(lia))).
  Qed.

  Lemma umap_foot_cases : forall NS {V : Type} obj bl bc (ents : list (Z * (Z * V))) a,
    umap_foot NS obj bl bc ents a ->
    (obj <= a < obj + 40) \/ exists b, In b (umap_blocks NS bl bc ents) /\ fst b <= a < fst b + snd b.
  Proof using.
    intros NS V obj bl bc ents a [H|[[Hbc H]|(p & Hp & Ha)]]; [left; exact H | right | right].
    - exists (bl, 8 * bc). split; [| cbn; lia]. unfold umap_blocks. destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - apply in_map_iff in Hp. destruct Hp as ([p' kv] & Hp' & Hin). cbn in Hp'. subst p'.
      exists (p, NS). split; [| cbn; lia]. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, kv). split; [reflexivity | exact Hin].
  Qed.

  Lemma umapx_blocks_live : forall NS (V : Type) (nval : mem -> Z -> V -> Prop) (A : AS MI) M obj bl bc (ents : list (Z * (Z * V))) q k,
    umapx NS nval A M obj bl bc ents -> In (q, k) (umap_blocks NS bl bc ents) -> In (q, k) (live MI A).
  Proof using AC SEGS L MI.
    intros NS V nval A M obj bl bc ents q k U Hb.
    destruct U as [? ? ? ? ? ? Ublive ? ? ? ? ? ? ? Unode ?]. unfold umap_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
      destruct Ublive as [[? _]|[_ Hl]]; [lia | exact Hl].
    - apply in_map_iff in Hb. destruct Hb as ([q' [k' v']] & Hq & Hin). cbn in Hq. injection Hq as <- <-. exact (proj1 (Unode _ _ _ Hin)).
  Qed.

  Lemma umapx_hi_stores : forall NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      (HNS : 24 <= NS) (A : AS MI) M M' model obj bl bc (ents : list (Z * (Z * V))) (W : Z -> Prop),
    umapx NS nval A M obj bl bc ents -> ainv MI A M model -> stores_in W M M' ->
    (forall a, W a -> alloc_ceiling <= a /\ ~ (obj <= a < obj + 40)) ->
    umapx NS nval A M' obj bl bc ents.
  Proof using AC SEGS L MI.
    intros NS V nval nval_agree HNS A M M' model obj bl bc ents W U AI SI HW. pose proof ac_bounds_lit as Hcv.
    eapply (umapx_agree SEGS L MI NS V nval nval_agree HNS); [exact U | | intros q k _ Hl; exact Hl].
    intros a Ha. pose proof (u_obj_lo U) as Ulo. pose proof (u_obj_hi U) as Uhi.
    destruct (umap_foot_cases NS obj bl bc ents a Ha) as [Ho|(b & Hb & Hab)].
    - apply (proj1 SI). rewrite u64_of_Z by lia. intros Hw. exact (proj2 (HW _ Hw) Ho).
    - destruct b as [q k]. cbn in Hab.
      pose proof (umapx_blocks_live NS V nval A M obj bl bc ents q k U Hb) as Hl.
      destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & Hq0 & Hqc & _).
      apply (proj1 SI). rewrite u64_of_Z by lia. intros Hw. pose proof (proj1 (HW _ Hw)). lia.
  Qed.

  Lemma junk_junkL : forall A M model c (J : Z -> Prop) a,
    PMX w A M model c -> junk_ok MI A J -> J a -> junkL w a.
  Proof using AC SEGS L MI ST w.
    intros A M model c J a X HJ Ha. destruct (HJ a Ha) as (J1 & J2 & J3). split; [exact J1|]. split; [exact J2|].
    intros q k Hqk. apply (J3 q k). apply (Permutation_in (q, k) (Permutation_sym (x_live X))). apply in_app_iff. left. exact Hqk.
  Qed.
  Lemma junk_not_fprot : forall A M model c (J : Z -> Prop) a,
    PMX w A M model c -> junk_ok MI A J -> J a -> fprot c a -> False.
  Proof using AC SEGS L MI ST w.
    intros A M model c J a X HJ Ha HP. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    destruct (HJ a Ha) as (J1 & J2 & J3).
    unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin in *. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
    - destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). destruct Wpl as [Whi|(q' & k' & Hq' & Hq'1 & Hq'2)]; [lia|].
      apply (J3 q' k'); [| lia]. apply (Permutation_in (q', k') (Permutation_sym (x_live X))). apply in_app_iff. left. exact Hq'.
    - destruct b as [q' k']. cbn in Hab. exact (J3 q' k' (cblk_live _ _ _ _ _ X Hb) Hab).
  Qed.

  Lemma pmx_through : forall A M model c A' M' model' (S : Z) (F : Z -> Prop) (tr' : list (Z * Z)),
    PMX w A M model c ->
    ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
    eff MI A A' M M' (w_sp w - S, w_sp w) F -> 0 <= S <= w_STK w - PM_FRAME ->
    (forall a, F a -> fprot c a -> False) ->
    (forall a, F a -> PMF w a \/ zwin (w_sp w) (w_sp0 w) a) ->
    (forall a, F a -> zwin (w_sp w) (w_sp0 w) a -> M' (Z_to_bv 64 a) <> None) ->
    (forall b, In b (cblk c) -> In b (live MI A')) ->
    Permutation (live MI A') (w_L0 w ++ cblk c ++ tr') ->
    PMX w A' M' model' (set_tr c tr').
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLerr_img HLrw_relro HLerr_rw w.
    intros A M model c A' M' model' S F tr' X AI' MS' FS' FDS' EF HS HF HFsub HFdef HKEEP HPERM.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    assert (HL0' : forall b, In b (w_L0 w) -> In b (live MI A')).
    { intros b Hb. apply (Permutation_in b (Permutation_sym HPERM)). apply in_app_iff. left. exact Hb. }
    assert (HI : forall x, alloc_ceiling <= x -> ~ in_ranges (ly_img L) x) by (intros x Hx Hi; pose proof (HLimg_lo _ Hi); lia).
    assert (HFimg : forall a, F a -> ~ in_ranges (ly_img L) a).
    { intros a Ha. destruct (HFsub a Ha) as [[Hp|(_ & Hj & _)]|Hz]; [apply HI; unfold w_sp0, PM_FRAME in *; lia | exact Hj | apply HI; unfold zwin, w_sp0, PM_FRAME in *; lia]. }
    assert (AG : CRep.agree_on (fprot c) M M').
    { eapply agree_via_eff; [exact EF|]. intros a Ha.
      destruct (fprot_facts A M model c a X Ha) as (Hr & Ho & Hd & Hni & Hhi & Ho').
      split; [exact Hr|]. split; [exact Ho|]. split; [exact (Ho' A' M' model' AI' HKEEP HL0')|].
      split; [exact Hd|]. split; [intros Hf; exact (HF a Hf Ha)|]. split.
      - unfold W_of. cbn. intros Hw. destruct Hhi as [Hhi|Hhi]; [lia|]. unfold w_sp0, PM_FRAME in *. lia.
      - intros He. exact (Hni (HLerr_img _ He)). }
    assert (AGs : forall P, (forall a, P a -> fprot c a) -> CRep.agree_on P M M').
    { intros P HP a Ha. apply AG. apply HP. exact Ha. }
    assert (FLD : forall a k v, CRep.fld SEGS M a k v -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                  (forall x, a <= x < a + Z.of_nat k -> fprot c x) -> CRep.fld SEGS M' a k v).
    { intros a k v Hf Ha Hk HP. eapply fld_agree; [exact Ha | exact Hk | exact Hf |]. apply AGs. intros x Hx. apply HP. unfold zwin in Hx. exact Hx. }
    unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    constructor; cbn [set_tr c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr].
    all: unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    - exact AI'.
    - exact MS'.
    - rewrite FS'. exact (x_fs X).
    - rewrite FDS'. exact (x_fds X).
    - eapply sx_inv_via_eff; [exact (x_sx X) | exact AI | exact EF | exact (x_own_sx X) | exact (x_err_sx X) | exact HFimg | cbn; lia].
    - exact (x_sxh X).
    - eapply ro_clear_via_eff; [exact (x_roc X) | exact AI | exact EF | exact HFimg | cbn; lia].
    - assert (EF2 : eff MI A A' M M' (w_sp w + 880 - w_STK w, w_sp w + 880) (PMF w)).
      { eapply (eff_drop A A' M M' model' _ (PMF w) (fun a => F a /\ zwin (w_sp w) (w_sp w + 880) a)); [| exact AI' | |].
        - eapply eff_weaken; [eapply eff_widen; [exact EF | cbn; lia | cbn; lia] |].
          intros a Ha. destruct (HFsub a Ha) as [Hp|Hz]; [left; exact Hp | right; split; [exact Ha | exact Hz]].
        - intros a [_ Hz]. unfold W_of, zwin in *. cbn. lia.
        - intros a [Ha Hz] _. exact (HFdef a Ha Hz). }
      eapply eff_weaken.
      + eapply eff_trans; [exact (x_eff X) | exact EF2 |].
        intros a Ha. apply (hi_unowned A' M' model'); [exact AI'|]. unfold W_of in Ha. cbn in Ha. lia.
      + intros a [Ha|Ha]; exact Ha.
    - intros a Ho'. destruct (ef_own _ _ _ _ _ _ _ _ _ EF a Ho') as [Ho|[[Hni _]|Hf]].
      + exact (x_own_sx X a Ho).
      + intros Hs. exact (Hni (HLrw_img _ (sx_region_rw ST _ Hs))).
      + intros Hs. exact (HFimg a Hf (HLrw_img _ (sx_region_rw ST _ Hs))).
    - exact (x_err_sx X).
    - exact (x_win_sx X).
    - exact (x_geo X).
    - intros i Hi. pose proof (x_wdef X i Hi) as D0. unfold w_sp0, PM_FRAME in D0.
      destruct (ef_def _ _ _ _ _ _ _ _ _ EF (w_sp w + 880 - w_STK w + i) ltac:(lia) D0) as [H|[H|[H|H]]].
      + exact H.
      + exfalso. apply (x_wown X (w_sp w + 880 - w_STK w + i)); [unfold zwin, w_sp0, PM_FRAME; lia | exact H].
      + destruct (HFsub _ H) as [[Hp|(Hj & _)]|Hz]; [exfalso; lia | exfalso; lia | exact (HFdef _ H Hz)].
      + exfalso. pose proof (HLimg_lo _ (HLerr_img _ H)). lia.
    - intros a Ha. apply (hi_unowned A' M' model'); [exact AI'|]. unfold zwin, w_sp0, PM_FRAME in Ha. lia.
    - intros k Hk. pose proof (x_slots X k Hk) as SL.
      rewrite (rdn_agree_win SEGS M M'); [exact SL | unfold w_sp0, PM_FRAME; lia | cbn; unfold w_sp0, PM_FRAME; lia |].
      apply AGs. intros a Ha. left. unfold zwin, w_sp0, PM_FRAME in *. cbn in Ha. lia.
    - eapply mdef_agree; [exact (x_pdef X)|]. apply AGs. intros a Ha. right; left. unfold zwin, PARSER_SIZE in *. lia.
    - apply FLD; [exact (x_cons X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_user X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_hdrfn X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_insfn X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_hunk X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_words X) | unfold O_WORDS; lia | unfold O_WORDS; cbn; lia | intros x Hx; right; left; unfold O_WORDS in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_n X) | unfold O_N; lia | unfold O_N; cbn; lia | intros x Hx; right; left; unfold O_N in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_diag X) | unfold O_DIAG; lia | unfold O_DIAG; cbn; lia | intros x Hx; right; left; unfold O_DIAG in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | intros x Hx; right; left; unfold O_WIDX in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | intros x Hx; right; left; unfold O_ICOUNT in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | intros x Hx; right; left; unfold O_ENDIAN in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | intros x Hx; right; left; unfold O_FLAGS in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - exact (x_scal X).
    - apply FLD; [exact (x_consf X) | lia | cbn; lia | intros x Hx; right; right; left; cbn in Hx; lia].
    - eapply mdef_agree; [exact (x_consd X)|]. apply AGs. intros a Ha. right; right; left. unfold zwin in Ha. lia.
    - intros Hwz. eapply mdef_agree; [exact (x_wbuf X Hwz)|]. apply AGs. intros a Ha. right; right; right; left. split; [exact Hwz | exact Ha].
    - eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact (x_m1 X) | |].
      + intros a Ha. apply AG. destruct (umap_foot_cases 24 _ _ _ _ a Ha) as [Ho|(b & Hb & Hab)].
        * right; left. unfold O_M1 in Ho. unfold PARSER_SIZE. lia.
        * right; right; right; right. exists b. split; [| exact Hab]. unfold cblk. apply in_app_iff. left. exact Hb.
      + intros p n Hb _. apply HKEEP. unfold cblk. apply in_app_iff. left. exact Hb.
    - eapply (umapx_agree SEGS L MI 32 (Z * Z * Z)%type (nval32 SEGS) (nval32_agree SEGS) ltac:(lia)); [exact (x_m2 X) | |].
      + intros a Ha. apply AG. destruct (umap_foot_cases 32 _ _ _ _ a Ha) as [Ho|(b & Hb & Hab)].
        * right; left. unfold O_M2 in Ho. unfold PARSER_SIZE. lia.
        * right; right; right; right. exists b. split; [| exact Hab]. unfold cblk. rewrite !in_app_iff. right; left. exact Hb.
      + intros p n Hb _. apply HKEEP. unfold cblk. rewrite !in_app_iff. right; left. exact Hb.
    - eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact (x_m3 X) | |].
      + intros a Ha. apply AG. destruct (umap_foot_cases 24 _ _ _ _ a Ha) as [Ho|(b & Hb & Hab)].
        * right; left. unfold O_M3 in Ho. unfold PARSER_SIZE. lia.
        * right; right; right; right. exists b. split; [| exact Hab]. unfold cblk. rewrite !in_app_iff. right; right; left. exact Hb.
      + intros p n Hb _. apply HKEEP. unfold cblk. rewrite !in_app_iff. right; right; left. exact Hb.
    - eapply vec_opnd_relive; [eapply vec_opnd_frame; [exact (x_v1 X) | apply AGs; intros a Ha; right; left; unfold vec_opnd_fp, zwin, O_V1 in Ha; unfold PARSER_SIZE; lia] |].
      intros Hb Hin. apply HKEEP. unfold cblk, vec_opnd_blocks. rewrite !in_app_iff. right; right; right; left.
      destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity].
    - eapply vec32_relive; [eapply vec32_frame; [exact (x_v2 X) | apply AGs; intros a [Ha|[Hb Ha]]] |].
      + right; left. unfold zwin, O_V2 in Ha. unfold PARSER_SIZE. lia.
      + right; right; right; right. exists (t3a (c_v2 c), 4 * t3c (c_v2 c)). split.
        * unfold cblk. rewrite !in_app_iff. right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
        * cbn. pose proof (x_v2 X) as V. destruct V as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
      + intros Hb Hin. apply HKEEP. unfold cblk. rewrite !in_app_iff. right; right; right; right; left.
        destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
    - eapply vec32_relive; [eapply vec32_frame; [exact (x_v3 X) | apply AGs; intros a [Ha|[Hb Ha]]] |].
      + right; left. unfold zwin, O_V3 in Ha. unfold PARSER_SIZE. lia.
      + right; right; right; right. exists (t3a (c_v3 c), 4 * t3c (c_v3 c)). split.
        * unfold cblk. rewrite !in_app_iff. right; right; right; right; right. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
        * cbn. pose proof (x_v3 X) as V. destruct V as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
      + intros Hb Hin. apply HKEEP. unfold cblk. rewrite !in_app_iff. right; right; right; right; right.
        destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
    - rewrite c_blocks_split. cbn [c_tr]. replace (cblk (set_tr c tr')) with (cblk c) by reflexivity. exact HPERM.
    - pose proof (x_caps X) as (C1 & C2 & C3). rewrite (ef_caps _ _ _ _ _ _ _ _ _ EF), (ef_bigcap _ _ _ _ _ _ _ _ _ EF). repeat split; assumption.
  Qed.

  Lemma pmx_frame_stores : forall A M M' model c (W : Z -> Prop),
    PMX w A M model c -> stores_in W M M' ->
    (forall a, W a -> w_sp w <= a < w_sp0 w - 104) ->
    PMX w A M' model c.
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img w.
    intros A M M' model c W X SI HW. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    assert (HWhi : forall a, W a -> alloc_ceiling <= a /\ ~ in_ranges (ly_img L) a).
    { intros a Ha. pose proof (HW a Ha). unfold w_sp0, PM_FRAME in *. split; [lia|]. intros Hi. pose proof (HLimg_lo _ Hi). lia. }
    assert (AG : forall P : Z -> Prop, (forall a, P a -> fprot c a) -> CRep.agree_on P M M').
    { intros P HP. eapply stores_in_agree; [exact SI|]. intros a Ha.
      destruct (fprot_facts A M model c a X (HP a Ha)) as (Hr & _ & _ & _ & Hhi & _). split; [exact Hr|].
      intros HWa. pose proof (HW a HWa). pose proof (HP a Ha) as HF. unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin in *.
      destruct HF as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
      - destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). destruct (Wdj a Hwd) as [X1 _]. apply X1. lia.
      - destruct Hhi as [Hhi|Hhi]; [|lia].
        pose proof (cblk_live _ _ _ _ _ X Hb) as Hl. destruct b as [q k]. cbn in Hab.
        destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & _ & Hqc & _). lia. }
    assert (FLD : forall a k v, CRep.fld SEGS M a k v -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                  (forall x, a <= x < a + Z.of_nat k -> fprot c x) -> CRep.fld SEGS M' a k v).
    { intros a k v Hf Ha Hk HP. eapply fld_agree; [exact Ha | exact Hk | exact Hf |]. apply AG. intros x Hx. apply HP. unfold zwin in Hx. exact Hx. }
    unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    constructor; try (exact (x_ms X)); try (exact (x_fs X)); try (exact (x_fds X)); try (exact (x_sxh X));
      try (exact (x_own_sx X)); try (exact (x_err_sx X)); try (exact (x_win_sx X)); try (exact (x_geo X)); try (exact (x_scal X));
      try (exact (x_caps X)); try (exact (x_live X)).
    all: unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    - eapply stores_in_ainv; [exact AI | exact SI |]. intros a Ha. apply (hi_unowned A M model); [exact AI|]. apply HWhi; exact Ha.
    - eapply stores_in_sx; [exact (x_sx X) | exact SI |]. intros a Ha. destruct (HWhi a Ha) as [_ Hni].
      split; intros Hs; apply Hni; [exact (HLrw_img _ (sx_region_rw ST _ Hs)) | exact (HLrelro_img _ Hs)].
    - eapply ro_clear_frame; [exact (x_roc X) | eapply stores_in_frame_eq; [exact SI | intros a Ha; exact Ha] |].
      intros a (Hi & _) HWa. exact (proj2 (HWhi _ HWa) Hi).
    - eapply eff_weaken; [eapply eff_trans; [exact (x_eff X) | | intros a Ha; apply (hi_unowned A M model); [exact AI | unfold W_of in Ha; cbn in Ha; lia]] |].
      + apply (eff_store MI A M M' _ (fun _ => False)); [| exact (proj2 SI)]. intros a _ HWn. apply (proj1 SI). intros Hz. apply HWn.
        pose proof (HW _ Hz). unfold W_of. cbn. pose proof (bv_unsigned_in_range 64 a). lia.
      + intros a [Ha|[]]; exact Ha.
    - eapply stores_in_mdef; [exact SI | exact (x_wdef X)].
    - exact (x_wown X).
    - intros k Hk. pose proof (x_slots X k Hk) as SL. unfold w_sp0, PM_FRAME in SL.
      rewrite (rdn_agree_win SEGS M M'); [exact SL | lia | cbn; lia |]. apply AG. intros a Ha. left. unfold zwin, w_sp0, PM_FRAME in *. cbn in Ha. lia.
    - eapply mdef_agree; [exact (x_pdef X)|]. apply AG. intros a Ha. right; left. unfold zwin, PARSER_SIZE in *. lia.
    - apply FLD; [exact (x_cons X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_user X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_hdrfn X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_insfn X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_hunk X) | lia | cbn; lia | intros x Hx; right; left; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_words X) | unfold O_WORDS; lia | unfold O_WORDS; cbn; lia | intros x Hx; right; left; unfold O_WORDS in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_n X) | unfold O_N; lia | unfold O_N; cbn; lia | intros x Hx; right; left; unfold O_N in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_diag X) | unfold O_DIAG; lia | unfold O_DIAG; cbn; lia | intros x Hx; right; left; unfold O_DIAG in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | intros x Hx; right; left; unfold O_WIDX in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | intros x Hx; right; left; unfold O_ICOUNT in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | intros x Hx; right; left; unfold O_ENDIAN in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | intros x Hx; right; left; unfold O_FLAGS in Hx; unfold PARSER_SIZE; cbn in Hx; lia].
    - apply FLD; [exact (x_consf X) | lia | cbn; lia | intros x Hx; right; right; left; cbn in Hx; lia].
    - eapply mdef_agree; [exact (x_consd X)|]. apply AG. intros a Ha. right; right; left. unfold zwin in Ha. lia.
    - intros Hwz. eapply mdef_agree; [exact (x_wbuf X Hwz)|]. apply AG. intros a Ha. right; right; right; left. split; [exact Hwz | exact Ha].
    - eapply (umapx_hi_stores 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact (x_m1 X) | exact AI | exact SI |].
      intros a Ha. split; [apply HWhi; exact Ha|]. pose proof (HW a Ha). unfold O_M1. lia.
    - eapply (umapx_hi_stores 32 (Z * Z * Z)%type (nval32 SEGS) (nval32_agree SEGS) ltac:(lia)); [exact (x_m2 X) | exact AI | exact SI |].
      intros a Ha. split; [apply HWhi; exact Ha|]. pose proof (HW a Ha). unfold O_M2. lia.
    - eapply (umapx_hi_stores 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact (x_m3 X) | exact AI | exact SI |].
      intros a Ha. split; [apply HWhi; exact Ha|]. pose proof (HW a Ha). unfold O_M3. lia.
    - eapply vec_opnd_frame; [exact (x_v1 X) | apply AG; intros a Ha; right; left; unfold vec_opnd_fp, zwin, O_V1 in Ha; unfold PARSER_SIZE; lia].
    - eapply vec32_frame; [exact (x_v2 X) | apply AG; intros a [Ha|[Hb Ha]]].
      + right; left. unfold zwin, O_V2 in Ha. unfold PARSER_SIZE. lia.
      + right; right; right; right. exists (t3a (c_v2 c), 4 * t3c (c_v2 c)). split.
        * unfold cblk. rewrite !in_app_iff. right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
        * cbn. pose proof (x_v2 X) as V. destruct V as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
    - eapply vec32_frame; [exact (x_v3 X) | apply AG; intros a [Ha|[Hb Ha]]].
      + right; left. unfold zwin, O_V3 in Ha. unfold PARSER_SIZE. lia.
      + right; right; right; right. exists (t3a (c_v3 c), 4 * t3c (c_v3 c)). split.
        * unfold cblk. rewrite !in_app_iff. right; right; right; right; right. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
        * cbn. pose proof (x_v3 X) as V. destruct V as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
  Qed.

  Definition set_scal (c : pmc) (widx icount endian reqconv : Z) : pmc :=
    {| c_widx := widx; c_icount := icount; c_endian := endian; c_reqconv := reqconv;
       c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.
  Definition scal_win (a : Z) : Prop := w_p w + O_WIDX <= a < w_p w + O_FLAGS + 2.

  Lemma pmx_stores : forall A M M' model c (W : Z -> Prop) (widx icount endian reqconv : Z),
    PMX w A M model c -> stores_in W M M' ->
    (forall a, W a -> (w_sp0 w - w_STK w <= a < w_sp0 w - 104) \/ scal_win a) ->
    CRep.fld SEGS M' (w_p w + O_WIDX) 8 widx -> CRep.fld SEGS M' (w_p w + O_ICOUNT) 8 icount ->
    CRep.fld SEGS M' (w_p w + O_ENDIAN) 4 endian -> CRep.fld SEGS M' (w_p w + O_FLAGS) 2 reqconv ->
    0 <= widx <= w_n w -> 0 <= icount <= widx -> 0 <= endian < 2 ^ 32 -> (reqconv = 0 \/ reqconv = 1) ->
    PMX w A M' model (set_scal c widx icount endian reqconv).
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img w.
    intros A M M' model c W widx icount endian reqconv X SI HW Fw Fi Fe Ff Bw Bi Be Bf.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    assert (HWhi : forall a, W a -> alloc_ceiling <= a /\ ~ in_ranges (ly_img L) a).
    { intros a Ha. pose proof (HW a Ha). unfold scal_win, w_sp0, PM_FRAME, O_WIDX, O_FLAGS in *. split; [lia|]. intros Hi. pose proof (HLimg_lo _ Hi). lia. }
    assert (AG : forall P : Z -> Prop, (forall a, P a -> fprot c a /\ ~ scal_win a) -> CRep.agree_on P M M').
    { intros P HP. eapply stores_in_agree; [exact SI|]. intros a Ha. destruct (HP a Ha) as [HF HNS].
      destruct (fprot_facts A M model c a X HF) as (Hr & _ & _ & _ & Hhi & _). split; [exact Hr|].
      intros HWa. destruct (HW a HWa) as [Hwa|Hwa]; [|exact (HNS Hwa)]. unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin in *.
      destruct HF as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
      - destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). destruct (Wdj a Hwd) as [X1 _]. apply X1. lia.
      - destruct Hhi as [Hhi|Hhi]; [|lia].
        pose proof (cblk_live _ _ _ _ _ X Hb) as Hl. destruct b as [q k]. cbn in Hab.
        destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & _ & Hqc & _). lia. }
    assert (FLD : forall a k v, CRep.fld SEGS M a k v -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                  (forall x, a <= x < a + Z.of_nat k -> fprot c x /\ ~ scal_win x) -> CRep.fld SEGS M' a k v).
    { intros a k v Hf Ha Hk HP. eapply fld_agree; [exact Ha | exact Hk | exact Hf |]. apply AG. intros x Hx. apply HP. unfold zwin in Hx. exact Hx. }
    unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    constructor; try (exact (x_ms X)); try (exact (x_fs X)); try (exact (x_fds X)); try (exact (x_sxh X));
      try (exact (x_own_sx X)); try (exact (x_err_sx X)); try (exact (x_win_sx X)); try (exact (x_geo X));
      try (exact (x_caps X)); try (exact (x_live X)); try (exact Fw); try (exact Fi); try (exact Fe); try (exact Ff).
    all: unfold w_sp0, PARSER_SIZE, PM_FRAME in *; cbn [set_scal c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr].
    - eapply stores_in_ainv; [exact AI | exact SI |]. intros a Ha. apply (hi_unowned A M model); [exact AI|]. apply HWhi; exact Ha.
    - eapply stores_in_sx; [exact (x_sx X) | exact SI |]. intros a Ha. destruct (HWhi a Ha) as [_ Hni].
      split; intros Hs; apply Hni; [exact (HLrw_img _ (sx_region_rw ST _ Hs)) | exact (HLrelro_img _ Hs)].
    - eapply ro_clear_frame; [exact (x_roc X) | eapply stores_in_frame_eq; [exact SI | intros a Ha; exact Ha] |].
      intros a (Hi & _) HWa. exact (proj2 (HWhi _ HWa) Hi).
    - eapply eff_weaken; [eapply eff_trans; [exact (x_eff X) | | intros a Ha; apply (hi_unowned A M model); [exact AI | unfold W_of in Ha; cbn in Ha; lia]] |].
      + apply (eff_store MI A M M' _ (PMF w)); [| exact (proj2 SI)]. intros a HnF HWn. apply (proj1 SI). intros Hz.
        destruct (HW _ Hz) as [Hwa|Hwa].
        * apply HWn. unfold W_of. cbn. pose proof (bv_unsigned_in_range 64 a). lia.
        * apply HnF. left. unfold scal_win, O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
      + intros a [Ha|Ha]; exact Ha.
    - eapply stores_in_mdef; [exact SI | exact (x_wdef X)].
    - exact (x_wown X).
    - intros k Hk. pose proof (x_slots X k Hk) as SL. unfold w_sp0, PM_FRAME in SL.
      rewrite (rdn_agree_win SEGS M M'); [exact SL | lia | cbn; lia |]. apply AG. intros a Ha. cbn in Ha.
      split; [left; unfold zwin, w_sp0, PM_FRAME in *; lia | unfold zwin, scal_win, O_WIDX in *; lia].
    - eapply stores_in_mdef; [exact SI | exact (x_pdef X)].
    - apply FLD; [exact (x_cons X) | lia | cbn; lia | intros x Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_user X) | lia | cbn; lia | intros x Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_hdrfn X) | lia | cbn; lia | intros x Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_insfn X) | lia | cbn; lia | intros x Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_hunk X) | lia | cbn; lia | intros x Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_words X) | unfold O_WORDS; lia | unfold O_WORDS; cbn; lia | intros x Hx; unfold O_WORDS in Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_n X) | unfold O_N; lia | unfold O_N; cbn; lia | intros x Hx; unfold O_N in Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - apply FLD; [exact (x_diag X) | unfold O_DIAG; lia | unfold O_DIAG; cbn; lia | intros x Hx; unfold O_DIAG in Hx; cbn in Hx; split; [right; left; unfold PARSER_SIZE; lia | unfold scal_win, O_WIDX; lia]].
    - cbn. lia.
    - apply FLD; [exact (x_consf X) | lia | cbn; lia | intros x Hx; cbn in Hx; unfold scal_win, O_WIDX, O_FLAGS, PARSER_SIZE, apart in *; split; [right; right; left; lia | lia]].
    - eapply mdef_agree; [exact (x_consd X)|]. apply AG. intros a Ha. unfold zwin, scal_win, O_WIDX, O_FLAGS, PARSER_SIZE, apart in *. split; [right; right; left; lia | lia].
    - intros Hwz. eapply stores_in_mdef; [exact SI | exact (x_wbuf X Hwz)].
    - eapply (umapx_hi_stores 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact (x_m1 X) | exact AI | exact SI |].
      intros a Ha. split; [apply HWhi; exact Ha|]. destruct (HW a Ha); unfold scal_win, O_WIDX, O_FLAGS, O_M1 in *; lia.
    - eapply (umapx_hi_stores 32 (Z * Z * Z)%type (nval32 SEGS) (nval32_agree SEGS) ltac:(lia)); [exact (x_m2 X) | exact AI | exact SI |].
      intros a Ha. split; [apply HWhi; exact Ha|]. destruct (HW a Ha); unfold scal_win, O_WIDX, O_FLAGS, O_M2 in *; lia.
    - eapply (umapx_hi_stores 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact (x_m3 X) | exact AI | exact SI |].
      intros a Ha. split; [apply HWhi; exact Ha|]. destruct (HW a Ha); unfold scal_win, O_WIDX, O_FLAGS, O_M3 in *; lia.
    - eapply vec_opnd_frame; [exact (x_v1 X) | apply AG; intros a Ha; unfold vec_opnd_fp, zwin, O_V1, scal_win, O_WIDX, O_FLAGS in *; split; [right; left; unfold PARSER_SIZE; lia | lia]].
    - eapply vec32_frame; [exact (x_v2 X) | apply AG; intros a [Ha|[Hb Ha]]].
      + unfold zwin, O_V2, scal_win, O_WIDX, O_FLAGS in *. split; [right; left; unfold PARSER_SIZE; lia | lia].
      + split.
        * right; right; right; right. exists (t3a (c_v2 c), 4 * t3c (c_v2 c)). split.
          -- unfold cblk. rewrite !in_app_iff. right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
          -- cbn. pose proof (x_v2 X) as V. destruct V as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
        * pose proof (x_v2 X) as V. destruct V as (_ & _ & _ & Hlen & Hblk & _). unfold zwin, scal_win, O_WIDX in *.
          destruct Hblk as [[? _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hqc & _). lia.
    - eapply vec32_frame; [exact (x_v3 X) | apply AG; intros a [Ha|[Hb Ha]]].
      + unfold zwin, O_V3, scal_win, O_WIDX, O_FLAGS in *. split; [right; left; unfold PARSER_SIZE; lia | lia].
      + split.
        * right; right; right; right. exists (t3a (c_v3 c), 4 * t3c (c_v3 c)). split.
          -- unfold cblk. rewrite !in_app_iff. right; right; right; right; right. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
          -- cbn. pose proof (x_v3 X) as V. destruct V as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
        * pose proof (x_v3 X) as V. destruct V as (_ & _ & _ & Hlen & Hblk & _). unfold zwin, scal_win, O_WIDX in *.
          destruct Hblk as [[? _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hqc & _). lia.
  Qed.

  Lemma pmx_above_sp_frame : forall A M model c a n,
    PMX w A M model c -> w_sp w <= a -> a + n <= w_sp0 w -> above_sp MI A (w_sp w) a n.
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img w.
    intros A M model c a n X Ha Hn. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    split; [lia|]. split; [lia|]. intros i Hi. apply (hi_unowned A M model); [exact (x_ai X) | lia].
  Qed.

  Lemma pmx_frame_keep : forall A M model c A' M' (S : Z) (F : Z -> Prop) (P : Z -> Prop),
    PMX w A M model c -> eff MI A A' M M' (w_sp w - S, w_sp w) F -> 0 <= S ->
    (forall a, P a -> w_sp w <= a < w_sp0 w /\ ~ F a) -> CRep.agree_on P M M'.
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLerr_img w.
    intros A M model c A' M' S F P X EF HS HP. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    eapply agree_via_eff; [exact EF|]. intros a Ha. destruct (HP a Ha) as [Hr Hf].
    assert (HI : ~ in_ranges (ly_img L) a) by (intros Hi; pose proof (HLimg_lo _ Hi); lia).
    split; [lia|]. split; [apply (hi_unowned A M model); [exact (x_ai X) | lia]|].
    split; [intros Ho'; destruct (ef_own _ _ _ _ _ _ _ _ _ EF a Ho') as [Ho|[[Hni [_ Hn]]|Hfa]];
            [exact (hi_unowned A M model a (x_ai X) ltac:(lia) Ho) | | exact (Hf Hfa)] |].
    { pose proof (x_wdef X (a - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D. unfold w_sp0, PM_FRAME in D.
      replace (w_sp w + 880 - w_STK w + (a - (w_sp w + 880 - w_STK w))) with a in D by lia. exact (D Hn). }
    split; [| split; [exact Hf | split; [unfold W_of; cbn; lia | intros He; exact (HI (HLerr_img _ He))]]].
    pose proof (x_wdef X (a - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D. unfold w_sp0, PM_FRAME in D.
    replace (w_sp w + 880 - w_STK w + (a - (w_sp w + 880 - w_STK w))) with a in D by lia. exact D.
  Qed.

  Lemma nodup_app_ne : forall (l1 l2 : list (Z * Z)) p q,
    NoDup (map fst (l1 ++ l2)) -> In p (map fst l1) -> In q (map fst l2) -> p <> q.
  Proof using.
    intros l1 l2 p q N Hp Hq ->. rewrite map_app in N. apply (proj1 (list_relations.list.NoDup_app _ _)) in N.
    destruct N as (_ & Hx & _). apply (Hx q); apply list_elem_of_In; assumption.
  Qed.

  Lemma live_payload_disjoint : forall (A : AS MI) M model p n q k a,
    ainv MI A M model -> In (p, n) (live MI A) -> In (q, k) (live MI A) -> p <> q ->
    p <= a < p + n -> ~ (q <= a < q + k).
  Proof using AC SEGS L MI.
    intros A M model p n q k a AI Hp Hq Hne Ha Hb.
    destruct (ai_live_disjoint MI A M model p n q k AI Hp Hq Hne); lia.
  Qed.

  Lemma pmx_ds : forall A M model c A' M' model' (S ds : Z) (B B' rest : list (Z * Z)) (J Xf : Z -> Prop),
    PMX w A M model c -> c_tr c = B ++ rest ->
    ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
    eff MI A A' M M' (w_sp w - S, w_sp w) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a \/ Xf a) -> 0 <= S <= w_STK w - PM_FRAME ->
    w_sp w <= ds -> ds + DS_SIZE <= w_sp0 w - 104 ->
    junk_ok MI A J ->
    (forall a, Xf a -> w_sp w <= a < w_sp0 w - 104 /\ M' (Z_to_bv 64 a) <> None) ->
    mdef M' ds DS_SIZE ->
    blk_xfer B B' (live MI A) (live MI A') -> Zlength B <= 1 -> Zlength B' <= 1 ->
    PMX w A' M' model' (set_tr c (B' ++ rest)).
  Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLerr_img HLrw_relro HLerr_rw w.
    intros A M model c A' M' model' S ds B B' rest J Xf X Htr AI' MS' FS' FDS' EF HS Hds0 Hds1 HJ HXf Hdsdef XFER HB HB'.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    pose proof (x_live X) as PL. rewrite c_blocks_split, Htr in PL.

    set (R := w_L0 w ++ cblk c ++ rest).
    assert (PLB : Permutation (live MI A) (B ++ R)).
    { eapply Permutation_trans; [exact PL|]. unfold R. rewrite !app_assoc.
      apply Permutation_app; [| apply Permutation_refl].
      eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_refl. }
    pose proof (ai_live_nodup MI A M model AI) as ND. pose proof (ai_live_nodup MI A' M' model' AI') as ND'.
    destruct (blk_xfer_small B B' R (live MI A) (live MI A') HB HB' XFER PLB ND ND') as [PL' FR'].
    assert (HR' : forall b, In b R -> In b (live MI A')).
    { intros b Hb. apply (Permutation_in b (Permutation_sym PL')). apply in_app_iff. right. exact Hb. }
    assert (HRA : forall b, In b R -> In b (live MI A)).
    { intros b Hb. apply (Permutation_in b (Permutation_sym PLB)). apply in_app_iff. right. exact Hb. }
    assert (HBA : forall b, In b B -> In b (live MI A)).
    { intros b Hb. apply (Permutation_in b (Permutation_sym PLB)). apply in_app_iff. left. exact Hb. }
    assert (HB'A : forall b, In b B' -> In b (live MI A')).
    { intros b Hb. apply (Permutation_in b (Permutation_sym PL')). apply in_app_iff. left. exact Hb. }
    pose proof (perm_nodup_fst _ _ PLB ND) as NDB. pose proof (perm_nodup_fst _ _ PL' ND') as NDB'.
    unfold w_sp0, PM_FRAME in *.
    assert (HI : forall x, alloc_ceiling <= x -> ~ in_ranges (ly_img L) x) by (intros x Hx Hi; pose proof (HLimg_lo _ Hi); lia).
    eapply (pmx_through A M model c A' M' model' S _ (B' ++ rest) X AI' MS' FS' FDS' EF HS).
    -
      intros a HF HP. destruct (fprot_facts A M model c a X HP) as (_ & Ho & Hd & _ & Hhi & Ho').
      assert (CASEB : forall q k, In (q, k) B -> q <= a < q + k -> False).
      { intros q k Hqk Ha. destruct (ai_live_block MI A M model q k AI (HBA _ Hqk)) as (_ & _ & Hq0 & Hqc & _).
        unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE in HP. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; unfold zwin in *; [lia | lia | lia | |].
        - destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). destruct Wpl as [Whi|(q' & k' & Hq' & Hq'1 & Hq'2)]; [lia|].
          apply (live_payload_disjoint A M model q k q' k' a AI (HBA _ Hqk) (HRA _ ltac:(unfold R; rewrite !in_app_iff; left; exact Hq'))); try lia.
          apply (nodup_app_ne B R q q' NDB); [apply in_map_iff; exists (q, k); split; [reflexivity|exact Hqk] |].
          apply in_map_iff. exists (q', k'). split; [reflexivity|]. unfold R. rewrite !in_app_iff. left. exact Hq'.
        - destruct b as [q' k']. cbn in Hab.
          apply (live_payload_disjoint A M model q k q' k' a AI (HBA _ Hqk) (HRA _ ltac:(unfold R; rewrite !in_app_iff; right; left; exact Hb))); try lia.
          apply (nodup_app_ne B R q q' NDB); [apply in_map_iff; exists (q, k); split; [reflexivity|exact Hqk] |].
          apply in_map_iff. exists (q', k'). split; [reflexivity|]. unfold R. rewrite !in_app_iff. right; left. exact Hb. }
      assert (CASEB' : forall q k, In (q, k) B' -> q <= a < q + k -> False).
      { intros q k Hqk Ha. destruct (ai_live_block MI A' M' model' q k AI' (HB'A _ Hqk)) as (_ & _ & Hq0 & Hqc & _).
        unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE in HP. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; unfold zwin in *; [lia | lia | lia | |].
        - destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). destruct Wpl as [Whi|(q' & k' & Hq' & Hq'1 & Hq'2)]; [lia|].
          apply (live_payload_disjoint A' M' model' q k q' k' a AI' (HB'A _ Hqk) (HR' _ ltac:(unfold R; rewrite !in_app_iff; left; exact Hq'))); try lia.
          intros ->. apply (FR' _ Hqk). apply in_map_iff. exists (q', k'). split; [reflexivity|]. unfold R. rewrite !in_app_iff. left. exact Hq'.
        - destruct b as [q' k']. cbn in Hab.
          apply (live_payload_disjoint A' M' model' q k q' k' a AI' (HB'A _ Hqk) (HR' _ ltac:(unfold R; rewrite !in_app_iff; right; left; exact Hb))); try lia.
          intros ->. apply (FR' _ Hqk). apply in_map_iff. exists (q', k'). split; [reflexivity|]. unfold R. rewrite !in_app_iff. right; left. exact Hb. }
      destruct HF as [[Hobj|(q & k & Hqk & Ha)]|[[Hobj|(q & k & Hqk & Ha)]|[Hj|Hx]]].
      + unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin, DS_SIZE in *. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
        * destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). exact (proj1 (Wdj a Hwd) ltac:(lia)).
        * destruct Hhi as [Hhi|Hhi]; [|lia]. destruct b as [q k]. cbn in Hab.
          destruct (ai_live_block MI A M model q k AI (cblk_live _ _ _ _ _ X Hb)) as (_ & _ & _ & Hqc & _). lia.
      + exact (CASEB q k Hqk Ha).
      + unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin, DS_SIZE in *. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
        * destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). exact (proj1 (Wdj a Hwd) ltac:(lia)).
        * destruct Hhi as [Hhi|Hhi]; [|lia]. destruct b as [q k]. cbn in Hab.
          destruct (ai_live_block MI A M model q k AI (cblk_live _ _ _ _ _ X Hb)) as (_ & _ & _ & Hqc & _). lia.
      + exact (CASEB' q k Hqk Ha).
      + destruct (HJ a Hj) as (J1 & J2 & J3).
        unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin in *. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
        * destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). destruct Wpl as [Whi|(q' & k' & Hq' & Hq'1 & Hq'2)]; [lia|].
          exact (J3 q' k' (HRA _ ltac:(unfold R; rewrite !in_app_iff; left; exact Hq')) ltac:(lia)).
        * destruct b as [q' k']. cbn in Hab. exact (J3 q' k' (cblk_live _ _ _ _ _ X Hb) Hab).
      + destruct (HXf a Hx) as [Hr _]. unfold fprot, w_sp0, PM_FRAME, PARSER_SIZE, zwin in *. destruct HP as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; try lia.
        * destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). exact (proj1 (Wdj a Hwd) ltac:(lia)).
        * destruct Hhi as [Hhi|Hhi]; [|lia]. destruct b as [q k]. cbn in Hab.
          destruct (ai_live_block MI A M model q k AI (cblk_live _ _ _ _ _ X Hb)) as (_ & _ & _ & Hqc & _). lia.
    -
      intros a HF.
      assert (JB : forall q k, In (q, k) B -> q <= a < q + k -> junkL w a).
      { intros q k Hqk Ha. destruct (ai_live_block MI A M model q k AI (HBA _ Hqk)) as (_ & _ & Hq0 & Hqc & Hpay).
        destruct (Hpay a Ha) as (_ & Hni & _). split; [lia|]. split; [exact Hni|]. intros q' k' Hq'.
        apply (live_payload_disjoint A M model q k q' k' a AI (HBA _ Hqk) (HRA _ ltac:(unfold R; rewrite !in_app_iff; left; exact Hq'))); [|exact Ha].
        apply (nodup_app_ne B R q q' NDB); [apply in_map_iff; exists (q, k); split; [reflexivity|exact Hqk] |].
        apply in_map_iff. exists (q', k'). split; [reflexivity|]. unfold R. rewrite !in_app_iff. left. exact Hq'. }
      assert (JB' : forall q k, In (q, k) B' -> q <= a < q + k -> junkL w a).
      { intros q k Hqk Ha. destruct (ai_live_block MI A' M' model' q k AI' (HB'A _ Hqk)) as (_ & _ & Hq0 & Hqc & Hpay).
        destruct (Hpay a Ha) as (_ & Hni & _). split; [lia|]. split; [exact Hni|]. intros q' k' Hq'.
        apply (live_payload_disjoint A' M' model' q k q' k' a AI' (HB'A _ Hqk) (HR' _ ltac:(unfold R; rewrite !in_app_iff; left; exact Hq'))); [|exact Ha].
        intros ->. apply (FR' _ Hqk). apply in_map_iff. exists (q', k'). split; [reflexivity|]. unfold R. rewrite !in_app_iff. left. exact Hq'. }
      destruct HF as [[Hobj|(q & k & Hqk & Ha)]|[[Hobj|(q & k & Hqk & Ha)]|[Hj|Hx]]].
      + right. unfold zwin, DS_SIZE, w_sp0, PM_FRAME in *. lia.
      + left. right. exact (JB q k Hqk Ha).
      + right. unfold zwin, DS_SIZE, w_sp0, PM_FRAME in *. lia.
      + left. right. exact (JB' q k Hqk Ha).
      + left. right. destruct (HJ a Hj) as (J1 & J2 & J3). split; [exact J1|]. split; [exact J2|].
        intros q' k' Hq'. exact (J3 q' k' (HRA _ ltac:(unfold R; rewrite !in_app_iff; left; exact Hq'))).
      + right. destruct (HXf a Hx) as [Hr _]. unfold zwin, w_sp0, PM_FRAME in *. lia.
    -
      intros a HF Hz. unfold zwin, w_sp0, PM_FRAME in Hz.
      destruct HF as [[Hobj|(q & k & Hqk & Ha)]|[[Hobj|(q & k & Hqk & Ha)]|[Hj|Hx]]].
      + unfold zwin in Hobj. pose proof (Hdsdef (a - ds) ltac:(lia)) as D. replace (ds + (a - ds)) with a in D by lia. exact D.
      + exfalso. destruct (ai_live_block MI A M model q k AI (HBA _ Hqk)) as (_ & _ & Hq0 & Hqc & _). lia.
      + unfold zwin in Hobj. pose proof (Hdsdef (a - ds) ltac:(lia)) as D. replace (ds + (a - ds)) with a in D by lia. exact D.
      + exfalso. destruct (ai_live_block MI A' M' model' q k AI' (HB'A _ Hqk)) as (_ & _ & Hq0 & Hqc & _). lia.
      + exfalso. destruct (HJ a Hj) as (J1 & _). lia.
      + exact (proj2 (HXf a Hx)).
    - intros b Hb. apply HR'. unfold R. rewrite !in_app_iff. right; left. exact Hb.
    - eapply Permutation_trans; [exact PL'|]. unfold R. rewrite <- ?app_assoc.
      eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_app_swap_app.
  Qed.

  Lemma pmx_callB : forall A M model c R (ret S : Z),
    PMX w A M model c -> call_regs L R (w_sp w) ret -> 0 <= S <= w_STK w - PM_FRAME ->
    callB MI ST A (w_s w) R M model (w_sp w) ret S.
  Proof using AC SEGS L MI ST w.
    intros A M model c R ret S X CR HS. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    constructor.
    - exact (x_ai X). - exact (x_ms X). - exact (pmx_img_ro_clear w _ _ _ _ X). - exact (x_sx X). - exact (x_sxh X).
    - exact CR. - lia.
    - unfold stack_room. pose proof (x_wdef X) as WD. unfold w_sp0, PM_FRAME in WD.
      replace (w_sp w - S) with ((w_sp w + 880 - w_STK w) + (w_STK w - 880 - S)) by lia.
      apply (mdef_store_ok_off SEGS M _ (w_STK w)); [exact WD | lia | lia | lia | rewrite Z2Nat.id by lia; lia].
    - intros a Ha. split.
      + apply (x_wown X). unfold w_sp0, PM_FRAME, zwin in *. lia.
      + apply (x_win_sx X). unfold w_sp0, PM_FRAME, zwin in *. lia.
    - exact (x_own_sx X).
    - exact (x_err_sx X).
  Qed.
End Transport.

Section Budget.

  Hypothesis HC24 : size_class MI 24 <= 2.
  Hypothesis HC32 : size_class MI 32 <= 2 /\ size_class MI 24 <> size_class MI 32.
  Hypothesis HBIG : 4096 <= BIG MI.
  Hypothesis RB : round_big_law MI.

  #[local] Notation cnt l c := (count_class_f (size_class MI) (BIG MI) l c).
  #[local] Notation bigb l := (big_bytes_f (round_big MI) (BIG MI) l).

  Lemma cnt_app : forall l1 l2 c, cnt (l1 ++ l2) c = cnt l1 c + cnt l2 c.
  Proof using AC SEGS L MI. intros. apply count_class_f_app. Qed.
  Lemma bigb_app : forall l1 l2, bigb (l1 ++ l2) = bigb l1 + bigb l2.
  Proof using AC SEGS L MI. intros. apply big_bytes_f_app. Qed.

  Lemma cnt_le_len : forall l c, cnt l c <= Zlength l.
  Proof using AC SEGS L MI.
    intros l c. induction l as [|[q k] l IH]; [unfold Zlength; cbn; lia|]. cbn [count_class_f]. rewrite Zlength_cons.
    destruct (_ && _); lia.
  Qed.

  Lemma bigb_le : forall l (bound : Z),
    (forall b, In b l -> 0 <= snd b) -> fold_right (fun b acc => (if BIG MI <=? snd b then snd b + 4116 else 0) + acc) 0 l <= bound -> bigb l <= bound.
  Proof using AC SEGS L MI RB.
    intros l bound Hl Hb. revert bound Hb. induction l as [|[q k] l IH]; intros bound Hb; cbn in *; [lia|].
    assert (Hk : 0 <= k) by (pose proof (Hl (q, k) (or_introl eq_refl)); cbn in *; lia).
    specialize (IH ltac:(intros b Hb'; apply Hl; right; exact Hb') (bound - (if BIG MI <=? k then k + 4116 else 0)) ltac:(lia)).
    destruct (Z.leb_spec (BIG MI) k); [pose proof (RB k Hk); lia | lia].
  Qed.

  Lemma bigb_nodes : forall {V : Type} NS (ents : list (Z * (Z * V))),
    NS = 24 \/ NS = 32 -> bigb (map (fun e => (fst e, NS)) ents) = 0.
  Proof using AC SEGS L MI HBIG.
    intros V NS ents HNS. induction ents as [|[q kv] ents IH]; [reflexivity|]. cbn [map fst big_bytes_f].
    destruct (Z.leb_spec (BIG MI) NS); [destruct HNS; lia|]. lia.
  Qed.

  Lemma cnt_nodes_eq : forall {V : Type} NS (ents : list (Z * (Z * V))) c,
    cnt (map (fun e => (fst e, NS)) ents) c = (if (NS <? BIG MI) && (size_class MI NS =? c) then Zlength ents else 0).
  Proof using AC SEGS L MI.
    intros V NS ents c. induction ents as [|[q kv] ents IH]; [unfold Zlength; cbn; destruct (_ && _); reflexivity|].
    cbn [map fst count_class_f]. rewrite Zlength_cons, IH. destruct (_ && _); lia.
  Qed.
  Lemma cnt_umap_eq : forall {V : Type} NS bl bc (ents : list (Z * (Z * V))) c,
    cnt (umap_blocks NS bl bc ents) c <= 1 + (if (NS <? BIG MI) && (size_class MI NS =? c) then Zlength ents else 0).
  Proof using AC SEGS L MI.
    intros V NS bl bc ents c. unfold umap_blocks. rewrite cnt_app, cnt_nodes_eq.
    assert (cnt (if bc =? 0 then [] else [(bl, 8 * bc)]) c <= 1).
    { destruct (bc =? 0); cbn; [lia|]. destruct (_ && _); lia. }
    lia.
  Qed.

  Definition pm_bud (n : Z) (c : pmc) : Prop :=
    (2 * Zlength (t3c (c_m1 c)) <= n + 2 /\ 2 * Zlength (t3c (c_m2 c)) <= n + 2 /\ 3 * Zlength (t3c (c_m3 c)) <= n + 3)
    /\ 0 <= 8 * t3b (c_m1 c) <= 8 * n + 4096 /\ 0 <= 8 * t3b (c_m2 c) <= 8 * n + 4096 /\ 0 <= 8 * t3b (c_m3 c) <= 8 * n + 4096
    /\ 0 <= OPND_SZ * t3c (c_v1 c) <= 2 ^ 23 /\ 0 <= 4 * t3c (c_v2 c) <= 2 ^ 20 /\ 0 <= 4 * t3c (c_v3 c) <= 2 ^ 26
    /\ Zlength (c_tr c) <= 2 /\ (forall b, In b (c_tr c) -> 0 < snd b <= 2 ^ 28).

  Lemma cnt_single_le1 : forall q k c, cnt [(q, k)] c <= 1.
  Proof using AC SEGS L MI. intros. cbn. destruct (_ && _); lia. Qed.
  Lemma cnt_opt_le1 : forall (b : bool) q k c, cnt (if b then [] else [(q, k)]) c <= 1.
  Proof using AC SEGS L MI. intros. destruct b; cbn; [lia|]. destruct (_ && _); lia. Qed.

  Lemma cnt_c_blocks : forall n c cls, pm_bud n c -> 0 <= n ->
    cnt (c_blocks c) cls <= (if cls <? 4 then PM_NODES n else 0) + 10.
  Proof using AC SEGS L MI HC24 HC32 HBIG.
    intros n c cls B Hn. destruct B as ((Bn1 & Bn2 & Bn3) & _ & _ & _ & _ & _ & _ & Btr & _).
    unfold c_blocks. rewrite !cnt_app.
    pose proof (cnt_umap_eq 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) cls) as U1.
    pose proof (cnt_umap_eq 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) cls) as U2.
    pose proof (cnt_umap_eq 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) cls) as U3.
    pose proof (cnt_opt_le1 (t3a (c_v1 c) =? 0) (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c)) cls). unfold vec_opnd_blocks.
    pose proof (cnt_opt_le1 (t3a (c_v2 c) =? 0) (t3a (c_v2 c)) (4 * t3c (c_v2 c)) cls).
    pose proof (cnt_opt_le1 (t3a (c_v3 c) =? 0) (t3a (c_v3 c)) (4 * t3c (c_v3 c)) cls).
    pose proof (cnt_le_len (c_tr c) cls).
    assert (0 <= Zlength (t3c (c_m1 c)) /\ 0 <= Zlength (t3c (c_m2 c)) /\ 0 <= Zlength (t3c (c_m3 c))) by (unfold Zlength; lia).
    assert (Hdiv : Zlength (t3c (c_m1 c)) <= n / 2 + 1 /\ Zlength (t3c (c_m2 c)) <= n / 2 + 1 /\ Zlength (t3c (c_m3 c)) <= n / 3 + 1).
    { pose proof (Z.div_mod n 2 ltac:(lia)). pose proof (Z.mod_pos_bound n 2 ltac:(lia)).
      pose proof (Z.div_mod n 3 ltac:(lia)). pose proof (Z.mod_pos_bound n 3 ltac:(lia)). lia. }
    unfold PM_NODES. pose proof (proj1 HC32) as HC32a. pose proof (proj2 HC32) as HCNE.
    destruct (Z.ltb_spec cls 4).
    - destruct (24 <? BIG MI), (32 <? BIG MI); cbn [andb] in U1, U2, U3;
        destruct (Z.eqb_spec (size_class MI 24) cls), (Z.eqb_spec (size_class MI 32) cls); lia.
    - destruct (Z.ltb_spec 24 (BIG MI)), (Z.ltb_spec 32 (BIG MI)); try lia; cbn [andb] in U1, U2, U3;
        destruct (Z.eqb_spec (size_class MI 24) cls), (Z.eqb_spec (size_class MI 32) cls); lia.
  Qed.

  Lemma bigb_opt_le : forall (b : bool) q k, 0 <= k -> bigb (if b then [] else [(q, k)]) <= k + 4116.
  Proof using AC SEGS L MI RB. intros b q k Hk. destruct b; cbn; [lia|]. destruct (Z.leb_spec (BIG MI) k); [pose proof (RB k Hk); lia | lia]. Qed.

  Lemma bigb_umap : forall {V : Type} NS bl bc (ents : list (Z * (Z * V))),
    NS = 24 \/ NS = 32 -> 0 <= 8 * bc -> bigb (umap_blocks NS bl bc ents) <= 8 * bc + 4116.
  Proof using AC SEGS L MI HBIG RB.
    intros V NS bl bc ents HNS Hbc. unfold umap_blocks. rewrite bigb_app, (bigb_nodes NS ents HNS).
    pose proof (bigb_opt_le (bc =? 0) bl (8 * bc) Hbc). lia.
  Qed.

  Lemma bigb_c_blocks : forall n c, pm_bud n c -> 0 <= n -> bigb (c_blocks c) <= 24 * n + 2 ^ 29 + 2 ^ 28 - 2 ^ 24 - 2 ^ 27 + 2 ^ 26.
  Proof using AC SEGS L MI HBIG RB.
    intros n c B Hn. destruct B as (Bn & B1 & B2 & B3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
    unfold c_blocks, vec_opnd_blocks. rewrite !bigb_app.
    pose proof (bigb_umap 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) (or_introl eq_refl) ltac:(lia)).
    pose proof (bigb_umap 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) (or_intror eq_refl) ltac:(lia)).
    pose proof (bigb_umap 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) (or_introl eq_refl) ltac:(lia)).
    pose proof (bigb_opt_le (t3a (c_v1 c) =? 0) (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c)) ltac:(lia)).
    pose proof (bigb_opt_le (t3a (c_v2 c) =? 0) (t3a (c_v2 c)) (4 * t3c (c_v2 c)) ltac:(lia)).
    pose proof (bigb_opt_le (t3a (c_v3 c) =? 0) (t3a (c_v3 c)) (4 * t3c (c_v3 c)) ltac:(lia)).
    assert (Htr : bigb (c_tr c) <= 2 ^ 29 + 4 * 4116).
    { apply bigb_le; [intros b Hb; pose proof (Btrp b Hb); lia|].
      assert (G : forall l : list (Z * Z), 0 <= Zlength l -> (forall b, In b l -> 0 < snd b <= 2 ^ 28) ->
                 fold_right (fun b acc => (if BIG MI <=? snd b then snd b + 4116 else 0) + acc) 0 l
                 <= Zlength l * (2 ^ 28 + 4116)).
      { intros l. induction l as [|[q k] l IH]; intros Hl Hp; [unfold Zlength; cbn; lia|].
        cbn [fold_right snd] in *. rewrite Zlength_cons in *.
        assert (0 <= Zlength l) by (unfold Zlength; lia).
        specialize (IH ltac:(lia) ltac:(intros b Hb; apply Hp; right; exact Hb)).
        pose proof (Hp (q, k) (or_introl eq_refl)). cbn in *. destruct (BIG MI <=? k); lia. }
      pose proof (G (c_tr c) ltac:(unfold Zlength; lia) Btrp). lia. }
    lia.
  Qed.

  Lemma pmx_room : forall (w : pmw) A M model c (n : Z),
    PMX w A M model c -> pm_bud (w_n w) c ->
    (forall cls, 4 <= cls -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_SMALL_SLACK <= CAP_SMALL) ->
    (forall cls, 0 <= cls < 4 -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_NODES (w_n w) + PM_SMALL_SLACK <= CAP_NODE) ->
    big_bytes_f (round_big MI) (BIG MI) (w_L0 w) + PM_BIG (w_n w) <= LIB_BIGCAP ->
    0 < n <= 2 ^ 28 -> roomL MI A (live MI A) n.
  Proof using AC SEGS L MI ST HC24 HC32 HBIG RB.
    intros w A M model c n X B HS HN HB Hn. pose proof (x_geo X) as GEO.
    destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn & _).
    pose proof (x_caps X) as (Ccaps & Cbig & Cnmax). pose proof (x_live X) as PL.
    pose proof (ai_size_class_range MI) as SCR. pose proof (ai_big_pos MI) as BP.
    unfold roomL. rewrite Ccaps, Cbig. split.
    - intros Hsmall. pose proof (SCR n ltac:(lia)) as Hcls.
      rewrite !(count_class_f_perm _ _ _ _ _ PL), !cnt_app.
      pose proof (cnt_c_blocks (w_n w) c (size_class MI n) B ltac:(lia)) as C1.
      pose proof (cnt_c_blocks (w_n w) c (size_class MI n + 1) B ltac:(lia)) as C2.
      unfold PM_SMALL_SLACK, CAP_SMALL, CAP_NODE in *.
      split.
      + destruct (Z.ltb_spec (size_class MI n) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n) ltac:(lia)). unfold CAP_SMALL in *. lia.
      + destruct (Z.ltb_spec (size_class MI n + 1) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n + 1) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n + 1) ltac:(lia)). unfold CAP_SMALL in *. lia.
    - intros Hbigreq. rewrite (big_bytes_f_perm _ _ _ _ PL), bigb_app.
      pose proof (bigb_c_blocks (w_n w) c B ltac:(lia)). pose proof (RB n ltac:(lia)).
      unfold PM_BIG, LIB_BIGCAP in *. lia.
  Qed.

  Lemma pmx_room2 : forall (w : pmw) A M model c (n m : Z),
    PMX w A M model c -> pm_bud (w_n w) c ->
    (forall cls, 4 <= cls -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_SMALL_SLACK <= CAP_SMALL) ->
    (forall cls, 0 <= cls < 4 -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_NODES (w_n w) + PM_SMALL_SLACK <= CAP_NODE) ->
    big_bytes_f (round_big MI) (BIG MI) (w_L0 w) + PM_BIG (w_n w) <= LIB_BIGCAP ->
    0 < n -> 0 <= m -> n + m <= 2 ^ 28 + 2 ^ 26 -> roomL MI A ((0, m) :: live MI A) n.
  Proof using AC SEGS L MI ST HC24 HC32 HBIG RB.
    intros w A M model c n m X B HS HN HB Hn Hm Hnm. pose proof (x_geo X) as GEO.
    destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn & _).
    pose proof (x_caps X) as (Ccaps & Cbig & Cnmax). pose proof (x_live X) as PL.
    pose proof (ai_size_class_range MI) as SCR. pose proof (ai_big_pos MI) as BP.
    unfold roomL. rewrite Ccaps, Cbig. change ((0, m) :: live MI A) with ([(0, m)] ++ live MI A). split.
    - intros Hsmall. pose proof (SCR n ltac:(lia)) as Hcls.
      rewrite !cnt_app, !(count_class_f_perm _ _ _ _ _ PL), !cnt_app.
      pose proof (cnt_c_blocks (w_n w) c (size_class MI n) B ltac:(lia)) as C1.
      pose proof (cnt_c_blocks (w_n w) c (size_class MI n + 1) B ltac:(lia)) as C2.
      pose proof (cnt_single_le1 0 m (size_class MI n)) as S1. pose proof (cnt_single_le1 0 m (size_class MI n + 1)) as S2.
      unfold PM_SMALL_SLACK, CAP_SMALL, CAP_NODE in *.
      split.
      + destruct (Z.ltb_spec (size_class MI n) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n) ltac:(lia)). unfold CAP_SMALL in *. lia.
      + destruct (Z.ltb_spec (size_class MI n + 1) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n + 1) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n + 1) ltac:(lia)). unfold CAP_SMALL in *. lia.
    - intros Hbigreq. rewrite bigb_app, (big_bytes_f_perm _ _ _ _ PL), bigb_app.
      pose proof (bigb_c_blocks (w_n w) c B ltac:(lia)). pose proof (RB n ltac:(lia)).
      assert (Hs : bigb [(0, m)] <= m + 4116).
      { cbn [big_bytes_f]. destruct (Z.leb_spec (BIG MI) m); [pose proof (RB m ltac:(lia)); lia | lia]. }
      unfold PM_BIG, LIB_BIGCAP in *. lia.
  Qed.

  Lemma bigb_c_blocks1 : forall n c, pm_bud n c -> 0 <= n -> Zlength (c_tr c) <= 1 ->
    bigb (c_blocks c) <= 24 * n + 2 ^ 28 + 2 ^ 26 + 2 ^ 23 + 2 ^ 20 + 12288 + 7 * 4116.
  Proof using AC SEGS L MI HBIG RB.
    intros n c B Hn Hlen. destruct B as (Bn & B1 & B2 & B3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
    unfold c_blocks, vec_opnd_blocks. rewrite !bigb_app.
    pose proof (bigb_umap 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) (or_introl eq_refl) ltac:(lia)).
    pose proof (bigb_umap 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) (or_intror eq_refl) ltac:(lia)).
    pose proof (bigb_umap 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) (or_introl eq_refl) ltac:(lia)).
    pose proof (bigb_opt_le (t3a (c_v1 c) =? 0) (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c)) ltac:(lia)).
    pose proof (bigb_opt_le (t3a (c_v2 c) =? 0) (t3a (c_v2 c)) (4 * t3c (c_v2 c)) ltac:(lia)).
    pose proof (bigb_opt_le (t3a (c_v3 c) =? 0) (t3a (c_v3 c)) (4 * t3c (c_v3 c)) ltac:(lia)).
    assert (Htr : bigb (c_tr c) <= 2 ^ 28 + 4116).
    { destruct (c_tr c) as [|[q k] [|b2 l]].
      - cbn. lia.
      - pose proof (Btrp (q, k) (or_introl eq_refl)) as Hk. cbn in Hk. cbn [big_bytes_f].
        destruct (Z.leb_spec (BIG MI) k); [pose proof (RB k ltac:(lia)); lia | lia].
      - rewrite !Zlength_cons in Hlen. assert (0 <= Zlength l) by (unfold Zlength; lia). lia. }
    unfold OPND_SZ in *. lia.
  Qed.

  Lemma pmx_room3 : forall (w : pmw) A M model c (n m : Z),
    PMX w A M model c -> pm_bud (w_n w) c ->
    (forall cls, 4 <= cls -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_SMALL_SLACK <= CAP_SMALL) ->
    (forall cls, 0 <= cls < 4 -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_NODES (w_n w) + PM_SMALL_SLACK <= CAP_NODE) ->
    big_bytes_f (round_big MI) (BIG MI) (w_L0 w) + PM_BIG (w_n w) <= LIB_BIGCAP ->
    Zlength (c_tr c) <= 1 -> 0 < n <= 2 ^ 28 -> 0 <= m <= 2 ^ 28 -> roomL MI A ((0, m) :: live MI A) n.
  Proof using AC SEGS L MI ST HC24 HC32 HBIG RB.
    intros w A M model c n m X B HS HN HB Hlen Hn Hm. pose proof (x_geo X) as GEO.
    destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn & _).
    pose proof (x_caps X) as (Ccaps & Cbig & Cnmax). pose proof (x_live X) as PL.
    pose proof (ai_size_class_range MI) as SCR. pose proof (ai_big_pos MI) as BP.
    unfold roomL. rewrite Ccaps, Cbig. change ((0, m) :: live MI A) with ([(0, m)] ++ live MI A). split.
    - intros Hsmall. pose proof (SCR n ltac:(lia)) as Hcls.
      rewrite !cnt_app, !(count_class_f_perm _ _ _ _ _ PL), !cnt_app.
      pose proof (cnt_c_blocks (w_n w) c (size_class MI n) B ltac:(lia)) as C1.
      pose proof (cnt_c_blocks (w_n w) c (size_class MI n + 1) B ltac:(lia)) as C2.
      pose proof (cnt_single_le1 0 m (size_class MI n)) as S1. pose proof (cnt_single_le1 0 m (size_class MI n + 1)) as S2.
      unfold PM_SMALL_SLACK, CAP_SMALL, CAP_NODE in *.
      split.
      + destruct (Z.ltb_spec (size_class MI n) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n) ltac:(lia)). unfold CAP_SMALL in *. lia.
      + destruct (Z.ltb_spec (size_class MI n + 1) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n + 1) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n + 1) ltac:(lia)). unfold CAP_SMALL in *. lia.
    - intros Hbigreq. rewrite bigb_app, (big_bytes_f_perm _ _ _ _ PL), bigb_app.
      pose proof (bigb_c_blocks1 (w_n w) c B ltac:(lia) Hlen). pose proof (RB n ltac:(lia)).
      assert (Hs : bigb [(0, m)] <= m + 4116).
      { cbn [big_bytes_f]. destruct (Z.leb_spec (BIG MI) m); [pose proof (RB m ltac:(lia)); lia | lia]. }
      unfold PM_BIG, LIB_BIGCAP in *. lia.
  Qed.

  Lemma pm_bud_sizes : forall (w : pmw) A M model c b,
    PMX w A M model c -> pm_bud (w_n w) c -> In b (c_blocks c) -> 0 < snd b <= PM_BIG (w_n w).
  Proof using AC SEGS L MI ST.
    intros w A M model c b X B Hb. pose proof (x_geo X) as GEO.
    destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn & _).
    destruct B as (Bn & B1 & B2 & B3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
    assert (UM : forall NS (V : Type) nv o (m : Z * Z * list (Z * (Z * V))),
              umapx NS nv A M o (t3a m) (t3b m) (t3c m) -> (NS = 24 \/ NS = 32) -> 8 * t3b m <= 8 * w_n w + 4096 ->
              In b (umap_blocks NS (t3a m) (t3b m) (t3c m)) -> 0 < snd b <= PM_BIG (w_n w)).
    { intros NS V nv o m U HNS Hbc Hin. unfold umap_blocks in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - destruct (Z.eqb_spec (t3b m) 0); [destruct Hin|]. destruct Hin as [<-|[]]. cbn.
        pose proof (u_bseq U) as HB. unfold PM_BIG.
        assert (0 <= t3b m) by (unfold BSEQ in HB; repeat (destruct HB as [<-|HB]; [lia|]); destruct HB). lia.
      - apply in_map_iff in Hin. destruct Hin as (e & <- & _). cbn. unfold PM_BIG. lia. }
    assert (SUM0 : forall l : list (Z * Z), (forall x, In x l -> 0 < snd x) -> 0 <= fold_right (fun x acc => snd x + acc) 0 l).
    { intros l. induction l as [|x l IH]; intros Hp; cbn; [lia|].
      pose proof (Hp x (or_introl eq_refl)). specialize (IH ltac:(intros z Hz; apply Hp; right; exact Hz)). lia. }
    assert (TR : forall l : list (Z * Z), (forall x, In x l -> 0 < snd x) -> In b l -> snd b <= fold_right (fun x acc => snd x + acc) 0 l).
    { intros l. induction l as [|x l IH]; intros Hp Hin; [destruct Hin|]. cbn.
      pose proof (SUM0 l ltac:(intros z Hz; apply Hp; right; exact Hz)).
      destruct Hin as [<-|Hin]; [lia|].
      pose proof (Hp x (or_introl eq_refl)). specialize (IH ltac:(intros z Hz; apply Hp; right; exact Hz) Hin). lia. }
    unfold c_blocks in Hb. rewrite !in_app_iff in Hb.
    destruct Hb as [Hb|[Hb|[Hb|[Hb|[Hb|[Hb|Hb]]]]]].
    - exact (UM 24 Z _ _ _ (x_m1 X) (or_introl eq_refl) ltac:(lia) Hb).
    - exact (UM 32 (Z * Z * Z)%type _ _ _ (x_m2 X) (or_intror eq_refl) ltac:(lia) Hb).
    - exact (UM 24 Z _ _ _ (x_m3 X) (or_introl eq_refl) ltac:(lia) Hb).
    - unfold vec_opnd_blocks in Hb. destruct (Z.eqb_spec (t3a (c_v1 c)) 0) as [|Hnz]; [destruct Hb|]. destruct Hb as [<-|[]]. cbn.
      pose proof (x_v1 X) as V. destruct V as (_ & _ & _ & _ & Hbk & _). destruct Hbk as [[? _]|(_ & _ & Hc & _)]; [lia|]. unfold PM_BIG, OPND_SZ in *. lia.
    - destruct (Z.eqb_spec (t3a (c_v2 c)) 0) as [|Hnz]; [destruct Hb|]. destruct Hb as [<-|[]]. cbn.
      pose proof (x_v2 X) as V. destruct V as (_ & _ & _ & _ & Hbk & _). destruct Hbk as [[? _]|(_ & _ & Hc & _)]; [lia|]. unfold PM_BIG in *. lia.
    - destruct (Z.eqb_spec (t3a (c_v3 c)) 0) as [|Hnz]; [destruct Hb|]. destruct Hb as [<-|[]]. cbn.
      pose proof (x_v3 X) as V. destruct V as (_ & _ & _ & _ & Hbk & _). destruct Hbk as [[? _]|(_ & _ & Hc & _)]; [lia|]. unfold PM_BIG in *. lia.
    - pose proof (Btrp b Hb). unfold PM_BIG. lia.
  Qed.
End Budget.

End Base.

Arguments w_sp {AC SEGS L MI ST} _.
Arguments w_STK {AC SEGS L MI ST} _.
Arguments w_ret {AC SEGS L MI ST} _.
Arguments w_p {AC SEGS L MI ST} _.
Arguments w_cons {AC SEGS L MI ST} _.
Arguments w_user {AC SEGS L MI ST} _.
Arguments w_diag {AC SEGS L MI ST} _.
Arguments w_words {AC SEGS L MI ST} _.
Arguments w_n {AC SEGS L MI ST} _.
Arguments w_L0 {AC SEGS L MI ST} _.
Arguments w_R0 {AC SEGS L MI ST} _.
Arguments w_A0 {AC SEGS L MI ST} _.
Arguments w_M0 {AC SEGS L MI ST} _.
Arguments w_model0 {AC SEGS L MI ST} _.
Arguments w_s {AC SEGS L MI ST} _.
Arguments w_sp0 {AC SEGS L MI ST} _.
Arguments PMF {AC SEGS L} MI {ST} _ _.
Arguments junkL {AC SEGS L} MI {ST} _ _.
Arguments PMX {AC SEGS L} MI ST _ _ _ _ _.
Arguments pmw {AC SEGS L} MI ST.
Arguments pm_bud _ _ : simpl nomatch.
Arguments cblk _ : simpl nomatch.
Arguments fprot {AC SEGS L MI ST} _ _ _.
Arguments cblk_live {AC SEGS L MI ST} _ {A M model c} _ _ _.
Arguments pmx_callB {AC SEGS L MI ST} _ {A M model c R} _ _ _ _ _.
Arguments eff_widen {AC SEGS L} MI {A A' M M'} _ _ _ _ _ _.
Arguments set_tr _ _ : simpl nomatch.
Arguments MKPMX {AC SEGS L MI ST w A M model c}.
Arguments x_ai {AC SEGS L MI ST w A M model c} _.
Arguments x_ms {AC SEGS L MI ST w A M model c} _.
Arguments x_fs {AC SEGS L MI ST w A M model c} _.
Arguments x_fds {AC SEGS L MI ST w A M model c} _.
Arguments x_sx {AC SEGS L MI ST w A M model c} _.
Arguments x_sxh {AC SEGS L MI ST w A M model c} _.
Arguments x_roc {AC SEGS L MI ST w A M model c} _.
Arguments x_eff {AC SEGS L MI ST w A M model c} _.
Arguments x_own_sx {AC SEGS L MI ST w A M model c} _.
Arguments x_err_sx {AC SEGS L MI ST w A M model c} _.
Arguments x_win_sx {AC SEGS L MI ST w A M model c} _.
Arguments x_geo {AC SEGS L MI ST w A M model c} _.
Arguments x_wdef {AC SEGS L MI ST w A M model c} _.
Arguments x_wown {AC SEGS L MI ST w A M model c} _.
Arguments x_slots {AC SEGS L MI ST w A M model c} _.
Arguments x_pdef {AC SEGS L MI ST w A M model c} _.
Arguments x_cons {AC SEGS L MI ST w A M model c} _.
Arguments x_user {AC SEGS L MI ST w A M model c} _.
Arguments x_hdrfn {AC SEGS L MI ST w A M model c} _.
Arguments x_insfn {AC SEGS L MI ST w A M model c} _.
Arguments x_hunk {AC SEGS L MI ST w A M model c} _.
Arguments x_words {AC SEGS L MI ST w A M model c} _.
Arguments x_n {AC SEGS L MI ST w A M model c} _.
Arguments x_diag {AC SEGS L MI ST w A M model c} _.
Arguments x_widx {AC SEGS L MI ST w A M model c} _.
Arguments x_icount {AC SEGS L MI ST w A M model c} _.
Arguments x_endian {AC SEGS L MI ST w A M model c} _.
Arguments x_flags {AC SEGS L MI ST w A M model c} _.
Arguments x_scal {AC SEGS L MI ST w A M model c} _.
Arguments x_consf {AC SEGS L MI ST w A M model c} _.
Arguments x_consd {AC SEGS L MI ST w A M model c} _.
Arguments x_wbuf {AC SEGS L MI ST w A M model c} _.
Arguments x_m1 {AC SEGS L MI ST w A M model c} _.
Arguments x_m2 {AC SEGS L MI ST w A M model c} _.
Arguments x_m3 {AC SEGS L MI ST w A M model c} _.
Arguments x_v1 {AC SEGS L MI ST w A M model c} _.
Arguments x_v2 {AC SEGS L MI ST w A M model c} _.
Arguments x_v3 {AC SEGS L MI ST w A M model c} _.
Arguments x_live {AC SEGS L MI ST w A M model c} _.
Arguments x_caps {AC SEGS L MI ST w A M model c} _.
Arguments pmx_img_ro_clear {AC SEGS L MI ST} _ {A M model c} _.
Arguments hi_unowned {AC SEGS L} MI _ _ {A M model} _ _ _.
