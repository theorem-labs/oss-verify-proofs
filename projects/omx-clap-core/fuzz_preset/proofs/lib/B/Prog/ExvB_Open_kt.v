(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: EXB ACROSS A STRETCH that writes only ex_value's own frame
   area and the cursor cells (T1, shared with ExvLoop / ExvDisp). From a cut state with EXB, a stretch at the SAME
   allocator state (lyc, Sc, Hpc, Wc) - an engine run of straight-line code, or a runtime call whose rule keeps the
   allocator state (YGcallMx aj_strcmp_at_x / aj_bcmp_at_x) - whose journal from the entry is given, which leaves every
   byte outside [exv_sp E - exv_STK E, exv_s1 E + 176) and the FP cursor cells in [e_q E, e_q E + 40) unchanged, which
   keeps every present byte present, which keeps the memnorm keep from the entry memory (the _inv runner's
   P := memnorm (e_mem E) -> memnorm _ at the end memory, or the call rule's m-form keep), and which keeps the
   registers EXB reads, ends in EXB again (the room part of EXB's exv_rm is at the same Sc, carried as is).
   - every byte below alloc_ceiling is kept (the written bytes are on the real stack): the ledger (exk_ledger_kept,
     ex_ws_x.v's exw_ledger_kept restated), the text and scratch bytes and every shadow byte of an address below
     2 ^ 47, the frame's flag pointer;
   - the saved-register slots [sp - 104, sp) and 176(s1) lie above the written frame area (s1 <= sp - 288);
   - the tree: its footprint misses the stack window and the cursor (EXV_PRE) and lies below 2 ^ 47 (its blocks are
     Lam blocks: exv_node_D; its root is at home), so its bytes are kept and its writable bytes stay writable (presence
     grows); its root's shadow is below alloc_ceiling.
   Rule 24: proves no function (kind: segment lemma helper). Numerals: 288, 304, 319 (LENGTH: ex_value's frame and its
   32-alignment slack, B 0x8352c / 0x8356c), 176, 184, 280, 104 (LENGTH: slot offsets of B's code / exv_saved), 120,
   127, 128 (LENGTH: flag-pointer slot and the class-1 frame), 56 (LENGTH: tree node), 32, 8 (LENGTH: alignments),
   40 (LENGTH: struct ex), 2 ^ 47, 2 ^ 64 (LENGTH: address-space bounds), 2, 3, 4, 8, 9, 18, 19, 24, 25, 26 (WORD:
   register numbers). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YK1b YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

(* ---- frame geometry and slot ranges ---- *)
Lemma exv_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

Lemma exv_s1_le : forall E, exv_sp E - 319 <= exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0.
Proof.
intros E. unfold exv_s1. rewrite exv_land32. pose proof (Z.mod_pos_bound (exv_sp E - 288) 32 ltac:(lia)).
split; [lia|]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.

Lemma exv_saved_rng : forall o r, In (o, r) exv_saved -> 184 <= o <= 280.
Proof.
intros o r H. unfold exv_saved in H.
repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.

(* ---- shadow facts of addresses below 2 ^ 47 read only bytes below alloc_ceiling ---- *)
Section g. Context {rc : YM05.RunCeil}.
Lemma exv_ra_keep : forall (rd rd' : reader) a n,
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Hn HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
pose proof asan_consts as (C1 & _). rewrite HK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.

Lemma exv_hull_keep : forall (rd rd' : reader) x n,
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) -> 0 <= x -> x + n <= 2 ^ 47 ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n HK Hx Hn H s Hs. pose proof asan_consts as (C1 & _).
unfold shadow_addr, SHADOW_OFF in Hs.
assert (Hs0 : 0 <= s < alloc_ceiling).
{ destruct (Z_lt_le_dec n 1) as [Hn1|Hn1].
  - pose proof (Z.div_le_mono (x + n - 1) x 8 ltac:(lia) ltac:(lia)). lia.
  - lia. }
rewrite HK by exact Hs0. apply H. unfold shadow_addr, SHADOW_OFF. exact Hs.
Qed.
End g.

(* ---- the blocks a tree owns are lblk blocks (pj_nodeR, PRH_Reader.v:133-152) ---- *)
Lemma exv_items_D : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a D,
  Forall (fun u => forall p D1, P p u D1 -> forall b, In b D1 -> Q b) l ->
  PRH_Reader.pj_itemsR P a l D -> forall b, In b D -> Q b.
Proof.
intros P Q l. induction l as [|u l IH]; intros a D HF H b Hb; cbn [PRH_Reader.pj_itemsR] in H.
- subst D. destruct Hb.
- destruct H as (D1 & D2 & -> & H1 & H2). inversion HF as [|u' l' Hu HF']. subst.
  apply in_app_or in Hb as [Hb|Hb]; [exact (Hu _ _ H1 b Hb) | exact (IH (a + 56) D2 HF' H2 b Hb)].
Qed.

Lemma exv_mems_D : forall m (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  Forall (fun mm => forall p D1, P p (snd mm) D1 -> forall b, In b D1 -> lblk (fst b) (snd b)) l ->
  PRH_Reader.pj_memsR rsegs m lblk P a ka l D -> forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros m lblk P l. induction l as [|[nm u] l IH]; intros a ka D HF H b Hb; cbn [PRH_Reader.pj_memsR] in H.
- subst D. destruct Hb.
- destruct H as (x & k & D1 & D2 & -> & _ & (Hl & _) & H1 & H2). inversion HF as [|mm l' Hu HF']. subst.
  destruct Hb as [<-|Hb]; [exact Hl|].
  apply in_app_or in Hb as [Hb|Hb]; [exact (Hu _ _ H1 b Hb) | exact (IH (a + 56) (ka + 8) D2 HF' H2 b Hb)].
Qed.

Lemma exv_node_D : forall t m lblk p D, PRH_Reader.pj_nodeR rsegs m lblk p t D ->
  forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk p D H b Hb; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & H).
- destruct H as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct H as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct H as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct H as (_ & _ & _ & _ & _ & k & (Hl & _) & ->). destruct Hb as [<-|[]]. exact Hl.
- destruct H as (_ & _ & _ & _ & k & (Hl & _) & ->). destruct Hb as [<-|[]]. exact Hl.
- destruct H as (_ & _ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (Z.eqb_spec cap 0) as [E0|E0]; [destruct Hb|].
    destruct Hc as [(Hc0 & _)|(_ & Hl)]; [exfalso; exact (E0 Hc0)|]. destruct Hb as [<-|[]]. exact Hl.
  + apply (exv_items_D (PRH_Reader.pj_nodeR rsegs m lblk) (fun b => lblk (fst b) (snd b)) items kids Di);
      [|exact Hi|exact Hb].
    revert IH. apply Forall_impl. intros u Hu p0 D1 H1 b1 Hb1. exact (Hu m lblk p0 D1 H1 b1 Hb1).
- destruct H as (_ & _ & _ & Hc & Di & -> & Hm). apply in_app_or in Hb as [Hb|Hb].
  + destruct (Z.eqb_spec cap 0) as [E0|E0]; [destruct Hb|].
    destruct Hc as [(Hc0 & _)|(_ & Hl1 & Hl2)]; [exfalso; exact (E0 Hc0)|].
    destruct Hb as [<-|[<-|[]]]; [exact Hl1 | exact Hl2].
  + apply (exv_mems_D m lblk (PRH_Reader.pj_nodeR rsegs m lblk) members kids keys Di); [|exact Hm|exact Hb].
    revert IH. apply Forall_impl. intros mm Hu p0 D1 H1 b1 Hb1. exact (Hu m lblk p0 D1 H1 b1 Hb1).
Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* ex_ws_x.v's exw_val_kept / exw_garr8_kept / exw_ledger_kept, restated (this file does not load ex_ws_x) *)
Lemma exk_val_kept : forall H (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs H m' x = aview rsegs H m x) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview rsegs H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma exk_garr8_kept : forall H (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview rsegs H m' a = aview rsegs H m a) ->
  garr8 rsegs (mrestrict H m) p L -> garr8 rsegs (mrestrict H m') p L.
Proof.
intros H m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview rsegs H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma exk_ledger_kept : forall ly S Hp (W : world rsegs) mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HK (HG & HND & HB & HP).
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as (AC1 & AC2).
assert (VK : forall a n v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem rsegs (mrestrict (w_H W) mem) a n v -> val_mem rsegs (mrestrict (w_H W) mem') a n v).
{ intros a n v Ha Hn. apply (exk_val_kept (w_H W) mem mem' a n v). intros x Hx. apply HK. lia. }
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (GM & GMr) & (GO & GOr) & GR).
  refine (conj (VK _ _ _ _ _ G1) (conj (VK _ _ _ _ _ G2) (conj (VK _ _ _ _ _ G3) (conj (VK _ _ _ _ _ G4)
    (conj (VK _ _ _ _ _ G5) (conj (conj (VK _ _ _ _ _ GM) GMr) (conj (conj (VK _ _ _ _ _ GO) GOr) GR))))))).
  all: cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
    pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B];
    try change (Z.of_nat 8) with 8; try change (Z.of_nat 1) with 1; lia.
- revert HB. apply Forall_impl. intros [a k] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Kin) as (B1 & B2 & B3 & _).
  apply (VK (a - cf_head) 8%nat k); [lia | | exact Kv]. change (Z.of_nat 8) with 8.
  pose proof (@cf_head_nonneg cp) as CH0.
  assert (HU : exists u, a - cf_head = 16 * u).
  { exists ((a - cf_head) / 16). rewrite (Z.div_mod (a - cf_head) 16) at 1 by discriminate. rewrite B1, Z.add_0_r.
    reflexivity. }
  assert (HV : exists v, alloc_ceiling = 4096 * v).
  { exists (alloc_ceiling / 4096). rewrite (Z.div_mod alloc_ceiling 4096) at 1 by discriminate. rewrite AC2, Z.add_0_r.
    reflexivity. }
  destruct HU as [u Hu]. destruct HV as [v Hv]. clear B1 AC2.
  revert B3. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0) as [Hz|Hz]; intros B3; lia.
Qed.

(* a tree at home lies below 2 ^ 47 *)
Lemma exv_foot_rng : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) v t D,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_Reader.pj_nodeR rsegs (mrestrict (w_H W) mem) (prh_lin Lam) v t D -> prhex_home ly S Lam regs v 56 ->
  ly_stk_hi ly <= 2 ^ 47 ->
  forall x, PRH_Reader.pj_footR v D x -> 0 <= x < 2 ^ 47.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs v t D HAR HLED Hnd Hhome Hhi x Hx.
pose proof (eh_laws B ARx SK HYP) as LAWS. pose proof asan_consts as (C1 & _).
pose proof (@cf_head_nonneg cp) as CH0.
assert (LAMB : forall b k, In (b, k) Lam -> 4096 <= b /\ b + k <= alloc_ceiling).
{ intros b k Hin. pose proof HLED as (_ & _ & HB & _). rewrite Forall_forall in HB.
  destruct (HB (b, k) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
  destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & H4096 & Hc & _).
  assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  lia. }
destruct Hx as [Hx | (b & Hb & Hx)].
- destruct Hhome as [(b & k & Hin & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]].
  + destruct (LAMB b k Hin). lia.
  + destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid). lia.
  + pose proof (bv_unsigned_in_range _ (getr regs 2%bv)) as R. unfold spZ in H1. lia.
- pose proof (exv_node_D t _ _ v D Hnd b Hb) as Hl. destruct b as [b k]. unfold prh_lin in Hl. cbn [fst snd] in Hl.
  destruct (LAMB b k Hl). unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx. lia.
Qed.

(* T1: EXB across a stretch that writes only [exv_sp E - exv_STK E, exv_s1 E + 176) and the FP cursor cells *)
Lemma exv_kt : forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos
    (regs' : bvmap 5 word) memc' mdc' k',
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  EXB B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k' pos.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k' HPRE HB HJ' HK HG HMN HR.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv0 & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
unfold EXB in HB |- *. cbv zeta in HB |- *.
destruct HB as (HJ & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
unfold exv_sp, exv_STK in *.
assert (Hsp0 : 0 <= spZ (e_regs E)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)) as R; unfold spZ; lia).
(* the bytes below alloc_ceiling are kept *)
assert (KEEP : forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a).
{ intros a Ha. apply HK; [lia | lia | intros (_ & Hq); lia]. }
(* presence grows, so writability grows *)
assert (MG : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc')).
{ intros x Hx. unfold mrestrict in *. destruct (w_H Wc x) eqn:Hh; [exact Hx|].
  destruct (memc x) as [b|] eqn:Hm; [|exfalso; exact (Hx eq_refl)].
  destruct (HG (bv_unsigned x)) as [_ [b' Hb']].
  { split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Hm]. }
  rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate. }
assert (Hreg : forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) by exact HR.
assert (SP' : spZ regs' = spZ regs) by (unfold spZ; rewrite (Hreg 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); reflexivity).
split; [exact HJ'|].
split.
{ intros a Ha Hf. rewrite HK; [exact (HWIN a Ha Hf) | lia | lia | tauto]. }
split; [exact HFR|]. split; [exact HFZ|]. split; [exact HHp|]. split; [exact HAB|].
split; [exact (conj (proj1 HRM) HMN)|].
split; [eapply exk_ledger_kept; eassumption|].
split; [exact HCNT|].
split; [rewrite (Hreg 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R2|].
split; [rewrite (Hreg 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R8|].
split; [rewrite (Hreg 9%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R9|].
split; [rewrite (Hreg 18%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R18|].
split; [rewrite (Hreg 24%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R24|].
split; [rewrite (Hreg 25%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R25|].
split; [rewrite (Hreg 26%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R26|].
split; [rewrite (Hreg 19%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R19|].
split; [rewrite (Hreg 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R3|].
split; [rewrite (Hreg 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R4|].
split.
{ intros o r Hin. pose proof (exv_saved_rng o r Hin) as Ho.
  eapply exk_val_kept; [|exact (HSV o r Hin)].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK; [lia | lia | intros (_ & Hq); lia]. }
split.
{ eapply exk_val_kept; [|exact H176].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK; [lia | lia | intros (_ & Hq); lia]. }
split.
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin1) as (F1 & F2 & _).
  change (fs_frame_bytes 1) with 128 in F2.
  rewrite (rdword_ext (aview rsegs (w_H Wc) memc) (aview rsegs (w_H Wc) memc') (frame_addr lyc 1 pos + 120));
    [exact HFL|].
  intros kk Hk. apply KEEP. lia. }
split.
{ destruct HSRC as (Hby & H4096 & Hce & Ham & Hra & Hhull).
  split; [|split; [exact H4096|split; [exact Hce|split; [exact Ham|split]]]].
  - eapply exk_garr8_kept; [|exact Hby]. intros a Ha. apply KEEP. lia.
  - apply (exv_ra_keep _ _ _ _ KEEP); [lia | lia | exact Hra].
  - intros Hn. apply (exv_hull_keep _ _ _ _ KEEP); [lia | lia | exact (Hhull Hn)]. }
split; [exact HTB|].
split.
{ destruct HWD as (W1 & W2 & W3 & W4 & W5 & W6).
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split.
  - intros a Ha. destruct (W4 a Ha) as (Wa & Wb & _).
    split; [eapply writable_at_grows; [exact MG | exact Wa]|]. split; [exact Wb|]. lia.
  - split.
    + apply (exv_ra_keep _ _ _ _ KEEP); [lia | lia | exact W5].
    + intros Hn. apply (exv_hull_keep _ _ _ _ KEEP); [lia | lia | exact (W6 Hn)]. }
split; [exact HSB|].
split; [apply (exv_ra_keep _ _ _ _ KEEP); [lia | lia | exact HQR]|].
destruct Hv0 as [Hv0 | (_ & _ & HDJ)]; [left; exact Hv0|].
destruct HTREE as [Hv | (Hnd & Hhome & Hra & Hhull)]; [left; exact Hv|]. right.
pose proof HJ as (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
assert (Hhi : ly_stk_hi lyc <= 2 ^ 47) by lia.
pose proof (exv_foot_rng lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) regs
  (e_v E) (e_t E) (e_D E) HAR HLED Hnd Hhome Hhi) as FOOT.
assert (Fv0 := FOOT (e_v E) ltac:(left; lia)).
assert (Fv1 := FOOT (e_v E + 55) ltac:(left; lia)).
split.
{ apply (PRH_Reader.pj_nodeR_frame rsegs (e_t E) (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc')
    (prh_lin (e_Lam E)) (e_v E) (e_D E) Hnd).
  intros x Hx. pose proof (FOOT x Hx) as Hxb. destruct (HDJ x Hx) as (_ & Hxq & Hxs & _). split.
  - apply (mbyte_of_aview rsegs). apply HK; [lia | lia | intros (_ & Hq); lia].
  - intros Hw. eapply writable_at_grows; [exact MG | exact Hw]. }
split; [unfold prhex_home in *; rewrite SP'; exact Hhome|].
split; [apply (exv_ra_keep _ _ _ _ KEEP); [lia | lia | exact Hra]|].
apply (exv_hull_keep _ _ _ _ KEEP); [lia | lia | exact Hhull].
Qed.
End t.

Print Assumptions exv_kt.
