(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, twin bff8519b), ex_value piece 5 (ev_number), lane M:
   ev_mid across the piece's own writes. Proves S8aNumCut.v's ev_mid_keep_stmt and ev_mid_cur_stmt as ev_mid_keep and
   ev_mid_cur, generic over {L} {PA} as stated. No machine walk: every conjunct of ev_mid (S8aIface.v:172-189) other
   than the journal and the room conjunct (carried at the same S) reads bytes outside ev_wz (and outside in->p /
   in->differs for _keep), by the allocator laws (AR_laws_x), the journal's layout and frame facts, and ev_pre's
   separations:
   - the s1 window [S1 - STK_RT_STRTOD, S1 + 128) lies on the real stack, inside ex_value's STK below sp0;
   - the frame's slots, its flag word and its shadow bytes: the own fake frame (1, pos) is apart from every allocator
     block and every older frame (alx_sep), in the application range (alx_frames), 32-aligned;
   - the scratch, the text and the tree's kids are inside allocator blocks; the tree's root is in a block, an older
     fake frame or the real stack above sp0 (prhex_home at the entry);
   - errno and the seven program-written statics (prh_pst) are image bytes (below the shadow, outside every block and frame).
   A shadow byte visible before stays visible (the root's hull, the text's and the scratch's): one outside ev_wz keeps
   its view; one inside is the own frame's shadow byte (+4 / +8), present at mem' by the journal's ARx and alx_frames.
   Section hypotheses beyond LAWS (separations neither ev_pre nor the journal carries; each holds at preset's instance):
     IMG           ev_img_ok (S8aNumCut.v: 272 <= pi_frame F_ex_value; prh_img_A: 272, PRH_Img.v:35)
     HERR          errno's 4 bytes are image bytes (the errno-in-image premise ev_C_stmt and ev_number_of_pieces carry)
     CUTFIX_head   8 <= cf_head                         (preset's CfParams: 16, CfParamsPreset.v:17)
     CUTFIX_pst    the statics are image bytes and not errno (PRH_Img.v against TFIB_ERRNO, AF0m.v:19)
   The tree frame lemma is PRH_Reader.pj_nodeR_frame (the kit's tree predicate prhex_tree states over); the D-block
   lemma nm_node_lblk is the form of the plain parse_items_shape.v:335 pis_node_lblk, restated over pj_nodeR.
   Numerals: 272 (LENGTH: ex_value's frame, 256 plus the 32-realignment's 16), 256 (LENGTH: `addi sp, sp, -256`),
   128 / 120 (DERIVED: fs_frame_bytes 1 and its last word), 152 / 248 (LENGTH: EV_SAVED's least / greatest offset),
   4 8 16 32 36 40 55 56 (LENGTH: struct ex / pj field and node sizes, the shadow granule), 4096 (LENGTH: a page),
   2 ^ 47 / 2 ^ 64 (LENGTH: address widths). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.
(* lia handles div / mod by constants (the shadow granule, the 32-realignment) through euclidean equations *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- pure helpers ---- *)
Lemma nm_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]. Qed.

Lemma nm_zmaxl_ge : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. unfold zmaxl. induction l as [|y l IH]; intros H; [destruct H|]. cbn [fold_right].
destruct H as [<-|H]; [lia | specialize (IH H); lia].
Qed.

Ltac nm_lia := unfold shadow_addr, SHADOW_OFF, STK_RT_STRTOD, ESTACK, app_addr, in_app, ASAN_CEIL,
  kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd in *; lia.

(* ---- memory transfer through equal views ---- *)
Section mt.
Variable segs : list Segment.

Lemma nm_vm : forall H m m' a n v,
  (forall k, (k < n)%nat -> aview segs H m' (a + Z.of_nat k) = aview segs H m (a + Z.of_nat k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v E V k Hk. rewrite (mbyte_of_aview segs H H m m' _ (E k Hk)). exact (V k Hk).
Qed.

Lemma nm_garr8 : forall H m m' a l,
  (forall j, (j < length l)%nat -> aview segs H m' (a + Z.of_nat j) = aview segs H m (a + Z.of_nat j)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H m') a l.
Proof.
intros H m m' a l E G j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
apply (nm_vm H m m'); [|exact V]. intros k Hk.
replace (a + Z.of_nat j + Z.of_nat k) with (a + Z.of_nat j) by lia. exact (E j Hj).
Qed.

Lemma nm_rdword : forall (rd rd' : reader) a, (forall z, a <= z < a + 8 -> rd' z = rd z) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a E. unfold rdword.
rewrite (E a ltac:(lia)), (E (a + 1) ltac:(lia)), (E (a + 2) ltac:(lia)), (E (a + 3) ltac:(lia)),
  (E (a + 4) ltac:(lia)), (E (a + 5) ltac:(lia)), (E (a + 6) ltac:(lia)), (E (a + 7) ltac:(lia)).
reflexivity.
Qed.

Lemma nm_ra : forall (rd rd' : reader) y n,
  (forall x, y <= x < y + n -> rd' (shadow_addr x) = rd (shadow_addr x)) ->
  range_addressable rd SHADOW_OFF y n -> range_addressable rd' SHADOW_OFF y n.
Proof.
intros rd rd' y n E R x Hx. destruct (R x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *. rewrite (E x Hx). exact Hs.
Qed.

Lemma nm_hull : forall (rd rd' : reader) y n,
  (forall s, shadow_addr y / 8 * 8 <= s < shadow_addr (y + n - 1) / 8 * 8 + 8 -> rd s <> None -> rd' s <> None) ->
  shadow_hull_vis rd y n -> shadow_hull_vis rd' y n.
Proof. intros rd rd' y n E Hh s Hs. exact (E s Hs (Hh s Hs)). Qed.

(* outside the image a byte's view is its raw cell: equal views give equal cells, so writability carries *)
Lemma nm_raw : forall H (m m' : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ in_img segs x ->
  aview segs H m' x = aview segs H m x -> mrestrict H m' (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x).
Proof.
intros H m m' x Hr Hn E. apply mbyte_of_aview in E. unfold YP09.mbyte in E.
rewrite (seg_rom_none segs x Hr Hn) in E.
destruct (mrestrict H m' (Z_to_bv 64 x)), (mrestrict H m (Z_to_bv 64 x)); congruence.
Qed.

Lemma nm_wr : forall (m m' : word -> option byte) x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  writable_at segs m x -> writable_at segs m' x.
Proof. intros m m' x E Hw. unfold writable_at, wview in *. rewrite E. exact Hw. Qed.

Lemma nm_pres_vis : forall H m a, apresent H m a -> aview segs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, YP09.mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* every block a tree's D lists is one of lblk's (form of plain parse_items_shape.v:107-361, restated over pj_nodeR) *)
Lemma nm_items_in : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a D,
  (forall a u D1, In u l -> P a u D1 -> forall b, In b D1 -> Q b) ->
  PRH_Reader.pj_itemsR P a l D -> forall b, In b D -> Q b.
Proof.
intros P Q l. induction l as [|u r IH]; intros a D H Hl b Hb; cbn [PRH_Reader.pj_itemsR] in Hl.
- subst D. destruct Hb.
- destruct Hl as (D1 & D2 & E & HP & HR). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + exact (H a u D1 (or_introl eq_refl) HP b Hb).
  + apply (IH (a + 56) D2); [|exact HR|exact Hb]. intros a' u' D3 Hu. apply H. right. exact Hu.
Qed.

Lemma nm_mems_in : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> forall b, In b D1 -> Q b) ->
  (forall x k nm, PRH_Reader.pj_cstrR segs m lblk x k nm -> Q (x, k)) ->
  PRH_Reader.pj_memsR segs m lblk P a ka l D -> forall b, In b D -> Q b.
Proof.
intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H HC Hl b Hb; cbn [PRH_Reader.pj_memsR] in Hl.
- subst D. destruct Hb.
- destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR). subst D. destruct Hb as [Hb|Hb].
  + subst b. exact (HC x k nm Hc).
  + apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    * exact (H a u D1 (ex_intro _ nm (or_introl eq_refl)) HP b Hb).
    * apply (IH (a + 56) (ka + 8) D2); [|exact HC|exact HR|exact Hb].
      intros a' u' D3 (nm' & Hu). apply H. exists nm'. right. exact Hu.
Qed.

Lemma nm_node_lblk : forall t m lblk p D, PRH_Reader.pj_nodeR segs m lblk p t D ->
  forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H b Hb;
  cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb').
- destruct Hb' as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hb' as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hb' as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hb' as (_ & _ & _ & _ & _ & k & (Hl & _) & ED). subst D. destruct Hb as [<-|[]]. exact Hl.
- destruct Hb' as (_ & _ & _ & _ & k & (Hl & _) & ED). subst D. destruct Hb as [<-|[]]. exact Hl.
- destruct Hb' as (_ & _ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec. destruct Hb as [<-|[]].
    destruct Hcap as [(Hc0 & _)|(_ & Hl)]; [lia | exact Hl].
  + apply (nm_items_in (PRH_Reader.pj_nodeR segs m lblk) (fun b => lblk (fst b) (snd b)) items kids Di);
      [|exact Hi|exact Hb].
    intros a u D1 Hu HP b' Hb'. rewrite Forall_forall in IH. exact (IH u Hu m lblk a D1 HP b' Hb').
- destruct Hb' as (_ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hcap as [(Hc0 & _)|(_ & L0 & L1)]; [lia|].
    destruct Hb as [<-|[<-|[]]]; [exact L0 | exact L1].
  + apply (nm_mems_in m lblk (PRH_Reader.pj_nodeR segs m lblk) (fun b => lblk (fst b) (snd b)) members kids keys Di);
      [| |exact Hi|exact Hb].
    * intros a u D1 (nm & Hu) HP b' Hb'. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu).
      cbn [snd] in IH. exact (IH m lblk a D1 HP b' Hb').
    * intros x k nm (Hl & _). exact Hl.
Qed.
End mt.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the allocator laws, at a head length hl that no lemma here reads *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* ex_value's frame at the image: 256 plus the 32-realignment's 16 (prh_img_A: 272) *)
Hypothesis IMG : ev_img_ok.
(* a harness block's hidden head holds its 8-byte size (preset: 16) *)
Hypothesis CUTFIX_head : 8 <= cf_head.
(* errno is an image byte (api_env's clause; TfibLib tl_errno_img) *)
Hypothesis HERR : forall a0, as_errno B <= a0 < as_errno B + 4 -> in_img segs a0.
(* alloc.c's statics are image bytes, apart from errno *)
Hypothesis CUTFIX_pst : forall z, Exists (in_zr z) prh_pst -> in_img segs z /\ ~ (as_errno B <= z < as_errno B + 4).

(* the bytes ev_mid_cur_stmt lets change: ev_wz, in->p, in->differs *)
Definition ev_zc (a : ev_act) (z : Z) : Prop :=
  ev_wz B a z \/ (ea_q a <= z < ea_q a + 8) \/ (ea_q a + 32 <= z < ea_q a + 36).

Lemma nm_nzw : forall a z,
  ~ (ea_S1 a - STK_RT_STRTOD <= z < ea_S1 a + 128) -> ~ (ea_fr a + 32 <= z < ea_fr a + 40) ->
  ~ (ea_fr a + 64 <= z < ea_fr a + 72) -> z <> shadow_addr (ea_fr a) + 4 -> z <> shadow_addr (ea_fr a) + 8 ->
  ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) -> ~ (as_errno B <= z < as_errno B + 4) -> ~ ev_wz B a z.
Proof. intros a z H1 H2 H3 H4 H5 H6 H7. unfold ev_wz. cbv zeta. intuition. Qed.

Lemma nm_nz : forall a z,
  ~ (ea_S1 a - STK_RT_STRTOD <= z < ea_S1 a + 128) -> ~ (ea_fr a + 32 <= z < ea_fr a + 40) ->
  ~ (ea_fr a + 64 <= z < ea_fr a + 72) -> z <> shadow_addr (ea_fr a) + 4 -> z <> shadow_addr (ea_fr a) + 8 ->
  ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) -> ~ (as_errno B <= z < as_errno B + 4) ->
  ~ (ea_q a <= z < ea_q a + 8) -> ~ (ea_q a + 32 <= z < ea_q a + 36) -> ~ ev_zc a z.
Proof.
intros a z H1 H2 H3 H4 H5 H6 H7 H8 H9 [H|[H|H]]; [exact (nm_nzw a z H1 H2 H3 H4 H5 H6 H7 H) | exact (H8 H) | exact (H9 H)].
Qed.

Lemma nm_zc_fr : forall a z, ~ ev_zc a z -> ~ (ea_fr a + 32 <= z < ea_fr a + 40) /\ ~ (ea_fr a + 64 <= z < ea_fr a + 72).
Proof.
intros a z H. unfold ev_zc, ev_wz in H. cbv zeta in H.
split; intros H'; apply H; left; [right; left | right; right; left]; exact H'.
Qed.

Section a.
Variable ac : ev_act.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
  (k p dep dl : Z) (mem' : word -> option byte) (md' : Model) (k' : Z).
Hypothesis PRE : @ev_pre fx rc cp PI L PA B ARx ac.
Hypothesis MIDH : @ev_mid rc cp PI RL L PA B ARx SK ac ly S Hp W mem md k p dep dl.
Hypothesis AJH : ajournal_x (SK := SK) segs B prh_pst ARx (ea_STK ac + ea_d ac) (ea_sp0 ac + ea_d ac)
  (ea_FP ac) (ea_ly ac) (ea_S ac) (ea_Hp ac) (ea_W ac) (ea_mem ac) (ea_md ac) [(1, ea_pos ac)] ly S Hp W mem' md' k'.
(* the bytes that may change, inside ev_zc *)
Variable Zx : Z -> Prop.
Hypothesis Zx_sub : forall z, Zx z -> ev_zc ac z.
Hypothesis HE : forall z, 0 <= z < 2 ^ 64 -> ~ Zx z -> aview segs (w_H W) mem' z = aview segs (w_H W) mem z.

Lemma nm_HE : forall z, 0 <= z < 2 ^ 64 -> ~ ev_zc ac z -> aview segs (w_H W) mem' z = aview segs (w_H W) mem z.
Proof. intros z Hz Hn. apply HE; [exact Hz | intros Hx; exact (Hn (Zx_sub z Hx))]. Qed.

Ltac pre_destr := pose proof PRE as (Pfpre & Pfrm & Pcnt & Pa0 & Pa1 & Pcur & Pqm & Pch & Pspq & Pq40 & Pwin & Psrc &
  Ptxt & Plen & Pi0 & Pdep & Pdn & Pdl & Pwd & Pscr & Psx & Psq & Ptree & Pled & Pmn).

(* the layout numbers every separation below uses *)
Lemma nm_geo :
  ea_sp0 ac mod 16 = 0 /\ alloc_ceiling <= ea_sp0 ac - ea_STK ac /\ 272 + STK_RT_STRTOD <= ea_STK ac /\
  ea_sp0 ac - 272 <= ea_S1 ac <= ea_sp0 ac - 256 /\ 0 <= ea_d ac /\ ea_sp0 ac + ea_d ac <= 2 ^ 47 /\
  ea_sp0 ac <= ea_q ac /\ ea_q ac + 40 <= ea_sp0 ac + ea_d ac /\
  ea_fr ac = frame_addr ly 1 (ea_pos ac) /\ In (1, ea_pos ac) (frames S) /\
  ea_fr ac mod 32 = 0 /\ 4096 <= ea_fr ac /\ ea_fr ac + 128 <= alloc_ceiling /\ in_app (ea_fr ac) 128 /\
  0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd /\ ly_stk_hi (ea_ly ac) <= 2 ^ 47 /\
  (forall c p0, frame_addr (ea_ly ac) c p0 = frame_addr ly c p0) /\
  ARx ly S Hp W mem md /\ ARx ly S Hp W mem' md'.
Proof.
pre_destr.
destruct Pfpre as ((_ & _ & _ & _ & _ & Pstk & _) & _).
destruct Pstk as (Hal & HS0 & Hceil & Hlo & Hhi & H47 & _ & Htop1 & Htop2).
destruct Pwin as (Hd0 & _ & Hdtop & _).
change (spZ (ea_regs ac)) with (ea_sp0 ac) in Hal, Hlo, Hhi, Htop1, Pspq, Pq40, Hdtop.
pose proof MIDH as ((HAR & Hly & _ & _ & _ & Hfrs & _) & _).
pose proof AJH as (HAR' & _).
destruct Hly as (_ & _ & _ & _ & _ & HF & _).
assert (Hin : In (1, ea_pos ac) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : forall c p0, frame_addr (ea_ly ac) c p0 = frame_addr ly c p0)
  by (intros c p0; unfold frame_addr; rewrite HF; reflexivity).
assert (Hfr : ea_fr ac = frame_addr ly 1 (ea_pos ac)) by (unfold ea_fr; apply Hfa).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md 1 (ea_pos ac) HAR Hin) as (Hal32 & Happ & _ & _).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 (ea_pos ac) HAR Hin) as (H4096 & Hfc & _).
rewrite <- Hfr in Hal32, Happ, H4096, Hfc. change (fs_frame_bytes 1) with 128 in Happ, Hfc.
pose proof (pa_segs_low (as_errno B) (HERR (as_errno B) ltac:(lia))) as He0.
pose proof (pa_segs_low (as_errno B + 3) (HERR (as_errno B + 3) ltac:(lia))) as He3.
assert (HSTK : 272 + STK_RT_STRTOD <= ea_STK ac).
{ unfold ea_STK, STK_ex_value.
  pose proof (nm_zmaxl_ge STK_RT_STRTOD [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]
    ltac:(right; right; left; reflexivity)) as Hz.
  pose proof IMG as Himg. unfold ev_img_ok in Himg.
  rewrite Nat2Z.inj_succ. pose proof (Nat2Z.is_nonneg (ea_n ac)). nia. }
assert (HS1 : ea_sp0 ac - 272 <= ea_S1 ac <= ea_sp0 ac - 256) by (unfold ea_S1, ea_SA; lia).
refine (conj Hal (conj _ (conj HSTK (conj HS1 (conj Hd0 (conj _ (conj Pspq (conj Pq40 (conj Hfr (conj Hin
  (conj Hal32 (conj H4096 (conj Hfc (conj Happ (conj _ (conj _ (conj H47 (conj Hfa (conj HAR HAR')))))))))))))))))));
lia.
Qed.

Ltac geo_destr := pose proof nm_geo as (Gsp & Gstk & GSTK & GS1 & Gd & Gd47 & Gq0 & Gq40 & Gfr & Gfin & Gfr32 & Gfr0 &
  Gfrc & Gfrapp & Ge0 & Ge4 & Ghi & Gfa & GAR & GAR').

(* the scratch's block *)
Lemma nm_scr : exists bs ms, In (bs, ms) (ablocks B ly S) /\ bs <= ea_scr ac /\
  ea_scr ac + ea_len ac + 1 <= bs + req_size ms /\ (In bs Hp -> bs + cf_head <= ea_scr ac) /\
  4096 <= bs /\ bs + req_size ms <= alloc_ceiling /\ in_app bs (req_size ms).
Proof.
pre_destr. destruct Pscr as (bs & ms & Hin0 & Hb1 & Hb2 & HbHp).
pose proof MIDH as (_ & _ & HHp & Hab & _).
assert (Hin : In (bs, ms) (ablocks B ly S)) by (rewrite Hab; exact Hin0).
geo_destr.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md bs ms GAR Hin) as (_ & H4096 & Hceil & Happ & _ & _).
pose proof (nm_req_ge ms).
exists bs, ms. refine (conj Hin (conj Hb1 (conj _ (conj _ (conj H4096 (conj Hceil Happ)))))); [lia|].
rewrite HHp. exact HbHp.
Qed.

(* a byte of a live allocator block: apart from the own frame, outside the image, below the ceiling *)
Lemma nm_blk0 : forall b m z, In (b, m) (ablocks B ly S) -> b <= z < b + req_size m ->
  ~ (ea_fr ac <= z < ea_fr ac + 128) /\ ~ in_img segs z /\ 4096 <= z < alloc_ceiling /\ app_addr z.
Proof.
intros b m z Hin Hz. geo_destr.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m GAR Hin) as (_ & H4096 & Hceil & Happ & _ & _).
pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md b m 1 (ea_pos ac) GAR Hin Gfin) as Hd.
rewrite <- Gfr in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (blk_img_x _ _ _ LAWS ly S Hp W mem md b m z GAR Hin Hz) as Hni.
split; [lia|]. split; [exact Hni|]. split; [lia|]. exact (in_app_addr _ _ _ Happ Hz).
Qed.

Lemma nm_blk : forall b m z, In (b, m) (ablocks B ly S) -> b <= z < b + req_size m ->
  ~ (ea_scr ac <= z < ea_scr ac + ea_len ac + 1) -> ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd.
Proof.
intros b m z Hin Hz Hs. destruct (nm_blk0 b m z Hin Hz) as (Hf & Hni & Hr & Hap). geo_destr.
assert (He : ~ (as_errno B <= z < as_errno B + 4)) by (intros He; exact (Hni (HERR z He))).
pose proof asan_consts as AC.
split; [|split; [exact Hni | nm_lia]].
apply nm_nz; try exact Hs; try exact He; nm_lia.
Qed.

(* a byte of an older fake frame (live at the entry) *)
Lemma nm_frm0 : forall c p0 z, In (c, p0) (frames (ea_S ac)) ->
  frame_addr ly c p0 <= z < frame_addr ly c p0 + fs_frame_bytes c ->
  ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd.
Proof.
intros c p0 z Hin Hz. geo_destr.
pose proof MIDH as ((_ & _ & _ & _ & _ & Hfrs & _) & _).
assert (Hin' : In (c, p0) (frames S)) by (rewrite Hfrs; right; exact Hin).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md c p0 GAR Hin') as (H0 & Hc & Happ).
apply in_split in Hin as (l2 & l3 & E).
pose proof (sep_frames_pos_x _ _ _ LAWS ly S Hp W mem md (1, ea_pos ac) (c, p0) [] l2 l3 GAR
  ltac:(rewrite Hfrs, E; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite <- Gfr in Hd. change (fs_frame_bytes 1) with 128 in Hd.
destruct nm_scr as (bs & ms & Hbs & Hs1 & Hs2 & _ & _ & _ & _).
pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md bs ms c p0 GAR Hbs Hin') as Hd2.
unfold zdisjoint in Hd2; cbn [fst snd] in Hd2.
pose proof (frm_img_x _ _ _ LAWS ly S Hp W mem md c p0 z GAR Hin' Hz) as Hni.
assert (He : ~ (as_errno B <= z < as_errno B + 4)) by (intros He; exact (Hni (HERR z He))).
pose proof (in_app_addr _ _ _ Happ Hz) as Hap. pose proof asan_consts as AC.
split; [|split; [exact Hni | nm_lia]].
apply nm_nz; try exact He; nm_lia.
Qed.

(* the own frame's flag word (fs_frame_bytes 1 - 8 .. fs_frame_bytes 1) *)
Lemma nm_flag : forall z, ea_fr ac + 120 <= z < ea_fr ac + 128 -> ~ ev_zc ac z /\ 0 <= z < 2 ^ 64.
Proof.
intros z Hz. geo_destr.
destruct nm_scr as (bs & ms & Hbs & Hs1 & Hs2 & _ & _ & _ & _).
pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md bs ms 1 (ea_pos ac) GAR Hbs Gfin) as Hd2.
rewrite <- Gfr in Hd2. change (fs_frame_bytes 1) with 128 in Hd2. unfold zdisjoint in Hd2; cbn [fst snd] in Hd2.
assert (Hni : ~ in_img segs z).
{ apply (frm_img_x _ _ _ LAWS ly S Hp W mem md 1 (ea_pos ac) z GAR Gfin).
  rewrite <- Gfr. change (fs_frame_bytes 1) with 128. lia. }
assert (He : ~ (as_errno B <= z < as_errno B + 4)) by (intros He; exact (Hni (HERR z He))).
pose proof asan_consts as AC.
split; [|nm_lia]. apply nm_nz; try exact He; nm_lia.
Qed.

(* the real stack from the entry sp up *)
Lemma nm_stkw : forall z, ea_sp0 ac <= z < 2 ^ 47 -> ~ ev_wz B ac z /\ ~ in_img segs z.
Proof.
intros z Hz. geo_destr.
destruct nm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & _ & Hsc & _).
pose proof asan_consts as AC.
assert (Hni : ~ in_img segs z) by (intros Hi; pose proof (pa_segs_low z Hi); nm_lia).
split; [|exact Hni]. apply nm_nzw; nm_lia.
Qed.

Lemma nm_stk : forall z, ea_sp0 ac <= z < 2 ^ 47 -> ~ (ea_q ac <= z < ea_q ac + 8) -> ~ (ea_q ac + 32 <= z < ea_q ac + 36) ->
  ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd.
Proof.
intros z Hz H1 H2. destruct (nm_stkw z Hz) as [Hw Hni].
split; [intros [H|[H|H]]; [exact (Hw H) | exact (H1 H) | exact (H2 H)]|]. split; [exact Hni|].
geo_destr. pose proof asan_consts as AC. nm_lia.
Qed.

(* the save area [SA + 152, sp0) *)
Lemma nm_save : forall z, ea_SA ac + 152 <= z < ea_sp0 ac -> ~ ev_zc ac z /\ 0 <= z < 2 ^ 64.
Proof.
intros z Hz. geo_destr. destruct nm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & _ & Hsc & _). pose proof asan_consts as AC.
unfold ea_SA in Hz. split; [|nm_lia]. apply nm_nz; nm_lia.
Qed.

(* a shadow byte of an application byte outside the frame's two slots *)
Lemma nm_sh : forall y, 0 <= y < kHighMemEnd -> ~ (ea_fr ac + 32 <= y < ea_fr ac + 40) ->
  ~ (ea_fr ac + 64 <= y < ea_fr ac + 72) -> ~ ev_zc ac (shadow_addr y) /\ 0 <= shadow_addr y < 2 ^ 64.
Proof.
intros y Hy H1 H2. geo_destr. destruct nm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & Hb0 & Hsc & Hbapp).
pose proof asan_consts as AC.
split; [|nm_lia]. apply nm_nz; nm_lia.
Qed.

(* alloc.c's statics *)
Lemma nm_pst : forall z, Exists (in_zr z) prh_pst -> ~ ev_zc ac z /\ 0 <= z < 2 ^ 64.
Proof.
intros z Hz. destruct (CUTFIX_pst z Hz) as [Hi He]. pose proof (pa_segs_low z Hi) as Hlow.
geo_destr. destruct nm_scr as (bs & ms & Hbs & Hs1 & Hs2 & _ & _ & _ & _).
assert (Hnf : ~ (ea_fr ac <= z < ea_fr ac + 128)).
{ intros Hf. apply (frm_img_x _ _ _ LAWS ly S Hp W mem md 1 (ea_pos ac) z GAR Gfin); [|exact Hi].
  rewrite <- Gfr. change (fs_frame_bytes 1) with 128. lia. }
assert (Hns : ~ (ea_scr ac <= z < ea_scr ac + ea_len ac + 1)).
{ intros Hs. apply (blk_img_x _ _ _ LAWS ly S Hp W mem md bs ms z GAR Hbs); [lia | exact Hi]. }
pose proof asan_consts as AC.
split; [|nm_lia]. apply nm_nz; try exact Hns; try exact He; nm_lia.
Qed.

(* a byte visible before stays visible, errno aside: a written byte is present by the laws or the journal *)
Lemma nm_vis : forall s, 0 <= s < 2 ^ 64 -> ~ (as_errno B <= s < as_errno B + 4) ->
  aview segs (w_H W) mem s <> None -> aview segs (w_H W) mem' s <> None.
Proof.
intros s Hs Hne Hv E.
assert (N : ~ ev_zc ac s -> False) by (intros Hn; rewrite (nm_HE s Hs Hn) in E; exact (Hv E)).
apply N. intros Hz.
assert (P : apresent (w_H W) mem' s).
{ geo_destr. pose proof AJH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct nm_scr as (bs & ms & Hbs & Hs1 & Hs2 & _ & _ & _ & _).
  destruct (alx_frames _ _ _ LAWS ly S Hp W mem' md' 1 (ea_pos ac) GAR' Gfin) as (_ & _ & Hfb & Hsb).
  rewrite <- Gfr in Hfb, Hsb. change (fs_frame_bytes 1) with 128 in Hfb, Hsb.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem' md' bs ms GAR' Hbs) as (_ & _ & _ & _ & Hpb & _).
  unfold ev_zc, ev_wz in Hz; cbv zeta in Hz.
  destruct Hz as [[H|[H|[H|[H|[H|[H|H]]]]]]|[H|H]].
  - apply Hpres. lia.
  - exact (proj1 (Hfb s ltac:(lia))).
  - exact (proj1 (Hfb s ltac:(lia))).
  - rewrite H. exact (proj1 (Hsb 4 ltac:(lia))).
  - rewrite H. exact (proj1 (Hsb 8 ltac:(lia))).
  - exact (proj1 (Hpb s ltac:(lia))).
  - exfalso. exact (Hne H).
  - apply Hpres. nm_lia.
  - apply Hpres. nm_lia. }
exact (nm_pres_vis segs (w_H W) mem' s P E).
Qed.

Lemma nm_ra_keep : forall y n,
  (forall x, y <= x < y + n -> 0 <= x < kHighMemEnd /\ ~ (ea_fr ac + 32 <= x < ea_fr ac + 40) /\
     ~ (ea_fr ac + 64 <= x < ea_fr ac + 72)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> range_addressable (aview segs (w_H W) mem') SHADOW_OFF y n.
Proof.
intros y n Hx. apply nm_ra. intros x Hr. destruct (Hx x Hr) as (H0 & H1 & H2).
destruct (nm_sh x H0 H1 H2) as [Hn Hb]. exact (nm_HE _ Hb Hn).
Qed.

(* the hull of an application range [y, y + n) (a block, a fake frame, the real stack): its shadow bytes are above
   errno and below 2 ^ 64, so nm_vis carries each *)
Lemma nm_hull_keep : forall y n, 0 <= y -> y + n <= kHighMemEnd -> 0 < n ->
  shadow_hull_vis (aview segs (w_H W) mem) y n -> shadow_hull_vis (aview segs (w_H W) mem') y n.
Proof.
intros y n Hy Hn Hpos. apply nm_hull. intros s Hs Hv. geo_destr. pose proof asan_consts as AC.
apply nm_vis; [nm_lia | nm_lia | exact Hv].
Qed.

Lemma nm_vm_keep : forall a0 n v,
  (forall k, (k < n)%nat -> ~ ev_zc ac (a0 + Z.of_nat k) /\ 0 <= a0 + Z.of_nat k < 2 ^ 64) ->
  val_mem segs (rdW W mem) a0 n v -> val_mem segs (rdW W mem') a0 n v.
Proof.
intros a0 n v Hx. apply nm_vm. intros k0 Hk. destruct (Hx k0 Hk) as [Hn Hb]. exact (nm_HE _ Hb Hn).
Qed.

(* ---- the conjuncts of ev_mid at mem' ---- *)
Lemma nm_win :
  (forall z, ea_sp0 ac <= z < ea_sp0 ac + ea_d ac -> ~ inFP (ea_FP ac) z ->
     aview segs (w_H W) mem z = aview segs (w_H (ea_W ac)) (ea_mem ac) z) ->
  (forall z, ea_sp0 ac <= z < ea_sp0 ac + ea_d ac -> ~ inFP (ea_FP ac) z ->
     aview segs (w_H W) mem' z = aview segs (w_H (ea_W ac)) (ea_mem ac) z).
Proof.
intros H z Hz Hnf. geo_destr. pose proof asan_consts as AC.
assert (Hq1 : ~ (ea_q ac <= z < ea_q ac + 8)).
{ intros Hq. apply Hnf. exists (ea_q ac, ea_q ac + 8). split; [unfold ea_FP; right; left; reflexivity | cbn [fst snd]; lia]. }
assert (Hq2 : ~ (ea_q ac + 32 <= z < ea_q ac + 36)).
{ intros Hq. apply Hnf. exists (ea_q ac + 32, ea_q ac + 36).
  split; [unfold ea_FP; right; right; right; left; reflexivity | cbn [fst snd]; lia]. }
destruct (nm_stk z ltac:(lia) Hq1 Hq2) as (Hn & _ & Hr).
rewrite (nm_HE z ltac:(nm_lia) Hn). exact (H z Hz Hnf).
Qed.

Lemma nm_ledger :
  prh_ledger B ly S Hp W mem (ea_Lam ac) (ea_peak ac) (ea_cnt ac) (ea_fail ac) (ea_ran ac) (ea_most ac) (ea_own ac) ->
  prh_ledger B ly S Hp W mem' (ea_Lam ac) (ea_peak ac) (ea_cnt ac) (ea_fail ac) (ea_ran ac) (ea_most ac) (ea_own ac).
Proof.
intros ((G1 & G2 & G3 & G4 & G5 & (G6 & B6) & (G7 & B7) & Gn) & HND & HFB & Hperm).
assert (Hst : forall c n v, (forall k, (k < n)%nat -> Exists (in_zr (c + Z.of_nat k)) prh_pst) ->
  val_mem segs (rdW W mem) c n v -> val_mem segs (rdW W mem') c n v).
{ intros c n v Hc. apply nm_vm_keep. intros k0 Hk. exact (nm_pst _ (Hc k0 Hk)). }
refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ B6) (conj (conj _ B7) Gn)))))))
  (conj HND (conj _ Hperm))).
- apply Hst; [|exact G1]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_hd. unfold in_zr; cbn [fst snd]; lia.
- apply Hst; [|exact G2]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_tl, Exists_cons_hd. unfold in_zr; cbn [fst snd]; lia.
- apply Hst; [|exact G3]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr; cbn [fst snd]; lia.
- apply Hst; [|exact G4]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr; cbn [fst snd]; lia.
- apply Hst; [|exact G5]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr; cbn [fst snd]; lia.
- (* #102's g_most, the sixth static *)
  apply Hst; [|exact G6]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  unfold in_zr; cbn [fst snd]; lia.
- (* #102's g_own_ran_out, the seventh static *)
  apply Hst; [|exact G7]. intros k0 Hk. unfold prh_pst.
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  unfold in_zr; cbn [fst snd]; lia.
- rewrite Forall_forall in HFB |- *. intros [a0 k0] Hin. destruct (HFB _ Hin) as (Hk0 & Hb & HHp0 & Hal & Hvm).
  cbn [fst snd] in Hk0, Hb, HHp0, Hal, Hvm |- *.
  split; [exact Hk0|]. split; [exact Hb|]. split; [exact HHp0|]. split; [exact Hal|].
  apply nm_vm_keep; [|exact Hvm]. intros i Hi. geo_destr.
  destruct nm_scr as (bs & ms & Hbs & Hs1 & Hs2 & HsHp & _ & _ & _).
  pose proof (nm_req_ge (k0 + cf_head)) as Hrq.
  assert (Hns : ~ (ea_scr ac <= a0 - cf_head + Z.of_nat i < ea_scr ac + ea_len ac + 1)).
  { destruct (Z.eq_dec bs (a0 - cf_head)) as [Eb|Nb].
    - subst bs. specialize (HsHp HHp0). lia.
    - pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md bs ms (a0 - cf_head) (k0 + cf_head) GAR Hbs Hb
        ltac:(congruence)) as Hd.
      unfold zdisjoint in Hd; cbn [fst snd] in Hd. pose proof (nm_req_ge ms). lia. }
  assert (Hrange : a0 - cf_head <= a0 - cf_head + Z.of_nat i < a0 - cf_head + req_size (k0 + cf_head)).
  { pose proof CUTFIX_head. lia. }
  destruct (nm_blk (a0 - cf_head) (k0 + cf_head) (a0 - cf_head + Z.of_nat i) Hb Hrange Hns) as (Hn & _ & Hr).
  split; [exact Hn | unfold kHighMemEnd in Hr; lia].
Qed.

Lemma nm_txt_ok : forall z, ea_x0 ac <= z < ea_x0 ac + ea_len ac ->
  ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd.
Proof.
intros z Hz. pre_destr. destruct (Ptxt ltac:(lia)) as (bt & mt & Hin0 & Hb1 & Hb2 & _).
pose proof MIDH as (_ & _ & _ & Hab & _).
pose proof (nm_req_ge mt).
apply (nm_blk bt mt z); [rewrite Hab; exact Hin0 | lia | lia].
Qed.

Lemma nm_src : src_rd W mem (ea_x0 ac) (ea_x ac) -> src_rd W mem' (ea_x0 ac) (ea_x ac).
Proof.
intros (Sb & S0 & Sc & Sa & Sr & Sh).
change (Z.of_nat (length (ea_x ac))) with (ea_len ac) in *.
split; [|split; [exact S0 | split; [exact Sc | split; [exact Sa | split]]]].
- unfold bytes_at in *. apply (nm_garr8 segs (w_H W) mem mem'); [|exact Sb]. intros j Hj.
  destruct (nm_txt_ok (ea_x0 ac + Z.of_nat j) ltac:(unfold ea_len; lia)) as (Hn & _ & Hr).
  apply nm_HE; [unfold kHighMemEnd in Hr; lia | exact Hn].
- apply nm_ra_keep; [|exact Sr]. intros x Hx. destruct (nm_txt_ok x Hx) as (Hn & _ & Hr).
  destruct (nm_zc_fr _ _ Hn). auto.
- intros Hpos. apply nm_hull_keep; [lia | pose proof asan_consts as AC; unfold ea_len in Sc; nm_lia | lia | exact (Sh Hpos)].
Qed.

Lemma nm_wd : wdest_ok B (ea_STK ac) ly S W (ea_regs ac) mem (ea_scr ac) (ea_len ac + 1) ->
  wdest_ok B (ea_STK ac) ly S W (ea_regs ac) mem' (ea_scr ac) (ea_len ac + 1).
Proof.
intros (W0 & W1 & W2 & W3 & W4 & W5). geo_destr.
destruct nm_scr as (bs & ms & Hbs & Hs1 & Hs2 & _ & Hb0 & Hbc & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem' md' bs ms GAR' Hbs) as (_ & _ & _ & _ & Hpb & _).
split; [exact W0|]. split; [exact W1|]. split; [exact W2|]. split.
{ intros z Hz. destruct (W3 z Hz) as (_ & Ho & Hk). split; [|split; [exact Ho | exact Hk]].
  apply apresent_writable. exact (proj1 (Hpb z ltac:(lia))). }
split.
{ apply nm_ra_keep; [|exact W4]. intros x Hx. destruct (nm_blk0 bs ms x Hbs ltac:(lia)) as (Hf & _ & Hr & _).
  pose proof asan_consts as AC. split; [nm_lia | split; lia]. }
{ intros Hpos. apply nm_hull_keep; [lia | pose proof asan_consts as AC; nm_lia | lia | exact (W5 Hpos)]. }
Qed.

Lemma nm_tree :
  (ea_v ac = 0 \/ prhex_tree ly S (ea_Lam ac) W (ea_regs ac) mem (ea_v ac) (ea_t ac) (ea_D ac)) ->
  prh_ledger B ly S Hp W mem (ea_Lam ac) (ea_peak ac) (ea_cnt ac) (ea_fail ac) (ea_ran ac) (ea_most ac) (ea_own ac) ->
  (ea_v ac = 0 \/ prhex_tree ly S (ea_Lam ac) W (ea_regs ac) mem' (ea_v ac) (ea_t ac) (ea_D ac)).
Proof.
intros Ht Hled. pre_destr.
destruct Ptree as [Hv0|((_ & Hh0 & _) & _ & Hfoot)]; [left; exact Hv0|].
destruct Ht as [Hv|(Hn & Hh & Hra & Hhv)]; [left; exact Hv|]. right.
geo_destr.
destruct Hled as (_ & _ & HFB & _). rewrite Forall_forall in HFB.
assert (HLam : forall b0 m0 z, In (b0, m0) (ea_Lam ac) -> b0 <= z < b0 + m0 ->
  ~ (ea_scr ac <= z < ea_scr ac + ea_len ac + 1) -> ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd).
{ intros b0 m0 z HL Hz Hs. destruct (HFB _ HL) as (Hm0 & Hb & _). cbn [fst snd] in Hm0, Hb.
  pose proof (nm_req_ge (m0 + cf_head)). apply (nm_blk (b0 - cf_head) (m0 + cf_head) z Hb); [lia | exact Hs]. }
assert (Hroot : forall z, ea_v ac <= z < ea_v ac + 56 -> ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd).
{ intros z Hz. destruct (Hfoot z (or_introl Hz)) as (Hs & Hq & _ & _).
  destruct Hh0 as [(b0 & m0 & HL & H1 & H2) | [(c & p0 & Hc & H1 & H2) | (H1 & H2)]].
  - apply (HLam b0 m0 z HL); [lia | exact Hs].
  - rewrite !Gfa in H1, H2. apply (nm_frm0 c p0 z Hc). lia.
  - change (spZ (ea_regs ac)) with (ea_sp0 ac) in H1. apply nm_stk; lia. }
assert (HD : forall b, In b (ea_D ac) -> forall z, PRH_Reader.pj_holdsR b z ->
  ~ ev_zc ac z /\ ~ in_img segs z /\ 0 <= z < kHighMemEnd).
{ intros [a0 k0] Hb z Hz. unfold PRH_Reader.pj_holdsR in Hz; cbn [fst snd] in Hz.
  pose proof (nm_node_lblk _ _ _ _ _ _ Hn (a0, k0) Hb) as HL. cbn [fst snd] in HL. unfold prh_lin in HL.
  destruct (Hfoot z (or_intror (ex_intro _ (a0, k0) (conj Hb Hz)))) as (Hs & _).
  apply (HLam a0 k0 z HL); [lia | exact Hs]. }
split; [|split; [exact Hh|split]].
- apply (PRH_Reader.pj_nodeR_frame segs (ea_t ac) (rdW W mem) (rdW W mem') (prh_lin (ea_Lam ac)) (ea_v ac) (ea_D ac) Hn).
  intros x Hx.
  assert (Hc : ~ ev_zc ac x /\ ~ in_img segs x /\ 0 <= x < kHighMemEnd).
  { destruct Hx as [Hx|(b & Hb & Hx)]; [exact (Hroot _ Hx) | exact (HD b Hb _ Hx)]. }
  destruct Hc as (Hn' & Hni & Hrg). assert (Hr : 0 <= x < 2 ^ 64) by (unfold kHighMemEnd in Hrg; lia).
  pose proof (nm_HE x Hr Hn') as E.
  split; [exact (mbyte_of_aview segs (w_H W) (w_H W) mem mem' x E)|].
  exact (nm_wr segs (rdW W mem) (rdW W mem') x (nm_raw segs (w_H W) mem mem' x Hr Hni E)).
- apply nm_ra_keep; [|exact Hra]. intros x Hx. destruct (Hroot x Hx) as (Hn' & _ & Hrg).
  destruct (nm_zc_fr _ _ Hn'). auto.
- (* the root's hull: the root lies in [0, kHighMemEnd) (its home) *)
  destruct (Hroot (ea_v ac) ltac:(lia)) as (_ & _ & R0).
  destruct (Hroot (ea_v ac + 55) ltac:(lia)) as (_ & _ & R1).
  apply nm_hull_keep; [lia | lia | lia | exact Hhv].
Qed.

Lemma nm_saved : ev_saved ac W mem -> ev_saved ac W mem'.
Proof.
unfold ev_saved. intros Hs.
assert (Hr : Forall (fun orr : Z * Z => 152 <= fst orr <= 248) EV_SAVED)
  by (unfold EV_SAVED; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil).
rewrite Forall_forall in Hs, Hr |- *. intros orr Hin. apply nm_vm_keep; [|exact (Hs orr Hin)].
intros i Hi. specialize (Hr orr Hin). apply nm_save. geo_destr. unfold ea_SA. lia.
Qed.

Lemma nm_flagw :
  rdword (aview segs (w_H W) mem) (ea_fr ac + fs_frame_bytes 1 - 8) = Some (flag_addr (ea_ly ac) 1 (ea_pos ac)) ->
  rdword (aview segs (w_H W) mem') (ea_fr ac + fs_frame_bytes 1 - 8) = Some (flag_addr (ea_ly ac) 1 (ea_pos ac)).
Proof.
intros H. rewrite <- H. apply nm_rdword. intros z Hz. change (fs_frame_bytes 1) with 128 in Hz.
destruct (nm_flag z ltac:(lia)) as [Hn Hb]. exact (nm_HE _ Hb Hn).
Qed.

(* ev_mid at mem' for the cursor mem' holds; the room conjunct is the input's (same S) *)
Lemma nm_core : forall p' dl', prhex_cur W mem' (ea_q ac) p' (ea_x0 ac + ea_len ac) dep (ea_scr ac) dl' ->
  YAkMemnorm.memnorm segs mem' ->
  @ev_mid rc cp PI RL L PA B ARx SK ac ly S Hp W mem' md' k' p' dep dl'.
Proof.
intros p' dl' Hcur' Hmn.
pose proof MIDH as (HJ & HC2 & HHp & Hab & Hled & Hcur & Hsrc & Hwd & Htree & Hsv & Hflag & Hrl & Hrp & _).
split; [exact AJH|]. split; [exact (nm_win HC2)|]. split; [exact HHp|]. split; [exact Hab|].
split; [exact (nm_ledger Hled)|]. split; [exact Hcur'|]. split; [exact (nm_src Hsrc)|].
split; [exact (nm_wd Hwd)|]. split; [exact (nm_tree Htree Hled)|]. split; [exact (nm_saved Hsv)|].
split; [exact (nm_flagw Hflag)|]. split; [exact Hrl|]. split; [exact Hrp | exact Hmn].
Qed.

(* the cursor kept: its bytes lie on the real stack above sp0, outside ev_wz *)
Lemma nm_cur_keep :
  (forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B ac z -> aview segs (w_H W) mem' z = aview segs (w_H W) mem z) ->
  prhex_cur W mem (ea_q ac) p (ea_x0 ac + ea_len ac) dep (ea_scr ac) dl ->
  prhex_cur W mem' (ea_q ac) p (ea_x0 ac + ea_len ac) dep (ea_scr ac) dl.
Proof.
intros HEk (P0 & P1 & P2 & P3 & P4). geo_destr.
assert (Hq : forall z, ea_q ac <= z < ea_q ac + 40 -> aview segs (w_H W) mem' z = aview segs (w_H W) mem z).
{ intros z Hz. destruct (nm_stkw z ltac:(lia)) as [Hw _]. pose proof asan_consts as AC.
  apply HEk; [nm_lia | exact Hw]. }
split; [|split; [|split; [|split]]].
- apply (nm_vm segs (w_H W) mem mem'); [|exact P0]. intros k0 Hk. apply Hq. lia.
- apply (nm_vm segs (w_H W) mem mem'); [|exact P1]. intros k0 Hk. apply Hq. lia.
- apply (nm_vm segs (w_H W) mem mem'); [|exact P2]. intros k0 Hk. apply Hq. lia.
- apply (nm_vm segs (w_H W) mem mem'); [|exact P3]. intros k0 Hk. apply Hq. lia.
- apply (nm_vm segs (w_H W) mem mem'); [|exact P4]. intros k0 Hk. apply Hq. lia.
Qed.
End a.

Lemma ev_mid_keep : forall a, @ev_mid_keep_stmt fx rc cp PI RL L PA B ARx SK a.
Proof.
intros a. unfold ev_mid_keep_stmt. cbv zeta.
intros ly S Hp W mem md k p dep dl mem' md' k' PRE MID AJ HEk Hmn.
pose proof MID as (_ & _ & _ & _ & _ & Hcur & _).
eapply nm_core with (Zx := ev_wz B a); try eassumption.
- intros z H. left. exact H.
- eapply nm_cur_keep; eassumption.
Qed.

Lemma ev_mid_cur : forall a, @ev_mid_cur_stmt fx rc cp PI RL L PA B ARx SK a.
Proof.
intros a. unfold ev_mid_cur_stmt. cbv zeta.
intros ly S Hp W mem md k p dep dl mem' md' k' p' dl' PRE MID AJ HEc Hcur Hmn.
eapply nm_core with (Zx := ev_zc a); try eassumption.
- intros z H. exact H.
- intros z Hz Hn. apply HEc; [exact Hz | intros H; apply Hn; left; exact H | intros H; apply Hn; right; left; exact H
    | intros H; apply Hn; right; right; exact H].
Qed.
End m.
