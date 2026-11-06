(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepGluecf.v (commit f01d79f3fb5, cf refill round 3; file sha256 4f2fa4d6843b) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, the class-full report walk, slice F4 / RepF4Append's glue): placement and
   apartness facts of the error-message buffer's map, for the Realloc walk (RepF4Append.ReallocWalk, RepReallocf.v).
   rule 24: proves no function (kind: invariant lemmas, no machine code runs in this file; the lane's reuse search is
   `proof-index UnmapOrDie internal_memset internal_memcpy internal_strlen GetNamedMappingFd IncreaseTotalMmap`,
   2026-10-30T02:55Z, 0 released lemmas; the non-cf original YG0j.anon_grant_facts is in this tree).
   - anon_grant_facts_cf: the cf twin of YG0j.v:292 anon_grant_facts.  The proof body is YG0j's, with WfP_cf for WfP
     (YG0scf.v:152 wf_no_prim_hole_cf for YG02.wf_noholes, YG08cf.v:150 sec_extents_sizes64P_cf for
     YG08.sec_extents_sizes64P) and ALedger_cf for ALedger: the two fields that differ (alc_cover, alc_eager_x) are not
     read, the others sit at the same positions.
   - rep_grant_apart: a fresh grant of a page-multiple size is off the image (below TFIB_IMG_LO or at or above
     TFIB_IMG_END: grant_ok_na_pin and in_app allow [0x1000, 0x10000)), below the stack window and apart from the
     errbuf vector object C_ERRBUF_VEC (three words).
   - rep_buf_apart: the same for the current errbuf buffer [errb_data_cf, errb_data_cf + errb_cap_cf), with its
     page alignment and its map in the model. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08 YK0v YK13 YA05 YA06 YG0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0f YG0v YG0n YG0s YG08 YG0h YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0scf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RepIFcf.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* 1. YG0j.v:292's anon_grant_facts at the cf invariant and ledger. *)
Lemma anon_grant_facts_cf : forall U pp cc bb (ly : alayout) (S : astate) (md : Model) (a n : word),
layout_ok ly -> WfP_cf U pp cc bb S -> sec_placed ly S -> ALedger_cf tfibsegs ly S md ->
grant_ok_na_pin md a (bv_unsigned n) = true -> 0 < bv_unsigned n -> bv_unsigned n mod 4096 = 0 ->
page_aligned (bv_unsigned a) /\ in_app (bv_unsigned a) (bv_unsigned n) /\ bv_unsigned a + bv_unsigned n <= ASAN_CEIL /\
Forall (zdisjoint (bv_unsigned a, bv_unsigned n)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
intros U pp cc bb ly S md a n LO W PL L G Hn Hnal.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1.
assert (Hn64 : Z_to_bv 64 (bv_unsigned n) = n) by (apply w64_uw). rewrite Hn64 in G4.
set (lo := bv_unsigned a) in *. set (len := bv_unsigned n) in *.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (CE : lo + len <= ASAN_CEIL).
{ unfold ASAN_CEIL. apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md)) (lo + len) L13); [| exact G3].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. apply Z.mod_divide in Hnal as [q' Hq']; [|lia]. rewrite Hq, Hq'.
replace (q * 4096 + q' * 4096) with ((q + q') * 4096) by lia. apply Z_mod_mult. }
ceil.
assert (RF : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 ->
In (wiv z) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. pose proof (YK13.region_free_In _ a n (w64 (fst z)) (w64 (snd z)) G4 Hin) as D.
unfold w64 in D. rewrite !Z_to_bv_unsigned, !bv_wrap_small in D by (unfold bv_modulus; lia). unfold zdisjoint. cbn [fst snd]. subst lo len. lia. }
assert (RFm : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 -> In (wiv z) (vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. apply RF; [exact Z1 | exact Z2 | exact Z3 | apply in_app_iff; right; exact Hin]. }
assert (BAND : Forall (zdisjoint (lo, len)) band_maps).
{ apply Forall_forall. intros z Hz. apply RFm; [ | | | exact (L11 z Hz)]; unfold band_maps in Hz; cbn in Hz;
destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia. }
assert (APP : in_app lo len).
{ pose proof BAND as B'. unfold band_maps in B'. apply Forall_cons_iff in B' as [D1 B']. apply Forall_cons_iff in B' as [D2 B']. apply Forall_cons_iff in B' as [D3 _].
unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
split; [| clear - D1 D2 D3 Hn CE CR0; lia].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. subst lo len. clear - Hq G2. lia. }
split; [exact G1|]. split; [exact APP|]. split; [exact CE|].
pose proof (lo_high ly LO) as [HP1 HP2].
assert (PRIM : zdisjoint (lo, len) (ly_prim ly, kPrimResvSize)).
{ destruct L4 as (pieces & (P1 & P2 & P3) & P4).
unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (ly_prim ly + kPrimResvSize)) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (ly_prim ly) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (ly_prim ly)).
assert (Hx : ly_prim ly <= x < ly_prim ly + kPrimResvSize) by (subst x; unfold kPrimResvSize in *; lia).
assert (NH : ~ prim_hole_at ly S x) by exact (wf_no_prim_hole_cf U pp cc bb S ly x W).
apply (P3 x Hx) in NH. apply Exists_exists in NH as (p0 & Hp0 & Hin0). unfold in_zr in Hin0.
pose proof (proj1 (P4 p0) Hp0) as (Hm0 & C1 & C2 & C3).
pose proof (RFm p0 ltac:(unfold kHighMemBeg in HP1; lia) ltac:(lia) ltac:(clear - C2 C3 HP1 HP2 CR CR0; unfold kPrimResvSize, kHighMemBeg, ASAN_CEIL in *; lia) Hm0) as D.
unfold zdisjoint in D. cbn [fst snd] in D. subst x. lia. }
pose proof (lo_stk_ceil ly LO) as STK.
assert (IMG : zdisjoint (lo, len) (ly_img ly)).
{ pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3). unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (fst (ly_img ly) + snd (ly_img ly))) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (fst (ly_img ly)) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (fst (ly_img ly))).
destruct (L14 x ltac:(unfold in_zr; subst x; lia)) as (e & He & E1).
pose proof (YK13.region_free_In _ a n (fst e) (snd e) G4 ltac:(apply in_app_iff; left; rewrite L3, <- surjective_pairing; exact He)) as D.
subst lo len x. lia. }
assert (PERM : Forall (zdisjoint (lo, len)) (perm_maps ly)).
{ apply Forall_forall. intros z Hz. pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _). apply RFm; [lia | lia | lia | exact (L10 z Hz)]. }
assert (QQ : zdisjoint (lo, len) (ly_Q ly, kPtrArrayResv)).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [Q1 Q2]. cbn [fst snd] in Q1, Q2.
apply RFm; [cbn [fst]; lia | cbn [snd]; unfold kPtrArrayResv; lia | cbn [fst snd]; unfold kLowShadowBeg, kPtrArrayResv, ASAN_CEIL in *; lia | exact L5]. }
assert (SEC : Forall (zdisjoint (lo, len)) (sec_extents ly S)).
{ apply Forall_forall. intros e He. destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [E1 E2] & E3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_sizes64P_cf U pp cc bb ly S W) e He) as E4. cbn beta in E4.
apply RFm; [lia | lia | unfold ASAN_CEIL in *; lia | exact (L7 e He)]. }
rewrite !Forall_app. split; [| split; [exact SEC | split; [exact PERM | exact BAND]]].
unfold static_extents, owned_extents. apply Forall_app. split.
- pose proof PERM as PM. unfold perm_maps in PM. apply Forall_app in PM as [PM _].
apply Forall_cons_iff in PM as [PT PM]. apply Forall_cons_iff in PM as [PFk PM]. apply Forall_cons_iff in PM as [PNB PM].
apply Forall_cons_iff in PM as [PSB PM]. apply Forall_cons_iff in PM as [PC PM]. apply Forall_cons_iff in PM as [PD _].
repeat apply Forall_cons; try apply Forall_nil; try assumption.
unfold zdisjoint in PC |- *. cbn [fst snd] in PC |- *. unfold kCtxMapSize in PC. lia.
- apply Forall_cons; [| apply Forall_cons; [exact IMG | apply Forall_nil]].
unfold zdisjoint. cbn [fst snd]. left. unfold ASAN_CEIL in *. lia.
Qed.

(* the image extent of static_extents *)
Lemma rg_img_of_static : forall (ly : alayout) (e : Z * Z),
Forall (zdisjoint e) (static_extents ly) -> zdisjoint e (ly_img ly).
Proof.
intros ly e F. unfold static_extents in F. apply Forall_app in F as [_ F].
apply Forall_cons_iff in F as [_ F]. apply Forall_cons_iff in F as [F _]. exact F.
Qed.

(* off the image: [kImgLo, kImgLo + snd (ly_img ly)) covers [TFIB_IMG_LO, TFIB_IMG_END) (img_cover) *)
Lemma rg_off_img : forall (ly : alayout) (lo len : Z),
layout_ok ly -> img_cover ly -> zdisjoint (lo, len) (ly_img ly) -> lo + len <= TFIB_IMG_LO \/ TFIB_IMG_END <= lo.
Proof.
intros ly lo len LO [_ IC2] D. pose proof (lo_img ly LO) as (J0 & _). unfold zdisjoint in D. cbn [fst snd] in D.
rewrite J0 in D, IC2. unfold kImgLo, TFIB_IMG_LO in *. lia.
Qed.

(* 2. GAPART: every grant of a page-multiple size [ncap] is off the image, below a stack window above ly_stk_lo, and
   apart from the vector object C_ERRBUF_VEC (data / capacity / size). *)
Lemma rep_grant_apart : forall (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) (ncap sp K : Z),
errb_call_pre B lk Hp ly S W mem md -> 0 < ncap -> ncap mod 4096 = 0 -> ly_stk_lo ly <= sp - K -> sp < 2 ^ 64 ->
forall a', grant_ok_na_pin md (w64 a') ncap = true ->
(a' + ncap <= TFIB_IMG_LO \/ TFIB_IMG_END <= a') /\ (a' + ncap <= sp - K \/ sp <= a') /\
(a' + ncap <= C_ERRBUF_VEC \/ C_ERRBUF_VEC + 24 <= a').
Proof.
intros lk Hp ly S W mem md ncap sp K PRE Hn Hal HSTK Hsp a' G.
destruct PRE as (_ & _ & LO & IC & _ & _ & (_ & AR & _) & _).
destruct AR as (M & L & _).
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_placed _ _ _ _ _ M) as PL.
pose proof G as G0. unfold grant_ok_na_pin in G0. apply andb_prop in G0 as [G0 _]. apply andb_prop in G0 as [_ G3]. apply Z.leb_le in G3.
assert (ATL : alloc_top (m_vmmaps md) < 2 ^ 64) by (unfold alloc_top, stack_max_size; pose proof (u64_range (vm_init_sp (m_vmmaps md))); lia).
pose proof (u64_range (w64 a')) as Ra.
assert (Hn64 : bv_unsigned (w64 ncap) = ncap) by (unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
assert (G' : grant_ok_na_pin md (w64 a') (bv_unsigned (w64 ncap)) = true) by (rewrite Hn64; exact G).
destruct (anon_grant_facts_cf _ 0 0 0 ly S md (w64 a') (w64 ncap) LO WF PL L G' ltac:(lia) ltac:(rewrite Hn64; exact Hal))
  as (_ & FA2 & FA3 & FA4).
rewrite Hn64 in FA2, FA3, FA4.
apply Forall_app in FA4 as [FS _]. pose proof (rg_off_img ly _ _ LO IC (rg_img_of_static ly _ FS)) as OFF.
pose proof (lo_stk_ceil ly LO) as STK. ceil.
assert (Ea : bv_unsigned (w64 a') = a' mod 2 ^ 64) by (unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
pose proof (Z.div_mod a' (2 ^ 64) ltac:(lia)) as DM. rewrite <- Ea in DM.
set (g := bv_unsigned (w64 a')) in *. set (q := a' / 2 ^ 64) in *.
unfold in_app in FA2. unfold TFIB_IMG_LO, TFIB_IMG_END, C_ERRBUF_VEC, ASAN_CEIL in *.
split; [|split]; lia.
Qed.

(* 3. The current buffer: off the image, below the stack window, apart from the object, page-aligned and mapped. *)
Lemma rg_last_cap_none : forall l i acc, last_cap_idx l i acc = None -> acc = None /\ List.filter is_errb_cap l = [].
Proof.
induction l as [|sm t IH]; intros i acc H; cbn [last_cap_idx List.filter] in *; [split; [exact H | reflexivity]|].
destruct (is_errb_cap sm) eqn:E.
- destruct (IH _ _ H) as [X _]. discriminate X.
- exact (IH _ _ H).
Qed.

Lemma rg_cap_none : forall S, last_cap_idx (st_secs S) 0 None = None -> errb_cap_cf S = 0.
Proof.
intros S E. destruct (rg_last_cap_none _ _ _ E) as [_ F].
unfold errb_cap_cf, errb_e. rewrite F. reflexivity.
Qed.

Lemma rep_buf_apart : forall (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) (sp K : Z),
errb_call_pre B lk Hp ly S W mem md -> ly_stk_lo ly <= sp - K ->
let d := YG0ncf.errb_data_cf ly S in let cap := errb_cap_cf S in
(d + cap <= sp - K \/ sp <= d) /\ (d + cap <= C_ERRBUF \/ C_ERRBUF + 56 <= d) /\ cap mod 4096 = 0 /\
((d = 0 /\ cap = 0) \/
 (d mod 4096 = 0 /\ 4096 <= d /\ (d + cap <= TFIB_IMG_LO \/ TFIB_IMG_END <= d) /\ d + cap <= ASAN_CEIL /\
  In (w64 d, w64 cap) (vm_maps (m_vmmaps md)))).
Proof.
intros lk Hp ly S W mem md sp K PRE HSTK. cbv zeta.
pose proof PRE as (_ & _ & LO & IC & _ & _ & (_ & AR & _) & XM & _ & _ & _ & EC & _).
pose proof (YGcfInstBase.errb_cells_cf_szcap B _ _ _ EC) as [_ CM]. unfold kPage in CM.
pose proof (xs_placed_of_ARcf tfibsegs B ly S Hp W _ md AR) as XP.
pose proof (lo_stk_ceil ly LO) as STK. ceil.
pose proof (errb_cap_cf_nonneg S) as C0.
destruct (last_cap_idx (st_secs S) 0 None) as [i|] eqn:E.
- assert (Ed : YG0ncf.errb_data_cf ly S = ly_sec ly i) by (unfold YG0ncf.errb_data_cf; rewrite E; reflexivity).
  rewrite Ed.
  assert (INX : In (ly_sec ly i, errb_cap_cf S) (xs_cf ly S)) by (unfold xs_cf; rewrite E; left; reflexivity).
  unfold xs_placed_cf in XP. pose proof (proj1 (Forall_forall _ _) XP _ INX) as (PA & IA & CE & DJ). cbn [fst snd] in PA, IA, CE, DJ.
  apply Forall_app in DJ as [_ DJ]. apply Forall_app in DJ as [DS _].
  pose proof (rg_off_img ly _ _ LO IC (rg_img_of_static ly _ DS)) as OFF.
  pose proof (XM _ INX) as MAP. unfold wiv in MAP. cbn [fst snd] in MAP.
  unfold page_aligned in PA. unfold in_app in IA.
  split; [|split; [|split; [exact CM|]]].
  + left. unfold ASAN_CEIL in *. lia.
  + unfold TFIB_IMG_LO, TFIB_IMG_END, C_ERRBUF in *. lia.
  + right. split; [exact PA|]. split; [lia|]. split; [exact OFF|]. split; [unfold ASAN_CEIL; exact CE | exact MAP].
- assert (Ed : YG0ncf.errb_data_cf ly S = 0) by (unfold YG0ncf.errb_data_cf; rewrite E; reflexivity).
  rewrite Ed, (rg_cap_none S E).
  split; [|split; [|split]].
  + left. unfold ASAN_CEIL in *. lia.
  + left. unfold C_ERRBUF. lia.
  + reflexivity.
  + left. split; reflexivity.
Qed.

(* 4. A grant is below the whole stack span: below the ceiling, which is at or below ly_stk_lo (lo_stk_ceil).  With
   a' a 64-bit value this is the strong form; for an arbitrary integer a' (w64 wraps) the disjunction. *)
Lemma rep_grant_below_ceil : forall (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate)
  (W : world tfibsegs) (mem : word -> option byte) (md : Model) (ncap : Z),
errb_call_pre B lk Hp ly S W mem md -> 0 < ncap -> ncap mod 4096 = 0 ->
forall a', 0 <= a' < 2 ^ 64 -> grant_ok_na_pin md (w64 a') ncap = true ->
  a' + ncap <= ASAN_CEIL /\ ASAN_CEIL <= ly_stk_lo ly.
Proof.
intros lk Hp ly S W mem md ncap PRE Hn Hal a' Ha G.
destruct PRE as (_ & _ & LO & _ & _ & _ & (_ & AR & _) & _).
destruct AR as (M & L & _).
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_placed _ _ _ _ _ M) as PL.
pose proof G as G0. unfold grant_ok_na_pin in G0. apply andb_prop in G0 as [G0 _]. apply andb_prop in G0 as [_ G3]. apply Z.leb_le in G3.
assert (ATL : alloc_top (m_vmmaps md) < 2 ^ 64) by (unfold alloc_top, stack_max_size; pose proof (u64_range (vm_init_sp (m_vmmaps md))); lia).
pose proof (u64_range (w64 a')) as Ra.
assert (Hn64 : bv_unsigned (w64 ncap) = ncap) by (unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
assert (G' : grant_ok_na_pin md (w64 a') (bv_unsigned (w64 ncap)) = true) by (rewrite Hn64; exact G).
destruct (anon_grant_facts_cf _ 0 0 0 ly S md (w64 a') (w64 ncap) LO WF PL L G' ltac:(lia) ltac:(rewrite Hn64; exact Hal))
  as (_ & _ & FA3 & _).
assert (Ea : bv_unsigned (w64 a') = a') by (unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
rewrite Hn64, Ea in FA3. split; [exact FA3 | exact (lo_stk_ceil ly LO)].
Qed.

Lemma rep_grant_above_stack : forall (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate)
  (W : world tfibsegs) (mem : word -> option byte) (md : Model) (ncap : Z),
errb_call_pre B lk Hp ly S W mem md -> 0 < ncap -> ncap mod 4096 = 0 ->
forall a', grant_ok_na_pin md (w64 a') ncap = true ->
  a' + ncap <= ly_stk_lo ly \/ ly_stk_hi ly <= a'.
Proof.
intros lk Hp ly S W mem md ncap PRE Hn Hal a' G.
destruct PRE as (_ & _ & LO & _ & _ & _ & (_ & AR & _) & _).
destruct AR as (M & L & _).
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_placed _ _ _ _ _ M) as PL.
pose proof G as G0. unfold grant_ok_na_pin in G0. apply andb_prop in G0 as [G0 _]. apply andb_prop in G0 as [_ G3]. apply Z.leb_le in G3.
assert (ATL : alloc_top (m_vmmaps md) < 2 ^ 64) by (unfold alloc_top, stack_max_size; pose proof (u64_range (vm_init_sp (m_vmmaps md))); lia).
pose proof (u64_range (w64 a')) as Ra.
assert (Hn64 : bv_unsigned (w64 ncap) = ncap) by (unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
assert (G' : grant_ok_na_pin md (w64 a') (bv_unsigned (w64 ncap)) = true) by (rewrite Hn64; exact G).
destruct (anon_grant_facts_cf _ 0 0 0 ly S md (w64 a') (w64 ncap) LO WF PL L G' ltac:(lia) ltac:(rewrite Hn64; exact Hal))
  as (_ & _ & FA3 & _).
rewrite Hn64 in FA3.
pose proof (lo_stk_ceil ly LO) as STK. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & _). ceil.
assert (Ea : bv_unsigned (w64 a') = a' mod 2 ^ 64) by (unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
pose proof (Z.div_mod a' (2 ^ 64) ltac:(lia)) as DM. rewrite <- Ea in DM.
set (g := bv_unsigned (w64 a')) in *. set (q := a' / 2 ^ 64) in *.
unfold ASAN_CEIL, kHighMemEnd in *. lia.
Qed.
End a.
