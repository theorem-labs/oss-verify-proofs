(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcConst.v (commit 6fdbdd538bcf, H4 flag-free secondary Recycle walk set; file sha256 44f8c034269d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; 14 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcConst.v at commit edc7f827e38, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (15 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4): the frame lemmas of the image's CONSTANT cells (as_const) for the two walks
   of __asan::QuarantineCallback::Recycle (0x33e88).  rc_prim_const: memory equal off the primary walk's windows
   (YFgs.WIN) keeps every const cell (as YFg7.CONST_OUT, with the chunk's place in the primary region from YFgs.free_hyps).
   rc_sec_const: memory equal off the secondary walks' windows (DMrcSecMun.WPRE, DMrcSecGv.WIN3), with the allocator mutex
   word at A_ALLOCATOR + 680 rewritten to 0, keeps every const cell (as YFf4.CONST', with the geometry from the fields of
   DMrcSecFc.sec_cut).
   rule 24: no function proved (kind: frame lemmas about the image's constant cells, for two walks already proved). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb YFg8 YFfc YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecWalk DMrcSecF6 DMrcSecF7 DMrcSecF9 DMrcSecMun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT MemnormLocG MemnormSafereply DMrcReads DMrcSecReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DIfaceR DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YFfn YA05 YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFg7 YFf4 YFgs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Ltac cnum := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL,
  kThreadObjSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, KSTACK, t_stats, A_ALLOCATOR, TFIB_INST, TFIB_TSD, TFIB_TP, kPage in *.

(* YFg7.GEO from the layout and the image cover alone. *)
Lemma GEO_ly : forall ly, layout_ok ly -> img_cover ly ->
(ly_prim ly + kPrimResvSize <= ly_T ly \/ ly_T ly + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_prim ly) /\
(ly_T ly + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= ly_T ly) /\
(ly_T ly + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= ly_T ly) /\
(ly_T ly + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_T ly) /\
(ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_C ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly) /\
zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
intros ly LO IMG.
pose proof (lo_disj ly LO) as HD.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear; lia) (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(clear; lia) (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK. cbn [fst snd] in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* ---------- (1) the primary walk's windows (YFgs.WIN) ---------- *)
Section p.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (c base rz nn hb1 cbp muc j1 j2 : Z).
Hypothesis FH : YFgs.free_hyps W ly regs mem c base rz nn hb1 cbp muc j1 j2.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation WINr := (YFgs.WIN ly regs base rz nn).
(* YFg7.WIN_zone, with the chunk's place in the primary region from the record *)
Lemma WIN_zone_p : forall a, WINr a -> (sp0 - 256 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/
  (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/ (0x2008fff7000 <= a < kHighMemBeg).
Proof.
intros a Hw.
pose proof (YFgs.derived_ranges W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dB1 & dB2 & _ & _ & dM & dU & _ & _ & dBM & dUN & _ & _ & dN1 & dRZ & dSP1 & dSP2 & _).
pose proof (YFgs.LYB W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as (_ & _ & _ & L4 & L5 & _).
pose proof (YFgs.class_facts W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as (K1 & _).
unfold YFgs.WIN, YFgs.WINF, YFgs.WINS in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[[_ Hw]|Hw]]|Hw]].
- left. exact Hw.
- do 2 right; left. clear - Hw dB1 dB2 dM dU dUN dN1 dBM L4 L5. unfold kSpaceSize, kPrimResvSize, YFgs.Mv, YFgs.Uv in *. lia.
- do 2 right; left. clear - Hw dB1 dB2 K1 L4 L5. unfold kSpaceSize, kMaxSize, kPrimResvSize in *. lia.
- right; left. clear - Hw. unfold kThreadObjSize, t_stats in *. lia.
- do 3 right. clear - Hw dSP1 dSP2. lia.
Qed.
Lemma CONST_OUT_p : Forall (fun ce => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w ce)) ->
  ~ WINr (aeval B ly (c_at ce) + i) /\ 0 <= aeval B ly (c_at ce) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros ce Hce i Hi.
pose proof (proj1 (forallb_forall _ _) (YFg7.Tfib_const_locr ly) ce Hce) as K. unfold YFg7.const_loc_okr in K.
pose proof (YFgs.LYB W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as
  (hT1 & hT2 & hP1 & _ & _ & hP2 & _ & _ & _ & _ & hS1 & G_TP & G_TS & G_PS & _).
pose proof (YFgs.fh_Hsp W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as [S1 S2]. fold sp0 in S1, S2.
pose proof (GEO_ly ly (YFgs.fh_LY _ _ _ _ _ _ _ _ _ _ _ _ _ FH) (YFgs.fh_IMG _ _ _ _ _ _ _ _ _ _ _ _ _ FH))
  as (G_PT & G_PC & G_PD & G_PS' & G_TC & G_TD & G_TS' & G_CD & G_CS & G_DS & ZC & ZD).
assert (ZN : forall a, ~ ((sp0 - 256 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/ (0x2008fff7000 <= a < kHighMemBeg)) -> ~ WINr a).
{ intros a Hn Hw. exact (Hn (WIN_zone_p a Hw)). }
assert (LOW : forall a, YFg7.low_okr a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ WINr (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L'. unfold YFg7.low_okr in L'.
  split; [apply ZN|]; clear - L' Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *;
  change (65536 / 8) with 8192 in *; change (6275072 / 8) with 784384 in *; lia. }
destruct (c_at ce); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS'; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi ZC S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi ZD S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
Qed.
End p.

Lemma rc_prim_const : forall (B : asyms), TfibSyms B -> forall (W : world tfibsegs) ly regs mem c base rz nn hb1 cbp muc j1 j2 (mem' : word -> option byte),
  YFgs.free_hyps W ly regs mem c base rz nn hb1 cbp muc j1 j2 ->
  ly_tsd ly = TFIB_TSD ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) ->
  (forall x : word, ~ YFgs.WIN ly regs base rz nn (bv_unsigned x) -> mem' x = mem x) ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly).
Proof.
intros B TB W ly regs mem c base rz nn hb1 cbp muc j1 j2 mem' FH HTSD OLD KEEP.
pose proof (CONST_OUT_p B TB W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH HTSD) as OUT.
apply Forall_forall. intros ce Hce.
apply (cell_holds_agree B ly (aview tfibsegs (w_H W) mem)); [exact (proj1 (Forall_forall _ _) OLD ce Hce)|].
intros i Hi. destruct (proj1 (Forall_forall _ _) OUT ce Hce i Hi) as [Y1 Y2]. apply aview_same.
apply KEEP. rewrite unsigned_lit_small by exact Y2. exact Y1.
Qed.

(* ---------- (2) the secondary walks' windows (DMrcSecMun.WPRE, DMrcSecGv.WIN3) ---------- *)
Section s.
Variable B : asyms.
Variables (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis SC : DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation qi := (YFg8.qi ly i).
Local Notation lst := (YFg8.lst ly X r).
Definition oks (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ~ DMrcSecMun.WPRE ly regs a /\ ~ DMrcSecGv.WIN3 ly regs MAP LEN qi lst a.
(* the windows' zones: every byte of WPRE \/ WIN3 is in one of these *)
Lemma WIN_zone_s : forall a, DMrcSecMun.WPRE ly regs a \/ DMrcSecGv.WIN3 ly regs MAP LEN qi lst a ->
  (sp0 - DMrcSecGv.GDEPTH <= a < sp0) \/
  (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (A_ALLOCATOR + 120 <= a < A_ALLOCATOR + 129) \/
  (A_ALLOCATOR + 144 <= a < A_ALLOCATOR + 160) \/ (A_ALLOCATOR + 704 <= a < A_ALLOCATOR + 720) \/
  (Q <= a < Q + kPtrArrayResv) \/ (T + 80 <= a < T + kThreadObjSize) \/ (lst + 24 <= a < lst + 32) \/
  (DMrcSecGv.SHAv MAP <= a < DMrcSecGv.SHAv MAP + DMrcSecGv.CNTv LEN) \/ (MAP <= a < MAP + LEN).
Proof.
intros a Hw.
pose proof (DMrcSecFc.sc_ARRF _ _ _ _ _ _ _ _ _ _ _ SC) as (_ & _ & _ & AN1 & AN2).
unfold DMrcSecMun.WPRE, DMrcSecGv.WIN3, DMrcSecGv.WIN, DMrcSecGv.WINS, DMrcSecGv.WINM in Hw. fold sp0 in Hw.
unfold YFg8.qi, YFg8.idx, YFg8.nA in *.
destruct Hw as [[Hw|[Hw|Hw]]|[[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]]]|[Hw|Hw]]].
all: first
  [ left; exact Hw
  | right; left; exact Hw
  | do 2 right; left; exact Hw
  | do 3 right; left; exact Hw
  | do 4 right; left; exact Hw
  | do 5 right; left; clear - Hw AN1 AN2; unfold kPtrArrayResv in *; lia
  | do 6 right; left; clear - Hw; unfold kThreadObjSize, t_stats in *; lia
  | do 7 right; left; exact Hw
  | do 8 right; left; exact Hw
  | do 9 right; exact Hw ].
Qed.
(* the map's shadow lies in the low/high shadow gap, off the image's own shadow *)
Lemma SHB : forall m l, zone3 m l -> 0 <= l ->
  kLowShadowBeg <= DMrcSecGv.SHAv m /\ DMrcSecGv.SHAv m + DMrcSecGv.CNTv l <= kHighMemBeg /\
  (DMrcSecGv.SHAv m + DMrcSecGv.CNTv l <= SHADOW_OFF + 8192 \/ SHADOW_OFF + 784384 <= DMrcSecGv.SHAv m).
Proof.
intros m l (Z0 & Z1 & Z2) L0. unfold DMrcSecGv.SHAv, DMrcSecGv.CNTv. ceil.
assert (D1 : m / 8 + l / 8 <= (m + l) / 8) by (Z.div_mod_to_equations; lia).
assert (D2 : 0 <= m / 8) by (apply Z.div_pos; lia).
splits.
- clear - D2. unfold kLowShadowBeg, SHADOW_OFF. lia.
- assert (D3 : (m + l) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; unfold ASAN_CEIL in *; lia).
  change (0x7fffff800000 / 8) with 17592184995840 in D3. clear - D1 D2 D3. unfold kHighMemBeg, SHADOW_OFF. lia.
- unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in Z2. destruct Z2 as [Z2|[[Z2 _]|[Z2 _]]].
  + left. assert (D3 : (m + l) / 8 <= 65536 / 8) by (apply Z.div_le_mono; lia). change (65536 / 8) with 8192 in D3. clear - D1 D3. lia.
  + right. assert (D3 : 6275072 / 8 <= m / 8) by (apply Z.div_le_mono; lia). change (6275072 / 8) with 784384 in D3. clear - D3. lia.
  + right. assert (D3 : 6275072 / 8 <= m / 8) by (apply Z.div_le_mono; lia). change (6275072 / 8) with 784384 in D3. clear - D3. lia.
Qed.
Lemma GEO_s :
  kHighMemBeg + KSTACK <= sp0 /\ ASAN_CEIL <= ly_stk_lo ly /\ ly_stk_lo ly + KSTACK <= sp0 /\
  zone3 Q kPtrArrayResv /\ zone3 T kThreadObjSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096 /\
  zone3 lst 8192 /\ zone3 MAP LEN /\
  (kLowShadowBeg <= DMrcSecGv.SHAv MAP /\ DMrcSecGv.SHAv MAP + DMrcSecGv.CNTv LEN <= kHighMemBeg /\
   (DMrcSecGv.SHAv MAP + DMrcSecGv.CNTv LEN <= SHADOW_OFF + 8192 \/ SHADOW_OFF + 784384 <= DMrcSecGv.SHAv MAP)) /\
  (T + kThreadObjSize <= Q \/ Q + kPtrArrayResv <= T) /\ (ly_C ly + 256 <= Q \/ Q + kPtrArrayResv <= ly_C ly) /\
  (ly_D ly + 4096 <= Q \/ Q + kPtrArrayResv <= ly_D ly) /\
  (T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\ (T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
  (ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
  (exists sz, 32 <= sz /\ (lst + sz <= T \/ T + kThreadObjSize <= lst) /\ (lst + sz <= ly_C ly \/ ly_C ly + 256 <= lst) /\
     (lst + sz <= ly_D ly \/ ly_D ly + 4096 <= lst)) /\
  (MAP + LEN <= T \/ T + kThreadObjSize <= MAP) /\ (MAP + LEN <= ly_C ly \/ ly_C ly + 256 <= MAP) /\
  (MAP + LEN <= ly_D ly \/ ly_D ly + 4096 <= MAP).
Proof.
pose proof (DMrcSecFc.sc_HI _ _ _ _ _ _ _ _ _ _ _ SC) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hTC & hTQ & hCQ).
pose proof (DMrcSecFc.sc_HSP _ _ _ _ _ _ _ _ _ _ _ SC) as [S1 S2]. fold sp0 in S1, S2.
pose proof (GEO_ly ly (DMrcSecFc.sc_LO _ _ _ _ _ _ _ _ _ _ _ SC) (DMrcSecFc.sc_IMG _ _ _ _ _ _ _ _ _ _ _ SC))
  as (_ & _ & _ & _ & G_TC & G_TD & _ & G_CD & _ & _ & ZC & ZD).
pose proof (DMrcSecFc.sc_last_facts _ _ _ _ _ _ _ _ _ _ _ SC) as (_ & _ & _ & _ & _ & LZ1 & _).
pose proof (DMrcSecFc.sc_GEOM _ _ _ _ _ _ _ _ _ _ _ SC) as (GZ & _ & _ & GL & _).
pose proof (SHB MAP LEN GZ ltac:(clear - GL; lia)) as (SH1 & SH2 & SH3).
pose proof (DMrcSecFc.sc_ELEN _ _ _ _ _ _ _ _ _ _ _ SC) as (EL & _).
pose proof (DMrcSecFc.sc_SX _ _ _ _ _ _ _ _ _ _ _ SC 7 1 _ _ eq_refl eq_refl ltac:(lia)) as DQ. unfold zdisjoint in DQ. cbn [fst snd] in DQ.
pose proof (DMrcSecFc.sc_LST _ _ _ _ _ _ _ _ _ _ _ SC) as (y & _ & _ & LIN & _ & _ & _ & LSZ & _).
change (YFf4.lst ly X r) with lst in LIN.
pose proof (DMrcSecFc.sc_SECX _ _ _ _ _ _ _ _ _ _ _ SC _ 2 _ LIN eq_refl) as LT.
pose proof (DMrcSecFc.sc_SECX _ _ _ _ _ _ _ _ _ _ _ SC _ 6 _ LIN eq_refl) as LC.
pose proof (DMrcSecFc.sc_SECX _ _ _ _ _ _ _ _ _ _ _ SC _ 7 _ LIN eq_refl) as LD.
pose proof (DMrcSecFc.sc_MAPX _ _ _ _ _ _ _ _ _ _ _ SC 2 _ eq_refl) as MT.
pose proof (DMrcSecFc.sc_MAPX _ _ _ _ _ _ _ _ _ _ _ SC 6 _ eq_refl) as MC.
pose proof (DMrcSecFc.sc_MAPX _ _ _ _ _ _ _ _ _ _ _ SC 7 _ eq_refl) as MD.
change (YFf4.MAP ly r) with MAP in MT, MC, MD. change (YFf4.LEN k) with (sec_map_size (ck_req k)) in MT, MC, MD. rewrite <- EL in MT, MC, MD.
unfold zdisjoint in LT, LC, LD, MT, MC, MD. cbn [fst snd] in LT, LC, LD, MT, MC, MD.
split; [clear - S1 hS1; unfold KSTACK, kHighMemBeg in *; lia|].
splits; try assumption.
exists (sec_map_size (ck_req y)). split; [clear - LSZ; lia|]. splits; assumption.
Qed.
Ltac win_cases a Hw Zw :=
  split; intros Hw; [pose proof (WIN_zone_s a (or_introl Hw)) as Zw | pose proof (WIN_zone_s a (or_intror Hw)) as Zw]; clear Hw;
  unfold DMrcSecGv.GDEPTH in Zw;
  destruct Zw as [Zw|[Zw|[Zw|[Zw|[Zw|[Zw|[Zw|[Zw|[Zw|Zw]]]]]]]]].
Lemma ok_low : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END ->
  ~ ((A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (A_ALLOCATOR + 120 <= a < A_ALLOCATOR + 129) \/
     (A_ALLOCATOR + 144 <= a < A_ALLOCATOR + 160) \/ (A_ALLOCATOR + 704 <= a < A_ALLOCATOR + 720)) -> oks a.
Proof.
intros a Ha NI. pose proof GEO_s as (G1 & G2 & G3 & ZQ & ZT & _ & _ & ZL & ZM & (SH1 & SH2 & SH3) & _).
split; [clear - Ha; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia|].
win_cases a Hw Zw.
all: first
  [ solve [clear - Zw NI; tauto]
  | solve [clear - Zw Ha G1; cnum; lia]
  | solve [clear - Zw Ha ZQ; cnum; lia]
  | solve [clear - Zw Ha ZT; cnum; lia]
  | solve [clear - Zw Ha ZL; cnum; lia]
  | solve [clear - Zw Ha SH1; cnum; lia]
  | solve [clear - Zw Ha ZM; cnum; lia] ].
Qed.
Lemma ok_imgsh : forall a, SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8 -> oks a.
Proof.
intros a Ha. pose proof GEO_s as (G1 & G2 & G3 & ZQ & ZT & _ & _ & ZL & ZM & (SH1 & SH2 & SH3) & _).
unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in Ha. change (65536 / 8) with 8192 in Ha. change (6275072 / 8) with 784384 in Ha.
split; [clear - Ha; lia|].
win_cases a Hw Zw.
all: first
  [ solve [clear - Zw Ha G1; cnum; lia]
  | solve [clear - Zw Ha; cnum; lia]
  | solve [clear - Zw Ha ZQ; cnum; lia]
  | solve [clear - Zw Ha ZT; cnum; lia]
  | solve [clear - Zw Ha ZL; cnum; lia]
  | solve [clear - Zw Ha SH3; cnum; lia]
  | solve [clear - Zw Ha ZM; cnum; lia] ].
Qed.
Lemma ok_T : forall a, T <= a < T + 80 -> oks a.
Proof.
intros a Ha. pose proof GEO_s as (G1 & G2 & G3 & ZQ & ZT & _ & _ & ZL & ZM & (SH1 & SH2 & SH3) & DTQ & _ & _ & _ & _ & _ & (sz & SZ & LT & _) & MT & _).
split; [clear - Ha ZT; cnum; lia|].
win_cases a Hw Zw.
all: first
  [ solve [clear - Zw Ha ZT G2 G3; cnum; lia]
  | solve [clear - Zw Ha ZT; cnum; lia]
  | solve [clear - Zw Ha DTQ; cnum; lia]
  | solve [clear - Zw Ha; cnum; lia]
  | solve [clear - Zw Ha SZ LT; cnum; lia]
  | solve [clear - Zw Ha ZT SH1 SH2; cnum; lia]
  | solve [clear - Zw Ha MT; cnum; lia] ].
Qed.
Lemma ok_C : forall a, ly_C ly <= a < ly_C ly + 256 -> oks a.
Proof.
intros a Ha. pose proof GEO_s as (G1 & G2 & G3 & ZQ & ZT & ZC & _ & ZL & ZM & (SH1 & SH2 & SH3) & _ & DCQ & _ & DTC & _ & _ & (sz & SZ & _ & LC & _) & _ & MC & _).
split; [clear - Ha ZC; cnum; lia|].
win_cases a Hw Zw.
all: first
  [ solve [clear - Zw Ha ZC G2 G3; cnum; lia]
  | solve [clear - Zw Ha ZC; cnum; lia]
  | solve [clear - Zw Ha DCQ; cnum; lia]
  | solve [clear - Zw Ha DTC; cnum; lia]
  | solve [clear - Zw Ha SZ LC; cnum; lia]
  | solve [clear - Zw Ha ZC SH1 SH2; cnum; lia]
  | solve [clear - Zw Ha MC; cnum; lia] ].
Qed.
Lemma ok_D : forall a, ly_D ly <= a < ly_D ly + 4096 -> oks a.
Proof.
intros a Ha. pose proof GEO_s as (G1 & G2 & G3 & ZQ & ZT & ZC & ZD & ZL & ZM & (SH1 & SH2 & SH3) & _ & _ & DDQ & _ & DTD & _ & (sz & SZ & _ & _ & LD) & _ & _ & MD).
split; [clear - Ha ZD; cnum; lia|].
win_cases a Hw Zw.
all: first
  [ solve [clear - Zw Ha ZD G2 G3; cnum; lia]
  | solve [clear - Zw Ha ZD; cnum; lia]
  | solve [clear - Zw Ha DDQ; cnum; lia]
  | solve [clear - Zw Ha DTD; cnum; lia]
  | solve [clear - Zw Ha SZ LD; cnum; lia]
  | solve [clear - Zw Ha ZD SH1 SH2; cnum; lia]
  | solve [clear - Zw Ha MD; cnum; lia] ].
Qed.
End s.

Lemma rc_sec_const : forall (B : asyms), TfibSyms B -> forall ly X k (W : world tfibsegs) regs mem r o sm i (mem' : word -> option byte),
  DMrcSecFc.sec_cut B ly X k W regs mem r o sm i ->
  ly_tsd ly = TFIB_TSD ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) ->
  (forall x : word, ~ DMrcSecMun.WPRE ly regs (bv_unsigned x) -> ~ DMrcSecGv.WIN3 ly regs (YFg8.MAP ly r) (YFg8.LEN sm) (YFg8.qi ly i) (YFg8.lst ly X r) (bv_unsigned x) -> mem' x = mem x) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 680) 4 0 ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly).
Proof.
intros B TB ly X k W regs mem r o sm i mem' SC HTSD OLDc KEEP MUT.
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem') in *.
assert (AGok : forall a, oks ly X regs r sm i a -> rd' a = rd a).
{ intros a (Ua & N1 & N2). subst rd rd'. apply aview_same. apply KEEP; rewrite unsigned_lit_small by exact Ua; assumption. }
assert (MUT' : forall j, 0 <= j < 4 -> rd' (A_ALLOCATOR + 680 + j) = Some 0).
{ intros j Hj. subst rd'. replace j with (Z.of_nat (Z.to_nat j)) by lia.
  rewrite (YFg7.val_mem_aview _ _ _ _ _ (Z.to_nat j) MUT) by lia. rewrite le_byte_0. reflexivity. }
rewrite (ts_const _ TB) in OLDc |- *.
apply Forall_forall. intros ce Hce. pose proof (proj1 (Forall_forall _ _) OLDc ce Hce) as Hold.
pose proof (proj1 (forallb_forall _ _) (Tfib_const_locs ly) ce Hce) as K. pose proof (proj1 (forallb_forall _ _) (Tfib_const_pads ly) ce Hce) as P.
cbn beta in K, P. clear Hce OLDc.
destruct ce as [ca cw cv]. cbv beta zeta delta [const_loc_oks c_at c_w c_val] in K, P.
set (w := Z.max 1 (Z.of_nat cw)) in K, P.
assert (XFER : (forall j, 0 <= j < w -> oks ly X regs r sm i (aeval B ly ca + j)) -> cell_holds B ly rd' (ACell ca cw cv)).
{ intros Hok. apply (cell_holds_agree B ly rd rd' _ Hold). cbn [c_at c_w]. intros j Hj. apply AGok. apply Hok. subst w. exact Hj. }
assert (LOW : forall a, low_oks a w = true -> forall j, 0 <= j < w -> oks ly X regs r sm i (a + j)).
{ intros a La j Hj. unfold low_oks in La. subst w. apply Bool.orb_true_iff in La as [La|La].
  - apply (ok_low B ly X k W regs mem r o sm i SC); clear - La Hj; unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, A_ALLOCATOR in *; lia.
  - apply (ok_imgsh B ly X k W regs mem r o sm i SC). clear - La Hj. unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *.
    change (65536 / 8) with 8192 in La. change (6275072 / 8) with 784384 in La. cbn -[Z.add Z.leb Z.mul] in La. lia. }
destruct ca; try discriminate K; cbn [aeval] in XFER |- *.
- destruct (((z =? TFIB_INST + 681) && (w =? 1)) || ((z =? TFIB_INST + 682) && (w =? 2))) eqn:C5.
  + cbn [negb Nat.eqb orb] in P. destruct cv as [e|mk mv]; [|discriminate P]. destruct e; try discriminate P. destruct z0; try discriminate P.
    unfold cell_holds. cbn [c_at c_w c_val aeval]. intros kk Hkk. rewrite le_byte_0.
    replace (z + Z.of_nat kk) with (A_ALLOCATOR + 680 + (z - TFIB_INST - 680 + Z.of_nat kk)) by (unfold A_ALLOCATOR, TFIB_INST; lia).
    apply MUT'. subst w. clear - C5 Hkk. lia.
  + destruct (low_oks z w) eqn:C1; [apply XFER; exact (LOW z C1) | discriminate K].
- destruct ((0 <=? off) && (off + w <=? 80)) eqn:C2; [|discriminate K].
  apply XFER. intros j Hj. subst w. apply (ok_T B ly X k W regs mem r o sm i SC). clear - C2 Hj. lia.
- destruct ((0 <=? off) && (off + w <=? 256)) eqn:C2; [|discriminate K].
  apply XFER. intros j Hj. subst w. apply (ok_C B ly X k W regs mem r o sm i SC). clear - C2 Hj. lia.
- destruct (low_oks (TFIB_TSD + off) w) eqn:C1; [|discriminate K]. apply XFER. rewrite HTSD. exact (LOW _ C1).
- destruct (low_oks (TFIB_INST + off) w) eqn:C1; [|discriminate K]. apply XFER. rewrite (ts_inst _ TB). exact (LOW _ C1).
- destruct (low_oks (TFIB_TP + off) w) eqn:C1; [|discriminate K]. apply XFER. rewrite (ts_tp _ TB). exact (LOW _ C1).
- destruct ((0 <=? off) && (off + w <=? 4096)) eqn:C2; [|discriminate K].
  apply XFER. intros j Hj. subst w. apply (ok_D B ly X k W regs mem r o sm i SC). clear - C2 Hj. lia.
Qed.
End d.
