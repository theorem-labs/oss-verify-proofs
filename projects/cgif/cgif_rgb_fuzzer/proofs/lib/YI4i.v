(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI07
YI1e YI1i YI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
YI3h YI4v YI4r YI4s YI4w YI4u YI4h YP12.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Ltac2 sat_vars () := [@API; @L; @A; @regs0; @mem0; @md0; @r; @cfp; @g; @wfn; @ctx; @path; @attr; @gen; @loops; @W; @H; @bef; @beffmt; @cur; @s; @N; @img; @fmt; @fattr; @fgen; @delay; @rest; @Lq; @Aq; @mdq; @memD; @flt; @fimg; @t; @ha; @pnew; @cq].
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac inK := repeat (first [left; apply bv_eq; reflexivity | right]).
Ltac in_sub Hrr := cbn [In] in Hrr; repeat (destruct Hrr as [<- | Hrr]; [inK|]); destruct Hrr.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section e.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree) (ha pnew cq : Z).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis HtreeD : tree_at src2segs memD t. Hypothesis Hfull : tree_full t. Hypothesis Hwft : tree_forall tnode_wf t.
Hypothesis Hnodes : forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Hypothesis Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n.
Hypothesis Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * M <= tn_addr n.
Hypothesis Hha : ha = 0 \/ (ha = 1 /\ fmt = 4).
Hypothesis Hsl96 : slot regs0 memD SL_96 bef. Hypothesis Hsl112 : bef <> 0 -> slot regs0 memD SL_112 beffmt.
Hypothesis Hbefb : bef <> 0 -> (beffmt = 3 \/ beffmt = 4) /\ In (bef, beffmt * N) (blocks Lq Aq) /\ (bef + beffmt * N <= flt \/ flt + 4 * M <= bef).
Hypothesis Rbef : 0 <= bef < 2 ^ 64.
Local Notation memIv := (memIN N memD fimg).
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5136 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 158.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte src2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma tree_now : forall m, memIv m -> tree_at src2segs m t.
Proof.
intros m HMI. pose proof di_consts as (HRv & HFv & _ & HNSv & Hac & _). eapply tree_at_frame; [exact HtreeD|].
intros n a Hn Ha. destruct (Hnodes n Hn) as (X1 & X2 & X3). pose proof (Hsep_tf n Hn). apply HMI; lia.
Qed.
Lemma slot_now' : forall m off v, memIv m -> 0 <= off -> off + 8 <= RGBA_FRAME -> slot regs0 memD off v -> slot regs0 m off v.
Proof.
intros m off v HMI Ho1 Ho2 Hs k Hk. pose proof di_consts as (HRv & HFv & _ & _ & Hac & _).
unfold slot, word_mem in Hs. rewrite HMI; [apply Hs; exact Hk | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia].
Qed.
Definition NC_REGS : list reg := [2; 3; 4; 10; 26; 27; 25; 12; 17; 24; 20; 8]%bv.
Definition nregs_c (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 spv /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 10 = Z_to_bv 64 flt /\ getr regs 26 = Z_to_bv 64 fmt /\ getr regs 27 = Z_to_bv 64 (troot t) /\ getr regs 25 = Z_to_bv 64 fimg /\
getr regs 12 = Z_to_bv 64 N /\ getr regs 17 = Z_to_bv 64 (nha ha) /\ getr regs 24 = Z_to_bv 64 pnew /\ getr regs 20 = Z_to_bv 64 cq /\ getr regs 8 = Z_to_bv 64 r.
Definition nregs (regs : bvmap 5 word) (i : Z) : Prop := nregs_c regs /\ getr regs 11 = Z_to_bv 64 i.
Lemma nregs_c_kept : forall regs regs', (forall rr : reg, In rr NC_REGS -> getr regs' rr = getr regs rr) -> nregs_c regs -> nregs_c regs'.
Proof.
intros regs regs' HK (G2 & G3 & G4 & G10 & G26 & G27 & G25 & G12 & G17 & G24 & G20 & G8).
unfold nregs_c. rewrite (HK 2%bv), (HK 3%bv), (HK 4%bv), (HK 10%bv), (HK 26%bv), (HK 27%bv), (HK 25%bv), (HK 12%bv), (HK 17%bv), (HK 24%bv), (HK 20%bv), (HK 8%bv) by inK.
repeat (split; [assumption|]). assumption.
Qed.
Ltac nc_sub := intros rr Hrr; unfold NC_REGS in Hrr; in_sub Hrr.
Lemma NC_sub_NM : forall rr : reg, In rr NC_REGS -> In rr NM_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NA : forall rr : reg, In rr NC_REGS -> In rr NA_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NB0 : forall rr : reg, In rr NC_REGS -> In rr NB0_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NBm : forall rr : reg, In rr NC_REGS -> In rr NBm_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NB2 : forall rr : reg, In rr NC_REGS -> In rr NB2_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_ND0 : forall rr : reg, In rr NC_REGS -> In rr ND0_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NDL : forall rr : reg, In rr NC_REGS -> In rr NDL_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NLF : forall rr : reg, In rr NC_REGS -> In rr NLF_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NST : forall rr : reg, In rr NC_REGS -> In rr NST_KEEP. Proof. nc_sub. Qed.
Definition npost (i pc : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\ memIv mem' /\ nregs regs' i.
Lemma NSTORE_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem ->
nregs regs i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_ST) mem (seg_rom src2segs)) mdq) (npost (i + 1) (if i + 1 <? N then PN_LH else PC_QE)).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI (HNC & G11).
pose proof HNC as (G2 & G3 & G4 & G10 & G26 & G27 & G25 & G12 & G17 & G24 & G20 & G8).
eapply SR_mono.
{ ltac2:(satvl NST_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem i Hi HJ G25 G11 G12). }
cbv beta. intros c2 (regs2 & mem2 & -> & HJ2 & Hm2 & R11 & Hk2).
exists fy, regs2, mem2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfrm|].
split; [eapply memIN_trans; [exact HMI|]; intros a Ha H1; apply Hm2; [exact Ha | lia]|].
split; [exact (nregs_c_kept regs regs2 (fun rr Hrr => Hk2 rr (NC_sub_NST rr Hrr)) HNC) | exact R11].
Qed.
Lemma NDESC_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem ->
nregs regs i -> getr regs 13 = Z_to_bv 64 (fmt * i) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_D0) mem (seg_rom src2segs)) mdq) (npost (i + 1) (if i + 1 <? N then PN_LH else PC_QE)).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI (HNC & G11) G13.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HNC as (G2 & G3 & G4 & G10 & G26 & G27 & G25 & G12 & G17 & G24 & G20 & G8).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
pose proof (tree_now mem HMI) as Htree.
destruct (root_cases mem t Htree Hfull) as (n & lf & c0 & c1 & Hroot & Hnin & Hlf & Hlen & Hobj & HifL & HifN).
destruct (Hnodes n Hnin) as (Hn0 & Hn1 & Hn16).
eapply SR_bind.
{ ltac2:(satvl ND0_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem i n c0 c1 lf Hi Hlf HJ ltac:(rewrite G27, Hroot; reflexivity) G13 G10 Hobj Hlen Hn0 Hn1 Hn16). }
cbv beta. intros c3 (regs3 & -> & S14 & S13 & Hk3).
pose proof (nregs_c_kept regs regs3 (fun rr Hrr => Hk3 rr (NC_sub_ND0 rr Hrr)) HNC) as HNC3.
assert (T11 : getr regs3 11 = Z_to_bv 64 i) by (rewrite (Hk3 11%bv) by inK; exact G11).
assert (LEAFST : forall (fy4 : FPState) regs4 m d0 d1, frm_zero (@fp_csr fy4) -> In m (tree_leaves t) ->
obj_at src2segs mem (tn_addr m) LAY_Node (node_vals d0 d1 m 1) -> nregs_c regs4 -> getr regs4 11 = Z_to_bv 64 i -> getr regs4 14 = Z_to_bv 64 (tn_addr m) ->
SR src2segs (mkCfg (@mkst fy4 regs4 (Z_to_bv 64 PN_LF) mem (seg_rom src2segs)) mdq) (npost (i + 1) (if i + 1 <? N then PN_LH else PC_QE))).
{ intros fy4 regs4 m d0 d1 Hfrm4 Hlm Hobjm HNC4 R11 R14.
destruct (leaf_facts mem t m Htree Hlm) as (Hmn & Hmlen & _). destruct (Hnodes m Hmn) as (Hm0 & Hm1 & Hm16).
eapply SR_bind; [ltac2:(satvl NLEAF_run using (sat_vars ()) as LEM); exact (LEM fy4 regs4 mem m d0 d1 Hh Hlz R14 Hobjm Hmlen Hm0 Hm1 Hm16)|].
cbv beta. intros c5 (regs5 & -> & Hk5).
apply (NSTORE_run fy4 regs5 mem i Hi HJ Hfrm4 HMI).
split; [exact (nregs_c_kept regs4 regs5 (fun rr Hrr => Hk5 rr (NC_sub_NLF rr Hrr)) HNC4) | rewrite (Hk5 11%bv) by inK; exact R11]. }
destruct Hlf as [-> | ->].
-
change (if 0 =? 0 then PN_DL else PN_LF) with PN_DL.
destruct (HifN eq_refl) as (tl & tr & Ht).
assert (HpM : 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia). assert (Hfi : 0 <= fmt * i) by nia.
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
eapply SR_bind.
{ ltac2:(satvl NDG_run using (sat_vars ()) as LEM); apply (LEM t n tl tr fy regs3 mem (flt + 4 * (fmt * i)) Ht Hh Hlz Hfrm S14 (S13 eq_refl) Htree Hfull).
- intros m Hm. split; [unfold tree_forall in Hwft; exact (proj1 (Forall_forall _ _) Hwft m Hm)|].
destruct (Hnodes m Hm) as (X1 & X2 & X3). pose proof (Hsep_tl m Hm). repeat split; lia.
- lia. - lia.
- replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia. rewrite Z.mod_add by lia. exact Hf4.
- intros j Hj. rewrite <- Z.add_assoc. apply (flt_present mem HJ). lia. }
cbv beta. intros c4 (fy4 & regs4 & m & -> & Hfrm4 & Hlm & S13m & Hk4).
destruct (leaf_facts mem t m Htree Hlm) as (_ & _ & d0 & d1 & Hobjm).
apply (LEAFST fy4 regs4 m d0 d1 Hfrm4 Hlm Hobjm (nregs_c_kept regs3 regs4 (fun rr Hrr => Hk4 rr (NC_sub_NDL rr Hrr)) HNC3) ltac:(rewrite (Hk4 11%bv) by inK; exact T11) S13m).
-
change (if 1 =? 0 then PN_DL else PN_LF) with PN_LF.
pose proof (HifL eq_refl) as Ht.
assert (Hlm : In n (tree_leaves t)) by (rewrite Ht; left; reflexivity).
apply (LEAFST fy regs3 n c0 c1 Hfrm Hlm Hobj HNC3 T11 S14).
Qed.
Lemma NPIX_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> nregs regs i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom src2segs)) mdq) (npost (i + 1) (if i + 1 <? N then PN_LH else PC_QE)).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI HN. pose proof HN as (HNC & G11).
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HNC as (G2 & G3 & G4 & G10 & G26 & G27 & G25 & G12 & G17 & G24 & G20 & G8).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
eapply SR_bind; [ltac2:(satvl NM_run using (sat_vars ()) as LEM); exact (LEM fy regs mem i Hi Hh Hlz G26 G11)|].
cbv beta. intros c1 (regs1 & -> & Q13 & Hk1).
pose proof (nregs_c_kept regs regs1 (fun rr Hrr => Hk1 rr (NC_sub_NM rr Hrr)) HNC) as HNC1.
assert (T11 : getr regs1 11 = Z_to_bv 64 i) by (rewrite (Hk1 11%bv) by inK; exact G11).
pose proof HNC1 as (P2 & _ & _ & P10 & _ & _ & _ & _ & P17 & _).
assert (CONT : forall K (c' : config) (fy1 : FPState), (forall rr : reg, In rr NC_REGS -> In rr K) -> In (11%bv : reg) K ->
ntest_post fmt mdq fy1 regs1 mem i K c' -> SR src2segs c' (npost (i + 1) (if i + 1 <? N then PN_LH else PC_QE))).
{ intros K c' fy1 HKs HK11 (fy2 & regs2 & ti & -> & Hfrm2 & Q13' & Hk2).
pose proof (nregs_c_kept regs1 regs2 (fun rr Hrr => Hk2 rr (HKs rr Hrr)) HNC1) as HNC2.
assert (T11' : getr regs2 11 = Z_to_bv 64 i) by (rewrite (Hk2 11%bv HK11); exact T11).
destruct ti.
- exact (NSTORE_run fy2 regs2 mem i Hi HJ Hfrm2 HMI (conj HNC2 T11')).
- exact (NDESC_run fy2 regs2 mem i Hi HJ Hfrm2 HMI (conj HNC2 T11') (Q13' eq_refl)). }
pose proof (slot_now' mem SL_96 bef HMI ltac:(unfold SL_96; lia) ltac:(unfold SL_96, RGBA_FRAME; lia) Hsl96) as S96.
destruct Hha as [Hha0 | [Hha1 F4]].
-
assert (P17' : getr regs1 17 = Z_to_bv 64 1) by (rewrite P17, Hha0; reflexivity).
destruct (Z.eq_dec bef 0) as [Hb0 | Hb].
+ eapply SR_bind; [ltac2:(satvl NB0_run using (sat_vars ()) as LEM); exact (LEM fy regs1 mem Hh Hlz ltac:(rewrite <- Hb0; exact S96) P2 P17')|].
cbv beta. intros c2 (regs2 & -> & Hk2).
apply (NDESC_run fy regs2 mem i Hi HJ Hfrm HMI).
* split; [exact (nregs_c_kept regs1 regs2 (fun rr Hrr => Hk2 rr (NC_sub_NB0 rr Hrr)) HNC1) | rewrite (Hk2 11%bv) by inK; exact T11].
* rewrite (Hk2 13%bv) by inK. exact Q13.
+ pose proof (slot_now' mem SL_112 beffmt HMI ltac:(unfold SL_112; lia) ltac:(unfold SL_112, RGBA_FRAME; lia) (Hsl112 Hb)) as S112.
eapply SR_bind.
{ ltac2:(satvl NBm_run using (sat_vars ()) as LEM).
exact (LEM fy regs1 mem i Hi Hb HJ S96 S112 P2 P17' Q13 T11). }
cbv beta. intros c2 (regs2 & -> & Q14 & Q15 & Hk2).
pose proof (nregs_c_kept regs1 regs2 (fun rr Hrr => Hk2 rr (NC_sub_NBm rr Hrr)) HNC1) as HNC2.
pose proof HNC2 as (R2 & _ & _ & R10 & _).
eapply SR_bind.
{ ltac2:(satvl NB2_run using (sat_vars ()) as LEM).
exact (LEM fy regs2 mem i Hi Hb HJ Hfrm ltac:(rewrite (Hk2 13%bv) by inK; exact Q13) Q14 Q15 R10 R2 S96). }
cbv beta. intros c3 HT.
destruct HT as (fy3 & regs3 & ti & -> & Hfrm3 & Q13' & Hk3).
apply (CONT NB2_KEEP _ fy NC_sub_NB2 ltac:(inK)).
exists fy3, regs3, ti. split; [reflexivity|]. split; [exact Hfrm3|]. split; [exact Q13'|].
intros rr Hrr. rewrite (Hk3 rr Hrr). apply Hk2. revert Hrr. clear. intros Hrr. unfold NB2_KEEP in Hrr. in_sub Hrr.
-
assert (P17' : getr regs1 17 = Z_to_bv 64 0) by (rewrite P17, Hha1; reflexivity).
eapply SR_bind.
{ ltac2:(satvl NA_run using (sat_vars ()) as LEM).
exact (LEM fy regs1 mem i Hi F4 HJ Hfrm P17' Q13 P10). }
cbv beta. intros c2 HT. exact (CONT NA_KEEP _ fy NC_sub_NA ltac:(inK) HT).
Qed.
Lemma NLOOP_run : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> Z.of_nat k = N - 1 - i ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> nregs regs i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom src2segs)) mdq) (npost N PC_QE).
Proof.
induction k as [|k IH]; intros fy regs mem i Hi Hk HJ Hfrm HMI HD.
- assert (Hlast : i + 1 = N) by lia.
eapply SR_mono; [exact (NPIX_run fy regs mem i Hi HJ Hfrm HMI HD)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & HMI' & HD').
replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Hlast in HD'.
exists fy', regs', mem'. repeat (split; [first [reflexivity | assumption]|]). exact HD'.
- eapply SR_bind; [exact (NPIX_run fy regs mem i Hi HJ Hfrm HMI HD)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & HMI' & HD').
replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
exact (IH fy' regs' mem' (i + 1) ltac:(lia) ltac:(lia) HJ' Hfrm' HMI' HD').
Qed.
End e.
Section f.
Context {fxi : YK11.FPState}.
Definition ss_NPREx : sstate :=
mkSS PC_ND sr_atoms [] None (mkFacts [ (22%nat, mkAF 1 RGB_NMAX 0) ] [] []).
Definition ss_NPRE : sstate := mkSST PC_ND (ss_regs ss_NPREx) (sfr_atoms 64) (ss_mem ss_NPREx) None (ss_facts ss_NPREx).
Lemma ND_at : forall regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
K_QE (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_ND (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_ND) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hnd & HQR & Hsl & Hsq & Hfc & Hobj & Hcg & Himg & Hchq & Htok & Hpnew & Hfimg & Hfnz & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
destruct HQR as (G10 & G11 & G17 & G1 & G27 & G24 & G26 & G22 & G25 & G20 & G8).
pose proof Htok as (Htree & Hfull & Hth & Hwft & Hnodes).
pose proof Hsl as (SN & Scfp & Snew & Sfimg & Sfa1). pose proof Hsq as ((S88 & S96 & S112) & S72 & S80 & S104).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
set (keep := BASEv ++ cht_blks C ++ tree_blocks t).
assert (HBk : Permutation (blocks Lc Ac) (keep ++ [(pnew, fmt * N); (fimg, N); (flt, 4 * (fmt * N))])).
{ eapply Permutation_trans; [exact HB|]. subst keep. perm_tac. }
assert (Hsub : forall x0, In x0 BASEv -> In x0 keep) by (intros x0 Hx0; subst keep; apply in_app_iff; left; exact Hx0).
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ flt (4 * (fmt * N)) HHc HBk HBent Hsub ltac:(right; right; left; reflexivity) ltac:(lia)) as [Hfin Hfnot].
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ fimg N HHc HBk HBent Hsub ltac:(right; left; reflexivity) ltac:(lia)) as [Hgin Hgnot].
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ pnew (fmt * N) HHc HBk HBent Hsub ltac:(left; reflexivity) ltac:(lia)) as [Hpin _].
destruct (heap_blocks_range _ _ LAWS _ _ _ _ flt (4 * (fmt * N)) HHc Hfin ltac:(lia)) as (Hflt0 & Hflt1 & Hflt16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc Hgin ltac:(lia)) as (Hfimg0 & Hfimg1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ pnew (fmt * N) HHc Hpin ltac:(lia)) as (Hpnew0 & Hpnew1 & _).
assert (HBf : Permutation (blocks Lc Ac) ((flt, 4 * (fmt * N)) :: (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t))).
{ eapply Permutation_trans; [exact HB|]. perm_tac. }
assert (HBg : Permutation (blocks Lc Ac) ((fimg, N) :: (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]))).
{ eapply Permutation_trans; [exact HB|]. perm_tac. }
assert (Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lc Ac) (fimg + i)).
{ intros i Hi. right. right. exists fimg, N. split; [exact Hgin|]. split; [exact Hgnot | lia]. }
assert (Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n).
{ intros n Hn. pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (tn_addr n, NODE_SIZE) HHc HBg
ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; apply tree_blocks_in_nodes; exists n; auto)) as X. cbn [fst snd] in X. lia. }
assert (Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * (fmt * N) <= tn_addr n).
{ intros n Hn. pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (tn_addr n, NODE_SIZE) HHc HBf
ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply tree_blocks_in_nodes; exists n; auto)) as X. cbn [fst snd] in X. lia. }
assert (Hbefb : bef <> 0 -> (beffmt = 3 \/ beffmt = 4) /\ In (bef, beffmt * N) (blocks Lc Ac) /\ (bef + beffmt * N <= flt \/ flt + 4 * (fmt * N) <= bef)).
{ intros Hb. assert (Hbf : beffmt = 3 \/ beffmt = 4) by (destruct Hbef as [Hbef|Hbef]; [lia | exact Hbef]).
assert (Hbin : In (bef, beffmt * N) BASEv).
{ right. apply in_app_iff. right. apply in_app_iff. left. unfold optb. replace (bef =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb). left. reflexivity. }
split; [exact Hbf|]. split; [eapply blocks_perm_in; [exact HBf|]; right; apply in_app_iff; left; exact Hbin|].
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (bef, beffmt * N) HHc HBf ltac:(apply in_app_iff; left; exact Hbin)) as X. cbn [fst snd] in X. lia. }
assert (Rbef : 0 <= bef < 2 ^ 64).
{ destruct (Z.eq_dec bef 0) as [-> | Hb]; [lia|]. destruct (Hbefb Hb) as (Hbf & Hbin & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bef (beffmt * N) HHc Hbin ltac:(lia)) as (X1 & X2 & _). lia. }
set (E0 := Ereg regs1 []).
set (E := ew_fregs E0 64 (@fp_regs fxi)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs1 rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs1 rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (U22 : bv_unsigned (ew E0 22) = N) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok src2segs fxi E0 ss_NPREx (@mkst fxi regs1 (Z_to_bv 64 PC_ND) memc (seg_rom src2segs))).
{ unfold ss_NPREx. subst E0. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pose proof (st_ok_enterF src2segs fxi 64 E0 ss_NPREx _ HS0 ltac:(vm_compute; reflexivity) HFRM) as HS.
change (ew_fregs E0 64 (@fp_regs fxi)) with E in HS.
change (mkSST (ss_pc ss_NPREx) (ss_regs ss_NPREx) (sfr_atoms 64) (ss_mem ss_NPREx) (ss_resv ss_NPREx) (ss_facts ss_NPREx)) with ss_NPRE in HS.
clear HS0. rewrite <- !HEE in U22 by lia.
change memc with (ms_mem (@mkst fxi regs1 (Z_to_bv 64 PC_ND) memc (seg_rom src2segs))) in HJ.
jrunF_to LAWS src2tbl_ok HS HJ PN_LH. { wr_ok_eval. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
assert (Hmm : ms_mem ms = memc).
{ apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
rewrite Hmm in HJ. rewrite (st_okF_mkst src2segs E _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm.
assert (RG : forall rr : reg, getr (ms_regs ms) rr = sv_denot E (sr_get (ss_regs (fst (sym_run_toFN src2segs src2tbl FUEL PN_LH ss_NPRE))) rr)) by (intros rr; exact (st_okF_reg src2segs E _ _ rr HS)).
match type of RG with context [ss_regs (fst ?x)] => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in RG end.
pose proof (st_okF_regs_kept src2segs E _ _ regs1 [2; 3; 4; 10; 26; 27; 25; 17; 24; 20; 8]%bv HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as Hk0.
assert (HD0 : nregs flt fimg t ha pnew (ch_c C) (ms_regs ms) 0).
{ split.
- unfold nregs_c. rewrite (Hk0 2%bv), (Hk0 3%bv), (Hk0 4%bv), (Hk0 10%bv), (Hk0 26%bv), (Hk0 27%bv), (Hk0 25%bv), (Hk0 17%bv), (Hk0 24%bv), (Hk0 20%bv), (Hk0 8%bv) by inK.
repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); assumption].
rewrite (RG 12%bv); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, (HE 22%nat 22%bv eq_refl), Z_to_bv_bv_unsigned; exact G22.
- rewrite (RG 11%bv); eval_sr_get; cbn [sv_denot]; reflexivity. }
pose proof (st_okF_frm src2segs E _ _ HS) as Hfrm1. clear HS HF RG.
eapply SR_bind.
{ assert (S112' : bef <> 0 -> slot regs0 memc SL_112 beffmt).
{ intros Hb. destruct (Hbefb Hb) as (Hbf & _). rewrite <- (sx32v_small beffmt) by lia. exact S112. }
pose (Lq := Lc). pose (Aq := Ac). pose (mdq := mdc). pose (memD := memc). pose (cq := ch_c C).
ltac2:(satvl NLOOP_run using (sat_vars ()) as LEM).
exact (LEM (Z.to_nat (N - 1)) (fp_of ms) (ms_regs ms) memc 0 ltac:(lia) ltac:(lia) HJ Hfrm1 ltac:(intros a0 _ _; reflexivity) HD0). }
cbv beta. intros cE (fyE & regsE & memE & -> & HJE & HfrmE & HMIE & HDE). clear HJ.
destruct HDE as ((F2 & F3 & F4 & F10 & F26 & F27 & F25 & F12 & F17 & F24 & F20 & F8) & F11).
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte src2segs memE x = mbyte src2segs memc x).
{ intros x Hx Hs Hna. apply HMIE; lia. }
assert (KB : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte src2segs memE (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi.
assert (Hbf : In (b, m) (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t)).
{ apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; exact Hbm]. }
assert (Hbg : In (b, m) (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))])).
{ apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; rewrite app_assoc; apply in_app_iff; left; exact Hbm]. }
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (b, m) HHc HBg Hbg) as X2. cbn [fst snd] in X2.
destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc ltac:(eapply blocks_perm_in; [exact HBf | right; exact Hbf]) ltac:(lia)) as (Y1 & Y2 & _).
apply HMIE; lia. }
destruct (qfacts_kept regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest memc memE ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH KB)
as (TR & TS & TQ & TF & TO & TC & TI & TH & TT).
apply (KQE fyE regsE Lc Ac memE mdc ha pnew fimg imgl C cnt pal t flt HfrmE).
split.
{ split; [exact HJE|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split; [exact (TR HRA)|]. split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply KH; unfold sp, sp0, RGBA_FRAME, OFF_apal in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [exact F2 | split; [exact F3 | exact F4]]|].
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|].
split; [exact F10|]. split; [exact F27|]. split; [exact F20|]. split; [exact F8|]. split; [exact F24|].
split; [exact (TS Hsl)|]. split; [exact (TQ Hsq)|]. split; [exact (TF Hfc)|]. split; [exact (TO Hobj)|]. split; [exact (TC Hcg)|].
split; [exact (TI Himg)|]. split; [exact (TH Hchq)|]. split; [exact (TT Htok)|].
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfnz|]. exact HB.
Qed.
End f.
Lemma src2_rgbadd_ND : seg_ND (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KQE fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt HFRM HAT. exact (ND_at regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT). Qed.
End d.
End c.
