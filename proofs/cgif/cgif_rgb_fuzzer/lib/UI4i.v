(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
UI3h UI4v UIZm UI4w UI4u UI4h YP12 UIZ8.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Ltac2 sat_vars () := [@API; @L; @A; @regs0; @mem0; @md0; @r; @cfp; @g; @wfn; @ctx; @path; @attr; @gen; @loops; @W; @H; @bef; @beffmt; @cur; @s; @N; @img; @fmt; @fattr; @fgen; @delay; @rest; @Lq; @Aq; @mdq; @memD; @flt; @fimg; @t; @ha; @cq; @bfw].
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac inK := repeat (first [left; apply bv_eq; reflexivity | right]).
Ltac in_sub Hrr := cbn [In] in Hrr; repeat (destruct Hrr as [<- | Hrr]; [inK|]); destruct Hrr.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis GLNI : forall fx', glni_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section e.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree) (ha cq bfw : Z).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis HtreeD : tree_at ubs2segs memD t. Hypothesis Hfull : tree_full t. Hypothesis Hwft : tree_forall tnode_wf t.
Hypothesis Hnodes : forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Hypothesis Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n.
Hypothesis Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * M <= tn_addr n.
Hypothesis Hha : ha = 0 \/ (ha = 1 /\ fmt = 4).
Hypothesis Hsl48 : slot regs0 memD 48 fimg. Hypothesis Hsl80 : slot regs0 memD 80 (troot t). Hypothesis Hsl88 : slot regs0 memD 88 bef.
Hypothesis Hsl104 : slot regs0 memD 104 bfw. Hypothesis Hsl120 : slot regs0 memD 120 fmt.
Hypothesis Hbefb : bef <> 0 -> (beffmt = 3 \/ beffmt = 4) /\ In (bef, beffmt * N) (blocks Lq Aq) /\ (bef + beffmt * N <= flt \/ flt + 4 * M <= bef).
Hypothesis Rbef : 0 <= bef < 2 ^ 64. Hypothesis Rbfw : 0 <= bfw < 2 ^ 64. Hypothesis Hbfw : bef <> 0 -> bfw = beffmt.
Local Notation memIv := (memIN N memD fimg).
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5168 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 166.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte ubs2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma tree_now : forall m, memIv m -> tree_at ubs2segs m t.
Proof.
intros m HMI. pose proof di_consts as (HRv & HFv & _ & HNSv & Hac & _). eapply tree_at_frame; [exact HtreeD|].
intros n a Hn Ha. destruct (Hnodes n Hn) as (X1 & X2 & X3). pose proof (Hsep_tf n Hn). apply HMI; lia.
Qed.
Lemma slot_now' : forall m off v, memIv m -> 0 <= off -> off + 8 <= RGBA_FRAME -> slot regs0 memD off v -> slot regs0 m off v.
Proof.
intros m off v HMI Ho1 Ho2 Hs k Hk. pose proof di_consts as (HRv & HFv & _ & _ & Hac & _).
unfold slot, word_mem in Hs. rewrite HMI; [apply Hs; exact Hk | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia].
Qed.
Definition NC_REGS : list reg := [2; 3; 4; 8; 18; 20; 21; 22; 23; 24; 27]%bv.
Definition nregs_c (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 spv /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\ getr regs 8 = Z_to_bv 64 r /\
getr regs 18 = Z_to_bv 64 (nha ha) /\ getr regs 20 = Z_to_bv 64 cq /\ getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - flt) /\
getr regs 22 = Z_to_bv 64 (2 ^ 64 - 1 - bef) /\ getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) /\ getr regs 24 = Z_to_bv 64 flt /\
getr regs 27 = Z_to_bv 64 N.
Definition nregs (regs : bvmap 5 word) (i : Z) : Prop :=
nregs_c regs /\ getr regs 19 = Z_to_bv 64 i /\ getr regs 9 = Z_to_bv 64 (fmt * i) /\ getr regs 25 = Z_to_bv 64 (bfw * i + 2) /\
getr regs 7 = Z_to_bv 64 fmt.
Lemma nregs_c_kept : forall regs regs', (forall rr : reg, In rr NC_REGS -> getr regs' rr = getr regs rr) -> nregs_c regs -> nregs_c regs'.
Proof.
intros regs regs' HK (G2 & G3 & G4 & G8 & G18 & G20 & G21 & G22 & G23 & G24 & G27).
unfold nregs_c. rewrite (HK 2%bv), (HK 3%bv), (HK 4%bv), (HK 8%bv), (HK 18%bv), (HK 20%bv), (HK 21%bv), (HK 22%bv), (HK 23%bv), (HK 24%bv), (HK 27%bv) by inK.
repeat (split; [assumption|]). assumption.
Qed.
Ltac nc_sub := intros rr Hrr; unfold NC_REGS in Hrr; in_sub Hrr.
Lemma NC_sub_NT : forall rr : reg, In rr NC_REGS -> In rr NT_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NST : forall rr : reg, In rr NC_REGS -> In rr NST_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_NCL : forall rr : reg, In rr NC_REGS -> In rr NCL_KEEP. Proof. nc_sub. Qed.
Lemma NC_sub_CS : forall rr : reg, In rr NC_REGS -> In rr CALLEE_SAVED. Proof. nc_sub. Qed.
Definition npost (i pc : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\ memIv mem' /\ nregs regs' i.
Lemma NSTP_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z) (b : bool),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem ->
nregs_c regs -> getr regs 19 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 (fmt * i) -> getr regs 25 = Z_to_bv 64 (bfw * i + 2) ->
(b = false -> getr regs 7 = Z_to_bv 64 fmt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 (if b then PN_RT else PN_TR)) mem (seg_rom ubs2segs)) mdq)
(npost (i + 1) (if i + 1 <? N then PN_LH else PN_QE)).
Proof.
intros fy regs mem i b Hi HJ Hfrm HMI HNC G19 G9 G25 G7.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HNC as (G2 & G3 & G4 & G8 & G18 & G20 & G21 & G22 & G23 & G24 & G27).
pose proof (slot_now' mem 48 fimg HMI ltac:(lia) ltac:(unfold RGBA_FRAME; lia) Hsl48) as S48.
pose proof (slot_now' mem 104 bfw HMI ltac:(lia) ltac:(unfold RGBA_FRAME; lia) Hsl104) as S104.
pose proof (slot_now' mem 120 fmt HMI ltac:(lia) ltac:(unfold RGBA_FRAME; lia) Hsl120) as S120.
eapply SR_mono.
{ ltac2:(satvl NST_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem i bfw b Hi Rbfw HJ S48 S104 S120 G2 G19 G27 G23 G9 G25 G7). }
cbv beta. intros c2 (regs2 & mem2 & -> & HJ2 & Hm2 & R19 & R9 & R25 & R7 & Hk2).
exists fy, regs2, mem2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfrm|].
split; [intros a Ha H1; rewrite (Hm2 a Ha ltac:(lia)); apply HMI; assumption|].
split; [exact (nregs_c_kept regs regs2 (fun rr Hrr => Hk2 rr (NC_sub_NST rr Hrr)) HNC)|].
exact (conj R19 (conj R9 (conj R25 R7))).
Qed.
Lemma NCALL_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> nregs regs i ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_CL) mem (seg_rom ubs2segs)) mdq) (npost (i + 1) (if i + 1 <? N then PN_LH else PN_QE)).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI (HNC & G19 & G9 & G25 & G7).
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HNC as (G2 & G3 & G4 & G8 & G18 & G20 & G21 & G22 & G23 & G24 & G27).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
pose proof (tree_now mem HMI) as Htree.
destruct (troot_in_nodes t Hfull) as (m0 & Hm0 & Hrt). destruct (Hnodes m0 Hm0) as (Hr0 & Hr1 & _).
assert (HpM : 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia). assert (Hfi : 0 <= fmt * i) by nia.
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
pose proof (slot_now' mem 80 (troot t) HMI ltac:(lia) ltac:(unfold RGBA_FRAME; lia) Hsl80) as S80.
eapply SR_bind.
{ ltac2:(satvl NCL_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem i (troot t) Hi ltac:(rewrite Hrt; lia) Hh Hlz S80 G2 G9 G24 G21). }
cbv beta. intros c1 (regs1 & -> & Q1 & Q10 & Q11 & Hk1).
eapply SR_bind.
{ eapply (GLNI fy RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq regs1 t (flt + 4 * (fmt * i)) HJ);
[ rewrite Q1; apply ret_ok_even; vm_compute; reflexivity
| exact Hfrm | exact Q10 | exact Q11 | exact Htree | exact Hfull
| intros m Hm; split; [unfold tree_forall in Hwft; exact (proj1 (Forall_forall _ _) Hwft m Hm)|];
destruct (Hnodes m Hm) as (X1 & X2 & X3); pose proof (Hsep_tl m Hm); repeat split; lia
| lia | lia
| replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia; rewrite Z.mod_add by lia; exact Hf4
| intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia ]. }
cbv beta. intros c2 (fy2 & regs2 & m & -> & Hfrm2 & _ & HP2 & _ & _). rewrite Q1.
assert (KP : forall rr : reg, In rr CALLEE_SAVED -> In rr NCL_KEEP -> getr regs2 rr = getr regs rr).
{ intros rr Hc Hn. rewrite (regs_preserved_in regs1 regs2 rr HP2 Hc). exact (Hk1 rr Hn). }
apply (NSTP_run fy2 regs2 mem i true Hi HJ Hfrm2 HMI).
- exact (nregs_c_kept regs regs2 (fun rr Hrr => KP rr (NC_sub_CS rr Hrr) (NC_sub_NCL rr Hrr)) HNC).
- rewrite (KP 19%bv) by inK. exact G19.
- rewrite (KP 9%bv) by inK. exact G9.
- rewrite (KP 25%bv) by inK. exact G25.
- intros Hc. discriminate Hc.
Qed.
Lemma NPIX_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> nregs regs i ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs)) mdq) (npost (i + 1) (if i + 1 <? N then PN_LH else PN_QE)).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI (HNC & G19 & G9 & G25 & G7).
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HNC as (G2 & G3 & G4 & G8 & G18 & G20 & G21 & G22 & G23 & G24 & G27).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
pose proof (slot_now' mem 88 bef HMI ltac:(lia) ltac:(unfold RGBA_FRAME; lia) Hsl88) as S88.
assert (CONT : forall c', ntest_post mdq fy regs mem c' -> SR ubs2segs c' (npost (i + 1) (if i + 1 <? N then PN_LH else PN_QE))).
{ intros c' (fy2 & regs2 & ti & -> & Hfrm2 & Hk2).
pose proof (nregs_c_kept regs regs2 (fun rr Hrr => Hk2 rr (NC_sub_NT rr Hrr)) HNC) as HNC2.
assert (R19 : getr regs2 19 = Z_to_bv 64 i) by (rewrite (Hk2 19%bv) by inK; exact G19).
assert (R9 : getr regs2 9 = Z_to_bv 64 (fmt * i)) by (rewrite (Hk2 9%bv) by inK; exact G9).
assert (R25 : getr regs2 25 = Z_to_bv 64 (bfw * i + 2)) by (rewrite (Hk2 25%bv) by inK; exact G25).
assert (R7 : getr regs2 7 = Z_to_bv 64 fmt) by (rewrite (Hk2 7%bv) by inK; exact G7).
destruct ti.
- exact (NSTP_run fy2 regs2 mem i false Hi HJ Hfrm2 HMI HNC2 R19 R9 R25 (fun _ => R7)).
- exact (NCALL_run fy2 regs2 mem i Hi HJ Hfrm2 HMI (conj HNC2 (conj R19 (conj R9 (conj R25 R7))))). }
destruct Hha as [Hha0 | [Hha1 F4]].
- assert (P18 : getr regs 18 = Z_to_bv 64 1) by (rewrite G18, Hha0; reflexivity).
destruct (Z.eq_dec bef 0) as [Hb0 | Hb].
+ rewrite Hb0 in S88. eapply SR_bind; [|exact CONT].
ltac2:(satvl NT0_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem Hh Hlz Hfrm S88 G2 P18).
+ eapply SR_bind; [|exact CONT].
ltac2:(satvl NTB_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem i Hi Hb HJ Hfrm S88 G2 P18 G9 G24 G21 G22 ltac:(rewrite G25, (Hbfw Hb); reflexivity)).
- assert (P18 : getr regs 18 = Z_to_bv 64 0) by (rewrite G18, Hha1; reflexivity).
eapply SR_bind; [|exact CONT].
ltac2:(satvl NTA_run using (sat_vars ()) as LEM).
exact (LEM fy regs mem i Hi F4 HJ Hfrm P18 G9 G24 G21).
Qed.
Lemma NLOOP_run : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> Z.of_nat k = N - 1 - i ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> nregs regs i ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs)) mdq) (npost N PN_QE).
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
Lemma ND_at : forall regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
K_QE (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_ND (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_ND) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hnd & HQR & G18 & Hsl & Hsq & S80 & Hfc & Hobj & Hcg & Himg & Hchq & Htok & Hpnew & Hfimg & Hfnz & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
destruct HQR as (G24 & G25 & G7 & G20 & G8 & G21).
pose proof Htok as (Htree & Hfull & Hth & Hwft & Hmok & Hnodes).
pose proof Hsl as (S8 & S16 & S24 & S48).
pose proof Hsq as ((S64 & S88 & S104 & S112 & S120) & S32 & S40).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
set (keep := BASEv ++ cht_blks C ++ tree_blocks t).
assert (HBk : Permutation (blocks Lc Ac) (keep ++ [(pnew, fmt * N); (fimg, N); (flt, 4 * (fmt * N))])).
{ eapply Permutation_trans; [exact HB|]. subst keep. perm_tac. }
assert (Hsub : forall x0, In x0 BASEv -> In x0 keep) by (intros x0 Hx0; subst keep; apply in_app_iff; left; exact Hx0).
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ flt (4 * (fmt * N)) HHc HBk HBent Hsub ltac:(right; right; left; reflexivity) ltac:(lia)) as [Hfin Hfnot].
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ fimg N HHc HBk HBent Hsub ltac:(right; left; reflexivity) ltac:(lia)) as [Hgin Hgnot].
destruct (heap_blocks_range _ _ LAWS _ _ _ _ flt (4 * (fmt * N)) HHc Hfin ltac:(lia)) as (Hflt0 & Hflt1 & Hflt16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc Hgin ltac:(lia)) as (Hfimg0 & Hfimg1 & _).
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
assert (Rbff : 0 <= beffmt < 2 ^ 32).
{ pose proof (obj_at_nth ubs2segs memc r LAY_Rgb _ 10 _ _ Hobj eq_refl eq_refl) as [_ X]. cbn [fst snd] in X.
  change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in X. exact X. }
set (bfw := sx32v beffmt).
assert (Rbfw : 0 <= bfw < 2 ^ 64) by (subst bfw; apply sx32v_range; exact Rbff).
assert (Hbfw : bef <> 0 -> bfw = beffmt).
{ intros Hb. destruct (Hbefb Hb) as (Hbf & _). subst bfw. apply sx32v_small. lia. }
set (memD := memc).
assert (HtreeD : tree_at ubs2segs memD t) by exact Htree.
assert (Hsl48 : slot regs0 memD 48 fimg) by exact S48.
assert (Hsl80 : slot regs0 memD 80 (troot t)) by exact S80.
assert (Hsl88 : slot regs0 memD 88 bef) by exact S88.
assert (Hsl104 : slot regs0 memD 104 bfw) by exact S104.
assert (Hsl120 : slot regs0 memD 120 fmt) by exact S120.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
eapply SR_bind.
{ pose (Lq := Lc). pose (Aq := Ac). pose (mdq := mdc). pose (cq := ch_c C).
  ltac2:(satvl NEN_run using (sat_vars ()) as LEM).
  exact (LEM fxi regs1 memc Hh Hlz HFRM S48 S88 G2 G25 G24). }
cbv beta. intros c1 (fy1 & regs2 & -> & Hfrm1 & R9 & R19 & R25 & R27 & R21 & R22 & R23 & Hk1).
assert (HD0 : nregs flt fimg ha (ch_c C) bfw regs2 0).
{ unfold nregs, nregs_c.
  rewrite (Hk1 2%bv), (Hk1 3%bv), (Hk1 4%bv), (Hk1 8%bv), (Hk1 18%bv), (Hk1 20%bv), (Hk1 24%bv), (Hk1 7%bv) by inK.
  split; [|split; [exact R19|]; split; [rewrite Z.mul_0_r; exact R9|]; split; [rewrite Z.mul_0_r, Z.add_0_l; exact R25 | exact G7]].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [exact G18|]. split; [exact G20|].
  split; [exact R21|]. split; [exact R22|]. split; [exact R23|]. split; [exact G24 | exact R27]. }
eapply SR_bind.
{ pose (Lq := Lc). pose (Aq := Ac). pose (mdq := mdc). pose (cq := ch_c C).
  ltac2:(satvl NLOOP_run using (sat_vars ()) as LEM).
  exact (LEM (Z.to_nat (N - 1)) fy1 regs2 memc 0 ltac:(lia) ltac:(lia) HJ Hfrm1 ltac:(intros a0 _ _; reflexivity) HD0). }
cbv beta. intros cE (fyE & regsE & memE & -> & HJE & HfrmE & HMIE & HDE). clear HJ.
destruct HDE as ((F2 & F3 & F4 & F8 & F18 & F20 & F21 & F22 & F23 & F24 & F27) & F19 & F9 & F25 & F7).
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte ubs2segs memE x = mbyte ubs2segs memc x).
{ intros x Hx Hs Hna. apply HMIE; lia. }
assert (KB : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte ubs2segs memE (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi.
  assert (Hbf : In (b, m) (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t)).
  { apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; exact Hbm]. }
  assert (Hbg : In (b, m) (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))])).
  { apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; rewrite app_assoc; apply in_app_iff; left; exact Hbm]. }
  pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (b, m) HHc HBg Hbg) as X2. cbn [fst snd] in X2.
  destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc ltac:(eapply blocks_perm_in; [exact HBf | right; exact Hbf]) ltac:(lia)) as (Y1 & Y2 & _).
  apply HMIE; lia. }
ltac2:(satvl qfacts_kept using (sat_vars ()) as QK).
destruct (QK memc memE ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH KB) as (TR & TS & TQ & TF & TO & TC & TI & TH & TT).
pose proof (TQ Hsq) as ((T64 & _) & _).
assert (T80 : slot regs0 memE SL_80 (troot t)).
{ intros k Hk. rewrite KH; [apply S80; exact Hk | | | ]; unfold sp, sp0, RGBA_FRAME, OFF_apal, SL_80 in *; lia. }
apply (KQE fyE regsE Lc Ac memE mdc ha pnew fimg imgl C cnt pal t flt HfrmE).
split.
{ split; [exact HJE|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
  split; [exact (TR HRA)|]. split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
  split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
    intros i Hi. unfold RGBFC_SIZE in *. apply KH; unfold sp, sp0, RGBA_FRAME, OFF_apal in *; lia. }
  split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [exact F2 | split; [exact F3 | exact F4]]|].
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|].
split; [exact F24|]. split; [exact F20|]. split; [exact F8|].
split; [exact (TS Hsl)|]. split; [exact T80|]. split; [exact T64|].
split; [exact (TF Hfc)|]. split; [exact (TO Hobj)|]. split; [exact (TC Hcg)|].
split; [exact (TI Himg)|]. split; [exact (TH Hchq)|]. split; [exact (TT Htok)|].
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfnz|]. exact HB.
Qed.
End f.
Lemma ubs2_rgbadd_ND : seg_ND (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KQE fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt HFRM HAT. exact (ND_at regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT). Qed.
End d.
End c.
