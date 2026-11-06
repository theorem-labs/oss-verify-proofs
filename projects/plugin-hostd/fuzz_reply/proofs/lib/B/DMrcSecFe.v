(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecFe.v (commit 6fdbdd538bcf, H4 flag-free secondary Recycle walk set; file sha256 61d2ff6d28d5) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved: 2 data addresses by port_addr_check e55e1b52a8a0 MAPS predictions; 0 function pairs; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecFe.v at commit edc7f827e38, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4): TWIN of YFfe.v over the CUT-READ record DMrcSecFc.sec_cut and the cut
   relation ARXr (rcc_pre_x) instead of cgif's ARm (rcc_pre); the size bounds come from lmaxd_ok / nmaxd_ok. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb DMrcSecGx DMrcSecGxWalk DMrcSecGv YFg8 YFfc DMrcSecF6 YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF DMrcSecFc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, YFgu.GFRAME, DMrcSecGx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section c.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable inst : Z.
Hypothesis PRE : rcc_pre_x B ARXr inst ly X k cbp W regs mem md.
Hypothesis SC : DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Local Notation fc_LO := (DMrcSecFc.sc_LO B ly X k W regs mem r o sm i SC).
Local Notation fc_IMG := (DMrcSecFc.sc_IMG B ly X k W regs mem r o sm i SC).
Local Notation fc_Hk := (DMrcSecFc.sc_Hk B ly X k W regs mem r o sm i SC).
Local Notation fc_HSP := (DMrcSecFc.sc_HSP B ly X k W regs mem r o sm i SC).
Local Notation fc_HI := (DMrcSecFc.sc_HI B ly X k W regs mem r o sm i SC).
Local Notation fc_ARRF := (DMrcSecFc.sc_ARRF B ly X k W regs mem r o sm i SC).
Local Notation fc_slot_geom := (DMrcSecFc.sc_slot_geom B ly X k W regs mem r o sm i SC).
Local Notation fc_slot_val := (DMrcSecFc.sc_slot_val B ly X k W regs mem r o sm i SC).
Local Notation fc_ELEN := (DMrcSecFc.sc_ELEN B ly X k W regs mem r o sm i SC).
Local Notation fc_const_vals := (DMrcSecFc.sc_const_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_inst_vals := (DMrcSecFc.sc_inst_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_junkD_vals := (DMrcSecFc.sc_junkD_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_last_facts := (DMrcSecFc.sc_last_facts B ly X k W regs mem r o sm i SC).
Local Notation fc_maph_vals := (DMrcSecFc.sc_maph_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_qi_val := (DMrcSecFc.sc_qi_val B ly X k W regs mem r o sm i SC).
Local Notation fc_shadow_present := (DMrcSecFc.sc_shadow_present B ly X k W regs mem r o sm i SC).
Local Notation fc_thread_present := (DMrcSecFc.sc_thread_present B ly X k W regs mem r o sm i SC).
Local Notation fc_tls_vals := (DMrcSecFc.sc_tls_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_hw_val := (DMrcSecFc.sc_hw_val B ly X k W regs mem r o sm i SC).
Local Notation fc_junk_vals := (DMrcSecFc.sc_junk_vals B ly X k W regs mem r o sm i SC).
Local Notation fc_MAPX := (DMrcSecFc.sc_MAPX B ly X k W regs mem r o sm i SC).
Local Notation fc_SX := (DMrcSecFc.sc_SX B ly X k W regs mem r o sm i SC).
Local Notation fc_SECX := (DMrcSecFc.sc_SECX B ly X k W regs mem r o sm i SC).
Local Notation fc_LST := (DMrcSecFc.sc_LST B ly X k W regs mem r o sm i SC).
Local Notation fc_FH_A := (DMrcSecFc.sc_FH_A B ly X k W regs mem r o sm i SC).
Local Notation fc_GEOM := (DMrcSecFc.GEOMw B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE).
Local Notation fc_hdr_facts := (DMrcSecFc.hdr_factsw B ly X k W regs mem r o sm i SC NMAXD NOK HN).
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation nA := (YFg8.nA X).
Local Notation hdr := (YFfc.hdr B ly k).
Local Notation HWv := (YFfc.HWv B ly k W mem).
Local Notation j1 := (YFfc.j1 ly W mem).
Local Notation j2 := (YFfc.j2 ly W mem).
Local Notation v := (DMrcSecF6.v regs).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
Local Notation vs3 := (DMrcSecF6.v regs 19%bv).
Local Notation vs4 := (DMrcSecF6.v regs 20%bv).
Local Notation WINA := (DMrcSecF6.WINA regs).
Local Notation E0x := (DMrcSecGx.E0 ly).
Let LO : layout_ok ly := fc_LO.
Lemma Uv : forall r', 0 <= v r' < 2 ^ 64. Proof. intros r'. unfold DMrcSecF6.v. apply u64_range. Qed.
Lemma chunk_litx : forall regsX mm a (w : BinNums.N) x, val_mem tfibsegs mm a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) mm 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros regsX mm a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_litx_at : forall regsX mm base a (w : BinNums.N) x, val_mem tfibsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) mm base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros regsX mm base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atomx : forall regsX mm base a (w : BinNums.N) k0 d x, ew (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs mm (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) mm base (YP09.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros regsX mm base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Theorem XSEED : forall regsX memX, DMrcSecF6.STX B ly X k cbp W regs mem r regsX memX ->
DMrcSecGx.free_hyps W ly regsX memX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4.
Proof.
intros regsX memX (regsL & PX & SR & R13).
destruct PX as (SRL & L2 & L1r & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & MQA & PRS & V1 & V8 & V9 & V18 & V19 & V20 & V56 & V10 & V72 & V80 & VM).
pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & _ & Hal & HloCF & Hcb1 & Hcb2 & _ & HPRESCF & _ & _ & _ & Htp & _ & _). assert (Hlo : ly_stk_lo ly + KSTACK <= spZ regs) by (clear - HloCF; unfold KSTACK_CF, KSTACK in *; lia). assert (HPRES : forall a, spZ regs - KSTACK <= a < spZ regs -> apresent (w_H W) mem a) by (intros a0 Ha0'; apply HPRESCF; clear - Ha0'; unfold KSTACK_CF, KSTACK in *; lia).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof (fc_HI) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & hTAL & hCAL & _).
pose proof hT1 as ZT3. pose proof hC1 as ZC3.
pose proof (fc_hdr_facts) as (D1 & D2 & D3 & D4 & _).
pose proof (fc_GEOM) as (M1 & M2 & M3 & M4 & M5 & _).
pose proof (fc_hw_val) as (W1 & W2 & WP & WR).
pose proof (fc_maph_vals) as (H1v & H2v & _ & _ & HPm).
pose proof (fc_tls_vals) as (T1 & T2 & T3 & T4 & T5 & T6).
pose proof (fc_inst_vals) as (I1 & I2 & _ & _).
pose proof (fc_junk_vals) as ([J1R J1] & [J2R J2]).
pose proof (DMrcSecF6.CBP B ly X k cbp W regs mem md r o sm i ARXr inst PRE SC) as (C10 & C1 & C2 & C3 & CR).
pose proof (fc_MAPX 0%nat _ eq_refl) as DP.
pose proof (fc_MAPX 2%nat _ eq_refl) as DT.
pose proof (fc_MAPX 6%nat _ eq_refl) as DC.
cbn [fst snd] in DP, DT, DC. pose proof (fc_ELEN) as (E & _).
unfold YFf4.MAP, YFf4.LEN in DP, DT, DC. rewrite <- E in DP, DT, DC. fold (YFg8.MAP ly r) in DP, DT, DC. clear E.
pose proof (fc_thread_present) as TPRES.
clear LO.
assert (XFER : forall a (w : nat) x, val_mem tfibsegs m0 a w x -> (forall kk, (kk < w)%nat -> ~ WINA (a + Z.of_nat kk) /\ 0 <= a + Z.of_nat kk < 2 ^ 64) ->
val_mem tfibsegs (mrestrict H0 memX) a w x).
{ intros a w x Hv Hout. apply (val_mem_frame (w_H W) mem memX); [|exact Hv]. intros kk Hkk. apply MQA. destruct (Hout kk Hkk) as [O1 O2]. rewrite unsigned_lit_small by exact O2. exact O1. }
assert (PXFER : forall a, apresent H0 mem a -> ~ WINA a -> 0 <= a < 2 ^ 64 -> apresent H0 memX a).
{ intros a Hp Ho Ha. apply (apresent_same (w_H W) mem); [apply MQA; rewrite unsigned_lit_small by exact Ha; exact Ho | exact Hp]. }
assert (X2 : getr regsX 2 = w64 (sp0 - 80)) by (rewrite (SR 2%bv ltac:(inS)); exact L2).
assert (USX : bv_unsigned (getr regsX 2) = sp0 - 80) by (rewrite X2; unfold w64; apply unsigned_lit_small; clear - Hlo hS1 Hcb1 Hcb2 hS2; numconst; lia).
assert (HREGS : getr regsX 10 = w64 (A_ALLOCATOR + 64) /\ getr regsX 11 = w64 hdr /\ getr regsX 13 = w64 MAP /\ getr regsX 8 = w64 (A_ALLOCATOR + 680) /\
getr regsX 9 = w64 hdr /\ getr regsX 18 = w64 vs2 /\ getr regsX 19 = w64 A_ALLOCATOR /\ getr regsX 20 = w64 (2 ^ 37)).
{ splits.
- rewrite (SR 10%bv ltac:(inS)). exact L10.
- rewrite (SR 11%bv ltac:(inS)). exact L11.
- exact R13.
- rewrite (SR 8%bv ltac:(inS)). exact L8.
- rewrite (SR 9%bv ltac:(inS)). exact L9.
- rewrite (SR 18%bv ltac:(inS)), (SRL 18%bv ltac:(inS)). unfold DMrcSecF6.v, w64. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite (SR 19%bv ltac:(inS)). exact L19.
- rewrite (SR 20%bv ltac:(inS)). exact L20. }
assert (XTP : getr regsX 4 = w64 TFIB_TP) by (rewrite (SR 4%bv ltac:(inS)), (SRL 4%bv ltac:(inS)), Htp, (ts_tp _ TB); reflexivity).
clear SR SRL L2 L1r L8 L9 L10 L11 L12 L13 L14 L19 L20 R13 Htp.
assert (OUT_img : forall a, 0 <= a < TFIB_IMG_END -> ~ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) -> ~ WINA a /\ 0 <= a < 2 ^ 64).
{ intros a Ha Hm. unfold DMrcSecF6.WINA. fold sp0. clear - Ha Hm Hlo hS1. numconst. lia. }
assert (OUT_z : forall x sz a, zone3 x sz -> x <= a < x + sz -> ~ WINA a /\ 0 <= a < 2 ^ 64).
{ intros x sz a Z3 Ha. unfold DMrcSecF6.WINA. fold sp0. clear - Z3 Ha Hlo hS1 hCE. numconst. lia. }
pose proof M1 as ZM3.
pose proof (Uv 1%bv) as U1. pose proof (Uv 8%bv) as U8. pose proof (Uv 9%bv) as U9. pose proof (Uv 18%bv) as U18. pose proof (Uv 19%bv) as U19. pose proof (Uv 20%bv) as U20.
constructor.
- exact (fc_LO).
- exact (fc_IMG).
- exact XTP.
- exact HREGS.
- rewrite USX. replace (sp0 - 80 + DMrcSecGx.GFRAME) with sp0 by (numconst; lia). split; [exact Hlo | clear - Hcb1 Hcb2; lia].
- rewrite USX. clear - Hal. apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q - 5). lia.
- rewrite USX. replace (sp0 - 80 + DMrcSecGx.GFRAME) with sp0 by (numconst; lia). intros a Ha.
destruct (Z_lt_le_dec a (sp0 - 80)) as [LOW|HI'].
+ apply PXFER; [apply HPRES; lia | unfold DMrcSecF6.WINA; fold sp0; clear - Ha LOW Hlo hS1; numconst; lia | clear - Ha LOW Hlo hS1 hS2 Hcb1 Hcb2; numconst; lia].
+ apply PRS. lia.
- rewrite USX. splits.
+ exact V80.
+ replace (sp0 - 80 + 8) with (sp0 - 72) by lia. exact V72.
+ replace (sp0 - 80 + 16) with (sp0 - 64) by lia. exact V10.
+ replace (sp0 - 80 + 24) with (sp0 - 56) by lia. exact V56.
+ replace (sp0 - 80 + 32) with (sp0 - 48) by lia. exact V20.
+ replace (sp0 - 80 + 40) with (sp0 - 40) by lia. exact V19.
+ replace (sp0 - 80 + 48) with (sp0 - 32) by lia. exact V18.
+ replace (sp0 - 80 + 56) with (sp0 - 24) by lia. exact V9.
+ replace (sp0 - 80 + 64) with (sp0 - 16) by lia. exact V8.
+ replace (sp0 - 80 + 72) with (sp0 - 8) by lia. exact V1.
- clear - U1 U8 U9 U18 U19 U20 C1 C2 C3 CR. unfold DMrcSecF6.v in *. splits; lia.
- split; [exact M1|]. clear - M1 M2 M3 M4 M5 D1 D2 D3 D4 DP hSP1 hSP2 hP1 hP2. unfold zdisjoint in DP. cbn [fst snd] in DP. numconst. splits; try assumption; lia.
- splits.
+ apply XFER; [exact H1v | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk M4; lia].
+ apply XFER; [exact H2v | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk M4; lia].
+ intros a Ha. apply PXFER; [apply HPm; lia | |]; destruct (OUT_z _ _ a ZM3 ltac:(clear - Ha M4; lia)) as [O1 O2]; assumption.
- split; [exact WR | exact D2].
- splits.
+ apply XFER; [exact W1 | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; lia].
+ apply XFER; [exact W2 | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; lia].
+ intros a Ha. apply PXFER; [apply WP; lia | |]; destruct (OUT_z _ _ a ZM3 ltac:(clear - Ha D1 D2 D3 M4; lia)) as [O1 O2]; assumption.
-   intros kk Hkk. destruct kk; [|lia]. exact (VM 0%nat ltac:(lia)).
- apply XFER; [exact I1 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
- splits.
+ apply XFER; [exact T4 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
+ apply XFER; [exact T5 | intros kk Hkk; apply (OUT_z _ _ _ ZC3); clear - Hkk; lia].
+ apply XFER; [exact T6 | intros kk Hkk; apply (OUT_z _ _ _ ZC3); clear - Hkk; lia].
- split; [|split; [|split; [exact J1R | split; [exact J2R |]]]].
+ apply XFER; [exact J1 | intros kk Hkk; apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; lia].
+ apply XFER; [exact J2 | intros kk Hkk; apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; lia].
+ intros a Ha. apply PXFER; [apply TPRES; clear - Ha; numconst; lia | |]; destruct (OUT_z _ _ a ZT3 ltac:(clear - Ha; unfold t_stats, kThreadObjSize in *; lia)) as [O1 O2]; assumption.
-
assert (VX : val_mem tfibsegs (mrestrict H0 memX) MAP 8 MAP /\ val_mem tfibsegs (mrestrict H0 memX) (MAP + 8) 8 LEN /\
val_mem tfibsegs (mrestrict H0 memX) hdr 4 HWv /\ val_mem tfibsegs (mrestrict H0 memX) (hdr + 4) 4 (ck_n k) /\
val_mem tfibsegs (mrestrict H0 memX) (ly_C ly + 8) 4 0 /\ val_mem tfibsegs (mrestrict H0 memX) (ly_C ly + 152) 8 T /\
val_mem tfibsegs (mrestrict H0 memX) (T + t_stats + 40) 8 j1 /\ val_mem tfibsegs (mrestrict H0 memX) (T + t_stats + 48) 8 j2 /\
val_mem tfibsegs (mrestrict H0 memX) (A_ALLOCATOR + 64) 8 4096 /\ val_mem tfibsegs (mrestrict H0 memX) (A_ALLOCATOR + 32) 8 SB /\
val_mem tfibsegs (mrestrict H0 memX) 0xa5ea0 1 1 /\ val_mem tfibsegs (mrestrict H0 memX) 0xa5ea4 4 0 /\
val_mem tfibsegs (mrestrict H0 memX) (TFIB_TP - 88) 8 TFIB_TSD /\ val_mem tfibsegs (mrestrict H0 memX) TFIB_TSD 8 (ly_C ly)).
{ splits.
- apply XFER; [exact H1v | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk M4; lia].
- apply XFER; [exact H2v | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk M4; lia].
- apply XFER; [exact W1 | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; lia].
- apply XFER; [exact W2 | intros kk Hkk; apply (OUT_z _ _ _ ZM3); clear - Hkk D1 D2 D3 M4; lia].
- apply XFER; [exact T5 | intros kk Hkk; apply (OUT_z _ _ _ ZC3); clear - Hkk; lia].
- apply XFER; [exact T6 | intros kk Hkk; apply (OUT_z _ _ _ ZC3); clear - Hkk; lia].
- apply XFER; [exact J1 | intros kk Hkk; apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; lia].
- apply XFER; [exact J2 | intros kk Hkk; apply (OUT_z _ _ _ ZT3); clear - Hkk; unfold t_stats, kThreadObjSize in *; lia].
- apply XFER; [exact I2 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
- apply XFER; [exact I1 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
- apply XFER; [exact T1 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
- apply XFER; [exact T2 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
- apply XFER; [exact T3 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia].
- apply XFER; [exact T4 | intros kk Hkk; apply OUT_img; clear - Hkk; numconst; lia]. }
destruct VX as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14).
assert (TJP : forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent H0 memX a).
{ intros a Ha. apply PXFER; [apply TPRES; clear - Ha; numconst; lia | |]; destruct (OUT_z _ _ a ZT3 ltac:(clear - Ha; unfold t_stats, kThreadObjSize in *; lia)) as [O1 O2]; assumption. }
pose proof hI1 as J1'. pose proof hI2 as J2'. rewrite hIE in J1', J2'.
clear XFER PXFER HPRES MQA H1v H2v W1 W2 WP HPm T1 T2 T3 T4 T5 T6 I1 I2 J1 J2 TPRES OUT_img OUT_z hI1 hI2 hIE hQ1 hQ2 hQAL C10.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, KSTACK, kLowMemEnd, TFIB_INST in hP1, hP2, hT1, hT2, hC1, hC2, hS1, hS2, hCE, hSP1, hSP2, Hlo, J1', J2', M1, M2, M4, D1, D3, C1, C2.
rewrite restrict_mkst_fx. unfold DMrcSecGx.SS0, DMrcSecGx.SR0, sr_set. cbn [bv_eqb]. unfold DMrcSecGx.E0, w64. apply (entry_st_ok_full tfibsegs).
+ destruct HREGS as (R10 & R11 & R13' & R8 & R9 & R18 & R19 & R20).
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact XTP]
| intros XX; discriminate | cbn [sv_denot]; exact R10]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite DMrcSecGx.EqM, R11; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite DMrcSecGx.EqMAP, R13'; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; exact R8]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite DMrcSecGx.EqM, R9; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4); rewrite DMrcSecGx.EqS2, R18; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]
| intros XX; discriminate | cbn [sv_denot]; exact R19]
| intros XX; discriminate | cbn [sv_denot]; exact R20].
+ vm_compute. reflexivity.
+
cbn [ms_mem mkst]. fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
unfold DMrcSecGx.REG0, DMrcSecGx.R_STK, DMrcSecGx.R_MAPH, DMrcSecGx.R_HDR, DMrcSecGx.R_MUT1, DMrcSecGx.R_CTX, DMrcSecGx.R_JST, flit1, flit4, flit8, fatom8.
apply Forall_cons.
{   reg_intro. rewrite (DMrcSecGx.E2 ly regsX), X2. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o' Ho'. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; lia | apply PRS; lia]. }
repeat (apply Forall_cons); [..|apply Forall_nil].
- apply (chunk_atomx _ _ _ _ 8 46%nat 0 vs2); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact V80 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 35%nat 0 hdr); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 8) with (sp0 - 72) by lia; exact V72 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 42%nat 0 cbp); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 16) with (sp0 - 64) by lia; exact V10 | r8 | cbn; lia].
- apply chunk_litx_at; [replace (sp0 - 80 + 24) with (sp0 - 56) by lia; exact V56 | cbn; lia | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 48%nat 0 vs4); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 32) with (sp0 - 48) by lia; exact V20 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 47%nat 0 vs3); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 40) with (sp0 - 40) by lia; exact V19 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 46%nat 0 vs2); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 48) with (sp0 - 32) by lia; exact V18 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 45%nat 0 vs1); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 56) with (sp0 - 24) by lia; exact V9 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 44%nat 0 vs0); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 64) with (sp0 - 16) by lia; exact V8 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 43%nat 0 vra); [rewrite Z.sub_0_r; reflexivity | lia | replace (sp0 - 80 + 72) with (sp0 - 8) by lia; exact V1 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite DMrcSecGx.EqMAP. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atomx _ _ _ _ 8 36%nat 0 MAP); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact Y1 | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 37%nat 0 LEN); [rewrite Z.sub_0_r; reflexivity | lia | exact Y2 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite DMrcSecGx.EqM. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atomx _ _ _ _ 4 38%nat 0 HWv); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact Y3 | r4 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 4 39%nat 0 (ck_n k)); [rewrite Z.sub_0_r; reflexivity | lia | exact Y4 | r4 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split.
{ intros o' Ho'. apply rw_writable. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_litx; [| cbn; lia | cbn; lia]. intros kk Hkk. destruct kk; [|lia]. exact (VM 0%nat ltac:(lia)). }
apply Forall_cons.
{   reg_intro. rewrite DMrcSecGx.EqC. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_litx_at; [exact Y5 | cbn; lia | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 32%nat 0 T); [rewrite DMrcSecGx.EqT; unfold w64; f_equal; lia | lia | exact Y6 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite DMrcSecGx.EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o' Ho'. apply apresent_writable_off; [apply (zone3_off_img _ _ _ ZT3); unfold kThreadObjSize; lia|]. apply TJP. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atomx _ _ _ _ 8 40%nat 0 j1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact Y7 | lia] | r8 | cbn; lia].
- apply (chunk_atomx _ _ _ _ 8 41%nat 0 j2); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact Y8 | lia] | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_litx; [exact Y9 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomx _ _ _ _ 8 34%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact Y10 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil]. apply chunk_litx; [exact Y11 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{   reg_intro. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil]. apply chunk_litx; [exact Y12 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_litx; [exact Y13 | unfold TFIB_TSD; cbn; lia | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{   reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomx _ _ _ _ 8 33%nat 0 (ly_C ly)); [rewrite DMrcSecGx.EqC; unfold w64; f_equal; lia | lia | rewrite Z.add_0_l; exact Y14 | cbn; lia | cbn; lia]. }
+
fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4). apply pairwise_disjoint_of_extents.
unfold DMrcSecGx.REG0, DMrcSecGx.R_STK, DMrcSecGx.R_MAPH, DMrcSecGx.R_HDR, DMrcSecGx.R_MUT1, DMrcSecGx.R_CTX, DMrcSecGx.R_JST, flit1, flit4, flit8, fatom8, extent_of_region.
cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (DMrcSecGx.E2 ly regsX), X2, DMrcSecGx.EqMAP, DMrcSecGx.EqM, DMrcSecGx.EqC, DMrcSecGx.EqT. unfold w64.
pose proof (fc_HI) as HIF.
destruct HIF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hTC & _ & _).
clear - Hlo Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hC1 hC2 hTC M1 M2 M4 D1 D3 DT DC J1' J2'. unfold zdisjoint in DT, DC. cbn [fst snd] in DT, DC. numconst. rewrite !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
+
fold (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4). split; [|split; exact I].
assert (AF : forall k0 Xv lo hi al, ew (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew (E0x regsX hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4) 2 = w64 (sp0 - 80)) by (rewrite (DMrcSecGx.E2 ly regsX); exact X2).
cbn [DMrcSecGx.FFX f_atoms atoms_ok]. numconst.
split. { apply (AF 2%nat (sp0 - 80)); [exact E2'| | | |]. all: clear - CR0 Hlo Hcb1 Hcb2 hS1 hS2 hCE Hal; first [lia | apply Z.mod_divide in Hal as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (q - 5); change (2 ^ 4) with 16; lia]. }
split. { apply (AF 32%nat T); [reflexivity| | | |]. all: clear - CR0 hT1 hT2 hTAL; first [lia | change (2 ^ 12) with 4096; exact hTAL]. }
split. { apply (AF 33%nat (ly_C ly)); [reflexivity| | | |]. all: clear - CR0 hC1 hC2 hCAL; first [lia | change (2 ^ 3) with 8; exact hCAL]. }
split. { apply (AF 34%nat SB); [reflexivity| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 hSAL; first [lia | apply Z.mod_divide in hSAL as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists q; change (2 ^ 16) with 65536; lia]. }
split. { apply (AF 35%nat hdr); [reflexivity| | | |]. all: clear - CR0 D1 D3 D2 D4 M1 M2 M4; first [lia | change (2 ^ 4) with 16; exact D4]. }
split. { apply (AF 36%nat MAP); [reflexivity| | | |]. all: clear - CR0 M1 M2 M3 M4; first [lia | change (2 ^ 12) with 4096; exact M3]. }
split. { apply (AF 37%nat LEN); [reflexivity| | | |]. all: clear - M4 M5; first [lia | change (2 ^ 12) with 4096; exact M5]. }
split. { apply (AF 38%nat HWv); [reflexivity| | | |]. all: clear - WR; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 39%nat (ck_n k)); [reflexivity| | | |]. all: clear - D2; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat j1); [reflexivity| | | |]. all: clear - J1R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 41%nat j2); [reflexivity| | | |]. all: clear - J2R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 42%nat cbp); [reflexivity| | | |]. all: clear - CR0 C1 C2 C3 CR; first [lia | change (2 ^ 3) with 8; exact C3]. }
split. { apply (AF 43%nat vra); [reflexivity| | | |]. all: clear - U1; unfold DMrcSecF6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 44%nat vs0); [reflexivity| | | |]. all: clear - U8; unfold DMrcSecF6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 45%nat vs1); [reflexivity| | | |]. all: clear - U9; unfold DMrcSecF6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 46%nat vs2); [reflexivity| | | |]. all: clear - U18; unfold DMrcSecF6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 47%nat vs3); [reflexivity| | | |]. all: clear - U19; unfold DMrcSecF6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 48%nat vs4); [reflexivity| | | |]. all: clear - U20; unfold DMrcSecF6.v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
Qed.
End c.
End b.
