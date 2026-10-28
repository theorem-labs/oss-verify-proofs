(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFgx AFfd AFgv AFg8 AFfc AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, AFgu.GFRAME, AFgx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros md. destruct md as [? [? ? ?] ? ? ? ? ? ? ?]; reflexivity. Qed.
Section c.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
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
Local Notation arr := (st_sec_arr X).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation hdr := (AFfc.hdr B ly k).
Local Notation HWv := (AFfc.HWv B ly k W mem).
Local Notation j1 := (AFfc.j1 ly W mem).
Local Notation j2 := (AFfc.j2 ly W mem).
Local Notation IMG := (AFfc.IMG B ly X k cbp W regs mem md PRE).
Definition v (r' : bv 5) : Z := bv_unsigned (getr regs r').
Local Notation vra := (v 1%bv).
Local Notation vs0 := (v 8%bv).
Local Notation vs1 := (v 9%bv).
Local Notation vs2 := (v 18%bv).
Local Notation vs3 := (v 19%bv).
Local Notation vs4 := (v 20%bv).
Definition hs : list Z := List.map (fun rj => ly_sec ly rj) arr.
Definition lim : Z := Q + 8 * nA.
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.
Lemma Uv : forall r', 0 <= v r' < 2 ^ 64. Proof. intros r'. unfold v. apply u64_range. Qed.
Lemma HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly. Proof. exact (AFfc.HSP B ly X k cbp W regs mem md PRE). Qed.
Lemma CBP : getr regs 10 = w64 cbp /\ kHighMemBeg <= cbp /\ cbp + 16 <= kHighMemEnd /\ cbp mod 8 = 0 /\ 0 <= cbp < 2 ^ 64.
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & Hcb3 & _ & _ & _ & _ & _ & Ha0 & _). unfold spZ in *.
pose proof (AFfc.HI B TB ly X k cbp W regs mem md PRE) as (_ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _).
split; [exact Ha0|]. clear - Hlo Hcb1 Hcb2 Hcb3 hS1 hS2. numconst. lia.
Qed.
Definition WINA (a : Z) : Prop := (sp0 - 80 <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684).
Definition MEQA (mm : word -> option byte) : Prop := forall x : word, ~ WINA (bv_unsigned x) -> mm x = mem x.
Definition PREX (regsL : bvmap 5 word) (memL : word -> option byte) : Prop :=
(forall r' : bv 5, In r' AFgu.SREGS -> getr regsL r' = getr regs r') /\
getr regsL 2 = w64 (sp0 - 80) /\ getr regsL 1 = w64 0x335e4 /\ getr regsL 8 = w64 (A_ALLOCATOR + 680) /\ getr regsL 9 = w64 hdr /\
getr regsL 10 = w64 (A_ALLOCATOR + 64) /\ getr regsL 11 = w64 hdr /\ getr regsL 12 = w64 Q /\ getr regsL 13 = w64 0 /\ getr regsL 14 = w64 (Q + 8 * nA) /\
getr regsL 19 = w64 A_ALLOCATOR /\ getr regsL 20 = w64 (2 ^ 37) /\
MEQA memL /\
(forall a, sp0 - 80 <= a < sp0 -> apresent H0 memL a) /\
val_mem tfibsegs (mrestrict H0 memL) (sp0 - 8) 8 vra /\ val_mem tfibsegs (mrestrict H0 memL) (sp0 - 16) 8 vs0 /\
val_mem tfibsegs (mrestrict H0 memL) (sp0 - 24) 8 vs1 /\ val_mem tfibsegs (mrestrict H0 memL) (sp0 - 32) 8 vs2 /\
val_mem tfibsegs (mrestrict H0 memL) (sp0 - 40) 8 vs3 /\ val_mem tfibsegs (mrestrict H0 memL) (sp0 - 48) 8 vs4 /\
val_mem tfibsegs (mrestrict H0 memL) (sp0 - 56) 8 0x335e4 /\ val_mem tfibsegs (mrestrict H0 memL) (sp0 - 64) 8 cbp /\
val_mem tfibsegs (mrestrict H0 memL) (sp0 - 72) 8 hdr /\ val_mem tfibsegs (mrestrict H0 memL) (sp0 - 80) 8 vs2 /\
val_mem tfibsegs (mrestrict H0 memL) (A_ALLOCATOR + 680) 4 1.
Definition STX (regsX : bvmap 5 word) (memX : word -> option byte) : Prop :=
exists regsL, PREX regsL memX /\ (forall r' : bv 5, In r' AFgw.SREGS -> getr regsX r' = getr regsL r') /\ getr regsX 13 = w64 MAP.
Definition ATX (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsX memX matX, c' = mkCfg (mkst regsX (w64 0x33888) memX (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matX md) /\ STX regsX memX.
Lemma hs_facts : length hs = length arr /\ hs <> [] /\ In MAP hs /\ Forall (fun h => 0 <= h) hs /\
(forall j h, nth_error hs j = Some h -> exists rj, nth_error arr j = Some rj /\ h = ly_sec ly rj).
Proof.
pose proof (AFfc.ARRF B ly X k cbp W regs mem md r i PRE Hi) as (A1 & A2 & A3 & A4 & A5).
unfold hs. rewrite length_map. splits.
- reflexivity.
- destruct (st_sec_arr X) as [|x t] eqn:E; [cbn in A4; unfold AFg8.nA in A4; rewrite E in A4; cbn in A4; lia | discriminate].
- apply in_map_iff. exists r. split; [reflexivity | exact A1].
- apply Forall_forall. intros h Hh. apply in_map_iff in Hh as (rj & <- & Hrj).
destruct (In_nth_error _ _ Hrj) as [j Hj]. destruct (AFfc.slot_geom B ly X k cbp W regs mem md r o sm PRE Hb Hsm j rj Hj) as (y & _ & _ & _ & G1 & _). clear - G1. numconst. lia.
- intros j h Hj. rewrite nth_error_map in Hj. destruct (nth_error (st_sec_arr X) j) as [rj|] eqn:E; [|discriminate Hj]. cbn in Hj. injection Hj as <-. exists rj. auto.
Qed.
Lemma scan_is_MAP : scan hdr 0 hs = MAP.
Proof.
pose proof hs_facts as (L1 & L2 & L3 & L4 & L5). pose proof (AFfc.GEOM B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (M1 & M2 & M3 & M4 & _).
pose proof (AFfc.hdr_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (D1 & D2 & D3 & _).
apply (scan_finds_map hdr hs MAP LEN (fun _ => 1) L4 L3).
- lia.
- intros h Hh Hne. destruct (In_nth_error _ _ Hh) as [j Hj]. destruct (L5 j h Hj) as (rj & Hrj & ->).
destruct (AFfc.slot_geom B ly X k cbp W regs mem md r o sm PRE Hb Hsm j rj Hrj) as (y & _ & _ & _ & G1 & G2 & G3 & G4 & G5). specialize (G5 Hne). lia.
- intros; lia.
- clear - M1. numconst. lia.
Qed.
Lemma L0_STL : forall W' c', AFgu.at_L0 W regs mem md hdr nA Q W' c' ->
W' = W /\ exists regsL memL matL, c' = mkCfg (mkst regsL (w64 0x3385c) memL (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matL md) /\
AFfb.stL W hdr lim Q 0 hs regsL memL /\ PREX regsL memL.
Proof.
intros W' c' HL. destruct HL as (-> & regsL & memL & matL & -> & SR & R2 & R1 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R19 & R20 & MQ & PRS & VALS).
pose proof (AFfc.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof HSP as [S1 S2]. pose proof (AFfc.ARRF B ly X k cbp W regs mem md r i PRE Hi) as (A1 & A2 & A3 & A4 & A5).
pose proof (AFfc.hdr_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (D1 & D2 & D3 & _).
pose proof (AFfc.GEOM B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (M1 & M2 & M3 & M4 & _).
pose proof hs_facts as (L1 & L2 & L3 & L4 & L5). pose proof CBP as (C10 & _).
assert (MQA : MEQA memL).
{ intros x Hx. apply MQ. unfold AFgu.WIN. fold sp0. unfold WINA in Hx. numconst. exact Hx. }
split; [reflexivity|]. exists regsL, memL, matL. split; [reflexivity|]. split.
-
unfold AFfb.stL. splits; try assumption.
+ clear - hQ1. unfold zone3 in hQ1. lia.
+ clear - hQAL. apply Z.mod_divide in hQAL as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 512). lia.
+ rewrite L1. unfold lim, AFg8.nA. lia.
+ lia.
+ clear - D1 M1. numconst. lia.
+ intros j h Hj. destruct (L5 j h Hj) as (rj & Hrj & ->).
destruct (AFfc.slot_val B TB ly X k cbp W regs mem md r i PRE Hi j rj Hrj) as [SV SP].
destruct (AFfc.slot_geom B ly X k cbp W regs mem md r o sm PRE Hb Hsm j rj Hrj) as (y & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof (nth_error_lt _ _ _ Hrj) as JL.
assert (OUT : forall a, Q + 8 * Z.of_nat j <= a < Q + 8 * Z.of_nat j + 8 -> ~ WINA a /\ 0 <= a < 2 ^ 64).
{ intros a Ha. unfold WINA. unfold AFg8.nA in A4. clear - Ha hQ1 hQ2 hCE S1 JL A4. numconst. lia. }
splits.
* apply (val_mem_frame (w_H W) mem memL); [|exact SV]. intros kk Hkk. apply MQA. destruct (OUT (Q + 8 * Z.of_nat j + Z.of_nat kk) ltac:(lia)) as [O1 O2].
rewrite unsigned_lit_small by exact O2. exact O1.
* intros a Ha. destruct (OUT a Ha) as [O1 O2]. apply (apresent_same (w_H W) mem); [apply MQA; rewrite unsigned_lit_small by exact O2; exact O1 | exact (SP a Ha)].
* clear - G1. unfold zone3 in G1. lia.
* lia.
* exact G3.
-
unfold PREX. cbv zeta in VALS. fold sp0 in PRS, VALS |- *. unfold v.
destruct VALS as (V1 & V8 & V9 & V18 & V19 & V20 & V56 & V10 & V72 & V80 & VM).
unfold w64 in C10. pose proof CBP as (_ & _ & _ & _ & CR). rewrite C10 in V10. rewrite unsigned_lit_small in V10 by exact CR.
splits; first [assumption | exact V1 | exact V8 | exact V9 | exact V18 | exact V19 | exact V20 | exact V56 | exact V10 | exact V72 | exact V80 | exact VM].
Qed.
Lemma HP : 4096 <= hdr < ASAN_CEIL /\ hdr mod 16 = 0.
Proof.
pose proof (AFfc.hdr_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (D1 & D2 & D3 & D4 & _).
pose proof (AFfc.GEOM B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (M1 & M2 & M3 & M4 & _). split; [clear - D1 D2 D3 M1 M2; unfold zone3 in M1; lia | exact D4].
Qed.
Lemma HLIM : lim <= ASAN_CEIL /\ lim mod 8 = 0.
Proof.
pose proof (AFfc.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof (AFfc.ARRF B ly X k cbp W regs mem md r i PRE Hi) as (_ & _ & _ & A4 & _). unfold lim. split; [clear - hQ2 A4; numconst; lia|].
apply Z.mod_divide in hQAL as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q * 512 + nA). lia.
Qed.
Theorem to_XG : forall mat, SRr tfibsegs W (mkCfg (mkst regs (w64 A_RChunk) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) ATX.
Proof.
intros mat. pose proof (AFfc.FH_A B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as FHA.
eapply SRr_bind; [exact (AFf5.segGA W ly regs mem md hdr nA Q mat FHA)|].
intros W1 c1 _ HL0. destruct (L0_STL W1 c1 HL0) as (-> & regsL & memL & matL & -> & STL & PX).
pose proof hs_facts as (L1 & L2 & _).
eapply SRr_mono; [exact (AFfb.gloop W ly md hdr lim LO IMG HP HLIM hs Q 0 regsL memL matL L2 STL)|].
intros W2 c2 _ HX. destruct HX as (-> & regsX & memX & matX & -> & SR & A12 & A13 & MQ).
split; [reflexivity|]. exists regsX, memX, matX. split; [reflexivity|].
assert (EM : memX = memL) by (apply functional_extensionality; exact MQ). rewrite EM.
exists regsL. split; [exact PX|]. split; [exact SR|]. rewrite A13, scan_is_MAP. reflexivity.
Qed.
End c.
End b.
