(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1df.v (a working branch 84ee52cd012, file sha256 5227e7dd65a6) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 4 image addresses moved by code-verified function pairs (4 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: cgif_file's released Drain walk (AFet.v: tfib_drain_arm, with FIN_a, EPI) restated to
   the drain field of DGif0.DIface (DMspec.tfib_drain_spec_cf at ARX_cgif / aowned / drain_body / qloose): the post is
   DMspec.acall_post_x, whose raw frame clause comes from the walk's raw MEQ frames (AFgj.at_RETD, AFer.ATDR) and the
   raw frame of DoRecycle (DGif1dc.tfib_dorecycle_ok_x), and DoRecycle runs with the recycle callees in DIface's types. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFew AFff AFeu AFey AFgj AFgg AFgh AFgl AFh0 AFgt AFh8 AFev AFer AB13 AFet.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif1da DGif1dc.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis RCH : rch_cgif B.
Hypothesis CDH : cdh_cgif B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : drain_pre B ly X W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation GLv := (AFgj.GLv ly gq).
Local Notation TFv := (AFgj.TFv ly tq).
Local Notation TLv := (AFgj.TLv ly tq).
Local Notation M := (AFev.M B ly X W regs mem md PRE).
Local Notation HSP := (AFev.HSP B ly X W regs mem md PRE).
Local Notation HI := (AFev.HI B ly X W regs mem md PRE).
Local Notation IMG := (AFev.IMG B ly X W regs mem md PRE).
Local Notation batch_facts := (AFev.batch_facts B ly X W regs mem md PRE).
Local Notation g_facts := (AFev.g_facts B ly X W regs mem md PRE).
Local Notation t_facts := (AFev.t_facts B ly X W regs mem md PRE).
Local Notation L := (AFer.L X).
Local Notation addr := (AFer.addr ly).
Local Notation firstaddr := (AFer.firstaddr ly).
Local Notation lastaddr := (AFer.lastaddr ly).
Local Notation zlen := AFer.zlen.
Local Notation sp1 := (AFer.sp1 regs).
Local Notation DW := (AFer.DW ly X regs).
Local Notation LST := (AFer.LST ly X W regs mem md).
Local Notation ATDR := (AFer.ATDR ly X W regs mem md).
Let WF : Wf (as_universe B) X := am_wf B ly X _ M.
Let LO : layout_ok ly := am_layout B ly X _ M.
Local Notation XT := (AFey.XT X).
Local Notation HTB := (AFev.HTB B ly X W regs mem md PRE).

(* The walk's windows lie in YFey's window D (AFet.FIN_a / AFet.DRPRE). *)
Lemma WIN_D : forall a, AFgj.WIN ly regs gq a -> AFey.D B ly X [] sp0 a.
Proof.
pose proof (AFev.AQ B TB) as EAQ.
intros a Hw. unfold AFey.D, AFey.DT, AFey.DQ, AFey.DL, AFey.DS.
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in Hw. fold sp0 in Hw. rewrite EAQ in Hw.
unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- do 4 right. clear - Hw. unfold DSTACK. lia.
- right; left. left. lia.
- right; left. right. lia.
- left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFey.GLv, AFey.addr. unfold AFgj.GLv in Hw. destruct (rev G); [exact Hw | exact Hw].
Qed.
Lemma DW_D : forall P a, DW P a -> AFey.D B ly X P sp0 a.
Proof.
pose proof (AFev.AQ B TB) as EAQ.
intros P a Hw. unfold AFey.D, AFey.DT, AFey.DQ, AFey.DL, AFey.DP, AFey.DS.
unfold AFer.DW, AFgj.WINF in Hw. fold sp0 in Hw. rewrite EAQ in Hw. unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b & Hb & Hw)]]].
- do 4 right. clear - Hw. unfold DSTACK, LFRAME in *. lia.
- right; left. left. lia.
- right; left. right. lia.
- left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFey.GLv, AFey.addr. unfold AFgj.GLv in Hw. destruct (rev G); [exact Hw | exact Hw].
- right; right; right; left. exists b. split; [exact Hb|]. unfold AFey.addr. unfold AFer.addr in Hw. exact Hw.
Qed.

(* Drain's return without recycling: AFet.FIN_a, and the raw frame from at_RETD's MEQ. *)
Lemma FIN_x : forall W' c', AFgj.at_RETD W ly regs mem md gq tq W' c' ->
drain_leaf_raw_cf B (ARX_cgif B) (aowned B) TFIB_INST ly X W regs mem md (tt, XT) W' c'.
Proof.
intros W' c' HR. pose proof (AFet.FIN_a B TB ly X W regs mem md PRE W' c' HR) as DL.
destruct HR as (-> & regs' & mem' & mat & -> & R2 & CS & MQ & _).
destruct DL as (regs'' & mem'' & md'' & EQ & (AR' & LLE & WLE & CSV & SIO & FR & PRS)).
assert (EM : mem'' = mem') by (unfold cfg_at in EQ; injection EQ; intros; congruence).
exists regs'', mem'', md''. split; [exact EQ|].
split.
{ split; [split; [reflexivity | exact AR']|]. split; [exact LLE|]. split; [exact WLE|]. split; [exact CSV|]. split; [exact SIO|].
  split; [exact FR | exact PRS]. }
intros x NO NO' NS _. rewrite EM. apply (MQ x). intros HW. apply WIN_D in HW.
destruct (AFey.D_owned B ly X _ M [] L eq_refl sp0 HSP IMG (bv_unsigned x) (proj1 (u64_range x)) HW) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O].
Qed.
(* EPI_x with the epilogue's memory exported: the epilogue (AFh8.segX) leaves DoRecycle's return memory unchanged. *)
Lemma EPI_m : forall P R regs2 mem2 mat r W6 c6,
L = P ++ R ->
getr regs2 2 = w64 sp1 -> getr regs2 1 = w64 0x33e1c -> (forall r5 : bv 5, In r5 AFer.SREGS -> getr regs2 r5 = getr regs r5) ->
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) ->
(let m := mrestrict H0 mem2 in
val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> aview tfibsegs H0 mem2 a = rd0 a) ->
(forall x : word, ~ DW P (bv_unsigned x) -> mem2 x = mem x) ->
AR tfibsegs B ly (AFey.S' X P R) W mem2 (with_vm_backing (m_vm_lazy md) mat md) ->
dr_leaf_x B ly (AFey.S' X P R) W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) r W6 c6 ->
SRr tfibsegs W6 c6 (fun W7 c7 => drain_leaf_raw_cf B (ARX_cgif B) (aowned B) TFIB_INST ly X W regs mem md r W7 c7 /\
  ms_mem (cfg_ms c7) = ms_mem (cfg_ms c6)).
Proof.
intros P R regs2 mem2 mat [ru X3] W6 c6 HL R2 R1 CS PRS2 SLOTS AG2 MQ2 AR2 HDL. cbv zeta in SLOTS. destruct SLOTS as (Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp1 : 0 <= sp1 < 2 ^ 64) by (unfold AFer.sp1, LFRAME; fold sp0; clear - Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia).
assert (SP1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; rewrite unsigned_lit_small by exact Usp1; reflexivity).
destruct HDL as (regs3 & mem3 & md3 & -> & ([_ AR3] & LLE & WLE & CS3 & SIO & FR3 & PRS3) & RAW3 & PRE3). cbn [fst snd] in *.
unfold acall_raw_x in RAW3.
unfold spZ, raZ, ascratch in FR3, RAW3, PRS3, PRE3. rewrite R2, SP1 in FR3, RAW3, PRS3, PRE3. unfold spZ in FR3, RAW3. rewrite R2, SP1 in FR3, RAW3.
assert (NOWN : forall a, sp0 - DSTACK <= a < sp0 -> ~ aowned B ly (AFey.S' X P R) a /\ ~ aowned B ly X3 a).
{ intros a Ha. split.
- apply (AR_stack_law_ok tfibsegs B ly _ W mem2 _ a AR2). clear - Ha Hlo Hhi. unfold DSTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X3 W6 mem3 md3 a AR3). clear - Ha Hlo Hhi. unfold DSTACK in *. lia. }
assert (AGS : forall a, sp0 - DSTACK <= a < sp0 -> ~ (sp1 - DRSTACK_X <= a < sp1 + 32) -> aview tfibsegs (w_H W6) mem3 a = aview tfibsegs H0 mem2 a).
{ intros a Ha Hn. destruct (NOWN a Ha) as [N1 N2]. apply FR3; [clear - Ha Usp hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; lia | exact N1 | exact N2 | | clear - Hn; unfold DRSTACK_X in *; lia].
intros [Hs|Hs]; [clear - Hs Hn; unfold DRSTACK_X in *; lia|]. rewrite (ts_errno _ TB) in Hs. clear - Hs Ha hS1 HSP'. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, DSTACK, kHighMemBeg in *. lia. }
assert (PRS6 : forall a, sp0 - DSTACK <= a < sp0 -> apresent (w_H W6) mem3 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp1 - DRSTACK_X)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp1) as [L2|L2]; [apply PRS3; lia | destruct (Z_lt_le_dec a (sp1 + 32)) as [L3|L3]; [apply PRE3; lia|]]].
all: pose proof (PRS2 a Ha) as P0; apply apresent_mbyte in P0 as [b Hb];
assert (A : aview tfibsegs H0 mem2 a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- (AGS a Ha ltac:(lia)) in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W6) mem3 a b' ltac:(clear - Ha Usp hS1 HSP'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, TFIB_IMG_END in *; lia) Hb'). }
set (vra := bv_unsigned (getr regs 1)). set (vs0 := bv_unsigned (getr regs 8)). set (vs1 := bv_unsigned (getr regs 9)).
set (vs2 := bv_unsigned (getr regs 18)). set (vs3 := bv_unsigned (getr regs 19)). set (vs4 := bv_unsigned (getr regs 20)).
assert (CS3' : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs3 r = getr regs2 r) by (intros r5 z Hz <-; exact (CS3 z Hz)).
assert (Q2 : getr regs3 2 = w64 sp1) by (rewrite (CS3' 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact R2).
assert (Q4 : getr regs3 4 = w64 TFIB_TP).
{ rewrite (CS3' 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)), (CS 4%bv ltac:(cbn; tauto)), Htp, (ts_tp _ TB). reflexivity. }
assert (XF : forall a (n : nat) v, sp1 + 32 <= a -> a + Z.of_nat n <= sp0 -> val_mem tfibsegs (mrestrict H0 mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W6) mem3) a n v).
{ intros a n v H1 H2 Hv. eapply val_mem_aview_xfer; [|exact Hv]. intros k Hk. apply AGS; unfold AFer.sp1, LFRAME, DRSTACK_X in *; fold sp0 in H1 |- *; clear - H1 H2 Hk HSP' hS1; unfold DSTACK in *; lia. }
assert (FHX : AFgt.free_hyps W6 regs3 mem3 vra vs0 vs1 vs2 vs3 vs4).
{ constructor.
- exact Q4.
- subst vra. unfold w64. rewrite Z_to_bv_bv_unsigned. exact Hra.
- rewrite Q2, SP1. unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. lia.
- rewrite Q2, SP1. replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia). rewrite Z_mod_plus_full. exact Hal.
- subst vra vs0 vs1 vs2 vs3 vs4. splits; apply u64_range.
-
rewrite restrict_mkst_fx. unfold AFgt.SS0, AFgt.SR0, sr_set. cbn [bv_eqb]. unfold AFgt.E0, w64. apply (entry_st_ok_full tfibsegs).
+ apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Q4].
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. fold (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). unfold AFgt.REG0, AFgt.R_STK. apply Forall_cons; [|apply Forall_nil].
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (AFgt.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2, SP1. unfold LFRAME.
split; [clear - Usp1; lia|]. split; [unfold AFer.sp1, LFRAME; fold sp0; clear - HSP' hS2; unfold kHighMemEnd in *; lia|]. split; [intros o Ho; lia|].
assert (CA : forall a k0 x, ew (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W6) mem3) (sp1 + a) (N.to_nat 8) x ->
YP09.chunk_ok tfibsegs (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) (mrestrict (w_H W6) mem3) sp1 (YP09.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros a k0 x Hk0 Hr Hm. eapply chunk_ok_val; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr | cbn; lia | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (CA 72 32%nat vra); [reflexivity | subst vra; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs72]].
* apply (CA 64 33%nat vs0); [reflexivity | subst vs0; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs64]].
* apply (CA 56 34%nat vs1); [reflexivity | subst vs1; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs56]].
* apply (CA 48 35%nat vs2); [reflexivity | subst vs2; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs48]].
* apply (CA 40 36%nat vs3); [reflexivity | subst vs3; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs40]].
* apply (CA 32 37%nat vs4); [reflexivity | subst vs4; apply u64_range | apply XF; [lia | unfold AFer.sp1, LFRAME; fold sp0; cbn; lia | exact Cs32]].
+   cbn [pairwise_disjoint all_disjoint AFgt.REG0]. split; exact I.
+ fold (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). split; [|split; exact I].
assert (AF : forall k0 Xv lo hi al, ew (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (AFgt.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (SAL : sp1 mod 16 = 0) by (replace sp1 with (sp0 + (-5) * 16) by (unfold AFer.sp1, LFRAME; fold sp0; lia); rewrite Z_mod_plus_full; exact Hal).
cbn [AFgt.FFX f_atoms atoms_ok].
split. { apply (AF 2%nat sp1); [rewrite (AFgt.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2; reflexivity | exact Usp1 | | change (2 ^ 4) with 16; exact SAL | lia].
unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. lia. }
split. { apply (AF 32%nat vra); [reflexivity | subst vra; apply u64_range | pose proof (u64_range (getr regs 1)); subst vra; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 33%nat vs0); [reflexivity | subst vs0; apply u64_range | pose proof (u64_range (getr regs 8)); subst vs0; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 34%nat vs1); [reflexivity | subst vs1; apply u64_range | pose proof (u64_range (getr regs 9)); subst vs1; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 35%nat vs2); [reflexivity | subst vs2; apply u64_range | pose proof (u64_range (getr regs 18)); subst vs2; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 36%nat vs3); [reflexivity | subst vs3; apply u64_range | pose proof (u64_range (getr regs 19)); subst vs3; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (AF 37%nat vs4); [reflexivity | subst vs4; apply u64_range | pose proof (u64_range (getr regs 20)); subst vs4; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. } }
unfold cfg_at, raZ. rewrite <- (wvb_self md3) at 1. rewrite R1. unfold w64 at 2. rewrite (unsigned_lit_small 0x33e1c) by (clear; lia).
eapply SRr_mono; [exact (AFh8.segX W6 regs3 mem3 md3 vra vs0 vs1 vs2 vs3 vs4 (m_vm_materialized md3) FHX)|].
intros W7 c7 _ (-> & regs4 & mat4 & -> & T2 & T1 & T8 & T9 & T18 & T19 & T20 & TS).
split; [|reflexivity].
rewrite Q2, SP1 in T2. unfold LFRAME in T2.
exists regs4, mem3, (with_vm_backing (m_vm_lazy md3) mat4 md3). split; [subst vra; reflexivity|].
assert (CSx : forall z (r5 : bv 5), Z_to_bv 5 z = r5 -> getr regs4 r5 = getr regs r5 -> getr regs4 (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)) by (intros z r5 <- E; exact E).
assert (VIA3 : forall (r5 : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r5 -> In r5 AFgt.SREGS -> In r5 AFer.SREGS -> getr regs4 r5 = getr regs r5).
{ intros r5 z Hz Ez I1 I2. rewrite (TS r5 I1), (CS3' r5 z Hz Ez). apply CS. exact I2. }
split; [split; [split; [reflexivity|] | split; [apply layout_le_refl | split; [exact WLE | split; [|split; [|split]]]]] | ].
- apply (AR_model_same B ly X3 W6 mem3 md3); [exact AR3 | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
- intros r Hr. pose proof Hr as Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr'.
repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; subst r.
+ apply (CSx _ 2%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T2. unfold AFer.sp1, LFRAME. fold sp0. replace (sp0 - 80 + 80) with sp0 by lia. unfold sp0, w64. apply Z_to_bv_bv_unsigned.
+ apply (VIA3 3%bv 3 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 4%bv 4 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (CSx _ 8%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T8. subst vs0. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 9%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T9. subst vs1. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 18%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T18. subst vs2. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 19%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T19. subst vs3. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (CSx _ 20%bv); [apply bv_eq; vm_compute; reflexivity|]. rewrite T20. subst vs4. unfold w64. apply Z_to_bv_bv_unsigned.
+ apply (VIA3 21%bv 21 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 22%bv 22 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 23%bv 23 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 24%bv 24 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 25%bv 25 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 26%bv 26 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
+ apply (VIA3 27%bv 27 Hr); [apply bv_eq; vm_compute; reflexivity | cbn; tauto | cbn; tauto].
- eapply same_io_trans; [apply same_io_with_vm_backing|]. eapply same_io_trans; [exact SIO | apply same_io_with_vm_backing].
-
intros a Ha NO NO3 NS NF. unfold ascratch, spZ in NS. fold sp0 in NS.
assert (NOS : ~ aowned B ly (AFey.S' X P R) a).
{ intros O. apply NO. exact (aowned_same_cf B ly X _ a (AFey.S'_chunks X P R) (AFey.S'_fs X P R) O). }
transitivity (aview tfibsegs H0 mem2 a).
+ apply FR3; [exact Ha | exact NOS | exact NO3 | | intros HE; apply NS; left; unfold AFer.sp1, LFRAME in HE; fold sp0 in HE; clear - HE; try unfold DSTACK; try unfold YFeuC.DSTACK; lia].
intros [Hs|Hs]; apply NS; [left; unfold AFer.sp1, LFRAME, DRSTACK_X in Hs; fold sp0 in Hs; clear - Hs; try unfold DSTACK; try unfold YFeuC.DSTACK; lia | right; exact Hs].
+ apply AG2; [exact Ha|]. intros HD.
destruct (AFey.D_owned B ly X _ M P R HL sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; left; exact O].
- intros a Ha. apply PRS6. unfold spZ in Ha. exact Ha.
-
intros x NO NO3 NS NF. unfold ascratch, spZ in NS. fold sp0 in NS.
assert (NOS : ~ aowned B ly (AFey.S' X P R) (bv_unsigned x)).
{ intros O. apply NO. exact (aowned_same_cf B ly X _ _ (AFey.S'_chunks X P R) (AFey.S'_fs X P R) O). }
transitivity (mem2 x).
+ apply RAW3; [exact NOS | exact NO3 | | intros HE; apply NS; left; unfold AFer.sp1, LFRAME in HE; fold sp0 in HE; clear - HE; try unfold DSTACK; try unfold YFeuC.DSTACK; lia].
intros [Hs|Hs]; apply NS; [left; unfold AFer.sp1, LFRAME, DRSTACK_X in Hs; fold sp0 in Hs; clear - Hs; try unfold DSTACK; try unfold YFeuC.DSTACK; lia | right; exact Hs].
+ apply MQ2. intros HD. apply DW_D in HD.
destruct (AFey.D_owned B ly X _ M P R HL sp0 HSP' IMG (bv_unsigned x) (proj1 (u64_range x)) HD) as [O|O]; [exact (NO O) | apply NS; left; exact O].
Qed.
Lemma EPI_x : forall P R regs2 mem2 mat r W6 c6,
L = P ++ R ->
getr regs2 2 = w64 sp1 -> getr regs2 1 = w64 0x33e1c -> (forall r5 : bv 5, In r5 AFer.SREGS -> getr regs2 r5 = getr regs r5) ->
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) ->
(let m := mrestrict H0 mem2 in
val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> aview tfibsegs H0 mem2 a = rd0 a) ->
(forall x : word, ~ DW P (bv_unsigned x) -> mem2 x = mem x) ->
AR tfibsegs B ly (AFey.S' X P R) W mem2 (with_vm_backing (m_vm_lazy md) mat md) ->
dr_leaf_x B ly (AFey.S' X P R) W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) r W6 c6 ->
SRr tfibsegs W6 c6 (drain_leaf_raw_cf B (ARX_cgif B) (aowned B) TFIB_INST ly X W regs mem md r).
Proof.
intros P R regs2 mem2 mat r W6 c6 HL R2 R1 CS PRS2 SLOTS AG2 MQ2 AR2 HDL.
eapply SRr_mono; [exact (EPI_m P R regs2 mem2 mat r W6 c6 HL R2 R1 CS PRS2 SLOTS AG2 MQ2 AR2 HDL)|]. intros W7 c7 _ [HD _]. exact HD.
Qed.
Lemma drain_body_unfold :
drain_body X X = (if qc_bytes gq + qc_bytes tq <=? kQuarantineMax then ret tt else recycle_body (transfer_g X)) XT.
Proof. unfold drain_body, bind, put. cbn [ibind]. reflexivity. Qed.
(* drain_arm_x's composition over any leaf [LEAF], from its three parts: the return without recycling (FIN_x's
   premise), DoRecycle's contract with any leaf [DRL], and the epilogue after DoRecycle (EPI_x's premises). *)
Lemma drain_arm_g : forall (LEAF : unit * astate -> world tfibsegs -> config -> Prop)
(DRL : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model ->
  unit * astate -> world tfibsegs -> config -> Prop),
(forall W' c', AFgj.at_RETD W ly regs mem md gq tq W' c' -> LEAF (tt, XT) W' c') ->
(forall ly' X' P W' regs' mem' md', dr_pre_x B ly' X' P W' regs' mem' md' ->
  amreal tfibsegs (do_recycle 100000%nat P X') W' (cfg_at tfibsegs A_DoRecycle regs' mem' md') (DRL ly' X' W' regs' mem' md')) ->
(forall P R regs2 mem2 mat r W6 c6,
  L = P ++ R ->
  getr regs2 2 = w64 sp1 -> getr regs2 1 = w64 0x33e1c -> (forall r5 : bv 5, In r5 AFer.SREGS -> getr regs2 r5 = getr regs r5) ->
  (forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) ->
  (let m := mrestrict H0 mem2 in
  val_mem tfibsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfibsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem tfibsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfibsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfibsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AFey.D B ly X P sp0 a -> aview tfibsegs H0 mem2 a = rd0 a) ->
  (forall x : word, ~ DW P (bv_unsigned x) -> mem2 x = mem x) ->
  AR tfibsegs B ly (AFey.S' X P R) W mem2 (with_vm_backing (m_vm_lazy md) mat md) ->
  DRL ly (AFey.S' X P R) W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) r W6 c6 ->
  SRr tfibsegs W6 c6 (LEAF r)) ->
amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) LEAF.
Proof.
intros LEAF DRL HFIN HDR HEPI.
pose proof (AFev.FH_ok B TB ly X W regs mem md PRE) as FH.
pose proof (AFer.sum_L B ly X W regs mem md PRE) as SL. pose proof (AFer.len_L B ly X W regs mem md PRE) as LL.
assert (WALK : (kQuarantineMax < qc_bytes gq + qc_bytes tq -> 2 * (kBatchBytes * Z.of_nat (length L)) <= qc_bytes gq + qc_bytes tq) ->
SRr tfibsegs W (cfg_at tfibsegs A_Drain regs mem md) (AFgj.postD W ly regs mem md gq tq)).
{ intros HM. unfold cfg_at, A_Drain. rewrite <- (wvb_self md) at 1.
assert (HM' : kQuarantineMax < AFgj.LBv gq tq -> 2 * (kBatchBytes * AFgj.LSZv gq tq) <= AFgj.LBv gq tq).
{ unfold AFgj.LBv, AFgj.GBv, AFgj.TBv, AFgj.LSZv, AFgj.GSZv, AFgj.TSZv. intros H1.
unfold AFer.L in HM. rewrite length_app, Nat2Z.inj_add in HM. exact (HM H1). }
destruct G as [|g0 G'] eqn:EG.
- apply (AFgg.segDE W ly regs mem md gq tq (m_vm_materialized md) FH); [exact EG | exact HM'].
- apply (AFgh.segDN W ly regs mem md gq tq (m_vm_materialized md) FH); [rewrite EG; discriminate | exact HM']. }
rewrite drain_body_unfold. unfold AFgj.postD, AFgj.LBv, AFgj.GBv, AFgj.TBv in WALK.
destruct (Z.leb_spec (qc_bytes gq + qc_bytes tq) kQuarantineMax) as [LE|GT].
-
cbn [amreal ret]. eapply SRr_mono; [exact (WALK ltac:(intros; lia))|]. intros W' c' _ HR. exact (HFIN W' c' HR).
-
unfold recycle_body, mcheck. cbn [qc_list qc_bytes transfer_g].
destruct (Z.leb_spec (2 * (kBatchBytes * Z.of_nat (length (G ++ Tq)))) (qc_bytes gq + qc_bytes tq)) as [MC|MC].
2:{   unfold bind, fail. cbn [ibind amreal]. exact I. }
unfold bind at 1. unfold ret. cbn [ibind].
destruct (pop_batches 100000 (transfer_g X) []) as [g' P] eqn:EP.
pose proof (pop_batches_spec _ _ _ _ _ EP) as (P0 & EP0 & EL & EB). cbn [rev app] in EP0. subst P0. cbn [transfer_g qc_list qc_bytes] in EL, EB.
assert (LEN : (length (qc_list (transfer_g X)) < 100000)%nat).
{ cbn [transfer_g qc_list]. unfold AFer.zlen, AFer.L in LL. apply Nat2Z.inj_lt. rewrite of_nat_100000. lia. }
pose proof (pop_batches_stop _ _ _ _ _ EP LEN) as STOP.
destruct g' as [R s]. cbn [qc_list qc_bytes] in EL, EB, STOP.
assert (HL : L = P ++ R) by exact EL.
assert (SR : sum_bytes R <= kQuarantineMax).
{ rewrite HL, sum_bytes_app in SL. destruct STOP as [S1|S1]; [unfold kQuarantineMin, kQuarantineMax in *; lia | subst R; cbn; unfold kQuarantineMax; lia]. }
unfold bind, modify. cbn [ibind].
change (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (AFey.S' X P R) || (replace (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (AFey.S' X P R) by (unfold AFey.S'; cbn [st_qglobal qc_bytes AFey.XT set_qglobal]; rewrite EB; reflexivity)).
apply amreal_after_SRr.
eapply SRr_bind; [exact (WALK ltac:(intros _; unfold AFer.L; exact MC))|]. intros W1 c1 _ H1.
pose proof (AFet.L0_LST B TB ly X W regs mem md PRE W1 c1 H1) as H2.
eapply SRr_bind.
{ apply (AFer.LOOP B TB ly X W regs mem md PRE L [] 100000%nat W1 c1 H2 eq_refl); [rewrite SL; unfold kQuarantineMin, kQuarantineMax in *; lia | exact LEN]. }
intros W2 c2 _ H3. cbn beta zeta in H3. cbn [rev] in H3. rewrite SL in H3. change (AFer.L X) with (G ++ Tq) in H3. unfold transfer_g in EP. rewrite EP in H3. cbn [fst snd qc_list] in H3.
destruct (AFet.DRPRE B TB ly X W regs mem md PRE P R W2 c2 H3 HL SR) as (regs2 & mem2 & mat & -> & -> & R2 & R1 & R13 & CS & MQ & PRS & SLOTS & AG & DPRE).
assert (SPR2 : spZ regs2 = sp1).
{ pose proof HSP as HSP'. pose proof HI as (_ & _ & _ & _ & hS1 & hS2 & _). unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small.
  unfold AFer.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold kHighMemBeg, kHighMemEnd, DSTACK in *. lia. }
assert (HST2 : ly_stk_lo ly + DRSTACK_X <= spZ regs2) by (rewrite SPR2; unfold AFer.sp1, LFRAME; fold sp0; pose proof HSP as HSP'; clear - HSP'; unfold DSTACK, DRSTACK_X in *; lia).
assert (HPR2 : forall a, spZ regs2 - DRSTACK_X <= a < spZ regs2 -> apresent (w_H W) mem2 a).
{ intros a Ha. rewrite SPR2 in Ha. apply PRS. unfold AFer.sp1, LFRAME, DRSTACK_X in Ha. fold sp0 in Ha. clear - Ha. unfold DSTACK. lia. }
apply SRr_ret. eapply amreal_then_SRr; [exact (HDR ly _ P W regs2 mem2 _ (conj DPRE (conj HST2 HPR2)))|].
intros r W6 c6 HDL. exact (HEPI P R regs2 mem2 mat r W6 c6 HL R2 R1 CS PRS SLOTS AG MQ (proj1 DPRE) HDL).
Qed.
Theorem drain_arm_x : amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) (drain_leaf_raw_cf B (ARX_cgif B) (aowned B) TFIB_INST ly X W regs mem md).
Proof.
exact (drain_arm_g (drain_leaf_raw_cf B (ARX_cgif B) (aowned B) TFIB_INST ly X W regs mem md) (dr_leaf_x B) FIN_x
  (tfib_dorecycle_ok_x B TB RCH CDH) EPI_x).
Qed.
End f.
(* The drain field of cgif_file's DIface instance, from the recycle callees' fields. *)
Theorem tfib_drain_ok_cf : forall B, TfibSyms B -> rch_cgif B -> cdh_cgif B -> forall L24,
drain_spec_raw_cf B (ARX_cgif B) (aowned B) drain_body L24 qloose.
Proof.
intros B TB RCH CDH L24 inst ly X W regs mem md PREcf.
destruct PREcf as ([-> HAR] & HTB & HQL & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
assert (PRE : drain_pre B ly X W regs mem md)
  by (refine (conj HAR (conj HTB (conj HQL (conj Hra (conj Hra4 (conj Hal (conj Hlo (conj Hhi (conj HPRES (conj Hgp (conj Htp (conj Ha0 (conj Ha1 Ha2)))))))))))))).
eapply drain_arm_x; eassumption.
Qed.
End d.
