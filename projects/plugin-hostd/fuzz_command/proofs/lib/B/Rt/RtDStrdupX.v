(* The contract of plugin-hostd/fuzz_command's strdup entry, composed: the three stretches of the entry's own
   code (RtDStrdupP1.v, RtDStrdupP2.v, RtDStrdupT.v) with the allocator's own step between the second and the
   third, and the leaf of RtAlloc.v's astrdup_realizes assembled from them. The proof of lib/A/Rt/RtDStrdupX.v on
   plugin-hostd/fuzz_command's ASan+UBSan image (fuzz_command.asan-ubsan), its addresses moved by the name-keyed A-to-B
   address map; the unwinder's call spec is discharged by lib/B/YFl4.v tfib_unwind_ok, the image-B twin of
   lib/A/AFl4.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d YK06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG07 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YFl4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtSRegion.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import
RtDefs RtString RtAlloc RtAPI RtDDefs RtSRegionDef RtDStrdupD RtDStrdupP1 RtDStrdupP2 RtDStrdupT
RtDStrdupG RtDStrdupW.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32 YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
(* __asan::asan_malloc 0x34574 with the trace the entry built: the named hypothesis this file still takes. The
   relocated malloc chain's refactor discharges it. *)
Hypothesis MALLOC_IN : amalloc_inner_realizes tfibsegs B PC_asan_malloc.

Lemma sd_trace_len1 : forall ly sp0 ra0 nfp0 ch, (1 <= length (sd_trace ly sp0 ra0 nfp0 ch))%nat.
Proof.
intros ly sp0 ra0 nfp0 ch. unfold sd_trace.
destruct (sp0 + 16 <? ly_top ly); [unfold unwind_of_chain, kUnwindMax; cbn [firstn length]; lia | cbn [length]; lia].
Qed.

Theorem cmd_strdup : astrdup_realizes tfibsegs B PC_strdup PC_STRDUP_RA0.
Proof.
intros ly S W regs mem md x s ch HPRE G10 Hx HSTR HRD HKEPT HROM Hmax Hlive Htr.
pose proof HPRE as (HAR & HREG & Hra & Hal16 & Hslo & Hbot & Hhi & HpresA & Hgp & Htp & Hchain & Hqm).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as Lceil.
pose proof HRD as (Hx0 & Hxn & Hn32 & Hsrcw & Ham & Hraok & Hhull).
set (sp0 := spZ regs) in *.
set (len := astr_len s) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47)
by (unfold ASTACK in Hslo; unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi; lia).
assert (Hal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16. rewrite Hal16 in D16. rewrite D16 at 1.
replace (16 * (sp0 / 16) + 0) with (0 + (2 * (sp0 / 16)) * 8) by lia. rewrite Z_mod_plus_full. reflexivity. }
set (ra0 := raZ regs) in *. set (nfp0 := s0Z regs) in *.
assert (HTREQ : call_trace ly PC_STRDUP_RA0 regs ch = sd_trace ly sp0 ra0 nfp0 ch)
by (unfold call_trace, sd_trace, frame0_ok; reflexivity).
assert (HLEN : (length (sd_trace ly sp0 ra0 nfp0 ch) <= kUnwindMax)%nat)
by (rewrite <- HTREQ; apply call_trace_len).
eapply amreal_SRr_pre.
{ exact (sd_p1_srr B LAWS TB (RtSRegion.cmd_region_zero_stk B LAWS TB) ly S W regs mem md x len s
HAR Hra Hal16 Hslo Hhi HpresA Hgp Htp G10 Hx HSTR eq_refl HRD ltac:(unfold astr_len in *; lia) HROM). }
intros W1 c1 Hle1 (HW1 & regs1 & mem1 & md1 & Hc1 & HAR1 & SBM1 & R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23
& RK1 & HSAV & HFR1 & HPR1).
subst W1. rewrite Hc1. clear Hc1 c1.
pose proof HSAV as (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23).
assert (HPR1A : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a)
by (intros a Ha; apply HPR1; apply HpresA; exact Ha).
eapply amreal_SRr_pre.
{ apply (sd_p2_srr B LAWS TB YFl4.tfib_unwind_ok ly S W regs1 mem1 md1 sp0 x (len + 1) ra0 nfp0 ch HAR1 Hsp
ltac:(exact Hal16) ltac:(exact Hslo) Hbot Hhi HPR1A).
- apply (YF0x.val_mem_rdword (w_H W) mem1 (sp0 - 8) ra0); [unfold ra0, raZ; apply u64_range | exact V1].
- apply (YF0x.val_mem_rdword (w_H W) mem1 (sp0 - 16) nfp0); [unfold nfp0, s0Z; apply u64_range | exact V8].
- exact (proj1 Hchain).
- pose proof (proj2 Hchain) as HC. unfold frame0_ok in HC. fold sp0 in HC. fold nfp0 in HC.
destruct (sp0 + 16 <? ly_top ly) eqn:HF; [|exact HC].
destruct (bad_next sp0 (ly_top ly) nfp0) eqn:HB; [exact HC|].
destruct HC as [HC1 HC2]. split; [exact HC1|].
unfold bad_next in HB. apply orb_false_elim in HB as [HB1 _]. apply orb_false_elim in HB1 as [_ HB12].
apply Z.leb_gt in HB12.
apply (fpchain_frame ch (rdword (aview tfibsegs (w_H W) mem)) (rdword (aview tfibsegs (w_H W) mem1))
sp0 nfp0 (ly_top ly)); [| lia | lia | exact HC2].
intros a Ha1 Ha2. apply rdword_frame. intros k Hk.
apply HFR1; unfold kHighMemEnd in Lhi; lia.
- exact R2.
- exact R8.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- exact R9.
- exact R18.
- unfold astr_len in *. lia.
- exact R22.
- exact R23.
- unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
intros W2 c2 Hle2 (HW2 & regs2 & mem2 & md2 & Hc2 & HAR2 & SBM2 & Q1 & Q2 & Q10 & Q11 & Q3 & Q4 & Q8 & Q9
& Q18 & QK2 & HTRACE & HFR2 & HPR2).
subst W2. rewrite Hc2. clear Hc2 c2.
assert (HSP2 : spZ regs2 = sp0 - 2144)
by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
rewrite HTREQ.
eapply amreal_then_SRr.
- eapply (amreal_and_tok (malloc (len + 1) (sd_trace ly sp0 ra0 nfp0 ch) S) W
(cfg_at tfibsegs PC_asan_malloc regs2 mem2 md2) _ (malloc_post (as_universe B) S (len + 1)) true).
+ apply (MALLOC_IN ly S W regs2 mem2 md2 (len + 1) (sp0 - 2144) (sd_trace ly sp0 ra0 nfp0 ch) HAR2 HREG).
* rewrite Q1. apply YE2y.ret_ok_lit; [lia | reflexivity].
* rewrite HSP2. replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
* rewrite HSP2. unfold MALLOC_ASAN_STK, ASTACK in *. lia.
* rewrite HSP2. lia.
* intros a Ha. rewrite HSP2 in Ha. apply HPR2. apply HPR1. apply HpresA.
unfold MALLOC_ASAN_STK, ASTACK in *. lia.
* rewrite Q3, R3. exact Hgp.
* rewrite Q4, R4. exact Htp.
* exact Hqm.
* exact Q10.
* exact Q11.
* rewrite HSP2. lia.
* replace (sp0 - 2144) with (sp0 + (-268) * 8) by lia. rewrite Z_mod_plus_full. exact Hal8.
* lia.
* exact HTRACE.
* apply sd_trace_len1.
* exact HLEN.
* unfold astr_len in *. lia.
* unfold astr_len in *. lia.
* rewrite <- HTREQ. exact Htr.
+ apply (amalloc_tok B ly S W mem2 md2 (len + 1) (sd_trace ly sp0 ra0 nfp0 ch) HAR2 HREG).
* unfold astr_len in *. lia.
* unfold astr_len in *. lia.
* rewrite <- HTREQ. apply tr_admit_call. exact Htr.
- intros r W3 c3 HPOST. destruct r as (p & S1).
destruct HPOST as ((ly1 & regs3 & mem3 & md3 & Hc3 & HCP & A10 & HQT) & bns & HMP).
rewrite Hc3. unfold raZ. rewrite Q1. unfold w64. rewrite unsigned_lit_small by lia.
pose proof HCP as (HAR3 & HLE & HWLE & HPRES3 & HIO3 & HVIEW3 & HPRESW3).
pose proof HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo1 & Hhi1 & _).
set (v := sptr_addr B ly1 p) in *.
(* the new block is a live block of the state the allocator returns *)
assert (HPN : p = PNull \/ (p <> PNull /\ blocks S1 = blocks S ++ [(p, len + 1)])).
{ pose proof HMP as HM. cbn in HM. destruct HM as (_ & _ & _ & _ & HB & _).
destruct p as [|o|r o|c q]; [left; reflexivity | right | right | right];
(split; [discriminate | exact (proj1 HB)]). }
assert (HPNZ : p <> PNull -> In (v, len + 1) (ablocks B ly1 S1)).
{ intros HNN. destruct HPN as [HE|[_ HB]]; [exfalso; exact (HNN HE)|].
unfold ablocks. rewrite HB, map_app. apply in_or_app. right. left. reflexivity. }
assert (HBLK : p <> PNull ->
(forall a, v <= a < v + req_size (len + 1) -> apresent (w_H W3) mem3 a /\ ~ aowned B ly1 S1 a) /\
in_app v (req_size (len + 1)) /\ v mod 16 = 0 /\ 4096 <= v /\ v + req_size (len + 1) <= alloc_ceiling /\
0 <= len + 1 < MALLOC_MAX)
by (intros HNN; exact (dup_blk_facts B LAWS ly1 S1 W3 mem3 md3 v (len + 1) HAR3 (HPNZ HNN))).
assert (HREQ : req_size (len + 1) = len + 1)
by (unfold req_size, astr_len in *; replace (len + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
(* the block list of the state the allocator returns *)
assert (HBL : p <> PNull -> ablocks B ly1 S1 = ablocks B ly S ++ [(v, len + 1)]).
{ intros HNN. destruct HPN as [HE|[_ HB]]; [exfalso; exact (HNN HE)|].
exact (ablocks_snoc B LAWS ly ly1 S S1 W mem md p (len + 1) HAR HLE HB). }
(* every byte of the source keeps its value across the whole walk *)
assert (HSRCV : forall a, x <= a < x + (len + 1) ->
aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha.
assert (Hband : ~ ascratch_stk ASTACK regs a) by (exact (proj2 (Hsrcw a Ha))).
unfold ascratch_stk, ASTACK in Hband. fold sp0 in Hband.
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Ham; lia).
pose proof (HKEPT a Ha) as HK.
assert (HOUT3 : ~ aowned B ly S a /\ ~ aowned B ly1 S1 a /\
~ (p <> PNull /\ v <= a < v + req_size (len + 1))).
{ destruct HPN as [HE|[HNN HB]].
- assert (HAB : ablocks B ly1 S1 = ablocks B ly S).
{ pose proof HMP as HM. cbn in HM. destruct HM as (_ & _ & _ & _ & HBl & _).
rewrite HE in HBl. unfold ablocks. rewrite HBl.
exact (proj1 (al_layout _ _ LAWS ly S W mem md ly1 HAR HLE)). }
destruct HK as (Herr & [[Himg Hown] | [Hstk | (b & m & Hbm & Hin)]]).
+ split; [intros HO; apply Hown; exact (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR Himg) HO)|].
split; [intros HO; apply Hown;
exact (proj1 (al_owned_image _ _ LAWS ly1 S1 W3 mem3 md3 a HAR3 Himg) HO)|].
intros [HC _]. exact (HC HE).
+ split; [exact (al_stack _ _ LAWS ly S W mem md a HAR Hstk)|].
split; [apply (al_stack _ _ LAWS ly1 S1 W3 mem3 md3 a HAR3); rewrite Hlo1, Hhi1; exact Hstk|].
intros [HC _]. exact (HC HE).
+ assert (Hin1 : In (b, m) (ablocks B ly1 S1)) by (rewrite HAB; exact Hbm).
destruct (dup_blk_facts B LAWS ly S W mem md b m HAR Hbm) as (HbyS & _).
destruct (dup_blk_facts B LAWS ly1 S1 W3 mem3 md3 b m HAR3 Hin1) as (HbyS1 & _).
split; [exact (proj2 (HbyS a Hin))|]. split; [exact (proj2 (HbyS1 a Hin))|].
intros [HC _]. exact (HC HE).
- destruct (dup_src_outside B LAWS ly S W mem md ly1 S1 W3 mem3 md3 v (len + 1) a HAR HAR3 HLE
(HBL HNN) HK) as (N1 & N2 & N3).
split; [exact N1|]. split; [exact N2|]. intros [_ HC]. exact (N3 HC). }
destruct HOUT3 as (N1 & N2 & N3).
rewrite (HVIEW3 a Ha64 N1 N2 ltac:(unfold ascratch; rewrite HSP2; intros [HC1|HC2];
[unfold MALLOC_ASAN_STK, ASTACK in *; lia | exact (proj1 HK HC2)]) N3).

rewrite (HFR2 a Ha64 ltac:(lia)). rewrite (HFR1 a Ha64 ltac:(lia)). reflexivity. }
(* the errno cell of this image is far below the stack *)
assert (HNERR : forall a, 2 ^ 43 <= a -> ~ aerrno_cell B a).
{ intros a Ha. unfold aerrno_cell. rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia. }
(* the block the allocator returns lies below the stack *)
assert (HVSTK : p <> PNull -> v + req_size (len + 1) <= sp0 - 2304).
{ intros HNN. destruct (HBLK HNN) as (_ & _ & _ & _ & Hce & _).
unfold ASAN_CEIL in Lceil. unfold ASTACK in Hslo. lia. }
assert (HVLO : p <> PNull -> v + req_size (len + 1) <= ly_stk_lo ly).
{ intros HNN. destruct (HBLK HNN) as (_ & _ & _ & _ & Hce & _).
unfold ASAN_CEIL in Lceil. unfold ASTACK in Hslo. lia. }
assert (HVB : p <> PNull -> 0 < v /\ v + (len + 1) <= 2 ^ 63).
{ intros HNN. destruct (HBLK HNN) as (_ & _ & _ & H4k & Hce & _).
pose proof alloc_ceiling_lt as HACL. rewrite HREQ in Hce. unfold astr_len in *. lia. }
(* the entry's own frame survives the allocator *)
assert (HV32 : forall a, sp0 - 2144 <= a < sp0 ->
aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W) mem2 a).
{ intros a Ha.
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold kHighMemEnd in *; lia).
assert (Hstk : ly_stk_lo ly <= a < ly_stk_hi ly) by (unfold ASTACK in Hslo; lia).
exact (HVIEW3 a Ha64 (al_stack _ _ LAWS ly S W mem md a HAR Hstk)
ltac:(apply (al_stack _ _ LAWS ly1 S1 W3 mem3 md3 a HAR3); rewrite Hlo1, Hhi1; exact Hstk)
ltac:(unfold ascratch; rewrite HSP2; intros [HC1|HC2];
[unfold MALLOC_ASAN_STK in *; lia | exact (HNERR a ltac:(lia) HC2)])
ltac:(intros [HNN HC]; cbn [fst snd] in HNN, HC; fold v in HC;
pose proof (HVSTK HNN) as HVS; lia)). }
(* the nine saved words survive the trace build and the allocator *)
assert (HKEEP3 : forall a, sp0 - 72 <= a < sp0 ->
aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W) mem1 a).
{ intros a Ha. rewrite (HV32 a ltac:(lia)).
exact (HFR2 a ltac:(unfold kHighMemEnd in *; lia) ltac:(lia)). }
(* the nine saved words, as the epilogue reads them *)
assert (HSAV3 : sd_saved W3 mem3 sp0 regs).
{ unfold sd_saved in HSAV |- *.
repeat split;
(apply (YE2y.val_mem_kept (w_H W) (w_H W3) mem1 mem3); [intros k Hk; apply HKEEP3; cbn [Z.of_nat] in Hk; lia|]);
[exact V1 | exact V8 | exact V9 | exact V18 | exact V19 | exact V20 | exact V21 | exact V22 | exact V23]. }
(* the two words of the memcpy pointer *)
assert (HG1 : val_mem tfibsegs (mrestrict (w_H W3) mem3) 0xa5f78 8 0xa7e08)
by (exact (tfib_const_lookup B TB ly1 S1 (w_H W3) mem3 0xa5f78 8 0xa7e08 (proj1 HAR3)
(YE2y.const_chk_sound ly1 0xa5f78 8%N 0xa7e08 ltac:(vm_compute; reflexivity)))).
assert (HG2 : val_mem tfibsegs (mrestrict (w_H W3) mem3) 0xa7e08 8 0x9e698)
by (exact (tfib_const_lookup B TB ly1 S1 (w_H W3) mem3 0xa7e08 8 0x9e698 (proj1 HAR3)
(YE2y.const_chk_sound ly1 0xa7e08 8%N 0x9e698 ltac:(vm_compute; reflexivity)))).
(* no byte of the source is a byte of the new block *)
assert (HNOBLK : p <> PNull -> forall a, x <= a < x + (len + 1) ->
~ (v <= a < v + req_size (len + 1))).
{ intros HNN a Ha. exact (proj2 (proj2 (dup_src_outside B LAWS ly S W mem md ly1 S1 W3 mem3 md3 v (len + 1) a
HAR HAR3 HLE (HBL HNN) (HKEPT a Ha)))). }
assert (HDISJ : p <> PNull -> v + (len + 1) <= x \/ x + (len + 1) <= v).
{ intros HNN. destruct (Z_le_gt_dec (v + (len + 1)) x) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (x + (len + 1)) v) as [H2|H2]; [right; exact H2|].
exfalso. apply (HNOBLK HNN (Z.max x v) ltac:(unfold astr_len in *; lia)).
rewrite HREQ. unfold astr_len in *. lia. }
(* the new block is writable *)
assert (HST : p <> PNull ->
store_ok tfibsegs (mrestrict (w_H W3) mem3) (Z_to_bv 64 v) (Z.to_nat (len + 1)) = true).
{ intros HNN. destruct (HBLK HNN) as (Hby & _ & _ & H4k & Hce & _).
rewrite HREQ in Hby, Hce. pose proof alloc_ceiling_lt as HACL.
apply (store_ok_of_all tfibsegs (Z.to_nat (len + 1)) (mrestrict (w_H W3) mem3) (Z_to_bv 64 v)).
- rewrite unsigned_lit_small by (unfold astr_len in *; lia).
rewrite Z2Nat.id by (unfold astr_len in *; lia). unfold astr_len in *; lia.
- intros z Hz. rewrite unsigned_lit_small in Hz by (unfold astr_len in *; lia).
rewrite Z2Nat.id in Hz by (unfold astr_len in *; lia).
pose proof (proj1 (Hby (bv_unsigned z) ltac:(lia))) as Hpz.
pose proof (YE2y.apresent_writable (w_H W3) mem3 (bv_unsigned z) Hpz) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
(* the source bytes, as musl memcpy reads them *)
assert (HOUTL : length (s ++ [Z_to_bv 8 0]) = Z.to_nat (len + 1))
by (rewrite length_app; cbn [length]; unfold astr_len in *; lia).
assert (HOUT : rdn tfibsegs (mrestrict (w_H W3) mem3) (Z_to_bv 64 x) (Z.to_nat (len + 1))
= Some (s ++ [Z_to_bv 8 0])).
{ pose proof HSTR as (HBY & _).
apply (proj2 (rdn_mbytes tfibsegs (mrestrict (w_H W3) mem3) (Z.to_nat (len + 1)) x (s ++ [Z_to_bv 8 0]))).
split; [exact HOUTL|].
intros i Hi.
assert (Hil : (i < length (s ++ [Z_to_bv 8 0]))%nat) by (rewrite HOUTL; exact Hi).
pose proof (HBY i Hil) as Hv.
rewrite <- (HSRCV (x + Z.of_nat i) ltac:(rewrite HOUTL in Hil; unfold astr_len in *; lia)) in Hv.
destruct (YE2y.aview_byte_ex (w_H W3) mem3 (x + Z.of_nat i) _ Hv) as (b & Hb & Hbe & _).
assert (Hbn : b = nth i (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) by (apply bv_eq; symmetry; exact Hbe).
rewrite Hb, Hbn. symmetry. apply nth_error_nth'. exact Hil. }
(* the window the tail asks for is present *)
assert (HPRESX : forall a, sp0 - 2304 <= a < sp0 -> apresent (w_H W3) mem3 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo|Hlo].
- apply HPRESW3. rewrite HSP2. unfold MALLOC_ASAN_STK. lia.
- apply (apresent_of_view (w_H W) (w_H W3) mem2 mem3 a).
+ apply YF0x.seg_rom_none_high. unfold YF0x.TFIB_IMG_END. unfold kHighMemEnd in *. lia.
+ exact (HV32 a ltac:(lia)).
+ apply HPR2. apply HPR1. apply HpresA. unfold ASTACK. lia. }
(* the registers the epilogue needs *)
assert (R3C : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r).
{ intros r Hr. pose proof (HPRES3 (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
assert (T2 : getr regs3 2 = w64 (sp0 - 2144))
by (rewrite (R3C 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)); exact Q2).
assert (T9 : getr regs3 9 = w64 x)
by (rewrite (R3C 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9; exact R9).
assert (T18 : getr regs3 18 = w64 (len + 1))
by (rewrite (R3C 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18; exact R18).
assert (HVNULL : p = PNull -> v = 0) by (intros HE; unfold v; rewrite HE; reflexivity).
assert (HVNN : v <> 0 -> p <> PNull) by (intros Hv0 HE; exact (Hv0 (HVNULL HE))).
assert (HV64 : 0 <= v < 2 ^ 64).
{ destruct HPN as [HE|[HNN _]]; [rewrite (HVNULL HE); lia|].
destruct (HBLK HNN) as (_ & _ & _ & H4k & Hce & _). pose proof alloc_ceiling_lt as HACL.
rewrite HREQ in Hce. unfold astr_len in *. lia. }
eapply SRr_mono.
+ apply (sd_tail_srr W3 regs3 mem3 md3 sp0 v x (len + 1) (s ++ [Z_to_bv 8 0])
(bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
(bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
(bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23))
Hsp Hal16 T2 T9 T18 A10 HV64 ltac:(unfold astr_len in *; lia) Hx0 Hxn);
[ exact (proj1 HSAV3) | exact (proj1 (proj2 HSAV3)) | exact (proj1 (proj2 (proj2 HSAV3)))
| exact (proj1 (proj2 (proj2 (proj2 HSAV3)))) | exact (proj1 (proj2 (proj2 (proj2 (proj2 HSAV3)))))
| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HSAV3))))))
| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HSAV3)))))))
| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HSAV3))))))))
| exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HSAV3))))))))
| apply u64_range | exact (ret_ok_mod2 _ Hra) | exact (proj1 Hchain)
| apply u64_range | apply u64_range | apply u64_range | apply u64_range
| apply u64_range | apply u64_range | apply u64_range | apply u64_range
| exact HPRESX | exact HG1 | exact HG2
| intros _; exact HOUTL | intros _; exact HOUT | intros Hv0; exact (HST (HVNN Hv0))
| intros Hv0; exact (HDISJ (HVNN Hv0))
| intros Hv0; exact (HVB (HVNN Hv0))
| intros Hv0; left; pose proof (HVLO (HVNN Hv0)) as HVS; rewrite HREQ in HVS; unfold ASTACK in Hslo; lia ].
+ cbv beta. intros W4 c4 Hle4 (HW4 & regs4 & md4 & Hc4 & SBM4 & U10 & U2 & U1 & U8 & U9 & U18 & U19 & U20
& U21 & U22 & U23 & U3 & U4 & UK).
subst W4. rewrite Hc4. clear Hc4 c4.
set (out := s ++ [Z_to_bv 8 0]) in *.
set (mem4 := if v =? 0 then mem3 else munrestrict (w_H W3) mem3 (wbytes (mrestrict (w_H W3) mem3) (Z_to_bv 64 v) out)).
assert (HOUTN : Z.of_nat (length out) = len + 1)
by (rewrite HOUTL; apply Z2Nat.id; unfold astr_len in *; lia).
(* the memory the entry returns: the copy where the block is, the allocator's memory elsewhere *)
assert (HM4out : forall a, 0 <= a < 2 ^ 64 -> ~ (p <> PNull /\ v <= a < v + req_size (len + 1)) ->
aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. unfold mem4. destruct (v =? 0) eqn:Ev; [reflexivity|].
apply Z.eqb_neq in Ev. pose proof (HVNN Ev) as HNN. destruct (HVB HNN) as (Hv0 & Hvn).
rewrite HREQ in Hn.
apply aview_wr_out; [lia | rewrite HOUTN; lia | exact Ha | rewrite HOUTN; intros Hin; exact (Hn (conj HNN Hin))]. }
assert (HM4in : p <> PNull -> abytes_at tfibsegs W3 mem4 v out).
{ intros HNN i Hi. destruct (HVB HNN) as (Hv0 & Hvn).
assert (Ev : (v =? 0) = false) by (apply Z.eqb_neq; lia).
unfold mem4. rewrite Ev.
destruct (HBLK HNN) as (Hby & _). rewrite HREQ in Hby.
apply aview_wr_in; [lia | rewrite HOUTN; lia | exact Hi |].
exact (proj1 (proj1 (Hby (v + Z.of_nat i) ltac:(lia)))). }
assert (HAR4 : AR tfibsegs B ly1 S1 W3 mem4 md4).
{ unfold mem4. destruct (v =? 0) eqn:Ev.
- exact (p1_AR_md B LAWS ly1 S1 W3 mem3 md3 md4 HAR3 SBM4).
- apply Z.eqb_neq in Ev. pose proof (HVNN Ev) as HNN. destruct (HVB HNN) as (Hv0 & Hvn).
destruct (HBLK HNN) as (Hby & _). rewrite HREQ in Hby.
apply (AR_wr B LAWS ly1 S1 W3 mem3 md3 md4 v out HAR3); [lia | rewrite HOUTN; lia | | exact SBM4].
intros a Ha. rewrite HOUTN in Ha. exact (Hby a Ha). }
(* the caller's window is present after the entry *)
assert (HPR4 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W3) mem4 a).
{ intros a Ha. unfold ASTACK in Ha.
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold kHighMemEnd in *; lia).
assert (Hrom : seg_rom tfibsegs (Z_to_bv 64 a) = None)
by (apply YF0x.seg_rom_none_high; unfold YF0x.TFIB_IMG_END; unfold kHighMemEnd in *; lia).
assert (HNB : ~ (p <> PNull /\ v <= a < v + req_size (len + 1))).
{ intros [HNN HC]. pose proof (HVLO HNN) as HVS. unfold ASTACK in Hslo. lia. }
apply (apresent_of_view (w_H W3) (w_H W3) mem3 mem4 a Hrom (HM4out a Ha64 HNB)).
destruct (Z_lt_le_dec a (sp0 - 2144 - MALLOC_ASAN_STK)) as [L|L].
- apply (apresent_of_view (w_H W) (w_H W3) mem2 mem3 a Hrom).
+ apply (HVIEW3 a Ha64).
* exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold ASTACK in Hslo; lia)).
* apply (al_stack _ _ LAWS ly1 S1 W3 mem3 md3 a HAR3). rewrite Hlo1, Hhi1. unfold ASTACK in Hslo. lia.
* unfold ascratch. rewrite HSP2. intros [HC1|HC2]; [lia | exact (HNERR a ltac:(lia) HC2)].
* exact HNB.
+ apply HPR2. apply HPR1. apply HpresA. unfold ASTACK. lia.
- destruct (Z_lt_le_dec a (sp0 - 2144)) as [L2|L2].
+ apply HPRESW3. rewrite HSP2. lia.
+ apply HPRESX. lia. }
(* every callee-saved register is the caller's *)
assert (HRP4 : aregs_preserved regs regs4).
{ assert (K4 : forall r0 : bv 5, 24 <= bv_unsigned r0 <= 27 -> getr regs4 r0 = getr regs r0).
{ intros r0 Hr0. rewrite (UK r0 Hr0). rewrite (R3C r0 ltac:(unfold acallee_saved; lia)).
rewrite (QK2 r0 ltac:(lia)). exact (RK1 r0 Hr0). }
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U2.
change (Z_to_bv 64 (bv_unsigned (getr regs 2%bv)) = getr regs 2%bv). apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite U3, (R3C 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3. exact R3.
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite U4, (R3C 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4. exact R4.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U8. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U9. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U18. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U19. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U20. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U21. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U22. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite U23. unfold w64. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). apply K4. change (bv_unsigned (24%bv : bv 5)) with 24. lia.
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). apply K4. change (bv_unsigned (25%bv : bv 5)) with 25. lia.
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). apply K4. change (bv_unsigned (26%bv : bv 5)) with 26. lia.
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). apply K4. change (bv_unsigned (27%bv : bv 5)) with 27. lia. }
assert (HIO4 : same_io md md4)
by exact (same_io_trans md md2 md4 (same_io_trans md md1 md2 (sbm_same_io md md1 SBM1) (sbm_same_io md1 md2 SBM2))
(same_io_trans md2 md3 md4 HIO3 (sbm_same_io md3 md4 SBM4))).
(* the leaf *)
exists ly1, regs4, mem4, md4.
split; [reflexivity|].
split.
{ split; [exact HAR4|]. split; [exact HLE|]. split; [exact HWLE|]. split; [exact HRP4|].
split; [exact HIO4|]. split; [| exact HPR4].
intros a Ha N1 N2 N3 N4. cbn [fst snd] in N4. fold v in N4.
assert (Hout : ~ (sp0 - 16384 <= a < sp0)) by (intros H'; apply N3; left; unfold ASTACK; exact H').
rewrite (HM4out a Ha N4).
rewrite (HVIEW3 a Ha N1 N2 ltac:(unfold ascratch; rewrite HSP2; intros [HC1|HC2];
[unfold MALLOC_ASAN_STK in HC1; lia | apply N3; right; exact HC2]) N4).
rewrite (HFR2 a Ha ltac:(lia)).
exact (HFR1 a Ha ltac:(lia)). }
split; [exact U10|]. split; [exact HQT | exact HM4in].
Qed.

End c.
