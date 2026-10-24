(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0v YK02 YP0n YM06 YK1j YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO14 YO0v YO0q YO0u YO15 YO10 YO12 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02
YN2b YN2e YN0g YN0d YN0c YN25 YN0a YN0p
YN2j YN2h YN2n YN2m YN2d YN2i
YN2k YN0j YN0h YN0i YN1k YN1l YN1m
YN2w YN1d YN31 YN0z YN13 YN14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM01.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mreal_pure {R} : forall segs c (t : itree astate R) Q,
(forall q s k, t <> IAsk q s k) -> (forall r, t = IRet r -> SR segs c (Q r)) -> mreal segs c t Q.
Proof.
intros segs c t Q NA HR. destruct t as [r | q s k | e]; cbn; [exact (HR r eq_refl) | exfalso; exact (NA q s k eq_refl) | exact I].
Qed.
Section f.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Variables (j1 j2 : Z).
Let sp : Z := bv_unsigned (getr regs 2).
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let nu : Z := cs L A sc g j1 j2 35.
Section MC.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis Km : In m (keys s1).
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Hypothesis ERRW1 : forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a.
Variable E3 : env.
Hypothesis HA3 : env_agree 40 E00 E3.
Hypothesis E3_40 : ew E3 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis E3_56 : ew E3 56 = Z_to_bv 64 (usage_of s1 sc).
Hypothesis E3_61 : ew E3 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc)).
Hypothesis E3_62 : ew E3 62 = Z_to_bv 64 (16 * nu * initial_cnt sc (usage_of s1 sc)).
Hypothesis E3_67 : ew E3 67 = Z_to_bv 64 (if is_bouncing s1 sc then 1 else 0).
Variable E6 : env.
Hypothesis AG6 : env_agree 73 E3 E6.
Let usage : Z := usage_of s1 sc.
Let K : Z := initial_cnt sc usage.
Let s3 : astate := seq_st (ab_st sc s1).
Let plan : Z * Z := mmap_plan s1 sc n K usage.
Hypothesis E6_81 : ew E6 81 = Z_to_bv 64 (snd plan).
Hypothesis E6_82 : ew E6 82 = Z_to_bv 64 (fst plan).
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Local Notation FRcB := (YN14.FRcB regs mem1).
Lemma E6_facts : env_agree 40 E00 E6 /\ ew E6 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew E6 10 = Z_to_bv 64 sc /\ ew E6 33 = Z_to_bv 64 (csn 33) /\ ew E6 2 = getr regs 2.
Proof.
destruct AG6 as [Y D]. assert (AG' : env_agree 40 E00 E6) by (eapply env_agree_trans; [exact HA3 | split; [intros k Hk; apply Y; lia | exact D]]).
split; [exact AG'|]. split; [rewrite (Y 40%nat) by lia; exact E3_40|]. split; [rewrite (agree_reg' E6 10 AG') by lia; exact R10|].
split; [exact (agree_cs' E6 33 AG' ltac:(lia)) | exact (agree_reg' E6 2 AG' ltac:(lia))].
Qed.
Lemma s3_factsC : Inv (m :: X) None U s3 /\ Xclean (m :: X) s3 /\ ama_ok s3 /\ keys s3 = keys s1 /\ MT s3 m = MT s1 m /\ bounded s3.
Proof.
pose proof (s3_facts X U sc m s1 HI1 RX1 Mm AMA1 BND1) as (I3 & X3 & A3 & _ & B3).
pose proof (ab_st_fields sc s1) as (F1 & _). pose proof (seq_st_fields (ab_st sc s1)) as (G1 & _).
split; [exact I3|]. split; [exact X3|]. split; [exact A3|]. subst s3. unfold keys, MT. rewrite G1, F1. split; [reflexivity|]. split; [reflexivity|]. exact B3.
Qed.
Lemma mslot_facts : forall mm, midrep B L1 s3 mm md1 ->
(forall i, 0 <= i < 40 -> mbyte src0segs mm (ptr_addr L1 m + i) = Some (Z_to_bv 8 0)) /\
(forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> present mm x /\ ~ in_img B x /\ 4096 <= x < alloc_ceiling).
Proof.
intros mm HM. pose proof s3_factsC as (I3 & X3 & A3 & K3 & M3 & _).
pose proof (inv_keys I3) as (_ & KP & _ & _ & Kc). rewrite K3 in KP. destruct (KP m Km) as (a & k & Ha & Hk & Em).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
assert (PG : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> ptr_addr L1 a <= x < ptr_addr L1 a + PGSZ).
{ intros x Hx. rewrite Em, ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
split.
- pose proof (memrep_cell B L1 s3 mm) as MC.
assert (CELLS : forall c, In c (meta_slot_cells m (MT s3 m)) -> cell_mem B L1 mm c).
{ intros c Hc. apply (MC c (mid_mem _ _ _ _ _ HM)). unfold image. rewrite !in_app_iff. right. left.
apply (slot_cells_in_areas s3 (st_areas s3) a k c Ha Hk'). unfold slot_of. rewrite <- Em. exact Hc. }
rewrite M3 in CELLS.
assert (BY : forall off w, In (MCell (LMem (padd m off)) w (VZ 0)) (meta_slot_cells m (MT s1 m)) -> forall j, (j < w)%nat -> mbyte src0segs mm (ptr_addr L1 m + off + Z.of_nat j) = Some (Z_to_bv 8 0)).
{ intros off w Hin j Hj. pose proof (CELLS _ Hin) as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C.
change (loc_addr L1 (LMem (padd m off))) with (ptr_addr L1 (padd m off)) in C. rewrite ptr_addr_padd in C. change (ms_segs B) with src0segs in C.
rewrite (C j Hj). f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
assert (IN : forall off w, In (MCell (LMem (padd m off)) w (VZ 0)) [MCell (LMem (padd m META_prev)) 8 (VZ 0); MCell (LMem (padd m META_next)) 8 (VZ 0); MCell (LMem (padd m META_mem)) 8 (VZ 0);
MCell (LMem (padd m META_avail)) 4 (VZ 0); MCell (LMem (padd m META_freed)) 4 (VZ 0); MCell (LMem (padd m META_bits)) 8 (VZ 0)] ->
In (MCell (LMem (padd m off)) w (VZ 0)) (meta_slot_cells m (MT s1 m))).
{ intros off w Hin. destruct Mm as [E1|E1]; rewrite E1; cbn [meta_slot_cells optr]; exact Hin. }
intros i Hi.
assert (CASES : exists off w j, (In (off, w) [(0, 8%nat); (8, 8%nat); (16, 8%nat); (24, 4%nat); (28, 4%nat); (32, 8%nat)]) /\ (j < w)%nat /\ i = off + Z.of_nat j).
{ destruct (Z_lt_le_dec i 8); [exists 0, 8%nat, (Z.to_nat i); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 16); [exists 8, 8%nat, (Z.to_nat (i - 8)); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 24); [exists 16, 8%nat, (Z.to_nat (i - 16)); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 28); [exists 24, 4%nat, (Z.to_nat (i - 24)); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 32); [exists 28, 4%nat, (Z.to_nat (i - 28)); split; [inlist | split; lia]|].
exists 32, 8%nat, (Z.to_nat (i - 32)); split; [inlist | split; lia]. }
destruct CASES as (off & w & j & Hin & Hj & ->). rewrite Z.add_assoc. apply (BY off w); [| exact Hj].
apply IN. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits. cbn [In] in Hin.
destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <-; inlist.
- intros x Hx. specialize (PG x Hx). pose proof (areas_off_img B (m :: X) None U L1 s3 mm md1 I3 HM a x Ha PG) as [NI Rx].
split; [| split; [exact NI | exact Rx]].
pose proof (mid_mem _ _ _ _ _ HM) as (_ & _ & FT).
assert (Hin : In (LMem a, PGSZ) (footprint s3)) by (right; apply in_app_iff; left; apply in_map_iff; eexists; split; [reflexivity | exact Ha]).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as FO. cbn [foot_ok fst snd] in FO. apply FO. exact PG.
Qed.
Lemma planC : 1 <= fst plan <= 32 /\ 4096 <= snd plan <= 2 ^ 20 /\ snd plan mod 4096 = 0.
Proof.
pose proof (plan_facts X U L A regs mem md sc n HI Hsc Hn MID g j1 j2 s1 BND1) as (P1 & P2 & P3 & _). exact (conj P1 (conj P2 P3)).
Qed.
Lemma skel_MK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_MK) = skel_M1 /\ ss_atoms_lt 86 ss_MK = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma skel_M1_apart : forall E lo hi r, env_agree 40 E00 E -> lo < hi -> (forall x, lo <= x < hi -> ~ in_img B x /\ x < alloc_ceiling) ->
In (r_base r, r_lo r, r_hi r) skel_M1 ->
hi <= base_val E (r_base r) + r_lo r \/ base_val E (r_base r) + r_hi r <= lo.
Proof.
intros E lo hi r HA Hlh Hoff Hin. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (_ & _ & P3 & _). destruct cs_facts' as (C33 & _).
assert (IMG : forall a b, 0x1e000 <= a -> b <= 0x51000 -> a < b -> hi <= a \/ b <= lo).
{ intros a b Ha Hb Hab. destruct (Z_lt_le_dec lo a) as [H1|H1].
- destruct (Z_le_dec hi a); [left; lia|]. exfalso. exact (proj1 (Hoff a ltac:(lia)) (src0_rwseg_img a ltac:(lia))).
- destruct (Z_le_dec b lo); [right; lia|]. exfalso. exact (proj1 (Hoff lo ltac:(lia)) (src0_rwseg_img lo ltac:(lia))). }
pose proof (Hoff lo ltac:(lia)) as [_ Rlo]. pose proof (Hoff (hi - 1) ltac:(lia)) as [_ Rhi]. pose proof Hstk as [SK1 SK2]. unfold ASF in SK1.
unfold skel_M1 in Hin. cbn [In] in Hin.
destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?(agree_cs' E 33 HA), ?(agree_reg' E 2 HA) by lia; rewrite ?lit64_small by (lits; lia);
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; lits; first [lia | apply IMG; lia].
Qed.
Lemma mslot_region : forall E mm, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) -> midrep B L1 s3 mm md1 ->
region_ok src0segs E mm R_mslot /\
(forall r, In (r_base r, r_lo r, r_hi r) skel_M1 -> extent_disjoint E R_mslot r).
Proof.
intros E mm AG E40 HM. pose proof (proj1 alloc_ceiling_val) as AC. destruct (mslot_facts mm HM) as [ZB RB].
destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & NIm & Rm).
assert (Um : bv_unsigned (ew E 40) = ptr_addr L1 m) by (rewrite E40; apply lit64_small; lia).
split.
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_mslot ms_mem]; rewrite Um; [lia | lia | |].
+ intros o Ho. apply present_writable. apply (proj1 (RB (ptr_addr L1 m + o) ltac:(lia))).
+ assert (CH : forall off (w : nat), 0 <= off -> off + Z.of_nat w <= 40 -> chunk_ok src0segs E mm (ptr_addr L1 m) (mkChunk off (CVal (N.of_nat w) (SLit 0)))).
{ intros off w Ho Hw. apply (chunk_ok_cval src0segs E mm (ptr_addr L1 m) off w (SLit 0) 0); [reflexivity | lia |].
intros k Hk. rewrite <- Z.add_assoc. rewrite ZB by lia. f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
repeat apply Forall_cons; try apply Forall_nil;
first [exact (CH 0 8%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 8 8%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 16 8%nat ltac:(lia) ltac:(cbn; lia))
| exact (CH 24 4%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 28 4%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 32 8%nat ltac:(lia) ltac:(cbn; lia))].
- intros r Hr. unfold extent_disjoint. cbn [r_base r_lo r_hi R_mslot base_val]. rewrite Um.
destruct (skel_M1_apart E (ptr_addr L1 m) (ptr_addr L1 m + 40) r AG ltac:(lia) ltac:(intros x Hx; destruct (RB x Hx) as (_ & NI & Rx); split; [exact NI | lia]) Hr); lia.
Qed.
Lemma mslot_fresh : forall mm (a : word) len, midrep B L1 s3 mm md1 -> 0 < len -> 0 < bv_unsigned a -> bv_unsigned a + len <= 2 ^ 64 ->
region_free (vm_reserved (m_vmmaps md1) ++ vm_maps (m_vmmaps md1)) a (Z_to_bv 64 len) = true ->
forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> ~ (bv_unsigned a <= x < bv_unsigned a + len).
Proof.
intros mm a len HM Hlen Ha0 Hal RF x Hx. pose proof s3_factsC as (I3 & X3 & A3 & K3 & M3 & _).
pose proof (inv_keys I3) as (_ & KP & _ & _ & Kc). rewrite K3 in KP. destruct (KP m Km) as (ar & k & Ha & Hk & Em).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb ar _); lia).
pose proof (inv_areas I3) as (_ & Hareas & _). destruct (Hareas ar Ha) as (r & o & rg & Ear & Ho & Hlo & Hr & Hl & Hlen' & _).
apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM) a len Hlen Ha0 Hal RF r rg x Hr Hl).
rewrite Em, ptr_addr_padd, Ear in Hx. unfold ptr_addr in Hx. cbn [loc_addr] in Hx.
assert (Hrl : reg_lo rg <= PGSZ) by (unfold reg_lo; destruct (rg_kind rg); unfold PGSZ; lia).
clear - Hx Hrl Hlo Hlen' Hk'. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma map_grant_exists : forall mm len, midrep B L1 s3 mm md1 -> mgrant s3 (KMmapRW len) -> 0 < len ->
exists a, grant_ok (Z_to_bv 64 0) md1 a (page_round len) = true.
Proof.
intros mm len HM (Hpos & Hlive & Hsl & Hreq) Hlen. pose proof s3_factsC as (I3 & _).
pose proof (mid_ledger _ _ _ _ _ HM) as G. pose proof (mid_ledgerx _ _ _ _ _ HM) as LX.
unfold req_len in Hpos, Hlive, Hreq. unfold MG_LIVE, MG_SLOTS, MG_REQ in *.
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas I3))))))))) as NN. cbv beta in NN.
pose proof (live_bytes_nonneg' s3 NN) as Hlb.
destruct src0_reserved_small as [RS RL]. pose proof src0_reserved_bytes as RB.
destruct (region_free_exists28_std (vm_reserved (m_vmmaps md1) ++ vm_maps (m_vmmaps md1)) (page_round len)) as (a & Ha1 & Ha2 & Ha3 & Ha4).
- pose proof (page_round_ge len). pose proof (page_round_lt len). lia.
- rewrite length_app. rewrite (lg_reserved _ _ _ _ G). pose proof (lg_count _ _ _ _ G). change (ms_segs B) with src0segs. lia.
- rewrite ivs_bytes_app, (lg_reserved _ _ _ _ G). change (ms_segs B) with src0segs.
rewrite (ivs_bytes_live_bytes (vm_maps (m_vmmaps md1))). pose proof (lx_lb _ _ _ LX). lia.
- exists a. unfold grant_ok.
rewrite (proj2 (Z.eqb_eq _ _) Ha1), (proj2 (Z.ltb_lt 0 _)) by lia.
pose proof (YM05.ceil_le_top _ (lg_ceil _ _ _ _ G)) as Htop.
assert (Ha3' : bv_unsigned a + page_round len <= alloc_top (m_vmmaps md1)) by lia.
rewrite (proj2 (Z.leb_le _ _) Ha3'), Ha4.
rewrite (proj2 (Z.leb_le _ _)).
2:{ pose proof (lg_backing _ _ _ _ G). pose proof (lg_limit _ _ _ _ G). unfold SRC_LIM_MIN in *.
pose proof (page_round_ge len). pose proof (page_round_lt len). change (2 ^ 32) with 4294967296 in Hlive. lia. }
reflexivity.
Qed.
Lemma to_Kf : forall regs3 mem3 RET, regs_ok E6 (ss_regs ss_MK) regs3 -> mem_ok src0segs E6 mem3 (ss_mem ss_MK) -> facts_ok E6 (ss_facts ss_MK) ->
RET = Z_to_bv 64 (2 ^ 64 - 12) -> midrep B L1 s3 mem3 md1 -> FRcB mem3 ->
st_ok src0segs E6 ss_Kf (mkst (regupd regs3 10 RET) (v_addi (Z_to_bv 64 (ss_pc ss_MK)) 4) mem3 (seg_rom src0segs)).
Proof.
intros regs3 mem3 RET Hregs Hmem HG -> HM HF. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct E6_facts as (AG & E40 & E10 & E33 & E2). destruct (mslot_facts mem3 HM) as [ZB RB].
pose proof (st_ok_resume_sv src0segs E6 ss_MK regs3 mem3 (SLit (2 ^ 64 - 12)) _ Hregs Hmem HG eq_refl) as HS0.
destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & NIm & Rm).
assert (Um : bv_unsigned (ew E6 40) = ptr_addr L1 m) by (rewrite E40; apply lit64_small; lia).
assert (HS1 : st_ok src0segs E6 (mkSS (ss_pc (resume ss_MK (SLit (2 ^ 64 - 12)) (ss_mem ss_MK) (ss_facts ss_MK))) (ss_regs (resume ss_MK (SLit (2 ^ 64 - 12)) (ss_mem ss_MK) (ss_facts ss_MK)))
(R_mslot :: ss_mem ss_MK) None (ss_facts ss_MK)) (mkst (regupd regs3 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 (ss_pc ss_MK)) 4) mem3 (seg_rom src0segs))).
{ apply (st_ok_add_region src0segs E6 _ _ R_mslot HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_mslot ms_mem]; rewrite Um; [lia | lia | |].
+ intros o Ho. apply present_writable. apply (proj1 (RB (ptr_addr L1 m + o) ltac:(lia))).
+ assert (CH : forall off (w : nat), 0 <= off -> off + Z.of_nat w <= 40 -> chunk_ok src0segs E6 mem3 (ptr_addr L1 m) (mkChunk off (CVal (N.of_nat w) (SLit 0)))).
{ intros off w Ho Hw. apply (chunk_ok_cval src0segs E6 mem3 (ptr_addr L1 m) off w (SLit 0) 0); [reflexivity | lia |].
intros k Hk. rewrite <- Z.add_assoc. rewrite ZB by lia. f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
repeat apply Forall_cons; try apply Forall_nil;
first [exact (CH 0 8%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 8 8%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 16 8%nat ltac:(lia) ltac:(cbn; lia))
| exact (CH 24 4%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 28 4%nat ltac:(lia) ltac:(cbn; lia)) | exact (CH 32 8%nat ltac:(lia) ltac:(cbn; lia))].
- cbn [ss_mem resume]. apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite (proj1 skel_MK) in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_mslot base_val]. rewrite Um.
destruct (skel_M1_apart E6 (ptr_addr L1 m) (ptr_addr L1 m + 40) r AG ltac:(lia) ltac:(intros x Hx; destruct (RB x Hx) as (_ & NI & Rx); split; [exact NI | lia]) Hr); lia. }
assert (HS2 : st_ok src0segs E6 (mkSS (ss_pc (resume ss_MK (SLit (2 ^ 64 - 12)) (ss_mem ss_MK) (ss_facts ss_MK))) (ss_regs (resume ss_MK (SLit (2 ^ 64 - 12)) (ss_mem ss_MK) (ss_facts ss_MK)))
(R_errnoS :: R_mslot :: ss_mem ss_MK) None (ss_facts ss_MK)) (mkst (regupd regs3 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 (ss_pc ss_MK)) 4) mem3 (seg_rom src0segs))).
{ apply (st_ok_add_region src0segs E6 _ _ R_errnoS HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_errnoS ms_mem]; [lits; lia | lits; lia | | apply Forall_nil].
intros o Ho. rewrite Z.add_0_l. apply (writable_ext1 mem1); [apply HF; [lits; lia | unfold WS; lits; lia | unfold CTX_SIZE; lits; lia] | apply ERRW1; lia].
- cbn [ss_mem]. apply Forall_cons.
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_errnoS R_mslot base_val]. rewrite Um. destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & NI & _).
destruct (Z_le_dec (ptr_addr L1 m + 40) ERRNO); [right; lits; lia|]. left.
destruct (Z_le_dec (ERRNO + 4) (ptr_addr L1 m)); [lits; lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) ERRNO).
* exact (proj1 (proj2 (RB ERRNO ltac:(lits; lia))) (src0_rwseg_img ERRNO ltac:(lits; lia))).
* apply NI. apply src0_rwseg_img. lits. lia.
+ apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite (proj1 skel_MK) in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_errnoS base_val]. unfold skel_M1 in Hr. cbn [In] in Hr.
destruct Hr as [H|[H|[H|[H|[H|[]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?E33, ?E2; rewrite ?lit64_small by (destruct cs_facts' as (C33 & _); lits; lia); fold sp; destruct cs_facts' as (C33 & _); lits; lia. }
exact HS2.
Qed.
Lemma skel_Kg : ss_atoms_lt 86 ss_MK = true /\ region_atoms_lt 41 R_mslot = true /\
ss_Kg = mkSS (ss_pc (resume ss_MK (SOff 86 0) (ss_mem ss_MK) (addfact 86 F_map (ss_facts ss_MK))))
(ss_regs (resume ss_MK (SOff 86 0) (ss_mem ss_MK) (addfact 86 F_map (ss_facts ss_MK))))
(R_grp :: R_mslot :: ss_mem ss_MK) None (addfact 86 F_map (ss_facts ss_MK)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma grant_facts : forall mm (a : word) len, midrep B L1 s3 mm md1 -> 4096 <= len -> len mod 4096 = 0 ->
grant_ok (Z_to_bv 64 0) md1 a (page_round len) = true ->
page_round len = len /\ bv_unsigned a mod 4096 = 0 /\ 4096 <= bv_unsigned a /\ bv_unsigned a + len <= alloc_ceiling /\
region_free (vm_reserved (m_vmmaps md1) ++ vm_maps (m_vmmaps md1)) a (Z_to_bv 64 len) = true /\
(forall x, bv_unsigned a <= x < bv_unsigned a + len -> ~ in_img B x /\ 4096 <= x < alloc_ceiling).
Proof.
intros mm a len HM Hlen Hmod GR. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
assert (PR : page_round len = len) by (apply page_round_fixed; unfold PGSZ; exact Hmod). rewrite PR in GR.
unfold grant_ok in GR. apply andb_prop in GR as [GR _]. apply andb_prop in GR as [GR RF].
apply andb_prop in GR as [GR Htop]. apply andb_prop in GR as [Hal Ha0].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Ha0. apply Z.leb_le in Htop. unfold page_size in Hal.
assert (Hceil : bv_unsigned a + len <= alloc_ceiling).
{ apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ (mid_ledger _ _ _ _ _ HM))); [| exact Htop].
rewrite Z.add_mod, Hal, Hmod by lia. reflexivity. }
assert (Ha4096 : 4096 <= bv_unsigned a) by (destruct (Z_lt_le_dec (bv_unsigned a) 4096); [rewrite Z.mod_small in Hal by lia; lia | lia]).
split; [exact PR|]. split; [exact Hal|]. split; [exact Ha4096|]. split; [exact Hceil|]. split; [exact RF|].
intros x Hx. split; [| lia]. intros Hi. exact (fresh_img B L1 s3 md1 (mid_ledger _ _ _ _ _ HM) a len ltac:(lia) Ha0 ltac:(lia) RF x Hi Hx).
Qed.
Lemma to_Kg : forall regs3 mem3 (a : word), regs_ok E6 (ss_regs ss_MK) regs3 -> mem_ok src0segs E6 mem3 (ss_mem ss_MK) -> facts_ok E6 (ss_facts ss_MK) ->
midrep B L1 s3 mem3 md1 -> grant_ok (Z_to_bv 64 0) md1 a (page_round (snd plan)) = true ->
st_ok src0segs (ewset E6 86 a) ss_Kg
(mkst (regupd regs3 10 a) (v_addi (Z_to_bv 64 (ss_pc ss_MK)) 4) (apply_zeros mem3 [(a, Z_to_bv 64 (page_round (snd plan)))]) (seg_rom src0segs)).
Proof.
intros regs3 mem3 a Hregs Hmem HG HM GR. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
destruct planC as (P1 & P2 & P3). destruct (grant_facts mem3 a (snd plan) HM ltac:(lia) P3 GR) as (PR & Hal & Ha4096 & Hceil & RF & Pfacts). rewrite PR in *.
destruct E6_facts as (AG & E40 & E10 & E33 & E2). destruct skel_Kg as (AT86 & AT41 & EKg).
set (len := snd plan) in *.
assert (Hmem4 : mem_ok src0segs E6 (apply_zeros mem3 [(Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 len)]) (ss_mem ss_MK)).
{ apply (mem_ok_zeros_outside src0segs E6 mem3 (ss_mem ss_MK) (bv_unsigned a) len Hmem); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 skel_MK) in Hr'.
destruct (skel_M1_apart E6 (bv_unsigned a) (bv_unsigned a + len) r' AG ltac:(lia) ltac:(intros x Hx; destruct (Pfacts x Hx) as [NI Rx]; split; [exact NI | lia]) Hr') as [H|H]; [right; exact H | left; exact H]. }
rewrite Z_to_bv_bv_unsigned in Hmem4.
pose proof (st_ok_resume_atom src0segs 86 F_map E6 ss_MK regs3 _ a Hregs Hmem4 HG AT86
ltac:(unfold F_map; cbn [af_lo af_hi]; lia) ltac:(unfold F_map; cbn [af_al2]; lia) ltac:(unfold F_map; cbn [af_al2]; change (2 ^ 12) with 4096; exact Hal)) as HS0.
change (mkFacts ((86%nat, F_map) :: f_atoms (ss_facts ss_MK)) (f_conds (ss_facts ss_MK)) (f_alias (ss_facts ss_MK))) with (addfact 86 F_map (ss_facts ss_MK)) in HS0.
set (E7 := ewset E6 86 a) in *.
assert (AG67 : env_agree 86 E6 E7) by (apply env_agree_ewset).
assert (AG7 : env_agree 40 E00 E7) by (eapply env_agree_trans; [exact AG | split; [intros k Hk; apply (proj1 AG67); lia | exact (proj2 AG67)]]).
assert (E7_40 : ew E7 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E40; apply (proj1 AG67); lia).
assert (E7_86 : ew E7 86 = a) by (unfold E7; apply ew_ewset_same).
set (mem4 := apply_zeros mem3 [(a, Z_to_bv 64 len)]) in *.
assert (Z4 : forall x, bv_unsigned a <= x < bv_unsigned a + len -> mem4 (Z_to_bv 64 x) = Some (Z_to_bv 8 0)).
{ intros x Hx. unfold mem4. apply apply_zeros1_in. rewrite !u64_of_Z by lia. lia. }
assert (K4 : forall x, 0 <= x < 2 ^ 64 -> ~ (bv_unsigned a <= x < bv_unsigned a + len) -> mem4 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
{ intros x Hx Hnot. unfold mem4. apply apply_zeros1_out. rewrite !u64_of_Z by lia. lia. }
destruct (mslot_region E7 mem3 AG7 E7_40 HM) as [RGm DJm]. destruct (mslot_facts mem3 HM) as [_ RB].
assert (Um : bv_unsigned (ew E7 40) = ptr_addr L1 m) by (rewrite E7_40; apply lit64_small; destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & _ & Rm); lia).
pose proof (mslot_fresh mem3 a len HM ltac:(lia) ltac:(lia) ltac:(lia) RF) as FRm.
assert (HS1 : st_ok src0segs E7 (mkSS (ss_pc (resume ss_MK (SOff 86 0) (ss_mem ss_MK) (addfact 86 F_map (ss_facts ss_MK)))) (ss_regs (resume ss_MK (SOff 86 0) (ss_mem ss_MK) (addfact 86 F_map (ss_facts ss_MK))))
(R_mslot :: ss_mem ss_MK) None (addfact 86 F_map (ss_facts ss_MK))) (mkst (regupd regs3 10 a) (v_addi (Z_to_bv 64 (ss_pc ss_MK)) 4) mem4 (seg_rom src0segs))).
{ apply (st_ok_add_region src0segs E7 _ _ R_mslot HS0); [reflexivity | |].
- cbn [ms_mem]. apply (region_ok_transport src0segs E7 mem3 mem4 R_mslot RGm eq_refl); cbn [r_base r_lo r_hi r_wlo r_whi base_val R_mslot]; rewrite Um; intros x Hx.
+ apply mbyte_ext1. apply K4; [destruct (RB x ltac:(lia)) as (_ & _ & Rx); lia | exact (FRm x ltac:(lia))].
+ apply writable_ext1. apply K4; [destruct (RB x ltac:(lia)) as (_ & _ & Rx); lia | exact (FRm x ltac:(lia))].
- cbn [ss_mem resume]. apply Forall_forall. intros r Hr. apply DJm. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite (proj1 skel_MK) in Hr. exact Hr. }
rewrite EKg. apply (st_ok_add_region src0segs E7 _ _ R_grp HS1); [reflexivity | |].
- cbn [ms_mem]. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_grp]; rewrite E7_86; [lia | lia | |].
+ intros o Ho. apply present_writable. exists (Z_to_bv 8 0). apply Z4. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply chunk_ok_czero. intros i Hi. unfold mbyte. rewrite Z4 by lia. reflexivity.
- cbn [ss_mem]. apply Forall_cons.
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_grp R_mslot base_val]. rewrite E7_86, Um.
destruct (Z_lt_le_dec (ptr_addr L1 m) (bv_unsigned a)) as [Hlt|Hge].
* right. destruct (Z_le_dec (ptr_addr L1 m + 40) (bv_unsigned a)); [lia|]. exfalso. apply (FRm (bv_unsigned a) ltac:(lia)). lia.
* left. destruct (Z_le_dec (bv_unsigned a + 16) (ptr_addr L1 m)); [lia|]. exfalso. apply (FRm (ptr_addr L1 m) ltac:(lia)). lia.
+ apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite (proj1 skel_MK) in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_grp base_val]. rewrite E7_86.
destruct (skel_M1_apart E7 (bv_unsigned a) (bv_unsigned a + len) r AG7 ltac:(lia) ltac:(intros x Hx; destruct (Pfacts x Hx) as [NI Rx]; split; [exact NI | lia]) Hr); lia.
Qed.
Definition KfPost (c : config) : Prop :=
exists ms, c = mkCfg ms md1 /\ st_ok src0segs E6 ss_Kf ms /\ midrep B L1 s3 (ms_mem ms) md1 /\ FRcB (ms_mem ms).
Definition KgPost (a : word) (c : config) : Prop :=
exists ms mem3, c = mkCfg ms (mmap_model a (Z_to_bv 64 (snd plan)) md1) /\ st_ok src0segs (ewset E6 86 a) ss_Kg ms /\
ms_mem ms = apply_zeros mem3 [(a, Z_to_bv 64 (snd plan))] /\ midrep B L1 s3 mem3 md1 /\ FRcB mem3 /\
grant_ok (Z_to_bv 64 0) md1 a (snd plan) = true.
Lemma wsub_MMK : wsub (ss_mem ss_MM) SKS = true. Proof. vm_compute. reflexivity. Qed.
Theorem step_MM : forall {R} (Kt : Z -> itree astate R) (Q : R -> config -> Prop) ms,
st_ok src0segs E6 ss_MM ms -> midrep B L1 s3 (ms_mem ms) md1 -> FRcB (ms_mem ms) ->
(forall c, KfPost c -> mreal src0segs c (Kt 0) Q) ->
(forall a c, KgPost a c -> mreal src0segs c (Kt 1) Q) ->
SR src0segs (mkCfg ms md1) (fun c1 => knode src0segs c1 (KMmapRW (snd plan)) s3 (fun z c2 => mreal src0segs c2 (Kt z) Q)).
Proof.
intros R Kt Q ms HS HM HF LF LG. pose proof s3_factsC as (I3 & X3 & A3 & _). destruct E6_facts as (AG & E40 & E10 & E33 & E2).
destruct planC as (P1 & P2 & P3).
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E6 ss_MM ss_MK); [exact Mh1 | exact Mlz1 | exact HS | apply run_MM |].
intros ms2 HS2 Hfr.
assert (ST : forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ms_mem ms2 (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)).
{ intros x Hx Hw. apply (frame_of_at E6 _ _ _ x Hfr Hx). intros Hin. destruct (in_wrange_wsub regs E6 _ SKS x wsub_MMK Hin) as (b & lo & hi & Hl & Hx').
unfold SKS in Hl. destruct Hl as [Hl|[]]. injection Hl as <- <- <-. exact (Hw (win_stack L A regs sc g j1 j2 s1 E6 x AG Hx')). }
assert (HM2 : midrep B L1 s3 (ms_mem ms2) md1) by exact (midrep_stack_gen U regs mem stk PRE Hstk (m :: X) L1 s3 (ms_mem ms) md1 (ms_mem ms2) I3 X3 A3 HM ST).
assert (HF2 : FRcB (ms_mem ms2)) by (intros x Hx Hw Hc; rewrite (ST x Hx Hw); exact (HF x Hx Hw Hc)).
destruct (st_ok_ecall_shape src0segs E6 ss_MK ms2 HS2 eq_refl) as (regs3 & mem3 & Hms & Hregs & Hmem & HG).
rewrite Hms. rewrite Hms in HM2, HF2. cbn [ms_mem pend_at] in HM2, HF2. rewrite ss_MK_pc.
apply SR_ret.
assert (RG : sr_get (ss_regs ss_MK) 17 = SLit 222 /\ sr_get (ss_regs ss_MK) 11 = SOff 81 0 /\ sr_get (ss_regs ss_MK) 12 = SLit 3 /\ sr_get (ss_regs ss_MK) 13 = SLit 34 /\
sr_get (ss_regs ss_MK) 14 = SLit 18446744073709551615 /\ sr_get (ss_regs ss_MK) 15 = SLit 0 /\ sr_get (ss_regs ss_MK) 10 = SLit 0) by (vm_compute; repeat split; reflexivity).
destruct RG as (G17 & G11 & G12 & G13 & G14 & G15 & G10).
apply (knode_mmap_rw src0segs regs3 (Z_to_bv 64 (src0_A_mmap + 0xc4)) mem3 (seg_rom src0segs) md1 s3 (snd plan)).
- exact Mh1. - exact Mlz1.
- rewrite (Hregs 17%bv), G17. reflexivity.
- rewrite (Hregs 11%bv), G11. cbn [sv_denot]. rewrite E6_81, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- lia.
- rewrite (Hregs 12%bv), G12. reflexivity.
- rewrite (Hregs 13%bv), G13. reflexivity.
- rewrite (Hregs 14%bv), G14. apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs 15%bv), G15. reflexivity.
-
intros e He. apply LF.
assert (Ee : errno_ret e = Z_to_bv 64 (2 ^ 64 - 12)) by (destruct He as [<-|[]]; unfold errno_ret; apply bv_eq; reflexivity). rewrite Ee.
exists (mkst (regupd regs3 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 (src0_A_mmap + 0xc4)) 4) mem3 (seg_rom src0segs)).
split; [reflexivity|]. split; [| split; [exact HM2 | exact HF2]].
rewrite <- ss_MK_pc. exact (to_Kf regs3 mem3 _ Hregs Hmem HG eq_refl HM2 HF2).
-
intros a GR. apply (LG a).
assert (GR0 : grant_ok (Z_to_bv 64 0) md1 a (page_round (snd plan)) = true) by (rewrite (Hregs 10%bv), G10 in GR; exact GR).
destruct (grant_facts mem3 a (snd plan) HM2 ltac:(lia) P3 GR0) as (PR & _).
pose proof (to_Kg regs3 mem3 a Hregs Hmem HG HM2 GR0) as T. rewrite PR in T, GR0. rewrite PR.
eexists _, mem3. split; [reflexivity|]. split; [| split; [reflexivity | split; [exact HM2 | split; [exact HF2 | exact GR0]]]].
rewrite <- ss_MK_pc. exact T.
-
intros Hmg. rewrite (Hregs 10%bv), G10. cbn [sv_denot]. exact (map_grant_exists mem3 (snd plan) HM2 Hmg ltac:(lia)).
Qed.
End MC.
End f.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
