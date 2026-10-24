(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1j YK0v YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0u YO15 YO10 YO12 YO14 YO0t YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26
YN2a YN2q YN2o YN0b YN07 YN0a YN08
YN0t YN2u YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition optrZ (L : layout) (o : option sptr) : Z :=
match o with Some p => ptr_addr L p | None => 0 end.
Lemma fetch_nt_ret : fetch_word src0segs (Z_to_bv 64 NT_RET) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma SR_nt_ret E ss ms md Q :
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = NT_RET ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (ew E 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E 1) (ms_mem ms) (seg_rom src0segs)) md) ->
SR src0segs (mkCfg ms md) Q.
Proof.
intros HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst src0segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_nt_ret | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Lemma le_byte_mod64 z k : le_byte (z mod 2 ^ 64) 8 k = le_byte z 8 k.
Proof. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma img_gap lo n a0 ln :
(forall x, lo <= x < lo + n -> in_img1 x) -> 0 < n -> (forall x, a0 <= x < a0 + ln -> ~ in_img B1 x) -> 0 < ln ->
lo + n <= a0 \/ a0 + ln <= lo.
Proof.
intros Hi Hn Ho Hln. destruct (Z_le_dec (lo + n) a0); [left; lia|]. destruct (Z_le_dec (a0 + ln) lo); [right; lia|]. exfalso.
destruct (Z_le_dec lo a0).
- apply (Ho a0); [lia|]. apply in_img1_in_img. apply Hi. lia.
- apply (Ho lo); [lia|]. apply in_img1_in_img. apply Hi. lia.
Qed.
Lemma Forall_app_intro {T} (P : T -> Prop) l1 l2 : Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros H1 H2. apply Forall_app. auto. Qed.
Lemma metas_apart X R U s L p q xp xq :
Inv X R U s -> layout_ok L s -> MT s p = Some xp -> MT s q = Some xq -> p <> q ->
ptr_addr L p + META_SIZE <= ptr_addr L q \/ ptr_addr L q + META_SIZE <= ptr_addr L p.
Proof.
intros HI HL Mp Mq Hne. pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP p (MT_Some_In_keys _ _ _ Mp)) as (a & k & Ha & Hk & Ep).
destruct (KP q (MT_Some_In_keys _ _ _ Mq)) as (a' & k' & Ha' & Hk' & Eq).
assert (Hk0 : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
assert (Hk0' : 0 <= k' < METAS_PER_AREA) by (unfold handed in Hk'; destruct (sptr_eqb a' _); lia).
unfold ptr_addr. rewrite Ep, Eq, !loc_addr_padd'.
destruct (sptr_eq_dec a a') as [<-|Hna].
- assert (k <> k') by (intros <-; apply Hne; congruence). unfold AREA_HDR, META_SIZE in *. nia.
- pose proof HL as (_ & _ & PW & _).
assert (Ia : In (LMem a, PGSZ) (footprint s)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
assert (Ia' : In (LMem a', PGSZ) (footprint s)) by (right; apply in_app_iff; left; apply in_map_iff; exists a'; auto).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW Ia Ia' ltac:(congruence)) as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd] in D; unfold ptr_addr; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; nia.
Qed.
Definition toMp (p : bpath) : bpathM := match p with P0 => MP0 | P1V1 => MP1V1 | P1V2 => MP1V2 | P2V2 => MP2V2 end.
Definition toMv (v : bvar) : bvarM := match v with VB1 => MVB1 | VB2 => MVB2 | VB3 => MVB3 | VB4a => MVB4a | VB4b => MVB4b end.
Lemma validB_M p v : validB p v = validBM (toMp p) (toMv v).
Proof. destruct p, v; reflexivity. Qed.
Section l.
Variables (X : list sptr) (U : Z -> Z) (fuel : nat) (L : layout) (A : astate) (g : sptr) (i : Z) (am : ameta).
Variables (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (gv : Z).
Variables (p : bpath) (v : bvar) (h hp : sptr) (ah ahp : ameta).
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HB : bounded A.
Hypothesis NPRE : nt_pre B1 X (S fuel) L A regs mem md g i.
Hypothesis Hgv : word_mem src0segs mem GUARD gv.
Hypothesis HC1 : nt_C1 A g i am = false.
Hypothesis VALID : validB p v = true.
Hypothesis PF : pfacts A g i am (toMp p).
Hypothesis VF : vfacts X A g am (toMv v) h hp ah ahp.
Let G := ptr_addr L g.
Let SP := spZ regs.
Let sc := am_sc am.
Lemma Mg : MT A g = Some (MUsed am). Proof. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma HL : layout_ok L A. Proof. exact (proj1 (proj2 NPRE)). Qed.
Lemma SO : syms_ok B1. Proof. exact (proj1 NPRE). Qed.
Lemma Hctx : ly_ctx L = CTX. Proof. exact (proj1 (proj2 (proj2 NPRE))). Qed.
Lemma MR : memrepX B1 X L A mem. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 NPRE))))). Qed.
Lemma sc48 : 0 <= am_sc am < 48. Proof. exact (proj1 (else_branch_facts X U A g i am HI Hu HC1)). Qed.
Definition xvB (n : nat) : Z :=
if (n <? 32)%nat then bv_unsigned (getr regs (nat_to_reg n))
else match n with
| 41%nat => optrZ L (am_prev am) mod 2 ^ 64
| 42%nat => optrZ L (am_next am) mod 2 ^ 64
| 43%nat => ptr_addr L (am_mem am) mod 2 ^ 64
| 44%nat => am_avail am
| 45%nat => am_freed am
| 46%nat => meta_bits am
| 47%nat => gv mod 2 ^ 64
| 48%nat => am_sc am
| 49%nat => CTX + 80 + 8 * am_sc am
| 50%nat => ptr_addr L h mod 2 ^ 64
| 51%nat => ptr_addr L hp mod 2 ^ 64
| 52%nat => TBL + 2 * am_sc am
| 53%nat => scl_of (am_sc am)
| 54%nat => usage_of A (am_sc am) mod 2 ^ 64
| 55%nat => znth (am_sc am - 7) (st_bounces A) mod 256
| 56%nat => am_last am
| 57%nat => (am_maplen am * 4096) mod 2 ^ 64
| _ => 0
end.
Lemma g_facts :
0 <= i <= am_last am /\ 0 <= am_last am <= 31 /\
0 <= am_avail am < 2 ^ 32 /\ 0 <= am_freed am < 2 ^ 32 /\
0 <= meta_bits am < 2 ^ 64 /\ Z.land (meta_bits am) 32 = 32 /\
4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall x, G <= x < G + 40 -> ~ in_img B1 x) /\
(exists a, In a (st_areas A) /\ In (LMem a, PGSZ) (footprint A) /\ loc_addr L (LMem a) <= G /\ G + 40 <= loc_addr L (LMem a) + PGSZ) /\
0 <= am_maplen am < 2 ^ 40.
Proof.
pose proof NPRE as (SO' & HL' & Hctx' & Hsec & MR' & ST & LG & _).
destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & _). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
pose proof (inv_groups HI g am Hu) as GG.
pose proof GG as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
assert (Hav32 : am_avail am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros j Hj; apply (proj1 (Gabove j Hj))]).
assert (Hfr32 : am_freed am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros j Hj; apply (proj2 (Gabove j Hj))]).
assert (Hsc : 0 <= am_sc am < 64) by (destruct Gcl as [(C & _)|(C & _)]; lia).
destruct (used_group_region X (Some (g, i)) U A g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & Hml0).
destruct (lg_placed _ _ _ _ LG _ _ Hr Hl) as (_ & R4096 & Rceil & _). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (Hml : 0 <= am_maplen am < 2 ^ 40).
{ split; [exact Gml|]. destruct (Z_lt_dec 0 (am_maplen am)); [|lia].
destruct (Gmp ltac:(lia)) as (r2 & rg2 & Em & Hr2 & _ & _ & Hlen2 & _). rewrite Em in Hr. cbn [prid] in Hr.
rewrite Hr in Hr2. injection Hr2 as <-. rewrite Em in *. cbn [poff] in *. unfold PGSZ in *. unfold group_extent, UNIT, IB in Hext. lia. }
pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP g ltac:(unfold keys; apply in_map_iff; exists (g, MUsed am); split; [reflexivity | apply In_of_mlookup; exact Mg])) as (a & k & Ha & Hk2 & Eg).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk2; destruct (sptr_eqb a _); lia).
destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & _).
destruct (lg_placed _ _ _ _ LG _ _ Hra Hral) as (Aal & A4096 & Aceil & Aimg).
assert (EG : G = ly_reg L ra + oa + AREA_HDR + META_SIZE * k).
{ unfold G, ptr_addr, loc_addr. rewrite Eg, Ea. cbn [padd]. lia. }
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia.
- unfold meta_bits. pose proof (bits_nonneg (am_last am) (am_sc am) (am_maplen am)). unfold bits_enc in *. lia.
- unfold meta_bits. pose proof (bits_lt64 (am_last am) (am_sc am) (am_maplen am)). unfold bits_enc in *. lia.
- assert (E5 : meta_bits am / 32 = 1 + 2 * (am_sc am + 64 * am_maplen am)).
{ unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((1 + 2 * (am_sc am + 64 * am_maplen am)) * 32 + am_last am) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. change 32 with (2 ^ 5).
destruct (Z.eq_dec j 5) as [->|Hne].
+ rewrite Z.pow2_bits_true by lia. rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2 ^ 5) with 32. rewrite E5.
replace (1 + 2 * (am_sc am + 64 * am_maplen am)) with (1 + (am_sc am + 64 * am_maplen am) * 2) by lia. rewrite Z.mod_add by lia. reflexivity.
+ rewrite Z.pow2_bits_eqb by lia. replace (5 =? j) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
- rewrite EG.
pose proof (proj2 (Z.div_exact (ly_reg L ra) 4096 ltac:(lia)) Aal) as E1. pose proof (proj2 (Z.div_exact oa 4096 ltac:(lia)) Hoa) as E2.
replace (ly_reg L ra + oa + 24 + 40 * k) with ((512 * (ly_reg L ra / 4096) + 512 * (oa / 4096) + 3 + 5 * k) * 8) by lia.
apply Z_mod_mult.
- intros x Hx. apply Aimg. lia.
- exists a. split; [exact Ha|]. split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
rewrite Ea. cbn [loc_addr]. lia.
Qed.
Lemma meta_facts q aq : usedX X A q aq ->
4096 <= ptr_addr L q /\ ptr_addr L q + 40 <= alloc_ceiling /\ ptr_addr L q mod 8 = 0 /\
(forall x, ptr_addr L q <= x < ptr_addr L q + 40 -> ~ in_img B1 x) /\
(exists a, In a (st_areas A) /\ In (LMem a, PGSZ) (footprint A) /\ loc_addr L (LMem a) <= ptr_addr L q /\ ptr_addr L q + 40 <= loc_addr L (LMem a) + PGSZ).
Proof.
intros Huq. pose proof NPRE as (SO' & HL' & Hctx' & Hsec & MR' & ST & LG & _).
pose proof (usedX_MT _ _ _ _ Huq) as [Mq _].
pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP q (MT_Some_In_keys _ _ _ Mq)) as (a & k & Ha & Hk2 & Eq).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk2; destruct (sptr_eqb a _); lia).
destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & _).
destruct (lg_placed _ _ _ _ LG _ _ Hra Hral) as (Aal & A4096 & Aceil & Aimg).
assert (EQ : ptr_addr L q = ly_reg L ra + oa + AREA_HDR + META_SIZE * k).
{ unfold ptr_addr, loc_addr. rewrite Eq, Ea. cbn [padd]. lia. }
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. pose proof (proj1 alloc_ceiling_val).
repeat match goal with |- _ /\ _ => split end; try lia.
- rewrite EQ.
pose proof (proj2 (Z.div_exact (ly_reg L ra) 4096 ltac:(lia)) Aal) as E1. pose proof (proj2 (Z.div_exact oa 4096 ltac:(lia)) Hoa) as E2.
replace (ly_reg L ra + oa + 24 + 40 * k) with ((512 * (ly_reg L ra / 4096) + 512 * (oa / 4096) + 3 + 5 * k) * 8) by lia.
apply Z_mod_mult.
- intros x Hx. apply Aimg. lia.
- exists a. split; [exact Ha|]. split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
rewrite Ea. cbn [loc_addr]. lia.
Qed.
Lemma XR : forall n, 0 <= xvB n < 2 ^ 64.
Proof.
intros n. pose proof g_facts as (_ & Hlast & Hav & Hfr & Hbits & _). pose proof sc48 as Hsc. unfold xvB.
destruct (n <? 32)%nat; [apply u64_range|].
assert (M64 : forall z, 0 <= z mod 2 ^ 64 < 2 ^ 64) by (intros z; apply Z.mod_pos_bound; lia).
assert (M256 : forall z, 0 <= z mod 256 < 2 ^ 64) by (intros z; pose proof (Z.mod_pos_bound z 256 ltac:(lia)); lia).
assert (HSCL : 0 <= scl_of (am_sc am) < 2 ^ 64) by (unfold scl_of; destruct (am_sc am <? 48) eqn:E; [pose proof (scl_range (am_sc am) Hsc); lia | lia]).
unfold CTX, TBL, src0_D_malloc_context, src0_D_size_classes.
do 58 (destruct n as [|n]; [first [apply M64 | apply M256 | exact HSCL | lia] |]). lia.
Qed.
Lemma CELL c : In c (imageX X A) -> cell_mem B1 L mem c.
Proof. intros Hc. exact (proj1 (Forall_forall _ _) (proj1 MR) _ Hc). Qed.
Lemma meta_cell q aq c : usedX X A q aq -> In c (meta_slot_cells q (Some (MUsed aq))) -> cell_mem B1 L mem c.
Proof.
intros Huq Hc. apply CELL. unfold imageX. apply in_app_iff. right. apply in_app_iff. left.
exact (meta_cells_in_areas X (Some (g, i)) U A HI q aq c (proj1 (usedX_MT _ _ _ _ Huq)) Hc).
Qed.
Lemma ctx_active_cell k : (k < 48)%nat ->
bytes_are mem (CTX + 80 + 8 * Z.of_nat k) 8 (optrZ L (nth k (st_active A) None)).
Proof.
intros Hk. assert (Hc : In (MCell (LCtx (CTX_active + 8 * Z.of_nat k)) 8 (optr (nth k (st_active A) None))) (ctx_cells A)).
{ unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
pose proof (CELL _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr] in C. rewrite Hctx in C. unfold CTX_active in C.
intros kk Hkk. destruct (nth k (st_active A) None) as [q|]; cbn [optr optrZ sval_num] in *;
(etransitivity; [|exact (C kk Hkk)]; unfold ptr_addr; f_equal; lia).
Qed.
Lemma ctx_usage_cell k : (k < 48)%nat ->
bytes_are mem (CTX + 464 + 8 * Z.of_nat k) 8 (nth k (st_usage A) 0).
Proof.
intros Hk. assert (Hc : In (MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ (nth k (st_usage A) 0))) (ctx_cells A)).
{ unfold ctx_cells. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
pose proof (CELL _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr sval_num] in C. rewrite Hctx in C. unfold CTX_usage in C.
intros kk Hkk. etransitivity; [|exact (C kk Hkk)]. f_equal. lia.
Qed.
Lemma ctx_bounces_cell k : (k < 32)%nat ->
bytes_are mem (CTX + 880 + Z.of_nat k) 1 (nth k (st_bounces A) 0).
Proof.
intros Hk. assert (Hc : In (MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ (nth k (st_bounces A) 0))) (ctx_cells A)).
{ unfold ctx_cells. rewrite !in_app_iff. right; right; right; right. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
pose proof (CELL _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr sval_num] in C. rewrite Hctx in C. unfold CTX_bounces in C.
intros kk Hkk. etransitivity; [|exact (C kk Hkk)]. f_equal. lia.
Qed.
Lemma ctx_writable x : CTX <= x < CTX + CTX_SIZE -> writable_at src0segs mem x.
Proof. intros Hx. exact (proj1 (so_ctx_rw _ SO mem x Hx)). Qed.
Lemma ctx_img x : CTX <= x < CTX + CTX_SIZE -> in_img1 x.
Proof. unfold CTX, src0_D_malloc_context, CTX_SIZE, in_img1. lia. Qed.
Lemma meta_present q aq x : usedX X A q aq -> ptr_addr L q <= x < ptr_addr L q + 40 -> present mem x.
Proof.
intros Huq Hx. destruct (meta_facts q aq Huq) as (_ & _ & _ & _ & a & Ha & Hfa & Q1 & Q2).
apply (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) _ Hfa). cbn [fst snd]. unfold PGSZ in *. lia.
Qed.
Lemma tq_bytes : bytes_are mem (TBL + 2 * am_sc am) 2 (scl_of (am_sc am)).
Proof.
pose proof NPRE as (SO' & HL' & Hctx' & Hsec & MR' & ST & LG & _). pose proof sc48 as Hsc.
assert (Escl : scl_of (am_sc am) = znth (am_sc am) size_classes) by (unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
pose proof (scl_range (am_sc am) Hsc) as SR. rewrite Escl.
destruct (so_size_classes _ SO' (Z.to_nat (am_sc am)) ltac:(lia)) as (lo & hi & Hlo & Hhi & Hsum). rewrite Z2Nat.id in Hlo, Hhi by lia.
pose proof (u8_range lo). pose proof (u8_range hi).
pose proof (st_tables _ _ ST) as STB. unfold table_addr in STB.
cbn [ms_segs ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms] in STB.
cbn [ms_segs ms_size_classes src0_msyms] in Hlo, Hhi. unfold w64 in STB, Hlo, Hhi.
unfold znth. rewrite <- Hsum.
intros kk Hkk. unfold TBL. rewrite STB by (unfold src0_D_size_classes, src0_D_debruijn32, src0_D_small_cnt_tab, src0_D_med_cnt_tab; lia).
destruct kk as [|[|]]; [| | lia]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
+ rewrite Z.add_0_r, Hlo. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 lo) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small _ 65536) by lia. rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
+ change (Z.of_nat 1) with 1. rewrite Hhi. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 hi) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small _ 65536) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. symmetry. apply Z.mod_small. lia.
Qed.
Lemma sp_facts :
SP mod 16 = 0 /\ alloc_ceiling + 96 + 96 * Z.of_nat fuel <= SP /\ SP < 2 ^ 63 /\
(forall x, SP - 96 * Z.of_nat (S fuel) <= x < SP -> writable_at src0segs mem x).
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hceil & Hsp63 & Hstk & _).
unfold NT_FRAME in *. unfold SP. split; [exact Hal|]. split; [lia|]. split; [exact Hsp63|]. intros x Hx. apply Hstk. lia.
Qed.
Lemma EG : xvB 10 = G.
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ha0 & _). pose proof g_facts as (_&_&_&_&_&_&G1&G2&_). pose proof (proj1 alloc_ceiling_val).
unfold xvB. cbn [Nat.ltb Nat.leb nat_to_reg]. rewrite Ha0. apply lit64_small. unfold G in *. lia.
Qed.
Lemma EI : xvB 11 = i.
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ha1 & _). pose proof g_facts as (Hi & Hl & _).
unfold xvB. cbn [Nat.ltb Nat.leb nat_to_reg]. rewrite Ha1. apply lit64_small. lia.
Qed.
Lemma ESP : xvB 2 = SP. Proof. reflexivity. Qed.
Definition H : Z := ptr_addr L h.
Definition HP : Z := ptr_addr L hp.
Lemma h_facts : match v with VB4a | VB4b =>
usedX X A h ah /\ h <> g /\
4096 <= H /\ H + 40 <= alloc_ceiling /\ H mod 8 = 0 /\ (forall x, H <= x < H + 40 -> ~ in_img B1 x) /\
(G + 40 <= H \/ H + 40 <= G) /\ xvB aH = H
| _ => True end.
Proof.
pose proof (proj1 alloc_ceiling_val).
assert (K : usedX X A h ah -> h <> g -> usedX X A h ah /\ h <> g /\
4096 <= H /\ H + 40 <= alloc_ceiling /\ H mod 8 = 0 /\ (forall x, H <= x < H + 40 -> ~ in_img B1 x) /\
(G + 40 <= H \/ H + 40 <= G) /\ xvB aH = H).
{ intros Uh Hhg. destruct (meta_facts h ah Uh) as (F1 & F2 & F3 & F4 & _). unfold H.
repeat match goal with |- _ /\ _ => split end; auto.
- pose proof (metas_apart X _ U A L g h _ _ HI HL Mg (proj1 (usedX_MT _ _ _ _ Uh)) ltac:(intros E; exact (Hhg (eq_sym E)))) as D.
unfold META_SIZE, G in *. lia.
- unfold xvB, aH. cbn [Nat.ltb Nat.leb]. apply Z.mod_small. lia. }
destruct v; try exact I; cbn [toMv vfacts] in VF.
- destruct VF as (_ & _ & Hhg & _ & _ & Uh & _). exact (K Uh Hhg).
- destruct VF as (_ & _ & Hhg & _ & _ & Uh & _). exact (K Uh Hhg).
Qed.
Lemma hp_facts : match v with VB4b =>
usedX X A hp ahp /\ hp <> g /\ hp <> h /\
4096 <= HP /\ HP + 40 <= alloc_ceiling /\ HP mod 8 = 0 /\ (forall x, HP <= x < HP + 40 -> ~ in_img B1 x) /\
(G + 40 <= HP \/ HP + 40 <= G) /\ (H + 40 <= HP \/ HP + 40 <= H) /\ xvB aHP = HP
| _ => True end.
Proof.
pose proof (proj1 alloc_ceiling_val). destruct v; try exact I. cbn [toMv vfacts] in VF.
destruct VF as (_ & _ & Hhg & _ & _ & Uh & _ & _ & Hph & Hpg & Uhp & _).
destruct (meta_facts hp ahp Uhp) as (F1 & F2 & F3 & F4 & _). unfold HP.
repeat match goal with |- _ /\ _ => split end; auto.
- pose proof (metas_apart X _ U A L g hp _ _ HI HL Mg (proj1 (usedX_MT _ _ _ _ Uhp)) ltac:(intros E; exact (Hpg (eq_sym E)))) as D.
unfold META_SIZE, G in *. lia.
- pose proof (metas_apart X _ U A L h hp _ _ HI HL (proj1 (usedX_MT _ _ _ _ Uh)) (proj1 (usedX_MT _ _ _ _ Uhp)) ltac:(intros E; exact (Hph (eq_sym E)))) as D.
unfold META_SIZE, H in *. lia.
- unfold xvB, aHP. cbn [Nat.ltb Nat.leb]. apply Z.mod_small. lia.
Qed.
Lemma regsB_ok : regs_ok (EV xvB) regs_init regs.
Proof.
apply regs_ok_init. intros n Hn. unfold xvB. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply Z_to_bv_bv_unsigned.
Qed.
Ltac denB := cbn [sv_denot]; rewrite ?alu64_and, ?alu64_or, ?alu64_srl, ?alu64_sll, ?alu64_add, ?alu64_sub; rewrite ?(ew_EV xvB XR);
unfold aSP, aNG, aNI, aPREV, aNEXT, aGMEM, aGAV, aGFR, aGBITS, aGV, aSC, aACT, aH, aHP, aTQ2, aSCL, aUSG, aBNC, aLAST, aMP;
rewrite ?EG, ?EI; unfold xvB; cbn [Nat.ltb Nat.leb nat_to_reg]; rewrite ?Z.add_0_r.
Ltac weq := apply (proj2 (word_eq _ _)).
Lemma atomsB_ok : atoms_ok (EV xvB) (nt_atoms ++ p_atoms p ++ v_atoms v).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml).
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof sc48 as Hsc. pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof h_facts as HF. pose proof hp_facts as HPF.
assert (M64 : forall z, 0 <= z mod 2 ^ 64 <= 2 ^ 64 - 1) by (intros z; pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)); lia).
assert (HSCL : 1 <= scl_of (am_sc am) <= 8191) by (unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); apply scl_range; lia).
apply atoms_ok_app; [|apply atoms_ok_app].
- cbn [nt_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xvB XR).
unfold aSP, aNG, aNI, aPREV, aNEXT, aGMEM, aGAV, aGFR, aGBITS, aGV, aSC, aACT, aLAST, aUSG, aBNC. rewrite EG, EI, ESP.
unfold xvB. cbn [Nat.ltb Nat.leb]. unfold CEIL, CTX, src0_D_malloc_context.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
pose proof (M64 (optrZ L (am_prev am))). pose proof (M64 (optrZ L (am_next am))). pose proof (M64 (ptr_addr L (am_mem am))). pose proof (M64 gv).
pose proof (M64 (usage_of A (am_sc am))). pose proof (Z.mod_pos_bound (znth (am_sc am - 7) (st_bounces A)) 256 ltac:(lia)).
unfold G, SP in *.
repeat split; try lia.
apply ctx_al8.
- destruct p; cbn [p_atoms atoms_ok]; [exact I| | |];
unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite !(ew_EV xvB XR); unfold aTQ2, aSCL, aMP; unfold xvB; cbn [Nat.ltb Nat.leb];
unfold TBL, src0_D_size_classes; change (2 ^ 1) with 2; change (2 ^ 0) with 1; change (2 ^ 12) with 4096; rewrite ?Z.mod_1_r;
cbn [toMp pfacts] in PF; destruct PF as ((_ & Hml0 & _) & _);
rewrite (Z.mod_small (am_maplen am * 4096)) by lia;
(repeat split; try lia; [apply tbl_al2 | apply Z_mod_mult]).
- destruct v; cbn [v_atoms atoms_ok]; try exact I;
unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite !(ew_EV xvB XR); change (2 ^ 3) with 8.
+ destruct HF as (_ & _ & F1 & F2 & F3 & _ & _ & ->). repeat split; lia.
+ destruct HF as (_ & _ & F1 & F2 & F3 & _ & _ & ->). destruct HPF as (_ & _ & _ & P1 & P2 & P3 & _ & _ & _ & ->). repeat split; lia.
Qed.
Lemma Ebits : meta_bits am = bits_enc (am_last am) (am_sc am) (am_maplen am).
Proof. reflexivity. Qed.
Lemma U_NSELF : bv_unsigned (sv_denot (EV xvB) NSELF) = sx32 (2 ^ i).
Proof.
pose proof g_facts as (Hi & Hlast & _).
unfold NSELF. change (sv_denot (EV xvB) (SAluw ALU_SLL (SLit 1) (SOff aNI 0))) with (sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV xvB) (SLit 1))) (low32 (sv_denot (EV xvB) (SOff aNI 0))))).
rewrite sllw_rr_unsigned, (den_off0 _ XR), U_lit, (lit64_small (xvB aNI)) by apply XR. change (1 mod 2 ^ 64) with 1.
unfold aNI. rewrite EI. rewrite sllw_1 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma U_NMASK : bv_unsigned (sv_denot (EV xvB) NMASK) = sx32 (nt_mask am).
Proof.
unfold NMASK. change (sv_denot (EV xvB) (SAlu ALU_OR (SExt true 32 (SOff aGAV 0)) (SExt true 32 (SOff aGFR 0)))) with
(alu64 ALU_OR (sv_denot (EV xvB) (SExt true 32 (SOff aGAV 0))) (sv_denot (EV xvB) (SExt true 32 (SOff aGFR 0)))).
rewrite alu64_or, !U_sext32, !(U_off0 _ XR). unfold aGAV, aGFR, xvB. cbn [Nat.ltb Nat.leb]. unfold nt_mask. rewrite Z.lor_comm. apply lor_sx32.
Qed.
Lemma U_NMS : bv_unsigned (sv_denot (EV xvB) NMS) = sx32 (nt_mask am + 2 ^ i).
Proof.
unfold NMS. change (sv_denot (EV xvB) (SAluw ALU_ADD NMASK NSELF)) with (sext 64 (alu32 ALU_ADD (low32 (sv_denot (EV xvB) NMASK)) (low32 (sv_denot (EV xvB) NSELF)))).
rewrite addw_rr_unsigned, U_NMASK, U_NSELF. apply addw_masks.
Qed.
Lemma U_NALL : bv_unsigned (sv_denot (EV xvB) NALL) = sx32 (ones (am_last am)).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & _).
unfold NALL. change (sv_denot (EV xvB) (SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff aGBITS 0)) (SLit (-1)))) with
(sext 64 (alu32 ALU_ADD (low32 (sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV xvB) (SLit 2))) (low32 (sv_denot (EV xvB) (SOff aGBITS 0)))))) (low32 (sv_denot (EV xvB) (SLit (-1)))))).
rewrite addw_rr_unsigned, sllw_rr_unsigned, (U_off0 _ XR). cbn [sv_denot]. rewrite (lit64_unsigned (-1)), !lit64_small by lia.
unfold aGBITS, xvB. cbn [Nat.ltb Nat.leb]. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite (proj2 (addiw_sllw2_m1 (meta_bits am) ltac:(lia))). f_equal. f_equal.
unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + (1 + 2 * am_sc am + 128 * am_maplen am) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma mask_self_range : 0 <= nt_mask am + 2 ^ i < 2 ^ 32 /\ 0 <= ones (am_last am) < 2 ^ 32 /\ 0 <= nt_mask am < 2 ^ 32 /\ 0 < 2 ^ i < 2 ^ 32.
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & _).
pose proof (mask_facts X U A g i am HI Hu) as (_ & _ & Hm0 & Hbit & _).
assert (Hb : 0 < 2 ^ i < 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
assert (D : Z.land (nt_mask am) (2 ^ i) = 0).
{ apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec i j) as [<-|]; [rewrite Hbit; reflexivity | apply andb_false_r]. }
pose proof (lor_range (am_freed am) (am_avail am) 32 ltac:(lia) ltac:(lia)) as LR. unfold nt_mask in *.
split; [rewrite (Z.add_nocarry_lxor _ _ D); apply lxor_range; lia|]. split; [|split; [lia | exact Hb]].
unfold ones. assert (0 < 2 ^ (am_last am + 1) <= 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]). lia.
Qed.
Lemma aliasB_ok : alias_ok (EV xvB) (nt_alias ++ p_alias p).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof sc48 as Hsc.
pose proof (Z.mod_pos_bound (am_maplen am * 4096) (2 ^ 64) ltac:(lia)) as MPR.
apply alias_ok_app.
- cbn [nt_alias alias_ok]. split; [|split; [|split; [|exact I]]].
+ weq. change (sv_denot (EV xvB) (SAlu ALU_ADD (SExt true 32 (SOff aGFR 0)) (SLit 0))) with (alu64 ALU_ADD (sv_denot (EV xvB) (SExt true 32 (SOff aGFR 0))) (sv_denot (EV xvB) (SLit 0))).
rewrite alu64_add, U_lit. change (0 mod 2 ^ 64) with 0. pose proof (u64_range (sv_denot (EV xvB) (SExt true 32 (SOff aGFR 0)))). unfold add64. rewrite Z.add_0_r. apply Z.mod_small. lia.
+ weq. unfold SCX. denB. rewrite !lit64_small by lia.
change (52 mod 64) with 52. change (58 mod 64) with 58. rewrite Ebits. apply bits_sc; lia.
+ weq. denB. unfold CTX, src0_D_malloc_context. rewrite !lit64_small by lia.
change (3 mod 64) with 3. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.mod_small by lia. lia.
- unfold p_alias. apply alias_ok_app.
+ destruct p; [exact I| | |]; cbn [toMp pfacts] in PF; destruct PF as ((_ & Hml0 & _) & _); cbn [alias_ok]; (split; [|split; [|split; [|exact I]]]); weq; denB;
unfold TBL, src0_D_size_classes; rewrite ?(lit64_unsigned (-4096)); rewrite ?lit64_small by lia; rewrite ?Ebits.
all: try (change (5 mod 64) with 5; rewrite bits_2sc by lia; lia).
all: try (change (1 mod 64) with 1; unfold sll64; rewrite Z.shiftl_mul_pow2, Z.mod_small by lia; lia).
all: change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096); rewrite bits_maplen_bytes by lia; rewrite Z.mod_small by lia; reflexivity.
+ cbn [alias_ok]. split; [|exact I]. weq. denB. rewrite !lit64_small by lia. rewrite Ebits, bits_land31 by lia.
destruct p; denB; rewrite ?lit64_small by lia; try reflexivity.
cbn [toMp pfacts] in PF. destruct PF as (_ & -> & _). reflexivity.
Qed.
Lemma U_NINE : bv_unsigned (sv_denot (EV xvB) NINE) = 9 * (am_last am + 1).
Proof.
pose proof g_facts as (Hi & Hlast & _).
unfold NINE. change (sv_denot (EV xvB) (SAlu ALU_ADD (SMd M_MUL (SOff aLAST 0) (SLit 9)) (SLit 9))) with
(alu64 ALU_ADD (mul_div M_MUL (sv_denot (EV xvB) (SOff aLAST 0)) (sv_denot (EV xvB) (SLit 9))) (sv_denot (EV xvB) (SLit 9))).
rewrite alu64_add, mul64_unsigned, (U_off0 _ XR), U_lit. unfold aLAST, xvB. cbn [Nat.ltb Nat.leb]. change (9 mod 2 ^ 64) with 9.
unfold mul64, add64. rewrite (Z.mod_small (am_last am * 9)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bounces_range : 7 <= am_sc am <= 38 -> 0 <= znth (am_sc am - 7) (st_bounces A) <= 255.
Proof.
intros Hsc. pose proof (inv_ctx HI) as (_ & _ & _ & Lb & _ & _ & Bb & _). apply Bb. unfold znth. apply nth_In. rewrite Lb. lia.
Qed.
Lemma usage_range : 0 <= usage_of A (am_sc am) < 2 ^ 48.
Proof. exact (proj1 HB (am_sc am)). Qed.
Ltac cprep := unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?branch_geu, ?branch_ltu, ?branch_eq, ?branch_ne.
Lemma cond_C32_ok : acond_ok (EV xvB) cond_C32.
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & _). unfold cond_C32. cprep. denB. rewrite !lit64_small by lia.
change (32 mod 2 ^ 64) with 32. rewrite Hb32. reflexivity.
Qed.
Lemma okay_conds_ok : okay_false A g i am -> conds_ok (EV xvB) okay_conds.
Proof.
intros (Eall & Hml0 & Hnx & Hsc7 & Hbn). unfold bit in Eall.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof sc48 as Hsc. pose proof (proj1 alloc_ceiling_val).
pose proof mask_self_range as (R1 & R2 & R3 & R4). pose proof (bounces_range Hsc7) as BR.
cbn [okay_conds conds_ok]. repeat split; cprep.
- rewrite U_NMS, U_NALL, Eall. apply Z.eqb_refl.
- denB. rewrite !lit64_small by lia. destruct (Z.ltb_spec 47 (am_sc am)); [lia | reflexivity].
- denB. rewrite !lit64_small by lia. change (12 mod 64) with 12. change (0 mod 2 ^ 64) with 0. rewrite Ebits, bits_shiftr12 by lia.
destruct (Z.eqb_spec (am_maplen am) 0); [lia | reflexivity].
- denB. rewrite Hnx. cbn [optrZ]. fold G. rewrite (Z.mod_small G) by lia. apply Z.eqb_refl.
- denB. rewrite !lit64_small by lia. destruct (Z.ltb_spec 31 (am_sc am + -7)); [lia | reflexivity].
- denB. rewrite (Z.mod_small _ 256) by lia. rewrite !lit64_small by lia. destruct (Z.ltb_spec (znth (am_sc am - 7) (st_bounces A)) 100); [lia | reflexivity].
Qed.
Lemma pconds_ok : conds_ok (EV xvB) (p_conds p).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof sc48 as Hsc.
pose proof mask_self_range as (R1 & R2 & R3 & R4). pose proof usage_range as UR.
assert (Escl : class_size (am_sc am) = 16 * scl_of (am_sc am)).
{ unfold class_size, scl_of, UNIT. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
assert (HSCL : 1 <= scl_of (am_sc am) <= 8191) by (unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); apply scl_range; lia).
destruct p; cbn [toMp pfacts] in PF; cbn [p_conds].
- split; [|exact I]. unfold bit in PF. cprep. rewrite U_NMS, U_NALL. destruct (Z.eqb_spec (sx32 (nt_mask am + 2 ^ i)) (sx32 (ones (am_last am)))) as [E|E]; [|reflexivity].
exfalso. apply PF. exact (proj1 (sx32_inj_u32 _ _ R1 R2) E).
- destruct PF as (OKF & L0 & Hstr & Hus). pose proof OKF as (_ & Hml0 & _). apply conds_ok_app; [apply okay_conds_ok; exact OKF|]. cbn [conds_ok]. repeat split; cprep.
+ denB. unfold UNIT in Hstr. rewrite (Z.mod_small (am_maplen am * 4096)) by lia. rewrite !lit64_small by lia. change (4 mod 64) with 4.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite Z.mod_small by lia.
destruct (Z.ltb_spec (am_maplen am * 4096 + -16) (scl_of (am_sc am) * 16)); [lia | reflexivity].
+ denB. rewrite (Z.mod_small (usage_of A (am_sc am))) by lia. rewrite !lit64_small by lia. change (9 mod 2 ^ 64) with 9. apply Z.ltb_lt. lia.
- destruct PF as (OKF & L0 & Hus). apply conds_ok_app; [apply okay_conds_ok; exact OKF|]. cbn [conds_ok]. repeat split; cprep.
+ denB. rewrite !lit64_small by lia. change (0 mod 2 ^ 64) with 0. destruct (Z.eqb_spec (am_last am) 0); [lia | reflexivity].
+ rewrite U_NINE. denB. rewrite (Z.mod_small (usage_of A (am_sc am))) by lia. rewrite !lit64_small by lia. apply Z.ltb_lt. lia.
- destruct PF as (OKF & L0 & Hus & H18). apply conds_ok_app; [apply okay_conds_ok; exact OKF|]. cbn [conds_ok]. repeat split; cprep.
+ denB. rewrite !lit64_small by lia. change (0 mod 2 ^ 64) with 0. destruct (Z.eqb_spec (am_last am) 0); [lia | reflexivity].
+ rewrite U_NINE. denB. rewrite (Z.mod_small (usage_of A (am_sc am))) by lia. rewrite !lit64_small by lia.
destruct (Z.ltb_spec (usage_of A (am_sc am)) (9 * (am_last am + 1))); [lia | reflexivity].
+ denB. rewrite !lit64_small by lia. change (18 mod 2 ^ 64) with 18. apply Z.ltb_lt. lia.
Qed.
Lemma vconds_ok : conds_ok (EV xvB) (v_conds v).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof sc48 as Hsc. pose proof (proj1 alloc_ceiling_val).
pose proof mask_self_range as (R1 & R2 & R3 & R4). pose proof h_facts as HF.
assert (CM0 : nt_mask am = 0 -> acond_ok (EV xvB) (mkAC BC_EQ NMASK (SLit 0))).
{ intros Hm. cprep. rewrite U_NMASK, U_lit, Hm. reflexivity. }
assert (CSC : acond_ok (EV xvB) (mkAC BC_LTU (SOff aSC 0) (SLit 48))).
{ cprep. denB. rewrite !lit64_small by lia. apply Z.ltb_lt. lia. }
assert (CH : match v with VB4a | VB4b => acond_ok (EV xvB) (mkAC BC_NE (SOff aH 0) (SOff aNG 0)) | _ => True end).
{ destruct v; try exact I; destruct HF as (_ & _ & F1 & F2 & F3 & _ & F5 & EH); cprep; rewrite !(U_off0 _ XR), EH; unfold aNG; rewrite EG; unfold H, G in *;
(destruct (Z.eqb_spec (ptr_addr L h) (ptr_addr L g)); [lia | reflexivity]). }
destruct v; cbn [toMv vfacts] in VF; cbn [v_conds conds_ok].
- split; [|exact I]. cprep. rewrite U_NMASK, U_lit. change (0 mod 2 ^ 64) with 0.
destruct (Z.eqb_spec (sx32 (nt_mask am)) 0) as [E|E]; [|reflexivity]. exfalso. apply VF. exact (proj1 (sx32_zero_iff_u32 _ R3) E).
- destruct VF as (Hm & _). auto.
- destruct VF as (Hm & _). auto.
- destruct VF as (Hm & _). auto.
- destruct VF as (Hm & _). auto.
Qed.
Lemma factsB_ok : facts_ok (EV xvB) (b_facts p v).
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
unfold b_facts, facts_ok. cbn [f_atoms f_conds f_alias]. split; [apply atomsB_ok|]. split; [|apply aliasB_ok].
split; [apply cond_C32_ok|]. apply conds_ok_app; [apply pconds_ok | apply vconds_ok].
Qed.
Lemma M64w z : 0 <= z mod 2 ^ 64 < 2 ^ (8 * Z.of_N 8).
Proof. apply Z.mod_pos_bound. cbn. lia. Qed.
Lemma bytes_are_at' m a a' w x : bytes_are m a w x -> a = a' -> bytes_are m a' w x.
Proof. intros Hb <-. exact Hb. Qed.
Lemma rok_metag : region_ok src0segs (EV xvB) mem (reg_metag_v v).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (BY : forall d w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd g d)) w val) (meta_slot_cells g (Some (MUsed am))) ->
bytes_are mem (G + d) w (sval_num L val)).
{ intros d w val Hv Hc kk Hkk. pose proof (meta_cell g am _ Hu Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
assert (W : forall o, 0 <= o < 40 -> writable_at src0segs mem (G + o)).
{ intros o Ho. apply present_writable. apply (meta_present g am _ Hu). unfold G; lia. }
assert (CH16 : Forall (chunk_ok src0segs (EV xvB) mem G)
[mkChunk 16 (CVal 8 (SOff aGMEM 0)); mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 28 (CVal 4 (SOff aGFR 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))]).
{ repeat apply Forall_cons; [| | | | apply Forall_nil].
- apply (chunk_ok_val _ _ _ _ 8%N _ (ptr_addr L (am_mem am) mod 2 ^ 64)); [apply (U_off0 _ XR) | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. apply (BY 16 8%nat (VP (am_mem am)) I ltac:(cbn; tauto) kk Hkk).
- apply (chunk_ok_val _ _ _ _ 4%N _ (am_avail am)); [apply (U_off0 _ XR) | cbn; lia |]. apply (BY 24 4%nat (VZ (am_avail am)) I ltac:(cbn; tauto)).
- apply (chunk_ok_val _ _ _ _ 4%N _ (am_freed am)); [apply (U_off0 _ XR) | cbn; lia |]. apply (BY 28 4%nat (VZ (am_freed am)) I ltac:(cbn; tauto)).
- apply (chunk_ok_val _ _ _ _ 8%N _ (meta_bits am)); [apply (U_off0 _ XR) | cbn; lia |]. apply (BY 32 8%nat (VZ (meta_bits am)) I ltac:(cbn; tauto)). }
assert (BP : bytes_are mem (G + 0) 8 (optrZ L (am_prev am))).
{ pose proof (BY 0 8%nat (optr (am_prev am)) ltac:(destruct (am_prev am); exact I) ltac:(cbn; tauto)) as B0. unfold optrZ. destruct (am_prev am); exact B0. }
assert (BN : bytes_are mem (G + 8) 8 (optrZ L (am_next am))).
{ pose proof (BY 8 8%nat (optr (am_next am)) ltac:(destruct (am_next am); exact I) ltac:(cbn; tauto)) as B0. unfold optrZ. destruct (am_next am); exact B0. }
destruct v;
(apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_metag_v reg_metag reg_metag0 metag_chunks]; rewrite (base_val_EV _ XR); unfold aNG; rewrite EG; [lia | lia | intros o Ho; apply W; lia |]);
(apply Forall_cons; [|apply Forall_cons; [|exact CH16]]).
1,3: apply (chunk_ok_val _ _ _ _ 8%N _ (optrZ L (am_prev am) mod 2 ^ 64)); [apply (U_off0 _ XR) | apply M64w | intros kk Hkk; rewrite le_byte_mod64; exact (BP kk Hkk)].
1,2: apply (chunk_ok_val _ _ _ _ 8%N _ (optrZ L (am_next am) mod 2 ^ 64)); [apply (U_off0 _ XR) | apply M64w | intros kk Hkk; rewrite le_byte_mod64; exact (BN kk Hkk)].
all: cbn [toMv vfacts] in VF.
all: first [destruct VF as (_ & _ & _ & Hp & Hn & _ & _) | destruct VF as (_ & _ & Hp & Hn)].
all: apply chunk_ok_lit0; intros kk Hkk.
1,3,5: pose proof (BP kk Hkk) as B0; rewrite Hp in B0; cbn [optrZ] in B0; rewrite le_byte_0 in B0; exact B0.
all: pose proof (BN kk Hkk) as B0; rewrite Hn in B0; cbn [optrZ] in B0; rewrite le_byte_0 in B0; exact B0.
Qed.
Lemma rok_got : region_ok src0segs (EV xvB) mem reg_got.
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & ST & _).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_got base_val]; unfold GOT, src0_D_got_stack_chk_guard; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ GUARD); [apply U_lit | cbn; unfold GUARD, src0_D_stack_chk_guard; lia |].
intros kk Hkk. exact (st_got _ _ ST kk Hkk).
Qed.
Lemma rok_guard : region_ok src0segs (EV xvB) mem reg_guard.
Proof.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_guard base_val]; unfold GUARD, src0_D_stack_chk_guard; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (gv mod 2 ^ 64)); [apply (U_off0 _ XR) | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. exact (Hgv kk Hkk).
Qed.
Lemma rok_stk : region_ok src0segs (EV xvB) mem reg_ntstk.
Proof.
pose proof sp_facts as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_ntstk]; rewrite (base_val_EV _ XR); unfold aSP; rewrite ESP; [lia | lia | | apply Forall_nil].
intros o Ho. apply WSTK. lia.
Qed.
Lemma Eact : active_hd A (am_sc am) = nth (Z.to_nat (am_sc am)) (st_active A) None.
Proof. reflexivity. Qed.
Lemma act_bytes : bytes_are mem (xvB aACT + 0) 8 (optrZ L (active_hd A (am_sc am))).
Proof.
pose proof sc48 as Hsc. eapply bytes_are_at'; [apply (ctx_active_cell (Z.to_nat (am_sc am))); lia|].
unfold xvB, aACT. cbn [Nat.ltb Nat.leb]. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma rok_v : Forall (region_ok src0segs (EV xvB) mem) (v_mem v).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof sc48 as Hsc.
pose proof h_facts as HF. pose proof hp_facts as HPF. pose proof act_bytes as AB.
assert (AR : 0x4fdb8 + 80 <= xvB aACT /\ xvB aACT + 392 < 2 ^ 64) by (unfold xvB, aACT; cbn [Nat.ltb Nat.leb]; unfold CTX, src0_D_malloc_context; lia).
assert (AW : forall o, 0 <= o < 8 -> writable_at src0segs mem (xvB aACT + o)).
{ intros o Ho. apply ctx_writable. unfold xvB, aACT. cbn [Nat.ltb Nat.leb]. unfold CTX_SIZE. lia. }
assert (RACT : forall val w, bv_unsigned (sv_denot (EV xvB) val) = optrZ L (active_hd A (am_sc am)) mod 2 ^ 64 ->
region_ok src0segs (EV xvB) mem (reg_act val w)).
{ intros val w Hval. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_act]; rewrite (base_val_EV _ XR); [lia | lia | intros o Ho; apply AW; destruct w; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (optrZ L (active_hd A (am_sc am)) mod 2 ^ 64)); [exact Hval | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. exact (AB kk Hkk). }
destruct v; cbn [v_mem]; cbn [toMv vfacts] in VF.
- apply Forall_nil.
- destruct VF as (_ & Hhd). apply Forall_cons; [|apply Forall_nil]. apply RACT. rewrite (U_off0 _ XR), Hhd. unfold aNG. rewrite EG. cbn [optrZ]. unfold G in *. rewrite Z.mod_small by lia. reflexivity.
- destruct VF as (_ & Hhd & _). apply Forall_cons; [|apply Forall_nil]. apply RACT. rewrite U_lit, Hhd. reflexivity.
- destruct VF as (_ & Hhd & Hhg & _ & _ & Uh & _ & Ehp & _). destruct HF as (_ & _ & F1 & F2 & F3 & F4 & F5 & EH).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ apply RACT. rewrite (U_off0 _ XR), Hhd, EH. cbn [optrZ]. unfold H in *. rewrite Z.mod_small by lia. reflexivity.
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_h2]; rewrite (base_val_EV _ XR), EH; [lia | lia | |].
* intros o Ho. apply present_writable. apply (meta_present h ah _ Uh). unfold H in *. lia.
* apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ H); [rewrite (U_off0 _ XR), EH; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia |].
pose proof (meta_cell h ah _ Uh ltac:(cbn; left; reflexivity)) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C. rewrite Ehp in C. cbn [optr sval_num] in C.
rewrite loc_addr_padd, Z.add_0_r in C. intros kk Hkk. unfold H. rewrite Z.add_0_r. exact (C kk Hkk).
- destruct VF as (_ & Hhd & Hhg & _ & _ & Uh & _ & Ehp & Hph & Hpg & Uhp & _). destruct HF as (_ & _ & F1 & F2 & F3 & F4 & F5 & EH).
destruct HPF as (_ & _ & _ & P1 & P2 & P3 & P4 & P5 & P6 & EHP).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply RACT. rewrite (U_off0 _ XR), Hhd, EH. cbn [optrZ]. unfold H in *. rewrite Z.mod_small by lia. reflexivity.
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_h1]; rewrite (base_val_EV _ XR), EH; [lia | lia | |].
* intros o Ho. apply present_writable. apply (meta_present h ah _ Uh). unfold H in *. lia.
* apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ HP); [rewrite (U_off0 _ XR), EHP; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia |].
pose proof (meta_cell h ah _ Uh ltac:(cbn; left; reflexivity)) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C. rewrite Ehp in C. cbn [optr sval_num] in C.
rewrite loc_addr_padd, Z.add_0_r in C. intros kk Hkk. unfold H. rewrite Z.add_0_r. exact (C kk Hkk).
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_hp]; rewrite (base_val_EV _ XR), EHP; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. apply (meta_present hp ahp _ Uhp). unfold HP in *. lia.
Qed.
Lemma rok_p : Forall (region_ok src0segs (EV xvB) mem) (p_mem p).
Proof.
pose proof sc48 as Hsc. pose proof usage_range as UR.
assert (K : okay_false A g i am -> Forall (region_ok src0segs (EV xvB) mem) [reg_tq2; reg_bnc; reg_usg]).
{ intros (Eall & Hml0 & Hnx & Hsc7 & Hbn). pose proof (bounces_range Hsc7) as BR.
assert (HSCL : 1 <= scl_of (am_sc am) <= 8191) by (unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); apply scl_range; lia).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_tq2]; rewrite (base_val_EV _ XR); unfold xvB, aTQ2; cbn [Nat.ltb Nat.leb]; unfold TBL, src0_D_size_classes; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 2%N _ (scl_of (am_sc am))); [rewrite (U_off0 _ XR); reflexivity | cbn; lia |].
rewrite Z.add_0_r. exact tq_bytes.
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_bnc]; rewrite (base_val_EV _ XR); unfold xvB, aSC; cbn [Nat.ltb Nat.leb]; unfold CTX, src0_D_malloc_context; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 1%N _ (znth (am_sc am - 7) (st_bounces A))); [rewrite (U_off0 _ XR); unfold xvB, aBNC; cbn [Nat.ltb Nat.leb]; apply Z.mod_small; lia | cbn; lia |].
eapply bytes_are_at'; [apply (ctx_bounces_cell (Z.to_nat (am_sc am - 7))); lia|]. unfold CTX, src0_D_malloc_context. rewrite Z2Nat.id by lia. lia.
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_usg]; rewrite (base_val_EV _ XR); unfold xvB, aACT; cbn [Nat.ltb Nat.leb]; unfold CTX, src0_D_malloc_context; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (usage_of A (am_sc am))); [rewrite (U_off0 _ XR); unfold xvB, aUSG; cbn [Nat.ltb Nat.leb]; apply Z.mod_small; lia | cbn; lia |].
eapply bytes_are_at'; [apply (ctx_usage_cell (Z.to_nat (am_sc am))); lia|]. unfold CTX, src0_D_malloc_context. rewrite Z2Nat.id by lia. lia. }
destruct p; cbn [p_mem]; [apply Forall_nil| | |]; apply K; cbn [toMp pfacts] in PF; exact (proj1 PF).
Qed.
Lemma regionsB_ok : Forall (region_ok src0segs (EV xvB) mem) (b_mem p v).
Proof.
unfold b_mem, common_memB. apply Forall_cons; [apply rok_metag|]. apply Forall_cons; [apply rok_got|]. apply Forall_cons; [apply rok_guard|].
apply Forall_cons; [apply rok_stk|]. apply Forall_app_intro; [apply rok_v | apply rok_p].
Qed.
Lemma off_img a0 : (forall x, a0 <= x < a0 + 40 -> ~ in_img B1 x) -> a0 + 40 <= 0x10000 \/ 0x51000 <= a0.
Proof.
intros Ho. destruct (img_gap 0x10000 (0x51000 - 0x10000) a0 40 ltac:(intros x Hx; unfold in_img1; lia) ltac:(lia) Ho ltac:(lia)); lia.
Qed.
Lemma pdB : pairwise_disjoint (EV xvB) (b_mem p v).
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof sc48 as Hsc.
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (off_img G Gimg) as GI.
pose proof h_facts as HF. pose proof hp_facts as HPF.
assert (HH : match v with VB4a | VB4b => 4096 <= H /\ H + 40 <= alloc_ceiling /\ (G + 40 <= H \/ H + 40 <= G) /\ xvB aH = H /\ (H + 40 <= 0x10000 \/ 0x51000 <= H) | _ => True end).
{ destruct v; try exact I; destruct HF as (_ & _ & F1 & F2 & F3 & F4 & F5 & EH); pose proof (off_img H F4); repeat split; auto. }
assert (HHP : match v with VB4b => 4096 <= HP /\ HP + 40 <= alloc_ceiling /\ (G + 40 <= HP \/ HP + 40 <= G) /\ (H + 40 <= HP \/ HP + 40 <= H) /\ xvB aHP = HP /\ (HP + 40 <= 0x10000 \/ 0x51000 <= HP) | _ => True end).
{ destruct v; try exact I. destruct HPF as (_ & _ & _ & P1 & P2 & P3 & P4 & P5 & P6 & EHP); pose proof (off_img HP P4); repeat split; auto. }
clear HF HPF Hi Hav Hfr Hbits Hb32 Hml Gimg.
unfold b_mem, common_memB.
destruct p, v; try discriminate VALID;
cbn [v_mem p_mem app pairwise_disjoint all_disjoint reg_metag_v]; unfold extent_disjoint;
cbn [r_base r_lo r_hi reg_metag reg_metag0 reg_got reg_guard reg_ntstk reg_act reg_h2 reg_h1 reg_hp reg_tq2 reg_bnc reg_usg]; rewrite !(base_val_EV _ XR); cbn [base_val];
unfold aNG, aSP; rewrite EG, ESP;
try (destruct HH as (F1 & F2 & F5 & -> & HI')); try (destruct HHP as (P1 & P2 & P5 & P6 & -> & HPI));
unfold xvB, aACT, aTQ2, aSC; cbn [Nat.ltb Nat.leb];
unfold GOT, GUARD, CTX, TBL, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_malloc_context, src0_D_size_classes; unfold G, H, HP, SP in *;
repeat split; lia.
Qed.
Theorem memB_ok : mem_ok src0segs (EV xvB) mem (b_mem p v).
Proof.
split; [destruct p, v; try discriminate VALID; vm_compute; reflexivity|]. split; [apply regionsB_ok | apply pdB].
Qed.
Theorem ntB_entry_st_ok :
st_ok src0segs (EV xvB) (ss_ntB p v) (mkst regs (Z_to_bv 64 src0_A_nontrivial_free) mem (seg_rom src0segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_ntB resv_denot].
repeat (split; [reflexivity|]). split; [apply regsB_ok|]. split; [apply memB_ok | apply factsB_ok].
Qed.
Definition A' : astate :=
match v with
| VB1 | VB2 => A_B A g i am
| VB3 => A_B3 A g i am
| VB4a => A_B4a A g i am h ah
| VB4b => A_B4b A g i am h hp ah ahp
end.
Definition am' : ameta :=
match v with
| VB1 | VB2 => am_B i am
| VB3 => am_B' i am g g
| VB4a => am_B' i am h h
| VB4b => am_B' i am hp h
end.
Lemma am'_fields :
am_mem am' = am_mem am /\ am_avail am' = am_avail am /\ am_freed am' = Z.lor (am_freed am) (bit i) /\ meta_bits am' = meta_bits am /\
grp_same am am' /\
am_prev am' = match v with VB1 | VB2 => am_prev am | VB3 => Some g | VB4a => Some h | VB4b => Some hp end /\
am_next am' = match v with VB1 | VB2 => am_next am | VB3 => Some g | VB4a | VB4b => Some h end.
Proof. unfold am', am_B, am_B', am_lk, grp_same, meta_bits; destruct v; destruct am; cbn; repeat split; reflexivity. Qed.
Lemma nt_tree_B : nontrivial_free (S fuel) g i A = IRet (None, A').
Proof.
pose proof sc48 as Hsc. rewrite (nt_tree fuel A g i am Mg). rewrite HC1. unfold A'.
destruct v; cbn [toMv vfacts] in VF.
- apply nt_TB_mask_nonzero; [exact Mg | exact VF].
- destruct VF as (Hm & Hhd). apply nt_TB_head; [exact Mg | exact Hm | lia | exact Hhd].
- destruct VF as (Hm & Hhd & Hp & Hn). apply nt_TB_B3; [exact Mg | exact Hm | lia | exact Hhd | exact Hp | exact Hn].
- destruct VF as (Hm & Hhd & Hhg & Hp & Hn & Uh & _ & Ehp & Ehph). apply (nt_TB_B4a A g i am Mg h hp ah Hhg (proj1 (usedX_MT _ _ _ _ Uh))); [rewrite Ehph; exact Ehp | exact Hm | lia | exact Hhd | exact Hp | exact Hn | exact Ehph].
- destruct VF as (Hm & Hhd & Hhg & Hp & Hn & Uh & _ & Ehp & Hph & Hpg & Uhp & _).
apply (nt_TB_B4b A g i am Mg h hp ah ahp Hhg (proj1 (usedX_MT _ _ _ _ Uh)) Ehp (proj1 (usedX_MT _ _ _ _ Uhp)) Hm ltac:(lia) Hhd Hp Hn Hph Hpg).
Qed.
Section t.
Variable ms1 : machine_state.
Hypothesis HS1 : st_ok src0segs (EV xvB) (SSB p v) ms1.
Hypothesis HF1 : frame_of (EV xvB) (b_mem p v) mem (ms_mem ms1).
Hypothesis HI2 : Inv X None U A'.
Let mem1 := ms_mem ms1.
Let regs1 := ms_regs ms1.
Lemma post_shape : ms1 = mkst regs1 (Z_to_bv 64 NT_RET) mem1 (seg_rom src0segs) /\ sr_get (ss_regs (SSB p v)) 1 = SOff 1 0.
Proof.
pose proof (SSB_shape p v VALID) as SH. pose proof HS1 as HS. remember (SSB p v) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _).
split.
- rewrite <- Hpc. apply (st_ok_mkst src0segs _ _ _ HS Hrv).
- unfold callee_view, callee_view0 in Hview. cbn [map] in Hview. injection Hview. auto.
Qed.
Lemma post_regs :
regs_preserved regs regs1 /\ getr regs1 10 = Z_to_bv 64 0 /\ getr regs1 11 = Z_to_bv 64 0.
Proof.
pose proof (SSB_shape p v VALID) as SH. pose proof HS1 as HS. remember (SSB p v) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & H10 & H11 & _).
pose proof (fun r => st_ok_reg src0segs _ _ ms1 r HS) as R.
unfold callee_view, callee_view0 in Hview. cbn [map] in Hview.
injection Hview as V1 V2 V3 V4 V8 V9 V18 V19 V20 V21 V22 V23 V24 V25 V26 V27.
assert (K : forall n (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0), (1 <= n <= 31)%nat -> getr regs1 (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))).
{ intros n V Hn. unfold regs1. rewrite (R (Z_to_bv 5 (Z.of_nat n))), V. cbn [sv_denot EV ew]. rewrite Z.add_0_r. unfold xvB.
replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [nat_to_reg]. rewrite !Z_to_bv_bv_unsigned. f_equal.
clear -Hn. apply bv_eq. rewrite nat_to_reg_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
split; [|split; [unfold regs1; rewrite (R (10%bv : reg)), H10; reflexivity | unfold regs1; rewrite (R (11%bv : reg)), H11; reflexivity]].
intros r Hr. destruct (callee_saved_cases r Hr) as [Hr32 Hin]. rewrite <- (Z2Nat.id r) by lia.
repeat (destruct Hin as [<-|Hin]; [apply K; [assumption | lia] |]). destruct Hin.
Qed.
Lemma footprint_hi e : In e (footprint A) -> loc_addr L (fst e) + snd e <= alloc_ceiling.
Proof.
intros He. pose proof NPRE as (SO' & _ & _ & _ & _ & _ & LG & _).
destruct (In_footprint_inv A e He) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr].
- rewrite Hctx. pose proof (so_ctx_hi _ SO'). unfold CTX. cbn [ms_ctx src0_msyms] in *. lia.
- destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr].
destruct (lg_placed _ _ _ _ LG r rg Hr Hl) as (_ & H1 & H2 & _). unfold PGSZ in *. lia.
- destruct (lg_placed _ _ _ _ LG k r Hr Hl) as (_ & H1 & H2 & _). lia.
Qed.
Lemma footprint_below e x : In e (footprint A) -> loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> 4096 <= x < alloc_ceiling.
Proof.
intros He Hx. pose proof NPRE as (SO' & _ & _ & _ & _ & _ & LG & _).
destruct (In_footprint_inv A e He) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- rewrite Hctx in Hx. pose proof (so_ctx_lo _ SO'). pose proof (so_ctx_hi _ SO'). unfold CTX in Hx. cbn [ms_ctx src0_msyms] in *. lia.
- destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ LG r rg Hr Hl) as (_ & H1 & H2 & _). unfold PGSZ in *. lia.
- destruct (lg_placed _ _ _ _ LG k r Hr Hl) as (_ & H1 & H2 & _). lia.
Qed.
Definition NEWg : list mcell := meta_slot_cells g (Some (MUsed am')).
Definition NEWv : list mcell :=
match v with
| VB1 | VB2 => []
| VB3 => [act_cell (Z.to_nat (am_sc am)) (Some g)]
| VB4a => [MCell (LMem (padd h 0)) 8 (VP g); MCell (LMem (padd h 8)) 8 (VP g)]
| VB4b => [MCell (LMem (padd h 0)) 8 (VP g); MCell (LMem (padd hp 8)) 8 (VP g)]
end.
Definition NEW : list mcell := NEWg ++ NEWv.
Definition in_win (a : Z) : Prop :=
(match v with VB1 | VB2 => G + 28 <= a < G + 32 | _ => G <= a < G + 32 end) \/
(SP - 96 <= a < SP) \/
match v with
| VB3 => xvB aACT <= a < xvB aACT + 8
| VB4a => H <= a < H + 16
| VB4b => (H <= a < H + 8) \/ (HP + 8 <= a < HP + 16)
| _ => False
end.
Lemma wrange_win a : in_wrange (EV xvB) (b_mem p v) a -> in_win a.
Proof.
pose proof h_facts as HF. pose proof hp_facts as HPF.
intros (r & Hr & Ha). unfold b_mem, common_memB in Hr. unfold in_win.
rewrite !in_app_iff in Hr. cbn [In v_mem p_mem] in Hr.
assert (EH : match v with VB4a | VB4b => xvB aH = H | _ => True end) by (destruct v; try exact I; destruct HF as (_&_&_&_&_&_&_& E); exact E).
assert (EHP : match v with VB4b => xvB aHP = HP | _ => True end) by (destruct v; try exact I; destruct HPF as (_&_&_&_&_&_&_&_&_& E); exact E).
destruct Hr as [[<-|[<-|[<-|[<-|[]]]]] | [Hr | Hr]].
- left. destruct v; cbn [reg_metag_v reg_metag reg_metag0 r_base r_wlo r_whi] in Ha; rewrite (base_val_EV _ XR) in Ha; unfold aNG in Ha; rewrite EG in Ha; lia.
- cbn [reg_got r_base r_wlo r_whi base_val] in Ha. lia.
- cbn [reg_guard r_base r_wlo r_whi base_val] in Ha. lia.
- right; left. cbn [reg_ntstk r_base r_wlo r_whi] in Ha. rewrite (base_val_EV _ XR) in Ha. unfold aSP in Ha. rewrite ESP in Ha. lia.
- right; right. destruct v; cbn [In] in Hr;
repeat (destruct Hr as [<-|Hr]); try (destruct Hr; fail); try destruct Hr;
cbn [reg_act reg_h2 reg_h1 reg_hp r_base r_wlo r_whi] in Ha; rewrite (base_val_EV _ XR) in Ha; rewrite ?EH, ?EHP in Ha; lia.
- exfalso. destruct p; cbn [In] in Hr; [destruct Hr| | |];
(destruct Hr as [<-|[<-|[<-|[]]]]; cbn [reg_tq2 reg_bnc reg_usg r_base r_wlo r_whi] in Ha; lia).
Qed.
Lemma frame1 a : 0 <= a < 2 ^ 64 -> ~ in_win a -> mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros Ha Hw. unfold mem1. apply (HF1 (Z_to_bv 64 a)). intros Hin. apply Hw. apply wrange_win. rewrite Z_to_bv_unsigned in Hin.
unfold bv_wrap in Hin. change (bv_modulus 64) with (2 ^ 64) in Hin. rewrite Z.mod_small in Hin by lia. exact Hin.
Qed.
Lemma final_regions :
region_ok src0segs (EV xvB) mem1 (metag_outB v) /\ region_ok src0segs (EV xvB) mem1 reg_ntstk' /\
Forall (region_ok src0segs (EV xvB) mem1) (v_memB_out v).
Proof.
pose proof (SSB_shape p v VALID) as SH. pose proof HS1 as HS. remember (SSB p v) as ss eqn:Ess. clear Ess.
destruct SH as (_ & _ & _ & _ & _ & Hm). pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & ROK & _). rewrite Hm in ROK. unfold memB_out in ROK.
apply Forall_app in ROK as [R1 R2]. apply Forall_app in R2 as [R2 _].
apply Forall_cons_iff in R1 as [Ra R1]. apply Forall_cons_iff in R1 as [_ R1]. apply Forall_cons_iff in R1 as [_ R1]. apply Forall_cons_iff in R1 as [Rs _].
unfold mem1. auto.
Qed.
Lemma old_meta_cell q aq c : usedX X A q aq -> In c (meta_slot_cells q (Some (MUsed aq))) -> In c (imageX X A ++ tail_cellsX X A).
Proof.
intros Huq Hc. apply in_app_iff. left. unfold imageX. apply in_app_iff. right. apply in_app_iff. left.
exact (meta_cells_in_areas X (Some (g, i)) U A HI q aq c (proj1 (usedX_MT _ _ _ _ Huq)) Hc).
Qed.
Lemma len_active : length (st_active A) = 48%nat.
Proof. exact (proj1 (inv_ctx HI)). Qed.
Lemma A'_facts : footprint A' = footprint A /\ st_regions A' = st_regions A /\ st_areas A' = st_areas A /\ MT A' g = Some (MUsed am').
Proof.
unfold A', am', A_B, A_B3, A_B4a, A_B4b. destruct v; rewrite ?footprint_upd_meta, ?MT_upd_same; repeat split; reflexivity.
Qed.
Lemma cellsB c : In c (imageX X A' ++ tail_cellsX X A') -> In c NEW \/ In c (imageX X A ++ tail_cellsX X A).
Proof.
pose proof sc48 as Hsc. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 am'_fields))))) as GS. pose proof len_active as LA.
unfold NEW, NEWg, NEWv. unfold A', am' in *.
assert (T : forall s q a a' c0, MT s q = Some (MUsed a) -> grp_same a a' -> In c0 (tail_cellsX X (upd_meta q (MUsed a') s)) -> In c0 (tail_cellsX X s))
by (intros; eapply tail_cellsX_upd_meta; eauto).
intros Hc. destruct v; cbn [toMv vfacts] in VF; apply in_app_iff in Hc.
- destruct Hc as [Hc|Hc].
+ destruct (imageX_upd_meta X A g am _ c Mg GS Hc) as [H1|H1]; [left; apply in_app_iff; left; exact H1 | right; apply in_app_iff; left; exact H1].
+ right. apply in_app_iff. right. exact (T _ _ _ _ _ Mg GS Hc).
- destruct Hc as [Hc|Hc].
+ destruct (imageX_upd_meta X A g am _ c Mg GS Hc) as [H1|H1]; [left; apply in_app_iff; left; exact H1 | right; apply in_app_iff; left; exact H1].
+ right. apply in_app_iff. right. exact (T _ _ _ _ _ Mg GS Hc).
- unfold A_B3 in Hc. destruct Hc as [Hc|Hc].
+ destruct (imageX_upd_meta X _ g am _ c ltac:(rewrite MT_set_active; exact Mg) GS Hc) as [H1|H1]; [left; apply in_app_iff; left; exact H1 |].
unfold act_g in H1. destruct (imageX_set_active X A (Z.to_nat (am_sc am)) (Some g) c ltac:(rewrite LA; lia) H1) as [H2|H2]; [left; apply in_app_iff; right; left; symmetry; exact H2 | right; apply in_app_iff; left; exact H2].
+ right. apply in_app_iff. right. rewrite <- (tail_cellsX_set_active X A (act_g A g am)). exact (T _ _ _ _ _ ltac:(rewrite MT_set_active; exact Mg) GS Hc).
- destruct VF as (Hm & Hhd & Hhg & Hp & Hn & Uh & _). pose proof (proj1 (usedX_MT _ _ _ _ Uh)) as Mh.
assert (Mg' : MT (upd_meta h (MUsed (ah_a g ah)) A) g = Some (MUsed am)) by (rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg).
unfold A_B4a in Hc. destruct Hc as [Hc|Hc].
+ destruct (imageX_upd_meta X _ g am _ c Mg' GS Hc) as [H1|H1]; [left; apply in_app_iff; left; exact H1 |].
destruct (imageX_upd_meta X A h ah _ c Mh (grp_same_links _ _ ah) H1) as [H2|H2]; [| right; apply in_app_iff; left; exact H2].
cbn [meta_slot_cells ah_a am_set_links am_prev am_next am_mem am_avail am_freed optr] in H2.
destruct H2 as [<-|[<-|H2]]; [left; apply in_app_iff; right; cbn; tauto | left; apply in_app_iff; right; cbn; tauto |].
right. apply (old_meta_cell h ah _ Uh). cbn [meta_slot_cells optr]. replace (meta_bits (am_set_links (Some g) (Some g) ah)) with (meta_bits ah) in H2 by (destruct ah; reflexivity). cbn in H2 |- *. tauto.
+ right. apply in_app_iff. right. exact (T _ _ _ _ _ Mh (grp_same_links _ _ ah) (T _ _ _ _ _ Mg' GS Hc)).
- destruct VF as (Hm & Hhd & Hhg & Hp & Hn & Uh & _ & Ehp & Hph & Hpg & Uhp & _). pose proof (proj1 (usedX_MT _ _ _ _ Uh)) as Mh. pose proof (proj1 (usedX_MT _ _ _ _ Uhp)) as Mhp.
assert (Mh' : MT (upd_meta hp (MUsed (ahp_b g ahp)) A) h = Some (MUsed ah)) by (rewrite MT_upd_other by (intros E; exact (Hph (eq_sym E))); exact Mh).
assert (Mg' : MT (upd_meta h (MUsed (ah_b g ah)) (upd_meta hp (MUsed (ahp_b g ahp)) A)) g = Some (MUsed am)).
{ rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))). rewrite MT_upd_other by (intros E; exact (Hpg (eq_sym E))). exact Mg. }
unfold A_B4b in Hc. destruct Hc as [Hc|Hc].
+ destruct (imageX_upd_meta X _ g am _ c Mg' GS Hc) as [H1|H1]; [left; apply in_app_iff; left; exact H1 |].
destruct (imageX_upd_meta X _ h ah _ c Mh' (grp_same_links _ _ ah) H1) as [H2|H2].
* cbn [meta_slot_cells ah_b am_set_links am_prev am_next am_mem am_avail am_freed optr] in H2.
destruct H2 as [<-|H2]; [left; apply in_app_iff; right; cbn; tauto |].
right. apply (old_meta_cell h ah _ Uh). cbn [meta_slot_cells optr]. replace (meta_bits (am_set_links (Some g) (am_next ah) ah)) with (meta_bits ah) in H2 by (destruct ah; reflexivity). cbn in H2 |- *. tauto.
* destruct (imageX_upd_meta X A hp ahp _ c Mhp (grp_same_links _ _ ahp) H2) as [H3|H3]; [| right; apply in_app_iff; left; exact H3].
cbn [meta_slot_cells ahp_b am_set_links am_prev am_next am_mem am_avail am_freed optr] in H3.
destruct H3 as [H3|[<-|H3]]; [| left; apply in_app_iff; right; cbn; tauto |].
-- right. apply (old_meta_cell hp ahp _ Uhp). cbn [meta_slot_cells]. left. exact H3.
-- right. apply (old_meta_cell hp ahp _ Uhp). cbn [meta_slot_cells optr]. replace (meta_bits (am_set_links (am_prev ahp) (Some g) ahp)) with (meta_bits ahp) in H3 by (destruct ahp; reflexivity). cbn in H3 |- *. tauto.
+ right. apply in_app_iff. right. exact (T _ _ _ _ _ Mhp (grp_same_links _ _ ahp) (T _ _ _ _ _ Mh' (grp_same_links _ _ ah) (T _ _ _ _ _ Mg' GS Hc))).
Qed.
Lemma new_home n : In n NEW -> In n (areas_cells A' (st_areas A')) \/ In n (ctx_cells A').
Proof.
pose proof sc48 as Hsc. pose proof len_active as LA. pose proof A'_facts as (_ & _ & _ & Mg').
intros Hn. unfold NEW in Hn. apply in_app_iff in Hn as [Hn|Hn].
- left. exact (slot_cells_in_areas X None U A' HI2 g (MUsed am') n Mg' Hn).
- unfold NEWv in Hn. unfold A' in *. destruct v; cbn [toMv vfacts] in VF; try (destruct Hn; fail).
+ destruct Hn as [<-|[]]. right. unfold A_B3. rewrite ctx_cells_upd_meta. unfold act_g. apply act_cell_In; [lia | exact LA].
+ destruct VF as (Hm & Hhd & Hhg & _). left. apply (slot_cells_in_areas X None U _ HI2 h (MUsed (ah_a g ah))).
* unfold A_B4a. rewrite MT_upd_other by exact Hhg. apply MT_upd_same.
* cbn. destruct Hn as [<-|[<-|[]]]; tauto.
+ destruct VF as (Hm & Hhd & Hhg & Hp & Hn' & Uh & _ & Ehp & Hph & Hpg & Uhp & _). left. destruct Hn as [<-|[<-|[]]].
* apply (slot_cells_in_areas X None U _ HI2 h (MUsed (ah_b g ah))); [|cbn; tauto].
unfold A_B4b. rewrite MT_upd_other by exact Hhg. apply MT_upd_same.
* apply (slot_cells_in_areas X None U _ HI2 hp (MUsed (ahp_b g ahp))); [|cbn; tauto].
unfold A_B4b. rewrite MT_upd_other by exact Hpg. rewrite MT_upd_other by exact Hph. apply MT_upd_same.
Qed.
Lemma chunk8_cell base off e z loc (val : sval) :
chunk_ok src0segs (EV xvB) mem1 base (mkChunk off (CVal 8 e)) ->
bv_unsigned (sv_denot (EV xvB) e) = z mod 2 ^ 64 -> loc_addr L loc = base + off -> sval_num L val = z ->
match val with VLo5 _ => False | _ => True end ->
cell_mem B1 L mem1 (MCell loc 8 val).
Proof.
intros Hc Hv Hloc Hval Hnl. unfold cell_mem. cbn [mc_val mc_loc mc_w]. rewrite Hloc.
assert (K : forall k, (k < 8)%nat -> mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte z 8 k))).
{ intros k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word. rewrite Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z_to_bv8_mod. reflexivity. }
destruct val; cbn [sval_num] in Hval |- *; rewrite ?Hval; first [exact K | destruct Hnl].
Qed.
Lemma chunk4_cell_sx base off e y loc :
chunk_ok src0segs (EV xvB) mem1 base (mkChunk off (CVal 4 e)) ->
bv_unsigned (sv_denot (EV xvB) e) = sx32 y -> 0 <= y -> loc_addr L loc = base + off ->
cell_mem B1 L mem1 (MCell loc 4 (VZ y)).
Proof.
intros Hc Hv Hy Hloc. unfold cell_mem. cbn [mc_val mc_loc mc_w sval_num]. rewrite Hloc. intros k Hk.
enough (E : mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte y 4 k))) by exact E.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word. rewrite Hv. apply byte_sx32; [exact Hy | exact Hk].
Qed.
Lemma chunk4_cell base off e y loc :
chunk_ok src0segs (EV xvB) mem1 base (mkChunk off (CVal 4 e)) ->
bv_unsigned (sv_denot (EV xvB) e) = y -> 0 <= y < 2 ^ 32 -> loc_addr L loc = base + off ->
cell_mem B1 L mem1 (MCell loc 4 (VZ y)).
Proof.
intros Hc Hv Hy Hloc. unfold cell_mem. cbn [mc_val mc_loc mc_w sval_num]. rewrite Hloc. intros k Hk.
enough (E : mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte y 4 k))) by exact E.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word, le_byte. rewrite Hv, Z_to_bv8_mod. f_equal. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma U_NFREED : bv_unsigned (sv_denot (EV xvB) NFREED) = sx32 (Z.lor (am_freed am) (bit i)).
Proof.
unfold NFREED. change (sv_denot (EV xvB) (SAlu ALU_OR (SExt true 32 (SOff aGFR 0)) NSELF)) with (alu64 ALU_OR (sv_denot (EV xvB) (SExt true 32 (SOff aGFR 0))) (sv_denot (EV xvB) NSELF)).
rewrite alu64_or, U_sext32, (U_off0 _ XR), U_NSELF. unfold aGFR, xvB. cbn [Nat.ltb Nat.leb]. unfold bit. apply lor_sx32.
Qed.
Definition e0 : sv := match v with VB1 | VB2 => SOff aPREV 0 | VB3 => SOff aNG 0 | VB4a => SOff aH 0 | VB4b => SOff aHP 0 end.
Definition e8 : sv := match v with VB1 | VB2 => SOff aNEXT 0 | VB3 => SOff aNG 0 | VB4a | VB4b => SOff aH 0 end.
Lemma chunks_g :
let CH off w e := chunk_ok src0segs (EV xvB) mem1 G (mkChunk off (CVal w e)) in
CH 0 8%N e0 /\ CH 8 8%N e8 /\ CH 16 8%N (SOff aGMEM 0) /\ CH 24 4%N (SOff aGAV 0) /\ CH 28 4%N NFREED /\ CH 32 8%N (SOff aGBITS 0) /\
(forall o, (match v with VB1 | VB2 => 28 | _ => 0 end) <= o < 32 -> writable_at src0segs mem1 (G + o)).
Proof.
destruct final_regions as (Rg & _ & _). unfold e0, e8. destruct v; cbn [metag_outB] in Rg; destruct Rg as (_ & _ & W & C);
cbn [r_base r_wlo r_whi r_chunks] in W, C; rewrite (base_val_EV _ XR) in W, C; unfold aNG in W, C; rewrite EG in W, C;
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H] end; cbn zeta; repeat split; assumption.
Qed.
Lemma val_e0 : bv_unsigned (sv_denot (EV xvB) e0) = optrZ L (am_prev am') mod 2 ^ 64.
Proof.
pose proof am'_fields as (_ & _ & _ & _ & _ & -> & _). pose proof h_facts as HF. pose proof hp_facts as HPF. pose proof g_facts as (_&_&_&_&_&_&G1&G2&_). pose proof (proj1 alloc_ceiling_val).
unfold e0; destruct v; rewrite (U_off0 _ XR); cbn [optrZ].
- reflexivity.
- reflexivity.
- unfold aNG. rewrite EG. unfold G. symmetry. apply Z.mod_small. unfold G in *. lia.
- destruct HF as (_&_&F1&F2&_&_&_& ->). unfold H in *. symmetry. apply Z.mod_small. lia.
- destruct HPF as (_&_&_&P1&P2&_&_&_&_& ->). unfold HP in *. symmetry. apply Z.mod_small. lia.
Qed.
Lemma val_e8 : bv_unsigned (sv_denot (EV xvB) e8) = optrZ L (am_next am') mod 2 ^ 64.
Proof.
pose proof am'_fields as (_ & _ & _ & _ & _ & _ & ->). pose proof h_facts as HF. pose proof g_facts as (_&_&_&_&_&_&G1&G2&_). pose proof (proj1 alloc_ceiling_val).
unfold e8; destruct v; rewrite (U_off0 _ XR); cbn [optrZ].
- reflexivity.
- reflexivity.
- unfold aNG. rewrite EG. unfold G. symmetry. apply Z.mod_small. unfold G in *. lia.
- destruct HF as (_&_&F1&F2&_&_&_& ->). unfold H in *. symmetry. apply Z.mod_small. lia.
- destruct HF as (_&_&F1&F2&_&_&_& ->). unfold H in *. symmetry. apply Z.mod_small. lia.
Qed.
Lemma optr_facts (o : option sptr) : sval_num L (optr o) = optrZ L o /\ match optr o with VLo5 _ => False | _ => True end.
Proof. destruct o; cbn; auto. Qed.
Lemma new_mem n : In n NEW -> cell_mem B1 L mem1 n.
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof sc48 as Hsc. pose proof (proj1 alloc_ceiling_val).
pose proof am'_fields as (Fm & Fav & Ffr & Fbits & _).
pose proof chunks_g as (C0 & C8 & C16 & C24 & C28 & C32 & _).
intros Hn. unfold NEW in Hn. apply in_app_iff in Hn as [Hn|Hn].
- unfold NEWg in Hn. cbn [meta_slot_cells] in Hn. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hn.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
+ destruct (optr_facts (am_prev am')) as [E1 E2]. eapply (chunk8_cell G 0 e0 _ _ _ C0 val_e0); [rewrite loc_addr_padd; reflexivity | exact E1 | exact E2].
+ destruct (optr_facts (am_next am')) as [E1 E2]. eapply (chunk8_cell G 8 e8 _ _ _ C8 val_e8); [rewrite loc_addr_padd; reflexivity | exact E1 | exact E2].
+ rewrite Fm. eapply (chunk8_cell G 16 _ _ _ _ C16); [rewrite (U_off0 _ XR); reflexivity | rewrite loc_addr_padd; reflexivity | reflexivity | exact I].
+ rewrite Fav. eapply (chunk4_cell G 24 _ _ _ C24); [rewrite (U_off0 _ XR); reflexivity | lia | rewrite loc_addr_padd; reflexivity].
+ rewrite Ffr. eapply (chunk4_cell_sx G 28 _ _ _ C28 U_NFREED); [apply Z.lor_nonneg; split; [lia | unfold bit; apply Z.pow_nonneg; lia] | rewrite loc_addr_padd; reflexivity].
+ rewrite Fbits. eapply (chunk8_cell G 32 _ _ _ _ C32); [rewrite (U_off0 _ XR); unfold aGBITS, xvB; cbn [Nat.ltb Nat.leb]; symmetry; apply Z.mod_small; lia | rewrite loc_addr_padd; reflexivity | reflexivity | exact I].
- destruct final_regions as (_ & _ & Rv). pose proof h_facts as HF. pose proof hp_facts as HPF.
unfold NEWv in Hn. destruct v; cbn [v_memB_out] in Rv; try (destruct Hn; fail).
+ apply Forall_cons_iff in Rv as [Ra _].
destruct Hn as [<-|[]]. destruct Ra as (_ & _ & _ & C). cbn [r_base r_chunks reg_act] in C. rewrite (base_val_EV _ XR) in C. apply Forall_cons_iff in C as [C _].
unfold act_cell. eapply (chunk8_cell _ 0 _ _ _ _ C); [rewrite (U_off0 _ XR); unfold aNG; rewrite EG; symmetry; apply Z.mod_small; unfold G in *; lia | | reflexivity | exact I].
cbn [loc_addr]. rewrite Hctx. unfold xvB, aACT, CTX_active. cbn [Nat.ltb Nat.leb]. rewrite Z2Nat.id by lia. lia.
+ apply Forall_cons_iff in Rv as [_ Rv]. apply Forall_cons_iff in Rv as [Rb _].
destruct HF as (_&_&F1&F2&_&_&_& EH). destruct Rb as (_ & _ & _ & C). cbn [r_base r_chunks] in C. rewrite (base_val_EV _ XR), EH in C.
apply Forall_cons_iff in C as [Ca C]. apply Forall_cons_iff in C as [Cb _].
destruct Hn as [<-|[<-|[]]].
* eapply (chunk8_cell _ 0 _ _ _ _ Ca); [rewrite (U_off0 _ XR); unfold aNG; rewrite EG; symmetry; apply Z.mod_small; unfold G in *; lia | rewrite loc_addr_padd; reflexivity | reflexivity | exact I].
* eapply (chunk8_cell _ 8 _ _ _ _ Cb); [rewrite (U_off0 _ XR); unfold aNG; rewrite EG; symmetry; apply Z.mod_small; unfold G in *; lia | rewrite loc_addr_padd; reflexivity | reflexivity | exact I].
+ apply Forall_cons_iff in Rv as [_ Rv]. apply Forall_cons_iff in Rv as [Rb Rv]. apply Forall_cons_iff in Rv as [Rc _].
destruct HF as (_&_&F1&F2&_&_&_& EH). destruct HPF as (_&_&_&P1&P2&_&_&_&_& EHP).
destruct Rb as (_ & _ & _ & Ca). cbn [r_base r_chunks reg_h1] in Ca. rewrite (base_val_EV _ XR), EH in Ca. apply Forall_cons_iff in Ca as [Ca _].
destruct Rc as (_ & _ & _ & Cb). cbn [r_base r_chunks reg_hp'] in Cb. rewrite (base_val_EV _ XR), EHP in Cb. apply Forall_cons_iff in Cb as [Cb _].
destruct Hn as [<-|[<-|[]]].
* eapply (chunk8_cell _ 0 _ _ _ _ Ca); [rewrite (U_off0 _ XR); unfold aNG; rewrite EG; symmetry; apply Z.mod_small; unfold G in *; lia | rewrite loc_addr_padd; reflexivity | reflexivity | exact I].
* eapply (chunk8_cell _ 8 _ _ _ _ Cb); [rewrite (U_off0 _ XR); unfold aNG; rewrite EG; symmetry; apply Z.mod_small; unfold G in *; lia | rewrite loc_addr_padd; reflexivity | reflexivity | exact I].
Qed.
Lemma off_img_present x o (m : word -> option byte) :
(forall y, x <= y < x + 40 -> ~ in_img B1 y) -> 4096 <= x -> x + 40 <= alloc_ceiling -> 0 <= o < 40 ->
writable_at src0segs m (x + o) -> present m (x + o).
Proof.
pose proof (proj1 alloc_ceiling_val). intros Himg Hx1 Hx2 Ho W. apply writable_off_img_present; [lia | | exact W].
intros I1. apply (Himg (x + o)); [lia|]. apply in_img1_in_img. exact I1.
Qed.
Lemma present_g a : G <= a < G + 40 -> present mem1 a.
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof sc48 as Hsc.
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (off_img G Gimg) as GI.
pose proof h_facts as HF. pose proof hp_facts as HPF. pose proof chunks_g as (_ & _ & _ & _ & _ & _ & Wg).
intros Ha.
destruct (Z_le_dec (match v with VB1 | VB2 => G + 28 | _ => G end) a) as [L1|L1]; [destruct (Z_lt_dec a (G + 32)) as [L2|L2]|].
- replace a with (G + (a - G)) by lia. apply (off_img_present G (a - G) mem1 Gimg G1 G2); [lia|]. apply Wg. destruct v; lia.
-
destruct (meta_present g am a Hu ltac:(unfold G in Ha; lia)) as [b Hb]. exists b. rewrite <- Hb. apply frame1; [lia|].
unfold in_win. intros [W | [W | W]]; [destruct v; lia | lia |].
destruct v; try exact W.
+ unfold xvB, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX, src0_D_malloc_context in W. lia.
+ destruct HF as (_&_&F1&F2&F3&F4&F5&_). lia.
+ destruct HF as (_&_&F1&F2&F3&F4&F5&_). destruct HPF as (_&_&_&P1&P2&P3&P4&P5&P6&_). lia.
- destruct (meta_present g am a Hu ltac:(unfold G in Ha; lia)) as [b Hb]. exists b. rewrite <- Hb. apply frame1; [lia|].
unfold in_win. intros [W | [W | W]]; [destruct v; lia | lia |].
destruct v; try exact W.
+ unfold xvB, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX, src0_D_malloc_context in W. lia.
+ destruct HF as (_&_&F1&F2&F3&F4&F5&_). lia.
+ destruct HF as (_&_&F1&F2&F3&F4&F5&_). destruct HPF as (_&_&_&P1&P2&P3&P4&P5&P6&_). lia.
Qed.
Lemma new_present n k : In n NEW -> (k < mc_w n)%nat -> (exists q, mc_loc n = LMem q) -> present mem1 (loc_addr L (mc_loc n) + Z.of_nat k).
Proof.
pose proof h_facts as HF. pose proof hp_facts as HPF. destruct final_regions as (_ & _ & Rv).
intros Hn Hk [q Hq]. unfold NEW in Hn. apply in_app_iff in Hn as [Hn|Hn].
- apply present_g. unfold NEWg in Hn. cbn [meta_slot_cells] in Hn. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hn.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd; unfold G; lia.
- unfold NEWv in Hn. destruct v; try (destruct Hn; fail); cbn [v_memB_out] in Rv.
+ destruct Hn as [<-|[]]. cbn in Hq. discriminate.
+ apply Forall_cons_iff in Rv as [_ Rv]. apply Forall_cons_iff in Rv as [Rb _]. destruct HF as (Uh&_&F1&F2&F3&F4&_& EH).
destruct Rb as (_ & _ & W & _). cbn [r_base r_wlo r_whi] in W. rewrite (base_val_EV _ XR), EH in W.
destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd; fold H.
* replace (H + 0 + Z.of_nat k) with (H + Z.of_nat k) by lia. apply (off_img_present H _ mem1 F4 F1 F2); [lia|]. apply W. lia.
* replace (H + 8 + Z.of_nat k) with (H + (8 + Z.of_nat k)) by lia. apply (off_img_present H _ mem1 F4 F1 F2); [lia|]. apply W. lia.
+ apply Forall_cons_iff in Rv as [_ Rv]. apply Forall_cons_iff in Rv as [Rb Rv]. apply Forall_cons_iff in Rv as [Rc _].
destruct HF as (Uh&_&F1&F2&F3&F4&_& EH). destruct HPF as (Uhp&_&_&P1&P2&P3&P4&_&_& EHP).
destruct Rb as (_ & _ & Wb & _). cbn [r_base r_wlo r_whi reg_h1] in Wb. rewrite (base_val_EV _ XR), EH in Wb.
destruct Rc as (_ & _ & Wc & _). cbn [r_base r_wlo r_whi reg_hp'] in Wc. rewrite (base_val_EV _ XR), EHP in Wc.
destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd.
* fold H. replace (H + 0 + Z.of_nat k) with (H + Z.of_nat k) by lia. apply (off_img_present H _ mem1 F4 F1 F2); [lia|]. apply Wb. lia.
* fold HP. replace (HP + 8 + Z.of_nat k) with (HP + (8 + Z.of_nat k)) by lia. apply (off_img_present HP _ mem1 P4 P1 P2); [lia|]. apply Wc. lia.
Qed.
Lemma win_covered a :
in_win a -> (SP - 96 <= a < SP) \/ exists n, In n NEW /\ in_range a (cell_range L n).
Proof.
pose proof h_facts as HF. pose proof hp_facts as HPF. pose proof sc48 as Hsc.
assert (NG : forall c, In c (meta_slot_cells g (Some (MUsed am'))) -> In c NEW) by (intros c Hc; unfold NEW, NEWg; apply in_app_iff; left; exact Hc).
assert (NV : forall c, In c NEWv -> In c NEW) by (intros c Hc; unfold NEW; apply in_app_iff; right; exact Hc).
assert (RG : forall d w val, In (MCell (LMem (padd g d)) w val) (meta_slot_cells g (Some (MUsed am'))) -> G + d <= a < G + d + Z.of_nat w ->
exists n, In n NEW /\ in_range a (cell_range L n)).
{ intros d w val Hc Ha. exists (MCell (LMem (padd g d)) w val). split; [apply NG; exact Hc|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. unfold G in Ha. lia. }
intros [W | [W | W]]; [right | left; exact W | right].
- assert (K : G + 0 <= a < G + 0 + Z.of_nat 8 \/ G + 8 <= a < G + 8 + Z.of_nat 8 \/ G + 16 <= a < G + 16 + Z.of_nat 8 \/ G + 24 <= a < G + 24 + Z.of_nat 4 \/ G + 28 <= a < G + 28 + Z.of_nat 4) by (destruct v; lia).
cbn [meta_slot_cells] in RG. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in RG.
destruct K as [K|[K|[K|[K|K]]]]; (eapply RG; [| exact K]); cbn; tauto.
- unfold NEWv in NV. destruct v; try (destruct W; fail).
+ exists (act_cell (Z.to_nat (am_sc am)) (Some g)). split; [apply NV; left; reflexivity|].
unfold act_cell, in_range, cell_range. cbn [mc_loc mc_w fst snd loc_addr]. rewrite Hctx. unfold xvB, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX_active. rewrite Z2Nat.id by lia. lia.
+ assert (K : H + 0 <= a < H + 0 + 8 \/ H + 8 <= a < H + 8 + 8) by lia. destruct K as [K|K].
* exists (MCell (LMem (padd h 0)) 8 (VP g)). split; [apply NV; cbn; tauto|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. unfold H in K. lia.
* exists (MCell (LMem (padd h 8)) 8 (VP g)). split; [apply NV; cbn; tauto|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. unfold H in K. lia.
+ destruct W as [K|K].
* exists (MCell (LMem (padd h 0)) 8 (VP g)). split; [apply NV; cbn; tauto|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. unfold H in K. lia.
* exists (MCell (LMem (padd hp 8)) 8 (VP g)). split; [apply NV; cbn; tauto|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. unfold HP in K. lia.
Qed.
Lemma win_owned a : in_win a -> (SP - 96 <= a < SP) \/ alloc_owned L A a.
Proof.
pose proof h_facts as HF. pose proof hp_facts as HPF. pose proof sc48 as Hsc.
intros [W | [W | W]]; [right | left; exact W | right].
- apply (meta_bytes_owned X (Some (g, i)) U A L HI HL g _ (MUsed am) Mg). unfold META_SIZE. unfold G in W. destruct v; lia.
- destruct v; try (destruct W; fail).
+ apply (ctx_bytes_owned X (Some (g, i)) U A L HI HL). rewrite Hctx. unfold xvB, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX_SIZE. lia.
+ destruct HF as (Uh & _). apply (meta_bytes_owned X (Some (g, i)) U A L HI HL h _ (MUsed ah) (proj1 (usedX_MT _ _ _ _ Uh))). unfold META_SIZE. unfold H in W. lia.
+ destruct HF as (Uh & _). destruct HPF as (Uhp & _). destruct W as [W|W].
* apply (meta_bytes_owned X (Some (g, i)) U A L HI HL h _ (MUsed ah) (proj1 (usedX_MT _ _ _ _ Uh))). unfold META_SIZE. unfold H in W. lia.
* apply (meta_bytes_owned X (Some (g, i)) U A L HI HL hp _ (MUsed ahp) (proj1 (usedX_MT _ _ _ _ Uhp))). unfold META_SIZE. unfold HP in W. lia.
Qed.
Lemma in_win_dec a : in_win a \/ ~ in_win a.
Proof.
unfold in_win. destruct v;
repeat match goal with |- context [?x <= a < ?y] =>
lazymatch goal with
| H : (x <= a < y) \/ ~ (x <= a < y) |- _ => fail
| _ => assert ((x <= a < y) \/ ~ (x <= a < y)) by lia
end end; tauto.
Qed.
Theorem memrep1 : memrepX B1 X L A' mem1.
Proof.
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof A'_facts as (Efp & Erg & _).
refine (memrepX_after B1 X X (Some (g, i)) None U U A A' L mem mem1 NEW [] (SP - 96, 96) HI HI2 HL Efp Erg MR cellsB new_home new_mem new_present _ _ _ _).
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. pose proof (footprint_hi e He). lia.
- intros a Ha Hno _ Hns.
assert (NW : ~ in_win a).
{ intros W. destruct (win_covered a W) as [S | (n & Hn & Hin)]; [apply Hns; unfold in_range; cbn [fst snd]; lia | exact (Hno n Hn Hin)]. }
pose proof (frame1 a Ha NW) as E. split; [exact (proj1 (same_byte_views mem mem1 a E))|].
intros [b Hb]. exists b. rewrite E. exact Hb.
Qed.
Lemma statics1 : statics_ok B1 mem1.
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & ST & _). pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (off_img G Gimg) as GI. pose proof sc48 as Hsc. pose proof h_facts as HF. pose proof hp_facts as HPF.
apply (statics_ok_ext B1 mem mem1 ST). intros x Hs.
assert (R : 0x10000 <= x < 0x51000).
{ unfold static_owned in Hs. cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B1 src0_msyms] in Hs.
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs. lia. }
enough (NW : ~ in_win x) by exact (proj1 (same_byte_views mem mem1 x (frame1 x ltac:(lia) NW))).
intros W. destruct W as [W|[W|W]]; [destruct v; lia | lia |].
destruct v; try exact W.
- unfold xvB, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX, src0_D_malloc_context in W.
unfold static_owned in Hs. cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B1 src0_msyms] in Hs.
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs. lia.
- destruct HF as (_&_&F1&F2&F3&F4&F5&_). pose proof (off_img H F4). lia.
- destruct HF as (_&_&F1&F2&F3&F4&F5&_). destruct HPF as (_&_&_&P1&P2&P3&P4&P5&P6&_). pose proof (off_img H F4). pose proof (off_img HP P4). lia.
Qed.
Theorem ntB_post :
nt_post B1 X (S fuel) L A regs mem md (None, A') (mkCfg (mkst regs1 (getr regs 1) mem1 (seg_rom src0segs)) md).
Proof.
pose proof sp_facts as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml).
pose proof sc48 as Hsc. pose proof h_facts as HF. pose proof hp_facts as HPF.
destruct post_regs as (RP & R10 & R11). destruct final_regions as (_ & Rs & _).
exists regs1, mem1. split; [reflexivity|]. split; [apply memrep1|]. split; [apply statics1|]. split; [exact RP|].
split; [exact R10|]. split; [exact R11|]. unfold NT_FRAME. fold SP. split.
- intros a Ha NO NS.
assert (NW : ~ in_win a) by (intros W; destruct (win_owned a W) as [W'|W']; [apply NS; lia | exact (NO W')]).
exact (same_byte_views mem mem1 a (frame1 a Ha NW)).
- intros a Ha. destruct (Z_le_dec (SP - 96) a) as [L1|L1].
+ destruct Rs as (_ & _ & W & _). cbn [r_base r_wlo r_whi reg_ntstk'] in W. rewrite (base_val_EV _ XR) in W. unfold aSP in W. rewrite ESP in W.
replace a with (SP + (a - SP)) by lia. apply W. lia.
+ assert (NW : ~ in_win a).
{ intros [W|[W|W]]; [destruct v; lia | lia |]. destruct v; try exact W.
- unfold xvB, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX, src0_D_malloc_context in W. lia.
- destruct HF as (_&_&F1&F2&_). lia.
- destruct HF as (_&_&F1&F2&_). destruct HPF as (_&_&_&P1&P2&_). lia. }
apply (writable_same mem mem1 a (frame1 a ltac:(lia) NW)). apply WSTK. lia.
Qed.
End t.
Theorem ntB_mreal :
Inv X None U A' ->
mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_nontrivial_free) mem (seg_rom src0segs)) md)
(nontrivial_free (S fuel) g i A) (nt_post B1 X (S fuel) L A regs mem md).
Proof.
intros HI2. pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & Hh & Hlz & Hmat & _ & _ & Hret & _).
rewrite nt_tree_B. cbn [mreal].
eapply SR_bind; [eapply (ntB_run p v _ _ md VALID ntB_entry_st_ok Hh Hlz)|].
intros c1 (ms1 & -> & HS1 & HF1).
destruct (post_shape ms1 HS1) as [Ems Hra].
eapply (SR_nt_ret (EV xvB) (SSB p v) ms1 md _ HS1).
- exact (proj1 (proj2 (SSB_shape p v VALID))).
- exact (proj1 (SSB_shape p v VALID)).
- exact Hra.
- cbn [EV ew]. unfold xvB. cbn [Nat.ltb Nat.leb nat_to_reg]. rewrite Z_to_bv_bv_unsigned. exact Hret.
- exact Hh.
- exact Hlz.
- cbn [EV ew]. unfold xvB at 1. cbn [Nat.ltb Nat.leb nat_to_reg]. rewrite Z_to_bv_bv_unsigned. cbn [ms_mem mkst] in HF1.
exact (ntB_post ms1 HS1 HF1 HI2).
Qed.
End l.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
