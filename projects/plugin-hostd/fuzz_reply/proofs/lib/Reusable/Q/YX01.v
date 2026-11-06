From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN03 YN02 YN2b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN0b YN07 YN0a YN1q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW0e YX00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record small_ctx (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region) : Prop := SCX {
sx_pre : call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md;
sx_used : usedX [] A g am;
sx_idx : 0 <= idx <= am_last am;
sx_fr : ss_fr (nth_slot am idx) = Some fr;
sx_kind : fr_kind fr = FUser;
sx_in : In (frame_ptr am idx fr, fr_n fr) (user_blocks A);
sx_a0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am idx fr));
sx_a1 : getr regs 11 = Z_to_bv 64 n;
sx_n : 0 <= n < 2 ^ 62;
sx_sc : am_sc am < 48;
sx_area : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka);
sx_rg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg }.
Definition nS (n : Z) : Z := if n <? MMAP_THRESHOLD then n else 0.
Definition kkS (n : Z) : Z := (nS n + 3) / 16.
Definition vS (L : layout) (regs : bvmap 5 word) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (a : sptr) (rg : YO0i.region) : fvals :=
fv_of regs L g am idx fr a (rg_len rg).
Definition xvS (L : layout) (regs : bvmap 5 word) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (a : sptr) (rg : YO0i.region) (n : Z) (k : nat) : Z :=
if (k <? 96)%nat then xvf (vS L regs g am idx fr a rg) k
else match k with
| 109%nat => ptr_addr L (frame_ptr am idx fr) + n
| 112%nat => ptr_addr L (am_mem am) + stride_of am * idx
| 113%nat => kkS n
| 114%nat => t0_e (kkS n)
| 115%nat => 2 ^ t0_e (kkS n)
| 116%nat => DEBR + dbj_idx (2 ^ t0_e (kkS n))
| 117%nat => t0_t1 (kkS n)
| 118%nat => SCTR + 2 * (4 * t0_e (kkS n) - 3)
| 119%nat => znth (t0_i3 (kkS n)) size_classes
| 120%nat => SCTR + 2 * t0_i3 (kkS n)
| 121%nat => size_to_class (nS n)
| _ => 0
end.
Definition ES (L : layout) (regs : bvmap 5 word) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (a : sptr) (rg : YO0i.region) (n : Z) : env :=
EV (xvS L regs g am idx fr a rg n).
Definition nc_facts (nc : ncase) : facts := mkFacts (nc_atoms nc) (nc_conds nc) (nc_alias nc).
Definition avail_of (am : ameta) (fr : frame) : Z := stride_of am - IB - UNIT * fr_off fr.
Definition nc_ok (am : ameta) (fr : frame) (n : Z) (nc : ncase) : Prop :=
match nc with
| NBig => MMAP_THRESHOLD <= n
| NOver => n < MMAP_THRESHOLD /\ avail_of am fr < n
| NSmall ge => n < 157 /\ n <= avail_of am fr /\ ge = (am_sc am <=? size_to_class n + 1)
| NMid b1 ge => 157 <= n < MMAP_THRESHOLD /\ n <= avail_of am fr /\ b1 = t0_b1 (kkS n) /\ ge = (am_sc am <=? size_to_class n + 1)
end.
Lemma nc_cover am fr n : 0 <= n -> exists nc, nc_ok am fr n nc.
Proof.
intros Hn. destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hm|Hm]; [|exists NBig; exact Hm].
destruct (Z_lt_le_dec (avail_of am fr) n) as [Ha|Ha]; [exists NOver; split; assumption|].
destruct (Z_lt_le_dec n 157) as [Hs|Hs].
- exists (NSmall (am_sc am <=? size_to_class n + 1)). cbn. auto.
- exists (NMid (t0_b1 (kkS n)) (am_sc am <=? size_to_class n + 1)). cbn. auto.
Qed.
Lemma nc_c1 am fr n nc : nc_ok am fr n nc ->
ra_c1 am (fr_off fr) n = match nc with NSmall ge | NMid _ ge => ge | _ => false end.
Proof.
unfold ra_c1. change (stride_of am - IB - UNIT * fr_off fr) with (avail_of am fr).
destruct nc as [| |ge|b1 ge]; cbn; intros H.
- replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; exact H). rewrite andb_false_r. reflexivity.
- destruct H as [_ H]. replace (n <=? avail_of am fr) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity.
- destruct H as (H1 & H2 & ->). replace (n <=? avail_of am fr) with true by (symmetry; apply Z.leb_le; exact H2).
replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; unfold MMAP_THRESHOLD; lia). reflexivity.
- destruct H as (H1 & H2 & _ & ->). replace (n <=? avail_of am fr) with true by (symmetry; apply Z.leb_le; exact H2).
replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma ptr_addr_padd' Lx p d : ptr_addr Lx (padd p d) = ptr_addr Lx p + d.
Proof. destruct p as [rr o]. unfold ptr_addr, loc_addr, padd. lia. Qed.
Lemma znth_sc_range i : 0 <= znth i size_classes <= 8191.
Proof.
unfold znth. assert (F : Forall (fun x => 0 <= x <= 8191) size_classes) by (repeat constructor; lia).
destruct (nth_in_or_default (Z.to_nat i) size_classes 0) as [H|H]; [|rewrite H; lia].
rewrite Forall_forall in F. exact (F _ H).
Qed.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation V := (vS L regs g am idx fr a rg).
Local Abbreviation XV := (xvS L regs g am idx fr a rg n).
Local Abbreviation E := (ES L regs g am idx fr a rg n).
Lemma MXS : MRx src0_msyms L A mem md.
Proof using HC. exact (proj1 (sx_pre _ _ _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.
Lemma MS : MRc src0_msyms L A mem md.
Proof using HC. exact (MRx_MRc _ _ _ _ _ MXS). Qed.
Lemma HWS : WF A.
Proof using HC. exact (mc_wf _ _ _ _ _ MS). Qed.
Lemma FPS : free_pre (kcase_of am) (rcase_of (reserved_of am fr)) V mem.
Proof using HC.
destruct HC as [PRE Hu Hidx Hfr Hk Hin Ha0 Ha1 Hn Hsc Harea Hrg].
pose proof PRE as (MX' & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _).
unfold vS. eapply free_pre_intro; try eassumption.
- exact (MRx_MRc _ _ _ _ _ MX').
- exact (MRx_rsv _ _ _ _ _ MX').
- unfold REALLOC_STACK, ALLOC_STACK in *. repeat split; lia.
- intros x Hx. apply Hstk. unfold REALLOC_STACK, ALLOC_STACK in *. lia.
Qed.
Lemma kc_small : kcase_of am <> K3b.
Proof using HC.
pose proof (sx_sc _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as H. unfold kcase_of.
replace (am_sc am =? 63) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (am_maplen am =? 0); [discriminate|]. destruct (am_last am =? 0); discriminate.
Qed.
Lemma P_range : 4096 <= ptr_addr L (frame_ptr am idx fr) /\ ptr_addr L (frame_ptr am idx fr) + fr_n fr < alloc_ceiling /\
ptr_addr L (frame_ptr am idx fr) = ptr_addr L (am_mem am) + UNIT + stride_of am * idx + UNIT * fr_off fr /\
4096 <= ptr_addr L (am_mem am) /\ 0 <= fr_off fr /\ 0 <= fr_n fr /\ 16 <= stride_of am.
Proof using HC.
pose proof FPS as FP. pose proof (fp_grp _ _ _ _ FP) as GR. pose proof (fp_vals _ _ _ _ FP) as VL.
pose proof (stride_pos _ _ _ _ _ (inv_groups HWS g am (sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC))) as Sp.
pose proof (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hidx.
pose proof (inv_groups HWS g am (sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & Gsl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite (sx_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HC) in S3. destruct S3 as (_ & _ & (F1 & F2 & _) & _).
assert (ESS : ptr_addr L (frame_ptr am idx fr) = ptr_addr L (am_mem am) + UNIT + stride_of am * idx + UNIT * fr_off fr).
{ unfold frame_ptr, slot_start. rewrite !ptr_addr_padd'. lia. }
change (fv_glo V) with (ly_reg L (prid (am_mem am))) in GR. change (fv_mem V) with (ptr_addr L (am_mem am)) in GR, VL.
change (fv_pn V) with (ptr_addr L (frame_ptr am idx fr) + fr_n fr) in GR, VL.
unfold CEIL in GR. destruct GR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
assert (0 <= stride_of am * idx) by nia. unfold UNIT in *. repeat split; lia.
Qed.
Lemma XS : forall k, 0 <= XV k < 2 ^ 64.
Proof using HC.
pose proof FPS as FP. pose proof (xvf_range _ _ _ _ FP) as XR.
pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
pose proof YM05.alloc_ceiling_lt as HCV.
pose proof (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hidx.
pose proof P_range as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
assert (0 <= stride_of am * idx) by nia.
assert (Kk : 0 <= kkS n <= 8190).
{ unfold kkS, nS. destruct (n <? MMAP_THRESHOLD) eqn:E0.
- apply Z.ltb_lt in E0. unfold MMAP_THRESHOLD in E0. split; [apply Z.div_pos; lia|].
assert ((n + 3) / 16 < 8191) by (apply Z.div_lt_upper_bound; lia). lia.
- change ((0 + 3) / 16) with 0. lia. }
assert (Ke : 0 <= t0_e (kkS n) <= 12).
{ unfold t0_e. split; [apply Z.log2_nonneg|]. change 12 with (Z.log2 8191). apply Z.log2_le_mono. lia. }
assert (Kp : 1 <= 2 ^ t0_e (kkS n) <= 4096).
{ split; [change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia|]. change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; lia. }
assert (Ki3 : -4 <= t0_i3 (kkS n) <= 46) by (unfold t0_i3; destruct (t0_b1 (kkS n)); lia).
assert (Kc : 0 <= size_to_class (nS n) < 48).
{ apply (proj1 (size_to_class_range (nS n) ltac:(unfold nS; destruct (n <? MMAP_THRESHOLD) eqn:E0; [apply Z.ltb_lt in E0|]; unfold MMAP_THRESHOLD in *; lia))). }
pose proof (dbj_idx_range (2 ^ t0_e (kkS n))) as Kd.
pose proof (znth_sc_range (t0_i3 (kkS n))) as Kz.
pose proof (znth_sc_range (4 * t0_e (kkS n) - 3)) as Kt.
intros k. unfold xvS. destruct (k <? 96)%nat eqn:Ek; [apply XR|].
unfold DEBR, SCTR, src0_D_debruijn32, src0_D_size_classes, t0_t1 in *.
do 96 (destruct k as [|k]; [discriminate|]).
do 13 (destruct k as [|k]; [cbv beta iota; lia|]).
destruct k as [|k]; [cbv beta iota; lia|].
do 2 (destruct k as [|k]; [cbv beta iota; lia|]).
destruct k as [|k]; [cbv beta iota; unfold UNIT in *; lia|].
do 9 (destruct k as [|k]; [cbv beta iota; lia|]).
cbv beta iota; lia.
Qed.
Lemma ES_agree : env_agree 96 (EV (xvf V)) E.
Proof using.
split; [|reflexivity]. intros k Hk96. unfold ES, EV. cbn [ew]. unfold xvS.
replace (k <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk96). reflexivity.
Qed.
Lemma XS_reg k : (k <= 31)%nat -> XV k = bv_unsigned (getr regs (nat_to_reg k)).
Proof using. intros Hk. unfold xvS. replace (k <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply xvf_reg. exact Hk. Qed.
Lemma XS_P : XV aP = ptr_addr L (frame_ptr am idx fr).
Proof using HC.
rewrite XS_reg by (cbv; lia). change (nat_to_reg aP) with (10%bv : bv 5). rewrite (sx_a0 _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
apply lit64_small. pose proof P_range as (P1 & P2 & _ & _ & _ & P6 & _). pose proof YM05.alloc_ceiling_lt. lia.
Qed.
Lemma XS_SP : XV aSP = spZ regs.
Proof using. rewrite XS_reg by (cbv; lia). reflexivity. Qed.
Lemma XS_N : XV aN = n.
Proof using HC.
rewrite XS_reg by (cbv; lia). change (nat_to_reg aN) with (11%bv : bv 5). rewrite (sx_a1 _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
apply lit64_small. pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.
End b.
End a.
