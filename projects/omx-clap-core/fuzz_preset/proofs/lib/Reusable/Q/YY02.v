(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_rgb_fuzzer/lib/YO11.v, with its module paths, module names and numbers changed; 642 of its 955 lines of code are new or changed and 747 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YP0n YM06 YK0s YM02 YK1j YK1a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN03 YN02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN2b YN25 YN26 YN28.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN0b YN07 YN0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW0e YW05 YW06 YW07 YW0b YY00 YY01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Suggest Proof Using.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma lit5 k : (1 <= k <= 31)%nat -> Z_to_bv 5 (Z.of_nat k) = nat_to_reg k.
Proof using. intros Hk. rewrite (Z_to_bv5_nat_to_reg (Z.of_nat k)) by lia. rewrite Nat2Z.id. reflexivity. Qed.
End f.
Ltac vnth H i V := pose proof (f_equal (fun l => List.nth i l (SLit 0)) H) as V; cbn [List.nth] in V;
try (rewrite lit5 in V by lia; cbn [nat_to_reg] in V).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma regs_ok_intro E0 sr rs : nth 0 sr (SLit 0) = SLit 0 ->
(forall i, (1 <= i <= 31)%nat -> getr rs (nat_to_reg i) = sv_denot E0 (nth i sr (SLit 0))) -> regs_ok E0 sr rs.
Proof using.
intros H0 H r. unfold sr_get. pose proof (u5_range r) as Hr. destruct (bv_eqb r 0) eqn:Eq.
- unfold getr. rewrite Eq. reflexivity.
- assert (Hr0 : bv_unsigned r <> 0).
{ intros Z0. assert (r = 0%bv) as -> by (apply bv_eq; exact Z0). rewrite bv_eqb_refl in Eq. discriminate. }
unfold ridx. rewrite <- (nat_to_reg_ridx r) at 1. apply H. lia.
Qed.
Lemma anyblock_off_img L0 A0 m0 md0 q k x : MRc src0_msyms L0 A0 m0 md0 -> In (q, k) (user_blocks A0) ->
ptr_addr L0 q <= x < ptr_addr L0 q + k -> ~ in_img1 x.
Proof using.
intros M0 Hq Hx Hi. destruct (block_region A0 q k (mc_wf _ _ _ _ _ M0) Hq) as (kr & o & rg0 & Ep & Hrg0 & _ & Hl0 & Ho & Hk & Hon & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M0) kr rg0 Hrg0 Hl0) as (_ & _ & _ & Himg).
apply (Himg x); [| apply in_img1_in_img; exact Hi]. unfold ptr_addr in Hx. rewrite Ep in Hx. cbn [loc_addr] in Hx. lia.
Qed.
Lemma errno_img x : ERRNO2 <= x < ERRNO2 + 4 -> in_img1 x.
Proof using. intros Hx. apply src0_img_range. apply src0_errno_img. exact Hx. Qed.
Lemma owned_img_any L0 A0 m0 md0 L' A' m' md' x :
MRc src0_msyms L0 A0 m0 md0 -> MRc src0_msyms L' A' m' md' -> in_img src0_msyms x ->
owned src0_msyms L' A' x -> owned src0_msyms L0 A0 x.
Proof using.
intros M0 M' Hi [[(e & He & Hxe) Hnb] | Hs]; [| right; exact Hs]. left.
destruct (In_footprint_inv A' e He) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hxe.
- split.
+ exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. rewrite (mc_ctx _ _ _ _ _ M0). rewrite (mc_ctx _ _ _ _ _ M') in Hxe. exact Hxe.
+ intros (b & Hb & Hxb). destruct b as [bp bk]. cbn [fst snd] in Hxb. unfold loc_addr in Hxb.
apply (anyblock_off_img L0 A0 m0 md0 bp bk x M0 Hb); [unfold ptr_addr, loc_addr; exact Hxb | apply src0_img_range; exact Hi].
- exfalso. destruct (inv_areas (mc_wf _ _ _ _ _ M')) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg0 & -> & _ & Ho & Hr & Hl & Hlen0 & _). cbn [loc_addr] in Hxe.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M') r rg0 Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold PGSZ in *; lia | exact Hi].
- exfalso. destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M') k r Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [lia | exact Hi].
Qed.
Lemma frame_chunks_slots c : In c frame_chunks ->
exists o r, c = mkChunk o (CVal 8 (SOff r 0)) /\ In (o, r) FB_SLOTS /\ (1 <= r <= 31)%nat /\ -64 <= o /\ o + 8 <= 0.
Proof using.
unfold frame_chunks. cbn [In]. intros Hc.
repeat (destruct Hc as [<-|Hc]; [do 2 eexists; split; [reflexivity|]; split; [unfold FB_SLOTS; cbn [In]; repeat (first [left; reflexivity | right]) | lia] |]).
destruct Hc.
Qed.
Lemma ptr_neq_of_split (l1 l2 : list (sptr * Z)) q k p k' :
List.NoDup (map fst (l1 ++ (q, k) :: l2)) -> In (p, k') (l1 ++ l2) -> q <> p.
Proof using.
intros ND Hin ->. rewrite map_app in ND. cbn [map fst] in ND. apply NoDup_remove_2 in ND. apply ND.
rewrite <- map_app. apply (in_map fst _ _ Hin).
Qed.
Section FB.
Hypothesis MALLOC : malloc_impl_realizes.
Hypothesis FREE : free_impl_realizes.
Hypothesis MEMCPY : memcpy_spec.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (nold n : Z) (regs4 : bvmap 5 word) (mem4 : word -> option byte).
Hypothesis FA : fb_arrival L A regs mem md p nold n regs4 mem4.
Let PRE := fa_pre _ _ _ _ _ _ _ _ _ _ FA.
Let Hin : In (p, nold) (user_blocks A) := fa_in _ _ _ _ _ _ _ _ _ _ FA.
Let MX : MRx src0_msyms L A mem md := proj1 PRE.
Let M : MRc src0_msyms L A mem md := MRx_MRc _ _ _ _ _ MX.
Let HW : WF A := mc_wf _ _ _ _ _ M.
Definition SPa : Z := spZ regs.
Definition Pa : Z := ptr_addr L p.
Definition STKa (x : Z) : Prop := SPa - 8256 <= x < SPa.
Definition ERRa (x : Z) : Prop := ERRNO2 <= x < ERRNO2 + 4.
Definition Ma : Z := Z.min n nold.
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof using M. exact (mc_md _ _ _ _ _ M). Qed.
Lemma PREf : YK0s.ret_ok (getr regs 1) /\ SPa mod 16 = 0 /\ alloc_ceiling + 8256 <= SPa /\ SPa < 2 ^ 63 /\
(forall x, STKa x -> writable_at src0segs mem x) /\ getr regs 4 = Z_to_bv 64 src0_tp /\
(forall x, ERRa x -> writable_at src0segs mem x).
Proof using PRE.
pose proof PRE as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
unfold REALLOC_STACK, ALLOC_STACK in *. unfold STKa, ERRa, SPa.
repeat split; auto.
Qed.
Lemma Hinit : st_init_done A = true. Proof using HW Hin. exact (init_done_of_block A _ HW Hin). Qed.
Lemma Hn : 0 <= n < 2 ^ 62. Proof using FA. exact (fa_n _ _ _ _ _ _ _ _ _ _ FA). Qed.
Lemma Pblk : 4096 <= Pa /\ 0 <= nold /\ Pa + nold <= alloc_ceiling /\ Pa mod 16 = 0 /\
(forall i, 0 <= i < nold -> present mem (Pa + i) /\ ~ owned src0_msyms L A (Pa + i)).
Proof using HW Hin.
pose proof (mr_blocks_range _ _ (MRx_laws src0_msyms) L A mem md _ _ MX Hin) as [H1 H2].
destruct (block_region A p nold HW Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & Hk & _).
split; [exact H1|]. split; [exact Hk|]. split; [exact H2|].
split; [exact (mr_blocks_aligned _ _ (MRx_laws src0_msyms) L A mem md _ _ MX Hin)|]. intros i Hi.
pose proof (mr_blocks _ _ (MRx_laws src0_msyms) L A mem md _ _ i MX Hin Hi) as (Q1 & _ & _ & Q4). auto.
Qed.
Lemma STK_fb x : fb_stk regs x <-> STKa x.
Proof using. unfold fb_stk, STKa, SPa, REALLOC_STACK, ALLOC_STACK. lia. Qed.
Lemma RAW4 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ~ ERRa x -> mem4 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof using FA.
intros x Hx N1 N2. apply (fa_raw _ _ _ _ _ _ _ _ _ _ FA x Hx); [rewrite STK_fb; exact N1 | exact N2].
Qed.
Definition xg (rs : bvmap 5 word) (nv q : Z) (k : nat) : Z :=
if ((64 <=? k) && (k <? 96))%nat then bv_unsigned (getr rs (nat_to_reg (k - 64)))
else if (k =? 101)%nat then nv else if (k =? 102)%nat then q
else if ((1 <=? k) && (k <=? 31))%nat then bv_unsigned (getr regs (nat_to_reg k)) else 0.
Lemma xg_range rs nv q : 0 <= nv < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> forall k, 0 <= xg rs nv q k < 2 ^ 64.
Proof using.
intros Hnv Hq k. unfold xg. destruct ((64 <=? k) && (k <? 96))%nat; [apply u64_range|].
destruct (k =? 101)%nat; [lia|]. destruct (k =? 102)%nat; [lia|].
destruct ((1 <=? k) && (k <=? 31))%nat; [apply u64_range | lia].
Qed.
Lemma xg_reg rs nv q i : (1 <= i <= 31)%nat -> xg rs nv q i = bv_unsigned (getr regs (nat_to_reg i)).
Proof using.
intros Hi. unfold xg. replace ((64 <=? i) && (i <? 96))%nat with false.
2:{ symmetry. apply andb_false_iff. left. apply Nat.leb_gt. lia. }
replace (i =? 101)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (i =? 102)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace ((1 <=? i) && (i <=? 31))%nat with true; [reflexivity|].
symmetry. apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.
Lemma xg_junk rs nv q i : (i < 32)%nat -> xg rs nv q (64 + i) = bv_unsigned (getr rs (nat_to_reg i)).
Proof using.
intros Hi. unfold xg. replace ((64 <=? 64 + i) && (64 + i <? 96))%nat with true.
2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia. }
f_equal. f_equal. f_equal. lia.
Qed.
Lemma xg_nv rs nv q : xg rs nv q aNOLD = nv. Proof using. reflexivity. Qed.
Lemma xg_q rs nv q : xg rs nv q aQ = q. Proof using. reflexivity. Qed.
Lemma xg_SP rs nv q : xg rs nv q aSP = SPa. Proof using. reflexivity. Qed.
Lemma xg_P rs nv q : xg rs nv q aP = Pa.
Proof using HW Hin.
unfold aP. rewrite xg_reg by lia. change (nat_to_reg 10) with (10%bv : bv 5).
rewrite (fa_a0 _ _ _ _ _ _ _ _ _ _ FA). apply lit64_small.
pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val. unfold Pa in *. lia.
Qed.
Lemma xg_N rs nv q : xg rs nv q aN = n.
Proof using FA.
unfold aN. rewrite xg_reg by lia. change (nat_to_reg 11) with (11%bv : bv 5).
rewrite (fa_a1 _ _ _ _ _ _ _ _ _ _ FA). apply lit64_small. pose proof Hn. lia.
Qed.
Lemma xg_TP rs nv q : xg rs nv q aTP = src0_tp.
Proof using PRE.
unfold aTP. rewrite xg_reg by lia. change (nat_to_reg 4) with (4%bv : bv 5).
destruct PREf as (_ & _ & _ & _ & _ & -> & _). apply lit64_small. unfold src0_tp. lia.
Qed.
Section env.
Variables (rs : bvmap 5 word) (nv q : Z).
Hypothesis Hnv : 0 <= nv < 2 ^ 64.
Hypothesis Hq : 0 <= q < 2 ^ 64.
Let XR := xg_range rs nv q Hnv Hq.
Lemma den_regG i : (1 <= i <= 31)%nat -> sv_denot (EV (xg rs nv q)) (SOff i 0) = getr regs (nat_to_reg i).
Proof using XR. intros Hi. rewrite (den_off0 _ XR), (xg_reg rs nv q i Hi). apply Z_to_bv_bv_unsigned. Qed.
Lemma den_junkG i : (i < 32)%nat -> sv_denot (EV (xg rs nv q)) (junk i) = getr rs (nat_to_reg i).
Proof using XR. intros Hi. unfold junk. rewrite (den_off0 _ XR), (xg_junk rs nv q i Hi). apply Z_to_bv_bv_unsigned. Qed.
Lemma den_xg k : sv_denot (EV (xg rs nv q)) (SOff k 0) = Z_to_bv 64 (xg rs nv q k).
Proof using XR. exact (den_off0 _ XR k). Qed.
Lemma ew_xg k : bv_unsigned (ew (EV (xg rs nv q)) k) = xg rs nv q k.
Proof using XR. exact (ew_EV _ XR k). Qed.
Lemma base_SPG : base_val (EV (xg rs nv q)) (Some aSP) = SPa.
Proof using XR. rewrite (base_val_EV _ XR). apply xg_SP. Qed.
Lemma frame_chunks_of m : (forall x, SPa - 64 <= x < SPa -> mbyte src0segs m x = mbyte src0segs mem4 x) ->
Forall (chunk_ok src0segs (EV (xg rs nv q)) m SPa) frame_chunks.
Proof using FA XR.
intros EQ. apply Forall_forall. intros c Hc. destruct (frame_chunks_slots c Hc) as (o & r & -> & Hs & Hr & O1 & O2).
intros i Hi. cbn [c_len c_val cv_len] in Hi. change (Z.of_N 8) with 8 in Hi.
exists (byte_of_word (getr regs (nat_to_reg r)) i). split.
- cbn [cbyte c_val c_off]. rewrite den_regG by exact Hr. reflexivity.
- cbn [c_off]. rewrite EQ by lia. apply (fa_frame _ _ _ _ _ _ _ _ _ _ FA o r i Hs Hi).
Qed.
Lemma mem_ok_at m : Forall (chunk_ok src0segs (EV (xg rs nv q)) m SPa) frame_chunks ->
(forall x, STKa x -> writable_at src0segs m x) -> mem_ok src0segs (EV (xg rs nv q)) m after_memR.
Proof using PRE XR.
intros C W. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
split; [vm_compute; reflexivity|]. split; [| cbn; tauto].
apply Forall_cons; [| apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite base_SPG; [lia | lia | | exact C].
intros o Ho. apply W. unfold STKa. lia.
Qed.
Lemma atoms_okG : 0 <= nv <= 2 ^ 62 - 1 -> 4096 <= q <= CEIL_MAX -> q mod 16 = 0 ->
atoms_ok (EV (xg rs nv q)) atomsG.
Proof using HW Hin XR.
intros Hnv' Hq1 Hq2.
pose proof PREf as (_ & Hal & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val. pose proof Pblk as (P1 & P0 & P2 & P3 & _). pose proof Hn.
unfold atomsG. cbn [atoms_ok f_atoms]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite !ew_xg, xg_SP, xg_TP, xg_P, xg_N, xg_nv, xg_q.
unfold CEIL, src0_tp in *. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
rewrite ?Z.mod_1_r. repeat match goal with |- _ /\ _ => split | |- True => exact I end; try lia.
all: try reflexivity.
Qed.
Lemma alias_oldG : nv = nold -> alias_ok (EV (xg rs nv q)) [ALIAS_OLD].
Proof using HW Hin XR.
intros Env. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val.
split; [| exact I]. apply (proj2 (word_eq _ _)). unfold ALIAS_OLD. cbn [fst snd sv_denot].
rewrite alu64_sub, alu64_add, !ew_xg, !Z.add_0_r, xg_nv, xg_P, Env.
rewrite !lit64_small by lia. unfold add64, sub64. rewrite (Z.mod_small (Pa + nold)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
End env.
Definition cM : branch_cond := if nold <=? n then BC_GEU else BC_LTU.
Lemma cM_cases : cM = BC_GEU \/ cM = BC_LTU.
Proof using. unfold cM. destruct (nold <=? n); [left | right]; reflexivity. Qed.
Lemma cond_okM rs q : 0 <= q < 2 ^ 64 -> conds_ok (EV (xg rs nold q)) [mkAC cM (SOff aN 0) (SOff aNOLD 0)].
Proof using HW Hin.
intros Hq. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val. pose proof Hn.
assert (Hnv : 0 <= nold < 2 ^ 64) by lia.
split; [| exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite !(den_xg rs nold q Hnv Hq), xg_N, xg_nv. unfold cM.
destruct (Z.leb_spec nold n); cbn [branch_taken]; rewrite bv_ltu_unsigned, !lit64_small by lia.
- apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
- apply Z.ltb_lt. lia.
Qed.
Lemma mlen_M rs q : 0 <= q < 2 ^ 64 -> sv_denot (EV (xg rs nold q)) (mlen cM) = Z_to_bv 64 Ma.
Proof using HW Hin.
intros Hq. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val.
assert (Hnv : 0 <= nold < 2 ^ 64) by lia.
unfold cM, Ma. destruct (Z.leb_spec nold n); cbn [mlen]; rewrite (den_xg rs nold q Hnv Hq).
- rewrite xg_nv. f_equal. lia.
- rewrite xg_N. f_equal. lia.
Qed.
Lemma MRx_frame_gen L0 A0 m0 m1 md0 (dlo dhi : Z) :
let D := fun x => dlo <= x < dhi in
MRx src0_msyms L0 A0 m0 md0 -> alloc_ceiling + 8256 <= SPa ->
(forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ~ ERRa x -> ~ D x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
(forall x, D x -> ~ owned src0_msyms L0 A0 x /\ (present m0 x -> present m1 x)) ->
MRx src0_msyms L0 A0 m1 md0.
Proof using.
intros D MX0 Hceil RAW HD. pose proof (MRx_MRc _ _ _ _ _ MX0) as M0. destruct (mc_md _ _ _ _ _ M0) as (Hh & Hlz & Hmat).
pose proof YM05.alloc_ceiling_val as HCV.
assert (OW : forall x, owned src0_msyms L0 A0 x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)).
{ intros x Ho. pose proof (owned_low _ L0 A0 m0 md0 x M0 Ho). apply RAW; [lia | unfold STKa; intro; lia | |].
- intros He. exact (src0_errno_not_owned L0 A0 m0 md0 x M0 He Ho).
- intros HDx. exact (proj1 (HD x HDx) Ho). }
eapply (mr_frame _ _ (MRx_laws src0_msyms)); [exact MX0 | | | | reflexivity | exact Hh | exact Hlz | exact Hmat].
- intros x Ho. apply (proj1 (same_byte_views2 m0 m1 x (OW x Ho))).
- intros x Ho Hp. exact (present_same m0 m1 x (OW x Ho) Hp).
- intros q k i Hq Hi. pose proof (mr_blocks _ _ (MRx_laws src0_msyms) L0 A0 m0 md0 q k i MX0 Hq Hi) as (Hp & Hlo & Hhi & _).
assert (DEC : D (ptr_addr L0 q + i) \/ ~ D (ptr_addr L0 q + i)) by (subst D; cbn beta; lia).
destruct DEC as [HDx | HDx]; [exact (proj2 (HD _ HDx) Hp)|].
apply (present_same m0 m1); [| exact Hp]. apply RAW; [lia | unfold STKa; intro; lia | | exact HDx].
intros He. exact (anyblock_off_img L0 A0 m0 md0 q k (ptr_addr L0 q + i) M0 Hq ltac:(lia) (errno_img _ He)).
Qed.
Lemma MRx_scratch L0 A0 m0 m1 md0 :
MRx src0_msyms L0 A0 m0 md0 -> alloc_ceiling + 8256 <= SPa ->
(forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ~ ERRa x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
MRx src0_msyms L0 A0 m1 md0.
Proof using.
intros MX0 Hceil RAW. apply (MRx_frame_gen L0 A0 m0 m1 md0 0 0 MX0 Hceil).
- intros x Hx N1 N2 _. exact (RAW x Hx N1 N2).
- intros x Hx. exfalso. lia.
Qed.
Lemma R4 : getr regs4 1 = Z_to_bv 64 RA_MALLOC /\ getr regs4 2 = Z_to_bv 64 (SPa - 64) /\
getr regs4 4 = getr regs 4 /\ getr regs4 10 = Z_to_bv 64 n.
Proof using FA.
split; [exact (fa_ra _ _ _ _ _ _ _ _ _ _ FA)|]. split; [exact (fa_sp _ _ _ _ _ _ _ _ _ _ FA)|].
split; [exact (fa_keep _ _ _ _ _ _ _ _ _ _ FA 4%nat ltac:(cbn; tauto)) | exact (fa_arg _ _ _ _ _ _ _ _ _ _ FA)].
Qed.
Lemma pre4 : call_pre src0_msyms (MRx src0_msyms) L A regs4 mem4 md.
Proof using HW Hin.
pose proof PREf as (Hret & Hal & Hceil & H63 & Hstk & Htp & Herrw). pose proof R4 as (R1 & R2 & Rtp & _).
pose proof PRE as (_ & _ & HB & _). pose proof YM05.alloc_ceiling_val.
assert (ESP : spZ regs4 = SPa - 64) by (unfold spZ; rewrite R2; apply lit64_small; lia).
unfold call_pre. rewrite ESP. split; [exact (MRx_scratch L A mem mem4 md MX Hceil RAW4)|].
split; [exact HW|]. split; [exact HB|]. split; [rewrite R1; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite <- Zminus_mod_idemp_l, Hal; reflexivity|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
split; [intros x Hx; apply (fa_stk _ _ _ _ _ _ _ _ _ _ FA); rewrite STK_fb; unfold STKa, ALLOC_STACK in *; lia|].
split; [rewrite Rtp; exact Htp|]. split; [intros x Hx; apply (fa_err _ _ _ _ _ _ _ _ _ _ FA); exact Hx|].
intros Hf. rewrite Hinit in Hf. discriminate.
Qed.
Lemma malloc_call :
mreal src0segs (mkCfg (mkst regs4 (Z_to_bv 64 src0_A_libc_malloc_impl) mem4 (seg_rom src0segs)) md) (malloc n A)
(fun r c => malloc_leaf src0_msyms (MRx src0_msyms) L A regs4 mem4 md n r c /\
(length (st_regions A) <= length (st_regions (snd r)))%nat).
Proof using HW Hin MALLOC.
apply mreal_tall; [| apply malloc_regions_tall].
apply MALLOC; [exact pre4 | exact (proj2 (proj2 (proj2 R4))) | exact Hn].
Qed.
Section s.
Variables (L5 : layout) (A5 : astate) (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model).
Hypothesis POST : call_post src0_msyms (MRx src0_msyms) L A regs4 mem4 md (fun _ => False) L5 A5 regs5 mem5 md5.
Hypothesis LEN5 : (length (st_regions A) <= length (st_regions A5))%nat.
Let MX5 : MRx src0_msyms L5 A5 mem5 md5 := proj1 POST.
Lemma M5 : MRc src0_msyms L5 A5 mem5 md5. Proof using MX5. exact (MRx_MRc _ _ _ _ _ MX5). Qed.
Lemma Hmd5 : m_halted md5 = None /\ m_vm_lazy md5 = [] /\ m_vm_materialized md5 = [].
Proof using MX5. exact (mc_md _ _ _ _ _ M5). Qed.
Lemma POST_facts :
WF A5 /\ bounded A5 /\ layout_le A L L5 /\
(forall b k, In (b, k) (user_blocks A) -> In (b, k) (user_blocks A5) -> ptr_addr L5 b = ptr_addr L b) /\
regs_preserved regs4 regs5 /\ (exists vm', md5 = with_vmmaps vm' md) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img src0_msyms x) ->
~ owned src0_msyms L A x -> ~ owned src0_msyms L5 A5 x -> ~ scratch src0_msyms regs4 x ->
mbyte src0segs mem5 x = mbyte src0segs mem4 x /\ (writable_at src0segs mem4 x <-> writable_at src0segs mem5 x)) /\
(forall b k i, In (b, k) (user_blocks A) -> In (b, k) (user_blocks A5) -> 0 <= i < k ->
mbyte src0segs mem5 (ptr_addr L b + i) = mbyte src0segs mem4 (ptr_addr L b + i)) /\
(forall x, scratch src0_msyms regs4 x -> writable_at src0segs mem5 x).
Proof using POST.
pose proof POST as (_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
repeat (split; [assumption|]). split; [| split; [exact H8 | exact H9]].
intros x Hx N1 N2 N3. apply (H7 x Hx N1 N2 N3). intros [].
Qed.
Lemma scratch4 x : scratch src0_msyms regs4 x <-> (SPa - 8256 <= x < SPa - 64) \/ ERRa x.
Proof using LEN5 PRE.
pose proof R4 as (_ & R2 & _). pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
unfold scratch, spZ. rewrite R2, lit64_small by lia. unfold ALLOC_STACK, ERRa. rewrite ERRNO2_val.
change (errno_addr src0_msyms) with (src0_tp + -164). lia.
Qed.
Lemma frame_kept x : SPa - 64 <= x < SPa ->
mbyte src0segs mem5 x = mbyte src0segs mem4 x /\ (writable_at src0segs mem4 x <-> writable_at src0segs mem5 x).
Proof using LEN5 M MX5.
intros Hx. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
destruct POST_facts as (_ & _ & _ & _ & _ & _ & FR & _). apply FR.
- left. lia.
- intros Ho. pose proof (owned_low _ L A mem md x M Ho). lia.
- intros Ho. pose proof (owned_low _ L5 A5 mem5 md5 x M5 Ho). lia.
- intros Hs. apply scratch4 in Hs. unfold ERRa in Hs. rewrite ERRNO2_val in Hs. unfold src0_tp in Hs. lia.
Qed.
Lemma stk_writable5 x : STKa x -> writable_at src0segs mem5 x.
Proof using LEN5 M MX5.
intros Hx. destruct (Z_lt_le_dec x (SPa - 64)).
- apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 POST_facts)))))))). apply scratch4. left. unfold STKa in Hx. lia.
- apply (proj1 (proj2 (frame_kept x ltac:(unfold STKa in Hx; lia)))). apply (fa_stk _ _ _ _ _ _ _ _ _ _ FA). rewrite STK_fb. exact Hx.
Qed.
Lemma errno_writable5 x : ERRa x -> writable_at src0segs mem5 x.
Proof using LEN5 POST PRE. intros Hx. apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 POST_facts)))))))). apply scratch4. right. exact Hx. Qed.
Lemma CS5 j : In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr regs5 (nat_to_reg j) = getr regs4 (nat_to_reg j).
Proof using LEN5 POST.
intros Hj. destruct POST_facts as (_ & _ & _ & _ & PRES & _).
assert (H : (1 <= j <= 31)%nat /\ callee_saved (Z.of_nat j)).
{ unfold callee_saved. cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [split; [lia|lia] |]). destruct Hj. }
destruct H as [H1 H2]. rewrite <- (lit5 j) by lia. apply PRES. exact H2.
Qed.
Lemma keep5 i : In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr regs5 (nat_to_reg i) = getr regs (nat_to_reg i).
Proof using FA LEN5 POST.
intros Hi. rewrite CS5 by (cbn in Hi |- *; tauto). apply (fa_keep _ _ _ _ _ _ _ _ _ _ FA i Hi).
Qed.
Section rk.
Variables (nv q : Z) (res s2v : sv).
Hypothesis Hnv : 0 <= nv < 2 ^ 64.
Hypothesis Hq : 0 <= q < 2 ^ 64.
Hypothesis Hres : getr regs5 10 = sv_denot (EV (xg regs5 nv q)) res.
Hypothesis Hs2v : Z_to_bv 64 (Pa + nold) = sv_denot (EV (xg regs5 nv q)) s2v.
Lemma regs_ok5 : regs_ok (EV (xg regs5 nv q)) (regs_mallocG res s2v) regs5.
Proof using HW Hin Hnv Hq Hres Hs2v LEN5 POST.
pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_mallocG]; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_junkG regs5 nv q Hnv Hq) by lia; reflexivity).
- rewrite CS5 by (cbn; tauto). cbn [nat_to_reg]. rewrite (proj1 (proj2 R4)).
rewrite (den_off _ (xg_range regs5 nv q Hnv Hq)), xg_SP; [reflexivity|]. rewrite xg_SP. lia.
- rewrite (keep5 3%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
- rewrite (keep5 4%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
- rewrite CS5 by (cbn; tauto). cbn [nat_to_reg]. rewrite (fa_s0 _ _ _ _ _ _ _ _ _ _ FA).
rewrite (den_xg regs5 nv q Hnv Hq), xg_N. reflexivity.
- rewrite CS5 by (cbn; tauto). cbn [nat_to_reg]. rewrite (fa_s1 _ _ _ _ _ _ _ _ _ _ FA).
rewrite (den_xg regs5 nv q Hnv Hq), xg_P. reflexivity.
- exact Hres.
- rewrite CS5 by (cbn; tauto). cbn [nat_to_reg]. rewrite (fa_s2 _ _ _ _ _ _ _ _ _ _ FA). exact Hs2v.
- rewrite (keep5 23%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
- rewrite (keep5 24%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
- rewrite (keep5 25%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
- rewrite (keep5 26%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
- rewrite (keep5 27%nat) by (cbn; tauto). symmetry. apply den_regG; lia.
Qed.
Lemma mem_ok5 : mem_ok src0segs (EV (xg regs5 nv q)) mem5 after_memR.
Proof using Hnv Hq LEN5 M MX5.
apply mem_ok_at; [exact Hnv | exact Hq | | exact stk_writable5].
apply frame_chunks_of; [exact Hnv | exact Hq |]. intros x Hx. exact (proj1 (frame_kept x Hx)).
Qed.
End rk.
Section t.
Hypothesis A0_5 : getr regs5 10 = Z_to_bv 64 0.
Hypothesis UB5 : user_blocks A5 = user_blocks A.
Let E6 := EV (xg regs5 (Pa + nold) 4096).
Lemma Hnv6 : 0 <= Pa + nold < 2 ^ 64.
Proof using HW Hin LEN5. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val. lia. Qed.
Lemma Hq6 : 0 <= 4096 < 2 ^ 64. Proof using LEN5. lia. Qed.
Lemma st_ok6 : st_ok src0segs E6 G6z (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom src0segs)).
Proof using A0_5 HW Hin LEN5 MX5.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts G6z resv_denot].
repeat (split; [reflexivity|]). split.
- apply regs_ok5; [exact Hnv6 | exact Hq6 | rewrite A0_5; reflexivity |].
rewrite (den_xg regs5 (Pa + nold) 4096 Hnv6 Hq6), xg_nv. reflexivity.
- split; [exact (mem_ok5 _ _ Hnv6 Hq6)|]. split; [| split; exact I].
pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val.
apply atoms_okG; [exact Hnv6 | exact Hq6 | unfold CEIL in *; lia | unfold CEIL in *; lia | reflexivity].
Qed.
Lemma leaf_none :
SR src0segs (mkCfg (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom src0segs)) md5)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n (None, A5)).
Proof using A0_5 HW Hin LEN5 MX5 UB5.
destruct Hmd5 as (Hh5 & Hlz5 & Hmat5). pose proof PREf as (Hret & Hal & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val as HCV.
pose proof Hnv6 as Hnv. pose proof Hq6 as Hq.
eapply SR_bind; [exact (G7_run E6 _ md5 Hh5 Hlz5 st_ok6)|]. intros c7 (ms7 & -> & HS7 & HF7). cbn [ms_mem] in HF7.
destruct G7_shape as (Hpc7 & Hrv7 & Hview7 & Ha07 & Hsm7).
pose proof (st_ok_regs_ok src0segs E6 _ _ HS7) as R7.
unfold callee_view, callee_view0, view in Hview7. cbn [map] in Hview7.
vnth Hview7 0%nat V1. vnth Hview7 1%nat V2. vnth Hview7 2%nat V3. vnth Hview7 3%nat V4. vnth Hview7 4%nat V8. vnth Hview7 5%nat V9.
vnth Hview7 6%nat V18. vnth Hview7 7%nat V19. vnth Hview7 8%nat V20. vnth Hview7 9%nat V21. vnth Hview7 10%nat V22. vnth Hview7 11%nat V23.
vnth Hview7 12%nat V24. vnth Hview7 13%nat V25. vnth Hview7 14%nat V26. vnth Hview7 15%nat V27.
assert (CV : forall i, In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
getr (ms_regs ms7) (nat_to_reg i) = getr regs (nat_to_reg i)).
{ intros i Hi0. rewrite <- (den_regG regs5 (Pa + nold) 4096 Hnv Hq i) by (cbn in Hi0; lia).
rewrite (R7 (nat_to_reg i)). f_equal. cbn in Hi0.
repeat (destruct Hi0 as [<-|Hi0]; [cbn [nat_to_reg]; assumption|]). destruct Hi0. }
assert (E1 : ew E6 1 = getr regs 1).
{ pose proof (den_regG regs5 (Pa + nold) 4096 Hnv Hq 1 ltac:(lia)) as D. cbn [sv_denot] in D.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D. exact D. }
assert (RAW7 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ms_mem ms7 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x)).
{ intros x Hx N1. apply HF7. rewrite lit64_small by lia. intros W. apply wr_after in W. rewrite (base_SPG regs5 _ _ Hnv Hq : base_val E6 (Some aSP) = SPa) in W. exact (N1 W). }
eapply (SR_realloc_ret E6 G7 ms7 md5 _ HS7 Hrv7 Hpc7 V1); [rewrite E1; exact Hret | exact Hh5 | exact Hlz5 |].
unfold realloc_leaf. exists L5, (ms_regs ms7), (ms_mem ms7), md5. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [| split; [rewrite (R7 10%bv), Ha07; reflexivity | exact UB5]].
destruct POST_facts as (W5 & B5 & LE5 & AD5 & PRES5 & VM5 & FR5 & BL5 & SC5).
pose proof (st_ok_mem_ok src0segs E6 _ _ HS7) as (_ & ROK7 & _). rewrite Hsm7 in ROK7. apply Forall_inv in ROK7.
destruct ROK7 as (_ & _ & W7 & _). cbn [r_base r_wlo r_whi] in W7. rewrite (base_SPG regs5 _ _ Hnv Hq : base_val E6 (Some aSP) = SPa) in W7.
unfold call_post_k. change (ms_segs src0_msyms) with src0segs.
split; [| split; [exact W5 | split; [exact B5 | split; [exact LE5 | split; [exact AD5 | split; [| split; [exact VM5 | split; [| split]]]]]]]].
-   apply (MRx_scratch L5 A5 mem5 (ms_mem ms7) md5 MX5 Hceil). intros x Hx N1 _. exact (RAW7 x Hx N1).
-   intros r Hr. destruct (callee_saved_cases r Hr) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r Rr). apply CV. cbn. cbn in RI. tauto.
-   intros x Hx N1 N2 N3 N4.
assert (Hx64 : 0 <= x < 2 ^ 64) by (destruct Hx as [Hx|Hx]; [lia | apply src0_img_range in Hx; unfold in_img1 in Hx; lia]).
assert (NS : ~ STKa x /\ ~ ERRa x).
{ unfold scratch_k, REALLOC_STACK, ALLOC_STACK in N3. unfold STKa, ERRa. rewrite ERRNO2_val. change (errno_addr src0_msyms) with (src0_tp + -164) in N3. change (spZ regs) with SPa in N3. split; intro; apply N3; lia. }
destruct NS as [NS1 NS2].
destruct (same_byte_views2 mem5 (ms_mem ms7) x (RAW7 x Hx64 NS1)) as [A1 A2].
destruct (FR5 x Hx N1 N2 ltac:(intros Hs; apply scratch4 in Hs; destruct Hs as [Hs|Hs]; [unfold STKa in NS1; lia | exact (NS2 Hs)])) as [B1 B2].
destruct (same_byte_views2 mem mem4 x (RAW4 x Hx64 NS1 NS2)) as [C1 C2].
rewrite A1, B1, C1. tauto.
-   intros b k i Hb1 Hb2 Hi.
pose proof (mr_blocks_range _ _ (MRx_laws src0_msyms) L A mem md b k MX Hb1) as [Lo Hi2].
assert (Hx64 : 0 <= ptr_addr L b + i < 2 ^ 64) by lia.
assert (NS1 : ~ STKa (ptr_addr L b + i)) by (unfold STKa; intro; lia).
assert (NS2 : ~ ERRa (ptr_addr L b + i)) by (intros He; exact (anyblock_off_img L A mem md b k (ptr_addr L b + i) M Hb1 ltac:(lia) (errno_img _ He))).
rewrite (proj1 (same_byte_views2 mem5 (ms_mem ms7) _ (RAW7 _ Hx64 NS1))).
rewrite (BL5 b k i Hb1 Hb2 Hi). apply (proj1 (same_byte_views2 mem mem4 _ (RAW4 _ Hx64 NS1 NS2))).
-   intros x Hs. unfold scratch_k, REALLOC_STACK, ALLOC_STACK in Hs.
change (errno_addr src0_msyms) with (src0_tp + -164) in Hs. change (spZ regs) with SPa in Hs.
destruct Hs as [Hs|Hs].
+ replace x with (SPa + (x - SPa)) by lia. apply W7. lia.
+ apply (writable_same2 mem5 (ms_mem ms7) x); [apply RAW7; [unfold src0_tp in Hs; lia | unfold STKa; unfold src0_tp in Hs; intro; lia] |].
apply errno_writable5. unfold ERRa. rewrite ERRNO2_val. lia.
Qed.
End t.
Lemma mem_ok_xfer rs1 nv1 q1 rs2 nv2 q2 (m1 m2 : word -> option byte) :
0 <= nv1 < 2 ^ 64 -> 0 <= q1 < 2 ^ 64 -> 0 <= nv2 < 2 ^ 64 -> 0 <= q2 < 2 ^ 64 ->
mem_ok src0segs (EV (xg rs1 nv1 q1)) m1 after_memR ->
(forall x, SPa - 64 <= x < SPa -> m2 (Z_to_bv 64 x) = m1 (Z_to_bv 64 x)) ->
(forall x, STKa x -> writable_at src0segs m2 x) -> mem_ok src0segs (EV (xg rs2 nv2 q2)) m2 after_memR.
Proof using LEN5 PRE.
intros H1 H2 H3 H4 (Hwf & ROK & PD) EQ W2.
apply mem_ok_at; [exact H3 | exact H4 | | exact W2].
apply Forall_inv in ROK. destruct ROK as (_ & _ & _ & R4c). cbn [r_base r_chunks] in R4c. rewrite (base_SPG rs1 _ _ H1 H2) in R4c.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) R4c c Hc) as Cc.
destruct (frame_chunks_slots c Hc) as (o & r & -> & _ & Hr & O1 & O2).
intros i Hi. destruct (Cc i Hi) as (b & Hb1 & Hb2). exists b. split.
- rewrite <- Hb1. cbn [cbyte c_val]. rewrite (den_regG rs2 nv2 q2 H3 H4 r Hr), (den_regG rs1 nv1 q1 H1 H2 r Hr). reflexivity.
- rewrite <- Hb2. cbn [c_len c_val cv_len c_off] in Hi |- *. change (Z.of_N 8) with 8 in Hi.
apply (proj1 (same_byte_views2 m1 m2 _ (EQ (SPa + o + i) ltac:(lia)))).
Qed.
Section v.
Variables (q : sptr) (l1 l2 : list (sptr * Z)).
Hypothesis A0_5 : getr regs5 10 = Z_to_bv 64 (ptr_addr L5 q).
Hypothesis NZ5 : ptr_addr L5 q <> 0.
Hypothesis UB5 : user_blocks A5 = l1 ++ (q, n) :: l2.
Hypothesis UBA : user_blocks A = l1 ++ l2.
Definition Qa : Z := ptr_addr L5 q.
Lemma q_in5 : In (q, n) (user_blocks A5). Proof using UB5. rewrite UB5. apply in_or_app. right. left. reflexivity. Qed.
Lemma p_in5 : In (p, nold) (user_blocks A5).
Proof using Hin UB5 UBA. pose proof Hin as H. rewrite UBA in H. rewrite UB5. apply in_app_iff in H. apply in_or_app. destruct H; [left; assumption | right; right; assumption]. Qed.
Lemma P5 : ptr_addr L5 p = Pa.
Proof using Hin POST UB5 UBA. destruct POST_facts as (_ & _ & _ & AD & _). apply (AD p nold); [exact Hin | exact p_in5]. Qed.
Lemma q_neq_p : q <> p.
Proof using Hin POST UB5 UBA.
destruct POST_facts as (W5 & _). pose proof (user_block_ptrs_NoDup A5 W5) as ND. rewrite UB5 in ND.
pose proof Hin as H. rewrite UBA in H. exact (ptr_neq_of_split l1 l2 q n p nold ND H).
Qed.
Lemma Qblk : 4096 <= Qa /\ Qa + n <= alloc_ceiling /\ Qa mod 16 = 0 /\
(forall i, 0 <= i < n -> present mem5 (Qa + i) /\ ~ owned src0_msyms L5 A5 (Qa + i)).
Proof using MX5 UB5.
pose proof (mr_blocks_range _ _ (MRx_laws src0_msyms) L5 A5 mem5 md5 _ _ MX5 q_in5) as [H1 H2].
split; [exact H1|]. split; [exact H2|]. split; [exact (mr_blocks_aligned _ _ (MRx_laws src0_msyms) L5 A5 mem5 md5 _ _ MX5 q_in5)|].
intros i Hi. pose proof (mr_blocks _ _ (MRx_laws src0_msyms) L5 A5 mem5 md5 _ _ i MX5 q_in5 Hi) as (B1 & _ & _ & B4). unfold Qa. auto.
Qed.
Lemma Pblk5 : forall i, 0 <= i < nold -> present mem5 (Pa + i) /\ ~ owned src0_msyms L5 A5 (Pa + i).
Proof using Hin MX5 UB5 UBA.
intros i Hi. pose proof (mr_blocks _ _ (MRx_laws src0_msyms) L5 A5 mem5 md5 _ _ i MX5 p_in5 Hi) as (B1 & _ & _ & B4).
rewrite P5 in B1, B4. auto.
Qed.
Lemma PQ_disjoint : Qa + n <= Pa \/ Pa + nold <= Qa.
Proof using Hin LEN5 MX5 UB5 UBA.
pose proof (mr_blocks_disjoint _ _ (MRx_laws src0_msyms) L5 A5 mem5 md5 MX5) as PW. unfold blocks in PW. rewrite UB5 in PW.
pose proof Hin as H. rewrite UBA in H.
change (l1 ++ (q, n) :: l2) with (l1 ++ [(q, n)] ++ l2) in PW.
destruct (YN26.pairwise_app_mid ranges_disjoint (fun b : sptr * Z => (ptr_addr L5 (fst b), snd b)) l1 [(q, n)] l2 (q, n) (p, nold) PW ltac:(left; reflexivity) H) as [D|D];
unfold ranges_disjoint in D; cbn [fst snd] in D; rewrite P5 in D; unfold Qa; lia.
Qed.
Lemma Mrange : 0 <= Ma /\ Ma <= n /\ Ma <= nold.
Proof using HW Hin LEN5. pose proof Pblk as (_ & P0 & _). pose proof Hn. unfold Ma. lia. Qed.
Lemma Hnv7 : 0 <= nold < 2 ^ 64.
Proof using HW Hin LEN5. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val. lia. Qed.
Lemma Hq7 : 0 <= Qa < 2 ^ 64.
Proof using FA LEN5 MX5 UB5. pose proof Qblk as (Q1 & Q2 & _). pose proof YM05.alloc_ceiling_val. pose proof Hn. lia. Qed.
Lemma facts_q rs cs al : (cs = [] \/ cs = [mkAC cM (SOff aN 0) (SOff aNOLD 0)]) -> (al = [] \/ al = [ALIAS_OLD]) ->
facts_ok (EV (xg rs nold Qa)) (mkFacts atomsG cs al).
Proof using HW Hin LEN5 MX5 UB5.
intros Hcs Hal0. pose proof Hnv7 as Hnv. pose proof Hq7 as Hq. pose proof Qblk as (Q1 & Q2 & Q3 & _).
pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val. pose proof Hn.
split; [| split].
- apply atoms_okG; [exact Hnv | exact Hq | lia | unfold CEIL in *; lia | exact Q3].
- cbn [f_conds]. destruct Hcs as [-> | ->]; [exact I | exact (cond_okM rs Qa Hq)].
- cbn [f_alias]. destruct Hal0 as [-> | ->]; [exact I | exact (alias_oldG rs nold Qa Hnv Hq eq_refl)].
Qed.
Let E6 := EV (xg regs5 nold Qa).
Lemma st_ok6q : st_ok src0segs E6 (G6q cM) (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom src0segs)).
Proof using A0_5 HW Hin LEN5 MX5 UB5.
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YM05.alloc_ceiling_val.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts G6q resv_denot].
repeat (split; [reflexivity|]). split.
- apply regs_ok5; [exact Hnv | exact Hq | rewrite A0_5, (den_xg regs5 nold Qa Hnv Hq), xg_q; reflexivity |].
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add, !(ew_xg regs5 nold Qa Hnv Hq), !Z.add_0_r, xg_P, xg_nv.
unfold add64. rewrite !lit64_small by lia. rewrite Z.mod_small by lia. reflexivity.
- split; [exact (mem_ok5 _ _ Hnv Hq)|]. apply facts_q; right; reflexivity.
Qed.
Definition K10 (regs9 : bvmap 5 word) (mem8 : word -> option byte) (bs : list byte) (ms10 : machine_state) : Prop :=
st_ok src0segs (EV (xg regs9 nold Qa)) G10 ms10 /\
(forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> mem8 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x)) /\
rdn src0segs mem8 (Z_to_bv 64 Pa) (Z.to_nat Ma) = Some bs /\ length bs = Z.to_nat Ma /\
(forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ms_mem ms10 (Z_to_bv 64 x) = wbytes mem8 (Z_to_bv 64 Qa) bs (Z_to_bv 64 x)).
Lemma to_S10 :
SR src0segs (mkCfg (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom src0segs)) md5)
(fun c => exists regs9 mem8 bs ms10, c = mkCfg ms10 md5 /\ K10 regs9 mem8 bs ms10).
Proof using A0_5 HW Hin LEN5 MEMCPY MX5 UB5 UBA.
destruct Hmd5 as (Hh5 & Hlz5 & Hmat5). pose proof PREf as (Hret & Hal & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val as HCV.
pose proof Pblk as (P1 & P0 & P2 & _). pose proof Qblk as (Q1 & Q2 & Q3 & Q4). pose proof Mrange as (M0 & M1 & M2).
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq.
eapply SR_bind; [exact (G8_run E6 _ md5 Hh5 Hlz5 cM cM_cases st_ok6q)|]. intros c8 (ms8 & -> & HS8 & HF8). cbn [ms_mem] in HF8.
destruct (G8_shape cM cM_cases) as (Hpc8 & Hrv8 & Hv8 & Hsm8). pose proof (st_ok_regs_ok src0segs E6 _ _ HS8) as R8.
unfold view in Hv8. cbn [map] in Hv8.
vnth Hv8 0%nat V1. vnth Hv8 6%nat V10. vnth Hv8 7%nat V11. vnth Hv8 8%nat V12.
assert (RAW8 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ms_mem ms8 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x)).
{ intros x Hx N1. apply HF8. rewrite lit64_small by lia. intros W. apply wr_after in W. rewrite (base_SPG regs5 _ _ Hnv Hq : base_val E6 (Some aSP) = SPa) in W. exact (N1 W). }
assert (H10 : getr (ms_regs ms8) 10 = Z_to_bv 64 Qa) by (rewrite (R8 10%bv), V10, (den_xg regs5 nold Qa Hnv Hq), xg_q; reflexivity).
assert (H11 : getr (ms_regs ms8) 11 = Z_to_bv 64 Pa) by (rewrite (R8 11%bv), V11, (den_xg regs5 nold Qa Hnv Hq), xg_P; reflexivity).
assert (H12 : getr (ms_regs ms8) 12 = Z_to_bv 64 Ma) by (rewrite (R8 12%bv), V12; exact (mlen_M regs5 Qa Hq)).
assert (PR8 : forall i, 0 <= i < Ma -> present (ms_mem ms8) (Pa + i)).
{ intros i Hi. apply (present_same mem5); [apply RAW8; [lia | unfold STKa; intro; lia] | exact (proj1 (Pblk5 i ltac:(lia)))]. }
assert (PQ8 : forall i, 0 <= i < Ma -> present (ms_mem ms8) (Qa + i)).
{ intros i Hi. apply (present_same mem5); [apply RAW8; [lia | unfold STKa; intro; lia] | exact (proj1 (Q4 i ltac:(lia)))]. }
destruct (rdn_of_present (ms_mem ms8) (Z.to_nat Ma) Pa ltac:(intros i Hi; apply PR8; lia) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present (ms_mem ms8) (Z.to_nat Ma) Qa ltac:(intros i Hi; apply PQ8; lia) ltac:(lia) ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (MEMCPY bs (Z_to_bv 64 Qa) (Z_to_bv 64 Pa) (Z_to_bv 64 Ma) (ms_mem ms8) (seg_rom src0segs) (ms_regs ms8) H10 H11 H12)
as (regs9 & MS & Ha0 & Hfr9).
{ rewrite lit64_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite lit64_small by lia. lia. }
{ rewrite lit64_small by lia. lia. }
{ rewrite !lit64_small by lia. pose proof PQ_disjoint. lia. }
rewrite (st_ok_mkst src0segs E6 _ _ HS8 Hrv8), Hpc8.
eapply SR_msteps; [exact Hh5 | exact Hlz5 | exact MS |].
replace (v_jalr (getr (ms_regs ms8) 1) 0) with (Z_to_bv 64 RA_MEMCPY).
2:{ rewrite (R8 1%bv), V1. apply bv_eq. vm_compute. reflexivity. }
set (mem9 := wbytes (ms_mem ms8) (Z_to_bv 64 Qa) bs).
set (E9 := EV (xg regs9 nold Qa)).
assert (Q9 : forall x, 0 <= x < 2 ^ 64 -> ~ (Qa <= x < Qa + Ma) -> mem9 (Z_to_bv 64 x) = ms_mem ms8 (Z_to_bv 64 x)).
{ intros x Hx NQ. subst mem9. destruct (Z_lt_le_dec x Qa).
- apply wbytes_below; rewrite ?Hlen, !lit64_small by lia; lia.
- apply wbytes_above. rewrite !lit64_small by lia. rewrite Hlen. lia. }
assert (HS9 : st_ok src0segs E9 G9 (mkst regs9 (Z_to_bv 64 RA_MEMCPY) mem9 (seg_rom src0segs))).
{ unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts G9 resv_denot].
subst E9. repeat (split; [reflexivity|]). split; [| split].
- vnth Hv8 1%nat V2. vnth Hv8 2%nat V3. vnth Hv8 3%nat V4. vnth Hv8 4%nat V8. vnth Hv8 5%nat V9.
vnth Hv8 13%nat V23. vnth Hv8 14%nat V24. vnth Hv8 15%nat V25. vnth Hv8 16%nat V26. vnth Hv8 17%nat V27.
assert (KEEP : forall i, In i [2; 3; 4; 8; 9; 23; 24; 25; 26; 27]%nat -> getr regs9 (nat_to_reg i) = getr (ms_regs ms8) (nat_to_reg i)).
{ intros i Hi0. cbn [In] in Hi0.
repeat (destruct Hi0 as [<-|Hi0]; [apply Hfr9; cbn [nat_to_reg]; intros HH; discriminate HH |]). destruct Hi0. }
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_callG]; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_junkG regs9 nold Qa Hnv Hq) by lia; reflexivity).
all: rewrite KEEP by (cbn; tauto); cbn [nat_to_reg].
+ rewrite (R8 2%bv), V2, (den_off _ (xg_range regs9 nold Qa Hnv Hq)), (den_off _ (xg_range regs5 nold Qa Hnv Hq)), !xg_SP; [reflexivity | |];
pose proof PREf as (_ & _ & PC & PS & _); rewrite xg_SP; lia.
+ rewrite (R8 3%bv), V3, (den_regG regs9 nold Qa Hnv Hq 3 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 3 ltac:(lia)).
+ rewrite (R8 4%bv), V4. unfold aTP. rewrite (den_regG regs9 nold Qa Hnv Hq 4 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 4 ltac:(lia)).
+ rewrite (R8 8%bv), V8, (den_xg regs9 nold Qa Hnv Hq), (den_xg regs5 nold Qa Hnv Hq), !xg_q. reflexivity.
+ rewrite (R8 9%bv), V9, (den_xg regs9 nold Qa Hnv Hq), (den_xg regs5 nold Qa Hnv Hq), !xg_P. reflexivity.
+ rewrite (R8 23%bv), V23, (den_regG regs9 nold Qa Hnv Hq 23 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 23 ltac:(lia)).
+ rewrite (R8 24%bv), V24, (den_regG regs9 nold Qa Hnv Hq 24 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 24 ltac:(lia)).
+ rewrite (R8 25%bv), V25, (den_regG regs9 nold Qa Hnv Hq 25 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 25 ltac:(lia)).
+ rewrite (R8 26%bv), V26, (den_regG regs9 nold Qa Hnv Hq 26 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 26 ltac:(lia)).
+ rewrite (R8 27%bv), V27, (den_regG regs9 nold Qa Hnv Hq 27 ltac:(lia)). apply (den_regG regs5 nold Qa Hnv Hq 27 ltac:(lia)).
- pose proof (st_ok_mem_ok src0segs E6 _ _ HS8) as MOK8. rewrite Hsm8 in MOK8.
apply (mem_ok_xfer regs5 nold Qa regs9 nold Qa (ms_mem ms8) mem9 Hnv Hq Hnv Hq MOK8).
+ intros x Hx. pose proof PREf as (_ & _ & PC & PS & _). apply Q9; lia.
+ intros x Hx. apply (writable_at_grows src0segs (ms_mem ms8) mem9); [apply wbytes_grows|].
destruct MOK8 as (_ & ROK8 & _). apply Forall_inv in ROK8. destruct ROK8 as (_ & _ & W8 & _).
cbn [r_base r_wlo r_whi] in W8. rewrite (base_SPG regs5 _ _ Hnv Hq : base_val E6 (Some aSP) = SPa) in W8. unfold STKa in Hx. replace x with (SPa + (x - SPa)) by lia. apply W8. lia.
- apply facts_q; left; reflexivity. }
eapply SR_mono; [exact (G10_run E9 _ md5 Hh5 Hlz5 HS9)|].
intros c10 (ms10 & -> & HS10 & HF10). cbn [ms_mem] in HF10.
exists regs9, (ms_mem ms8), bs, ms10. split; [reflexivity|].
split; [exact HS10|]. split; [exact RAW8|]. split; [exact Hbs|]. split; [exact Hlen|].
intros x Hx N1. apply HF10. rewrite lit64_small by lia. intros W. apply wr_after in W.
subst E9. rewrite (base_SPG regs9 _ _ Hnv Hq) in W. exact (N1 W).
Qed.
Section w.
Variables (regs9 : bvmap 5 word) (mem8 : word -> option byte) (bs : list byte) (ms10 : machine_state).
Hypothesis HK : K10 regs9 mem8 bs ms10.
Let E9 := EV (xg regs9 nold Qa).
Let regs10 := ms_regs ms10.
Let mem10 := ms_mem ms10.
Let mem9 := wbytes mem8 (Z_to_bv 64 Qa) bs.
Lemma HS10 : st_ok src0segs E9 G10 ms10. Proof using HK. exact (proj1 HK). Qed.
Lemma RAW8 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> mem8 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x). Proof using HK. exact (proj1 (proj2 HK)). Qed.
Lemma Hbs : rdn src0segs mem8 (Z_to_bv 64 Pa) (Z.to_nat Ma) = Some bs. Proof using HK. exact (proj1 (proj2 (proj2 HK))). Qed.
Lemma Hlen : length bs = Z.to_nat Ma. Proof using HK. exact (proj1 (proj2 (proj2 (proj2 HK)))). Qed.
Lemma RAW10 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> mem10 (Z_to_bv 64 x) = mem9 (Z_to_bv 64 x). Proof using HK. exact (proj2 (proj2 (proj2 (proj2 HK)))). Qed.
Lemma Q9 : forall x, 0 <= x < 2 ^ 64 -> ~ (Qa <= x < Qa + Ma) -> mem9 (Z_to_bv 64 x) = mem8 (Z_to_bv 64 x).
Proof using HK HW Hin LEN5 MX5 UB5.
pose proof Qblk as (Q1 & Q2 & _). pose proof Mrange as (M0 & M1 & M2). pose proof YM05.alloc_ceiling_val.
intros x Hx NQ. unfold mem9. destruct (Z_lt_le_dec x Qa).
- apply wbytes_below; rewrite ?Hlen, !lit64_small by lia; lia.
- apply wbytes_above. rewrite !lit64_small by lia. rewrite Hlen. lia.
Qed.
Lemma copy9 : forall i, 0 <= i < Ma -> mbyte src0segs mem9 (Qa + i) = mbyte src0segs mem8 (Pa + i).
Proof using HK HW Hin LEN5 MX5 UB5.
pose proof Qblk as (Q1 & Q2 & _). pose proof Pblk as (P1 & P0 & P2 & _). pose proof Mrange as (M0 & M1 & M2). pose proof YM05.alloc_ceiling_val.
intros i Hi. unfold mem9. rewrite (wbytes_mbyte src0segs bs mem8 Qa (Qa + i)) by (rewrite ?Hlen; lia).
rewrite Hlen. replace ((Qa <=? Qa + i) && (Qa + i <? Qa + Z.of_nat (Z.to_nat Ma))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
pose proof (proj2 (proj1 (rdn_mbytes src0segs mem8 (Z.to_nat Ma) Pa bs) Hbs)) as Hb.
replace (Z.to_nat (Qa + i - Qa)) with (Z.to_nat i) by lia.
rewrite <- (Hb (Z.to_nat i)) by lia. replace (Pa + Z.of_nat (Z.to_nat i)) with (Pa + i) by lia. reflexivity.
Qed.
Lemma S10_regs :
getr regs10 1 = Z_to_bv 64 RA_FREE /\ getr regs10 2 = Z_to_bv 64 (SPa - 64) /\
getr regs10 4 = getr regs 4 /\ getr regs10 10 = Z_to_bv 64 Pa /\
(forall i, In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr regs10 (nat_to_reg i) = getr regs (nat_to_reg i)) /\
getr regs10 8 = Z_to_bv 64 Qa /\ getr regs10 9 = Z_to_bv 64 Pa.
Proof using E9 HK HW Hin LEN5 MX5 UB5.
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq.
destruct G10_shape as (_ & _ & Hv & _). unfold view in Hv. cbn [map] in Hv.
vnth Hv 0%nat V1. vnth Hv 1%nat V2. vnth Hv 2%nat V3. vnth Hv 3%nat V4. vnth Hv 4%nat V8. vnth Hv 5%nat V9. vnth Hv 6%nat V10.
vnth Hv 11%nat V23. vnth Hv 12%nat V24. vnth Hv 13%nat V25. vnth Hv 14%nat V26. vnth Hv 15%nat V27.
pose proof (st_ok_regs_ok src0segs E9 _ _ HS10) as R. change (regs_ok E9 (ss_regs G10) regs10) in R.
pose proof PREf as (_ & _ & P3 & P4 & _). pose proof YM05.alloc_ceiling_val.
split; [rewrite (R 1%bv), V1; reflexivity|].
split; [rewrite (R 2%bv), V2, (den_off _ (xg_range regs9 nold Qa Hnv Hq)), xg_SP; [reflexivity|]; rewrite xg_SP; lia|].
split; [rewrite (R 4%bv), V4; exact (den_regG regs9 nold Qa Hnv Hq 4 ltac:(lia))|].
split; [rewrite (R 10%bv), V10, (den_xg regs9 nold Qa Hnv Hq), xg_P; reflexivity|].
split; [| split; [rewrite (R 8%bv), V8, (den_xg regs9 nold Qa Hnv Hq), xg_q; reflexivity | rewrite (R 9%bv), V9, (den_xg regs9 nold Qa Hnv Hq), xg_P; reflexivity]].
intros i Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [nat_to_reg];
[rewrite (R 3%bv), V3 | rewrite (R 4%bv), V4 | rewrite (R 23%bv), V23 | rewrite (R 24%bv), V24 | rewrite (R 25%bv), V25 | rewrite (R 26%bv), V26 | rewrite (R 27%bv), V27];
apply (den_regG regs9 nold Qa Hnv Hq); lia.
Qed.
Lemma S10_mem :
(forall x, STKa x -> writable_at src0segs mem10 x) /\ mem_ok src0segs E9 mem10 after_memR.
Proof using HK HW Hin LEN5 MX5 UB5.
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq.
pose proof (st_ok_mem_ok src0segs E9 _ _ HS10) as MOK. change (ms_mem ms10) with mem10 in MOK.
destruct G10_shape as (_ & _ & _ & Hsm). rewrite Hsm in MOK. split; [| exact MOK].
destruct MOK as (_ & ROK & _). apply Forall_inv in ROK.
destruct ROK as (_ & _ & W & _). cbn [r_base r_wlo r_whi] in W. rewrite (base_SPG regs9 _ _ Hnv Hq : base_val E9 (Some aSP) = SPa) in W.
intros x Hx. unfold STKa in Hx. replace x with (SPa + (x - SPa)) by lia. apply W. lia.
Qed.
Lemma RAW105 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ~ (Qa <= x < Qa + Ma) -> mem10 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x).
Proof using HK HW Hin LEN5 MX5 UB5 mem9. intros x Hx N1 N2. rewrite (RAW10 x Hx N1), (Q9 x Hx N2). apply RAW8; assumption. Qed.
Lemma pre10 : call_pre src0_msyms (MRx src0_msyms) L5 A5 regs10 mem10 md5.
Proof using E9 HK HW Hin LEN5 MX5 UB5 mem9.
pose proof PREf as (Hret & Hal & Hceil & H63 & Hstk & Htp & Herrw). pose proof S10_regs as (R1 & R2 & R4' & _).
pose proof S10_mem as (W1 & _). pose proof POST_facts as (W5 & B5 & _). pose proof YM05.alloc_ceiling_val.
pose proof Qblk as (Q1 & Q2 & Q3 & Q4). pose proof Mrange as (M0 & M1 & M2).
assert (ESP : spZ regs10 = SPa - 64) by (unfold spZ; rewrite R2; apply lit64_small; lia).
unfold call_pre. rewrite ESP. split.
{ apply (MRx_frame_gen L5 A5 mem5 mem10 md5 Qa (Qa + Ma) MX5 Hceil).
- intros x Hx N1 N2 N3. apply RAW105; assumption.
- intros x Hx. cbn beta in Hx. destruct (Q4 (x - Qa) ltac:(lia)) as [Pq Oq]. replace (Qa + (x - Qa)) with x in Pq, Oq by lia.
split; [exact Oq|]. intros _. apply (present_same mem9).
+ apply RAW10; [lia | unfold STKa; intro; lia].
+ unfold mem9. destruct (present_same mem5 mem8 x (RAW8 x ltac:(lia) ltac:(unfold STKa; intro; lia)) Pq) as [b Hb].
unfold present. destruct (wbytes mem8 (Z_to_bv 64 Qa) bs (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; reflexivity|].
exfalso. apply (wbytes_grows bs mem8 (Z_to_bv 64 Qa) (Z_to_bv 64 x)); [rewrite Hb; discriminate | exact Eb]. }
split; [exact W5|]. split; [exact B5|]. split; [rewrite R1; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite <- Zminus_mod_idemp_l, Hal; reflexivity|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
split; [intros x Hx; apply W1; unfold STKa, ALLOC_STACK in *; lia|].
split; [rewrite R4'; exact Htp|]. split.
{ intros x Hx. pose proof (errno_img x ltac:(exact Hx)) as Hi. unfold in_img1 in Hi.
apply (writable_same2 mem5 mem10); [apply RAW105; [lia | unfold STKa; intro; lia |] |].
{ intros HQ. apply (anyblock_off_img L5 A5 mem5 md5 q n x M5 q_in5); [unfold Qa in HQ; lia | unfold in_img1; lia]. }
apply errno_writable5. exact Hx. }
intros Hf. rewrite (init_done_of_block A5 _ W5 q_in5) in Hf. discriminate.
Qed.
Lemma free_call :
mreal src0segs (mkCfg ms10 md5) (free (Some p) A5)
(fun r c => free_leaf src0_msyms (MRx src0_msyms) L5 A5 regs10 mem10 md5 p nold r c /\
(length (st_regions A5) <= length (st_regions (snd r)))%nat).
Proof using E9 FREE HK HW Hin LEN5 MX5 UB5 UBA mem9.
destruct G10_shape as (Hpc & Hrv & _). pose proof S10_regs as (_ & _ & _ & R10 & _).
rewrite (st_ok_mkst src0segs E9 _ _ HS10 Hrv), Hpc.
apply mreal_tall; [| apply free_regions_tall].
apply FREE; [exact pre10 | exact p_in5 | rewrite R10, P5; reflexivity].
Qed.
Section y.
Variables (L11 : layout) (A11 : astate) (regs11 : bvmap 5 word) (mem11 : word -> option byte) (md11 : Model).
Variables (k1 k2 : list (sptr * Z)).
Hypothesis POSTF : call_post src0_msyms (MRx src0_msyms) L5 A5 regs10 mem10 md5 (fun x => ptr_addr L5 p <= x < ptr_addr L5 p + nold) L11 A11 regs11 mem11 md11.
Hypothesis UB5' : user_blocks A5 = k1 ++ (p, nold) :: k2.
Hypothesis UB11 : user_blocks A11 = k1 ++ k2.
Let MX11 : MRx src0_msyms L11 A11 mem11 md11 := proj1 POSTF.
Lemma M11 : MRc src0_msyms L11 A11 mem11 md11. Proof using MX11. exact (MRx_MRc _ _ _ _ _ MX11). Qed.
Lemma Hmd11 : m_halted md11 = None /\ m_vm_lazy md11 = [] /\ m_vm_materialized md11 = [].
Proof using MX11. exact (mc_md _ _ _ _ _ M11). Qed.
Lemma POSTF_facts :
WF A11 /\ bounded A11 /\ layout_le A5 L5 L11 /\
(forall b k, In (b, k) (user_blocks A5) -> In (b, k) (user_blocks A11) -> ptr_addr L11 b = ptr_addr L5 b) /\
regs_preserved regs10 regs11 /\ (exists vm', md11 = with_vmmaps vm' md5) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img src0_msyms x) ->
~ owned src0_msyms L5 A5 x -> ~ owned src0_msyms L11 A11 x -> ~ scratch src0_msyms regs10 x -> ~ (Pa <= x < Pa + nold) ->
mbyte src0segs mem11 x = mbyte src0segs mem10 x /\ (writable_at src0segs mem10 x <-> writable_at src0segs mem11 x)) /\
(forall b k i, In (b, k) (user_blocks A5) -> In (b, k) (user_blocks A11) -> 0 <= i < k ->
mbyte src0segs mem11 (ptr_addr L5 b + i) = mbyte src0segs mem10 (ptr_addr L5 b + i)) /\
(forall x, scratch src0_msyms regs10 x -> writable_at src0segs mem11 x).
Proof using Hin POST POSTF UB5 UBA.
pose proof POSTF as (_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). rewrite P5 in H7.
repeat (split; [assumption|]). exact H9.
Qed.
Lemma scratch10 x : scratch src0_msyms regs10 x <-> (SPa - 8256 <= x < SPa - 64) \/ ERRa x.
Proof using E9 HK HW Hin LEN5 MX5 UB5.
pose proof S10_regs as (_ & R2 & _). pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
unfold scratch, spZ. rewrite R2, lit64_small by lia. unfold ALLOC_STACK, ERRa. rewrite ERRNO2_val.
change (errno_addr src0_msyms) with (src0_tp + -164). lia.
Qed.
Lemma q_cases :
(exists u, k1 = l1 ++ (q, n) :: u /\ l2 = u ++ (p, nold) :: k2) \/
(exists u, l1 = k1 ++ (p, nold) :: u /\ k2 = u ++ (q, n) :: l2).
Proof using Hin POST UB5 UB5' UBA.
apply app_mid_cases; [rewrite <- UB5, <- UB5'; reflexivity|].
intros E0. injection E0 as Eq _. exact (q_neq_p Eq).
Qed.
Lemma q_in11 : In (q, n) (user_blocks A11).
Proof using Hin POST UB11 UB5 UB5' UBA.
rewrite UB11. destruct q_cases as [(u & -> & _) | (u & _ & ->)]; apply in_or_app.
- left. apply in_or_app. right. left. reflexivity.
- right. apply in_or_app. right. left. reflexivity.
Qed.
Lemma blocks11 : exists a1 a2 m1 m2, user_blocks A = a1 ++ (p, nold) :: a2 /\ m1 ++ m2 = a1 ++ a2 /\ user_blocks A11 = m1 ++ (q, n) :: m2.
Proof using Hin POST UB11 UB5 UB5' UBA.
rewrite UBA, UB11. destruct q_cases as [(u & -> & ->) | (u & -> & ->)].
- exists (l1 ++ u), k2, l1, (u ++ k2). rewrite <- !app_assoc. cbn. repeat split; reflexivity.
- exists k1, (u ++ l2), (k1 ++ u), l2. rewrite <- !app_assoc. cbn. repeat split; reflexivity.
Qed.
Lemma A_sub_A5 b k : In (b, k) (user_blocks A) -> In (b, k) (user_blocks A5).
Proof using UB5 UBA. rewrite UBA, UB5. intros H. apply in_app_iff in H. apply in_or_app. destruct H; [left | right; right]; assumption. Qed.
Let E11 := EV (xg regs11 nold Qa).
Lemma CS11 j : In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr regs11 (nat_to_reg j) = getr regs10 (nat_to_reg j).
Proof using Hin LEN5 POST POSTF UB5 UBA.
intros Hj. destruct POSTF_facts as (_ & _ & _ & _ & PRES & _).
assert (H : (1 <= j <= 31)%nat /\ callee_saved (Z.of_nat j)).
{ unfold callee_saved. cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [split; [lia|lia] |]). destruct Hj. }
destruct H as [H1 H2]. rewrite <- (lit5 j) by lia. apply PRES. exact H2.
Qed.
Lemma frame_kept11 x : SPa - 64 <= x < SPa ->
mbyte src0segs mem11 x = mbyte src0segs mem10 x /\ (writable_at src0segs mem10 x <-> writable_at src0segs mem11 x).
Proof using E9 HK HW Hin LEN5 MX11 MX5 UB5 UBA.
intros Hx. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val. pose proof Pblk as (P1 & P0 & P2 & _).
destruct POSTF_facts as (_ & _ & _ & _ & _ & _ & FR & _). apply FR.
- left. lia.
- intros Ho. pose proof (owned_low _ L5 A5 mem5 md5 x M5 Ho). lia.
- intros Ho. pose proof (owned_low _ L11 A11 mem11 md11 x M11 Ho). lia.
- intros Hs. apply scratch10 in Hs. unfold ERRa in Hs. rewrite ERRNO2_val in Hs. unfold src0_tp in Hs. lia.
- lia.
Qed.
Lemma stk_writable11 x : STKa x -> writable_at src0segs mem11 x.
Proof using E9 HK HW Hin LEN5 MX11 MX5 UB5 UBA.
intros Hx. destruct (Z_lt_le_dec x (SPa - 64)).
- apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 POSTF_facts)))))))). apply scratch10. left. unfold STKa in Hx. lia.
- apply (proj1 (proj2 (frame_kept11 x ltac:(unfold STKa in Hx; lia)))). apply (proj1 S10_mem). exact Hx.
Qed.
Lemma regs_ok11 : regs_ok E11 regs_callG regs11.
Proof using E9 HK HW Hin LEN5 MX5 POSTF UB5 UBA.
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq.
pose proof S10_regs as (R1 & R2 & R4' & R10 & RK & R8 & R9).
pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val as HCV.
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_callG]; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_junkG regs11 nold Qa Hnv Hq) by lia; reflexivity).
all: rewrite CS11 by (cbn; tauto); cbn [nat_to_reg].
- rewrite R2, (den_off _ (xg_range regs11 nold Qa Hnv Hq)), xg_SP; [reflexivity|]. rewrite xg_SP. lia.
- pose proof (RK 3%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; lia.
- pose proof (RK 4%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; unfold aTP; lia.
- rewrite R8, (den_xg regs11 nold Qa Hnv Hq), xg_q. reflexivity.
- rewrite R9, (den_xg regs11 nold Qa Hnv Hq), xg_P. reflexivity.
- pose proof (RK 23%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; lia.
- pose proof (RK 24%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; lia.
- pose proof (RK 25%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; lia.
- pose proof (RK 26%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; lia.
- pose proof (RK 27%nat ltac:(cbn; tauto)) as K. cbn [nat_to_reg] in K. rewrite K. symmetry. apply den_regG; lia.
Qed.
Lemma st_ok11 : st_ok src0segs E11 G11 (mkst regs11 (Z_to_bv 64 RA_FREE) mem11 (seg_rom src0segs)).
Proof using E9 HK HW Hin LEN5 MX11 MX5 UB5 UBA.
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts G11 resv_denot].
repeat (split; [reflexivity|]). split; [exact regs_ok11|]. split.
- apply (mem_ok_xfer regs9 nold Qa regs11 nold Qa mem10 mem11 Hnv Hq Hnv Hq (proj2 S10_mem)).
+ intros x Hx. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
rewrite <- (mbyte_off_img2 mem11 x), <- (mbyte_off_img2 mem10 x) by (unfold in_img1; first [lia | intro; lia]).
apply (proj1 (frame_kept11 x Hx)).
+ apply stk_writable11.
- apply facts_q; left; reflexivity.
Qed.
Lemma leaf_some :
SR src0segs (mkCfg (mkst regs11 (Z_to_bv 64 RA_FREE) mem11 (seg_rom src0segs)) md11)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n (Some q, A11)).
Proof using E11 E9 HK HW Hin LEN5 MX11 MX5 NZ5 UB11 UB5 UB5' UBA mem9.
destruct Hmd11 as (Hh11 & Hlz11 & Hmat11). pose proof PREf as (Hret & Hal & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val as HCV.
pose proof Hnv7 as Hnv. pose proof Hq7 as Hq. pose proof Pblk as (P1 & P0 & P2 & _). pose proof Qblk as (Q1 & Q2 & Q3 & Q4).
pose proof Mrange as (M0 & M1 & M2).
eapply SR_bind; [exact (G12_run E11 _ md11 Hh11 Hlz11 st_ok11)|]. intros c12 (ms12 & -> & HS12 & HF12). cbn [ms_mem] in HF12.
destruct G12_shape as (Hpc12 & Hrv12 & Hview12 & Ha012 & Hsm12).
pose proof (st_ok_regs_ok src0segs E11 _ _ HS12) as R12.
unfold callee_view, callee_view0, view in Hview12. cbn [map] in Hview12.
vnth Hview12 0%nat V1. vnth Hview12 1%nat V2. vnth Hview12 2%nat V3. vnth Hview12 3%nat V4. vnth Hview12 4%nat V8. vnth Hview12 5%nat V9.
vnth Hview12 6%nat V18. vnth Hview12 7%nat V19. vnth Hview12 8%nat V20. vnth Hview12 9%nat V21. vnth Hview12 10%nat V22. vnth Hview12 11%nat V23.
vnth Hview12 12%nat V24. vnth Hview12 13%nat V25. vnth Hview12 14%nat V26. vnth Hview12 15%nat V27.
assert (CV : forall i, In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
getr (ms_regs ms12) (nat_to_reg i) = getr regs (nat_to_reg i)).
{ intros i Hi0. rewrite <- (den_regG regs11 nold Qa Hnv Hq i) by (cbn in Hi0; lia).
rewrite (R12 (nat_to_reg i)). f_equal. cbn in Hi0.
repeat (destruct Hi0 as [<-|Hi0]; [cbn [nat_to_reg]; assumption|]). destruct Hi0. }
assert (E1 : ew E11 1 = getr regs 1).
{ pose proof (den_regG regs11 nold Qa Hnv Hq 1 ltac:(lia)) as D. cbn [sv_denot] in D.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D. exact D. }
assert (RAW12 : forall x, 0 <= x < 2 ^ 64 -> ~ STKa x -> ms_mem ms12 (Z_to_bv 64 x) = mem11 (Z_to_bv 64 x)).
{ intros x Hx N1. apply HF12. rewrite lit64_small by lia. intros W. apply wr_after in W. rewrite (base_SPG regs11 _ _ Hnv Hq : base_val E11 (Some aSP) = SPa) in W. exact (N1 W). }
eapply (SR_realloc_ret E11 G12 ms12 md11 _ HS12 Hrv12 Hpc12 V1); [rewrite E1; exact Hret | exact Hh11 | exact Hlz11 |].
destruct POST_facts as (W5 & B5 & LE5 & AD5 & PRES5 & VM5 & FR5 & BL5 & SC5).
destruct POSTF_facts as (W11 & B11 & LE11 & AD11 & PRES11 & VM11 & FR11 & BL11 & SC11).
assert (AQ : ptr_addr L11 q = Qa) by (unfold Qa; apply (AD11 q n); [exact q_in5 | exact q_in11]).
unfold realloc_leaf. exists L11, (ms_regs ms12), (ms_mem ms12), md11. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [| split; [| split; [| split; [exact blocks11 |]]]].
2:{ rewrite (R12 10%bv), Ha012, (den_xg regs11 nold Qa Hnv Hq), xg_q, AQ. reflexivity. }
2:{ rewrite AQ. lia. }
2:{   intros i Hi. rewrite AQ. change (ms_segs src0_msyms) with src0segs.
assert (Hi' : 0 <= i < Ma) by (unfold Ma; lia).
assert (NSq : ~ STKa (Qa + i)) by (unfold STKa; intro; lia).
assert (NSp : ~ STKa (Pa + i)) by (unfold STKa; intro; lia).
change (ptr_addr L p) with Pa.
rewrite (proj1 (same_byte_views2 mem11 (ms_mem ms12) _ (RAW12 (Qa + i) ltac:(lia) NSq))).
pose proof (BL11 q n i q_in5 q_in11 ltac:(lia)) as E11q. change (ptr_addr L5 q) with Qa in E11q. rewrite E11q.
rewrite (proj1 (same_byte_views2 mem9 mem10 _ (RAW10 (Qa + i) ltac:(lia) NSq))).
rewrite (copy9 i Hi').
rewrite (proj1 (same_byte_views2 mem5 mem8 _ (RAW8 (Pa + i) ltac:(lia) NSp))).
pose proof (BL5 p nold i Hin p_in5 ltac:(lia)) as E5p. change (ptr_addr L p) with Pa in E5p. rewrite E5p.
apply (proj1 (same_byte_views2 mem mem4 _ (RAW4 (Pa + i) ltac:(lia) NSp ltac:(intros He; exact (anyblock_off_img L A mem md p nold (Pa + i) M Hin ltac:(unfold Pa; lia) (errno_img _ He)))))). }
pose proof (st_ok_mem_ok src0segs E11 _ _ HS12) as (_ & ROK12 & _). rewrite Hsm12 in ROK12. apply Forall_inv in ROK12.
destruct ROK12 as (_ & _ & W12 & _). cbn [r_base r_wlo r_whi] in W12. rewrite (base_SPG regs11 _ _ Hnv Hq : base_val E11 (Some aSP) = SPa) in W12.
unfold call_post_k. change (ms_segs src0_msyms) with src0segs.
split; [| split; [exact W11 | split; [exact B11 | split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
-   apply (MRx_scratch L11 A11 mem11 (ms_mem ms12) md11 MX11 Hceil). intros x Hx N1 _. exact (RAW12 x Hx N1).
-   destruct LE5 as (C1 & C2 & C3 & C4). destruct LE11 as (D1 & D2 & D3 & D4).
split; [congruence|]. split; [congruence|]. split; [congruence|]. intros r Hr. rewrite D4 by (pose proof LEN5; lia). apply C4. exact Hr.
-   intros b k Hb HbF. rewrite (AD11 b k (A_sub_A5 b k Hb) HbF). apply (AD5 b k); [exact Hb | exact (A_sub_A5 b k Hb)].
-   intros r Hr. destruct (callee_saved_cases r Hr) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r Rr). apply CV. cbn. cbn in RI. tauto.
-   destruct VM5 as [v1 ->]. destruct VM11 as [v2 ->]. exists v2. apply with_vmmaps_twice.
-   intros x Hx N1 N2 N3 N4.
assert (Hx64 : 0 <= x < 2 ^ 64) by (destruct Hx as [Hx|Hx]; [lia | apply src0_img_range in Hx; unfold in_img1 in Hx; lia]).
assert (NS : ~ STKa x /\ ~ ERRa x).
{ unfold scratch_k, REALLOC_STACK, ALLOC_STACK in N3. unfold STKa, ERRa. rewrite ERRNO2_val. change (errno_addr src0_msyms) with (src0_tp + -164) in N3. change (spZ regs) with SPa in N3. split; intro; apply N3; lia. }
destruct NS as [NS1 NS2].
assert (N5 : ~ owned src0_msyms L5 A5 x).
{ destruct Hx as [Hx|Hx]; [intros Ho; pose proof (owned_low _ L5 A5 mem5 md5 x M5 Ho); lia|].
intros Ho. exact (N1 (owned_img_any L A mem md L5 A5 mem5 md5 x M M5 Hx Ho)). }
assert (NQ : ~ (Qa <= x < Qa + Ma)).
{ destruct Hx as [Hx|Hx]; [lia|]. intros HQ. exact (anyblock_off_img L5 A5 mem5 md5 q n x M5 q_in5 ltac:(unfold Qa in HQ; lia) (src0_img_range _ Hx)). }
destruct (same_byte_views2 mem11 (ms_mem ms12) x (RAW12 x Hx64 NS1)) as [A1 A2].
destruct (FR11 x Hx N5 N2 ltac:(intros Hs; apply scratch10 in Hs; destruct Hs as [Hs|Hs]; [unfold STKa in NS1; lia | exact (NS2 Hs)]) ltac:(unfold Pa; intro; apply N4; lia)) as [B1 B2].
destruct (same_byte_views2 mem5 mem10 x (RAW105 x Hx64 NS1 NQ)) as [C1 C2].
destruct (FR5 x Hx N1 N5 ltac:(intros Hs; apply scratch4 in Hs; destruct Hs as [Hs|Hs]; [unfold STKa in NS1; lia | exact (NS2 Hs)])) as [D1 D2].
destruct (same_byte_views2 mem mem4 x (RAW4 x Hx64 NS1 NS2)) as [F1 F2].
rewrite A1, B1, C1, D1, F1. tauto.
-   intros b k i Hb HbF Hi.
pose proof (A_sub_A5 b k Hb) as Hb5.
pose proof (mr_blocks_range _ _ (MRx_laws src0_msyms) L A mem md b k MX Hb) as [Lo Hi2].
assert (Hx64 : 0 <= ptr_addr L b + i < 2 ^ 64) by lia.
assert (NS1 : ~ STKa (ptr_addr L b + i)) by (unfold STKa; intro; lia).
assert (NS2 : ~ ERRa (ptr_addr L b + i)) by (intros He; exact (anyblock_off_img L A mem md b k (ptr_addr L b + i) M Hb ltac:(lia) (errno_img _ He))).
assert (Eb5 : ptr_addr L5 b = ptr_addr L b) by (apply (AD5 b k); assumption).
assert (NQ : ~ (Qa <= ptr_addr L b + i < Qa + Ma)).
{ pose proof (mr_blocks_disjoint _ _ (MRx_laws src0_msyms) L5 A5 mem5 md5 MX5) as PW. unfold blocks in PW. rewrite UB5 in PW.
pose proof Hb as Hb'. rewrite UBA in Hb'.
change (l1 ++ (q, n) :: l2) with (l1 ++ [(q, n)] ++ l2) in PW.
destruct (YN26.pairwise_app_mid ranges_disjoint (fun b0 : sptr * Z => (ptr_addr L5 (fst b0), snd b0)) l1 [(q, n)] l2 (q, n) (b, k) PW ltac:(left; reflexivity) Hb') as [D|D];
unfold ranges_disjoint in D; cbn [fst snd] in D; rewrite Eb5 in D; unfold Qa; lia. }
rewrite (proj1 (same_byte_views2 mem11 (ms_mem ms12) _ (RAW12 _ Hx64 NS1))).
rewrite <- Eb5. rewrite (BL11 b k i Hb5 HbF Hi). rewrite Eb5.
rewrite (proj1 (same_byte_views2 mem5 mem10 _ (RAW105 _ Hx64 NS1 NQ))).
rewrite (BL5 b k i Hb Hb5 Hi). apply (proj1 (same_byte_views2 mem mem4 _ (RAW4 _ Hx64 NS1 NS2))).
-   intros x Hs. unfold scratch_k, REALLOC_STACK, ALLOC_STACK in Hs.
change (errno_addr src0_msyms) with (src0_tp + -164) in Hs. change (spZ regs) with SPa in Hs.
destruct Hs as [Hs|Hs].
+ replace x with (SPa + (x - SPa)) by lia. apply W12. lia.
+ apply (writable_same2 mem11 (ms_mem ms12) x); [apply RAW12; [unfold src0_tp in Hs; lia | unfold STKa; unfold src0_tp in Hs; intro; lia] |].
apply SC11. apply scratch10. right. unfold ERRa. rewrite ERRNO2_val. lia.
Qed.
End y.
End w.
End v.
End s.
Theorem fb_main :
mreal src0segs (mkCfg (mkst regs4 (Z_to_bv 64 src0_A_libc_malloc_impl) mem4 (seg_rom src0segs)) md)
(realloc_move p n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n).
Proof using FREE HW Hin MALLOC MEMCPY.
unfold realloc_move. eapply mreal_mbind; [exact malloc_call|].
intros q A5 c5 [HL LEN5]. cbn [snd] in LEN5.
destruct HL as (L5 & regs5 & mem5 & md5 & -> & POST & Hq). cbn [fst snd] in POST, Hq.
change (ms_segs src0_msyms) with src0segs in *. rewrite (proj1 R4).
destruct q as [q|].
- destruct Hq as (A0 & NZ & (l1 & l2 & UB5 & UBA) & _).
eapply mreal_SR_pre; [eapply to_S10; eassumption|].
intros c10 (regs9 & mem8 & bs & ms10 & -> & HK).
eapply mreal_mbind; [eapply free_call; eassumption|].
intros [] A11 c11 [HFL LEN11]. cbn [snd] in LEN11.
destruct HFL as (L11 & regs11 & mem11 & md11 & -> & POSTF & (k1 & k2 & UB5' & UB11)). cbn [fst snd] in POSTF, UB5', UB11.
edestruct S10_regs as (F1 & _); try eassumption.
unfold ret. apply mreal_leaf. change (ms_segs src0_msyms) with src0segs in *. rewrite F1.
eapply leaf_some; eassumption.
- destruct Hq as [A0 UB]. unfold ret. apply mreal_leaf. eapply leaf_none; eassumption.
Qed.
End FB.
Theorem fb_gen_of_api : malloc_impl_realizes -> free_impl_realizes -> memcpy_spec -> OBL_fb_gen.
Proof using.
intros HM HF HC L A regs mem md p nold n regs4 mem4 FA.
exact (fb_main HM HF HC L A regs mem md p nold n regs4 mem4 FA).
Qed.
End h.
