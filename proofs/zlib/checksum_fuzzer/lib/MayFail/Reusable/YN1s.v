(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1s.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN22.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma DEB_facts : 0x10000 <= DEB /\ DEB + 32 <= 0x51000. Proof. unfold DEB, src0_D_debruijn32. lia. Qed.
Section g.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z).
Hypothesis PRE : call_pre B (MRx B) L A regs mem md.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte).
Hypothesis AT : at_PA regs mem n regs1 mem1.
Variable regs2 : bvmap 5 word.
Hypothesis PBS : at_PB L A regs n regs2.
Variables (gm : sptr) (am : ameta).
Hypothesis Hhd : active_hd A (sc A n) = Some gm.
Hypothesis Mg : MT A gm = Some (MUsed am).
Hypothesis Hav : am_avail am <> 0.
Let rom := seg_rom src0segs.
Let SP0 : Z := spZ regs.
Definition mask : Z := am_avail am.
Definition first : Z := lowbit mask.
Definition idx : Z := ctz32 first.
Definition jidx : Z := srlw (mul64 (sx32 first) DBJ_MUL) 27.
Definition am2 : ameta := am_set_avail (mask - first) am.
Definition A2 : astate := upd_meta gm (MUsed am2) A.
Definition G : Z := ptr_addr L gm.
Lemma PRE_facts : MRx B L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\
SP0 mod 16 = 0 /\ alloc_ceiling + 8192 <= SP0 /\ SP0 < 2 ^ 63 /\
(forall a, SP0 - 8192 <= a < SP0 -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at src0segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) SP0 mem).
Proof. unfold call_pre, ALLOC_STACK in PRE. exact PRE. Qed.
Lemma HI : Inv [] None U0 A. Proof. exact (HI L A regs mem md PRE). Qed.
Lemma MID1 : midrep B L A mem1 md. Proof. exact (MID1 L A regs mem md n PRE regs1 mem1 AT). Qed.
Lemma MR1 : memrepX B [] L A mem1. Proof. exact (MR1 L A regs mem md n PRE regs1 mem1 AT). Qed.
Lemma Hctx : ly_ctx L = YN0t.CTX. Proof. exact (Hctx L A regs mem md n PRE regs1 mem1 AT). Qed.
Lemma gm_facts : usedX [] A gm am /\ am_sc am = (sc A n) /\ 0 <= (sc A n) < 48 /\ n + IB <= class_size (sc A n) /\
4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall x, G <= x < G + 40 -> ~ in_img B x) /\
0 < mask < 2 ^ 32 /\ 0 <= am_freed am < 2 ^ 32.
Proof.
destruct (sc_head L A regs mem md n PRE Hn gm Hhd) as (am' & Hu & Hsc & M'). rewrite Mg in M'. injection M' as <-.
pose proof (sc_range L A regs mem md n PRE Hn) as [R F].
destruct (meta_facts [] None U0 L A md HI (mid_ledger _ _ _ _ _ MID1) gm am Hu) as (M1 & M2 & M3 & M4 & _).
pose proof (mask_range L A regs mem md PRE gm am Hu) as [[R1 R1'] R2]. unfold mask in *.
repeat (split; [assumption|]). split; [|exact R2]. pose proof Hav. unfold mask. lia.
Qed.
Lemma take_facts : 0 <= idx < 32 /\ first = bit idx /\ Z.testbit mask idx = true /\ Inv [] (Some (gm, idx)) U0 A2 /\
0 <= idx <= am_last am /\ n + IB <= stride_of am /\ 0 <= jidx < 32 /\ znth jidx DEBRUIJN = idx /\
0 < first <= mask /\ length (am_slots am) = Z.to_nat (am_last am + 1).
Proof.
pose proof gm_facts as (Hu & Hsc & R & F & _ & _ & _ & _ & Mr & _).
pose proof (take_bit_Inv [] U0 A gm am HI Hu ltac:(lia) ltac:(rewrite Hsc; exact Hhd) Hav) as (K1 & K2 & K3 & K4).
pose proof (inv_groups HI gm am Hu) as ((Glast & Gaidx & Glen & _) & _).
pose proof (avail_bit_not_undersized [] None U0 A gm am idx HI Hu ltac:(lia) ltac:(unfold idx, first, mask in *; lia) ltac:(rewrite Z.lor_spec; unfold idx, first, mask in *; rewrite K3; reflexivity)) as US.
pose proof (dbj_ctz32 mask ltac:(lia)) as [J1 J2]. pose proof (lowbit_le mask ltac:(lia)) as LB.
pose proof (ctz32_lt (lowbit mask) 32 ltac:(lia) ltac:(lia)) as CR.
assert (CZ : ctz32 (lowbit (am_avail am)) = ctz32 (am_avail am)) by (pose proof Mr as Mr'; unfold mask in Mr'; unfold ctz32; rewrite lowbit_lowbit by lia; reflexivity).
unfold A2, am2, jidx, idx, first, mask in *. rewrite Hsc in US. rewrite !CZ in *.
repeat (split; [assumption || lia|]). exact Glen.
Qed.
Definition xv2 (i : nat) : Z :=
if (i <? 32)%nat then bv_unsigned (getr regs2 (nat_to_reg i))
else match i with 42%nat => mask | 43%nat => DEB + jidx | 44%nat => idx | _ => 0 end.
Lemma xv2_reg k : (k <= 31)%nat -> xv2 k = bv_unsigned (getr regs2 (nat_to_reg k)).
Proof. intros Hk. unfold xv2. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma X18 : xv2 18%nat = G.
Proof.
pose proof gm_facts as (_ & _ & _ & _ & G1 & G2 & _). pose proof (proj1 alloc_ceiling_val).
rewrite xv2_reg by lia. change (nat_to_reg 18) with (18%bv : bv 5). rewrite (pb_18 _ _ _ _ _ PBS). unfold gaddr. rewrite Hhd. cbn [optrZ]. apply lit64_small. unfold G in *. lia.
Qed.
Lemma X8 : xv2 8%nat = n.
Proof. rewrite xv2_reg by lia. change (nat_to_reg 8) with (8%bv : bv 5). rewrite (pb_8 _ _ _ _ _ PBS). apply lit64_small. unfold MMAP_THRESHOLD in Hn. lia. Qed.
Lemma X2 : xv2 2%nat = SP0 - 48.
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & _ & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val).
rewrite xv2_reg by lia. change (nat_to_reg 2) with (2%bv : bv 5). rewrite (pb_2 _ _ _ _ _ PBS). apply lit64_small. unfold SP0 in *. lia.
Qed.
Lemma XR2 : forall k, 0 <= xv2 k < 2 ^ 64.
Proof.
intros k. pose proof gm_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Mr & _). pose proof take_facts as (I1 & _ & _ & _ & _ & _ & J & _).
unfold xv2. destruct (k <? 32)%nat; [apply u64_range|]. pose proof DEB_facts. do 45 (destruct k as [|k]; [lia|]). lia.
Qed.
Local Abbreviation E2 := (EV xv2).
Lemma mask_denot : bv_unsigned (sv_denot E2 MASKX) = sx32 mask.
Proof. unfold MASKX, E2. rewrite (U_sext32 xv2), (U_off0 xv2 XR2). reflexivity. Qed.
Lemma lowbit_denot : bv_unsigned (sv_denot E2 LOWBIT) = sx32 first /\ bv_unsigned (sv_denot E2 LOWBIT) <> 0.
Proof.
pose proof gm_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Mr & _).
exact (take_first_word (sv_denot E2 MASKX) (sv_denot E2 LOWBIT) mask Mr mask_denot eq_refl).
Qed.
Lemma tqaddr_denot : sv_denot E2 TQADDR = Z_to_bv 64 (DEB + jidx).
Proof.
pose proof take_facts as (_ & _ & _ & _ & _ & _ & J & _). destruct lowbit_denot as [L1 _].
apply word_eq. unfold TQADDR. cbn [sv_denot]. rewrite alu64_add, srlw_rr_unsigned, mul64_unsigned, L1.
change (bv_unsigned (Z_to_bv 64 DBJ)) with DBJ_MUL. change (bv_unsigned (Z_to_bv 64 27)) with 27. fold jidx.
pose proof DEB_facts. rewrite (lit64_small DEB) by lia. rewrite (lit64_small (DEB + jidx)) by lia.
apply add64_small. lia.
Qed.
Lemma avail'_denot : bv_unsigned (sv_denot E2 AVAIL') mod 2 ^ 32 = mask - first.
Proof.
pose proof gm_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Mr & _). destruct lowbit_denot as [L1 _].
unfold AVAIL'. cbn [sv_denot]. fold (sv_denot E2 MASKX). fold (sv_denot E2 LOWBIT).
pose proof (take_rest_word (sv_denot E2 MASKX) (sv_denot E2 LOWBIT) _ mask Mr mask_denot L1 eq_refl) as R.
rewrite low32_unsigned in R. unfold lo32 in R. exact R.
Qed.
Lemma T2f_st_ok : st_ok src0segs E2 ss_T2f (mkst regs2 (Z_to_bv 64 PB) mem1 rom).
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof gm_facts as (Hu & Hsc & R & F & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_facts as (I1 & _ & _ & _ & I2 & _ & J & Jz & _).
pose proof (off_img G Gimg) as GF. destruct lowbit_denot as [L1 L2].
pose proof (mid_statics _ _ _ _ _ MID1) as ST.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T2f resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok_sv. intros k Hk.
destruct (Nat.eq_dec k 10) as [->|Hk10].
{ cbn [find fst Nat.eqb]. change (nat_to_reg 10) with (10%bv : bv 5). rewrite (pb_10 _ _ _ _ _ PBS). apply word_eq. rewrite mask_denot.
unfold gmask. rewrite Hhd. unfold avail_of, amo. rewrite Mg. apply lit64_small. apply sx32_range. }
destruct (Nat.eq_dec k 9) as [->|Hk9]; [cbn; exact (pb_9 _ _ _ _ _ PBS)|].
destruct (Nat.eq_dec k 19) as [->|Hk19]; [cbn; exact (pb_19 _ _ _ _ _ PBS)|].
destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact (pb_4 _ _ _ _ _ PBS)|].
replace (find (fun p : nat * sv => Nat.eqb (fst p) k) [(10%nat, MASKX); (9%nat, SLit LOCK); (19%nat, SLit DEB); (4%nat, SLit TP)]) with (@None (nat * sv)).
2:{ cbn [find fst]. rewrite !(proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
rewrite xv2_reg by lia. symmetry. apply Z_to_bv_bv_unsigned.
- split; [vm_compute; reflexivity|]. split.
+ unfold t2f_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_gw]; rewrite (base_val_EV xv2 XR2), X18; [lia | lia | |].
{ intros o Ho. apply present_writable. apply (meta_present [] None U0 L A mem1 md HI MR1 (mid_ledger _ _ _ _ _ MID1) gm am _ Hu). unfold G in *. lia. }
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val xv2 _ _ _ 4); [apply (U_off0 xv2 XR2) | change (xv2 aAV) with mask; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia |].
change (xv2 aAV) with mask. exact (proj1 (meta_mask_cells L A regs mem md n PRE regs1 mem1 AT gm am Hu)).
* pose proof DEB_facts. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_tqj]; rewrite (base_val_EV xv2 XR2); change (xv2 aTQ) with (DEB + jidx); [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val xv2 _ _ _ 1); [apply (U_off0 xv2 XR2) | change (xv2 aJ) with idx; change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
change (xv2 aJ) with idx. rewrite Z.add_0_r, <- Jz. apply (deb_byte mem1 ST). exact J.
+ cbn [pairwise_disjoint all_disjoint t2f_mem]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_gw R_tqj].
rewrite !(base_val_EV xv2 XR2), X18. change (xv2 aTQ) with (DEB + jidx). pose proof DEB_facts. repeat split; try exact I. lia.
- split; [|split].
+ cbn [atoms_ok t2f_facts f_atoms]. unfold afact_ok; cbn [af_lo af_hi af_al2 F_sp48]; rewrite !(ew_EV xv2 XR2), X18, X2.
change (xv2 aAV) with mask. change (xv2 aTQ) with (DEB + jidx). change (xv2 aJ) with idx. pose proof DEB_facts. unfold CEIL.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; try lia. unfold SP0 in *. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
+ cbn [conds_ok t2f_facts f_conds]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b C_lb]. fold E2.
rewrite branch_ne. cbn [sv_denot]. fold (sv_denot E2 MASKX). fold (sv_denot E2 LOWBIT). rewrite (lit64_small 0) by lia.
destruct (Z.eqb_spec (bv_unsigned (sv_denot E2 LOWBIT)) 0); [exfalso; exact (L2 e) | reflexivity].
+ cbn [alias_ok t2f_facts f_alias]. split; [|exact I]. rewrite tqaddr_denot. rewrite (den_off0 xv2 XR2). reflexivity.
Qed.
Record at_PC (rg : bvmap 5 word) (mc : word -> option byte) : Prop := PC_ {
pc_18 : getr rg 18 = Z_to_bv 64 G;
pc_19 : getr rg 19 = Z_to_bv 64 idx;
pc_8 : getr rg 8 = Z_to_bv 64 n;
pc_9 : getr rg 9 = Z_to_bv 64 LOCK;
pc_2 : getr rg 2 = Z_to_bv 64 (SP0 - 48);
pc_4 : getr rg 4 = Z_to_bv 64 TP;
pc_cs : forall i, In i CSAVED -> getr rg (nat_to_reg i) = getr regs (nat_to_reg i);
pc_out : forall x, 0 <= x < 2 ^ 64 -> ~ (G + 24 <= x < G + 28) -> mc (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x);
pc_avail : bytes_are mc (G + 24) 4 (mask - first);
pc_win : forall a, G + 24 <= a < G + 28 -> writable_at src0segs mc a }.
Lemma T2f_post ms3 : st_ok src0segs E2 SST2f ms3 -> frame_of E2 t2f_mem mem1 (ms_mem ms3) ->
ms3 = mkst (ms_regs ms3) (Z_to_bv 64 PC) (ms_mem ms3) rom /\ at_PC (ms_regs ms3) (ms_mem ms3).
Proof.
intros HS1 HF. pose proof SST2f_view as V. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof gm_facts as (Hu & Hsc & R & F & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_facts as (I1 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (reg_of _ _ _ 18 _ HS1 ltac:(lia) ltac:(reg_eq V 0%nat)) as G18.
pose proof (reg_of _ _ _ 19 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G19.
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G2'.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 4%nat)) as G8'.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G9.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms3) (nat_to_reg i) = sv_denot E2 (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs SST2f) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 6%nat | reg_eq V 7%nat | reg_eq V 8%nat | reg_eq V 9%nat | reg_eq V 10%nat | reg_eq V 11%nat | reg_eq V 12%nat | reg_eq V 13%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
pose proof (st_ok_mem_ok src0segs _ _ _ HS1) as (_ & MOK & _). rewrite Hmem in MOK. apply Forall_inv in MOK.
destruct MOK as (_ & _ & WR & CH). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_gw'] in WR, CH. rewrite (base_val_EV xv2 XR2), X18 in WR, CH.
pose proof (Forall_inv CH) as C1.
pose proof (st_ok_mkst src0segs _ _ _ HS1 Hrv) as SHAPE. rewrite Hpc in SHAPE. clear V Hpc Hrv Hmem CH.
split; [exact SHAPE|]. split.
- change (18%bv : bv 5) with (nat_to_reg 18). rewrite G18. rewrite (den_off0 xv2 XR2), X18. reflexivity.
- change (19%bv : bv 5) with (nat_to_reg 19). rewrite G19. rewrite (den_off0 xv2 XR2). reflexivity.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8'. rewrite (den_off0 xv2 XR2), X8. reflexivity.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9. reflexivity.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2'. rewrite (den_off0 xv2 XR2), X2. reflexivity.
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- intros i Hi. rewrite (GS i Hi). rewrite (den_off0 xv2 XR2), xv2_reg by (pose proof (csaved_cases i Hi); lia).
rewrite Z_to_bv_bv_unsigned. apply (pb_cs _ _ _ _ _ PBS). exact Hi.
- intros x Hx Hnx. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx.
intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]]; cbn [r_base r_wlo r_whi R_gw R_tqj] in Hr; unfold E2 in Hr; rewrite (base_val_EV xv2 XR2) in Hr; [rewrite X18 in Hr|]; lia.
- rewrite <- avail'_denot. change (2 ^ 32) with (2 ^ (8 * Z.of_N 4)). apply (chunk_bytes xv2 _ _ _ 4 AVAIL'); [exact C1 | reflexivity].
- intros a Ha. replace a with (G + (a - G)) by lia. apply WR. lia.
Qed.
Section h.
Variables (rg : bvmap 5 word) (mc : word -> option byte).
Hypothesis APC : at_PC rg mc.
Lemma grp_same2 : grp_same am am2.
Proof. unfold am2. apply grp_same_avail. Qed.
Lemma A2_facts : footprint A2 = footprint A /\ st_regions A2 = st_regions A /\ st_areas A2 = st_areas A /\
MT A2 gm = Some (MUsed am2) /\ usedX [] A2 gm am2 /\ user_blocks A2 = user_blocks A /\ ub_same A A2.
Proof.
pose proof gm_facts as (Hu & _). pose proof take_facts as (_ & _ & _ & HI2 & _).
assert (UB : ub_same A A2).
{ unfold A2. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mg|]. rewrite Mg. cbn. unfold am2. apply blocks_of_avail. }
unfold A2. rewrite footprint_upd_meta. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [apply MT_upd_same|]. split; [apply usedX_upd; left; split; [reflexivity | split; [exact (proj2 (usedX_MT _ _ _ _ Hu)) | reflexivity]]|].
split; [| exact UB]. apply ub_same_user_blocks; [exact (proj1 (inv_keys HI)) | exact (proj1 (inv_keys HI2)) | exact UB].
Qed.
Definition cAV : mcell := MCell (LMem (padd gm META_avail)) 4 (VZ (mask - first)).
Lemma memrep2 : memrepX B [] L A2 mc.
Proof.
pose proof gm_facts as (Hu & Hsc & R & F & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_facts as (I1 & _ & _ & HI2 & _ & _ & _ & _ & LB & _).
pose proof A2_facts as (Efp & Erg & Ear & M2 & Hu2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (mid_layout _ _ _ _ _ MID1) as HL.
refine (memrepX_after B [] [] None (Some (gm, idx)) U0 U0 A A2 L mem1 mc [cAV] [] (alloc_ceiling, 0) HI HI2 HL Efp Erg MR1 _ _ _ _ _ _ _ _).
-
intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
+ destruct (imageX_upd_meta [] A gm am am2 c Mg grp_same2 Hc) as [Hm|Ho]; [|right; apply in_app_iff; left; exact Ho].
cbn [meta_slot_cells] in Hm.
assert (OLD : forall c', In c' (meta_slot_cells gm (Some (MUsed am))) -> In c' (imageX [] A ++ tail_cellsX [] A)).
{ intros c' Hc'. exact (old_meta_cell [] None U0 A HI gm am c' Hu Hc'). }
unfold am2, mask, first in Hm. unfold cAV, mask, first. destruct am as [pr nx mm av fr lst sc' ml ai sl] eqn:Eam.
cbn [am_prev am_next am_mem am_avail am_freed meta_bits am_last am_sc am_maplen am_set_avail] in Hm |- *.
cbn [meta_slot_cells am_prev am_next am_mem am_avail am_freed meta_bits am_last am_sc am_maplen] in OLD.
destruct Hm as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
[ right; apply OLD; left; reflexivity
| right; apply OLD; right; left; reflexivity
| right; apply OLD; do 2 right; left; reflexivity
| left; left; reflexivity
| right; apply OLD; do 4 right; left; reflexivity
| right; apply OLD; do 5 right; left; unfold meta_bits; cbn [am_last am_sc am_maplen]; reflexivity ].
+ right. apply in_app_iff. right. exact (tail_cellsX_upd_meta [] A gm am am2 c Mg grp_same2 Hc).
-
intros c [<-|[]]. left. apply (meta_cells_in_areas [] (Some (gm, idx)) U0 A2 HI2 gm am2 _ M2). unfold am2, cAV. destruct am; cbn. auto 10.
-
intros c [<-|[]]. unfold cell_mem, cAV. cbn [mc_val mc_loc mc_w sval_num]. rewrite loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_avail. fold G.
intros k Hk. rewrite (pc_avail _ _ APC k Hk). reflexivity.
-
intros c k [<-|[]] Hk _. unfold cAV in Hk |- *. cbn [mc_loc mc_w] in Hk |- *. rewrite loc_addr_padd'. fold G. unfold META_avail.
apply writable_off_img_present; [lia | | apply (pc_win _ _ APC); lia]. intros Hi. apply (Gimg (G + 24 + Z.of_nat k)); [lia|]. apply in_img1_in_img. exact Hi.
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. exact (footprint_hi [] None U0 L A md HI (mid_syms _ _ _ _ _ MID1) Hctx (mid_ledger _ _ _ _ _ MID1) e He).
- intros a Ha Hno _ _.
assert (NW : ~ (G + 24 <= a < G + 28)).
{ intros W. apply (Hno cAV (or_introl eq_refl)). unfold in_range, cell_range, cAV. cbn [fst snd mc_loc mc_w]. rewrite loc_addr_padd'. fold G. unfold META_avail. lia. }
pose proof (pc_out _ _ APC a Ha NW) as E. split; [apply mbyte_ext; exact E|]. intros [b Hb]. exists b. rewrite E. exact Hb.
Qed.
Lemma midrep2 : midrep B L A2 mc md.
Proof.
pose proof gm_facts as (Hu & Hsc & R & F & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_facts as (I1 & _ & _ & HI2 & _).
pose proof A2_facts as (Efp & Erg & Ear & M2 & Hu2 & UBe & UB). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof (off_img G Gimg) as GF.
split.
- exact (mid_syms _ _ _ _ _ MID1).
- apply (proj1 (memrepX_nil B L A2 mc)). apply memrep2.
-
unfold tail_geom. apply Forall_forall. intros c Hc k Hk.
assert (Hc' : In c (tail_cells A)).
{ pose proof (tail_cellsX_upd_meta [] A gm am am2 c Mg grp_same2) as T. unfold tail_cellsX in T. rewrite !used_metasX_nil in T. exact (T Hc). }
apply (alloc_owned_same L A2 A _ (eq_sym Efp) (eq_sym UBe)). exact (proj1 (Forall_forall _ _) (mid_tailg _ _ _ _ _ MID1) c Hc' k Hk).
- apply (statics_ok_ext B mem1 mc (mid_statics _ _ _ _ _ MID1)). intros a Hs. apply mbyte_ext. apply (pc_out _ _ APC).
+ pose proof (src0_img_range' a (so_statics_img _ (mid_syms _ _ _ _ _ MID1) a Hs)). lia.
+ intros W. apply (Gimg a); [lia|]. exact (so_statics_img _ (mid_syms _ _ _ _ _ MID1) a Hs).
- unfold A2. apply ledger_ok_upd_meta. exact (mid_ledger _ _ _ _ _ MID1).
- eapply ledger_x_same_regions; [exact (mid_ledgerx _ _ _ _ _ MID1) | exact Erg | reflexivity | reflexivity].
- unfold A2. apply (proj2 (layout_ok_upd_meta L gm _ A)). exact (mid_layout _ _ _ _ _ MID1).
- exact (mid_ctx _ _ _ _ _ MID1).
- exact (mid_sec _ _ _ _ _ MID1).
- exact (mid_md _ _ _ _ _ MID1).
Qed.
Lemma rsv2 : rsv_ok A2.
Proof.
pose proof gm_facts as (Hu & _). pose proof take_facts as (I1 & _ & _ & HI2 & I2 & _ & _ & _ & _ & Glen).
pose proof (MRx_rsv _ _ _ _ _ (proj1 PRE_facts)) as RS.
assert (SE : shape_eq am am2 idx) by (unfold am2; destruct am; cbn; repeat split; reflexivity).
destruct (inv_reserved HI2 gm idx eq_refl) as (am_ & Hu_ & _ & Hfr_ & _).
pose proof (usedX_fun _ _ _ _ _ Hu_ (proj1 (proj2 (proj2 (proj2 (proj2 A2_facts)))))) as ->.
intros g0 am0 i fr Hin Hk. destruct (frames_upd A gm am am2 idx g0 am0 i fr Mg SE Hfr_ Hin) as (am1 & Hin1 & Hst).
unfold reserved_of. rewrite <- Hst. apply (RS g0 am1 i fr Hin1 Hk).
Qed.
Theorem fast_tail :
mreal src0segs (mkCfg (mkst rg (Z_to_bv 64 PC) mc rom) md)
(ibind (enframe gm idx n (st_mmap_counter A2) FUser A2) (fun ps => IRet (Some (fst ps), snd ps)))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
pose proof PRE_facts as (MX & _ & HB & _ & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof gm_facts as (Hu & Hsc & R & F & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_facts as (I1 & _ & Hbit & HI2 & I2 & Hfit & _).
pose proof A2_facts as (Efp & Erg & Ear & M2 & Hu2 & UBe & UB).
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (Hh & Hlz & Hmat).
change (st_mmap_counter A2) with (ctr A2).
apply (succ_tail L A regs mem md n PRE Hn L A2 mc md gm am2 idx (sc A n) rg midrep2 HI2 Hu2).
- unfold am2. destruct am; cbn in *. split; [exact Hsc | exact R].
- unfold am2. destruct am; cbn in *. exact Hfit.
- unfold am2. destruct am; cbn in *. exact I2.
- unfold A2. apply (proj2 (bounded_upd_meta _ _ _)). exact HB.
- unfold ama_ok, A2 in *. cbn. exact (MRx_ama _ _ _ _ _ MX).
- apply rsv2.
- unfold A2. apply (span_ok_upd_same3 A gm am); [exact (MRx_span _ _ _ _ _ MX) | exact Mg | reflexivity | reflexivity | reflexivity].
- apply layout_le_refl.
- exists (m_vmmaps md). apply with_vmmaps_self; assumption.
- exact UB.
- exact (pc_18 _ _ APC).
- exact (pc_19 _ _ APC).
- exact (pc_8 _ _ APC).
- exact (pc_9 _ _ APC).
- unfold SPv. exact (pc_2 _ _ APC).
- exact (pc_4 _ _ APC).
- exact (pc_cs _ _ APC).
- intros off r Hin. unfold SPv. apply (bytes_are_ext mem1); [| exact (pa_frame _ _ _ _ _ AT off r Hin)].
assert (Hoff : 0 <= off <= 40).
{ unfold FRAME_SLOTS in Hin. cbn in Hin. decompose [or] Hin; try contradiction; match goal with H : (_, _) = (off, r) |- _ => injection H as <- <- end; lia. }
intros i Hi. apply (pc_out _ _ APC); unfold YN1p.SP0; lia.
- intros x Hx NO NO2 _ NS. rewrite (pc_out _ _ APC x Hx).
+ apply (pa_out _ _ _ _ _ AT x Hx). unfold scratch, ALLOC_STACK in NS. unfold YN1p.SP0. intros W. apply NS. left. lia.
+ intros W. apply NO. left. apply (meta_bytes_owned [] None U0 A L HI (mid_layout _ _ _ _ _ MID1) gm _ (MUsed am) Mg). unfold META_SIZE. unfold G in W. lia.
- intros a Hsa. assert (NW : ~ (G + 24 <= a < G + 28)).
{ unfold scratch, ALLOC_STACK in Hsa. intros W. destruct Hsa as [Hsa|Hsa]; [lia|]. apply (Gimg a); [lia|]. apply errno_img'. exact Hsa. }
assert (Ha : 0 <= a < 2 ^ 64).
{ unfold scratch, ALLOC_STACK in Hsa. destruct Hsa as [Hsa|Hsa]; [lia|]. pose proof (src0_img_range' a (errno_img' a Hsa)). lia. }
apply (proj1 (writable_ext mem1 mc a (pc_out _ _ APC a Ha NW))).
destruct (Z_le_dec (SP0 - 48) a) as [L1|L1]; [destruct (Z_lt_dec a SP0) as [L2|L2]; [apply (pa_win _ _ _ _ _ AT); unfold YN1p.SP0; lia|]|];
(apply (proj1 (writable_ext mem mem1 a (pa_out _ _ _ _ _ AT a Ha ltac:(unfold YN1p.SP0; lia))));
unfold scratch, ALLOC_STACK in Hsa; (destruct Hsa as [Hsa|Hsa]; [apply Hstk; lia | apply Herr; exact Hsa])).
- intros US. exfalso. pose proof take_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof (avail_bit_not_undersized [] None U0 A gm am idx HI Hu ltac:(lia) ltac:(lia) ltac:(rewrite Z.lor_spec; unfold mask in Hbit; rewrite Hbit; reflexivity)).
rewrite Hsc in H. replace (stride_of am2) with (stride_of am) in US by (unfold am2; destruct am; reflexivity). lia.
Qed.
End h.
Theorem fast_path :
mreal src0segs (mkCfg (mkst regs2 (Z_to_bv 64 PB) mem1 rom) md)
(ibind (enframe gm idx n (st_mmap_counter A2) FUser A2) (fun ps => IRet (Some (fst ps), snd ps)))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
pose proof PRE_facts as (MX & _). destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (Hh & Hlz & _).
eapply mreal_SR_pre; [eapply (T2f_run E2); [exact T2f_st_ok | exact Hh | exact Hlz]|].
intros c' (ms3 & -> & HS3 & HF). cbn [ms_mem mkst] in HF.
destruct (T2f_post ms3 HS3 HF) as [SHAPE POST]. rewrite SHAPE. apply (fast_tail _ _ POST).
Qed.
End g.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
