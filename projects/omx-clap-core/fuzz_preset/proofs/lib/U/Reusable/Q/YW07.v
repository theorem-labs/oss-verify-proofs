(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YN03 YN02 YN2b YN25 YN26.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.Q Require Import YW03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YN0b YN07 YN0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.Q Require Import YW0e YW06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ERRNO2 : Z := errno_addr src0_msyms.
Lemma ERRNO2_val : ERRNO2 = src0_tp - 164.
Proof. reflexivity. Qed.
Lemma errno_rom2 k : (k < 4)%nat -> seg_rom src0segs (Z_to_bv 64 (ERRNO2 + Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof. intros Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
Lemma le_byte4 (v0 v1 v2 v3 : Z) k :
0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> (k < 4)%nat ->
le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 k = nth k [v0; v1; v2; v3] 0.
Proof.
intros H0 H1 H2 H3 Hk. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth Z.of_nat Z.mul Pos.of_succ_nat Pos.mul Pos.succ].
- change (2 ^ 0) with 1. rewrite Z.div_1_r.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with (v0 + (v1 + 256 * v2 + 65536 * v3) * 256) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- change (2 ^ 8) with 256.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with (v0 + (v1 + (v2 + 256 * v3) * 256) * 256) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l, Z_mod_plus_full by lia. apply Z.mod_small. lia.
- change (2 ^ 16) with 65536.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with ((v0 + 256 * v1) + (v2 + v3 * 256) * 65536) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l, Z_mod_plus_full by lia. apply Z.mod_small. lia.
- change (2 ^ 24) with 16777216.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with ((v0 + 256 * v1 + 65536 * v2) + v3 * 16777216) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. apply Z.mod_small. lia.
Qed.
Lemma errno_bytes_any2 m : exists err, 0 <= err < 2 ^ 32 /\ bytes_are m ERRNO2 4 err.
Proof.
assert (B : forall k, (k < 4)%nat -> exists b : byte, mbyte src0segs m (ERRNO2 + Z.of_nat k) = Some b).
{ intros k Hk. unfold mbyte. destruct (m (Z_to_bv 64 (ERRNO2 + Z.of_nat k))) as [b|]; [exists b; reflexivity|].
rewrite (errno_rom2 k Hk). eexists; reflexivity. }
destruct (B 0%nat ltac:(lia)) as [b0 H0]. destruct (B 1%nat ltac:(lia)) as [b1 H1].
destruct (B 2%nat ltac:(lia)) as [b2 H2]. destruct (B 3%nat ltac:(lia)) as [b3 H3].
pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
exists (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
split; [lia|]. intros k Hk. rewrite le_byte4 by assumption.
destruct k as [|[|[|[|k]]]]; [rewrite H0 | rewrite H1 | rewrite H2 | rewrite H3 | lia]; cbn [nth]; rewrite Z_to_bv_bv_unsigned; reflexivity.
Qed.
Lemma word_mem_bytes m a v : word_mem src0segs m a v -> bytes_are m a 8 v.
Proof. intros H k Hk. exact (H k Hk). Qed.
Section d.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Local Notation VV := (YW06.vv L regs g am fr a rg).
Variable rcr : rcase.
Hypothesis FP : free_pre K3b rcr VV mem.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let M : MRc src0_msyms L A mem md := M L A regs mem md g am fr n a ka rg HC.
Lemma guard_any : exists gd, 0 <= gd < 2 ^ 64 /\ bytes_are mem src0_D_stack_chk_guard 8 gd.
Proof.
destruct (st_guard _ _ (mc_statics _ _ _ _ _ M)) as [gd Hgd].
exists (gd mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
intros k Hk. cbn [ms_guard ms_segs src0_msyms] in Hgd. rewrite (Hgd k Hk). f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma got_bytes : bytes_are mem src0_D_got_stack_chk_guard 8 src0_D_stack_chk_guard.
Proof. apply word_mem_bytes. pose proof (st_got _ _ (mc_statics _ _ _ _ _ M)) as H. cbn [ms_guard ms_got_guard ms_segs src0_msyms] in H. exact H. Qed.
Lemma off_rangeG : 0 <= fr_off fr <= 255.
Proof.
pose proof (inv_groups (HW _ _ _ _ _ _ _ _ _ _ _ _ HC) g am (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & Gsl & _).
pose proof (Gsl 0 ltac:(rewrite (rc_last _ _ _ _ _ _ _ _ _ _ _ _ HC); lia)) as (_ & _ & S3).
rewrite (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) in S3. destruct S3 as (_ & _ & (_ & F2 & _) & _). exact F2.
Qed.
Lemma needed_rangeG : n + UNIT * fr_off fr + UNIT + IB <= needed fr n /\ needed fr n mod PGSZ = 0 /\ 0 < needed fr n < 2 ^ 63.
Proof using HC.
pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn. pose proof off_rangeG as OR.
pose proof (YO0q.page_round_ge (n + UNIT * fr_off fr + UNIT + IB)) as H1. pose proof (YO0q.page_round_mod (n + UNIT * fr_off fr + UNIT + IB)) as H2.
unfold needed. split; [exact H1|]. split; [exact H2|]. split; [unfold UNIT, IB in *; lia|].
unfold page_round, PGSZ, UNIT, IB in *. pose proof (Z.mul_div_le (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.
Lemma xvr_rangeG gd err : 0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 -> forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64.
Proof.
intros Hgd Herr k.
unfold xvr. destruct (k <? 96)%nat eqn:Ek; [exact (xvf_range _ _ _ _ FP k)|].
pose proof needed_rangeG as NR. pose proof off_rangeG as OR. unfold YW06.NEEDED.
unfold UNIT, IB in *.
do 96 (destruct k as [|k]; [discriminate|]).
do 10 (destruct k as [|k]; [cbn; lia|]). cbn. lia.
Qed.
Section e.
Variables (gd err : Z).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Herr : 0 <= err < 2 ^ 32.
Hypothesis Hgd2 : bytes_are mem src0_D_stack_chk_guard 8 gd.
Hypothesis Herr2 : bytes_are mem ERRNO2 4 err.
Let E := Er L regs g am fr n a rg gd err.
Let NEEDED := needed fr n.
Lemma needed_range : n + UNIT * fr_off fr + UNIT + IB <= NEEDED /\ NEEDED mod PGSZ = 0 /\ 0 < NEEDED < 2 ^ 63.
Proof. exact needed_rangeG. Qed.
Lemma off_range : 0 <= fr_off fr <= 255.
Proof. exact off_rangeG. Qed.
Lemma xvr_range k : 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64.
Proof. exact (xvr_rangeG gd err Hgd Herr k). Qed.
Lemma E_agree : env_agree 96 (EV (xvf VV)) E.
Proof. exact (Er_agree L regs g am fr n a rg gd err). Qed.
Lemma ew_E k : bv_unsigned (ew E k) = xvr L regs g am fr n a rg gd err k.
Proof. unfold E, Er. apply (ew_EV _ xvr_range). Qed.
Lemma xvr_lo k : (k < 96)%nat -> xvr L regs g am fr n a rg gd err k = xvf VV k.
Proof. intros Hk. unfold xvr. replace (k <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk). reflexivity. Qed.




Lemma meta_present : forall x, fv_g VV <= x < fv_g VV + 40 -> present mem x.
Proof.
intros x Hx. pose proof (HW _ _ _ _ _ _ _ _ _ _ _ _ HC) as HW.
destruct (rc_area _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hain & Hka & Eg).
destruct (proj1 (proj2 (inv_areas HW)) a Hain) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & Hrak).
assert (In2 : In (LMem a, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) _ In2) as F.
cbn [foot_ok fst snd] in F. rewrite Ea in F. cbn [loc_addr] in F. apply F.
assert (Eg' : fv_g VV = ly_reg L ra + oa + AREA_HDR + META_SIZE * ka).
{ unfold YW06.vv, fv_of. cbn [fv_g]. unfold ptr_addr, loc_addr. rewrite Eg, Ea. cbn [padd]. lia. }
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma meta_writable : forall x, fv_g VV + 16 <= x < fv_g VV + 40 -> writable_at src0segs mem x.
Proof. intros x Hx. apply present_writable. apply meta_present. lia. Qed.
Ltac xfer H := eapply (region_ok_agree src0segs 96 (EV (xvf VV)) E mem); [exact E_agree | reflexivity | exact H].
Ltac reg_numR := match goal with FP : free_pre _ _ ?v _ |- _ =>
unfold extent_disjoint; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_hdr reg_grp reg_meta reg_area reg_ctx reg_nl reg_stk reg_tq reg_end1 reg_end5 reg_pn
reg_metaR reg_hdr0 reg_meta0 reg_stkR reg_got reg_guard reg_errnoR];
rewrite ?(base_val_EV (xvf _) (xvf_range _ _ _ _ FP)); cbn [base_val];
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP;
cbn [xvf Nat.ltb Nat.leb nat_to_reg] end.
Lemma region_ok_ro E0 m r : region_ok src0segs E0 m r -> region_ok src0segs E0 m (YP09.mkRegion (r_base r) (r_lo r) (r_hi r) 0 0 (r_chunks r)).
Proof. intros (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [cbn [r_wlo r_whi]; intros o Ho; lia | exact H4]. Qed.
Lemma rok_metaR0 : region_ok src0segs (EV (xvf VV)) mem reg_meta0.
Proof.
apply region_ok_intro; reg_numR; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil).
- chunk_from (fp_c_g16 _ _ _ _ FP).
- chunk_from (fp_c_g24 _ _ _ _ FP).
- chunk_from (fp_c_g28 _ _ _ _ FP).
- eapply chunk_ok_val; [val_tac | pose proof (fp_vals _ _ _ _ FP) as V; unfold YW06.vv, fv_of in V; cbn in V |- *; lia
| eapply (bytes_are_at _ _ _ _ _ (fp_c_g32 _ _ _ _ FP)); lin].
Qed.
Lemma PRE_facts : YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\ alloc_ceiling + REALLOC_STACK <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall x, spZ regs - REALLOC_STACK <= x < spZ regs -> writable_at src0segs mem x) /\
getr regs 4 = Z_to_bv 64 src0_tp /\
(forall x, ERRNO2 <= x < ERRNO2 + 4 -> writable_at src0segs mem x).
Proof.
pose proof PRE as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
repeat split; auto.
Qed.

Lemma xvf4 : xvf VV 4 = src0_tp.
Proof. rewrite xvf_reg by lia. change (nat_to_reg 4) with (4%bv : bv 5). destruct PRE_facts as (_ & _ & _ & _ & _ & Htp & _).
unfold YW06.vv, fv_of. cbn [fv_regs]. rewrite Htp. reflexivity. Qed.
Lemma rok_stkR0 : region_ok src0segs (EV (xvf VV)) mem reg_stkR.
Proof.
destruct PRE_facts as (_ & Hal & Hceil & Hsp63 & Hstk & _). pose proof YM05.alloc_ceiling_val as HCV.
apply region_ok_intro; reg_numR; change (fv_regs VV) with regs; change (nat_to_reg 2) with (2%bv : bv 5); unfold spZ, REALLOC_STACK, ALLOC_STACK in *;
[lia | lia | intros o Ho; apply Hstk; lia | apply Forall_nil].
Qed.
Lemma rok_got : region_ok src0segs E mem reg_got.
Proof.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_got base_val]; unfold src0_D_got_stack_chk_guard; [lia | lia | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil).
unfold E, Er. eapply chunk_ok_val; [cbn [sv_denot]; apply lit64_small; unfold src0_D_stack_chk_guard; lia | unfold src0_D_stack_chk_guard; cbn; lia |].
eapply bytes_are_at; [exact got_bytes | reflexivity].
Qed.
Lemma rok_guard : region_ok src0segs E mem reg_guard.
Proof.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_guard base_val]; unfold src0_D_stack_chk_guard; [lia | lia | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil).
unfold E, Er. eapply (chunk_ok_val _ mem _ _ 8 (SOff aGUARD 0) gd); [rewrite (U_off0 _ xvr_range); reflexivity | cbn; lia |].
eapply bytes_are_at; [exact Hgd2 | reflexivity].
Qed.
Lemma rok_errnoR : region_ok src0segs E mem reg_errnoR.
Proof.
destruct PRE_facts as (_ & _ & _ & _ & _ & _ & Herrw).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_errnoR]; unfold E, Er, aTP; rewrite ?(base_val_EV _ xvr_range);
rewrite ?xvr_lo by (cbv; lia); rewrite ?xvf4; unfold src0_tp; [lia | lia | intros o Ho; apply Herrw; rewrite ERRNO2_val; unfold src0_tp; lia |].
repeat (apply Forall_cons || apply Forall_nil).
eapply (chunk_ok_val _ mem _ _ 4 (SOff aERRR 0) err); [rewrite (U_off0 _ xvr_range); reflexivity | cbn; lia |].
eapply bytes_are_at; [exact Herr2 | rewrite ERRNO2_val; unfold src0_tp; lia].
Qed.
Lemma fv_regs_VV : fv_regs VV = regs. Proof. reflexivity. Qed.
Lemma TP4 : bv_unsigned (getr regs 4) = src0_tp.
Proof. destruct PRE_facts as (_ & _ & _ & _ & _ & Htp & _). rewrite Htp. reflexivity. Qed.
Ltac reg_numE :=
unfold extent_disjoint; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_hdr reg_grp reg_meta reg_area reg_ctx reg_nl reg_stk reg_tq reg_end1 reg_end5 reg_pn
reg_metaR reg_hdr0 reg_meta0 reg_stkR reg_got reg_guard reg_errnoR];
unfold E, Er;
match goal with XR : forall k, 0 <= xvr _ _ _ _ _ _ _ _ _ _ k < _ |- _ => rewrite ?(base_val_EV _ XR) end; cbn [base_val];
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP,
aN, aGUARD, aRET, aNP, aNEND, aNPN, aNOLD, aQ, aB16, aNEED, aERRR;
unfold xvr; cbn [xvf Nat.ltb Nat.leb nat_to_reg]; rewrite ?fv_regs_VV.
Ltac linE :=
cbn zeta in *; pose proof YM05.alloc_ceiling_val as HCV;
unfold CEIL, TBL, src0_D_size_classes, src0_D_malloc_context, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_tp, REALLOC_STACK, ALLOC_STACK in *;
unfold fv_p, fv_sp, spZ in *; rewrite ?fv_regs_VV in *; lia.
Lemma regions_ok_entry : Forall (region_ok src0segs E mem) (entry_mem rcr).
Proof.
pose proof (rok_end5 _ _ _ _ FP) as E5. pose proof (rok_pn _ _ _ _ FP) as PN.
unfold entry_mem. apply Forall_app. split.
- repeat (apply Forall_cons || apply Forall_nil).
+ xfer (region_ok_ro _ _ _ (rok_hdr _ _ _ _ FP)).
+ xfer (rok_grp _ _ _ _ FP).
+ xfer rok_metaR0.
+ xfer (rok_area _ _ _ _ FP).
+ xfer (rok_ctx _ _ _ _ FP).
+ xfer (rok_nl _ _ _ _ FP).
+ xfer rok_stkR0.
+ apply rok_got.
+ apply rok_guard.
+ apply rok_errnoR.
- destruct rcr; cbn [r_mem] in *;
repeat (apply Forall_cons || apply Forall_nil);
first [xfer (rok_end1 _ _ _ _ FP) | xfer E5 | xfer PN].
Qed.
Lemma pd_entry : pairwise_disjoint E (entry_mem rcr).
Proof.
pose proof (fp_pn6 _ _ _ _ FP) as P6. pose proof (fp_c_end5 _ _ _ _ FP) as C5.
pose proof xvr_range as XR. pose proof (lin_facts _ _ _ _ FP) as LF. pose proof PRE_facts as (_ & _ & PF3 & PF4 & _). pose proof TP4 as T4.
unfold entry_mem. destruct rcr; cbn [r_mem app pairwise_disjoint all_disjoint];
repeat match goal with |- _ /\ _ => split | |- True => exact I end; try (destruct C5 as (_ & _ & C5)); reg_numE; linE.
Qed.
Theorem entry_mem_ok : mem_ok src0segs E mem (entry_mem rcr).
Proof.
split; [destruct rcr; vm_compute; reflexivity|].
split; [apply regions_ok_entry | apply pd_entry].
Qed.
Lemma free_facts_E : facts_ok E (free_facts K3b rcr).
Proof.
eapply (facts_ok_agree 96 (EV (xvf VV)) E); [exact E_agree | destruct rcr; vm_compute; reflexivity |].
exact (st_ok_facts_ok _ _ _ _ (free_entry_st_ok _ _ _ _ FP)).
Qed.

Lemma off_eq : fv_off VV = fr_off fr.
Proof. unfold YW06.vv, fv_of. cbn [fv_off]. unfold hdr_off16. rewrite Z.mul_0_r. unfold UNIT. rewrite Z.div_0_l by lia. lia. Qed.
Lemma n_eq : xvf VV 11 = n.
Proof using HC.
rewrite xvf_reg by lia. change (nat_to_reg 11) with (11%bv : bv 5). change (fv_regs VV) with regs.
rewrite (rc_a1 _ _ _ _ _ _ _ _ _ _ _ _ HC). apply lit64_small. pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.
Lemma n_eq' : bv_unsigned (getr regs 11) = n.
Proof. rewrite <- n_eq. rewrite xvf_reg by lia. reflexivity. Qed.
Lemma K3facts : 1 <= fv_ml VV /\ fv_sc VV = 63 /\ fv_idx VV = 0 /\ fv_last VV = 0 /\ fv_end VV = fv_mem VV + 4096 * fv_ml VV - 4.
Proof. pose proof (fp_k _ _ _ _ FP) as K. cbn in K. tauto. Qed.
Lemma atoms_entry_n lo hi : lo <= n <= hi -> atoms_ok E (entry_atoms_n lo hi rcr).
Proof using FP Herr Hgd NEEDED PRE fx.
intros Hlh. destruct free_facts_E as (FA & _ & _). unfold free_facts in FA. cbn [f_atoms] in FA.
pose proof needed_range as NR. pose proof off_range as OR. pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) as RN.
pose proof n_eq as N11. pose proof xvf4 as T4.
unfold entry_atoms_n. cbn [atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite !ew_E.
unfold aN, aB16, aNEED, aGUARD, aTP, aERRR, aSP. unfold xvr; cbn [Nat.ltb Nat.leb]. rewrite N11, T4.
change (xvf VV 2) with (fv_sp VV).
unfold NEEDED, YW06.NEEDED, MMAP_THRESHOLD, UNIT, IB, PGSZ, src0_tp in *.
pose proof (lin_facts _ _ _ _ FP) as LF. pose proof PRE_facts as (_ & Hal & PF3 & PF4 & _).
pose proof (Z_div_mod_eq_full (needed fr n) 4096) as ND.
change (2 ^ 4) with 16. change (2 ^ 12) with 4096. change (2 ^ 0) with 1.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; try exact FA; try exact Hal;
rewrite ?Z.mod_1_r; try lia; try linE.
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Ltac denE := unfold NEEDX1, NEEDX2; cbn [sv_denot]; unfold E, Er; rewrite ?(ew_EV _ xvr_range);
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP,
aN, aGUARD, aRET, aNP, aNEND, aNPN, aNOLD, aQ, aB16, aNEED, aERRR;
unfold xvr; cbn [xvf Nat.ltb Nat.leb nat_to_reg]; change (fv_regs VV) with regs; rewrite ?Z.add_0_r.
Lemma alias_entry : alias_ok E (entry_alias rcr).
Proof using FP HC Herr Hgd NEEDED fx.
destruct free_facts_E as (_ & _ & FL). unfold free_facts in FL. cbn [f_alias] in FL.
pose proof K3facts as (K1 & K2 & K3 & K4 & K5). pose proof off_eq as OE. pose proof n_eq' as N11.
pose proof needed_range as NR. pose proof off_range as OR. pose proof (fp_pmem _ _ _ _ FP) as PM.
pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF. unfold CEIL in LF.
pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) as RN.
unfold NEEDED, YW06.NEEDED, PGSZ in *.
unfold entry_alias. cbn [alias_ok]. repeat match goal with |- _ /\ _ => split | |- True => exact I end; try exact FL.
-   weq. denE. rewrite alu64_add, mul64_unsigned, !lit64_small by lia. rewrite K3.
unfold mul64, add64. rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_r by lia. rewrite Z.mod_small by lia. reflexivity.
-   weq. denE. rewrite alu64_add, !lit64_small by lia. unfold add64. rewrite K5. rewrite Z.mod_small by lia. lia.
-   weq. denE. change (bv_unsigned (getr regs 10)) with (fv_p VV). pose proof YM05.alloc_ceiling_val.
rewrite alu64_sub, !lit64_small by lia. unfold sub64. rewrite PM, OE. rewrite Z.mod_small by lia. lia.
-   weq. denE. unfold YW06.NEEDED, needed, page_round, PGSZ, UNIT, IB in *.
replace (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) with (n + 4115 + 16 * fr_off fr) in * by lia.
pose proof (Z.div_mod (n + 4115 + 16 * fr_off fr) 4096 ltac:(lia)).
rewrite N11. rewrite alu64_and, alu64_add, (lit64_unsigned (-4096)), !lit64_small by lia.
change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12). unfold add64. rewrite Z.mod_small by lia. rewrite land_neg_pow2_u64 by lia.
change (2 ^ 12) with 4096. lia.
-   weq. denE. unfold YW06.NEEDED, needed, page_round, PGSZ, UNIT, IB in *.
replace (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) with (16 * fr_off fr + 4115 + n) in * by lia.
pose proof (Z.div_mod (16 * fr_off fr + 4115 + n) 4096 ltac:(lia)).
rewrite N11. rewrite alu64_and, alu64_add, (lit64_unsigned (-4096)), !lit64_small by lia.
change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12). unfold add64. rewrite Z.mod_small by lia. rewrite land_neg_pow2_u64 by lia.
change (2 ^ 12) with 4096. lia.
Qed.
Theorem entry_facts_ok_n lo hi cs : lo <= n <= hi -> conds_ok E cs -> facts_ok E (entry_facts_n lo hi cs rcr).
Proof using FP Herr Hgd NEEDED PRE fx.
intros Hlh Hcs. destruct free_facts_E as (_ & FC & _). unfold free_facts in FC. cbn [f_conds] in FC.
split; [apply atoms_entry_n; exact Hlh|]. split; [cbn [entry_facts_n f_conds]; apply conds_ok_app; [exact Hcs | exact FC] | apply alias_entry].
Qed.
Theorem entry_st_ok_n lo hi cs : lo <= n <= hi -> conds_ok E cs ->
st_ok src0segs E (S0n lo hi cs rcr) (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)).
Proof using FP Herr Herr2 Hgd Hgd2 M NEEDED PRE.
intros Hlh Hcs.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts S0n resv_denot].
repeat (split; [reflexivity|]). split; [| split; [apply entry_mem_ok | apply entry_facts_ok_n; assumption]].
eapply (regs_ok_agree 96 (EV (xvf VV)) E); [exact E_agree | reflexivity | exact (free_regs_ok VV)].
Qed.
End e.
Theorem OBL_entry_n lo hi cs : lo <= n <= hi -> (forall gd err, conds_ok (Er L regs g am fr n a rg gd err) cs) ->
exists gd err, 0 <= gd < 2 ^ 64 /\ 0 <= err < 2 ^ 32 /\
st_ok src0segs (Er L regs g am fr n a rg gd err) (S0n lo hi cs rcr) (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)).
Proof using FP M PRE.
intros Hlh Hcs. destruct guard_any as (gd & Hgd1 & Hgd2). destruct (errno_bytes_any2 mem) as (err & He1 & He2).
exists gd, err. split; [exact Hgd1|]. split; [exact He1|]. apply entry_st_ok_n; auto.
Qed.
End d.
Theorem src0_realloc_entry : OBL_entry_T.
Proof using.
intros L A regs mem md g am fr n a ka rg HC Hth.
exact (OBL_entry_n L A regs mem md g am fr n a ka rg HC (rcr am fr) (FP L A regs mem md g am fr n a ka rg HC) 131052 (2 ^ 62 - 1) []
ltac:(pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC); unfold MMAP_THRESHOLD in Hth; lia) (fun _ _ => I)).
Qed.
End c.
