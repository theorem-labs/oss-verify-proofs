(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YP0n YM06 YK0s YM02 YK1j YK1a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0d YO0e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN03 YN02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW01 YW00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN2b YN25 YN26 YN28.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN0b YN07 YN0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW0e YW06 YW07 YW0c YW0b YY00 YV00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma lit5 k : (1 <= k <= 31)%nat -> Z_to_bv 5 (Z.of_nat k) = nat_to_reg k.
Proof. intros Hk. rewrite (Z_to_bv5_nat_to_reg (Z.of_nat k)) by lia. rewrite Nat2Z.id. reflexivity. Qed.
End f.
Ltac vnth H i V := pose proof (f_equal (fun l => List.nth i l (SLit 0)) H) as V; cbn [List.nth] in V;
try (rewrite lit5 in V by lia; cbn [nat_to_reg] in V).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ptr_addr_paddR Lx p d : ptr_addr Lx (padd p d) = ptr_addr Lx p + d.
Proof. destruct p as [rr o]. unfold ptr_addr, loc_addr, padd. lia. Qed.
Lemma frame_slot o r : In (o, r) FB_SLOTS -> In (mkChunk o (CVal 8 (SOff r 0))) frame_chunks /\ (1 <= r <= 31)%nat.
Proof using.
unfold FB_SLOTS, frame_chunks. cbn [In]. intros H.
repeat (destruct H as [H|H]; [injection H as <- <-; split; [repeat (first [left; reflexivity | right]) | lia] |]). destruct H.
Qed.
Section FB.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Variables (gd err : Z).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Herr : 0 <= err < 2 ^ 32.
Local Notation VV := (YW06.vv L regs g am fr a rg).
Local Notation rcr := (YW06.rcr am fr).
Local Notation E := (Er L regs g am fr n a rg gd err).
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let M : MRc src0_msyms L A mem md := M L A regs mem md g am fr n a ka rg HC.
Let MX : MRx src0_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
Let HW : WF A := HW L A regs mem md g am fr n a ka rg HC.
Let XR : forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64 :=
xvr_rangeG L A regs mem md g am fr n a ka rg HC rcr FP gd err Hgd Herr.
Definition SP : Z := spZ regs.
Definition P : Z := ptr_addr L (pp am fr).
Definition NOLD : Z := fr_n fr.
Definition STK (x : Z) : Prop := SP - 8256 <= x < SP.
Definition ERRN (x : Z) : Prop := ERRNO2 <= x < ERRNO2 + 4.
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ M). Qed.
Lemma PREf : YK0s.ret_ok (getr regs 1) /\ SP mod 16 = 0 /\ alloc_ceiling + 8256 <= SP /\ SP < 2 ^ 63 /\
(forall x, STK x -> writable_at src0segs mem x) /\ getr regs 4 = Z_to_bv 64 src0_tp /\
(forall x, ERRN x -> writable_at src0segs mem x).
Proof.
pose proof PRE as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
unfold REALLOC_STACK, ALLOC_STACK in *. unfold STK, ERRN, SP.
repeat split; auto.
Qed.
Lemma Hin : In (pp am fr, NOLD) (user_blocks A). Proof. exact (rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Hinit : st_init_done A = true. Proof. exact (init_done_of_block A _ HW Hin). Qed.
Lemma Hn : 0 <= n < 2 ^ 62. Proof using HC. exact (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Ha0 : getr regs 10 = Z_to_bv 64 P. Proof. exact (rc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Pblk : 4096 <= P /\ 0 <= NOLD /\ P + NOLD <= alloc_ceiling.
Proof using HW MX.
pose proof (mr_blocks_range _ _ (MRx_laws src0_msyms) L A mem md _ _ MX Hin) as [H1 H2].
destruct (block_region A (pp am fr) NOLD HW Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & Hk & _). auto.
Qed.
Lemma E_reg i : (1 <= i <= 31)%nat -> ew E i = getr regs (nat_to_reg i).
Proof.
intros Hi. cbn [ew Er EV]. unfold xvr. replace (i <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite xvf_reg by lia. change (fv_regs VV) with regs. apply Z_to_bv_bv_unsigned.
Qed.
Lemma den_reg i : (1 <= i <= 31)%nat -> sv_denot E (SOff i 0) = getr regs (nat_to_reg i).
Proof. intros Hi. cbn [sv_denot]. rewrite E_reg by lia. apply bv_eq. rewrite Z_to_bv_unsigned, Z.add_0_r. apply bv_wrap_small. apply u64_range || (pose proof (u64_range (getr regs (nat_to_reg i))); change (bv_modulus 64) with (2 ^ 64); lia). Qed.
Lemma XP : xvr L regs g am fr n a rg gd err aP = P.
Proof.
unfold xvr, aP. cbn [Nat.ltb Nat.leb]. rewrite xvf_reg by lia. change (fv_regs VV) with regs. change (nat_to_reg 10) with (10%bv : bv 5).
rewrite Ha0. apply lit64_small. pose proof Pblk as (P1 & P0 & P2). pose proof YM05.alloc_ceiling_val. lia.
Qed.
Lemma XN : xvr L regs g am fr n a rg gd err aN = n.
Proof. unfold xvr, aN. cbn [Nat.ltb Nat.leb]. exact (n_eq L A regs mem md g am fr n a ka rg HC). Qed.
Lemma XSP : xvr L regs g am fr n a rg gd err aSP = SP.
Proof. reflexivity. Qed.

Lemma den_ENDR : sv_denot E (ENDR rcr) = Z_to_bv 64 (P + NOLD).
Proof.
pose proof (fp_r _ _ _ _ FP) as R. pose proof (lin_facts _ _ _ _ FP) as LF. cbn zeta in LF.
assert (Ersv : fv_rsv VV = reserved_of am fr) by reflexivity.
assert (Eend : fv_end VV = P + NOLD + reserved_of am fr).
{ unfold YW06.vv, fv_of. cbn [fv_end]. unfold P, NOLD, pp, slot_end, frame_ptr, reserved_of.
rewrite !ptr_addr_paddR. lia. }
assert (Epn : fv_pn VV = P + NOLD) by reflexivity.
clearbody XR. clear FP. unfold YW06.rcr in *. unfold rcase_of in *.
destruct (reserved_of am fr =? 0) eqn:E0; [| destruct (reserved_of am fr <? 5) eqn:E1; [| destruct (reserved_of am fr =? 5) eqn:E2]]; cbn [ENDR].
- apply Z.eqb_eq in E0. rewrite (den_off0 _ XR). apply (f_equal (Z_to_bv 64)). change (xvr L regs g am fr n a rg gd err aEND) with (fv_end VV). lia.
- rewrite (den_off0 _ XR). apply (f_equal (Z_to_bv 64)). exact Epn.
- apply Z.eqb_eq in E2. rewrite (den_off _ XR); [apply (f_equal (Z_to_bv 64)); change (xvr L regs g am fr n a rg gd err aEND) with (fv_end VV); lia|].
change (xvr L regs g am fr n a rg gd err aEND) with (fv_end VV). unfold CEIL in LF. lia.
- rewrite (den_off0 _ XR). apply (f_equal (Z_to_bv 64)). exact Epn.
Qed.
Lemma base_SP : base_val E (Some aSP) = SP.
Proof. cbn [base_val]. unfold aSP. rewrite E_reg by lia. reflexivity. Qed.
Lemma base_TP : base_val E (Some aTP) = src0_tp.
Proof.
cbn [base_val]. unfold aTP. rewrite E_reg by lia. change (nat_to_reg 4) with (4%bv : bv 5).
destruct PREf as (_ & _ & _ & _ & _ & -> & _). apply lit64_small. unfold src0_tp. lia.
Qed.
Lemma not_wr_entry x : 0 <= x < 2 ^ 64 -> ~ STK x -> ~ ERRN x -> ~ in_wrange E (entry_mem rcr) x.
Proof.
intros Hx N1 N2 W. apply wr_entry in W. rewrite base_SP, base_TP in W. unfold STK, ERRN in *. rewrite ERRNO2_val in N2. lia.
Qed.
Lemma fb_of_arr regs4 mem4 : arr_ok E rcr mem regs4 mem4 -> fb_arrival L A regs mem md (pp am fr) NOLD n regs4 mem4.
Proof using HW MX PRE XR.
intros [R1 R2 R8 R9 R10 R18 RK CF W1 W2 RW].
pose proof PREf as (_ & Hal & Hceil & H63 & _). pose proof YM05.alloc_ceiling_val.
split.
- exact PRE.
- exact Hin.
- exact Ha0.
- exact (rc_a1 _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact Hn.
- exact R1.
- rewrite R2, (den_off _ XR); [reflexivity|]. change (xvr L regs g am fr n a rg gd err aSP) with SP. lia.
- rewrite R8, (den_off0 _ XR), XN. reflexivity.
- rewrite R9, (den_off0 _ XR), XP. reflexivity.
- rewrite R10, (den_off0 _ XR), XN. reflexivity.
- rewrite R18. exact den_ENDR.
- intros i Hi. rewrite (RK i Hi). apply den_reg. cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [lia|]). destruct Hi.
- intros o r i Hs Hi. destruct (frame_slot o r Hs) as [Hc Hr].
destruct (proj1 (Forall_forall _ _) CF _ Hc i ltac:(cbn [c_len c_val cv_len]; change (Z.of_N 8) with 8; lia)) as (b & Hb1 & Hb2).
cbn [cbyte c_val c_off] in Hb1, Hb2. rewrite den_reg in Hb1 by exact Hr. rewrite base_SP in Hb2. unfold SP in Hb2. rewrite Hb2. symmetry. exact Hb1.
- intros x Hx. replace x with (base_val E (Some aSP) + (x - SP)) by (rewrite base_SP; lia). apply W1.
unfold fb_stk, REALLOC_STACK, ALLOC_STACK in Hx. unfold SP. lia.
- intros x Hx. replace x with (base_val E (Some aTP) + (x - src0_tp)) by (rewrite base_TP; lia). apply W2.
unfold fb_errno in Hx. change (errno_addr src0_msyms) with ERRNO2 in Hx. rewrite ERRNO2_val in Hx. lia.
- intros x Hx N1 N2. apply RW. rewrite lit64_small by exact Hx. apply not_wr_entry; [exact Hx | | exact N2].
intros HS. apply N1. unfold fb_stk, REALLOC_STACK, ALLOC_STACK. unfold STK, SP in HS. lia.
Qed.
Section S2.
Variables (regs2 : bvmap 5 word) (mem2 : word -> option byte).
Hypothesis AT2 : at_S2 L regs mem g am fr n a rg gd err regs2 mem2.
Definition RAW (m0 m1 : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ~ ERRN x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x).
Lemma to_S4 :
SR src0segs (mkCfg (mkst (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem2 (seg_rom src0segs)) md)
(fun c4 => exists ms4, c4 = mkCfg ms4 md /\ st_ok src0segs E (S4 rcr) ms4 /\ RAW mem (ms_mem ms4)).
Proof.
destruct AT2 as (_ & _ & Hregs2 & Hmem2 & HG2 & HF2). destruct Hmd as (Hh & Hlz & _).
destruct (S2_run_ok rcr) as (_ & Hpc2 & Hrv2).
assert (HS : st_ok src0segs E (S2no rcr) (mkst (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem2 (seg_rom src0segs))).
{ rewrite <- Hpc2. unfold S2no. apply st_ok_resume_sv; [exact Hregs2 | exact Hmem2 | exact HG2 | reflexivity]. }
eapply SR_mono; [exact (S4_run E _ md Hh Hlz rcr HS)|].
intros c4 (ms4 & -> & HS4 & HF4). exists ms4. split; [reflexivity|]. split; [exact HS4|].
cbn [ms_mem] in HF4. rewrite mem_S2no in HF4.
intros x Hx N1 N2. transitivity (mem2 (Z_to_bv 64 x)).
- apply HF4. rewrite lit64_small by lia. intros W. apply (not_wr_entry x Hx N1 N2).
eapply in_wrange_skeleton; [exact (skel_S2 rcr) | exact W].
- apply HF2. rewrite lit64_small by lia. exact (not_wr_entry x Hx N1 N2).
Qed.
Section m.
Variable ms4 : machine_state.
Hypothesis HS4 : st_ok src0segs E (S4 rcr) ms4.
Hypothesis RAW4 : RAW mem (ms_mem ms4).
Let regs4 := ms_regs ms4.
Let mem4 := ms_mem ms4.
Lemma S4_regs :
getr regs4 1 = Z_to_bv 64 RA_MALLOC /\ getr regs4 2 = Z_to_bv 64 (SP - 64) /\ getr regs4 3 = getr regs 3 /\
getr regs4 4 = getr regs 4 /\ getr regs4 8 = Z_to_bv 64 n /\ getr regs4 9 = Z_to_bv 64 P /\ getr regs4 10 = Z_to_bv 64 n /\
getr regs4 18 = Z_to_bv 64 (P + NOLD) /\ getr regs4 19 = Z_to_bv 64 (16 * fr_off fr) /\ getr regs4 20 = Z_to_bv 64 4095 /\ getr regs4 21 = Z_to_bv 64 P /\ getr regs4 22 = Z_to_bv 64 n /\
(forall i, In i [23; 24; 25; 26; 27]%nat -> getr regs4 (nat_to_reg i) = getr regs (nat_to_reg i)).
Proof.
destruct (S4_shape rcr) as (_ & _ & Hv & _). unfold view in Hv. cbn [map] in Hv.
vnth Hv 0%nat V1. vnth Hv 1%nat V2. vnth Hv 2%nat V3. vnth Hv 3%nat V4. vnth Hv 4%nat V8. vnth Hv 5%nat V9. vnth Hv 6%nat V10.
vnth Hv 7%nat V18. vnth Hv 8%nat V23. vnth Hv 9%nat V24. vnth Hv 10%nat V25. vnth Hv 11%nat V26. vnth Hv 12%nat V27.
pose proof (S4_view2 rcr) as Hv2.
unfold view in Hv2. cbn [map] in Hv2. vnth Hv2 0%nat V19. vnth Hv2 1%nat V20. vnth Hv2 2%nat V21. vnth Hv2 3%nat V22.
pose proof (st_ok_regs_ok src0segs E _ _ HS4) as R. change (regs_ok E (ss_regs (S4 rcr)) regs4) in R.
pose proof XP as XP. pose proof XN as XN.
repeat match goal with |- _ /\ _ => split end.
- rewrite (R 1%bv), V1. reflexivity.
- rewrite (R 2%bv), V2. rewrite (den_off _ XR); [reflexivity|]. change (xvr L regs g am fr n a rg gd err 2) with SP.
pose proof PREf as (_ & _ & P3 & P4 & _). pose proof YM05.alloc_ceiling_val. lia.
- rewrite (R 3%bv), V3. exact (den_reg 3 ltac:(lia)).
- rewrite (R 4%bv), V4. exact (den_reg 4 ltac:(lia)).
- rewrite (R 8%bv), V8, (den_off0 _ XR), XN. reflexivity.
- rewrite (R 9%bv), V9, (den_off0 _ XR), XP. reflexivity.
- rewrite (R 10%bv), V10, (den_off0 _ XR), XN. reflexivity.
- rewrite (R 18%bv), V18. exact den_ENDR.
- rewrite (R 19%bv), V19, (den_off0 _ XR). reflexivity.
- rewrite (R 20%bv), V20. reflexivity.
- rewrite (R 21%bv), V21, (den_off0 _ XR), XP. reflexivity.
- rewrite (R 22%bv), V22, (den_off0 _ XR), XN. reflexivity.
- intros i Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [nat_to_reg];
[rewrite (R 23%bv), V23 | rewrite (R 24%bv), V24 | rewrite (R 25%bv), V25 | rewrite (R 26%bv), V26 | rewrite (R 27%bv), V27];
apply den_reg; lia.
Qed.
Lemma S4_mem :
(forall x, STK x -> writable_at src0segs mem4 x) /\ (forall x, ERRN x -> writable_at src0segs mem4 x) /\
Forall (chunk_ok src0segs E mem4 SP) frame_chunks.
Proof.
pose proof (st_ok_mem_ok src0segs E _ _ HS4) as (_ & ROK & _). change (ms_mem ms4) with mem4 in ROK.
destruct (S4_shape rcr) as (_ & _ & _ & Hsm). rewrite Hsm in ROK.
assert (Rstk : region_ok src0segs E mem4 (stk3 rcr)) by (eapply (proj1 (Forall_forall _ _) ROK); cbn; tauto).
assert (Rerr : region_ok src0segs E mem4 (YP09.mkRegion (Some aTP) (-164) (-160) (-164) (-160) [mkChunk (-164) (CVal 4 (SLit 12))]))
by (eapply (proj1 (Forall_forall _ _) ROK); cbn; tauto).
destruct Rstk as (_ & _ & Wstk & Cstk). destruct Rerr as (_ & _ & Werr & _).
cbn [r_base r_wlo r_whi r_chunks stk3] in Wstk, Cstk, Werr. rewrite base_SP in Wstk, Cstk. rewrite base_TP in Werr.
split; [|split].
- intros x Hx. unfold STK in Hx. replace x with (SP + (x - SP)) by lia. apply Wstk. lia.
- intros x Hx. unfold ERRN in Hx. rewrite ERRNO2_val in Hx. replace x with (src0_tp + (x - src0_tp)) by lia. apply Werr. lia.
- apply Forall_app in Cstk as [_ Cstk]. apply Forall_app in Cstk as [_ Cstk]. exact Cstk.
Qed.
Lemma fb_at_S4 : fb_arrival L A regs mem md (pp am fr) NOLD n regs4 mem4.
Proof using HS4 HW MX PRE RAW4 XR.
pose proof S4_regs as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R18 & _ & _ & _ & _ & RK).
pose proof S4_mem as (W1 & W2 & CF).
split.
- exact PRE.
- exact Hin.
- exact Ha0.
- exact (rc_a1 _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact Hn.
- exact R1.
- exact R2.
- exact R8.
- exact R9.
- exact R10.
- exact R18.
- intros i Hi. cbn [In] in Hi. destruct Hi as [<-|[<-|Hi]]; [exact R3 | exact R4 | apply RK; cbn [In]; tauto].
- intros o r i Hs Hi. destruct (frame_slot o r Hs) as [Hc Hr].
destruct (proj1 (Forall_forall _ _) CF _ Hc i ltac:(cbn [c_len c_val cv_len]; change (Z.of_N 8) with 8; lia)) as (b & Hb1 & Hb2).
cbn [cbyte c_val c_off] in Hb1, Hb2. rewrite den_reg in Hb1 by exact Hr. unfold SP in Hb2. rewrite Hb2. symmetry. exact Hb1.
- intros x Hx. apply W1. unfold fb_stk, REALLOC_STACK, ALLOC_STACK in Hx. unfold STK, SP. lia.
- intros x Hx. apply W2. exact Hx.
- intros x Hx N1 N2. apply RAW4; [exact Hx | intros HS; apply N1; unfold fb_stk, REALLOC_STACK, ALLOC_STACK; unfold STK, SP in HS; lia | exact N2].
Qed.
End m.
End S2.
End FB.
Theorem src0_realloc_fb : OBL_fb_T.
Proof using.
intros FB L A regs mem md g am fr n a ka rg HC Hth gd err regs2 mem2 AT2.
pose proof (proj1 AT2) as Hgd. pose proof (proj1 (proj2 AT2)) as Herr.
eapply mreal_SR_pre; [eapply to_S4; eassumption|].
intros c4 (ms4 & -> & HS4 & RAW4).
destruct (S4_shape (rcr am fr)) as (Hpc & Hrv & _).
rewrite (st_ok_mkst src0segs (Er L regs g am fr n a rg gd err) _ _ HS4 Hrv), Hpc.
unfold OBL_fb_gen in FB. apply FB. eapply fb_at_S4; eassumption.
Qed.
End h.
