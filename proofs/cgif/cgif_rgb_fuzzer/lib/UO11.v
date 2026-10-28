(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YK0v YQ0k YN06 YK0s YN02 YK1j YK1a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0a YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0q YP0m YP0o YP10 YP0v
YP0n YP0r YP0u YP0c YP0e YP0f.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YQ01 YO2f
YO29 YO2a YO2c YO30
UO0c UO08 UO0b UO16 UO0y UO0z
UO14 UO13.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma lit5 k : (1 <= k <= 31)%nat -> Z_to_bv 5 (Z.of_nat k) = nat_to_reg k.
Proof. intros Hk. rewrite (Z_to_bv5_nat_to_reg (Z.of_nat k)) by lia. rewrite Nat2Z.id. reflexivity. Qed.
End f.
Ltac vnth H i V := pose proof (f_equal (fun l => List.nth i l (SLit 0)) H) as V; cbn [List.nth] in V;
try (rewrite lit5 in V by lia; cbn [nat_to_reg] in V).
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ptr_addr_paddR Lx p d : ptr_addr Lx (padd p d) = ptr_addr Lx p + d.
Proof. destruct p as [rr o]. unfold ptr_addr, loc_addr, padd. lia. Qed.
Lemma regs_ok_intro E0 sr rs : nth 0 sr (SLit 0) = SLit 0 ->
(forall i, (1 <= i <= 31)%nat -> getr rs (nat_to_reg i) = sv_denot E0 (nth i sr (SLit 0))) -> regs_ok E0 sr rs.
Proof.
intros H0 H r. unfold sr_get. pose proof (u5_range r) as Hr. destruct (bv_eqb r 0) eqn:Eq.
- unfold getr. rewrite Eq. reflexivity.
- assert (Hr0 : bv_unsigned r <> 0).
{ intros Z0. assert (r = 0%bv) as -> by (apply bv_eq; exact Z0). rewrite bv_eqb_refl in Eq. discriminate. }
unfold ridx. rewrite <- (nat_to_reg_ridx r) at 1. apply H. lia.
Qed.
Section FB.
Hypothesis MALLOC : malloc_impl_realizes.
Hypothesis FREE : free_impl_realizes.
Hypothesis MEMCPY : memcpy_spec.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YP0j.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Variables (gd err : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte).
Hypothesis AT2 : at_S2 L regs mem g am fr n a rg gd err regs2 mem2.
Lemma Hgd : 0 <= gd < 2 ^ 64. Proof. exact (proj1 AT2). Qed.
Lemma Herr : 0 <= err < 2 ^ 32. Proof. exact (proj1 (proj2 AT2)). Qed.
Local Notation VV := (UO0y.vv L regs g am fr a rg).
Local Notation rcr := (UO0y.rcr am fr).
Local Notation E := (Er L regs g am fr n a rg gd err).
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let M : MRc ubs2_msyms L A mem md := M L A regs mem md g am fr n a ka rg HC.
Let MX : MRx ubs2_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
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
(forall x, STK x -> writable_at ubs2segs mem x) /\ getr regs 4 = Z_to_bv 64 ubs2_tp /\
(forall x, ERRN x -> writable_at ubs2segs mem x).
Proof.
pose proof PRE as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
unfold REALLOC_STACK, ALLOC_STACK in *. unfold STK, ERRN, SP.
repeat split; auto.
Qed.
Lemma Hin : In (pp am fr, NOLD) (user_blocks A). Proof. exact (rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Hinit : st_init_done A = true. Proof. exact (init_done_of_block A _ HW Hin). Qed.
Lemma Hn : NOLD + PGSZ <= n < 2 ^ 62. Proof. exact (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Hbig : MMAP_THRESHOLD < NOLD. Proof. exact (rc_big _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Ha0 : getr regs 10 = Z_to_bv 64 P. Proof. exact (rc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma Pblk : 4096 <= P /\ 0 < NOLD /\ P + NOLD <= alloc_ceiling /\ (forall i, 0 <= i < NOLD -> present mem (P + i) /\ ~ owned ubs2_msyms L A (P + i)).
Proof.
pose proof (mr_blocks_range _ _ (MRx_laws ubs2_msyms) L A mem md _ _ MX Hin) as [H1 H2].
split; [exact H1|]. split; [pose proof Hbig; unfold MMAP_THRESHOLD in *; lia|]. split; [exact H2|]. intros i Hi.
pose proof (mr_blocks _ _ (MRx_laws ubs2_msyms) L A mem md _ _ i MX Hin Hi) as (Q1 & _ & _ & Q4). auto.
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
rewrite Ha0. apply lit64_small. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YN05.alloc_ceiling_val. lia.
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
{ unfold UO0y.vv, fv_of. cbn [fv_end]. unfold P, NOLD, pp, slot_end, frame_ptr, reserved_of.
rewrite !ptr_addr_paddR. lia. }
assert (Epn : fv_pn VV = P + NOLD) by reflexivity.
clearbody XR. clear FP. unfold UO0y.rcr in *. unfold rcase_of in *.
destruct (reserved_of am fr =? 0) eqn:E0; [| destruct (reserved_of am fr <? 5) eqn:E1; [| destruct (reserved_of am fr =? 5) eqn:E2]]; cbn [ENDR].
- apply Z.eqb_eq in E0. rewrite (den_off0 _ XR). apply (f_equal (Z_to_bv 64)). change (xvr L regs g am fr n a rg gd err aEND) with (fv_end VV). lia.
- rewrite (den_off0 _ XR). apply (f_equal (Z_to_bv 64)). exact Epn.
- apply Z.eqb_eq in E2. rewrite (den_off _ XR); [apply (f_equal (Z_to_bv 64)); change (xvr L regs g am fr n a rg gd err aEND) with (fv_end VV); lia|].
change (xvr L regs g am fr n a rg gd err aEND) with (fv_end VV). unfold CEIL in LF. lia.
- rewrite (den_off0 _ XR). apply (f_equal (Z_to_bv 64)). exact Epn.
Qed.
Lemma base_SP : base_val E (Some aSP) = SP.
Proof. cbn [base_val]. unfold aSP. rewrite E_reg by lia. reflexivity. Qed.
Lemma base_TP : base_val E (Some aTP) = ubs2_tp.
Proof.
cbn [base_val]. unfold aTP. rewrite E_reg by lia. change (nat_to_reg 4) with (4%bv : bv 5).
destruct PREf as (_ & _ & _ & _ & _ & -> & _). apply lit64_small. unfold ubs2_tp. lia.
Qed.
Lemma not_wr_entry x : 0 <= x < 2 ^ 64 -> ~ STK x -> ~ ERRN x -> ~ in_wrange E (entry_mem rcr) x.
Proof.
intros Hx N1 N2 W. apply wr_entry in W. rewrite base_SP, base_TP in W. unfold STK, ERRN in *. rewrite ERRNO2_val in N2. lia.
Qed.

Lemma anyblock_off_img L0 A0 m0 md0 q k x : MRc ubs2_msyms L0 A0 m0 md0 -> In (q, k) (user_blocks A0) ->
ptr_addr L0 q <= x < ptr_addr L0 q + k -> ~ in_img1 x.
Proof.
intros M0 Hq Hx Hi. destruct (block_region A0 q k (mc_wf _ _ _ _ _ M0) Hq) as (kr & o & rg0 & Ep & Hrg0 & _ & Hl0 & Ho & Hk & Hon & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M0) kr rg0 Hrg0 Hl0) as (_ & _ & _ & Himg).
apply (Himg x); [| apply in_img1_in_img; exact Hi]. unfold ptr_addr in Hx. rewrite Ep in Hx. cbn [loc_addr] in Hx. lia.
Qed.
Lemma errno_img x : ERRN x -> in_img1 x.
Proof. intros Hx. apply ubs2_img_range. apply ubs2_errno_img. exact Hx. Qed.
Lemma MRx_frame_gen L0 A0 m0 m1 md0 (dlo dhi : Z) :
let D := fun x => dlo <= x < dhi in
MRx ubs2_msyms L0 A0 m0 md0 -> alloc_ceiling + 8256 <= SP ->
(forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ~ ERRN x -> ~ D x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
(forall x, D x -> ~ owned ubs2_msyms L0 A0 x /\ (present m0 x -> present m1 x)) ->
MRx ubs2_msyms L0 A0 m1 md0.
Proof.
intros D MX0 Hceil RAW HD. pose proof (MRx_MRc _ _ _ _ _ MX0) as M0. destruct (mc_md _ _ _ _ _ M0) as (Hh & Hlz & Hmat).
pose proof YN05.alloc_ceiling_val as HCV.
assert (OW : forall x, owned ubs2_msyms L0 A0 x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)).
{ intros x Ho. pose proof (owned_low _ L0 A0 m0 md0 x M0 Ho). apply RAW; [lia | unfold STK; intro; lia | |].
- intros He. exact (ubs2_errno_not_owned L0 A0 m0 md0 x M0 He Ho).
- intros HDx. exact (proj1 (HD x HDx) Ho). }
eapply (mr_frame _ _ (MRx_laws ubs2_msyms)); [exact MX0 | | | | reflexivity | exact Hh | exact Hlz | exact Hmat].
- intros x Ho. apply (proj1 (same_byte_views2 m0 m1 x (OW x Ho))).
- intros x Ho Hp. exact (present_same m0 m1 x (OW x Ho) Hp).
- intros q k i Hq Hi. pose proof (mr_blocks _ _ (MRx_laws ubs2_msyms) L0 A0 m0 md0 q k i MX0 Hq Hi) as (Hp & Hlo & Hhi & _).
assert (DEC : D (ptr_addr L0 q + i) \/ ~ D (ptr_addr L0 q + i)) by (subst D; cbn beta; lia).
destruct DEC as [HDx | HDx]; [exact (proj2 (HD _ HDx) Hp)|].
apply (present_same m0 m1); [| exact Hp]. apply RAW; [lia | unfold STK; intro; lia | | exact HDx].
intros He. exact (anyblock_off_img L0 A0 m0 md0 q k (ptr_addr L0 q + i) M0 Hq ltac:(lia) (errno_img _ He)).
Qed.
Lemma MRx_scratch L0 A0 m0 m1 md0 :
MRx ubs2_msyms L0 A0 m0 md0 -> alloc_ceiling + 8256 <= SP ->
(forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ~ ERRN x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
MRx ubs2_msyms L0 A0 m1 md0.
Proof.
intros MX0 Hceil RAW. apply (MRx_frame_gen L0 A0 m0 m1 md0 0 0 MX0 Hceil).
- intros x Hx N1 N2 _. exact (RAW x Hx N1 N2).
- intros x Hx. exfalso. lia.
Qed.
Definition RAW (m0 m1 : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ~ ERRN x -> m1 (Z_to_bv 64 x) = m0 (Z_to_bv 64 x).
Lemma to_S4 :
SR ubs2segs (mkCfg (mkst (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem2 (seg_rom ubs2segs)) md)
(fun c4 => exists ms4, c4 = mkCfg ms4 md /\ st_ok ubs2segs E (S4 rcr) ms4 /\ RAW mem (ms_mem ms4)).
Proof.
destruct AT2 as (_ & _ & Hregs2 & Hmem2 & HG2 & HF2). destruct Hmd as (Hh & Hlz & _).
destruct (S2_run_ok rcr) as (_ & Hpc2 & Hrv2).
assert (HS : st_ok ubs2segs E (S2no rcr) (mkst (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem2 (seg_rom ubs2segs))).
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
Hypothesis HS4 : st_ok ubs2segs E (S4 rcr) ms4.
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
pose proof (st_ok_regs_ok ubs2segs E _ _ HS4) as R. change (regs_ok E (ss_regs (S4 rcr)) regs4) in R.
pose proof XP as XP. pose proof XN as XN.
repeat match goal with |- _ /\ _ => split end.
- rewrite (R 1%bv), V1. reflexivity.
- rewrite (R 2%bv), V2. rewrite (den_off _ XR); [reflexivity|]. change (xvr L regs g am fr n a rg gd err 2) with SP.
pose proof PREf as (_ & _ & P3 & P4 & _). pose proof YN05.alloc_ceiling_val. lia.
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
(forall x, STK x -> writable_at ubs2segs mem4 x) /\ (forall x, ERRN x -> writable_at ubs2segs mem4 x) /\
Forall (chunk_ok ubs2segs E mem4 SP) frame_chunks.
Proof.
pose proof (st_ok_mem_ok ubs2segs E _ _ HS4) as (_ & ROK & _). change (ms_mem ms4) with mem4 in ROK.
destruct (S4_shape rcr) as (_ & _ & _ & Hsm). rewrite Hsm in ROK.
assert (Rstk : region_ok ubs2segs E mem4 (stk3 rcr)) by (eapply (proj1 (Forall_forall _ _) ROK); cbn; tauto).
assert (Rerr : region_ok ubs2segs E mem4 (YQ0b.mkRegion (Some aTP) (-164) (-160) (-164) (-160) [mkChunk (-164) (CVal 4 (SLit 12))]))
by (eapply (proj1 (Forall_forall _ _) ROK); cbn; tauto).
destruct Rstk as (_ & _ & Wstk & Cstk). destruct Rerr as (_ & _ & Werr & _).
cbn [r_base r_wlo r_whi r_chunks stk3] in Wstk, Cstk, Werr. rewrite base_SP in Wstk, Cstk. rewrite base_TP in Werr.
split; [|split].
- intros x Hx. unfold STK in Hx. replace x with (SP + (x - SP)) by lia. apply Wstk. lia.
- intros x Hx. unfold ERRN in Hx. rewrite ERRNO2_val in Hx. replace x with (ubs2_tp + (x - ubs2_tp)) by lia. apply Werr. lia.
- apply Forall_app in Cstk as [_ Cstk]. apply Forall_app in Cstk as [_ Cstk]. exact Cstk.
Qed.
Lemma pre4 : call_pre ubs2_msyms (MRx ubs2_msyms) L A regs4 mem4 md.
Proof.
pose proof PREf as (Hret & Hal & Hceil & H63 & Hstk & Htp & Herrw). pose proof S4_regs as (R1 & R2 & R3 & R4 & _).
pose proof S4_mem as (W1 & W2 & _). pose proof PRE as (_ & _ & HB & _). pose proof YN05.alloc_ceiling_val.
assert (ESP : spZ regs4 = SP - 64) by (unfold spZ; rewrite R2; apply lit64_small; lia).
unfold call_pre. rewrite ESP. split; [exact (MRx_scratch L A mem mem4 md MX Hceil RAW4)|].
split; [exact HW|]. split; [exact HB|]. split; [rewrite R1; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite <- Zminus_mod_idemp_l, Hal; reflexivity|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
split; [intros x Hx; apply W1; unfold STK, ALLOC_STACK in *; lia|].
split; [rewrite R4; exact Htp|]. split; [intros x Hx; apply W2; unfold ERRN; rewrite ERRNO2_val; exact Hx|].
intros Hf. rewrite Hinit in Hf. discriminate.
Qed.
Lemma malloc_call :
mreal ubs2segs (mkCfg ms4 md) (malloc n A)
(fun r c => malloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs4 mem4 md n r c /\
(length (st_regions A) <= length (st_regions (snd r)))%nat).
Proof.
destruct (S4_shape rcr) as (Hpc & Hrv & _). pose proof S4_regs as (_ & _ & _ & _ & _ & _ & R10 & _). pose proof Hn. pose proof Hbig.
rewrite (st_ok_mkst ubs2segs E _ _ HS4 Hrv), Hpc.
apply mreal_tall; [| apply malloc_regions_tall].
apply MALLOC; [exact pre4 | exact R10 | unfold MMAP_THRESHOLD, PGSZ in *; lia].
Qed.
Section s.
Variables (L5 : layout) (A5 : astate) (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model).
Hypothesis POST : call_post ubs2_msyms (MRx ubs2_msyms) L A regs4 mem4 md (fun _ => False) L5 A5 regs5 mem5 md5.
Hypothesis LEN5 : (length (st_regions A) <= length (st_regions A5))%nat.
Let MX5 : MRx ubs2_msyms L5 A5 mem5 md5 := proj1 POST.
Lemma M5 : MRc ubs2_msyms L5 A5 mem5 md5. Proof. exact (MRx_MRc _ _ _ _ _ MX5). Qed.
Lemma Hmd5 : m_halted md5 = None /\ m_vm_lazy md5 = [] /\ m_vm_materialized md5 = [].
Proof. exact (mc_md _ _ _ _ _ M5). Qed.
Definition xvj (rs : bvmap 5 word) (nold q : Z) (k : nat) : Z :=
if ((64 <=? k) && (k <? 96))%nat then bv_unsigned (getr rs (nat_to_reg (k - 64)))
else if (k =? 101)%nat then nold else if (k =? 102)%nat then q else xvr L regs g am fr n a rg gd err k.
Lemma xvj_range rs nold q : 0 <= nold < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> forall k, 0 <= xvj rs nold q k < 2 ^ 64.
Proof.
intros Hnold Hq k. unfold xvj. destruct ((64 <=? k) && (k <? 96))%nat; [apply u64_range|].
destruct (k =? 101)%nat; [lia|]. destruct (k =? 102)%nat; [lia|]. apply XR.
Qed.
Lemma xvj_low rs nold q k : (k < 64)%nat -> xvj rs nold q k = xvr L regs g am fr n a rg gd err k.
Proof.
intros Hk. unfold xvj. replace (64 <=? k)%nat with false by (symmetry; apply Nat.leb_gt; lia). cbn [andb].
replace (k =? 101)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (k =? 102)%nat with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
Lemma xvj_junk rs nold q i : (i < 32)%nat -> xvj rs nold q (64 + i) = bv_unsigned (getr rs (nat_to_reg i)).
Proof.
intros Hi. unfold xvj. replace ((64 <=? 64 + i) && (64 + i <? 96))%nat with true.
2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia. }
f_equal. f_equal. f_equal. lia.
Qed.
Lemma POST_facts :
WF A5 /\ bounded A5 /\ layout_le A L L5 /\
(forall b k, In (b, k) (user_blocks A) -> In (b, k) (user_blocks A5) -> ptr_addr L5 b = ptr_addr L b) /\
regs_preserved regs4 regs5 /\ (exists vm', md5 = with_vmmaps vm' md) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img ubs2_msyms x) ->
~ owned ubs2_msyms L A x -> ~ owned ubs2_msyms L5 A5 x -> ~ scratch ubs2_msyms regs4 x ->
mbyte ubs2segs mem5 x = mbyte ubs2segs mem4 x /\ (writable_at ubs2segs mem4 x <-> writable_at ubs2segs mem5 x)) /\
(forall b k i, In (b, k) (user_blocks A) -> In (b, k) (user_blocks A5) -> 0 <= i < k ->
mbyte ubs2segs mem5 (ptr_addr L b + i) = mbyte ubs2segs mem4 (ptr_addr L b + i)) /\
(forall x, scratch ubs2_msyms regs4 x -> writable_at ubs2segs mem5 x).
Proof.
pose proof POST as (_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
repeat (split; [assumption|]). split; [| split; [exact H8 | exact H9]].
intros x Hx N1 N2 N3. apply (H7 x Hx N1 N2 N3). intros [].
Qed.
Lemma scratch4 x : scratch ubs2_msyms regs4 x <-> (SP - 8256 <= x < SP - 64) \/ ERRN x.
Proof.
pose proof S4_regs as (_ & R2 & _). pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val.
unfold scratch, spZ. rewrite R2, lit64_small by lia. unfold ALLOC_STACK, ERRN. rewrite ERRNO2_val.
change (errno_addr ubs2_msyms) with (ubs2_tp + -164). lia.
Qed.
Lemma frame_kept x : SP - 64 <= x < SP ->
mbyte ubs2segs mem5 x = mbyte ubs2segs mem4 x /\ (writable_at ubs2segs mem4 x <-> writable_at ubs2segs mem5 x).
Proof.
intros Hx. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val.
destruct POST_facts as (_ & _ & _ & _ & _ & _ & FR & _). apply FR.
- left. lia.
- intros Ho. pose proof (owned_low _ L A mem md x M Ho). lia.
- intros Ho. pose proof (owned_low _ L5 A5 mem5 md5 x M5 Ho). lia.
- intros Hs. apply scratch4 in Hs. unfold ERRN in Hs. rewrite ERRNO2_val in Hs. unfold ubs2_tp in Hs. lia.
Qed.
Lemma stk_writable5 x : STK x -> writable_at ubs2segs mem5 x.
Proof.
intros Hx. destruct (Z_lt_le_dec x (SP - 64)).
- apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 POST_facts)))))))). apply scratch4. left. unfold STK in Hx. lia.
- apply (proj1 (proj2 (frame_kept x ltac:(unfold STK in Hx; lia)))). apply (proj1 S4_mem). exact Hx.
Qed.
Lemma errno_writable5 x : ERRN x -> writable_at ubs2segs mem5 x.
Proof. intros Hx. apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 POST_facts)))))))). apply scratch4. right. exact Hx. Qed.
Lemma frame_chunks5 E' : env_agree 32 E E' -> Forall (chunk_ok ubs2segs E' mem5 SP) frame_chunks.
Proof.
intros HA. pose proof (proj2 (proj2 S4_mem)) as C4.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C4 c Hc) as Cc.
assert (Hoff : -64 <= c_off c /\ c_off c + c_len c <= 0 /\ exists r, (1 <= r <= 31)%nat /\ c_val c = CVal 8 (SOff r 0)).
{ unfold frame_chunks in Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [cbn; split; [lia|]; split; [lia|]; eexists; split; [|reflexivity]; lia|]). destruct Hc. }
destruct Hoff as (O1 & O2 & r & Hr & Ec).
intros i Hi. destruct (Cc i Hi) as (b & Hb1 & Hb2). exists b. split.
- rewrite <- Hb1. rewrite Ec. cbn [cbyte sv_denot]. rewrite (proj1 HA r ltac:(lia)). reflexivity.
- rewrite <- Hb2. apply (proj1 (frame_kept (SP + c_off c + i) ltac:(lia))).
Qed.
Lemma CS5 j : In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr regs5 (nat_to_reg j) = getr regs4 (nat_to_reg j).
Proof.
intros Hj. destruct POST_facts as (_ & _ & _ & _ & PRES & _).
assert (H : (1 <= j <= 31)%nat /\ callee_saved (Z.of_nat j)).
{ unfold callee_saved. cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [split; [lia|lia] |]). destruct Hj. }
destruct H as [H1 H2]. rewrite <- (lit5 j) by lia. apply PRES. exact H2.
Qed.
Ltac oncs i R := rewrite (CS5 i) by (cbn; tauto); cbn [nat_to_reg]; rewrite R.
Section t.
Hypothesis A0_5 : getr regs5 10 = Z_to_bv 64 0.
Hypothesis UB5 : user_blocks A5 = user_blocks A.
Let E6 := EV (xvj regs5 (P + NOLD) 4096).
Lemma XR6 : forall k, 0 <= xvj regs5 (P + NOLD) 4096 k < 2 ^ 64.
Proof. apply xvj_range; [| lia]. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YN05.alloc_ceiling_val. lia. Qed.
Lemma EA6 : env_agree 64 E E6.
Proof. split; [| reflexivity]. intros k Hk. unfold E6, Er, EV. cbn [ew]. rewrite xvj_low by exact Hk. reflexivity. Qed.
Lemma regs_ok6 : regs_ok E6 (regs_after_malloc (SLit 0) (SOff aNOLD 0)) regs5.
Proof.
pose proof S4_regs as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21 & R22 & R23).
pose proof XR6 as XR6. pose proof EA6 as EA6. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YN05.alloc_ceiling_val as HCV.
pose proof PREf as (_ & _ & Hceil & H63 & _).
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_after_malloc]; unfold junk; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_off0 _ XR6), xvj_junk by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
- oncs 2%nat R2. rewrite (den_off _ XR6); [reflexivity|]. change (xvj regs5 (P + NOLD) 4096 aSP) with SP. lia.
- oncs 3%nat R3. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 3 ltac:(lia)).
- oncs 4%nat R4. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 4 ltac:(lia)).
- oncs 8%nat R8. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XN. reflexivity.
- oncs 9%nat R9. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- cbn [nat_to_reg]. rewrite A0_5. reflexivity.
- oncs 18%nat R18. rewrite (den_off0 _ XR6). reflexivity.
- oncs 19%nat R19. rewrite (den_off0 _ XR6). reflexivity.
- oncs 20%nat R20. reflexivity.
- oncs 21%nat R21. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- oncs 22%nat R22. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XN. reflexivity.
- rewrite (CS5 23%nat) by (cbn; tauto). rewrite (R23 23%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 23 ltac:(lia)).
- rewrite (CS5 24%nat) by (cbn; tauto). rewrite (R23 24%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 24 ltac:(lia)).
- rewrite (CS5 25%nat) by (cbn; tauto). rewrite (R23 25%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 25 ltac:(lia)).
- rewrite (CS5 26%nat) by (cbn; tauto). rewrite (R23 26%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 26 ltac:(lia)).
- rewrite (CS5 27%nat) by (cbn; tauto). rewrite (R23 27%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 27 ltac:(lia)).
Qed.
Lemma EA6_32 : env_agree 32 E E6.
Proof. split; [| reflexivity]. intros k Hk. apply (proj1 EA6). lia. Qed.
Lemma base_SP6 : base_val E6 (Some aSP) = SP.
Proof. cbn [base_val]. rewrite (proj1 EA6 aSP ltac:(unfold aSP; lia)). exact base_SP. Qed.
Lemma mem_ok6 : mem_ok ubs2segs E6 mem5 after_memR.
Proof.
pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val.
split; [vm_compute; reflexivity|]. split; [| cbn; tauto].
apply Forall_cons; [| apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite base_SP6; [lia | lia | | exact (frame_chunks5 E6 EA6_32)].
intros o Ho. apply stk_writable5. unfold STK. lia.
Qed.
Lemma facts_ok6 : facts_ok E6 (mkFacts after_atomsR [] []).
Proof.
pose proof PREf as (_ & Hal & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val. pose proof Pblk as (P1 & P0 & P2 & _).
pose proof (fp_p _ _ _ _ FP) as [_ Pal]. change (fv_p VV) with (xvr L regs g am fr n a rg gd err aP) in Pal. rewrite XP in Pal. pose proof Hn. pose proof Hbig.
split; [| split; exact I].
unfold after_atomsR. cbn [atoms_ok f_atoms]. unfold afact_ok; cbn [af_lo af_hi af_al2].
unfold E6. rewrite !(ew_EV _ XR6).
change (xvj regs5 (P + NOLD) 4096 aSP) with SP.
change (xvj regs5 (P + NOLD) 4096 aNOLD) with (P + NOLD). change (xvj regs5 (P + NOLD) 4096 aQ) with 4096.
rewrite (xvj_low _ _ _ aTP ltac:(unfold aTP; lia)), (xvj_low _ _ _ aN ltac:(unfold aN; lia)), XN, (xvj_low _ _ _ aP ltac:(unfold aP; lia)), XP.
replace (xvr L regs g am fr n a rg gd err aTP) with ubs2_tp.
2:{ symmetry. unfold xvr, aTP. cbn [Nat.ltb Nat.leb]. exact (xvf4 L A regs mem md g am fr n a ka rg HC). }
unfold CEIL, ubs2_tp, MMAP_THRESHOLD, PGSZ in *. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
rewrite ?Z.mod_1_r. repeat match goal with |- _ /\ _ => split | |- True => exact I end; try lia.
all: reflexivity.
Qed.
Lemma st_ok6 : st_ok ubs2segs E6 S6z (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom ubs2segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts S6z resv_denot].
repeat (split; [reflexivity|]). split; [exact regs_ok6|]. split; [exact mem_ok6 | exact facts_ok6].
Qed.
Lemma leaf_none :
SR ubs2segs (mkCfg (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom ubs2segs)) md5)
(realloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs mem md (pp am fr) (fr_n fr) n (None, A5)).
Proof.
destruct Hmd5 as (Hh5 & Hlz5 & Hmat5). pose proof PREf as (Hret & Hal & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val as HCV.
pose proof EA6 as EA6. pose proof XR6 as XR6.
eapply SR_bind; [exact (S7_run E6 _ md5 Hh5 Hlz5 st_ok6)|]. intros c7 (ms7 & -> & HS7 & HF7). cbn [ms_mem] in HF7.
destruct S7_shape as (Hpc7 & Hrv7 & Hview7 & Ha07 & Hsm7).
pose proof (st_ok_regs_ok ubs2segs E6 _ _ HS7) as R7.
unfold callee_view, callee_view0, view in Hview7. cbn [map] in Hview7.
vnth Hview7 0%nat V1. vnth Hview7 1%nat V2. vnth Hview7 2%nat V3. vnth Hview7 3%nat V4. vnth Hview7 4%nat V8. vnth Hview7 5%nat V9.
vnth Hview7 6%nat V18. vnth Hview7 7%nat V19. vnth Hview7 8%nat V20. vnth Hview7 9%nat V21. vnth Hview7 10%nat V22. vnth Hview7 11%nat V23.
vnth Hview7 12%nat V24. vnth Hview7 13%nat V25. vnth Hview7 14%nat V26. vnth Hview7 15%nat V27.
assert (CV : forall i, In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
getr (ms_regs ms7) (nat_to_reg i) = getr regs (nat_to_reg i)).
{ intros i Hi0. rewrite <- (den_reg i) by (cbn in Hi0; lia). rewrite <- (sv_denot_agree 64 E E6 _ EA6) by (cbn in Hi0; destruct Hi0 as [<-|Hi0]; [reflexivity|]; repeat (destruct Hi0 as [<-|Hi0]; [reflexivity|]); destruct Hi0).
rewrite (R7 (nat_to_reg i)). f_equal. cbn in Hi0.
repeat (destruct Hi0 as [<-|Hi0]; [cbn [nat_to_reg]; assumption|]). destruct Hi0. }
assert (E1 : ew E6 1 = getr regs 1) by (rewrite (proj1 EA6 1%nat ltac:(lia)); exact (E_reg 1 ltac:(lia))).
assert (RAW7 : forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ms_mem ms7 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x)).
{ intros x Hx N1. apply HF7. rewrite lit64_small by lia. intros W. apply wr_after in W. rewrite base_SP6 in W. exact (N1 W). }
eapply (SR_realloc_ret E6 S7 ms7 md5 _ HS7 Hrv7 Hpc7 V1); [rewrite E1; exact Hret | exact Hh5 | exact Hlz5 |].
unfold realloc_leaf. exists L5, (ms_regs ms7), (ms_mem ms7), md5. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [| split; [rewrite (R7 10%bv), Ha07; reflexivity | exact UB5]].
destruct POST_facts as (W5 & B5 & LE5 & AD5 & PRES5 & VM5 & FR5 & BL5 & SC5).
pose proof (st_ok_mem_ok ubs2segs E6 _ _ HS7) as (_ & ROK7 & _). rewrite Hsm7 in ROK7. apply Forall_inv in ROK7.
destruct ROK7 as (_ & _ & W7 & _). cbn [r_base r_wlo r_whi] in W7. rewrite base_SP6 in W7.
unfold call_post_k. change (ms_segs ubs2_msyms) with ubs2segs.
split; [| split; [exact W5 | split; [exact B5 | split; [exact LE5 | split; [exact AD5 | split; [| split; [exact VM5 | split; [| split]]]]]]]].
-   apply (MRx_scratch L5 A5 mem5 (ms_mem ms7) md5 MX5 Hceil). intros x Hx N1 _. exact (RAW7 x Hx N1).
-   intros r Hr. destruct (callee_saved_cases r Hr) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r Rr). apply CV. cbn. cbn in RI. tauto.
-   intros x Hx N1 N2 N3 N4.
assert (Hx64 : 0 <= x < 2 ^ 64) by (destruct Hx as [Hx|Hx]; [lia | apply ubs2_img_range in Hx; unfold in_img1 in Hx; lia]).
assert (NS : ~ STK x /\ ~ ERRN x).
{ unfold scratch_k, REALLOC_STACK, ALLOC_STACK in N3. unfold STK, ERRN. rewrite ERRNO2_val. change (errno_addr ubs2_msyms) with (ubs2_tp + -164) in N3. change (spZ regs) with SP in N3. split; intro; apply N3; lia. }
destruct NS as [NS1 NS2].
destruct (same_byte_views2 mem5 (ms_mem ms7) x (RAW7 x Hx64 NS1)) as [A1 A2].
destruct (FR5 x Hx N1 N2 ltac:(intros Hs; apply scratch4 in Hs; destruct Hs as [Hs|Hs]; [unfold STK in NS1; lia | exact (NS2 Hs)])) as [B1 B2].
destruct (same_byte_views2 mem mem4 x (RAW4 x Hx64 NS1 NS2)) as [C1 C2].
rewrite A1, B1, C1. tauto.
-   intros b k i Hb1 Hb2 Hi.
pose proof (mr_blocks_range _ _ (MRx_laws ubs2_msyms) L A mem md b k MX Hb1) as [Lo Hi2].
assert (Hx64 : 0 <= ptr_addr L b + i < 2 ^ 64) by lia.
assert (NS1 : ~ STK (ptr_addr L b + i)) by (unfold STK; intro; lia).
assert (NS2 : ~ ERRN (ptr_addr L b + i)) by (intros He; exact (anyblock_off_img L A mem md b k (ptr_addr L b + i) M Hb1 ltac:(lia) (errno_img _ He))).
rewrite (proj1 (same_byte_views2 mem5 (ms_mem ms7) _ (RAW7 _ Hx64 NS1))).
rewrite (BL5 b k i Hb1 Hb2 Hi). apply (proj1 (same_byte_views2 mem mem4 _ (RAW4 _ Hx64 NS1 NS2))).
-   intros x Hs. unfold scratch_k, REALLOC_STACK, ALLOC_STACK in Hs.
change (errno_addr ubs2_msyms) with (ubs2_tp + -164) in Hs. change (spZ regs) with SP in Hs.
destruct Hs as [Hs|Hs].
+ replace x with (SP + (x - SP)) by lia. apply W7. lia.
+ apply (writable_same2 mem5 (ms_mem ms7) x); [apply RAW7; [unfold ubs2_tp in Hs; lia | unfold STK; unfold ubs2_tp in Hs; intro; lia] |].
apply errno_writable5. unfold ERRN. rewrite ERRNO2_val. lia.
Qed.
End t.
Lemma mem_ok_after_xfer E1 E2 (m1 m2 : word -> option byte) :
env_agree 32 E E1 -> env_agree 32 E E2 -> mem_ok ubs2segs E1 m1 after_memR ->
(forall x, SP - 64 <= x < SP -> m2 (Z_to_bv 64 x) = m1 (Z_to_bv 64 x)) ->
(forall x, STK x -> writable_at ubs2segs m2 x) -> mem_ok ubs2segs E2 m2 after_memR.
Proof.
intros A1 A2 (Hwf & ROK & PD) EQ W2.
assert (B1 : base_val E1 (Some aSP) = SP) by (cbn [base_val]; rewrite (proj1 A1 aSP ltac:(unfold aSP; lia)); exact base_SP).
assert (B2 : base_val E2 (Some aSP) = SP) by (cbn [base_val]; rewrite (proj1 A2 aSP ltac:(unfold aSP; lia)); exact base_SP).
split; [exact Hwf|]. split; [| cbn; tauto]. apply Forall_inv in ROK.
destruct ROK as (R1 & R2 & R3 & R4). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks] in R1, R2, R3, R4. rewrite B1 in R1, R2, R3, R4.
apply Forall_cons; [| apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite B2; [exact R1 | exact R2 | |].
- intros o Ho. apply W2. unfold STK. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) R4 c Hc) as Cc.
assert (Hoff : -64 <= c_off c /\ c_off c + c_len c <= 0 /\ exists r, (1 <= r <= 31)%nat /\ c_val c = CVal 8 (SOff r 0)).
{ unfold frame_chunks in Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [cbn; split; [lia|]; split; [lia|]; eexists; split; [|reflexivity]; lia|]). destruct Hc. }
destruct Hoff as (O1 & O2 & r & Hr & Ec).
intros i Hi. destruct (Cc i Hi) as (b & Hb1 & Hb2). exists b. split.
+ rewrite <- Hb1. rewrite Ec. cbn [cbyte sv_denot]. rewrite (proj1 A2 r ltac:(lia)), (proj1 A1 r ltac:(lia)). reflexivity.
+ rewrite <- Hb2. apply (proj1 (same_byte_views2 m1 m2 _ (EQ (SP + c_off c + i) ltac:(lia)))).
Qed.
Section v.
Variables (q : sptr) (l1 l2 : list (sptr * Z)).
Hypothesis A0_5 : getr regs5 10 = Z_to_bv 64 (ptr_addr L5 q).
Hypothesis NZ5 : ptr_addr L5 q <> 0.
Hypothesis UB5 : user_blocks A5 = l1 ++ (q, n) :: l2.
Hypothesis UBA : user_blocks A = l1 ++ l2.
Definition Q : Z := ptr_addr L5 q.
Lemma q_in5 : In (q, n) (user_blocks A5). Proof. rewrite UB5. apply in_or_app. right. left. reflexivity. Qed.
Lemma p_in5 : In (pp am fr, NOLD) (user_blocks A5).
Proof. pose proof Hin as H. rewrite UBA in H. rewrite UB5. apply in_app_iff in H. apply in_or_app. destruct H; [left; assumption | right; right; assumption]. Qed.
Lemma P5 : ptr_addr L5 (pp am fr) = P.
Proof. destruct POST_facts as (_ & _ & _ & AD & _). apply (AD (pp am fr) NOLD); [exact Hin | exact p_in5]. Qed.
Lemma Qblk : 4096 <= Q /\ Q + n <= alloc_ceiling /\ Q mod 16 = 0 /\
(forall i, 0 <= i < n -> present mem5 (Q + i) /\ ~ owned ubs2_msyms L5 A5 (Q + i)).
Proof.
pose proof (mr_blocks_range _ _ (MRx_laws ubs2_msyms) L5 A5 mem5 md5 _ _ MX5 q_in5) as [H1 H2].
split; [exact H1|]. split; [exact H2|]. split; [exact (mr_blocks_aligned _ _ (MRx_laws ubs2_msyms) L5 A5 mem5 md5 _ _ MX5 q_in5)|].
intros i Hi. pose proof (mr_blocks _ _ (MRx_laws ubs2_msyms) L5 A5 mem5 md5 _ _ i MX5 q_in5 Hi) as (B1 & _ & _ & B4). unfold Q. auto.
Qed.
Lemma Pblk5 : forall i, 0 <= i < NOLD -> present mem5 (P + i) /\ ~ owned ubs2_msyms L5 A5 (P + i).
Proof.
intros i Hi. pose proof (mr_blocks _ _ (MRx_laws ubs2_msyms) L5 A5 mem5 md5 _ _ i MX5 p_in5 Hi) as (B1 & _ & _ & B4).
rewrite P5 in B1, B4. auto.
Qed.
Lemma PQ_disjoint : Q + n <= P \/ P + NOLD <= Q.
Proof.
pose proof (mr_blocks_disjoint _ _ (MRx_laws ubs2_msyms) L5 A5 mem5 md5 MX5) as PW. unfold blocks in PW. rewrite UB5 in PW.
pose proof Hin as H. rewrite UBA in H.
change (l1 ++ (q, n) :: l2) with (l1 ++ [(q, n)] ++ l2) in PW.
destruct (pairwise_app_mid ranges_disjoint (fun b : sptr * Z => (ptr_addr L5 (fst b), snd b)) l1 [(q, n)] l2 (q, n) (pp am fr, NOLD) PW ltac:(left; reflexivity) H) as [D|D];
unfold ranges_disjoint in D; cbn [fst snd] in D; rewrite P5 in D; unfold Q; lia.
Qed.
Lemma XRq rs : forall k, 0 <= xvj rs NOLD Q k < 2 ^ 64.
Proof. apply xvj_range; pose proof Qblk as (Q1 & Q2 & _); pose proof Pblk as (P1 & P0 & P2 & _); pose proof Hn; pose proof YN05.alloc_ceiling_val; unfold Q, PGSZ in *; lia. Qed.
Lemma EAq rs : env_agree 64 E (EV (xvj rs NOLD Q)).
Proof. split; [| reflexivity]. intros k Hk. unfold Er, EV. cbn [ew]. rewrite xvj_low by exact Hk. reflexivity. Qed.
Lemma EAq32 rs : env_agree 32 E (EV (xvj rs NOLD Q)).
Proof. split; [| reflexivity]. intros k Hk. apply (proj1 (EAq rs)). lia. Qed.
Lemma facts_after rs cs al :
(cs = [] \/ cs = [mkAC BC_GEU (SOff aN 0) (SOff aNOLD 0)]) ->
(al = [] \/ al = [(SAlu ALU_SUB (SAlu ALU_ADD (SOff aP 0) (SOff aNOLD 0)) (SOff aP 0), SOff aNOLD 0)]) ->
facts_ok (EV (xvj rs NOLD Q)) (mkFacts after_atomsR cs al).
Proof.
intros Hcs Hal0.
pose proof PREf as (_ & Hal & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val. pose proof Pblk as (P1 & P0 & P2 & _). pose proof Qblk as (Q1 & Q2 & Q3 & _).
pose proof (fp_p _ _ _ _ FP) as [_ Pal]. change (fv_p VV) with (xvr L regs g am fr n a rg gd err aP) in Pal. rewrite XP in Pal. pose proof Hn. pose proof Hbig.
pose proof (XRq rs) as XR'.
assert (TP : xvr L regs g am fr n a rg gd err aTP = ubs2_tp).
{ unfold xvr, aTP. cbn [Nat.ltb Nat.leb]. exact (xvf4 L A regs mem md g am fr n a ka rg HC). }
split; [| split].
- unfold after_atomsR. cbn [atoms_ok f_atoms]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite !(ew_EV _ XR').
change (xvj rs NOLD Q aSP) with SP. change (xvj rs NOLD Q aNOLD) with NOLD. change (xvj rs NOLD Q aQ) with Q.
rewrite (xvj_low _ _ _ aTP ltac:(unfold aTP; lia)), (xvj_low _ _ _ aN ltac:(unfold aN; lia)), XN, (xvj_low _ _ _ aP ltac:(unfold aP; lia)), XP, TP.
unfold CEIL, ubs2_tp, MMAP_THRESHOLD, PGSZ in *. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
rewrite ?Z.mod_1_r. repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- cbn [f_conds]. destruct Hcs as [-> | ->]; [exact I|]. split; [| exact I].
unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken]. rewrite !(den_off0 _ XR').
change (xvj rs NOLD Q aNOLD) with NOLD. rewrite (xvj_low _ _ _ aN ltac:(unfold aN; lia)), XN.
rewrite bv_ltu_unsigned, !lit64_small by (unfold MMAP_THRESHOLD, PGSZ in *; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. unfold PGSZ in *. lia.
- cbn [f_alias]. destruct Hal0 as [-> | ->]; [exact I|]. split; [| exact I].
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_sub, alu64_add, !(ew_EV _ XR'), !Z.add_0_r.
change (xvj rs NOLD Q aNOLD) with NOLD. rewrite (xvj_low _ _ _ aP ltac:(unfold aP; lia)), XP.
rewrite !lit64_small by (unfold MMAP_THRESHOLD in *; lia). unfold add64, sub64. rewrite (Z.mod_small (P + NOLD)) by lia.
rewrite Z.mod_small by (unfold MMAP_THRESHOLD in *; lia). lia.
Qed.
Let E6 := EV (xvj regs5 NOLD Q).
Lemma regs_ok6q : regs_ok E6 (regs_after_malloc (SOff aQ 0) (SAlu ALU_ADD (SOff aP 0) (SOff aNOLD 0))) regs5.
Proof.
pose proof S4_regs as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R18 & R19 & R20 & R21 & R22 & R23).
pose proof (XRq regs5) as XR6. pose proof (EAq regs5) as EA6. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YN05.alloc_ceiling_val as HCV.
pose proof PREf as (_ & _ & Hceil & H63 & _).
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_after_malloc]; unfold junk; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_off0 _ XR6), xvj_junk by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
- oncs 2%nat R2. rewrite (den_off _ XR6); [reflexivity|]. change (xvj regs5 NOLD Q aSP) with SP. lia.
- oncs 3%nat R3. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 3 ltac:(lia)).
- oncs 4%nat R4. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 4 ltac:(lia)).
- oncs 8%nat R8. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XN. reflexivity.
- oncs 9%nat R9. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- cbn [nat_to_reg]. rewrite A0_5, (den_off0 _ XR6). reflexivity.
- oncs 18%nat R18. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add, !(ew_EV _ XR6), !Z.add_0_r.
change (xvj regs5 NOLD Q aNOLD) with NOLD. rewrite (xvj_low _ _ _ aP ltac:(unfold aP; lia)), XP.
unfold add64. rewrite !lit64_small by lia. rewrite Z.mod_small by lia. reflexivity.
- oncs 19%nat R19. rewrite (den_off0 _ XR6). reflexivity.
- oncs 20%nat R20. reflexivity.
- oncs 21%nat R21. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- oncs 22%nat R22. rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XN. reflexivity.
- rewrite (CS5 23%nat) by (cbn; tauto). rewrite (R23 23%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 23 ltac:(lia)).
- rewrite (CS5 24%nat) by (cbn; tauto). rewrite (R23 24%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 24 ltac:(lia)).
- rewrite (CS5 25%nat) by (cbn; tauto). rewrite (R23 25%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 25 ltac:(lia)).
- rewrite (CS5 26%nat) by (cbn; tauto). rewrite (R23 26%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 26 ltac:(lia)).
- rewrite (CS5 27%nat) by (cbn; tauto). rewrite (R23 27%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E6 _ EA6) by reflexivity. symmetry. exact (den_reg 27 ltac:(lia)).
Qed.
Lemma st_ok6q : st_ok ubs2segs E6 S6q' (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom ubs2segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts S6q' resv_denot].
repeat (split; [reflexivity|]). split; [exact regs_ok6q|]. split.
- apply (mem_ok_after_xfer (EV (xvj regs5 (P + NOLD) 4096)) E6 mem5 mem5).
+ apply EA6_32. + apply EAq32. + apply mem_ok6. + intros; reflexivity. + apply stk_writable5.
- apply facts_after; right; reflexivity.
Qed.
Definition K10 (regs9 : bvmap 5 word) (mem8 : word -> option byte) (bs : list byte) (ms10 : machine_state) : Prop :=
st_ok ubs2segs (EV (xvj regs9 NOLD Q)) S10 ms10 /\
(forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> mem8 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x)) /\
rdn ubs2segs mem8 (Z_to_bv 64 P) (Z.to_nat NOLD) = Some bs /\ length bs = Z.to_nat NOLD /\
(forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ms_mem ms10 (Z_to_bv 64 x) = wbytes mem8 (Z_to_bv 64 Q) bs (Z_to_bv 64 x)).
Lemma to_S10 :
SR ubs2segs (mkCfg (mkst regs5 (Z_to_bv 64 RA_MALLOC) mem5 (seg_rom ubs2segs)) md5)
(fun c => exists regs9 mem8 bs ms10, c = mkCfg ms10 md5 /\ K10 regs9 mem8 bs ms10).
Proof.
destruct Hmd5 as (Hh5 & Hlz5 & Hmat5). pose proof PREf as (Hret & Hal & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val as HCV.
pose proof Pblk as (P1 & P0 & P2 & _). pose proof Qblk as (Q1 & Q2 & Q3 & Q4). pose proof Hn as Hn'. unfold PGSZ in Hn'.
assert (XR6 : forall k, 0 <= xvj regs5 NOLD Q k < 2 ^ 64) by exact (XRq regs5).
assert (EA6 : env_agree 64 E E6) by exact (EAq regs5).
eapply SR_bind; [exact (S8_run E6 _ md5 Hh5 Hlz5 st_ok6q)|]. intros c8 (ms8 & -> & HS8 & HF8). cbn [ms_mem] in HF8.
destruct S8_shape as (Hpc8 & Hrv8 & Hv8 & Hsm8). pose proof (st_ok_regs_ok ubs2segs E6 _ _ HS8) as R8.
unfold view in Hv8. cbn [map] in Hv8.
vnth Hv8 0%nat V1. vnth Hv8 6%nat V10. vnth Hv8 7%nat V11. vnth Hv8 8%nat V12.
assert (BSP8 : base_val E6 (Some aSP) = SP) by (cbn [base_val]; rewrite (proj1 EA6 aSP ltac:(unfold aSP; lia)); exact base_SP).
assert (RAW8 : forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ms_mem ms8 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x)).
{ intros x Hx N1. apply HF8. rewrite lit64_small by lia. intros W. apply wr_after in W. rewrite BSP8 in W. exact (N1 W). }
assert (H10 : getr (ms_regs ms8) 10 = Z_to_bv 64 Q) by (rewrite (R8 10%bv), V10, (den_off0 _ XR6); reflexivity).
assert (H11 : getr (ms_regs ms8) 11 = Z_to_bv 64 P).
{ rewrite (R8 11%bv), V11, (sv_denot_agree 64 E E6 _ EA6) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity. }
assert (H12 : getr (ms_regs ms8) 12 = Z_to_bv 64 NOLD) by (rewrite (R8 12%bv), V12, (den_off0 _ XR6); reflexivity).
assert (PR8 : forall i, 0 <= i < NOLD -> present (ms_mem ms8) (P + i)).
{ intros i Hi. apply (present_same mem5); [apply RAW8; [lia | unfold STK; intro; lia] | exact (proj1 (Pblk5 i Hi))]. }
assert (PQ8 : forall i, 0 <= i < NOLD -> present (ms_mem ms8) (Q + i)).
{ intros i Hi. apply (present_same mem5); [apply RAW8; [lia | unfold STK; intro; lia] | exact (proj1 (Q4 i ltac:(lia)))]. }
destruct (rdn_of_present (ms_mem ms8) (Z.to_nat NOLD) P ltac:(intros i Hi; apply PR8; lia) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present (ms_mem ms8) (Z.to_nat NOLD) Q ltac:(intros i Hi; apply PQ8; lia) ltac:(lia) ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (MEMCPY bs (Z_to_bv 64 Q) (Z_to_bv 64 P) (Z_to_bv 64 NOLD) (ms_mem ms8) (seg_rom ubs2segs) (ms_regs ms8) H10 H11 H12)
as (regs9 & MS & Ha0 & Hfr9).
{ rewrite lit64_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite lit64_small by lia. lia. }
{ rewrite lit64_small by lia. lia. }
{ rewrite !lit64_small by lia. pose proof PQ_disjoint. lia. }
rewrite (st_ok_mkst ubs2segs E6 _ _ HS8 Hrv8), Hpc8.
eapply SR_msteps; [exact Hh5 | exact Hlz5 | exact MS |].
replace (v_jalr (getr (ms_regs ms8) 1) 0) with (Z_to_bv 64 RA_MEMCPY).
2:{ rewrite (R8 1%bv), V1. apply bv_eq. vm_compute. reflexivity. }
set (mem9 := wbytes (ms_mem ms8) (Z_to_bv 64 Q) bs).
set (E9 := EV (xvj regs9 NOLD Q)). pose proof (XRq regs9) as XR9. pose proof (EAq regs9) as EA9.
assert (Q9 : forall x, 0 <= x < 2 ^ 64 -> ~ (Q <= x < Q + NOLD) -> mem9 (Z_to_bv 64 x) = ms_mem ms8 (Z_to_bv 64 x)).
{ intros x Hx NQ. subst mem9. destruct (Z_lt_le_dec x Q).
- apply wbytes_below; rewrite ?Hlen, !lit64_small by lia; lia.
- apply wbytes_above. rewrite !lit64_small by lia. rewrite Hlen. lia. }
assert (HS9 : st_ok ubs2segs E9 S9 (mkst regs9 (Z_to_bv 64 RA_MEMCPY) mem9 (seg_rom ubs2segs))).
{ unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts S9 resv_denot].
repeat (split; [reflexivity|]). split; [| split].
-
pose proof S8_view2 as Hv2. unfold view in Hv2. cbn [map] in Hv2.
vnth Hv8 1%nat V2. vnth Hv8 2%nat V3. vnth Hv8 3%nat V4. vnth Hv8 4%nat V8. vnth Hv8 5%nat V9.
vnth Hv8 9%nat V23. vnth Hv8 10%nat V24. vnth Hv8 11%nat V25. vnth Hv8 12%nat V26. vnth Hv8 13%nat V27.
vnth Hv2 0%nat V19. vnth Hv2 1%nat V20. vnth Hv2 2%nat V21. vnth Hv2 3%nat V22.
assert (KEEP : forall i, In i [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr regs9 (nat_to_reg i) = getr (ms_regs ms8) (nat_to_reg i)).
{ intros i Hi0. cbn [In] in Hi0.
repeat (destruct Hi0 as [<-|Hi0]; [apply Hfr9; cbn [nat_to_reg]; intros HH; discriminate HH |]). destruct Hi0. }
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_after_memcpy]; unfold junk; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_off0 _ XR9), xvj_junk by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
all: rewrite KEEP by (cbn; tauto); cbn [nat_to_reg].
+ rewrite (R8 2%bv), V2, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 3%bv), V3, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 4%bv), V4, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 8%bv), V8, (den_off0 _ XR9), (den_off0 _ XR6). reflexivity.
+ rewrite (R8 9%bv), V9, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 19%bv), V19, (den_off0 _ XR9), (den_off0 _ XR6). reflexivity.
+ rewrite (R8 20%bv), V20. reflexivity.
+ rewrite (R8 21%bv), V21, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 22%bv), V22, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 23%bv), V23, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 24%bv), V24, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 25%bv), V25, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 26%bv), V26, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
+ rewrite (R8 27%bv), V27, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. apply (sv_denot_agree 64 E E6 _ EA6). reflexivity.
-
pose proof (st_ok_mem_ok ubs2segs E6 _ _ HS8) as MOK8. rewrite Hsm8 in MOK8.
apply (mem_ok_after_xfer E6 E9 (ms_mem ms8) mem9 (EAq32 regs5) (EAq32 regs9) MOK8).
+ intros x Hx. apply Q9; [lia | lia].
+ intros x Hx. apply (writable_at_grows ubs2segs (ms_mem ms8) mem9); [apply wbytes_grows|].
destruct MOK8 as (_ & ROK8 & _). apply Forall_inv in ROK8. destruct ROK8 as (_ & _ & W8 & _).
cbn [r_base r_wlo r_whi] in W8. rewrite BSP8 in W8. unfold STK in Hx. replace x with (SP + (x - SP)) by lia. apply W8. lia.
- apply facts_after; left; reflexivity. }
eapply SR_mono; [exact (S10_run E9 _ md5 Hh5 Hlz5 HS9)|].
intros c10 (ms10 & -> & HS10 & HF10). cbn [ms_mem] in HF10.
exists regs9, (ms_mem ms8), bs, ms10. split; [reflexivity|].
split; [exact HS10|]. split; [exact RAW8|]. split; [exact Hbs|]. split; [exact Hlen|].
intros x Hx N1. apply HF10. rewrite lit64_small by lia. intros W. apply wr_after in W.
subst E9. cbn [base_val] in W. rewrite (proj1 EA9 aSP ltac:(unfold aSP; lia)) in W. change (bv_unsigned (ew E aSP)) with (base_val E (Some aSP)) in W.
rewrite base_SP in W. exact (N1 W).
Qed.
Section w.
Variables (regs9 : bvmap 5 word) (mem8 : word -> option byte) (bs : list byte) (ms10 : machine_state).
Hypothesis HK : K10 regs9 mem8 bs ms10.
Let E9 := EV (xvj regs9 NOLD Q).
Let regs10 := ms_regs ms10.
Let mem10 := ms_mem ms10.
Let mem9 := wbytes mem8 (Z_to_bv 64 Q) bs.
Lemma HS10 : st_ok ubs2segs E9 S10 ms10. Proof. exact (proj1 HK). Qed.
Lemma RAW8 : forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> mem8 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x). Proof. exact (proj1 (proj2 HK)). Qed.
Lemma Hbs : rdn ubs2segs mem8 (Z_to_bv 64 P) (Z.to_nat NOLD) = Some bs. Proof. exact (proj1 (proj2 (proj2 HK))). Qed.
Lemma Hlen : length bs = Z.to_nat NOLD. Proof. exact (proj1 (proj2 (proj2 (proj2 HK)))). Qed.
Lemma RAW10 : forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> mem10 (Z_to_bv 64 x) = mem9 (Z_to_bv 64 x). Proof. exact (proj2 (proj2 (proj2 (proj2 HK)))). Qed.
Lemma Q9 : forall x, 0 <= x < 2 ^ 64 -> ~ (Q <= x < Q + NOLD) -> mem9 (Z_to_bv 64 x) = mem8 (Z_to_bv 64 x).
Proof.
pose proof Qblk as (Q1 & Q2 & _). pose proof Pblk as (P1 & P0 & P2 & _). pose proof Hn. pose proof YN05.alloc_ceiling_val. unfold PGSZ in *.
intros x Hx NQ. subst mem9. destruct (Z_lt_le_dec x Q).
- apply wbytes_below; rewrite ?Hlen, !lit64_small by lia; lia.
- apply wbytes_above. rewrite !lit64_small by lia. rewrite Hlen. lia.
Qed.
Lemma copy9 : forall i, 0 <= i < NOLD -> mbyte ubs2segs mem9 (Q + i) = mbyte ubs2segs mem8 (P + i).
Proof.
pose proof Qblk as (Q1 & Q2 & _). pose proof Pblk as (P1 & P0 & P2 & _). pose proof Hn. pose proof YN05.alloc_ceiling_val. unfold PGSZ in *.
intros i Hi. subst mem9. rewrite (wbytes_mbyte ubs2segs bs mem8 Q (Q + i)) by (rewrite ?Hlen; lia).
rewrite Hlen. replace ((Q <=? Q + i) && (Q + i <? Q + Z.of_nat (Z.to_nat NOLD))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
pose proof (proj2 (proj1 (rdn_mbytes ubs2segs mem8 (Z.to_nat NOLD) P bs) Hbs)) as Hb.
replace (Z.to_nat (Q + i - Q)) with (Z.to_nat i) by lia.
rewrite <- (Hb (Z.to_nat i)) by lia. replace (P + Z.of_nat (Z.to_nat i)) with (P + i) by lia. reflexivity.
Qed.
Lemma XR9 : forall k, 0 <= xvj regs9 NOLD Q k < 2 ^ 64. Proof. exact (XRq regs9). Qed.
Lemma EA9 : env_agree 64 E E9. Proof. exact (EAq regs9). Qed.
Lemma BSP9 : base_val E9 (Some aSP) = SP.
Proof. cbn [base_val]. rewrite (proj1 EA9 aSP ltac:(unfold aSP; lia)). exact base_SP. Qed.
Lemma S10_regs :
getr regs10 1 = Z_to_bv 64 RA_FREE /\ getr regs10 2 = Z_to_bv 64 (SP - 64) /\ getr regs10 3 = getr regs 3 /\
getr regs10 4 = getr regs 4 /\ getr regs10 8 = Z_to_bv 64 Q /\ getr regs10 9 = Z_to_bv 64 P /\ getr regs10 10 = Z_to_bv 64 P /\
getr regs10 19 = Z_to_bv 64 (16 * fr_off fr) /\ getr regs10 20 = Z_to_bv 64 4095 /\ getr regs10 21 = Z_to_bv 64 P /\ getr regs10 22 = Z_to_bv 64 n /\
(forall i, In i [23; 24; 25; 26; 27]%nat -> getr regs10 (nat_to_reg i) = getr regs (nat_to_reg i)).
Proof.
destruct S10_shape as (_ & _ & Hv & _). unfold view in Hv. cbn [map] in Hv.
vnth Hv 0%nat V1. vnth Hv 1%nat V2. vnth Hv 2%nat V3. vnth Hv 3%nat V4. vnth Hv 4%nat V8. vnth Hv 5%nat V9. vnth Hv 6%nat V10.
vnth Hv 7%nat V23. vnth Hv 8%nat V24. vnth Hv 9%nat V25. vnth Hv 10%nat V26. vnth Hv 11%nat V27.
pose proof S10_view2 as Hv2. unfold view in Hv2. cbn [map] in Hv2. vnth Hv2 0%nat V19. vnth Hv2 1%nat V20. vnth Hv2 2%nat V21. vnth Hv2 3%nat V22.
pose proof (st_ok_regs_ok ubs2segs E9 _ _ HS10) as R. change (regs_ok E9 (ss_regs S10) regs10) in R.
pose proof XP as XP. pose proof XN as XN. pose proof XR9 as XR9. pose proof EA9 as EA9.
pose proof PREf as (_ & _ & P3 & P4 & _). pose proof YN05.alloc_ceiling_val.
repeat match goal with |- _ /\ _ => split end.
- rewrite (R 1%bv), V1. reflexivity.
- rewrite (R 2%bv), V2. rewrite (den_off _ XR9); [reflexivity|]. change (xvj regs9 NOLD Q 2) with SP. lia.
- rewrite (R 3%bv), V3, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. exact (den_reg 3 ltac:(lia)).
- rewrite (R 4%bv), V4, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. exact (den_reg 4 ltac:(lia)).
- rewrite (R 8%bv), V8, (den_off0 _ XR9). reflexivity.
- rewrite (R 9%bv), V9, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- rewrite (R 10%bv), V10, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- rewrite (R 19%bv), V19, (den_off0 _ XR9). reflexivity.
- rewrite (R 20%bv), V20. reflexivity.
- rewrite (R 21%bv), V21, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- rewrite (R 22%bv), V22, (sv_denot_agree 64 E E9 _ EA9) by reflexivity. rewrite (den_off0 _ XR), XN. reflexivity.
- intros i Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [nat_to_reg];
[rewrite (R 23%bv), V23 | rewrite (R 24%bv), V24 | rewrite (R 25%bv), V25 | rewrite (R 26%bv), V26 | rewrite (R 27%bv), V27];
rewrite (sv_denot_agree 64 E E9 _ EA9) by reflexivity; apply den_reg; lia.
Qed.
Lemma S10_mem :
(forall x, STK x -> writable_at ubs2segs mem10 x) /\ Forall (chunk_ok ubs2segs E9 mem10 SP) frame_chunks.
Proof.
pose proof (st_ok_mem_ok ubs2segs E9 _ _ HS10) as (_ & ROK & _). change (ms_mem ms10) with mem10 in ROK.
destruct S10_shape as (_ & _ & _ & Hsm). rewrite Hsm in ROK. apply Forall_inv in ROK.
destruct ROK as (_ & _ & W & C). cbn [r_base r_wlo r_whi r_chunks] in W, C. rewrite BSP9 in W, C.
split; [| exact C]. intros x Hx. unfold STK in Hx. replace x with (SP + (x - SP)) by lia. apply W. lia.
Qed.
Lemma RAW105 : forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ~ (Q <= x < Q + NOLD) -> mem10 (Z_to_bv 64 x) = mem5 (Z_to_bv 64 x).
Proof. intros x Hx N1 N2. rewrite (RAW10 x Hx N1), (Q9 x Hx N2). apply RAW8; assumption. Qed.
Lemma pre10 : call_pre ubs2_msyms (MRx ubs2_msyms) L5 A5 regs10 mem10 md5.
Proof.
pose proof PREf as (Hret & Hal & Hceil & H63 & Hstk & Htp & Herrw). pose proof S10_regs as (R1 & R2 & R3 & R4 & _).
pose proof S10_mem as (W1 & _). pose proof POST_facts as (W5 & B5 & _). pose proof YN05.alloc_ceiling_val.
pose proof Qblk as (Q1 & Q2 & Q3 & Q4). pose proof Hn as Hn'. unfold PGSZ in Hn'.
assert (ESP : spZ regs10 = SP - 64) by (unfold spZ; rewrite R2; apply lit64_small; lia).
unfold call_pre. rewrite ESP. split.
{ apply (MRx_frame_gen L5 A5 mem5 mem10 md5 Q (Q + NOLD) MX5 Hceil).
- intros x Hx N1 N2 N3. apply RAW105; assumption.
- intros x Hx. cbn beta in Hx. destruct (Q4 (x - Q) ltac:(lia)) as [Pq Oq]. replace (Q + (x - Q)) with x in Pq, Oq by lia.
split; [exact Oq|]. intros _. apply (present_same mem9).
+ apply RAW10; [lia | unfold STK; intro; lia].
+ subst mem9. destruct (present_same mem5 mem8 x (RAW8 x ltac:(lia) ltac:(unfold STK; intro; lia)) Pq) as [b Hb].
unfold present. destruct (wbytes mem8 (Z_to_bv 64 Q) bs (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; reflexivity|].
exfalso. apply (wbytes_grows bs mem8 (Z_to_bv 64 Q) (Z_to_bv 64 x)); [rewrite Hb; discriminate | exact Eb]. }
split; [exact W5|]. split; [exact B5|]. split; [rewrite R1; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite <- Zminus_mod_idemp_l, Hal; reflexivity|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
split; [intros x Hx; apply W1; unfold STK, ALLOC_STACK in *; lia|].
split; [rewrite R4; exact Htp|]. split.
{ intros x Hx. pose proof (errno_img x ltac:(unfold ERRN; rewrite ERRNO2_val; exact Hx)) as Hi. unfold in_img1 in Hi.
apply (writable_same2 mem5 mem10); [apply RAW105; [lia | unfold STK; intro; lia |] |].
{ intros HQ. apply (anyblock_off_img L5 A5 mem5 md5 q n x M5 q_in5); [unfold Q in HQ; lia | unfold in_img1; lia]. }
apply errno_writable5. unfold ERRN. rewrite ERRNO2_val. exact Hx. }
intros Hf. rewrite (init_done_of_block A5 _ W5 q_in5) in Hf. discriminate.
Qed.
Lemma free_call :
mreal ubs2segs (mkCfg ms10 md5) (free (Some (pp am fr)) A5)
(fun r c => free_leaf ubs2_msyms (MRx ubs2_msyms) L5 A5 regs10 mem10 md5 (pp am fr) NOLD r c /\
(length (st_regions A5) <= length (st_regions (snd r)))%nat).
Proof.
destruct S10_shape as (Hpc & Hrv & _). pose proof S10_regs as (_ & _ & _ & _ & _ & _ & R10 & _).
rewrite (st_ok_mkst ubs2segs E9 _ _ HS10 Hrv), Hpc.
apply mreal_tall; [| apply free_regions_tall].
apply FREE; [exact pre10 | exact p_in5 | rewrite R10, P5; reflexivity].
Qed.
Section y.
Variables (L11 : layout) (A11 : astate) (regs11 : bvmap 5 word) (mem11 : word -> option byte) (md11 : Model).
Variables (k1 k2 : list (sptr * Z)).
Hypothesis POSTF : call_post ubs2_msyms (MRx ubs2_msyms) L5 A5 regs10 mem10 md5 (fun x => ptr_addr L5 (pp am fr) <= x < ptr_addr L5 (pp am fr) + NOLD) L11 A11 regs11 mem11 md11.
Hypothesis UB5' : user_blocks A5 = k1 ++ (pp am fr, NOLD) :: k2.
Hypothesis UB11 : user_blocks A11 = k1 ++ k2.
Hypothesis LEN11 : (length (st_regions A5) <= length (st_regions A11))%nat.
Let MX11 : MRx ubs2_msyms L11 A11 mem11 md11 := proj1 POSTF.
Lemma M11 : MRc ubs2_msyms L11 A11 mem11 md11. Proof. exact (MRx_MRc _ _ _ _ _ MX11). Qed.
Lemma Hmd11 : m_halted md11 = None /\ m_vm_lazy md11 = [] /\ m_vm_materialized md11 = [].
Proof. exact (mc_md _ _ _ _ _ M11). Qed.
Lemma POSTF_facts :
WF A11 /\ bounded A11 /\ layout_le A5 L5 L11 /\
(forall b k, In (b, k) (user_blocks A5) -> In (b, k) (user_blocks A11) -> ptr_addr L11 b = ptr_addr L5 b) /\
regs_preserved regs10 regs11 /\ (exists vm', md11 = with_vmmaps vm' md5) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img ubs2_msyms x) ->
~ owned ubs2_msyms L5 A5 x -> ~ owned ubs2_msyms L11 A11 x -> ~ scratch ubs2_msyms regs10 x -> ~ (P <= x < P + NOLD) ->
mbyte ubs2segs mem11 x = mbyte ubs2segs mem10 x /\ (writable_at ubs2segs mem10 x <-> writable_at ubs2segs mem11 x)) /\
(forall b k i, In (b, k) (user_blocks A5) -> In (b, k) (user_blocks A11) -> 0 <= i < k ->
mbyte ubs2segs mem11 (ptr_addr L5 b + i) = mbyte ubs2segs mem10 (ptr_addr L5 b + i)) /\
(forall x, scratch ubs2_msyms regs10 x -> writable_at ubs2segs mem11 x).
Proof.
pose proof POSTF as (_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). rewrite P5 in H7.
repeat (split; [assumption|]). exact H9.
Qed.
Lemma scratch10 x : scratch ubs2_msyms regs10 x <-> (SP - 8256 <= x < SP - 64) \/ ERRN x.
Proof.
pose proof S10_regs as (_ & R2 & _). pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val.
unfold scratch, spZ. rewrite R2, lit64_small by lia. unfold ALLOC_STACK, ERRN. rewrite ERRNO2_val.
change (errno_addr ubs2_msyms) with (ubs2_tp + -164). lia.
Qed.
Lemma q_cases :
(exists u, k1 = l1 ++ (q, n) :: u /\ l2 = u ++ (pp am fr, NOLD) :: k2) \/
(exists u, l1 = k1 ++ (pp am fr, NOLD) :: u /\ k2 = u ++ (q, n) :: l2).
Proof.
apply app_mid_cases; [rewrite <- UB5, <- UB5'; reflexivity|].
intros E0. injection E0 as _ En. pose proof Hn. unfold PGSZ in *. lia.
Qed.
Lemma q_in11 : In (q, n) (user_blocks A11).
Proof.
rewrite UB11. destruct q_cases as [(u & -> & _) | (u & _ & ->)]; apply in_or_app.
- left. apply in_or_app. right. left. reflexivity.
- right. apply in_or_app. right. left. reflexivity.
Qed.
Lemma blocks11 : exists a1 a2 m1 m2, user_blocks A = a1 ++ (pp am fr, NOLD) :: a2 /\ m1 ++ m2 = a1 ++ a2 /\ user_blocks A11 = m1 ++ (q, n) :: m2.
Proof.
rewrite UBA, UB11. destruct q_cases as [(u & -> & ->) | (u & -> & ->)].
- exists (l1 ++ u), k2, l1, (u ++ k2). rewrite <- !app_assoc. cbn. repeat split; reflexivity.
- exists k1, (u ++ l2), (k1 ++ u), l2. rewrite <- !app_assoc. cbn. repeat split; reflexivity.
Qed.
Lemma A_sub_A5 b k : In (b, k) (user_blocks A) -> In (b, k) (user_blocks A5).
Proof. rewrite UBA, UB5. intros H. apply in_app_iff in H. apply in_or_app. destruct H; [left | right; right]; assumption. Qed.
Lemma owned_img_any L0 A0 m0 md0 L' A' m' md' x :
MRc ubs2_msyms L0 A0 m0 md0 -> MRc ubs2_msyms L' A' m' md' -> in_img ubs2_msyms x ->
owned ubs2_msyms L' A' x -> owned ubs2_msyms L0 A0 x.
Proof.
intros M0 M' Hi [[(e & He & Hxe) Hnb] | Hs]; [| right; exact Hs]. left.
destruct (In_footprint_inv A' e He) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hxe.
- split.
+ exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. rewrite (mc_ctx _ _ _ _ _ M0). rewrite (mc_ctx _ _ _ _ _ M') in Hxe. exact Hxe.
+ intros (b & Hb & Hxb). destruct b as [bp bk]. cbn [fst snd] in Hxb. unfold loc_addr in Hxb.
apply (anyblock_off_img L0 A0 m0 md0 bp bk x M0 Hb); [unfold ptr_addr, loc_addr; exact Hxb | apply ubs2_img_range; exact Hi].
- exfalso. destruct (inv_areas (mc_wf _ _ _ _ _ M')) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg0 & -> & _ & Ho & Hr & Hl & Hlen0 & _). cbn [loc_addr] in Hxe.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M') r rg0 Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold PGSZ in *; lia | exact Hi].
- exfalso. destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M') k r Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [lia | exact Hi].
Qed.
Let E11 := EV (xvj regs11 NOLD Q).
Lemma XR11 : forall k, 0 <= xvj regs11 NOLD Q k < 2 ^ 64. Proof. exact (XRq regs11). Qed.
Lemma EA11 : env_agree 64 E E11. Proof. exact (EAq regs11). Qed.
Lemma BSP11 : base_val E11 (Some aSP) = SP.
Proof. cbn [base_val]. rewrite (proj1 EA11 aSP ltac:(unfold aSP; lia)). exact base_SP. Qed.
Lemma CS11 j : In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr regs11 (nat_to_reg j) = getr regs10 (nat_to_reg j).
Proof.
intros Hj. destruct POSTF_facts as (_ & _ & _ & _ & PRES & _).
assert (H : (1 <= j <= 31)%nat /\ callee_saved (Z.of_nat j)).
{ unfold callee_saved. cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [split; [lia|lia] |]). destruct Hj. }
destruct H as [H1 H2]. rewrite <- (lit5 j) by lia. apply PRES. exact H2.
Qed.
Lemma frame_kept11 x : SP - 64 <= x < SP ->
mbyte ubs2segs mem11 x = mbyte ubs2segs mem10 x /\ (writable_at ubs2segs mem10 x <-> writable_at ubs2segs mem11 x).
Proof.
intros Hx. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val. pose proof Pblk as (P1 & P0 & P2 & _).
destruct POSTF_facts as (_ & _ & _ & _ & _ & _ & FR & _). apply FR.
- left. lia.
- intros Ho. pose proof (owned_low _ L5 A5 mem5 md5 x M5 Ho). lia.
- intros Ho. pose proof (owned_low _ L11 A11 mem11 md11 x M11 Ho). lia.
- intros Hs. apply scratch10 in Hs. unfold ERRN in Hs. rewrite ERRNO2_val in Hs. unfold ubs2_tp in Hs. lia.
- lia.
Qed.
Lemma stk_writable11 x : STK x -> writable_at ubs2segs mem11 x.
Proof.
intros Hx. destruct (Z_lt_le_dec x (SP - 64)).
- apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 POSTF_facts)))))))). apply scratch10. left. unfold STK in Hx. lia.
- apply (proj1 (proj2 (frame_kept11 x ltac:(unfold STK in Hx; lia)))). apply (proj1 S10_mem). exact Hx.
Qed.
Ltac oncs11 i R := rewrite (CS11 i) by (cbn; tauto); cbn [nat_to_reg]; rewrite R.
Lemma regs_ok11 : regs_ok E11 regs_after_free regs11.
Proof.
pose proof S10_regs as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R19 & R20 & R21 & R22 & R23).
pose proof XR11 as XR'. pose proof EA11 as EA'. pose proof Pblk as (P1 & P0 & P2 & _). pose proof YN05.alloc_ceiling_val as HCV.
pose proof PREf as (_ & _ & Hceil & H63 & _).
apply regs_ok_intro; [reflexivity|]. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [nth regs_after_free]; unfold junk; [lia | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | lia].
all: try (rewrite (den_off0 _ XR'), xvj_junk by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
- oncs11 2%nat R2. rewrite (den_off _ XR'); [reflexivity|]. change (xvj regs11 NOLD Q aSP) with SP. lia.
- oncs11 3%nat R3. rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 3 ltac:(lia)).
- oncs11 4%nat R4. rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 4 ltac:(lia)).
- oncs11 8%nat R8. rewrite (den_off0 _ XR'). reflexivity.
- oncs11 9%nat R9. rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- oncs11 19%nat R19. rewrite (den_off0 _ XR'). reflexivity.
- oncs11 20%nat R20. reflexivity.
- oncs11 21%nat R21. rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. rewrite (den_off0 _ XR), XP. reflexivity.
- oncs11 22%nat R22. rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. rewrite (den_off0 _ XR), XN. reflexivity.
- rewrite (CS11 23%nat) by (cbn; tauto). rewrite (R23 23%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 23 ltac:(lia)).
- rewrite (CS11 24%nat) by (cbn; tauto). rewrite (R23 24%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 24 ltac:(lia)).
- rewrite (CS11 25%nat) by (cbn; tauto). rewrite (R23 25%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 25 ltac:(lia)).
- rewrite (CS11 26%nat) by (cbn; tauto). rewrite (R23 26%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 26 ltac:(lia)).
- rewrite (CS11 27%nat) by (cbn; tauto). rewrite (R23 27%nat) by (cbn; tauto). rewrite (sv_denot_agree 64 E E11 _ EA') by reflexivity. symmetry. exact (den_reg 27 ltac:(lia)).
Qed.
Lemma st_ok11 : st_ok ubs2segs E11 S11 (mkst regs11 (Z_to_bv 64 RA_FREE) mem11 (seg_rom ubs2segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts S11 resv_denot].
repeat (split; [reflexivity|]). split; [exact regs_ok11|]. split.
- pose proof (st_ok_mem_ok ubs2segs E9 _ _ HS10) as MOK10. destruct S10_shape as (_ & _ & _ & Hsm). rewrite Hsm in MOK10.
apply (mem_ok_after_xfer E9 E11 mem10 mem11 (EAq32 regs9) (EAq32 regs11) MOK10).
+ intros x Hx. pose proof PREf as (_ & _ & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val.
rewrite <- (mbyte_off_img2 mem11 x), <- (mbyte_off_img2 mem10 x) by (unfold in_img1; first [lia | intro; lia]).
apply (proj1 (frame_kept11 x Hx)).
+ apply stk_writable11.
- apply facts_after; left; reflexivity.
Qed.
Lemma leaf_some :
SR ubs2segs (mkCfg (mkst regs11 (Z_to_bv 64 RA_FREE) mem11 (seg_rom ubs2segs)) md11)
(realloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs mem md (pp am fr) (fr_n fr) n (Some q, A11)).
Proof.
destruct Hmd11 as (Hh11 & Hlz11 & Hmat11). pose proof PREf as (Hret & Hal & Hceil & H63 & _). pose proof YN05.alloc_ceiling_val as HCV.
pose proof EA11 as EA'. pose proof XR11 as XR'. pose proof Pblk as (P1 & P0 & P2 & _). pose proof Qblk as (Q1 & Q2 & Q3 & Q4).
pose proof Hn as Hn'. unfold PGSZ in Hn'.
eapply SR_bind; [exact (S12_run E11 _ md11 Hh11 Hlz11 st_ok11)|]. intros c12 (ms12 & -> & HS12 & HF12). cbn [ms_mem] in HF12.
destruct S12_shape as (Hpc12 & Hrv12 & Hview12 & Ha012 & Hsm12).
pose proof (st_ok_regs_ok ubs2segs E11 _ _ HS12) as R12.
unfold callee_view, callee_view0, view in Hview12. cbn [map] in Hview12.
vnth Hview12 0%nat V1. vnth Hview12 1%nat V2. vnth Hview12 2%nat V3. vnth Hview12 3%nat V4. vnth Hview12 4%nat V8. vnth Hview12 5%nat V9.
vnth Hview12 6%nat V18. vnth Hview12 7%nat V19. vnth Hview12 8%nat V20. vnth Hview12 9%nat V21. vnth Hview12 10%nat V22. vnth Hview12 11%nat V23.
vnth Hview12 12%nat V24. vnth Hview12 13%nat V25. vnth Hview12 14%nat V26. vnth Hview12 15%nat V27.
assert (CV : forall i, In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
getr (ms_regs ms12) (nat_to_reg i) = getr regs (nat_to_reg i)).
{ intros i Hi0. rewrite <- (den_reg i) by (cbn in Hi0; lia). rewrite <- (sv_denot_agree 64 E E11 _ EA') by (cbn in Hi0; destruct Hi0 as [<-|Hi0]; [reflexivity|]; repeat (destruct Hi0 as [<-|Hi0]; [reflexivity|]); destruct Hi0).
rewrite (R12 (nat_to_reg i)). f_equal. cbn in Hi0.
repeat (destruct Hi0 as [<-|Hi0]; [cbn [nat_to_reg]; assumption|]). destruct Hi0. }
assert (E1 : ew E11 1 = getr regs 1) by (rewrite (proj1 EA' 1%nat ltac:(lia)); exact (E_reg 1 ltac:(lia))).
assert (RAW12 : forall x, 0 <= x < 2 ^ 64 -> ~ STK x -> ms_mem ms12 (Z_to_bv 64 x) = mem11 (Z_to_bv 64 x)).
{ intros x Hx N1. apply HF12. rewrite lit64_small by lia. intros W. apply wr_after in W. rewrite BSP11 in W. exact (N1 W). }
eapply (SR_realloc_ret E11 S12 ms12 md11 _ HS12 Hrv12 Hpc12 V1); [rewrite E1; exact Hret | exact Hh11 | exact Hlz11 |].
destruct POST_facts as (W5 & B5 & LE5 & AD5 & PRES5 & VM5 & FR5 & BL5 & SC5).
destruct POSTF_facts as (W11 & B11 & LE11 & AD11 & PRES11 & VM11 & FR11 & BL11 & SC11).
assert (AQ : ptr_addr L11 q = Q) by (unfold Q; apply (AD11 q n); [exact q_in5 | exact q_in11]).
unfold realloc_leaf. exists L11, (ms_regs ms12), (ms_mem ms12), md11. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [| split; [| split; [| split; [exact blocks11 |]]]].
2:{ rewrite (R12 10%bv), Ha012, (den_off0 _ XR'), AQ. reflexivity. }
2:{ rewrite AQ. lia. }
2:{   intros i Hi. rewrite AQ. change (ms_segs ubs2_msyms) with ubs2segs.
assert (Hi' : 0 <= i < NOLD) by (unfold NOLD in *; lia).
assert (NSq : ~ STK (Q + i)) by (unfold STK; intro; lia).
assert (NSp : ~ STK (P + i)) by (unfold STK; intro; lia).
change (ptr_addr L (pp am fr)) with P.
rewrite (proj1 (same_byte_views2 mem11 (ms_mem ms12) _ (RAW12 (Q + i) ltac:(lia) NSq))).
pose proof (BL11 q n i q_in5 q_in11 ltac:(lia)) as E11q. change (ptr_addr L5 q) with Q in E11q. rewrite E11q.
rewrite (proj1 (same_byte_views2 mem9 mem10 _ (RAW10 (Q + i) ltac:(lia) NSq))).
rewrite (copy9 i Hi').
rewrite (proj1 (same_byte_views2 mem5 mem8 _ (RAW8 (P + i) ltac:(lia) NSp))).
pose proof (BL5 (pp am fr) NOLD i Hin p_in5 Hi') as E5p. change (ptr_addr L (pp am fr)) with P in E5p. rewrite E5p.
apply (proj1 (same_byte_views2 mem mem4 _ (RAW4 (P + i) ltac:(lia) NSp ltac:(intros He; exact (anyblock_off_img L A mem md (pp am fr) NOLD (P + i) M Hin ltac:(unfold P; lia) (errno_img _ He)))))). }
pose proof (st_ok_mem_ok ubs2segs E11 _ _ HS12) as (_ & ROK12 & _). rewrite Hsm12 in ROK12. apply Forall_inv in ROK12.
destruct ROK12 as (_ & _ & W12 & _). cbn [r_base r_wlo r_whi] in W12. rewrite BSP11 in W12.
unfold call_post_k. change (ms_segs ubs2_msyms) with ubs2segs.
split; [| split; [exact W11 | split; [exact B11 | split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
-   apply (MRx_scratch L11 A11 mem11 (ms_mem ms12) md11 MX11 Hceil). intros x Hx N1 _. exact (RAW12 x Hx N1).
-   destruct LE5 as (C1 & C2 & C3 & C4). destruct LE11 as (D1 & D2 & D3 & D4).
split; [congruence|]. split; [congruence|]. split; [congruence|]. intros r Hr. rewrite D4 by lia. apply C4. exact Hr.
-   intros b k Hb HbF. rewrite (AD11 b k (A_sub_A5 b k Hb) HbF). apply (AD5 b k); [exact Hb | exact (A_sub_A5 b k Hb)].
-   intros r Hr. destruct (callee_saved_cases r Hr) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r Rr). apply CV. cbn. cbn in RI. tauto.
-   destruct VM5 as [v1 ->]. destruct VM11 as [v2 ->]. exists v2. apply with_vmmaps_twice.
-   intros x Hx N1 N2 N3 N4.
assert (Hx64 : 0 <= x < 2 ^ 64) by (destruct Hx as [Hx|Hx]; [lia | apply ubs2_img_range in Hx; unfold in_img1 in Hx; lia]).
assert (NS : ~ STK x /\ ~ ERRN x).
{ unfold scratch_k, REALLOC_STACK, ALLOC_STACK in N3. unfold STK, ERRN. rewrite ERRNO2_val. change (errno_addr ubs2_msyms) with (ubs2_tp + -164) in N3. change (spZ regs) with SP in N3. split; intro; apply N3; lia. }
destruct NS as [NS1 NS2].
assert (N5 : ~ owned ubs2_msyms L5 A5 x).
{ destruct Hx as [Hx|Hx]; [intros Ho; pose proof (owned_low _ L5 A5 mem5 md5 x M5 Ho); lia|].
intros Ho. exact (N1 (owned_img_any L A mem md L5 A5 mem5 md5 x M M5 Hx Ho)). }
assert (NQ : ~ (Q <= x < Q + NOLD)).
{ destruct Hx as [Hx|Hx]; [lia|]. intros HQ. exact (anyblock_off_img L5 A5 mem5 md5 q n x M5 q_in5 ltac:(unfold Q in HQ; lia) (ubs2_img_range _ Hx)). }
destruct (same_byte_views2 mem11 (ms_mem ms12) x (RAW12 x Hx64 NS1)) as [A1 A2].
destruct (FR11 x Hx N5 N2 ltac:(intros Hs; apply scratch10 in Hs; destruct Hs as [Hs|Hs]; [unfold STK in NS1; lia | exact (NS2 Hs)]) ltac:(unfold P, NOLD; intro; apply N4; lia)) as [B1 B2].
destruct (same_byte_views2 mem5 mem10 x (RAW105 x Hx64 NS1 NQ)) as [C1 C2].
destruct (FR5 x Hx N1 N5 ltac:(intros Hs; apply scratch4 in Hs; destruct Hs as [Hs|Hs]; [unfold STK in NS1; lia | exact (NS2 Hs)])) as [D1 D2].
destruct (same_byte_views2 mem mem4 x (RAW4 x Hx64 NS1 NS2)) as [F1 F2].
rewrite A1, B1, C1, D1, F1. tauto.
-   intros b k i Hb HbF Hi.
pose proof (A_sub_A5 b k Hb) as Hb5.
pose proof (mr_blocks_range _ _ (MRx_laws ubs2_msyms) L A mem md b k MX Hb) as [Lo Hi2].
assert (Hx64 : 0 <= ptr_addr L b + i < 2 ^ 64) by lia.
assert (NS1 : ~ STK (ptr_addr L b + i)) by (unfold STK; intro; lia).
assert (NS2 : ~ ERRN (ptr_addr L b + i)) by (intros He; exact (anyblock_off_img L A mem md b k (ptr_addr L b + i) M Hb ltac:(lia) (errno_img _ He))).
assert (Eb5 : ptr_addr L5 b = ptr_addr L b) by (apply (AD5 b k); assumption).
assert (NQ : ~ (Q <= ptr_addr L b + i < Q + NOLD)).
{ pose proof (mr_blocks_disjoint _ _ (MRx_laws ubs2_msyms) L5 A5 mem5 md5 MX5) as PW. unfold blocks in PW. rewrite UB5 in PW.
pose proof Hb as Hb'. rewrite UBA in Hb'.
change (l1 ++ (q, n) :: l2) with (l1 ++ [(q, n)] ++ l2) in PW.
destruct (pairwise_app_mid ranges_disjoint (fun b0 : sptr * Z => (ptr_addr L5 (fst b0), snd b0)) l1 [(q, n)] l2 (q, n) (b, k) PW ltac:(left; reflexivity) Hb') as [D|D];
unfold ranges_disjoint in D; cbn [fst snd] in D; rewrite Eb5 in D; unfold Q; lia. }
rewrite (proj1 (same_byte_views2 mem11 (ms_mem ms12) _ (RAW12 _ Hx64 NS1))).
rewrite <- Eb5. rewrite (BL11 b k i Hb5 HbF Hi). rewrite Eb5.
rewrite (proj1 (same_byte_views2 mem5 mem10 _ (RAW105 _ Hx64 NS1 NQ))).
rewrite (BL5 b k i Hb Hb5 Hi). apply (proj1 (same_byte_views2 mem mem4 _ (RAW4 _ Hx64 NS1 NS2))).
-   intros x Hs. unfold scratch_k, REALLOC_STACK, ALLOC_STACK in Hs.
change (errno_addr ubs2_msyms) with (ubs2_tp + -164) in Hs. change (spZ regs) with SP in Hs.
destruct Hs as [Hs|Hs].
+ replace x with (SP + (x - SP)) by lia. apply W12. lia.
+ apply (writable_same2 mem11 (ms_mem ms12) x); [apply RAW12; [unfold ubs2_tp in Hs; lia | unfold STK; unfold ubs2_tp in Hs; intro; lia] |].
apply SC11. apply scratch10. right. unfold ERRN. rewrite ERRNO2_val. lia.
Qed.
End y.
End w.
End v.
End s.
End m.
Theorem fb_main :
mreal ubs2segs
(mkCfg (mkst (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem2 (seg_rom ubs2segs)) md)
(realloc_move (pp am fr) n A)
(realloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs mem md (pp am fr) (fr_n fr) n).
Proof.
unfold realloc_move. eapply mreal_SR_pre; [exact to_S4|]. intros c4 (ms4 & -> & HS4 & RAW4).
eapply mreal_mbind; [exact (malloc_call ms4 HS4 RAW4)|].
intros q A5 c5 [HL LEN5]. cbn [snd] in LEN5.
destruct HL as (L5 & regs5 & mem5 & md5 & -> & POST & Hq). cbn [fst snd] in POST, Hq.
pose proof (S4_regs ms4 HS4) as (R1 & _). change (ms_segs ubs2_msyms) with ubs2segs in *. rewrite R1.
destruct q as [q|].
- destruct Hq as (A0 & NZ & (l1 & l2 & UB5 & UBA) & _).
eapply mreal_SR_pre; [eapply (to_S10 ms4); eassumption|].
intros c10 (regs9 & mem8 & bs & ms10 & -> & HK).
eapply mreal_mbind; [eapply (free_call ms4); eassumption|].
intros [] A11 c11 [HFL LEN11]. cbn [snd] in LEN11.
destruct HFL as (L11 & regs11 & mem11 & md11 & -> & POSTF & (k1 & k2 & UB5' & UB11)). cbn [fst snd] in POSTF, UB5', UB11.
edestruct (S10_regs ms4) as (F1 & _); try eassumption.
unfold ret. apply mreal_leaf. change (ms_segs ubs2_msyms) with ubs2segs in *. rewrite F1.
eapply (leaf_some ms4); eassumption.
- destruct Hq as [A0 UB]. unfold ret. apply mreal_leaf. eapply (leaf_none ms4); eassumption.
Qed.
End FB.
Theorem ubs2_realloc_fb : OBL_fb_T.
Proof.
intros MALLOC FREE MEMCPY L A regs mem md g am fr n a ka rg HC gd err regs2 mem2 AT2.
exact (fb_main MALLOC FREE MEMCPY L A regs mem md g am fr n a ka rg HC gd err regs2 mem2 AT2).
Qed.
End h.
