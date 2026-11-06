(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN03 YN02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW01 YW00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN2b YN25 YN26.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW03 YW04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN0b YN07 YN0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW0e YW06 YW07 YW0c YW0b YW09 YW0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma with_vmmaps_self' md : md = with_vmmaps (m_vmmaps md) md.
Proof. destruct md as [fd vm io fs proc lim tm sch sig]. destruct vm. reflexivity. Qed.
Lemma src0_scratch_hi regs x :
alloc_ceiling + REALLOC_STACK <= spZ regs ->
scratch_k src0_msyms REALLOC_STACK regs x ->
alloc_ceiling <= x \/ (in_img src0_msyms x /\ ~ static_owned src0_msyms x /\ ~ (ms_ctx src0_msyms <= x < ms_ctx src0_msyms + CTX_SIZE)).
Proof.
intros Hsp [Hs|He]; [left; lia|]. right. change (errno_addr src0_msyms) with ERRNO2 in He.
split; [exact (src0_errno_img x He)|]. rewrite ERRNO2_val in He.
unfold static_owned. cbn. unfold src0_tp, src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard,
src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_malloc_context, CTX_SIZE in *. lia.
Qed.
Lemma SCR_scratch regs x : SCR regs x <-> scratch_k src0_msyms REALLOC_STACK regs x.
Proof.
unfold SCR, STK, ERRN, YW0f.SP, scratch_k, REALLOC_STACK, ALLOC_STACK, ERRNO2.
change (8192 + 64) with 8256. tauto.
Qed.
Lemma S1_regs_lt r : regs_atoms_lt 106 (ss_regs (S1 r)) = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma entry_facts_lt r : facts_atoms_lt 106 (entry_facts r) = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma stk1_lt : region_atoms_lt 106 stk1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wf9_stk1 : regions_wf [reg_area; reg_ctx; reg_nl; stk1; reg_got; reg_guard; reg_errnoR; reg_metaR; reg_nhdr] = true.
Proof. vm_compute. reflexivity. Qed.
Section c.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Variables (gd err : Z).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Herr : 0 <= err < 2 ^ 32.
Variable ms1 : machine_state.
Local Notation rcr := (YW06.rcr am fr).
Local Notation VV := (YW06.vv L regs g am fr a rg).
Local Notation E := (Er L regs g am fr n a rg gd err).
Hypothesis HS1 : st_ok src0segs E (S1 rcr) ms1.
Hypothesis HF1 : frame_of E (entry_mem rcr) mem (ms_mem ms1).
Hypothesis Heq : old_len am = needed fr n.
Hypothesis Hth : MMAP_THRESHOLD <= n.
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let MX : MRx src0_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
Let XR : forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64 :=
xvr_rangeG L A regs mem md g am fr n a ka rg HC rcr FP gd err Hgd Herr.
Local Notation MEM := (YW0f.MEM L am).
Local Notation NEEDED := (YW0f.NEEDED fr n).
Local Notation OLDLEN := (YW0f.OLDLEN am).
Local Notation OFF := (YW0f.OFF fr).
Local Notation NOLD := (YW0f.NOLD fr).
Local Notation P := (YW0f.P L am fr).
Local Notation G := (YW0f.G L g).
Local Notation SP := (YW0f.SP regs).
Local Notation AREA := (YW0f.AREA L a).
Local Notation RSV' := (YW0f.RSV' fr n).
Local Notation RC' := (YW0f.RC' fr n).
Local Notation t := (YW0f.t fr n).
Local Notation NP := (YW0f.NP fr MEM).
Local Notation NEND := (YW0f.NEND fr n MEM).
Local Notation NPN := (YW0f.NPN fr n MEM).
Local Notation Et := (YW0f.Et L regs g am fr n a rg gd err MEM).
Lemma EQN : OLDLEN = NEEDED. Proof. exact Heq. Qed.
Lemma RET_facts : 4096 <= MEM /\ MEM + NEEDED <= alloc_ceiling /\ MEM mod 16 = 0 /\ RET_img fr n MEM /\ RET_area L fr n a MEM /\
NP = P /\ MEM mod 4096 = 0.
Proof.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
pose proof EQN as EQ. unfold RET_img, RET_area, NP.
split; [exact C9|]. split; [clear - C10 EQ; lia|]. split.
{ clear - C11 C9. apply Z.mod_divide in C11; [|lia]. destruct C11 as [q Hq]. rewrite Hq.
replace (q * 4096) with ((q * 256) * 16) by lia. apply Z_mod_mult. }
split; [clear - C25 EQ; lia|]. split; [clear - C23 EQ; lia|]. split; [clear - C8; lia | exact C11].
Qed.
Let RETlo : 4096 <= MEM := proj1 RET_facts.
Let REThi : MEM + NEEDED <= alloc_ceiling := proj1 (proj2 RET_facts).
Let RETal : MEM mod 16 = 0 := proj1 (proj2 (proj2 RET_facts)).
Let RETimg : RET_img fr n MEM := proj1 (proj2 (proj2 (proj2 RET_facts))).
Let RETarea : RET_area L fr n a MEM := proj1 (proj2 (proj2 (proj2 (proj2 RET_facts)))).
Let ENP : NP = P := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RET_facts))))).
Local Notation TL X := (X L A regs mem md g am fr n a ka rg HC gd err Hgd Herr MEM RETlo REThi RETal) (only parsing).
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)). Qed.
Lemma base_SP : base_val E (Some aSP) = SP.
Proof.
unfold Er. rewrite (base_val_EV _ XR). unfold xvr, aSP. cbn [Nat.ltb Nat.leb]. rewrite xvf_reg by lia. reflexivity.
Qed.
Lemma base_TP : base_val E (Some aTP) = src0_tp.
Proof.
unfold Er. rewrite (base_val_EV _ XR). unfold xvr, aTP. cbn [Nat.ltb Nat.leb]. exact (xvf4 L A regs mem md g am fr n a ka rg HC).
Qed.
Lemma kept1 x : 0 <= x < 2 ^ 64 -> ~ SCR regs x -> ms_mem ms1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros Hx Hs. apply HF1. rewrite lit64_small by exact Hx. intros W. apply wr_entry in W.
rewrite base_SP, base_TP in W. apply Hs. unfold SCR, STK, ERRN. rewrite ERRNO2_val. clear - W. lia.
Qed.
Lemma mem_ok_1 : mem_ok src0segs Et (ms_mem ms1) (tail_mem (S1 rcr) t).
Proof.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
clear C6 C11 C26. pose proof EQN as EQ. pose proof ENP as EP'.
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO).
pose proof HS1 as (_ & _ & _ & _ & _ & _ & _ & Fmem & _).
destruct (S1_shape rcr) as (_ & _ & _ & _ & Hsm). rewrite Hsm in Fmem. fold stk1 in Fmem.
destruct (kept_of_mem_ok E (ms_mem ms1) stk1 (r_mem rcr) Fmem) as [KEPT PD].
rewrite tail_mem_S1. apply (TL mem_ok_tail); [| | | exact RETimg | exact RETarea | reflexivity | reflexivity | reflexivity | exact stk1_lt | apply (TL wf_tail); exact wf9_stk1 | exact KEPT | exact PD].
-   intros i Hi. apply kept1; [clear - Hi C14 C15 C12; lia|].
unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold src0_tp. clear - Hi C12 C13 C14 C15 C16 C17 C18 C19 C24. lia.
-   intros i Hi. rewrite EP'. apply kept1; [clear - Hi C8 C9 C10 C7 C1 C2 C12; lia|].
unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold src0_tp. clear - Hi C1 C2 C7 C8 C9 C10 C12 C13 C25. lia.
-   intros x Hx. apply present_writable. apply (present_same mem).
+ apply kept1; [clear - Hx C9 C10 C12 EQ; lia|]. unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold src0_tp. clear - Hx C9 C10 C12 C13 C25 EQ. lia.
+ apply (old_present src0_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)).
rewrite NM, NO. clear - Hx EQ. lia.
Qed.
Lemma facts_ok_1 : facts_ok Et (facts_app (ss_facts (S1 rcr)) (t_atoms t) (condEQ :: t_conds t) (t_alias aMEM t)).
Proof.
pose proof HS1 as (_ & _ & _ & _ & _ & _ & _ & _ & Ffacts).
destruct (S1_shape rcr) as (_ & _ & _ & Hsf & _). rewrite Hsf in Ffacts |- *.
pose proof (TL vals) as (VRET & VNP & VNEND & VNPN & VMEM & VG & VP & VN & VB16 & VNEED & VSP & VTP & VOFF & VIDX & VAV & VFR & VBITS & VH3 & VAREA & VMP & V1).
apply (TL facts_ok_app).
- exact (facts_ok_agree 106 E Et _ (TL Et_agree) (entry_facts_lt rcr) Ffacts).
- exact (TL atoms_t).
- cbn [conds_ok]. split; [| exact (TL conds_t)].
unfold acond_ok, condEQ. cbn [ac_c ac_a ac_b]. rewrite branch_eq.
rewrite !(den_off0 _ (TL XRt)), !lit64_small by (apply (TL XRt)). rewrite VMP, VNEED, EQN. apply Z.eqb_refl.
- apply (TL alias_t). exact VMEM.
Qed.
Theorem st_ok_1 : st_ok src0segs Et (S1eq rcr t) ms1.
Proof.
pose proof HS1 as (F1 & F2 & F3 & F4 & F5 & F6 & Fregs & Fmem & Ffacts).
destruct (S1_shape rcr) as (_ & Hrv & _).
unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts S1eq].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [rewrite F4, Hrv; reflexivity|].
split; [exact F5|]. split; [exact F6|]. split; [| split; [exact mem_ok_1 | exact facts_ok_1]].
exact (regs_ok_agree 106 E Et _ _ (TL Et_agree) (S1_regs_lt rcr) Fregs).
Qed.
Lemma names_eqE :
YW04.ENDe L am = NEND /\ YW04.RSVe am fr n = RSV' /\ YW04.RCe am fr n = RC' /\
(forall x, YW04.TW L am fr n x <-> ((0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND)) /\
YW04.P L am fr = NP /\ NPN = P + n.
Proof.
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO). pose proof EQN as EQ. pose proof ENP as EP'.
assert (E1 : YW04.ENDe L am = NEND) by (unfold YW04.ENDe, NEND; rewrite NM, NO, EQ; reflexivity).
assert (E2 : YW04.RSVe am fr n = RSV') by (unfold YW04.RSVe, YW0f.RSV'; rewrite NO, NOF, EQ; reflexivity).
assert (E3 : NPN = P + n) by (unfold NPN; rewrite EP'; reflexivity).
split; [exact E1|]. split; [exact E2|]. split; [unfold YW04.RCe, YW0f.RC'; rewrite E2; reflexivity|].
split; [| split; [rewrite NP', EP'; reflexivity | exact E3]].
intros x. unfold YW04.TW. rewrite E1, E2, NP', E3. tauto.
Qed.
Lemma gctx : realloc_gctx src0_msyms L A mem md g am fr n.
Proof using Hth MX.
split; [exact MX | exact (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)
| exact (conj Hth (proj2 (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC))) | exact (rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.
Theorem eq_leaf :
SR src0segs (mkCfg ms1 md) (realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n (Some (pp am fr), A_eq A g am fr n)).
Proof using ENP HF1 HS1 Hth MX PRE RETal RETarea REThi RETimg RETlo XR.
destruct Hmd as (Hh & Hlz & Hmat). pose proof EQN as EQ. pose proof ENP as EP'.
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO).
pose proof names_eqE as (EEND & ERSV & ERC & ETW & ENP' & ENPN).
pose proof PRE as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & _).
pose proof (TL vals) as (VRET & VNP & VNEND & VNPN & VMEM & _).
eapply SR_bind; [exact (S3_run Et ms1 md Hh Hlz rcr t st_ok_1)|].
intros c3 (ms3 & -> & HS3 & HF3). cbn [ms_mem] in HF3. change (ss_mem (S1eq rcr t)) with (tail_mem (S1 rcr) t) in HF3. rewrite tail_mem_S1 in HF3.
destruct (S3_shape rcr t) as (Hpc3 & Hrv3 & Hcv3 & Ha03 & Hsm3).
pose proof (TL final_read aMEM stk1 (S3 rcr t) ms3 RETimg HS3 Hsm3 VMEM Hcv3 Ha03 eq_refl eq_refl eq_refl) as FR.
lazy zeta in FR. destruct FR as (B4 & B3 & B2 & G16 & G24 & G28 & G32 & BEND & BPN & B45 & WS & PRS & RP & A03 & E1).
assert (KEPT3 : forall x, 0 <= x < 2 ^ 64 -> ~ (P - 4 <= x < P) -> ~ (G + 16 <= x < G + 40) ->
~ ((0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND) -> ~ SCR regs x ->
ms_mem ms3 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx N1 N2 N3 N4. transitivity (ms_mem ms1 (Z_to_bv 64 x)); [| exact (kept1 x Hx N4)].
apply HF3. rewrite lit64_small by exact Hx. intros W.
apply (TL wr_tail stk1 x eq_refl eq_refl eq_refl) in W. rewrite EP' in W. unfold SCR in N4. clear - W N1 N2 N3 N4. tauto. }
assert (EM : eq_memspec src0_msyms L A mem g am fr n (ms_mem ms3) (SCR regs)).
{ rewrite EP' in B4, B3, B2, PRS.
split; rewrite ?NM, ?NO, ?NP', ?NG, ?NN, ?NOF, ?EEND, ?ERSV, ?ERC, <- ?ENPN.
- intros x Hx. apply (src0_scratch_hi regs x Hceil). apply SCR_scratch. exact Hx.
- exact B4. - exact B3. - exact B2. - exact G16. - exact G24. - exact G28. - rewrite EQ. exact G32. - exact BEND. - exact BPN. - exact B45.
- intros x Hx. apply PRS. rewrite ETW in Hx. exact Hx.
- intros x Hx N1 N2 N3 N4. apply KEPT3; [exact Hx | exact N1 | exact N2 | rewrite <- ETW; exact N3 | exact N4]. }
assert (EQI : YW04.OLDLEN am = YW04.NEEDED fr n) by (rewrite NO, NN; exact EQ).
destruct (realloc_eq_leaf src0_msyms L A mem md g am fr n (ms_mem ms3) (SCR regs) gctx EQI EM)
as (MX3 & WF3 & BND3 & FRM3 & BLK3 & [EPP Pnz] & CNT3 & UB3 & _).
rewrite NP' in EPP, Pnz, CNT3. rewrite NNO in CNT3, UB3. rewrite Ae_is in MX3, WF3, BND3, BLK3, UB3.
change (frame_ptr am 0 fr) with (pp am fr) in EPP, UB3.
pose proof Hcv3 as V1. unfold callee_view, callee_view0, view in V1. cbn [map] in V1.
apply (f_equal (fun l => List.nth 0 l (SLit 0))) in V1. cbn [List.nth] in V1. rewrite lit5 in V1 by lia. cbn [nat_to_reg] in V1.
eapply (SR_realloc_ret Et (S3 rcr t) ms3 md _ HS3 Hrv3 Hpc3 V1); [rewrite E1; exact Hret | exact Hh | exact Hlz |].
unfold realloc_leaf. exists L, (ms_regs ms3), (ms_mem ms3), md. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split.
-
unfold call_post_k. change (ms_segs src0_msyms) with src0segs.
split; [exact MX3|]. split; [exact WF3|]. split; [exact BND3|]. split; [apply layout_le_refl|].
split; [intros; reflexivity|]. split; [exact RP|]. split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
split; [| split; [exact BLK3|]].
+ intros x Hx _ _ N3 _. apply FRM3; [exact Hx|]. intros Hs. apply N3. apply SCR_scratch. exact Hs.
+ intros x Hs. apply WS. apply SCR_scratch in Hs. exact Hs.
-
split; [rewrite A03, EP'; reflexivity|]. split; [unfold YW0f.P in Pnz; exact Pnz|].
split; [exact UB3|].
intros i Hi. unfold YW0f.P in CNT3. apply CNT3. unfold YW0f.NOLD. exact Hi.
Qed.
End c.
Theorem src0_realloc_eq : OBL_eq_T.
Proof using.
intros L A regs mem md g am fr n a ka rg HC Hth gd err ms1 Hgd Herr HS1 HF1 Heq.
exact (eq_leaf L A regs mem md g am fr n a ka rg HC gd err Hgd Herr ms1 HS1 HF1 Heq Hth).
Qed.
End b.
