(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YK0v YQ0k YN06 YK0s YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0a YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0q YP0m YP0o YP10 YP0v
YP0n YP0r YP0u YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YQ01 YO2f
YO29 YO2a YO30 YO2z
UO0c UO08 UO0b UO16 UO0y UO0z
UO14 UO13 UO11 UO17.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma with_vmmaps_self' md : md = with_vmmaps (m_vmmaps md) md.
Proof. destruct md as [fd vm io fs proc lim tm sch sig]. destruct vm. reflexivity. Qed.
Lemma ubs2_scratch_hi regs x :
alloc_ceiling + REALLOC_STACK <= spZ regs ->
scratch_k ubs2_msyms REALLOC_STACK regs x ->
alloc_ceiling <= x \/ (in_img ubs2_msyms x /\ ~ static_owned ubs2_msyms x /\ ~ (ms_ctx ubs2_msyms <= x < ms_ctx ubs2_msyms + CTX_SIZE)).
Proof.
intros Hsp [Hs|He]; [left; lia|]. right. change (errno_addr ubs2_msyms) with ERRNO2 in He.
split; [exact (ubs2_errno_img x He)|]. rewrite ERRNO2_val in He.
unfold static_owned. cbn. unfold ubs2_tp, ubs2_D_malloc_lock, ubs2_D_libc, ubs2_D_got_stack_chk_guard, ubs2_D_stack_chk_guard,
ubs2_D_debruijn32, ubs2_D_size_classes, ubs2_D_small_cnt_tab, ubs2_D_med_cnt_tab, ubs2_D_malloc_context, CTX_SIZE in *. lia.
Qed.
Lemma SCR_scratch regs x : SCR regs x <-> scratch_k ubs2_msyms REALLOC_STACK regs x.
Proof.
unfold SCR, STK, ERRN, UO17.SP, scratch_k, REALLOC_STACK, ALLOC_STACK, ERRNO2.
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
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YP0j.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Variables (gd err : Z).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Herr : 0 <= err < 2 ^ 32.
Variable ms1 : machine_state.
Local Notation rcr := (UO0y.rcr am fr).
Local Notation VV := (UO0y.vv L regs g am fr a rg).
Local Notation E := (Er L regs g am fr n a rg gd err).
Hypothesis HS1 : st_ok ubs2segs E (S1 rcr) ms1.
Hypothesis HF1 : frame_of E (entry_mem rcr) mem (ms_mem ms1).
Hypothesis Heq : old_len am = needed fr n.
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let MX : MRx ubs2_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
Let XR : forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64 :=
xvr_rangeG L A regs mem md g am fr n a ka rg HC rcr FP gd err Hgd Herr.
Local Notation MEM := (UO17.MEM L am).
Local Notation NEEDED := (UO17.NEEDED fr n).
Local Notation OLDLEN := (UO17.OLDLEN am).
Local Notation OFF := (UO17.OFF fr).
Local Notation NOLD := (UO17.NOLD fr).
Local Notation P := (UO17.P L am fr).
Local Notation G := (UO17.G L g).
Local Notation SP := (UO17.SP regs).
Local Notation AREA := (UO17.AREA L a).
Local Notation RSV' := (UO17.RSV' fr n).
Local Notation RC' := (UO17.RC' fr n).
Local Notation t := (UO17.t fr n).
Local Notation NP := (UO17.NP fr MEM).
Local Notation NEND := (UO17.NEND fr n MEM).
Local Notation NPN := (UO17.NPN fr n MEM).
Local Notation Et := (UO17.Et L regs g am fr n a rg gd err MEM).
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
Lemma base_TP : base_val E (Some aTP) = ubs2_tp.
Proof.
unfold Er. rewrite (base_val_EV _ XR). unfold xvr, aTP. cbn [Nat.ltb Nat.leb]. exact (xvf4 L A regs mem md g am fr n a ka rg HC).
Qed.
Lemma kept1 x : 0 <= x < 2 ^ 64 -> ~ SCR regs x -> ms_mem ms1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros Hx Hs. apply HF1. rewrite lit64_small by exact Hx. intros W. apply wr_entry in W.
rewrite base_SP, base_TP in W. apply Hs. unfold SCR, STK, ERRN. rewrite ERRNO2_val. clear - W. lia.
Qed.
Lemma mem_ok_1 : mem_ok ubs2segs Et (ms_mem ms1) (tail_mem (S1 rcr) t).
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
unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hi C12 C13 C14 C15 C16 C17 C18 C19 C24. lia.
-   intros i Hi. rewrite EP'. apply kept1; [clear - Hi C8 C9 C10 C7 C1 C2 C12; lia|].
unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hi C1 C2 C7 C8 C9 C10 C12 C13 C25. lia.
-   intros x Hx. apply present_writable. apply (present_same mem).
+ apply kept1; [clear - Hx C9 C10 C12 EQ; lia|]. unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hx C9 C10 C12 C13 C25 EQ. lia.
+ apply (old_present ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)).
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
Theorem st_ok_1 : st_ok ubs2segs Et (S1eq rcr t) ms1.
Proof.
pose proof HS1 as (F1 & F2 & F3 & F4 & F5 & F6 & Fregs & Fmem & Ffacts).
destruct (S1_shape rcr) as (_ & Hrv & _).
unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts S1eq].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [rewrite F4, Hrv; reflexivity|].
split; [exact F5|]. split; [exact F6|]. split; [| split; [exact mem_ok_1 | exact facts_ok_1]].
exact (regs_ok_agree 106 E Et _ _ (TL Et_agree) (S1_regs_lt rcr) Fregs).
Qed.
Lemma names_eqE :
YO2z.ENDe L am = NEND /\ YO2z.RSVe am fr n = RSV' /\ YO2z.RCe am fr n = RC' /\
(forall x, YO2z.TW L am fr n x <-> ((0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND)) /\
YO2z.P L am fr = NP /\ NPN = P + n.
Proof.
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO). pose proof EQN as EQ. pose proof ENP as EP'.
assert (E1 : YO2z.ENDe L am = NEND) by (unfold YO2z.ENDe, NEND; rewrite NM, NO, EQ; reflexivity).
assert (E2 : YO2z.RSVe am fr n = RSV') by (unfold YO2z.RSVe, UO17.RSV'; rewrite NO, NOF, EQ; reflexivity).
assert (E3 : NPN = P + n) by (unfold NPN; rewrite EP'; reflexivity).
split; [exact E1|]. split; [exact E2|]. split; [unfold YO2z.RCe, UO17.RC'; rewrite E2; reflexivity|].
split; [| split; [rewrite NP', EP'; reflexivity | exact E3]].
intros x. unfold YO2z.TW. rewrite E1, E2, NP', E3. tauto.
Qed.
Lemma gctx : realloc_gctx ubs2_msyms L A mem md g am fr n.
Proof.
split; [exact MX | exact (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)
| exact (rc_big _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.
Theorem eq_leaf :
SR ubs2segs (mkCfg ms1 md) (realloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs mem md (pp am fr) (fr_n fr) n (Some (pp am fr), A_eq A g am fr n)).
Proof.
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
assert (EM : eq_memspec ubs2_msyms L A mem g am fr n (ms_mem ms3) (SCR regs)).
{ rewrite EP' in B4, B3, B2, PRS.
split; rewrite ?NM, ?NO, ?NP', ?NG, ?NN, ?NOF, ?EEND, ?ERSV, ?ERC, <- ?ENPN.
- intros x Hx. apply (ubs2_scratch_hi regs x Hceil). apply SCR_scratch. exact Hx.
- exact B4. - exact B3. - exact B2. - exact G16. - exact G24. - exact G28. - rewrite EQ. exact G32. - exact BEND. - exact BPN. - exact B45.
- intros x Hx. apply PRS. rewrite ETW in Hx. exact Hx.
- intros x Hx N1 N2 N3 N4. apply KEPT3; [exact Hx | exact N1 | exact N2 | rewrite <- ETW; exact N3 | exact N4]. }
assert (EQI : YO2z.OLDLEN am = YO2z.NEEDED fr n) by (rewrite NO, NN; exact EQ).
destruct (realloc_eq_leaf ubs2_msyms L A mem md g am fr n (ms_mem ms3) (SCR regs) gctx EQI EM)
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
unfold call_post_k. change (ms_segs ubs2_msyms) with ubs2segs.
split; [exact MX3|]. split; [exact WF3|]. split; [exact BND3|]. split; [apply layout_le_refl|].
split; [intros; reflexivity|]. split; [exact RP|]. split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
split; [| split; [exact BLK3|]].
+ intros x Hx _ _ N3 _. apply FRM3; [exact Hx|]. intros Hs. apply N3. apply SCR_scratch. exact Hs.
+ intros x Hs. apply WS. apply SCR_scratch in Hs. exact Hs.
-
split; [rewrite A03, EP'; reflexivity|]. split; [unfold UO17.P in Pnz; exact Pnz|].
split; [exact UB3|].
intros i Hi. unfold UO17.P in CNT3. apply CNT3. unfold UO17.NOLD.
pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC). clear - Hi H. unfold PGSZ in H. lia.
Qed.
End c.
Theorem ubs2_realloc_eq : OBL_eq_T.
Proof.
intros L A regs mem md g am fr n a ka rg HC gd err ms1 Hgd Herr HS1 HF1 Heq.
exact (eq_leaf L A regs mem md g am fr n a ka rg HC gd err Hgd Herr ms1 HS1 HF1 Heq).
Qed.
End b.
