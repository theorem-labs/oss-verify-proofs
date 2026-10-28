(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
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
YO29 YO2a YO2b YO2h YO30 YO2z
UO0c UO08 UO0b UO16 UO0y UO0z
UO14 UO13 UO11 UO17 UO10.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ubs2_in_img x : 0x10000 <= x < 0x54000 -> in_img ubs2_msyms x.
Proof.
intros Hx.
destruct (Z_lt_le_dec x 0x12000); [eapply (covered_sound ubs2_msyms 0x10000 0x2000); [vm_compute; reflexivity | lia]|].
destruct (Z_lt_le_dec x 0x21000); [eapply (covered_sound ubs2_msyms 0x12000 0xf000); [vm_compute; reflexivity | lia]|].
destruct (Z_lt_le_dec x 0x22000); [eapply (covered_sound ubs2_msyms 0x21000 0x1000); [vm_compute; reflexivity | lia]|].
eapply (covered_sound ubs2_msyms 0x22000 0x32000); [vm_compute; reflexivity | lia].
Qed.
Lemma S2_regs_lt r : regs_atoms_lt 106 (ss_regs (S2 r)) = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma S2_facts_lt r : facts_atoms_lt 106 (ss_facts (S2 r)) = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma stk2_lt r : region_atoms_lt 106 (stk2 r) = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma wf9_stk2 r : regions_wf [reg_area; reg_ctx; reg_nl; stk2 r; reg_got; reg_guard; reg_errnoR; reg_metaR; reg_nhdr] = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma ss_mem_S2ok r t0 : ss_mem (S2ok r t0) = tail_mem (S2 r) t0.
Proof. reflexivity. Qed.
Section d.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YP0j.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Variables (gd err : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (RETw : word) (memM : word -> option byte).
Local Notation rcr := (UO0y.rcr am fr).
Local Notation VV := (UO0y.vv L regs g am fr a rg).
Local Notation E := (Er L regs g am fr n a rg gd err).
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
Hypothesis AT2 : at_S2 L regs mem g am fr n a rg gd err regs2 mem2.
Hypothesis Hne : old_len am <> needed fr n.
Hypothesis PM : mremap_post_mem mem2 memM MEM OLDLEN (bv_unsigned RETw) NEEDED.
Hypothesis CASES :
(RETw = Z_to_bv 64 MEM /\ MEM + NEEDED <= alloc_ceiling /\
(region_free (vm_reserved (m_vmmaps md) ++ map_remove (vm_maps (m_vmmaps md)) (Z_to_bv 64 MEM))
(Z_to_bv 64 MEM) (Z_to_bv 64 NEEDED) = true
\/ NEEDED < OLDLEN))
\/ (OLDLEN < NEEDED /\ mremap_fresh_b md OLDLEN NEEDED (Z_to_bv 64 MEM) (Z_to_bv 64 OLDLEN) RETw (Z_to_bv 64 NEEDED) = true).
Definition RET : Z := bv_unsigned RETw.
Local Notation NP := (UO17.NP fr RET).
Local Notation NEND := (UO17.NEND fr n RET).
Local Notation NPN := (UO17.NPN fr n RET).
Local Notation Et := (UO17.Et L regs g am fr n a rg gd err RET).
Lemma Hgd : 0 <= gd < 2 ^ 64. Proof. exact (proj1 AT2). Qed.
Lemma Herr : 0 <= err < 2 ^ 32. Proof. exact (proj1 (proj2 AT2)). Qed.
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let MX : MRx ubs2_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
Let M : MRc ubs2_msyms L A mem md := M L A regs mem md g am fr n a ka rg HC.
Let XR : forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64 :=
xvr_rangeG L A regs mem md g am fr n a ka rg HC rcr FP gd err Hgd Herr.
Lemma ERETw : RETw = Z_to_bv 64 RET.
Proof. unfold RET. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma PMr : mremap_post_mem mem2 memM MEM OLDLEN RET NEEDED.
Proof. exact PM. Qed.
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ M). Qed.
Lemma old_entry : exists r, MEM = ly_reg L r /\ region_of A r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
rg_len rg = OLDLEN /\ In (Z_to_bv 64 MEM, Z_to_bv 64 OLDLEN) (vm_maps (m_vmmaps md)).
Proof.
destruct (grp_region L A regs mem md g am fr n a ka rg HC) as (r & Hmem & Hr & Hk & Hlv & Hlen & Hml).
assert (EMEM : MEM = ly_reg L r) by (unfold UO17.MEM, ptr_addr; rewrite Hmem; cbn [loc_addr]; lia).
assert (ELEN : rg_len rg = OLDLEN) by (rewrite Hlen; reflexivity).
exists r. repeat (split; [assumption|]). rewrite EMEM, <- ELEN.
exact (lg_maps _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hlv ltac:(rewrite Hk; discriminate)).
Qed.
Lemma okfacts :
4096 <= RET /\ RET + NEEDED <= alloc_ceiling /\ RET mod 4096 = 0 /\
(forall e, In e (vm_maps (m_vmmaps md)) -> e <> (w64 MEM, w64 OLDLEN) -> ranges_disjoint (RET, NEEDED) (iv_lo e, iv_len e)) /\
(forall x, RET <= x < RET + NEEDED -> ~ in_img ubs2_msyms x).
Proof.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
clear C23 C24 C26.
pose proof (placed ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & Pimg & P5).
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & _). rewrite NM, NO in Pimg. rewrite NO in P5.
pose proof YN05.alloc_ceiling_val as HCV. pose proof (lx_disj _ _ _ (MRx_ledger_x _ _ _ _ _ MX)) as LD.
pose proof (lx_maps _ _ _ (MRx_ledger_x _ _ _ _ _ MX)) as LM.
pose proof (lg_reserved _ _ _ _ (mc_ledger _ _ _ _ _ M)) as LR. change (ms_segs ubs2_msyms) with ubs2segs in LR.
destruct old_entry as (r & EMEM & Hr & Hk & Hlv & ELEN & OIN).
assert (NPOS : 0 < NEEDED). { clear - C3 C4 C1 C2. lia. }
assert (IMGseg : forall x lo nn, region_free (vm_reserved (m_vmmaps md)) (Z_to_bv 64 lo) (Z_to_bv 64 nn) = true ->
0 <= lo -> 0 < nn -> lo + nn < 2 ^ 64 -> lo <= x < lo + nn -> ~ in_img ubs2_msyms x).
{ intros x lo nn RF Hlo Hnn Hhi Hx [_ (s & Hs & Hxs)]. change (ms_segs ubs2_msyms) with ubs2segs in Hs. rewrite <- LR in Hs.
destruct s as [b sz]. pose proof (region_free_In _ _ _ _ _ RF Hs) as OV. cbn [fst snd] in Hxs.
unfold iv_overlap in OV. rewrite !lit64_small in OV by lia.
apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
assert (RFapp : forall l1 l2 lo nn, region_free (l1 ++ l2) lo nn = true -> region_free l1 lo nn = true /\ region_free l2 lo nn = true).
{ intros l1 l2 lo nn RF. split; apply region_free_intro; intros b sz Hin; apply (region_free_In _ _ _ _ _ RF); apply in_or_app; [left | right]; exact Hin. }
destruct CASES as [(ER & Hce & SUB) | (Hlt & FR)].
-
assert (ERET : RET = MEM) by (unfold RET; rewrite ER; apply lit64_small; lia). rewrite ERET.
split; [exact C9|]. split; [exact Hce|]. split; [exact C11|].
destruct SUB as [RF | SHR].
+
destruct (RFapp _ _ _ _ RF) as [RF1 RF2]. split.
* intros e He Hneq. destruct e as [elo elen]. destruct (LM _ He) as [Lpos Lhi]. unfold iv_lo, iv_len in *. cbn [fst snd] in *.
assert (Hlo : elo <> Z_to_bv 64 MEM).
{ intros Elo. destruct (LD _ _ He OIN) as [EQ | DJ]; [exact (Hneq EQ)|].
unfold ranges_disjoint, iv_lo, iv_len in DJ. cbn [fst snd] in DJ. rewrite Elo, !lit64_small in DJ by lia. clear - DJ Lpos P5. lia. }
assert (Hin : In (elo, elen) (map_remove (vm_maps (m_vmmaps md)) (Z_to_bv 64 MEM))).
{ unfold map_remove. apply filter_In. split; [exact He|]. cbn [fst]. destruct (bv_eqb elo (Z_to_bv 64 MEM)) eqn:Eb; [|reflexivity].
apply bv_eqb_eq in Eb. exact (False_ind _ (Hlo Eb)). }
pose proof (region_free_In _ _ _ _ _ RF2 Hin) as OV. unfold iv_overlap in OV. rewrite !lit64_small in OV by lia.
unfold ranges_disjoint. cbn [fst snd]. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; clear - OV; lia.
* intros x Hx. apply (IMGseg x MEM NEEDED RF1); clear - Hx C9 Hce HCV NPOS; lia.
+
split.
* intros e He Hneq. destruct (LD _ _ He OIN) as [EQ | DJ]; [exact (False_ind _ (Hneq EQ))|].
unfold ranges_disjoint, iv_lo, iv_len in DJ |- *. cbn [fst snd] in DJ |- *. rewrite !lit64_small in DJ by lia. clear - DJ SHR NPOS. lia.
* intros x Hx. apply Pimg. clear - Hx SHR. lia.
-
pose proof (mremap_fresh_facts md (Z_to_bv 64 MEM) (Z_to_bv 64 OLDLEN) RETw (Z_to_bv 64 NEEDED)) as FF.
rewrite !lit64_small in FF by lia. specialize (FF FR). destruct FF as (Hneq & Hal & Hpos & Hce & RF & _).
fold RET in Hal, Hpos, Hce. unfold page_size in Hal.
assert (Hce' : RET + NEEDED <= alloc_ceiling)
by (apply (YN05.grant_below_ceil _ _ (lg_ceil _ _ _ _ (mc_ledger _ _ _ _ _ M))); [rewrite Z.add_mod, Hal, C6 by lia; reflexivity | exact Hce]).
clear Hce. rename Hce' into Hce.
assert (R4096 : 4096 <= RET).
{ clear - Hal Hpos. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. lia. }
rewrite ERETw in RF. destruct (RFapp _ _ _ _ RF) as [RF1 RF2].
split; [exact R4096|]. split; [exact Hce|]. split; [exact Hal|]. split.
+ intros e He _. destruct e as [elo elen]. destruct (LM _ He) as [Lpos Lhi]. unfold iv_lo, iv_len in *. cbn [fst snd] in *.
pose proof (region_free_In _ _ _ _ _ RF2 He) as OV. unfold iv_overlap in OV. rewrite !lit64_small in OV by lia.
unfold ranges_disjoint. cbn [fst snd]. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; clear - OV; lia.
+ intros x Hx. apply (IMGseg x RET NEEDED RF1); clear - Hx R4096 Hce HCV NPOS; lia.
Qed.
Let RETlo : 4096 <= RET := proj1 okfacts.
Let REThi : RET + NEEDED <= alloc_ceiling := proj1 (proj2 okfacts).
Let RETpg : RET mod 4096 = 0 := proj1 (proj2 (proj2 okfacts)).
Let DISJ := proj1 (proj2 (proj2 (proj2 okfacts))).
Let NIMG : forall x, RET <= x < RET + NEEDED -> ~ in_img ubs2_msyms x := proj2 (proj2 (proj2 (proj2 okfacts))).
Lemma RETal16 : RET mod 16 = 0.
Proof.
pose proof RETpg as H. pose proof RETlo as H0. clear - H H0. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. rewrite Hq.
replace (q * 4096) with ((q * 256) * 16) by lia. apply Z_mod_mult.
Qed.
Let RETal : RET mod 16 = 0 := RETal16.
Lemma RETimg' : RET_img fr n RET.
Proof.
unfold RET_img. pose proof NIMG as NI. pose proof RETlo as R0.
destruct (Z_le_dec (RET + NEEDED) 0x10000) as [Hl|Hl]; [left; exact Hl|].
destruct (Z_le_dec 0x54000 RET) as [Hh|Hh]; [right; exact Hh|]. exfalso.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as (C1 & C2 & C3 & C4 & _).
apply (NI (Z.max RET 0x10000)); [clear - Hl Hh C1 C2 C3 C4; lia|]. apply ubs2_in_img. clear - Hl Hh R0. lia.
Qed.
Let RETimg : RET_img fr n RET := RETimg'.
Lemma RETarea' : RET_area L fr n a RET.
Proof.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
clear C24 C25 C26 C6 C11. pose proof DISJ as DJ. pose proof RETlo as R0.
pose proof (placed ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & _ & P5).
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & _). rewrite NO in P5.
destruct (rc_area _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hain & Hka & Eg).
destruct (proj1 (proj2 (inv_areas (HW L A regs mem md g am fr n a ka rg HC))) a Hain) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & Hrak).
assert (EAREA : AREA = ly_reg L ra + oa) by (unfold UO17.AREA, ptr_addr; rewrite Ea; cbn [loc_addr]; lia).
pose proof (lx_cov _ _ _ (MRx_ledger_x _ _ _ _ _ MX) ra rga) as COV. pose proof (reg_lo_le rga) as RLO.
pose proof YN05.alloc_ceiling_val as HCV.
assert (PT : forall x, AREA <= x < AREA + 4096 -> ~ (RET <= x < RET + NEEDED)).
{ intros x Hx HxR. destruct (COV x Hra Hral ltac:(unfold PGSZ in *; clear - Hx EAREA RLO Hoa2 Hoalen; lia)) as (e & He & Hxe).
assert (Hneq : e <> (w64 MEM, w64 OLDLEN)).
{ intros ->. unfold iv_lo, iv_len, w64 in Hxe. cbn [fst snd] in Hxe. rewrite !lit64_small in Hxe by lia. clear - Hxe Hx C23. lia. }
pose proof (DJ e He Hneq) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. clear - D Hxe HxR. lia. }
unfold RET_area.
destruct (Z_le_dec (RET + NEEDED) AREA) as [Hl|Hl]; [left; exact Hl|].
destruct (Z_le_dec (AREA + 4096) RET) as [Hh|Hh]; [right; exact Hh|]. exfalso.
apply (PT (Z.max RET AREA)); clear - Hl Hh C1 C2 C3 C4; lia.
Qed.
Let RETarea : RET_area L fr n a RET := RETarea'.
Local Notation TL X := (X L A regs mem md g am fr n a ka rg HC gd err Hgd Herr RET RETlo REThi RETal) (only parsing).
Lemma base_SP : base_val E (Some aSP) = SP.
Proof. unfold Er. rewrite (base_val_EV _ XR). unfold xvr, aSP. cbn [Nat.ltb Nat.leb]. rewrite xvf_reg by lia. reflexivity. Qed.
Lemma base_TP : base_val E (Some aTP) = ubs2_tp.
Proof. unfold Er. rewrite (base_val_EV _ XR). unfold xvr, aTP. cbn [Nat.ltb Nat.leb]. exact (xvf4 L A regs mem md g am fr n a ka rg HC). Qed.
Lemma base_AREA : base_val E (Some aAREA) = AREA.
Proof. unfold Er. rewrite (base_val_EV _ XR). reflexivity. Qed.
Lemma kept2 x : 0 <= x < 2 ^ 64 -> ~ SCR regs x -> mem2 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros Hx Hs. destruct AT2 as (_ & _ & _ & _ & _ & HF2). apply HF2. rewrite lit64_small by exact Hx. intros W. apply wr_entry in W.
rewrite base_SP, base_TP in W. apply Hs. unfold SCR, STK, ERRN. rewrite ERRNO2_val. clear - W. lia.
Qed.
Lemma keptM x : 0 <= x < 2 ^ 64 -> ~ (MEM <= x < MEM + OLDLEN) -> ~ (RET <= x < RET + NEEDED) -> memM (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x).
Proof. intros Hx N1 N2. destruct PMr as (_ & _ & _ & PM4). exact (PM4 x Hx N1 N2). Qed.
Lemma off_both x :
(AREA <= x < AREA + 4096) \/ (0x10000 <= x < 0x54000) \/ (alloc_ceiling <= x < 2 ^ 64) ->
0 <= x < 2 ^ 64 /\ ~ (MEM <= x < MEM + OLDLEN) /\ ~ (RET <= x < RET + NEEDED).
Proof.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
pose proof RETlo as R0. pose proof REThi as R1. pose proof RETimg as RI. pose proof RETarea as RA. unfold RET_img in RI. unfold RET_area in RA.
intros [Hx|[Hx|Hx]].
- clear - Hx C23 RA C16 C19 C12. lia.
- clear - Hx C25 RI C9 R0. lia.
- clear - Hx C10 R1 C12 C9 R0. lia.
Qed.
Definition msM : machine_state := mkst (regupd regs2 10 RETw) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) memM (seg_rom ubs2segs).
Lemma mem_ok_M : mem_ok ubs2segs Et memM (tail_mem (S2 rcr) t).
Proof.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
clear C6 C11 C26. pose proof RETlo as R0. pose proof REThi as R1.
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO).
destruct AT2 as (_ & _ & Hregs2 & Hmem2 & HG2 & HF2). rewrite S2_mem in Hmem2.
destruct (kept_of_mem_ok E mem2 (stk2 rcr) (r_mem rcr) Hmem2) as [_ PD].
pose proof YN05.alloc_ceiling_val as HCV.
rewrite tail_mem_S2. apply (TL mem_ok_tail); [| | | exact RETimg | exact RETarea | reflexivity | reflexivity | reflexivity | exact (stk2_lt rcr) | apply (TL wf_tail); exact (wf9_stk2 rcr) | | exact PD].
-   intros i Hi.
destruct (off_both (G + i) ltac:(left; clear - Hi C17 C18; lia)) as (X1 & X2 & X3). rewrite (keptM _ X1 X2 X3).
apply kept2; [exact X1|]. unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hi C12 C13 C14 C15 C16 C17 C18 C19 C24. lia.
-   intros i Hi. destruct PMr as (PM1 & _).
unfold UO17.NP. replace (RET + 16 + 16 * OFF - 4 + i) with (RET + (12 + 16 * OFF + i)) by lia.
rewrite (PM1 (12 + 16 * OFF + i)) by (clear - Hi C1 C2 C3 C4 C7; lia). replace (MEM + (12 + 16 * OFF + i)) with (P - 4 + i) by (clear - C8; lia).
apply kept2; [clear - Hi C8 C9 C10 C7 C1 C2 C12; lia|].
unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hi C1 C2 C7 C8 C9 C10 C12 C13 C25. lia.
-   intros x Hx. apply present_writable. destruct PMr as (PM1 & PM2 & _).
destruct (Z_lt_le_dec (x - RET) (Z.min OLDLEN NEEDED)) as [Hlt|Hge].
+ replace x with (RET + (x - RET)) by lia. unfold present. rewrite (PM1 (x - RET)) by (clear - Hx Hlt; lia).
change (present mem2 (MEM + (x - RET))). apply (present_same mem).
* apply kept2; [clear - Hx Hlt C9 C10 C12; lia|]. unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hx Hlt C9 C10 C12 C13 C25. lia.
* apply (old_present ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)).
rewrite NM, NO. clear - Hx Hlt. lia.
+ exists (Z_to_bv 8 0). replace x with (RET + (x - RET)) by lia. apply PM2. clear - Hx Hge. lia.
-
apply (fixed7_ext E mem2 memM (stk2 rcr) (r_mem rcr) Hmem2). intros r0 x Hr0 Hx.
assert (OB : (AREA <= x < AREA + 4096) \/ (0x10000 <= x < 0x54000) \/ (alloc_ceiling <= x < 2 ^ 64)).
{ unfold fixed7 in Hr0. destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
cbn [r_base r_lo r_hi reg_area reg_ctx reg_nl stk2 reg_got reg_guard reg_errnoR] in Hx; rewrite ?base_AREA, ?base_SP, ?base_TP in Hx; cbn [base_val] in Hx;
unfold ubs2_D_malloc_context, ubs2_D_libc, ubs2_D_got_stack_chk_guard, ubs2_D_stack_chk_guard, ubs2_tp in Hx.
- left. clear - Hx. lia. - right; left. clear - Hx. lia. - right; left. clear - Hx. lia. - right; right. clear - Hx C12 C13. lia.
- right; left. clear - Hx. lia. - right; left. clear - Hx. lia. - right; left. clear - Hx. lia. }
destruct (off_both x OB) as (X1 & X2 & X3). exact (keptM x X1 X2 X3).
Qed.
Theorem st_ok_M : st_ok ubs2segs Et (S2ok rcr t) msM.
Proof.
destruct AT2 as (_ & _ & Hregs2 & Hmem2 & HG2 & HF2). destruct (S2_run_ok rcr) as (_ & Hpc2 & Hrv2).
pose proof (TL vals) as (VRET & _).
unfold msM, S2ok. rewrite <- Hpc2.
apply (st_ok_resume_mem _ 106 E Et (S2 rcr) regs2 memM (SOff aRET 0) RETw (tail_mem (S2 rcr) t)).
- exact Hregs2.
- exact (TL Et_agree).
- exact (S2_regs_lt rcr).
- rewrite (den_off0 _ (TL XRt)), VRET. symmetry. exact ERETw.
- exact mem_ok_M.
- apply (TL facts_ok_app).
+ exact (facts_ok_agree 106 E Et _ (TL Et_agree) (S2_facts_lt rcr) HG2).
+ cbn [atoms_ok]. split; [exact (TL atom_RET RETpg) | exact (TL atoms_t)].
+ exact (TL conds_t).
+ apply (TL alias_t). exact VRET.
Qed.
Definition md5 : Model := mremap_model_next md (Z_to_bv 64 MEM) (Z_to_bv 64 OLDLEN) RETw (Z_to_bv 64 NEEDED).
Lemma md5_eq : md5 = YO2z.md' L md am fr n RET /\ m_halted md5 = None /\ m_vm_lazy md5 = [].
Proof.
destruct Hmd as (Hh & Hlz & Hmat). pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & _).
unfold md5, YO2z.md', YO2z.vm'. split; [| split].
- rewrite (mremap_next_with_vmmaps md _ _ _ _ Hlz Hmat). rewrite NM, ERETw. reflexivity.
- rewrite mremap_next_halted. exact Hh.
- apply mremap_next_lazy. exact Hlz.
Qed.
Lemma gctx : realloc_gctx ubs2_msyms L A mem md g am fr n.
Proof.
split; [exact MX | exact (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)
| exact (rc_big _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.
Lemma names_ok :
YO2z.P' fr RET = NP /\ YO2z.END' fr n RET = NEND /\
YO2z.RSV' fr n = RSV' /\ YO2z.RC' fr n = RC' /\
YO2z.OFF fr = OFF /\ YO2z.NOLD fr = NOLD /\ YO2z.G L g = G /\
YO2z.NEEDED fr n = NEEDED /\ NPN = NP + n.
Proof. repeat split; reflexivity. Qed.
Lemma at_S5 ms5 :
st_ok ubs2segs Et (S5 rcr t) ms5 -> frame_of Et (tail_regs fr n (stk2 rcr)) memM (ms_mem ms5) ->
ok_memspec ubs2_msyms L A mem g am fr n RET (ms_mem ms5) (SCR regs) /\
(forall x, STK regs x \/ ERRN x -> writable_at ubs2segs (ms_mem ms5) x) /\
regs_preserved regs (ms_regs ms5) /\ getr (ms_regs ms5) 10 = Z_to_bv 64 NP /\ ew Et 1 = getr regs 1.
Proof.
intros HS5 HF5.
pose proof (ctx_lin L A regs mem md g am fr n a ka rg HC) as CL.
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26).
clear C6 C11 C26. pose proof RETlo as R0. pose proof REThi as R1. pose proof YN05.alloc_ceiling_val as HCV.
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO).
pose proof names_ok as (KP & KEND & KRSV & KRC & KOFF & KNOLD & KG & KNEED & KNPN).
pose proof PRE as (_ & _ & _ & Hret & Hal & Hceil & Hsp63 & _).
pose proof (TL vals) as (VRET & VNP & VNEND & VNPN & VMEM & _).
pose proof RETimg as RI. unfold RET_img in RI. pose proof RETarea as RA. unfold RET_area in RA.
destruct (S5_shape rcr t) as (Hpc5 & Hrv5 & Hcv5 & Ha05 & Hsm5).
pose proof (TL final_read aRET (stk2 rcr) (S5 rcr t) ms5 RETimg HS5 Hsm5 VRET Hcv5 Ha05 eq_refl eq_refl eq_refl) as FR.
lazy zeta in FR. destruct FR as (B4 & B3 & B2 & G16 & G24 & G28 & G32 & BEND & BPN & B45 & WS & PRS & RP & A05 & E1).
split; [| split; [exact WS | split; [exact RP | split; [exact A05 | exact E1]]]].
assert (KEPT5 : forall x, 0 <= x < 2 ^ 64 -> ~ SCR regs x -> ~ (G + 16 <= x < G + 40) -> ~ (NP - 4 <= x < NP) ->
~ ((0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND) ->
ms_mem ms5 (Z_to_bv 64 x) = memM (Z_to_bv 64 x)).
{ intros x Hx N1 N2 N3 N4. apply HF5. rewrite lit64_small by exact Hx. intros W.
apply (TL wr_tail (stk2 rcr) x eq_refl eq_refl eq_refl) in W. unfold SCR in N1. clear - W N1 N2 N3 N4. tauto. }
pose proof (old_bytes ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC))
as (h3 & h16 & _ & _ & _ & _ & _ & _ & OP4 & OP2). rewrite NP' in OP4, OP2. rewrite NOF in OP2.
assert (RAW : forall m x v, mbyte ubs2segs m x = Some v -> 0 <= x < 2 ^ 64 -> (x + 1 <= 0x10000 \/ 0x54000 <= x) -> m (Z_to_bv 64 x) = Some v).
{ intros m x v Hb Hx Hi. rewrite <- (mbyte_off_img2 m x Hx ltac:(unfold in_img1; clear - Hi; lia)). exact Hb. }
split; rewrite ?NM, ?NO, ?KP, ?KEND, ?KRSV, ?KRC, ?KOFF, ?KNOLD, ?KG, ?KNEED, <- ?KNPN; unfold w64.
- intros x Hx. apply (ubs2_scratch_hi regs x Hceil). apply SCR_scratch. exact Hx.
-   intros i Hi Hi13. destruct PMr as (PM1 & _).
assert (D : (i = 16 * OFF + 12 \/ i = 16 * OFF + 14 \/ i = 16 * OFF + 15) \/ ~ (16 * OFF + 12 <= i < 16 * OFF + 16)) by (clear - Hi Hi13; lia).
destruct D as [D | D].
+
assert (NI1 : RET + i + 1 <= 0x10000 \/ 0x54000 <= RET + i) by (clear - Hi RI C1 C2 C3 C4; lia).
assert (NI0 : MEM + i + 1 <= 0x10000 \/ 0x54000 <= MEM + i) by (clear - Hi C25 C1 C2 C7; lia).
destruct D as [-> | [-> | ->]].
* replace (RET + (16 * OFF + 12)) with (NP - 4 + Z.of_nat 0) by (unfold UO17.NP; lia).
rewrite (RAW _ _ _ (B4 0%nat ltac:(lia))); [| clear - R0 R1 HCV C1 C2 C3 C4; unfold UO17.NP; lia | clear - NI1; unfold UO17.NP; lia].
replace (MEM + (16 * OFF + 12)) with (P - 4 + Z.of_nat 0) by (clear - C8; lia).
rewrite (RAW _ _ _ (OP4 0%nat ltac:(lia))); [reflexivity | clear - C8 C9 C10 HCV C1 C2 C7; lia | clear - NI0 C8; lia].
* replace (RET + (16 * OFF + 14)) with (NP - 2 + Z.of_nat 0) by (unfold UO17.NP; lia).
rewrite (RAW _ _ _ (B2 0%nat ltac:(lia))); [| clear - R0 R1 HCV C1 C2 C3 C4; unfold UO17.NP; lia | clear - NI1; unfold UO17.NP; lia].
replace (MEM + (16 * OFF + 14)) with (P - 2 + Z.of_nat 0) by (clear - C8; lia).
rewrite (RAW _ _ _ (OP2 0%nat ltac:(lia))); [reflexivity | clear - C8 C9 C10 HCV C1 C2 C7; lia | clear - NI0 C8; lia].
* replace (RET + (16 * OFF + 15)) with (NP - 2 + Z.of_nat 1) by (unfold UO17.NP; lia).
rewrite (RAW _ _ _ (B2 1%nat ltac:(lia))); [| clear - R0 R1 HCV C1 C2 C3 C4; unfold UO17.NP; lia | clear - NI1; unfold UO17.NP; lia].
replace (MEM + (16 * OFF + 15)) with (P - 2 + Z.of_nat 1) by (clear - C8; lia).
rewrite (RAW _ _ _ (OP2 1%nat ltac:(lia))); [reflexivity | clear - C8 C9 C10 HCV C1 C2 C7; lia | clear - NI0 C8; lia].
+ rewrite KEPT5.
* rewrite (PM1 i) by (clear - Hi C1 C2 C3 C4 C7; lia). apply kept2; [clear - Hi C1 C2 C7 C9 C10 C12; lia|].
unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hi C1 C2 C7 C9 C10 C12 C13 C25. lia.
* clear - Hi C1 C2 C3 C4 C7 C9 C10 C12 R0 R1 HCV. lia.
* unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hi C1 C2 C3 C4 R0 R1 C12 C13 RI. lia.
* clear - Hi C1 C2 C3 C4 C17 C18 RA. lia.
* unfold UO17.NP. clear - D C1. lia.
* unfold UO17.NPN, UO17.NEND, UO17.NP. clear - Hi C1 C2 C3 C4. lia.
- exact B3. - exact G16. - exact G24. - exact G28. - exact G32. - exact BEND. - exact BPN. - exact B45.
-   intros x Hx. destruct PMr as (PM1 & PM2 & _).
assert (D : ((NP - 4 <= x < NP) \/ (0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND) \/
~ ((NP - 4 <= x < NP) \/ (0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND)) by (clear; lia).
destruct D as [D|D]; [apply PRS; clear - D; tauto|].
unfold present. rewrite KEPT5; [| clear - Hx R0 R1 HCV; lia | | clear - Hx RA C17 C18; lia | clear - D; tauto | clear - D; tauto].
2:{ unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hx R0 R1 C12 C13 RI. lia. }
destruct (Z_lt_le_dec (x - RET) (Z.min OLDLEN NEEDED)) as [Hlt|Hge].
+ replace x with (RET + (x - RET)) by lia. rewrite (PM1 (x - RET)) by (clear - Hx Hlt; lia).
change (present mem2 (MEM + (x - RET))). apply (present_same mem).
* apply kept2; [clear - Hx Hlt C9 C10 C12; lia|]. unfold SCR, STK, ERRN. rewrite ERRNO2_val. unfold ubs2_tp. clear - Hx Hlt C9 C10 C12 C13 C25. lia.
* apply (old_present ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)).
rewrite NM, NO. clear - Hx Hlt. lia.
+ exists (Z_to_bv 8 0). replace x with (RET + (x - RET)) by lia. apply PM2. clear - Hx Hge. lia.
-   intros x Hx N1 N2 N3 N4. rewrite KEPT5; [| exact Hx | exact N4 | exact N3 | unfold UO17.NP; clear - N1 C1 C2 C3 C4; lia
| unfold UO17.NPN, UO17.NEND, UO17.NP; clear - N1 C1 C3 C4 C2; lia].
rewrite (keptM x Hx N2 N1). apply kept2; [exact Hx | exact N4].
- intros x Hx. apply PRS. right; left. exact Hx.
Qed.
Lemma run5 : SR ubs2segs (mkCfg msM md5) (to_state Et msM md5 (S5 rcr t) (ss_mem (S2ok rcr t))).
Proof. destruct md5_eq as (Emd5 & Hh5 & Hlz5). exact (S5_run Et msM md5 Hh5 Hlz5 rcr t st_ok_M). Qed.
Lemma leaf5 ms5 :
st_ok ubs2segs Et (S5 rcr t) ms5 -> frame_of Et (tail_regs fr n (stk2 rcr)) memM (ms_mem ms5) ->
SR ubs2segs (mkCfg ms5 md5)
(realloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs mem md (pp am fr) (fr_n fr) n (Some (p_ok A am fr n), A_ok A g am fr n)).
Proof.
intros HS5 HF5.
pose proof RETlo as R0. destruct md5_eq as (Emd5 & Hh5 & Hlz5).
pose proof (names_eq L A regs mem md g am fr n a ka rg HC) as (NM & NO & NP' & NG & NN & NOF & NNO).
pose proof names_ok as (KP & KEND & KRSV & KRC & KOFF & KNOLD & KG & KNEED & KNPN).
pose proof PRE as (_ & _ & _ & Hret & _).
destruct (S5_shape rcr t) as (Hpc5 & Hrv5 & Hcv5 & Ha05 & Hsm5).
destruct (at_S5 ms5 HS5 HF5) as (OM & WS & RP & A05 & E1).
assert (NEI : YO2z.OLDLEN am <> YO2z.NEEDED fr n) by (rewrite NO, NN; exact Hne).
destruct (realloc_ok_leaf ubs2_msyms L A mem md g am fr n RET (ms_mem ms5) (SCR regs) gctx NEI
ltac:(unfold PGSZ; exact RETpg) ltac:(clear - R0; lia) REThi
ltac:(intros e He Hq; apply (DISJ e He); rewrite <- NM, <- NO; exact Hq) NIMG OM)
as (MX5 & WF5 & BND5 & LE5 & ADDR5 & FRM5 & BLK5 & [EPP Pnz] & CNT5 & UB5 & _).
rewrite A'_is in MX5, WF5, BND5, BLK5, UB5. rewrite <- Emd5 in MX5. rewrite KOFF in EPP, Pnz, CNT5. rewrite NP' in CNT5. rewrite KNOLD in CNT5, UB5.
change (frame_ptr am 0 fr) with (pp am fr) in UB5.
pose proof Hcv5 as V1. unfold callee_view, callee_view0, view in V1. cbn [map] in V1.
apply (f_equal (fun l => List.nth 0 l (SLit 0))) in V1. cbn [List.nth] in V1. rewrite lit5 in V1 by lia. cbn [nat_to_reg] in V1.
eapply (SR_realloc_ret Et (S5 rcr t) ms5 md5 _ HS5 Hrv5 Hpc5 V1); [rewrite E1; exact Hret | exact Hh5 | exact Hlz5 |].
unfold realloc_leaf. exists (YO2z.L' L A RET), (ms_regs ms5), (ms_mem ms5), md5. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split.
-
unfold call_post_k. change (ms_segs ubs2_msyms) with ubs2segs.
split; [exact MX5|]. split; [exact WF5|]. split; [exact BND5|]. split; [exact LE5|].
split; [intros q k Hq _; exact (ADDR5 q k Hq)|]. split; [exact RP|].
split; [exists (YO2z.vm' L md am fr n RET); exact Emd5|].
split; [| split; [exact BLK5|]].
+ intros x Hx _ _ N3 _. apply FRM5; [exact Hx|]. intros Hs. apply N3. apply SCR_scratch. exact Hs.
+ intros x Hs. apply WS. apply SCR_scratch in Hs. exact Hs.
-
split; [rewrite A05, EPP; reflexivity|]. split; [rewrite EPP; exact Pnz|].
split; [exact UB5|].
intros i Hi. rewrite EPP. unfold UO17.P in CNT5. apply CNT5. unfold UO17.NOLD.
pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC). clear - Hi H. unfold PGSZ in H. lia.
Qed.
Theorem ok_leaf :
SR ubs2segs (mkCfg msM md5)
(realloc_leaf ubs2_msyms (MRx ubs2_msyms) L A regs mem md (pp am fr) (fr_n fr) n (Some (p_ok A am fr n), A_ok A g am fr n)).
Proof.
eapply SR_bind; [exact run5|].
intros c5 (ms5 & -> & HS5 & HF5). cbn [ms_mem msM] in HF5. rewrite ss_mem_S2ok, tail_mem_S2 in HF5.
exact (leaf5 ms5 HS5 HF5).
Qed.
End d.
Theorem ubs2_realloc_ok : OBL_ok_T.
Proof.
intros L A regs mem md g am fr n a ka rg HC gd err regs2 mem2 RET mem' AT2 Hne PM CASES.
exact (ok_leaf L A regs mem md g am fr n a ka rg HC gd err regs2 mem2 RET mem' AT2 Hne PM CASES).
Qed.
End c.
