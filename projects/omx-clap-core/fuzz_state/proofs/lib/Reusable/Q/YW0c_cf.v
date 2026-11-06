(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN03 YN02_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW01_cf YW00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN2b YN25_cf YN26_cf YN27 YN2c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW03_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN0b_cf YN07_cf YN0a_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW0e_cf YW06_cf YW07_cf YY00_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma region_free_intro : forall l (lo n : word),
(forall a sz, In (a, sz) l -> iv_overlap lo n a sz = false) -> region_free l lo n = true.
Proof.
induction l as [|[a sz] l IH]; intros lo n H; [reflexivity|].
cbn [region_free]. rewrite (H a sz ltac:(left; reflexivity)). cbn [negb andb].
apply IH. intros a' sz' Hin. apply H. right. exact Hin.
Qed.
Lemma region_free_of_img : forall (B : malloc_syms) lo n,
ms_segs B <> [] -> Forall (fun s => 0 < bv_unsigned (snd s)) (segments_reserved (ms_segs B)) ->
0 < n -> 0 <= lo -> lo + n < 2 ^ 64 ->
(forall a, lo <= a < lo + n -> ~ in_img B a) ->
region_free (segments_reserved (ms_segs B)) (Z_to_bv 64 lo) (Z_to_bv 64 n) = true.
Proof.
intros B lo n Hne Hpos Hn Hlo Hhi Himg. apply region_free_intro. intros a sz Hin.
pose proof (proj1 (Forall_forall _ _) Hpos _ Hin) as Hsz. cbn [snd] in Hsz.
unfold iv_overlap. rewrite !lit64_small by lia.
destruct (Z.ltb_spec lo (bv_unsigned a + bv_unsigned sz)); [|reflexivity].
destruct (Z.ltb_spec (bv_unsigned a) (lo + n)); [|reflexivity].
exfalso. apply (Himg (Z.max lo (bv_unsigned a))); [lia|].
split; [exact Hne|]. exists (a, sz). split; [exact Hin|]. cbn [fst snd]. lia.
Qed.
Lemma src0_segs_pos : Forall (fun s => 0 < bv_unsigned (snd s)) (segments_reserved src0segs).
Proof. vm_compute. repeat constructor. Qed.
Lemma src0_segs_ne : src0segs <> [].
Proof. vm_compute. discriminate. Qed.
Lemma region_free_of_disjoint : forall l lo n,
0 <= lo -> 0 < n -> lo + n < 2 ^ 64 ->
(forall e, In e l -> ranges_disjoint (lo, n) (iv_lo e, iv_len e)) ->
region_free l (Z_to_bv 64 lo) (Z_to_bv 64 n) = true.
Proof.
intros l lo n Hlo Hn Hhi H. apply region_free_intro. intros a sz Hin.
specialize (H (a, sz) Hin). unfold ranges_disjoint, iv_lo, iv_len in H. cbn [fst snd] in H.
unfold iv_overlap. rewrite !lit64_small by lia.
destruct (Z.ltb_spec lo (bv_unsigned a + bv_unsigned sz)); [|reflexivity].
destruct (Z.ltb_spec (bv_unsigned a) (lo + n)); [|reflexivity]. exfalso. lia.
Qed.
Section c.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Let E gd err := Er L regs g am fr n a rg gd err.
Let MEM := ptr_addr L (am_mem am).
Let OLDLEN := old_len am.
Let NEEDED := needed fr n.
Definition at_S2 (gd err : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
0 <= gd < 2 ^ 64 /\ 0 <= err < 2 ^ 32 /\
regs_ok (E gd err) (ss_regs (S2 (rcr am fr))) regs2 /\
mem_ok src0segs (E gd err) mem2 (ss_mem (S2 (rcr am fr))) /\
facts_ok (E gd err) (ss_facts (S2 (rcr am fr))) /\
frame_of (E gd err) (entry_mem (rcr am fr)) mem mem2.
Definition OBL_ok_at (gd err : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (RET : word) (mem' : word -> option byte) : Prop :=
at_S2 gd err regs2 mem2 ->
old_len am <> needed fr n ->
mremap_post_mem mem2 mem' MEM OLDLEN (bv_unsigned RET) NEEDED ->
( (RET = Z_to_bv 64 MEM /\ MEM + NEEDED <= alloc_ceiling /\
(region_free (vm_reserved (m_vmmaps md) ++ map_remove (vm_maps (m_vmmaps md)) (Z_to_bv 64 MEM))
(Z_to_bv 64 MEM) (Z_to_bv 64 NEEDED) = true
\/ NEEDED < OLDLEN))
\/ (OLDLEN < NEEDED /\
mremap_fresh_b md OLDLEN NEEDED (Z_to_bv 64 MEM) (Z_to_bv 64 OLDLEN) RET (Z_to_bv 64 NEEDED) = true) ) ->
SR_cfv src0segs (mkCfg (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem' (seg_rom src0segs))
(mremap_model_next md (Z_to_bv 64 MEM) (Z_to_bv 64 OLDLEN) RET (Z_to_bv 64 NEEDED)))
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n (Some (p_ok A am fr n), A_ok A g am fr n)).
Definition OBL_fb_at (gd err : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
at_S2 gd err regs2 mem2 ->
mreal_cf src0segs
(mkCfg (mkst (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 MREMAP_ECALL) 4) mem2 (seg_rom src0segs)) md)
(realloc_move (pp am fr) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n).
End c.
Definition OBL_ok_T : Prop :=
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg),
MMAP_THRESHOLD <= n -> forall gd err regs2 mem2 RET mem',
OBL_ok_at L A regs mem md g am fr n a rg gd err regs2 mem2 RET mem'.
Definition OBL_fb_T : Prop :=
OBL_fb_gen ->
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg),
MMAP_THRESHOLD <= n -> forall gd err regs2 mem2,
OBL_fb_at L A regs mem md g am fr n a rg gd err regs2 mem2.
Lemma skel_S1 : forall r, skeleton (entry_mem r) = skeleton (ss_mem (S1 r)).
Proof. intros r. destruct (S1_shape r) as (_ & _ & _ & _ & ->). destruct r; reflexivity. Qed.
Section d.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Variables (gd err : Z).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Herr : 0 <= err < 2 ^ 32.
Local Notation VV := (YW06_cf.vv L regs g am fr a rg).
Local Notation rcr := (YW06_cf.rcr am fr).
Local Notation E := (Er L regs g am fr n a rg gd err).
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let M : MRc src0_msyms L A mem md := M L A regs mem md g am fr n a ka rg HC.
Let MX : MRx src0_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
Let HW : WF A := HW L A regs mem md g am fr n a ka rg HC.
Lemma grp_region : exists r, am_mem am = YO0i.SP r 0 /\ region_of A r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
rg_len rg = am_maplen am * PGSZ /\ 1 <= am_maplen am.
Proof using HW.
pose proof (inv_groups HW g am (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & Gcl & Gmp & _).
destruct (rm_shape U0 A g am 0 HW (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (Hl & Hml & _).
destruct (Gmp ltac:(lia)) as (r & rg' & Hmem & Hr & Hk & Hlv & Hlen & _).
destruct (rc_rg _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hrg & _). rewrite Hmem in Hrg. cbn [prid] in Hrg. rewrite Hr in Hrg. injection Hrg as ->.
exists r. repeat split; auto.
Qed.
Let XR : forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64 :=
xvr_rangeG L A regs mem md g am fr n a ka rg HC rcr FP gd err Hgd Herr.
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ M). Qed.
Lemma den_aMEM : sv_denot E (SOff aMEM 0) = Z_to_bv 64 (ptr_addr L (am_mem am)).
Proof. rewrite (den_off0 _ XR). reflexivity. Qed.
Lemma den_aMP : sv_denot E (SOff aMP 0) = Z_to_bv 64 (old_len am).
Proof. rewrite (den_off0 _ XR). unfold old_len. f_equal. cbn. lia. Qed.
Lemma den_aNEED : sv_denot E (SOff aNEED 0) = Z_to_bv 64 (needed fr n).
Proof. rewrite (den_off0 _ XR). reflexivity. Qed.
Lemma needed_range : n + UNIT * fr_off fr + UNIT + IB <= needed fr n /\ needed fr n mod PGSZ = 0 /\ 0 < needed fr n < 2 ^ 63.
Proof. exact (needed_rangeG L A regs mem md g am fr n a ka rg HC). Qed.
Section f.
Hypothesis OOK : forall regs2 mem2 RET mem', OBL_ok_at L A regs mem md g am fr n a rg gd err regs2 mem2 RET mem'.
Hypothesis OFB : forall regs2 mem2, OBL_fb_at L A regs mem md g am fr n a rg gd err regs2 mem2.
Theorem realloc_node : forall ms1,
st_ok src0segs E (S1 rcr) ms1 -> frame_of E (entry_mem rcr) mem (ms_mem ms1) ->
old_len am <> needed fr n ->
SR_cfv src0segs (mkCfg ms1 md)
(fun c1 => knode_cf src0segs c1 (KMremap (rid am) (old_len am) (needed fr n)) A
(fun z c2 => mreal_cf src0segs c2
(if negb (z =? 0) then IRet (Some (p_ok A am fr n), A_ok A g am fr n) else realloc_move (pp am fr) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n))).
Proof.
intros ms1 HS1 HF1 Hne. destruct Hmd as (Hh & Hlz & Hmat). pose proof needed_range as (NR1 & NR2 & NR3).
destruct grp_region as (r & Hmem & Hr & Hk & Hlv & Hlen & Hml).
pose proof (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hlv) as (Pal & Plo & Pce & Pimg).
pose proof YM05.alloc_ceiling_val as HCV.
assert (EMEM : ptr_addr L (am_mem am) = ly_reg L r) by (rewrite Hmem; unfold ptr_addr; cbn [loc_addr]; lia).
assert (ELEN : old_len am = rg_len rg) by (rewrite Hlen; unfold old_len, PGSZ; lia).
unfold PGSZ in *. assert (RLEN : 0 < old_len am < 2 ^ 63) by (rewrite ELEN, Hlen; lia).
assert (HS1' : st_ok src0segs E (add_cond (S1 rcr) condNE) ms1).
{ apply st_ok_add_cond; [exact HS1|]. rewrite den_aMP, den_aNEED. cbn [branch_taken].
apply Bool.negb_true_iff. apply bv_eqb_neq. intros X. apply (f_equal bv_unsigned) in X.
rewrite !lit64_small in X by lia. exact (Hne X). }
eapply SR_cfv_bind; [exact (S2_run E ms1 md Hh Hlz rcr HS1')|].
intros c2 (ms2 & -> & HS2 & HF2).
destruct (S2_run_ok rcr) as (_ & Hpc2 & Hrv2).
destruct (st_ok_ecall_shape _ E (S2 rcr) ms2 HS2 Hrv2) as (regs3 & mem3 & Ems2 & Hregs3 & Hmem3 & HG3).
rewrite Ems2 in HF2 |- *. cbn [ms_mem pend_at] in HF2. rewrite Hpc2.
destruct (S2_shape rcr) as (Hv1 & _ & _ & _). unfold view in Hv1. cbn [map] in Hv1.
pose proof (f_equal (fun l => List.nth 0 l (SLit 0)) Hv1) as V10. cbn [List.nth] in V10.
pose proof (f_equal (fun l => List.nth 1 l (SLit 0)) Hv1) as V11. cbn [List.nth] in V11.
pose proof (f_equal (fun l => List.nth 2 l (SLit 0)) Hv1) as V12. cbn [List.nth] in V12.
pose proof (f_equal (fun l => List.nth 3 l (SLit 0)) Hv1) as V13. cbn [List.nth] in V13.
pose proof (f_equal (fun l => List.nth 4 l (SLit 0)) Hv1) as V14. cbn [List.nth] in V14.
pose proof (f_equal (fun l => List.nth 5 l (SLit 0)) Hv1) as V17. cbn [List.nth] in V17.
assert (E10 : getr regs3 10 = Z_to_bv 64 (ptr_addr L (am_mem am))).
{ rewrite (Hregs3 10%bv). replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite V10. apply den_aMEM. }
assert (E11 : getr regs3 11 = Z_to_bv 64 (old_len am)).
{ rewrite (Hregs3 11%bv). replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). rewrite V11. apply den_aMP. }
assert (E12 : getr regs3 12 = Z_to_bv 64 (needed fr n)).
{ rewrite (Hregs3 12%bv). replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). rewrite V12. apply den_aNEED. }
assert (E13 : getr regs3 13 = Z_to_bv 64 1).
{ rewrite (Hregs3 13%bv). replace (13%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 13)) by (apply bv_eq; reflexivity). rewrite V13. reflexivity. }
assert (E17 : bv_unsigned (getr regs3 17) = 216).
{ rewrite (Hregs3 17%bv). replace (17%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 17)) by (apply bv_eq; reflexivity). rewrite V17. reflexivity. }
assert (AT2 : at_S2 L regs mem g am fr n a rg gd err regs3 mem3).
{ split; [exact Hgd|]. split; [exact Herr|]. split; [exact Hregs3|]. split; [exact Hmem3|]. split; [exact HG3|].
eapply frame_of_trans; [exact (skel_S1 rcr) | exact HF1 | exact HF2]. }
apply SR_cfv_ret.
eapply (knode_cf_mremap_cases src0segs regs3 (Z_to_bv 64 MREMAP_ECALL) mem3 (seg_rom src0segs) md A (rid am) (old_len am) (needed fr n));
[exact Hh | | | | | | |].
-
constructor; rewrite ?E10, ?E11, ?E12, ?E13, ?E17; rewrite ?lit64_small by lia; try lia.
+ reflexivity.
+ rewrite EMEM. exact Pal.
+ unfold old_len. unfold page_size. apply Z_mod_mult.
+ exact NR2.
+
pose proof (YM05.ceil_le_top _ (lg_ceil _ _ _ _ (mc_ledger _ _ _ _ _ M))). rewrite EMEM, ELEN. lia.
+   rewrite (lg_reserved _ _ _ _ (mc_ledger _ _ _ _ _ M)).
apply (region_free_of_img src0_msyms); [exact src0_segs_ne | exact src0_segs_pos | lia | lia | lia |].
rewrite EMEM, ELEN. exact Pimg.
+   apply map_has_In. rewrite EMEM, ELEN. exact (lg_maps _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hlv ltac:(rewrite Hk; discriminate)).
+   apply region_free_of_disjoint; [lia | lia | lia |].
intros e He. destruct (lx_noacc _ _ _ (MRx_ledger_x _ _ _ _ _ MX) e He) as (E0 & HE0 & Hlo0 & Hhi0 & Hd).
specialize (Hd r rg Hr Hlv Hk ltac:(lia)). rewrite EMEM, ELEN. unfold ranges_disjoint in *. cbn [fst snd] in *. lia.
+ exact Hlz.
-
intros e [<-|[]]. cbn [Z.eqb negb].
replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12)) by (apply bv_eq; reflexivity).
exact (OFB regs3 mem3 AT2).
-
intros mem' HPM Hce Hrf. cbn [Z.eqb negb]. apply mreal_cf_leaf.
rewrite E10, E11, E12 in *. rewrite !lit64_small in HPM by lia. rewrite !lit64_small in Hce by lia.
apply (OOK regs3 mem3 (Z_to_bv 64 (ptr_addr L (am_mem am))) mem' AT2 Hne).
+ rewrite lit64_small by lia. exact HPM.
+ left. split; [reflexivity|].
split; [
apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ (mc_ledger _ _ _ _ _ M))); [| exact Hce];
rewrite EMEM, Z.add_mod, Pal, NR2 by lia; reflexivity |].
destruct Hrf as [Hrf|Hrf]; [left; exact Hrf | right; rewrite !lit64_small in Hrf by lia; exact Hrf].
-
intros dst mem' Hlt Hfresh HPM. cbn [Z.eqb negb]. apply mreal_cf_leaf.
rewrite E10, E11, E12 in *. rewrite !lit64_small in HPM by lia. rewrite !lit64_small in Hlt by lia.
rewrite !lit64_small in Hfresh by lia.
apply (OOK regs3 mem3 dst mem' AT2 Hne HPM). right. split; [exact Hlt | exact Hfresh].
- exact (proj2 (proj2 (mc_md _ _ _ _ _ M))).
- exact (lx_lb _ _ _ (MRx_ledger_x _ _ _ _ _ MX)).
- rewrite E12, lit64_small by lia. lia.
Qed.
End f.
End d.
Theorem src0_realloc_node : OBL_ok_T -> OBL_fb_T -> OBL_node_T.
Proof using.
intros OOK OFB FB L A regs mem md g am fr n a ka rg HC Hth gd err ms1 Hgd Herr HS1 HF1 Hne.
exact (realloc_node L A regs mem md g am fr n a ka rg HC gd err Hgd Herr
(fun regs2 mem2 RET mem' => OOK L A regs mem md g am fr n a ka rg HC Hth gd err regs2 mem2 RET mem')
(fun regs2 mem2 => OFB FB L A regs mem md g am fr n a ka rg HC Hth gd err regs2 mem2)
ms1 HS1 HF1 Hne).
Qed.
End b.
