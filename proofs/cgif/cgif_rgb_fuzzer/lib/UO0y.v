(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YQ0k YN06 YK0s YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0a YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0q YP0m YP0o YP10 YP0v
YP0n YP0r YP0u YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YQ01 YO2f
YO29 YO2a YO30
UO0c UO08 UO0b UO16.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B2 := ubs2_msyms (only parsing).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition memcpy_spec : Prop :=
forall (bs : list byte) (d s n : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = n ->
bv_unsigned n = Z.of_nat (length bs) ->
rdn ubs2segs mem s (length bs) = Some bs ->
store_ok ubs2segs mem d (length bs) = true ->
bv_unsigned d + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned s + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned d + Z.of_nat (length bs) <= bv_unsigned s
\/ bv_unsigned s + Z.of_nat (length bs) <= bv_unsigned d) ->
exists regs',
msteps ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_memcpy) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv ->
r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs' r = getr regs r).
Definition malloc_impl_realizes : Prop :=
forall L A regs mem md n,
call_pre B2 (MRx B2) L A regs mem md ->
getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
mreal ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_libc_malloc_impl) mem (seg_rom ubs2segs)) md)
(malloc n A) (malloc_leaf B2 (MRx B2) L A regs mem md n).
Definition free_impl_realizes : Prop :=
forall L A regs mem md p n,
call_pre B2 (MRx B2) L A regs mem md ->
In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
mreal ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_libc_free) mem (seg_rom ubs2segs)) md)
(free (Some p) A) (free_leaf B2 (MRx B2) L A regs mem md p n).
Record realloc_ctx (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YP0j.region) : Prop := RCX {
rc_pre : call_pre_k B2 (MRx B2) REALLOC_STACK L A regs mem md;
rc_used : usedX [] A g am;
rc_fr : ss_fr (nth_slot am 0) = Some fr;
rc_kind : fr_kind fr = FUser;
rc_in : In (frame_ptr am 0 fr, fr_n fr) (user_blocks A);
rc_a0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am 0 fr));
rc_a1 : getr regs 11 = Z_to_bv 64 n;
rc_big : MMAP_THRESHOLD < fr_n fr;
rc_n : fr_n fr + PGSZ <= n < 2 ^ 62;
rc_63 : am_sc am = 63;
rc_last : am_last am = 0;
rc_area : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka);
rc_rg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg }.
Section c.
Hypothesis MALLOC : malloc_impl_realizes.
Hypothesis FREE : free_impl_realizes.
Hypothesis MEMCPY : memcpy_spec.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YP0j.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hu := rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hfr := rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hk := rc_kind _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hin := rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Ha0 := rc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Ha1 := rc_a1 _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hbig := rc_big _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hn := rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let H63 := rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hlast := rc_last _ _ _ _ _ _ _ _ _ _ _ _ HC.
Definition pp : sptr := frame_ptr am 0 fr.
Definition P : Z := ptr_addr L pp.
Definition G : Z := ptr_addr L g.
Definition SP : Z := spZ regs.
Definition nold : Z := fr_n fr.
Definition rcr : rcase := rcase_of (reserved_of am fr).
Definition vv : fvals := fv_of regs L g am 0 fr a (rg_len rg).
Definition NEEDED : Z := needed fr n.
Lemma MX : MRx B2 L A mem md. Proof. exact (proj1 PRE). Qed.
Lemma M : MRc B2 L A mem md. Proof. exact (MRx_MRc _ _ _ _ _ MX). Qed.
Lemma HW : WF A. Proof. exact (mc_wf _ _ _ _ _ M). Qed.
Lemma HL : layout_ok L A. Proof. exact (mc_layout _ _ _ _ _ M). Qed.
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ M). Qed.
Lemma Hth : MMAP_THRESHOLD <= n. Proof. unfold MMAP_THRESHOLD, PGSZ in *. lia. Qed.
Lemma Hn62 : n < 2 ^ 62. Proof. lia. Qed.
Lemma K3 : kcase_of am = K3b. Proof. unfold kcase_of. rewrite H63. reflexivity. Qed.
Lemma FP : free_pre K3b rcr vv mem.
Proof.
pose proof PRE as (MX' & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _).
rewrite <- K3. unfold rcr, vv. eapply free_pre_intro; try eassumption.
- exact M. - exact (MRx_rsv _ _ _ _ _ MX). - rewrite Hlast. lia.
- unfold REALLOC_STACK, ALLOC_STACK in *. repeat split; lia.
- intros x Hx. apply Hstk. unfold REALLOC_STACK, ALLOC_STACK in *. lia.
- exact (rc_area _ _ _ _ _ _ _ _ _ _ _ _ HC).
- exact (rc_rg _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
Definition xvr (gd err : Z) (k : nat) : Z :=
if (k <? 96)%nat then xvf vv k
else match k with
| 96%nat => gd
| 103%nat => 16 * fr_off fr
| 104%nat => NEEDED
| 105%nat => err
| _ => 0
end.
Definition Er (gd err : Z) : env := EV (xvr gd err).
Lemma Er_agree gd err : env_agree 96 (EV (xvf vv)) (Er gd err).
Proof.
split; [|reflexivity]. intros k Hk96. unfold Er, EV. cbn [ew]. unfold xvr.
replace (k <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk96). reflexivity.
Qed.
Lemma tree :
realloc (Some pp) n A =
if old_len am =? NEEDED then IRet (Some pp, A_eq A g am fr n)
else IAsk (KMremap (rid am) (old_len am) NEEDED) A
(fun z => if negb (z =? 0) then IRet (Some (p_ok A am fr n), A_ok A g am fr n) else realloc_move pp n A).
Proof. exact (realloc_tree A g am fr n HW Hu Hfr H63 Hlast Hth Hn62). Qed.
Hypothesis OBL_entry : exists gd err, 0 <= gd < 2 ^ 64 /\ 0 <= err < 2 ^ 32 /\
st_ok ubs2segs (Er gd err) (S0 rcr) (mkst regs (Z_to_bv 64 ubs2_A_realloc) mem (seg_rom ubs2segs)).
Hypothesis OBL_eq : forall gd err ms1, 0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok ubs2segs (Er gd err) (S1 rcr) ms1 -> frame_of (Er gd err) (entry_mem rcr) mem (ms_mem ms1) ->
old_len am = NEEDED ->
SR ubs2segs (mkCfg ms1 md) (realloc_leaf B2 (MRx B2) L A regs mem md pp (fr_n fr) n (Some pp, A_eq A g am fr n)).
Hypothesis OBL_node : forall gd err ms1, 0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok ubs2segs (Er gd err) (S1 rcr) ms1 -> frame_of (Er gd err) (entry_mem rcr) mem (ms_mem ms1) ->
old_len am <> NEEDED ->
SR ubs2segs (mkCfg ms1 md)
(fun c1 => knode ubs2segs c1 (KMremap (rid am) (old_len am) NEEDED) A
(fun z c2 => mreal ubs2segs c2
(if negb (z =? 0) then IRet (Some (p_ok A am fr n), A_ok A g am fr n) else realloc_move pp n A)
(realloc_leaf B2 (MRx B2) L A regs mem md pp (fr_n fr) n))).
Theorem realloc_mreal :
mreal ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_realloc) mem (seg_rom ubs2segs)) md)
(realloc (Some pp) n A)
(realloc_leaf B2 (MRx B2) L A regs mem md pp (fr_n fr) n).
Proof.
destruct Hmd as (Hh & Hlz & _). destruct OBL_entry as (gd & err & Hgd & Herr & HS0).
rewrite tree. destruct (old_len am =? NEEDED) eqn:E.
- apply Z.eqb_eq in E. apply mreal_leaf.
eapply SR_bind; [exact (S1_run (Er gd err) _ md Hh Hlz rcr HS0)|].
intros c' (ms1 & -> & HS1 & HF1). exact (OBL_eq gd err ms1 Hgd Herr HS1 HF1 E).
- apply Z.eqb_neq in E. apply (mreal_ask ubs2segs).
eapply SR_bind; [exact (S1_run (Er gd err) _ md Hh Hlz rcr HS0)|].
intros c' (ms1 & -> & HS1 & HF1). exact (OBL_node gd err ms1 Hgd Herr HS1 HF1 E).
Qed.
End c.
Definition OBL_entry_T : Prop :=
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg),
exists gd err, 0 <= gd < 2 ^ 64 /\ 0 <= err < 2 ^ 32 /\
st_ok ubs2segs (Er L regs g am fr n a rg gd err) (S0 (rcr am fr)) (mkst regs (Z_to_bv 64 ubs2_A_realloc) mem (seg_rom ubs2segs)).
Definition OBL_eq_T : Prop :=
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg) gd err ms1,
0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok ubs2segs (Er L regs g am fr n a rg gd err) (S1 (rcr am fr)) ms1 ->
frame_of (Er L regs g am fr n a rg gd err) (entry_mem (rcr am fr)) mem (ms_mem ms1) ->
old_len am = needed fr n ->
SR ubs2segs (mkCfg ms1 md) (realloc_leaf B2 (MRx B2) L A regs mem md (pp am fr) (fr_n fr) n (Some (pp am fr), A_eq A g am fr n)).
Definition OBL_node_T : Prop :=
malloc_impl_realizes -> free_impl_realizes -> memcpy_spec ->
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg) gd err ms1,
0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok ubs2segs (Er L regs g am fr n a rg gd err) (S1 (rcr am fr)) ms1 ->
frame_of (Er L regs g am fr n a rg gd err) (entry_mem (rcr am fr)) mem (ms_mem ms1) ->
old_len am <> needed fr n ->
SR ubs2segs (mkCfg ms1 md)
(fun c1 => knode ubs2segs c1 (KMremap (rid am) (old_len am) (needed fr n)) A
(fun z c2 => mreal ubs2segs c2
(if negb (z =? 0) then IRet (Some (p_ok A am fr n), A_ok A g am fr n) else realloc_move (pp am fr) n A)
(realloc_leaf B2 (MRx B2) L A regs mem md (pp am fr) (fr_n fr) n))).
Theorem ubs2_realloc_realizes :
forall (MALLOC : malloc_impl_realizes) (FREE : free_impl_realizes) (MEMCPY : memcpy_spec),
OBL_entry_T -> OBL_eq_T -> OBL_node_T ->
realloc_realizes B2 (MRx B2).
Proof.
intros MALLOC FREE MEMCPY O1 O2 O3 pc L A regs mem md p nold n Hpc PRE Hin Ha0 Ha1 Hth Hbig Hrange.
cbn [ms_realloc ubs2_msyms] in Hpc. injection Hpc as <-.
pose proof (MRx_MRc _ _ _ _ _ (proj1 PRE)) as MR. pose proof (mc_wf _ _ _ _ _ MR) as HWA.
destruct (user_blocks_frame A p nold HWA Hin) as (g & am & idx & fr & Hu & Hidx & Hfr & Hk & Hn & Hp).
destruct (big_block_direct A g am idx fr HWA Hu Hidx Hfr ltac:(lia)) as (H63 & -> & Hlast & Hml & _). subst p nold.
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (meta_in_area A g (MUsed am) HWA (In_of_mlookup _ _ _ Mg)) as (a & ka & Hain & Hka & Eg).
destruct (used_group_region [] None U0 A g am HWA Hu) as (rg & Hrg & Hkd & Hl & Ho & Hext & _).
assert (HC : realloc_ctx L A regs mem md g am fr n a ka rg) by (split; auto; lia).
change (ms_segs B2) with ubs2segs. change (frame_ptr am 0 fr) with (pp am fr).
exact (realloc_mreal L A regs mem md g am fr n a ka rg HC (O1 _ _ _ _ _ _ _ _ _ _ _ _ HC)
(O2 _ _ _ _ _ _ _ _ _ _ _ _ HC) (O3 MALLOC FREE MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ HC)).
Qed.
End b.
