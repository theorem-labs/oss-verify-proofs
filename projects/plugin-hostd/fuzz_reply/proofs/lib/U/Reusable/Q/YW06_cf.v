(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN03 YN02_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW01_cf YW00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN2b YN25_cf YN26_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW03_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN0b_cf YN07_cf YN0a_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW0e_cf YY00_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B2 := src0_msyms (only parsing).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition memcpy_spec : Prop :=
forall (bs : list byte) (d s n : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = n ->
bv_unsigned n = Z.of_nat (length bs) ->
rdn src0segs mem s (length bs) = Some bs ->
store_ok src0segs mem d (length bs) = true ->
bv_unsigned d + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned s + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned d + Z.of_nat (length bs) <= bv_unsigned s
\/ bv_unsigned s + Z.of_nat (length bs) <= bv_unsigned d) ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 src0_A_memcpy) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv ->
r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs' r = getr regs r).
Lemma z2bv_ne : forall a b, bv_unsigned (Z_to_bv 64 a) <> bv_unsigned (Z_to_bv 64 b) -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b H E. apply H. rewrite E. reflexivity. Qed.
Definition malloc_impl_realizes : Prop :=
forall L A regs mem md n,
call_pre B2 (MRx B2) L A regs mem md ->
getr regs 1 <> Z_to_bv 64 src0_A_malloc ->
getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
mreal_cf src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_libc_malloc_impl) mem (seg_rom src0segs)) md)
(malloc n A) (malloc_leaf B2 (MRx B2) L A regs mem md n).
Definition free_impl_realizes : Prop :=
forall L A regs mem md p n,
call_pre B2 (MRx B2) L A regs mem md ->
getr regs 1 <> Z_to_bv 64 src0_A_free ->
In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
mreal_cf src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_libc_free) mem (seg_rom src0segs)) md)
(free (Some p) A) (free_leaf B2 (MRx B2) L A regs mem md p n).
Record realloc_ctx (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region) : Prop := RCX {
rc_pre : call_pre_k B2 (MRx B2) REALLOC_STACK L A regs mem md;
rc_used : usedX [] A g am;
rc_fr : ss_fr (nth_slot am 0) = Some fr;
rc_kind : fr_kind fr = FUser;
rc_in : In (frame_ptr am 0 fr, fr_n fr) (user_blocks A);
rc_a0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am 0 fr));
rc_a1 : getr regs 11 = Z_to_bv 64 n;
rc_n : 0 <= n < 2 ^ 62;
rc_63 : am_sc am = 63;
rc_last : am_last am = 0;
rc_area : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka);
rc_rg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg }.
Section c.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hu := rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hfr := rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hk := rc_kind _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hin := rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Ha0 := rc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Ha1 := rc_a1 _ _ _ _ _ _ _ _ _ _ _ _ HC.
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
Lemma Hn62 : n < 2 ^ 62. Proof. lia. Qed.
Hypothesis Hth : MMAP_THRESHOLD <= n.
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
st_ok src0segs (Er gd err) (S0 rcr) (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)).
Hypothesis OBL_eq : forall gd err ms1, 0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok src0segs (Er gd err) (S1 rcr) ms1 -> frame_of (Er gd err) (entry_mem rcr) mem (ms_mem ms1) ->
old_len am = NEEDED ->
SR_cfv src0segs (mkCfg ms1 md) (realloc_leaf B2 (MRx B2) L A regs mem md pp (fr_n fr) n (Some pp, A_eq A g am fr n)).
Hypothesis OBL_node : forall gd err ms1, 0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok src0segs (Er gd err) (S1 rcr) ms1 -> frame_of (Er gd err) (entry_mem rcr) mem (ms_mem ms1) ->
old_len am <> NEEDED ->
SR_cfv src0segs (mkCfg ms1 md)
(fun c1 => knode_cf src0segs c1 (KMremap (rid am) (old_len am) NEEDED) A
(fun z c2 => mreal_cf src0segs c2
(if negb (z =? 0) then IRet (Some (p_ok A am fr n), A_ok A g am fr n) else realloc_move pp n A)
(realloc_leaf B2 (MRx B2) L A regs mem md pp (fr_n fr) n))).
Theorem realloc_mreal :
mreal_cf src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) md)
(realloc (Some pp) n A)
(realloc_leaf B2 (MRx B2) L A regs mem md pp (fr_n fr) n).
Proof.
destruct Hmd as (Hh & Hlz & _). destruct OBL_entry as (gd & err & Hgd & Herr & HS0).
rewrite tree. destruct (old_len am =? NEEDED) eqn:E.
- apply Z.eqb_eq in E. apply mreal_cf_leaf.
eapply SR_cfv_bind; [exact (S1_run (Er gd err) _ md Hh Hlz rcr HS0)|].
intros c' (ms1 & -> & HS1 & HF1). exact (OBL_eq gd err ms1 Hgd Herr HS1 HF1 E).
- apply Z.eqb_neq in E. apply (mreal_cf_ask src0segs).
eapply SR_cfv_bind; [exact (S1_run (Er gd err) _ md Hh Hlz rcr HS0)|].
intros c' (ms1 & -> & HS1 & HF1). exact (OBL_node gd err ms1 Hgd Herr HS1 HF1 E).
Qed.
End c.
Definition OBL_entry_T : Prop :=
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg),
MMAP_THRESHOLD <= n ->
exists gd err, 0 <= gd < 2 ^ 64 /\ 0 <= err < 2 ^ 32 /\
st_ok src0segs (Er L regs g am fr n a rg gd err) (S0 (rcr am fr)) (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)).
Definition OBL_eq_T : Prop :=
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg),
MMAP_THRESHOLD <= n -> forall gd err ms1,
0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok src0segs (Er L regs g am fr n a rg gd err) (S1 (rcr am fr)) ms1 ->
frame_of (Er L regs g am fr n a rg gd err) (entry_mem (rcr am fr)) mem (ms_mem ms1) ->
old_len am = needed fr n ->
SR_cfv src0segs (mkCfg ms1 md) (realloc_leaf B2 (MRx B2) L A regs mem md (pp am fr) (fr_n fr) n (Some (pp am fr), A_eq A g am fr n)).
Definition OBL_node_T : Prop :=
OBL_fb_gen ->
forall L A regs mem md g am fr n a ka rg (HC : realloc_ctx L A regs mem md g am fr n a ka rg),
MMAP_THRESHOLD <= n -> forall gd err ms1,
0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 ->
st_ok src0segs (Er L regs g am fr n a rg gd err) (S1 (rcr am fr)) ms1 ->
frame_of (Er L regs g am fr n a rg gd err) (entry_mem (rcr am fr)) mem (ms_mem ms1) ->
old_len am <> needed fr n ->
SR_cfv src0segs (mkCfg ms1 md)
(fun c1 => knode_cf src0segs c1 (KMremap (rid am) (old_len am) (needed fr n)) A
(fun z c2 => mreal_cf src0segs c2
(if negb (z =? 0) then IRet (Some (p_ok A am fr n), A_ok A g am fr n) else realloc_move (pp am fr) n A)
(realloc_leaf B2 (MRx B2) L A regs mem md (pp am fr) (fr_n fr) n))).
Lemma realloc_ctx_of L A regs mem md p nold n g am idx fr :
call_pre_k B2 (MRx B2) REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
0 <= n < 2 ^ 62 ->
usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
fr_n fr = nold -> p = frame_ptr am idx fr -> am_sc am = 63 ->
idx = 0 /\ exists a ka rg, realloc_ctx L A regs mem md g am fr n a ka rg.
Proof using.
intros PRE Hin Ha0 Ha1 Hrange Hu Hidx Hfr Hk Hn Hp H63.
pose proof (MRx_MRc _ _ _ _ _ (proj1 PRE)) as MR. pose proof (mc_wf _ _ _ _ _ MR) as HWA.
destruct (rm_shape U0 A g am 0 HWA Hu H63) as (Hlast & _).
assert (idx = 0) as -> by lia. split; [reflexivity|]. subst p nold.
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (meta_in_area A g (MUsed am) HWA (In_of_mlookup _ _ _ Mg)) as (a & ka & Hain & Hka & Eg).
destruct (used_group_region [] None U0 A g am HWA Hu) as (rg & Hrg & Hkd & Hl & Ho & Hext & _).
exists a, ka, rg. split; auto.
Qed.
Theorem src0_realloc_realizes :
OBL_fb_gen -> OBL_entry_T -> OBL_eq_T -> OBL_node_T ->
forall pc L A regs mem md p nold n g am idx fr,
ms_realloc B2 = Some pc ->
call_pre_k B2 (MRx B2) REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
MMAP_THRESHOLD <= n < 2 ^ 62 ->
usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
fr_n fr = nold -> p = frame_ptr am idx fr -> am_sc am = 63 ->
mreal_cf (ms_segs B2) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B2))) md)
(realloc (Some p) n A)
(realloc_leaf B2 (MRx B2) L A regs mem md p nold n).
Proof using.
intros FB O1 O2 O3 pc L A regs mem md p nold n g am idx fr Hpc PRE Hin Ha0 Ha1 Hrange Hu Hidx Hfr Hk Hn Hp H63.
cbn [ms_realloc src0_msyms] in Hpc. injection Hpc as <-.
destruct (realloc_ctx_of L A regs mem md p nold n g am idx fr PRE Hin Ha0 Ha1 ltac:(unfold MMAP_THRESHOLD in Hrange; lia) Hu Hidx Hfr Hk Hn Hp H63)
as (-> & a & ka & rg & HC).
subst p nold. change (ms_segs B2) with src0segs. change (frame_ptr am 0 fr) with (pp am fr).
exact (realloc_mreal L A regs mem md g am fr n a ka rg HC (proj1 Hrange) (O1 _ _ _ _ _ _ _ _ _ _ _ _ HC (proj1 Hrange))
(O2 _ _ _ _ _ _ _ _ _ _ _ _ HC (proj1 Hrange)) (O3 FB _ _ _ _ _ _ _ _ _ _ _ _ HC (proj1 Hrange))).
Qed.
End b.
