(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YP14 YI08 YI0c YI0g YI0f YI0d YI0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition GL_LOOP : Z := Eval vm_compute in (ubs2_A_get_leave_node_index + 0x18).
Definition GL_XORI : Z := Eval vm_compute in (ubs2_A_get_leave_node_index + 0x64).
Definition GL_RET : Z := Eval vm_compute in (ubs2_A_get_leave_node_index + 0x88).
Definition GL_KEEP : list reg := [1; 2; 3; 4; 6; 7; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition gn_lits (ocut : option Z) (leaf : Z) : list (option Z) :=
[None; None; None; None; None; None; None; ocut; None; Some leaf].
Definition gn_regs : list sv := sr_set (sr_set sr_atoms 13%bv (SLit 2)) 14%bv (SLit 3).
Definition ss_ge : sstate :=
mkSS ubs2_A_get_leave_node_index sr_atoms [] None
(mkFacts [ (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (11%nat, mkAF 4096 (CEIL_MAX - 12) 2) ] [] []).
Definition ss_lf : sstate :=
mkSS GL_LOOP gn_regs [ YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (gn_lits None 1)) ] None
(mkFacts [ (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (40%nat, mkAF 0 255 0) ] [] []).
Definition ss_ndx (cut : Z) : sstate :=
mkSS GL_LOOP gn_regs
[ YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (gn_lits (Some cut) 0));
YQ0b.mkRegion (Some 11%nat) 0 12 0 0 [mkChunk 0 (CData 0 0 12)] ] None
(mkFacts [ (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (11%nat, mkAF 4096 (CEIL_MAX - 12) 2);
(12%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
(32%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (33%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4);
(42%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0) ] []
[ (SAlu ALU_XOR (SOff 10 16) (SLit (-1)), SOff 42 0) ]).
Lemma troot_in_nodes : forall t, tree_full t -> exists m, In m (tree_nodes t) /\ troot t = tn_addr m.
Proof.
intros [|m|m l r] H; cbn in H |- *; [destruct H | |]; exists m; split; [left; reflexivity | reflexivity | left; reflexivity | reflexivity].
Qed.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Definition glni_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (t : tree) (pix : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs 1) -> frm_zero (@fp_csr fx) ->
getr regs 10 = Z_to_bv 64 (troot t) -> getr regs 11 = Z_to_bv 64 pix ->
tree_at ubs2segs memc t -> tree_full t ->
(forall m, In m (tree_nodes t) -> tnode_wf m /\ 4096 <= tn_addr m /\ tn_addr m + NODE_SIZE <= alloc_ceiling /\ tn_addr m mod 16 = 0 /\
(tn_addr m + NODE_SIZE <= pix \/ pix + 12 <= tn_addr m)) ->
4096 <= pix -> pix + 12 <= alloc_ceiling -> pix mod 4 = 0 ->
(forall j, 0 <= j < 12 -> exists b, mbyte ubs2segs memc (pix + j) = Some b) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_get_leave_node_index) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists (fx' : FPState) regs2 m,
c' = mkCfg (@mkst fx' regs2 (getr regs 1) memc (seg_rom ubs2segs)) mdc /\ frm_zero (@fp_csr fx') /\
fregs_preserved (@fp_regs fx) (@fp_regs fx') /\ regs_preserved regs regs2 /\
In m (tree_leaves t) /\ getr regs2 10 = Z_to_bv 64 (tn_cidx m)).
Section d.
Variables (regs0 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (pix : Z).
Hypothesis Hh : m_halted mdc = None. Hypothesis Hlz : m_vm_lazy mdc = [].
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hp0 : 4096 <= pix. Hypothesis Hp1 : pix + 12 <= alloc_ceiling. Hypothesis Hp4 : pix mod 4 = 0.
Hypothesis Hpres : forall j, 0 <= j < 12 -> exists b, mbyte ubs2segs memc (pix + j) = Some b.
Definition gl_at (regs1 : bvmap 5 word) (a : Z) : Prop :=
getr regs1 10 = Z_to_bv 64 a /\ getr regs1 11 = Z_to_bv 64 pix /\ getr regs1 12 = Z_to_bv 64 (2 ^ 64 - 1 - pix) /\
getr regs1 13 = Z_to_bv 64 2 /\ getr regs1 14 = Z_to_bv 64 3 /\ (forall rr, In rr GL_KEEP -> getr regs1 rr = getr regs0 rr).
Lemma gl_leaf : forall (fy : FPState) (regs1 : bvmap 5 word) (n : tnode) (c0 c1 : Z),
gl_at regs1 (tn_addr n) ->
obj_at ubs2segs memc (tn_addr n) LAY_Node (node_vals c0 c1 n 1) -> length (tn_mean n) = 3%nat -> 0 <= tn_cidx n < 256 ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
SR ubs2segs (mkCfg (@mkst fy regs1 (Z_to_bv 64 GL_LOOP) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs', c' = mkCfg (@mkst fy regs' (getr regs0 1) memc (seg_rom ubs2segs)) mdc /\
(forall rr, In rr GL_KEEP -> getr regs' rr = getr regs0 rr) /\ getr regs' 10 = Z_to_bv 64 (tn_cidx n)).
Proof.
intros fy regs1 n c0 c1 (G10 & G11 & G12 & G13 & G14 & GK) Hobj Hlen Hcx Hn0 Hn1 Hn16.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
set (E := Ereg regs1 (map (Z_to_bv 64) (node_vals c0 c1 n 1) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n 1) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 n 1 Hlen) in Hobj, HV.
assert (U10 : bv_unsigned (ew E 10) = tn_addr n) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E 40) = tn_cidx n) by (rewrite (HV 8%nat (tn_cidx n) eq_refl : ew E 40 = _); apply unsigned_lit_small; lia).
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros k Hk; rewrite !ew_Ereg_lt by exact Hk; reflexivity | reflexivity]. }
assert (HS : @st_ok ubs2segs fy E ss_lf (@mkst fy regs1 (Z_to_bv 64 GL_LOOP) memc (seg_rom ubs2segs))).
{ unfold ss_lf, gn_regs. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G13; reflexivity]
| intros X; discriminate X | rewrite G14; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ memc 10 (tn_addr n)); [exact U10 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 10 (destruct j as [|j]; [cbn in Hj |- *; congruence|]). destruct j; cbn in Hj; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, U40. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to ubs2tbl_ok HS GL_RET.
lazymatch type of Hms with msteps _ _ (@mkst _ ?rg ?pc ?mm _) =>
pose proof (pure_ret ubs2segs ubs2tbl ubs2tbl_ok E _ _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hms) as Hms2;
change (ms_regs (@mkst fy rg pc mm (seg_rom ubs2segs))) with rg in Hms2;
change (ms_mem (@mkst fy rg pc mm (seg_rom ubs2segs))) with mm in Hms2;
assert (RK : forall rr, In rr GL_KEEP -> getr rg rr = getr regs1 rr)
by (exact (regs_kept_of_st_ok ubs2segs E _ _ regs1 [] GL_KEEP HS EA0 ltac:(vm_compute; reflexivity)));
assert (R10 : getr rg 10 = Z_to_bv 64 (tn_cidx n))
by (jreg HS (10%bv:reg) as X; eapply eq_trans; [exact X|]; exact (HV 8%nat (tn_cidx n) eq_refl));
assert (Hpc : v_jalr (getr rg 1) 0 = getr regs0 1)
by (rewrite (RK 1%bv ltac:(left; reflexivity)), (GK 1%bv ltac:(left; reflexivity)); exact Hra);
eapply (SR_msteps ubs2segs _ _ mdc _ Hh Hlz Hms2); apply SR_ret;
exists rg; split; [rewrite Hpc; reflexivity|]; split; [intros rr Hrr; rewrite (RK rr Hrr); apply GK; exact Hrr | exact R10]
end.
Qed.
Lemma gl_node : forall (fy : FPState) (regs1 : bvmap 5 word) (n : tnode) (c0 c1 : Z),
frm_zero (@fp_csr fy) -> gl_at regs1 (tn_addr n) ->
obj_at ubs2segs memc (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> length (tn_mean n) = 3%nat -> 0 <= tn_cut n <= 2 ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
(tn_addr n + NODE_SIZE <= pix \/ pix + 12 <= tn_addr n) ->
4096 <= c0 -> c0 + NODE_SIZE <= alloc_ceiling -> c0 mod 16 = 0 ->
4096 <= c1 -> c1 + NODE_SIZE <= alloc_ceiling -> c1 mod 16 = 0 ->
SR ubs2segs (mkCfg (@mkst fy regs1 (Z_to_bv 64 GL_LOOP) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists (fy' : FPState) regs', c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 GL_LOOP) memc (seg_rom ubs2segs)) mdc /\
frm_zero (@fp_csr fy') /\ fregs_preserved (@fp_regs fy) (@fp_regs fy') /\ (gl_at regs' c0 \/ gl_at regs' c1)).
Proof.
intros fy regs1 n c0 c1 Hfrm (G10 & G11 & G12 & G13 & G14 & GK) Hobj Hlen Hcut Hn0 Hn1 Hn16 Hsep Q0 Q1 Q16 R0 R1 R16.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (bytes_of_present ubs2segs memc pix 12 Hpres) as (bp & Lbp & Hbp).
set (E0 := EregB regs1 (map (Z_to_bv 64) (node_vals c0 c1 n 0 ++ [2 ^ 64 - 1 - (tn_addr n + 16)])) [bp]).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs1 rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n 0 ++ [2 ^ 64 - 1 - (tn_addr n + 16)]) j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E0; apply EregB_vals; exact Hj).
rewrite (node_vals_expand c0 c1 n 0 Hlen) in Hobj, HV.
assert (HVn : forall j v, nth_error [c0; c1; nth 0 (tn_mean n) 0; nth 1 (tn_mean n) 0; nth 2 (tn_mean n) 0; tn_imin n; tn_imax n; tn_cut n; tn_cidx n; 0] j = Some v ->
ew E0 (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HV. rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]. }
assert (A32 : ew E0 32 = Z_to_bv 64 c0) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 c1) by (apply (HV 1%nat); reflexivity).
assert (A42 : ew E0 42 = Z_to_bv 64 (2 ^ 64 - 1 - (tn_addr n + 16))) by (apply (HV 10%nat); reflexivity).
assert (A10 : ew E0 10 = Z_to_bv 64 (tn_addr n)) by (rewrite (HE0 10%nat 10%bv eq_refl); exact G10).
assert (U10 : bv_unsigned (ew E0 10) = tn_addr n) by (rewrite A10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E0 11) = pix) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E0 12) = 2 ^ 64 - 1 - pix) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = c0) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = c1) by (rewrite A33; apply unsigned_lit_small; lia).
assert (U42 : bv_unsigned (ew E0 42) = 2 ^ 64 - 1 - (tn_addr n + 16)) by (rewrite A42; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok ubs2segs fy E0 (ss_ndx (tn_cut n)) (@mkst fy regs1 (Z_to_bv 64 GL_LOOP) memc (seg_rom ubs2segs))).
{ unfold ss_ndx, gn_regs. apply entry_st_ok_env.
- apply regs_ok_pin; [apply regs_ok_pin; [subst E0; apply regs_ok_EregB | intros X; discriminate X | rewrite G13; reflexivity]
| intros X; discriminate X | rewrite G14; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj_gen ubs2segs _ memc 10 (tn_addr n)); [exact U10 | lia | lia | exact Hobj | reflexivity | exact HVn | | intros k Hk; lia].
intros j z Hj. do 10 (destruct j as [|j]; [cbn in Hj |- *; congruence|]). destruct j; cbn in Hj; discriminate Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U11.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length bp)) by (rewrite Lbp; reflexivity).
apply (chunk_ok_data ubs2segs E0 memc _ 0 0 bp ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hbp. rewrite <- Lbp. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U10, U11.
repeat split; try exact I; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I|]].
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, U11, U12, U32, U33, U42.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [alias_ok]. split; [|exact I]. apply U_inj.
rewrite (U_not_off E0 10 (tn_addr n) 16 A10), (U_atom E0 42 _ A42) by lia. reflexivity. }
pose proof (st_ok_enterF ubs2segs fy 64 E0 _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
clear HS0.
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs1 rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HEf : forall r : reg, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; subst E; apply ew_fregs_at).
assert (HE32 : ew E 32 = Z_to_bv 64 c0) by (rewrite HEE by lia; exact A32).
assert (HE33 : ew E 33 = Z_to_bv 64 c1) by (rewrite HEE by lia; exact A33).
assert (Hk : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by lia.
destruct Hk as [Hk|[Hk|Hk]]; rewrite Hk in HS.
all: pureF_to ubs2tbl_ok HS GL_XORI.
all: jregF HS (15%bv:reg) as Hq15; rewrite fcmp_denot in Hq15.
all: lazymatch type of Hq15 with getr _ _ = (if ?bexp then w1 else w0) =>
destruct bexp;
[ pose proof (st_okF_pin_reg ubs2segs E _ _ 15%bv (SLit 1) HS ltac:(intros HH0; discriminate HH0) Hq15) as HS'
| pose proof (st_okF_pin_reg ubs2segs E _ _ 15%bv (SLit 0) HS ltac:(intros HH0; discriminate HH0) Hq15) as HS' ]
end.
all: clear HS; rename HS' into HS.
all: match type of HS with st_okF _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
all: pureF_to ubs2tbl_ok HS GL_LOOP.
all: cbn [ms_mem mkst] in Hmem, Hsh0; rewrite Hmem in Hsh0.
all: eapply (SR_msteps ubs2segs _ _ mdc _ Hh Hlz); [eapply msteps_trans; [exact Hms | exact Hms0]|].
all: rewrite Hsh0; apply SR_ret.
all: exists (fp_of ms0), (ms_regs ms0).
all: split; [reflexivity|].
all: split; [exact (st_okF_frm ubs2segs E _ _ HS)|].
all: split; [intros rr Hrr; cbn [fp_regs fp_of]; exact (st_okF_fregs_kept ubs2segs E _ _ 64 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) rr Hrr)|].
all: pose proof (st_okF_regs_kept ubs2segs E _ _ regs1 GL_KEEP HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as RK.
all: jregF HS (10%bv:reg) as R10; jregF HS (11%bv:reg) as R11; jregF HS (12%bv:reg) as R12; jregF HS (13%bv:reg) as R13; jregF HS (14%bv:reg) as R14.
all: first [left; split; [rewrite R10, HE32; reflexivity|] | right; split; [rewrite R10, HE33; reflexivity|]].
all: split; [rewrite R11, (HE 11%nat 11%bv eq_refl); exact G11|].
all: split; [rewrite R12, (HE 12%nat 12%bv eq_refl); exact G12|].
all: split; [exact R13|]. all: split; [exact R14|].
all: intros rr Hrr; rewrite (RK rr Hrr); apply GK; exact Hrr.
Qed.
Lemma gl_run : forall (t : tree) (fy : FPState) (regs1 : bvmap 5 word),
frm_zero (@fp_csr fy) -> fregs_preserved (@fp_regs fx) (@fp_regs fy) -> gl_at regs1 (troot t) ->
tree_at ubs2segs memc t -> tree_full t ->
(forall m, In m (tree_nodes t) -> tnode_wf m /\ 4096 <= tn_addr m /\ tn_addr m + NODE_SIZE <= alloc_ceiling /\ tn_addr m mod 16 = 0 /\
(tn_addr m + NODE_SIZE <= pix \/ pix + 12 <= tn_addr m)) ->
SR ubs2segs (mkCfg (@mkst fy regs1 (Z_to_bv 64 GL_LOOP) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists (fx' : FPState) regs2 m,
c' = mkCfg (@mkst fx' regs2 (getr regs0 1) memc (seg_rom ubs2segs)) mdc /\ frm_zero (@fp_csr fx') /\
fregs_preserved (@fp_regs fx) (@fp_regs fx') /\ (forall rr, In rr GL_KEEP -> getr regs2 rr = getr regs0 rr) /\
In m (tree_leaves t) /\ getr regs2 10 = Z_to_bv 64 (tn_cidx m)).
Proof.
induction t as [|n|n l IHl r IHr]; intros fy regs1 Hfrm Hfp Hat Ht Hfull Hns.
- destruct Hfull.
- cbn [tree_at] in Ht. destruct Ht as (Hnz & Hlen & c0 & c1 & Hobj).
destruct (Hns n ltac:(left; reflexivity)) as ((_ & Hcx & _) & N0 & N1 & N16 & _).
cbn [troot] in Hat.
eapply SR_mono; [exact (gl_leaf fy regs1 n c0 c1 Hat Hobj Hlen Hcx N0 N1 N16)|].
cbv beta. intros c' (rg & -> & RK & R10). exists fy, rg, n.
split; [reflexivity|]. split; [exact Hfrm|]. split; [exact Hfp|]. split; [exact RK|]. split; [left; reflexivity | exact R10].
- cbn [tree_at] in Ht. fold (tree_at ubs2segs) in Ht. destruct Ht as (Hnz & Hlen & Hobj & Hl & Hr). destruct Hfull as [Hfl Hfr].
destruct (Hns n ltac:(left; reflexivity)) as ((Hcut & _) & N0 & N1 & N16 & Nsep).
assert (Hnl : forall m, In m (tree_nodes l) -> In m (tree_nodes (TNode n l r))) by (intros m Hm; right; apply in_app_iff; left; exact Hm).
assert (Hnr : forall m, In m (tree_nodes r) -> In m (tree_nodes (TNode n l r))) by (intros m Hm; right; apply in_app_iff; right; exact Hm).
destruct (troot_in_nodes l Hfl) as (ml & Hml & Erl). destruct (troot_in_nodes r Hfr) as (mr & Hmr & Err).
destruct (Hns ml (Hnl ml Hml)) as (_ & L0 & L1 & L16 & _). destruct (Hns mr (Hnr mr Hmr)) as (_ & Q0 & Q1 & Q16 & _).
cbn [troot] in Hat.
eapply SR_bind.
{ exact (gl_node fy regs1 n (troot l) (troot r) Hfrm Hat Hobj Hlen Hcut N0 N1 N16 Nsep
ltac:(rewrite Erl; exact L0) ltac:(rewrite Erl; exact L1) ltac:(rewrite Erl; exact L16)
ltac:(rewrite Err; exact Q0) ltac:(rewrite Err; exact Q1) ltac:(rewrite Err; exact Q16)). }
cbv beta. intros c' (fy1 & rg & -> & Hfrm1 & Hfp1 & [Ga|Ga]).
+ eapply SR_mono.
{ apply (IHl fy1 rg Hfrm1 (fun rr Hrr => eq_trans (Hfp1 rr Hrr) (Hfp rr Hrr)) Ga Hl Hfl (fun m Hm => Hns m (Hnl m Hm))). }
cbv beta. intros c'' (fx' & rg' & m & -> & Hf' & Hfp' & RK' & Hm & R10). exists fx', rg', m.
split; [reflexivity|]. split; [exact Hf'|]. split; [exact Hfp'|]. split; [exact RK'|].
split; [cbn [tree_leaves]; apply in_app_iff; left; exact Hm | exact R10].
+ eapply SR_mono.
{ apply (IHr fy1 rg Hfrm1 (fun rr Hrr => eq_trans (Hfp1 rr Hrr) (Hfp rr Hrr)) Ga Hr Hfr (fun m Hm => Hns m (Hnr m Hm))). }
cbv beta. intros c'' (fx' & rg' & m & -> & Hf' & Hfp' & RK' & Hm & R10). exists fx', rg', m.
split; [reflexivity|]. split; [exact Hf'|]. split; [exact Hfp'|]. split; [exact RK'|].
split; [cbn [tree_leaves]; apply in_app_iff; right; exact Hm | exact R10].
Qed.
End d.
Theorem ubs2_get_leave_node_index : glni_spec.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs t pix HJ Hra Hfrm G10 G11 Ht Hfull Hns Hp0 Hp1 Hp4 Hpres.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
destruct (troot_in_nodes t Hfull) as (m0 & Hm0 & Ert).
destruct (Hns m0 Hm0) as (_ & M0 & M1 & M16 & _).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U10 : bv_unsigned (ew E 10) = tn_addr m0) by (rewrite (HE 10%nat 10%bv eq_refl), G10, Ert; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = pix) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HE11 : ew E 11 = Z_to_bv 64 pix) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HS : st_ok ubs2segs E ss_ge (mkst regs (Z_to_bv 64 ubs2_A_get_leave_node_index) memc (seg_rom ubs2segs))).
{ unfold ss_ge. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- first [exact I | cbn; exact I | constructor].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, U11.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. repeat split; lia. }
pure_to ubs2tbl_ok HS GL_LOOP.
lazymatch type of Hms with msteps _ _ (@mkst _ ?rg ?pc ?mm _) =>
assert (RK : forall rr, In rr GL_KEEP -> getr rg rr = getr regs rr)
by (exact (regs_kept_of_st_ok ubs2segs E _ _ regs [] GL_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)));
assert (Hat : gl_at regs pix rg (troot t));
[ split; [jreg HS (10%bv:reg) as X; eapply eq_trans; [exact X|]; rewrite (HE 10%nat 10%bv eq_refl); exact G10|];
split; [jreg HS (11%bv:reg) as X; eapply eq_trans; [exact X|]; rewrite (HE 11%nat 11%bv eq_refl); exact G11|];
split; [refine (getr_of_U ubs2segs E _ (mkst rg pc mm (seg_rom ubs2segs)) 12%bv _ HS _); eval_sr_get; apply (U_not E 11 pix HE11); lia|];
split; [jreg HS (13%bv:reg) as X; exact X|];
split; [jreg HS (14%bv:reg) as X; exact X|];
exact RK
| ];
eapply (SR_msteps ubs2segs _ _ mdc _ Hh Hl Hms);
eapply SR_mono;
[ exact (gl_run regs memc mdc pix Hh Hl Hra Hp0 Hp1 Hp4 Hpres t fx rg Hfrm (fun rr _ => eq_refl) Hat Ht Hfull Hns) | ];
cbv beta; intros c' (fx' & rg' & m & -> & Hf' & Hfp' & RK' & Hm & R10);
exists fx', rg', m;
split; [reflexivity|]; split; [exact Hf'|]; split; [exact Hfp'|];
split; [apply regs_preserved_intro_g; apply RK'; cbv; auto 30 | split; [exact Hm | exact R10]]
end.
Qed.
End S.
End b.
