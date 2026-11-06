(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI07
YI1e YI1i YI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
YI3h YI4v YI4r YI4s YI4w YI3s YP12.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_DLT : Z := 0x1411c.
Lemma U_mul_lit : forall E n c i,
ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 32 -> 0 <= c < 2 ^ 16 ->
sv_denot E (SMd M_MUL (SLit c) (SOff n 0)) = Z_to_bv 64 (c * i).
Proof.
intros E n c i Hn Hi Hc. rewrite denot_lit_U. f_equal.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit. rewrite (U_atom E n i Hn) by lia.
rewrite (zcanon_id c) by (unfold M64; lia). apply zcanon_id. unfold M64; nia.
Qed.
Lemma U_add2 : forall E n m x y,
bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros E n m x y Hn Hm Hx Hy Hxy. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia). apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_add_shl : forall E n m b x k p,
2 ^ k = p -> bv_unsigned (ew E m) = b -> bv_unsigned (ew E n) = x -> 0 <= b -> 0 <= x < 2 ^ 32 -> 0 <= k <= 4 -> b + x * p < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SLL (SOff n 0) (SLit k))) = Z_to_bv 64 (b + x * p).
Proof.
intros E n m b x k p Hp Hm Hn Hb Hx Hk Hbx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hm, Hn, !Z.add_0_r.
assert (Hk2 : 0 < 2 ^ k <= 16) by (split; [apply Z.pow_pos_nonneg; lia | change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia]).
rewrite (zcanon_id b), (zcanon_id x) by (unfold M64; lia).
replace (Z.land (zcanon k) 63) with k.
2:{ rewrite zcanon_id by (unfold M64; lia). assert (X : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
destruct X as [-> |[-> |[-> |[-> | ->]]]]; reflexivity. }
rewrite Z.shiftl_mul_pow2 by lia. rewrite Hp. rewrite (zcanon_id (x * p)) by (unfold M64; nia). apply zcanon_id. unfold M64; nia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section l.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis HW1 : 1 <= W. Hypothesis HWN : exists h, 1 <= h /\ N = W * h.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hdisj : flt + 4 * M <= fimg \/ fimg + N <= flt.
Hypothesis Hfro : flt + 4 * M <= SRC2_RO9 \/ SRC2_RO9 + 8 <= flt.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbf : forall i, 0 <= i < 4 * M -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (flt + i).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis HtreeD : tree_at src2segs memD t. Hypothesis Hfull : tree_full t. Hypothesis Hwft : tree_forall tnode_wf t.
Hypothesis Hnodes : forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Hypothesis Hntb : forall b, In b (tree_blocks t) -> In b (blocks Lq Aq).
Hypothesis Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n.
Hypothesis Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * M <= tn_addr n.
Hypothesis HslotW : slot regs0 memD SL_64 W.
Hypothesis Hro0 : src2_rgb_rodata_ok mem0.
Local Notation memIv := (memI N fmt memD flt fimg).
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5136 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 158.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte src2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma flt_writable : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, flt <= a < flt + 4 * M -> writable_at src2segs m a.
Proof.
intros m HJ a Ha. replace a with (flt + (a - flt)) by lia. apply (present_writable src2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) (a - flt) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin ltac:(lia))).
Qed.
Lemma fimg_writable : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, fimg <= a < fimg + N -> writable_at src2segs m a.
Proof.
intros m HJ a Ha. replace a with (fimg + (a - fimg)) by lia. apply (present_writable src2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq fimg N (a - fimg) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia))).
Qed.

Definition ss_H3 : sstate :=
mkSS PC_DIH (sr_set (sr_set sr_atoms 26%bv (SLit 3)) 16%bv (SLit 4)) [] None
(mkFacts [ (14%nat, mkAF 0 RGB_NMAX 0); (11%nat, mkAF 0 (2^20) 0); (25%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition ss_H4x : sstate :=
mkSS PC_DIH (sr_set (sr_set sr_atoms 26%bv (SLit 4)) 16%bv (SLit 4))
[ YQ0b.mkRegion (Some 32%nat) 0 16 0 0 [mkChunk 0 (CData 0 0 16)]; YQ0b.mkRegion (Some 33%nat) 0 1 0 1 [] ] None
(mkFacts [ (14%nat, mkAF 0 RGB_NMAX 0); (11%nat, mkAF 0 (2^20) 0); (10%nat, mkAF 4096 CEIL_MAX 2); (25%nat, mkAF 4096 CEIL_MAX 0);
(32%nat, mkAF 4096 CEIL_MAX 2); (33%nat, mkAF 4096 CEIL_MAX 0) ] []
[ (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 14 0) (SLit 4)), SOff 32%nat 0); (SAlu ALU_ADD (SOff 25 0) (SOff 14 0), SOff 33%nat 0) ]).
Definition ss_H4 : sstate := mkSST PC_DIH (ss_regs ss_H4x) (sfr_atoms 64) (ss_mem ss_H4x) None (ss_facts ss_H4x).
Definition H_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 17; 19; 20; 21; 22; 23; 24; 25; 27; 28]%bv.
Definition H_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (i : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem' (skip : bool),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if skip then PC_IN else PC_CL)) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
getr regs' 30 = Z_to_bv 64 (fimg + i) /\ getr regs' 29 = Z_to_bv 64 (i + 1) /\
getr regs' 26 = Z_to_bv 64 fmt /\ getr regs' 16 = Z_to_bv 64 4 /\
(forall rr : reg, In rr H_KEEP -> getr regs' rr = getr regs rr) /\
(forall a, 0 <= a < 2 ^ 64 -> a <> fimg + i -> mbyte src2segs mem' a = mbyte src2segs mem a) /\
(skip = false -> getr regs' 9 = Z_to_bv 64 (fmt * i + 3) /\ getr regs' 31 = Z_to_bv 64 (fmt * i) /\ getr regs' 18 = Z_to_bv 64 (fmt * i)) /\
(skip = true -> getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18).
Lemma H_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 14 = Z_to_bv 64 i -> getr regs 25 = Z_to_bv 64 fimg -> getr regs 26 = Z_to_bv 64 fmt -> getr regs 16 = Z_to_bv 64 4 ->
getr regs 11 = Z_to_bv 64 (fmt * i) -> getr regs 10 = Z_to_bv 64 flt ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom src2segs)) mdq) (H_post fy regs mem i).
Proof.
intros fy regs mem i Hi HJ Hfrm G6 G21 G25 G15 G11 G10.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct Hfmt as [F3 | F4].
-
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U6 : bv_unsigned (ew E 14) = i) by (rewrite (HE 14%nat 14%bv eq_refl), G6; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = fmt * i) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; nia).
assert (U21 : bv_unsigned (ew E 25) = fimg) by (rewrite (HE 25%nat 25%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E ss_H3 (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom src2segs))).
{ unfold ss_H3. apply entry_st_ok_env.
- apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; rewrite <- F3; exact G25] | intros HH0; discriminate HH0 | cbn [sv_denot]; exact G15].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U6, U11, U21.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS PC_CL.
eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- H_post _ _ _ _ (mkCfg (@mkst _ ?rg _ _ _) _) => rename rg into regs2 end.
exists fy, regs2, mem, false. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrm|].
assert (RG : forall rr : reg, getr regs2 rr = sv_denot E (sr_get (ss_regs (fst (sym_run_toN src2segs src2tbl FUEL PC_CL ss_H3))) rr)) by (intros rr; exact (st_ok_reg src2segs E _ _ rr HS)).
match type of RG with context [ss_regs (fst ?x)] => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in RG end.
split; [rewrite (RG 30%bv); eval_sr_get; rewrite (U_add2 E 14 25 i fimg U6 U21) by lia; f_equal; lia|].
split; [rewrite (RG 29%bv); eval_sr_get; cbn [sv_denot]; rewrite U6; reflexivity|].
split; [rewrite (RG 26%bv); eval_sr_get; cbn [sv_denot]; rewrite F3; reflexivity|].
split; [rewrite (RG 16%bv); eval_sr_get; cbn [sv_denot]; reflexivity|].
split; [exact (regs_kept_of_st_ok _ _ _ _ regs _ H_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))|].
split; [intros; reflexivity|].
split; [|intros HH0; discriminate HH0].
intros _. split; [rewrite (RG 9%bv); eval_sr_get; cbn [sv_denot]; rewrite U11; reflexivity|].
split; [rewrite (RG 31%bv); eval_sr_get; rewrite (U_mul_lit E 14 3 i) by first [rewrite <- U6; symmetry; apply Z_to_bv_bv_unsigned | lia]; rewrite F3; reflexivity|].
rewrite (RG 18%bv); eval_sr_get; cbn [sv_denot]; rewrite U11, Z.add_0_r; reflexivity.
-
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 16 <= 4 * M) by (subst M; nia).
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * i)) 16 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0).
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * (fmt * i); fimg + i]) [b0]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * (fmt * i))) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 (fimg + i)) by (subst E0; apply (EregB_vals regs _ _ 1%nat); reflexivity).
assert (U6 : bv_unsigned (ew E0 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), G6; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E0 11) = fmt * i) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; nia).
assert (U21 : bv_unsigned (ew E0 25) = fimg) by (rewrite (HE0 25%nat 25%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E0 10) = flt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * (fmt * i)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = fimg + i) by (rewrite A33; apply unsigned_lit_small; lia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (HS0 : @st_ok src2segs fy E0 ss_H4x (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom src2segs))).
{ unfold ss_H4x. apply entry_st_ok_env.
- apply regs_ok_pin; [apply regs_ok_pin; [subst E0; apply regs_ok_EregB | intros HH0; discriminate HH0 | cbn [sv_denot]; rewrite <- F4; exact G25] | intros HH0; discriminate HH0 | cbn [sv_denot]; exact G15].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 16 with (Z.of_nat (length b0)) by (rewrite Lb0; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0. rewrite <- Lb0. exact Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (fimg_writable mem HJ); lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U32, U33. split; [|exact (conj I I)]. split; [subst M; lia | exact I].
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U6, U11, U10, U21, U32, U33.
change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * (fmt * i)) mod 4 = 0) by (replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
repeat split; lia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok]. split; [|split; [|exact I]].
* rewrite (U_add_shl E0 14 10 flt i 4 16 eq_refl U10 U6) by lia. cbn [sv_denot]. rewrite Z.add_0_r, U32. f_equal. rewrite F4. lia.
* rewrite (U_add2 E0 25 14 fimg i U21 U6) by lia. cbn [sv_denot]. rewrite Z.add_0_r, U33. reflexivity. }
pose proof (st_ok_enterF src2segs fy 64 E0 ss_H4x _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_H4x) (ss_regs ss_H4x) (sfr_atoms 64) (ss_mem ss_H4x) (ss_resv ss_H4x) (ss_facts ss_H4x)) with ss_H4 in HS.
clear HS0. rewrite <- !HEE in U6, U11, U21, U10, U32, U33 by lia.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom src2segs))) in HJ.
assert (Hwr : forall cs1 cs2, wr_ok E [YQ0b.mkRegion (Some 32%nat) 0 16 0 0 cs1; YQ0b.mkRegion (Some 33%nat) 0 1 0 1 cs2] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros cs1 cs2. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact U33 | cbn [r_wlo r_whi]; intros a Ha; replace a with (fimg + (a - fimg)) by lia; apply Hwbg; lia | apply wr_ok_nil]. }
assert (POST : forall (ssx : sstate) (msx : machine_state) (skip : bool), st_okF src2segs E ssx msx -> ss_resv ssx = None ->
ss_pc ssx = (if skip then PC_IN else PC_CL) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) H_KEEP = true ->
sr_get (ss_regs ssx) 30%bv = SOff 33%nat 0 -> sr_get (ss_regs ssx) 29%bv = SOff 14%nat 1 ->
sr_get (ss_regs ssx) 26%bv = SLit 4 -> sr_get (ss_regs ssx) 16%bv = SLit 4 ->
(skip = false -> sr_get (ss_regs ssx) 9%bv = SOff 11%nat 3 /\ sr_get (ss_regs ssx) 31%bv = SMd M_MUL (SLit 4) (SOff 14 0) /\ sr_get (ss_regs ssx) 18%bv = SOff 11%nat 0) ->
(skip = true -> sr_get (ss_regs ssx) 9%bv = SOff 9%nat 0 /\ sr_get (ss_regs ssx) 18%bv = SOff 18%nat 0) ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem msx) mdq ->
(forall a, 0 <= a < 2 ^ 64 -> a <> fimg + i -> mbyte src2segs (ms_mem msx) a = mbyte src2segs mem a) ->
H_post fy regs mem i (mkCfg msx mdq)).
{ intros ssx msx skip HSx Hrv Hpc Hkb Q8 Q30 Q25 Q15 Qns Qsk HJx Hmb. exists (fp_of msx), (ms_regs msx), (ms_mem msx), skip.
split; [rewrite (st_okF_mkst src2segs E ssx msx HSx Hrv), Hpc; reflexivity|]. split; [exact HJx|]. split; [exact (st_okF_frm src2segs E _ _ HSx)|].
assert (RG : forall rr : reg, getr (ms_regs msx) rr = sv_denot E (sr_get (ss_regs ssx) rr)) by (intros rr; exact (st_okF_reg src2segs E ssx msx rr HSx)).
split; [rewrite (RG 30%bv), Q8; cbn [sv_denot]; rewrite Z.add_0_r, HEE, A33, Z_to_bv_bv_unsigned by lia; reflexivity|].
split; [rewrite (RG 29%bv), Q30; cbn [sv_denot]; rewrite U6; reflexivity|].
split; [rewrite (RG 26%bv), Q25; cbn [sv_denot]; rewrite F4; reflexivity|].
split; [rewrite (RG 16%bv), Q15; cbn [sv_denot]; reflexivity|].
split; [exact (st_okF_regs_kept src2segs E ssx msx _ H_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb)|].
split; [exact Hmb|].
split.
{ intros Hsk. destruct (Qns Hsk) as (Q9 & Q31 & Q18).
split; [rewrite (RG 9%bv), Q9; cbn [sv_denot]; rewrite U11, F4; reflexivity|].
split; [rewrite (RG 31%bv), Q31, (U_mul_lit E 14 4 i) by first [rewrite <- U6; symmetry; apply Z_to_bv_bv_unsigned | lia]; rewrite F4; reflexivity|].
rewrite (RG 18%bv), Q18; cbn [sv_denot]; rewrite U11, F4, Z.add_0_r; reflexivity. }
intros Hsk. destruct (Qsk Hsk) as (Q9 & Q18).
split; [rewrite (RG 9%bv), Q9; cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity|].
rewrite (RG 18%bv), Q18; cbn [sv_denot]; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity. }
jrunF_to LAWS src2tbl_ok HS HJ PC_CL. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF, HJ.
jbranchF src2tbl HS.
+
jrunF_to LAWS src2tbl_ok HS HJ PC_CL. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ. apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros _; repeat split; reflexivity | intros HH0; discriminate HH0 | exact HJ |].
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?U32, ?U33; lia). reflexivity.
+
jrunF_to LAWS src2tbl_ok HS HJ PC_IN. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ. apply SR_ret.
eapply (POST _ _ true HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros HH0; discriminate HH0 | intros _; split; reflexivity | exact HJ |].
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?U32, ?U33; lia). reflexivity.
Qed.
Definition ss_CLx : sstate :=
mkSS PC_CL sr_atoms [ YQ0b.mkRegion (Some 32%nat) 0 4 0 4 [mkChunk 0 (CData 0 0 4)] ] None
(mkFacts [ (18%nat, mkAF 0 (2^20) 0); (9%nat, mkAF 0 (2^20) 0); (10%nat, mkAF 4096 CEIL_MAX 2); (32%nat, mkAF 4096 CEIL_MAX 2) ] []
[ (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 18 0) (SLit 2)), SOff 32%nat 0) ]).
Definition ss_CL : sstate := mkSST PC_CL (ss_regs ss_CLx) (sfr_atoms 64) (ss_mem ss_CLx) None (ss_facts ss_CLx).
Definition CL_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition CL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (v e : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if v + 1 =? e then PC_D0 else PC_CL)) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
getr regs' 18 = Z_to_bv 64 (v + 1) /\
(forall rr : reg, In rr CL_KEEP -> getr regs' rr = getr regs rr) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * v <= a < flt + 4 * v + 4) -> mbyte src2segs mem' a = mbyte src2segs mem a).
Lemma CL_step : forall (fy : FPState) (regs : bvmap 5 word) mem (v e : Z),
0 <= v < e -> e < 2 ^ 20 -> 4 * v + 4 <= 4 * M ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 18 = Z_to_bv 64 v -> getr regs 9 = Z_to_bv 64 e -> getr regs 10 = Z_to_bv 64 flt ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom src2segs)) mdq) (CL_post fy regs mem v e).
Proof.
intros fy regs mem v e Hv He HvM HJ Hfrm G18 G9 G10.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (bytes_of_present src2segs mem (flt + 4 * v) 4 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0).
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * v]) [b0]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * v)) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (U18 : bv_unsigned (ew E0 18) = v) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E0 9) = e) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E0 10) = flt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * v) by (rewrite A32; apply unsigned_lit_small; lia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (HS0 : @st_ok src2segs fy E0 ss_CLx (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom src2segs))).
{ unfold ss_CLx. apply entry_st_ok_env.
- subst E0; apply regs_ok_EregB.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (flt_writable mem HJ); lia|].
apply Forall_cons; [|apply Forall_nil]. replace 4 with (Z.of_nat (length b0)) at 2 by (rewrite Lb0; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0. rewrite <- Lb0. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U9, U10, U32.
change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * v) mod 4 = 0) by (replace (flt + 4 * v) with (flt + v * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
repeat split; lia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok]. split; [|exact I].
rewrite (U_add_shl E0 18 10 flt v 2 4 eq_refl U10 U18) by lia. cbn [sv_denot]. rewrite Z.add_0_r, U32. f_equal. lia. }
pose proof (st_ok_enterF src2segs fy 64 E0 ss_CLx _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_CLx) (ss_regs ss_CLx) (sfr_atoms 64) (ss_mem ss_CLx) (ss_resv ss_CLx) (ss_facts ss_CLx)) with ss_CL in HS.
clear HS0. rewrite <- !HEE in U18, U9, U10, U32 by lia.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom src2segs))) in HJ.
assert (Hwr : forall cs, wr_ok E [YQ0b.mkRegion (Some 32%nat) 0 4 0 4 cs] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros cs. eapply wr_ok_cons_gen; [reflexivity | exact U32 | cbn [r_wlo r_whi]; intros a Ha; replace a with (flt + (a - flt)) by lia; apply Hwbf; lia | apply wr_ok_nil]. }
assert (POST : forall (ssx : sstate) (msx : machine_state) pc, st_okF src2segs E ssx msx -> ss_resv ssx = None -> ss_pc ssx = pc ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) CL_KEEP = true ->
sr_get (ss_regs ssx) 18%bv = SOff 18%nat 1 ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem msx) mdq ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * v <= a < flt + 4 * v + 4) -> mbyte src2segs (ms_mem msx) a = mbyte src2segs mem a) ->
(if v + 1 =? e then PC_D0 else PC_CL) = pc ->
CL_post fy regs mem v e (mkCfg msx mdq)).
{ intros ssx msx pc HSx Hrv Hpc Hkb Q18 HJx Hmb Hpce. exists (fp_of msx), (ms_regs msx), (ms_mem msx).
split; [rewrite (st_okF_mkst src2segs E ssx msx HSx Hrv), Hpc, Hpce; reflexivity|]. split; [exact HJx|]. split; [exact (st_okF_frm src2segs E _ _ HSx)|].
split; [rewrite (st_okF_reg src2segs E ssx msx 18%bv HSx), Q18; cbn [sv_denot]; rewrite U18; reflexivity|].
split; [exact (st_okF_regs_kept src2segs E ssx msx _ CL_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb)|].
exact Hmb. }
jrunF_to LAWS src2tbl_ok HS HJ PC_D0. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF, HJ.
jbranchF src2tbl HS;
(jrunF_to LAWS src2tbl_ok HS HJ PC_D0; [wr_ok_eval; apply Hwr|]); cbn [ms_mem mkst] in HF0, HJ;
jbranchF src2tbl HS;
(jrunF_to LAWS src2tbl_ok HS HJ PC_D0; [wr_ok_eval; apply Hwr|]); cbn [ms_mem mkst] in HF1, HJ;
jbranchF src2tbl HS.
all: lazymatch goal with Hb : branch_taken _ (sv_denot _ (SOff 18 1)) (sv_denot _ (SOff 9 0)) = ?bb |- _ =>
rewrite branch_ne_U, !U_SOff, U18, U9, Z.add_0_r, !zcanon_id in Hb by (unfold M64; lia);
first [
constr_eq bb true;
jrunF_to LAWS src2tbl_ok HS HJ PC_CL; [wr_ok_eval; apply Hwr|]; cbn [ms_mem mkst] in HF2, HJ; apply SR_ret;
eapply (POST _ _ PC_CL HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | |
destruct (Z.eqb_spec (v + 1) e); [exfalso; destruct (Z.eqb_spec (v + 1) (e + 0)); [discriminate Hb | lia] | reflexivity]]
| constr_eq bb false;
jrunF_to LAWS src2tbl_ok HS HJ PC_D0; [wr_ok_eval; apply Hwr|]; cbn [ms_mem mkst] in HF2, HJ; apply SR_ret;
eapply (POST _ _ PC_D0 HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | |
destruct (Z.eqb_spec (v + 1) e); [reflexivity | exfalso; destruct (Z.eqb_spec (v + 1) (e + 0)); [lia | discriminate Hb]]] ];
intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity
end.
Qed.
Lemma CL3_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 18 = Z_to_bv 64 (fmt * i) -> getr regs 9 = Z_to_bv 64 (fmt * i + 3) -> getr regs 10 = Z_to_bv 64 flt ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom src2segs)) mdq)
(fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_D0) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
(forall rr : reg, In rr CL_KEEP -> getr regs' rr = getr regs rr) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * (fmt * i) <= a < flt + 4 * (fmt * i) + 12) -> mbyte src2segs mem' a = mbyte src2segs mem a)).
Proof.
intros fy regs mem i Hi HJ Hfrm G18 G9 G10.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
assert (HM : 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia). assert (Hfi : 0 <= fmt * i) by nia.
set (v := fmt * i) in *. clearbody v.
eapply SR_bind; [exact (CL_step fy regs mem v (v + 3) ltac:(lia) ltac:(lia) ltac:(lia) HJ Hfrm G18 G9 G10)|].
cbv beta. intros c1 (fy1 & regs1 & mem1 & -> & HJ1 & Hfrm1 & G18a & Hk1 & Hm1).
replace (v + 1 =? v + 3) with false by (symmetry; apply Z.eqb_neq; lia).
eapply SR_bind; [exact (CL_step fy1 regs1 mem1 (v + 1) (v + 3) ltac:(lia) ltac:(lia) ltac:(lia) HJ1 Hfrm1 G18a
ltac:(rewrite (Hk1 9%bv ltac:(cbv; tauto)); exact G9) ltac:(rewrite (Hk1 10%bv ltac:(cbv; tauto)); exact G10))|].
cbv beta. intros c2 (fy2 & regs2 & mem2 & -> & HJ2 & Hfrm2 & G18b & Hk2 & Hm2).
replace (v + 1 + 1 =? v + 3) with false by (symmetry; apply Z.eqb_neq; lia).
eapply SR_mono; [exact (CL_step fy2 regs2 mem2 (v + 1 + 1) (v + 3) ltac:(lia) ltac:(lia) ltac:(lia) HJ2 Hfrm2 G18b
ltac:(rewrite (Hk2 9%bv ltac:(cbv; tauto)), (Hk1 9%bv ltac:(cbv; tauto)); exact G9)
ltac:(rewrite (Hk2 10%bv ltac:(cbv; tauto)), (Hk1 10%bv ltac:(cbv; tauto)); exact G10))|].
cbv beta. intros c3 (fy3 & regs3 & mem3 & -> & HJ3 & Hfrm3 & G18c & Hk3 & Hm3).
replace (v + 1 + 1 + 1 =? v + 3) with true by (symmetry; apply Z.eqb_eq; lia).
exists fy3, regs3, mem3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrm3|].
split; [intros rr Hrr; rewrite (Hk3 rr Hrr), (Hk2 rr Hrr); apply Hk1; exact Hrr|].
intros a Ha Hna. rewrite (Hm3 a Ha) by lia. rewrite (Hm2 a Ha) by lia. apply Hm1; [exact Ha | lia].
Qed.
Definition nd_lits (lf : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some lf].
Definition ss_D0 (lf : Z) : sstate :=
mkSS PC_D0 sr_atoms [ YQ0b.mkRegion (Some 27%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (nd_lits lf)) ] None
(mkFacts [ (27%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (31%nat, mkAF 0 (2^20) 0); (10%nat, mkAF 4096 CEIL_MAX 2) ] [] []).
Definition D0_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30]%bv.
Lemma D0_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z) (n : tnode) (c0 c1 lf : Z),
0 <= i < N -> (lf = 0 \/ lf = 1) ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq ->
getr regs 27 = Z_to_bv 64 (tn_addr n) -> getr regs 31 = Z_to_bv 64 (fmt * i) -> getr regs 10 = Z_to_bv 64 flt ->
obj_at src2segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n lf) -> length (tn_mean n) = 3%nat ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_D0) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if lf =? 0 then PC_DL else PC_LF)) mem (seg_rom src2segs)) mdq /\
getr regs' 9 = Z_to_bv 64 (tn_addr n) /\ (lf = 0 -> getr regs' 31 = Z_to_bv 64 (flt + 4 * (fmt * i))) /\
(forall rr : reg, In rr D0_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i n c0 c1 lf Hi Hlf HJ G24 G31 G10 Hobj Hlen Hn0 Hn1 Hn16.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 n lf) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n lf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 n lf Hlen) in Hobj, HV.
assert (U24 : bv_unsigned (ew E 27) = tn_addr n) by (rewrite (HE 27%nat 27%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U31 : bv_unsigned (ew E 31) = fmt * i) by (rewrite (HE 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; nia).
assert (U10 : bv_unsigned (ew E 10) = flt) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E (ss_D0 lf) (@mkst fy regs (Z_to_bv 64 PC_D0) mem (seg_rom src2segs))).
{ unfold ss_D0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen src2segs _ mem 27 (tn_addr n)); [exact U24 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24, U31, U10.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
repeat split; try lia; nia. }
assert (POST : forall ss1 regsx pc, @st_ok src2segs fy E ss1 (@mkst fy regsx (Z_to_bv 64 pc) mem (seg_rom src2segs)) ->
sr_get (ss_regs ss1) 9%bv = SOff 27%nat 0 ->
(lf = 0 -> sr_get (ss_regs ss1) 31%bv = SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 31 0) (SLit 2))) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss1) rr) (SOff (ridx rr) 0)) D0_KEEP = true ->
getr regsx 9 = Z_to_bv 64 (tn_addr n) /\ (lf = 0 -> getr regsx 31 = Z_to_bv 64 (flt + 4 * (fmt * i))) /\
(forall rr : reg, In rr D0_KEEP -> getr regsx rr = getr regs rr)).
{ intros ss1 regsx pc HS1 Q9 Q31 Hkb.
assert (RG : forall rr : reg, getr regsx rr = sv_denot E (sr_get (ss_regs ss1) rr)) by (intros rr; exact (st_ok_reg src2segs E ss1 _ rr HS1)).
split; [rewrite (RG 9%bv), Q9; cbn [sv_denot]; rewrite Z.add_0_r, U24; reflexivity|].
split; [intros Hl0; rewrite (RG 31%bv), (Q31 Hl0), (U_add_shl E 31 10 flt (fmt * i) 2 4 eq_refl U10 U31) by nia; f_equal; lia|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ D0_KEEP HS1 (env_agree_refl _ _) Hkb). }
destruct Hlf as [-> | ->].
- pure_to src2tbl_ok HS PC_DL. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
eapply (POST _ _ _ HS); [reflexivity | intros _; reflexivity | vm_compute; reflexivity].
- pure_to src2tbl_ok HS PC_LF. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
eapply (POST _ _ _ HS); [reflexivity | intros HH0; discriminate HH0 | vm_compute; reflexivity].
Qed.
Definition ss_DLT (lf : Z) : sstate :=
mkSS PC_DLT sr_atoms [ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (nd_lits lf)) ] None
(mkFacts [ (9%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Definition DLT_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma DLT_run : forall (fy : FPState) (regs : bvmap 5 word) mem (m : tnode) (c0 c1 lf : Z),
(lf = 0 \/ lf = 1) -> m_halted mdq = None -> m_vm_lazy mdq = [] ->
getr regs 9 = Z_to_bv 64 (tn_addr m) ->
obj_at src2segs mem (tn_addr m) LAY_Node (node_vals c0 c1 m lf) -> length (tn_mean m) = 3%nat ->
4096 <= tn_addr m -> tn_addr m + NODE_SIZE <= alloc_ceiling -> tn_addr m mod 16 = 0 ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DLT) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if lf =? 0 then PC_DL else PC_LF)) mem (seg_rom src2segs)) mdq /\
(forall rr : reg, In rr DLT_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem m c0 c1 lf Hlf Hh Hlz G9 Hobj Hlen Hn0 Hn1 Hn16.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 m lf) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 m lf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 m lf Hlen) in Hobj, HV.
assert (U9 : bv_unsigned (ew E 9) = tn_addr m) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E (ss_DLT lf) (@mkst fy regs (Z_to_bv 64 PC_DLT) mem (seg_rom src2segs))).
{ unfold ss_DLT. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen src2segs _ mem 9 (tn_addr m)); [exact U9 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 4) with 16. repeat split; lia. }
destruct Hlf as [-> | ->].
- pure_to src2tbl_ok HS PC_DL. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ DLT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- pure_to src2tbl_ok HS PC_LF. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ DLT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition dl_lits (cut : Z) : list (option Z) := [None; None; None; None; None; None; None; Some cut; None; Some 0].
Definition ss_DLx (cut : Z) : sstate :=
mkSS PC_DL sr_atoms
[ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (dl_lits cut));
YQ0b.mkRegion (Some 31%nat) 0 12 0 0 [mkChunk 0 (CData 0 0 12)] ] None
(mkFacts [ (9%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (31%nat, mkAF 4096 CEIL_MAX 2) ] [] []).
Definition ss_DL (cut : Z) : sstate := mkSST PC_DL (ss_regs (ss_DLx cut)) (sfr_atoms 64) (ss_mem (ss_DLx cut)) None (ss_facts (ss_DLx cut)).
Definition DL_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma DL_body : forall (fy : FPState) (regs : bvmap 5 word) mem (n : tnode) (c0 c1 pix : Z),
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy) ->
getr regs 9 = Z_to_bv 64 (tn_addr n) -> getr regs 31 = Z_to_bv 64 pix ->
obj_at src2segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> length (tn_mean n) = 3%nat -> 0 <= tn_cut n <= 2 ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
4096 <= pix -> pix + 12 <= alloc_ceiling -> pix mod 4 = 0 -> (tn_addr n + NODE_SIZE <= pix \/ pix + 12 <= tn_addr n) ->
(forall j, 0 <= j < 12 -> exists b, mbyte src2segs mem (pix + j) = Some b) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DL) mem (seg_rom src2segs)) mdq)
(fun c' => exists (fy' : FPState) regs',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_DLT) mem (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy') /\
(getr regs' 9 = Z_to_bv 64 c0 \/ getr regs' 9 = Z_to_bv 64 c1) /\
(forall rr : reg, In rr DL_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem n c0 c1 pix Hh Hlz Hfrm G9 G31 Hobj Hlen Hcut Hn0 Hn1 Hn16 Hp0 Hp1 Hp4 Hsep Hpres.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (bytes_of_present src2segs mem pix 12 Hpres) as (bp & Lbp & Hbp).
set (E0 := EregB regs (map (Z_to_bv 64) (node_vals c0 c1 n 0)) [bp]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HV : forall j v, nth_error (node_vals c0 c1 n 0) j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply EregB_vals; exact Hj).
rewrite (node_vals_expand c0 c1 n 0 Hlen) in Hobj, HV.
assert (A32 : ew E0 32 = Z_to_bv 64 c0) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 c1) by (apply (HV 1%nat); reflexivity).
assert (U9 : bv_unsigned (ew E0 9) = tn_addr n) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U31 : bv_unsigned (ew E0 31) = pix) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok src2segs fy E0 (ss_DLx (tn_cut n)) (@mkst fy regs (Z_to_bv 64 PC_DL) mem (seg_rom src2segs))).
{ unfold ss_DLx. apply entry_st_ok_env.
- subst E0; apply regs_ok_EregB.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj_gen src2segs _ mem 9 (tn_addr n)); [exact U9 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 7 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; [cbn in Hj |- *; congruence|].
destruct j as [|j]; [cbn in Hj; congruence|]. destruct j as [|j]; [cbn in Hj |- *; congruence|]. destruct j; discriminate Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U31.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length bp)) by (rewrite Lbp; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 0 bp ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hbp. rewrite <- Lbp. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U31.
split; [|exact (conj I I)]. split; [lia | exact I].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U31.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. repeat split; lia. }
pose proof (st_ok_enterF src2segs fy 64 E0 (ss_DLx (tn_cut n)) _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc (ss_DLx (tn_cut n))) (ss_regs (ss_DLx (tn_cut n))) (sfr_atoms 64) (ss_mem (ss_DLx (tn_cut n))) (ss_resv (ss_DLx (tn_cut n))) (ss_facts (ss_DLx (tn_cut n))))
with (ss_DL (tn_cut n)) in HS.
clear HS0. rewrite <- !HEE in U9, U31, A32, A33 by lia.
assert (Hk : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by lia.
destruct Hk as [Hk|[Hk|Hk]]; rewrite Hk in HS;
pureF_to src2tbl_ok HS PC_DC;
jregF HS (18%bv:reg) as Hq18; rewrite fcmp_denot in Hq18;
(lazymatch type of Hq18 with getr _ _ = (if ?bexp then w1 else w0) =>
destruct bexp;
[ pose proof (st_okF_pin_reg src2segs E _ _ 18%bv (SLit 1) HS ltac:(intros HH0; discriminate HH0) Hq18) as HS'
| pose proof (st_okF_pin_reg src2segs E _ _ 18%bv (SLit 0) HS ltac:(intros HH0; discriminate HH0) Hq18) as HS' ]
end);
clear HS; rename HS' into HS;
(match type of HS with st_okF _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end);
pureF_to src2tbl_ok HS PC_DLT;
cbn [ms_mem mkst] in Hmem, Hsh0; rewrite Hmem in Hsh0;
(eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz); [eapply msteps_trans; [exact Hms | exact Hms0]|]);
rewrite Hsh0; apply SR_ret;
(exists (fp_of ms0), (ms_regs ms0));
(split; [reflexivity|]);
(split; [exact (st_okF_frm src2segs E _ _ HS)|]);
(split; [jregF HS (9%bv:reg) as Hq9; cbn [ms_regs mkst] in Hq9; rewrite Hq9; first [left; exact A32 | right; exact A33] |]);
exact (st_okF_regs_kept src2segs E _ _ regs DL_KEEP HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)).
Qed.
Lemma DL_KEEP_sub : forall rr : reg, In rr DL_KEEP -> In rr DLT_KEEP.
Proof.
intros rr Hrr. cbv [DL_KEEP In] in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr.
Qed.
Lemma DG_run : forall (u : tree) (n : tnode) (ul ur : tree) (fy : FPState) (regs : bvmap 5 word) mem (pix : Z),
u = TNode n ul ur ->
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy) ->
getr regs 9 = Z_to_bv 64 (tn_addr n) -> getr regs 31 = Z_to_bv 64 pix ->
tree_at src2segs mem u -> tree_full u ->
(forall m, In m (tree_nodes u) -> tnode_wf m /\ 4096 <= tn_addr m /\ tn_addr m + NODE_SIZE <= alloc_ceiling /\ tn_addr m mod 16 = 0 /\
(tn_addr m + NODE_SIZE <= pix \/ pix + 12 <= tn_addr m)) ->
4096 <= pix -> pix + 12 <= alloc_ceiling -> pix mod 4 = 0 ->
(forall j, 0 <= j < 12 -> exists b, mbyte src2segs mem (pix + j) = Some b) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DL) mem (seg_rom src2segs)) mdq)
(fun c' => exists (fy' : FPState) regs' m,
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_LF) mem (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy') /\
In m (tree_leaves u) /\ getr regs' 9 = Z_to_bv 64 (tn_addr m) /\
(forall rr : reg, In rr DL_KEEP -> getr regs' rr = getr regs rr)).
Proof.
induction u as [|m0|n0 l0 IHl r0 IHr]; intros n ul ur fy regs mem pix Hu Hh Hlz Hfrm G9 G31 Hutree Hufull Hns Hp0 Hp1 Hp4 Hpres;
[discriminate Hu | discriminate Hu |].
injection Hu as En El Er. subst n0 l0 r0.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
cbn [tree_at] in Hutree. fold (tree_at src2segs) in Hutree. destruct Hutree as (Hnz & Hlen & Hobj & Hl & Hr). destruct Hufull as [Hfl Hfr].
destruct (Hns n ltac:(left; reflexivity)) as (Hwf & Hn0 & Hn1 & Hn16 & Hsepn). destruct Hwf as (Hcut & _).
eapply SR_bind; [exact (DL_body fy regs mem n (troot ul) (troot ur) pix Hh Hlz Hfrm G9 G31 Hobj Hlen Hcut Hn0 Hn1 Hn16 Hp0 Hp1 Hp4 Hsepn Hpres)|].
cbv beta. intros c1 (fy1 & regs1 & -> & Hfrm1 & G9a & Hk1).
assert (HC : exists v, (v = ul \/ v = ur) /\ getr regs1 9 = Z_to_bv 64 (troot v)) by (destruct G9a as [G|G]; [exists ul | exists ur]; auto).
destruct HC as (v & Hv & G9v).
assert (Hvt : tree_at src2segs mem v) by (destruct Hv as [-> | ->]; assumption).
assert (Hvf : tree_full v) by (destruct Hv as [-> | ->]; assumption).
assert (Hvn : forall m, In m (tree_nodes v) -> In m (tree_nodes (TNode n ul ur))) by (intros m Hm; right; apply in_app_iff; destruct Hv as [-> | ->]; auto).
assert (Hvl : forall m, In m (tree_leaves v) -> In m (tree_leaves (TNode n ul ur))) by (intros m Hm; cbn [tree_leaves]; apply in_app_iff; destruct Hv as [-> | ->]; auto).
assert (IHv : forall n' ul' ur' (fy' : FPState) (regs' : bvmap 5 word) mem' pix', v = TNode n' ul' ur' ->
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy') ->
getr regs' 9 = Z_to_bv 64 (tn_addr n') -> getr regs' 31 = Z_to_bv 64 pix' ->
tree_at src2segs mem' v -> tree_full v ->
(forall m, In m (tree_nodes v) -> tnode_wf m /\ 4096 <= tn_addr m /\ tn_addr m + NODE_SIZE <= alloc_ceiling /\ tn_addr m mod 16 = 0 /\
(tn_addr m + NODE_SIZE <= pix' \/ pix' + 12 <= tn_addr m)) ->
4096 <= pix' -> pix' + 12 <= alloc_ceiling -> pix' mod 4 = 0 ->
(forall j, 0 <= j < 12 -> exists b, mbyte src2segs mem' (pix' + j) = Some b) ->
SR src2segs (mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_DL) mem' (seg_rom src2segs)) mdq)
(fun c' => exists (fy'' : FPState) regs'' m,
c' = mkCfg (@mkst fy'' regs'' (Z_to_bv 64 PC_LF) mem' (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy'') /\
In m (tree_leaves v) /\ getr regs'' 9 = Z_to_bv 64 (tn_addr m) /\
(forall rr : reg, In rr DL_KEEP -> getr regs'' rr = getr regs' rr)))
by (destruct Hv as [-> | ->]; [exact IHl | exact IHr]).
clear IHl IHr.
destruct v as [|m|nv lv rv]; [destruct Hvf | |].
-
cbn [tree_at] in Hvt. destruct Hvt as (Hmz & Hmlen & c0 & c1 & Hobjm). cbn [troot] in G9v.
destruct (Hns m (Hvn m ltac:(left; reflexivity))) as (_ & Hm0 & Hm1 & Hm16 & _).
eapply SR_mono; [exact (DLT_run fy1 regs1 mem m c0 c1 1 ltac:(right; reflexivity) Hh Hlz G9v Hobjm Hmlen Hm0 Hm1 Hm16)|].
cbv beta. intros c2 (regs2 & -> & Hk2). change (if 1 =? 0 then PC_DL else PC_LF) with PC_LF.
exists fy1, regs2, m. split; [reflexivity|]. split; [exact Hfrm1|]. split; [apply Hvl; left; reflexivity|].
split; [rewrite (Hk2 9%bv ltac:(cbv; tauto)); exact G9v|].
intros rr Hrr. rewrite (Hk2 rr (DL_KEEP_sub rr Hrr)). apply Hk1. exact Hrr.
-
cbn [troot] in G9v.
assert (Hvt' := Hvt). cbn [tree_at] in Hvt'. fold (tree_at src2segs) in Hvt'. destruct Hvt' as (Hmz & Hmlen & Hobjv & _ & _).
destruct (Hns nv (Hvn nv ltac:(left; reflexivity))) as (_ & Hm0 & Hm1 & Hm16 & _).
eapply SR_bind; [exact (DLT_run fy1 regs1 mem nv (troot lv) (troot rv) 0 ltac:(left; reflexivity) Hh Hlz G9v Hobjv Hmlen Hm0 Hm1 Hm16)|].
cbv beta. intros c2 (regs2 & -> & Hk2). change (if 0 =? 0 then PC_DL else PC_LF) with PC_DL.
eapply SR_mono.
{ apply (IHv nv lv rv fy1 regs2 mem pix eq_refl Hh Hlz Hfrm1); try assumption.
- rewrite (Hk2 9%bv ltac:(cbv; tauto)). exact G9v.
- rewrite (Hk2 31%bv ltac:(cbv; tauto)), (Hk1 31%bv ltac:(cbv; tauto)). exact G31.
- intros m Hm. apply Hns. apply Hvn. exact Hm. }
cbv beta. intros c3 (fy3 & regs3 & m & -> & Hfrm3 & Hlm & G9m & Hk3).
exists fy3, regs3, m. split; [reflexivity|]. split; [exact Hfrm3|]. split; [apply Hvl; exact Hlm|]. split; [exact G9m|].
intros rr Hrr. rewrite (Hk3 rr Hrr), (Hk2 rr (DL_KEEP_sub rr Hrr)). apply Hk1. exact Hrr.
Qed.
End l.
End f.
End d.
