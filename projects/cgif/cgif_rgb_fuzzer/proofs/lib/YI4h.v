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
YI3h YI4v YI4r YI4s YI4u YP12.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac inK := repeat (first [left; apply bv_eq; reflexivity | right]).
Definition PN_LH : Z := 0x1431c.
Definition PN_A : Z := 0x14320.
Definition PN_B2 : Z := 0x1433c.
Definition PN_D0 : Z := 0x143d4.
Definition PN_DL : Z := 0x143f0.
Definition PN_DC : Z := 0x14414.
Definition PN_DLT : Z := 0x14424.
Definition PN_LF : Z := 0x1442c.
Definition PN_ST : Z := 0x14454.
Lemma U_shl : forall E n x k p,
2 ^ k = p -> bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 32 -> 0 <= k <= 4 ->
sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit k)) = Z_to_bv 64 (x * p).
Proof.
intros E n x k p Hp Hn Hx Hk. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, !Z.add_0_r.
assert (Hk2 : 0 < 2 ^ k <= 16) by (split; [apply Z.pow_pos_nonneg; lia | change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia]).
rewrite (zcanon_id x) by (unfold M64; lia).
replace (Z.land (zcanon k) 63) with k.
2:{ rewrite zcanon_id by (unfold M64; lia). assert (X : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
destruct X as [-> |[-> |[-> |[-> | ->]]]]; reflexivity. }
rewrite Z.shiftl_mul_pow2 by lia. rewrite Hp. apply zcanon_id. unfold M64; nia.
Qed.
Lemma U_mul_off' : forall E a b x y k,
ew E a = Z_to_bv 64 x -> bv_unsigned (ew E b) = y -> 0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 32 -> 0 <= y + k < 2 ^ 32 ->
sv_denot E (SMd M_MUL (SOff a 0) (SOff b k)) = Z_to_bv 64 (x * (y + k)).
Proof.
intros E a b x y k Ha Hb Hx Hy Hyk. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E a x Ha) by lia. rewrite U_SOff, Hb.
rewrite (zcanon_id (y + k)) by (unfold M64; lia). apply zcanon_id. unfold M64; nia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
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
Section e.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree) (ha : Z).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis HtreeD : tree_at src2segs memD t. Hypothesis Hfull : tree_full t. Hypothesis Hwft : tree_forall tnode_wf t.
Hypothesis Hnodes : forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Hypothesis Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n.
Hypothesis Hha : ha = 0 \/ (ha = 1 /\ fmt = 4).
Hypothesis Hsl96 : slot regs0 memD SL_96 bef. Hypothesis Hsl112 : bef <> 0 -> slot regs0 memD SL_112 beffmt.
Hypothesis Hbefb : bef <> 0 -> (beffmt = 3 \/ beffmt = 4) /\ In (bef, beffmt * N) (blocks Lq Aq) /\ (bef + beffmt * N <= flt \/ flt + 4 * M <= bef).
Hypothesis Rbef : 0 <= bef < 2 ^ 64.
Definition memIN (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (fimg <= a < fimg + N) -> mbyte src2segs m a = mbyte src2segs memD a.
Lemma memIN_trans : forall m m', memIN m ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (fimg <= a < fimg + N) -> mbyte src2segs m' a = mbyte src2segs m a) -> memIN m'.
Proof. intros m m' Hm Hk a Ha H1. rewrite (Hk a Ha H1). apply Hm; assumption. Qed.
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5136 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 158.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte src2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma bef_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq -> bef <> 0 ->
forall i, 0 <= i < beffmt * N -> exists b, mbyte src2segs m (bef + i) = Some b.
Proof.
intros m HJ Hb i Hi. destruct (Hbefb Hb) as (_ & Hin & _). apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq bef (beffmt * N) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hin Hi)).
Qed.
Lemma bef_range : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq -> bef <> 0 ->
4096 <= bef /\ bef + beffmt * N <= alloc_ceiling.
Proof.
intros m HJ Hb. destruct (Hbefb Hb) as (Hbf & Hin & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bef (beffmt * N) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hin ltac:(lia)) as (X1 & X2 & _). lia.
Qed.
Lemma fimg_writable : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, fimg <= a < fimg + N -> writable_at src2segs m a.
Proof.
intros m HJ a Ha. replace a with (fimg + (a - fimg)) by lia. apply (present_writable src2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq fimg N (a - fimg) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia))).
Qed.

Definition ss_NM : sstate := mkSS PN_LH sr_atoms [] None (mkFacts [ (26%nat, mkAF 3 4 0); (11%nat, mkAF 0 RGB_NMAX 0) ] [] []).
Definition NM_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NM_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> m_halted mdq = None -> m_vm_lazy mdq = [] ->
getr regs 26 = Z_to_bv 64 fmt -> getr regs 11 = Z_to_bv 64 i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 PN_A) mem (seg_rom src2segs)) mdq /\
getr regs' 13 = Z_to_bv 64 (fmt * i) /\ (forall rr : reg, In rr NM_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i Hi Hh Hlz G26 G11. pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U26 : bv_unsigned (ew E 26) = fmt) by (rewrite (HE 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = i) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E ss_NM (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom src2segs))).
{ unfold ss_NM. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I |].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U26, U11. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS PN_A. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
split; [pose proof (st_ok_reg src2segs E _ _ 13%bv HS) as Q; eval_sr_get_in Q; cbn [ms_regs mkst] in Q; rewrite Q;
rewrite (U_mul_off' E 26 11 fmt i 0) by first [rewrite <- U26; symmetry; apply Z_to_bv_bv_unsigned | exact U11 | lia]; f_equal; lia|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NM_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NAx : sstate :=
mkSS PN_A sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 4 0 0 [mkChunk 0 (CData 0 0 4)] ] None
(mkFacts [ (13%nat, mkAF 0 (2^20) 0); (10%nat, mkAF 4096 CEIL_MAX 2); (32%nat, mkAF 4096 CEIL_MAX 2) ] [mkAC BC_EQ (SOff 17%nat 0) (SLit 0)]
[ (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 13 3) (SLit 2)), SOff 32%nat 0) ]).
Definition ss_NA : sstate := mkSST PN_A (ss_regs ss_NAx) (sfr_atoms 64) (ss_mem ss_NAx) None (ss_facts ss_NAx).
Definition NA_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition ntest_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (i : Z) (K : list reg) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' (ti : bool),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if ti then PN_ST else PN_D0)) mem (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy') /\
(ti = false -> getr regs' 13 = Z_to_bv 64 (fmt * i)) /\
(forall rr : reg, In rr K -> getr regs' rr = getr regs rr).
Lemma NA_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> fmt = 4 ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 13 = Z_to_bv 64 (fmt * i) -> getr regs 10 = Z_to_bv 64 flt ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_A) mem (seg_rom src2segs)) mdq) (ntest_post fy regs mem i NA_KEEP).
Proof.
intros fy regs mem i Hi F4 HJ Hfrm G17 G13 G10.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
assert (Hci : 0 <= 4 * (fmt * i + 3) /\ 4 * (fmt * i + 3) + 4 <= 4 * M) by (subst M; nia).
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * i + 3)) 4 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0).
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * (fmt * i + 3)]) [b0]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * (fmt * i + 3))) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (U17 : bv_unsigned (ew E0 17) = 0) by (rewrite (HE0 17%nat 17%bv eq_refl), G17; reflexivity).
assert (U13 : bv_unsigned (ew E0 13) = fmt * i) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; nia).
assert (U10 : bv_unsigned (ew E0 10) = flt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * (fmt * i + 3)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (HS0 : @st_ok src2segs fy E0 ss_NAx (@mkst fy regs (Z_to_bv 64 PN_A) mem (seg_rom src2segs))).
{ unfold ss_NAx. apply entry_st_ok_env.
- subst E0; apply regs_ok_EregB.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 4 with (Z.of_nat (length b0)) at 2 by (rewrite Lb0; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0. rewrite <- Lb0. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U13, U10, U32.
change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * (fmt * i + 3)) mod 4 = 0) by (replace (flt + 4 * (fmt * i + 3)) with (flt + (fmt * i + 3) * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I].
rewrite branch_eq_U, U_SOff, U_SLit, U17. reflexivity.
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U10, U13, U32, Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id (fmt * i + 3)) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id ((fmt * i + 3) * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
pose proof (st_ok_enterF src2segs fy 64 E0 ss_NAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_NAx) (ss_regs ss_NAx) (sfr_atoms 64) (ss_mem ss_NAx) (ss_resv ss_NAx) (ss_facts ss_NAx)) with ss_NA in HS.
clear HS0. rewrite <- !HEE in U13, U10, U32 by lia.
assert (POST : forall (ssx : sstate) (msx : machine_state) (ti : bool), st_okF src2segs E ssx msx -> ss_resv ssx = None ->
ss_pc ssx = (if ti then PN_ST else PN_D0) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) NA_KEEP = true ->
(ti = false -> sr_get (ss_regs ssx) 13%bv = SOff 13%nat 0) ->
ms_mem msx = mem ->
ntest_post fy regs mem i NA_KEEP (mkCfg msx mdq)).
{ intros ssx msx ti HSx Hrv Hpc Hkb Q13 Hmm. exists (fp_of msx), (ms_regs msx), ti.
split; [rewrite (st_okF_mkst src2segs E ssx msx HSx Hrv), Hpc, Hmm; reflexivity|]. split; [exact (st_okF_frm src2segs E _ _ HSx)|].
split; [intros Hti; rewrite (st_okF_reg src2segs E ssx msx 13%bv HSx), (Q13 Hti); cbn [sv_denot]; rewrite U13, Z.add_0_r; reflexivity|].
exact (st_okF_regs_kept src2segs E ssx msx _ NA_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb). }
pureF_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). cbn [ms_mem mkst] in Hmem.
jbranchF src2tbl HS.
-
pureF_to src2tbl_ok HS PN_D0. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | intros _; reflexivity | rewrite Hmem0; exact Hmem].
-
pureF_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
eapply (POST _ _ true HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | intros HH0; discriminate HH0 | rewrite Hmem0; exact Hmem].
Qed.
Definition ss_NB0 : sstate :=
mkSS PN_A sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk SL_96 (CVal 8 (SLit 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [mkAC BC_NE (SOff 17%nat 0) (SLit 0)] []).
Definition NB0_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NB0_run : forall (fy : FPState) (regs : bvmap 5 word) mem,
m_halted mdq = None -> m_vm_lazy mdq = [] -> slot regs0 mem SL_96 0 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 17 = Z_to_bv 64 1 ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_A) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 PN_D0) mem (seg_rom src2segs)) mdq /\
(forall rr : reg, In rr NB0_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem Hh Hlz S96 G2 G17. pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U17 : bv_unsigned (ew E 17) = 1) by (rewrite (HE 17%nat 17%bv eq_refl), G17; reflexivity).
assert (HS : @st_ok src2segs fy E ss_NB0 (@mkst fy regs (Z_to_bv 64 PN_A) mem (seg_rom src2segs))).
{ unfold ss_NB0. apply entry_st_ok_env.
- subst E; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S96].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2.
change (2 ^ 4) with 16. unfold sp, sp0 in *.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I].
rewrite branch_ne_U, U_SOff, U_SLit, U17. reflexivity. }
pure_to src2tbl_ok HS PN_D0. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NB0_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NBm : sstate :=
mkSS PN_A sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk SL_96 (CVal 8 (SOff 34 0)); mkChunk SL_112 (CVal 8 (SOff 35 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (13%nat, mkAF 0 (2^20) 0); (35%nat, mkAF 3 4 0); (11%nat, mkAF 0 RGB_NMAX 0); (34%nat, mkAF 4096 CEIL_MAX 0) ]
[mkAC BC_NE (SOff 17%nat 0) (SLit 0); mkAC BC_NE (SOff 34%nat 0) (SLit 0)] []).
Definition NBm_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NBm_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> bef <> 0 ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq ->
slot regs0 mem SL_96 bef -> slot regs0 mem SL_112 beffmt ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 17 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 (fmt * i) -> getr regs 11 = Z_to_bv 64 i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_A) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 PN_B2) mem (seg_rom src2segs)) mdq /\
getr regs' 14 = Z_to_bv 64 (beffmt * i) /\ getr regs' 15 = Z_to_bv 64 (4 * (fmt * i)) /\
(forall rr : reg, In rr NBm_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i Hi Hb HJ S96 S112 G2 G17 G13 G11. pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct (Hbefb Hb) as (Hbf & _ & _). destruct (bef_range mem HJ Hb) as [Hb0 Hb1].
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; bef; beffmt] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A34 : ew E 34 = Z_to_bv 64 bef) by (subst E; apply (Ereg_vals regs [0; 0; bef; beffmt] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 beffmt) by (subst E; apply (Ereg_vals regs [0; 0; bef; beffmt] [] 3%nat); reflexivity).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U34 : bv_unsigned (ew E 34) = bef) by (rewrite A34; apply unsigned_lit_small; lia).
assert (U17 : bv_unsigned (ew E 17) = 1) by (rewrite (HE 17%nat 17%bv eq_refl), G17; reflexivity).
assert (U13 : bv_unsigned (ew E 13) = fmt * i) by (rewrite (HE 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; nia).
assert (U11 : bv_unsigned (ew E 11) = i) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = beffmt) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E ss_NBm (@mkst fy regs (Z_to_bv 64 PN_A) mem (seg_rom src2segs))).
{ unfold ss_NBm. apply entry_st_ok_env.
- subst E; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S96].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S112].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U13, U35, U11, U34.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold sp, sp0 in *.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|split; [|exact I]].
* rewrite branch_ne_U, U_SOff, U_SLit, U17. reflexivity.
* rewrite branch_ne_U, U_SOff, U_SLit, U34, Z.add_0_r, !zcanon_id by (unfold M64; lia). destruct (Z.eqb_spec bef 0); [lia | reflexivity]. }
pure_to src2tbl_ok HS PN_B2. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
split; [pose proof (st_ok_reg src2segs E _ _ 14%bv HS) as Q; eval_sr_get_in Q; cbn [ms_regs mkst] in Q; rewrite Q;
rewrite (U_mul_off' E 35 11 beffmt i 0 A35 U11) by lia; f_equal; lia|].
split; [pose proof (st_ok_reg src2segs E _ _ 15%bv HS) as Q; eval_sr_get_in Q; cbn [ms_regs mkst] in Q; rewrite Q;
rewrite (U_shl E 13 (fmt * i) 2 4 eq_refl U13) by nia; f_equal; lia|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NBm_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NB2x : sstate :=
mkSS PN_B2 sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 12 0 0 [mkChunk 0 (CData 0 0 12)]; YQ0b.mkRegion (Some 33%nat) 0 3 0 0 [mkChunk 0 (CData 1 0 3)];
YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk SL_96 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (13%nat, mkAF 0 (2^20) 0); (14%nat, mkAF 0 (2^20) 0); (15%nat, mkAF 0 (2^24) 2); (10%nat, mkAF 4096 CEIL_MAX 2); (34%nat, mkAF 4096 CEIL_MAX 0);
(32%nat, mkAF 4096 CEIL_MAX 2); (33%nat, mkAF 4096 CEIL_MAX 0) ] []
[ (SAlu ALU_ADD (SOff 10 0) (SOff 15 0), SOff 32%nat 0);
(SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 13 1) (SLit 2)), SOff 32%nat 4);
(SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 13 2) (SLit 2)), SOff 32%nat 8);
(SAlu ALU_ADD (SOff 34 0) (SOff 14 0), SOff 33%nat 0);
(SAlu ALU_ADD (SOff 34 0) (SOff 14 1), SOff 33%nat 1);
(SAlu ALU_ADD (SOff 34 0) (SOff 14 2), SOff 33%nat 2) ]).
Definition ss_NB2 : sstate := mkSST PN_B2 (ss_regs ss_NB2x) (sfr_atoms 64) (ss_mem ss_NB2x) None (ss_facts ss_NB2x).
Definition NB2_KEEP : list reg := [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NB2_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> bef <> 0 ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 13 = Z_to_bv 64 (fmt * i) -> getr regs 14 = Z_to_bv 64 (beffmt * i) -> getr regs 15 = Z_to_bv 64 (4 * (fmt * i)) ->
getr regs 10 = Z_to_bv 64 flt -> getr regs 2 = Z_to_bv 64 spv -> slot regs0 mem SL_96 bef ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_B2) mem (seg_rom src2segs)) mdq) (ntest_post fy regs mem i NB2_KEEP).
Proof.
intros fy regs mem i Hi Hb HJ Hfrm G13 G14 G15 G10 G2 S96.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct (Hbefb Hb) as (Hbf & _ & Hbsep). destruct (bef_range mem HJ Hb) as [Hb0 Hb1].
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia).
assert (Hbi : 0 <= beffmt * i /\ beffmt * i + 3 <= beffmt * N) by nia.
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * i)) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0').
destruct (bytes_of_present src2segs mem (bef + beffmt * i) 3 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (bef_present mem HJ Hb); lia)) as (b1 & Lb1 & Hb1').
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * (fmt * i); bef + beffmt * i; bef]) [b0; b1]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * (fmt * i))) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 (bef + beffmt * i)) by (subst E0; apply (EregB_vals regs _ _ 1%nat); reflexivity).
assert (A34 : ew E0 34 = Z_to_bv 64 bef) by (subst E0; apply (EregB_vals regs _ _ 2%nat); reflexivity).
assert (U2 : bv_unsigned (ew E0 2) = spv) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U13 : bv_unsigned (ew E0 13) = fmt * i) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; nia).
assert (U14 : bv_unsigned (ew E0 14) = beffmt * i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; nia).
assert (U15 : bv_unsigned (ew E0 15) = 4 * (fmt * i)) by (rewrite (HE0 15%nat 15%bv eq_refl), G15; apply unsigned_lit_small; nia).
assert (U10 : bv_unsigned (ew E0 10) = flt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E0 34) = bef) by (rewrite A34; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * (fmt * i)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = bef + beffmt * i) by (rewrite A33; apply unsigned_lit_small; lia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (AL1 : forall k, 0 <= k <= 2 -> sv_denot E0 (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 13 k) (SLit 2))) = sv_denot E0 (SOff 32%nat (4 * k))).
{ intros k Hk. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U10, U13, U32, Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id (fmt * i + k)) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id ((fmt * i + k) * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
assert (AL2 : forall k, 0 <= k <= 2 -> sv_denot E0 (SAlu ALU_ADD (SOff 34 0) (SOff 14 k)) = sv_denot E0 (SOff 33%nat k)).
{ intros k Hk. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U34, U14, U33, Z.add_0_r.
rewrite (zcanon_id bef), (zcanon_id (beffmt * i + k)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
assert (HS0 : @st_ok src2segs fy E0 ss_NB2x (@mkst fy regs (Z_to_bv 64 PN_B2) mem (seg_rom src2segs))).
{ unfold ss_NB2x. apply entry_st_ok_env.
- subst E0; apply regs_ok_EregB.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length b0)) by (rewrite Lb0; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0'. rewrite <- Lb0. exact Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace (CData 1 0 3) with (CData 1 0 (Z.of_nat (length b1))) by (rewrite Lb1; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 1 b1 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb1'. rewrite <- Lb1. exact Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S96].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U32, U33, U2.
split; [split; [subst M; nia | split; [unfold sp, sp0 in *; subst M; nia | exact I]]|].
split; [split; [unfold sp, sp0 in *; nia | exact I] | exact (conj I I)].
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U13, U14, U15, U10, U34, U32, U33.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * (fmt * i)) mod 4 = 0) by (replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
assert ((4 * (fmt * i)) mod 4 = 0) by (replace (4 * (fmt * i)) with ((fmt * i) * 4) by lia; apply Z_mod_mult).
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
unfold sp, sp0 in *. repeat split; try lia; nia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok].
split; [rewrite (U_add2 E0 10 15 flt (4 * (fmt * i)) U10 U15) by lia; cbn [sv_denot]; rewrite Z.add_0_r, U32; reflexivity|].
split; [rewrite (AL1 1) by lia; reflexivity|]. split; [rewrite (AL1 2) by lia; reflexivity|].
split; [exact (AL2 0 ltac:(lia))|]. split; [exact (AL2 1 ltac:(lia))|]. split; [exact (AL2 2 ltac:(lia))|]. exact I. }
pose proof (st_ok_enterF src2segs fy 64 E0 ss_NB2x _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_NB2x) (ss_regs ss_NB2x) (sfr_atoms 64) (ss_mem ss_NB2x) (ss_resv ss_NB2x) (ss_facts ss_NB2x)) with ss_NB2 in HS.
clear HS0. rewrite <- !HEE in U2, U13, U14, U15, U10, U34, U32, U33 by lia.
assert (POST : forall (ssx : sstate) (msx : machine_state) (ti : bool), st_okF src2segs E ssx msx -> ss_resv ssx = None ->
ss_pc ssx = (if ti then PN_ST else PN_D0) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) NB2_KEEP = true ->
(ti = false -> sr_get (ss_regs ssx) 13%bv = SOff 13%nat 0) ->
ms_mem msx = mem ->
ntest_post fy regs mem i NB2_KEEP (mkCfg msx mdq)).
{ intros ssx msx ti HSx Hrv Hpc Hkb Q13 Hmm. exists (fp_of msx), (ms_regs msx), ti.
split; [rewrite (st_okF_mkst src2segs E ssx msx HSx Hrv), Hpc, Hmm; reflexivity|]. split; [exact (st_okF_frm src2segs E _ _ HSx)|].
split; [intros Hti; rewrite (st_okF_reg src2segs E ssx msx 13%bv HSx), (Q13 Hti); cbn [sv_denot]; rewrite U13, Z.add_0_r; reflexivity|].
exact (st_okF_regs_kept src2segs E ssx msx _ NB2_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb). }
pureF_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). cbn [ms_mem mkst] in Hmem.
jbranchF src2tbl HS.
-
pureF_to src2tbl_ok HS PN_D0. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | intros _; reflexivity | rewrite Hmem0; exact Hmem].
- pureF_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms0). cbn [ms_mem mkst] in Hmem0.
jbranchF src2tbl HS.
+
pureF_to src2tbl_ok HS PN_D0. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms1). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | intros _; reflexivity | rewrite Hmem1, Hmem0; exact Hmem].
+ pureF_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms1). cbn [ms_mem mkst] in Hmem1.
jbranchF src2tbl HS.
*
pureF_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms2). apply SR_ret.
eapply (POST _ _ true HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | intros HH0; discriminate HH0 | rewrite Hmem2, Hmem1, Hmem0; exact Hmem].
*
pureF_to src2tbl_ok HS PN_D0. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms2). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | intros _; reflexivity | rewrite Hmem2, Hmem1, Hmem0; exact Hmem].
Qed.
Definition ss_ND0 (lf : Z) : sstate :=
mkSS PN_D0 sr_atoms [ YQ0b.mkRegion (Some 27%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (nd_lits lf)) ] None
(mkFacts [ (27%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (13%nat, mkAF 0 (2^20) 0); (10%nat, mkAF 4096 CEIL_MAX 2) ] [] []).
Definition ND0_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma ND0_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z) (n : tnode) (c0 c1 lf : Z),
0 <= i < N -> (lf = 0 \/ lf = 1) ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq ->
getr regs 27 = Z_to_bv 64 (tn_addr n) -> getr regs 13 = Z_to_bv 64 (fmt * i) -> getr regs 10 = Z_to_bv 64 flt ->
obj_at src2segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n lf) -> length (tn_mean n) = 3%nat ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_D0) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if lf =? 0 then PN_DL else PN_LF)) mem (seg_rom src2segs)) mdq /\
getr regs' 14 = Z_to_bv 64 (tn_addr n) /\ (lf = 0 -> getr regs' 13 = Z_to_bv 64 (flt + 4 * (fmt * i))) /\
(forall rr : reg, In rr ND0_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i n c0 c1 lf Hi Hlf HJ G27 G13 G10 Hobj Hlen Hn0 Hn1 Hn16.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 n lf) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n lf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 n lf Hlen) in Hobj, HV.
assert (U27 : bv_unsigned (ew E 27) = tn_addr n) by (rewrite (HE 27%nat 27%bv eq_refl), G27; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = fmt * i) by (rewrite (HE 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; nia).
assert (U10 : bv_unsigned (ew E 10) = flt) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E (ss_ND0 lf) (@mkst fy regs (Z_to_bv 64 PN_D0) mem (seg_rom src2segs))).
{ unfold ss_ND0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen src2segs _ mem 27 (tn_addr n)); [exact U27 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U27, U13, U10.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
repeat split; try lia; nia. }
assert (POST : forall ss1 regsx pc, @st_ok src2segs fy E ss1 (@mkst fy regsx (Z_to_bv 64 pc) mem (seg_rom src2segs)) ->
sr_get (ss_regs ss1) 14%bv = SOff 27%nat 0 ->
(lf = 0 -> sr_get (ss_regs ss1) 13%bv = SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 13 0) (SLit 2))) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss1) rr) (SOff (ridx rr) 0)) ND0_KEEP = true ->
getr regsx 14 = Z_to_bv 64 (tn_addr n) /\ (lf = 0 -> getr regsx 13 = Z_to_bv 64 (flt + 4 * (fmt * i))) /\
(forall rr : reg, In rr ND0_KEEP -> getr regsx rr = getr regs rr)).
{ intros ss1 regsx pc HS1 Q14 Q13 Hkb.
assert (RG : forall rr : reg, getr regsx rr = sv_denot E (sr_get (ss_regs ss1) rr)) by (intros rr; exact (st_ok_reg src2segs E ss1 _ rr HS1)).
split; [rewrite (RG 14%bv), Q14; cbn [sv_denot]; rewrite Z.add_0_r, U27; reflexivity|].
split; [intros Hl0; rewrite (RG 13%bv), (Q13 Hl0), (U_add_shl E 13 10 flt (fmt * i) 2 4 eq_refl U10 U13) by nia; f_equal; lia|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ ND0_KEEP HS1 (env_agree_refl _ _) Hkb). }
destruct Hlf as [-> | ->].
- pure_to src2tbl_ok HS PN_DL. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
eapply (POST _ _ _ HS); [reflexivity | intros _; reflexivity | vm_compute; reflexivity].
- pure_to src2tbl_ok HS PN_LF. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
eapply (POST _ _ _ HS); [reflexivity | intros HH0; discriminate HH0 | vm_compute; reflexivity].
Qed.
Definition ss_NDLT (lf : Z) : sstate :=
mkSS PN_DLT sr_atoms [ YQ0b.mkRegion (Some 14%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (nd_lits lf)) ] None
(mkFacts [ (14%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Definition NDLT_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NDLT_run : forall (fy : FPState) (regs : bvmap 5 word) mem (m : tnode) (c0 c1 lf : Z),
(lf = 0 \/ lf = 1) -> m_halted mdq = None -> m_vm_lazy mdq = [] ->
getr regs 14 = Z_to_bv 64 (tn_addr m) ->
obj_at src2segs mem (tn_addr m) LAY_Node (node_vals c0 c1 m lf) -> length (tn_mean m) = 3%nat ->
4096 <= tn_addr m -> tn_addr m + NODE_SIZE <= alloc_ceiling -> tn_addr m mod 16 = 0 ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_DLT) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if lf =? 0 then PN_DL else PN_LF)) mem (seg_rom src2segs)) mdq /\
(forall rr : reg, In rr NDLT_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem m c0 c1 lf Hlf Hh Hlz G14 Hobj Hlen Hn0 Hn1 Hn16.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 m lf) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 m lf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 m lf Hlen) in Hobj, HV.
assert (U14 : bv_unsigned (ew E 14) = tn_addr m) by (rewrite (HE 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E (ss_NDLT lf) (@mkst fy regs (Z_to_bv 64 PN_DLT) mem (seg_rom src2segs))).
{ unfold ss_NDLT. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen src2segs _ mem 14 (tn_addr m)); [exact U14 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U14. change (2 ^ 4) with 16. repeat split; lia. }
destruct Hlf as [-> | ->].
- pure_to src2tbl_ok HS PN_DL. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NDLT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- pure_to src2tbl_ok HS PN_LF. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NDLT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NDLx (cut : Z) : sstate :=
mkSS PN_DL sr_atoms
[ YQ0b.mkRegion (Some 14%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (dl_lits cut));
YQ0b.mkRegion (Some 13%nat) 0 12 0 0 [mkChunk 0 (CData 0 0 12)] ] None
(mkFacts [ (14%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (13%nat, mkAF 4096 CEIL_MAX 2) ] [] []).
Definition ss_NDL (cut : Z) : sstate := mkSST PN_DL (ss_regs (ss_NDLx cut)) (sfr_atoms 64) (ss_mem (ss_NDLx cut)) None (ss_facts (ss_NDLx cut)).
Definition NDL_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NDL_body : forall (fy : FPState) (regs : bvmap 5 word) mem (n : tnode) (c0 c1 pix : Z),
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy) ->
getr regs 14 = Z_to_bv 64 (tn_addr n) -> getr regs 13 = Z_to_bv 64 pix ->
obj_at src2segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> length (tn_mean n) = 3%nat -> 0 <= tn_cut n <= 2 ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
4096 <= pix -> pix + 12 <= alloc_ceiling -> pix mod 4 = 0 -> (tn_addr n + NODE_SIZE <= pix \/ pix + 12 <= tn_addr n) ->
(forall j, 0 <= j < 12 -> exists b, mbyte src2segs mem (pix + j) = Some b) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_DL) mem (seg_rom src2segs)) mdq)
(fun c' => exists (fy' : FPState) regs',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PN_DLT) mem (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy') /\
(getr regs' 14 = Z_to_bv 64 c0 \/ getr regs' 14 = Z_to_bv 64 c1) /\
(forall rr : reg, In rr NDL_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem n c0 c1 pix Hh Hlz Hfrm G14 G13 Hobj Hlen Hcut Hn0 Hn1 Hn16 Hp0 Hp1 Hp4 Hsep Hpres.
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
assert (U14 : bv_unsigned (ew E0 14) = tn_addr n) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E0 13) = pix) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok src2segs fy E0 (ss_NDLx (tn_cut n)) (@mkst fy regs (Z_to_bv 64 PN_DL) mem (seg_rom src2segs))).
{ unfold ss_NDLx. apply entry_st_ok_env.
- subst E0; apply regs_ok_EregB.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj_gen src2segs _ mem 14 (tn_addr n)); [exact U14 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 7 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; [cbn in Hj |- *; congruence|].
destruct j as [|j]; [cbn in Hj; congruence|]. destruct j as [|j]; [cbn in Hj |- *; congruence|]. destruct j; discriminate Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U13.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length bp)) by (rewrite Lbp; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 0 bp ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hbp. rewrite <- Lbp. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U14, U13.
split; [|exact (conj I I)]. split; [lia | exact I].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U14, U13.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. repeat split; lia. }
pose proof (st_ok_enterF src2segs fy 64 E0 (ss_NDLx (tn_cut n)) _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc (ss_NDLx (tn_cut n))) (ss_regs (ss_NDLx (tn_cut n))) (sfr_atoms 64) (ss_mem (ss_NDLx (tn_cut n))) (ss_resv (ss_NDLx (tn_cut n))) (ss_facts (ss_NDLx (tn_cut n))))
with (ss_NDL (tn_cut n)) in HS.
clear HS0. rewrite <- !HEE in U14, U13, A32, A33 by lia.
assert (Hk : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by lia.
destruct Hk as [Hk|[Hk|Hk]]; rewrite Hk in HS;
pureF_to src2tbl_ok HS PN_DC;
jregF HS (15%bv:reg) as Hq18; rewrite fcmp_denot in Hq18;
(lazymatch type of Hq18 with getr _ _ = (if ?bexp then w1 else w0) =>
destruct bexp;
[ pose proof (st_okF_pin_reg src2segs E _ _ 15%bv (SLit 1) HS ltac:(intros HH0; discriminate HH0) Hq18) as HS'
| pose proof (st_okF_pin_reg src2segs E _ _ 15%bv (SLit 0) HS ltac:(intros HH0; discriminate HH0) Hq18) as HS' ]
end);
clear HS; rename HS' into HS;
(match type of HS with st_okF _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end);
pureF_to src2tbl_ok HS PN_DLT;
cbn [ms_mem mkst] in Hmem, Hsh0; rewrite Hmem in Hsh0;
(eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz); [eapply msteps_trans; [exact Hms | exact Hms0]|]);
rewrite Hsh0; apply SR_ret;
(exists (fp_of ms0), (ms_regs ms0));
(split; [reflexivity|]);
(split; [exact (st_okF_frm src2segs E _ _ HS)|]);
(split; [jregF HS (14%bv:reg) as Hq9; cbn [ms_regs mkst] in Hq9; rewrite Hq9; first [left; exact A32 | right; exact A33] |]);
exact (st_okF_regs_kept src2segs E _ _ regs NDL_KEEP HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)).
Qed.
Lemma NDL_KEEP_sub : forall rr : reg, In rr NDL_KEEP -> In rr NDLT_KEEP.
Proof.
intros rr Hrr. cbv [NDL_KEEP In] in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [inK|]). destruct Hrr.
Qed.
Lemma NDG_run : forall (u : tree) (n : tnode) (ul ur : tree) (fy : FPState) (regs : bvmap 5 word) mem (pix : Z),
u = TNode n ul ur ->
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy) ->
getr regs 14 = Z_to_bv 64 (tn_addr n) -> getr regs 13 = Z_to_bv 64 pix ->
tree_at src2segs mem u -> tree_full u ->
(forall m, In m (tree_nodes u) -> tnode_wf m /\ 4096 <= tn_addr m /\ tn_addr m + NODE_SIZE <= alloc_ceiling /\ tn_addr m mod 16 = 0 /\
(tn_addr m + NODE_SIZE <= pix \/ pix + 12 <= tn_addr m)) ->
4096 <= pix -> pix + 12 <= alloc_ceiling -> pix mod 4 = 0 ->
(forall j, 0 <= j < 12 -> exists b, mbyte src2segs mem (pix + j) = Some b) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_DL) mem (seg_rom src2segs)) mdq)
(fun c' => exists (fy' : FPState) regs' m,
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PN_LF) mem (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy') /\
In m (tree_leaves u) /\ getr regs' 14 = Z_to_bv 64 (tn_addr m) /\
(forall rr : reg, In rr NDL_KEEP -> getr regs' rr = getr regs rr)).
Proof.
induction u as [|m0|n0 l0 IHl r0 IHr]; intros n ul ur fy regs mem pix Hu Hh Hlz Hfrm G14 G13 Hutree Hufull Hns Hp0 Hp1 Hp4 Hpres;
[discriminate Hu | discriminate Hu |].
injection Hu as En El Er. subst n0 l0 r0.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
cbn [tree_at] in Hutree. fold (tree_at src2segs) in Hutree. destruct Hutree as (Hnz & Hlen & Hobj & Hl & Hr). destruct Hufull as [Hfl Hfr].
destruct (Hns n ltac:(left; reflexivity)) as (Hwf & Hn0 & Hn1 & Hn16 & Hsepn). destruct Hwf as (Hcut & _).
eapply SR_bind; [exact (NDL_body fy regs mem n (troot ul) (troot ur) pix Hh Hlz Hfrm G14 G13 Hobj Hlen Hcut Hn0 Hn1 Hn16 Hp0 Hp1 Hp4 Hsepn Hpres)|].
cbv beta. intros c1 (fy1 & regs1 & -> & Hfrm1 & G9a & Hk1).
assert (HC : exists v, (v = ul \/ v = ur) /\ getr regs1 14 = Z_to_bv 64 (troot v)) by (destruct G9a as [G|G]; [exists ul | exists ur]; auto).
destruct HC as (v & Hv & G9v).
assert (Hvt : tree_at src2segs mem v) by (destruct Hv as [-> | ->]; assumption).
assert (Hvf : tree_full v) by (destruct Hv as [-> | ->]; assumption).
assert (Hvn : forall m, In m (tree_nodes v) -> In m (tree_nodes (TNode n ul ur))) by (intros m Hm; right; apply in_app_iff; destruct Hv as [-> | ->]; auto).
assert (Hvl : forall m, In m (tree_leaves v) -> In m (tree_leaves (TNode n ul ur))) by (intros m Hm; cbn [tree_leaves]; apply in_app_iff; destruct Hv as [-> | ->]; auto).
assert (IHv : forall n' ul' ur' (fy' : FPState) (regs' : bvmap 5 word) mem' pix', v = TNode n' ul' ur' ->
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy') ->
getr regs' 14 = Z_to_bv 64 (tn_addr n') -> getr regs' 13 = Z_to_bv 64 pix' ->
tree_at src2segs mem' v -> tree_full v ->
(forall m, In m (tree_nodes v) -> tnode_wf m /\ 4096 <= tn_addr m /\ tn_addr m + NODE_SIZE <= alloc_ceiling /\ tn_addr m mod 16 = 0 /\
(tn_addr m + NODE_SIZE <= pix' \/ pix' + 12 <= tn_addr m)) ->
4096 <= pix' -> pix' + 12 <= alloc_ceiling -> pix' mod 4 = 0 ->
(forall j, 0 <= j < 12 -> exists b, mbyte src2segs mem' (pix' + j) = Some b) ->
SR src2segs (mkCfg (@mkst fy' regs' (Z_to_bv 64 PN_DL) mem' (seg_rom src2segs)) mdq)
(fun c' => exists (fy'' : FPState) regs'' m,
c' = mkCfg (@mkst fy'' regs'' (Z_to_bv 64 PN_LF) mem' (seg_rom src2segs)) mdq /\ frm_zero (@fp_csr fy'') /\
In m (tree_leaves v) /\ getr regs'' 14 = Z_to_bv 64 (tn_addr m) /\
(forall rr : reg, In rr NDL_KEEP -> getr regs'' rr = getr regs' rr)))
by (destruct Hv as [-> | ->]; [exact IHl | exact IHr]).
clear IHl IHr.
destruct v as [|m|nv lv rv]; [destruct Hvf | |].
-
cbn [tree_at] in Hvt. destruct Hvt as (Hmz & Hmlen & c0 & c1 & Hobjm). cbn [troot] in G9v.
destruct (Hns m (Hvn m ltac:(left; reflexivity))) as (_ & Hm0 & Hm1 & Hm16 & _).
eapply SR_mono; [exact (NDLT_run fy1 regs1 mem m c0 c1 1 ltac:(right; reflexivity) Hh Hlz G9v Hobjm Hmlen Hm0 Hm1 Hm16)|].
cbv beta. intros c2 (regs2 & -> & Hk2). change (if 1 =? 0 then PN_DL else PN_LF) with PN_LF.
exists fy1, regs2, m. split; [reflexivity|]. split; [exact Hfrm1|]. split; [apply Hvl; left; reflexivity|].
split; [rewrite (Hk2 14%bv ltac:(inK)); exact G9v|].
intros rr Hrr. rewrite (Hk2 rr (NDL_KEEP_sub rr Hrr)). apply Hk1. exact Hrr.
-
cbn [troot] in G9v.
assert (Hvt' := Hvt). cbn [tree_at] in Hvt'. fold (tree_at src2segs) in Hvt'. destruct Hvt' as (Hmz & Hmlen & Hobjv & _ & _).
destruct (Hns nv (Hvn nv ltac:(left; reflexivity))) as (_ & Hm0 & Hm1 & Hm16 & _).
eapply SR_bind; [exact (NDLT_run fy1 regs1 mem nv (troot lv) (troot rv) 0 ltac:(left; reflexivity) Hh Hlz G9v Hobjv Hmlen Hm0 Hm1 Hm16)|].
cbv beta. intros c2 (regs2 & -> & Hk2). change (if 0 =? 0 then PN_DL else PN_LF) with PN_DL.
eapply SR_mono.
{ apply (IHv nv lv rv fy1 regs2 mem pix eq_refl Hh Hlz Hfrm1); try assumption.
- rewrite (Hk2 14%bv ltac:(inK)). exact G9v.
- rewrite (Hk2 13%bv ltac:(inK)), (Hk1 13%bv ltac:(inK)). exact G13.
- intros m Hm. apply Hns. apply Hvn. exact Hm. }
cbv beta. intros c3 (fy3 & regs3 & m & -> & Hfrm3 & Hlm & G9m & Hk3).
exists fy3, regs3, m. split; [reflexivity|]. split; [exact Hfrm3|]. split; [apply Hvl; exact Hlm|]. split; [exact G9m|].
intros rr Hrr. rewrite (Hk3 rr Hrr), (Hk2 rr (NDL_KEEP_sub rr Hrr)). apply Hk1. exact Hrr.
Qed.
Definition ss_NLF : sstate :=
mkSS PN_LF sr_atoms [ YQ0b.mkRegion (Some 14%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (nd_lits 1)) ] None
(mkFacts [ (14%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Definition NLF_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NLEAF_run : forall (fy : FPState) (regs : bvmap 5 word) mem (m : tnode) (c0 c1 : Z),
m_halted mdq = None -> m_vm_lazy mdq = [] ->
getr regs 14 = Z_to_bv 64 (tn_addr m) ->
obj_at src2segs mem (tn_addr m) LAY_Node (node_vals c0 c1 m 1) -> length (tn_mean m) = 3%nat ->
4096 <= tn_addr m -> tn_addr m + NODE_SIZE <= alloc_ceiling -> tn_addr m mod 16 = 0 ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LF) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 PN_ST) mem (seg_rom src2segs)) mdq /\
(forall rr : reg, In rr NLF_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem m c0 c1 Hh Hlz G14 Hobj Hlen Hn0 Hn1 Hn16.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 m 1) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 m 1) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 m 1 Hlen) in Hobj, HV.
assert (U14 : bv_unsigned (ew E 14) = tn_addr m) by (rewrite (HE 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E ss_NLF (@mkst fy regs (Z_to_bv 64 PN_LF) mem (seg_rom src2segs))).
{ unfold ss_NLF. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen src2segs _ mem 14 (tn_addr m)); [exact U14 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U14. change (2 ^ 4) with 16. repeat split; lia. }
pure_to src2tbl_ok HS PN_ST. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NLF_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NST : sstate :=
mkSS PN_ST sr_atoms [ YQ0b.mkRegion (Some 32%nat) 0 1 0 1 [] ] None
(mkFacts [ (25%nat, mkAF 4096 CEIL_MAX 0); (11%nat, mkAF 0 RGB_NMAX 0); (12%nat, mkAF 0 RGB_NMAX 0); (32%nat, mkAF 4096 CEIL_MAX 0) ] []
[ (SAlu ALU_ADD (SOff 25 0) (SOff 11 0), SOff 32%nat 0) ]).
Definition NST_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NST_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq ->
getr regs 25 = Z_to_bv 64 fimg -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 N ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_ST) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs' mem',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if i + 1 <? N then PN_LH else PC_QE)) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\
(forall a, 0 <= a < 2 ^ 64 -> a <> fimg + i -> mbyte src2segs mem' a = mbyte src2segs mem a) /\
getr regs' 11 = Z_to_bv 64 (i + 1) /\
(forall rr : reg, In rr NST_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i Hi HJ G25 G11 G12.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
set (E := Ereg regs (map (Z_to_bv 64) [fimg + i] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (fimg + i)) by (subst E; apply (Ereg_vals regs [fimg + i] [] 0%nat); reflexivity).
assert (U25 : bv_unsigned (ew E 25) = fimg) by (rewrite (HE 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = i) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = fimg + i) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E ss_NST (@mkst fy regs (Z_to_bv 64 PN_ST) mem (seg_rom src2segs))).
{ unfold ss_NST. apply entry_st_ok_env.
- subst E; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (fimg_writable mem HJ); lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25, U11, U12, U32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok]. split; [|exact I].
rewrite (U_add2 E 25 11 fimg i U25 U11) by lia. cbn [sv_denot]. rewrite Z.add_0_r, U32. reflexivity. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PN_ST) mem (seg_rom src2segs))) in HJ.
assert (Hwr : forall cs, wr_ok E [YQ0b.mkRegion (Some 32%nat) 0 1 0 1 cs] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros cs. eapply wr_ok_cons_gen; [reflexivity | exact U32 | cbn [r_wlo r_whi]; intros a Ha; replace a with (fimg + (a - fimg)) by lia; apply Hwbg; lia | apply wr_ok_nil]. }
assert (POST : forall ss1 (msx : machine_state), @st_ok src2segs fy E ss1 msx ->
sr_get (ss_regs ss1) 11%bv = SOff 11%nat 1 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss1) rr) (SOff (ridx rr) 0)) NST_KEEP = true ->
getr (ms_regs msx) 11 = Z_to_bv 64 (i + 1) /\ (forall rr : reg, In rr NST_KEEP -> getr (ms_regs msx) rr = getr regs rr)).
{ intros ss1 msx HS1 Q11 Hkb.
split; [rewrite (st_ok_reg src2segs E ss1 _ 11%bv HS1), Q11; cbn [sv_denot]; rewrite U11; reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NST_KEEP HS1 (env_agree_refl _ _) Hkb). }
jrun_to LAWS src2tbl_ok HS HJ PC_QE. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF, HJ.
jbranch src2tbl HS.
- rewrite branch_ne_U, !U_SOff, U11, U12, !zcanon_id in Hc by (unfold M64; lia).
destruct (Z_lt_ge_dec (i + 1) N) as [Hlt|Hge]; [| exfalso; destruct (Z.eqb_spec (i + 1) (N + 0)); [discriminate Hc | lia]].
jrun_to LAWS src2tbl_ok HS HJ PN_LH. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ. replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite (st_ok_mkst src2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split; [intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity|].
eapply (POST _ _ HS); [reflexivity | vm_compute; reflexivity].
- rewrite branch_ne_U, !U_SOff, U11, U12, !zcanon_id in Hc by (unfold M64; lia).
destruct (Z_lt_ge_dec (i + 1) N) as [Hlt|Hge]; [exfalso; destruct (Z.eqb_spec (i + 1) (N + 0)); [lia | discriminate Hc] |].
jrun_to LAWS src2tbl_ok HS HJ PC_QE. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ. replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (st_ok_mkst src2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split; [intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity|].
eapply (POST _ _ HS); [reflexivity | vm_compute; reflexivity].
Qed.
End e.
End d.
End c.
