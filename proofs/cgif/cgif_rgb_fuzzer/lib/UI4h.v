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
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
UI3h UI4v UI4u YP12.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac inK := repeat (first [left; apply bv_eq; reflexivity | right]).
Definition PN_LH : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x144c).
Definition PN_CL : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1528).
Definition PN_RT : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1548).
Definition PN_TR : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1588).
Definition PN_QE : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x15ac).
Definition PN_EN : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1418).
Lemma alias_fi : forall E k x y, bv_unsigned (ew E 24) = x -> bv_unsigned (ew E 9) = y -> bv_unsigned (ew E k) = x + 4 * y ->
0 <= x -> 0 <= y < 2 ^ 32 -> x + 4 * y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 9 0) (SLit 2))) = sv_denot E (SOff k 0).
Proof.
intros E k x y Hx Hy Hk Hx0 Hy0 Hxy. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit, Hx, Hy, Hk, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (y * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Ltac nst_reg HS :=
lazymatch goal with |- getr _ ?rr = _ =>
let Q := fresh "Q" in
pose proof (st_ok_reg ubs2segs _ _ _ rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q; rewrite Q; clear Q
end.
Ltac nen_reg HS :=
lazymatch goal with |- getr _ ?rr = _ =>
let Q := fresh "Q" in
pose proof (st_okF_reg ubs2segs _ _ _ rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q; rewrite Q; clear Q
end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section e.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis Hbefb : bef <> 0 -> (beffmt = 3 \/ beffmt = 4) /\ In (bef, beffmt * N) (blocks Lq Aq) /\ (bef + beffmt * N <= flt \/ flt + 4 * M <= bef).
Hypothesis Rbef : 0 <= bef < 2 ^ 64.
Definition memIN (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (fimg <= a < fimg + N) -> mbyte ubs2segs m a = mbyte ubs2segs memD a.
Lemma memIN_trans : forall m m', memIN m ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (fimg <= a < fimg + N) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) -> memIN m'.
Proof. intros m m' Hm Hk a Ha H1. rewrite (Hk a Ha H1). apply Hm; assumption. Qed.
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5168 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 166.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte ubs2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma bef_present : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq -> bef <> 0 ->
forall i, 0 <= i < beffmt * N -> exists b, mbyte ubs2segs m (bef + i) = Some b.
Proof.
intros m HJ Hb i Hi. destruct (Hbefb Hb) as (_ & Hin & _). apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq bef (beffmt * N) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hin Hi)).
Qed.
Lemma bef_range : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq -> bef <> 0 ->
4096 <= bef /\ bef + beffmt * N <= alloc_ceiling.
Proof.
intros m HJ Hb. destruct (Hbefb Hb) as (Hbf & Hin & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bef (beffmt * N) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hin ltac:(lia)) as (X1 & X2 & _). lia.
Qed.
Lemma fimg_writable : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, fimg <= a < fimg + N -> writable_at ubs2segs m a.
Proof.
intros m HJ a Ha. replace a with (fimg + (a - fimg)) by lia. apply (present_writable ubs2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq fimg N (a - fimg) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia))).
Qed.

Definition NT_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition NTB_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
Definition ntest_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' (ti : bool),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if ti then PN_TR else PN_CL)) mem (seg_rom ubs2segs)) mdq /\ frm_zero (@fp_csr fy') /\
(forall rr : reg, In rr NT_KEEP -> getr regs' rr = getr regs rr).
Definition ss_NT0 : sstate :=
mkSS PN_LH sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk 88 (CVal 8 (SLit 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [mkAC BC_NE (SOff 18%nat 0) (SLit 0)] []).
Lemma NT0_run : forall (fy : FPState) (regs : bvmap 5 word) mem,
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy) -> slot regs0 mem 88 0 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 18 = Z_to_bv 64 1 ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs)) mdq) (ntest_post fy regs mem).
Proof.
intros fy regs mem Hh Hlz Hfrm S88 G2 G18. pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U18 : bv_unsigned (ew E 18) = 1) by (rewrite (HE 18%nat 18%bv eq_refl), G18; reflexivity).
assert (HS : @st_ok ubs2segs fy E ss_NT0 (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs))).
{ unfold ss_NT0. apply entry_st_ok_env.
- subst E; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S88].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2.
change (2 ^ 4) with 16. unfold sp, sp0 in *.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I].
rewrite branch_ne_U, U_SOff, U_SLit, U18. reflexivity. }
pure_to ubs2tbl_ok HS PN_CL. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists fy, rg, false end.
split; [reflexivity|]. split; [exact Hfrm|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NTAx : sstate :=
mkSS PN_LH sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 16 0 0 [mkChunk 0 (CData 0 0 16)] ] None
(mkFacts [ (9%nat, mkAF 0 (2^20) 0); (21%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0); (32%nat, mkAF 4096 CEIL_MAX 2) ]
[mkAC BC_EQ (SOff 18%nat 0) (SLit 0)]
[ (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 9 0) (SLit 2)), SOff 32%nat 0) ]).
Definition ss_NTA : sstate := mkSST PN_LH (ss_regs ss_NTAx) (sfr_atoms 64) (ss_mem ss_NTAx) None (ss_facts ss_NTAx).
Lemma NTA_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> fmt = 4 ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 18 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 (fmt * i) -> getr regs 24 = Z_to_bv 64 flt ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - flt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs)) mdq) (ntest_post fy regs mem).
Proof.
intros fy regs mem i Hi F4 HJ Hfrm G18 G9 G24 G21.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 16 <= 4 * M) by (subst M; nia).
destruct (bytes_of_present ubs2segs mem (flt + 4 * (fmt * i)) 16 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0).
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * (fmt * i)]) [b0]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * (fmt * i))) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (U18 : bv_unsigned (ew E0 18) = 0) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; reflexivity).
assert (U9 : bv_unsigned (ew E0 9) = fmt * i) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; nia).
assert (U24 : bv_unsigned (ew E0 24) = flt) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E0 21) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * (fmt * i)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (HS0 : @st_ok ubs2segs fy E0 ss_NTAx (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs))).
{ unfold ss_NTAx. apply entry_st_ok_env.
- subst E0; apply regs_ok_EregB.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 16 with (Z.of_nat (length b0)) by (rewrite Lb0; reflexivity).
apply (chunk_ok_data ubs2segs E0 mem _ 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0. rewrite <- Lb0. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U21, U32.
change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * (fmt * i)) mod 4 = 0) by (replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
repeat split; try lia; nia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I].
rewrite branch_eq_U, U_SOff, U_SLit, U18. reflexivity.
+ cbn [f_alias alias_ok]. split; [|exact I].
exact (alias_fi E0 32 flt (fmt * i) U24 U9 U32 ltac:(lia) ltac:(nia) ltac:(nia)). }
pose proof (st_ok_enterF ubs2segs fy 64 E0 ss_NTAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_NTAx) (ss_regs ss_NTAx) (sfr_atoms 64) (ss_mem ss_NTAx) (ss_resv ss_NTAx) (ss_facts ss_NTAx)) with ss_NTA in HS.
clear HS0.
assert (POST : forall (ssx : sstate) (msx : machine_state) (ti : bool), st_okF ubs2segs E ssx msx -> ss_resv ssx = None ->
ss_pc ssx = (if ti then PN_TR else PN_CL) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) NT_KEEP = true ->
ms_mem msx = mem ->
ntest_post fy regs mem (mkCfg msx mdq)).
{ intros ssx msx ti HSx Hrv Hpc Hkb Hmm. exists (fp_of msx), (ms_regs msx), ti.
split; [rewrite (st_okF_mkst ubs2segs E ssx msx HSx Hrv), Hpc, Hmm; reflexivity|]. split; [exact (st_okF_frm ubs2segs E _ _ HSx)|].
exact (st_okF_regs_kept ubs2segs E ssx msx _ NT_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb). }
pureF_to ubs2tbl_ok HS PN_TR. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). cbn [ms_mem mkst] in Hmem.
jbranchF ubs2tbl HS.
-
pureF_to ubs2tbl_ok HS PN_CL. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | rewrite Hmem0; exact Hmem].
-
pureF_to ubs2tbl_ok HS PN_TR. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
eapply (POST _ _ true HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | rewrite Hmem0; exact Hmem].
Qed.
Definition ss_NTBx : sstate :=
mkSS PN_LH (sr_set sr_atoms 25%bv (SOff 33 2))
[ YQ0b.mkRegion (Some 32%nat) 0 12 0 0 [mkChunk 0 (CData 0 0 12)]; YQ0b.mkRegion (Some 35%nat) 0 3 0 0 [mkChunk 0 (CData 1 0 3)];
YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk 88 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 0 (2^20) 0); (21%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
(22%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0); (32%nat, mkAF 4096 CEIL_MAX 2); (33%nat, mkAF 0 (2^20) 0);
(34%nat, mkAF 4096 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0) ]
[mkAC BC_NE (SOff 18%nat 0) (SLit 0)]
[ (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 9 0) (SLit 2)), SOff 32%nat 0); (SAlu ALU_ADD (SOff 34 0) (SOff 33 0), SOff 35%nat 0) ]).
Definition ss_NTB : sstate := mkSST PN_LH (ss_regs ss_NTBx) (sfr_atoms 64) (ss_mem ss_NTBx) None (ss_facts ss_NTBx).
Lemma NTB_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> bef <> 0 ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> slot regs0 mem 88 bef ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 18 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 (fmt * i) -> getr regs 24 = Z_to_bv 64 flt ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - flt) -> getr regs 22 = Z_to_bv 64 (2 ^ 64 - 1 - bef) ->
getr regs 25 = Z_to_bv 64 (beffmt * i + 2) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs)) mdq) (ntest_post fy regs mem).
Proof.
intros fy regs mem i Hi Hb HJ Hfrm S88 G2 G18 G9 G24 G21 G22 G25.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct (Hbefb Hb) as (Hbf & _ & Hbsep). destruct (bef_range mem HJ Hb) as [Hb0 Hb1].
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia).
assert (Hbi : 0 <= beffmt * i /\ beffmt * i + 3 <= beffmt * N) by nia.
destruct (bytes_of_present ubs2segs mem (flt + 4 * (fmt * i)) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0').
destruct (bytes_of_present ubs2segs mem (bef + beffmt * i) 3 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (bef_present mem HJ Hb); lia)) as (b1 & Lb1 & Hb1').
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * (fmt * i); beffmt * i; bef; bef + beffmt * i]) [b0; b1]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * (fmt * i))) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 (beffmt * i)) by (subst E0; apply (EregB_vals regs _ _ 1%nat); reflexivity).
assert (A34 : ew E0 34 = Z_to_bv 64 bef) by (subst E0; apply (EregB_vals regs _ _ 2%nat); reflexivity).
assert (A35 : ew E0 35 = Z_to_bv 64 (bef + beffmt * i)) by (subst E0; apply (EregB_vals regs _ _ 3%nat); reflexivity).
assert (U2 : bv_unsigned (ew E0 2) = spv) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U18 : bv_unsigned (ew E0 18) = 1) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; reflexivity).
assert (U9 : bv_unsigned (ew E0 9) = fmt * i) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; nia).
assert (U24 : bv_unsigned (ew E0 24) = flt) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E0 21) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E0 22) = 2 ^ 64 - 1 - bef) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * (fmt * i)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = beffmt * i) by (rewrite A33; apply unsigned_lit_small; nia).
assert (U34 : bv_unsigned (ew E0 34) = bef) by (rewrite A34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E0 35) = bef + beffmt * i) by (rewrite A35; apply unsigned_lit_small; nia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (HS0 : @st_ok ubs2segs fy E0 ss_NTBx (@mkst fy regs (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs))).
{ unfold ss_NTBx. apply entry_st_ok_env.
- apply regs_ok_pin; [subst E0; apply regs_ok_EregB | intros X; discriminate X |].
rewrite G25. cbn [sv_denot]. rewrite U33. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length b0)) by (rewrite Lb0; reflexivity).
apply (chunk_ok_data ubs2segs E0 mem _ 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0'. rewrite <- Lb0. exact Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U35.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace (CData 1 0 3) with (CData 1 0 (Z.of_nat (length b1))) by (rewrite Lb1; reflexivity).
apply (chunk_ok_data ubs2segs E0 mem _ 0 1 b1 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb1'. rewrite <- Lb1. exact Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S88].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U32, U35, U2.
split; [split; [subst M; nia | split; [unfold sp, sp0 in *; subst M; nia | exact I]]|].
split; [split; [unfold sp, sp0 in *; nia | exact I] | exact (conj I I)].
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U21, U22, U32, U33, U34, U35.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * (fmt * i)) mod 4 = 0) by (replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
unfold sp, sp0 in *. repeat split; try lia; nia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I].
rewrite branch_ne_U, U_SOff, U_SLit, U18. reflexivity.
+ cbn [f_alias alias_ok].
split; [exact (alias_fi E0 32 flt (fmt * i) U24 U9 U32 ltac:(lia) ltac:(nia) ltac:(nia))|].
split; [|exact I]. rewrite (U_add2 E0 34 33 bef (beffmt * i) U34 U33) by nia. cbn [sv_denot]. rewrite Z.add_0_r, U35. reflexivity. }
pose proof (st_ok_enterF ubs2segs fy 64 E0 ss_NTBx _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_NTBx) (ss_regs ss_NTBx) (sfr_atoms 64) (ss_mem ss_NTBx) (ss_resv ss_NTBx) (ss_facts ss_NTBx)) with ss_NTB in HS.
clear HS0.
assert (POST : forall (ssx : sstate) (msx : machine_state) (ti : bool), st_okF ubs2segs E ssx msx -> ss_resv ssx = None ->
ss_pc ssx = (if ti then PN_TR else PN_CL) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) NTB_KEEP = true ->
sr_get (ss_regs ssx) 25%bv = SOff 33 2 ->
ms_mem msx = mem ->
ntest_post fy regs mem (mkCfg msx mdq)).
{ intros ssx msx ti HSx Hrv Hpc Hkb Q25 Hmm. exists (fp_of msx), (ms_regs msx), ti.
split; [rewrite (st_okF_mkst ubs2segs E ssx msx HSx Hrv), Hpc, Hmm; reflexivity|]. split; [exact (st_okF_frm ubs2segs E _ _ HSx)|].
pose proof (st_okF_regs_kept ubs2segs E ssx msx _ NTB_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb) as HK.
assert (X25 : getr (ms_regs msx) 25 = getr regs 25).
{ rewrite (st_okF_reg ubs2segs E ssx msx 25%bv HSx), Q25, G25. cbn [sv_denot]. rewrite (HEE 33%nat) by lia. rewrite U33. reflexivity. }
intros rr Hrr. unfold NT_KEEP in Hrr. cbn [In] in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [first [exact X25 | apply HK; inK] |]). destruct Hrr. }
pureF_to ubs2tbl_ok HS PN_TR. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). cbn [ms_mem mkst] in Hmem.
jbranchF ubs2tbl HS.
-
pureF_to ubs2tbl_ok HS PN_CL. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | rewrite Hmem0; exact Hmem].
- pureF_to ubs2tbl_ok HS PN_TR. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms0). cbn [ms_mem mkst] in Hmem0.
jbranchF ubs2tbl HS.
+
pureF_to ubs2tbl_ok HS PN_CL. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms1). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | rewrite Hmem1, Hmem0; exact Hmem].
+ pureF_to ubs2tbl_ok HS PN_TR. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms1). cbn [ms_mem mkst] in Hmem1.
jbranchF ubs2tbl HS.
*
pureF_to ubs2tbl_ok HS PN_TR. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms2). apply SR_ret.
eapply (POST _ _ true HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | rewrite Hmem2, Hmem1, Hmem0; exact Hmem].
*
pureF_to ubs2tbl_ok HS PN_CL. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms2). apply SR_ret.
eapply (POST _ _ false HS); [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | rewrite Hmem2, Hmem1, Hmem0; exact Hmem].
Qed.
Definition ss_NCL : sstate :=
mkSS PN_CL sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk 80 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 0 (2^20) 0); (21%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0) ] []
[ (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 9 0) (SLit 2)), SOff 32%nat 0) ]).
Definition NCL_KEEP : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma NCL_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i tr : Z),
0 <= i < N -> 0 <= tr < 2 ^ 64 ->
m_halted mdq = None -> m_vm_lazy mdq = [] -> slot regs0 mem 80 tr ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 9 = Z_to_bv 64 (fmt * i) -> getr regs 24 = Z_to_bv 64 flt ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - flt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_CL) mem (seg_rom ubs2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 ubs2_A_get_leave_node_index) mem (seg_rom ubs2segs)) mdq /\
getr regs' 1 = Z_to_bv 64 PN_RT /\ getr regs' 10 = Z_to_bv 64 tr /\ getr regs' 11 = Z_to_bv 64 (flt + 4 * (fmt * i)) /\
(forall rr : reg, In rr NCL_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i tr Hi Htr Hh Hlz S80 G2 G9 G24 G21. pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia).
set (E := Ereg regs (map (Z_to_bv 64) [flt + 4 * (fmt * i); tr] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (flt + 4 * (fmt * i))) by (subst E; apply (Ereg_vals regs [flt + 4 * (fmt * i); tr] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 tr) by (subst E; apply (Ereg_vals regs [flt + 4 * (fmt * i); tr] [] 1%nat); reflexivity).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U9 : bv_unsigned (ew E 9) = fmt * i) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; nia).
assert (U24 : bv_unsigned (ew E 24) = flt) by (rewrite (HE 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = 2 ^ 64 - 1 - flt) by (rewrite (HE 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = flt + 4 * (fmt * i)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok ubs2segs fy E ss_NCL (@mkst fy regs (Z_to_bv 64 PN_CL) mem (seg_rom ubs2segs))).
{ unfold ss_NCL. apply entry_st_ok_env.
- subst E; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S80].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U21.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
unfold sp, sp0 in *. repeat split; try lia; nia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok]. split; [|exact I].
exact (alias_fi E 32 flt (fmt * i) U24 U9 U32 ltac:(lia) ltac:(nia) ltac:(nia)). }
pure_to ubs2tbl_ok HS ubs2_A_get_leave_node_index. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => exists rg end. split; [reflexivity|].
split; [pose proof (st_ok_reg ubs2segs E _ _ 1%bv HS) as Q; eval_sr_get_in Q; cbn [ms_regs mkst sv_denot] in Q; rewrite Q; reflexivity|].
split; [pose proof (st_ok_reg ubs2segs E _ _ 10%bv HS) as Q; eval_sr_get_in Q; cbn [ms_regs mkst sv_denot] in Q;
rewrite Q, Z.add_0_r, Z_to_bv_bv_unsigned, A33; reflexivity|].
split; [pose proof (st_ok_reg ubs2segs E _ _ 11%bv HS) as Q; eval_sr_get_in Q; cbn [ms_regs mkst sv_denot] in Q;
rewrite Q, Z.add_0_r, Z_to_bv_bv_unsigned, A32; reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NCL_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NST (pc0 : Z) : sstate :=
mkSS pc0 sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 1 [];
YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk 48 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0)); mkChunk 120 (CVal 8 (SOff 35 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (19%nat, mkAF 0 RGB_NMAX 0); (23%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0) ] []
[ (SAlu ALU_ADD (SOff 33 0) (SOff 19 0), SOff 32%nat 0) ]).
Definition NST_KEEP : list reg := [1; 2; 3; 4; 5; 6; 8; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
Lemma NST_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i bfw : Z) (b : bool),
0 <= i < N -> 0 <= bfw < 2 ^ 64 ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq ->
slot regs0 mem 48 fimg -> slot regs0 mem 104 bfw -> slot regs0 mem 120 fmt ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 19 = Z_to_bv 64 i -> getr regs 27 = Z_to_bv 64 N ->
getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 9 = Z_to_bv 64 (fmt * i) -> getr regs 25 = Z_to_bv 64 (bfw * i + 2) ->
(b = false -> getr regs 7 = Z_to_bv 64 fmt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 (if b then PN_RT else PN_TR)) mem (seg_rom ubs2segs)) mdq)
(fun c' => exists regs' mem',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if i + 1 <? N then PN_LH else PN_QE)) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\
(forall a, 0 <= a < 2 ^ 64 -> a <> fimg + i -> mbyte ubs2segs mem' a = mbyte ubs2segs mem a) /\
getr regs' 19 = Z_to_bv 64 (i + 1) /\ getr regs' 9 = Z_to_bv 64 (fmt * (i + 1)) /\
getr regs' 25 = Z_to_bv 64 (bfw * (i + 1) + 2) /\ getr regs' 7 = Z_to_bv 64 fmt /\
(forall rr : reg, In rr NST_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i bfw b Hi Hbw HJ S48 S104 S120 G2 G19 G27 G23 G9 G25 G7.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
set (E := Ereg regs (map (Z_to_bv 64) [fimg + i; fimg; bfw; fmt] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (fimg + i)) by (subst E; apply (Ereg_vals regs [fimg + i; fimg; bfw; fmt] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs [fimg + i; fimg; bfw; fmt] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 bfw) by (subst E; apply (Ereg_vals regs [fimg + i; fimg; bfw; fmt] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 fmt) by (subst E; apply (Ereg_vals regs [fimg + i; fimg; bfw; fmt] [] 3%nat); reflexivity).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U19 : bv_unsigned (ew E 19) = i) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = N) by (rewrite (HE 27%nat 27%bv eq_refl), G27; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = 2 ^ 64 - 1 - fimg) by (rewrite (HE 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = fimg + i) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = fimg) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS : @st_ok ubs2segs fy E (ss_NST (if b then PN_RT else PN_TR)) (@mkst fy regs (Z_to_bv 64 (if b then PN_RT else PN_TR)) mem (seg_rom ubs2segs))).
{ unfold ss_NST. apply entry_st_ok_env.
- subst E; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (fimg_writable mem HJ); lia | constructor].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S48].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S104].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S120].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U32, U2.
split; [split; [unfold sp, sp0 in *; lia | exact I] | exact (conj I I)].
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U19, U23, U32, U33.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
unfold sp, sp0 in *. repeat split; lia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok]. split; [|exact I].
rewrite (U_add2 E 33 19 fimg i U33 U19) by lia. cbn [sv_denot]. rewrite Z.add_0_r, U32. reflexivity. }
assert (Hwr : forall cs r2, r_whi r2 <= r_wlo r2 -> wr_ok E [YQ0b.mkRegion (Some 32%nat) 0 1 0 1 cs; r2] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros cs r2 Hr2. eapply wr_ok_cons_gen; [reflexivity | exact U32 | cbn [r_wlo r_whi]; intros a Ha; replace a with (fimg + (a - fimg)) by lia; apply Hwbg; lia |].
apply wr_ok_cons_ro; [exact Hr2 | apply wr_ok_nil]. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 (if b then PN_RT else PN_TR)) mem (seg_rom ubs2segs))) in HJ.
destruct b.
- jrun_to LAWS ubs2tbl_ok HS HJ PN_QE. { wr_ok_eval. apply Hwr. cbn. lia. }
cbn [ms_mem mkst] in HF, HJ.
jbranch ubs2tbl HS.
+ rewrite branch_ne_U, !U_SOff, U27, U19, !zcanon_id in Hc by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PN_LH. { wr_ok_eval. apply Hwr. cbn. lia. }
cbn [ms_mem mkst] in HF0, HJ. replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite (st_ok_mkst ubs2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split; [intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity|].
split; [nst_reg HS; rewrite U19; reflexivity|].
split; [nst_reg HS; rewrite ?A35, ?(HE 7%nat 7%bv eq_refl), (HE 9%nat 9%bv eq_refl), G9; try rewrite (G7 eq_refl); rewrite alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; rewrite A34, (HE 25%nat 25%bv eq_refl), G25, alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; first [rewrite A35; reflexivity | rewrite (HE 7%nat 7%bv eq_refl); exact (G7 eq_refl)]|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NST_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
+ rewrite branch_ne_U, !U_SOff, U27, U19, !zcanon_id in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PN_QE. { wr_ok_eval. apply Hwr. cbn. lia. }
cbn [ms_mem mkst] in HF0, HJ. replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (st_ok_mkst ubs2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split; [intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity|].
split; [nst_reg HS; rewrite U19; reflexivity|].
split; [nst_reg HS; rewrite ?A35, ?(HE 7%nat 7%bv eq_refl), (HE 9%nat 9%bv eq_refl), G9; try rewrite (G7 eq_refl); rewrite alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; rewrite A34, (HE 25%nat 25%bv eq_refl), G25, alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; first [rewrite A35; reflexivity | rewrite (HE 7%nat 7%bv eq_refl); exact (G7 eq_refl)]|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NST_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- jrun_to LAWS ubs2tbl_ok HS HJ PN_QE. { wr_ok_eval. apply Hwr. cbn. lia. }
cbn [ms_mem mkst] in HF, HJ.
jbranch ubs2tbl HS.
+ rewrite branch_ne_U, !U_SOff, U27, U19, !zcanon_id in Hc by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PN_LH. { wr_ok_eval. apply Hwr. cbn. lia. }
cbn [ms_mem mkst] in HF0, HJ. replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite (st_ok_mkst ubs2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split; [intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity|].
split; [nst_reg HS; rewrite U19; reflexivity|].
split; [nst_reg HS; rewrite ?A35, ?(HE 7%nat 7%bv eq_refl), (HE 9%nat 9%bv eq_refl), G9; try rewrite (G7 eq_refl); rewrite alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; rewrite A34, (HE 25%nat 25%bv eq_refl), G25, alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; first [rewrite A35; reflexivity | rewrite (HE 7%nat 7%bv eq_refl); exact (G7 eq_refl)]|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NST_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
+ rewrite branch_ne_U, !U_SOff, U27, U19, !zcanon_id in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PN_QE. { wr_ok_eval. apply Hwr. cbn. lia. }
cbn [ms_mem mkst] in HF0, HJ. replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (st_ok_mkst ubs2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split; [intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity|].
split; [nst_reg HS; rewrite U19; reflexivity|].
split; [nst_reg HS; rewrite ?A35, ?(HE 7%nat 7%bv eq_refl), (HE 9%nat 9%bv eq_refl), G9; try rewrite (G7 eq_refl); rewrite alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; rewrite A34, (HE 25%nat 25%bv eq_refl), G25, alu64_add_lit; f_equal; ring|].
split; [nst_reg HS; first [rewrite A35; reflexivity | rewrite (HE 7%nat 7%bv eq_refl); exact (G7 eq_refl)]|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NST_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_NENx : sstate :=
mkSS PN_EN sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (25%nat, mkAF 1 RGB_NMAX 0) ] []
[ (SAlu ALU_XOR (SOff 24 0) (SLit (-1)), SOff 34%nat 0); (SAlu ALU_XOR (SOff 33 0) (SLit (-1)), SOff 35%nat 0);
(SAlu ALU_XOR (SOff 32 0) (SLit (-1)), SOff 36%nat 0) ]).
Definition ss_NEN : sstate := mkSST PN_EN (ss_regs ss_NENx) (sfr_atoms 64) (ss_mem ss_NENx) None (ss_facts ss_NENx).
Definition NEN_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 12; 13; 14; 15; 16; 17; 18; 20; 24; 28; 29; 30; 31]%bv.
Lemma NEN_run : forall (fy : FPState) (regs : bvmap 5 word) mem,
m_halted mdq = None -> m_vm_lazy mdq = [] -> frm_zero (@fp_csr fy) -> slot regs0 mem 48 fimg -> slot regs0 mem 88 bef ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 25 = Z_to_bv 64 N -> getr regs 24 = Z_to_bv 64 flt ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PN_EN) mem (seg_rom ubs2segs)) mdq)
(fun c' => exists (fy' : FPState) regs', c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PN_LH) mem (seg_rom ubs2segs)) mdq /\
frm_zero (@fp_csr fy') /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 2 /\
getr regs' 27 = Z_to_bv 64 N /\ getr regs' 21 = Z_to_bv 64 (2 ^ 64 - 1 - flt) /\ getr regs' 22 = Z_to_bv 64 (2 ^ 64 - 1 - bef) /\
getr regs' 23 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) /\ (forall rr : reg, In rr NEN_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem Hh Hlz Hfrm S48 S88 G2 G25 G24. pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
set (vals := [fimg; bef; 2 ^ 64 - 1 - flt; 2 ^ 64 - 1 - bef; 2 ^ 64 - 1 - fimg]).
set (E0 := Ereg regs (map (Z_to_bv 64) vals ++ [])).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 fimg) by (subst E0; apply (Ereg_vals regs vals [] 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 bef) by (subst E0; apply (Ereg_vals regs vals [] 1%nat); reflexivity).
assert (A34 : ew E0 34 = Z_to_bv 64 (2 ^ 64 - 1 - flt)) by (subst E0; apply (Ereg_vals regs vals [] 2%nat); reflexivity).
assert (A35 : ew E0 35 = Z_to_bv 64 (2 ^ 64 - 1 - bef)) by (subst E0; apply (Ereg_vals regs vals [] 3%nat); reflexivity).
assert (A36 : ew E0 36 = Z_to_bv 64 (2 ^ 64 - 1 - fimg)) by (subst E0; apply (Ereg_vals regs vals [] 4%nat); reflexivity).
assert (A24 : ew E0 24 = Z_to_bv 64 flt) by (rewrite (HE0 24%nat 24%bv eq_refl); exact G24).
assert (U2 : bv_unsigned (ew E0 2) = spv) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U25 : bv_unsigned (ew E0 25) = N) by (rewrite (HE0 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok ubs2segs fy E0 ss_NENx (@mkst fy regs (Z_to_bv 64 PN_EN) mem (seg_rom ubs2segs))).
{ unfold ss_NENx. apply entry_st_ok_env.
- subst E0; apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S48].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S88].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U25.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
unfold sp, sp0 in *. repeat split; lia.
+ cbn [f_conds conds_ok]. exact I.
+ cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]]; apply U_inj.
* rewrite (U_not_off E0 24 flt 0 A24), (U_atom E0 34 _ A34) by lia. lia.
* rewrite (U_not_off E0 33 bef 0 A33), (U_atom E0 35 _ A35) by lia. lia.
* rewrite (U_not_off E0 32 fimg 0 A32), (U_atom E0 36 _ A36) by lia. lia. }
pose proof (st_ok_enterF ubs2segs fy 64 E0 ss_NENx _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_NENx) (ss_regs ss_NENx) (sfr_atoms 64) (ss_mem ss_NENx) (ss_resv ss_NENx) (ss_facts ss_NENx)) with ss_NEN in HS.
clear HS0.
pureF_to ubs2tbl_ok HS PN_LH. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret. cbn [ms_mem mkst] in Hmem.
exists (fp_of ms), (ms_regs ms).
split; [rewrite (st_okF_mkst ubs2segs E _ ms HS eq_refl), Hmem; reflexivity|]. split; [exact (st_okF_frm ubs2segs E _ _ HS)|].
split; [nen_reg HS; reflexivity|]. split; [nen_reg HS; reflexivity|]. split; [nen_reg HS; reflexivity|].
split; [nen_reg HS; rewrite (HE 25%nat 25%bv eq_refl); exact G25|].
split; [nen_reg HS; rewrite HEE by lia; exact A34|]. split; [nen_reg HS; rewrite HEE by lia; exact A35|].
split; [nen_reg HS; rewrite HEE by lia; exact A36|].
exact (st_okF_regs_kept ubs2segs E _ ms regs NEN_KEEP HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)).
Qed.
End e.
End d.
End c.
