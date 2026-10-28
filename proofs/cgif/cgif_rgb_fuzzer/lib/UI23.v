(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l UO3m YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI20 UI2r UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k UI21 UI22.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YI0d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FL_P2  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x858).
Definition FL_P2X : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x86c).
Lemma U_sll1 : forall E n k, ew E n = Z_to_bv 64 k -> 0 <= k <= 17 -> U E (SAlu ALU_SLL (SLit 1) (SOff n 0)) = 2 ^ k.
Proof.
intros E n k Hn Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_lit by lia. rewrite (U_atom _ n k Hn) by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite Z.mod_small by lia.
rewrite Z.shiftl_1_l. apply zcanon_id. unfold M64. split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
Qed.
Definition ss_p2 : sstate :=
mkSS FL_P2 (sr_set (sr_set sr_atoms 11%bv (SLit 1)) 12%bv (SLit 64)) [] None
(mkFacts [ (10%nat, mkAF 0 16 0); (20%nat, mkAF 0 65535 0) ] [] []).
Definition FL_T3 : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x8e4).
Lemma U_sll_lit : forall E a k, 0 <= k < 64 -> U E (SAlu ALU_SLL a (SLit k)) = (U E a * 2 ^ k) mod 2 ^ 64.
Proof.
intros E a k Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_lit by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma land_ffff : forall x, 0 <= x < 65536 -> Z.land x 65535 = x.
Proof. intros x Hx. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma fl_stk_word : forall (m : word -> option byte) a, CEIL_MIN <= a -> a + 8 <= 2 ^ 64 ->
(forall k, 0 <= k < 8 -> writable_at ubs2segs m (a + k)) -> exists v, 0 <= v < 2 ^ 64 /\ word_mem ubs2segs m a v.
Proof.
intros m a Ha0 Ha1 Hw.
assert (Hb : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? CEIL_MIN) ubs2segs = true) by (vm_compute; reflexivity).
destruct (YI0d.val_mem_of_present8 ubs2segs m a) as (v & Hv & HV).
- intros k Hk. specialize (Hw k Hk). unfold writable_at, wview in Hw. unfold mbyte.
destruct (m (Z_to_bv 64 (a + k))) as [b|]; [exists b; reflexivity|]. exfalso.
destruct (find_segment ubs2segs (bv_unsigned (Z_to_bv 64 (a + k))) 1) as [sg|] eqn:Hf; [| apply Hw; reflexivity].
pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2]. pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin.
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as Hle. cbn beta in Hle. apply Z.leb_le in Hle.
rewrite unsigned_lit_small in H2 by lia. lia.
- exists v. split; [exact Hv|]. apply val_mem_word_mem. exact HV.
Qed.
Definition fl_Rfn (n : nat) : YQ0b.region := YQ0b.mkRegion (Some n) 0 40 0 0 (obj_chunks_gen LAY_Frame A_F []).
Definition t_more_chunks : list YQ0b.chunk :=
[mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 81 0)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 32 (CVal 8 (SOff 83 0));
mkChunk 24 (CVal 8 (SOff 84 0)); mkChunk 16 (CVal 8 (SOff 85 0)); mkChunk 56 (CVal 8 (SOff 86 0)); mkChunk 104 (CVal 8 (SOff 88 0))].
Definition ss_t3 : sstate :=
mkSS FL_T3 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_stk_saved 32 ++ t_more_chunks ++ [mkChunk 64 (CVal 8 (SOff 87 0))]) ;
fl_Rfb 18 ] None
(mkFacts ([(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (18%nat, mkAF 4096 (CEIL_MAX - 40) 3);
(87%nat, mkAF 1 65535 0); (23%nat, mkAF 1 65535 0); (82%nat, mkAF 0 65535 0); (22%nat, mkAF 0 65535 0); (88%nat, mkAF 1 65535 0);
(8%nat, mkAF 4096 CEIL_MAX 0)] ++ fl_bfacts) [] []).
Definition t4_stk : list YQ0b.chunk :=
fl_stk_saved 32 ++ [mkChunk 112 (CVal 8 (SOff 45 0)); mkChunk 120 (CVal 8 (SOff 46 0)); mkChunk 96 (CVal 8 (SOff 47 0)); mkChunk 32 (CVal 8 (SOff 48 0));
mkChunk 24 (CVal 8 (SOff 49 0)); mkChunk 16 (CVal 8 (SOff 50 0)); mkChunk 56 (CVal 8 (SOff 51 0)); mkChunk 64 (CVal 8 (SOff 52 0));
mkChunk 40 (CVal 8 (SOff 53 0)); mkChunk 48 (CVal 8 (SOff 54 0))].
Definition ss_t4 : sstate :=
mkSS FL_TOUTX sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t4_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4)] [] []).
Definition FL_T2B : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x8b4).
Definition FL_MRET : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x8c8).
Definition FL_CRET : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x8e4).
Definition ss_t2b (pz : bool) : sstate :=
mkSS FL_T2B (if pz then sr_set sr_atoms 8%bv (SLit 0) else sr_atoms)
[ YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_stk_saved 32 ++ t_more_chunks) ; fl_Rfn 81 ] None
(mkFacts ([(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (81%nat, mkAF 4096 (CEIL_MAX - 40) 3);
(19%nat, mkAF 1 65535 0); (27%nat, mkAF 1 65535 0); (16%nat, mkAF 1 65535 0); (23%nat, mkAF 1 65535 0); (82%nat, mkAF 0 65535 0); (22%nat, mkAF 0 65535 0)]
++ (if pz then [] else [(8%nat, mkAF 1 (2^64 - 1) 0)]) ++ fl_ffacts) [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Definition P2_KEPT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma fl_pow2 : forall (n : nat) (k : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc np,
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
0 <= k <= 16 -> Z.of_nat n = 17 - k -> 0 <= np <= 65535 ->
getr regs 10 = Z_to_bv 64 k -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 64 -> getr regs 20 = Z_to_bv 64 np ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_P2) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' (p : Z), c' = mkCfg (mkst regs' (Z_to_bv 64 FL_P2X) mem' (seg_rom ubs2segs)) mdc /\
(forall x, mem' x = memc x) /\ journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
getr regs' 10 = Z_to_bv 64 p /\ 0 <= p <= 16 /\
(forall r : reg, In r P2_KEPT -> getr regs' r = getr regs r)).
Proof.
intros n. induction n as [|n IH]; intros k STK sp0 FP L A mem md Lc Ac mdc regs memc np HJ Hk Hn Hnp G10 G11 G12 G20; [lia|].
set (E := Ereg regs []).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE10 : ew E 10 = Z_to_bv 64 k) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE20 : ew E 20 = Z_to_bv 64 np) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HFA : atoms_ok E [ (10%nat, mkAF 0 16 0); (20%nat, mkAF 0 65535 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE10, HE20, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok ubs2segs E ss_p2 (mkst regs (Z_to_bv 64 FL_P2) memc (seg_rom ubs2segs))).
{ unfold ss_p2. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor | cbn [pairwise_disjoint all_disjoint]; exact I | split; [exact HFA | split; exact I]].
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite G11; reflexivity] | intros Hx; discriminate Hx |].
rewrite G12. reflexivity. }
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_P2) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch ubs2tbl HS.
-
rewrite branch_geu_U, (U_sll1 E 10 k HE10 ltac:(lia)), (U_atom _ 20 np HE20) in Hc by lia.
jrun_to LAWS ubs2tbl_ok HS HJ FL_P2X. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall x, ms_mem ms0 x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs [] P2_KEPT HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
apply SR_ret. exists (ms_regs ms0), (ms_mem ms0), k.
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); reflexivity|]. split; [exact K2|]. split; [exact HJ|].
split; [reg_nowF HS ltac:(rewrite HE10, unsigned_lit_small by lia; f_equal; lia) |]. split; [lia|].
exact HKR.
-
rewrite branch_geu_U, (U_sll1 E 10 k HE10 ltac:(lia)), (U_atom _ 20 np HE20) in Hc by lia.
apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc.
assert (Hk15 : k <= 15).
{ destruct (Z.le_gt_cases k 15) as [|Hgt]; [assumption|]. exfalso. assert (k = 16) by lia. subst k. change (2 ^ 16) with 65536 in Hc. lia. }
jrun_to LAWS ubs2tbl_ok HS HJ FL_P2. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall x, ms_mem ms0 x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs [] P2_KEPT HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (k + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ np); [ | lia | lia | exact Hnp | | | | ].
- eapply (journal_exec _ _ LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; cbn [ms_mem mkst]; reflexivity | apply mem_grows_of_eq; intros x; reflexivity | intros a []].
- reg_nowF HS ltac:(rewrite HE10, unsigned_lit_small by lia; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20. }
cbv beta. intros c' (regs' & mem' & p & -> & Hm & HJ' & Hp & Hpr & HK'). exists regs', mem', p.
split; [reflexivity|]. split; [intros x; rewrite Hm; apply K2|]. split; [exact HJ'|]. split; [exact Hp|]. split; [exact Hpr|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
Qed.
Local Ltac cw Hcs off e HEx :=
apply (chunk_word _ _ _ off _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk off (CVal 8 e)) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; try ew_havocA; rewrite Z.add_0_r, HEx, Z_to_bv_bv_unsigned; reflexivity | ].
Lemma fl_t3 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (pTmp Nt tv w h top left : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
nth_error (cg_frames s) (i - 1) = Some (Some b) ->
(forall b' n a, In (b', n) (cgif_blocks g s N) -> b' <= a < b' + n -> inFP FP a) ->
Permutation (blocks Lc Ac) ((pTmp, Nt) :: cgif_blocks g s N ++ rest) ->
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
1 <= w -> 0 <= left -> left + w <= cg_W s -> 1 <= h -> 0 <= top -> top + h <= cg_H s -> w * h <= Nt -> 0 <= tv < 2 ^ 64 ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 9 = Z_to_bv 64 tv ->
getr regs1 23 = Z_to_bv 64 w -> word_mem ubs2segs memc (sp0 - 272 + 96) top -> getr regs1 22 = Z_to_bv 64 left ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> word_mem ubs2segs memc (sp0 - 272 + 112) g -> word_mem ubs2segs memc (sp0 - 272 + 120) (fr_ptr f) ->
getr regs1 18 = Z_to_bv 64 (fr_ptr b) -> getr regs1 8 = Z_to_bv 64 pTmp ->
word_mem ubs2segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) -> word_mem ubs2segs memc (sp0 - 272 + 104) (cg_W s) ->
word_mem ubs2segs memc (sp0 - 272 + 64) h ->
fl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_T3) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP pTmp Nt tv w h top left sp0
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf Hb HFP HB Htmp_fp Hw Hl0 Hlw Hh Ht0 Hth Hwh Htv HSV
G9 G23 Wtop G22 G2 Wg Wf G18 G8 WuL WW Whgt [G3 G4].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ ((pTmp, Nt) :: rest))).
{ eapply Permutation_trans; [exact HB|]. apply Permutation_middle. }
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HBc) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom API Lc Ac memc mdc g s N _ f HH0 HBc Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
destruct (fl_img_geom API Lc Ac memc mdc g s N _ b HH0 HBc Hbin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Hbi0 Hbi1].
pose proof (af_frames_sep API Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HBc Hf Hb ltac:(lia)) as Hfb.
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (Hfrs b Hb1in) as Hbobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf. pose proof (obj_at_range _ _ _ _ _ Hbobj) as Rb.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
assert (Htin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Htin) as [T0 T1].
assert (Hbimgin : In (fr_img b, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif g s N b); [exact Hbin | right; left; reflexivity]. }
assert (M16 : forall fr, In (Some fr) (cg_frames s) -> fr_ptr fr mod 8 = 0).
{ intros fr Hfr.
pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fr) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N fr); [exact Hfr | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
pose proof (M16 f Hfin) as Hp8. pose proof (M16 b Hbin) as Hq8.
pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfa.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfa.
pose proof (Z_land_upper (fr_attr f) 1 ltac:(lia)) as Ru1.
destruct (fl_stk_word memc (sp0 - 272 + 32) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d32 & Rd32 & Wd32).
destruct (fl_stk_word memc (sp0 - 272 + 24) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d24 & Rd24 & Wd24).
destruct (fl_stk_word memc (sp0 - 272 + 16) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d16 & Rd16 & Wd16).
set (MO := [g; fr_ptr f; top; d32; d24; d16; Z.land (fr_attr f) 1; h; cg_W s]).
set (E := fl_E regs1 regs0 s f1 (Some b) MO).
pose proof (fl_HE regs1 regs0 s f1 (Some b) MO : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 (Some b) MO : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HX regs1 regs0 s f1 (Some b) MO : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HB regs1 regs0 s f1 (Some b) MO : forall n j v, _ -> _ -> ew E n = _) as HBv.
pose proof (fl_HM regs1 regs0 s f1 (Some b) MO : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hq0 Hq1 Hac HFRv; lia).
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (HM 80%nat 0%nat _ eq_refl eq_refl)).
assert (HE81 : ew E 81 = Z_to_bv 64 (fr_ptr f)) by (apply (HM 81%nat 1%nat _ eq_refl eq_refl)).
assert (HE82 : ew E 82 = Z_to_bv 64 top) by (apply (HM 82%nat 2%nat _ eq_refl eq_refl)).
assert (HE83 : ew E 83 = Z_to_bv 64 d32) by (apply (HM 83%nat 3%nat _ eq_refl eq_refl)).
assert (HE84 : ew E 84 = Z_to_bv 64 d24) by (apply (HM 84%nat 4%nat _ eq_refl eq_refl)).
assert (HE85 : ew E 85 = Z_to_bv 64 d16) by (apply (HM 85%nat 5%nat _ eq_refl eq_refl)).
assert (HE86 : ew E 86 = Z_to_bv 64 (Z.land (fr_attr f) 1)) by (apply (HM 86%nat 6%nat _ eq_refl eq_refl)).
assert (HE87 : ew E 87 = Z_to_bv 64 h) by (apply (HM 87%nat 7%nat _ eq_refl eq_refl)).
assert (HE88 : ew E 88 = Z_to_bv 64 (cg_W s)) by (apply (HM 88%nat 8%nat _ eq_refl eq_refl)).
assert (HE72 : ew E 72 = Z_to_bv 64 (fr_img b)) by (apply (HBv 72%nat 1%nat _ eq_refl eq_refl)).
assert (HE23 : ew E 23 = Z_to_bv 64 w) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE22 : ew E 22 = Z_to_bv 64 left) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE8 : ew E 8 = Z_to_bv 64 pTmp) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 tv) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 168
(fl_stk_saved 32 ++ t_more_chunks ++ [mkChunk 64 (CVal 8 (SOff 87 0))]))).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
unfold t_more_chunks. cbn [app]. repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r; erewrite HM by reflexivity; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; eassumption]).
all: clear - Hg0 Hg1 Hp0 Hp1 Ht0 Hth Hh RH RW Rd32 Rd24 Rd16 Ru1 Hac HGSv HFRv; lia. }
pose proof (fl_Rfb_ok regs1 regs0 s f1 (Some b) MO memc 18 (fr_ptr b) b HU18 eq_refl eq_refl ltac:(lia) ltac:(lia) Hbobj) as HR1.
assert (HPD : pairwise_disjoint E (ss_mem ss_t3)).
{ cbn [ss_mem ss_t3]. unfold fl_Rfb. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU18. clear - Hq1 Hceil HFSv HFRv Hac. repeat split; lia. }
assert (HFA : atoms_ok E ([(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (18%nat, mkAF 4096 (CEIL_MAX - 40) 3);
(87%nat, mkAF 1 65535 0); (23%nat, mkAF 1 65535 0); (82%nat, mkAF 0 65535 0); (22%nat, mkAF 0 65535 0); (88%nat, mkAF 1 65535 0);
(8%nat, mkAF 4096 CEIL_MAX 0)] ++ fl_bfacts)).
{ apply atoms_ok_app; [| exact (fl_bfacts_ok regs1 regs0 s f1 (Some b) MO memc (fr_ptr b) b eq_refl Hbobj Hbi0 ltac:(clear - Hbi1 HN HW1 HH1; nia))].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU18, HE87, HE23, HE82, HE22, HE88, HE8.
assert (HNt1 : 1 <= Nt) by (clear - Hw Hh Hwh; nia).
rewrite !unsigned_lit_small by (clear - Hw Hl0 Hlw Hh Ht0 Hth RW RH T0 T1 HNt1 Hac; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hceil Hsp063 Hal16 Hq0 Hq1 Hq8 Hw Hl0 Hlw Hh Ht0 Hth RW RH T0 T1 HNt1 HFSv HFRv Hac. repeat split; try lia;
try (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16). }
assert (HS : st_ok ubs2segs E ss_t3 (mkst regs1 (Z_to_bv 64 FL_T3) memc (seg_rom ubs2segs))).
{ unfold ss_t3. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor. }
clear HR0 HR1 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_T3) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_TOUT.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHm.
assert (SEP : forall y, In y (cgif_blocks g s N ++ rest) -> pTmp + Nt <= fst y \/ fst y + snd y <= pTmp)
by (intros y Hy; exact (heap_sep_perm _ _ LAWS Lc Ac memc mdc (pTmp, Nt) _ y HH0 HB Hy)).
assert (SEPc : forall bb nn, In (bb, nn) (cgif_blocks g s N) -> pTmp + Nt <= bb \/ bb + nn <= pTmp)
by (intros bb nn Hy; exact (SEP (bb, nn) ltac:(apply in_app_iff; left; exact Hy))).
pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp. pose proof (Rg 3%nat (cg_pal s) eq_refl) as Rgpal. cbn [nth snd LAY_CGIF Z.of_N] in Rngp, Rgpal.
pose proof (Rf 5%nat (fr_nlp f) eq_refl) as Rfnlp. pose proof (Rf 0%nat (fr_lpal f) eq_refl) as Rflpal. pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr.
pose proof (Rb 5%nat (fr_nlp b) eq_refl) as Rbnlp. pose proof (Rb 0%nat (fr_lpal b) eq_refl) as Rblpal. pose proof (Rb 2%nat (fr_attr b) eq_refl) as Rbattr.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfnlp, Rflpal, Rfattr, Rbnlp, Rblpal, Rbattr.
assert (CTB : forall fr, In (Some fr) (cg_frames s) -> 0 <= fr_nlp fr ->
In (ct_sel (fr_attr fr) (fr_lpal fr) (cg_pal s), 3 * ct_sel (fr_attr fr) (fr_nlp fr) (cg_ngp s)) (cgif_blocks g s N) /\
0 <= 3 * ct_sel (fr_attr fr) (fr_nlp fr) (cg_ngp s)).
{ intros fr Hfr Hnl. unfold ct_sel. destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0) as [Hz|Hz].
- split; [| clear - Rngp; lia]. unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks.
rewrite (proj1 (Hfwf fr Hfr) Hz). cbn. left. reflexivity.
- split; [| clear - Hnl; lia]. apply (frame_blocks_in_cgif g s N fr _ _ Hfr). unfold frame_blocks. right. right.
destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0); [lia|]. left. reflexivity. }
destruct (CTB f Hfin ltac:(clear - Rfnlp; lia)) as [CTf Sf0]. destruct (CTB b Hbin ltac:(clear - Rbnlp; lia)) as [CTb Sb0]. clear CTB.
assert (CTf' : In (ct_sel (fr_attr f) (fr_lpal f) (cg_pal s), 3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s)) (blocks Lc Ac))
by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact CTf).
assert (CTb' : In (ct_sel (fr_attr b) (fr_lpal b) (cg_pal s), 3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s)) (blocks Lc Ac))
by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact CTb).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTf') as [Sc0 Sc1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTb') as [Sd0 Sd1].
destruct (rdn_of_present ubs2_msyms (ms_mem ms) (Z.to_nat (3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s))) (ct_sel (fr_attr f) (fr_lpal f) (cg_pal s))
ltac:(intros k Hk; apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc _ _ k HHm CTf' ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
destruct (rdn_of_present ubs2_msyms (ms_mem ms) (Z.to_nat (3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s))) (ct_sel (fr_attr b) (fr_lpal b) (cg_pal s))
ltac:(intros k Hk; apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc _ _ k HHm CTb' ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (KB1 : forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs (ms_mem ms) (bb + k) = mbyte ubs2segs memc (bb + k)).
{ intros bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K1; clear - R0 R1 Hk Hceil HFSv Hac; lia. }
assert (Og1 : obj_at ubs2segs (ms_mem ms) g LAY_CGIF (cgif_vals s)).
{ eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB1 g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]]. }
assert (Oc1 : obj_at ubs2segs (ms_mem ms) (fr_ptr f) LAY_FrameConfig (firstn 7 (frame_vals f1))).
{ rewrite LAY_Frame_split in Hfobj.
apply (proj1 (obj_at_app ubs2segs _ (fr_ptr f) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals f1)) (skipn 7 (frame_vals f1)) eq_refl)).
eapply obj_at_transport_range; [exact Hfobj | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB1 (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity. }
assert (Ob1 : obj_at ubs2segs (ms_mem ms) (fr_ptr b) LAY_FrameConfig (firstn 7 (frame_vals b))).
{ pose proof Hbobj as Hbobj'. rewrite LAY_Frame_split in Hbobj'.
apply (proj1 (obj_at_app ubs2segs _ (fr_ptr b) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals b)) (skipn 7 (frame_vals b)) eq_refl)).
eapply obj_at_transport_range; [exact Hbobj' | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB1 (fr_ptr b) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N b _ _ Hbin). left. reflexivity. }
lazymatch type of HS with st_ok _ _ ?ssx _ =>
pose proof (st_region_chunks ubs2segs E ssx ms 0 _ 2%nat (sp0 - 272) HS eq_refl eq_refl HU2) as Hcs end.
cbn [r_chunks] in Hcs.
assert (HNt1 : 1 <= Nt) by (clear - Hw Hh Hwh; nia).
assert (Wg1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 112) g) by (cw Hcs 112 (SOff 80 0) HE80; clear - Hg0 Hg1 HGSv Hac; lia).
assert (Wc1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 120) (fr_ptr f)) by (cw Hcs 120 (SOff 81 0) HE81; clear - Hp0 Hp1 HFRv Hac; lia).
assert (Wsh1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 72) (w * 2 ^ 48)).
{ apply (chunk_word E _ _ 72 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 72 (CVal 8 (SAlu ALU_SLL (SOff 23 0) (SLit 48)))) ltac:(cbn [In]; repeat (first [left; reflexivity | right])))); [| clear - Hw Hlw Hl0 RW; nia].
apply denot_of_U'. rewrite U_sll_lit by lia.
rewrite (U_atom _ 23 w HE23) by (clear - Hw Hlw Hl0 RW; lia). apply Z.mod_small. clear - Hw Hlw Hl0 RW; nia. }
assert (Whh1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 80) h) by (cw Hcs 80 (SOff 87 0) HE87; clear - Hh Hth Ht0 RH; lia).
assert (Ww1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 88) w).
{ apply (chunk_word E _ _ 88 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 88 (CVal 8 (SAlu ALU_AND (SOff 23 0) (SLit 65535)))) ltac:(cbn [In]; repeat (first [left; reflexivity | right])))); [| clear - Hw Hlw Hl0 RW; lia].
apply denot_of_U'. rewrite U_and_lit by lia.
rewrite (U_atom _ 23 w HE23) by (clear - Hw Hlw Hl0 RW; lia). apply land_ffff. clear - Hw Hlw Hl0 RW; lia. }
assert (WW1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 104) (cg_W s)) by (cw Hcs 104 (SOff 88 0) HE88; clear - RW; lia).
assert (Wtop1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 96) top) by (cw Hcs 96 (SOff 82 0) HE82; clear - Ht0 Hth Hh RH; lia).
assert (Wdisp1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 32) d32) by (cw Hcs 32 (SOff 83 0) HE83; clear - Rd32; lia).
assert (Wha1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 24) d24) by (cw Hcs 24 (SOff 84 0) HE84; clear - Rd24; lia).
assert (WhST1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 16) d16) by (cw Hcs 16 (SOff 85 0) HE85; clear - Rd16; lia).
assert (WuL1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 56) (Z.land (fr_attr f) 1)) by (cw Hcs 56 (SOff 86 0) HE86; clear - Ru1; lia).
assert (Whgt1 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 64) h) by (cw Hcs 64 (SOff 87 0) HE87; clear - Hh Hth Ht0 RH; lia).
assert (Ww40 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 40) w) by (cw Hcs 40 (SOff 23 0) HE23; clear - Hw Hlw Hl0 RW; lia).
assert (Wl48 : word_mem ubs2segs (ms_mem ms) (sp0 - 272 + 48) left) by (cw Hcs 48 (SOff 22 0) HE22; clear - Hl0 Hlw Hw RW; lia).
jreg HS (2%bv:reg) as Q2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Q2.
jreg HS (8%bv:reg) as Q8. rewrite HE8 in Q8.
jreg HS (9%bv:reg) as Q9. rewrite HE9 in Q9.
jreg HS (18%bv:reg) as Q18. rewrite (HE 18%nat 18%bv eq_refl), G18 in Q18.
jreg HS (22%bv:reg) as Q22.
jreg HS (21%bv:reg) as Q21.
jreg HS (24%bv:reg) as Q24. rewrite HE72 in Q24.
jreg HS (26%bv:reg) as Q26.
jreg HS (3%bv:reg) as Q3. rewrite (HE 3%nat 3%bv eq_refl) in Q3. jreg HS (4%bv:reg) as Q4. rewrite (HE 4%nat 4%bv eq_refl) in Q4.
assert (Q21' : getr (ms_regs ms) 21 = Z_to_bv 64 (0 * w)) by (rewrite Q21; f_equal; lia).
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
assert (Q27 : getr (ms_regs msx) 27 = Z_to_bv 64 ((top + 0) * cg_W s + left));
[ rewrite (st_ok_reg ubs2segs E ssx msx 27%bv HS); eval_sr_get; apply denot_of_U';
rewrite (U_add_small E _ _ (top * cg_W s) left); [clear; lia | | rewrite U_and_lit by lia; rewrite (U_atom _ 22 left HE22) by (clear - Hl0 Hlw Hw RW; lia); apply land_ffff; clear - Hl0 Hlw Hw RW; lia
| clear - Ht0 RW; nia | exact Hl0 | clear - Ht0 Hth Hh Hl0 Hlw Hw RW RH HN HNle; nia];
apply (U_mul_small' E _ _ top (cg_W s)); [rewrite U_and_lit by lia; rewrite (U_atom _ 82 top HE82) by (clear - Ht0 Hth Hh RH; lia); apply land_ffff; clear - Ht0 Hth Hh RH; lia
| apply (U_atom _ 88 (cg_W s) HE88); clear - RW; lia | exact Ht0 | clear - RW; lia | clear - Ht0 Hth Hh RW RH HN HNle; nia]
| ] end.
assert (Hh31 : h < 2 ^ 31) by (clear - Hh Hth Ht0 RH; lia).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_tout API IMG (ms_mem ms) g (fr_ptr f) (fr_ptr b) (fr_img b) N pTmp Nt (sp0 - 272) tv (cgif_vals s) (firstn 7 (frame_vals f1)) (firstn 7 (frame_vals b))
(fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_lpal f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (fr_lpal b) (cg_ngp s) (cg_pal s) ctcur ctbef
Og1 eq_refl eq_refl Oc1 eq_refl eq_refl eq_refl eq_refl Ob1 eq_refl eq_refl eq_refl eq_refl
Hg0 Hg1 Hg16) with (n := Z.to_nat h) (i := 0) (w := w) (h := h) (top := top) (left := left) (Wd := cg_W s) (Hd := cg_H s) (wsh := w * 2 ^ 48);
[ exact Hp0 | clear - Hp1 HFRv Hac; lia | exact Hp8 | exact Hq0 | clear - Hq1 HFRv Hac; lia | exact Hq8
| clear - Hpg HGSv HFRv; lia | clear - Hqg HGSv HFRv; lia | clear - Hfb HFRv; lia
| exact Rct | exact Rbt | exact Sc0 | exact Sc1 | exact Sd0 | exact Sd1 | exact Sf0 | exact Sb0
| exact Hbi0 | exact Hbi1 | clear - HNle; lia | exact T0 | exact T1
| pose proof (SEPc _ _ ltac:(left; reflexivity)) as X; cbn [fst snd] in X; clear - X; lia
| pose proof (SEPc _ _ (frame_blocks_in_cgif g s N f _ _ Hfin ltac:(left; reflexivity))) as X; clear - X HFRv; lia
| pose proof (SEPc _ _ (frame_blocks_in_cgif g s N b _ _ Hbin ltac:(left; reflexivity))) as X; clear - X HFRv; lia
| pose proof (SEPc _ _ CTf) as X; clear - X; lia
| pose proof (SEPc _ _ CTb) as X; clear - X; lia
| pose proof (SEPc _ _ (frame_blocks_in_cgif g s N b _ _ Hbin ltac:(right; left; reflexivity))) as X; clear - X; lia
| clear - Hceil HFSv; lia | clear - Hsp063; lia | replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| exact Wg1 | exact Wc1 | exact Htv
| exact Hw | exact Hlw | exact Hl0 | exact Hh | exact Hth | exact Ht0 | exact HN | exact Hwh
| exact Wsh1 | clear - Hw Hlw Hl0 RW; nia | exact Whh1 | exact Ww1 | exact WW1 | exact Hh31
| exact HJ | intros a _ _; reflexivity | exact Htin | exact Htmp_fp | exact Hbimgin | clear; lia | clear - Hh; lia | clear - Hh; lia | clear - HFSv; lia | reflexivity
| exact Q2 | exact Q8 | exact Q9 | exact Q18 | exact Q22 | exact Q21' | exact Q27 | exact Q24 | exact Q26 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & K4 & HK4).
assert (KS : forall a v, word_mem ubs2segs (ms_mem ms) (sp0 - 272 + a) v -> 0 <= a -> a + 8 <= 272 -> word_mem ubs2segs mem4 (sp0 - 272 + a) v).
{ intros a v Hv Ha0 Ha1 k Hk. rewrite <- (Hv k Hk). apply K4; clear - Ha0 Ha1 Hk Hceil Hsp063 HFSv T0 T1 Hac; lia. }
pose proof (KS 112 g Wg1 ltac:(clear; lia) ltac:(clear; lia)) as W112.
pose proof (KS 120 (fr_ptr f) Wc1 ltac:(clear; lia) ltac:(clear; lia)) as W120.
pose proof (KS 96 top Wtop1 ltac:(clear; lia) ltac:(clear; lia)) as W96.
pose proof (KS 32 d32 Wdisp1 ltac:(clear; lia) ltac:(clear; lia)) as W32.
pose proof (KS 24 d24 Wha1 ltac:(clear; lia) ltac:(clear; lia)) as W24.
pose proof (KS 16 d16 WhST1 ltac:(clear; lia) ltac:(clear; lia)) as W16.
pose proof (KS 56 (Z.land (fr_attr f) 1) WuL1 ltac:(clear; lia) ltac:(clear; lia)) as W56.
pose proof (KS 64 h Whgt1 ltac:(clear; lia) ltac:(clear; lia)) as W64.
pose proof (KS 40 w Ww40 ltac:(clear; lia) ltac:(clear; lia)) as W40.
pose proof (KS 48 left Wl48 ltac:(clear; lia) ltac:(clear; lia)) as W48.
assert (HSV4 : fl_saved_ok mem4 sp0 regs0).
{ apply (fl_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite K4; [apply K1|..]; clear - Ha Hceil Hsp063 HFSv T0 T1 Hac; lia. }
set (vals4 := fl_saved_vals regs0 ++ [g; fr_ptr f; top; d32; d24; d16; Z.land (fr_attr f) 1; h; w; left]).
set (E4 := Ereg regs4 (map (Z_to_bv 64) vals4 ++ [])).
assert (HE4 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E4 n = getr regs4 rr) by (intros; subst E4; apply ew_Ereg_nat; assumption).
assert (HA4 : forall j v, nth_error vals4 j = Some v -> ew E4 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E4; apply Ereg_vals; exact Hj).
assert (HK4s : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E4 (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA4. subst vals4. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HV4 : forall n j v, n = (45 + j)%nat -> nth_error [g; fr_ptr f; top; d32; d24; d16; Z.land (fr_attr f) 1; h; w; left] j = Some v -> ew E4 n = Z_to_bv 64 v).
{ intros n j v -> Hj. replace (45 + j)%nat with (32 + (13 + j))%nat by lia. apply HA4. subst vals4. rewrite nth_error_app2 by (cbn; lia). replace (13 + j - length (fl_saved_vals regs0))%nat with j by (cbn; lia). exact Hj. }
assert (G4_2 : getr regs4 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HK4 2%bv ltac:(cbv; auto 20)); exact Q2).
assert (HU4_2 : bv_unsigned (ew E4 2) = sp0 - 272) by (rewrite (HE4 2%nat 2%bv eq_refl), G4_2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR4 : region_ok ubs2segs E4 mem4 (YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t4_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU4_2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold t4_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E4 mem4 sp0 regs0 32 HSV4); intros j v Hj; exact (HK4s j v Hj)|].
repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r; erewrite HV4 by reflexivity; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; assumption]).
all: clear - Hg0 Hg1 Hp0 Hp1 Ht0 Hth Hh RH Rd32 Rd24 Rd16 Ru1 Hw Hlw Hl0 RW Hac HGSv HFRv; lia. }
assert (HFA4 : atoms_ok E4 [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU4_2. change (2 ^ 4) with 16.
try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 HFSv. repeat split; try lia. replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS4 : st_ok ubs2segs E4 ss_t4 (mkst regs4 (Z_to_bv 64 FL_TOUTX) mem4 (seg_rom ubs2segs))).
{ unfold ss_t4. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR4 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA4 | split; exact I]]. }
clear HR4 HFA4.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 FL_TOUTX) mem4 (seg_rom ubs2segs))) in HJ4.
jrun_to LAWS ubs2tbl_ok HS4 HJ4 FL_RAW. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K5 : forall x, ms_mem ms0 x = mem4 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (RG : forall (r : reg) n wv, sr_get (ss_regs ltac:(lazymatch type of HS4 with st_ok _ _ ?ssx _ => exact ssx end)) r = SOff n 0 -> ew E4 n = wv -> getr (ms_regs ms0) r = wv).
{ intros r n wv Hr Hv. lazymatch type of HS4 with st_ok _ _ ?ssx ?msx => rewrite (st_ok_reg ubs2segs E4 ssx msx r HS4), Hr end. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hv. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS4 eq_refl). cbn [ss_pc].
eapply (fl_tail API IMG RAWADD L A mem md regs0 (ms_regs ms0) Lc Ac (ms_mem ms0) mdc g N s i f gen1 rest FP [(pTmp, Nt)] pTmp Nt tv w h FL_RAW);
[ exact HJ4 | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact HFP | exact HB
| right; split; [reflexivity | split; [clear - T0; lia | exact Hwh]] | exact Htmp_fp | left; reflexivity
| clear - Hw Hlw Hl0; lia | clear - Hh Hth Ht0; lia | exact Htv
| apply (fl_saved_ok_kept mem4); [exact HSV4 | intros a Ha; apply mbyte_of_eq; exact K5]
| apply (RG 2%bv 2%nat); [reflexivity | rewrite (HE4 2%nat 2%bv eq_refl); exact G4_2]
| apply (RG 8%bv 8%nat); [reflexivity | rewrite (HE4 8%nat 8%bv eq_refl), (HK4 8%bv ltac:(cbv; auto 20)); exact Q8]
| apply (RG 9%bv 9%nat); [reflexivity | rewrite (HE4 9%nat 9%bv eq_refl), (HK4 9%bv ltac:(cbv; auto 20)); exact Q9]
| apply (RG 16%bv 52%nat); [reflexivity | exact (HV4 52%nat 7%nat _ eq_refl eq_refl)]
| intros k Hk; unfold mbyte; rewrite K5; apply (W112 k Hk)
| intros k Hk; unfold mbyte; rewrite K5; apply (W120 k Hk)
| intros k Hk; unfold mbyte; rewrite K5; apply (W56 k Hk)
| intros k Hk; unfold mbyte; rewrite K5; apply (W96 k Hk)
| intros Hc; exfalso; clear - Hc; unfold FL_RAW, FL_RAW2 in Hc; lia
| intros _; split; [apply (RG 22%bv 54%nat); [reflexivity | exact (HV4 54%nat 9%nat _ eq_refl eq_refl)] | apply (RG 23%bv 53%nat); [reflexivity | exact (HV4 53%nat 8%nat _ eq_refl eq_refl)]]
| split; [ apply (RG 3%bv 3%nat); [reflexivity | rewrite (HE4 3%nat 3%bv eq_refl), (HK4 3%bv ltac:(cbv; auto 20)), Q3; exact G3]
| apply (RG 4%bv 4%nat); [reflexivity | rewrite (HE4 4%nat 4%bv eq_refl), (HK4 4%bv ltac:(cbv; auto 20)), Q4; exact G4] ] ].
assert (KB4 : forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs (ms_mem ms0) (bb + k) = mbyte ubs2segs memc (bb + k)).
{ intros bb nn k Hbn Hk. rewrite (mbyte_of_eq _ _ _ _ K5). pose proof (SEPc bb nn Hbn) as X.
assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1].
rewrite K4; [apply (KB1 bb nn k Hbn Hk) | clear - R0 R1 Hk Hac; lia | clear - X Hk; lia]. }
split; [| split].
- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB4 g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB4 (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB4 (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB4 (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N x _ _ Hin). left. reflexivity.
Qed.
Lemma fl_t2b :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
nth_error (cg_frames s) (i - 1) = Some (Some b) ->
(forall b' n a, In (b', n) (cgif_blocks g s N) -> b' <= a < b' + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest) ->
((tmp = [] /\ pTmp = 0) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ w * h <= Nt)) ->
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
1 <= w -> 0 <= left -> left + w <= cg_W s -> 1 <= h -> 0 <= top -> top + h <= cg_H s -> 0 <= tv < 2 ^ 64 ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 9 = Z_to_bv 64 tv ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> word_mem ubs2segs memc (sp0 - 272 + 112) g -> word_mem ubs2segs memc (sp0 - 272 + 120) (fr_ptr f) ->
getr regs1 18 = Z_to_bv 64 (fr_ptr b) -> getr regs1 8 = Z_to_bv 64 pTmp ->
word_mem ubs2segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) -> getr regs1 27 = Z_to_bv 64 (cg_W s) -> word_mem ubs2segs memc (sp0 - 272 + 104) (cg_W s) ->
getr regs1 19 = Z_to_bv 64 (cg_H s) ->
getr regs1 16 = Z_to_bv 64 h -> getr regs1 23 = Z_to_bv 64 w -> word_mem ubs2segs memc (sp0 - 272 + 96) top -> getr regs1 22 = Z_to_bv 64 left ->
fl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_T2B) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tmp pTmp Nt tv w h top left sp0
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf Hb HFP HB Htmp Htmp_fp Hw Hl0 Hlw Hh Ht0 Hth Htv HSV
G9 G2 Wg Wf G18 G8 WuL G27 WW G19 G16 G23 Wtop G22 [G3 G4].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity. assert (ASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & Hgone & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (tmp ++ rest))) by (eapply Permutation_trans; [exact HB|]; apply Permutation_app_swap_app).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HBc) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom API Lc Ac memc mdc g s N _ f HH0 HBc Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
assert (Himgfin : In (fr_img f, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif g s N f); [exact Hfin | right; left; reflexivity]. }
pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr.
pose proof (Z_land_upper (fr_attr f) 1 ltac:(lia)) as Ru1.
destruct (fl_stk_word memc (sp0 - 272 + 32) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d32 & Rd32 & Wd32).
destruct (fl_stk_word memc (sp0 - 272 + 24) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d24 & Rd24 & Wd24).
destruct (fl_stk_word memc (sp0 - 272 + 16) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d16 & Rd16 & Wd16).
set (MO := [g; fr_ptr f; top; d32; d24; d16; Z.land (fr_attr f) 1; h; cg_W s]).
set (E := fl_E regs1 regs0 s f1 None MO).
pose proof (fl_HE regs1 regs0 s f1 None MO : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 None MO : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HF regs1 regs0 s f1 None MO : forall n j v, _ -> _ -> ew E n = _) as HFf.
pose proof (fl_HM regs1 regs0 s f1 None MO : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (HM 80%nat 0%nat _ eq_refl eq_refl)).
assert (HE81 : ew E 81 = Z_to_bv 64 (fr_ptr f)) by (apply (HM 81%nat 1%nat _ eq_refl eq_refl)).
assert (HE82 : ew E 82 = Z_to_bv 64 top) by (apply (HM 82%nat 2%nat _ eq_refl eq_refl)).
assert (HE83 : ew E 83 = Z_to_bv 64 d32) by (apply (HM 83%nat 3%nat _ eq_refl eq_refl)).
assert (HE84 : ew E 84 = Z_to_bv 64 d24) by (apply (HM 84%nat 4%nat _ eq_refl eq_refl)).
assert (HE85 : ew E 85 = Z_to_bv 64 d16) by (apply (HM 85%nat 5%nat _ eq_refl eq_refl)).
assert (HE86 : ew E 86 = Z_to_bv 64 (Z.land (fr_attr f) 1)) by (apply (HM 86%nat 6%nat _ eq_refl eq_refl)).
assert (HE88 : ew E 88 = Z_to_bv 64 (cg_W s)) by (apply (HM 88%nat 8%nat _ eq_refl eq_refl)).
assert (HU81 : bv_unsigned (ew E 81) = fr_ptr f) by (rewrite HE81; apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HE63 : ew E 63 = Z_to_bv 64 (fr_img f)) by (apply (HFf 63%nat 1%nat _ eq_refl eq_refl)).
assert (HE16h : ew E 16 = Z_to_bv 64 h) by (rewrite (HE 16%nat 16%bv eq_refl); exact G16).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_stk_saved 32 ++ t_more_chunks))).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
unfold t_more_chunks. repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r; erewrite HM by reflexivity; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; eassumption]).
all: clear - Hg0 Hg1 Hp0 Hp1 Ht0 Hth Hh RH RW Rd32 Rd24 Rd16 Ru1 Hac HGSv HFRv; lia. }
assert (HR1 : region_ok ubs2segs E memc (fl_Rfn 81)).
{ unfold fl_Rfn, A_F. eapply (region_ok_obj_gen ubs2segs E memc 81 (fr_ptr f) 40 0 0 LAY_Frame (frame_vals f1) 62 []);
[exact HU81 | lia | clear - Hp1 Hac HFRv; lia | exact Hfobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros i0 Hi0; lia].
intros j v Hj. apply (HFf (62 + j)%nat j v eq_refl Hj). }
assert (HPD : forall pz, pairwise_disjoint E (ss_mem (ss_t2b pz))).
{ intros pz. cbn [ss_mem ss_t2b]. unfold fl_Rfn. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU81. clear - Hp1 Hceil HFSv HFRv Hac. repeat split; lia. }
assert (Hp8 : fr_ptr f mod 8 = 0).
{ pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
assert (HFAa : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (81%nat, mkAF 4096 (CEIL_MAX - 40) 3);
(19%nat, mkAF 1 65535 0); (27%nat, mkAF 1 65535 0); (16%nat, mkAF 1 65535 0); (23%nat, mkAF 1 65535 0); (82%nat, mkAF 0 65535 0); (22%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU81, (HE 19%nat 19%bv eq_refl), (HE 27%nat 27%bv eq_refl), (HE 16%nat 16%bv eq_refl), (HE 23%nat 23%bv eq_refl), HE82, (HE 22%nat 22%bv eq_refl),
G19, G27, G16, G23, G22.
rewrite !unsigned_lit_small by (clear - Hw Hl0 Hlw Hh Ht0 Hth RW RH; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hceil Hsp063 Hal16 Hp0 Hp1 Hp8 Hw Hl0 Hlw Hh Ht0 Hth RW RH HFSv HFRv Hac. repeat split; try lia;
try (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16). }
pose proof (fl_ffacts_ok regs1 regs0 s f1 None MO memc (fr_ptr f) Hfobj Him0 ltac:(change (fr_img f1) with (fr_img f); clear - Him1 HN HW1 HH1; nia)) as HFAc.
assert (HFAd : pTmp <> 0 -> atoms_ok E [(8%nat, mkAF 1 (2^64 - 1) 0)]).
{ intros Hpz. destruct Htmp as [[_ Hz] | (Htm & _ & Hle)]; [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1].
assert (T2 : pTmp < alloc_ceiling) by (clear - T1 Hle Hw Hh; nia).
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 8%nat 8%bv eq_refl), G8, unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - T0 T2 Hac. repeat split; lia. }
assert (MK : forall (pz : bool), (if pz then pTmp = 0 else pTmp <> 0) ->
st_ok ubs2segs E (ss_t2b pz) (mkst regs1 (Z_to_bv 64 FL_T2B) memc (seg_rom ubs2segs))).
{ intros pz Hpz. unfold ss_t2b. apply entry_st_ok_full; [| vm_compute; destruct pz; reflexivity | | exact (HPD pz) |].
- destruct pz; [| apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G8, Hpz. reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor.
- split; [| split; exact I]. apply atoms_ok_app; [exact HFAa|]. apply atoms_ok_app; [| exact HFAc]. destruct pz; [exact I | exact (HFAd Hpz)]. }
clear HR0 HR1 HPD HFAa HFAc HFAd.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_T2B) memc (seg_rom ubs2segs))) in HJ.
assert (WR : forall E0 cs rs blc, bv_unsigned (ew E0 2) = sp0 - 272 -> Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E0 (YQ0b.mkRegion (Some 2%nat) 0 272 0 168 cs :: rs) FLUSH_STK sp0 FP (blocks L A) blc).
{ intros E0 cs rs blc H2 Hrs. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
induction Hrs as [|r rs' Hr Hrs' IHrs]; [apply wr_ok_nil | apply wr_ok_cons_ro; [exact Hr | exact IHrs]]. }
assert (GO3 : forall (regs3 : bvmap 5 word) (mem3 : word -> option byte) Lc3 Ac3 mdc3 pT Ntt,
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc3 Ac3 mem3 mdc3 -> st_init_done Ac3 = true ->
Permutation (blocks Lc3 Ac3) ((pT, Ntt) :: cgif_blocks g s N ++ rest) ->
(In (pT, Ntt) (blocks L A) -> forall k, 0 <= k < Ntt -> inFP FP (pT + k)) -> w * h <= Ntt ->
(forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs mem3 (bb + k) = mbyte ubs2segs memc (bb + k)) ->
(forall a, sp0 - 272 + 168 <= a < sp0 -> mbyte ubs2segs mem3 a = mbyte ubs2segs memc a) ->
getr regs3 9 = Z_to_bv 64 tv ->
getr regs3 23 = Z_to_bv 64 w -> word_mem ubs2segs mem3 (sp0 - 272 + 96) top -> getr regs3 22 = Z_to_bv 64 left ->
getr regs3 2 = Z_to_bv 64 (sp0 - 272) -> word_mem ubs2segs mem3 (sp0 - 272 + 112) g -> word_mem ubs2segs mem3 (sp0 - 272 + 120) (fr_ptr f) ->
getr regs3 18 = Z_to_bv 64 (fr_ptr b) -> getr regs3 8 = Z_to_bv 64 pT ->
word_mem ubs2segs mem3 (sp0 - 272 + 56) (Z.land (fr_attr f) 1) -> word_mem ubs2segs mem3 (sp0 - 272 + 104) (cg_W s) ->
word_mem ubs2segs mem3 (sp0 - 272 + 64) h ->
getr regs3 3 = getr regs0 3 -> getr regs3 4 = getr regs0 4 ->
SR ubs2segs (mkCfg (mkst regs3 (Z_to_bv 64 FL_T3) mem3 (seg_rom ubs2segs)) mdc3) (fl_post API regs0 g s N i rest FP L A mem md)).
{ intros regs3 mem3 Lc3 Ac3 mdc3 pT Ntt HJ3 Hid3 HB3 Hfp3 Hwh KB Khi R9 R23 W96 R22 R2 W112 W120 R18 R8 W56 W104 W64 R3 R4.
eapply (fl_t3 L A mem md regs0 regs3 Lc3 Ac3 mem3 mdc3 g N s i f b gen1 rest FP pT Ntt tv w h top left);
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact Hb | exact HFP | exact HB3 | exact Hfp3
| exact Hw | exact Hl0 | exact Hlw | exact Hh | exact Ht0 | exact Hth | exact Hwh | exact Htv
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply Khi; clear - Ha; lia]
| exact R9 | exact R23 | exact W96 | exact R22 | exact R2 | exact W112 | exact W120 | exact R18 | exact R8 | exact W56 | exact W104 | exact W64
| split; [exact R3 | exact R4] ].
split; [| split].
- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N x _ _ Hin). left. reflexivity. }
assert (KBof : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs m a = mbyte ubs2segs memc a) ->
forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs m (bb + k) = mbyte ubs2segs memc (bb + k)).
{ intros m K bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hceil HFSv Hac; lia. }
destruct (Z.eq_dec pTmp 0) as [Hpz | Hpz].
-
pose proof (MK true Hpz) as HS. clear MK.
destruct Htmp as [[Htm _] | (_ & Hz & _)]; [| exfalso; exact (Hz Hpz)]. subst tmp. cbn [app] in HB.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { apply WR; [exact HU2 | repeat constructor; cbn; lia]. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs2segs Ec ssc msc 10%bv HS) as Hm10; eval_sr_get_in Hm10; rewrite ?denot_add0 in Hm10;
first [ rewrite (denot_mul_atoms _ 19 27 (cg_H s) (cg_W s)) in Hm10 by first [clear - RW RH HN HNle; nia | rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 27%nat 27%bv eq_refl); exact G27]
| rewrite (denot_mul_atoms _ 27 19 (cg_W s) (cg_H s)) in Hm10 by first [clear - RW RH HN HNle; nia | rewrite (HE 27%nat 27%bv eq_refl); exact G27 | rewrite (HE 19%nat 19%bv eq_refl); exact G19] ] end.
replace (cg_H s * cg_W s) with N in Hm10 by (clear - HN; lia). replace (cg_W s * cg_H s) with N in Hm10 by (clear - HN; lia).
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hmra.
assert (Hspm : (sp0 - 272) mod 16 = 0) by (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := N) (spc := sp0 - 272);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hm10 | clear - HN HNle HW1 HH1; nia
| exact Hm2 | clear - Hceil Hsp063 HFSv Hac; lia | exact Hspm | clear - HFSv ASv; lia | clear; lia | exact Hm4 | exact Hmra | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & pNew & -> & HJ3 & Hid3 & HP3 & Hi10 & Hres & Hkeep3 & Hhi3). clear HJ.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
jafter_call_keep HS 89%nat regs3 mem3 HP3 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | clear - HFSv ASv; lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 81 _ _ _ _ _ (fr_ptr f) FRAME_SIZE); [ew_havocA; exact HU81 | | exact Hkeep3 | cbn; lia | cbn; clear - HFRv; lia | cbn; lia].
apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq93. cbn [ms_regs mkst] in Hq93. rewrite Hi10 in Hq93. symmetry in Hq93.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ((exists bb m, In (bb, m) (blocks Lc Ac) /\ bb <= a < bb + m) \/ sp0 - 272 <= a) -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) ->
mbyte ubs2segs mem3 a = mbyte ubs2segs memc a).
{ intros a Ha Hwa Hna. rewrite <- (K1 a Ha Hna). destruct Hwa as [(bb & m & Hbm & Hab) | Hwa].
- replace a with (bb + (a - bb)) by lia. apply (Hkeep3 bb m (a - bb) Hbm). lia.
- apply (proj1 (Hhi3 a ltac:(clear - Ha Hwa Hceil HFSv Hac; lia) ltac:(clear - Hwa Hna ASv; lia))). }
destruct Hres as [[-> Hbl] | (Hnz & Hi16 & (b1 & b2 & Hbl3 & Hblc3) & Hwr3)].
+
pin_reg HS (10%bv:reg) 0 Hi10.
jrun_to LAWS ubs2tbl_ok HS HJ3 FL_RET. { apply WR; [ew_havocA; exact HU2 | repeat constructor; cbn; lia]. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms0) a = mbyte ubs2segs mem3 a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply (fl_ret API IMG L A mem md regs0 _ L3 A3 (ms_mem ms0) md3 g N s i f gen1 (rw_cur s) rest FP);
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16 | | exact Hwf | exact Hf | rewrite Hbl; exact HB | | | ].
* split; [| split].
-- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk].
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); left; reflexivity).
rewrite K3 by (clear - Hk Hg0 Hg1 Hceil HFSv HGSv Hac; lia). apply K2; [clear - Hk Hg0 Hg1 Hac HGSv; lia | left; exists g, CGIF_SIZE; split; [exact Hgin | clear - Hk HGSv; lia] | clear - Hk Hg1 Hceil HFSv HGSv Hac; lia].
-- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
assert (Hrin : In (cg_raw s, RAW_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); right; left; reflexivity).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk].
rewrite K3 by (clear - Hk Hr0 Hr1 Hceil HFSv HRWv Hac; lia). apply K2; [clear - Hk Hr0 Hr1 Hac HRWv; lia | left; exists (cg_raw s), RAW_SIZE; split; [exact Hrin | clear - Hk HRWv; lia] | clear - Hk Hr1 Hceil HFSv HRWv Hac; lia].
-- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
assert (XX : exists y, In (Some y) (cg_frames s) /\ fr_ptr y = fr_ptr x).
{ destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]]; [exists f; auto | exists x; auto]. }
destruct XX as (y & Hy & Hyx). destruct (Hfgeom y Hy) as (Y0 & Y1 & _).
assert (Hyin : In (fr_ptr y, FRAME_SIZE) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif g s N y _ _ Hy). left. reflexivity. }
eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk]. rewrite <- Hyx.
rewrite K3 by (clear - Hk Y0 Y1 Hceil HFSv HFRv Hac; lia). apply K2; [clear - Hk Y0 Y1 Hac HFRv; lia | left; exists (fr_ptr y), FRAME_SIZE; split; [exact Hyin | clear - Hk HFRv; lia] | clear - Hk Y1 Hceil HFSv HFRv Hac; lia].
* apply (fl_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite K3 by (clear - Ha Hceil Hsp063 HFSv Hac; lia).
apply K2; [clear - Ha Hceil Hsp063 HFSv Hac; lia | right; clear - Ha; lia | clear - Ha; lia].
* reg_nowF HS ltac:(ew_havocA; rewrite (HE 2%nat 2%bv eq_refl), G2, Z_to_bv_bv_unsigned; reflexivity).
* split; [reg_nowF HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3) | reg_nowF HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)].
+
assert (Hnewin : In (pNew, N) (blocks L3 A3)) by (rewrite Hbl3; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L3 A3 mem3 md3 pNew N HH3 Hnewin) as [Hn0 Hn1].
assert (Hsub3 : forall bb, In bb (blocks Lc Ac) -> In bb (blocks L3 A3)).
{ intros bb Hbb. rewrite Hbl3. rewrite Hblc3 in Hbb. apply in_app_iff in Hbb. apply in_app_iff. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; right; exact Hbb]. }
assert (Hsepn : forall y, In y (blocks Lc Ac) -> pNew + N <= fst y \/ fst y + snd y <= pNew).
{ intros y Hy. apply (heap_sep _ _ LAWS L3 A3 mem3 md3 b1 (pNew, N) b2 y HH3 Hbl3). rewrite <- Hblc3. exact Hy. }
assert (Hnew_notc : ~ In (pNew, N) (blocks Lc Ac)) by (rewrite Hblc3; exact (fresh_not_in API L3 A3 mem3 md3 b1 b2 pNew N HH3 Hbl3 ltac:(clear - HN HW1 HH1; nia))).
assert (Hnew_fp : In (pNew, N) (blocks L A) -> forall k, 0 <= k < N -> inFP FP (pNew + k)) by (intros Hin k Hk; exact (Hgone pNew N k Hin Hnew_notc Hk)).
assert (HB3 : Permutation (blocks L3 A3) ((pNew, N) :: cgif_blocks g s N ++ rest)).
{ rewrite Hbl3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc3. exact HB. }
add_fact HS 93%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq93, unsigned_lit_small by lia. change (2 ^ 4) with 16. clear - Hn0 Hn1 Hi16 Hac HN HW1 HH1. nia. }
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_memcpy. { apply WR; [ew_havocA; exact HU2 | repeat constructor; cbn; lia]. }
jreg HS (10%bv:reg) as M0. rewrite Hq93 in M0.
jreg HS (11%bv:reg) as M1. rewrite HE63 in M1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs2segs Ec ssc msc 12%bv HS) as M2; eval_sr_get_in M2; rewrite ?denot_add0 in M2; ew_havocA_in M2;
first [ rewrite (denot_mul_atoms _ 19 27 (cg_H s) (cg_W s)) in M2 by first [clear - RW RH HN HNle; nia | ew_havocA; rewrite (HE 19%nat 19%bv eq_refl); exact G19 | ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27]
| rewrite (denot_mul_atoms _ 27 19 (cg_W s) (cg_H s)) in M2 by first [clear - RW RH HN HNle; nia | ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | ew_havocA; rewrite (HE 19%nat 19%bv eq_refl); exact G19] ] end.
replace (cg_H s * cg_W s) with N in M2 by (clear - HN; lia). replace (cg_W s * cg_H s) with N in M2 by (clear - HN; lia).
jreg HS (1%bv:reg) as Mra.
cbn [ms_mem mkst] in HF.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms0) a = mbyte ubs2segs mem3 a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2, ?HU81; lia |]); destruct Hr. }
clear HF.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs2_memcpy) with (d := pNew) (src := fr_img f) (n := N);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact M0 | exact M1 | exact M2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | clear - HN HW1 HH1; nia | clear - Hn0; lia | clear - Him0; lia | clear - Hn1 Hac; lia | clear - Him1 Hac; lia | | | | ].
- intros k Hk. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 pNew N k HH3 Hnewin Hk)).
- intros k Hk. apply (present_mbyte ubs2_msyms). match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 (fr_img f) N k HH3 (Hsub3 _ Himgfin) Hk)).
- pose proof (Hsepn _ Himgfin) as X. cbn [fst snd] in X. clear - X. lia.
- intros a Ha. replace a with (pNew + (a - pNew)) by lia. apply (Hwr3 (blocks L3 A3) (a - pNew) Hnewin). lia. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & Hd10 & Hfr5 & Hout5 & Hgr5 & Hcpy5). clear HJ3 HG.
jafter_stretch_keep HS 105%nat regs5 mem5 MEMCPY_CLOB FL_CRET [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr5 : P); [| assert (HKm5 : Q); [| specialize (HS2 HKr5 HKm5); clear HKr5 HKm5]] end.
{ intros rr Hrr. apply Hfr5. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; clear - Ha Hn1 Hceil HFSv Hac; lia | cbn; lia | cbn; lia].
- pose proof (Hsepn (fr_ptr f, FRAME_SIZE) ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N f _ _ Hfin); left; reflexivity)) as X. cbn [fst snd] in X.
eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU81; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU81; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU81; intros a Ha; clear - Ha X HFRv; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ec ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs Ec ssx msx 0 _ 2%nat (sp0 - 272) HS eq_refl eq_refl ltac:(ew_havocA; exact HU2)) as Hcs end.
cbn [r_chunks] in Hcs.
lazymatch type of HS with st_ok _ ?Ec ?ssx ?msx =>
assert (RG : forall (r : reg) n wv, sr_get (ss_regs ssx) r = SOff n 0 -> ew Ec n = wv -> getr (ms_regs msx) r = wv)
by (intros r n wv Hr Hv; rewrite (st_ok_reg ubs2segs Ec ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hv) end.
assert (ALL : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> (a < pNew \/ pNew + N <= a) ->
((exists bb m, In (bb, m) (blocks Lc Ac) /\ bb <= a < bb + m) \/ sp0 - 272 <= a) ->
mbyte ubs2segs mem5 a = mbyte ubs2segs memc a).
{ intros a Ha Hna W2 Hw'. unfold mbyte at 1. rewrite (Hout5 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; exact W2). fold (mbyte ubs2segs (ms_mem ms0) a).
rewrite (K3 a Ha Hna). apply (K2 a Ha Hw' Hna). }
assert (Hwh : w * h <= N) by (rewrite HN; clear - Hw Hlw Hl0 Hh Hth Ht0; nia).
apply (GO3 _ _ L3 A3 md3 pNew N HJ5 Hid3 HB3 Hnew_fp Hwh).
* intros bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. pose proof (Hsepn _ Hbn') as X. cbn [fst snd] in X.
apply ALL; [clear - R0 R1 Hk Hac; lia | clear - R0 R1 Hk Hceil HFSv Hac; lia | clear - X Hk; lia | left; exists bb, nn; split; [exact Hbn' | clear - Hk; lia]].
* intros a Ha. apply ALL; [clear - Ha Hceil Hsp063 HFSv Hac; lia | clear - Ha; lia | clear - Ha Hn1 Hceil HFSv Hac; lia | right; clear - Ha; lia].
* apply (RG 9%bv 9%nat _ eq_refl); ew_havocA; rewrite (HE 9%nat 9%bv eq_refl); exact G9.
* apply (RG 23%bv 23%nat _ eq_refl); ew_havocA; rewrite (HE 23%nat 23%bv eq_refl); exact G23.
* cw Hcs 96 (SOff 82 0) HE82. clear - Ht0 Hth Hh RH; lia.
* apply (RG 22%bv 22%nat _ eq_refl); ew_havocA; rewrite (HE 22%nat 22%bv eq_refl); exact G22.
* apply (RG 2%bv 2%nat _ eq_refl); ew_havocA; rewrite (HE 2%nat 2%bv eq_refl); exact G2.
* cw Hcs 112 (SOff 80 0) HE80. clear - Hg0 Hg1 HGSv Hac; lia.
* cw Hcs 120 (SOff 81 0) HE81. clear - Hp0 Hp1 HFRv Hac; lia.
* apply (RG 18%bv 18%nat _ eq_refl); ew_havocA; rewrite (HE 18%nat 18%bv eq_refl); exact G18.
* apply (RG 8%bv 93%nat _ eq_refl); ew_havocA; exact Hq93.
* cw Hcs 56 (SOff 86 0) HE86. clear - Ru1; lia.
* cw Hcs 104 (SOff 88 0) HE88. clear - RW; lia.
* cw Hcs 64 (SOff 16 0) HE16h. clear - Hh Hth Ht0 RH; lia.
* apply (RG 3%bv 3%nat _ eq_refl); ew_havocA; rewrite (HE 3%nat 3%bv eq_refl); exact G3.
* apply (RG 4%bv 4%nat _ eq_refl); ew_havocA; rewrite (HE 4%nat 4%bv eq_refl); exact G4.
-
pose proof (MK false Hpz) as HS. clear MK.
destruct Htmp as [[_ Hz] | (Htm & _ & Hwh)]; [exfalso; exact (Hpz Hz)|]. subst tmp.
jrun_to LAWS ubs2tbl_ok HS HJ FL_T3. { apply WR; [exact HU2 | repeat constructor; cbn; lia]. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
pose proof (st_region_chunks ubs2segs E ssx ms 0 _ 2%nat (sp0 - 272) HS eq_refl eq_refl HU2) as Hcs end.
cbn [r_chunks] in Hcs.
assert (RG : forall (r : reg) n wv, sr_get (ss_regs ltac:(lazymatch type of HS with st_ok _ _ ?ssx _ => exact ssx end)) r = SOff n 0 -> ew E n = wv -> getr (ms_regs ms) r = wv).
{ intros r n wv Hr Hv. lazymatch type of HS with st_ok _ _ ?ssx ?msx => rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr end. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hv. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO3 (ms_regs ms) (ms_mem ms) Lc Ac mdc pTmp Nt HJ Hid HB Htmp_fp Hwh (KBof _ K1));
[ intros a Ha; apply K1; clear - Ha Hceil Hsp063 HFSv Hac; lia
| apply (RG 9%bv 9%nat _ eq_refl); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG 23%bv 23%nat _ eq_refl); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| cw Hcs 96 (SOff 82 0) HE82; clear - Ht0 Hth Hh RH; lia
| apply (RG 22%bv 22%nat _ eq_refl); rewrite (HE 22%nat 22%bv eq_refl); exact G22
| apply (RG 2%bv 2%nat _ eq_refl); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| cw Hcs 112 (SOff 80 0) HE80; clear - Hg0 Hg1 HGSv Hac; lia
| cw Hcs 120 (SOff 81 0) HE81; clear - Hp0 Hp1 HFRv Hac; lia
| apply (RG 18%bv 18%nat _ eq_refl); rewrite (HE 18%nat 18%bv eq_refl); exact G18
| apply (RG 8%bv 8%nat _ eq_refl); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| cw Hcs 56 (SOff 86 0) HE86; clear - Ru1; lia
| cw Hcs 104 (SOff 88 0) HE88; clear - RW; lia
| cw Hcs 64 (SOff 16 0) HE16h; clear - Hh Hth Ht0 RH; lia
| apply (RG 3%bv 3%nat _ eq_refl); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG 4%bv 4%nat _ eq_refl); rewrite (HE 4%nat 4%bv eq_refl); exact G4 ].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
