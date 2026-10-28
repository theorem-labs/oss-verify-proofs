(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m
YI00 YI02 YI01 YI03 YI04 YI5a UI1e UI2m UI26 UI2r
UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl := cbv; repeat (first [ left; reflexivity | right ]).
Lemma U_zext32_sh : forall E a x,
U E a = x -> 0 <= x < 2 ^ 32 -> U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = x.
Proof.
intros E a x Hx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; change (2 ^ 32) with 4294967296 in *; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_zext16_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 -> U E (SExt false 16 (SOff n 0)) = v.
Proof.
intros E n v H Hv. rewrite U_zext, (U_atom E n v H) by lia. change (2 ^ Z.of_N 16) with 65536. apply Z.mod_small. lia.
Qed.
Lemma U_sltu_t : forall E a b x y, U E a = x -> U E b = y -> x < y -> U E (SAlu ALU_SLTU a b) = 1.
Proof. intros E a b x y Ha Hb Hxy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. destruct (Z.ltb_spec x y); [reflexivity | lia]. Qed.
Lemma U_sltu_f : forall E a b x y, U E a = x -> U E b = y -> y <= x -> U E (SAlu ALU_SLTU a b) = 0.
Proof. intros E a b x y Ha Hb Hxy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. destruct (Z.ltb_spec x y); [lia | reflexivity]. Qed.
Lemma U_xor01 : forall E a b x y, U E a = x -> U E b = y -> 0 <= x <= 1 -> 0 <= y <= 1 -> U E (SAlu ALU_XOR a b) = Z.lxor x y.
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb.
assert (Cx : x = 0 \/ x = 1) by lia. assert (Cy : y = 0 \/ y = 1) by lia.
destruct Cx as [-> | ->]; destruct Cy as [-> | ->]; reflexivity.
Qed.
Ltac uv :=
first
[ solve [apply U_lit; lia]
| solve [eapply U_atom; [eassumption | lia]]
| solve [eapply U_zext16_atom; [eassumption | lia]]
| solve [eapply U_zext32_sh; [uv | lia]]
| solve [eapply U_add_small; [uv | uv | lia | lia | lia]]
| solve [eapply U_addw_small; [uv | uv | lia | lia | lia]]
| solve [eapply U_mul_small; [uv | uv | lia | lia | first [lia | nia]]]
| solve [eapply U_sltu_t; [uv | uv | lia]]
| solve [eapply U_sltu_f; [uv | uv | lia]]
| solve [eapply U_xor01; [uv | uv | lia | lia]] ].
Ltac ueval_in H :=
repeat match type of H with context [U ?E0 ?e] =>
let v := fresh "v" in let Hv := fresh "Hv" in
evar (v : Z); assert (Hv : U E0 e = v); [subst v; uv | rewrite Hv in H; subst v; clear Hv] end.
Ltac bc_prop H :=
rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in H; ueval_in H;
first
[ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H
| apply negb_true_iff in H; first [apply Z.ltb_ge in H | apply Z.eqb_neq in H]
| apply negb_false_iff in H; first [apply Z.ltb_lt in H | apply Z.eqb_eq in H]
| idtac ].
Ltac chk_tac :=
exfalso; lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
bc_prop Hc; first [lia | (vm_compute in Hc; lia)] end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_Lcf (pc : Z) (fs : list (nat * afact)) : sstate :=
mkSS pc sr_atoms [YQ0b.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawFrameConfig 32 lits_RFC)] None
(mkFacts (fs ++ [(9%nat, mkAF (CEIL_MIN + 8704) (2^63 - 40) 3)]) [] []).
Definition FIMG : list (nat * afact) := [(33%nat, mkAF 4096 CEIL_MAX 0)].
Definition FDST (n : nat) : list (nat * afact) := [(n, mkAF 4096 CEIL_MAX 0)].
Definition ss_L1 : sstate := Eval vm_compute in ss_Lcf PC_L1 FIMG.
Definition ss_L1r : sstate := Eval vm_compute in ss_Lcf (PC_L1 + 0x38) (FDST 20).
Definition ss_L2 : sstate := Eval vm_compute in ss_Lcf PC_L2 FIMG.
Definition ss_L2r : sstate := Eval vm_compute in ss_Lcf (PC_L2 + 0x38) (FDST 21).
Definition ss_L3 : sstate := Eval vm_compute in ss_Lcf PC_L3 FIMG.
Definition ss_L3r : sstate := Eval vm_compute in ss_Lcf (PC_L3 + 0x38) (FDST 20).
Definition ss_L4 : sstate := Eval vm_compute in ss_Lcf PC_L4 FIMG.
Definition ss_L4r : sstate := Eval vm_compute in ss_Lcf (PC_L4 + 0x38) (FDST 21).
Definition LKEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 27]%bv.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition loop_post (pcx : Z) (rd rt : reg) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte)
(pint img w h i step R : Z) (c' : config) : Prop :=
exists regs' mem' (m : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 pcx) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
1 <= m /\ i + step * (m - 1) < h /\ h <= i + step * m /\
getr regs' rd = Z_to_bv 64 (pint + w * (R + m)) /\ getr regs' rt = Z_to_bv 64 (pint + w * (R + m)) /\
getr regs' 10 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 w /\
(forall r, In r LKEPT -> getr regs' r = getr regs r) /\
(forall x : word, bv_unsigned x < pint + w * R \/ pint + w * h <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem' /\
(forall j k, 0 <= j < m -> 0 <= k < w -> mbyte ubs2segs mem' (pint + w * (R + j) + k) = mbyte ubs2segs memc (img + w * (i + step * j) + k)).
Definition loop_stmt (pch pcx step : Z) (rc rd rt : reg) : Prop :=
forall (n : nat) (i R : Z) (regs : bvmap 5 word) memc STK sp0 FP L A mem md Lc Ac mdc (pint npint img Nimg w h cfp : Z) (cv : list Z),
h - i <= step * Z.of_nat n -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + step * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
In (pint, npint) (blocks Lc Ac) ->
(forall blc i, In (pint, npint) blc -> 0 <= i < npint -> wr_byte STK sp0 FP (blocks L A) blc (pint + i)) ->
In (img, Nimg) (blocks Lc Ac) ->
(pint + npint <= img \/ img + Nimg <= pint) ->
obj_at ubs2segs memc cfp LAY_RawFrameConfig cv -> nth_error cv 1 = Some img -> nth_error cv 3 = Some w -> nth_error cv 4 = Some h ->
alloc_ceiling + 8704 <= cfp -> cfp + 40 <= 2 ^ 63 -> cfp mod 8 = 0 -> getr regs 9 = Z_to_bv 64 cfp ->
getr regs rd = Z_to_bv 64 (pint + w * R) -> getr regs rc = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 w ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 pch) memc (seg_rom ubs2segs)) mdc)
(loop_post pcx rd rt STK sp0 FP L A mem md Lc Ac mdc regs memc pint img w h i step R).
Lemma il_loop1 : loop_stmt PC_L1 PC_L1X 8 26%bv 20%bv 21%bv.
Proof.
unfold loop_stmt.
induction n as [|n IH]; intros i R regs memc STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv
Hn Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Hpnot Himg Hsep HOC Hcv1 Hcv3 Hcv4 Hcfp0 Hcfp1 Hcfp8 G9 Gd Gc G12; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pint npint HH Hpin ltac:(nia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img Nimg HH Himg ltac:(nia)) as (Hi0 & Hi1 & _).
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by nia.
assert (Hwi : 0 <= w * i /\ w * (i + 1) <= w * h) by nia.
assert (Hiw : 0 <= i * w < 2 ^ 32) by nia.
assert (Hfar : pint + w * R + w <= cfp) by (clear - Hp1 HwR Hnp Hcfp0; lia).
remember (Ereg regs (map (Z_to_bv 64) cv ++ [])) as E eqn:HE0.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE9 : ew E 9 = Z_to_bv 64 cfp) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE33 : ew E 33 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs cv [] 1 img Hcv1)).
assert (HEd : ew E 20 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE 20%nat 20%bv eq_refl); exact Gd).
assert (HEc : ew E 26 = Z_to_bv 64 i) by (rewrite (HE 26%nat 26%bv eq_refl); exact Gc).
assert (HE12 : ew E 12 = Z_to_bv 64 w) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HS : st_ok ubs2segs E ss_L1 (mkst regs (Z_to_bv 64 PC_L1) memc (seg_rom ubs2segs))).
{ subst E. change ss_L1 with (ss_Lcf PC_L1 FIMG). unfold ss_Lcf, FIMG. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ memc 9 cfp); [rewrite HE9; apply unsigned_lit_small; lia | lia | lia | exact HOC | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE33, HE9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 PC_L1) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msM end.
jreg HS (10%bv:reg) as M10. rewrite HEd in M10.
reg_U HS (11%bv:reg) uv M11.
reg_U HS (12%bv:reg) uv M12.
jreg HS (1%bv:reg) as M1.
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ (LKEPT ++ [20; 26]%bv) HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ0 : forall x : word, ms_mem msM x = memc x) by (intros x; mem_chain ltac:(fun H => idtac)).
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs2_memcpy) with (d := pint + w * R) (src := img + w * i) (n := w);
[ exact HS | reflexivity | reflexivity | exact HJ | exact M10 | rewrite M11; f_equal; lia | exact M12 | exact M1
| cbn [sv_denot]; apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | clear - Hsep HwR Hwi Hnp HNi; lia | ].
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (pint + w * R + k) with (pint + (w * R + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pint npint (w * R + k) HH Hpin ltac:(nia))).
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (img + w * i + k) with (img + (w * i + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img Nimg (w * i + k) HH Himg ltac:(nia))).
- intros a Ha. replace a with (pint + (a - pint)) by lia. apply (Hpnot (blocks Lc Ac)); [exact Hpin | nia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3). change (ms_segs ubs2_msyms) with ubs2segs in Hcp3.
cbn [ms_regs ms_mem] in Hfr3, Hout3, Hgr3, HJ3.
assert (F : forall r : reg, In r (LKEPT ++ [20; 26]%bv) -> getr regs3 r = getr regs r).
{ intros r Hr. rewrite (Hfr3 r). { apply HK. exact Hr. }
cbv [LKEPT app In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (HOC3 : obj_at ubs2segs mem3 cfp LAY_RawFrameConfig cv).
{ eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. rewrite (Hout3 (Z_to_bv 64 (cfp + k))) by (rewrite unsigned_lit_small by lia; lia). apply MEQ0. }
remember (Ereg regs3 (map (Z_to_bv 64) cv ++ [])) as E3 eqn:HE3.
assert (HE' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E3 k = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (X9 : ew E3 9 = Z_to_bv 64 cfp) by (rewrite (HE' 9%nat 9%bv eq_refl), F by inl; exact G9).
assert (X35 : ew E3 35 = Z_to_bv 64 w) by (subst E3; apply (Ereg_vals regs3 cv [] 3 w Hcv3)).
assert (X36 : ew E3 36 = Z_to_bv 64 h) by (subst E3; apply (Ereg_vals regs3 cv [] 4 h Hcv4)).
assert (Xd : ew E3 20 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE' 20%nat 20%bv eq_refl), F by inl; exact Gd).
assert (Xc : ew E3 26 = Z_to_bv 64 i) by (rewrite (HE' 26%nat 26%bv eq_refl), F by inl; exact Gc).
assert (HS3 : st_ok ubs2segs E3 ss_L1r (mkst regs3 (Z_to_bv 64 (PC_L1 + 0x38)) mem3 (seg_rom ubs2segs))).
{ subst E3. change ss_L1r with (ss_Lcf (PC_L1 + 0x38) (FDST 20)). unfold ss_Lcf, FDST. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ mem3 9 cfp); [rewrite X9; apply unsigned_lit_small; lia | lia | lia | exact HOC3 | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Xd, X9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (PC_L1 + 0x38)) mem3 (seg_rom ubs2segs))) in HJ3.
clear HS. rename HS3 into HS.
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS.
-
bc_prop Hc.
assert (Hlt : i + 8 < h) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L1; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (20%bv:reg) uv Nd.
reg_U HS (26%bv:reg) uv Nc.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 8) (R + 1) _ _ STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv);
[lia | lia | lia | | lia | lia | exact Hnp | exact HNi | exact HJ3 | exact Hpin | exact Hpnot | exact Himg | exact Hsep
| | exact Hcv1 | exact Hcv3 | exact Hcv4 | exact Hcfp0 | exact Hcfp1 | exact Hcfp8 | rewrite HK2, F by inl; exact G9
| rewrite Nd; f_equal; lia | rewrite Nc; f_equal; lia | exact N12 ].
- intros j Hj Hij. pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)). lia.
- eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC3 | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. apply MEQ1. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & Pd & Pt & P10 & P12 & HKf & Hout' & Hgr' & Hcp').
exists regs', mem', (m + 1). split; [reflexivity|]. split; [exact HJ'|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Pd; f_equal; lia|]. split; [rewrite Pt; f_equal; lia|].
split; [exact P10|]. split; [exact P12|].
split. { intros r Hr. rewrite (HKf r Hr), (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. rewrite (Hout' x ltac:(nia)), MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { intros x Hx. apply Hgr'. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
intros j k Hj Hk. destruct (Z.eq_dec j 0) as [-> | Hj0].
* rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)).
{ apply mbyte_eq_of1'. rewrite (Hout' (Z_to_bv 64 (pint + w * R + k))) by (rewrite unsigned_lit_small by lia; nia). apply MEQ1. }
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
* replace (pint + w * (R + j) + k) with (pint + w * (R + 1 + (j - 1)) + k) by lia.
rewrite (Hcp' (j - 1) k) by lia.
match goal with |- mbyte _ _ ?a = mbyte _ _ ?b => replace a with b by lia end.
apply mbyte_eq_of1'. rewrite MEQ1.
lazymatch goal with |- _ (Z_to_bv 64 (img + w * ?r + k)) = _ =>
assert (Hrow : 0 <= r <= h - 1) by lia;
assert (Hwr1 : 0 <= w * r) by (apply Z.mul_nonneg_nonneg; lia);
assert (Hwr2 : w * r <= w * (h - 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
assert (Hxo : bv_unsigned (Z_to_bv 64 (img + w * r + k)) < pint + w * R \/ pint + w * R + w <= bv_unsigned (Z_to_bv 64 (img + w * r + k)))
by (clear - Hsep HwR Hwi Hnp HNi Hk Hrow Hwr1 Hwr2 Hi Hw Hh Hp0 Hp1 Hi0 Hi1 Hac HR; rewrite unsigned_lit_small by lia; lia)
end.
rewrite (Hout3 _ Hxo). apply MEQ0.
-
bc_prop Hc.
assert (Hge : h <= i + 8) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L1X; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (20%bv:reg) uv Nd.
reg_U HS (21%bv:reg) uv Nt.
reg_U HS (10%bv:reg) uv N10.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists (ms_regs msF), (ms_mem msF), 1. split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Nd; f_equal; lia|]. split; [rewrite Nt; f_equal; lia|].
split; [exact N10|]. split; [exact N12|].
split. { intros r Hr. rewrite (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. cbn [ms_mem]. rewrite MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { cbn [ms_mem]. intros x Hx. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
cbn [ms_mem]. intros j k Hj Hk. replace j with 0 by lia. rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)); [apply mbyte_eq_of1'; apply MEQ1|].
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
Qed.
Lemma il_loop2 : loop_stmt PC_L2 PC_L2X 8 26%bv 21%bv 20%bv.
Proof.
unfold loop_stmt.
induction n as [|n IH]; intros i R regs memc STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv
Hn Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Hpnot Himg Hsep HOC Hcv1 Hcv3 Hcv4 Hcfp0 Hcfp1 Hcfp8 G9 Gd Gc G12; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pint npint HH Hpin ltac:(nia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img Nimg HH Himg ltac:(nia)) as (Hi0 & Hi1 & _).
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by nia.
assert (Hwi : 0 <= w * i /\ w * (i + 1) <= w * h) by nia.
assert (Hiw : 0 <= i * w < 2 ^ 32) by nia.
assert (Hfar : pint + w * R + w <= cfp) by (clear - Hp1 HwR Hnp Hcfp0; lia).
remember (Ereg regs (map (Z_to_bv 64) cv ++ [])) as E eqn:HE0.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE9 : ew E 9 = Z_to_bv 64 cfp) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE33 : ew E 33 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs cv [] 1 img Hcv1)).
assert (HEd : ew E 21 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE 21%nat 21%bv eq_refl); exact Gd).
assert (HEc : ew E 26 = Z_to_bv 64 i) by (rewrite (HE 26%nat 26%bv eq_refl); exact Gc).
assert (HE12 : ew E 12 = Z_to_bv 64 w) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HS : st_ok ubs2segs E ss_L2 (mkst regs (Z_to_bv 64 PC_L2) memc (seg_rom ubs2segs))).
{ subst E. change ss_L2 with (ss_Lcf PC_L2 FIMG). unfold ss_Lcf, FIMG. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ memc 9 cfp); [rewrite HE9; apply unsigned_lit_small; lia | lia | lia | exact HOC | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE33, HE9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 PC_L2) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msM end.
jreg HS (10%bv:reg) as M10. rewrite HEd in M10.
reg_U HS (11%bv:reg) uv M11.
reg_U HS (12%bv:reg) uv M12.
jreg HS (1%bv:reg) as M1.
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ (LKEPT ++ [21; 26]%bv) HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ0 : forall x : word, ms_mem msM x = memc x) by (intros x; mem_chain ltac:(fun H => idtac)).
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs2_memcpy) with (d := pint + w * R) (src := img + w * i) (n := w);
[ exact HS | reflexivity | reflexivity | exact HJ | exact M10 | rewrite M11; f_equal; lia | exact M12 | exact M1
| cbn [sv_denot]; apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | clear - Hsep HwR Hwi Hnp HNi; lia | ].
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (pint + w * R + k) with (pint + (w * R + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pint npint (w * R + k) HH Hpin ltac:(nia))).
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (img + w * i + k) with (img + (w * i + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img Nimg (w * i + k) HH Himg ltac:(nia))).
- intros a Ha. replace a with (pint + (a - pint)) by lia. apply (Hpnot (blocks Lc Ac)); [exact Hpin | nia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3). change (ms_segs ubs2_msyms) with ubs2segs in Hcp3.
cbn [ms_regs ms_mem] in Hfr3, Hout3, Hgr3, HJ3.
assert (F : forall r : reg, In r (LKEPT ++ [21; 26]%bv) -> getr regs3 r = getr regs r).
{ intros r Hr. rewrite (Hfr3 r). { apply HK. exact Hr. }
cbv [LKEPT app In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (HOC3 : obj_at ubs2segs mem3 cfp LAY_RawFrameConfig cv).
{ eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. rewrite (Hout3 (Z_to_bv 64 (cfp + k))) by (rewrite unsigned_lit_small by lia; lia). apply MEQ0. }
remember (Ereg regs3 (map (Z_to_bv 64) cv ++ [])) as E3 eqn:HE3.
assert (HE' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E3 k = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (X9 : ew E3 9 = Z_to_bv 64 cfp) by (rewrite (HE' 9%nat 9%bv eq_refl), F by inl; exact G9).
assert (X35 : ew E3 35 = Z_to_bv 64 w) by (subst E3; apply (Ereg_vals regs3 cv [] 3 w Hcv3)).
assert (X36 : ew E3 36 = Z_to_bv 64 h) by (subst E3; apply (Ereg_vals regs3 cv [] 4 h Hcv4)).
assert (Xd : ew E3 21 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE' 21%nat 21%bv eq_refl), F by inl; exact Gd).
assert (Xc : ew E3 26 = Z_to_bv 64 i) by (rewrite (HE' 26%nat 26%bv eq_refl), F by inl; exact Gc).
assert (HS3 : st_ok ubs2segs E3 ss_L2r (mkst regs3 (Z_to_bv 64 (PC_L2 + 0x38)) mem3 (seg_rom ubs2segs))).
{ subst E3. change ss_L2r with (ss_Lcf (PC_L2 + 0x38) (FDST 21)). unfold ss_Lcf, FDST. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ mem3 9 cfp); [rewrite X9; apply unsigned_lit_small; lia | lia | lia | exact HOC3 | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Xd, X9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (PC_L2 + 0x38)) mem3 (seg_rom ubs2segs))) in HJ3.
clear HS. rename HS3 into HS.
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS.
-
bc_prop Hc.
assert (Hge : h <= i + 8) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L2X; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (21%bv:reg) uv Nd.
reg_U HS (20%bv:reg) uv Nt.
reg_U HS (10%bv:reg) uv N10.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists (ms_regs msF), (ms_mem msF), 1. split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Nd; f_equal; lia|]. split; [rewrite Nt; f_equal; lia|].
split; [exact N10|]. split; [exact N12|].
split. { intros r Hr. rewrite (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. cbn [ms_mem]. rewrite MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { cbn [ms_mem]. intros x Hx. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
cbn [ms_mem]. intros j k Hj Hk. replace j with 0 by lia. rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)); [apply mbyte_eq_of1'; apply MEQ1|].
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
-
bc_prop Hc.
assert (Hlt : i + 8 < h) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L2; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (21%bv:reg) uv Nd.
reg_U HS (26%bv:reg) uv Nc.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 8) (R + 1) _ _ STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv);
[lia | lia | lia | | lia | lia | exact Hnp | exact HNi | exact HJ3 | exact Hpin | exact Hpnot | exact Himg | exact Hsep
| | exact Hcv1 | exact Hcv3 | exact Hcv4 | exact Hcfp0 | exact Hcfp1 | exact Hcfp8 | rewrite HK2, F by inl; exact G9
| rewrite Nd; f_equal; lia | rewrite Nc; f_equal; lia | exact N12 ].
- intros j Hj Hij. pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)). lia.
- eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC3 | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. apply MEQ1. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & Pd & Pt & P10 & P12 & HKf & Hout' & Hgr' & Hcp').
exists regs', mem', (m + 1). split; [reflexivity|]. split; [exact HJ'|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Pd; f_equal; lia|]. split; [rewrite Pt; f_equal; lia|].
split; [exact P10|]. split; [exact P12|].
split. { intros r Hr. rewrite (HKf r Hr), (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. rewrite (Hout' x ltac:(nia)), MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { intros x Hx. apply Hgr'. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
intros j k Hj Hk. destruct (Z.eq_dec j 0) as [-> | Hj0].
* rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)).
{ apply mbyte_eq_of1'. rewrite (Hout' (Z_to_bv 64 (pint + w * R + k))) by (rewrite unsigned_lit_small by lia; nia). apply MEQ1. }
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
* replace (pint + w * (R + j) + k) with (pint + w * (R + 1 + (j - 1)) + k) by lia.
rewrite (Hcp' (j - 1) k) by lia.
match goal with |- mbyte _ _ ?a = mbyte _ _ ?b => replace a with b by lia end.
apply mbyte_eq_of1'. rewrite MEQ1.
lazymatch goal with |- _ (Z_to_bv 64 (img + w * ?r + k)) = _ =>
assert (Hrow : 0 <= r <= h - 1) by lia;
assert (Hwr1 : 0 <= w * r) by (apply Z.mul_nonneg_nonneg; lia);
assert (Hwr2 : w * r <= w * (h - 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
assert (Hxo : bv_unsigned (Z_to_bv 64 (img + w * r + k)) < pint + w * R \/ pint + w * R + w <= bv_unsigned (Z_to_bv 64 (img + w * r + k)))
by (clear - Hsep HwR Hwi Hnp HNi Hk Hrow Hwr1 Hwr2 Hi Hw Hh Hp0 Hp1 Hi0 Hi1 Hac HR; rewrite unsigned_lit_small by lia; lia)
end.
rewrite (Hout3 _ Hxo). apply MEQ0.
Qed.
Lemma il_loop3 : loop_stmt PC_L3 PC_L4P 4 26%bv 20%bv 21%bv.
Proof.
unfold loop_stmt.
induction n as [|n IH]; intros i R regs memc STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv
Hn Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Hpnot Himg Hsep HOC Hcv1 Hcv3 Hcv4 Hcfp0 Hcfp1 Hcfp8 G9 Gd Gc G12; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pint npint HH Hpin ltac:(nia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img Nimg HH Himg ltac:(nia)) as (Hi0 & Hi1 & _).
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by nia.
assert (Hwi : 0 <= w * i /\ w * (i + 1) <= w * h) by nia.
assert (Hiw : 0 <= i * w < 2 ^ 32) by nia.
assert (Hfar : pint + w * R + w <= cfp) by (clear - Hp1 HwR Hnp Hcfp0; lia).
remember (Ereg regs (map (Z_to_bv 64) cv ++ [])) as E eqn:HE0.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE9 : ew E 9 = Z_to_bv 64 cfp) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE33 : ew E 33 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs cv [] 1 img Hcv1)).
assert (HEd : ew E 20 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE 20%nat 20%bv eq_refl); exact Gd).
assert (HEc : ew E 26 = Z_to_bv 64 i) by (rewrite (HE 26%nat 26%bv eq_refl); exact Gc).
assert (HE12 : ew E 12 = Z_to_bv 64 w) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HS : st_ok ubs2segs E ss_L3 (mkst regs (Z_to_bv 64 PC_L3) memc (seg_rom ubs2segs))).
{ subst E. change ss_L3 with (ss_Lcf PC_L3 FIMG). unfold ss_Lcf, FIMG. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ memc 9 cfp); [rewrite HE9; apply unsigned_lit_small; lia | lia | lia | exact HOC | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE33, HE9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 PC_L3) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msM end.
jreg HS (10%bv:reg) as M10. rewrite HEd in M10.
reg_U HS (11%bv:reg) uv M11.
reg_U HS (12%bv:reg) uv M12.
jreg HS (1%bv:reg) as M1.
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ (LKEPT ++ [20; 26]%bv) HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ0 : forall x : word, ms_mem msM x = memc x) by (intros x; mem_chain ltac:(fun H => idtac)).
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs2_memcpy) with (d := pint + w * R) (src := img + w * i) (n := w);
[ exact HS | reflexivity | reflexivity | exact HJ | exact M10 | rewrite M11; f_equal; lia | exact M12 | exact M1
| cbn [sv_denot]; apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | clear - Hsep HwR Hwi Hnp HNi; lia | ].
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (pint + w * R + k) with (pint + (w * R + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pint npint (w * R + k) HH Hpin ltac:(nia))).
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (img + w * i + k) with (img + (w * i + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img Nimg (w * i + k) HH Himg ltac:(nia))).
- intros a Ha. replace a with (pint + (a - pint)) by lia. apply (Hpnot (blocks Lc Ac)); [exact Hpin | nia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3). change (ms_segs ubs2_msyms) with ubs2segs in Hcp3.
cbn [ms_regs ms_mem] in Hfr3, Hout3, Hgr3, HJ3.
assert (F : forall r : reg, In r (LKEPT ++ [20; 26]%bv) -> getr regs3 r = getr regs r).
{ intros r Hr. rewrite (Hfr3 r). { apply HK. exact Hr. }
cbv [LKEPT app In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (HOC3 : obj_at ubs2segs mem3 cfp LAY_RawFrameConfig cv).
{ eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. rewrite (Hout3 (Z_to_bv 64 (cfp + k))) by (rewrite unsigned_lit_small by lia; lia). apply MEQ0. }
remember (Ereg regs3 (map (Z_to_bv 64) cv ++ [])) as E3 eqn:HE3.
assert (HE' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E3 k = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (X9 : ew E3 9 = Z_to_bv 64 cfp) by (rewrite (HE' 9%nat 9%bv eq_refl), F by inl; exact G9).
assert (X35 : ew E3 35 = Z_to_bv 64 w) by (subst E3; apply (Ereg_vals regs3 cv [] 3 w Hcv3)).
assert (X36 : ew E3 36 = Z_to_bv 64 h) by (subst E3; apply (Ereg_vals regs3 cv [] 4 h Hcv4)).
assert (Xd : ew E3 20 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE' 20%nat 20%bv eq_refl), F by inl; exact Gd).
assert (Xc : ew E3 26 = Z_to_bv 64 i) by (rewrite (HE' 26%nat 26%bv eq_refl), F by inl; exact Gc).
assert (HS3 : st_ok ubs2segs E3 ss_L3r (mkst regs3 (Z_to_bv 64 (PC_L3 + 0x38)) mem3 (seg_rom ubs2segs))).
{ subst E3. change ss_L3r with (ss_Lcf (PC_L3 + 0x38) (FDST 20)). unfold ss_Lcf, FDST. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ mem3 9 cfp); [rewrite X9; apply unsigned_lit_small; lia | lia | lia | exact HOC3 | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Xd, X9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (PC_L3 + 0x38)) mem3 (seg_rom ubs2segs))) in HJ3.
clear HS. rename HS3 into HS.
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS.
-
bc_prop Hc.
assert (Hge : h <= i + 4) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L4P; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (20%bv:reg) uv Nd.
reg_U HS (21%bv:reg) uv Nt.
reg_U HS (10%bv:reg) uv N10.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists (ms_regs msF), (ms_mem msF), 1. split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Nd; f_equal; lia|]. split; [rewrite Nt; f_equal; lia|].
split; [exact N10|]. split; [exact N12|].
split. { intros r Hr. rewrite (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. cbn [ms_mem]. rewrite MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { cbn [ms_mem]. intros x Hx. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
cbn [ms_mem]. intros j k Hj Hk. replace j with 0 by lia. rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)); [apply mbyte_eq_of1'; apply MEQ1|].
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
-
bc_prop Hc.
assert (Hlt : i + 4 < h) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (20%bv:reg) uv Nd.
reg_U HS (26%bv:reg) uv Nc.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 4) (R + 1) _ _ STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv);
[lia | lia | lia | | lia | lia | exact Hnp | exact HNi | exact HJ3 | exact Hpin | exact Hpnot | exact Himg | exact Hsep
| | exact Hcv1 | exact Hcv3 | exact Hcv4 | exact Hcfp0 | exact Hcfp1 | exact Hcfp8 | rewrite HK2, F by inl; exact G9
| rewrite Nd; f_equal; lia | rewrite Nc; f_equal; lia | exact N12 ].
- intros j Hj Hij. pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)). lia.
- eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC3 | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. apply MEQ1. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & Pd & Pt & P10 & P12 & HKf & Hout' & Hgr' & Hcp').
exists regs', mem', (m + 1). split; [reflexivity|]. split; [exact HJ'|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Pd; f_equal; lia|]. split; [rewrite Pt; f_equal; lia|].
split; [exact P10|]. split; [exact P12|].
split. { intros r Hr. rewrite (HKf r Hr), (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. rewrite (Hout' x ltac:(nia)), MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { intros x Hx. apply Hgr'. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
intros j k Hj Hk. destruct (Z.eq_dec j 0) as [-> | Hj0].
* rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)).
{ apply mbyte_eq_of1'. rewrite (Hout' (Z_to_bv 64 (pint + w * R + k))) by (rewrite unsigned_lit_small by lia; nia). apply MEQ1. }
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
* replace (pint + w * (R + j) + k) with (pint + w * (R + 1 + (j - 1)) + k) by lia.
rewrite (Hcp' (j - 1) k) by lia.
match goal with |- mbyte _ _ ?a = mbyte _ _ ?b => replace a with b by lia end.
apply mbyte_eq_of1'. rewrite MEQ1.
lazymatch goal with |- _ (Z_to_bv 64 (img + w * ?r + k)) = _ =>
assert (Hrow : 0 <= r <= h - 1) by lia;
assert (Hwr1 : 0 <= w * r) by (apply Z.mul_nonneg_nonneg; lia);
assert (Hwr2 : w * r <= w * (h - 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
assert (Hxo : bv_unsigned (Z_to_bv 64 (img + w * r + k)) < pint + w * R \/ pint + w * R + w <= bv_unsigned (Z_to_bv 64 (img + w * r + k)))
by (clear - Hsep HwR Hwi Hnp HNi Hk Hrow Hwr1 Hwr2 Hi Hw Hh Hp0 Hp1 Hi0 Hi1 Hac HR; rewrite unsigned_lit_small by lia; lia)
end.
rewrite (Hout3 _ Hxo). apply MEQ0.
Qed.
Lemma il_loop4 : loop_stmt PC_L4 PC_L4X 2 20%bv 21%bv 11%bv.
Proof.
unfold loop_stmt.
induction n as [|n IH]; intros i R regs memc STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv
Hn Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Hpnot Himg Hsep HOC Hcv1 Hcv3 Hcv4 Hcfp0 Hcfp1 Hcfp8 G9 Gd Gc G12; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pint npint HH Hpin ltac:(nia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img Nimg HH Himg ltac:(nia)) as (Hi0 & Hi1 & _).
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by nia.
assert (Hwi : 0 <= w * i /\ w * (i + 1) <= w * h) by nia.
assert (Hiw : 0 <= i * w < 2 ^ 32) by nia.
assert (Hfar : pint + w * R + w <= cfp) by (clear - Hp1 HwR Hnp Hcfp0; lia).
remember (Ereg regs (map (Z_to_bv 64) cv ++ [])) as E eqn:HE0.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE9 : ew E 9 = Z_to_bv 64 cfp) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE33 : ew E 33 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs cv [] 1 img Hcv1)).
assert (HEd : ew E 21 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE 21%nat 21%bv eq_refl); exact Gd).
assert (HEc : ew E 20 = Z_to_bv 64 i) by (rewrite (HE 20%nat 20%bv eq_refl); exact Gc).
assert (HE12 : ew E 12 = Z_to_bv 64 w) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HS : st_ok ubs2segs E ss_L4 (mkst regs (Z_to_bv 64 PC_L4) memc (seg_rom ubs2segs))).
{ subst E. change ss_L4 with (ss_Lcf PC_L4 FIMG). unfold ss_Lcf, FIMG. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ memc 9 cfp); [rewrite HE9; apply unsigned_lit_small; lia | lia | lia | exact HOC | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE33, HE9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 PC_L4) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msM end.
jreg HS (10%bv:reg) as M10. rewrite HEd in M10.
reg_U HS (11%bv:reg) uv M11.
reg_U HS (12%bv:reg) uv M12.
jreg HS (1%bv:reg) as M1.
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ (LKEPT ++ [21; 20]%bv) HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ0 : forall x : word, ms_mem msM x = memc x) by (intros x; mem_chain ltac:(fun H => idtac)).
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs2_memcpy) with (d := pint + w * R) (src := img + w * i) (n := w);
[ exact HS | reflexivity | reflexivity | exact HJ | exact M10 | rewrite M11; f_equal; lia | exact M12 | exact M1
| cbn [sv_denot]; apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | clear - Hsep HwR Hwi Hnp HNi; lia | ].
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (pint + w * R + k) with (pint + (w * R + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pint npint (w * R + k) HH Hpin ltac:(nia))).
- intros k Hk. eapply present_grows; [intros x0 Hx0; rewrite MEQ0; exact Hx0|].
replace (img + w * i + k) with (img + (w * i + k)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img Nimg (w * i + k) HH Himg ltac:(nia))).
- intros a Ha. replace a with (pint + (a - pint)) by lia. apply (Hpnot (blocks Lc Ac)); [exact Hpin | nia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3). change (ms_segs ubs2_msyms) with ubs2segs in Hcp3.
cbn [ms_regs ms_mem] in Hfr3, Hout3, Hgr3, HJ3.
assert (F : forall r : reg, In r (LKEPT ++ [21; 20]%bv) -> getr regs3 r = getr regs r).
{ intros r Hr. rewrite (Hfr3 r). { apply HK. exact Hr. }
cbv [LKEPT app In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (HOC3 : obj_at ubs2segs mem3 cfp LAY_RawFrameConfig cv).
{ eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. rewrite (Hout3 (Z_to_bv 64 (cfp + k))) by (rewrite unsigned_lit_small by lia; lia). apply MEQ0. }
remember (Ereg regs3 (map (Z_to_bv 64) cv ++ [])) as E3 eqn:HE3.
assert (HE' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E3 k = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (X9 : ew E3 9 = Z_to_bv 64 cfp) by (rewrite (HE' 9%nat 9%bv eq_refl), F by inl; exact G9).
assert (X35 : ew E3 35 = Z_to_bv 64 w) by (subst E3; apply (Ereg_vals regs3 cv [] 3 w Hcv3)).
assert (X36 : ew E3 36 = Z_to_bv 64 h) by (subst E3; apply (Ereg_vals regs3 cv [] 4 h Hcv4)).
assert (Xd : ew E3 21 = Z_to_bv 64 (pint + w * R)) by (rewrite (HE' 21%nat 21%bv eq_refl), F by inl; exact Gd).
assert (Xc : ew E3 20 = Z_to_bv 64 i) by (rewrite (HE' 20%nat 20%bv eq_refl), F by inl; exact Gc).
assert (HS3 : st_ok ubs2segs E3 ss_L4r (mkst regs3 (Z_to_bv 64 (PC_L4 + 0x38)) mem3 (seg_rom ubs2segs))).
{ subst E3. change ss_L4r with (ss_Lcf (PC_L4 + 0x38) (FDST 21)). unfold ss_Lcf, FDST. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ mem3 9 cfp); [rewrite X9; apply unsigned_lit_small; lia | lia | lia | exact HOC3 | reflexivity | | | intros k Hk; lia].
+ intros j v Hj. apply Ereg_vals. exact Hj.
+ intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
- cbn. repeat split.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Xd, X9, !unsigned_lit_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (PC_L4 + 0x38)) mem3 (seg_rom ubs2segs))) in HJ3.
clear HS. rename HS3 into HS.
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS; [chk_tac | clear Hc].
jrun LAWS ubs2tbl_ok HS HJ3; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
jbranch ubs2tbl HS.
-
bc_prop Hc.
assert (Hlt : i + 2 < h) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L4; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (21%bv:reg) uv Nd.
reg_U HS (20%bv:reg) uv Nc.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 2) (R + 1) _ _ STK sp0 FP L A mem md Lc Ac mdc pint npint img Nimg w h cfp cv);
[lia | lia | lia | | lia | lia | exact Hnp | exact HNi | exact HJ3 | exact Hpin | exact Hpnot | exact Himg | exact Hsep
| | exact Hcv1 | exact Hcv3 | exact Hcv4 | exact Hcfp0 | exact Hcfp1 | exact Hcfp8 | rewrite HK2, F by inl; exact G9
| rewrite Nd; f_equal; lia | rewrite Nc; f_equal; lia | exact N12 ].
- intros j Hj Hij. pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)). lia.
- eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HOC3 | reflexivity |].
intros k Hk. apply mbyte_eq_of1'. apply MEQ1. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & Pd & Pt & P10 & P12 & HKf & Hout' & Hgr' & Hcp').
exists regs', mem', (m + 1). split; [reflexivity|]. split; [exact HJ'|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Pd; f_equal; lia|]. split; [rewrite Pt; f_equal; lia|].
split; [exact P10|]. split; [exact P12|].
split. { intros r Hr. rewrite (HKf r Hr), (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. rewrite (Hout' x ltac:(nia)), MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { intros x Hx. apply Hgr'. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
intros j k Hj Hk. destruct (Z.eq_dec j 0) as [-> | Hj0].
* rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)).
{ apply mbyte_eq_of1'. rewrite (Hout' (Z_to_bv 64 (pint + w * R + k))) by (rewrite unsigned_lit_small by lia; nia). apply MEQ1. }
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
* replace (pint + w * (R + j) + k) with (pint + w * (R + 1 + (j - 1)) + k) by lia.
rewrite (Hcp' (j - 1) k) by lia.
match goal with |- mbyte _ _ ?a = mbyte _ _ ?b => replace a with b by lia end.
apply mbyte_eq_of1'. rewrite MEQ1.
lazymatch goal with |- _ (Z_to_bv 64 (img + w * ?r + k)) = _ =>
assert (Hrow : 0 <= r <= h - 1) by lia;
assert (Hwr1 : 0 <= w * r) by (apply Z.mul_nonneg_nonneg; lia);
assert (Hwr2 : w * r <= w * (h - 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
assert (Hxo : bv_unsigned (Z_to_bv 64 (img + w * r + k)) < pint + w * R \/ pint + w * R + w <= bv_unsigned (Z_to_bv 64 (img + w * r + k)))
by (clear - Hsep HwR Hwi Hnp HNi Hk Hrow Hwr1 Hwr2 Hi Hw Hh Hp0 Hp1 Hi0 Hi1 Hac HR; rewrite unsigned_lit_small by lia; lia)
end.
rewrite (Hout3 _ Hxo). apply MEQ0.
-
bc_prop Hc.
assert (Hge : h <= i + 2) by lia. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_L4X; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ LKEPT HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK2.
reg_U HS (21%bv:reg) uv Nd.
reg_U HS (11%bv:reg) uv Nt.
reg_U HS (10%bv:reg) uv N10.
reg_U HS (12%bv:reg) uv N12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ1 : forall x : word, ms_mem msF x = mem3 x) by (intros x; mem_chain ltac:(fun H => idtac)).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists (ms_regs msF), (ms_mem msF), 1. split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Nd; f_equal; lia|]. split; [rewrite Nt; f_equal; lia|].
split; [exact N10|]. split; [exact N12|].
split. { intros r Hr. rewrite (HK2 r Hr). apply F. cbv [LKEPT app In] in Hr |- *. clear - Hr. tauto. }
split.
+ intros x Hx. cbn [ms_mem]. rewrite MEQ1, (Hout3 x ltac:(nia)). apply MEQ0.
+ split. { cbn [ms_mem]. intros x Hx. rewrite MEQ1. apply Hgr3. rewrite MEQ0. exact Hx. }
cbn [ms_mem]. intros j k Hj Hk. replace j with 0 by lia. rewrite Z.mul_0_r, !Z.add_0_r.
transitivity (mbyte ubs2segs mem3 (pint + w * R + k)); [apply mbyte_eq_of1'; apply MEQ1|].
rewrite (Hcp3 k Hk). cbn [ms_mem]. apply mbyte_eq_of1'. apply MEQ0.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
