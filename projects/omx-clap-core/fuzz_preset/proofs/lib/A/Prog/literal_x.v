(* Theorem Labs, 2026-10: fuzz_preset literal (asan image A, entry pa_val A_TEXT of literal_listing): program walk against tliteral_leafX.
   #102 (A', pin 1be0f53d96cb, unstripped twin bff8519bbe3e): relocated from the old-pin walk (origin/cold/h-verbs-1-lit-bridgeb
   34b0f96319c6, pin d83eb25dbf0d) by the alreloc of record c4338d099cfb8025; it moved the three values of literal_entry_pin
   (literal, __wrap_strlen, __wrap_bcmp entries, each by symbol); everything else is cited by name from the #102 leaf listing
   (lib/A/Listing_leaves.v 34474a8ac69d, PAImg_leaves.v 9c07e1905609: same 74 slots, objects and relro shape as the old pin).
   Read-only premise (2026-10-29): tliteral_leafX at rlo := RLO, rhi := RHI (PI_literal's relro range, = PI_prog_A's
   A_prog_relro_lo / _hi); the strlen call is YGcallMxmn.aj_strlen_at_xro (ASTRLEN : YGcallMxmn.astrlen_realizes_xro),
   its arodata_okP carried from entry by lit_rod_keep (pa_segs_low and pa_relro_img of PI_literal). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_leaves PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import literal_xs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition LBx : sv := SOff 34 0.
Definition LSH : list shent := [mkSHE 10 0 16; mkSHE 13 0 4].
Definition lit_facts : list (nat * afact) :=
[ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 16) 3); (13%nat, mkAF 4096 (2 ^ 47 - 8) 3);
(34%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ].
Definition qreg : YP09.region := YP09.mkRegion (Some 10%nat) 0 16 0 8
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition vreg : YP09.region := YP09.mkRegion (Some 13%nat) 0 4 0 4 [].
Definition lit_regions : smem := [stack_region 80; got_regionP; bcell_regionP 34; qreg].
Definition ss_lit : sstate := mkSS 0 sr_atoms lit_regions None (mkFacts lit_facts [] []).
Definition lit_extra (p e : Z) : list word := map (Z_to_bv 64) [p; e; SHADOW_OFF].
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
#[local] Notation PLl := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_leaves.PL_literal.
#[local] Notation PIl := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_leaves.PI_literal.
#[local] Notation SEGS := (@pa_segs _ literal_listing PIl).
#[local] Notation VAL := (@pa_val _ literal_listing PIl).
#[local] Notation SIGMA := (@pa_sigma _ literal_listing PIl).
#[local] Notation BASE := (@pa_val _ literal_listing PIl A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ literal_listing PIl).
#[local] Notation RHI := (@pa_relro_hi _ literal_listing PIl).
(* the image bounds of the leaf's off-image premise (lib/Prog/literal_xs.v): this instance's pa_lo / pa_hi *)
#[local] Notation ILO := (@pa_lo _ literal_listing PIl).
#[local] Notation ITOP := (@pa_hi _ literal_listing PIl).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis TL : PALibCore (PI := PIl) B.
Hypothesis ASTRLEN : YGcallMxmn.astrlen_realizes_xro SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA AS___wrap_bcmp).
Let HBgot := palc_got_shadow B TL. Let HBcell := palc_cell B TL.
Lemma lit_entry : forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) q v p e,
ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
getr regs 10 = w64 q -> getr regs 13 = w64 v ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LIT_STK -> spZ regs <= sp0 ->
q mod 8 = 0 -> 4096 <= q -> amem_range q 16 -> off_img_at ILO ITOP q 16 -> (spZ regs <= q \/ q + 16 <= spZ regs - LIT_STK) ->
(forall x, q <= x < q + 8 -> apresent (w_H W) memc x) ->
val_mem SEGS (mrestrict (w_H W) memc) q 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (q + 8) 8 e ->
0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
v mod 8 = 0 -> 4096 <= v -> amem_range v 4 ->
st_ok_pi SEGS VAL (Eimg (PI := PIl) (Ereg regs (lit_extra p e))) ss_lit
(mkst regs (Z_to_bv 64 (BASE + 0)) (mrestrict (w_H W) memc) (seg_rom SEGS)).
Proof.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q v p e
HJ H10 H13 Hsp16 Hspl Hsph Hq8 Hq4k Hqapp Hqimg Hqsp Hqpr Hqp Hqe Hp64 He Hv8 Hv4k Hvapp.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as CR.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img (PAImg := PIl) 12 ltac:(lia)) as HcellR. pose proof (palc_got_cell B TL) as HgcD.
pose proof (pa_obj_img (PAImg := PIl) 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (PAImg := PIl) (A_OBJ 0)) as Hv0. pose proof (pa_val_range (PAImg := PIl) (A_OBJ 12)) as Hv12.
assert (HPL : pa_lo (PAImg := PIl) = YImgTop.IMG_LO) by reflexivity. assert (HPH : pa_hi (PAImg := PIl) = YImgTop.IMG_TOP) by reflexivity.
rewrite HPL, HPH in HcellR, HgotR, Hqimg.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold (spZ regs) in SPR.
match goal with |- st_ok_pi _ _ ?EE _ _ => set (E := EE) end. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 e) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k0 v0 Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
unfold in_app, off_img_at, kLowShadowBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP, LIT_STK, ESTACK in *.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
unfold ss_lit. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lit_regions, stack_region, got_regionP, bcell_regionP, qreg.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ change (base_val E (Some 2%nat)) with (bv_unsigned (ew E 2)). rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 LBx SHADOW_OFF);
[cbn [sv_denot LBx]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
+ rewrite (VB 10%nat q E10) by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hqpr. lia. }
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Hqp.
* apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) e); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
exact Hqe.
- apply pairwise_disjoint_of_extents. unfold lit_regions, stack_region, got_regionP, bcell_regionP, qreg, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat q E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. change (base_val E (Some 2%nat)) with (bv_unsigned (ew E 2)). rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok lit_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E13, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try lia.
+ exact I.
Qed.
Let RUN := paj_run_x (SK := SK) (PL := PLl) (PI := PIl) B PST ARx LAWS.
Let RUNTO := paj_run_to_x (SK := SK) (PL := PLl) (PI := PIl) B PST ARx LAWS.
Let BR := paj_branch (PI := PIl).
Let RET := paj_ret_at (PL := PLl) (PI := PIl).
Let RUNF := paj_run_x_fr (SK := SK) (PL := PLl) (PI := PIl) B PST ARx LAWS.
Ltac lit_awr_fr Usp Fq Hq64 Fv Hv64 Hspl Hsph Hqwr Hvwr :=
let a' := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha' := fresh "Ha" in
intros a' (r & Hin & Ha'); lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha';
try rewrite Usp in Ha'; try (rewrite Fq in Ha'; rewrite unsigned_lit_small in Ha' by exact Hq64);
try (rewrite Fv in Ha'; rewrite unsigned_lit_small in Ha' by exact Hv64);
first [ exfalso; lia | left; left; lia | left; exact (proj1 (Hqwr a' ltac:(lia))) | exact (proj1 (Hvwr a' ltac:(lia))) ] |]);
destruct Hin.
Ltac lit_awr regs sp0 q v Usp E10 E13 Hqwr Hvwr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own => let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end;
repeat first [ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn; lia|])
| (eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |])
| (eapply awr_ok_cons_gen with (k := 10%nat) (b := q); [reflexivity | rewrite E10; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; apply Hqwr; lia |])
| (eapply awr_ok_cons_gen with (k := 13%nat) (b := v); [reflexivity | rewrite E13; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; apply Hvwr; lia |]) ].
Lemma lit_q_chunk : forall E ss m q p, st_ok_pi SEGS VAL E ss m -> In qreg (ss_mem ss) ->
ew E 10 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> ew E 32 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
val_mem SEGS (ms_mem m) q 8 p.
Proof.
intros E ss m q p HS Hin Hq Hq64 Hp Hp64.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) m HS) as HM.
pose proof (lit_region_val SEGS E _ _ 10 0 16 0 8 (YP09.r_chunks qreg) 0 8%N (SOff 32 0) p HM) as V.
rewrite Hq, unsigned_lit_small, Z.add_0_r in V by lia. apply V; [exact Hin | left; reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Hp, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Ltac lit_win Usp Fq Hq64 :=
let a' := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha' := fresh "Ha" in
intros a' (r & Hin & Ha'); lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha';
try rewrite Usp in Ha'; try (rewrite Fq in Ha'; rewrite unsigned_lit_small in Ha' by exact Hq64); clear - Ha'; lia |]);
destruct Hin.
Ltac lit_win2 Usp Fq Hq64 Fv Hv64 :=
let a' := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha' := fresh "Ha" in
intros a' (r & Hin & Ha'); lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha';
try rewrite Usp in Ha'; try (rewrite Fq in Ha'; rewrite unsigned_lit_small in Ha' by exact Hq64);
try (rewrite Fv in Ha'; rewrite unsigned_lit_small in Ha' by exact Hv64); clear - Ha'; lia |]);
destruct Hin.
Ltac lit_inq := lazymatch goal with |- In _ ?l => let l' := eval vm_compute in l in change l with l' end; repeat (first [left; reflexivity | right]).
Remark literal_entry_pin : BASE = 0x87f60 /\ SIGMA AS___wrap_strlen = 0x42d18 /\ SIGMA AS___wrap_bcmp = 0x42d2c.
Proof. vm_compute. repeat split. Qed.
Theorem literal_x_holds : tliteral_leafX SK SEGS B PST ARx RLO RHI ILO ITOP 4 BASE.
Proof.
unfold tliteral_leafX.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q w ty v p text len txt cw slack
HJ Hra Hgp Htp H10 H11 H12 H13 Hsp16 Hspl Hsph Hq8 Hq4k Hqapp Hqimg Hqsp Hqwr Hqp Hqe Hqra
Htx0 Hptx Htxl Hlen Gtx Hamt Hrat Hhut Htxsp Hw0 Hcw32 Hwb Gw Hnz Hsl Hamw Hamw8 Hraw Hhuw Hwsp Hrom
Hty Hv8 Hv4k Hvapp Hvimg Hvsp Hvwr Hvra Hqv.
pose proof (pa_wx (PAImg := PIl)) as Hwx. pose proof (pa_segs_low (PAImg := PIl)) as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as CR.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold (spZ regs) in SPR.
remember (Eimg (PI := PIl) (Ereg regs (lit_extra p (text + len)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E ss_lit (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx, HE.
apply (lit_entry STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q v p (text + len));
first [assumption | lia | (intros x Hx; exact (proj2 (Hqwr x Hx)))]. }
pose proof Hqapp as Hqa'. pose proof Hvapp as Hva'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqa', Hva'.
assert (HPLq : pa_lo (PAImg := PIl) = YImgTop.IMG_LO) by reflexivity. assert (HPHq : pa_hi (PAImg := PIl) = YImgTop.IMG_TOP) by reflexivity.
unfold off_img_at in Hqimg. rewrite HPLq, HPHq in Hqimg. clear HPLq HPHq.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hqimg. unfold LIT_STK, ESTACK in *.
assert (Ho16 : id ((spZ regs - 80 - sp0) mod 16 = 0)) by (unfold id; clear - Hsp16 Hal16; Z.div_mod_to_equations; lia).
assert (Hq64 : 0 <= q < 2 ^ 64) by lia. assert (Hv64 : 0 <= v < 2 ^ 64) by lia.
clear Hsp16 Hal16 Hq8 Hv8 CR.
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 ty) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (lit_extra p (text + len))) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (HBx : U E LBx = SHADOW_OFF) by (unfold LBx; rewrite (U_atom E 34 SHADOW_OFF E34) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS LBx LSH E (mrestrict (w_H W) memc)).
{ constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) memc E LBx 10 q 16 q 0 16 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) memc E LBx 13 v 4 v 0 4 Hvra HBx); [rewrite (U_atom E 13 v E13) by lia; reflexivity | lia | lia |].
intros x Hx. unfold SHADOW_OFF in *. lia. }
unfold cfg_at. change (w64 BASE) with (Z_to_bv 64 (BASE + 0)).
paj_run_tok_x RUN HS HJ SHOK BAND_SPAN.
{ unfold ss_lit, lit_regions. cbn [ss_mem].
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
apply awr_ok_cons_ro; [cbn; lia|].
apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen with (k := 10%nat) (b := q); [reflexivity | rewrite E10; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi qreg]. intros a Ha. apply (Hqwr a). lia. }
assert (Hamw' : w + Z.of_nat (length cw) + 1 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamw; lia).
assert (Hamt' : text + len <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt; lia).
assert (Hlo46 : SHADOW_OFF + 2 ^ 44 + 8 <= spZ regs - 8272) by (unfold SHADOW_OFF; lia).
pose proof (st_ok_mem_ok SEGS E _ _ HS) as HM1. cbn [ms_mem restrict ss_mem setpc] in HM1.
assert (Q1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 p).
{ pose proof (lit_region_val SEGS E _ _ 10 0 16 0 8 (YP09.r_chunks qreg) 0 8%N (SOff 32 0) p HM1) as V.
rewrite E10, unsigned_lit_small, Z.add_0_r in V by lia. apply V; [repeat (first [left; reflexivity | right]) | left; reflexivity | cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
assert (KF1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ apply (lit_aview_frame SEGS (w_H W) E (ss_mem ss_lit) memc (ms_mem ms) _ HFr).
intros a' (r & Hin & Ha'). unfold ss_lit, lit_regions in Hin. cbn [ss_mem] in Hin.
repeat destruct Hin as [<- | Hin]; try destruct Hin;
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi stack_region got_regionP bcell_regionP qreg] in Ha'.
- rewrite Usp in Ha'. lia. - lia. - lia. - rewrite E10, unsigned_lit_small in Ha' by lia. lia. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb. destruct (Z.le_gt_cases q a); [destruct (Z.lt_ge_cases a (q + 8))|].
- exact (lit_aview_of_val SEGS (w_H W) memc (ms_mem ms) q 8 p Hqp Q1 a ltac:(lia)).
- apply KF1; lia.
- apply KF1; lia. }
assert (Gw1 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) w (cw ++ 0 :: slack)).
{ apply (lit_garr8_keep SEGS (w_H W) memc (ms_mem ms) (spZ regs - 8272) (spZ regs) w _ K1); [lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact Gw]. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_strlen_at_xro (SK := SK) SEGS B PST ARx RLO RHI LAWS Hsegs (SIGMA AS___wrap_strlen) ASTRLEN W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc _ k w (Z.of_nat (length cw)) (spZ regs - 80 - sp0) (Z_to_bv 64 (BASE + 80)) HJ).
- rewrite Ra0, E11. reflexivity.
- exact Hw0. - lia. - exact Hcw32. - lia.
- unfold spZ at 1. rewrite Rsp, Usp, unsigned_lit_small by lia. lia.
- exact Ho16. - lia. - unfold ESTACK. lia.
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- exact (lit_first_byte SEGS W (ms_mem ms) w cw slack Gw1 Hnz).
- intros a Ha. split; [apply (lit_garr8_vis SEGS (w_H W) (ms_mem ms) w _ a Gw1); rewrite length_app; cbn [length]; lia|].
unfold spZ at 1 2. rewrite Rsp, Usp, unsigned_lit_small by lia. unfold ESTACK. lia.
- intros a Ha. unfold ESTACK. lia.
- exact Hamw8.
- apply (lit_ra_keep SEGS (w_H W) memc (ms_mem ms) (spZ regs - 8272) (spZ regs) w _ K1); [lia | lia | lia | exact Hraw].
- apply (lit_hull_keep SEGS (w_H W) memc (ms_mem ms) (spZ regs - 8272) (spZ regs) w _ K1); [lia | lia | lia | lia | exact Hhuw].
- exact (lit_overread SEGS (w_H W) (ms_mem ms) w cw slack Gw1 Hsl).
- apply (lit_rod_keep SEGS W memc (ms_mem ms) (spZ regs - 8272) (spZ regs) RLO RHI B K1 Hsegs (pa_relro_img (PAImg := PIl))); [unfold kLowMemEnd, SHADOW_OFF in *; lia | exact Hrom]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ra0' & Hfr2 & Hpres2). clear Hsl.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb. rewrite Hfr2 by (unfold ESTACK; lia). apply K1; lia. }
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
assert (E241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (E253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (pa_obj_img (PAImg := PIl) 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img (PAImg := PIl) 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (PAImg := PIl) (A_OBJ 0)) as Hv0. pose proof (pa_val_range (PAImg := PIl) (A_OBJ 12)) as Hv12.
assert (HPL : pa_lo (PAImg := PIl) = YImgTop.IMG_LO) by reflexivity. assert (HPH : pa_hi (PAImg := PIl) = YImgTop.IMG_TOP) by reflexivity.
rewrite HPL, HPH in HcellR, HgotR. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2s & _).
assert (Hqp1 : forall x, q <= x < q + 8 -> apresent (w_H W) (ms_mem ms) x).
{ intros x Hx. eapply apresent_grows; [exact HG | exact (proj2 (Hqwr x Hx))]. }
assert (Hvp1 : forall x, v <= x < v + 4 -> apresent (w_H W) (ms_mem ms) x).
{ intros x Hx. eapply apresent_grows; [exact HG | exact (proj2 (Hvwr x Hx))]. }
match type of HS2 with ?P -> _ => assert (HQK : P) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; apply lit_region_kept; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
- rewrite Usp. intros a Ha. apply Hfr2; [lia | unfold ESTACK; lia].
- rewrite Usp. intros a Ha. apply Hpres2s. lia.
- rewrite (E241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0)). intros a Ha. apply Hfr2; [lia | unfold ESTACK; lia].
- intros a Ha. lia.
- rewrite (E253 : bv_unsigned (ew E 253) = VAL (A_OBJ 12)). intros a Ha. apply Hfr2; [lia | unfold ESTACK; lia].
- intros a Ha. lia.
- rewrite E10, unsigned_lit_small by lia. intros a Ha. apply Hfr2; [lia | unfold ESTACK; lia].
- rewrite E10, unsigned_lit_small by lia. intros a Ha. apply Hpres2. apply Hqp1. lia. }
specialize (HS2 HQK). clear HS HQK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 _) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 40)%nat -> ew Ea n = ew E n) by (intros n0 Hn0; rewrite HEa; apply ew_havoc_old; exact Hn0).
assert (F44 : ew Ea 44 = getr regs2 10) by (rewrite HEa; reflexivity).
assert (HAEa : env_agree 32 (Ereg regs (lit_extra p (text + len))) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HEa.
assert (HBxa : U Ea LBx = SHADOW_OFF) by (unfold LBx; rewrite (U_atom Ea 34 SHADOW_OFF) by (try (rewrite OLDa by lia; exact E34); unfold SHADOW_OFF; lia); reflexivity).
assert (SHOKa : sh_ok SEGS LBx LSH Ea (mrestrict (w_H W) mem2)).
{ constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) mem2 Ea LBx 10 q 16 q 0 16); [| exact HBxa | rewrite (U_atom Ea 10 q) by (try (rewrite OLDa by lia; exact E10); lia); reflexivity | lia | lia |].
+ apply (lit_ra_keep SEGS (w_H W) memc mem2 (spZ regs - 8272) (spZ regs) q 16 K2); [lia | lia | lia | exact Hqra].
+ intros x Hx. unfold kHighMemBeg, SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem2 Ea LBx 13 v 4 v 0 4); [| exact HBxa | rewrite (U_atom Ea 13 v) by (try (rewrite OLDa by lia; exact E13); lia); reflexivity | lia | lia |].
+ apply (lit_ra_keep SEGS (w_H W) memc mem2 (spZ regs - 8272) (spZ regs) v 4 K2); [lia | lia | lia | exact Hvra].
+ intros x Hx. unfold kHighMemBeg, SHADOW_OFF in *. lia. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
assert (Fa10 : ew Ea 10 = Z_to_bv 64 q) by (rewrite OLDa by lia; exact E10).
clear HF HFr HG.
assert (Fa13 : ew Ea 13 = Z_to_bv 64 v) by (rewrite OLDa by lia; exact E13).
paj_run_tok_x RUN HS HJ2 SHOKa BAND_SPAN.
{ lit_awr regs sp0 q v Uspa Fa10 Fa13 Hqwr Hvwr. }
match goal with |- SRr _ _ {| cfg_ms := ?m |} _ => rename m into msb end.
assert (F32 : ew Ea 32 = Z_to_bv 64 p) by (rewrite OLDa by lia; exact E32).
assert (F33 : ew Ea 33 = Z_to_bv 64 (text + len)) by (rewrite OLDa by lia; exact E33).
assert (F44' : ew Ea 44 = Z_to_bv 64 (Z.of_nat (length cw))) by (rewrite F44, Ra0'; reflexivity).
psrr_branch_tok RUN BR HS SHOKa BAND_SPAN.
- assert (Hlt : text + len - p < Z.of_nat (length cw)).
{ rewrite branch_ltu_U, (lit_U_sub Ea 32 33 p (text + len) F32 F33) in Hc by lia.
rewrite (U_atom Ea 44 (Z.of_nat (length cw)) F44') in Hc by lia. apply Z.ltb_lt in Hc. exact Hc. }
rename HFr into HFr2. clear HF HG.
paj_run_tok_x RUN HS HJ2 SHOKa BAND_SPAN.
{ lit_awr regs sp0 q v Uspa Fa10 Fa13 Hqwr Hvwr. }
match goal with |- SRr _ _ {| cfg_ms := ?m |} _ => rename m into msF end.
rename HFr into HFr3.
pose proof (lit_q_chunk Ea _ _ q p HS ltac:(lit_inq) Fa10 ltac:(lia) F32 ltac:(lia)) as QF. cbn [ms_mem restrict] in QF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb. destruct (Z.le_gt_cases q a); [destruct (Z.lt_ge_cases a (q + 8))|].
- exact (lit_aview_of_val SEGS (w_H W) memc (ms_mem msF) q 8 p Hqp QF a ltac:(lia)).
- rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr3) by (first [lit_win Uspa Fa10 Hq64 | lia]).
rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr2) by (first [lit_win Uspa Fa10 Hq64 | lia]).
apply K2; lia.
- rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr3) by (first [lit_win Uspa Fa10 Hq64 | lia]).
rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr2) by (first [lit_win Uspa Fa10 Hq64 | lia]).
apply K2; lia. }
prreg HS (1%bv : bv 5) RraF. prreg HS (10%bv : bv 5) R10F.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
unfold tliteral_leaf_postX. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split.
{ rewrite RraF, OLDa, E1 by lia. pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'. rewrite Hra'. reflexivity. }
split; [eapply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (lit_extra p (text + len)) HS); [exact HAEa | vm_compute; reflexivity]|].
split; [intros a Ha Hb _ _; apply KF; [exact Ha | unfold LIT_STK, ESTACK in Hb; lia]|].
right. split; [apply lit_prefixb_short; rewrite length_skipn; lia|].
split; [rewrite R10F; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
intros a Ha Hb. apply KF; [exact Ha | unfold LIT_STK, ESTACK in Hb; lia].
- assert (Hge : Z.of_nat (length cw) <= text + len - p).
{ rewrite branch_ltu_U, (lit_U_sub Ea 32 33 p (text + len) F32 F33) in Hc by lia.
rewrite (U_atom Ea 44 (Z.of_nat (length cw)) F44') in Hc by lia. apply Z.ltb_ge in Hc. exact Hc. }
rename HFr into HFr2.
assert (Hqpb : forall x, q <= x < q + 8 -> apresent (w_H W) (ms_mem msb) x).
{ intros x Hx. eapply apresent_grows; [exact HG | apply Hpres2, Hqp1; lia]. }
assert (Hvpb : forall x, v <= x < v + 4 -> apresent (w_H W) (ms_mem msb) x).
{ intros x Hx. eapply apresent_grows; [exact HG | apply Hpres2, Hvp1; lia]. }
clear HF HG.
paj_run_tok_x RUN HS HJ2 SHOKa BAND_SPAN.
{ lit_awr regs sp0 q v Uspa Fa10 Fa13 Hqwr Hvwr. }
match goal with |- SRr _ _ {| cfg_ms := ?m |} _ => rename m into msc end.
rename HFr into HFr3.
assert (Hqpc : forall x, q <= x < q + 8 -> apresent (w_H W) (ms_mem msc) x).
{ intros x Hx. eapply apresent_grows; [exact HG | apply Hqpb; lia]. }
assert (Hvpc : forall x, v <= x < v + 4 -> apresent (w_H W) (ms_mem msc) x).
{ intros x Hx. eapply apresent_grows; [exact HG | apply Hvpb; lia]. }
clear HF HG.
pose proof (st_ok_mem_ok SEGS Ea _ _ HS) as HMc. cbn [ms_mem restrict ss_mem setpc] in HMc.
assert (Qc : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) q 8 p).
{ pose proof (lit_region_val SEGS Ea _ _ 10 0 16 0 8 (YP09.r_chunks qreg) 0 8%N (SOff 32 0) p HMc) as V.
rewrite Fa10, unsigned_lit_small, Z.add_0_r in V by lia. apply V; [lit_inq | left; reflexivity | cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
clear HMc.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb. destruct (Z.le_gt_cases q a); [destruct (Z.lt_ge_cases a (q + 8))|].
- exact (lit_aview_of_val SEGS (w_H W) memc (ms_mem msc) q 8 p Hqp Qc a ltac:(lia)).
- rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr3) by (first [lit_win Uspa Fa10 Hq64 | lia]).
rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr2) by (first [lit_win Uspa Fa10 Hq64 | lia]).
apply K2; lia.
- rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr3) by (first [lit_win Uspa Fa10 Hq64 | lia]).
rewrite (lit_aview_frame SEGS (w_H W) Ea _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr2) by (first [lit_win Uspa Fa10 Hq64 | lia]).
apply K2; lia. }
assert (Gt3 : garr8 SEGS (mrestrict (w_H W) (ms_mem msc)) text txt).
{ apply (lit_garr8_keep SEGS (w_H W) memc (ms_mem msc) (spZ regs - 8272) (spZ regs) text txt K3); [lia | lia | lia | exact Gtx]. }
assert (Gw3 : garr8 SEGS (mrestrict (w_H W) (ms_mem msc)) w (cw ++ 0 :: slack)).
{ apply (lit_garr8_keep SEGS (w_H W) memc (ms_mem msc) (spZ regs - 8272) (spZ regs) w _ K3); [lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact Gw]. }
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2. prreg HS (1%bv : bv 5) Rbra.
prreg HS (2%bv : bv 5) Rbsp. prreg HS (3%bv : bv 5) Rbgp. prreg HS (4%bv : bv 5) Rbtp.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_bcmp_at_x (SK := SK) SEGS B PST ARx LAWS Hsegs (SIGMA AS___wrap_bcmp) ABCMP W (ms_regs msc) (ms_mem msc) STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc _ k p w (Z.of_nat (length cw)) (spZ regs - 80 - sp0) (Z_to_bv 64 (BASE + 156)) HJ2).
- rewrite Rb0, F32. reflexivity.
- rewrite Rb1, OLDa, E11 by lia. reflexivity.
- rewrite Rb2, F44'. reflexivity.
- lia. - lia. - lia. - lia. - lia.
- unfold spZ at 1. rewrite Rbsp, Uspa, unsigned_lit_small by lia. lia.
- exact Ho16. - lia. - unfold ESTACK. lia.
- rewrite Rbgp, OLDa, E3 by lia. exact Hgp.
- rewrite Rbtp, OLDa, E4 by lia. exact Htp.
- exact Rbra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply (lit_garr8_vis SEGS (w_H W) (ms_mem msc) text txt a Gt3); lia|].
unfold spZ at 1 2. rewrite Rbsp, Uspa, unsigned_lit_small by lia. unfold ESTACK. lia.
- intros a Ha. split; [apply (lit_garr8_vis SEGS (w_H W) (ms_mem msc) w _ a Gw3); rewrite length_app; cbn [length]; lia|].
unfold spZ at 1 2. rewrite Rbsp, Uspa, unsigned_lit_small by lia. unfold ESTACK. lia.
- intros a Ha. unfold ESTACK. lia.
- intros a Ha. unfold ESTACK. lia.
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
- apply (range_addressable_sub _ _ text len); [apply (lit_ra_keep SEGS (w_H W) memc (ms_mem msc) (spZ regs - 8272) (spZ regs) text len K3); [lia | lia | lia | exact Hrat] | lia | lia].
- intros Hn0. apply (lit_hull_sub _ text len); [apply (lit_hull_keep SEGS (w_H W) memc (ms_mem msc) (spZ regs - 8272) (spZ regs) text len K3); [lia | lia | lia | lia | apply Hhut; lia] | lia | lia | lia | lia].
- apply (range_addressable_sub _ _ w (Z.of_nat (length cw) + 1)); [apply (lit_ra_keep SEGS (w_H W) memc (ms_mem msc) (spZ regs - 8272) (spZ regs) w _ K3); [lia | lia | lia | exact Hraw] | lia | lia].
- intros Hn0. apply (lit_hull_sub _ w (Z.of_nat (length cw) + 1)); [apply (lit_hull_keep SEGS (w_H W) memc (ms_mem msc) (spZ regs - 8272) (spZ regs) w _ K3); [lia | lia | lia | lia | exact Hhuw] | lia | lia | lia | lia]. }
cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & vv & -> & HJ4 & HP4 & Ra04 & Hcmp & Hfr4 & Hpres4).
pose proof (lit_cmp_prefix SEGS (w_H W) (ms_mem msc) text txt w cw slack p Gt3 Gw3 ltac:(lia) ltac:(lia)) as Hpfx.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb. rewrite Hfr4 by (unfold ESTACK; lia). apply K3; lia. }
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4s & _).
jafter_call_keep_pi HS 60%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2; 3]%nat HS4.
match type of HS4 with ?P -> _ => assert (HQK : P) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; apply lit_region_kept; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
- rewrite Uspa. intros a Ha. apply Hfr4; [lia | unfold ESTACK; lia].
- rewrite Uspa. intros a Ha. apply Hpres4s. lia.
- rewrite (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia) : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)). intros a Ha. apply Hfr4; [lia | unfold ESTACK; lia].
- intros a Ha. lia.
- rewrite (HEIa (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia) : bv_unsigned (ew Ea 253) = VAL (A_OBJ 12)). intros a Ha. apply Hfr4; [lia | unfold ESTACK; lia].
- intros a Ha. lia.
- rewrite Fa10, unsigned_lit_small by lia. intros a Ha. apply Hfr4; [lia | unfold ESTACK; lia].
- rewrite Fa10, unsigned_lit_small by lia. intros a Ha. apply Hpres4. apply Hqpc. lia. }
specialize (HS4 HQK). clear HS HQK. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc Ea 60 _) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 60)%nat -> ew Eb n = ew Ea n) by (intros n0 Hn0; rewrite HEb; apply ew_havoc_old; exact Hn0).
assert (F64 : ew Eb 64 = vv) by (rewrite HEb; exact Ra04).
assert (HAEb : env_agree 32 (Ereg regs (lit_extra p (text + len))) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [lia | exact HAEa]).
clear HEb.
assert (HBxb : U Eb LBx = SHADOW_OFF) by (unfold LBx; rewrite (U_atom Eb 34 SHADOW_OFF) by (try (rewrite OLDb, OLDa by lia; exact E34); unfold SHADOW_OFF; lia); reflexivity).
assert (Fb10 : ew Eb 10 = Z_to_bv 64 q) by (rewrite OLDb by lia; exact Fa10).
assert (Fb13 : ew Eb 13 = Z_to_bv 64 v) by (rewrite OLDb by lia; exact Fa13).
assert (Fb32 : ew Eb 32 = Z_to_bv 64 p) by (rewrite OLDb by lia; exact F32).
assert (Fb44 : ew Eb 44 = Z_to_bv 64 (Z.of_nat (length cw))) by (rewrite OLDb by lia; exact F44').
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Uspa).
assert (SHOKb : sh_ok SEGS LBx LSH Eb (mrestrict (w_H W) mem4)).
{ constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) mem4 Eb LBx 10 q 16 q 0 16); [| exact HBxb | rewrite (U_atom Eb 10 q) by (try exact Fb10; lia); reflexivity | lia | lia |].
+ apply (lit_ra_keep SEGS (w_H W) memc mem4 (spZ regs - 8272) (spZ regs) q 16 K4); [lia | lia | lia | exact Hqra].
+ intros x Hx. unfold kHighMemBeg, SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem4 Eb LBx 13 v 4 v 0 4); [| exact HBxb | rewrite (U_atom Eb 13 v) by (try exact Fb13; lia); reflexivity | lia | lia |].
+ apply (lit_ra_keep SEGS (w_H W) memc mem4 (spZ regs - 8272) (spZ regs) v 4 K4); [lia | lia | lia | exact Hvra].
+ intros x Hx. unfold kHighMemBeg, SHADOW_OFF in *. lia. }
clear Hc.
psrr_branch_tok RUN BR HS SHOKb BAND_SPAN.
+ assert (Hvv : vv <> Z_to_bv 64 0).
{ intros Hz. rewrite branch_ne_U, U_SLit, U_SOff, F64, Hz in Hc. vm_compute in Hc. discriminate. }
assert (Hnp : PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = false).
{ apply Bool.not_true_is_false. intros Ep. apply Hvv. exact (proj2 Hcmp (proj2 Hpfx Ep)). }
paj_run_tok_x RUN HS HJ4 SHOKb BAND_SPAN.
{ lit_awr regs sp0 q v Uspb Fb10 Fb13 Hqwr Hvwr. }
match goal with |- SRr _ _ {| cfg_ms := ?m |} _ => rename m into msF end.
rename HFr into HFr5.
pose proof (lit_q_chunk Eb _ _ q p HS ltac:(lit_inq) Fb10 ltac:(lia) Fb32 ltac:(lia)) as QF. cbn [ms_mem restrict] in QF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb. destruct (Z.le_gt_cases q a); [destruct (Z.lt_ge_cases a (q + 8))|].
- exact (lit_aview_of_val SEGS (w_H W) memc (ms_mem msF) q 8 p Hqp QF a ltac:(lia)).
- rewrite (lit_aview_frame SEGS (w_H W) Eb _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr5) by (first [lit_win Uspb Fb10 Hq64 | lia]).
apply K4; lia.
- rewrite (lit_aview_frame SEGS (w_H W) Eb _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8)) HFr5) by (first [lit_win Uspb Fb10 Hq64 | lia]).
apply K4; lia. }
prreg HS (1%bv : bv 5) RraF. prreg HS (10%bv : bv 5) R10F.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
unfold tliteral_leaf_postX. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split.
{ rewrite RraF, OLDb, OLDa, E1 by lia. pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'. rewrite Hra'. reflexivity. }
split; [eapply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ4|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (lit_extra p (text + len)) HS); [exact HAEb | vm_compute; reflexivity]|].
split; [intros a Ha Hb _ _; apply KF; [exact Ha | unfold LIT_STK, ESTACK in Hb; lia]|].
right. split; [exact Hnp|].
split; [rewrite R10F; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
intros a Ha Hb. apply KF; [exact Ha | unfold LIT_STK, ESTACK in Hb; lia].
+ assert (Hvv : vv = Z_to_bv 64 0).
{ rewrite branch_ne_U, U_SLit, U_SOff, F64 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
pose proof (bv_unsigned_in_range 64 vv) as R. unfold bv_modulus in R. cbn in R.
change (zcanon 0) with 0 in Hc. unfold zcanon, M64 in Hc. rewrite Z.add_0_r, Z.mod_small in Hc by lia.
apply bv_eq. rewrite Hc. reflexivity. }
assert (Hpt : PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = true) by (apply Hpfx, Hcmp; exact Hvv).
assert (Hvp4 : forall x, v <= x < v + 4 -> apresent (w_H W) mem4 x) by (intros x Hx; apply Hpres4, Hvpc; lia).
assert (Dg : v + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v).
{ apply (lit_apart _ v 4 (VAL (A_OBJ 0)) 8 Hvimg); [| lia | lia].
  apply lit_in_img_rng. vm_compute. reflexivity. }
assert (Dc : v + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v).
{ apply (lit_apart _ v 4 (VAL (A_OBJ 12)) 8 Hvimg); [| lia | lia].
  apply lit_in_img_rng. vm_compute. reflexivity. }
eapply st_ok_pi_add_region with (r := vreg) in HS; [ | vm_compute; reflexivity | | ].
2: { unfold region_ok. cbn [ms_mem restrict vreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val Eb (Some 13%nat)) with (bv_unsigned (ew Eb 13)). rewrite Fb13, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hvp4. lia. }
2: { apply all_disjoint_of_extents.
lazymatch goal with |- zall_disjoint _ (map _ ?rs) => let rs' := eval vm_compute in rs in change rs with rs' end.
unfold extent_of_region. cbn [map vreg YP09.r_base YP09.r_lo YP09.r_hi].
change (base_val Eb (Some 13%nat)) with (bv_unsigned (ew Eb 13)). change (base_val Eb (Some 10%nat)) with (bv_unsigned (ew Eb 10)).
change (base_val Eb (Some 2%nat)) with (bv_unsigned (ew Eb 2)).
change (base_val Eb (Some 241%nat)) with (bv_unsigned (ew Eb 241)). change (base_val Eb (Some 253%nat)) with (bv_unsigned (ew Eb 253)).
rewrite (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia) : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)).
rewrite (HEIb (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia) : bv_unsigned (ew Eb 253) = VAL (A_OBJ 12)).
rewrite Fb13, Fb10, Uspb, !unsigned_lit_small by lia.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
paj_run_tok_x RUNF HS HJ4 SHOKb BAND_SPAN.
{ lit_awr_fr Uspb Fb10 Hq64 Fb13 Hv64 Hspl Hsph Hqwr Hvwr. }
match goal with |- SRr _ _ {| cfg_ms := ?m |} _ => rename m into msH end.
rename HFr into HFh1.
lazymatch type of HS with st_ok_pi _ _ ?EE _ _ => set (Ec := EE) in HS end.
assert (OLDc : forall n, (n < 512)%nat -> ew Ec n = ew Eb n) by (intros n0 Hn0; unfold Ec; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (HAEc : env_agree 32 (Ereg regs (lit_extra p (text + len))) Ec).
{ split; [intros n0 Hn0; rewrite OLDc by lia; exact (proj1 HAEb n0 Hn0) | unfold Ec; repeat rewrite ed_ewset; exact (proj2 HAEb)]. }
assert (Fc10 : ew Ec 10 = Z_to_bv 64 q) by (rewrite OLDc by lia; exact Fb10).
assert (Fc12 : ew Ec 12 = Z_to_bv 64 ty) by (rewrite OLDc, OLDb, OLDa by lia; exact E12).
assert (Fc13 : ew Ec 13 = Z_to_bv 64 v) by (rewrite OLDc by lia; exact Fb13).
assert (Fc32 : ew Ec 32 = Z_to_bv 64 p) by (rewrite OLDc by lia; exact Fb32).
assert (Fc44 : ew Ec 44 = Z_to_bv 64 (Z.of_nat (length cw))) by (rewrite OLDc by lia; exact Fb44).
pose proof (st_ok_mem_ok SEGS Ec _ _ HS) as HMh. cbn [ms_mem restrict ss_mem setpc] in HMh.
assert (QH : val_mem SEGS (mrestrict (w_H W) (ms_mem msH)) q 8 (p + Z.of_nat (length cw))).
{ pose proof (lit_region_val SEGS Ec _ _ 10 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SAlu ALU_ADD (SOff 32 0) (SOff 44 0))); YP09.mkChunk 8 (CVal 8 (SOff 33 0))]
0 8%N (SAlu ALU_ADD (SOff 32 0) (SOff 44 0)) (p + Z.of_nat (length cw)) HMh) as V.
rewrite Fc10, unsigned_lit_small, Z.add_0_r in V by lia. apply V; [lit_inq | lit_inq | | cbn; lia | cbn; lia].
rewrite denot_lit_U, U_SAlu, (U_atom Ec 32 p Fc32), (U_atom Ec 44 _ Fc44) by lia. cbn [zalu_raw].
rewrite zcanon_id by (unfold M64; lia). reflexivity. }
assert (QV : val_mem SEGS (mrestrict (w_H W) (ms_mem msH)) v 4 ty).
{ pose proof (lit_region_val SEGS Ec _ _ 13 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 12 0))] 0 4%N (SOff 12 0) ty HMh) as V.
rewrite Fc13, unsigned_lit_small, Z.add_0_r in V by lia. apply V; [lit_inq | lit_inq | | cbn; lia | cbn; lia].
rewrite denot_lit_U, (U_atom Ec 12 ty Fc12) by lia. reflexivity. }
clear HMh.
assert (KH : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> ~ (q <= a < q + 8) -> ~ (v <= a < v + 4) ->
aview SEGS (w_H W) (ms_mem msH) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hb Hq' Hv'.
rewrite (lit_aview_frame SEGS (w_H W) Eb _ _ _ (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (v <= a < v + 4)) HFh1) by (first [lit_win2 Uspb Fb10 Hq64 Fb13 Hv64 | lia]).
apply K4; lia. }
prreg HS (1%bv : bv 5) RraH. prreg HS (10%bv : bv 5) R10H.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
unfold tliteral_leaf_postX. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split.
{ rewrite RraH, OLDc, OLDb, OLDa, E1 by lia. pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'. rewrite Hra'. reflexivity. }
split; [eapply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ4|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (lit_extra p (text + len)) HS); [exact HAEc | vm_compute; reflexivity]|].
split; [intros a Ha Hb Hq' Hv'; apply KH; [exact Ha | unfold LIT_STK, ESTACK in Hb; lia | exact Hq' | exact Hv']|].
left. split; [exact Hpt|].
split; [rewrite R10H; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
split; [exact QH | exact QV].
Qed.
End a.
