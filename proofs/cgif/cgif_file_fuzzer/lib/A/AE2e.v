(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AE2l AF0m AB1w AF0x AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE04 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IC_ENTRY : Z := 0x41958.
Definition IC_REAL : Z := 0x92ee4.
Definition IC_RET : Z := 0x46900.
Definition IC_FRAME : Z := 96.
Definition IC_STK : Z := 272.
Definition A_META_PTR : Z := 0xa5840.
Definition A_META_MEM : Z := 0xa5848.
Definition ic_cells : list (Z * Z * list (Z * N * Z)) :=
[ (0x9fd60, 16, [(0, 8%N, 0x9310c); (8, 8%N, 0x92ee4)]);
(A_META_PTR, 8, [(0, 8%N, A_META_MEM)]);
(0x103a0, 8, [(0, 8%N, 0xafffff00000fffff)]) ].
Definition stkC : YP09.region := YP09.mkRegion (Some 2%nat) (- IC_STK) 0 (- IC_STK) 0 [].
Definition imgC : YP09.region := YP09.mkRegion None 0x103c0 0x10428 0x103c0 0x103c0 [YP09.mkChunk 0x103c0 (CImg (0x10428 - 0x103c0))].
Definition mmC : YP09.region := YP09.mkRegion None A_META_MEM (A_META_MEM + 8) A_META_MEM A_META_MEM [YP09.mkChunk A_META_MEM (CVal 8 (SOff 32 0))].
Definition factsC : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 4096 (2^47) 4); (32%nat, mkAF 4096 (2^47) 12); (33%nat, mkAF 4096 (2^47) 3)].
Definition memC : smem := [stkC; bucketR 33; mmC; imgC] ++ map ro_region (icpt_rodata ++ ic_cells).
Definition ssC : sstate := mkSS IC_ENTRY sr_atoms memC None (mkFacts factsC [] [(hashS4 32 10, SOff 33 0)]).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_ff FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ff FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition eC : sstate := Eval vm_compute in fst (RUNTO IC_REAL ssC).
Lemma r_C : RUNTO IC_REAL ssC = (eC, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (n : N) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n' e => N.eqb n' n && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
match nth_error (ss_mem ss) i with Some r => existsb (chunk_is off n v) (YP09.r_chunks r) | None => false end.
Definition SAVEDC : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40)].
Definition KEPTC : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeC (ss : sstate) : bool :=
(ss_pc ss =? IC_REAL) &&
reg_is ss 10 (SOff 10 0) && reg_is ss 1 (SLit IC_RET) && reg_is ss 2 (SOff 2 (- IC_FRAME)) && reg_is ss 8 (SOff 10 0) && reg_is ss 19 (SLit 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTC &&
forallb (fun p => has_chunk ss 0 (snd p) 8 (SOff (Z.to_nat (fst p)) 0)) SAVEDC &&
has_chunk ss 1 0 8 (SLit 0) &&
match ss_mem ss with r0 :: r1 :: _ =>
obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - IC_STK) && (YP09.r_whi r0 =? 0) &&
obase_eqb (YP09.r_base r1) (Some 33%nat) && (YP09.r_wlo r1 =? 0) && (YP09.r_whi r1 =? 8)
| _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 2 (ss_mem ss)).
Lemma shapeC_ok : shapeC eC = true. Proof. vm_compute. reflexivity. Qed.
Definition tail_chunks : list YP09.chunk :=
[YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 (SOff 34 0));
YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 36 0))].
Definition ssT0 : sstate := mkSS IC_RET sr_atoms [YP09.mkRegion (Some 2%nat) 0 IC_FRAME 0 0 tail_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition ssT : sstate := mkSS (ss_pc ssT0) (sr_set (ss_regs ssT0) 19%bv (SLit 0)) (ss_mem ssT0) (ss_resv ssT0) (ss_facts ssT0).
Definition eT : sstate := Eval vm_compute in fst (RUN ssT).
Lemma r_T : RUN ssT = (eT, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition KEPTT : list Z := [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Definition shapeT (ss : sstate) : bool :=
(ss_pc ss =? 0x469b0) &&
reg_is ss 1 (SOff 32 0) && reg_is ss 2 (SOff 2 IC_FRAME) && reg_is ss 8 (SOff 33 0) && reg_is ss 9 (SOff 34 0) &&
reg_is ss 18 (SOff 35 0) && reg_is ss 19 (SOff 36 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTT &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (ss_mem ss).
Lemma shapeT_ok : shapeT eT = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off n v c, chunk_is off n v c = true -> c = YP09.mkChunk off (CVal n v).
Proof.
intros off n v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Definition meta_pre (H : word -> bool) (mem : word -> option byte) (M sp : Z) : Prop :=
val_mem tfibsegs (mrestrict H mem) A_META_MEM 8 M /\
(forall a, M <= a < M + AMETA_SIZE -> mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 0)) /\
TFIB_IMG_END <= M /\ M mod 4096 = 0 /\ M + AMETA_SIZE <= sp - IC_STK.
Theorem iclose_front : forall ly S (W : world tfibsegs) regs mem md f M,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + IC_STK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - IC_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 f -> 4096 <= f -> f + 16 <= 2 ^ 47 -> f mod 16 = 0 ->
cells_hold (mrestrict (w_H W) mem) ic_cells ->
ro_img (mrestrict (w_H W) mem) ->
meta_pre (w_H W) mem M (spZ regs) ->
SRr tfibsegs W (cfg_at tfibsegs IC_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs IC_REAL regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
getr regs1 10 = w64 f /\ getr regs1 1 = w64 IC_RET /\ getr regs1 2 = w64 (spZ regs - IC_FRAME) /\ getr regs1 8 = w64 f /\
getr regs1 19 = w64 0 /\
(forall r, In r KEPTC -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall j rz off, nth_error SAVEDC j = Some (rz, off) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IC_STK <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - IC_STK <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a)).
Proof.
intros ly S W regs mem md f M HAR Hal16 Hslo Hshi HpresE G10 Hf0 Hfhi Hfal HCELLS HIMG (HMM & HMZ & HMlo & HMal & HMhi).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold IC_STK, IC_FRAME in *.
assert (HIE : TFIB_IMG_END = 0x5fb000) by reflexivity. assert (HAS : AMETA_SIZE = 3727360) by reflexivity.
assert (HMP : A_META_MEM = 0xa5848) by reflexivity.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
set (b := M + 120 * ahm_idx f).
pose proof (ahm_idx_range f) as Hidx.
assert (Hb : M <= b /\ b + 120 <= M + AMETA_SIZE) by (subst b; rewrite HAS; lia).
set (EE := AE2y.Env regs [M; b]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 f) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE32 : ew EE 32 = Z_to_bv 64 M) by (exact (AE2y.Env_x regs [M; b] 0 M eq_refl)).
assert (EE33 : ew EE 33 = Z_to_bv 64 b) by (exact (AE2y.Env_x regs [M; b] 1 b eq_refl)).
assert (EE33u : bv_unsigned (ew EE 33) = b) by (rewrite EE33; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 IC_ENTRY) with (Z_to_bv 64 IC_ENTRY).
assert (HS0 : st_ok tfibsegs EE ssC (restrict H (mkst regs (Z_to_bv 64 IC_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [M; b])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memC. apply Forall_app; split.
+ apply Forall_cons.
{ unfold stkC. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 272)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia. }
apply Forall_cons.
{ apply (bucketR_ok EE _ 33 b EE33u); [lia | lia | intros a Ha; apply HMZ; lia |].
intros o Ho. apply AE2y.apresent_writable. apply (mbyte_off_apresent H mem (b + o) (Z_to_bv 8 0)); [apply off_img_high; lia | apply HMZ; lia]. }
apply Forall_cons.
{ unfold mmC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ 0 A_META_MEM 8 (SOff 32 0) M); [cbn [sv_denot]; rewrite EE32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HMM]. }
apply Forall_cons; [|apply Forall_nil].
{
pose proof (HIMG EE) as (_ & _ & _ & HCS). unfold img_ro_region, img_ro_chunks in HCS. cbn [YP09.r_chunks YP09.r_base base_val] in HCS.
do 5 (apply Forall_inv_tail in HCS). apply Forall_inv in HCS.
unfold imgC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [exact HCS | apply Forall_nil]. }
+ rewrite map_app. apply Forall_app. split.
* exact (AE2y.icpt_rodata_ok B TB ly S H mem EE (proj1 HAR)).
* exact (cells_region_ok _ EE ic_cells HCELLS).
- apply pairwise_disjoint_of_extents. unfold memC, stkC, bucketR, mmC, imgC, ic_cells, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2, EE33u.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HMP in *.
unfold IC_STK, IC_FRAME, A_META_PTR, A_META_MEM in *. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsC]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE32, EE33, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 12) with 4096. change (2 ^ 3) with 8.
assert (Hb8 : b mod 8 = 0).
{ destruct (Z.mod_divide M 4096 ltac:(lia)) as [Hd _]. destruct (Hd HMal) as [q Hq].
subst b. rewrite Hq. replace (q * 4096 + 120 * ahm_idx f) with ((512 * q + 15 * ahm_idx f) * 8) by lia. apply Z_mod_mult. }
repeat split; try lia; assumption.
+
cbn [f_alias alias_ok]. split; [|exact I].
apply bv_eq. change (U EE (hashS4 32 10) = U EE (SOff 33 0)).
rewrite (U_hashS4 EE 32 10 M f EE32 EE10) by lia. rewrite U_SOff, EE33u, Z.add_0_r. subst b. symmetry. apply zcanon_small. lia. }
eapply SRr_bind; [exact (ff_phase_to W EE IC_REAL ssC eC RS_running _ md HS0 r_C)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). apply SRr_ret. split; [reflexivity|].
assert (MEQ1 : forall z : word, ~ (sp0 - 272 <= bv_unsigned z < sp0) -> ~ (b <= bv_unsigned z < b + 8) -> ms_mem ms1 z = mem z).
{ intros z Hz1 Hz2. apply (HF1 z). intros Hin.
destruct (in_wrange_two_b EE memC (bv_unsigned z) 2 (- 272) 0 sp0 33 0 8 b ltac:(vm_compute; reflexivity) EE2 EE33u Hin); lia. }
clear HF1 HFr1.
pose proof shapeC_ok as Hsh. unfold shapeC in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HB0]. apply andb_prop in Hsh as [Hsh HSV].
apply andb_prop in Hsh as [Hsh HK']. apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R8]. apply andb_prop in Hsh as [Hsh R2].
apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hpc R10]. apply Z.eqb_eq in Hpc.
destruct (ss_mem eC) as [|r0 [|r1 rest]] eqn:Hmem; [discriminate | discriminate |].
apply andb_prop in Hwin as [Hwin W1c]. apply andb_prop in Hwin as [Hwin W1b]. apply andb_prop in Hwin as [Hwin W1a].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. apply obase_eqb_eq in W1a. apply Z.eqb_eq in W1b. apply Z.eqb_eq in W1c.
unfold IC_STK, IC_FRAME, IC_REAL in W0b, W0c, W1b, W1c, Hpc, R1, R2.
assert (RD : forall (r : bv 5) v, reg_is eC (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eC ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTC -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
set (regs1 := ms_regs ms1) in *.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (HBW : val_mem tfibsegs (mrestrict H (ms_mem ms1)) b 8 0).
{ unfold has_chunk in HB0. rewrite Hmem in HB0. cbn [nth_error] in HB0. apply existsb_exists in HB0 as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eC _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv (Forall_inv_tail Hrs)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite W1a in Hck. cbn [base_val] in Hck. rewrite EE33u in Hck.
replace b with (b + 0) at 1 by lia. apply (val_of_chunk_ok tfibsegs EE _ _ 0 8 (SLit 0) 0 Hck); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia]. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. destruct (Z_lt_le_dec a b) as [L|L]; [apply aview_same; apply MEQ1; rewrite unsigned_lit_small by lia; lia|].
destruct (Z_lt_le_dec a (b + 8)) as [L2|L2]; [| apply aview_same; apply MEQ1; rewrite unsigned_lit_small by lia; lia].
unfold aview. pose proof (HBW (Z.to_nat (a - b)) ltac:(lia)) as X1. rewrite Z2Nat.id in X1 by lia. replace (b + (a - b)) with a in X1 by lia.
rewrite X1, (HMZ a) by lia. cbn [option_map]. unfold YO0f.le_byte. rewrite Z.shiftr_0_l. reflexivity. }
assert (PRS1 : forall a, sp0 - 272 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eC ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PRSb : forall a, b <= a < b + 8 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eC ms1 1 r1 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite W1a, W1b, W1c. cbn [base_val]. rewrite EE33u. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 272)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(destruct (Z_lt_le_dec a' b) as [L4|L4]; [|destruct (Z_lt_le_dec a' (b + 8)) as [L5|L5]; [apply PRSb; lia|]]);
(apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 272)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply AE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ intros a Hband Hh. pose proof (in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
assert (NP : ~ apresent H mem a) by (intros [Hn _]; unfold H in Hn; rewrite Hh in Hn; discriminate).
destruct (Z_lt_le_dec a (sp0 - 272)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp0) as [L3|L3]; [exfalso; exact (NP (HpresE a ltac:(unfold sp0 in *; lia)))|]];
(destruct (Z_lt_le_dec a b) as [L4|L4]; [|destruct (Z_lt_le_dec a (b + 8)) as [L5|L5];
[exfalso; exact (NP (mbyte_off_apresent H mem a (Z_to_bv 8 0) (off_img_high a ltac:(lia)) (HMZ a ltac:(lia))))|]]);
(apply MEQ1; rewrite unsigned_lit_small by lia; lia). }
exists regs1, (ms_mem ms1), md1. split; [reflexivity|]. split; [exact MF1|]. split; [exact HAR1|].
split; [rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity|].
split; [rewrite (RD 1%bv (SLit IC_RET) R1); reflexivity|].
split; [rewrite (RD 2%bv (SOff 2 (- 96)) R2); cbn [sv_denot]; rewrite EE2; reflexivity|].
split; [rewrite (RD 8%bv (SOff 10 0) R8); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity|].
split; [rewrite (RD 19%bv (SLit 0) R19); reflexivity|].
split.
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTC in Hin; cbn in Hin; lia).
apply (RK (Z_to_bv 5 r) (Z.to_nat r)); [| rewrite Z2Nat.id by lia; exact Hin].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split.
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. cbn [nth_error] in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eC _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite W0a in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.
Theorem iclose_tail : forall (W : world tfibsegs) regs mem md (vra v8 v9 v18 v19 : Z),
getr regs 19 = w64 0 -> 2 ^ 43 <= spZ regs -> spZ regs + IC_FRAME <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 88) 8 vra -> val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 80) 8 v8 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 72) 8 v9 -> val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 64) 8 v18 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 56) 8 v19 ->
0 <= vra < 2 ^ 64 -> 0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 -> vra mod 2 = 0 ->
SRr tfibsegs W (cfg_at tfibsegs IC_RET regs mem md)
(fun W' c' => W' = W /\ exists regs1 md1,
c' = mkCfg (mkst regs1 (w64 vra) mem (seg_rom tfibsegs)) md1 /\ same_but_materialized md md1 /\
getr regs1 1 = w64 vra /\ getr regs1 2 = w64 (spZ regs + IC_FRAME) /\ getr regs1 8 = w64 v8 /\ getr regs1 9 = w64 v9 /\
getr regs1 18 = w64 v18 /\ getr regs1 19 = w64 v19 /\
(forall r, In r KEPTT -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))).
Proof.
intros W regs mem md vra v8 v9 v18 v19 G19 Hsplo Hsphi Hal16 C1 C8 C9 C18 C19 Rra R8 R9 R18 R19 Heven.
unfold IC_FRAME in *. set (sp0 := spZ regs) in *. set (H := w_H W) in *.
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs [vra; v8; v9; v18; v19]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EEx : forall j z, nth_error [vra; v8; v9; v18; v19] j = Some z -> ew EE (32 + j) = Z_to_bv 64 z) by (intros j z Hj; exact (AE2y.Env_x regs _ j z Hj)).
pose proof (EEx 0%nat vra eq_refl) as X32. pose proof (EEx 1%nat v8 eq_refl) as X33. pose proof (EEx 2%nat v9 eq_refl) as X34.
pose proof (EEx 3%nat v18 eq_refl) as X35. pose proof (EEx 4%nat v19 eq_refl) as X36. cbn [Nat.add] in X32, X33, X34, X35, X36.
unfold cfg_at. change (w64 IC_RET) with (Z_to_bv 64 IC_RET).
assert (HS0 : st_ok tfibsegs EE ssT (restrict H (mkst regs (Z_to_bv 64 IC_RET) mem (seg_rom tfibsegs)))).
{ unfold ssT. apply st_ok_pin_reg; [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; symmetry; exact G19].
unfold ssT0. rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [vra; v8; v9; v18; v19])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EE2. unfold IC_FRAME. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. unfold tail_chunks.
assert (CK : forall j off z, nth_error [vra; v8; v9; v18; v19] j = Some z -> 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) (sp0 + off) 8 z ->
YP09.chunk_ok tfibsegs EE (mrestrict H mem) sp0 (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off z Hj Hz Hv. eapply (chunk_ok_val tfibsegs EE _ sp0 off 8 _ z); [cbn [sv_denot]; rewrite (EEx j z Hj), Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact Hv]. }
apply Forall_cons; [exact (CK 0%nat 88 vra eq_refl Rra C1)|]. apply Forall_cons; [exact (CK 1%nat 80 v8 eq_refl R8 C8)|].
apply Forall_cons; [exact (CK 2%nat 72 v9 eq_refl R9 C9)|]. apply Forall_cons; [exact (CK 3%nat 64 v18 eq_refl R18 C18)|].
apply Forall_cons; [exact (CK 4%nat 56 v19 eq_refl R19 C19) | apply Forall_nil].
- apply pairwise_disjoint_of_extents. cbn. exact (conj I I).
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EE2. change (2 ^ 4) with 16.
repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (ff_phase W EE ssT eT _ _ md HS0 r_T)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z : word, ms_mem ms1 z = mem z).
{ intros z. apply (HF1 z). intros (r & Hin & Hr). unfold ssT in Hin. cbn [ss_mem] in Hin. destruct Hin as [<-|[]]. cbn in Hr. lia. }
pose proof shapeT_ok as Hsh. unfold shapeT in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK']. apply andb_prop in Hsh as [Hsh Q19]. apply andb_prop in Hsh as [Hsh Q18].
apply andb_prop in Hsh as [Hsh Q9]. apply andb_prop in Hsh as [Hsh Q8]. apply andb_prop in Hsh as [Hsh Q2]. apply andb_prop in Hsh as [Hpc Q1]. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eT (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eT ms1 r HS1). }
eapply (SRr_ret_at tfibsegs tbl_ff tbl_ff_ok Hwx W EE); [exact HS1 | reflexivity | rewrite Hpc; vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|].
assert (MEM : ms_mem ms1 = mem) by (apply functional_extensionality; exact MEQ1).
assert (P1 : getr (ms_regs ms1) 1 = w64 vra) by (rewrite (RD 1%bv (SOff 32 0) Q1); cbn [sv_denot]; rewrite X32, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
exists (ms_regs ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [rewrite MEM, P1, (AE2y.ret_ok_lit vra Rra Heven); reflexivity|].
split; [apply with_vm_backing_same|].
split; [exact P1|].
split; [rewrite (RD 2%bv (SOff 2 96) Q2); cbn [sv_denot]; rewrite EE2; reflexivity|].
split; [rewrite (RD 8%bv (SOff 33 0) Q8); cbn [sv_denot]; rewrite X33, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 9%bv (SOff 34 0) Q9); cbn [sv_denot]; rewrite X34, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 18%bv (SOff 35 0) Q18); cbn [sv_denot]; rewrite X35, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 19%bv (SOff 36 0) Q19); cbn [sv_denot]; rewrite X36, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTT in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK'. specialize (HK' _ Hin). cbn beta in HK'.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK'.
Qed.
End g.
End d.
