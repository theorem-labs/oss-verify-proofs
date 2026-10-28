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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2h AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IO_RET : Z := 0x463f4.
Definition IO_WIN : Z := 2160.
Definition IO_FRAME : Z := 2144.
Definition SH_PATH : Z := Eval vm_compute in (FF_SB + A_PATH / 8).
Definition SH_WB : Z := Eval vm_compute in (FF_SB + A_WB / 8).
Definition SH_WB0 : Z := Eval vm_compute in (SH_WB / 8 * 8).
Definition io_cells : list (Z * Z * list (Z * N * Z)) :=
[ (FF_got_fopen, 8, [(0, 8%N, FF_real_fopen)]);
(FF_got_cflags, 8, [(0, 8%N, FF_cflags)]);
(SH_PATH, 8, [(0, 8%N, 0xf9f90500)]);
(SH_WB0, 8, [(0, 8%N, 0xf9f9f90300000000)]);
(A_PATH, 16, [(0, 8%N, 0x74756f2f706d742f); (8, 4%N, 0x6669672e); (12, 1%N, 0)]);
(A_WB, 8, [(0, 8%N, 0x6277)]) ].
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_ff FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ff FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (n : N) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n' e => N.eqb n' n && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
match nth_error (ss_mem ss) i with Some r => existsb (chunk_is off n v) (YP09.r_chunks r) | None => false end.
Definition stkF : YP09.region := YP09.mkRegion (Some 2%nat) (- IO_WIN) 0 (- IO_WIN) 0 [].
Definition memF : smem := stkF :: map ro_region (icpt_rodata ++ io_cells).
Definition ssF0 : sstate := mkSS FF_pc_wrap_fopen sr_atoms memF None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition ssF1 : sstate := mkSS (ss_pc ssF0) (sr_set (ss_regs ssF0) 10%bv (SLit A_PATH)) (ss_mem ssF0) (ss_resv ssF0) (ss_facts ssF0).
Definition ssF : sstate := mkSS (ss_pc ssF1) (sr_set (ss_regs ssF1) 11%bv (SLit A_WB)) (ss_mem ssF1) (ss_resv ssF1) (ss_facts ssF1).
Definition eF : sstate := Eval vm_compute in fst (RUNTO FF_real_fopen ssF).
Lemma r_F : RUNTO FF_real_fopen ssF = (eF, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition SAVEDF : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64)].
Definition KEPTF : list Z := [3; 4; 23; 24; 25; 26; 27].
Definition shapeF (ss : sstate) : bool :=
(ss_pc ss =? FF_real_fopen) &&
reg_is ss 10 (SLit A_PATH) && reg_is ss 11 (SLit A_WB) && reg_is ss 1 (SLit IO_RET) && reg_is ss 2 (SOff 2 (- IO_FRAME)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTF &&
forallb (fun p => has_chunk ss 0 (snd p) 8 (SOff (Z.to_nat (fst p)) 0)) SAVEDF &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - IO_WIN) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
Lemma shapeF_ok : shapeF eF = true. Proof. vm_compute. reflexivity. Qed.
Definition tail_chunks : list YP09.chunk :=
[YP09.mkChunk 2136 (CVal 8 (SOff 32 0)); YP09.mkChunk 2128 (CVal 8 (SOff 33 0)); YP09.mkChunk 2120 (CVal 8 (SOff 34 0));
YP09.mkChunk 2112 (CVal 8 (SOff 35 0)); YP09.mkChunk 2104 (CVal 8 (SOff 36 0)); YP09.mkChunk 2096 (CVal 8 (SOff 37 0));
YP09.mkChunk 2088 (CVal 8 (SOff 38 0)); YP09.mkChunk 2080 (CVal 8 (SOff 39 0))].
Definition ssT : sstate := mkSS IO_RET sr_atoms [YP09.mkRegion (Some 2%nat) 0 IO_FRAME 0 0 tail_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition eT : sstate := Eval vm_compute in fst (RUN ssT).
Lemma r_T : RUN ssT = (eT, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition KEPTT : list Z := [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Definition shapeT (ss : sstate) : bool :=
(ss_pc ss =? 0x4641c) &&
reg_is ss 1 (SOff 32 0) && reg_is ss 2 (SOff 2 IO_FRAME) && reg_is ss 8 (SOff 33 0) && reg_is ss 9 (SOff 34 0) &&
reg_is ss 18 (SOff 35 0) && reg_is ss 19 (SOff 36 0) && reg_is ss 20 (SOff 37 0) && reg_is ss 21 (SOff 38 0) && reg_is ss 22 (SOff 39 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTT &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (ss_mem ss).
Lemma shapeT_ok : shapeT eT = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off n v c, chunk_is off n v c = true -> c = YP09.mkChunk off (CVal n v).
Proof.
intros off n v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem iopen_front : forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + IO_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - IO_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 A_PATH -> getr regs 11 = w64 A_WB ->
cells_hold (mrestrict (w_H W) mem) io_cells ->
SRr tfibsegs W (cfg_at tfibsegs FF_pc_wrap_fopen regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs FF_real_fopen regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
getr regs1 10 = w64 A_PATH /\ getr regs1 11 = w64 A_WB /\ getr regs1 1 = w64 IO_RET /\ getr regs1 2 = w64 (spZ regs - IO_FRAME) /\
(forall r, In r KEPTF -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall j rz off, nth_error SAVEDF j = Some (rz, off) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IO_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - IO_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a)).
Proof.
intros ly S W regs mem md HAR Hal16 Hslo Hshi HpresE G10 G11 HCELLS.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold IO_WIN, IO_FRAME in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at at 1. change (w64 FF_pc_wrap_fopen) with (Z_to_bv 64 FF_pc_wrap_fopen).
assert (HS0 : st_ok tfibsegs EE ssF (restrict H (mkst regs (Z_to_bv 64 FF_pc_wrap_fopen) mem (seg_rom tfibsegs)))).
{ unfold ssF. apply st_ok_pin_reg; [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
unfold ssF1. apply st_ok_pin_reg; [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G10; reflexivity].
unfold ssF0. rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memF. apply Forall_cons.
{ unfold stkF. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2160)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia. }
rewrite map_app. apply Forall_app. split.
+ exact (AE2y.icpt_rodata_ok B TB ly S H mem EE (proj1 HAR)).
+ exact (cells_region_ok _ EE io_cells HCELLS).
- apply pairwise_disjoint_of_extents. unfold memF, stkF, io_cells, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold FF_got_fopen, FF_got_cflags, SH_PATH, SH_WB0, A_PATH, A_WB, IO_WIN. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (ff_phase_to W EE FF_real_fopen ssF eF RS_running _ md HS0 r_F)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). apply SRr_ret. split; [reflexivity|].
assert (MEQ1 : forall z : word, ~ (sp0 - 2160 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
pose proof (in_wrange_single_b EE memF (bv_unsigned z) 2 (- 2160) 0 sp0 ltac:(vm_compute; reflexivity) EE2 Hin). lia. }
clear HF1 HFr1.
pose proof shapeF_ok as Hsh. unfold shapeF in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HSV].
apply andb_prop in Hsh as [Hsh HK']. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hpc R10]. apply Z.eqb_eq in Hpc.
destruct (ss_mem eF) as [|r0 rest] eqn:Hmem; [discriminate |].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c.
unfold IO_WIN, IO_FRAME in W0b, W0c, Hpc, R1, R2.
assert (RD : forall (r : bv 5) v, reg_is eF (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eF ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTF -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
set (regs1 := ms_regs ms1) in *.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2160 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2160 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eF ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2160)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2160)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply AE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
exists regs1, (ms_mem ms1), md1. split; [reflexivity|]. split; [exact MF1|]. split; [exact HAR1|].
split; [rewrite (RD 10%bv (SLit A_PATH) R10); reflexivity|].
split; [rewrite (RD 11%bv (SLit A_WB) R11); reflexivity|].
split; [rewrite (RD 1%bv (SLit IO_RET) R1); reflexivity|].
split; [rewrite (RD 2%bv (SOff 2 (- 2144)) R2); cbn [sv_denot]; rewrite EE2; reflexivity|].
split.
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTF in Hin; cbn in Hin; lia).
apply (RK (Z_to_bv 5 r) (Z.to_nat r)); [| rewrite Z2Nat.id by lia; exact Hin].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split.
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. cbn [nth_error] in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eF _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite W0a in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.
Theorem iopen_tail : forall (W : world tfibsegs) regs mem md (v : list Z),
length v = 8%nat -> Forall (fun z => 0 <= z < 2 ^ 64) v -> nth 0 v 0 mod 2 = 0 ->
2 ^ 43 <= spZ regs -> spZ regs + IO_FRAME <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall j, (j < 8)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 2136 - 8 * Z.of_nat j) 8 (nth j v 0)) ->
SRr tfibsegs W (cfg_at tfibsegs IO_RET regs mem md)
(fun W' c' => W' = W /\ exists regs1 md1,
c' = mkCfg (mkst regs1 (w64 (nth 0 v 0)) mem (seg_rom tfibsegs)) md1 /\ same_but_materialized md md1 /\
getr regs1 10 = getr regs 10 /\ getr regs1 1 = w64 (nth 0 v 0) /\ getr regs1 2 = w64 (spZ regs + IO_FRAME) /\
getr regs1 8 = w64 (nth 1 v 0) /\ getr regs1 9 = w64 (nth 2 v 0) /\ getr regs1 18 = w64 (nth 3 v 0) /\ getr regs1 19 = w64 (nth 4 v 0) /\
getr regs1 20 = w64 (nth 5 v 0) /\ getr regs1 21 = w64 (nth 6 v 0) /\ getr regs1 22 = w64 (nth 7 v 0) /\
(forall r, In r KEPTT -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))).
Proof.
intros W regs mem md v Hlen Hv Heven Hsplo Hsphi Hal16 HC.
destruct v as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|? ?]]]]]]]]]; try discriminate Hlen. clear Hlen. cbn [nth] in *.
pose proof (Forall_inv Hv) as R0. pose proof (Forall_inv (Forall_inv_tail Hv)) as R1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hv))) as R2.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hv)))) as R3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hv))))) as R4.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hv)))))) as R5.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hv))))))) as R6.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hv)))))))) as R7.
unfold IO_FRAME in *. set (sp0 := spZ regs) in *. set (H := w_H W) in *.
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs [v0; v1; v2; v3; v4; v5; v6; v7]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EEx : forall j z, nth_error [v0; v1; v2; v3; v4; v5; v6; v7] j = Some z -> ew EE (32 + j) = Z_to_bv 64 z) by (intros j z Hj; exact (AE2y.Env_x regs _ j z Hj)).
pose proof (EEx 0%nat v0 eq_refl) as X32. pose proof (EEx 1%nat v1 eq_refl) as X33. pose proof (EEx 2%nat v2 eq_refl) as X34. pose proof (EEx 3%nat v3 eq_refl) as X35.
pose proof (EEx 4%nat v4 eq_refl) as X36. pose proof (EEx 5%nat v5 eq_refl) as X37. pose proof (EEx 6%nat v6 eq_refl) as X38. pose proof (EEx 7%nat v7 eq_refl) as X39.
cbn [Nat.add] in X32, X33, X34, X35, X36, X37, X38, X39.
unfold cfg_at. change (w64 IO_RET) with (Z_to_bv 64 IO_RET).
assert (HS0 : st_ok tfibsegs EE ssT (restrict H (mkst regs (Z_to_bv 64 IO_RET) mem (seg_rom tfibsegs)))).
{ unfold ssT. rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [v0; v1; v2; v3; v4; v5; v6; v7])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EE2. unfold IO_FRAME. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. unfold tail_chunks.
assert (CK : forall j off z, nth_error [v0; v1; v2; v3; v4; v5; v6; v7] j = Some z -> 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) (sp0 + off) 8 z ->
YP09.chunk_ok tfibsegs EE (mrestrict H mem) sp0 (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off z Hj Hz Hvv. eapply (chunk_ok_val tfibsegs EE _ sp0 off 8 _ z); [cbn [sv_denot]; rewrite (EEx j z Hj), Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact Hvv]. }
apply Forall_cons; [apply (CK 0%nat 2136 v0 eq_refl R0); replace (sp0 + 2136) with (sp0 + 2136 - 8 * Z.of_nat 0) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 1%nat 2128 v1 eq_refl R1); replace (sp0 + 2128) with (sp0 + 2136 - 8 * Z.of_nat 1) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 2%nat 2120 v2 eq_refl R2); replace (sp0 + 2120) with (sp0 + 2136 - 8 * Z.of_nat 2) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 3%nat 2112 v3 eq_refl R3); replace (sp0 + 2112) with (sp0 + 2136 - 8 * Z.of_nat 3) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 4%nat 2104 v4 eq_refl R4); replace (sp0 + 2104) with (sp0 + 2136 - 8 * Z.of_nat 4) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 5%nat 2096 v5 eq_refl R5); replace (sp0 + 2096) with (sp0 + 2136 - 8 * Z.of_nat 5) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 6%nat 2088 v6 eq_refl R6); replace (sp0 + 2088) with (sp0 + 2136 - 8 * Z.of_nat 6) by lia; apply HC; lia|].
apply Forall_cons; [apply (CK 7%nat 2080 v7 eq_refl R7); replace (sp0 + 2080) with (sp0 + 2136 - 8 * Z.of_nat 7) by lia; apply HC; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. cbn. exact (conj I I).
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EE2. change (2 ^ 4) with 16.
repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (ff_phase W EE ssT eT _ _ md HS0 r_T)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z : word, ms_mem ms1 z = mem z).
{ intros z. apply (HF1 z). intros (r & Hin & Hr). unfold ssT in Hin. cbn [ss_mem] in Hin. destruct Hin as [<-|[]]. cbn in Hr. lia. }
pose proof shapeT_ok as Hsh. unfold shapeT in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK']. apply andb_prop in Hsh as [Hsh Q22]. apply andb_prop in Hsh as [Hsh Q21].
apply andb_prop in Hsh as [Hsh Q20]. apply andb_prop in Hsh as [Hsh Q19]. apply andb_prop in Hsh as [Hsh Q18].
apply andb_prop in Hsh as [Hsh Q9]. apply andb_prop in Hsh as [Hsh Q8]. apply andb_prop in Hsh as [Hsh Q2]. apply andb_prop in Hsh as [Hpc Q1]. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) vv, reg_is eT (bv_unsigned r) vv = true -> getr (ms_regs ms1) r = sv_denot EE vv).
{ intros r vv Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eT ms1 r HS1). }
eapply (SRr_ret_at tfibsegs tbl_ff tbl_ff_ok Hwx W EE); [exact HS1 | reflexivity | rewrite Hpc; vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|].
assert (MEM : ms_mem ms1 = mem) by (apply functional_extensionality; exact MEQ1).
assert (P1 : getr (ms_regs ms1) 1 = w64 v0) by (rewrite (RD 1%bv (SOff 32 0) Q1); cbn [sv_denot]; rewrite X32, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
exists (ms_regs ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [rewrite MEM, P1, (AE2y.ret_ok_lit v0 R0 Heven); reflexivity|].
split; [apply with_vm_backing_same|].
split; [rewrite (RD 10%bv (SOff 10 0)); [cbn [sv_denot]; rewrite (EEreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite forallb_forall in HK'; exact (HK' 10 ltac:(cbn; tauto))]|].
split; [exact P1|].
split; [rewrite (RD 2%bv (SOff 2 2144) Q2); cbn [sv_denot]; rewrite EE2; reflexivity|].
split; [rewrite (RD 8%bv (SOff 33 0) Q8); cbn [sv_denot]; rewrite X33, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 9%bv (SOff 34 0) Q9); cbn [sv_denot]; rewrite X34, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 18%bv (SOff 35 0) Q18); cbn [sv_denot]; rewrite X35, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 19%bv (SOff 36 0) Q19); cbn [sv_denot]; rewrite X36, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 20%bv (SOff 37 0) Q20); cbn [sv_denot]; rewrite X37, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 21%bv (SOff 38 0) Q21); cbn [sv_denot]; rewrite X38, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 22%bv (SOff 39 0) Q22); cbn [sv_denot]; rewrite X39, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTT in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK'. specialize (HK' _ Hin). cbn beta in HK'.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK'.
Qed.
End d.
End b.
