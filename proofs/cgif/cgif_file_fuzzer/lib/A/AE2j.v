(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition SC_ENTRY : Z := 0x418fc.
Definition SC_RETPC : Z := 0x42534.
Definition SC_WIN : Z := 2176.
Definition A_RWA : Z := 0x20124.
Definition A_WB : Z := 0x20e60.
Definition st_const : list (Z * Z * list (Z * N * Z)) :=
[ (0x9df88, 8, [(0, 8%N, 0x137b28)]); (0x137c18, 16, [(0, 8%N, 0x101000100000000); (8, 8%N, 0x101010101010101)]) ].
Lemma st_const_chk : forall ly, rodata_chk ly st_const = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition st_cells : list (Z * Z * list (Z * N * Z)) :=
[ (0x9fcc0, 8, [(0, 8%N, 0x97790)]); (0x7fffc020, 8, [(0, 8%N, 0)]); (0x7fffc1c8, 8, [(0, 8%N, 0xf9f9f90300000000)]); (A_WB, 8, [(0, 8%N, 0x6277)]) ].
Definition stkS : YP09.region := YP09.mkRegion (Some 2%nat) (- SC_WIN) 0 (- SC_WIN) 0 [].
Definition memS : smem := [stkS; img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells).
Definition ssS (s c : Z) : sstate := mkSS SC_ENTRY (sr_set (sr_set sr_atoms 10%bv (SLit s)) 11%bv (SLit c)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ff FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition KEPTS : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeS (res : Z) (ss : sstate) : bool :=
(ss_pc ss =? SC_RETPC) && match ss_resv ss with None => true | _ => false end && reg_is ss 10 (SLit res) && reg_is ss 1 (SOff 1 0) && reg_is ss 2 (SOff 2 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTS &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - SC_WIN) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
Definition INST : list (Z * Z * Z) := [(A_RWA, 119, A_RWA + 1); (A_WB, 43, 0); (A_WB, 120, 0); (A_WB, 101, 0)].
Definition eS1 : sstate := Eval vm_compute in fst (RUN (ssS A_RWA 119)).
Definition eS2 : sstate := Eval vm_compute in fst (RUN (ssS A_WB 43)).
Definition eS3 : sstate := Eval vm_compute in fst (RUN (ssS A_WB 120)).
Definition eS4 : sstate := Eval vm_compute in fst (RUN (ssS A_WB 101)).
Lemma r_S1 : RUN (ssS A_RWA 119) = (eS1, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS (A_RWA + 1) eS1 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma r_S2 : RUN (ssS A_WB 43) = (eS2, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS 0 eS2 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma r_S3 : RUN (ssS A_WB 120) = (eS3, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS 0 eS3 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma r_S4 : RUN (ssS A_WB 101) = (eS4, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS 0 eS4 = true. Proof. vm_compute. split; reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma strchr_inst : forall s c res eS,
RUN (ssS s c) = (eS, RS_stopped (SR_jalr (SOff 1 0))) -> shapeS res eS = true -> 0 <= s < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= res < 2 ^ 64 ->
forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + SC_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 s -> getr regs 11 = w64 c ->
cells_hold (mrestrict (w_H W) mem) st_cells -> ro_img (mrestrict (w_H W) mem) ->
SRr tfibsegs W (cfg_at tfibsegs SC_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs (raZ regs) regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
getr regs1 10 = w64 res /\ getr regs1 1 = getr regs 1 /\ getr regs1 2 = getr regs 2 /\
(forall r, In r KEPTS -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SC_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a)).
Proof.
intros s c res eS r_S Hsh Rs Rc Rres ly S W regs mem md HAR Hra Hal16 Hslo Hshi HpresE G10 G11 HCELLS HIMG.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold SC_WIN in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at at 1. change (w64 SC_ENTRY) with (Z_to_bv 64 SC_ENTRY).
assert (HS0 : st_ok tfibsegs EE (ssS s c) (restrict H (mkst regs (Z_to_bv 64 SC_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssS.
apply (st_ok_pin_reg EE (mkSS SC_ENTRY (sr_set sr_atoms 10%bv (SLit s)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] [])) _ 11%bv (SLit c));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
apply (st_ok_pin_reg EE (mkSS SC_ENTRY sr_atoms memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] [])) _ 10%bv (SLit s));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G10; reflexivity].
rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memS. apply Forall_cons.
{ unfold stkS. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2176)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia. }
apply Forall_cons; [apply (img_piece_ok _ EE 0x1cd1e (0x20b7c - 0x1cd1e)); [exact HIMG | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|].
apply Forall_cons; [apply (img_piece_ok _ EE 0x10330 (0x10398 - 0x10330)); [exact HIMG | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|].
rewrite !map_app. apply Forall_app. split; [exact (AE2y.icpt_rodata_ok B TB ly S H mem EE (proj1 HAR))|].
apply Forall_app. split; [exact (rodata_ok B TB st_const ly S H mem EE (st_const_chk ly) (proj1 HAR))|].
exact (cells_region_ok _ EE st_cells HCELLS).
- apply pairwise_disjoint_of_extents. unfold memS, stkS, img_piece, st_cells, st_const, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_WB, SC_WIN in *. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (ff_phase W EE (ssS s c) eS _ _ md HS0 r_S)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z : word, ~ (sp0 - 2176 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
pose proof (in_wrange_single_b EE memS (bv_unsigned z) 2 (- 2176) 0 sp0 ltac:(vm_compute; reflexivity) EE2 Hin). lia. }
clear HF1 HFr1.
unfold shapeS in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eS = None) by (destruct (ss_resv eS); [discriminate | reflexivity]).
destruct (ss_mem eS) as [|r0 rest] eqn:Hmem; [discriminate |].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. unfold SC_WIN, SC_RETPC in W0b, W0c, Hpc.
assert (RD : forall (r : bv 5) v, reg_is eS (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eS ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTS -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2176 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2176 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eS ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2176)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2176)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply AE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
eapply (SRr_ret_at tfibsegs tbl_ff tbl_ff_ok Hwx W EE); [exact HS1 | exact Hresv | rewrite Hpc; vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|].
assert (P1 : getr (ms_regs ms1) 1 = getr regs 1) by (rewrite (RD 1%bv (SOff 1 0) R1); cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HAR2 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat' md)).
{ assert (SBM : same_but_materialized (with_vm_backing (m_vm_lazy md) mat1 md) (with_vm_backing (m_vm_lazy md) mat' md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) mat' mat1 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBM) as MF.
apply (al_frame _ _ LAWS ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) (ms_mem ms1) _ HAR1);
[intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | intros a _ _; reflexivity]. }
exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [unfold cfg_at; rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply with_vm_backing_same|]. split; [exact HAR2|].
split; [rewrite (RD 10%bv (SLit res) R10); reflexivity|].
split; [exact P1|].
split; [rewrite (RD 2%bv (SOff 2 0) R2); cbn [sv_denot]; rewrite (EEreg 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTS in Hin; cbn in Hin; lia).
apply (RK (Z_to_bv 5 r) (Z.to_nat r)); [| rewrite Z2Nat.id by lia; exact Hin].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.
Definition strchr_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (res : Z)
: world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs (raZ regs) regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
getr regs1 10 = w64 res /\ getr regs1 1 = getr regs 1 /\ getr regs1 2 = getr regs 2 /\
(forall r, In r KEPTS -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SC_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a).
Theorem tfib_strchr_lit : forall s c res, In (s, c, res) INST ->
forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + SC_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 s -> getr regs 11 = w64 c ->
cells_hold (mrestrict (w_H W) mem) st_cells -> ro_img (mrestrict (w_H W) mem) ->
SRr tfibsegs W (cfg_at tfibsegs SC_ENTRY regs mem md) (strchr_post ly S W regs mem md res).
Proof.
intros s c res Hin. unfold INST, A_RWA, A_WB in Hin. cbn [In Z.add] in Hin.
destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <-; intros;
[ eapply (strchr_inst _ _ _ eS1 (proj1 r_S1) (proj2 r_S1))
| eapply (strchr_inst _ _ _ eS2 (proj1 r_S2) (proj2 r_S2))
| eapply (strchr_inst _ _ _ eS3 (proj1 r_S3) (proj2 r_S3))
| eapply (strchr_inst _ _ _ eS4 (proj1 r_S4) (proj2 r_S4)) ]; try eassumption; unfold A_RWA, A_WB; lia.
Qed.
End d.
End b.
