(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o YI6a UI1w UI3p UI3m UI3t
UI3w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma gce_garr8u : forall m a d27 dl t30,
val_mem ubs0segs m a 1 33 -> val_mem ubs0segs m (a + 1) 1 249 -> val_mem ubs0segs m (a + 2) 1 4 -> val_mem ubs0segs m (a + 3) 1 d27 -> 0 <= d27 < 256 ->
val_mem ubs0segs m (a + 4) 2 dl -> 0 <= dl < 65536 -> val_mem ubs0segs m (a + 6) 1 t30 -> 0 <= t30 < 256 -> val_mem ubs0segs m (a + 7) 1 0 ->
garr8 ubs0segs m a ([33; 249; 4; d27] ++ YO07.u16le dl ++ [t30; 0]).
Proof using.
intros m a d27 dl t30 V24 V25 V26 V27 R27 V28 R28 V30 R30 V31. cbn [app YO07.u16le].
apply garr8_cons_val1; [exact V24 | lia |]. apply garr8_cons_val1; [exact V25 | lia |]. replace (a + 1 + 1) with (a + 2) by lia.
apply garr8_cons_val1; [exact V26 | lia |]. replace (a + 2 + 1) with (a + 3) by lia. apply garr8_cons_val1; [exact V27 | lia |]. replace (a + 3 + 1) with (a + 4) by lia.
apply garr8_cons_val2; [exact V28 | lia |]. replace (a + 4 + 2) with (a + 6) by lia. apply garr8_cons_val1; [exact V30 | lia |]. replace (a + 6 + 1) with (a + 7) by lia.
apply garr8_cons_val1; [exact V31 | lia |]. apply garr8_nil.
Qed.
Definition enc_chunks : list YP09.chunk := [mkChunk 8 (CVal 8 (SOff 69%nat 0)); mkChunk 16 (CVal 4 (SOff 70%nat 0))].
Definition PC_G1 : Z := RA0 + 0x488.
Definition ssOK : sstate := ra_ssW PC_OK sr_atoms 24 32 (enc_chunks ++ chC 71 72) false [(70%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition gce_lits : list YP09.chunk := [mkChunk 24 (CVal 1 (SLit 33)); mkChunk 30 (CVal 1 (SLit 0)); mkChunk 31 (CVal 1 (SLit 0))].
Definition ssG1 : sstate :=
ra_ssW PC_G1 (sr_set (sr_set (sr_set sr_atoms 10%bv (SExt true 32 (SOff 34%nat 0))) 12%bv (SLit 18446744073709551609)) 13%bv (SLit 4)) 25 31
(enc_chunks ++ chC 71 72 ++ gce_lits) false [(70%nat, mkAF 0 (2^32-1) 0)] [] [].
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Definition at_T (pc : Z) (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p : Z) (S : list Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (bb Lbb M : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   ra_rb b A2 Lbb /\
ra_regs regs2 cx /\ getr regs2 23 = Z_to_bv 64 (c_slct cx) /\ getr regs2 24 = Z_to_bv 64 p /\ getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) /\
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) /\
word_mem ubs0segs mem2 (c_sp cx + 8) bb /\ val_mem ubs0segs mem2 (c_sp cx + 16) 4 M /\ 1 <= M <= Lbb /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M /\ M <= 2 * c_nP cx + 16 /\ fbC mem2 cx /\
sink_at ubs0_msyms mem2 md2 (c_f cx) (S ++ ra_gce cx) /\
getr regs2 19 = Z_to_bv 64 0.
Definition at_T3 (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (S : list Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (bb Lbb M : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 PC_T3) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   ra_rb b A2 Lbb /\
getr regs2 2 = Z_to_bv 64 (c_sp cx) /\ getr regs2 8 = Z_to_bv 64 (c_raw cx) /\
getr regs2 4 = Z_to_bv 64 (c_tp cx) /\ getr regs2 3 = Z_to_bv 64 (c_gp cx) /\
getr regs2 27 = Z_to_bv 64 (c_s11 cx) /\
getr regs2 18 = Z_to_bv 64 (c_g cx) /\ getr regs2 20 = Z_to_bv 64 ubs0_A_cgif_writecb /\
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) /\
word_mem ubs0segs mem2 (c_sp cx + 8) bb /\ val_mem ubs0segs mem2 (c_sp cx + 16) 4 M /\ 1 <= M <= Lbb /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M /\ M <= 2 * c_nP cx + 16 /\ fb7 mem2 cx /\
sink_at ubs0_msyms mem2 md2 (c_f cx) (S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV) /\
getr regs2 19 = Z_to_bv 64 0.
Lemma enc_of_region : forall E m sp xc bb M,
region_ok ubs0segs E m (YP09.mkRegion (Some 2%nat) (-16) 48 (-16) 48 xc) ->
bv_unsigned (ew E 2) = sp ->
In (mkChunk 8 (CVal 8 (SOff 69%nat 0))) xc -> In (mkChunk 16 (CVal 4 (SOff 70%nat 0))) xc ->
ew E 69 = Z_to_bv 64 bb -> ew E 70 = Z_to_bv 64 M -> 0 <= bb < 2 ^ 64 -> 0 <= M < 2 ^ 32 ->
word_mem ubs0segs m (sp + 8) bb /\ val_mem ubs0segs m (sp + 16) 4 M.
Proof using.
intros E m sp xc bb M (_ & _ & _ & Hcs) H2 H32 H40 H69 H70 Hbb HM. cbn [r_chunks r_base base_val] in Hcs. rewrite H2 in Hcs.
split.
- apply val_mem_word_mem. eapply (val_of_chunk_ok ubs0segs _ _ _ 8 8%N); [eapply (proj1 (Forall_forall _ _) Hcs); exact H32 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite H69, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
- eapply (val_of_chunk_ok ubs0segs _ _ _ 16 4%N); [eapply (proj1 (Forall_forall _ _) Hcs); exact H40 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite H70, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
Qed.
Lemma ra_t1 :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z) (S : list Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> ra_rb b A2 Lbb -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) ->
word_mem ubs0segs mem2 (c_sp cx + 8) bb -> val_mem ubs0segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) ->
(c_rcur cx = 0 \/ c_rcur cx = 6) ->
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M -> M <= 2 * c_nP cx + 16 -> fbC mem2 cx ->
sink_at ubs0_msyms mem2 md2 (c_f cx) S -> Z.of_nat (length S) + 2 * c_nP cx + 2048 <= SINK_MAX ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_OK) mem2 (seg_rom ubs0segs)) md2)
(at_T PC_T2 cx L A mem md regs0 p S b).
Proof using FWRITE IMG.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M S b Hcx HO HJ Hid HRB HB HR G23 G24 G22 HB2 Hwt W32 W40 HM Hobjs HFS Hrc HVOK HM2 HFBC HSK Hroom.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & _).
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (W40' : val_mem ubs0segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (HE71 : ew E 71 = Z_to_bv 64 (ra_iclen cx - 1)) by (apply (HMo 2%nat); reflexivity).
assert (HE72 : ew E 72 = Z_to_bv 64 (ra_packed cx)) by (apply (HMo 3%nat); reflexivity).
pose proof (E_cv regs2 cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx]) as HX. pose proof (E_rv regs2 cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx]) as HY. rewrite <- HE0 in HX, HY.
assert (HE34 : ew E 34 = Z_to_bv 64 (c_fattr cx)) by (apply (HX 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (c_h cx)) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 (c_top cx)) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 (c_left cx)) by (apply (HX 6%nat); reflexivity).
assert (HE39 : ew E 39 = Z_to_bv 64 (c_delay cx)) by (apply (HX 7%nat); reflexivity).
assert (HE41 : ew E 41 = Z_to_bv 64 (c_disp cx)) by (apply (HX 9%nat); reflexivity).
assert (HE42 : ew E 42 = Z_to_bv 64 (c_tidx cx)) by (apply (HX 10%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 (c_rattr cx)) by (apply (HY 3%nat); reflexivity).
assert (Rpk : 0 <= ra_packed cx < 256).
{ unfold ra_packed.
assert (Hpp : c_slct cx <> 0 -> 1 <= YO07.pal_pow (c_slct cx) <= 8).
{ intros Hnz. unfold YO07.pal_pow.
assert (Hc8 : exists k, 0 <= k <= 8 /\ (k = 0 -> c_slct cx <= 1) /\ (0 < k -> 2 ^ (k - 1) < c_slct cx) /\ c_slct cx <= 2 ^ k).
{ assert (Hcases : c_slct cx = 1 \/ c_slct cx = 2 \/ (3 <= c_slct cx <= 4) \/ (5 <= c_slct cx <= 8) \/ (9 <= c_slct cx <= 16) \/
(17 <= c_slct cx <= 32) \/ (33 <= c_slct cx <= 64) \/ (65 <= c_slct cx <= 128) \/ (129 <= c_slct cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]];
[exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6 | exists 7 | exists 8]; (split; [lia | split; [intros; lia | split; [intros; cbn; lia | cbn; lia]]]). }
destruct Hc8 as (k & Hk & H0 & Hlo & Hhi). rewrite (YI0j.np2_class k (c_slct cx) ltac:(lia) H0 Hlo Hhi). lia. }
destruct (Z.eqb_spec (c_slct cx) 0); cbn [negb]; destruct (YO07.flag (c_fattr cx) 2); lia. }
assert (Ric : 0 <= ra_iclen cx - 1 < 256).
{ unfold ra_iclen, YO07.calcInitCodeLen.
assert (Hne : 0 <= ra_ne cx <= 256) by (unfold ra_ne, num_eff; destruct (negb (c_slct cx =? 0)); destruct (_ && _ && _); lia).
assert (Hc8 : exists k, 0 <= k <= 8 /\ (k = 0 -> ra_ne cx <= 1) /\ (0 < k -> 2 ^ (k - 1) < ra_ne cx) /\ ra_ne cx <= 2 ^ k).
{ assert (Hcases : ra_ne cx <= 1 \/ ra_ne cx = 2 \/ (3 <= ra_ne cx <= 4) \/ (5 <= ra_ne cx <= 8) \/ (9 <= ra_ne cx <= 16) \/
(17 <= ra_ne cx <= 32) \/ (33 <= ra_ne cx <= 64) \/ (65 <= ra_ne cx <= 128) \/ (129 <= ra_ne cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]];
[exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6 | exists 7 | exists 8]; (split; [lia | split; [intros; lia | split; [intros; cbn; lia | cbn; lia]]]). }
destruct Hc8 as (k & Hk & H0 & Hlo & Hhi). rewrite (YI0j.np2_class k (ra_ne cx) ltac:(lia) H0 Hlo Hhi). destruct (Z.ltb_spec k 3); lia. }
assert (HS : st_ok ubs0segs E ssOK (mkst regs2 (Z_to_bv 64 PC_OK) mem2 (seg_rom ubs0segs))).
{ subst E. unfold ssOK.
apply (ra_st_okW cx (c_rcur cx) regs2 [bb; M'; ra_iclen cx - 1; ra_packed cx] mem2 PC_OK _ 24 32 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [| apply (chC_ok _ _ cx (c_rcur cx) 71 72 (objs_fields_ok _ _ _ Hobjs) HE35 HE36 HE37 HE38 HE71 Ric HE72 Rpk HFBC)]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_OK) mem2 (seg_rom ubs0segs))) in HJ.
Ltac wr HE2 := eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia].
jrun_to LAWS ubs0tbl_ok HS HJ PC_T2; [wr HE2|].
jbranch ubs0tbl HS.
-
jrun_to LAWS ubs0tbl_ok HS HJ PC_G1; [wr HE2|].
jreg HS (10%bv:reg) as A10. jreg HS (12%bv:reg) as A12. jreg HS (13%bv:reg) as A13.
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 22; 23; 24; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK1.
pose proof (fb_of_region _ _ _ _ _ _ _ _ 24 8%N (SLit 33) 33 (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) HE2 ltac:(cbv; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V24.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ1 : forall a, ~ (c_sp cx + 24 <= a < c_sp cx + 32) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
assert (Hobjs1 : objs_at (ms_mem msx) cx (c_rcur cx)) by (eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ1; lia);
assert (HFS1 : frame_savedN ubs0_msyms 12 regs0 (ms_mem msx) (spZ regs0)) by (eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; apply MEQ1; lia);
assert (HFBC1 : fbC (ms_mem msx) cx) by (eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQ1; lia);
assert (W32a : val_mem ubs0segs (ms_mem msx) (c_sp cx + 8) 8 bb) by (eapply fb_kept1; [apply val_mem_word_mem; exact W32 | intros a Ha; apply MEQ1; cbn in Ha; lia]);
assert (W40a : val_mem ubs0segs (ms_mem msx) (c_sp cx + 16) 4 M') by (eapply fb_kept1; [exact W40' | intros a Ha; apply MEQ1; cbn in Ha; lia]);
assert (HR1 : ra_regs (ms_regs msx) cx) by (unfold ra_regs; rewrite !HK1 by (cbv; tauto); exact HR)
end.
assert (GCEL : forall E0 m sp, bv_unsigned (ew E0 2) = sp -> val_mem ubs0segs m (sp + 24) 8 33 -> Forall (chunk_ok ubs0segs E0 m sp) gce_lits).
{ intros E0 m sp H2 V. unfold gce_lits.
assert (B : forall (k : nat) o i, (k < 8)%nat -> o + i = 24 + Z.of_nat k -> mbyte ubs0segs m (sp + o + i) = Some (Z_to_bv 8 (le_byte 33 8 k))).
{ intros k o i Hk Hoi. replace (sp + o + i) with (sp + 24 + Z.of_nat k) by lia. exact (V k Hk). }
repeat constructor.
- intros i Hi. cbn [c_len cv_len c_off c_val Z.of_N] in Hi |- *. assert (i = 0) by lia. subst i.
eexists. split; [reflexivity|]. rewrite (B 0%nat) by first [lia | reflexivity]. first [reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity].
- intros i Hi. cbn [c_len cv_len c_off c_val Z.of_N] in Hi |- *. assert (i = 0) by lia. subst i.
eexists. split; [reflexivity|]. rewrite (B 6%nat) by first [lia | reflexivity]. first [reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity].
- intros i Hi. cbn [c_len cv_len c_off c_val Z.of_N] in Hi |- *. assert (i = 0) by lia. subst i.
eexists. split; [reflexivity|]. rewrite (B 7%nat) by first [lia | reflexivity]. first [reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity]. }
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw1) & _). cbn beta in Hstw1.
remember (Ereg (ms_regs ms0) (ra_extra cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx])) as E1 eqn:HE1.
pose proof (E_cv (ms_regs ms0) cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx]) as HX1. pose proof (E_rv (ms_regs ms0) cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx]) as HY1.
pose proof (E_morev (ms_regs ms0) cx (c_rcur cx) [bb; M'; ra_iclen cx - 1; ra_packed cx] LG) as HMo1. rewrite <- HE1 in HX1, HY1, HMo1.
assert (F34 : ew E1 34 = Z_to_bv 64 (c_fattr cx)) by (apply (HX1 2%nat); reflexivity).
assert (F35 : ew E1 35 = Z_to_bv 64 (c_w cx)) by (apply (HX1 3%nat); reflexivity).
assert (F36 : ew E1 36 = Z_to_bv 64 (c_h cx)) by (apply (HX1 4%nat); reflexivity).
assert (F37 : ew E1 37 = Z_to_bv 64 (c_top cx)) by (apply (HX1 5%nat); reflexivity).
assert (F38 : ew E1 38 = Z_to_bv 64 (c_left cx)) by (apply (HX1 6%nat); reflexivity).
assert (F39 : ew E1 39 = Z_to_bv 64 (c_delay cx)) by (apply (HX1 7%nat); reflexivity).
assert (F41 : ew E1 41 = Z_to_bv 64 (c_disp cx)) by (apply (HX1 9%nat); reflexivity).
assert (F42 : ew E1 42 = Z_to_bv 64 (c_tidx cx)) by (apply (HX1 10%nat); reflexivity).
assert (F44 : ew E1 44 = Z_to_bv 64 (c_g cx)) by (apply (HY1 1%nat); reflexivity).
assert (F46 : ew E1 46 = Z_to_bv 64 (c_rattr cx)) by (apply (HY1 3%nat); reflexivity).
assert (F69 : ew E1 69 = Z_to_bv 64 bb) by (apply (HMo1 0%nat); reflexivity).
assert (F70 : ew E1 70 = Z_to_bv 64 M') by (apply (HMo1 1%nat); reflexivity).
assert (F71 : ew E1 71 = Z_to_bv 64 (ra_iclen cx - 1)) by (apply (HMo1 2%nat); reflexivity).
assert (F72 : ew E1 72 = Z_to_bv 64 (ra_packed cx)) by (apply (HMo1 3%nat); reflexivity).
assert (HS1 : st_ok ubs0segs E1 ssG1 ms0).
{ rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite HE1. unfold ssG1.
apply (ra_st_okW cx (c_rcur cx) (ms_regs ms0) [bb; M'; ra_iclen cx - 1; ra_packed cx] (ms_mem ms0) PC_G1 _ 25 31 false _ _ [] [] Hcx Hobjs1 HR1); rewrite <- ?HE1.
- rewrite HE1. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | ] | intros X; discriminate X | ] | intros X; discriminate X | cbn [sv_denot]; first [exact A13 | rewrite A13; cbn [sv_denot]; first [reflexivity | apply bv_eq; vm_compute; reflexivity]]].
{ rewrite <- HE1, A10. cbn [sv_denot]. rewrite F34, HE34, unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
{ cbn [sv_denot]. first [exact A12 | rewrite A12; cbn [sv_denot]; first [reflexivity | apply bv_eq; vm_compute; reflexivity]]. }
- intros a Ha. apply Hstw1. lia.
- intros X. discriminate X.
- reflexivity.
- apply Forall_app. split; [|apply Forall_app; split].
+ constructor; [|constructor; [|constructor]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite F69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W32a].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite F70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40a].
+ apply (chC_ok _ _ cx (c_rcur cx) 71 72 (objs_fields_ok _ _ _ Hobjs) F35 F36 F37 F38 F71 Ric F72 Rpk HFBC1).
+ apply GCEL; [| exact V24]. rewrite HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 2%bv 2 eq_refl). pose proof HR1 as (R2' & _). rewrite R2'. apply unsigned_lit_small. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite F70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
assert (G2 : bv_unsigned (ew E1 2) = c_sp cx) by (rewrite HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 2%bv 2 eq_refl); pose proof HR1 as (R2' & _); rewrite R2'; apply unsigned_lit_small; lia).
clear HS. rename HS1 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb; [wr G2|].
jbranch ubs0tbl HS.
+
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb; [wr G2|].
rewrite (gce_test E (c_fattr cx) (c_rattr cx) HE34 HE46 ltac:(lia) ltac:(lia)) in Hc.
pose proof (test1_sext32 E1 (c_fattr cx) true F34 ltac:(lia) Hc0) as Ht1. cbn [negb] in Ht1.
jreg HS (10%bv:reg) as Wa10. jreg HS (11%bv:reg) as Wa11. jreg HS (12%bv:reg) as Wa12. jreg HS (2%bv:reg) as Wa2. jreg HS (4%bv:reg) as Wa4. jreg HS (1%bv:reg) as Wa1.
rewrite F44 in Wa10. rewrite G2 in Wa11.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Wsp : spZ (ms_regs msx) = c_sp cx) by (unfold spZ; rewrite Wa2, <- (Z_to_bv_bv_unsigned 64 (ew E1 2)), G2; apply unsigned_lit_small; lia) end.
pose proof (R4' := proj1 (proj2 (proj2 (proj2 HR1)))). cbn beta in R4'.
lazymatch type of HS with st_ok _ _ _ ?msx =>
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRg;
assert (HGB : garr8 ubs0segs (ms_mem msx) (c_sp cx + 24) ([33; 249; 4; c_disp cx] ++ YO07.u16le (c_delay cx) ++ [0; 0]))
end.
{ apply gce_garr8u.
- eapply (fb_of_region _ _ _ _ _ _ _ _ 24 1%N (SLit 33) 33 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia].
- replace (c_sp cx + 24 + 1) with (c_sp cx + 25) by lia. first
[ eapply (vval_mem_of_chunk_mod ubs0segs _ _ _ 2%nat (c_sp cx) 25 1%N (SLit 18446744073709551609) 249 HRg); [reflexivity | cbv; tauto | exact G2 | vm_compute; reflexivity | cbn; lia]
| eapply (fb_of_region _ _ _ _ _ _ _ _ 25 1%N (SLit 249) 249 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia] ].
- replace (c_sp cx + 24 + 2) with (c_sp cx + 26) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 26 1%N (SLit 4) 4 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia].
- replace (c_sp cx + 24 + 3) with (c_sp cx + 27) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 27 1%N (SOff 41%nat 0) (c_disp cx) HRg G2); [cbv; tauto | cbn [sv_denot]; rewrite F41, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- lia.
- replace (c_sp cx + 24 + 4) with (c_sp cx + 28) by lia. eapply (vval_mem_of_chunk_mod ubs0segs _ _ _ 2%nat (c_sp cx) 28 2%N (SExt true 16 (SOff 39%nat 0)) (c_delay cx) HRg); [reflexivity | cbv; tauto | exact G2 | apply U_sext16_mod; [exact F39 | lia] | cbn; lia].
- lia.
- replace (c_sp cx + 24 + 6) with (c_sp cx + 30) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 30 1%N (SLit 0) 0 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia].
- lia.
- replace (c_sp cx + 24 + 7) with (c_sp cx + 31) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 31 1%N (SLit 0) 0 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia]. }
assert (HGCE : ra_gce cx = [33; 249; 4; c_disp cx] ++ YO07.u16le (c_delay cx) ++ [0; 0]).
{ unfold ra_gce. rewrite Hc, Ht1. rewrite (Z.mod_small (c_disp cx) 256) by lia. reflexivity. }
rewrite <- HGCE in HGB.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ2 : forall a, ~ (c_sp cx + 25 <= a < c_sp cx + 31) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs (ms_mem ms0) a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?G2 in H));
assert (Hobjs2 : objs_at (ms_mem msx) cx (c_rcur cx)) by (eapply objs_at_kept; [exact Hobjs1 | | |]; intros i Hi; apply MEQ2; lia);
assert (HSKc : sink_at ubs0_msyms (ms_mem msx) md2 (c_f cx) S)
by (apply (sink_at_frame ubs0_msyms mem2 _ md2 (c_f cx) S); [| exact HSK]; intros a Ha;
assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]);
rewrite MEQ2 by lia; apply MEQ1; lia)
end.
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (HfinA : In (c_f cx, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact Hfin]).
assert (Hgin2 : In (c_g cx, CGIF_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hgin]).
assert (Hfin2 : In (c_f cx, FILE_BLOCK) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact HfinA]).
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hrawin2 : In (c_raw cx, RAW_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hrawin]).
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2c.
assert (Hrf : c_raw cx + 48 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_raw cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_raw cx, RAW_SIZE) (c_f cx, FILE_BLOCK) HH2c Hrawin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hgf : c_g cx + 96 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_g cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_g cx, CGIF_SIZE) (c_f cx, FILE_BLOCK) HH2c Hgin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (HWv : WRITECB_STK = 528) by reflexivity.
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := c_g cx) (gvals := c_gvals cx) (src := c_sp cx + 24) (n := 8) (f := c_f cx) (S := S) (bs := ra_gce cx);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Wa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Wa10 | exact Wa11 | exact Wa12 | rewrite Wsp; exact Hspal | rewrite Wsp; lia | rewrite Wsp; lia | rewrite Wsp; lia
| rewrite Wa4, HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 4%bv 4 eq_refl), R4', Htpv; reflexivity
| exact (proj2 (proj2 Hobjs2)) | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HGB | rewrite HGCE; reflexivity
| lia | lia | lia | rewrite Wsp; lia | unfold c_nP in Hroom; lia | lia | ].
intros a Ha. destruct Ha as (r & Hr & Har). exists r. split; [right; exact Hr | exact Har]. }
cbv beta. intros c' (regsW & memW & mdW & -> & HJW & HPW & Hr10W & HSKW & HhiW & HblkW). rewrite Wsp in HhiW.
jafter_call2 HS 73%nat regsW memW HPW 0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact G2 | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [rewrite HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 9%bv 9 eq_refl), (proj1 (proj2 (proj2 HR1))); apply unsigned_lit_small; lia | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 8); [rewrite HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 8%bv 8 eq_refl), (proj1 (proj2 HR1)); apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_raw cx + (a - c_raw cx)) by lia. apply (HblkW (c_raw cx) RAW_SIZE (a - c_raw cx) Hrawin2); [lia|].
replace (c_raw cx + (a - c_raw cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
- eapply (region_kept_pointwise ubs0segs _ _ _ 44); [rewrite F44; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_g cx + (a - c_g cx)) by lia. apply (HblkW (c_g cx) CGIF_SIZE (a - c_g cx) Hgin2); [lia|].
replace (c_g cx + (a - c_g cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg' HS (10%bv:reg) 0 Hr10W.
lazymatch type of HS with st_ok _ _ _ ?msx => change memW with (ms_mem msx) in HJW end.
jrun_to LAWS ubs0tbl_ok HS HJW PC_T2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact G2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ (ms_regs ms0) _ [2; 3; 4; 8; 9; 22; 23; 24; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE1; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HKF.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HKF;
assert (MEQ3 : forall a, ~ (c_sp cx + 25 <= a < c_sp cx + 31) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?G2 in H));
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF
end.
assert (Hbbin2 : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
pose proof (heap_blocks_range ubs0_msyms MR LAWS L2 A2 _ md2 bb Lbb HH2c Hbbin2 ltac:(lia)) as (Rbb0 & Rbb1 & _).
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (KF_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 24 <= a < c_sp cx + 32) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (clear - MEQ3 HhiW MEQ2 MEQ1 Hsplo Hac Hsp47 HWv; intros a H1 H2; rewrite MEQ3 by lia; etransitivity; [apply (proj1 (HhiW a ltac:(lia) ltac:(lia)))|]; rewrite MEQ2, MEQ1 by lia; reflexivity);
assert (KF_cfg : forall i, 0 <= i < 40 -> mbyte ubs0segs (ms_mem msx) (c_cfp cx + i) = mbyte ubs0segs mem2 (c_cfp cx + i))
by (clear - MEQ3 HhiW MEQ2 MEQ1 Hsplo Hac Hsp47 HWv Hcfplo Hcfphi; intros i Hi; rewrite MEQ3 by lia; etransitivity; [apply (proj1 (HhiW (c_cfp cx + i) ltac:(lia) ltac:(lia)))|]; rewrite MEQ2, MEQ1 by lia; reflexivity);
assert (KF_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - MEQ3 HblkW MEQ2 MEQ1 Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hi; rewrite MEQ3 by lia; etransitivity; [apply (HblkW b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
rewrite MEQ2, MEQ1 by lia; reflexivity)
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- at_T _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) =>
exists L2, A2, (ms_regs msx), (ms_mem msx), mdW, bb, Lbb, M end.
split; [reflexivity|]. split; [exact HJW|]. split; [exact Hid|]. split; [exact HRB|].
split. { unfold ra_regs. rewrite !HKF by (cbv; tauto). exact HR1. }
split. { rewrite HKF by (cbv; tauto). rewrite HK1 by (cbv; tauto). exact G23. }
split. { rewrite HKF by (cbv; tauto). rewrite HK1 by (cbv; tauto). exact G24. }
split. { rewrite HKF by (cbv; tauto). rewrite HK1 by (cbv; tauto). exact G22. }
split; [exact HB2|]. split; [exact Hwt|].
split. { apply val_mem_word_mem. eapply (fb_of_region _ _ _ _ _ _ _ _ 8 8%N (SOff 69%nat 0) bb HRF); [ew_havoc; exact G2 | cbv; tauto | cbn [sv_denot]; ew_havoc; rewrite F69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia]. }
split. { change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in W40'. apply (proj2 (val_mem_mod _ _ _ _)). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). fold M'.
eapply (fb_of_region _ _ _ _ _ _ _ _ 16 4%N (SOff 70%nat 0) M' HRF); [ew_havoc; exact G2 | cbv; tauto | cbn [sv_denot]; ew_havoc; rewrite F70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia]. }
split; [exact HM|].
cbn [ms_mem mkst].
split. { eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; [apply KF_cfg; exact Hi | apply (KF_blk _ _ i Hrawin2); lia | apply (KF_blk _ _ i Hgin2); lia]. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply KF_stk; lia. }
split. { destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [|exact HMout].
apply (garr8_frame ubs0segs mem2 _ bb out HGout). intros a Ha. rewrite <- HMout in Ha. replace a with (bb + (a - bb)) by lia. apply (KF_blk _ _ (a - bb) Hbbin2); [lia | lia | | lia].
pose proof (heap_sep_perm ubs0_msyms MR LAWS L2 A2 _ md2 (bb, Lbb) _ (c_f cx, FILE_BLOCK) HH2c HB2 HfinA) as Hbf. cbn [fst snd] in Hbf. exact Hbf. }
split; [exact HM2|].
split. { eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply KF_stk; lia. }
split. { apply (sink_at_frame ubs0_msyms memW _ mdW (c_f cx)); [| exact HSKW]. intros a Ha.
assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
apply MEQ3; lia. }
cbn [ms_regs mkst]. jreg HS (19%bv:reg) as Q19. cbn [ms_regs mkst] in Q19.
first [exact Q19 | rewrite Q19; apply bv_eq; vm_compute; reflexivity].
+
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb; [wr G2|].
rewrite (gce_test E (c_fattr cx) (c_rattr cx) HE34 HE46 ltac:(lia) ltac:(lia)) in Hc.
pose proof (test1_sext32 E1 (c_fattr cx) false F34 ltac:(lia) Hc0) as Ht1. cbn [negb] in Ht1.
jreg HS (10%bv:reg) as Wa10. jreg HS (11%bv:reg) as Wa11. jreg HS (12%bv:reg) as Wa12. jreg HS (2%bv:reg) as Wa2. jreg HS (4%bv:reg) as Wa4. jreg HS (1%bv:reg) as Wa1.
rewrite F44 in Wa10. rewrite G2 in Wa11.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Wsp : spZ (ms_regs msx) = c_sp cx) by (unfold spZ; rewrite Wa2, <- (Z_to_bv_bv_unsigned 64 (ew E1 2)), G2; apply unsigned_lit_small; lia) end.
pose proof (R4' := proj1 (proj2 (proj2 (proj2 HR1)))). cbn beta in R4'.
lazymatch type of HS with st_ok _ _ _ ?msx =>
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRg;
assert (HGB : garr8 ubs0segs (ms_mem msx) (c_sp cx + 24) ([33; 249; 4; Z.lor (c_disp cx) 1] ++ YO07.u16le (c_delay cx) ++ [c_tidx cx; 0]))
end.
{ apply gce_garr8u.
- eapply (fb_of_region _ _ _ _ _ _ _ _ 24 1%N (SLit 33) 33 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia].
- replace (c_sp cx + 24 + 1) with (c_sp cx + 25) by lia. first
[ eapply (vval_mem_of_chunk_mod ubs0segs _ _ _ 2%nat (c_sp cx) 25 1%N (SLit 18446744073709551609) 249 HRg); [reflexivity | cbv; tauto | exact G2 | vm_compute; reflexivity | cbn; lia]
| eapply (fb_of_region _ _ _ _ _ _ _ _ 25 1%N (SLit 249) 249 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia] ].
- replace (c_sp cx + 24 + 2) with (c_sp cx + 26) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 26 1%N (SLit 4) 4 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia].
- replace (c_sp cx + 24 + 3) with (c_sp cx + 27) by lia. eapply (vval_mem_of_chunk_mod ubs0segs _ _ _ 2%nat (c_sp cx) 27 1%N (SAlu ALU_OR (SOff 41%nat 0) (SLit 1)) (Z.lor (c_disp cx) 1) HRg); [reflexivity | cbv; tauto | exact G2 | | cbn; lia].
change (U E1 (SAlu ALU_OR (SOff 41 0) (SLit 1)) mod 2 ^ (8 * Z.of_N 1) = Z.lor (c_disp cx) 1). rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 41 _ F41), U_SLit by lia. change (zcanon 1) with 1.
pose proof (lor_range 8 (c_disp cx) 1 ltac:(lia) ltac:(lia)) as HL8. rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. change (2 ^ (8 * Z.of_N 1)) with 256. lia.
- pose proof (lor_range 8 (c_disp cx) 1 ltac:(lia) ltac:(lia)). lia.
- replace (c_sp cx + 24 + 4) with (c_sp cx + 28) by lia. eapply (vval_mem_of_chunk_mod ubs0segs _ _ _ 2%nat (c_sp cx) 28 2%N (SExt true 16 (SOff 39%nat 0)) (c_delay cx) HRg); [reflexivity | cbv; tauto | exact G2 | apply U_sext16_mod; [exact F39 | lia] | cbn; lia].
- lia.
- replace (c_sp cx + 24 + 6) with (c_sp cx + 30) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 30 1%N (SOff 42%nat 0) (c_tidx cx) HRg G2); [cbv; tauto | cbn [sv_denot]; rewrite F42, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- lia.
- replace (c_sp cx + 24 + 7) with (c_sp cx + 31) by lia. eapply (fb_of_region _ _ _ _ _ _ _ _ 31 1%N (SLit 0) 0 HRg G2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia]. }
assert (HGCE : ra_gce cx = [33; 249; 4; Z.lor (c_disp cx) 1] ++ YO07.u16le (c_delay cx) ++ [c_tidx cx; 0]).
{ unfold ra_gce. rewrite Hc, Ht1. rewrite (Z.mod_small (c_disp cx) 256) by lia. reflexivity. }
rewrite <- HGCE in HGB.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ2 : forall a, ~ (c_sp cx + 25 <= a < c_sp cx + 31) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs (ms_mem ms0) a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?G2 in H));
assert (Hobjs2 : objs_at (ms_mem msx) cx (c_rcur cx)) by (eapply objs_at_kept; [exact Hobjs1 | | |]; intros i Hi; apply MEQ2; lia);
assert (HSKc : sink_at ubs0_msyms (ms_mem msx) md2 (c_f cx) S)
by (apply (sink_at_frame ubs0_msyms mem2 _ md2 (c_f cx) S); [| exact HSK]; intros a Ha;
assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]);
rewrite MEQ2 by lia; apply MEQ1; lia)
end.
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (HfinA : In (c_f cx, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact Hfin]).
assert (Hgin2 : In (c_g cx, CGIF_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hgin]).
assert (Hfin2 : In (c_f cx, FILE_BLOCK) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact HfinA]).
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hrawin2 : In (c_raw cx, RAW_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hrawin]).
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2c.
assert (Hrf : c_raw cx + 48 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_raw cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_raw cx, RAW_SIZE) (c_f cx, FILE_BLOCK) HH2c Hrawin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hgf : c_g cx + 96 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_g cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_g cx, CGIF_SIZE) (c_f cx, FILE_BLOCK) HH2c Hgin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (HWv : WRITECB_STK = 528) by reflexivity.
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := c_g cx) (gvals := c_gvals cx) (src := c_sp cx + 24) (n := 8) (f := c_f cx) (S := S) (bs := ra_gce cx);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Wa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Wa10 | exact Wa11 | exact Wa12 | rewrite Wsp; exact Hspal | rewrite Wsp; lia | rewrite Wsp; lia | rewrite Wsp; lia
| rewrite Wa4, HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 4%bv 4 eq_refl), R4', Htpv; reflexivity
| exact (proj2 (proj2 Hobjs2)) | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HGB | rewrite HGCE; reflexivity
| lia | lia | lia | rewrite Wsp; lia | unfold c_nP in Hroom; lia | lia | ].
intros a Ha. destruct Ha as (r & Hr & Har). exists r. split; [right; exact Hr | exact Har]. }
cbv beta. intros c' (regsW & memW & mdW & -> & HJW & HPW & Hr10W & HSKW & HhiW & HblkW). rewrite Wsp in HhiW.
jafter_call2 HS 73%nat regsW memW HPW 0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact G2 | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [rewrite HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 9%bv 9 eq_refl), (proj1 (proj2 (proj2 HR1))); apply unsigned_lit_small; lia | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 8); [rewrite HE1, (E_reg (ms_regs ms0) cx (c_rcur cx) _ 8%bv 8 eq_refl), (proj1 (proj2 HR1)); apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_raw cx + (a - c_raw cx)) by lia. apply (HblkW (c_raw cx) RAW_SIZE (a - c_raw cx) Hrawin2); [lia|].
replace (c_raw cx + (a - c_raw cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
- eapply (region_kept_pointwise ubs0segs _ _ _ 44); [rewrite F44; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_g cx + (a - c_g cx)) by lia. apply (HblkW (c_g cx) CGIF_SIZE (a - c_g cx) Hgin2); [lia|].
replace (c_g cx + (a - c_g cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg' HS (10%bv:reg) 0 Hr10W.
lazymatch type of HS with st_ok _ _ _ ?msx => change memW with (ms_mem msx) in HJW end.
jrun_to LAWS ubs0tbl_ok HS HJW PC_T2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact G2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ (ms_regs ms0) _ [2; 3; 4; 8; 9; 22; 23; 24; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE1; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HKF.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HKF;
assert (MEQ3 : forall a, ~ (c_sp cx + 25 <= a < c_sp cx + 31) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?G2 in H));
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF
end.
assert (Hbbin2 : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
pose proof (heap_blocks_range ubs0_msyms MR LAWS L2 A2 _ md2 bb Lbb HH2c Hbbin2 ltac:(lia)) as (Rbb0 & Rbb1 & _).
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (KF_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 24 <= a < c_sp cx + 32) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (clear - MEQ3 HhiW MEQ2 MEQ1 Hsplo Hac Hsp47 HWv; intros a H1 H2; rewrite MEQ3 by lia; etransitivity; [apply (proj1 (HhiW a ltac:(lia) ltac:(lia)))|]; rewrite MEQ2, MEQ1 by lia; reflexivity);
assert (KF_cfg : forall i, 0 <= i < 40 -> mbyte ubs0segs (ms_mem msx) (c_cfp cx + i) = mbyte ubs0segs mem2 (c_cfp cx + i))
by (clear - MEQ3 HhiW MEQ2 MEQ1 Hsplo Hac Hsp47 HWv Hcfplo Hcfphi; intros i Hi; rewrite MEQ3 by lia; etransitivity; [apply (proj1 (HhiW (c_cfp cx + i) ltac:(lia) ltac:(lia)))|]; rewrite MEQ2, MEQ1 by lia; reflexivity);
assert (KF_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - MEQ3 HblkW MEQ2 MEQ1 Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hi; rewrite MEQ3 by lia; etransitivity; [apply (HblkW b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
rewrite MEQ2, MEQ1 by lia; reflexivity)
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- at_T _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) =>
exists L2, A2, (ms_regs msx), (ms_mem msx), mdW, bb, Lbb, M end.
split; [reflexivity|]. split; [exact HJW|]. split; [exact Hid|]. split; [exact HRB|].
split. { unfold ra_regs. rewrite !HKF by (cbv; tauto). exact HR1. }
split. { rewrite HKF by (cbv; tauto). rewrite HK1 by (cbv; tauto). exact G23. }
split. { rewrite HKF by (cbv; tauto). rewrite HK1 by (cbv; tauto). exact G24. }
split. { rewrite HKF by (cbv; tauto). rewrite HK1 by (cbv; tauto). exact G22. }
split; [exact HB2|]. split; [exact Hwt|].
split. { apply val_mem_word_mem. eapply (fb_of_region _ _ _ _ _ _ _ _ 8 8%N (SOff 69%nat 0) bb HRF); [ew_havoc; exact G2 | cbv; tauto | cbn [sv_denot]; ew_havoc; rewrite F69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia]. }
split. { change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in W40'. apply (proj2 (val_mem_mod _ _ _ _)). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). fold M'.
eapply (fb_of_region _ _ _ _ _ _ _ _ 16 4%N (SOff 70%nat 0) M' HRF); [ew_havoc; exact G2 | cbv; tauto | cbn [sv_denot]; ew_havoc; rewrite F70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia]. }
split; [exact HM|].
cbn [ms_mem mkst].
split. { eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; [apply KF_cfg; exact Hi | apply (KF_blk _ _ i Hrawin2); lia | apply (KF_blk _ _ i Hgin2); lia]. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply KF_stk; lia. }
split. { destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [|exact HMout].
apply (garr8_frame ubs0segs mem2 _ bb out HGout). intros a Ha. rewrite <- HMout in Ha. replace a with (bb + (a - bb)) by lia. apply (KF_blk _ _ (a - bb) Hbbin2); [lia | lia | | lia].
pose proof (heap_sep_perm ubs0_msyms MR LAWS L2 A2 _ md2 (bb, Lbb) _ (c_f cx, FILE_BLOCK) HH2c HB2 HfinA) as Hbf. cbn [fst snd] in Hbf. exact Hbf. }
split; [exact HM2|].
split. { eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply KF_stk; lia. }
split. { apply (sink_at_frame ubs0_msyms memW _ mdW (c_f cx)); [| exact HSKW]. intros a Ha.
assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
apply MEQ3; lia. }
cbn [ms_regs mkst]. jreg HS (19%bv:reg) as Q19. cbn [ms_regs mkst] in Q19.
first [exact Q19 | rewrite Q19; apply bv_eq; vm_compute; reflexivity].
-
rewrite (gce_test E (c_fattr cx) (c_rattr cx) HE34 HE46 ltac:(lia) ltac:(lia)) in Hc.
assert (HGCE : ra_gce cx = []) by (unfold ra_gce; rewrite Hc; reflexivity).
jrun_to LAWS ubs0tbl_ok HS HJ PC_T2; [wr HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 22; 23; 24; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKF.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HKF;
assert (MEQ0 : forall a, ~ (c_sp cx + 24 <= a < c_sp cx + 32) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF
end.
assert (HfinA : In (c_f cx, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact Hfin]).
assert (Hbbin2 : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2c.
pose proof (heap_blocks_range ubs0_msyms MR LAWS L2 A2 _ md2 bb Lbb HH2c Hbbin2 ltac:(lia)) as (Rbb0 & Rbb1 & _).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- at_T _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) =>
exists L2, A2, (ms_regs msx), (ms_mem msx), md2, bb, Lbb, M end.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|]. split; [exact HRB|].
split. { unfold ra_regs. rewrite !HKF by (cbv; tauto). exact HR. }
split. { rewrite HKF by (cbv; tauto). exact G23. }
split. { rewrite HKF by (cbv; tauto). exact G24. }
split. { rewrite HKF by (cbv; tauto). exact G22. }
split; [exact HB2|]. split; [exact Hwt|].
cbn [ms_mem mkst].
split. { apply val_mem_word_mem. eapply fb_kept1; [apply val_mem_word_mem; exact W32 | intros a Ha; apply MEQ0; cbn in Ha; lia]. }
split. { eapply fb_kept1; [exact W40 | intros a Ha; apply MEQ0; cbn in Ha; lia]. }
split; [exact HM|].
split. { eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ0; lia. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply MEQ0; lia. }
split. { destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [|exact HMout].
apply (garr8_frame ubs0segs mem2 _ bb out HGout). intros a Ha. apply MEQ0; lia. }
split; [exact HM2|].
split. { eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQ0; lia. }
split. { rewrite HGCE, app_nil_r. apply (sink_at_frame ubs0_msyms mem2 _ md2 (c_f cx)); [| exact HSK]. intros a Ha.
assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
apply MEQ0; lia. }
cbn [ms_regs mkst]. jreg HS (19%bv:reg) as Q19. cbn [ms_regs mkst] in Q19.
first [exact Q19 | rewrite Q19; apply bv_eq; vm_compute; reflexivity].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
