(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32 YG0q YF0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0r.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem tfib_stack_malloc_at : forall ly S (W : world tfibsegs) regs mem md pos S',
ecall_pre tfibsegs B ly S W regs mem md ->
count_cid CID (frames S) < fs_frames CID ->
apath (stack_malloc CID S) [] (PFake CID pos, S') ->
SRr tfibsegs W (cfg_at tfibsegs FS_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly CID pos) /\
zero_shadow (aview tfibsegs (w_H W) mem') SHADOW_OFF (frame_addr ly CID pos) (fs_frame_bytes CID) /\
rdword (aview tfibsegs (w_H W) mem') (frame_addr ly CID pos + fs_frame_bytes CID - 8) = Some (flag_addr ly CID pos) /\
(forall a, frame_addr ly CID pos <= a < frame_addr ly CID pos + fs_frame_bytes CID -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md pos S' HPRE Hcnt Hpath.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof AF0x.Hwx_tfa as Hwx.
destruct (stack_malloc_inv CID S pos S' Hpath) as (hint' & Hprobe & HS'eq).
set (hints := fs_hint (st_fs S)) in *. set (live := fs_live (st_fs S)) in *. set (hint := znth 0 CID hints) in *.
assert (HNN : fs_frames CID = FS_N) by exact fs_frames_cid. assert (HN : FS_N = 8192) by reflexivity.
pose proof (proj1 HAR) as M.
pose proof (wfs_hints _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as [Hlen Hpos0]. fold hints in Hlen, Hpos0.
assert (Hh0 : 0 <= hint).
{ unfold hint, znth. destruct (Nat.lt_ge_cases (Z.to_nat CID) (length hints)) as [L|L]; [exact (proj1 (Forall_forall _ _) Hpos0 _ (nth_In _ 0 L)) | rewrite nth_overflow by exact L; lia]. }
destruct (fs_probe_facts _ _ _ _ _ _ Hprobe ltac:(rewrite HNN, HN; lia)) as (Hfree & Hposr & Hhh & Hposeq). rewrite HNN in Hposr, Hposeq.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e)).
{ intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)). }
pose proof (ZI (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as (HT1 & HT2 & HTz).
pose proof (ZI (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as (HF1 & HF2 & HFz).
pose proof (ZI (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as (HC1 & HC2 & HCz).
pose proof (ZI (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as (HD1 & HD2 & HDz).
cbn [fst snd] in HT1, HT2, HTz, HF1, HF2, HFz, HC1, HC2, HCz, HD1, HD2, HDz.
ceil; unfold ASAN_CEIL, kThreadObjSize, kFakeStackSize in HT1, HT2, HF1, HF2, HC1, HC2, HD1, HD2.
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kFakeStackSize in HTz, HFz, HCz, HDz.
assert (ZONE : exists hi : bool, if hi then 17594333495296 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling else 6270976 <= ly_F ly /\ ly_F ly + 11571200 <= 2147446784).
{ destruct HFz as [X|[X|X]]; [exfalso; clear - X HF1; lia | exists false; exact X | exists true; exact X]. }
destruct ZONE as [hi HZ].
clear HF1 HF2. assert (HF1 : 6270976 <= ly_F ly) by (clear - HZ; destruct hi; lia).
assert (HF2 : ly_F ly + 11571200 <= 140737479966720) by (clear - HZ; destruct hi; [ceil; lia | lia]).
assert (CE : alloc_ceiling <= 140737479966720) by (ceil; lia).
apply (fun X => Z.le_trans _ _ _ X CE) in HT2. apply (fun X => Z.le_trans _ _ _ X CE) in HC2. apply (fun X => Z.le_trans _ _ _ X CE) in HD2.
pose proof (lo_T_al ly HLY) as HTal. pose proof (lo_F_al ly HLY) as HFal. pose proof (lo_D_al ly HLY) as HDal. pose proof (lo_C_al ly HLY) as HCal.
unfold page_aligned in HTal, HFal, HDal.
pose proof (lo_disj ly HLY) as PW. unfold static_extents, owned_extents in PW. cbn [app pairwise] in PW.
destruct PW as (_ & _ & PWT & PWF & _ & _ & PWC & PWD & _).
assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize)) by (exact (Forall_inv PWT)).
assert (DTC : zdisjoint (ly_T ly, kThreadObjSize) (ly_C ly, 256)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT))))).
assert (DTD : zdisjoint (ly_T ly, kThreadObjSize) (ly_D ly, 4096)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT)))))).
assert (DTS : zdisjoint (ly_T ly, kThreadObjSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT))))))).
assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail PWF)))).
assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF))))).
assert (DFS : zdisjoint (ly_F ly, kFakeStackSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF)))))).
assert (DCD : zdisjoint (ly_C ly, 256) (ly_D ly, 4096)) by (exact (Forall_inv PWC)).
assert (DCS : zdisjoint (ly_C ly, 256) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail PWC))).
assert (DDS : zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv PWD)).
clear PWT PWF PWC PWD. unfold zdisjoint, kThreadObjSize, kFakeStackSize in DTF, DTC, DTD, DTS, DFC, DFD, DFS, DCD, DCS, DDS. cbn [fst snd] in DTF, DTC, DTD, DTS, DFC, DFD, DFS, DCD, DCS, DDS.
set (T := ly_T ly) in *. set (C := ly_C ly) in *. set (D := ly_D ly) in *. set (F := ly_F ly) in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Hslo Htop Lbeg Lhi; lia).
assert (HTPv : as_tp B = TP) by (rewrite (ts_tp B TB); reflexivity).
assert (HTSDv : ly_tsd ly = TSD) by (rewrite (am_tsd B ly S _ M), (ts_tsd B TB); reflexivity).
assert (VT0 : val_mem tfibsegs (mrestrict H mem) TP 8 F).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (ATp 0) 8 (AF 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VT8 : val_mem tfibsegs (mrestrict H mem) (TP + 8) 8 D).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (ATp 8) 8 (AD 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VD24 : val_mem tfibsegs (mrestrict H mem) (D + 24) 8 TP).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AD 24) 8 (ATp 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VTSD : val_mem tfibsegs (mrestrict H mem) TSD 8 C).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (ATsd 0) 8 (AC 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTSDv, !Z.add_0_r in V. exact V. }
assert (VC152 : val_mem tfibsegs (mrestrict H mem) (C + 152) 8 T).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AC 152) 8 (AT 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite !Z.add_0_r in V. exact V. }
assert (VT48 : val_mem tfibsegs (mrestrict H mem) (T + 48) 8 0x5d96c8).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AT 48) 8 (ANum 0x5d96c8) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. exact V. }
assert (VT56 : val_mem tfibsegs (mrestrict H mem) (T + 56) 8 0x5d97a4).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AT 56) 8 (ANum 0x5d97a4) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. exact V. }
assert (CELL : forall e (ww : nat) z, In (ACell e ww (AV (ANum z))) (fs_cells S) -> val_mem tfibsegs (mrestrict H mem) (aeval B ly e) ww z).
{ intros e ww z Hin. pose proof (cell_holds_val_mem B ly H mem e ww (ANum z) (proj1 (Forall_forall _ _) (am_cells B ly S _ M) _ (In_fs_cells_acells B ly S _ Hin))) as V. exact V. }
assert (VF88 : val_mem tfibsegs (mrestrict H mem) (F + 88) 8 20) by (exact (CELL (AF 88) 8%nat 20 ltac:(left; reflexivity))).
assert (VF96 : val_mem tfibsegs (mrestrict H mem) (F + 96) 1 0) by (exact (CELL (AF 96) 1%nat 0 ltac:(right; left; reflexivity))).
assert (VFH : val_mem tfibsegs (mrestrict H mem) (F + FS_HOFF) 8 hint).
{ refine (CELL (AF FS_HOFF) 8%nat hint _). right; right. unfold fs_cells.
change (AF FS_HOFF) with (AF (8 * Z.of_nat 1%nat)). unfold hint, znth. change (Z.to_nat CID) with 1%nat.
apply (in_map (fun iv : nat * Z => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) _ (1%nat, nth 1 hints 0)).
fold hints. rewrite <- Hlen. apply (combine_seq_nth hints 0 0 1). lia. }
set (hm := hint mod 2 ^ 64). assert (Hhm : 0 <= hm < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (VFH' : val_mem tfibsegs (mrestrict H mem) (F + FS_HOFF) 8 hm) by (exact (val_mem_mod64 _ _ _ VFH)).
assert (Hprobe' : fs_probe (Z.to_nat FS_N) live CID hm = Some (pos, hm + (hint' - hint))).
{ rewrite <- HNN. apply (fs_probe_shift _ _ _ hint); [rewrite HNN; lia | | exact Hprobe].
rewrite HNN. subst hm. change FS_N with (2 ^ 13). rewrite <- (Z.mod_mod_divide hint (2 ^ 64) (2 ^ 13)) by (first [exists (2 ^ (64 - 13)); reflexivity | lia]). reflexivity. }
set (E := Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 T) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 C) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 D) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 F) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 hm) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = T) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = C) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = D) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = F) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = hm) by (rewrite E36; apply unsigned_lit_small; lia).
assert (DEN : forall n c z, bv_unsigned (ew E n) = z -> 0 <= z + c < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (z + c)).
{ intros n c z Hn Hr. cbn [sv_denot]. rewrite Hn. reflexivity. }
assert (DEN0 : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 z).
{ intros n z Hn Hr. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : st_ok tfibsegs E ssA (restrict H (mkst regs (Z_to_bv 64 FS_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
apply (st_ok_regs tfibsegs E (mkSS FS_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite (EEreg 4%nat 4%bv eq_refl), Htp, HTPv; reflexivity) ] |]).
destruct Hr. }
unfold memA. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- assert (RO : Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region fsA_rodata)) by (exact (rodata_ok B TB fsA_rodata ly S H mem E (fsA_rodata_chk ly) M)).
assert (CK : forall base off (nn : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
val_mem tfibsegs (mrestrict H mem) (base + off) (N.to_nat nn) v -> YP09.chunk_ok tfibsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal nn e))).
{ intros. eapply (chunk_ok_val tfibsegs E); eassumption. }
change (stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: map ro_region fsA_rodata) with ([stkA; rTSD; rTP0; rTP8; rT; rC; rD; rF] ++ map ro_region fsA_rodata).
apply Forall_app. split; [|exact RO]. repeat apply Forall_cons; try apply Forall_nil.
+ unfold stkA, FS_WIN. apply (region_ok_stack tfibsegs E _ 2 sp0 (- 208)); [exact E2 | lia | lia |].
intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply HpresE. subst sp0. lia.
+ unfold rTSD, aC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold TSD.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ C); [apply (DEN0 _ C U33); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VTSD].
+ unfold rTP0, aF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold TP.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ F); [apply (DEN0 _ F U35); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VT0].
+ unfold rTP8, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold TP.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ D); [apply (DEN0 _ D U34); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VT8].
+ unfold rT, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [apply (CK T _ 8%N _ 0x5d96c8); [reflexivity | cbn; lia | cbn; lia | exact VT48]|].
apply Forall_cons; [apply (CK T _ 8%N _ 0x5d97a4); [reflexivity | cbn; lia | cbn; lia | exact VT56] | apply Forall_nil].
+ unfold rC, aC, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK C _ 8%N _ T); [apply (DEN0 _ T U32); lia | cbn; lia | cbn; lia | exact VC152].
+ unfold rD, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK D _ 8%N _ TP); [reflexivity | cbn; unfold TP; lia | cbn; lia | exact VD24].
+ unfold rF, aF, aH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35. unfold FS_HOFF.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (AF0x.apresent_writable H mem); [unfold TFIB_IMG_END; lia|].
replace (F + o) with (F + 8 + Z.of_nat (Z.to_nat (o - 8))) by lia.
eapply (AF0x.mbyte_high_apresent H mem); [unfold TFIB_IMG_END; lia|]. apply VFH'. lia. }
apply Forall_cons; [apply (CK F _ 8%N _ hm); [apply (DEN0 _ hm U36); lia | cbn; lia | cbn; lia | exact VFH']|].
apply Forall_cons; [apply (CK F _ 8%N _ 20); [reflexivity | cbn; lia | cbn; lia | exact VF88]|].
apply Forall_cons; [apply (CK F _ 1%N _ 0); [reflexivity | cbn; lia | cbn; lia | exact VF96] | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold stkA, rTSD, rTP0, rTP8, rT, rC, rD, rF, aT, aC, aD, aF, aH, fsA_rodata, icpt_rodata, ro_region, extent_of_region, FS_WIN, FS_HOFF, TSD, TP.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, U32, U33, U34, U35.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [ clear - HT1 HTz; lia | clear - HC1 HCz; lia | clear - HD1 HDz; lia | clear - HF1 HFz; lia
| clear DTF DTC DTD DTS DFC DFD DFS DCD DCS DDS HTz HFz HCz HDz; lia | clear HTz HFz HCz HDz; lia ].
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok, aT, aC, aD, aF, aH. cbn [af_lo af_hi af_al2].
rewrite E2, U32, U33, U34, U35, U36. ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kFakeStackSize, FS_WIN.
change (2 ^ 4) with 16. change (2 ^ 12) with 4096. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact HTal | exact HCal | exact HDal | exact HFal | apply Z.mod_1_r | clear HTz HFz HCz HDz; lia]. }
idtac "CHECKPOINT-1b".
clear DTF DTC DTD DTS DFC DFD DCD DCS DDS.
eapply SRr_bind; [apply (fs_phase_to W E FS_LOOP _ _ _ _ _ HS0 r_A)|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
assert (MEQA : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (F + 8 <= bv_unsigned z < F + 8 + 8) -> ms_mem msA z = mem z).
{ intros z Hz1 Hz2. apply HFA. intros Hin. destruct (memA_windows E _ Hin) as [Hw|Hw]; [rewrite E2 in Hw; unfold FS_WIN in Hw; lia | rewrite U35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFA HFrA.
pose proof shapeA_ok as SH. unfold shapeA in SH.
apply andb_prop in SH as [SH R2]. apply andb_prop in SH as [SH R8]. apply andb_prop in SH as [SH R9]. apply andb_prop in SH as [SH R10].
apply andb_prop in SH as [SH R13]. apply andb_prop in SH as [SH R14]. apply andb_prop in SH as [Rpc R12]. apply Z.eqb_eq in Rpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E eA msA r HSA). }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HSA eq_refl) as HshapeA. rewrite Rpc in HshapeA.
assert (FLAGS : forall p, 0 <= p < FS_N -> rdn tfibsegs (mrestrict H (ms_mem msA)) (Z_to_bv 64 (F + FS_FLOFF + p)) 1 = Some [Z_to_bv 8 (if mem_pos live CID p then 1 else 0)]).
{ intros p Hp. pose proof (am_flags B ly S _ M CID p ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hp)) as Hf.
unfold flag_addr, fs_flag_off in Hf. change (fs_flags_off CID) with (20480 - kFakeFlagsOff) in Hf. unfold kFakeFlagsOff in Hf. fold F in Hf.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
unfold FS_FLOFF. replace (F + 20480 + p) with (F + (4096 + (20480 - 4096) + p)) by lia.
apply (AF0x.aview_byte H). rewrite (aview_same H mem (ms_mem msA)); [exact Hf | apply MEQA; rewrite unsigned_lit_small by lia; unfold sp0 in *; lia]. }
destruct (probe_loop live (F + FS_FLOFF) (mrestrict H (ms_mem msA)) (seg_rom tfibsegs) ltac:(unfold FS_FLOFF, FS_N; lia) FLAGS
(Z.to_nat FS_N) hm (ms_regs msA) pos (hm + (hint' - hint)) Hprobe'
ltac:(rewrite (RD 12%bv _ R12); apply (DEN0 _ hm U36); lia) ltac:(rewrite (RD 14%bv _ R14); reflexivity)
ltac:(rewrite (RD 13%bv _ R13); unfold FS_FLOFF; apply (DEN _ _ F U35); lia) ltac:(rewrite (RD 10%bv _ R10); rewrite Z2Nat.id by (unfold FS_N; lia); reflexivity)
ltac:(rewrite Z2Nat.id by (unfold FS_N; lia); lia) ltac:(lia))
as (regsL & cL & HmsL & L12 & L17 & L15 & L5 & L10 & HcL & LK).
rewrite HshapeA. eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact HmsL|].
intros mdL HsbmL _. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb _ mdL HsbmL), wvb_collapse. clear HsbmL.
set (dlt := hint' - hint) in *. assert (Hdlt : 1 <= dlt) by (subst dlt; lia).
set (FLG := F + FS_FLOFF + pos). set (FF := frame_addr ly CID pos). set (SH := shadow_addr FF).
assert (HFF : FF = F + 1085440 + pos * 128) by (subst FF; rewrite frame_addr_cid; reflexivity).
assert (HB : FS_B = 128) by reflexivity. assert (HFLO : FS_FLOFF = 20480) by reflexivity.
assert (HFLG : FLG = F + 20480 + pos) by (subst FLG; reflexivity).
assert (HFFr : 6270976 <= FF /\ FF + 128 <= F + kFakeStackSize /\ FF mod 64 = 0).
{ rewrite HFF. unfold kFakeStackSize. split; [lia|]. split; [lia|].
replace (F + 1085440 + pos * 128) with ((F / 4096 * 64 + 16960 + pos * 2) * 64); [apply Z_mod_mult|].
pose proof (Z.div_mod F 4096 ltac:(lia)). lia. }
pose proof (Z.div_mod FF 8 ltac:(lia)) as HFF8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HFF8'.
assert (HF8m : F mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (F / 4096 * 512); pose proof (Z.div_mod F 4096 ltac:(lia)); lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. rewrite HF8m, Z.add_0_r in HF8. clear HF8m.
assert (HSH : SH = SHADOW_OFF + FF / 8) by reflexivity. unfold SHADOW_OFF in HSH.
assert (HSHr : AF0r.shLO hi <= SH /\ SH + 16 <= AF0r.shHI hi + 16).
{ rewrite HSH. unfold AF0r.shLO, AF0r.shHI, AF0r.FS_B, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFIB_IMG_END.
clear - HZ HFF HFFr HFF8 HFF8' Hposr HN. ceil. unfold kFakeStackSize in *. change (128 / 8) with 16. change (6270976 / 8) with 783872. destruct hi; cbn -[Z.div Z.add Z.sub Z.mul]; lia. }
assert (HSHe : 2148213760 <= SH /\ SH + 16 <= 17594333495296).
{ clear - HSHr. unfold AF0r.shLO, AF0r.shHI, AF0r.FS_B, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFIB_IMG_END in HSHr. change (128 / 8) with 16 in HSHr. change (6270976 / 8) with 783872 in HSHr. destruct hi; cbn -[Z.div Z.add Z.sub Z.mul] in HSHr; lia. }
assert (HSHF : SH + 16 <= F \/ F + 11571200 <= SH).
{ rewrite HSH. clear - HZ HFF HFFr HFF8 HFF8' Hposr HN. unfold kFakeStackSize in *. destruct hi; [left | right]; lia. }
set (EC := Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm; Z_to_bv 64 (hm + dlt - 1); w64 pos; w64 FLG; Z_to_bv 64 cL; w64 FF; w64 SH]).
assert (AGR : env_agree 37 E EC).
{ subst E EC. apply (env_agree_Ereg_app regs [w64 T; w64 C; w64 D; w64 F; w64 hm] [Z_to_bv 64 (hm + dlt - 1); w64 pos; w64 FLG; Z_to_bv 64 cL; w64 FF; w64 SH] 37). cbn. lia. }
assert (ECreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EC i = getr regs r) by (intros; subst EC; apply ew_Ereg_nat; assumption).
assert (EC2 : bv_unsigned (ew EC 2) = sp0) by (rewrite (ECreg 2%nat 2%bv eq_refl); reflexivity).
assert (V35 : bv_unsigned (ew EC 35) = F) by (subst EC; rewrite (ew_Ereg_extra regs _ 3); cbn [nth]; apply unsigned_lit_small; lia).
assert (V37 : ew EC 37 = Z_to_bv 64 (hm + dlt - 1)) by (subst EC; exact (ew_Ereg_extra regs _ 5)).
assert (V38 : bv_unsigned (ew EC 38) = pos) by (subst EC; rewrite (ew_Ereg_extra regs _ 6); cbn [nth]; apply unsigned_lit_small; lia).
assert (V39 : bv_unsigned (ew EC 39) = FLG) by (subst EC; rewrite (ew_Ereg_extra regs _ 7); cbn [nth]; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V40 : ew EC 40 = Z_to_bv 64 cL) by (subst EC; exact (ew_Ereg_extra regs _ 8)).
assert (V41 : bv_unsigned (ew EC 41) = FF) by (subst EC; rewrite (ew_Ereg_extra regs _ 9); cbn [nth]; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V42 : bv_unsigned (ew EC 42) = SH) by (subst EC; rewrite (ew_Ereg_extra regs _ 10); cbn [nth]; apply unsigned_lit_small; lia).
assert (DC0 : forall n z, bv_unsigned (ew EC n) = z -> 0 <= z < 2 ^ 64 -> sv_denot EC (SOff n 0) = Z_to_bv 64 z).
{ intros n z Hn Hr. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (INA : forall x l1 l2 l3 (l4 : list (aexp * Z)), In x l4 -> In x (l1 ++ l2 ++ l3 ++ l4)) by (intros; rewrite !in_app_iff; tauto).
assert (PRF : forall a, F <= a < F + kFakeStackSize -> apresent H mem a).
{ intros a Ha. pose proof (proj1 (Forall_forall _ _) (am_areas B ly S _ M) (AF 0, kFakeStackSize) ltac:(unfold aareas; apply INA; left; reflexivity)) as V.
specialize (V (a - F) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V. replace (ly_F ly + 0 + (a - F)) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
eapply (AF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
assert (PRS : forall a, shadow_addr (F + kFakeFramesOff) <= a < shadow_addr (F + kFakeFramesOff) + 1441792 -> apresent H mem a).
{ intros a Ha. pose proof (proj1 (Forall_forall _ _) (am_areas B ly S _ M) (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) ltac:(unfold aareas; apply INA; do 5 right; left; reflexivity)) as V.
change ((kFakeStackSize - kFakeFramesOff) / 8) with 1441792 in V.
specialize (V (a - shadow_addr (F + kFakeFramesOff)) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V.
replace (shadow_addr (ly_F ly + kFakeFramesOff) + (a - shadow_addr (F + kFakeFramesOff))) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
unfold shadow_addr, kFakeFramesOff, SHADOW_OFF in Ha. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) in Ha by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity).
eapply (AF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2 HF8; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
clear INA.
rewrite HshapeA in HSA. rewrite restrict_mkst_fx in HSA.
assert (HSC1 : st_ok tfibsegs EC ssC1 (restrict H (mkst regsL (Z_to_bv 64 FS_FOUND) (ms_mem msA) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- ssC1_eq. unfold preC1. apply st_ok_add_fact; [| reflexivity | unfold aPOS; rewrite V38; unfold FS_N; lia].
apply (st_ok_set_regs_mem tfibsegs 37 E EC eA (ms_regs msA) regsL (Z_to_bv 64 FS_LOOP) FS_FOUND
(mrestrict H (ms_mem msA)) (mrestrict H (ms_mem msA)) memC1 updC1 HSA AGR eA_atoms).
- vm_compute. reflexivity.
- intros r Hr. apply LK. unfold lkeep. repeat split; intros ->; vm_compute in Hr; discriminate Hr.
- unfold updC1, aH2, aPOS, aFLG, aCNT. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
+ rewrite L12, (DC0 _ ((hm + dlt - 1) mod 2 ^ 64)); [symmetry; apply Z_to_bv64_of_mod | rewrite V37, Z_to_bv_unsigned; reflexivity | apply Z.mod_pos_bound; lia].
+ rewrite L17. symmetry. apply DC0; [exact V38 | lia].
+ rewrite L15. rewrite (DC0 _ FLG V39); [subst FLG; reflexivity | unfold kFakeStackSize in *; lia].
+ rewrite L5. reflexivity.
+ rewrite L10. cbn [sv_denot]. rewrite V40, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-
pose proof (st_ok_agree tfibsegs 37 E EC eA _ HSA AGR eA_atoms) as HSA'.
pose proof (st_ok_mem_ok tfibsegs EC eA _ HSA') as (WFA & ROKA & PDA).
split; [vm_compute; reflexivity|]. split.
+ unfold memC1. apply Forall_cons; [refine (proj1 (Forall_forall _ _) ROKA (nth 0 (ss_mem eA) stkA) _); apply nth_In; vm_compute; repeat constructor|].
apply Forall_cons.
{ unfold rFLG, aFLG, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V39.
assert (Hfb : mbyte tfibsegs (mrestrict H (ms_mem msA)) FLG = Some (Z_to_bv 8 0)).
{ pose proof (FLAGS pos Hposr) as X. rewrite Hfree in X. apply (proj1 (rdn_mbytes tfibsegs _ 1 _ _)) in X as [_ X]. specialize (X 0%nat ltac:(lia)).
cbn [nth_error Z.of_nat] in X. rewrite Z.add_0_r in X. subst FLG. exact X. }
split; [unfold kFakeStackSize in *; lia|]. split; [unfold kFakeStackSize in *; lia|]. split.
{ intros o Ho. replace (FLG + o) with FLG by lia. eapply AF0x.mbyte_high_writable; [unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hfb]. }
apply Forall_cons; [|apply Forall_nil]. intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val Z.of_N] in Hi |- *.
exists (Z_to_bv 8 0). split; [cbn; replace i with 0 by lia; reflexivity | replace (FLG + 0 + i) with FLG by lia; exact Hfb]. }
apply Forall_forall. intros r Hr. apply in_map_iff in Hr as (i & <- & Hi). refine (proj1 (Forall_forall _ _) ROKA _ _). apply nth_In.
assert (Hi15 : (i < 15)%nat) by (clear - Hi; cbn in Hi; lia). eapply Nat.lt_le_trans; [exact Hi15|]. vm_compute. repeat constructor.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC1 in change memC1 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG DFS. unfold kFakeStackSize in *. repeat split; lia. }
idtac "CHECKPOINT-3".
eapply SRr_bind; [apply (fs_phase W EC ssC1 _ _ _ _ HSC1 r_C1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1). rewrite ?wvb_wvb in *. cbn [stC1] in HS1.
assert (MEQ1 : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> bv_unsigned z <> FLG -> ~ (F + 8 <= bv_unsigned z < F + 8 + 8) -> ms_mem ms1 z = ms_mem msA z).
{ intros z Hz1 Hz2 Hz3. apply HFm1. intros Hin. destruct (memC1_windows EC _ Hin) as [Hw|[Hw|Hw]]; [rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm1 HFrm1.
pose proof C1_facts as (PC1 & R9C1 & AT1 & RV1 & _).
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS1 RV1) as Hshape1. rewrite PC1 in Hshape1. rewrite Hshape1. rewrite Hshape1 in HS1. clear Hshape1.
assert (RD1 : forall (r : bv 5) v, reg_is eC1 (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H EC eC1 (mkst (ms_regs ms1) (Z_to_bv 64 FS_SDFF) (ms_mem ms1) (seg_rom tfibsegs)) r HS1). }
pose proof (RD1 9%bv s1C1 R9C1) as G9. rewrite (s1C1_denot EC F pos V35 V38 ltac:(lia) ltac:(lia) ltac:(unfold FS_FROFF, FS_B, kFakeStackSize in *; lia)) in G9.
unfold FS_FROFF, FS_B in G9. rewrite <- HFF in G9.
rewrite restrict_mkst_fx in HS1.
assert (HSC2 : st_ok tfibsegs EC (ssC2 hi) (restrict H (mkst (ms_regs ms1) (Z_to_bv 64 FS_SDFF) (ms_mem ms1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- (ssC2_eq hi). unfold preC2. rewrite PC1.
apply st_ok_add_fact; [| reflexivity | unfold aFF; rewrite V41; unfold AF0r.ffLO, AF0r.ffHI, AF0r.FS_B, kHighMemBeg, kLowShadowBeg; clear - HZ HFF Hposr HN CE; unfold kFakeStackSize in *; destruct hi; cbn -[Z.add Z.sub Z.mul]; lia].
apply (st_ok_set_regs_mem tfibsegs 43 EC EC eC1 (ms_regs ms1) (ms_regs ms1) (Z_to_bv 64 FS_SDFF) FS_SDFF (mrestrict H (ms_mem ms1)) (mrestrict H (ms_mem ms1)) memC2 [((9%bv : bv 5), SOff aFF 0)] HS1).
- split; [intros; reflexivity | reflexivity].
- exact AT1.
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G9. symmetry. apply (DC0 _ FF V41). unfold kFakeStackSize in *; lia.
- pose proof (st_ok_mem_ok tfibsegs EC eC1 _ HS1) as (WF1 & ROK1 & PD1).
assert (SPL1 : ss_mem eC1 = nth 0 (ss_mem eC1) stkA :: tl (ss_mem eC1)) by (vm_compute; reflexivity).
rewrite SPL1 in ROK1.
split; [vm_compute; reflexivity|]. split.
+ unfold memC2. apply Forall_cons; [exact (Forall_inv ROK1)|]. apply Forall_cons; [|exact (Forall_inv_tail ROK1)].
unfold rFF, aFF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V41.
split; [lia|]. split; [unfold FS_B; unfold kFakeStackSize in *; lia|]. split; [|apply Forall_nil].
intros o Ho. unfold FS_B in Ho. apply (AF0x.apresent_writable H); [unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia|].
apply (apresent_same H (ms_mem msA)); [apply MEQ1; rewrite unsigned_lit_small by (unfold kFakeStackSize in *; lia); lia |].
apply (apresent_same H mem); [apply MEQA; rewrite unsigned_lit_small by (unfold kFakeStackSize in *; lia); lia|]. apply PRF. lia.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC2 in change memC2 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39, ?V41.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG HFF DFS. unfold kFakeStackSize in *. repeat split; lia. }
idtac "CHECKPOINT-4".
eapply SRr_bind; [apply (fs_phase W EC (ssC2 hi) _ _ _ _ HSC2 (r_C2 hi))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HFm2 & HFrm2). rewrite ?wvb_wvb in *. rewrite (stC2_match hi) in HS2.
assert (MEQ2 : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (FF <= bv_unsigned z < FF + 128) -> bv_unsigned z <> FLG -> ~ (F + 8 <= bv_unsigned z < F + 8 + 8) ->
ms_mem ms2 z = ms_mem ms1 z).
{ intros z Hz1 Hz2 Hz3 Hz4. apply HFm2. intros Hin. destruct (memC2_windows hi EC _ Hin) as [Hw|[Hw|[Hw|Hw]]];
[rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V41 in Hw; unfold FS_B in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm2 HFrm2.
pose proof (C2_facts hi) as (PC2 & R11C2 & AT2 & RV2 & _).
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS2 RV2) as Hshape2. rewrite PC2 in Hshape2. rewrite Hshape2. rewrite Hshape2 in HS2. clear Hshape2.
assert (RD2 : forall (r : bv 5) v, reg_is (eC2 hi) (bv_unsigned r) v = true -> getr (ms_regs ms2) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H EC (eC2 hi) (mkst (ms_regs ms2) (Z_to_bv 64 FS_SDSH) (ms_mem ms2) (seg_rom tfibsegs)) r HS2). }
pose proof (RD2 11%bv a1C2 R11C2) as G11. rewrite (a1C2_denot EC FF V41 ltac:(unfold kFakeStackSize in *; lia)) in G11. unfold SHADOW_OFF in G11. rewrite <- HSH in G11.
rewrite restrict_mkst_fx in HS2.
assert (HSC3 : st_ok tfibsegs EC (ssC3 hi) (restrict H (mkst (ms_regs ms2) (Z_to_bv 64 FS_SDSH) (ms_mem ms2) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- (ssC3_eq hi). unfold preC3. rewrite PC2.
apply st_ok_add_fact; [| reflexivity | unfold aSH; rewrite V42; change (FS_B / 8) with 16; clear - HSHr; lia].
apply (st_ok_set_regs_mem tfibsegs 43 EC EC (eC2 hi) (ms_regs ms2) (ms_regs ms2) (Z_to_bv 64 FS_SDSH) FS_SDSH (mrestrict H (ms_mem ms2)) (mrestrict H (ms_mem ms2)) memC3 [((11%bv : bv 5), SOff aSH 0)] HS2).
- split; [intros; reflexivity | reflexivity].
- exact AT2.
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G11. symmetry. apply (DC0 _ SH V42). lia.
- pose proof (st_ok_mem_ok tfibsegs EC (eC2 hi) _ HS2) as (WF2 & ROK2 & PD2).
assert (SPL2 : ss_mem (eC2 hi) = nth 0 memC2e stkA :: tl memC2e) by (rewrite (eC2_mem hi); vm_compute; reflexivity).
rewrite SPL2 in ROK2.
split; [vm_compute; reflexivity|]. split.
+ unfold memC3. apply Forall_cons; [exact (Forall_inv ROK2)|]. apply Forall_cons; [|exact (Forall_inv_tail ROK2)].
unfold rSH, aSH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V42.
change (FS_B / 8) with 16. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (AF0x.apresent_writable H); [unfold TFIB_IMG_END; lia|].
apply (apresent_same H (ms_mem ms1)); [apply MEQ2; rewrite unsigned_lit_small by lia; unfold kFakeStackSize, kHighMemBeg in *; lia |].
apply (apresent_same H (ms_mem msA)); [apply MEQ1; rewrite unsigned_lit_small by lia; unfold kFakeStackSize, kHighMemBeg in *; lia |].
apply (apresent_same H mem); [apply MEQA; rewrite unsigned_lit_small by lia; unfold kFakeStackSize, kHighMemBeg in *; lia|].
apply PRS. unfold shadow_addr, kFakeFramesOff, SHADOW_OFF. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity). lia.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC3 in change memC3 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39, ?V41, ?V42.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG HFF HSHe HSHF DFS. unfold kFakeStackSize, kHighMemBeg in *. repeat split; lia. }
idtac "CHECKPOINT-5".
eapply SRr_bind; [apply (fs_phase W EC (ssC3 hi) _ _ _ _ HSC3 (r_C3 hi))|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HFm3 & HFrm3). rewrite ?wvb_wvb in *. rewrite (stC3_match hi) in HS3.
assert (MEQ3 : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 16) -> ~ (FF <= bv_unsigned z < FF + 128) ->
bv_unsigned z <> FLG -> ~ (F + 8 <= bv_unsigned z < F + 8 + 8) -> ms_mem ms3 z = ms_mem ms2 z).
{ intros z Hz1 Hz2 Hz3 Hz4 Hz5. apply HFm3. intros Hin. destruct (memC3_windows hi EC _ Hin) as [Hw|[Hw|[Hw|[Hw|Hw]]]];
[rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V42 in Hw; change (FS_B / 8) with 16 in Hw; lia | rewrite V41 in Hw; unfold FS_B in Hw; lia
| rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm3 HFrm3.
pose proof (C3_facts hi) as (ST3 & RV3 & FB3 & R10C3 & R4C3).
assert (MEQ : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 16) -> ~ (FF <= bv_unsigned z < FF + 128) ->
bv_unsigned z <> FLG -> ~ (F + 8 <= bv_unsigned z < F + 8 + 8) -> ms_mem ms3 z = mem z).
{ intros z Hz1 Hz2 Hz3 Hz4 Hz5. rewrite (MEQ3 z Hz1 Hz2 Hz3 Hz4 Hz5), (MEQ2 z Hz1 Hz3 Hz4 Hz5), (MEQ1 z Hz1 Hz4 Hz5). exact (MEQA z Hz1 Hz5). }
clear MEQ1 MEQ2 MEQ3.
eapply (SRr_ret_at tfibsegs tbl_fs tbl_fs_ok Hwx W EC); [exact HS3 | exact RV3 | rewrite (eC3_pc hi); vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (RD3 : forall (r : bv 5) v, reg_is (eC3 hi) (bv_unsigned r) v = true -> getr (ms_regs ms3) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EC (eC3 hi) ms3 r HS3). }
assert (RK3 : forall rz, In rz [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms3) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. rewrite forallb_forall in FB3. specialize (FB3 rz Hrz). cbn beta in FB3.
assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; cbn in Hrz; lia).
assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
rewrite (RD3 (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB3].
cbn [sv_denot]. rewrite (ECreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RK3 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs EC (eC3 hi) _ HS3) as (_ & ROK3 & _). change (ms_mem (restrict H ms3)) with (mrestrict H (ms_mem ms3)) in ROK3.
destruct (eC3_regions hi) as (NR0 & NR1 & NR2 & NR3 & NR4).
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR1)) as OKSH.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR2)) as OKFF.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR3)) as OKFLG.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR4)) as OKF.
unfold region_ok in OKSH, OKFF, OKFLG, OKF.
destruct rSH3_shape as (BSH & WSH1 & WSH2 & _). destruct rFF3_shape as (BFF & WFF1 & WFF2 & CFF). destruct rFLG3_shape as (BFL & WFL1 & WFL2 & CFL). destruct rF3_shape as (BF & WF1' & WF2' & CF).
rewrite BSH in OKSH. rewrite BFF in OKFF. rewrite BFL in OKFLG. rewrite BF in OKF. cbn [base_val] in OKSH, OKFF, OKFLG, OKF.
unfold aSH in OKSH. unfold aFF in OKFF. unfold aFLG in OKFLG. unfold aF in OKF. rewrite V42 in OKSH. rewrite V41 in OKFF. rewrite V39 in OKFLG. rewrite V35 in OKF.
destruct OKSH as (_ & _ & _ & CHSH). destruct OKFF as (_ & _ & _ & CHFF). destruct OKFLG as (_ & _ & _ & CHFL). destruct OKF as (_ & _ & _ & CHF).
assert (DH : sv_denot EC (SOff aH2 1) = Z_to_bv 64 (hint' mod 2 ^ 64)).
{ cbn [sv_denot]. unfold aH2. rewrite V37. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
subst dlt hm. rewrite Zplus_mod_idemp_l. replace (hint mod 2 ^ 64 + (hint' - hint) - 1 + 1) with (hint mod 2 ^ 64 + (hint' - hint)) by lia.
rewrite Zplus_mod_idemp_l, Z.mod_mod by lia. f_equal. lia. }
assert (VMH : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (F + FS_HOFF) 8 (hint' mod 2 ^ 64)).
{ apply (val_of_chunk_ok tfibsegs EC _ F FS_HOFF 8%N (SOff aH2 1) _ (proj1 (Forall_forall _ _) CHF _ (nth_error_In _ _ CF)) DH); [apply Z.mod_pos_bound; cbn; lia | cbn; lia]. }
assert (VMFL : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (FLG + 0) 1 1).
{ apply (val_of_chunk_ok tfibsegs EC _ FLG 0 1%N (SLit 1) 1 (proj1 (Forall_forall _ _) CHFL _ (nth_error_In _ _ CFL)) eq_refl); cbn; lia. }
assert (VMTR : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (FF + (FS_B - 8)) 8 FLG).
{ apply (val_of_chunk_ok tfibsegs EC _ FF (FS_B - 8) 8%N (SOff aFLG 0) FLG (proj1 (Forall_forall _ _) CHFF _ (nth_error_In _ _ CFF))); [apply (DC0 _ FLG V39); unfold kFakeStackSize in *; lia | cbn; unfold kFakeStackSize in *; lia | cbn; lia]. }
assert (ZSH : forall i, 0 <= i < 16 -> aview tfibsegs H (ms_mem ms3) (SH + i) = Some 0).
{ intros i Hi. pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
pose proof (rSH3_chunk (i / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) as HC.
pose proof (val_of_chunk_ok tfibsegs EC _ SH (8 * (i / 8)) 8%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHSH _ HC) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VM.
pose proof (aview_of_val_mem H (ms_mem ms3) _ 8 0 (Z.to_nat (i mod 8)) VM ltac:(lia)) as X.
rewrite Z2Nat.id in X by lia. replace (SH + 8 * (i / 8) + i mod 8) with (SH + i) in X by lia. rewrite X.
unfold YG0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
assert (PW : forall b, (sp0 - 208 <= b < sp0 \/ SH <= b < SH + 16 \/ FF <= b < FF + 128 \/ FLG <= b < FLG + 1 \/ F + 8 <= b < F + 8 + 8) -> apresent H (ms_mem ms3) b).
{ intros b Hb. destruct rSTK3_shape as (BS0 & WS01 & WS02).
destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 0 rSTK3 b HS3 NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EC2; unfold FS_WIN; lia | unfold TFIB_IMG_END; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 1 rSH3 b HS3 NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite V42; change (FS_B / 8) with 16; lia | unfold TFIB_IMG_END; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 2 rFF3 b HS3 NR2); [rewrite BFF, WFF1, WFF2; cbn [base_val]; unfold aFF; rewrite V41; unfold FS_B; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 3 rFLG3 b HS3 NR3); [rewrite BFL, WFL1, WFL2; cbn [base_val]; unfold aFLG; rewrite V39; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 4 rF3 b HS3 NR4); [rewrite BF, WF1', WF2'; cbn [base_val]; unfold aF; rewrite V35; unfold FS_HOFF; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia]. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 208 <= a < sp0 \/ SH <= a < SH + 16 \/ FF <= a < FF + 128 \/ FLG <= a < FLG + 1 \/ F + 8 <= a < F + 8 + 8) ->
aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem a).
{ intros a Ha Hn. apply aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; clear - Hn; lia. }
assert (NINF : ~ In (CID, pos) (frames S)) by (unfold frames; fold live; apply YG05.mem_pos_false; exact Hfree).
assert (HAR' : AR tfibsegs B ly S' W (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat' md)).
{ rewrite HS'eq. apply (astack_malloc_law_ok tfibsegs B ly S W mem md (ms_mem ms3) _ CID pos hint' HAR ltac:(unfold CID; lia) Hprobe).
all: change (w_H W) with H.
- intros k Hk. replace (ly_F ly + 8 * CID + Z.of_nat k) with (F + FS_HOFF + Z.of_nat k) by (unfold CID, FS_HOFF; subst F; lia).
rewrite (aview_of_val_mem H (ms_mem ms3) _ 8 _ k VMH Hk). unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
- rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. pose proof (aview_of_val_mem H (ms_mem ms3) _ 1 _ 0 VMFL ltac:(lia)) as X.
rewrite !Z.add_0_r in X. exact X.
- intros a Ha Hown Nh Nf Nfr Nsh. apply AVQ; [exact Ha|]. intros [Hs|[Hs|[Hs|[Hs|Hs]]]].
+ exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(clear - Hs Hslo Htop; lia) Hown).
+ apply Nsh. unfold in_zr. cbn [fst snd]. change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID / 8) with 16. fold SH. lia.
+ apply Nfr. unfold in_zr. cbn [fst snd]. change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID) with 128. lia.
+ apply Nf. rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. lia.
+ apply Nh. replace (ly_F ly) with F by reflexivity. unfold CID. lia.
- intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms3) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
assert (CS : (sp0 - 208 <= a' < sp0 \/ SH <= a' < SH + 16 \/ FF <= a' < FF + 128 \/ FLG <= a' < FLG + 1 \/ F + 8 <= a' < F + 8 + 8) \/
~ (sp0 - 208 <= a' < sp0 \/ SH <= a' < SH + 16 \/ FF <= a' < FF + 128 \/ FLG <= a' < FLG + 1 \/ F + 8 <= a' < F + 8 + 8)) by (clear; lia).
destruct CS as [CS|CS]; [apply aview_some_of_apresent; apply PW; exact CS | rewrite (AVQ a' Hr CS); exact Hv].
- apply MF. - apply MF. - apply MF.
- refine (hs_kept_gen H mem (ms_mem ms3) (fun b => sp0 - 208 <= b < sp0 \/ SH <= b < SH + 16 \/ FF <= b < FF + 128 \/ FLG <= b < FLG + 1 \/ F + 8 <= b < F + 8 + 8) _ _).
+ intros z Hz. apply MEQ; clear - Hz; lia.
+ intros b Hb. exists (ms_mem ms3). exact (PW b Hb). }
split; [exact HAR'|].
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
-
intros r Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec r 4) as [->|Hr4].
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (RD3 4%bv (SLit TP) R4C3). cbn [sv_denot]. rewrite Htp, HTPv. reflexivity.
+ apply RK3. clear - Hr Hr4. cbn. lia.
- apply with_vm_backing_same.
- rewrite (RD3 10%bv (SOff aFF 0) R10C3). apply (DC0 _ FF V41). unfold kFakeStackSize in *; lia.
- intros i Hi. change (fs_frame_bytes CID / 8) with 16 in Hi. change (shadow_of_addr SHADOW_OFF FF) with SH. exact (ZSH i Hi).
- replace (FF + fs_frame_bytes CID - 8) with (FF + (FS_B - 8)) by (change (fs_frame_bytes CID) with 128; unfold FS_B; lia).
rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. apply (AF0x.val_mem_rdword H (ms_mem ms3) _ FLG); [unfold kFakeStackSize in *; lia | exact VMTR].
- intros a Ha. apply PW. change (fs_frame_bytes CID) with 128 in Ha. lia.
- intros a Ha NS NS' Nstk. apply AVQ; [exact Ha|]. unfold ESTACK in Nstk. intros [Hs|[Hs|[Hs|[Hs|Hs]]]].
+ clear - Hs Nstk. lia.
+ apply NS. apply (own_free_frame_shadow B ly S _ CID pos a M ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hposr) NINF).
change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID / 8) with 16. fold SH. lia.
+ apply NS. apply (own_free_frame B ly S _ CID pos a M ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hposr) NINF).
change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID) with 128. lia.
+ apply NS. apply (own_F_low B ly S _ a M). fold F. unfold kFakeFramesOff. lia.
+ apply NS. apply (own_F_low B ly S _ a M). fold F. unfold kFakeFramesOff. lia.
- intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 208)) as [L|L].
+ apply (apresent_same H mem); [apply MEQ; rewrite unsigned_lit_small by (clear - Ha Hsp44; lia); clear - Ha L Hsp44 HSHe HF1 HF2 HFFr HFF HFLG Hposr HN Lbeg Hslo Htop DFS; unfold kFakeStackSize, kHighMemBeg in *; lia | apply HpresE; clear - Ha L; lia].
+ apply PW. lia.
Qed.
End f.
Corollary stack_malloc1_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> astack_malloc_realizes tfibsegs B 1.
Proof.
intros B LAWS TB ly S W regs mem md pos S' HPRE Hcnt Hpath. rewrite (ts_code B TB).
exact (tfib_stack_malloc_at B LAWS TB ly S W regs mem md pos S' HPRE Hcnt Hpath).
Qed.
End d.
