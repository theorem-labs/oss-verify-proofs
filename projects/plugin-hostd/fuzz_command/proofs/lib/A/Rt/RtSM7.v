(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the class-7 side-stack allocation contract of plugin-hostd/fuzz_command's
   __asan_stack_malloc_7 (0x40244), from cgif_rgb_fuzzer's lib/YF9c.v over the walk lib/A/Rt/RtSM7T.v, in the form of
   this tree's class-5 walk lib/A/Rt/RtSM5.v: stated over any relation ARx with the poisoned-head set Hp
   (lib/Reusable/FCiface.v), the premise AR_laws replaced by fs_iface and every AR read by the matching fs_iface field
   (image-side forms in lib/A/Rt/RtSMxA.v); the memset stretch is lib/A/Rt/RtSM7Fm.v; the image top is AF0x.TFIB_IMG_END;
   module paths; TraSyms becomes CmdBSyms; the corollaries are named cmd_stack_malloc7_contract_x (RtSMxDefs.v:24 form)
   and cmd_stack_malloc7_contract (RtStack.v:39 form, through RtSMxDefs.v:47). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtStack RtSMxDefs RtSMxA RtSM7Fm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtSM7T.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis FI : fs_iface tfibsegs B ARx.
Hypothesis TB : CmdBSyms B.
Theorem tfib_stack_malloc7_at_x : astack_malloc_sz_realizes_x tfibsegs B ARx FS_ENTRY CID.
Proof.
intros ly S Hp W regs mem md pos S' nq HPRE G10n Hnq Hnq8 Hcnt Hpath. change (fs_frame_bytes CID) with 8192 in Hnq.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof AF0x.Hwx_tfa as Hwx.
destruct (stack_malloc_inv CID S pos S' Hpath) as (hint' & Hprobe & HS'eq).
set (hints := fs_hint (st_fs S)) in *. set (live := fs_live (st_fs S)) in *. set (hint := znth 0 CID hints) in *.
assert (HNN : fs_frames CID = FS_N) by exact fs_frames_cid. assert (HN : FS_N = 128) by reflexivity.
pose proof (fi_hints _ _ _ FI ly S Hp W mem md HAR) as [Hlen Hpos0]. fold hints in Hlen, Hpos0.
assert (Hh0 : 0 <= hint).
{ unfold hint, znth. destruct (Nat.lt_ge_cases (Z.to_nat CID) (length hints)) as [L|L]; [exact (proj1 (Forall_forall _ _) Hpos0 _ (nth_In _ 0 L)) | rewrite nth_overflow by exact L; lia]. }
destruct (fs_probe_facts _ _ _ _ _ _ Hprobe ltac:(rewrite HNN, HN; lia)) as (Hfree & Hposr & Hhh & Hposeq). rewrite HNN in Hposr, Hposeq.
pose proof (fi_layout _ _ _ FI ly S Hp W mem md HAR) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof (img_cover_x B ARx FI ly S Hp W mem md HAR) as IMG.
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
assert (ZONE : exists hi : bool, if hi then kHighMemBeg <= ly_F ly /\ ly_F ly + kFakeStackSize <= alloc_ceiling
else TFIB_IMG_END <= ly_F ly /\ ly_F ly + kFakeStackSize <= kLowShadowBeg).
{ destruct HFz as [X|[X|X]]; [exfalso; clear - X HF1; lia | exists false; exact X | exists true; exact X]. }
destruct ZONE as [hi HZ]. unfold kHighMemBeg, kFakeStackSize, TFIB_IMG_END, kLowShadowBeg in HZ.
clear HF1 HF2. assert (HF1 : TFIB_IMG_END <= ly_F ly) by (unfold TFIB_IMG_END; clear - HZ; destruct hi; lia). unfold TFIB_IMG_END in HF1.
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
assert (HTSDv : ly_tsd ly = TSD) by (rewrite (fi_tsd _ _ _ FI ly S Hp W mem md HAR), (ts_tsd B TB); reflexivity).
assert (VT0 : val_mem tfibsegs (mrestrict H mem) TP 8 F).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (ATp 0) 8 (AF 0) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VT8 : val_mem tfibsegs (mrestrict H mem) (TP + 8) 8 D).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (ATp 8) 8 (AD 0) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VD24 : val_mem tfibsegs (mrestrict H mem) (D + 24) 8 TP).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (AD 24) 8 (ATp 0) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VTSD : val_mem tfibsegs (mrestrict H mem) TSD 8 C).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (ATsd 0) 8 (AC 0) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTSDv, !Z.add_0_r in V. exact V. }
assert (VC152 : val_mem tfibsegs (mrestrict H mem) (C + 152) 8 T).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (AC 152) 8 (AT 0) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite !Z.add_0_r in V. exact V. }
assert (VT48 : val_mem tfibsegs (mrestrict H mem) (T + 48) 8 T48).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (AT 48) 8 (ANum T48) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. exact V. }
assert (VT56 : val_mem tfibsegs (mrestrict H mem) (T + 56) 8 T56).
{ pose proof (const_lookup_sym_x B ARx FI TB ly S Hp W mem md (AT 56) 8 (ANum T56) HAR ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. exact V. }
assert (CELL : forall e (ww : nat) z, In (ACell e ww (AV (ANum z))) (fs_cells S) -> val_mem tfibsegs (mrestrict H mem) (aeval B ly e) ww z).
{ intros e ww z Hin. exact (cell_holds_val_mem B ly H mem e ww (ANum z) (proj1 (Forall_forall _ _) (fi_fs_cells _ _ _ FI ly S Hp W mem md HAR) _ Hin)). }
assert (VF88 : val_mem tfibsegs (mrestrict H mem) (F + 88) 8 20) by (exact (CELL (AF 88) 8%nat 20 ltac:(left; reflexivity))).
assert (VF96 : val_mem tfibsegs (mrestrict H mem) (F + 96) 1 0) by (exact (CELL (AF 96) 1%nat 0 ltac:(right; left; reflexivity))).
assert (VFH : val_mem tfibsegs (mrestrict H mem) (F + FS_HOFF) 8 hint).
{ refine (CELL (AF FS_HOFF) 8%nat hint _). right; right. unfold fs_cells.
change (AF FS_HOFF) with (AF (8 * Z.of_nat 7%nat)). unfold hint, znth. change (Z.to_nat CID) with 7%nat.
apply (in_map (fun iv : nat * Z => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) _ (7%nat, nth 7 hints 0)).
fold hints. rewrite <- Hlen. apply (combine_seq_nth hints 0 0 7). lia. }
set (hm := hint mod 2 ^ 64). assert (Hhm : 0 <= hm < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (VFH' : val_mem tfibsegs (mrestrict H mem) (F + FS_HOFF) 8 hm) by (exact (val_mem_mod64 _ _ _ VFH)).
assert (Hprobe' : fs_probe (Z.to_nat FS_N) live CID hm = Some (pos, hm + (hint' - hint))).
{ rewrite <- HNN. apply (fs_probe_shift _ _ _ hint); [rewrite HNN; lia | | exact Hprobe].
rewrite HNN. subst hm. change FS_N with (2 ^ 7). rewrite <- (Z.mod_mod_divide hint (2 ^ 64) (2 ^ 7)) by (first [exists (2 ^ (64 - 7)); reflexivity | lia]). reflexivity. }
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
assert (E10n : bv_unsigned (ew E 10) = nq) by (rewrite (EEreg 10%nat 10%bv eq_refl), G10n; apply unsigned_lit_small; lia).
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
- assert (RO : Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region fsA_rodata)) by (exact (rodata_ok_x B ARx FI TB fsA_rodata ly S Hp W mem md E (fsA_rodata_chk ly) HAR)).
assert (CK : forall base off (nn : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
val_mem tfibsegs (mrestrict H mem) (base + off) (N.to_nat nn) v -> YP09.chunk_ok tfibsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal nn e))).
{ intros. eapply (chunk_ok_val tfibsegs E); eassumption. }
change (stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: map ro_region fsA_rodata) with ([stkA; rTSD; rTP0; rTP8; rT; rC; rD; rF] ++ map ro_region fsA_rodata).
apply Forall_app. split; [|exact RO]. repeat apply Forall_cons; try apply Forall_nil.
+ unfold stkA, FS_WIN. apply (region_ok_stack tfibsegs E _ 2 sp0 (- 224)); [exact E2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia.
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
apply Forall_cons; [apply (CK T _ 8%N _ T48); [reflexivity | unfold T48; cbn; lia | cbn; lia | exact VT48]|].
apply Forall_cons; [apply (CK T _ 8%N _ T56); [reflexivity | unfold T56; cbn; lia | cbn; lia | exact VT56] | apply Forall_nil].
+ unfold rC, aC, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK C _ 8%N _ T); [apply (DEN0 _ T U32); lia | cbn; lia | cbn; lia | exact VC152].
+ unfold rD, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK D _ 8%N _ TP); [reflexivity | cbn; unfold TP; lia | cbn; lia | exact VD24].
+ unfold rF, aF, aH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35. unfold FS_HOFF.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (AF0x.apresent_writable H mem); [unfold TFIB_IMG_END; lia|].
replace (F + o) with (F + 56 + Z.of_nat (Z.to_nat (o - 56))) by lia.
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
rewrite E2, U32, U33, U34, U35, U36, E10n. ceil; unfold FS_B, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kFakeStackSize, FS_WIN.
change (2 ^ 4) with 16. change (2 ^ 12) with 4096. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact HTal | exact HCal | exact HDal | exact HFal | exact Hnq8 | apply Z.mod_1_r | clear HTz HFz HCz HDz; lia]. }
clear DTF DTC DTD DTS DFC DFD DCD DCS DDS.
eapply SRr_bind; [apply (fs_phase_to W E FS_LOOP _ _ _ _ _ HS0 r_A)|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
assert (MEQA : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) -> ms_mem msA z = mem z).
{ intros z Hz1 Hz2. apply HFA. intros Hin. destruct (memA_windows E _ Hin) as [Hw|Hw]; [rewrite E2 in Hw; unfold FS_WIN in Hw; lia | rewrite U35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFA HFrA.
pose proof shapeA_ok as SH. unfold shapeA in SH.
apply andb_prop in SH as [SH R9s]. apply andb_prop in SH as [SH R2]. apply andb_prop in SH as [SH R8]. apply andb_prop in SH as [SH R18]. apply andb_prop in SH as [SH R10].
apply andb_prop in SH as [SH R14]. apply andb_prop in SH as [SH R15]. apply andb_prop in SH as [Rpc R12]. apply Z.eqb_eq in Rpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E eA msA r HSA). }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HSA eq_refl) as HshapeA. rewrite Rpc in HshapeA.
assert (FLAGS : forall p, 0 <= p < FS_N -> rdn tfibsegs (mrestrict H (ms_mem msA)) (Z_to_bv 64 (F + FS_FLOFF + p)) 1 = Some [Z_to_bv 8 (if mem_pos live CID p then 1 else 0)]).
{ intros p Hp0. pose proof (fi_flags _ _ _ FI ly S Hp W mem md HAR CID p ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hp0)) as Hf.
unfold flag_addr, fs_flag_off in Hf. change (fs_flags_off CID) with (36608 - kFakeFlagsOff) in Hf. unfold kFakeFlagsOff in Hf. fold F in Hf.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
unfold FS_FLOFF. replace (F + 36608 + p) with (F + (4096 + (36608 - 4096) + p)) by lia.
apply (AF0x.aview_byte H). rewrite (aview_same H mem (ms_mem msA)); [exact Hf | apply MEQA; rewrite unsigned_lit_small by lia; unfold sp0 in *; lia]. }
destruct (probe_loop live (F + FS_FLOFF) (mrestrict H (ms_mem msA)) (seg_rom tfibsegs) ltac:(unfold FS_FLOFF, FS_N; lia) FLAGS
(Z.to_nat FS_N) hm (ms_regs msA) pos (hm + (hint' - hint)) Hprobe'
ltac:(rewrite (RD 12%bv _ R12); apply (DEN0 _ hm U36); lia) ltac:(rewrite (RD 15%bv _ R15); reflexivity)
ltac:(rewrite (RD 14%bv _ R14); unfold FS_FLOFF; apply (DEN _ _ F U35); lia) ltac:(rewrite (RD 10%bv _ R10); rewrite Z2Nat.id by (unfold FS_N; lia); reflexivity)
ltac:(rewrite Z2Nat.id by (unfold FS_N; lia); lia) ltac:(lia))
as (regsL & cL & HmsL & L12 & L17 & L13 & L5 & L10 & HcL & LK).
rewrite HshapeA. eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact HmsL|].
intros mdL HsbmL _. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb _ mdL HsbmL), wvb_collapse. clear HsbmL.
set (dlt := hint' - hint) in *. assert (Hdlt : 1 <= dlt) by (subst dlt; lia).
set (FLG := F + FS_FLOFF + pos). set (FF := frame_addr ly CID pos). set (SH := shadow_addr FF).
assert (HFF : FF = F + 7376896 + pos * 8192) by (subst FF; rewrite frame_addr_cid; reflexivity).
assert (HB : FS_B = 8192) by reflexivity. assert (HFLO : FS_FLOFF = 36608) by reflexivity.
assert (HFLG : FLG = F + 36608 + pos) by (subst FLG; reflexivity).
assert (HFFr : TFIB_IMG_END <= FF /\ FF + 8192 <= F + kFakeStackSize /\ FF mod 32 = 0).
{ rewrite HFF. unfold kFakeStackSize, TFIB_IMG_END. split; [lia|]. split; [lia|].
replace (F + 7376896 + pos * 8192) with ((F / 4096 * 128 + 230528 + pos * 256) * 32); [apply Z_mod_mult|].
pose proof (Z.div_mod F 4096 ltac:(lia)). lia. }
unfold TFIB_IMG_END in HFFr.
pose proof (Z.div_mod FF 8 ltac:(lia)) as HFF8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HFF8'.
assert (HF8m : F mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (F / 4096 * 512); pose proof (Z.div_mod F 4096 ltac:(lia)); lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. rewrite HF8m, Z.add_0_r in HF8. clear HF8m.
assert (HSH : SH = SHADOW_OFF + FF / 8) by reflexivity. unfold SHADOW_OFF in HSH.
assert (HSHe : 2147450880 <= SH /\ SH + 1024 <= 17594333495296).
{ rewrite HSH. clear - HZ HFF HFFr HFF8 HFF8' Hposr HN CE. unfold kFakeStackSize in *. destruct hi; lia. }
assert (HSHF : SH + 1024 <= F \/ F + 11571200 <= SH).
{ rewrite HSH. clear - HZ HFF HFFr HFF8 HFF8' Hposr HN. unfold kFakeStackSize in *. destruct hi; [left | right]; lia. }
set (EC := Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm; Z_to_bv 64 (hm + dlt - 1); w64 pos; w64 FLG; Z_to_bv 64 cL; w64 FF]).
assert (AGR : env_agree 37 E EC).
{ subst E EC. apply (env_agree_Ereg_app regs [w64 T; w64 C; w64 D; w64 F; w64 hm] [Z_to_bv 64 (hm + dlt - 1); w64 pos; w64 FLG; Z_to_bv 64 cL; w64 FF] 37). cbn. lia. }
assert (ECreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EC i = getr regs r) by (intros; subst EC; apply ew_Ereg_nat; assumption).
assert (EC2 : bv_unsigned (ew EC 2) = sp0) by (rewrite (ECreg 2%nat 2%bv eq_refl); reflexivity).
assert (V35 : bv_unsigned (ew EC 35) = F) by (subst EC; rewrite (ew_Ereg_extra regs _ 3); cbn [nth]; apply unsigned_lit_small; lia).
assert (V37 : ew EC 37 = Z_to_bv 64 (hm + dlt - 1)) by (subst EC; exact (ew_Ereg_extra regs _ 5)).
assert (V38 : bv_unsigned (ew EC 38) = pos) by (subst EC; rewrite (ew_Ereg_extra regs _ 6); cbn [nth]; apply unsigned_lit_small; lia).
assert (V39 : bv_unsigned (ew EC 39) = FLG) by (subst EC; rewrite (ew_Ereg_extra regs _ 7); cbn [nth]; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V40 : ew EC 40 = Z_to_bv 64 cL) by (subst EC; exact (ew_Ereg_extra regs _ 8)).
assert (V41 : bv_unsigned (ew EC 41) = FF) by (subst EC; rewrite (ew_Ereg_extra regs _ 9); cbn [nth]; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (EC10 : bv_unsigned (ew EC 10) = nq) by (rewrite (ECreg 10%nat 10%bv eq_refl), G10n; apply unsigned_lit_small; lia).
assert (DC0 : forall n z, bv_unsigned (ew EC n) = z -> 0 <= z < 2 ^ 64 -> sv_denot EC (SOff n 0) = Z_to_bv 64 z).
{ intros n z Hn Hr. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (PRF : forall a, F <= a < F + kFakeStackSize -> apresent H mem a).
{ intros a Ha. pose proof (fi_area_F _ _ _ FI ly S Hp W mem md HAR) as V. change (w_H W) with H in V.
specialize (V (a - F) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V. replace (ly_F ly + 0 + (a - F)) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
eapply (AF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
assert (PRS : forall a, shadow_addr (F + kFakeFramesOff) <= a < shadow_addr (F + kFakeFramesOff) + 1441792 -> apresent H mem a).
{ intros a Ha. pose proof (fi_area_Fsh _ _ _ FI ly S Hp W mem md HAR) as V. change (w_H W) with H in V.
change ((kFakeStackSize - kFakeFramesOff) / 8) with 1441792 in V.
specialize (V (a - shadow_addr (F + kFakeFramesOff)) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V.
replace (shadow_addr (ly_F ly + kFakeFramesOff) + (a - shadow_addr (F + kFakeFramesOff))) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
unfold shadow_addr, kFakeFramesOff, SHADOW_OFF in Ha. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) in Ha by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity).
eapply (AF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2 HF8; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
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
+ rewrite L13. rewrite (DC0 _ FLG V39); [subst FLG; reflexivity | unfold kFakeStackSize in *; lia].
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
assert (Hi28 : (i < 28)%nat) by (clear - Hi; cbn in Hi; lia). eapply Nat.lt_le_trans; [exact Hi28|]. vm_compute. repeat constructor.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC1 in change memC1 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG DFS. unfold kFakeStackSize in *. repeat split; lia. }
eapply SRr_bind; [apply (fs_phase W EC ssC1 _ _ _ _ HSC1 r_C1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1). rewrite ?wvb_wvb in *. cbn [stC1] in HS1.
assert (MEQ1 : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> bv_unsigned z <> FLG -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) -> ms_mem ms1 z = ms_mem msA z).
{ intros z Hz1 Hz2 Hz3. apply HFm1. intros Hin. destruct (memC1_windows EC _ Hin) as [Hw|[Hw|Hw]]; [rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm1 HFrm1.
pose proof C1_facts as (PC1 & R18C1 & AT1 & RV1 & _).
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS1 RV1) as Hshape1. rewrite PC1 in Hshape1. rewrite Hshape1. rewrite Hshape1 in HS1. clear Hshape1.
assert (RD1 : forall (r : bv 5) v, reg_is eC1 (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H EC eC1 (mkst (ms_regs ms1) (Z_to_bv 64 FS_SDFF) (ms_mem ms1) (seg_rom tfibsegs)) r HS1). }
pose proof (RD1 18%bv s2C1 R18C1) as G18. rewrite (s2C1_denot EC F pos V35 V38 ltac:(lia) ltac:(lia) ltac:(unfold FS_FROFF, FS_B, kFakeStackSize in *; lia)) in G18.
unfold FS_FROFF, FS_B in G18. rewrite <- HFF in G18.
rewrite restrict_mkst_fx in HS1.
assert (HSC2 : st_ok tfibsegs EC (ssC2 hi) (restrict H (mkst (ms_regs ms1) (Z_to_bv 64 FS_SDFF) (ms_mem ms1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- (ssC2_eq hi). unfold preC2. rewrite PC1.
apply st_ok_add_fact5; [| reflexivity | unfold aFF; rewrite V41; exact (proj2 (proj2 HFFr))
| unfold aFF; rewrite V41; unfold ffLO, ffHI, FS_B, kHighMemBeg, kLowShadowBeg; clear - HZ HFF Hposr HN CE; unfold kFakeStackSize in *; destruct hi; cbn -[Z.add Z.sub Z.mul]; lia].
apply (st_ok_set_regs_mem tfibsegs 43 EC EC eC1 (ms_regs ms1) (ms_regs ms1) (Z_to_bv 64 FS_SDFF) FS_SDFF (mrestrict H (ms_mem ms1)) (mrestrict H (ms_mem ms1)) memC2 [((18%bv : bv 5), SOff aFF 0)] HS1).
- split; [intros; reflexivity | reflexivity].
- exact AT1.
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G18. symmetry. apply (DC0 _ FF V41). unfold kFakeStackSize in *; lia.
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
eapply SRr_bind; [apply (fs_phase W EC (ssC2 hi) _ _ _ _ HSC2 (r_C2 hi))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HFm2 & HFrm2). rewrite ?wvb_wvb in *. rewrite (stC2_match hi) in HS2.
assert (MEQ2 : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> ~ (FF <= bv_unsigned z < FF + 8192) -> bv_unsigned z <> FLG -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) ->
ms_mem ms2 z = ms_mem ms1 z).
{ intros z Hz1 Hz2 Hz3 Hz4. apply HFm2. intros Hin. destruct (memC2_windows hi EC _ Hin) as [Hw|[Hw|[Hw|Hw]]];
[rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V41 in Hw; unfold FS_B in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm2 HFrm2.
assert (HFF8m : FF mod 8 = 0).
{ pose proof (Z.div_mod FF 32 ltac:(lia)) as D32. rewrite (proj2 (proj2 HFFr)), Z.add_0_r in D32. rewrite D32. replace (32 * (FF / 32)) with ((4 * (FF / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HFFn : 8 <= FF /\ FF + nq <= 2 ^ 63) by (clear - HFFr HF2 Hnq; unfold kFakeStackSize in *; lia).
set (cnt := nq / 8). assert (Hcnt8 : 1 <= cnt <= 1024) by (unfold cnt; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
pose proof (cntC2_U EC FF nq V41 EC10 (proj1 HFFn) (proj2 HFFn) HFF8m Hnq8 ltac:(lia)) as UC. fold cnt in UC.
assert (HS2c : st_ok tfibsegs EC (ssC2b hi) (restrict H ms2)).
{ rewrite <- (ssC2b_eq hi). unfold ACOND. apply (st_ok_add_cond tfibsegs EC _ _ BC_LTU cntC2 (SLit THR) HS2).
cbn [branch_taken]. rewrite bv_ltu_unsigned. apply Z.ltb_lt. change (bv_unsigned (sv_denot EC cntC2)) with (U EC cntC2). rewrite UC.
cbn [sv_denot]. unfold THR. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind; [apply (fs_phase W EC (ssC2b hi) _ _ _ _ HS2c (r_C2b hi))|].
cbv beta. intros W2b c2b _ (-> & ms2b & mat2b & -> & HS2b & HFm2b & HFrm2b). rewrite ?wvb_wvb in *. rewrite (stC2b_match hi) in HS2b.
assert (MEQ2b : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> ~ (FF <= bv_unsigned z < FF + 8192) -> bv_unsigned z <> FLG -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) ->
ms_mem ms2b z = ms_mem ms2 z).
{ intros z Hz1 Hz2 Hz3 Hz4. apply HFm2b. intros Hin. destruct (memC2b_windows hi EC _ Hin) as [Hw|[Hw|[Hw|Hw]]];
[rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V41 in Hw; unfold FS_B in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm2b HFrm2b.
pose proof (C2b_facts hi) as (_ & PC2b & RV2b & R10b & R11b & R12b & R1b & AT2b & NC2b).
assert (RD2b : forall (r : bv 5) v, reg_is (eC2b hi) (bv_unsigned r) v = true -> getr (ms_regs ms2b) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EC (eC2b hi) ms2b r HS2b). }
assert (G10b : getr (ms_regs ms2b) 10 = Z_to_bv 64 SH).
{ rewrite (RD2b 10%bv a0C2 R10b), (a0C2_denot EC FF V41 ltac:(unfold kFakeStackSize in *; lia)). rewrite HSH. reflexivity. }
assert (G12b : getr (ms_regs ms2b) 12 = Z_to_bv 64 cnt).
{ rewrite (RD2b 12%bv a2C2 R12b). rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot EC a2C2)). f_equal.
change (bv_unsigned (sv_denot EC a2C2)) with (U EC a2C2). exact (a2C2_U EC FF nq V41 EC10 (proj1 HFFn) (proj2 HFFn) HFF8m Hnq8 ltac:(lia)). }
assert (G1b : getr (ms_regs ms2b) 1 = Z_to_bv 64 FS_MSRET) by (rewrite (RD2b 1%bv (SLit FS_MSRET) R1b); reflexivity).
assert (G11b : getr (ms_regs ms2b) 11 = Z_to_bv 64 0) by (rewrite (RD2b 11%bv (SLit 0) R11b); reflexivity).
assert (MEQb : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> ~ (FF <= bv_unsigned z < FF + 8192) -> bv_unsigned z <> FLG -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) ->
ms_mem ms2b z = mem z).
{ intros z Hz1 Hz2 Hz3 Hz4. rewrite (MEQ2b z Hz1 Hz2 Hz3 Hz4), (MEQ2 z Hz1 Hz2 Hz3 Hz4), (MEQ1 z Hz1 Hz3 Hz4). exact (MEQA z Hz1 Hz4). }
clear MEQ1 MEQ2 MEQ2b.
assert (PRb : forall a, SH <= a < SH + cnt -> apresent H (ms_mem ms2b) a).
{ intros a Ha. apply (apresent_same H mem).
- apply MEQb; rewrite unsigned_lit_small by (clear - Ha HSHe Hcnt8; lia); clear - Ha HSHe HSHF Hcnt8 Hsp44 HFF HFFr HFLG Hposr HN HF1 HF2 Lbeg Hslo Htop; unfold kFakeStackSize, kHighMemBeg in *; lia.
- apply PRS. unfold shadow_addr, kFakeFramesOff, SHADOW_OFF. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity).
clear - Ha HSH HFF HFF8 HFF8' HF8 Hposr HN Hcnt8. lia. }
eapply (memset_stretch_nw W 43 EC (eC2b hi) ms2b _ SH cnt FS_MSRET _ HS2b RV2b PC2b AT2b NC2b G10b G12b G1b ltac:(lia) ltac:(unfold TFIB_IMG_END; clear - HSHe; lia)
ltac:(clear - HSHe Hcnt8; lia) ltac:(reflexivity) ltac:(unfold FS_MSRET; lia) PRb).
{
intros r Hr. destruct hi; vm_compute in Hr;
repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?EC2, ?V35, ?V39, ?V41;
clear - HSHe HSHF Hcnt8 Hsp44 HFF HFFr HFLG Hposr HN HF1 HF2 Lbeg Hslo Htop; unfold kFakeStackSize, kHighMemBeg in *; lia|]); destruct Hr. }
{ intros r a Hr Ha. destruct hi; vm_compute in Hr;
repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?EC2, ?V35, ?V39, ?V41 in Ha;
clear - Ha Hsp44 HFF HFFr HFLG Hposr HN HF1 HF2; unfold kFakeStackSize in *; lia|]); destruct Hr. }
intros regsM memM matM HSM G10M MOUT PKEEP MIN. pose proof (ssC3_eq hi) as XC3. unfold CLOB in XC3. rewrite XC3 in HSM. clear XC3. rewrite ?wvb_wvb in *.
set (EM := havoc EC 43 (map (getr regsM) [11; 12; 13; 14; 15; 16]%bv)) in *.
assert (EMold : forall i, (i < 43)%nat -> ew EM i = ew EC i) by (intros i Hi; subst EM; apply ew_havoc_old; exact Hi).
assert (EMreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EM i = getr regs r).
{ intros i r Hir. rewrite EMold; [apply ECreg; exact Hir|]. pose proof (bv_unsigned_in_range 5 r) as Rr. change (bv_modulus 5) with 32 in Rr. lia. }
assert (EM2 : bv_unsigned (ew EM 2) = sp0) by (rewrite EMold by lia; exact EC2).
assert (W35 : bv_unsigned (ew EM 35) = F) by (rewrite EMold by lia; exact V35).
assert (W37 : ew EM 37 = Z_to_bv 64 (hm + dlt - 1)) by (rewrite EMold by lia; exact V37).
assert (W39 : bv_unsigned (ew EM 39) = FLG) by (rewrite EMold by lia; exact V39).
assert (W41 : bv_unsigned (ew EM 41) = FF) by (rewrite EMold by lia; exact V41).
eapply SRr_bind; [apply (fs_phase W EM (ssC3 hi) _ _ _ _ HSM (r_C3 hi))|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HFm3 & HFrm3). rewrite ?wvb_wvb in *. rewrite (stC3_match hi) in HS3.
assert (MEQ3 : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> ~ (FF <= bv_unsigned z < FF + 8192) -> bv_unsigned z <> FLG -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) ->
ms_mem ms3 z = memM z).
{ intros z Hz1 Hz2 Hz3 Hz4. apply HFm3. intros Hin. destruct (memC3_windows hi EM _ Hin) as [Hw|[Hw|[Hw|Hw]]];
[rewrite EM2 in Hw; unfold FS_WIN in Hw; lia | rewrite W41 in Hw; unfold FS_B in Hw; lia | rewrite W39 in Hw; lia | rewrite W35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm3 HFrm3.
pose proof (C3_facts hi) as (ST3 & RV3 & FB3 & R10C3 & R4C3).
assert (MEQ : forall z : word, ~ (sp0 - 224 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + cnt) -> ~ (FF <= bv_unsigned z < FF + 8192) ->
bv_unsigned z <> FLG -> ~ (F + 56 <= bv_unsigned z < F + 56 + 8) -> ms_mem ms3 z = mem z).
{ intros z Hz1 Hz2 Hz3 Hz4 Hz5. rewrite (MEQ3 z Hz1 Hz3 Hz4 Hz5), (MOUT z Hz2). exact (MEQb z Hz1 Hz3 Hz4 Hz5). }
eapply (SRr_ret_at tfibsegs tbl_fs tbl_fs_ok Hwx W EM); [exact HS3 | exact RV3 | rewrite (eC3_pc hi); vm_compute; reflexivity |].
intros mat'. rewrite ?wvb_wvb.
assert (RD3 : forall (r : bv 5) v, reg_is (eC3 hi) (bv_unsigned r) v = true -> getr (ms_regs ms3) r = sv_denot EM v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EM (eC3 hi) ms3 r HS3). }
assert (RK3 : forall rz, In rz [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms3) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. rewrite forallb_forall in FB3. specialize (FB3 rz Hrz). cbn beta in FB3.
assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; cbn in Hrz; lia).
assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
rewrite (RD3 (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB3].
cbn [sv_denot]. rewrite (EMreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RK3 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
assert (DM0 : forall k z, bv_unsigned (ew EM k) = z -> 0 <= z < 2 ^ 64 -> sv_denot EM (SOff k 0) = Z_to_bv 64 z).
{ intros k z Hk Hr. cbn [sv_denot]. rewrite Hk, Z.add_0_r. reflexivity. }
pose proof (st_ok_mem_ok tfibsegs EM (eC3 hi) _ HS3) as (_ & ROK3 & _). change (ms_mem (restrict H ms3)) with (mrestrict H (ms_mem ms3)) in ROK3.
destruct (eC3_regions hi) as (NR0 & NR1 & NR2 & NR3).
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR1)) as OKFF.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR2)) as OKFLG.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR3)) as OKF.
unfold region_ok in OKFF, OKFLG, OKF.
destruct rFF3_shape as (BFF & WFF1 & WFF2 & CFF). destruct rFLG3_shape as (BFL & WFL1 & WFL2 & CFL). destruct rF3_shape as (BF & WF1' & WF2' & CF).
rewrite BFF in OKFF. rewrite BFL in OKFLG. rewrite BF in OKF. cbn [base_val] in OKFF, OKFLG, OKF.
unfold aFF in OKFF. unfold aFLG in OKFLG. unfold aF in OKF. rewrite W41 in OKFF. rewrite W39 in OKFLG. rewrite W35 in OKF.
destruct OKFF as (_ & _ & _ & CHFF). destruct OKFLG as (_ & _ & _ & CHFL). destruct OKF as (_ & _ & _ & CHF).
assert (DH : sv_denot EM (SOff aH2 1) = Z_to_bv 64 (hint' mod 2 ^ 64)).
{ cbn [sv_denot]. unfold aH2. rewrite W37. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
subst dlt hm. rewrite Zplus_mod_idemp_l. replace (hint mod 2 ^ 64 + (hint' - hint) - 1 + 1) with (hint mod 2 ^ 64 + (hint' - hint)) by lia.
rewrite Zplus_mod_idemp_l, Z.mod_mod by lia. f_equal. lia. }
assert (VMH : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (F + FS_HOFF) 8 (hint' mod 2 ^ 64)).
{ apply (val_of_chunk_ok tfibsegs EM _ F FS_HOFF 8%N (SOff aH2 1) _ (proj1 (Forall_forall _ _) CHF _ (nth_error_In _ _ CF)) DH); [apply Z.mod_pos_bound; cbn; lia | cbn; lia]. }
assert (VMFL : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (FLG + 0) 1 1).
{ apply (val_of_chunk_ok tfibsegs EM _ FLG 0 1%N (SLit 1) 1 (proj1 (Forall_forall _ _) CHFL _ (nth_error_In _ _ CFL)) eq_refl); cbn; lia. }
assert (VMTR : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (FF + (FS_B - 8)) 8 FLG).
{ apply (val_of_chunk_ok tfibsegs EM _ FF (FS_B - 8) 8%N (SOff aFLG 0) FLG (proj1 (Forall_forall _ _) CHFF _ (nth_error_In _ _ CFF))); [apply (DM0 _ FLG W39); unfold kFakeStackSize in *; lia | cbn; unfold kFakeStackSize in *; lia | cbn; lia]. }
assert (NW : forall b, SH <= b < SH + cnt -> ~ (sp0 - 224 <= b < sp0) /\ ~ (FF <= b < FF + 8192) /\ b <> FLG /\ ~ (F + 56 <= b < F + 56 + 8)).
{ intros b Hb. clear - Hb HSHe HSHF Hcnt8 Hsp44 HFF HFFr HFLG Hposr HN HF1 HF2 Lbeg Hslo Htop. unfold kFakeStackSize, kHighMemBeg in *. lia. }
assert (ZSH : forall i, 0 <= i < cnt -> aview tfibsegs H (ms_mem ms3) (SH + i) = Some 0).
{ intros i Hi. destruct (NW (SH + i) ltac:(lia)) as (N1 & N2 & N3 & N4). destruct (PRb (SH + i) ltac:(lia)) as [Hh _].
assert (UZ : bv_unsigned (Z_to_bv 64 (SH + i)) = SH + i) by (apply unsigned_lit_small; clear - Hi HSHe Hcnt8; lia).
unfold aview, mbyte, mrestrict. rewrite Hh. rewrite MEQ3 by (rewrite UZ; assumption). rewrite MIN by (rewrite UZ; lia). rewrite G11b. reflexivity. }
assert (PW : forall b, (sp0 - 224 <= b < sp0 \/ SH <= b < SH + cnt \/ FF <= b < FF + 8192 \/ FLG <= b < FLG + 1 \/ F + 56 <= b < F + 56 + 8) -> apresent H (ms_mem ms3) b).
{ intros b Hb. destruct rSTK3_shape as (BS0 & WS01 & WS02).
destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]].
- apply (st_ok_window_apresent H EM (eC3 hi) ms3 0 rSTK3 b HS3 NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EM2; unfold FS_WIN; lia | unfold TFIB_IMG_END; lia].
- destruct (NW b Hb) as (N1 & N2 & N3 & N4). apply (apresent_same H memM); [apply MEQ3; rewrite unsigned_lit_small by (clear - Hb HSHe Hcnt8; lia); assumption|].
apply PKEEP. apply PRb. exact Hb.
- apply (st_ok_window_apresent H EM (eC3 hi) ms3 1 rFF3 b HS3 NR1); [rewrite BFF, WFF1, WFF2; cbn [base_val]; unfold aFF; rewrite W41; unfold FS_B; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EM (eC3 hi) ms3 2 rFLG3 b HS3 NR2); [rewrite BFL, WFL1, WFL2; cbn [base_val]; unfold aFLG; rewrite W39; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EM (eC3 hi) ms3 3 rF3 b HS3 NR3); [rewrite BF, WF1', WF2'; cbn [base_val]; unfold aF; rewrite W35; unfold FS_HOFF; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia]. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 224 <= a < sp0 \/ SH <= a < SH + cnt \/ FF <= a < FF + 8192 \/ FLG <= a < FLG + 1 \/ F + 56 <= a < F + 56 + 8) ->
aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem a).
{ intros a Ha Hnw. apply aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; clear - Hnw; lia. }
assert (NINF : ~ In (CID, pos) (frames S)) by (unfold frames; fold live; apply YG05.mem_pos_false; exact Hfree).
assert (HAR' : ARx ly S' Hp W (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat' md)).
{ rewrite HS'eq. apply (fi_malloc_law _ _ _ FI ly S Hp W mem md (ms_mem ms3) _ CID pos hint' HAR ltac:(unfold CID; lia) Hprobe).
all: change (w_H W) with H.
- intros k Hk. replace (ly_F ly + 8 * CID + Z.of_nat k) with (F + FS_HOFF + Z.of_nat k) by (unfold CID, FS_HOFF; subst F; lia).
rewrite (aview_of_val_mem H (ms_mem ms3) _ 8 _ k VMH Hk). unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
- rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. pose proof (aview_of_val_mem H (ms_mem ms3) _ 1 _ 0 VMFL ltac:(lia)) as X.
rewrite !Z.add_0_r in X. exact X.
- intros a Ha Hown Nh Nf Nfr Nsh. apply AVQ; [exact Ha|]. intros [Hs|[Hs|[Hs|[Hs|Hs]]]].
+ exact (fi_stack _ _ _ FI ly S Hp W mem md a HAR ltac:(clear - Hs Hslo Htop; lia) Hown).
+ apply Nsh. unfold in_zr. cbn [fst snd]. change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID / 8) with 1024. fold SH. clear - Hs Hcnt8. lia.
+ apply Nfr. unfold in_zr. cbn [fst snd]. change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID) with 8192. lia.
+ apply Nf. rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. lia.
+ apply Nh. replace (ly_F ly) with F by reflexivity. unfold CID. lia.
- intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms3) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
assert (CS : (sp0 - 224 <= a' < sp0 \/ SH <= a' < SH + cnt \/ FF <= a' < FF + 8192 \/ FLG <= a' < FLG + 1 \/ F + 56 <= a' < F + 56 + 8) \/
~ (sp0 - 224 <= a' < sp0 \/ SH <= a' < SH + cnt \/ FF <= a' < FF + 8192 \/ FLG <= a' < FLG + 1 \/ F + 56 <= a' < F + 56 + 8)) by (clear; lia).
destruct CS as [CS|CS]; [apply aview_some_of_apresent; apply PW; exact CS | rewrite (AVQ a' Hr CS); exact Hv].
- apply MF. - apply MF. - apply MF.
- refine (hs_kept_gen H mem (ms_mem ms3) (fun b => sp0 - 224 <= b < sp0 \/ SH <= b < SH + cnt \/ FF <= b < FF + 8192 \/ FLG <= b < FLG + 1 \/ F + 56 <= b < F + 56 + 8) _ _).
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
- rewrite (RD3 10%bv (SOff aFF 0) R10C3). apply (DM0 _ FF W41). unfold kFakeStackSize in *; lia.
- intros i Hi. fold cnt in Hi. change (shadow_of_addr SHADOW_OFF FF) with SH. exact (ZSH i Hi).
- replace (FF + fs_frame_bytes CID - 8) with (FF + (FS_B - 8)) by (change (fs_frame_bytes CID) with 8192; unfold FS_B; lia).
rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. apply (AF0x.val_mem_rdword H (ms_mem ms3) _ FLG); [unfold kFakeStackSize in *; lia | exact VMTR].
- intros a Ha. apply PW. change (fs_frame_bytes CID) with 8192 in Ha. lia.
- intros a Ha NS NS' Nstk. apply AVQ; [exact Ha|]. unfold ESTACK in Nstk. intros [Hs|[Hs|[Hs|[Hs|Hs]]]].
+ clear - Hs Nstk. lia.
+ apply NS. apply (fi_own_free_frame_shadow _ _ _ FI ly S Hp W mem md CID pos a HAR ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hposr) NINF).
change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID / 8) with 1024. fold SH. clear - Hs Hcnt8. lia.
+ apply NS. apply (fi_own_free_frame _ _ _ FI ly S Hp W mem md CID pos a HAR ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hposr) NINF).
change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID) with 8192. lia.
+ apply NS. apply (fi_own_F_low _ _ _ FI ly S Hp W mem md a HAR). fold F. unfold kFakeFramesOff. lia.
+ apply NS. apply (fi_own_F_low _ _ _ FI ly S Hp W mem md a HAR). fold F. unfold kFakeFramesOff. lia.
- intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 224)) as [L|L].
+ apply (apresent_same H mem); [apply MEQ; rewrite unsigned_lit_small by (clear - Ha Hsp44; lia); clear - Ha L Hsp44 HSHe Hcnt8 HF1 HF2 HFFr HFF HFLG Hposr HN Lbeg Hslo Htop DFS; unfold kFakeStackSize, kHighMemBeg in *; lia | apply HpresE; clear - Ha L; lia].
+ apply PW. lia.
Qed.
End f.
Corollary cmd_stack_malloc7_contract_x : forall B ARx, fs_iface tfibsegs B ARx -> CmdBSyms B ->
astack_malloc_sz_realizes_x tfibsegs B ARx RtAPI.PC_stack_malloc_7 7.
Proof. intros B ARx FI TB. exact (tfib_stack_malloc7_at_x B ARx FI TB). Qed.
Corollary cmd_stack_malloc7_contract : forall B, AR_laws tfibsegs B -> CmdBSyms B -> astack_malloc_sz_realizes tfibsegs B RtAPI.PC_stack_malloc_7 7.
Proof.
intros B LAWS TB. apply (astack_malloc_sz_realizes_of_x tfibsegs B RtAPI.PC_stack_malloc_7 7).
exact (cmd_stack_malloc7_contract_x B (AR_nohp tfibsegs B) (fs_iface_AR tfibsegs B LAWS) TB).
Qed.
End d.
