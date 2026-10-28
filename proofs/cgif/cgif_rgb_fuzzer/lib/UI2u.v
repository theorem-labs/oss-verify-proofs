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
UI2s UI37 UI34.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ssT3 : sstate :=
ra_ss3 PC_T3 (sr_set (sr_set sr_atoms 18%bv (SOff 44%nat 0)) 20%bv (SLit ubs2_A_cgif_writecb)) enc_chunks true
[(70%nat, mkAF 0 (2^32-1) 0); (69%nat, mkAF 4096 CEIL_MAX 4)] [] [].
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma ra_t3 : forall cx L A mem md regs0 c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
at_T3 API cx L A mem md regs0 c1 ->
SR ubs2segs c1 (ra_post API cx L A mem md regs0).
Proof.
intros cx L A mem md regs0 c1 Hcx HO HB
(L2 & A2 & regs2 & mem2 & md2 & bb & Lbb & M & -> & HJ & Hid & G2 & G8 & G4 & G3 & G27 & G18 & G21 & HB2 & Hwt & W32 & W40 & HM & Hobjs & HFS).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & Hbb16).
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hrawin2 : In (c_raw cx, 48) (blocks L2 A2)) by (rewrite <- HRSv; eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hrawin]).
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (W40' : val_mem ubs2segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_rv regs2 cx (c_rcur cx) [bb; M']) as HY. rewrite <- HE0 in HY.
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (HS : st_ok ubs2segs E ssT3 (mkst regs2 (Z_to_bv 64 PC_T3) mem2 (seg_rom ubs2segs))).
{ subst E. unfold ssT3.
apply (ra_st_ok3 cx (c_rcur cx) regs2 [bb; M'] mem2 PC_T3 _ true _ _ [] [] Hcx Hobjs G2 G8); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite HE44, unsigned_lit_small, Z.add_0_r by lia; exact G18] | intros X; discriminate X | cbn [sv_denot]; exact G21].
- intros a Ha. apply Hstw. lia.
- intros _ a Ha. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 (c_raw cx) 48 (a - c_raw cx) HH2 Hrawin2 ltac:(lia))) || (replace a with (c_raw cx + (a - c_raw cx)) by lia; apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 (c_raw cx) 48 (a - c_raw cx) HH2 Hrawin2 ltac:(lia)))).
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2]. rewrite HE70, HE69, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; first [lia | exact Hbb16].
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T3) mem2 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ eapply ra_wr_ok3; [exact HE2 | lia | lia | right].
split; [rewrite HE8; apply unsigned_lit_small; lia|]. split; [exact Hrawin2|]. split; [lia|]. split; [lia|].
intros a Ha. exists (c_raw cx + 40, c_raw cx + 44). split; [left; reflexivity | cbn; lia]. }
jreg HS (10%bv:reg) as K10. rewrite HE69 in K10.
jreg HS (2%bv:reg) as K2. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in K2.
jreg HS (4%bv:reg) as K4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htpv in K4.
jreg HS (1%bv:reg) as K1.
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
let cs := eval vm_compute in (r_chunks (nth 1 (ss_mem ssx) (R_raw true))) in
lazymatch cs with context [mkChunk 40 (CVal 4 ?e)] =>
pose proof (st_ok_region_nth _ _ _ 1%nat _ HS eq_refl) as HRr;
assert (Vcur : val_mem ubs2segs (ms_mem msx) (c_raw cx + 40) 4 (U E e mod 2 ^ (8 * Z.of_N 4)));
[ destruct HRr as (_ & _ & _ & Hcs); cbn [r_chunks r_base base_val] in Hcs; rewrite HE8, unsigned_lit_small in Hcs by lia;
eapply (val_of_chunk_ok_mod _ _ _ 40 4%N e (U E e)); [eapply (proj1 (Forall_forall _ _) Hcs); cbv; tauto | apply denot_lit_U | let UR := fresh in pose proof (U_range E e) as UR; unfold M64 in UR; lia | cbn; lia]
| ]
end end.
set (cur' := U E _ mod 2 ^ (8 * Z.of_N 4)) in Vcur.
assert (Hcur' : 0 <= cur' < 2 ^ 32) by (subst cur'; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); apply Z.mod_pos_bound; lia).
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msA end.
assert (MEQA : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - 16 <= a < c_sp cx + 48) -> ~ (c_raw cx + 40 <= a < c_raw cx + 44) ->
mbyte ubs2segs (ms_mem msA) a = mbyte ubs2segs mem2 a).
{ intros a Ha Hn1 Hn2. mbyte_chain ltac:(fun H => rewrite ?HE2, ?HE8 in H). }
assert (HORA : obj_at ubs2segs (ms_mem msA) (c_raw cx) LAY_Raw (rvals' cx cur')).
{ eapply obj_at_raw_cur; [exact (proj1 (proj2 Hobjs)) | | exact Vcur | exact Hcur']. intros i Hi. apply MEQA; lia. }
assert (HFSA : frame_savedN ubs2_msyms 12 regs0 (ms_mem msA) (spZ regs0)).
{ eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]. intros a Ha. apply MEQA; lia. }
eapply SR_bind.
{ eapply (jfree_tok _ _ LAWS ubs2_errno_low_lzw IMG (aa_free API) (aa_free_null API)) with (a := bb) (n := Lbb) (spc := c_sp cx);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | | exact K10 | exact K2 | lia | exact Hspal | lia | lia | exact K4 | exact K1 | apply ret_ok_even; vm_compute; reflexivity ].
right. split; [exact Hbbin|]. eapply ftok_of_wtok; [exact Hwt | lia | lia]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & Hid3 & HP3 & Hrm & Hkeep3 & Hhi3).
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, Hrm.
destruct Hrm as [[Hz _] | [_ Hrm]]; [lia|].
assert (HB3 : Permutation (blocks L3 A3) (blocks L A)) by (eapply perm_after_rm1; [exact HB2 | exact Hrm]).
assert (Hrawin3 : In (c_raw cx, 48) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | rewrite <- HRSv; exact Hrawin]).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (MHI3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp cx - 8192 <= a < c_sp cx) -> mbyte ubs2segs mem3 a = mbyte ubs2segs (ms_mem msA) a).
{ intros a Ha Hna. apply (proj1 (Hhi3 a Ha Hna)). }
assert (HOR3 : obj_at ubs2segs mem3 (c_raw cx) LAY_Raw (rvals' cx cur')).
{ eapply obj_at_transport_range; [exact HORA | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply (Hkeep3 _ _ i Hrawin3). lia. }
assert (HFS3 : frame_savedN ubs2_msyms 12 regs0 mem3 (spZ regs0)).
{ eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFSA|]. intros a Ha. apply MHI3; lia. }
assert (HP3' : forall r : reg, In r [2; 3; 4; 8; 27]%bv -> getr regs3 r = getr regs2 r).
{ intros r Hr. rewrite <- (HK r Hr).
cbv [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
[exact (HP3 2 ltac:(cbv; lia)) | exact (HP3 3 ltac:(cbv; lia)) | exact (HP3 4 ltac:(cbv; lia)) | exact (HP3 8 ltac:(cbv; lia))
| exact (HP3 27 ltac:(unfold callee_saved; lia))]. }
clear HS.
remember (Ereg regs3 (map (Z_to_bv 64) (rvals' cx cur') ++ [])) as E3 eqn:HE3.
assert (X8 : ew E3 8 = Z_to_bv 64 (c_raw cx)) by (subst E3; rewrite (ew_Ereg_nat regs3 _ 8 8%bv) by reflexivity; rewrite HP3' by (cbv; tauto); exact G8).
assert (HS : st_ok ubs2segs E3 (mkSS (RA0 + 0x5c4) sr_atoms [YQ0b.mkRegion (Some 8%nat) 0 RAW_SIZE 0 0 (obj_chunks_gen LAY_Raw 32 lits_Raw)] None
(mkFacts [(8%nat, mkAF 4096 (CEIL_MAX - 48) 4)] [] []))
(mkst regs3 (Z_to_bv 64 (RA0 + 0x5c4)) mem3 (seg_rom ubs2segs))).
{ subst E3. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs2segs _ mem3 8 (c_raw cx)); [rewrite X8; apply unsigned_lit_small; lia | lia | lia | exact HOR3 | reflexivity | | apply lits_Raw_ok; reflexivity | intros i Hi; lia].
intros jj v Hj. apply Ereg_vals. exact Hj.
- cbn. repeat split.
- cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2]. rewrite X8, unsigned_lit_small by lia.
change (2 ^ 4) with 16. repeat split; first [lia | exact Hraw16]. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (RA0 + 0x5c4)) mem3 (seg_rom ubs2segs))) in HJ3.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_RET; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ [2; 3; 4; 27]%bv HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK3.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs2segs (ms_mem msF) a = mbyte ubs2segs mem3 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (ra_ret API IMG cx L A mem md L3 A3 md3 regs0 (ms_regs msF) (ms_mem msF) cur' (getr (ms_regs msF) 18));
[ exact (proj1 Hcx) | exact HO | exact HJ3 | exact Hid3 | exact HB3 | | | | | | | reflexivity ]; cbn [ms_regs ms_mem].
- eapply obj_at_transport_range; [exact HOR3 | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply MEQ3. lia.
- eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS3|]. intros a Ha. apply MEQ3; lia.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). exact G2.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). rewrite G3, Hgp0. reflexivity.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). rewrite G4, Htp0. reflexivity.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). rewrite G27, H27o. reflexivity.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
