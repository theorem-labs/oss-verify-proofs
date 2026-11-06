(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/AC95.v:145-147;
   proofs/cgif/cgif_file_fuzzer/lib/A/AC9z.v:176-178; proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v at f26f9fbd8777; walks reac-pw/fuzz_pin's reac_box_catalogue 0x80f7c (fuzz_pin.asan sha256 3e4859aed23f) against lib/A/PPgCSpec.v's tpin_catalogue_specX on the CONCRETE image tfibsegs / tfibtbl_lib, so the PAImg layer is gone (paj_run_tok / paj_ret_at / pa_entry_st_ok_full / st_ok_pi -> aj_run_tok tfibtbl_lib_ok / SRr_ret_at / entry_st_ok_full / st_ok; the image atoms VAL (A_OBJ 1) and VAL (A_OBJ 30) -> the literal cells got_region and bcell_region of lib/A/ACeh.v; the result VAL CAT_OBJ -> the literal table address A_CAT_TBL); cat_pR_ok / twr_ok / cat_pR_where / cat_pR_addressable / cat_frame_zone_lo -> the contract's frame premises (In (cid, pos) own with its two bounds, afobj, the off-stack disjunction), the write to the count cell allowed by the journal through In (cid, pos) own as libreac/fuzz_knock's lib/A/APgHeard.v does (at 6ebe35ba632); tcat_post -> pin_post_simple with E = [c, c + 8); cat_mod4096_mod8 / cat_sub_mod8 dropped (no stack-range case). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgCat.v of this library, for reac-pw/fuzz_pin's image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What differs: the entry A_CATALOGUE is image B's 0x8107c (st_value of reac_box_catalogue in the unstripped twin's .symtab) and the table A_CAT_TBL is image B's 0x98000 (st_value of fuzz_catalogue, and the auipc/addi pair at 0x810b4-0x810b8); the image modules are image B's lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh YCem YCep; YCeh.ro_tfa_below_ofl for ACeh's), so got_region / bcell_region are image B's shadow-base .got cell 0x99170 and shadow-base variable 0xa16f8; the contract lib/A/PPgCSpec.v and lib/A/PPgBase.v are the same text. Image B's code adds, before the instrumented check, `andi a1,a0,7` at 0x81088 and `bnez a1,0x810c8` at 0x8108c to the trap word `unimp` at 0x810c8; the engine decides the branch not taken from the alignment fact of atom 10 (al2 = 3, paid by CA1.1 c mod 8 = 0), so the walk is still one engine run and the proof text is image A's. *)
(* reac_box_catalogue, 0x8107c, 84 bytes, 21 instructions (image B). a0 = c (the count cell, c <> 0, c mod 8 = 0,
   inside a frame (cid, pos) of the journal's own list).
     8107c addi sp,sp,-0x10 ; 81080 sd ra,8(sp)          the 16-byte frame (stack_region 16)
     81084 beqz a0,810b4                                 decided by the engine: atom 10 (= c) has the fact 4096 <= c
     81088 andi a1,a0,7                                  a1 = c mod 8 = 0: the engine folds it to 0 from atom 10's
                                                         alignment fact (al2 = 3, from CA1.1 c mod 8 = 0)
     8108c bnez a1,810c8                                 decided by the engine: not taken (the trap word 0x810c8
                                                         `unimp` is not reached)
     81090 auipc a1,0x18 ; 81094 ld a1,0xe0(a1)          a1 = the word at 0x99170 = 0xa16f8 (got_region)
     81098 ld a1,0(a1)                                   a1 = the word at 0xa16f8 = 0x7fff8000 (bcell_region 32)
     8109c-810a4 srli/add/lbu                            the shadow byte of c: 0, by the shadow entry cat_SH (afobj)
     810a8 bnez a1,810cc                                 decided by the engine: not taken (errpath_store8 not reached)
     810ac addi a1,zero,0xb ; 810b0 sd a1,0(a0)          *c = 11 (region 0, the frame object, written through own)
     810b4 auipc a0,0x17 ; 810b8 addi a0,a0,-0xb4        a0 = 0x98000 (fuzz_catalogue)
     810bc ld ra,8(sp) ; 810c0 addi sp,sp,0x10 ; 810c4 ret
   One engine run reaches the ret. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* The numerals, each read from image B (fuzz_pin.asan-ubsan, d6f83d301522; excerpt
   reac_box_catalogue.fuzz_pin.asan-ubsan.s):
   A_CATALOGUE 0x8107c: the first instruction `addi sp,sp,-0x10` of reac_box_catalogue, excerpt line 2; st_value of
     reac_box_catalogue (size 0x54 = 84 bytes, 21 words) in the unstripped twin's .symtab.
   A_CAT_TBL 0x98000: `auipc a0,0x17` at 0x810b4 (0x810b4 + 0x17000 = 0x980b4) and `addi a0,a0,-0xb4` at 0x810b8
     (0x980b4 - 0xb4 = 0x98000, st_value of fuzz_catalogue), excerpt lines 16-17.
   0x99170 (A_GOT_shadow, lib/AU/YCeh.v): `auipc a1,0x18` at 0x81090 (0x99090) and `ld a1,0xe0(a1)` at 0x81094
     (0x99090 + 0xe0 = 0x99170), excerpt lines 7-8; image B's .got entry for the shadow-base variable 0xa16f8.
   0xa16f8 (A_shadow_glob, lib/AU/YCeh.v): the word loaded from 0x99170; `ld a1,0(a1)` at 0x81098 reads it (excerpt
     line 9); it is .bss, and AR's al_const gives its value SHADOW_OFF.
   0x7fff8000 (SB, lib/AU/YCeh.v, = SHADOW_OFF by SB_SHADOW_OFF): the shadow base the code adds at 0x810a0.
   0x810c8 (the trap word `unimp`): `andi a1,a0,7` at 0x81088 and `bnez a1,810c8` at 0x8108c, excerpt lines 5-6 and 21;
     the engine folds a1 to 0 from atom 10's alignment fact (cat_facts: al2 = 3, paid by c mod 8 = 0) and decides
     the branch not taken, so the address appears in no lemma.
   0x810cc (errpath_store8): `bnez a1,810cc` at 0x810a8 and `jal 58e18` at 0x810cc, excerpt lines 13 and 22; the
     engine decides the branch not taken from cat_SH, so the address appears in no lemma.
   11 (the count): `addi a1,zero,0xb` at 0x810ac and `sd a1,0(a0)` at 0x810b0, excerpt lines 14-15.
   16 (the frame): `addi sp,sp,-0x10` at 0x8107c and `addi sp,sp,0x10` at 0x810c0, excerpt lines 2 and 19. *)
Definition A_CATALOGUE : Z := 0x8107c.
Definition A_CAT_TBL : Z := 0x98000.
Definition cat_regions : smem :=
[ YP09.mkRegion (Some 10%nat) 0 8 0 8 []; stack_region 16; got_region; bcell_region 32 ].
Definition cat_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 8) 3); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_cat : sstate := mkSS A_CATALOGUE sr_atoms cat_regions None cat_facts.
Definition cat_SH : list shent := [ mkSHE 10 0 8 ].
Definition cat_extra : list word := [Z_to_bv 64 SB].
Definition CatBx : sv := SOff 32 0.
Definition CatBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma cat_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) c cid pos,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 c -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 16 -> spZ regs <= sp0 ->
c mod 8 = 0 -> In (cid, pos) own ->
frame_addr lyc cid pos <= c -> c + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(spZ regs <= c \/ c + 8 <= spZ regs - 16) ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF c 8 ->
st_ok tfibsegs (Ereg regs cat_extra) ss_cat
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_CATALOGUE) memc (seg_rom tfibsegs)))
/\ sh_ok tfibsegs CatBx cat_SH (Ereg regs cat_extra) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c cid pos
HJ H10 Hal16 Hwlo Hwhi Hc8 Hown Hc1 Hc2 Hside HRA.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (_ & _ & HFpres & _).
destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_img B lyc Sc W memc mdc cid pos HAR Hfin) as Hoff.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs cat_extra).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (UBx : U E CatBx = SHADOW_OFF).
{ unfold CatBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (U10 : U E (SOff 10 0) = c).
{ rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
split.
- unfold ss_cat. apply (entry_st_ok_full tfibsegs); change (Ereg regs cat_extra) with E.
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + unfold cat_regions, stack_region, got_region, bcell_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Uc. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (HFpres (c + o) ltac:(lia))).
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
    * split; [unfold A_GOT_shadow; lia|]. split; [unfold A_GOT_shadow; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E _ 0 A_GOT_shadow 8 (SLit A_shadow_glob) A_shadow_glob);
      [reflexivity | unfold A_shadow_glob; zside | zside |].
      rewrite Z.add_0_l. exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kgot).
    * split; [unfold A_shadow_glob; lia|]. split; [unfold A_shadow_glob; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E _ 0 A_shadow_glob 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_l. exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold cat_regions, stack_region, got_region, bcell_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Uc, Usp.
    unfold A_GOT_shadow, A_shadow_glob.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
    revert Hside Hoff Hc1 Hc2 HF4096 HFceil Hslo Hceil Hwlo Hwhi C1 Hstk0. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cat_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uc, USB.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hc8 Hc1 Hc2 HF4096 HFceil Hslo Hceil Hshi H47 Hwlo Hwhi C1 Hstk0 Hal16. clear. intros.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
- unfold sh_ok, cat_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) memc E CatBx 10%nat c 8 c 0 8 HRA); [exact UBx | exact U10 | lia | lia |].
  cbn [Z.min Z.max]. intros x Hx.
  destruct HFapp as (HA1 & [HA2 | (HA2 & HA3)]);
  revert Hx Hc1 Hc2 HA2; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg; clear; intros; lia.
Qed.
Theorem pin_pb_catalogueX : tpin_catalogue_specX tfibsegs B MT A_CATALOGUE A_CAT_TBL.
Proof using MTL TL LAWS.
unfold tpin_catalogue_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch c cid pos
HPRE H10 Hc0 Hc8 Hown Hcid Hfal Hc1 Hc2 Hside HFOBJ.
destruct HPRE as (HJ & Hra & Hra4 & Hgp & Htp & Hch & Hal16 & Hwlo & Hwhi & Hev).
unfold T_leaf_STK in Hwlo, Hside.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (HF4096 & HFceil & _).
destruct HFOBJ as (_ & _ & HRA).
destruct (cat_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c cid pos
  HJ H10 Hal16 Hwlo Hwhi Hc8 Hown Hc1 Hc2 Hside HRA) as [HS SHOK].
remember (Ereg regs cat_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs cat_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE.
unfold cfg_at. change (w64 A_CATALOGUE) with (Z_to_bv 64 A_CATALOGUE).
(* 0x8107c .. 0x810c4: one run to the ret *)
aj_run_tok tfibtbl_lib_ok HS HJ SHOK CatBspan;
[ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat c);
  [ reflexivity
  | exact Uc
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists cid, pos;
    split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia]
  |];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [ reflexivity
  | rewrite Usp; lia
  | cbn [YP09.r_wlo]; lia
  | cbn [YP09.r_whi]; lia
  |];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_nil
| ].
(* the count cell after the store: 11 at c (region 0's chunk) *)
lazymatch goal with
| HS : st_ok _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  assert (VpR : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msc)) (c + 0) (N.to_nat 8) 11);
  [ pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msc) 0%nat _ HS eq_refl) as HR0;
    cbn [restrict ms_mem] in HR0;
    eapply (field_of_region Ex _ 10%nat c _ _ _ _ _ 0 8%N _ 11 HR0);
    [ exact Uc
    | cbn; first [ left; reflexivity | right; left; reflexivity ]
    | first [ reflexivity | vm_compute; reflexivity ]
    | zside
    | zside ]
  | ]
end.
rewrite Z.add_0_r in VpR. change (N.to_nat 8) with 8%nat in VpR.
(* every byte outside the count cell and the 16-byte frame is kept by the run *)
lazymatch goal with
| HS : st_ok _ _ _ (restrict _ ?msc), HFr : frame_of ?Ex ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c <= a < c + 8) -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) (ms_mem msc) a = aview tfibsegs (w_H W) memc a);
  [ intros a Ha HnC HnS;
    refine (kept_of_frame Ex rs (w_H W) memc (ms_mem msc)
      (fun x => (c <= x < c + 8) \/ (spZ regs - 16 <= x < spZ regs)) HFr _ a Ha _);
    [ intros bb wlo whi x Hin Hr;
      try unfold ss_cat in Hin;
      cbn [ss_mem windows map cat_regions stack_region got_region bcell_region
           YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
      destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-;
      cbn [base_val] in Hr;
      first [ rewrite Uc in Hr; left; lia
            | rewrite Usp in Hr; right; lia
            | exfalso; lia ]
    | intros [Hq | Hq]; [exact (HnC Hq) | exact (HnS Hq)] ]
  | ]
end.
(* the ret: pin_post_simple with E = [c, c + 8) and R = (a0 = A_CAT_TBL /\ the 8 bytes at c hold 11) *)
lazymatch goal with
| HS : st_ok _ ?Ex _ (restrict (w_H W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
  eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W Ex); [exact HS | reflexivity | vm_compute; reflexivity |];
  intros mat';
  red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
  split; [rewrite R1, E1, Hra; reflexivity|];
  split; [unfold EV_leaf; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|];
  split; [eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [repeat first [ apply same_io_refl
                       | eapply same_io_trans; [| apply same_io_materialized; apply same_but_materialized_wvb_any] ]|];
  split; [exact (mo_le_refl MT MTL Sc)|];
  split; [intros a Ha HnS HnC; apply HKEEP; [exact Ha | exact HnC | unfold T_leaf_STK in HnS; exact HnS]|];
  split; [rewrite R10; first [reflexivity | vm_compute; reflexivity] | exact VpR]
end.
Qed.
End d.
End b.
Print Assumptions pin_pb_catalogueX.
