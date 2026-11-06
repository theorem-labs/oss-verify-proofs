(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan, sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): 0x80b44 -> the
   cut P1 at 0x80c4c (lib/A/PPgParseCx.v ss_P1). rule 24: no function proved (a segment of the walk).

   What changed against the donor, each read from the neutral excerpt of 0x80b44-0x80c48:
   - the function is a callee: the start is the contract's premises (PPgParseCx.v pp_pre, the caller's journal of
     pin_pre_kit) and the entry state ss_pp0 (pp_entry), not afn_pre / ajournal_init; every write of the walk is
     allowed by that journal (the save area lies in [sp0 - STK, sp0), the frame is in the journal's own list
     after the call).
   - 160-byte save area (`addi sp,sp,-0xa0` 0x80b44, `sd zero,0(sp)` at sp-160, ra .. s11 at sp-8 .. sp-104),
     `andi sp,sp,-0x20` at 0x80b84: sp1 = 32 * ((sp - 160) / 32) in [sp - 176, sp - 160] (donor: 192 / 208);
     the stack region is trimmed to the saves [-104, 0) (donor :228-234) and region 70 = [sp1+8, sp1+56) holds the
     spill of F at sp1+0x30 (donor :235-246 [16, 88)).
   - the GOT loads at 0x80b94-0x80ba8 (0x990a8 -> 0xa1600, the option word 1; 0x99050 -> 0xa15f8, SB into s3),
     `beqz a2` at 0x80bb0 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80bb4 / 0x80bb8 (RA
     0x80bbc): the class-0 call through aj_stack_malloc_atS with ASM0, its premises the call-site lemma
     pin_fs0_site below (count_cid 0 (frames Sc) < fs_frames 0 is the contract's premise).
   - the class-0 frame: 64 bytes, 8 shadow bytes, the flag pointer at F + 56 (donor class 1: 128 / 16 / F + 120).
   - 0x80bbc-0x80c48: `bnez s2` at 0x80bcc decided by HPTR 5 on F (the probe loop 0x80bd0-0x80be8 is not reached),
     `sd s11,0x30(s1)`, the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80b44, s4 = SB + F/8, the 8
     shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80c4c (the donor's size split has no
     counterpart here).
   - the hand-off is the continuation pp_from ss_P1 INV_P1 (PPgParseCx.v): the frame's shadow region made
     read-only, the four cell regions dropped, and the kept-memory fact (lib/Reusable/YCbq.v acall_kept, the
     form of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParse.v at 6ebe35ba632) carried from the entry memory
     through every step (lib/A/PPgParseLib.v pz_kept_refl / pz_kept_run / pz_kept_trans / pz_kept_own). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse0.v, with its module paths and numbers changed; 728 of its 779 lines of code are new or changed and 342 lines of the source are left out. *)
(* check_text_scribble (fuzz_codec.c:431-452) at image A 0x83798: the walk from the entry to the
   record point 0x83998 and to the head of the inlined owed_scribble_text at 0x838d0. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
check_text_scribble_A_R check_text_scribble_A_P check_text_scribble_A_XJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ABC : abcmp_realizes tfibsegs B A_BCMP.

Lemma cts_pre_holds :
astack_malloc_realizes tfibsegs B 0 -> stack_malloc_progressP B ->
aintrin_realizes tfibsegs B OSet A_MEMSET ->
cdc_scribble_text_specX tfibsegs B MT A_SCRIBBLE_TEXT ->
(forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q,
   cts_loop_goal B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
     S2 fpos SP1 E0 Q) ->
cdc_check_text_scribble_specX tfibsegs B MT A_CHECK_TEXT_SCRIBBLE.
Proof using MTL MTF TL LAWS ML ASF FFL ABC.
intros ASM0 SMP AMS SCR LOOP.
unfold cdc_check_text_scribble_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
  HE H10 Hstr Hoq Hoch H11 Hdst Hgj Hcjl H12 Hn Hdisj Howe Hfr.
(* the entry journal stays as HJ0; the runs take the newest journal, HJ *)
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as HJ1. rename HJ into HJ0. rename HJ1 into HJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble HE
  ltac:(unfold T_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_text_scribble, ESTACK in *.
assert (HS : st_ok tfibsegs (Ereg regs (cw_extra []))
  (mkSS A_CHECK_TEXT_SCRIBBLE sr_atoms (cw_regs 128 ++ cts_rs0) None (mkFacts (cw_atoms ++ cts_af0) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_TEXT_SCRIBBLE) memc (seg_rom tfibsegs)))).
{ apply (cw_entry B TL LAWS A_CHECK_TEXT_SCRIBBLE 128 [] cts_rs0 cts_af0 lyc Sc W regs memc mdc HAR ltac:(lia)).
  - lia.
  - exact Hal.
  - intros a Ha. apply Hpres. lia.
  - vm_compute. reflexivity.
  - destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (_ & Kuar & _ & Kguar).
    rewrite (tl_got_uar B TL), (tl_uar_cell B TL) in Kguar. rewrite (tl_uar_cell B TL) in Kuar.
    unfold cts_rs0, uar_got_region, uar_cell_region. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 A_GOT_uar 8 (SLit A_uar_glob) A_uar_glob);
      [reflexivity | unfold A_uar_glob; zside | zside |].
      rewrite Z.add_0_l. exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kguar).
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 A_uar_glob 4 (SLit 1) 1);
      [reflexivity | zside | zside |].
      rewrite Z.add_0_l. exact (val_mem_of_rd32 tfibsegs (w_H W) memc _ _ Kuar).
  - unfold cw_regs, stack_region, got_region, bcell_region, cts_rs0, uar_got_region, uar_cell_region.
    cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl).
    change (bv_unsigned (getr regs 2)) with (spZ regs).
    unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob. repeat split; lia.
  - cbn [cts_af0 atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r.
    repeat split; first [lia | apply Z.mod_1_r]. }
remember (Ereg regs (cw_extra [])) as E0 eqn:HE0 in HS.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hnn; rewrite HE0; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E0 32 = Z_to_bv 64 SB) by (rewrite HE0; apply cw_ew_SB).
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E0) by (rewrite HE0; apply env_agree_refl).
clear HE0.
assert (E1 : ew E0 1 = getr regs 1) by exact (EE 1%nat 1%bv eq_refl).
assert (E2 : ew E0 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (B2 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite E2; reflexivity).
assert (AG : forall nn, (nn < 33)%nat -> ew E0 nn = ew E0 nn) by (intros; reflexivity).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8352 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_TEXT_SCRIBBLE) with (Z_to_bv 64 A_CHECK_TEXT_SCRIBBLE).
(* 0x83798-0x83804: the prologue, the two .got loads, the cell's 1 decides the test, a0 = 64, jal 0x3d0fc *)
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) 8352
  (fun x => ch <= x < ch + 24) HJ0 ltac:(lia) ltac:(lia)) as KT.
cw_run cw_awr_stk.
cpw_keep cw_kwr_stk. cw_norm_model.
set (SP1 := 32 * ((spZ regs + -128) / 32)).
destruct (sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold SP1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= SP1 <= spZ regs - 128) by lia. clear Hsp1r.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 SP1)
(cts_denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 SP1)
(eq_trans (U_inj Ev _ _ (cts_U_add0 Ev _))
(cts_denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia))) R9 end.
(* sp = s1 = SP1: the fresh atom 33 *)
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 33 Ev (havoc Ev 33 [Z_to_bv 64 SP1]) ssv msv HS
(env_agree_havoc_ge 33 33 Ev Ev _ ltac:(lia) (env_agree_refl 33 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E33 : ew Ev 33 = Z_to_bv 64 SP1)
  by (rewrite HEv; exact (ew_havoc_new _ 33 [Z_to_bv 64 SP1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (U33 : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
assert (B2v : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2);
assert (E32v : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 33 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, R2; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (9%bv : bv 5) (SOff 33 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact R9)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
(* the fact of SP1, the save area trimmed to [sp - 96, sp), the spill slot 24(s1) *)
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 33 (mkAF (2 ^ 46 - 256) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-96) 0) in
pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS
  ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk1 & _).
pose proof Hstk1 as (Hsp0al & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 33%nat) 24 32 24 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U33; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply Hpres1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U33, B2v; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
(* 0x83808 jal 0x3d0fc: the class-0 side-stack frame request *)
rreg HS (1%bv : bv 5) R1. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
pose proof (cts_count_le 0 (frames Sc)) as Hcnt.
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
replace 250108 with (pc_stack_malloc (as_code B) 0) by (rewrite (tl_code B TL); reflexivity);
eapply SRr_bind;
[ eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS tfib_segs_low (tl_env B TL) ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (SP1 - sp0) (Z_to_bv 64 538636) HJ)
| ] end.
- unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
- lia.
- unfold ESTACK. lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1.
- apply ret_ok_even. vm_compute. reflexivity.
- change (fs_frames 0) with 16384. lia.
- cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin
    & Hnev2 & Hbb2 & Hz & Hflag & HK & HSf & HKown & HIOf).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  replace (sp0 + (SP1 - sp0)) with SP1 in HK, HKown by lia.
  assert (HKA : tcj_kept tfibsegs B ESTACK lyc Sc W (ms_mem ms) W mem2 SP1 (fun _ => False)).
  { eapply (cw_tcj_of_acall B ESTACK lyc Sc W (ms_mem ms) W mem2 SP1 (SP1 - ESTACK) SP1 (fun _ => False));
    [lia | lia | exact HK | intros a Ha; apply Hpres2; unfold ESTACK in *; lia]. }
  pose proof (cw_kept_call B 8352 lyc Sc W memc W (ms_mem ms) mem2 (spZ regs) (SP1 - ESTACK) SP1
    (fun x => ch <= x < ch + 24) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia) KT HK) as KT2.
  clear KT. rename KT2 into KT.
  aconstsF HJ Kgot1 Kcell1 Kguar1 Kuar1. aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (RK0 : region_kept tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2)
     (YP09.mkRegion (Some 33%nat) 24 32 24 32 []))
    by (eapply (region_kept_tcj_stack B Ev ESTACK lyc Sc W (ms_mem ms) W mem2 SP1 (fun _ => False) 33 24 32 24 32 [] SP1 HKA U33);
        intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; unfold ESTACK in *;
        repeat split; first [lia | intros []]);
  assert (RK1 : region_kept tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2)
     (YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0
       [YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
        YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
        YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
        YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
        YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
        YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]))
    by (eapply (region_kept_tcj_stack B Ev ESTACK lyc Sc W (ms_mem ms) W mem2 SP1 (fun _ => False) 2 (-96) 0 (-96) 0 _ (spZ regs) HKA B2v);
        intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; unfold ESTACK in *;
        repeat split; first [lia | intros []]);
  assert (RK2 : region_kept tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) got_region)
    by (unfold got_region; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot1 | exact Kgot2 | lia]);
  assert (RK3 : region_kept tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) (bcell_region 32))
    by (unfold bcell_region; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell1 | exact Kcell2 | lia]);
  assert (RK4 : region_kept tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) uar_got_region)
    by (unfold uar_got_region; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar1 | exact Kguar2 | lia]);
  assert (RK5 : region_kept tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) uar_cell_region)
    by (unfold uar_cell_region; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar1 | exact Kuar2 | lia]) end.
  reseat HS HJ2 HP2 [0;1;2;3;4;5]%nat AG
    ltac:(idtac; first [exact RK0 | exact RK1 | exact RK2 | exact RK3 | exact RK4 | exact RK5]).
  cw_norm_model.
  (* the frame F, its flag address FL and its shadow base: the atoms 38 (a0), 60 and 61 *)
  assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds tfibsegs B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
  destruct (frame_al64 tfibsegs B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
  pose proof (frm_off_img B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as HFimg.
  destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLce)).
  change (fs_frame_bytes 0) with 64 in *.
  set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite (Z.div_mod F 64) at 1 by lia; rewrite HF64, Z.add_0_r;
        replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
  assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. fold F in RF.
  symmetry in RF. unfold w64 in RF.
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_agree tfibsegs 60 Ev (havoc Ev 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) ssv msv HS
  (env_agree_havoc_ge 60 60 Ev Ev _ ltac:(lia) (env_agree_refl 60 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
  clear HS. rename HS3 into HS. rebaseE HS AG HEv.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E60 : ew Ev 60 = Z_to_bv 64 FL)
    by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (E61 : ew Ev 61 = Z_to_bv 64 (shadow_addr F))
    by (change 61%nat with (60 + 1)%nat; rewrite HEv;
        exact (ew_havoc_new _ 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
  clear HEv.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E38 : ew Ev 38 = Z_to_bv 64 F) by exact RF end.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  destruct (cw_frame_afacts B LAWS Ev 38 60 61 lyc S2 W mem2 md2 0 fpos FFL HAR2 Hfin2 E38 E60 E61) as (AF38 & AF60 & AF61) end.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev _ msx 61 _ (st_ok_add_fact tfibsegs Ev _ msx 60 _
    (st_ok_add_fact tfibsegs Ev ssx msx 38 _ HS AF38) AF60) AF61) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
  assert (U61 : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (B2w : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2);
  assert (U33w : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
  assert (E32v' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
  destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFal32 & _ & HFpres & HFSpres).
  change (fs_frame_bytes 0) with 64 in HFpres, HFSpres. change (64 / 8) with 8 in HFSpres.
  fold F in HFpres, HFSpres. fold FL in HFLown.
  assert (HFno : forall a, F <= a < F + 64 -> ~ aowned B lyc S2 a)
    by (intros a Ha; exact (proj2 (HFpres a Ha))).
  assert (HFSno : forall a, shadow_addr F <= a < shadow_addr F + 8 -> ~ aowned B lyc S2 a).
  { intros a Ha. pose proof (HFSpres (a - shadow_addr F) ltac:(lia)) as Hx.
    replace (shadow_addr F + (a - shadow_addr F)) with a in Hx by lia. exact (proj2 Hx). }
  assert (HFLF : FL + 1 <= F \/ F + 64 <= FL)
    by (destruct (cw_flag_apart B lyc S2 FL F (F + 64) HFLown HFno) as [Hx|Hx]; [right | left]; lia).
  assert (HFLS : FL + 1 <= shadow_addr F \/ shadow_addr F + 8 <= FL)
    by (destruct (cw_flag_apart B lyc S2 FL (shadow_addr F) (shadow_addr F + 8) HFLown HFSno) as [Hx|Hx];
        [right | left]; lia).
  assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
  assert (HFS : F + 64 <= shadow_addr F \/ shadow_addr F + 8 <= F).
  { unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
    destruct HFapp as (_ & [Hl | Hh]); [left | right]; lia. }
  assert (HSlo : SHADOW_OFF + 512 <= shadow_addr F) by (unfold shadow_addr; lia).
  assert (HShi : shadow_addr F + 8 <= SHADOW_OFF + 2 ^ 44 + 8) by (unfold shadow_addr; lia).
  (* the three regions of the frame: the frame itself (flag pointer at F + 56), its 8 shadow bytes (zero after
     the request) and the flag byte *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cw_frame_region 38 60 0) HS eq_refl
    (cw_frame_region_ok B LAWS FFL Ev 38 60 lyc S2 W mem2 md2 0 fpos HAR2 Hfin2 E38 E60 Hflag)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, cw_frame_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; change (fs_frame_bytes 0) with 64;
      rewrite U38, U33w, B2w; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
      repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cw_fshadow_region 61 0) HS eq_refl
    (cw_fshadow_region_ok B LAWS Ev 61 lyc S2 W mem2 md2 0 fpos HAR2 Hfin2 E61 Hz)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, cw_fshadow_region, cw_frame_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
      rewrite U61, U38, U33w, B2w; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, shadow_addr, SHADOW_OFF;
      repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  (* the flag byte: in the state with a closed window (the release re-opens it) *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 60%nat) 0 1 0 0 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite U60; split; [lia|]; split; [lia|]; split; [intros o Ho; lia | apply Forall_nil])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, cw_fshadow_region, cw_frame_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
      rewrite U60, U61, U38, U33w, B2w; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, shadow_addr, SHADOW_OFF;
      repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  (* the shadow of a frame byte is the frame-shadow region's *)
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_alias tfibsegs Ev ssx msx _ _ HS (shadow_decl_ok Ev 38 32 61 F SB E38 ltac:(lia) E32v' E61)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  (* 0x8380c-0x8388c: the frame header, the eight shadow bytes f1 x4 | f3 x4, the spill of F at 24(s1) *)
  assert (HOWN : In (0, fpos) ((0, fpos) :: own)) by (left; reflexivity).
  aj_run_to_sh tfibtbl_lib_ok HS HJ2 0x83890.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 fpos 61%nat);
      [reflexivity | exact U61 | exact HOWN | cbn [YP09.r_wlo]; lia
      | cbn [YP09.r_whi]; change (fs_frame_bytes 0 / 8) with 8; lia |].
    eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 fpos 38%nat);
      [reflexivity | exact U38 | exact HOWN | cbn [YP09.r_wlo]; lia
      | cbn [YP09.r_whi]; change (fs_frame_bytes 0) with 64; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (SP1 - sp0));
      [reflexivity | rewrite U33w; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
      [reflexivity | rewrite B2w; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
    repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
  rebaseE HS AG HEv. clear HEv. cw_norm_model.
  cw_hide HFLF. cw_hide HFLS. cw_hide HFS. cw_hide HFapp.
  (* what the call has kept of its entry state, carried from the call point *)
  assert (HEimg : forall a, ch <= a < ch + 24 -> ~ in_img tfibsegs a).
  { intros a Ha Him. pose proof Hdst as (_ & _ & Htd & _).
    exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc ch 24 a HAR Htd Ha Him). }
  assert (HZc : forall a, cw_fresh B lyc Sc a \/ (ch <= a < ch + 24) \/ (spZ regs - 8352 <= a < spZ regs) ->
    (spZ regs - 8352 <= a < spZ regs) \/ ((ch <= a < ch + 24) /\ ~ in_img tfibsegs a) \/ cw_fresh B lyc Sc a).
  { intros a [Ha | [Ha | Ha]]; [right; right; exact Ha | right; left; split; [exact Ha | exact (HEimg a Ha)] | left; exact Ha]. }
  assert (HZfr : forall a, (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL ->
    cw_fresh B lyc Sc a).
  { intros a Ha. apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
      lyc S2 W _ _ k 0 fpos a HJ0 HJ2 ltac:(rewrite Eab; apply Permutation_refl)).
    change (fs_frame_bytes 0) with 64. change (64 / 8) with 8.
    unfold frame_rng, in_zr. cbn [fst snd]. fold F FL. exact Ha. }
  cts_keep F FL KT HAR HZfr.
  (* the text and the record at the walk's state: a block's marks hold there, a frame's are what the
     request kept *)
  pose proof Hstr as (Hq0 & Hgtb & Hz0 & Hcrd).
  pose proof Hcrd as (Hcq0 & Hcqhi & Hcrdb & Hcra & Hchull & Hcam & Hcwin).
  assert (Htb1 : (1 <= length tb)%nat)
    by (destruct (length tb) eqn:EL; [destruct tb; [destruct Hz0 | discriminate EL] | lia]).
  assert (HEch : forall x, q <= x < q + Z.of_nat (length tb) -> ~ (ch <= x < ch + 24))
    by (clear - Hdisj; intros x Hx Hc; lia).
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ ?m3 _ _ |- _ =>
  assert (HRAq : range_addressable (aview tfibsegs (w_H W) m3) SHADOW_OFF q (Z.of_nat (length tb)));
  [ apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly3 S3 W m3 _ 8352 (spZ regs) (fun x => ch <= x < ch + 24)
      q (Z.of_nat (length tb)) HAR (proj1 HJ)
      ltac:(rewrite Eab; intros b m Hb; exact Hb) ltac:(intros cid pos; reflexivity)
      Hoq ltac:(clear - Hcq0; lia) ltac:(clear; lia) Hcra KT
      ltac:(intros x Hx Hw; cbn beta in Hw;
        exact (cts_shadow_apart x ch 24 ltac:(clear - Hcq0 Hx; lia)
          ltac:(clear - Hcam Hx; unfold amem_range in Hcam |- *; lia)
          ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdst))))))))
          ltac:(clear; lia) Hw)))
  | ] end.
  (* 0x83890-0x838a8: the check of the text's first byte (the engine's token, paid by HRAq), the spill of F
     at 24(s1), s10 = 0, s6 = F + 32; stop at 0x838ac beqz s3 (n = 0) *)
  repeat match goal with SH : sh_ok _ _ _ _ _ |- _ => clear SH end.
  (* The token engine takes no write window that meets the shadow band, and a frame's address fact (HPTR) does
     not keep its window off the band. The walk closes the frame's window and its shadow's for every token run
     (the chunks stay readable) and opens the frame's again, under the plain runner, for the one store into
     want. *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (map (fun r => match YP09.r_base r with
    | Some m => if Nat.eqb m 61 || Nat.eqb m 38 then set_window r 0 0 else r | None => r end) rs) in
  pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS
    ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch goal with HS : st_ok _ ?Ev _ (restrict (w_H W) ?ms3) |- _ =>
  assert (E10v : ew Ev 10 = Z_to_bv 64 q)
    by (rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10);
  assert (E32w : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
  assert (Hqhi : q <= 2 ^ 47 - 2) by (clear - Hcam Htb1 C4 C5; unfold amem_range in *; lia).
  (* the text pointer's range, for the engine's shadow entry *)
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 10 (mkAF 1 (2 ^ 47 - 2) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10v, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; repeat split; first [lia | apply Z.mod_1_r])) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch goal with HS : st_ok _ ?Ev _ (restrict (w_H W) ?ms3) |- _ =>
  assert (Htext : shent_ok tfibsegs CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) (mkSHE 10 0 1))
    by (apply (cw_shent_ra W (ms_mem ms3) Ev 10 q 1);
        [ intros x Hx; apply HRAq; lia
        | clear - Hcam Htb1; unfold amem_range in *; lia
        | lia | lia | lia | exact E10v | exact E32w ]);
  shok_auto_with SHOK CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) [mkSHE 10 0 1] ltac:(exact Htext) end.
  clear U38 U60 U61 U33w B2w E32v'.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  assert (U38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
  assert (U61 : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (U33w : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
  assert (B2w : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2) end.
  cw_run cts_awr.
  cts_keep F FL KT HAR HZfr.
  cw_norm_model.
  cts_rebase.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  assert (E12v : ew Ev 12 = Z_to_bv 64 n)
    by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12) end.
  (* the frame, its shadow and its flag are fresh, so they are not the record's bytes *)
  assert (Hchfr : forall a, (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL ->
    ~ (ch <= a < ch + 24)).
  { intros a Ha Hin. destruct (HZfr a Ha) as (_ & _ & Hblk & Hfrm).
    destruct Hoch as [(b & m & Hb & Hlo & Hhi) | (cid & pos & Hb & Hlo & Hhi)].
    - exact (Hblk b m (a - b) Hb ltac:(lia) ltac:(lia)).
    - destruct (Hfrm cid pos Hb) as (Hzz & _). apply Hzz. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
  pose proof Hdst as (Hch0 & Hchhi & Htd & Htwr & Hchra0 & Hchhull0 & Hcham & Hchwin).
  unfold coff_win in Hchwin. unfold coff_win in Hcwin.
  assert (HobjF : cobj_ok B lyc S2 F 64).
  { right. exists 0%Z, fpos. split; [rewrite Hfrs2; left; reflexivity|].
    change (fs_frame_bytes 0) with 64. lia. }
  assert (HMOsc : mo_le MT Sc S2 0)
    by (destruct HSf as (ff & Hff); rewrite Hff;
        apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL)).
  assert (HOLEN : length (fst (owed_scribble_text_spec tb n)) = Z.to_nat n)
    by (unfold owed_scribble_text_spec; apply cts_owe_len).
  assert (HLEN : length (fst (scribble_text_spec tb n)) = Z.to_nat n)
    by (rewrite <- Howe; exact HOLEN).
  (* what the walk has established: the caller's premises, its frame and its realigned sp *)
  assert (FCTX : cts_fctx B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0).
  { unfold cts_fctx.
    split; [exact HE|]. split; [exact H10|]. split; [exact Hstr|]. split; [exact Hoq|].
    split; [exact Hoch|]. split; [exact H11|]. split; [exact Hdst|]. split; [exact Hcjl|].
    split; [exact H12|]. split; [exact Hn|]. split; [exact Hdisj|]. split; [exact Howe|].
    split; [exact EE|]. split; [exact E32|]. split; [exact Hfrs2|]. split; [exact Eab|].
    split; [exact HMOsc|]. split; [exact Hsp1 | exact Hsp1al]. }
  lazymatch goal with |- SRr _ _ _ ?Qg =>
  assert (TAILQ : forall ly3 S3 W3 regs3 mem3 md3,
            cts_cut_ret B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
              ly3 S3 W3 regs3 mem3 md3 fpos ->
            SRr tfibsegs W3 (cfg_at tfibsegs A_CTS_RET regs3 mem3 md3) Qg)
    by (intros ly3 S3 W3 regs3 mem3 md3 HCUT; eapply cts_tail_holds; eassumption);
  assert (REC : cts_rec_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb
                  S2 fpos SP1 E0 Qg)
    by (eapply cts_rec_holds; eassumption);
  assert (PAD : cts_pad_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb
                  S2 fpos SP1 E0 Qg)
    by (eapply cts_pad_holds; eassumption) end.
  clear TAILQ.
  pose proof PAD as PADu.
  unfold cts_rec_cont in REC. unfold cts_pad_cont in PADu.
  change T_check_text_scribble with 8352 in REC, PADu.
  fold F in REC, PADu. fold FL in REC, PADu.
  (* 0x838ac beqz s3: n = 0 -> 0x83980, the pad skipped; else the text's first byte at 0x838b0 *)
  cw_branch Hc.
  + lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
    rewrite branch_eq_U, (U_atom_off Ev 12 n 0 E12v ltac:(lia)), U_lit in Hc by lia end.
    rewrite Z.add_0_r in Hc. apply Z.eqb_eq in Hc.
    (* 0x83980-0x839a4: a1 = 165, a2 = 24, a0 = s4 = ch, jal __asan_memset *)
    cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
    cw_run_to cts_awr 0x51e34.
    cts_keep F FL KT HAR HZfr. cts_rebase.
    (* 0x83984 bgeu a1,s3: a1 = s10 = 0 and n = 0, so the pad of want is skipped *)
    cw_branch Hpad.
    all: lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
         let Hn12 := fresh "Hn12" in
         assert (Hn12 : ew Ev 12 = Z_to_bv 64 n)
           by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12);
         rewrite branch_geu_U, (U_atom_off Ev 12 n 0 Hn12 ltac:(lia)), U_lit in Hpad by lia;
         rewrite Z.add_0_r in Hpad; clear Hn12 end.
    2: { exfalso. clear - Hpad Hc. rewrite Hc in Hpad. cbn in Hpad. discriminate Hpad. }
    (* the record point: run to it, join the state into cts_ss_rec, then the continuation *)
    cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
    cw_run_to cts_awr 0x83998.
    cts_keep F FL KT HAR HZfr. cts_rebase.
    rreg HS (26%bv : bv 5) SU0.
    cw_join_win HS cts_ss_rec 400%nat cts_deadR_bv ltac:(idtac).
    lazymatch type of HS with st_ok _ (havoc ?Ev 400 ?vals) _ (restrict _ ?msx) =>
    assert (E416n : ew (havoc Ev 400 vals) 416 = w64 (snd (owed_scribble_text_spec tb n)));
    [ change 416%nat with (400 + 16)%nat;
      rewrite (ew_havoc_new Ev 400 vals 16 (Z_to_bv 64 0) ltac:(cbn; lia));
      cbn [nth map cts_deadR_bv]; rewrite SU0, Hc;
      unfold owed_scribble_text_spec; cbn [Z.to_nat]; rewrite cts_owe_0; reflexivity | ] end.
    eapply REC.
    1: exact HS.
    1: (lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
        assert (SH2 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor;
        exact SH2 end).
    1: (intros nn Hnn; rewrite ew_havoc_old by (cbn; lia); apply AG; lia).
    1: (rewrite ew_havoc_old by (cbn; lia); exact E33).
    1: (rewrite ew_havoc_old by (cbn; lia); exact E38).
    1: (rewrite ew_havoc_old by (cbn; lia); exact E60).
    1: (rewrite ew_havoc_old by (cbn; lia); exact E61).
    1: exact E416n.
    1: eassumption.
    1: exact KT.
    1: (eapply same_io_trans; [exact HIOf | cpw_io]).
    1: (intros jj Hjj; rewrite HOLEN, Hc in Hjj; cbn in Hjj; lia).
  + (* n <> 0: 0x838b0 lbu a5,0(s5) reads the text's first byte, 0x838b8 beqz a5 *)
    lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
    rewrite branch_eq_U, (U_atom_off Ev 12 n 0 E12v ltac:(lia)), U_lit in Hc by lia end.
    rewrite Z.add_0_r in Hc. apply Z.eqb_neq in Hc.
    assert (Hnpos : 0 < n) by lia.
    (* the text's bytes and their usable marks at this state *)
    destruct (Hgtb 0%nat ltac:(lia)) as (Hb0c & Hb0r). rewrite Z.add_0_r in Hb0c.
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly5 ?S5 _ ?m5 _ _ |- _ =>
    assert (Hb0 : val_mem tfibsegs (mrestrict (w_H W) m5) q 1 (nth 0 tb 0))
      by (apply (cts_obj_val B lyc Sc W memc W m5 8352 (spZ regs) (fun y => ch <= y < ch + 24)
            q (Z.of_nat (length tb)) q 1%nat (nth 0 tb 0) Hoq ltac:(lia) ltac:(lia)
            ltac:(intros y Hy; exact (HEch y ltac:(lia))) KT Hb0c));
    assert (Hgtb3 : YI00.garr8 tfibsegs (mrestrict (w_H W) m5) q tb)
      by (intros j Hj; destruct (Hgtb j Hj) as (Hv & Hr); split; [|exact Hr];
          apply (cts_obj_val B lyc Sc W memc W m5 8352 (spZ regs) (fun y => ch <= y < ch + 24)
            q (Z.of_nat (length tb)) (q + Z.of_nat j) 1%nat (nth j tb 0) Hoq ltac:(lia) ltac:(lia)
            ltac:(intros y Hy; exact (HEch y ltac:(lia))) KT Hv));
    assert (HRAq3 : range_addressable (aview tfibsegs (w_H W) m5) SHADOW_OFF q (Z.of_nat (length tb)))
      by (apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly5 S5 W m5 _ 8352 (spZ regs)
            (fun x => ch <= x < ch + 24) q (Z.of_nat (length tb)) HAR (proj1 HJx)
            ltac:(rewrite Eab; intros b m Hb; exact Hb) ltac:(intros cid pos; reflexivity)
            Hoq ltac:(clear - Hcq0; lia) ltac:(clear; lia) Hcra KT
            ltac:(intros x Hx Hw; cbn beta in Hw;
                  exact (cts_shadow_apart x ch 24 ltac:(clear - Hcq0 Hx; lia)
                    ltac:(clear - Hcam Hx; unfold amem_range in *; lia)
                    Hcham ltac:(clear; lia) Hw)))) end.
    (* the walk's own frame, its shadow and its flag are not the text's bytes *)
    assert (Hqfr : forall a, (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL ->
      ~ (q <= a < q + Z.of_nat (length tb))).
    { intros a Ha Hin. destruct (HZfr a Ha) as (_ & _ & Hblk & Hfrm).
      destruct Hoq as [(b & m & Hb & Hlo & Hhi) | (cid & pos & Hb & Hlo & Hhi)].
      - exact (Hblk b m (a - b) Hb ltac:(lia) ltac:(lia)).
      - destruct (Hfrm cid pos Hb) as (Hzz & _). apply Hzz. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
    assert (HqF : q + Z.of_nat (length tb) <= F \/ F + 64 <= q)
      by (destruct (Z_le_gt_dec (q + Z.of_nat (length tb)) F) as [Hx|Hx]; [left; exact Hx|];
          destruct (Z_le_gt_dec (F + 64) q) as [Hy|Hy]; [right; exact Hy|];
          exfalso; apply (Hqfr (Z.max q F) ltac:(left; clear - Hx Hy Htb1; lia));
          clear - Hx Hy Htb1; lia).
    assert (HqS : q + Z.of_nat (length tb) <= shadow_addr F \/ shadow_addr F + 8 <= q)
      by (destruct (Z_le_gt_dec (q + Z.of_nat (length tb)) (shadow_addr F)) as [Hx|Hx]; [left; exact Hx|];
          destruct (Z_le_gt_dec (shadow_addr F + 8) q) as [Hy|Hy]; [right; exact Hy|];
          exfalso;
          apply (Hqfr (Z.max q (shadow_addr F)) ltac:(right; left; clear - Hx Hy Htb1; lia));
          clear - Hx Hy Htb1; lia).
    assert (HqFL : q + Z.of_nat (length tb) <= FL \/ FL + 1 <= q)
      by (destruct (Z_le_gt_dec (q + Z.of_nat (length tb)) FL) as [Hx|Hx]; [left; exact Hx|];
          destruct (Z_le_gt_dec (FL + 1) q) as [Hy|Hy]; [right; exact Hy|];
          exfalso; apply (Hqfr FL ltac:(right; right; reflexivity)); clear - Hx Hy Htb1; lia).
    clear Hqfr. cw_hide HqF. cw_hide HqS. cw_hide HqFL.
    (* keep the five regions of the joins; the output slots done, the text bytes used and the text's
       first byte become the atoms 417, 418 and 419 *)
    lazymatch type of HS with st_ok _ ?Ex ?ssx ?msX =>
    pose proof (st_ok_submem tfibsegs Ex ssx msX cts_rec_regions HS
      ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end. norm_ss HS.
    lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
    pose proof (YCeo.st_ok_havoc_win tfibsegs 417 Ev ssv msv
      [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)] HS
      ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS;
    assert (E417 : ew (havoc Ev 417 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)]) 417
                   = Z_to_bv 64 0)
      by (exact (ew_havoc_new Ev 417 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)] 0
                   (Z_to_bv 64 0) ltac:(cbn; lia)));
    assert (E418 : ew (havoc Ev 417 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)]) 418
                   = Z_to_bv 64 0)
      by (change 418%nat with (417 + 1)%nat;
          exact (ew_havoc_new Ev 417 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)] 1
                   (Z_to_bv 64 0) ltac:(cbn; lia)));
    assert (E419 : ew (havoc Ev 417 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)]) 419
                   = Z_to_bv 64 (nth 0 tb 0))
      by (change 419%nat with (417 + 2)%nat;
          exact (ew_havoc_new Ev 417 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (nth 0 tb 0)] 2
                   (Z_to_bv 64 0) ltac:(cbn; lia))) end.
    cts_rebase.
    lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_add_fact tfibsegs Ev ssx msx 419 (mkAF 0 255 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite E419, unsigned_lit_small by lia; rewrite Z.pow_0_r;
            repeat split; first [lia | apply Z.mod_1_r])) as HS3;
    clear HS; rename HS3 into HS end. norm_ss HS.
    lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_add_fact tfibsegs Ev ssx msx 417 (mkAF 0 8 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite E417, unsigned_lit_small by lia; rewrite Z.pow_0_r;
            repeat split; first [lia | apply Z.mod_1_r])) as HS3;
    clear HS; rename HS3 into HS end. norm_ss HS.
    (* the engine's shadow entry for the text's first byte, in the state's own environment *)
    repeat match goal with SH : sh_ok _ _ _ _ _ |- _ => clear SH end.
    lazymatch goal with HSx : st_ok _ ?Ev _ (restrict (w_H W) ?ms3) |- _ =>
    assert (E10w : ew Ev 10 = Z_to_bv 64 q)
      by (rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10);
    assert (E32w2 : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32);
    assert (Htext2 : shent_ok tfibsegs CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) (mkSHE 10 0 1))
      by (apply (cw_shent_ra W (ms_mem ms3) Ev 10 q 1);
          [ intros x Hx; apply HRAq3; clear - Hx Htb1; lia
          | clear - Hcam Htb1; unfold amem_range in *; lia
          | clear - Hcq0; lia | clear; lia | clear - Hcqhi Htb1; lia | exact E10w | exact E32w2 ]);
    shok_auto_with SHOK CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) [mkSHE 10 0 1] ltac:(exact Htext2) end.
    clear U38 U60 U61 U33w B2w.
    cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (U10q : bv_unsigned (ew Ev 10) = q)
      by (rewrite E10w; apply unsigned_lit_small; clear - Hcq0 Hcqhi Htb1; lia) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _
      (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 419 0))]) HS eq_refl
      ltac:(unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U10q; split; [clear - Hcq0; lia|]; split; [clear - Hcqhi Htb1; lia|];
        split; [intros oo Hoo; clear - Hoo; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val tfibsegs _ _ q 0 1%N (SOff 419 0) (nth 0 tb 0));
        [ cbn [sv_denot]; rewrite E419, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn [Z.of_N N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.mul Pos.mul]; clear - Hb0r; lia
        | cbn [Z.of_N]; clear; lia
        | rewrite Z.add_0_r; exact Hb0 ])
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite U10q, U38, U60, U61, U33w, B2w;
        unfold cw_hold in HFLF, HFLS, HFS, HqF, HqS, HqFL;
        repeat split;
        (clear - HqF HqS HqFL Hcwin Hsp1 Htb1 Hcq0 Hcqhi HFLF HFLS HFS HF4096 HFceil HSlo HShi
                 Hceil H47 H46 C1 Hsp1al16; zone_lia))) as HS3;
    clear HS; rename HS3 into HS end. norm_ss HS.
    (* 0x838b0-0x838b4, then the branch at 0x838b8 *)
    cw_run cts_awr.
    cts_keep F FL KT HAR HZfr. cts_rebase.
    cw_branch Hbz.
    all: lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
         rewrite branch_eq_U,
           (U_atom_off Ev 419 (nth 0 tb 0) 0 E419 ltac:(clear - Hb0r; lia)), U_lit
           in Hbz by (clear - Hb0r; lia) end.
    all: rewrite Z.add_0_r in Hbz.
    * (* the text's first byte is 0: owed_scribble_text owes n spaces and uses no byte *)
      apply Z.eqb_eq in Hbz.
      pose proof (cts_owe_zero tb 0%nat (Z.to_nat n) ltac:(clear - Htb1; lia) Hbz) as HOWZ.
      change (skipn 0%nat tb) with tb in HOWZ.
      cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
      cw_run_to cts_awr 0x83984.
      cts_keep F FL KT HAR HZfr. cts_rebase.
      (* a1 = the output slots done (atom 417), s10 = the text bytes used (atom 418), both 0 *)
      lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      let e11 := eval vm_compute in (sr_get (ss_regs ssx) (11%bv : bv 5)) in
      assert (RJ11 : getr (ms_regs msx) (11%bv : bv 5) = Z_to_bv 64 0);
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (11%bv : bv 5) HS) _);
        change (sv_denot Ev e11 = Z_to_bv 64 0);
        first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | ];
      let e26 := eval vm_compute in (sr_get (ss_regs ssx) (26%bv : bv 5)) in
      assert (RJ26 : getr (ms_regs msx) (26%bv : bv 5) = Z_to_bv 64 0);
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (26%bv : bv 5) HS) _);
        change (sv_denot Ev e26 = Z_to_bv 64 0);
        first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | ] end.
      lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (11%bv : bv 5) (SOff 417 0) HS
        ltac:(vm_compute; reflexivity)
        ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E417, Z.add_0_r, Z_to_bv_bv_unsigned;
              symmetry; exact RJ11)) as HS3;
      clear HS; rename HS3 into HS end. norm_ss HS.
      lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (26%bv : bv 5) (SOff 418 0) HS
        ltac:(vm_compute; reflexivity)
        ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E418, Z.add_0_r, Z_to_bv_bv_unsigned;
              symmetry; exact RJ26)) as HS3;
      clear HS; rename HS3 into HS end. norm_ss HS.
      cw_join_win HS cts_ss_pad 420%nat cts_deadP_bv ltac:(idtac).
      eapply PADu.
      1: exact HS.
      1: (lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
          assert (SH2 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor;
          exact SH2 end).
      1: (intros nn Hnn; rewrite ew_havoc_old by (cbn; lia); apply AG; lia).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E33).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E38).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E60).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E61).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E417).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E418).
      1: eassumption.
      1: exact KT.
      1: (eapply same_io_trans; [exact HIOf | cpw_io]).
      1: lia.
      1: lia.
      1: (lazymatch goal with |- length ?p = _ => unify p (@nil Z) end; reflexivity).
      1: (unfold owed_scribble_text_spec; rewrite HOWZ; cbn [fst app];
          replace (Z.to_nat n - Z.to_nat 0)%nat with (Z.to_nat n) by lia; reflexivity).
      1: (unfold owed_scribble_text_spec; rewrite HOWZ; reflexivity).
      1: (intros jj Hjj; cbn [length] in Hjj; lia).
    * (* the text's first byte is not 0: the inlined loop, from its head at 0x838d0 *)
      apply Z.eqb_neq in Hbz.
      assert (Hcstr1 : (0 < length (cts_cstr tb))%nat).
      { destruct tb as [|x tb']; [cbn [length] in Htb1; lia|].
        cbn [cts_cstr nth] in Hbz |- *.
        rewrite (proj2 (Z.eqb_neq x 0) Hbz). cbn [length]. lia. }
      cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
      cw_run_to cts_awr 0x838d0.
      cts_keep F FL KT HAR HZfr. cts_rebase.
      (* the text's bytes and their usable marks at the loop head *)
      lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly6 ?S6 _ ?m6 _ _ |- _ =>
      assert (Hgtb4 : YI00.garr8 tfibsegs (mrestrict (w_H W) m6) q tb)
        by (intros j Hj; destruct (Hgtb j Hj) as (Hv & Hr); split; [|exact Hr];
            apply (cts_obj_val B lyc Sc W memc W m6 8352 (spZ regs) (fun y => ch <= y < ch + 24)
              q (Z.of_nat (length tb)) (q + Z.of_nat j) 1%nat (nth j tb 0) Hoq
              ltac:(clear - Hj; lia) ltac:(clear - Hj; lia)
              ltac:(intros y Hy; exact (HEch y ltac:(clear - Hy Hj; lia))) KT Hv));
      assert (HRAq4 : range_addressable (aview tfibsegs (w_H W) m6) SHADOW_OFF q (Z.of_nat (length tb)))
        by (apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly6 S6 W m6 _ 8352 (spZ regs)
              (fun x => ch <= x < ch + 24) q (Z.of_nat (length tb)) HAR (proj1 HJx)
              ltac:(rewrite Eab; intros b m Hb; exact Hb) ltac:(intros cid pos; reflexivity)
              Hoq ltac:(clear - Hcq0; lia) ltac:(clear; lia) Hcra KT
              ltac:(intros x Hx Hw; cbn beta in Hw;
                    exact (cts_shadow_apart x ch 24 ltac:(clear - Hcq0 Hx; lia)
                      ltac:(clear - Hcam Hx; unfold amem_range in *; lia)
                      Hcham ltac:(clear; lia) Hw)))) end.
      (* a1 = atom 417 = 0, s10 = atom 418 = 0, a5 = atom 419 = the text's first byte *)
      lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      let e11 := eval vm_compute in (sr_get (ss_regs ssx) (11%bv : bv 5)) in
      assert (RL11 : getr (ms_regs msx) (11%bv : bv 5) = Z_to_bv 64 0);
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (11%bv : bv 5) HS) _);
        change (sv_denot Ev e11 = Z_to_bv 64 0);
        first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | ];
      let e26 := eval vm_compute in (sr_get (ss_regs ssx) (26%bv : bv 5)) in
      assert (RL26 : getr (ms_regs msx) (26%bv : bv 5) = Z_to_bv 64 0);
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (26%bv : bv 5) HS) _);
        change (sv_denot Ev e26 = Z_to_bv 64 0);
        first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | ];
      let e15 := eval vm_compute in (sr_get (ss_regs ssx) (15%bv : bv 5)) in
      assert (RL15 : getr (ms_regs msx) (15%bv : bv 5) = Z_to_bv 64 (nth 0 tb 0));
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (15%bv : bv 5) HS) _);
        change (sv_denot Ev e15 = Z_to_bv 64 (nth 0 tb 0));
        first [ reflexivity
              | cbn [sv_denot]; rewrite E419, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
              | cbn [sv_denot]; f_equal; apply zcanon_id; unfold M64; clear - Hb0r; lia
              | rewrite denot_lit_U; f_equal; rewrite U_SLit; apply zcanon_id; unfold M64;
                clear - Hb0r; lia ] | ] end.
      lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (11%bv : bv 5) (SOff 417 0) HS
        ltac:(vm_compute; reflexivity)
        ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E417, Z.add_0_r, Z_to_bv_bv_unsigned;
              symmetry; exact RL11)) as HS3;
      clear HS; rename HS3 into HS end. norm_ss HS.
      lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (26%bv : bv 5) (SOff 418 0) HS
        ltac:(vm_compute; reflexivity)
        ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E418, Z.add_0_r, Z_to_bv_bv_unsigned;
              symmetry; exact RL26)) as HS3;
      clear HS; rename HS3 into HS end. norm_ss HS.
      lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (15%bv : bv 5) (SOff 419 0) HS
        ltac:(vm_compute; reflexivity)
        ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E419, Z.add_0_r, Z_to_bv_bv_unsigned;
              symmetry; exact RL15)) as HS3;
      clear HS; rename HS3 into HS end. norm_ss HS.
      cw_join_win HS cts_ss_lp 440%nat cts_deadL_bv ltac:(idtac).
      lazymatch goal with |- SRr _ _ _ ?Qg =>
      eapply (LOOP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
                S2 fpos SP1 E0 Qg) end.
      1: exact HE.
      1: exact H10.
      1: exact H11.
      1: exact H12.
      1: exact Hn.
      1: exact Hstr.
      1: exact Hoq.
      1: exact Hoch.
      1: exact Hdst.
      1: exact Hdisj.
      1: exact EE.
      1: exact E32.
      1: exact Hfin2.
      1: exact Hfrs2.
      1: exact Eab.
      1: exact Hsp1.
      1: exact Hsp1al.
      1: exact PAD.
      1: exact HS.
      1: (lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
          assert (SH3 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor;
          exact SH3 end).
      1: (intros nn Hnn; rewrite ew_havoc_old by (cbn; lia); apply AG; lia).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E33).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E38).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E60).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E61).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E417).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E418).
      1: (rewrite ew_havoc_old by (cbn; lia); cbn [Z.to_nat]; exact E419).
      1: eassumption.
      1: exact KT.
      1: (eapply same_io_trans; [exact HIOf | cpw_io]).
      1: lia.
      1: (cbn [Z.to_nat]; lia).
      1: (lazymatch goal with |- length ?p = _ => unify p (@nil Z) end; reflexivity).
      1: (cbn [Z.to_nat]; apply cts_model_init).
      1: (intros jj Hjj; cbn [length] in Hjj; lia).
      1: exact Hgtb4.
      1: exact HRAq4.
Qed.
End d.
End b.
