(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) from
   proofs/libreac/fuzz_knock/lib/A/APgMain0.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed.
   rule 24: no function proved here alone; this is segment S0 of LLVMFuzzerTestOneInput's walk, whose top claim is
   lib/A/PPgMain.v.

   SEGMENT S0 ENTRY, pc 0x806b4 .. 0x807cc, ending at ss_H (0x807d0, lib/A/PPgMainSt.v). Every address was read from
   the pinned image bytes with capstone 5.0.7. The walk, with knock's line it follows:
   - 0x806b4-0x806f4: the 128-byte save frame (13 saves at [sp0-104, sp0)), s0 = sp0, `andi sp,sp,-0x20`; the first
     run stops at 0x806f8 (knock 0x7ef14); sp1 := 32 * ((sp0 - 128) / 32) into env slot 70 (knock -192).
   - the stack region is trimmed to the saves [sp0-104, sp0) (as knock), and region 70 = [s1+16, s1+24) is added
     for the one spill `sd s8,0x10(s1)` at 0x80758 (knock [16,88)).
   - 0x806f8-0x80724: the two GOT loads (0x99050 shadow base, 0x990a8 use-after-return option), s6 := SB, the
     option test `beqz a2` at 0x8071c decided by the option cell's SLit 1, a0 := 0x60, `jal 3ca58` at 0x80724
     (__asan_stack_malloc_1, class 1); the run stops at 0x3ca58 by SR_fetch.
   - the side-stack call through aj_stack_malloc_atS (lib/A/PPgMainCall.v) with class 1 and ASM1; its premise
     count_cid 1 (frames S) < fs_frames 1 is the call-site lemma pin_fs1_site.
   - the class-1 frame facts (F = frame_addr ly 1 fpos, 128 bytes, 16 shadow bytes, the flag address at F + 120),
     the atoms 75 / 87 / 88 and the alias SB + (F >> 3) = slot 88, as knock.
   - 0x80728-0x807c8: `bnez s2` decided by HPTR 5 on F (the real-stack path 0x8073c-0x80754 is never reached),
     `sd s8,0x10(s1)`, the frame header F[0..24) = 0x41B58AB3 / 0x1ffeb / 0x806b4, the 12 shadow bytes
     f1 x4, f8, f2 x3, f8, f3 x3 (0x80794-0x807c8).
   - 0x807cc `bnez a0` with a0 = n >> 26: split with SRr_sym_branch; the taken side (-> 0x80940) is refuted by
     n < 2 ^ 26 (atom 11); the fall-through runs to 0x807d0.
   - the join into ss_H (window 400) and the hand-off to the rest of the walk (RB).
   Section hypotheses: MTL TL LAWS ML ASM1 SMP FFL MTF and RB : rt_from B MT FP POST ss_H (INV_0 B MT 0). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgMain0.v, with its module paths and numbers changed; 387 of its 446 lines of code are new or changed and 228 lines of the source are left out. *)
(* owed_counter_text (fuzz_codec.c:402-429) at image A 0x83df8, the walk's first segment: from the entry to the loop
   head 0x83f48 with n = 0 (lib/A/Prog/owed_counter_text_A_base.v ss_L 0, INV_L 0).
   0x83df8-0x83e3c save ra, s0-s11 into [sp - 104, sp), s0 = sp, andi sp,sp,-32 (sp1, atom 70), mv s1,sp; the
   spills of dt (sp1 + 8) and the frame (sp1 + 16 / 24 / 48). 0x83e40-0x83e6c: the use-after-return test (the cell
   reads 1) and the class-1 frame request (lib/A/Prog/CPgWalkFrame.v cpg_stack_malloc_keep_io; F is atom 75, the flag
   address 87, SB + F / 8 88); 0x83e70-0x83f34: the frame's header, its shadow map f1 x4 | 00 | f2 x3 | 00 x4 | f3 x4,
   __asan_memset(F + 64, 0, 32) at 0x83f38 (YC85.aj_intrin_atS: dot[] all zero); 0x83f3c-0x83f44: n = 0,
   s3 = '.', s7 = s6 = q (atom 300). What the walk kept since its entry is carried as tcj_kept (CPgWalkKept.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgWalk CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* env_agree from the entry environment carried across a havoc HEv : Ev = havoc Eo K ws, K >= 32 *)
Ltac oc_hae HEv :=
  lazymatch type of HEv with ?Ev = havoc ?Eo ?K ?ws =>
  lazymatch goal with HAE : env_agree 32 ?E0 Eo |- _ =>
  let H2 := fresh "HAE" in
  assert (H2 : env_agree 32 E0 Ev) by (rewrite HEv; apply env_agree_havoc_ge; [cbv; lia | exact HAE]);
  clear HAE; rename H2 into HAE end end.
(* lib/A/AWalkFw2.v's reseatL with HAE (env_agree 32 from the entry environment) carried to the new environment *)
Ltac oc_reseatL HS HJ2 HP2 keep AG kept_tac :=
    let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
    let HS2 := fresh "HS2" in
    lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
    lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
    jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
    match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
    clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
    let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
    lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
    lazymatch type of HS with st_ok _ ?Enew _ _ =>
    remember Enew as Ev eqn:HEv in HS;
    assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
    by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
    repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
    lazymatch Eo with
    | Ev => fail
    | _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
    | true => let H2 := fresh H in
    assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
    clear H; rename H2 into H
    end end end;
    oc_hae HEv;
    clear HEv AG; rename AG2 into AG end end.

(* oc_win before sp1 exists: the save area's bytes lie in the walk's window directly *)
Ltac oc_winP a Hb :=
  first
  [ oc_win a Hb
  | exfalso; clear - Hb; lia
  | lazymatch goal with AGx : forall n, (n < 33)%nat -> _ |- _ => revert Hb; evalE AGx; intros Hb end;
    left; unfold T_owed_counter_text, ESTACK; clear - Hb; lia ].

Section oc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet 0x51e34.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

Lemma oc_prefix : forall cx0, oc_pre B GLYPHA ROSTRS cx0 ->
  (forall fuel, oc_from B MT GLYPHA ROSTRS (ss_L 0) (INV_L 0 fuel)) ->
  SRr tfibsegs (o_W cx0) (cfg_at tfibsegs 0x83df8 (o_regs cx0) (o_memc cx0) (o_mdc cx0)) (oc_post B MT cx0).
Proof using MTL TL LAWS ML ASM1 SMP MTF FFL AMEMSET.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj pos0] Hpre HL.
pose proof Hpre as Hpre0.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_q o_sg o_dt o_tb o_sj o_dj o_pos] in *.
unfold oc_pre in Hpre; cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_q o_sg o_dt o_tb o_sj o_dj oc_n] in Hpre.
destruct Hpre as (HE & H10 & Hcstr & Hcq & Hcsg & H11 & Hdsg & Hgsj & Hlsj & H12 & Hdt & Hdj & Hdsd & Hdqs & Hdqd & Hcimg & Hfr8).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_owed_counter_text HE
  ltac:(unfold T_owed_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as (HAR & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : T_owed_counter_text = 4288) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (cw_entry B TL LAWS 0x83df8 192 [] [uar_got_region; uar_cell_region] [] lyc Sc W regs memc mdc HAR
  ltac:(lia) ltac:(lia) Hal ltac:(intros a Ha; apply Hpres; lia) ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HE0 in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold region_ok, uar_got_region, uar_cell_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  unfold A_GOT_uar, A_uar_glob; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]);
  apply Forall_cons; try apply Forall_nil;
  first
  [ apply (chunk_ok_val tfibsegs E _ 0 0x9db68 8 (SLit 0xa6480) 0xa6480); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kguar)
  | apply (chunk_ok_val tfibsegs E _ 0 0xa6480 4 (SLit 1) 1); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rd32 tfibsegs (w_H W) memc _ _ Kuar) ])).
specialize (HS ltac:(apply pairwise_disjoint_of_extents;
  unfold cw_regs, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [base_val]; rewrite Usp;
  unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia)).
specialize (HS I).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (B2 := Usp).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (HAE : env_agree 32 E E) by apply env_agree_refl.
assert (E32o : ew E 32 = Z_to_bv 64 SB) by exact E32.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) T_owed_counter_text
  (fun x => sg <= x < sg + 8 \/ dt <= x < dt + 1) HJ Hwlo Hwhi) as HK.
unfold cfg_at. change (w64 0x83df8) with (Z_to_bv 64 0x83df8).
(* A1: 0x83df8 .. 0x83e3c, the save frame, s0 = sp0, andi sp,sp,-32, mv s1,sp *)
cw_run_to cw_awr_stk 0x83e40.
oc_kstep oc_winP.
(* A2: sp1 into atom 70 *)
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = Z_to_bv 64 sp1)
  by exact (oc_denot_and_m32 E 2 (spZ regs) (-160) E2v ltac:(lia) ltac:(lia) ltac:(lia)).
assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)))
    with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)))) (sv_denot E (SLit 0))).
  rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) Dand R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) Dadd R9.
clear Dand Dadd.
pose proof (st_ok_agree tfibsegs 70 E (havoc E 70 [Z_to_bv 64 sp1]) _ _ HS
  (env_agree_havoc_ge 70 70 E E _ ltac:(lia) (env_agree_refl 70 E)) ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS. rebaseE HS AG HEv. oc_hae HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E70 : ew Ev 70 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (9%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R9; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear R2 R9.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 70%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
  pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 70%nat) 8 56 8 56 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E70, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable tfibsegs); apply HJpres; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear HJpres.
(* A3: 0x83e40 .. jal frame_alloc_1 at 0x83e6c: the GOT loads, the use-after-return test (decided: the cell reads 1),
   a0 = 128; the run stops at the runtime entry 0x3d270 *)
reshok HS.
cw_run_to oc_awr 0x3d270.
oc_kstep oc_winP.
(* A4: the class-1 frame request (cpg_stack_malloc_keep_io) *)
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250480 with (pc_stack_malloc (as_code B) 1) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. evalE AG; lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
    rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp.
  - rewrite R4. evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - change (fs_frames 1) with 8192. pose proof (oc_count_le 1 (frames Sc)). lia. }
cbv beta. clear R2 R3 R4 R1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HKa & (f & ES2) & HKr & Hio).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
(* the kept invariant across the request (cw_kept_call: the runtime's stack lies in the walk's window) *)
pose proof (cw_kept_call B T_owed_counter_text lyc Sc W memc W _ mem2 (spZ regs) (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0))
  (fun x => sg <= x < sg + 8 \/ dt <= x < dt + 1) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia) HK HKa) as HK2.
clear HK. rename HK2 into HK.
oc_reseatL HS HJ2 HP2 [0; 1]%nat AG
  ltac:(idtac; eapply oc_region_kept;
    [ evalE AG
    | intros a Ha; apply (proj1 HKa); revert Ha; evalE AG; unfold ESTACK; intros Ha; lia
    | intros a Ha; apply HJ2pres; revert Ha; evalE AG; intros Ha; lia ]).
clear HKa HKr.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
assert (Hfin2 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 pos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *.
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
remember (frame_addr lyc 1 pos) as F eqn:HFeq. remember (flag_addr lyc 1 pos) as FL eqn:HFLeq.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_agree tfibsegs 87 Ev (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
    (env_agree_havoc_ge 87 87 Ev Ev _ ltac:(lia) (env_agree_refl 87 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv. oc_hae HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E87 : ew Ev 87 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (E88 : ew Ev 88 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL lyc S2 W mem2 md2 1 pos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). rewrite <- HFLeq in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 75 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 87 (HPTR 0) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E87, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r;
          unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg in HFLrng; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 88 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E88, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
          split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_add_alias tfibsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 75 32 88 F SB RF ltac:(lia) E32' E88)) as HS3;
  clear HS; rename HS3 into HS end.
(* the frame's regions: the header [0, 24), s[] [32, 40), the flag word [120, 128) (read only), the 16 shadow bytes *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val tfibsegs Ev _ F 120 8 _ FL);
          [cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
           replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag)])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite RF; evalE AG; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 32 40 32 40 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite RF; evalE AG; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 0 24 0 24 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite RF; evalE AG; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
assert (ZS : forall j, 0 <= j < 2 -> val_mem tfibsegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _
    (fshadow_region 88 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
    ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          change (fs_frame_bytes 1 / 8) with 16; rewrite E88, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
          [ intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
            apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
          | apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
            apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
            apply Forall_nil ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          change (fs_frame_bytes 1 / 8) with 16; rewrite E88, RF; evalE AG; unfold SB;
          clear - Hsp1 Hceil Hwlo Hwhi H47 TT C1 C3 HF4096 HFceil HFhigh HFimg HF8lo HF8hi HFq HF8; repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear ZS.
(* A5: 0x83e70 .. jal __asan_memset at 0x83f38: the frame is not 0 (HPTR), spills, header, shadow map, memset args *)
clear HJ. rename HJ2 into HJ.
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x51e34. { oc_awr. }
oc_kstep oc_winP.
(* A6: __asan_memset(F + 64, 0, 32) (aj_intrin_atS) *)
pose proof (proj1 HJ) as HARm.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HR0; cbn [ms_mem restrict] in HR0;
  assert (ZD : forall i, 0 <= i < 4 -> aview tfibsegs (w_H W) (ms_mem msX) (SB + F / 8 + (8 + i)) = Some 0) end.
{ intros i Hi. assert (Hi4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
  destruct Hi4 as [-> | [-> | [-> | ->]]];
  match goal with |- context [SB + F / 8 + (8 + ?j)] =>
    let v := eval cbv in (8 + j) in change (8 + j) with v;
    pose proof (field_of_region _ _ 88 (SB + F / 8) cs lo hi wlo whi v 1%N (SLit 0) 0 HR0
      ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz;
    exact (aview_of_val_mem1 tfibsegs _ _ _ 0 Vz ltac:(lia)) end end. }
clear HR0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_atS tfibsegs B LAWS Hsegs OSet 0x51e34 AMEMSET W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 _ k (F + 64) 0 32 (sp1 - sp0) _ HJ) end.
  - rewrite Ra0. evalE AG; reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite R2. evalE AG; lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
    rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp.
  - rewrite R4. evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split; [|unfold ESTACK; lia].
    right; right; right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite <- HFeq. change (fs_frame_bytes 1) with 128. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg in HFhigh. pose proof asan_consts as (_ & _ & D3 & D4 & D5).
    rewrite D3, D4, D5. lia.
  - apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 64) with ((4 * (F / 32) + 8) * 8) by lia; apply Z_mod_mult | reflexivity | lia |].
    intros i Hi. change (32 / 8) with 4 in Hi. rewrite <- SB_SHADOW_OFF.
    replace ((F + 64) / 8) with (F / 8 + 8) by (rewrite HFq; replace (32 * (F / 32) + 64) with ((4 * (F / 32) + 8) * 8) by lia;
      rewrite Z_div_mult by lia; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; rewrite Z_div_mult by lia; lia).
    replace (SB + (F / 8 + 8) + i) with (SB + F / 8 + (8 + i)) by lia. exact (ZD i Hi).
  - intros _. apply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc S2 W _ _ 1 pos (F + 64) 32 HARm Hfin2);
    [rewrite <- HFeq; lia | rewrite <- HFeq; change (fs_frame_bytes 1) with 128; lia | lia].
  - exact I. }
cbv beta. clear R2 R3 R4 R1 Ra0 Ra1 Ra2 ZD.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Hdst & Hkm & Hpr & Hsbm).
pose proof (proj1 HJ3) as HAR3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR3 Hfin2) as (_ & _ & HF3pres & HFS3pres).
rewrite <- HFeq in HF3pres, HFS3pres. change (fs_frame_bytes 1) with 128 in HF3pres, HFS3pres.
change (128 / 8) with 16 in HFS3pres. unfold shadow_addr in HFS3pres. rewrite <- SB_SHADOW_OFF in HFS3pres.
(* the kept invariant across the memset: the destination is the walk's frame, the runtime's stack its window *)
lazymatch type of HK with tcj_kept _ _ ?T ?lc ?Scx ?Wx ?m0 ?W1 ?m1 ?spx ?Eo =>
  pose proof (cw_kept_step B LAWS T lc Scx Wx m0 mdc W1 m1 mem3 spx Eo
    (fun a => (F + 64 <= a < F + 64 + 32) \/ (sp0 + (sp1 - sp0) - ESTACK <= a < sp0 + (sp1 - sp0))) ltac:(lia) HAR HK) as HK3 end.
specialize (HK3 ltac:(intros a Ha Hn; apply Hkm; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H])).
specialize (HK3 ltac:(intros a [Ha | Ha];
  [ right; right; apply (cw_fresh_frame B LAWS FFL lyc S2 W mem2 md2 lyc Sc 1 pos a HAR2 Hfrs2
      (fun b m => ltac:(rewrite Eab; tauto)) (fun c p => eq_refl));
    left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite <- HFeq; change (fs_frame_bytes 1) with 128; lia
  | left; unfold ESTACK in Ha; lia ])).
specialize (HK3 Hpr). clear HK. rename HK3 into HK.
oc_reseatL HS HJ3 HP3 [0; 1; 2; 3; 4; 5]%nat AG
  ltac:(idtac; first [eapply oc_region_kept | match goal with |- ?g => idtac "KEPT-HEAD" g; fail end];
    [ first [evalE AG | match goal with |- ?g => idtac "KEPT-BASE" g; fail end]
    | intros a Ha; revert Ha; evalE AG; intros Ha; first [apply Hkm | match goal with |- ?g => idtac "KEPT-APPLY" g; fail end];
      [ lia
      | intros Hx; first [clear - Ha Hx Hsp1 Hceil TT C1 C3 HFhigh HF8lo HF8hi HFq HF8 HF4096 HFceil; zone_lia | match goal with |- ?g => let t := type of Ha in idtac "KEPT-DEST" g t; fail end]
      | unfold ESTACK; intros Hx; first [clear - Ha Hx Hsp1 Hceil TT C1 C3 HFhigh HF8lo HF8hi HFq HF8 HF4096 HFceil; zone_lia | match goal with |- ?g => let t := type of Ha in idtac "KEPT-WIN" g t; fail end] ]
    | intros a Ha; revert Ha; evalE AG; intros Ha;
      first [ exfalso; lia | apply HJ3pres; lia | apply (proj1 (HF3pres a ltac:(lia)))
            | replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia; apply (proj1 (HFS3pres (a - (SB + F / 8)) ltac:(unfold SB in *; lia)))
            | match goal with |- ?g => let t := type of Ha in idtac "KEPT-PRES" g t; fail end ] ]).
pose proof (same_io_materialized _ _ Hsbm) as Hio3. clear HJ HP2 HP3 Hkm Hpr Hsbm. rename HJ3 into HJ.
(* dot[] = F + 64 .. F + 96, eight zero ints after the memset *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 64 96 64 96
    [YP09.mkChunk 64 (CVal 4 (SLit 0)); YP09.mkChunk 68 (CVal 4 (SLit 0)); YP09.mkChunk 72 (CVal 4 (SLit 0));
     YP09.mkChunk 76 (CVal 4 (SLit 0)); YP09.mkChunk 80 (CVal 4 (SLit 0)); YP09.mkChunk 84 (CVal 4 (SLit 0));
     YP09.mkChunk 88 (CVal 4 (SLit 0)); YP09.mkChunk 92 (CVal 4 (SLit 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          evalE AG; split; [lia|]; split; [lia|]; split;
          [ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HF3pres (F + o) ltac:(lia)))
          | repeat apply Forall_cons; try apply Forall_nil;
            (apply (chunk_ok_val tfibsegs Ev _ F _ 4 (SLit 0) 0); [reflexivity | zside | zside |]);
            apply oc_val_mem_zero4; intros ii Hii;
            match goal with |- context [F + ?o + ii] =>
              replace (F + o + ii) with (F + 64 + (o - 64 + ii)) by lia; rewrite (Hdst (o - 64 + ii) ltac:(lia)) end;
            reflexivity ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          change (fs_frame_bytes 1 / 8) with 16; evalE AG; unfold SB;
          clear - Hsp1 Hceil Hwlo Hwhi H47 TT C1 C3 HF4096 HFceil HFhigh HFimg HF8lo HF8hi HFq HF8; repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear Hdst.
(* A7: 0x83f3c .. 0x83f44: s2 = 0, s3 = '.', s7 = s6; stop at the loop head 0x83f48 *)
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x83f48. { oc_awr. }
oc_kstep oc_winP.
(* the join to the loop head ss_L 0: the cursor q into atom 300 *)
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_agree tfibsegs 300 Ev (havoc Ev 300 [Z_to_bv 64 (bv_unsigned (getr regs 10))]) ssv msv HS
    (env_agree_havoc_ge 300 300 Ev Ev _ ltac:(lia) (env_agree_refl 300 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv. oc_hae HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E300 : ew Ev 300 = Z_to_bv 64 (bv_unsigned (getr regs 10)))
    by (rewrite HEv; exact (ew_havoc_new _ 300 [Z_to_bv 64 (bv_unsigned (getr regs 10))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
rreg HS (22%bv : bv 5) R22. rreg HS (23%bv : bv 5) R23.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (22%bv : bv 5) (SOff 300 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E300, R22; rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); apply Z_to_bv_bv_unsigned)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (23%bv : bv 5) (SOff 300 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E300, R23; rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); apply Z_to_bv_bv_unsigned)) as HS3;
  clear HS; rename HS3 into HS end.
clear R22 R23.
oc_join HS (ss_L 0).
change OC_RT with 400%nat in HS.
rebaseE HS AG HEv. oc_hae HEv. clear HEv.
(* the boundary: the context with the frame's position, its environment, its carried state, INV_L 0 *)
set (cx := mkOC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj pos).
change (oc_post B MT (mkOC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj pos0)) with (oc_post B MT cx).
lazymatch goal with HS : st_ok _ ?Ev _ (restrict (w_H W) ?msx) |- SRr _ _ (mkCfg _ ?mdx) _ =>
  eapply (HL (length tb) cx Ev lyc S2 W msx mdx) end.
- exact Hpre0.
- split; [subst E; exact HAE|].
  split; [rewrite (AG 32%nat) by lia; exact E32o|].
  split; [exact E70|]. split; [unfold oc_F, cx; cbn [o_lyc o_pos]; rewrite <- HFeq; exact RF|].
  split; [unfold oc_FL, cx; cbn [o_lyc o_pos]; rewrite <- HFLeq; exact E87|].
  unfold oc_F, cx; cbn [o_lyc o_pos]; rewrite <- HFeq; exact E88.
- split; [exact HJ|]. split; [exact Hfrs2|]. split; [exact Hnin|].
  destruct (cw_frame_start MT MTL MTF B lyc Sc S2 (ex_intro _ f ES2)) as (HPm & HMo).
  split; [exact HPm|]. split; [exact HMo|]. split; [cw_io|]. exact HK.
- exists 0%nat, [], (repeat 0 8). split; [rewrite E300, H10; unfold w64; rewrite Z_to_bv_bv_unsigned; f_equal; cbn; lia|]. split; [split; intros kk Hk; lia|].
  split; [|cbn; lia].
  destruct Hcstr as (_ & _ & Hin0 & _).
  split; [destruct tb; [destruct Hin0 | cbn; lia]|]. split; [intros j Hj; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact codec_text.ct_inv_0|].
  split; [constructor|]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. left; exact Hx.
- exact HS.
Qed.
End oc.
