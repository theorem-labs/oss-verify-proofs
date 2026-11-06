(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module names changed; 315 of its 343 lines of code are new or changed and 262 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostReq.v at b561c36fcf63; ported to
   reac-pw/fuzz_rate's image A: rate's pcs, registers (s9 = &pp->corrupt, s6 / s7 the shadow byte and the address of
   &pp->len, s10 = len, s2 = K) and 20-entry value list, the tail split at 0x828ac (w10_tail8), the lane kit
   RtPgPostK and RtPgMem's / RtPgSteps' lemmas in place of role's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPostReq.v, with its module paths, module names and addresses changed; 188 of its 280 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostReq.v at 01f4363fe7d, for image B of
   reac-pw/fuzz_headamp: w10_ -> hw10_, rs_ -> hsu_ (the cut states of lib/AU/HPgSeg.v), rm_ -> hm_; the engine runs
   walk image B's own code, whose shadow address of pp->len is reloaded from R+0x150 and whose pod block is reached
   from the one atom s2 = pp (t2 and s8 pinned to pp + 0x4000 and pp + 0x4d18). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the end of the build segment of
   LLVMFuzzerTestOneInput (0x80c40), pod.h:447 and fuzz.h:73. Proves no function (kind: segment lemma).
   THE CODE (registers: s1 = R, s2 = pp, s8 = pp + 0x4d18, t2 = pp + 0x4000, s11 = K)
     0x82ec8 srli a0,s8,3 / add a0,a0,s11 / lb a0,0(a0)     the shadow byte of &pp->corrupt
     0x82ed4 bnez a0 -> 0x83b24                             its second test (andi a1,s8,7; addi a1,a1,3; blt a1,a0)
     0x82ed8 addi a0,zero,1 / 0x82edc sw a0,0(s8)          pp->corrupt = 1
     0x82ee0 ld a0,0x150(s1) / lbu a0,0(a0)                 the shadow byte of &pp->len (R+0x150 holds its address)
     0x82ee8 beqz a0 -> 0x82ef0, else j 0x83db4             the report
     0x82ef0 ld s5,0(t2)                                    len = pp->len
     0x82ef4 seqz a0,s5 / 0x82ef8 add a0,s5,a0              the second request, len + (len == 0)
     0x82efc jal malloc                                     the cut C2 (headamp_build_contract's end), not run here
   Each instrumented check is one shadow load of the engine's token path (lib/Reusable/YCbn.v): the bytes at
   &pp->corrupt and &pp->len lie in the first block, whose 19744 bytes are one shadow entry of the engine (they are
   marked usable, HPgMem.hm_blk_ra), so each load reads 0 and no check reaches its second test or its report.
   hw10_tail: from 0x82ee0 (the no-corruption arms of the post piece and the corruption's end) to C2;
   hw10_req: the statement hsu_piece_W10_req_stmt (lib/AU/HPgSeg.v), RT -> C2: the store of corrupt = 1, then
   hw10_tail. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW10Kit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* the regions of the tail: the cell R+0x150 (pp->len's shadow address) and pp->len *)
Definition hw10_r150 : YP09.region := YP09.mkRegion (Some 9%nat) 0x150 0x158 0 0 [YP09.mkChunk 0x150 (CVal 8 (hw10_sh 18 0x4000))].
Definition hw10_rlen : YP09.region := YP09.mkRegion (Some 18%nat) 0x4000 0x4008 0 0 [YP09.mkChunk 0x4000 (CVal 8 (SOff 32 0))].
(* t2 = pp + 0x4000 and s8 = pp + 0x4d18, pinned to the atom of s2 = pp *)
Definition hw10_sr_post : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 7) (SOff 18 0x4000)) (Z_to_bv 5 24) (SOff 18 0x4d18).

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- 0x82ee0 -> C2 ---- *)
Lemma hw10_tail : forall (cx : hsu_scx rsegs) POST rest ly2 S2 (W2 : world rsegs) regs2 mem2 md2,
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_from_C2 rsegs B MT headamp_himg_B cx POST rest ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
  hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_post rsegs cx) ->
  hsu_fsh_at rsegs cx W2 mem2 (hsu_P0 headamp_himg_B) ->
  hsu_pp_at rsegs cx W2 mem2 (pp_bytes (fst (pod_build rest))) ->
  e_len (x_e cx) = hd_len rest ->
  SRr rsegs W2 (cfg_at rsegs HW10_TAIL regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 HP HC2 HC HL Hfsh Hpp Hlen.
pose proof hw10_wx as Hwx. pose proof hw10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hin & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
destruct (hw10_F_ctx B cx _ HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hw10_rec_facts rest) as (Hwf & Hb & He & Hs).
pose proof (hw10_len_bounds rest) as HLb.
set (L := hd_len rest) in *.
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 L).
{ exact (hm_pp_len rsegs (buf (fst (pod_build rest))) _ _ _ _ _ Hb He Hs (w_H W2) mem2 (e_pp (x_e cx)) Hpp). }
pose proof HL as HL0.
unfold hsu_at_cx, hsu_at, hsu_L_post in HL. cbv zeta in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P27 & P7 & P18 & P24 & Q08 & Q18 & Q20 & Q38 & Q48 & Qe0 & Q108 & Q120 & Q148 & Q150 & _).
cbn [fst snd hd_at hd_xv] in P8, P9, P19, P27, P7, P18, P24, Q150.
pose proof HC as (HJ & _).
assert (HR0 : 0 <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= 2 ^ 47) by (unfold T_SEG_STK, ASTACK in *; lia).
remember (Ereg regs2 [Z_to_bv 64 L]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E18 : ew E 18 = Z_to_bv 64 (e_pp (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact P18).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (Hsh : 0 <= shadow_addr (e_pp (x_e cx) + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (e_pp (x_e cx) + 0x4000) 8 ltac:(lia) ltac:(lia)).
  assert ((e_pp (x_e cx) + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (HS : st_ok rsegs E (mkSS HW10_TAIL hw10_sr_post [hw10_r150; hw10_rlen] None
  (mkFacts [(18%nat, mkAF 4096 HW10_PPHI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_TAIL) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - unfold hw10_sr_post. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | |] | |].
    + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
    + rewrite (hw10_den_off _ 18 _ 0x4000 E18). exact P7.
    + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
    + rewrite (hw10_den_off _ 18 _ 0x4d18 E18). exact P24.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0x150 8 _ (shadow_addr (e_pp (x_e cx) + 0x4000))).
      * apply (hw10_den_sh _ 18 (e_pp (x_e cx)) 0x4000 E18); [lia | lia | exact E27].
      * cbn. lia.
      * cbn. lia.
      * unfold Layout.OFF_LEN in Q150. rewrite Z.mod_small in Q150 by lia. exact Q150.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 18 (e_pp (x_e cx))); [rewrite E18; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (e_pp (x_e cx)) 0x4000 8 (SOff 32 0) L).
      * exact (hw10_den_atom _ 32 L E32). * cbn. lia. * cbn. lia. * exact HLv.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd hw10_r150 hw10_rlen].
    rewrite E9, E18, !unsigned_lit_small by lia.
    unfold T_SEG_STK, ASTACK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, E27, E32, !unsigned_lit_small by (unfold SHADOW_OFF, HW10_PPHI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, HW10_PPHI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 4) with 16. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. exact Hal. }
assert (SHOK : sh_ok rsegs hw10_Bx [mkSHE 18 0 0x4d20] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 18 0 0x4d20 HAR Hin);
  change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
  rewrite (hw10_U_atom E 18 _ E18 ltac:(lia)); lia. }
assert (HAE0 : env_agree 33 E E) by apply env_agree_refl.
unfold cfg_at. change (w64 HW10_TAIL) with (Z_to_bv 64 HW10_TAIL).
aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_C2.
all: try solve [awr_ok_tac].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ =>
  assert (HAE : env_agree 33 E E') by env_agree_chain HAE0;
  assert (HAE32 : env_agree 32 (Ereg regs2 [Z_to_bv 64 L]) E')
    by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia) end.
(* the run's end, at C2 *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn in Hrb; lia. }
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2) [Z_to_bv 5 7; Z_to_bv 5 10; Z_to_bv 5 21; Z_to_bv 5 24] HS HAE32
  ltac:(vm_compute; reflexivity)) as RK.
assert (RK7 : getr (ms_regs ms) (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 33 (SOff 18 0x4000) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (hw10_den_off _ 18 _ 0x4000 E18). symmetry. exact P7. }
assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 33 (SOff 18 0x4d18) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_len (x_e cx))).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 33 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite Hlen. exact (hw10_den_atom _ 32 L E32). }
assert (R21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (e_len (x_e cx))).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 21) 33 (SOff 32 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite Hlen. exact (hw10_den_atom _ 32 L E32). }
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
unfold hsu_from_C2 in HC2. apply (HC2 ly2 S2). unfold hsu_cut_C2.
split; [|split; [|split; [|split]]].
- apply (hw10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
  + intros r Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply hw10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply HPgSteps.same_io_wvb.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- apply (hw10_L2_of_post cx (w_H W2) (ms_mem ms) (ms_regs ms)); [| exact R10 | exact R21 | lia].
  apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold hsu_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
    first [ exact RK7 | exact RK24
          | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) (hsu_P0 headamp_himg_B) Hfsh).
  intros i Hi. apply HK. change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia.
- apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_pp (x_e cx)) _ Hpp).
  intros x Hx. apply HK. try rewrite length_map in Hx. rewrite (length_pp_bytes _ Hwf) in Hx. unfold PP_SIZE in Hx. lia.
- exact Hlen.
Qed.

(* ---- RT -> C2: corrupt = 1, then the tail ---- *)
Theorem hw10_req : hsu_piece_W10_req_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
unfold hsu_piece_W10_req_stmt. intros cx POST rest Hst HC2.
unfold hsu_from_RT. intros ly2 S2 W2 regs2 mem2 md2 sh ps off bs r HRT.
destruct Hst as (HP & _ & _ & _).
destruct HRT as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hoff & Hob & Hb7).
pose proof hw10_wx as Hwx. pose proof hw10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
destruct (hw10_F_ctx B cx _ HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
unfold hsu_plen in Hob.
pose proof HL as HL0.
unfold hsu_at_cx, hsu_at, hsu_L_post in HL. cbv zeta in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P27 & P7 & P18 & P24 & Q08 & Q18 & Q20 & Q38 & Q48 & Qe0 & Q108 & Q120 & Q148 & Q150 & _).
cbn [fst snd hd_at hd_xv] in P8, P9, P19, P27, P7, P18, P24.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E18 : ew E 18 = Z_to_bv 64 (e_pp (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact P18).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (HS : st_ok rsegs E (mkSS HW10_RT (sr_set sr_atoms (Z_to_bv 5 24) (SOff 18 0x4d18))
  [YP09.mkRegion (Some 18%nat) 0x4d18 0x4d1c 0x4d18 0x4d1c []] None
  (mkFacts [(18%nat, mkAF 4096 HW10_PPHI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_RT) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    rewrite (hw10_den_off _ 18 _ 0x4d18 E18). exact P24.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ (w_H W2) mem2 18 (e_pp (x_e cx))).
    + rewrite E18. apply unsigned_lit_small. lia.
    + lia. + lia.
    + intros o Ho. apply Hpres. lia.
    + constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, E27, !unsigned_lit_small by (unfold SHADOW_OFF, HW10_PPHI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, HW10_PPHI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 4) with 16. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. exact Hal. }
(* the first block's bytes are one shadow entry of the engine: they are marked usable *)
assert (SHOK : sh_ok rsegs hw10_Bx [mkSHE 18 0 0x4d20] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 18 0 0x4d20 HAR Hinp);
  change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
  rewrite (hw10_U_atom E 18 _ E18 ltac:(lia)); lia. }
assert (HAE0 : env_agree 33 E E) by apply env_agree_refl.
unfold cfg_at. change (w64 (bi_RT headamp_bld_B)) with (Z_to_bv 64 HW10_RT).
aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_TAIL.
all: try solve [eapply (hw10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 18%nat (e_pp (x_e cx)) (e_pp (x_e cx)));
  [reflexivity | rewrite E18; apply unsigned_lit_small; lia | exact Hinp | exact Hfresh | cbn; lia
  | cbn; unfold PP_SIZE; lia | apply awr_ok_nil]].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ =>
  assert (HAE : env_agree 33 E E') by env_agree_chain HAE0;
  assert (HAE32 : env_agree 32 (Ereg regs2 []) E')
    by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia) end.
set (pc0 := e_pp (x_e cx) + 0x4d18) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pc0 <= a < pc0 + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. rewrite E18 in Hrb.
  rewrite unsigned_lit_small in Hrb by lia. apply Hn. subst pc0. lia. }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) pc0 4 1).
{ pose proof (HPgSteps.st_ok_region_at _ _ _ 0 _ HS eq_refl) as HR0.
  replace pc0 with (e_pp (x_e cx) + 0x4d18) by reflexivity.
  apply (hw10_field _ _ 18 (e_pp (x_e cx)) _ 0x4d18 0x4d1c 0x4d18 0x4d1c 0x4d18 4 (SLit 1) 1 HR0);
    [| left; reflexivity | reflexivity | cbn; lia | cbn; lia].
  transitivity (bv_unsigned (ew E 18)); [f_equal; exact (proj1 HAE 18%nat ltac:(lia)) | rewrite E18; apply unsigned_lit_small; lia]. }
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 24] HS HAE32
  ltac:(vm_compute; reflexivity)) as RK.
assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 33 (SOff 18 0x4d18) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia|]. subst pc0. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hnew : hsu_pp_at rsegs cx W2 (ms_mem ms) (pp_bytes (fst (pod_build rest)))).
{ rewrite Htie, <- (hw10_img_corrupt sh ps off bs Hwf ltac:(lia) ltac:(lia)).
  replace bs with (firstn (Z.to_nat (Z.of_nat (length bs))) bs) at 1 by (rewrite Nat2Z.id; apply firstn_all).
  fold (hsu_img_corr sh ps off bs (Z.of_nat (length bs))). unfold le32.
  assert (Himg : Z.of_nat (length (hsu_img_corr sh ps off bs (Z.of_nat (length bs)))) = PP_SIZE).
  { unfold hsu_img_corr. apply length_pp_image; [| exact HW3 | exact HW4].
    rewrite length_overwrite; [unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
  apply (hm_bytes_store rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_pp (x_e cx)) _ (Z.to_nat OFF_CORRUPT) 4 1 Hpp).
  - replace (e_pp (x_e cx) + Z.of_nat (Z.to_nat OFF_CORRUPT)) with pc0 by (subst pc0; unfold OFF_CORRUPT; lia). exact HV.
  - unfold OFF_CORRUPT, PP_SIZE in *. lia.
  - intros y Hy Hn. rewrite Himg in Hy. apply HK; [unfold PP_SIZE in *; lia|]. subst pc0. unfold OFF_CORRUPT in Hn. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (hw10_tail cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2).
- apply (hw10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun a => pc0 <= a < pc0 + 4) HC HJ).
  + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply hw10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply HPgSteps.same_io_wvb.
  + exact HK.
  + intros a Ha. right. subst pc0. unfold PP_SIZE. lia.
- apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold hsu_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
    first [ exact RK24
          | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) (hsu_P0 headamp_himg_B) Hfsh).
  intros i Hi. change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia|].
  pose proof (hw10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs. subst pc0. unfold PP_SIZE in Hs. lia.
- exact Hnew.
- exact Hlen.
Qed.
End r.

Print Assumptions hw10_tail.
Print Assumptions hw10_req.
