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
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the end of the build segment of
   LLVMFuzzerTestOneInput (0x80714), pod.h:447, fuzz_rate.c:245 and fuzz.h:73. Proves no function (kind: segment
   lemma).
   THE CODE
     0x82888 srli a0,s9,3 / add a0,a0,s2 / lb a0,0(a0)     the shadow byte of &pp->corrupt (s9 = pp + 0x4d18)
     0x82894 bnez a0 -> 0x831f4                             its second test (andi a1,s9,7; addi a1,a1,3; blt a1,a0)
     0x82898 addi a0,zero,1 / 0x8289c sw a0,0(s9)          pp->corrupt = 1
     0x828a0 lbu a0,0(s6) / bnez a0 -> 0x835e4              the shadow byte of &pp->len (s6 = (pp + 0x4000 >> 3) + K)
     0x828a8 ld s10,0(s7)                                   len = pp->len (s7 = pp + 0x4000)
     0x828ac seqz a0,s10 / 0x828b0 add a0,s10,a0            the second request, len + (len == 0)
     0x828b4 jal (the malloc wrapper)                       the cut C2 (rate_build_contract's end), not run here
   Each instrumented check is one shadow obligation of the engine's token path (lib/Reusable/YCbn.v): the 4 bytes at
   &pp->corrupt and the 8 at &pp->len lie in the first block, whose bytes are marked usable (RtPgMem.rtm_blk_ra), so
   the error path is not reached.
   w10_tail8: from 0x828ac (len in s10) to C2;
   w10_tail: from 0x828a0 (the no-corruption arms of the piece and the corruption's end): the len load, then
   w10_tail8;
   w10_req: RtPgSeg's rs_piece_W10_req_stmt, RT -> C2: the store of corrupt = 1, then w10_tail. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg RtPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSteps RtPgPostK.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the value of a chunk of a region of a run's state *)
Lemma w10r_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v HR Hn Hc He Hv Hw.
exact (val_of_chunk_ok rsegs E m b od w e v (rts_chunks E m n b cs lo hi wlo whi HR Hn _ Hc) He Hv Hw).
Qed.

(* ---- 0x828ac -> C2: the second request, len + (len == 0) = len ---- *)
Lemma w10_tail8 : forall (cx : rs_scx rsegs) POST rest ly2 S2 (W2 : world rsegs) regs2 mem2 md2,
  rs_pre rsegs B cx -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_post rsegs cx) ->
  getr regs2 (Z_to_bv 5 26) = w64 (q_len (x_e cx)) ->
  rs_fsh_at rsegs cx W2 mem2 rs_P0 ->
  rs_pp_at rsegs cx W2 mem2 (pp_bytes (fst (pod_build rest))) -> q_len (x_e cx) = rt_len rest ->
  SRr rsegs W2 (cfg_at rsegs 0x828ac regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 HP HC2 HC HL H26 Hfsh Hpp Hlen.
pose proof w10_wx as Hwx. pose proof w10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hin & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_rec_facts rest) as (Hwf & _ & _ & _).
pose proof (rt_len_bounds rest) as HLb. rewrite <- Hlen in HLb.
pose proof HL as HL0.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E26 : ew E 26 = Z_to_bv 64 (q_len (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact H26).
assert (HS : st_ok rsegs E (mkSS 0x828ac sr_atoms [] None (mkFacts [(26%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x828ac) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E26, !unsigned_lit_small by lia.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia;
    try (rewrite Z.pow_0_r; apply Z.mod_1_r). }
assert (SHOK : sh_ok rsegs W10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 0x828ac) with (Z_to_bv 64 0x828ac).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x828b4.
{ awr_ok_tac. }
(* the run's end, at C2 *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & _). cbn [ss_mem] in Hr. destruct Hr. }
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W2) [Z_to_bv 5 10] HS HAE
  ltac:(vm_compute; reflexivity)) as RK.
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (q_len (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). w10_sr_eval.
  exact (w10_den_atom _ 26 _ E26). }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (q_len (x_e cx))).
{ rewrite (RK (Z_to_bv 5 26)); [exact H26 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
assert (Hcell : forall o i, 0 <= o < 0x1e0 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
unfold rs_from_C2 in HC2. apply (HC2 ly2 S2). unfold rs_cut_C2.
split; [|split; [|split; [|split]]].
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
  + intros r Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply same_io_wvb.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- apply (w10_L2_of_post cx (w_H W2) (ms_mem ms) (ms_regs ms)); [| exact R10 | exact R26 | lia].
  apply (rtm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rs_L_post, rs_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtm_keeps rt_xv];
    first [ (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. apply HK. change (length rs_P0) with 56%nat in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)).
  assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia.
- apply (rtm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_pp (x_e cx)) _ Hpp).
  intros x Hx. apply HK. rewrite (length_pp_bytes _ Hwf) in Hx. unfold PP_SIZE in Hx. lia.
- exact Hlen.
Qed.

(* ---- 0x828a0 -> 0x828ac: the shadow test of &pp->len and the len load, then w10_tail8 ---- *)
Lemma w10_tail : forall (cx : rs_scx rsegs) POST rest ly2 S2 (W2 : world rsegs) regs2 mem2 md2,
  rs_pre rsegs B cx -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_post rsegs cx) -> rs_fsh_at rsegs cx W2 mem2 rs_P0 ->
  rs_pp_at rsegs cx W2 mem2 (pp_bytes (fst (pod_build rest))) -> q_len (x_e cx) = rt_len rest ->
  SRr rsegs W2 (cfg_at rsegs 0x828a0 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 HP HC2 HC HL Hfsh Hpp Hlen.
pose proof w10_wx as Hwx. pose proof w10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hin & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_rec_facts rest) as (Hwf & Hb & He & Hs).
pose proof (rt_len_bounds rest) as HLb.
set (L := rt_len rest) in *.
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 L).
{ exact (rtm_pp_len rsegs (buf (fst (pod_build rest))) _ _ _ _ _ Hb He Hs (w_H W2) mem2 (q_pp (x_e cx)) Hpp). }
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_post, rs_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P20 & P18 & P23 & P27 & P22 & P25 & Q18 & Q78 & Q58 & Qa8 & Qb8 & Qc0
  & Q20 & Q38 & Q40 & Q48 & Q50 & Q120 & _).
cbn [fst snd rt_at] in P8, P9, P20, P18, P23, P27, P22, P25.
pose proof HC as (HJ & _).
remember (Ereg regs2 [Z_to_bv 64 L]) as E eqn:HE.
assert (E23 : ew E 23 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact P18).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (HS : st_ok rsegs E (mkSS 0x828a0
  (sr_set sr_atoms (Z_to_bv 5 22) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)))
  [YP09.mkRegion (Some 23%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(23%nat, mkAF 4096 W10_HI 4); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x828a0) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
    rewrite (w10_den_sh _ 23 18 (q_pp (x_e cx) + 0x4000) E23 ltac:(lia) E18). exact P22.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtm_ro_region rsegs _ (w_H W2) mem2 23 (q_pp (x_e cx) + 0x4000)).
    + rewrite E23. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (q_pp (x_e cx) + 0x4000) 0 8 (SOff 32 0) L).
      * exact (w10_den_atom _ 32 L E32). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact HLv.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E23, E18, E32, !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity. }
assert (SHOK : sh_ok rsegs W10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 0x828a0) with (Z_to_bv 64 0x828a0).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x828ac.
{ (* the shadow obligation of the 8-byte load of pp->len *)
  apply (w10_ob_blk B ly2 S2 W2 mem2 md2 E (q_pp (x_e cx)) PP_SIZE (q_pp (x_e cx) + 0x4000) 8 (SOff 23 0) HAR Hin);
  [lia | change (req_size PP_SIZE) with 19744; lia
  | exact (w10_U_atom E 18 SHADOW_OFF E18 ltac:(unfold SHADOW_OFF; lia))
  | exact (w10_U_atom E 23 _ E23 ltac:(lia))]. }
{ awr_ok_tac. }
(* the run's end, at 0x828ac *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn in Hrb. lia. }
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 L]) (ewset E 33 w))
  by (subst E; eapply env_agree_le; [|apply env_agree_ewset]; lia).
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 [Z_to_bv 64 L] (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 26; Z_to_bv 5 22]
  HS HAE ltac:(vm_compute; reflexivity)) as RK.
assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = getr regs2 (Z_to_bv 5 22)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 22) HS). w10_sr_eval.
  rewrite (sv_denot_agree 33 E (ewset E 33 w)); [| apply env_agree_ewset | reflexivity].
  rewrite (w10_den_sh _ 23 18 (q_pp (x_e cx) + 0x4000) E23 ltac:(lia) E18). symmetry. exact P22. }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (q_len (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 26) HS). w10_sr_eval.
  rewrite (w10_den_atom _ 32 L); [rewrite Hlen; reflexivity|]. rewrite ew_ewset_other by lia. exact E32. }
assert (Hcell : forall o i, 0 <= o < 0x1e0 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (w10_tail8 cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2).
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
  + intros r Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply same_io_wvb.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- apply (rtm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rs_L_post, rs_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtm_keeps rt_xv];
    first [ exact R22
          | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- exact R26.
- apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. apply HK. change (length rs_P0) with 56%nat in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)).
  assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia.
- apply (rtm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_pp (x_e cx)) _ Hpp).
  intros x Hx. apply HK. rewrite (length_pp_bytes _ Hwf) in Hx. unfold PP_SIZE in Hx. lia.
- exact Hlen.
Qed.

(* ---- RT -> C2: corrupt = 1, then the tail ---- *)
Theorem w10_req : rs_piece_W10_req_stmt rsegs B MT.
Proof.
unfold rs_piece_W10_req_stmt. intros cx POST rest Hst HC2.
unfold rs_from_RT. intros ly2 S2 W2 regs2 mem2 md2 sh ps off bs r HRT.
destruct Hst as (HP & _).
destruct HRT as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hoff & Hob & Hb7).
pose proof w10_wx as Hwx. pose proof w10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
unfold rs_plen in Hob.
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_post, rs_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P20 & P18 & P23 & P27 & P22 & P25 & Q18 & Q78 & Q58 & Qa8 & Qb8 & Qc0
  & Q20 & Q38 & Q40 & Q48 & Q50 & Q120 & _).
cbn [fst snd rt_at] in P8, P9, P20, P18, P23, P27, P22, P25.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact P18).
assert (E25 : ew E 25 = Z_to_bv 64 (q_pp (x_e cx) + 0x4d18))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 25 (Z_to_bv 5 25) eq_refl); exact P25).
assert (HS : st_ok rsegs E (mkSS 0x82888 sr_atoms
  [YP09.mkRegion (Some 25%nat) 0 4 0 4 []] None
  (mkFacts [(25%nat, mkAF 4096 W10_HI 3); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82888) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtm_rw_region rsegs _ (w_H W2) mem2 25 (q_pp (x_e cx) + 0x4d18)).
    + rewrite E25. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + intros o Ho. apply Hpres. lia.
    + constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, E25, !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 3) with 8. rewrite Z.add_mod by lia.
    assert (Hm8 : q_pp (x_e cx) mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (2 * q). lia. }
    rewrite Hm8. reflexivity. }
(* the write window [pp + 0x4d18, + 4) is a shadow entry of the engine: its bytes are marked usable *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 25 0 4] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (q_pp (x_e cx)) PP_SIZE 25 0 4 HAR Hinp);
  change (req_size PP_SIZE) with 19744;
  [exact Happ | exact (w10_U_atom E 18 SHADOW_OFF E18 ltac:(unfold SHADOW_OFF; lia)) | | | lia];
  rewrite (w10_U_atom E 25 _ E25 ltac:(lia)); lia. }
unfold cfg_at. change (w64 RS_RT) with (Z_to_bv 64 0x82888).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x828a0.
{ eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 25%nat (q_pp (x_e cx) + 0x4d18) (q_pp (x_e cx)));
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | apply awr_ok_nil].
  rewrite E25. apply unsigned_lit_small. lia. }
set (pc0 := q_pp (x_e cx) + 0x4d18) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pc0 <= a < pc0 + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. rewrite E25 in Hrb.
  rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) pc0 4 1).
{ pose proof (rts_region_nth _ _ ms 0 _ (w_H W2) HS eq_refl) as HR0.
  replace pc0 with (pc0 + 0) by lia.
  apply (w10r_field _ _ 25 pc0 _ 0 4 0 4 0 4 (SLit 1) 1 HR0); [| left; reflexivity | reflexivity | cbn; lia | cbn; lia].
  rewrite !ew_ewset_other by lia. rewrite E25. apply unsigned_lit_small. lia. }
assert (HE0 : env_agree 32 (Ereg regs2 []) (ewset (ewset E 32 w) 33 w0)).
{ subst E. eapply env_agree_trans; [apply env_agree_ewset|]. eapply env_agree_le; [|apply env_agree_ewset]. lia. }
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 11] HS HE0
  ltac:(vm_compute; reflexivity)) as RK.
assert (Hcell : forall o i, 0 <= o < 0x1e0 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia|]. subst pc0. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Himg : Z.of_nat (length (rs_img_corr sh ps off bs (Z.of_nat (length bs)))) = PP_SIZE).
{ unfold rs_img_corr. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
assert (Hnew : rs_pp_at rsegs cx W2 (ms_mem ms) (pp_bytes (fst (pod_build rest)))).
{ rewrite Htie, <- (w10_img_corrupt sh ps off bs Hwf ltac:(lia) ltac:(lia)).
  replace bs with (firstn (Z.to_nat (Z.of_nat (length bs))) bs) at 1 by (rewrite Nat2Z.id; apply firstn_all).
  fold (rs_img_corr sh ps off bs (Z.of_nat (length bs))). unfold le32.
  apply (rtm_bytes_store rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_pp (x_e cx)) _ (Z.to_nat OFF_CORRUPT) 4 1 Hpp).
  - replace (q_pp (x_e cx) + Z.of_nat (Z.to_nat OFF_CORRUPT)) with pc0 by (subst pc0; unfold OFF_CORRUPT; lia).
    exact HV.
  - unfold OFF_CORRUPT, PP_SIZE in *. lia.
  - intros y Hy Hn. apply HK; [unfold PP_SIZE in *; lia|]. subst pc0. unfold OFF_CORRUPT in Hn. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (w10_tail cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2).
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun a => pc0 <= a < pc0 + 4) HC HJ).
  + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply same_io_wvb.
  + exact HK.
  + intros a Ha. right. subst pc0. unfold PP_SIZE. lia.
- apply (rtm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rs_L_post, rs_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtm_keeps rt_xv];
    first [ (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. change (length rs_P0) with 56%nat in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)).
  assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia|].
  pose proof (w10_shadow_not_pp (q_pp (x_e cx)) (q_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hsh.
  subst pc0. unfold PP_SIZE in Hsh. lia.
- exact Hnew.
- exact Hlen.
Qed.
End r.

Print Assumptions w10_tail8.
Print Assumptions w10_tail.
Print Assumptions w10_req.
