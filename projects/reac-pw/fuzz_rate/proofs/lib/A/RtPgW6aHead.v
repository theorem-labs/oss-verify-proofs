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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 186 of its 214 lines of code are new or changed and 262 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at ef33766f272a; ported to
   reac-pw/fuzz_rate's image A: module paths changed (images.Asan instead of lib/A/Img0, RtPgSteps instead of
   RPgCfgChanges); the pcs, the cells (k into [R+0x128], the address of e in [R+0x138]) and the shadow base register
   (s4 = x20 instead of s3) are rate's; the local helpers that lib/A/RtPgSteps.v states (rts_fdiv, rts_fbounds,
   rts_fsh_of, rts_fmod8, rts_den_atom, rts_callee, rts_val_kept, rts_chunk0, rts_region_nth, rts_chunks,
   rts_intrin_at) are taken from there; the post is rts_post with rts_caller_saved. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the block lemma w6_head of
   lib/A/RtPgW6aBase.v, the pod loop's head C 0x8127c of LLVMFuzzerTestOneInput through the memset of e (pod.h:279):
     0x8127c  sd a1,0x128(s1)                 [R+0x128] := k
     0x81280 .. 0x812b0  13 x sb zero,o(s4)   shadow_addr F + 0x1e .. 0x2a := 0
     0x812b4  addi a2,zero,0x68; 0x812b8 ld a0,0x138(s1); 0x812bc mv a1,zero
     0x812c0  jal 0x51cfc                      __asan_memset(F + 0xf0, 0, 104), back at 0x812c4
   Proves no function (kind: segment lemma).
   HOW. One engine run (lib/Reusable/YCbq.v aj_run_to over w6_tbl) from 0x8127c to the callee's entry 0x51cfc, over
   two regions: the real frame's cells [R+0x128, R+0x140) based at the s1 atom (write window [0x128, 0x130): the
   callers' stack window of the journal), whose chunk at 0x138 is the address of e held in the extra env slot 32; and
   the 13 shadow bytes [0x1e, 0x2b) of the frame (3, pos) based at the s4 atom (write window: the frame's shadow,
   in_frames). No instrumented check is in the block. The call is the Section hypothesis AMEMSET (the kernel's
   contract of __asan_memset, lib/Reusable/YG0d.v aintrin_realizes OSet), applied through lib/A/RtPgSteps.v
   rts_intrin_at (lib/Reusable/YCbq.v aj_intrin_at, which also keeps the callee's same_but_materialized); its
   destination e lies in the owned frame, its shadow is the 13 zero bytes just stored, and the callee's stack
   [R - ESTACK, R) lies in the journal's window. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps RtPgW6aBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments (as lib/A/RtPgSteps.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the entry state of the run ---- *)
(* env slot 32 = F + 0xf0, the address of e that [R+0x138] holds *)
Definition w6h_extra (F : Z) : list word := [w64 (F + 0xf0)].
Definition w6h_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x128 0x140 0x128 0x130 [YP09.mkChunk 0x138 (CVal 8 (SOff 32 0))].
Definition w6h_rS : YP09.region := YP09.mkRegion (Some 20%nat) 0x1e 0x2b 0x1e 0x2b [].
Definition w6h_ss0 : sstate := mkSS W6_C sr_atoms [w6h_rR; w6h_rS] None (mkFacts [] [] []).

(* the shadow hull of e = [F + 0xf0, F + 0x158) lies in the frame's shadow [shadow_addr F + 16, shadow_addr F + 56) *)
Lemma w6h_hull : forall F, F mod 32 = 0 -> forall s,
shadow_addr (F + 0xf0) / 8 * 8 <= s < shadow_addr (F + 0xf0 + 104 - 1) / 8 * 8 + 8 ->
shadow_addr F + 16 <= s < shadow_addr F + 56.
Proof.
intros F H s Hs. destruct (rts_fdiv F H) as [E1 E2]. rewrite E2. remember (F / 32) as q eqn:Hq. clear Hq.
assert (A1 : shadow_addr (F + 0xf0) = SHADOW_OFF + 4 * q + 30).
{ unfold shadow_addr. rewrite E1. replace (32 * q + 0xf0) with ((4 * q + 30) * 8) by ring. rewrite Z.div_mul by lia. ring. }
assert (A2 : shadow_addr (F + 0xf0 + 104 - 1) = SHADOW_OFF + 4 * q + 42).
{ unfold shadow_addr. rewrite E1. replace (32 * q + 0xf0 + 104 - 1) with ((4 * q + 42) * 8 + 7) by ring.
  rewrite Z.div_add_l by lia. change (7 / 8) with 0. ring. }
rewrite A1, A2 in Hs. clear A1 A2 E1 E2.
pose proof (Z.div_mod (SHADOW_OFF + 4 * q + 30) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + 4 * q + 30) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + 4 * q + 42) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + 4 * q + 42) 8 ltac:(lia)) as M2.
lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* __asan_memset at 0x51cfc: the kernel's contract of the intrinsic *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6_MEMSET.

Lemma w6_head : w6_head_stmt B MT.
Proof using MTL LAWS AMEMSET.
unfold w6_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos kk pat
(HJ & HR16 & HRs & HRlo & Hown & HF & Hrom) H2 H9 H20 H3 H4 H11 Hvf _ _.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in HRlo.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (Hal32 & Happ & _ & Hfsh).
rewrite <- HF in Hal32, Happ, Hfsh.
change (fs_frame_bytes 3) with 512 in Happ. change (fs_frame_bytes 3 / 8) with 64 in Hfsh.
destruct (rts_fbounds F Hal32 Happ) as (HF0 & HFc & Hsa0 & Hsac & Hsep & HamrF).
pose proof (HamrF 0xf0 104 ltac:(lia) ltac:(lia) ltac:(lia)) as Hamr. clear HamrF.
pose proof (rts_fmod8 F 30 Hal32) as Hm8. change (8 * 30) with 0xf0 in Hm8.
pose proof (rts_fsh_of F 0xf0 Hal32 ltac:(lia)) as Hshe. change (0xf0 / 8) with 0x1e in Hshe.
clear HAR.
(* the entry state *)
assert (U9 : bv_unsigned (ew (Ereg regs (w6h_extra F)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U20 : bv_unsigned (ew (Ereg regs (w6h_extra F)) 20) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w6h_extra F)) 32 = w64 (F + 0xf0)) by exact (ew_Ereg_extra regs (w6h_extra F) 0).
assert (E11 : ew (Ereg regs (w6h_extra F)) 11 = Z_to_bv 64 (kk mod 2 ^ 64)).
{ rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. symmetry. apply Z_to_bv_mod64. }
assert (HS : st_ok rsegs (Ereg regs (w6h_extra F)) w6h_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_C) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w6h_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, w6h_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0) (F + 0xf0)); [| cbn; lia | cbn; lia | exact Hvf].
        apply rts_den_atom; [exact E32 | lia].
    + unfold region_ok, w6h_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (Hfsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, w6h_rR, w6h_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
remember (Ereg regs (w6h_extra F)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (w6h_extra F)) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 W6_C) with (Z_to_bv 64 W6_C).
(* 0x8127c .. 0x812c0 jal: stop at the callee's entry 0x51cfc *)
aj_run_to w6_tbl_ok HS HJ W6_MEMSET.
{ (* the two write windows: the real frame's cell in the callers' stack window, e's shadow in the frame (3, pos) *)
  change (ss_mem w6h_ss0) with [w6h_rR; w6h_rS]. unfold w6h_rR, w6h_rS.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (shadow_addr F)); [reflexivity | exact U20 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists 3, pos. split; [exact Hown|]. right.
  unfold in_zr; cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 3 / 8) with 64. lia. }
(* after the run: registers, the stored bytes, the bytes kept *)
rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2. rreg HS (1%bv : bv 5) Gra.
lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?ms) =>
  pose proof (regs_kept_of_st_ok rsegs E ss ms regs (w6h_extra F) (w_H W) [1; 10; 11; 12]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK;
  let rR := eval vm_compute in (nth_error (ss_mem ss) 0) in
  let rS := eval vm_compute in (nth_error (ss_mem ss) 1) in
  lazymatch rR with Some ?r1 => lazymatch rS with Some ?r2 =>
    pose proof (rts_region_nth E ss ms 0 r1 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
    pose proof (rts_region_nth E ss ms 1 r2 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRS
  end end;
  rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl) at 1;
  replace (ss_pc ss) with W6_MEMSET by (vm_compute; reflexivity)
end.
assert (NK : forall r : bv 5, existsb (fun c => bv_eqb c r) [1; 10; 11; 12]%bv = false -> ~ In r [1; 10; 11; 12]%bv).
{ intros r Hb Hin. assert (Ht : existsb (fun c => bv_eqb c r) [1; 10; 11; 12]%bv = true)
    by (apply existsb_exists; exists r; split; [exact Hin | apply bv_eqb_refl]).
  rewrite Hb in Ht. discriminate Ht. }
assert (RK2 : getr (ms_regs ms) 2 = getr regs 2)
  by (apply RK; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity]).
assert (RK3 : getr (ms_regs ms) 3 = getr regs 3)
  by (apply RK; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity]).
assert (RK4 : getr (ms_regs ms) 4 = getr regs 4)
  by (apply RK; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity]).
(* [R+0x128] = k and the 13 zero shadow bytes, from the run's last regions *)
assert (VD : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x128) 8 (kk mod 2 ^ 64)).
{ pose proof (rts_chunks E _ 9%nat _ _ _ _ _ _ HRR U9 (YP09.mkChunk 0x128 (CVal 8 (SOff 11 0))) ltac:(cbn; tauto)) as Hc.
  exact (val_of_chunk_ok rsegs E _ R 0x128 8 (SOff 11 0) (kk mod 2 ^ 64) Hc
    (rts_den_atom E 11 _ E11 (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia))) (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia)) ltac:(cbn; lia)). }
assert (Z13 : forall i, 0 <= i < 13 -> aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 0x1e + i) = Some 0).
{ intros i Hi. rewrite <- Z.add_assoc. apply (rts_chunk0 E).
  apply (rts_chunks E _ 20%nat _ _ _ _ _ _ HRS U20).
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
    i = 11 \/ i = 12) by lia.
  repeat (destruct Hc as [Hc | Hc]; [subst i; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  subst i; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x128 <= a < R + 0x130) -> ~ (shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Ha1 Ha2. apply (aview_eq_of rsegs). apply HFr. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hin & Hr). change (ss_mem w6h_ss0) with [w6h_rR; w6h_rS] in Hin. unfold w6h_rR, w6h_rS in Hin.
  cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite U9 in Hr | rewrite U20 in Hr]; lia. }
clear HRR HRS.
(* the frame's shadow is present at the run's last memory (the journal's AR) *)
pose proof HJ as (HAR2 & _).
destruct (al_frames _ _ LAWS lyc Sc W _ _ 3 pos HAR2 Hin3) as (_ & _ & _ & Hfsh2).
rewrite <- HF in Hfsh2. change (fs_frame_bytes 3 / 8) with 64 in Hfsh2.
(* __asan_memset(F + 0xf0, 0, 104) at 0x51cfc *)
eapply SRr_bind.
{ apply (rts_intrin_at B LAWS OSet W6_MEMSET AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0xf0) 0 104 (R - sp0) (w64 W6_RET) HJ).
  - rewrite Ga0, E32. reflexivity.
  - rewrite Ga1. reflexivity.
  - rewrite Ga2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite RK2, H2. unfold w64. rewrite unsigned_lit_small by lia. ring.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite RK3. exact H3.
  - rewrite RK4. exact H4.
  - rewrite Gra. reflexivity.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + right; right; right. exists 3, pos. split; [exact Hown|]. left.
      unfold in_zr; cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 3) with 512. lia.
    + rewrite Hes. lia.
  - exact Hamr.
  - apply zero_shadow_range; [exact Hm8 | reflexivity |].
    intros i Hi. change (104 / 8) with 13 in Hi. rewrite Hshe. exact (Z13 i Hi).
  - intros _ s Hs. destruct (w6h_hull F Hal32 s Hs) as [Hs1 Hs2].
    replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
    apply (aview_some_of_apresent rsegs). exact (proj1 (Hfsh2 (s - shadow_addr F) ltac:(lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & H10 & HSET & KM).
apply SRr_ret.
unfold rts_post. exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (HP2 (bv_unsigned r) (rts_callee r Hr0 Hn)).
  rewrite Z_to_bv_bv_unsigned. apply RK; [exact Hr0|]. intros X. apply Hn. cbv [rts_caller_saved In] in X |- *. tauto. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [apply same_io_wvb | apply same_io_materialized; exact Hsame]|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a Ha Hn. unfold w6_head_wr in Hn.
  rewrite (KM a Ha ltac:(intros X; apply Hn; right; right; right; lia) ltac:(intros X; apply Hn; left; lia)).
  apply KR; [exact Ha | intros X; apply Hn; right; left; exact X | intros X; apply Hn; right; right; left; exact X]. }
split; [exact H10|].
split.
{ apply (rts_val_kept (w_H W) (ms_mem ms) mem2 (R + 0x128) 8 (kk mod 2 ^ 64)); [|exact VD].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply KM; [lia | lia | rewrite Hes; lia]. }
split.
{ intros i Hi. rewrite KM; [exact (Z13 i Hi) | lia | lia | rewrite Hes; lia]. }
intros i Hi. rewrite (HSET i Hi). reflexivity.
Qed.
End d.
End b.

Print Assumptions w6_head.
