(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 187 of its 212 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at ef33766f272a; ported to
   reac-pw/fuzz_rate's image A: module paths changed (images.Asan instead of lib/A/Img0, RtPgSteps instead of
   RPgCfgChanges); the pcs, the cells (k into [R+0x128], the address of e in [R+0x138]) and the shadow base register
   (s4 = x20 instead of s3) are rate's; the local helpers that lib/A/RtPgSteps.v states (rts_fdiv, rts_fbounds,
   rts_fsh_of, rts_fmod8, rts_den_atom, rts_callee, rts_val_kept, rts_chunk0, rts_region_nth, rts_chunks,
   rts_intrin_at) are taken from there; the post is rts_post with rts_caller_saved. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aHead.v at 88912827c774; ported to the
   same unit's image B (fuzz_rate.asan-ubsan): images.AsanUbsan, lib/AU/RtPgStepsB.v (its rtsb_ helpers) and
   lib/AU/RtPgW6aBaseB.v instead of images.Asan, RtPgSteps.v and RtPgW6aBase.v; the pcs are image B's; k goes into
   [R+0x178]; the address of e62 (F + 0x210) is the register s6 (no frame cell, so no extra env slot and no chunk);
   the shadow base is s3 (x19); the frame for locals is class 4 (1024 bytes, 128 shadow bytes) and e62's 13
   granules are shadow_addr F + 66 .. 78. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6aHeadB.v, with its module paths, module names and addresses changed; 39 of its 213 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at ef33766f272a; ported to
   reac-pw/fuzz_rate's image A: module paths changed (images.Asan instead of lib/A/Img0, RtPgSteps instead of
   RPgCfgChanges); the pcs, the cells (k into [R+0x128], the address of e in [R+0x138]) and the shadow base register
   (s4 = x20 instead of s3) are rate's; the local helpers that lib/A/RtPgSteps.v states (rts_fdiv, rts_fbounds,
   rts_fsh_of, rts_fmod8, rts_den_atom, rts_callee, rts_val_kept, rts_chunk0, rts_region_nth, rts_chunks,
   rts_intrin_at) are taken from there; the post is rts_post with rts_caller_saved. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aHead.v at 88912827c774; ported to the
   same unit's image B (fuzz_rate.asan-ubsan): images.AsanUbsan, lib/AU/RtPgStepsB.v (its rtsb_ helpers) and
   lib/AU/RtPgW6aBaseB.v instead of images.Asan, RtPgSteps.v and RtPgW6aBase.v; the pcs are image B's; k goes into
   [R+0x178]; the address of e62 (F + 0x210) is the register s6 (no frame cell, so no extra env slot and no chunk);
   the shadow base is s3 (x19); the frame for locals is class 4 (1024 bytes, 128 shadow bytes) and e62's 13
   granules are shadow_addr F + 66 .. 78. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6aHeadB.v at 265bf27a1874; ported to
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role (lib/AU/Img0.v rsegs,
   lib/A/RPgBase and RPgCSpec, lib/AU/RPgSteps.v's rl_ helpers, lib/AU/RPgW6aBase.v); the pcs are role B's; k goes
   into [R+0x150]; the address of e62 (F + 0x210) is read from the cell [R+0x158] (`ld a0,0x158(s1)`), so the entry
   state has the extra env slot 32 = F + 0x210 and the real frame's region carries the 8-byte chunk of that cell, as
   proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v does for its [R+0xf0]; the memset is checked_memset 0x51608. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the block lemma w6b_head of
   lib/AU/RPgW6aBase.v, the pod loop's head C 0x80b54 of LLVMFuzzerTestOneInput through the memset of e62
   (pod.h:279):
     0x80b54  sd a1,0x150(s1)                 [R+0x150] := k
     0x80b58 .. 0x80b88  13 x sb zero,o(s3)   shadow_addr F + 66 .. 78 := 0 (o = 70 71 72 73 66 67 68 69 74 .. 78)
     0x80b8c  li a2,104; 0x80b90 ld a0,0x158(s1) (= F + 0x210); 0x80b94 li a1,0
     0x80b98  jal 0x51608                      checked_memset(F + 0x210, 0, 104), back at 0x80b9c
   Proves no function (kind: segment lemma).
   HOW. One engine run (lib/Reusable/YCbq.v aj_run_to over w6b_tbl) from 0x80b54 to the callee's entry 0x51608, over
   two regions: the real frame's cells [R+0x150, R+0x160) based at the s1 atom (write window [0x150, 0x158): the
   callers' stack window of the journal), whose chunk at 0x158 is the address of e62 held in the extra env slot 32;
   and the 13 shadow bytes [66, 79) of the frame (4, pos) based at the s3 atom (write window: the frame's shadow,
   in_frames). No instrumented check is in the block. The call is the Section hypothesis AMEMSET (the kernel's
   contract of the memset intrinsic, lib/Reusable/YG0d.v aintrin_realizes OSet), applied through lib/AU/RPgSteps.v
   rl_intrin_at (lib/Reusable/YCbq.v aj_intrin_at, which also keeps the callee's same_but_materialized); its
   destination e62 lies in the owned frame, its shadow is the 13 zero bytes just stored, and the callee's stack
   [R - ESTACK, R) lies in the journal's window. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps RPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry state of the run ---- *)
(* env slot 32 = F + 0x210, the address of e62 that [R+0x158] holds *)
Definition w6bh_extra (F : Z) : list word := [w64 (F + 0x210)].
Definition w6bh_rR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x150 0x160 0x150 0x158 [YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
Definition w6bh_rS : YP09.region := YP09.mkRegion (Some 19%nat) 66 79 66 79 [].
Definition w6bh_ss0 : sstate := mkSS W6B_C sr_atoms [w6bh_rR; w6bh_rS] None (mkFacts [] [] []).

(* the shadow hull of e62 = [F + 0x210, F + 0x278) lies in the frame's shadow [shadow_addr F + 56, shadow_addr F + 88) *)
Lemma w6bh_hull : forall F, F mod 32 = 0 -> forall s,
shadow_addr (F + 0x210) / 8 * 8 <= s < shadow_addr (F + 0x210 + 104 - 1) / 8 * 8 + 8 ->
shadow_addr F + 56 <= s < shadow_addr F + 88.
Proof.
intros F H s Hs. destruct (rl_fdiv F H) as [E1 E2]. rewrite E2. remember (F / 32) as q eqn:Hq. clear Hq.
assert (A1 : shadow_addr (F + 0x210) = SHADOW_OFF + 4 * q + 66).
{ unfold shadow_addr. rewrite E1. replace (32 * q + 0x210) with ((4 * q + 66) * 8) by ring. rewrite Z.div_mul by lia. ring. }
assert (A2 : shadow_addr (F + 0x210 + 104 - 1) = SHADOW_OFF + 4 * q + 78).
{ unfold shadow_addr. rewrite E1. replace (32 * q + 0x210 + 104 - 1) with ((4 * q + 78) * 8 + 7) by ring.
  rewrite Z.div_add_l by lia. change (7 / 8) with 0. ring. }
rewrite A1, A2 in Hs. clear A1 A2 E1 E2.
pose proof (Z.div_mod (SHADOW_OFF + 4 * q + 66) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + 4 * q + 66) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + 4 * q + 78) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + 4 * q + 78) 8 ltac:(lia)) as M2.
lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* checked_memset at 0x51608: the kernel's contract of the intrinsic *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6B_MEMSET.

Lemma w6b_head : w6b_head_stmt B MT.
Proof using MTL LAWS AMEMSET.
unfold w6b_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos kk
(HJ & HR16 & HRs & HRlo & Hown & HF & Hrom) H2 H9 H19 H3 H4 H11 Hvf.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in HRlo.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hal32 & Happ & _ & Hfsh).
rewrite <- HF in Hal32, Happ, Hfsh.
change (fs_frame_bytes 4) with 1024 in Happ. change (fs_frame_bytes 4 / 8) with 128 in Hfsh.
destruct (rl_fbounds F Hal32 Happ) as (HF0 & HFc & Hsa0 & Hsac & Hsep & HamrF).
pose proof (HamrF 0x210 104 ltac:(lia) ltac:(lia) ltac:(lia)) as Hamr. clear HamrF.
pose proof (rl_fmod8 F 66 Hal32) as Hm8. change (8 * 66) with 0x210 in Hm8.
pose proof (rl_fsh_of F 0x210 Hal32 ltac:(lia)) as Hshe. change (0x210 / 8) with 66 in Hshe.
clear HAR.
(* the entry state *)
assert (U9 : bv_unsigned (ew (Ereg regs (w6bh_extra F)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew (Ereg regs (w6bh_extra F)) 19) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w6bh_extra F)) 32 = w64 (F + 0x210)) by exact (ew_Ereg_extra regs (w6bh_extra F) 0).
assert (E11 : ew (Ereg regs (w6bh_extra F)) 11 = Z_to_bv 64 (kk mod 2 ^ 64)).
{ rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. symmetry. apply Z_to_bv_mod64. }
assert (HS : st_ok rsegs (Ereg regs (w6bh_extra F)) w6bh_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_C) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w6bh_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, w6bh_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) (F + 0x210)); [| cbn; lia | cbn; lia | exact Hvf].
        apply rl_den_atom; [exact E32 | lia].
    + unfold region_ok, w6bh_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (Hfsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, w6bh_rR, w6bh_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
remember (Ereg regs (w6bh_extra F)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (w6bh_extra F)) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 W6B_C) with (Z_to_bv 64 W6B_C).
(* 0x80b54 .. 0x80b98 jal: stop at the callee's entry 0x51608 *)
aj_run_to w6b_tbl_ok HS HJ W6B_MEMSET.
{ (* the two write windows: the real frame's cell in the callers' stack window, e62's shadow in the frame (4, pos) *)
  change (ss_mem w6bh_ss0) with [w6bh_rR; w6bh_rS]. unfold w6bh_rR, w6bh_rS.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists 4, pos. split; [exact Hown|]. right.
  unfold in_zr; cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4 / 8) with 128. lia. }
(* after the run: registers, the stored bytes, the bytes kept *)
rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2. rreg HS (1%bv : bv 5) Gra.
lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?ms) =>
  pose proof (regs_kept_of_st_ok rsegs E ss ms regs (w6bh_extra F) (w_H W) [1; 10; 11; 12]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK;
  let rR := eval vm_compute in (nth_error (ss_mem ss) 0) in
  let rS := eval vm_compute in (nth_error (ss_mem ss) 1) in
  lazymatch rR with Some ?r1 => lazymatch rS with Some ?r2 =>
    pose proof (rl_region_nth E ss ms 0 r1 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
    pose proof (rl_region_nth E ss ms 1 r2 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRS
  end end;
  rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl) at 1;
  replace (ss_pc ss) with W6B_MEMSET by (vm_compute; reflexivity)
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
(* [R+0x150] = k and the 13 zero shadow bytes, from the run's last regions *)
assert (VD : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x150) 8 (kk mod 2 ^ 64)).
{ pose proof (rl_chunks E _ 9%nat _ _ _ _ _ _ HRR U9 (YP09.mkChunk 0x150 (CVal 8 (SOff 11 0))) ltac:(cbn; tauto)) as Hc.
  exact (val_of_chunk_ok rsegs E _ R 0x150 8 (SOff 11 0) (kk mod 2 ^ 64) Hc
    (rl_den_atom E 11 _ E11 (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia))) (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia)) ltac:(cbn; lia)). }
assert (Z13 : forall i, 0 <= i < 13 -> aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 66 + i) = Some 0).
{ intros i Hi. rewrite <- Z.add_assoc. apply (rl_chunk0 E).
  apply (rl_chunks E _ 19%nat _ _ _ _ _ _ HRS U19).
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
    i = 11 \/ i = 12) by lia.
  repeat (destruct Hc as [Hc | Hc]; [subst i; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  subst i; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x150 <= a < R + 0x158) -> ~ (shadow_addr F + 66 <= a < shadow_addr F + 79) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Ha1 Ha2. apply (aview_eq_of rsegs). apply HFr. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hin & Hr). change (ss_mem w6bh_ss0) with [w6bh_rR; w6bh_rS] in Hin. unfold w6bh_rR, w6bh_rS in Hin.
  cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite U9 in Hr | rewrite U19 in Hr]; lia. }
clear HRR HRS.
(* the frame's shadow is present at the run's last memory (the journal's AR) *)
pose proof HJ as (HAR2 & _).
destruct (al_frames _ _ LAWS lyc Sc W _ _ 4 pos HAR2 Hin4) as (_ & _ & _ & Hfsh2).
rewrite <- HF in Hfsh2. change (fs_frame_bytes 4 / 8) with 128 in Hfsh2.
(* checked_memset(F + 0x210, 0, 104) at 0x51608 *)
eapply SRr_bind.
{ apply (rl_intrin_at B LAWS OSet W6B_MEMSET AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0x210) 0 104 (R - sp0) (w64 W6B_RET) HJ).
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
    + right; right; right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr; cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + rewrite Hes. lia.
  - exact Hamr.
  - apply zero_shadow_range; [exact Hm8 | reflexivity |].
    intros i Hi. change (104 / 8) with 13 in Hi. rewrite Hshe. exact (Z13 i Hi).
  - intros _ s Hs. destruct (w6bh_hull F Hal32 s Hs) as [Hs1 Hs2].
    replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
    apply (aview_some_of_apresent rsegs). exact (proj1 (Hfsh2 (s - shadow_addr F) ltac:(lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & H10 & HSET & KM).
apply SRr_ret.
unfold rl_wpost. exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (HP2 (bv_unsigned r) (rl_callee r Hr0 Hn)).
  rewrite Z_to_bv_bv_unsigned. apply RK; [exact Hr0|]. intros X. apply Hn. cbv [rl_caller_saved In] in X |- *. tauto. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [apply same_io_wvb | apply same_io_materialized; exact Hsame]|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a Ha Hn. unfold w6b_head_wr in Hn.
  rewrite (KM a Ha ltac:(intros X; apply Hn; right; right; right; lia) ltac:(intros X; apply Hn; left; lia)).
  apply KR; [exact Ha | intros X; apply Hn; right; left; exact X | intros X; apply Hn; right; right; left; exact X]. }
split; [exact H10|].
split.
{ apply (rl_val_kept (w_H W) (ms_mem ms) mem2 (R + 0x150) 8 (kk mod 2 ^ 64)); [|exact VD].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply KM; [lia | lia | rewrite Hes; lia]. }
split.
{ intros i Hi. rewrite KM; [exact (Z13 i Hi) | lia | lia | rewrite Hes; lia]. }
intros i Hi. rewrite (HSET i Hi). reflexivity.
Qed.
End d.
End b.
