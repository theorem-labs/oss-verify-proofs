(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v, with its module paths changed; 221 of its 316 lines of code are new or changed and 404 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 876d0cb3d0d; for reac-pw/fuzz_headamp image A: module paths and the rl_ prefix renamed to hd_, every pc moved by +0xd20 (the memset at 0x521a8), the real-frame cells [R+0xd8] / [R+0xf0] moved to [R+0xf8] / [R+0x110] (the plan's slot map), the frame for locals of class 4 (1024 bytes, 128 shadow bytes). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW6aHead.v, with its addresses and numbers changed; 94 of its 222 lines of code are new or changed and 188 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (role's image-A
   block lemma w6_head) for reac-pw/fuzz_headamp's image B: every pc, register and real-frame cell measured on image
   B's twin; e62 at F+0x210 is held in s4 (no extra env slot); the frame is class 4 (1024 bytes, 128 shadow bytes);
   the shadow post is the frame pattern hm_setn pat 66 13 0 (lib/A/HPgMem.v hm_fsh_set); the context, the post and
   the memset step are lib/AU/HPgCaseB.v's cb_ctx / lib/AU/HPgSteps.v's hdu_blk_postE / HPgCaseB.v's cb_memset_at
   in place of the donor's own; AR_laws is YG0q.AR_laws_ok, not a hypothesis. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the block lemma w6b_head of lib/AU/HPgW6aBase.v, the pod loop's head C 0x81888 of LLVMFuzzerTestOneInput
   (0x80c40) through the memset of e62 (pod.h:279):
     0x81888  sd a1,0x158(s1)                  [R+0x158] := kk
     0x8188c .. 0x818bc  13 x sb zero,o(s3)   shadow_addr F + 66 .. 78 := 0 (e62 in scope, pod.h:426)
     0x818c0  addi a2,zero,0x68; 0x818c4 mv a0,s4 (= F + 0x210); 0x818c8 mv a1,zero
     0x818cc  jal 0x52228                      __asan_memset(F + 0x210, 0, 104), back at 0x818d0
   HOW. One engine run (lib/Reusable/YCbq.v aj_run_to over w6b_tbl) from 0x81888 to the callee's entry 0x52228,
   over two regions: the real frame's cell [R+0x158, R+0x160) based at the s1 atom (write window [0x158, 0x160): the
   callers' stack window of the journal), and the 13 shadow bytes [66, 79) of the frame (4, pos) based at the s3
   atom (write window: the frame's shadow row). No instrumented check is in the block. The call is the Section
   hypothesis AMEMSET (the kernel's contract of __asan_memset, lib/Reusable/YG0d.v aintrin_realizes OSet), applied
   through cb_memset_at; its destination e62 lies in the owned frame, its shadow is the 13 zero bytes just stored,
   and the callee's stack [R - ESTACK, R) lies in the journal's window. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgCaseB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry state of the run: no chunk is known at entry ---- *)
Definition w6bh_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x158 0x160 0x158 0x160 [].
Definition w6bh_rS : YP09.region := YP09.mkRegion (Some 19%nat) 66 79 66 79 [].
Definition w6bh_ss0 : sstate := mkSS W6B_C sr_atoms [w6bh_rR; w6bh_rS] None (mkFacts [] [] []).

(* ---- the shadow hull of e62's 104 bytes lies inside the frame's shadow row (F mod 32 = 0) ---- *)
Lemma w6bh_hull : forall F, F mod 32 = 0 -> forall s,
shadow_addr (F + 0x210) / 8 * 8 <= s < shadow_addr (F + 0x210 + 104 - 1) / 8 * 8 + 8 ->
shadow_addr F + 56 <= s < shadow_addr F + 88.
Proof.
intros F H s Hs. destruct (cb_div F H) as [E1 E2]. rewrite E2. remember (F / 32) as q eqn:Hq. clear Hq.
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
(* __asan_memset at image B's entry 0x52228: the kernel's contract of the intrinsic *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6B_MEMSET.

Theorem w6b_head : w6b_head_stmt B MT.
Proof using MTL AMEMSET.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
unfold w6b_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos kk pat
  (HJ & HR32 & HRs & HRlo & Hown & HF & Hrom) H2 H9 H19 H3 H4 H11 H20 Hfsh0 Hlen.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in HRlo.
assert (HR16 : R mod 16 = 0).
{ rewrite (Z.div_mod R 32) at 1 by lia. rewrite HR32, Z.add_0_r.
  replace (32 * (R / 32)) with ((2 * (R / 32)) * 16) by ring. apply Z_mod_mult. }
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hal32 & Happ & _ & Hfsh).
rewrite <- HF in Hal32, Happ, Hfsh.
change (fs_frame_bytes 4) with 1024 in Happ. change (fs_frame_bytes 4 / 8) with 128 in Hfsh.
destruct (cb_bounds F Hal32 Happ) as (HF0 & HFc & Hsa0 & Hsac & Hsep & Hamr).
pose proof (cb_c_mod8 F 0 Hal32 eq_refl) as HF8. rewrite Z.add_0_r in HF8.
clear HAR.
(* the entry state *)
assert (U9 : bv_unsigned (ew (Ereg regs []) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 (kk mod 2 ^ 64)).
{ rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. symmetry. apply Z_to_bv_mod64. }
assert (E20 : ew (Ereg regs []) 20 = w64 (F + 0x210)).
{ rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20. reflexivity. }
assert (HS : st_ok rsegs (Ereg regs []) w6bh_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_C) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w6bh_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, w6bh_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
    + unfold region_ok, w6bh_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (Hfsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, w6bh_rR, w6bh_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 W6B_C) with (Z_to_bv 64 W6B_C).
(* 0x81888 .. 0x818cc jal: stop at the callee's entry 0x52228 *)
aj_run_to w6b_tbl_ok HS HJ W6B_MEMSET.
{ (* the two write windows: the real frame's cell in the callers' stack window, e62's shadow in the frame (4, pos) *)
  change (ss_mem w6bh_ss0) with [w6bh_rR; w6bh_rS]. unfold w6bh_rR, w6bh_rS.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat 4 pos);
  [ reflexivity | rewrite U19, HF; reflexivity | exact Hown | cbn [YP09.r_wlo]; lia
  | cbn [YP09.r_whi]; change (fs_frame_bytes 4 / 8) with 128; lia | apply awr_ok_nil ]. }
(* after the run: registers, the stored bytes, the bytes kept *)
rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2. rreg HS (1%bv : bv 5) Gra.
lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?ms) =>
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs E ss ms regs [] (w_H W) [1; 10; 11; 12]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK;
  let rR := eval vm_compute in (nth_error (ss_mem ss) 0) in
  let rS := eval vm_compute in (nth_error (ss_mem ss) 1) in
  lazymatch rR with Some ?r1 => lazymatch rS with Some ?r2 =>
    pose proof (st_ok_region_at E ss (restrict (w_H W) ms) 0 r1 HS ltac:(vm_compute; reflexivity)) as HRR;
    pose proof (st_ok_region_at E ss (restrict (w_H W) ms) 1 r2 HS ltac:(vm_compute; reflexivity)) as HRS
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
(* [R+0x158] = kk and the 13 zero shadow bytes, from the run's last regions *)
assert (VD : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x158) 8 (kk mod 2 ^ 64)).
{ pose proof (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia)) as Hkb.
  pose proof (cb_chunks E _ 9%nat _ _ _ _ _ _ HRR U9 (YP09.mkChunk 0x158 (CVal 8 (SOff 11 0))) ltac:(cbn; tauto)) as Hc.
  exact (val_of_chunk_ok rsegs E _ R 0x158 8 (SOff 11 0) (kk mod 2 ^ 64) Hc
    (eq_trans (denot_lit_U E _) (f_equal (Z_to_bv 64) (U_atom E 11 _ E11 Hkb))) Hkb ltac:(cbn; lia)). }
assert (Z13 : forall i, 66 <= i < 79 -> aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + i) = Some 0).
{ destruct HRS as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite U19 in Hch.
  intros i Hi. unfold aview.
  assert (Hc : i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ i = 74 \/ i = 75 \/
    i = 76 \/ i = 77 \/ i = 78) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]). }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x158 <= a < R + 0x160) -> ~ (shadow_addr F + 66 <= a < shadow_addr F + 79) ->
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
(* __asan_memset(F + 0x210, 0, 104) at 0x52228 *)
eapply SRr_bind.
{ apply (cb_memset_at B W6B_MEMSET AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0x210) 0 104 (R - sp0) (w64 W6B_RET) HJ).
  - rewrite Ga0, E20. reflexivity.
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
  - apply zero_shadow_range; [exact (cb_c_mod8 F 0x210 Hal32 eq_refl) | reflexivity |].
    intros i Hi. change (104 / 8) with 13 in Hi. rewrite (cb_sh_off F 0x210 HF8 eq_refl).
    change (0x210 / 8) with 66. rewrite <- Z.add_assoc. apply Z13. lia.
  - intros _ s Hs. destruct (w6bh_hull F Hal32 s Hs) as [Hs1 Hs2].
    replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
    apply (aview_some_of_apresent rsegs). exact (proj1 (Hfsh2 (s - shadow_addr F) ltac:(lia))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & H10 & HSET & KM & _).
apply SRr_ret.
unfold hdu_blk_postE. exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (HP2 (bv_unsigned r) (cb_callee r Hr0 Hn)).
  rewrite Z_to_bv_bv_unsigned. apply RK; [exact Hr0|]. intros X. apply Hn. cbv [cb_caller_saved In] in X |- *. tauto. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [| exact Hio2];
  let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a Ha Hn. unfold w6b_head_wr in Hn.
  rewrite (KM a Ha ltac:(intros X; apply Hn; right; right; right; lia) ltac:(intros X; apply Hn; left; lia)).
  apply KR; [exact Ha | intros X; apply Hn; right; left; exact X | intros X; apply Hn; right; right; left; exact X]. }
split; [exact H10|].
split.
{ apply (val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem2 (R + 0x158) 8 (kk mod 2 ^ 64)); [|exact VD].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply KM; [lia | lia | rewrite Hes; lia]. }
split.
{ apply (hm_fsh_set rsegs (w_H W) memc (w_H W) mem2 F pat 66 13 0 Hfsh0).
  - intros i Hi. change (Z.of_nat 66) with 66 in Hi. change (Z.of_nat (66 + 13)) with 79 in Hi.
    rewrite KM; [exact (Z13 i Hi) | lia | lia | rewrite Hes; lia].
  - intros i Hi Hn. rewrite Hlen in Hi. change (Z.of_nat 116) with 116 in Hi.
    change (Z.of_nat 66) with 66 in Hn. change (Z.of_nat (66 + 13)) with 79 in Hn.
    rewrite KM; [| lia | lia | rewrite Hes; lia].
    apply KR; [lia | lia | lia]. }
intros i Hi. rewrite (HSET i Hi). reflexivity.
Qed.
End d.
End b.

Print Assumptions w6b_head.
Check w6b_head.
