(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_G.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
  evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14d44) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14c94) fc None m (seg_rom usegs)).
Proof.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold rctx_head_cells, rsecw in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (320304 + 912) with 321216 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
  let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14d70) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
                                   (Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14d44) fc None m (seg_rom usegs)).
Proof.
  intros until st. intros MR SH n.
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1. Local Ltac2 Set LiaHints.tbl := fun () => "0060>12589638492.3916075715145.3841416074189.3844418219648.3845337639803.388708555059.38 00000400800900=00A00ES2NRS2SHSS2SHS2SHS2SH".
st1.
  rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
  assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
  { rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
    change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv usegs m ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14d70) fc None m (seg_rom usegs)).
Proof.
  intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *. atop_facts.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>12367362435.6221918414723.6436423605256.5636993589379.643945979267.63 41631605457.5641809558659.6343060403331.6549345641752.5551481786499.618832910886.57 00000100200800900:00C00D00E00F00G00PSSS4LOLESSS2LO4LOLESSSSS4LOLE2Hx".
st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; atop_facts; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
  rmrep st m -> mem_inv usegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
  (s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= ATOP -> 1 <= n < 2^62 ->
  0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
                      (Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e34) fc None m' (seg_rom usegs)
        /\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
        /\ stk usegs m' lo (bv_unsigned sp + -64)
        /\ rmrep (mm_ok_st st rid n) m')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14d70) fc None m (seg_rom usegs)).
Proof.
  intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  assert (AL : Z.land (x + 4096) 4095 = 0).
  { change 4095 with (Z.ones 12). Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>11534345588.8011534345588.8111534345588.8411597480591.6813429885656.7017199868364.6618565334488.7019275818812.7019723209304.7020854405405.7021749137752.7022265173650.8022265173650.8122265173650.8423515551704.7025071629079.8025071629079.8125071629079.8427328322569.6837310060433.7238768291473.724135397976.70 5080255960.70 51633178584.705746812688.68 58584560107.8058584560107.8158584560107.8459205324044.6863412496541.7064879841368.707032214372.3  7040976984.70 00000100200300=00>00?00@00M00N00O00P00Q00R00S00T00U00V00W00X00a00e00f00g00h01501D01S01b01f01g01h01m01nSSSS2XC5ATOPRSSSS2X02XC5ATOPRSSSSSSSSSSSS4LOLE2HyS2HySSSS2X02XC5ATOPRS2LO4LOLE5ATOPRS2LO4LOLE5ATOPRS2LO4LOLE5ATOPRS2NRSSS3XALS".
rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
  change (x mod 4096 = 0) with (pgal x) in XAL.
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *. atop_facts.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  replace ((n + -1) * 1) with (n - 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
  { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
      rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
      lazymatch goal with H : rw_cells usegs ?mX 320304 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    - intros y Hy. apply ram_fp_stack. lia.
    - intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
