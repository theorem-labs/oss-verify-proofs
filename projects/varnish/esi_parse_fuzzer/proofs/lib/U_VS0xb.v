(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 ImgU U_VSe1y U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition VSB_finish_entry : Z := 0x19be4.
Definition VSB_data_entry : Z := 0x19c8c.
Definition VSB_len_entry : Z := 0x19cd0.
(* [comment removed for export] *)
Definition ERRNOU : Z := 0x42454.
Lemma ERRNOU_eq : al_errno LayoutPU = ERRNOU. Proof. vm_compute. reflexivity. Qed.

Definition vsb_result (e r : Z) : Z := if e =? 0 then r else -1.

(* [comment removed for export] *)

Definition VSB_finish_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (v : vsb_rec) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (vsb_result (vb_error v) 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v); (ERRNOU, ERRNOU + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' S (vsb_cells (vsb_set_flags v VSB_FLAGS_FIN))
    /\ u8arr rsegs m' (vb_buf v) (upd bs (Z.to_nat (vb_len v)) (Z_to_bv 8 0))
    /\ rw_cells rsegs m' ERRNOU [C4 (w64 (vb_error v))]
    /\ stk rsegs m' lo (bv_unsigned sp).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma VSB_finish_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (v : vsb_rec) (bs : list byte) (e : word) (lo : Z),
    a0 = Z_to_bv 64 S -> tp = al_tp LayoutPU ->
    rw_cells rsegs m S (vsb_cells v) -> vsb_inv v false ->
    u8arr rsegs m (vb_buf v) bs -> Z.of_nat (length bs) = vb_size v ->
    rw_cells rsegs m ERRNOU [C4 e] ->
    4096 <= S -> S mod 8 = 0 -> S + 40 <= alloc_ceiling -> vb_buf v + vb_size v <= alloc_ceiling ->
    off_image LayoutPU S 40 -> off_image LayoutPU (vb_buf v) (vb_size v) ->
    (S + 40 <= vb_buf v \/ vb_buf v + vb_size v <= S) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> alloc_ceiling <= lo ->
    bv_unsigned sp + 64 <= 2^47 ->
    mem_inv rsegs m ->
    evt rsegs (VSB_finish_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S v bs lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSB_finish_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros A0 TP VSBC VINV U8 LBS ERR Slo S8 Shi Bhi Simg Bimg DSB ST LO CEIL SPHI MI.
  rewrite A0, TP. change (al_tp LayoutPU) with (Z_to_bv 64 0x424f8). unfold VSB_finish_entry.
  pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
  unfold off_image in Simg, Bimg. cbn [al_image_lo al_image_hi LayoutPU] in Simg, Bimg.
  pose proof alloc_ceiling_val as ACV.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v); (ERRNOU, ERRNOU + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold ERRNOU in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold vsb_cells in VSBC.
  carve_frame 16%nat ST.
  do 4 zstep.
  (* [comment removed for export] *)
  zstep. call assert_integrity_spec.
  1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
  zstep. zstep. zstep.
  call (assert_state_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S v false).
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
  (* [comment removed for export] *)
  zstep. if_cases K7; zify_cond K7. { exfalso. klia K7. } clear K7.
  zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. decide_ltb KT. congruence. } clear KT.
  zstep. zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT. { unsign KT. decide_ltb KT. dead KT. } clear KT.
  zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. } clear KT.
  (* [comment removed for export] *)
  pose proof (u8arr_store_ok rsegs _ _ _ (vb_len v) _ U8 ltac:(lia) eq_refl) as SOK.
  zstep. rewrite le1_single. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  pose proof (u8arr_write rsegs _ _ _ (vb_len v) (Z_to_bv 8 0) U8 ltac:(lia)) as U8'. clear U8. store_done.
  (* [comment removed for export] *)
  zstep. zstep. zstep. rewrite Vfl.
  zstep.
  match type of VSBC with context [Z.lor ?x ?y] => let r := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with r in VSBC end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases KT; zify_cond KT. { dead KT. } clear KT.
  zstep. zstep. if_cases KT; zify_cond KT. { dead KT. } clear KT.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  do 2 zstep. zstep. zstep.
  try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold VSB_finish_post, vsb_result.
  pose proof Verr as E; rewrite E in *;   (* [comment removed for export] *)
    match goal with |- context [Z.b2z ?x + -1] => let r := eval vm_compute in (Z.b2z x + -1) in change (Z.b2z x + -1) with r end;
    match type of ERR with context [sx32 ?x] => let r := eval vm_compute in (sx32 x) in change (sx32 x) with r in ERR end;
    unfold ENOMEM; cbn [Z.eqb Pos.eqb];
    do 15 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]);
    (split; [unfold vsb_cells; cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_flags]; rewrite E; exact VSBC|]);
    (split; [exact U8'|]); (split; [exact ERR| exact ST]).
Qed.

(* [comment removed for export] *)

Definition VSB_pure_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma VSB_data_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (v : vsb_rec) (lo : Z),
    a0 = Z_to_bv 64 S ->
    rw_cells rsegs m S (vsb_cells v) -> vsb_inv v true ->
    4096 <= S -> S mod 8 = 0 -> S + 40 <= alloc_ceiling ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> alloc_ceiling <= lo ->
    bv_unsigned sp + 64 <= 2^47 ->
    mem_inv rsegs m ->
    evt rsegs (VSB_pure_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (vb_buf v) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSB_data_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros A0 VSBC VINV Slo S8 Shi ST LO CEIL SPHI MI.
  rewrite A0. unfold VSB_data_entry.
  pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
  pose proof alloc_ceiling_val as ACV.
  unfold vsb_cells in VSBC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST.
  do 4 zstep.
  (* [comment removed for export] *)
  zstep. call assert_integrity_spec.
  1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
  zstep. zstep. zstep.
  call (assert_state_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S v true).
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
  (* [comment removed for export] *)
  zstep. if_cases K7; zify_cond K7. { exfalso. klia K7. } clear K7.
  zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
  (* [comment removed for export] *)
  zstep. do 2 zstep. zstep. zstep.
  try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold VSB_pure_post.
  do 15 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption| exact ST]).
Qed.

(* [comment removed for export] *)

Lemma VSB_len_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (v : vsb_rec) (fin : bool) (lo : Z),
    a0 = Z_to_bv 64 S ->
    rw_cells rsegs m S (vsb_cells v) -> vsb_inv v fin ->
    4096 <= S -> S mod 8 = 0 -> S + 40 <= alloc_ceiling ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> alloc_ceiling <= lo ->
    bv_unsigned sp + 64 <= 2^47 ->
    mem_inv rsegs m ->
    evt rsegs (VSB_pure_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (vsb_result (vb_error v) (vb_len v)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSB_len_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros A0 VSBC VINV Slo S8 Shi ST LO CEIL SPHI MI.
  rewrite A0. unfold VSB_len_entry.
  pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
  pose proof alloc_ceiling_val as ACV.
  unfold vsb_cells in VSBC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST.
  do 4 zstep.
  (* [comment removed for export] *)
  zstep. call assert_integrity_spec.
  1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
  (* [comment removed for export] *)
  zstep. if_cases K7; zify_cond K7. { exfalso. klia K7. } clear K7.
  zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
  (* [comment removed for export] *)
  zstep. unfold vsb_result.
  pose proof Verr as E; rewrite E in *.   (* [comment removed for export] *)
  - zstep. if_cases KE; zify_cond KE. 2:{ exfalso. revert KE. vm_compute. congruence. } clear KE.
    (* [comment removed for export] *)
    zstep. do 2 zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold VSB_pure_post. cbn [Z.eqb].
    do 15 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption| exact ST]).
Qed.

End CEIL.
