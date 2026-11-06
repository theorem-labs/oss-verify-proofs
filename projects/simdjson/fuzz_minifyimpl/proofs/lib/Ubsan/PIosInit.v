(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg PIosImg PIosCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition ios_crt_hulls : list (Z * Z) := [(0xee488, 0xee490); (0xee490, 0xee5e0); (0x10e568, 0x10e598); (0x10e7c8, 0x10e7d0); (0x10e7d8, 0x10e858)].

Definition ios_init_post (usp lo : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0xbd778) (Z_to_bv 64 usp) gp (Z_to_bv 64 0xee558) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbd778) fc None m' (seg_rom usegs)
    /\ munch [(usp - 4096, usp); (0xec630, 0xed4bb); (0xedbf4, 0xedc48); (0xee528, 0xee530); (0x10e5a0, 0x10e7c0)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo usp
    /\ rw_cells usegs m' 0xec630 [CB 3723 ios_exp0]                      (* [comment removed for export] *)
    /\ rw_cells usegs m' 0xedbf4 [CB 84 ios_exp1]                        (* [comment removed for export] *)
    /\ rw_cells usegs m' 0xee528 [C8 (Z_to_bv 64 0x10e820)]               (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x10e5a0 [CB 544 ios_exp3].                      (* [comment removed for export] *)

Theorem ios_init_spec : forall (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c : word) (usp : Z) (m : mem),
  forall (lo : Z) (F : bvmap 5 word) (fc : bv 32), 0x7fff00000000 <= usp <= 0x800000000000 -> usp mod 16 = 0 ->
  stk usegs m lo usp -> lo <= usp - 4096 -> mem_inv usegs m ->
  rw_cells usegs m 0x10e7c8 [C8 c] ->                                   (* [comment removed for export] *)
  rw_cells usegs m 0xee528 [C8 (Z_to_bv 64 0x10e820)] ->                (* [comment removed for export] *)
  rw_cells usegs m 0x10e7eb [C1 (Z_to_bv 8 0)] ->                       (* [comment removed for export] *)
  (forall a : word, 0xd4000 <= bv_unsigned a < 0x110000 -> outside ios_crt_hulls (bv_unsigned a) -> m a = None) ->
  evt usegs (ios_init_post usp lo gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR (Z_to_bv 64 0xbd778) (Z_to_bv 64 usp) gp (Z_to_bv 64 0xee558) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810c0) fc None m (seg_rom usegs)).
Proof.
  intros gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c usp m lo F fc SPR SPA STK LO MI CAN LOC NL IMG.
  set (E := Env (vals_ev [Z_to_bv 64 0; Z_to_bv 64 0xbd778; Z_to_bv 64 usp; gp; Z_to_bv 64 0xee558; t0; t1; t2; s0; s1; a0; a1; a2; a3; a4; a5; a6; a7;
                          s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6; c]) (fun _ => [])).
  assert (USP : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (NONE : forall l h, 0x10000 <= l -> h <= 0x110000 -> (forall x, l <= x < h -> outside ios_crt_hulls x) ->
                 forall a : word, l <= bv_unsigned a < h -> m a = None).
  { intros l h H1 H2 HO a Ha. destruct (Z.lt_ge_cases (bv_unsigned a) 0xd4000) as [Hro|Hrw].
    - (* [comment removed for export] *)
      destruct (m a) as [b|] eqn:Em; [|reflexivity].
      exfalso. pose proof (MI a b Em) as RO. rewrite u_ro_addr in RO.
      destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.ltb_spec0 (bv_unsigned a) 0xd4000); cbn in RO; try discriminate; lia.
    - apply IMG; [lia | apply HO; exact Ha]. }
  assert (KN : know_ok usegs E m ios_kn0).
  { unfold ios_kn0. repeat apply Forall_cons; [ | | | | | | | | | | | | apply Forall_nil].
    - apply kn_range. cbn [edenot ev E vals_ev nth]. rewrite USP. lia.
    - apply kn_align; [lia|]. cbn [edenot ev E vals_ev nth]. rewrite USP. exact SPA.
    - apply (kn_wr usegs E m (EVar 2) (-4096) 4096 (usp - 4096)); try lia.
      + cbn [edenot ev E vals_ev nth]. rewrite USP. lia.
      + intros x Hx. apply (stk_wview usegs m lo usp x STK). lia.
    - destruct CAN as [[_ CB] _]. apply (kn_word usegs E m 0x10e7c8 8 (EVar 32) _ CB); [reflexivity | lia | reflexivity].
    - destruct LOC as [[_ CB] _]. apply (kn_word usegs E m 0xee528 8 (ELit 0x10e820) _ CB); [reflexivity | lia | reflexivity].
    - destruct NL as [[_ CB] _]. apply (kn_word usegs E m 0x10e7eb 1 (ELit 0) _ CB); [reflexivity | lia | reflexivity].
    - apply kn_img; [lia | lia |]. apply NONE; [lia | lia |]. intros x Hx. unfold ios_crt_hulls. cbn [outside]. lia.
    - apply kn_img; [lia | lia |]. apply NONE; [lia | lia |]. intros x Hx. unfold ios_crt_hulls. cbn [outside]. lia.
    - apply kn_img; [lia | lia |]. apply NONE; [lia | lia |]. intros x Hx. unfold ios_crt_hulls. cbn [outside]. lia.
    - apply kn_img; [lia | lia |]. apply NONE; [lia | lia |]. intros x Hx. unfold ios_crt_hulls. cbn [outside]. lia.
    - apply kn_img; [lia | lia |]. apply NONE; [lia | lia |]. intros x Hx. unfold ios_crt_hulls. cbn [outside]. lia.
    - apply (kn_wr usegs E m (ELit 0) 868352 245760 868352); try lia.
      + rewrite edenot_lit. reflexivity.
      + intros x Hx. apply p_rw_window. lia. }
  destruct (scheck_sound usegs ios_IT 40000%nat [ios_RET] ios_ss0 ios_W ios_RET ios_srF ios_exports ios_wexports ios_IT_ok ios_cert
              E m (seg_rom usegs) _ F fc (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              (regs_ok_mkR E ios_sr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl) KN MI)
    as (R' & m' & MST & FULL & RO & MU & WM & MI' & STKP & EXP & _).
  exists (MS R' F (Z_to_bv 64 ios_RET) fc None m' (seg_rom usegs)). split; [exact MST|].
  rewrite (regs_ok_canon E ios_srF R' FULL RO).
  unfold ios_init_post. do 15 eexists. exists m'.
  split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU]. unfold sub_fp, ios_W. cbn [map fpwin_den edenot ev E vals_ev nth outside].
    rewrite USP. change (bv_unsigned (Z_to_bv 64 0)) with 0. intros x Hx. lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact (STKP _ _ STK)|].
  pose proof (Forall_inv EXP) as X0. pose proof (Forall_inv (Forall_inv_tail EXP)) as X1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail EXP))) as X2.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail EXP)))) as X3.
  cbn [fst snd] in X0, X1, X2, X3.
  split; [exact X0|]. split; [exact X1|]. split; [|exact X3].
  apply (rw_cells_recast_u usegs m' _ _ _ X2); [cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
Qed.
