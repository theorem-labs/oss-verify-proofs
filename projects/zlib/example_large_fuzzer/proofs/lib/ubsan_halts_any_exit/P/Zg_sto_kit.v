(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Zg_defl_iface Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_HEAD : Z := 0x18130.
Definition Z_STO_LATCH : Z := 0x1812c.
Definition Z_STO_BREAK : Z := 0x183a8.
Definition Z_STO_BREAK2 : Z := 0x183cc.
Definition Z_STO_LASTT : Z := 0x184ec.
Definition Z_STO_FILL : Z := 0x18524.
Definition Z_STO_FIN2 : Z := 0x18658.
Definition Z_STO_EPI : Z := 0x187d0.

(* 1.4: sp+0 is never written (j0: the carve's 8 junk bytes); ai0 at 8, lz at 16, flush at 24, (flush<>0) at 32,
   min_block at 40, (flush==4) at 48. *)
Definition sto_frame (j0 : list byte) (flush ai0 lz : Z) (r : sregs) : list cell :=
  [CB 8 j0; C8 (wz ai0); C8 (wz lz); C8 (wz flush); C8 (wz (if flush =? 0 then 0 else 1)); C8 (wz 32768);
   C8 (wz (if flush =? 4 then 1 else 0));
   C8 (r_s11 r); C8 (r_s10 r); C8 (r_s9 r); C8 (r_s8 r); C8 (r_s7 r); C8 (r_s6 r); C8 (r_s5 r); C8 (r_s4 r);
   C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

Lemma sto_c32 : forall flush, 0 <= flush <= 5 ->
  Z.b2z (0 <? flush mod 18446744073709551616) = (if flush =? 0 then 0 else 1).
Proof.
  intros flush H.
  assert (C : flush = 0 \/ flush = 1 \/ flush = 2 \/ flush = 3 \/ flush = 4 \/ flush = 5) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; reflexivity.
Qed.

Lemma sto_c48 : forall flush, 0 <= flush <= 5 ->
  Z.b2z ((flush + -4) mod 18446744073709551616 <? 1) = (if flush =? 4 then 1 else 0).
Proof.
  intros flush H.
  assert (C : flush = 0 \/ flush = 1 \/ flush = 2 \/ flush = 3 \/ flush = 4 \/ flush = 5) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; reflexivity.
Qed.


Ltac sr :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty))
         (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5)
                         (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
     None
     (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4)
                   (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty)))
       (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6)
                         (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) _ ?pc _ _ _ _) =>
      idtac "== pc" pc; idtac "s1" x9; idtac "a0" x10; idtac "a1" x11; idtac "a2" x12; idtac "a3" x13; idtac "a4" x14;
      idtac "a5" x15; idtac "a6" x16; idtac "s2" x18; idtac "s3" x19; idtac "s4" x20; idtac "s5" x21; idtac "s6" x22; idtac "s7" x23;
      idtac "s10" x26; idtac "s11" x27
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "== pc (non-mkR regs)" pc
  end.

Definition sto_W := slow_W.

(* 1.4 register roles: s0 = As, s7 = s10 = As + 5928, s8 = 65535, s9 = 65534. s7 is clobbered (strm) between the
   flush_bits call and the copy; stoR7 leaves it free. *)
Definition stoR7 (L : dlay) (r : sregs) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word)
    : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned (r_sp r) + -160)) (r_gp r) (r_tp r) x5 x6 x7 (wz (dl_As L)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      x20 x21 x22 x23 (wz 65535) (wz 65534) (wz (dl_As L + 5928)) x27 x28 x29 x30 x31.

Definition stoR (L : dlay) (r : sregs) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word)
    : bvmap 5 word :=
  stoR7 L r x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (wz (dl_As L + 5928)) x27 x28 x29 x30 x31.

Record sto_ctx (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) : Prop := mkStoCtx {
  tc_lo : lo <= bv_unsigned (r_sp r) - Z_STORED_STACK;
  tc_sp16 : bv_unsigned (r_sp r) mod 16 = 0;
  tc_lay : dlay_ok L;
  tc_bel : dlay_below L lo (bv_unsigned (r_sp r));
  tc_io : dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo;
  tc_din : din me L inp }.

Definition STOINV (L : dlay) (flush ai0 lz : Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ dout m L rest0 (ds_strm X) /\ Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat
  /\ (exists j0, rw_cells psegs m (bv_unsigned (r_sp r) + -160) (sto_frame j0 flush ai0 lz r))
  /\ stk psegs m lo (bv_unsigned (r_sp r) + -160)
  /\ munch (sto_W L rest0 lo r) me m /\ wmono psegs me m /\ mem_inv psegs m.

Definition TK (L : dlay) (flush ai0 lz : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 lz rest0 lo r me X m' ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom psegs)).

Definition TK10 (L : dlay) (flush ai0 lz : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (v : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 lz rest0 lo r me X m' ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 (wz v) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom psegs)).

(* at Z_STO_LASTT: a0 = a1 = strstart, a3 = flush *)
Definition TK11 (L : dlay) (flush ai0 lz : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y12 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 lz rest0 lo r me X m' ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 (wz (ds_strstart X)) (wz (ds_strstart X)) y12 (wz flush) y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom psegs)).

Section KIT.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.

Lemma sto_din : forall m, munch (sto_W L rest0 lo r) me m -> din m L inp.
Proof using CTX.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO DIN]. unfold Z_STORED_STACK in LOsp. unfold din in *.
  eapply bytes_at_transport; [exact DIN| exact MU|]. unfold sto_W, slow_W. cbn [disjoint_from]. rewrite zb8_length.
  below_open BEL. pose proof IO as I0. io_open I0. unfold zlength in *.
  pose proof (io_is _ _ _ _ IO) as J1. pose proof (io_iw _ _ _ _ IO) as J2. pose proof (io_ip _ _ _ _ IO) as J3.
  pose proof (io_ih _ _ _ _ IO) as J4. pose proof (io_ib _ _ _ _ IO) as J5. pose proof (io_io _ _ _ _ IO) as J6.
  unfold apart, zlength in *. repeat split; lia.
Qed.

Lemma sto_epi : forall (lz : Z) (dF : deflate_state) (code : Z),
  TK10 L flush ai0 lz rest0 lo r F fc me (slow_post_gen r F fc L dF code inp rest0 lo me) Z_STO_EPI code dF.
Proof using CTX.
  intros lz dF code. unfold TK10. intros until m'. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EPI, stoR, stoR7.
  pose proof (sto_din m' MU) as DIN. unfold sto_W, slow_W in MU.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 13 zs.
  release_frame FR STK (bv_unsigned (r_sp r)). zs. zs.
  apply evt_done. unfold slow_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.
Definition Z_STO_EPIBU : Z := 0x187c0.

(* 1.4: li a1,8; sw a1,16(s7) (s->bi_used = 8, a junk cell); j epi *)
Lemma sto_epi_bu : forall (lz : Z) (dF : deflate_state) (code : Z),
  TK10 L flush ai0 lz rest0 lo r F fc me (slow_post_gen r F fc L dF code inp rest0 lo me) Z_STO_EPIBU code dF.
Proof using CTX.
  intros lz dF code. pose proof (sto_epi lz dF code) as E. unfold TK10 in E |- *. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EPIBU, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  open_DST ST. open_D GD. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zs. zs. zs. name_mem mB.
  unfold stoR, stoR7 in E. eapply E.
  tr_groups MUf WMf.
  split; [split; [first [exact ZS| eapply dzs_munch; [exact ZS| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|]|].
  { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
  split; [first [exact DOUT| eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|].
  split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End KIT.
