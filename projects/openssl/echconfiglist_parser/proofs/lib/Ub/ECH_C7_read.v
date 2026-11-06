(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rdonly_off0 : forall f, 0 <= f < 2^31 -> Z.land f 512 = 512 ->
  Z.land (Z.shiftr (Z.lxor f 18446744073709551615) 6) 8 = 0.
Proof.
  intros f Hf H9. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec, Z.lxor_spec, Z.bits_0 by lia.
  destruct (Z.eq_dec n 3) as [->|NE].
  - cbn [Z.add]. change 18446744073709551615 with (Z.ones 64). rewrite Z.ones_spec_low by lia.
    assert (B9 : Z.testbit f 9 = true).
    { apply (f_equal (fun z => Z.testbit z 9)) in H9. rewrite Z.land_spec in H9. change (Z.testbit 512 9) with true in H9.
      rewrite Bool.andb_true_r in H9. exact H9. }
    rewrite B9. reflexivity.
  - replace (Z.testbit 8 n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|].
    destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
    apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.

(* [comment removed for export] *)
Ltac membio_tac :=
  unfold MEMBIO, mb_after_bread, mb_after_read, mb_advance, mb_with_hdr, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY, BIO_FLAGS_RETRY_MASK;
  cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
  repeat lazymatch goal with |- _ /\ _ => split end;
  try assumption; try lia;
  try (unfold bio_cells, membio_bio, buf_cells, wz;
       cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
            mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
       first [assumption | rewrite ?Z.add_0_r; assumption]).
(* [comment removed for export] *)
Ltac extm MU WM MUc WMc :=
  lazymatch type of MU with munch ?Wfull ?mpre ?mmid =>
  lazymatch type of MUc with munch ?Wc mmid ?mpost =>
    let T := fresh "MUx" in
    assert (T : munch Wfull mpre mpost)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MUc];
          let xa := fresh "xa" in let Hxa := fresh "Hxa" in
          intros xa Hxa; cbn [outside MEMBIO_foot sub_fp] in Hxa |- *; unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE in Hxa |- *; lia);
    clear MU MUc; rename T into MU;
    let T2 := fresh "WMx" in pose proof (wmono_trans _ _ _ _ WM WMc) as T2; clear WM WMc; rename T2 into WM
  end end.
(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hidden T) in H end.
Ltac unhide H := unfold hidden in H.
(* [comment removed for export] *)
Ltac landx MU WM :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; land_exs PO; destruct_ands PO; subst ms';
  lazymatch type of MU with munch _ _ ?mmid =>
    match goal with MUc : munch _ mmid ?mpost |- _ =>
      match goal with WMc : wmono _ mmid mpost |- _ =>
        rewrite ?unsigned_lit in MUc by lia;
        repeat match goal with H : context [bv_unsigned (Z_to_bv 64 _)] |- _ =>
          lazymatch type of H with munch _ _ _ => fail | hidden _ => fail | _ => rewrite ?unsigned_lit in H by lia end end;
        carry MUc WMc; extm MU WM MUc WMc
      end
    end
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    repeat match goal with H : mem_inv _ ?mx |- _ => lazymatch mx with mc => fail | _ => clear H end end;
    repeat match goal with H : ECH_Kit.stale _ |- _ => clear H end;
    try (lazymatch goal with _ : stk _ mc _ _ |- _ => idtac end;
         match goal with H : stk _ mc _ _ |- _ => rename H into ST end)
  end;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end);
  repeat match goal with H : ?v = Z_to_bv 64 _ |- _ => is_var v; subst v end.


Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition MR_RA1 : Z := 0x208238.   (* [comment removed for export] *)
  Definition MR_RA2 : Z := 0x208270.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mr_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 -> (0 < out /\ out + outl <= 2^64) ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - MEMREAD_STACK -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 MR_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 a) (Z_to_bv 64 15) (Z_to_bv 64 outl) a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 out) (Z_to_bv 64 outl) (Z_to_bv 64 (mb_bm R)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_clear_flags) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells usegs m1 (bv_unsigned sp + -64)
               [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
          /\ MEMBIO LB m1 a R)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_mem_read) fc None m (seg_rom usegs)).
  Proof.
    intros until R. intros A0 A1 A2 OUTL OUT MB BL SEP ST CEIL LO MI. subst a0 a1 a2.
    unfold P_mem_read, P_BIO_clear_flags, MR_RA1, MEMREAD_STACK, FR_mem_read, BIOACC_STACK, FR_BIO_set_data in *.
    destruct MB as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    destruct BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY in *.
    unfold rblock_range in RB1, RB2, RB3, RB4.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold wz in BBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    pose proof RB1 as (_ & AAL & _). pose proof RB2 as (_ & BBAL & _).
    carve_frame 64%nat ST.
    do 9 st1.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.      (* [comment removed for export] *)
    step. step. ubal_by AAL. step. if_lit.                       (* [comment removed for export] *)
    st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0. (* [comment removed for export] *)
    step. step. ubal_by BBAL. step. if_lit.                      (* [comment removed for export] *)
    step.                                                         (* [comment removed for export] *)
    st1. zstep. zstep. zstep. rewrite (sx32_lit (mb_flags R)), (unsigned_lit (mb_flags R)) by lia. rewrite rdonly_off0 by lia. zstep. st1. step. step. step.
    finish. exact FR. membio_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma mr_seg2c :
    forall (sp gp tp t0 t1 t2 s2x a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outl out lo : Z) (R : membio) (fr : list cell),
      0 < outl < 2^31 -> (0 < out /\ out + outl <= 2^64) -> 0 <= mb_pos R <= mb_len R -> 0 <= mb_len R < 2^31 -> 0 < mb_buf R -> mb_buf R + mb_len R <= hceil ->
      0 < mb_rdn R outl -> mb_bm R mod 16 = 0 (* [comment removed for export] *) ->
      rw_cells usegs m (mb_bm R) [C8 (wz (mb_len R - mb_pos R)); C8 (wz (mb_buf R + mb_pos R)); C8 (wz (mb_len R - mb_pos R)); C8 (wz 0)] ->
      mb_bm R + 32 <= lo -> 0 < mb_bm R ->
      rw_cells usegs m (bv_unsigned sp + -64) fr -> cells_size fr = 64%nat ->
      stk usegs m lo (bv_unsigned sp + -64) -> hceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 MR_RA2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 out) (Z_to_bv 64 (mb_buf R + mb_pos R)) (Z_to_bv 64 (mb_rdn R outl)) a3 a4 a5 a6 a7
                       (Z_to_bv 64 (mb_rdn R outl)) (Z_to_bv 64 out) (Z_to_bv 64 outl) (Z_to_bv 64 (mb_bm R)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x2c04f0) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 MR_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 out) (Z_to_bv 64 outl) (Z_to_bv 64 (mb_bm R)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MR_RA1) fc None m (seg_rom usegs)).
  Proof.
    intros until fr. intros OUTL OUT POSR LENR BUFP BUFH NPOS BMAL BMC BL3 BMP FR FRS ST CEIL LO MI.
    unfold MR_RA1, MR_RA2, mb_rdn, mb_avail in *. unfold wz in BMC. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.         (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.         (* [comment removed for export] *)
    step. ubal_by BMAL. step. if_lit.                              (* [comment removed for export] *)
    st1. step. if_cases K1; zify_cond K1.                          (* [comment removed for export] *)
    - (* [comment removed for export] *)
      replace (Z.min outl (mb_len R - mb_pos R)) with (mb_len R - mb_pos R) in * by lia.
      step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
      step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
      st1. step. step. step. apply evt_done. reflexivity.
    - (* [comment removed for export] *)
      replace (Z.min outl (mb_len R - mb_pos R)) with outl in * by lia.
      step. step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
      step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
      st1. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mr_seg2z :
    forall (sp gp tp t0 t1 t2 s2x a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (s0c s1c s2c s3c s4c s5c rac : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outl out lo : Z) (R : membio) (j : list byte) (fl : Z),
      0 < outl < 2^31 -> (0 < out /\ out + outl <= 2^64) -> 0 <= mb_pos R <= mb_len R -> 0 <= mb_len R < 2^31 ->
      mb_rdn R outl = 0 -> 0 <= fl < 2^31 -> mb_numf R = 0 -> mb_bm R mod 16 = 0 (* [comment removed for export] *) ->
      rw_cells usegs m a (bio_cells (membio_bio (mb_with_hdr R fl (mb_numf R) (mb_next R) (mb_prev R)))) -> a + 128 <= lo -> 0 < a ->
      0 <= mb_next R < 2^64 -> 0 <= mb_prev R < 2^64 -> 0 <= mb_bb R < 2^64 -> 0 <= mb_nread R < 2^63 ->
      rw_cells usegs m (mb_bm R) [C8 (wz (mb_len R - mb_pos R)); C8 (wz (mb_buf R + mb_pos R)); C8 (wz (mb_len R - mb_pos R)); C8 (wz 0)] ->
      mb_bm R + 32 <= lo -> 0 < mb_bm R ->
      rw_cells usegs m (bv_unsigned sp + -64) [CB 8 j; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
      stk usegs m lo (bv_unsigned sp + -64) -> hceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR rac sp gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 0)
                       a1 a2 a3 a4 a5 a6 a7
                       s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rac) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 MR_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 out) (Z_to_bv 64 outl) (Z_to_bv 64 (mb_bm R)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MR_RA1) fc None m (seg_rom usegs)).
  Proof.
    intros until fl. intros OUTL OUT POSR LENR N0 FLR NUM0 BMAL BC BL1 AP NXT PRV BBR NRD BMC BL3 BMP FR ST CEIL LO MI.
    unfold MR_RA1, mb_rdn, mb_avail in *. unfold wz in BMC. hcb.
    unfold bio_cells, membio_bio, mb_with_hdr, wz in BC.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
         mb_flags mb_numf mb_next mb_prev mb_bb mb_nread] in BC. rewrite NUM0 in BC.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ BC) as BB. cbn [cells_size csize Nat.add] in BB. unfold A_mem_buf_method in *.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.           (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.           (* [comment removed for export] *)
    step. ubal_by BMAL. step. if_lit.                                (* [comment removed for export] *)
    st1. step. if_cases K1; zify_cond K1; [| kill K1]. clear K1.     (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.     (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3; [| kill K3]. clear K3.          (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.           (* [comment removed for export] *)
    step. try if_lit.                                                (* [comment removed for export] *)
    st1. step. if_cases K4; zify_cond K4; [kill K4|]. clear K4.      (* [comment removed for export] *)
    st1. step. if_cases K5; zify_cond K5; [| kill K5]. clear K5.     (* [comment removed for export] *)
    zstep. do 7 st1. step. step.
    release_frame FR ST (bv_unsigned sp). apply evt_done. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma mr_seg3 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (s0c s1c s2c s3c s4c s5c rac : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outl out lo n : Z) (R : membio) (j : list byte),
      0 < outl < 2^31 -> (0 < out /\ out + outl <= 2^64) -> 0 <= mb_pos R <= mb_len R -> 0 <= mb_len R < 2^31 -> 0 < mb_buf R -> mb_buf R + mb_len R <= hceil ->
      0 < n <= mb_len R - mb_pos R -> n <= outl ->
      rw_cells usegs m (mb_bm R) [C8 (wz (mb_len R - mb_pos R)); C8 (wz (mb_buf R + mb_pos R)); C8 (wz (mb_len R - mb_pos R)); C8 (wz 0)] ->
      mb_bm R + 32 <= lo -> 0 < mb_bm R ->
      rw_cells usegs m (bv_unsigned sp + -64) [CB 8 j; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
      stk usegs m lo (bv_unsigned sp + -64) -> hceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a1' a2' a3' : word) m',      (* [comment removed for export] *)
          ms' = MS (mkR rac sp gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 n)
                       a1' a2' a3' a4 a5 a6 a7
                       s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rac) fc None m' (seg_rom usegs)
          /\ munch [(mb_bm R, mb_bm R + 32)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
          /\ rw_cells usegs m' (mb_bm R) [C8 (wz (mb_len R - (mb_pos R + n))); C8 (wz (mb_buf R + (mb_pos R + n))); C8 (wz (mb_len R - (mb_pos R + n))); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 MR_RA2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                 (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 out) (Z_to_bv 64 outl) (Z_to_bv 64 (mb_bm R)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MR_RA2) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros OUTL OUT POSR LENR BUFP BUFH NR NLE BMC BL3 BMP FR ST CEIL LO MI.
    unfold MR_RA2 in *. unfold wz in BMC. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(mb_bm R, mb_bm R + 32)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. st1. st1. zstep. zstep. zstep.       (* [comment removed for export] *)
    change (Z_to_bv 64 (mb_len R - mb_pos R + - n)) with (wz (mb_len R - mb_pos R + - n)).
    replace (Z_to_bv 64 (n + (mb_buf R + mb_pos R))) with (wz (mb_buf R + mb_pos R + n)) by (unfold wz; f_equal; lia).
    st1. st1.                                  (* [comment removed for export] *)
    step. ub_dead_by (clear - NR POSR LENR BUFP BUFH HCEILB).      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.        (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.        (* [comment removed for export] *)
    st1. step.                                 (* [comment removed for export] *)
    zstep. rewrite Z.add_0_r, swrap32_small by lia. do 7 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    replace (mb_len R - (mb_pos R + n)) with (mb_len R - mb_pos R + - n) by lia.
    replace (mb_buf R + (mb_pos R + n)) with (mb_buf R + mb_pos R + n) by lia. exact BMC.
  Qed.

  (* [comment removed for export] *)
  Lemma clr_flags_facts : forall f, 0 <= f < 2^31 -> Z.land f 512 = 512 -> Z.land f 128 = 0 ->
    0 <= Z.land f (Z.lnot 15) < 2^31 /\ Z.land (Z.land f (Z.lnot 15)) 512 = 512 /\ Z.land (Z.land f (Z.lnot 15)) 128 = 0.
  Proof.
    intros f Hf H9 H7. change (Z.land f (Z.lnot 15)) with (Z.ldiff f 15).
    assert (RNG : 0 <= Z.ldiff f 15 < 2^31).
    { change 15 with (Z.ones 4). rewrite Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
      assert (0 <= f / 2^4 <= f / 1) by (split; [apply Z.div_pos; lia| apply Z.div_le_compat_l; lia]). rewrite Z.div_1_r in *. nia. }
    split; [exact RNG|]. split.
    - apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.ldiff_spec by lia.
      destruct (Z.eq_dec n 9) as [->|NE].
      + apply (f_equal (fun z => Z.testbit z 9)) in H9. rewrite Z.land_spec in H9. change (Z.testbit 512 9) with true in H9 |- *.
        change (Z.testbit 15 9) with false. rewrite Bool.andb_true_r in H9. rewrite H9. reflexivity.
      + replace (Z.testbit 512 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
        symmetry. destruct (Z.lt_ge_cases n 9) as [L|L].
        * destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
          destruct (Z.eq_dec n 3) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 4) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 5) as [->|]; [reflexivity|].
          destruct (Z.eq_dec n 6) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 7) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 8) as [->|]; [reflexivity|]. lia.
        * apply Z.bits_above_log2; [lia|]. cbn. lia.
    - apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0 by lia.
      destruct (Z.eq_dec n 7) as [->|NE].
      + apply (f_equal (fun z => Z.testbit z 7)) in H7. rewrite Z.land_spec, Z.bits_0 in H7. change (Z.testbit 128 7) with true in H7 |- *.
        rewrite Bool.andb_true_r in H7. rewrite H7. reflexivity.
      + replace (Z.testbit 128 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
        symmetry. destruct (Z.lt_ge_cases n 7) as [L|L].
        * destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
          destruct (Z.eq_dec n 3) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 4) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 5) as [->|]; [reflexivity|].
          destruct (Z.eq_dec n 6) as [->|]; [reflexivity|]. lia.
        * apply Z.bits_above_log2; [lia|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_mid : forall m A ds k n, bytes_at usegs m A ds -> (k + n <= length ds)%nat ->
    bytes_at usegs m (A + Z.of_nat k) (firstn n (skipn k ds)).
  Proof.
    intros m A ds k n HB HL. rewrite <- (firstn_skipn k ds) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite firstn_length_le in HB by lia. rewrite <- (firstn_skipn n (skipn k ds)) in HB. apply bytes_at_app in HB. exact (proj1 HB).
  Qed.
  (* [comment removed for export] *)
  Definition memread_stmt' : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> bytes_at usegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells usegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - MEMREAD_STACK -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mb_rdn R outl) a (mb_after_bread R (mb_rdn R outl)) ds
                   out (mb_take R ds (mb_rdn R outl)) outl None ((out, out + outl) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_mem_read) fc None m (seg_rom usegs)).

  Lemma memread_spec0 : memread_stmt'.
  Proof.
    unfold memread_stmt'. intros until junk; intros A0 A1 A2 OUTL MB BL SEP BS LEN OUTC MO ST CEIL LO MI RAE.
    pose proof MB as MB0.
    destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & AAL & _ & AH & _). pose proof RB2 as (BBP & _ & _ & BBH & _). pose proof RB3 as (BMP & BMAL & _ & BMH & _). pose proof RB4 as (RPP & _ & _ & RPH & _).
    hide RB1; hide RB2; hide RB3; hide RB4.
    pose proof BL as BL0. destruct BL0 as (BL1 & BL2 & BL3 & BL4).
    pose proof SEP as SEP0. destruct SEP0 as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4).
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY in *.
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4; hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB.
    unfold MEMREAD_STACK, FR_mem_read, BIOACC_STACK, FR_BIO_set_data in LO.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply mr_seg1; [exact A0| exact A1| exact A2| exact OUTL| lia| exact MB| exact BL| exact SEP| exact ST| exact CEIL| | exact MI].
      unfold MEMREAD_STACK, FR_mem_read, BIOACC_STACK, FR_BIO_set_data. lia. }
    cbv beta. intros ms' (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR & MB1). clear MB ST MI.
    unhide OUTR. carry MU1 WM1. extm MU WM MU1 WM1. hide OUTR.
    destruct MB1 as (BC & BBC & BMC & RPC & _).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply bioclearflags_spec with (B := membio_bio R) (lo := lo); [reflexivity| reflexivity| lia| exact AP| apply al16_8; exact AAL| exact BC| | unfold BIO_SIZE; lia| rewrite unsigned_lit by lia; exact ST1| unfold BIOACC_STACK, FR_BIO_set_data; rewrite unsigned_lit by lia; lia| assumption| unfold MR_RA1; rewrite unsigned_lit by lia; reflexivity].
      unfold bio_ok, membio_bio; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_mem_buf_method. lia. }
    unfold bioacc_post, BIO_SIZE. unhide AP1; unhide AP2; unhide AP3; unhide OF1; unhide PS1; unhide OUTR. landx MU WM.
    hide AP1; hide AP2; hide AP3; hide OF1; hide PS1; hide OUTR.
    replace (ret_pc (Z_to_bv 64 MR_RA1)) with (Z_to_bv 64 MR_RA1) by (symmetry; apply ret_pc_even; [unfold MR_RA1; lia| reflexivity]).
    match goal with H : rw_cells usegs _ a (bio_cells _) |- _ => rename H into BC2 end.
    pose proof (clr_flags_facts (mb_flags R) FLR RDO AEOF) as (FL1 & FL2 & FL3).
    unfold buf_cells, wz in BMC; cbn [bm_len bm_data bm_max bm_flags] in BMC.
    destruct (Z.eq_dec (mb_rdn R outl) 0) as [N0|NP].
    - (* [comment removed for export] *)
      eapply evt_cut.
      { eapply mr_seg2z with (R := R) (lo := lo) (fl := Z.land (mb_flags R) (Z.lnot 15)) (a := a) (out := out);
          [exact OUTL| lia| exact POSR| exact LENR| exact N0| exact FL1| exact NUMR| exact BMAL| exact BC2| lia| lia| exact NXT| exact PRV| lia| lia| exact BMC| lia| lia| exact FR| exact ST| exact CEIL| lia| assumption]. }
      cbv beta. intros ms' (-> & ST2).
      rewrite N0. apply evt_done. unfold memrd_post.
      pose proof (rw_cells_CB_split _ _ _ _ 0%nat _ OUTC ltac:(lia)) as [OUT1 OUT2]. cbn [firstn skipn Nat.sub] in OUT1, OUT2. rewrite Nat.sub_0_r in OUT2.
      do 14 eexists. exists v13, junk. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
      split. { unfold mb_after_bread. membio_tac; cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid]; rewrite ?Z.add_0_r; try assumption; try lia.
               all: match goal with |- ?G => idtac "MBLEFT:" G end. }
      split. { exact BS. }
      split; [| exact I].
      replace (mb_take R ds 0) with (@nil byte) by reflexivity. cbn [length]. rewrite Nat.sub_0_r.
      change ([CB 0%nat (@nil byte); CB (Z.to_nat outl) junk]) with ([CB 0%nat (@nil byte)] ++ [CB (Z.to_nat outl) junk]).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact OUT1| exact OUT2].
    - (* [comment removed for export] *)
      assert (NR : 0 < mb_rdn R outl <= mb_len R - mb_pos R /\ mb_rdn R outl <= outl) by (unfold mb_rdn, mb_avail in *; lia).
      eapply evt_cut.
      { eapply mr_seg2c with (R := R) (lo := lo) (a := a); [exact OUTL| lia| exact POSR| exact LENR| exact BUFP| exact BUFH| lia| exact BMAL| exact BMC| lia| lia| exact FR| reflexivity| exact ST| exact CEIL| lia| assumption]. }
      cbv beta. intros ms' ->.
      (* [comment removed for export] *)
      pose proof (rw_cells_CB_split _ _ _ _ (Z.to_nat (mb_rdn R outl)) _ OUTC ltac:(lia)) as [OUT1 OUT2].
      pose proof (bytes_at_mid _ _ _ (Z.to_nat (mb_pos R)) (Z.to_nat (mb_rdn R outl)) BS ltac:(lia)) as SRC. rewrite Z2Nat.id in SRC by lia.
      assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
      { unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
      eapply evt_cut.
      { eapply memcpy_spec with (src := mb_take R ds (mb_rdn R outl)); rewrite ?unsigned_lit by lia;
          [exact SRC| exact SL| exact OUT1| unhide OUTB; lia| assumption]. }
      unfold memcpy_post. unhide OF1; unhide OF2; unhide OF3; unhide OF4; unhide OUTR; unhide OUTB. landx MU WM.
      hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB.
      replace (ret_pc (Z_to_bv 64 MR_RA2)) with (Z_to_bv 64 MR_RA2) by (symmetry; apply ret_pc_even; [unfold MR_RA2; lia| reflexivity]).
      match goal with H : rw_cells usegs _ out [CB _ (mb_take _ _ _)] |- _ => rename H into OUT1' end.
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply mr_seg3 with (R := R) (lo := lo) (a := a) (out := out) (outl := outl); [exact OUTL| lia| exact POSR| exact LENR| exact BUFP| exact BUFH| | | exact BMC| lia| lia| exact FR| exact ST| exact CEIL| lia| assumption]; lia. }
      cbv beta. unhide AP2; unhide AP4; unhide AP6; unhide OF3; unhide PS3. landx MU WM. hide AP2; hide AP4; hide AP6; hide OF3; hide PS3.
      match goal with H : rw_cells usegs _ (mb_bm R) _ |- _ => rename H into BMC3 end.
      match goal with H : stk usegs _ lo (bv_unsigned sp) |- _ => rename H into ST3 end.
      apply evt_done. unfold memrd_post.
      do 14 eexists. eexists. exists (skipn (Z.to_nat (mb_rdn R outl)) junk). split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
      split. { unfold mb_after_bread. membio_tac; cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid]; try assumption; try lia.
               all: match goal with |- ?G => idtac "MBLEFT:" G end. }
      split. { exact BS. }
      split; [| exact I].
      rewrite SL. change ([CB (Z.to_nat (mb_rdn R outl)) (mb_take R ds (mb_rdn R outl)); CB (Z.to_nat outl - Z.to_nat (mb_rdn R outl)) (skipn (Z.to_nat (mb_rdn R outl)) junk)])
        with ([CB (Z.to_nat (mb_rdn R outl)) (mb_take R ds (mb_rdn R outl))] ++ [CB (Z.to_nat outl - Z.to_nat (mb_rdn R outl)) (skipn (Z.to_nat (mb_rdn R outl)) junk)]).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact OUT1'|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact OUT2.
  Qed.

  (* [comment removed for export] *)
  Lemma memread_spec : memread_stmt.
  Proof. exact memread_spec0. Qed.
End S.
