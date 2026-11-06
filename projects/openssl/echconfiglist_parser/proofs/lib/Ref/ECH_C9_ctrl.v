(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C7_read ECH_C7_rd ECH_C7_new.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma disjoint_from_above : forall W A n lo, Forall (fun iv : Z * Z => lo <= fst iv) W -> A + n <= lo -> disjoint_from W A n.
Proof.
  induction W as [|[wl wh] W IH]; intros A n lo FW LE; cbn; [exact I|].
  pose proof (Forall_inv FW) as K. cbn in K. split; [lia| eapply IH; [apply (Forall_inv_tail FW)| exact LE]].
Qed.

(* [comment removed for export] *)
Lemma div256k_mod64 : forall c q k, 0 <= k <= 3 -> ((c + 2^64 * q) / 256 ^ k) mod 256 = (c / 256 ^ k) mod 256.
Proof.
  intros c q k Hk.
  assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct K as [ -> | [ -> | [ -> | -> ] ] ]; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  - rewrite !Z.div_1_r. replace (c + 18446744073709551616 * q) with (c + (72057594037927936 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (c + 18446744073709551616 * q) with (c + (72057594037927936 * q) * 256) by lia. rewrite Z.div_add by lia.
    replace (c / 256 + 72057594037927936 * q) with (c / 256 + (281474976710656 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (c + 18446744073709551616 * q) with (c + (281474976710656 * q) * 65536) by lia. rewrite Z.div_add by lia.
    replace (c / 65536 + 281474976710656 * q) with (c / 65536 + (1099511627776 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (c + 18446744073709551616 * q) with (c + (1099511627776 * q) * 16777216) by lia. rewrite Z.div_add by lia.
    replace (c / 16777216 + 1099511627776 * q) with (c / 16777216 + (4294967296 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma le4_bytes_of_cont : forall (bs : list byte) cont,
  map bv_unsigned bs = map (fun z => z mod 256) [cont; cont / 256; cont / 65536; cont / 16777216] -> bs = le4 (wz cont).
Proof.
  intros bs cont E. apply bytes_eq_of_unsigned. rewrite E. unfold le4, wz. rewrite Z_to_bv_unsigned.
  cbn [Z_to_le_bytes map]. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2^64).
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod cont (2^64) ltac:(lia)) as DM. set (q := cont / 2 ^ 64) in DM.
  replace (cont mod 2^64) with (cont + 2^64 * (- q)) by lia.
  change (2 ^ 8) with (256 ^ 1). change (2 ^ (8 + 8)) with (256 ^ 2). change (2 ^ (8 + 8 + 8)) with (256 ^ 3).
  rewrite !div256k_mod64 by lia. rewrite Z.pow_1_r. change (256 ^ 2) with 65536. change (256 ^ 3) with 16777216.
  replace ((cont + 2 ^ 64 * - q) mod 256) with (cont mod 256); [reflexivity|].
  replace (cont + 2 ^ 64 * - q) with (cont + (- 72057594037927936 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma sx32_wz_small : forall c, - 2^31 <= c < 2^31 -> sx32 (wz c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold sx32, wz. f_equal. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2 ^ Z.of_N 64) with (2^64). change (2^32 / 2) with (2^31).
  pose proof (Z.div_mod c (2^64) ltac:(lia)) as DM. set (q := c / 2 ^ 64) in DM.
  replace (c mod 2^64 + 2^31) with ((c + 2^31) + (4294967296 * (- q)) * 2^32) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Lemma MEMBIO_frame_above : forall LB m m' a R lo W,
    MEMBIO LB m a R -> MEMBIO_below a R lo -> munch W m m' -> wmono rsegs m m' -> Forall (fun iv : Z * Z => lo <= fst iv) W -> MEMBIO LB m' a R.
  Proof.
    intros LB m m' a R lo W MB (B1 & B2 & B3 & B4) MU WM FW.
    destruct MB as (C1 & C2 & C3 & C4 & REST).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    split; [| split; [| split; [| split; [| exact REST]]]];
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]; eapply disjoint_from_above; [exact FW| cbn; lia]).
  Qed.
  Lemma METH_mem_frame_above : forall m m' W,
    METH_mem m -> munch W m m' -> wmono rsegs m m' -> Forall (fun iv : Z * Z => hceil <= fst iv) W -> METH_mem m'.
  Proof.
    intros m m' W ME MU WM FW. hcb. unfold METH_mem in *. eapply rw_cells_transport; [exact ME| exact MU| exact WM|].
    eapply disjoint_from_above; [exact FW|]. unfold A_mem_buf_method, O_METH_BREAD. cbn. lia.
  Qed.
End HCW.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma b64ctrl_spec : b64ctrl_stmt.
  Proof.
    unfold b64ctrl_stmt. intros until cont. intros A0 A1 A2 A3 PR BC NX BLK BEL CTX LH CONT CASE ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_b64_ctrl, FR_BIO_ctrl, FR_mem_ctrl in LO.
    unfold P_b64_ctrl, P_BIO_get_data in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & _ & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI).
    destruct BEL as (BL1 & BL2 & BL3). unfold BIO_SIZE, B64CTX_SIZE, BIO_CTRL_EOF, BIO_CTRL_PUSH, b64ctrl_rv in *.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. rewrite NX in BC.
    unfold b64ctx_used_cells, wz in CTX.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 11 st1. step. step. step. step. step. step.
    carve_frame 16%nat ST. do 4 st1. st1. do 3 st1. release_frame FR0 ST (bv_unsigned sp + -80). step.
    step. step. step. step.
    carve_frame 16%nat ST. do 4 st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. st1. do 3 st1. release_frame FR0 ST (bv_unsigned sp + -80). step.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step.
    destruct CASE as [(-> & MB & MBL & MSEP & METH)|(-> & CONTR)].
    - (* [comment removed for export] *)
      pose proof MB as MB0. destruct MB0 as (_ & _ & _ & _ & _ & _ & _ & _ & RBm & _). pose proof RBm as (MP & _ & _ & MH & _).
      step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
      step. step. step. if_false. step. step. step. step. st1. step. step. zstep.
      change (6 =? 2) with false. cbv iota.
      step. step. step. step. step. do 9 st1. step. release_frame FR ST (bv_unsigned sp). step. zstep.
      eapply evt_mono.
      { eapply bioctrl_mem_spec with (lo := lo) (LB := LB) (R := M) (cmd := 6) (larg := 0) (parg := parg); try reflexivity.
        all: try first [right; reflexivity| exact MBL| exact MSEP| exact CEIL| exact RAE].
        all: lazymatch goal with
             | |- MEMBIO _ _ _ _ => eapply MEMBIO_frame_above; [exact MB| exact MBL| exact MU| exact WM| apply Forall_cons; [cbn; lia| apply Forall_nil]]
             | |- _ -> METH_mem _ => intros _; eapply METH_mem_frame_above; [exact METH| exact MU| exact WM| apply Forall_cons; [cbn; lia| apply Forall_nil]]
             | |- stk _ _ _ _ => exact ST
             | |- mem_inv _ _ => assumption
             | |- _ => try (unfold BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl; lia); try lia
             end.
        all: match goal with |- ?G => idtac "PUSH-LEFT:" G end. }
      cbv beta. intros ms' PO. unfold memctrl_post in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & _).
      unfold mem_ctrl_rv, BIO_CTRL_EOF in *. change (6 =? 2) with false. cbv iota.
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2. split; [reflexivity|].
      split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        step. step. step. do 9 st1. step. release_frame FR ST (bv_unsigned sp). step.
        finish.
        all: match goal with |- ?G => idtac "EOF0-LEFT:" G end.
      + step. step. step. if_false. step. step. step. step. st1. step. step. zstep.
        change (2 =? 2) with true. cbv iota.
        (* [comment removed for export] *)
        st1. rewrite (le4_bytes_of_cont _ _ CONT). rewrite sext_extract_le4. rewrite sx32_wz_small by lia.
        step.
        if_cases K3; zify_cond K3; [| exfalso; rewrite ?unsigned_lit, ?signed_lit in * by lia; lia].
        step. do 9 st1. step. release_frame FR ST (bv_unsigned sp). step.
        finish.
        all: match goal with |- ?G => idtac "EOF-LEFT:" G end.
  Qed.
End S.
