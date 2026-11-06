(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import N6_tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_C9_ctrl.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ARD_RA_READ : Z := 0x51cdd8.    (* [comment removed for export] *)
Definition ARD_RA_TF1 : Z := 0x51cec8.     (* [comment removed for export] *)
Definition ARD_RA_DU : Z := 0x51d354.      (* [comment removed for export] *)
Definition ARD_RA_MC : Z := 0x51d3c0.      (* [comment removed for export] *)
Definition ARD_RA_TF2 : Z := 0x51cdf4.     (* [comment removed for export] *)
Definition ARD_RA_DF : Z := 0x51ce34.      (* [comment removed for export] *)
Definition ARD_RA_DI2 : Z := 0x51ce58.     (* [comment removed for export] *)
Definition ARD_HEAD : Z := 0x51cd90.
Definition ARD_EXIT : Z := 0x51d4e0.
Definition ASHB : Z := 2147450880.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ardslots (ctx fbase ff vret mb a nump : Z) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte) : list cell :=
  [C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 (Z.shiftr fbase 3 + ASHB)); C8 (Z_to_bv 64 fbase); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 vret);
   C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (Z.shiftr ctx 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 4)); C8 w104; C8 (Z_to_bv 64 (ctx + 1542));
   C8 (Z_to_bv 64 (ctx + 8)); C8 w128; C8 j136; C8 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)); C8 j152; C8 (Z_to_bv 64 (ctx + 40));
   C8 (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 32)); C8 (Z_to_bv 64 (Z.shiftr (ctx + 24) 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 24));
   C8 (Z_to_bv 64 (ctx + 12)); C8 (Z_to_bv 64 (ctx + 1542)); C8 w216; C8 w224; C8 (Z_to_bv 64 nump);
   C8 w240; C8 (Z_to_bv 64 ctx); CB 16 j256; C8 (Z_to_bv 64 fbase)].
(* [comment removed for export] *)
Definition ardsaves (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : list cell :=
  [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].
(* [comment removed for export] *)
Definition rdhdr (bl bo tl c enc : Z) : list cell :=
  [C4 (wz bl); C4 (wz bo); C4 (wz tl); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz enc)].

(* [comment removed for export] *)
Lemma unsigned_neg64 : forall c, - 2^64 <= c < 0 -> bv_unsigned (Z_to_bv 64 c) = c + 2^64.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  replace c with ((c + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma land64_neg : forall k, - 2^64 <= k < 0 -> Z.land k 18446744073709551615 = k + 2^64.
Proof.
  intros k Hk. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  replace k with ((k + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma land64_nonneg : forall k, 0 <= k < 2^64 -> Z.land k 18446744073709551615 = k.
Proof. intros k Hk. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac killb K :=
    first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; apply Z.ltb_lt in K'; exfalso; revert K K'; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia ].

  (* [comment removed for export] *)
  Lemma ard_head :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      0 < c < 2^31 -> 0 <= out < 2^64 -> 0 <= outl < 2^64 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_READ) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 mb) (Z_to_bv 64 (ctx + 1542)) (Z_to_bv 64 1024) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros C OUT OUTL CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_HEAD, ARD_RA_READ, P_BIO_read, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    (* [comment removed for export] *)
    st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC1 : accessible mx ctx 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW0]) end.
    (* [comment removed for export] *)
    st1. ck8_check ACC1 (ctx + 24).
    (* [comment removed for export] *)
    st1. st1. rewrite ?(sx32_lit c) by lia. step. if_cases K; zify_cond K; [killb K|]; try clear K.
    (* [comment removed for export] *)
    ck8_check ACC1 (ctx + 8).
    st1. rewrite ?(sx32_lit 0) by lia. st1. zstep. step. zstep. step. step. step.
    replace (Z_to_bv 64 (ctx + 1542 + 0)) with (Z_to_bv 64 (ctx + 1542)) by (f_equal; lia).
    finish.
    all: match goal with |- ?G => idtac "HEAD-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_head_exit :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      - 2^31 <= c <= 0 -> 0 <= out < 2^64 -> 0 <= outl < 2^64 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 a0',
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0' a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros C OUT OUTL CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_HEAD, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    (* [comment removed for export] *)
    st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC1 : accessible mx ctx 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW0]) end.
    (* [comment removed for export] *)
    st1. ck8_check ACC1 (ctx + 24).
    (* [comment removed for export] *)
    st1. st1. step. if_cases K; zify_cond K.
    2:{ exfalso. rewrite (ECH_C9_ctrl.sx32_wz_small c) in * by lia. destruct (Z.eq_dec c 0) as [E0|NZ].
        - rewrite E0 in *. rewrite unsigned_lit in * by lia. lia.
        - rewrite (unsigned_neg64 c) in * by lia. lia. }
    clear K.
    finish.
    all: match goal with |- ?G => idtac "HEADX-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_data1 :
    forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n bl bo c enc lo : Z),
      0 < n <= 1024 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_TF1) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 a) (Z_to_bv 64 (-1)) (Z_to_bv 64 ctx) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_test_flags) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 n) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo n c enc))
        (MS (mkR (Z_to_bv 64 ARD_RA_READ) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_READ) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros N CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_READ, ARD_RA_TF1, P_BIO_test_flags, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    step. st1. step. if_cases K; zify_cond K; [| killb K]; try clear K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC1 : accessible mx ctx 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW0]) end.
    (* [comment removed for export] *)
    ck8_load ACC1 (ctx + 8). st1. step. if_false_by (ck1_bnez_false 0 eq_refl).
    st1. rewrite ?(sx32_lit 0) by lia. zstep. zstep.
    replace (bv_swrap 32 (0 + n)) with n by (rewrite Z.add_0_l, swrap32_small by lia; reflexivity).
    (* [comment removed for export] *)
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC2 : accessible mx ctx 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW0]) end.
    (* [comment removed for export] *)
    zstep. ck8_check ACC2 (ctx + 20).
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 1) by lia. step. if_cases K; zify_cond K; [killb K|]; try clear K.
    (* [comment removed for export] *)
    st1. st1. step. step. step. step.
    finish.
    all: match goal with |- ?G => idtac "D1-LEFT:" G end.
  Qed.

  Local Ltac reacc ACC MU NSW AC2 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AC2 : accessible mx _ 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW]) end.

  (* [comment removed for export] *)
  Lemma ard_data2 :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n fl bl bo c enc lo : Z),
      0 <= fl < 2^31 -> Z.land fl BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 n) j256) ->
      rw_cells asegs m ctx (rdhdr bl bo n c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DU) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 enc) (Z_to_bv 64 (ctx + 40)) (Z_to_bv 64 ctx) (Z_to_bv 64 (ctx + 1542)) (Z_to_bv 64 n) a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeUpdate) fc None m1 (seg_rom asegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 n) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_TF1) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FL NONL CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_TF1, ARD_RA_DU, P_EVP_DecodeUpdate, B64CTX_SIZE, BIO_FLAGS_BASE64_NO_NL, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    zstep. rewrite NONL. step. if_cases K; zify_cond K; [| killb K]; try clear K.
    (* [comment removed for export] *)
    st1. st1. st1. step. st1.
    reacc ACC MU NSW0 ACC1.
    (* [comment removed for export] *)
    ck8_check ACC1 (ctx + 8). st1.
    reacc ACC MU NSW0 ACC2.
    (* [comment removed for export] *)
    st1. ck8_check ACC2 (ctx + 32).
    (* [comment removed for export] *)
    step. st1. st1. st1. step. step.
    finish.
    all: match goal with |- ?G => idtac "D2-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_du_neg :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n k bl bo c enc lo : Z),
      - 2^31 <= k < 0 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 a1',
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 k) a1' (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 4)) (Z_to_bv 64 ctx) a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 0) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr 0 0 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DU) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros K CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DU, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    ck8_check ACC (ctx + 8). st1.
    reacc ACC MU NSW0 ACC1.
    (* [comment removed for export] *)
    st1. ck8_check ACC1 (ctx + 24). st1. st1.
    reacc ACC MU NSW0 ACC2.
    (* [comment removed for export] *)
    st1. zstep. zstep. ck8_load ACC2 (ctx + 4). st1. step. if_false_by (ck1_bnez_false 0 eq_refl). st1.
    reacc ACC MU NSW0 ACC3.
    (* [comment removed for export] *)
    step. if_cases KK; zify_cond KK.
    2:{ exfalso. revert KK. rewrite ?(unsigned_neg64 k), ?(land64_neg k) by lia. lia. }
    clear KK.
    (* [comment removed for export] *)
    ck8_check ACC3 (ctx + 20). st1. ck8_load ACC3 ctx. st1. rewrite ?(sx32_lit 1) by lia. step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    step. step. zstep.
    match goal with |- context [Z_to_bv 64 (Z.land ?x (Z.land k ?y))] => change (Z.land x (Z.land k y)) with 0 end.
    st1.
    finish.
    all: match goal with |- ?G => idtac "DUN-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_du_pos :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n k bl bo c enc lo : Z),
      0 <= k < 2^31 -> 0 <= bl < 2^31 -> 0 < outl < 2^31 -> 0 <= out < 2^64 ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_MC) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 out) (Z_to_bv 64 (ctx + 40)) (Z_to_bv 64 (Z.min bl outl)) (Z_to_bv 64 (ctx + 4)) (Z_to_bv 64 ctx) a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.min bl outl)) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl 0 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DU) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros K BL OUTL OUT CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DU, ARD_RA_MC, AASAN_MEMCPY, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    ck8_check ACC (ctx + 8). st1.
    reacc ACC MU NSW0 ACC1.
    (* [comment removed for export] *)
    st1. ck8_check ACC1 (ctx + 24). st1. st1.
    reacc ACC MU NSW0 ACC2.
    (* [comment removed for export] *)
    st1. zstep. zstep. ck8_load ACC2 (ctx + 4). st1. step. if_false_by (ck1_bnez_false 0 eq_refl). st1.
    reacc ACC MU NSW0 ACC3.
    (* [comment removed for export] *)
    step. if_cases KK; zify_cond KK; rewrite ?(land64_nonneg k) in KK by lia; [killb KK|]; try clear KK.
    (* [comment removed for export] *)
    st1. ck8_check ACC3 ctx. st1. rewrite ?(sx32_lit bl) by lia.
    step. if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - (* [comment removed for export] *) replace (Z.min bl outl) with bl by lia.
      (* [comment removed for export] *)
      step. st1. step. step. step. finish.
    - (* [comment removed for export] *) step. replace (Z.min bl outl) with outl by lia.
      step. st1. step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_mc_loop :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl ret nump bl k enc lo : Z),
      0 <= bl < outl -> outl < 2^31 -> 0 <= ret -> ret + outl < 2^31 -> 0 <= out -> out + outl <= 2^64 ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff ret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl 0 0 k enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 a0' a1' a2' a3',
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0' a1' a2' a3' a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 bl) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 (outl - bl)) s9 (Z_to_bv 64 (out + bl)) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_HEAD) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff (ret + bl) mb a nump w104 w128 j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr 0 0 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 bl) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB))
                 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_MC) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BL OUTL RET RETO OUT OUTO CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_MC, ARD_HEAD, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    ck8_check ACC (ctx + 4). st1. st1.
    reacc ACC MU NSW0 ACC1.
    (* [comment removed for export] *)
    st1. ck8_load ACC1 ctx. st1. step. if_false_by (ck1_bnez_false 0 eq_refl).
    st1. rewrite ?(sx32_lit bl) by lia. step. if_cases KK; zify_cond KK; [killb KK|]; try clear KK.
    (* [comment removed for export] *)
    st1. ck8_check ACC1 ctx. st1.
    reacc ACC MU NSW0 ACC2.
    (* [comment removed for export] *)
    ck8_check ACC2 (ctx + 4). st1. st1.
    (* [comment removed for export] *)
    zstep. replace (bv_swrap 32 (bl + ret)) with (ret + bl) by (rewrite swrap32_small by lia; lia).
    st1. zstep. replace (bv_swrap 32 (outl - bl)) with (outl - bl) by (rewrite swrap32_small by lia; lia).
    zstep. st1.
    step. if_cases KK; zify_cond KK; [| killb KK]; try clear KK.
    finish.
    all: match goal with |- ?G => idtac "MCL-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_mc_done :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl ret nump bl k enc lo : Z),
      0 < outl <= bl -> bl < 2^31 -> 0 <= ret -> ret + outl < 2^31 -> 0 <= out -> out + outl <= 2^64 ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff ret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl 0 0 k enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 a0' a1' a2' a3',
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0' a1' a2' a3' a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 outl) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 0) s9 (Z_to_bv 64 (out + outl)) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff (ret + outl) mb a nump w104 w128 j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr (if bl =? outl then 0 else bl) (if bl =? outl then 0 else outl) 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 outl) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB))
                 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_MC) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BL BLH RET RETO OUT OUTO CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_MC, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    ck8_check ACC (ctx + 4). st1. st1.
    reacc ACC MU NSW0 ACC1.
    (* [comment removed for export] *)
    st1. ck8_load ACC1 ctx. st1. step. if_false_by (ck1_bnez_false 0 eq_refl).
    st1. rewrite ?(sx32_lit bl) by lia. step. if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - (* [comment removed for export] *)
      replace (bl =? outl) with false by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      zstep. replace (bv_swrap 32 (outl + ret)) with (ret + outl) by (rewrite swrap32_small by lia; lia).
      st1. zstep. replace (bv_swrap 32 (outl - outl)) with 0 by (rewrite swrap32_small by lia; lia).
      zstep. st1. step. if_cases KK2; zify_cond KK2; [killb KK2|]; try clear KK2. step.
      finish.
    - (* [comment removed for export] *)
      replace (bl =? outl) with true by (symmetry; apply Z.eqb_eq; lia).
      (* [comment removed for export] *)
      st1. ck8_check ACC1 ctx. st1.
      reacc ACC MU NSW0 ACC2.
      (* [comment removed for export] *)
      ck8_check ACC2 (ctx + 4). st1. st1.
      zstep. replace (bv_swrap 32 (outl + ret)) with (ret + outl) by (rewrite swrap32_small by lia; lia).
      st1. zstep. replace (bv_swrap 32 (outl - outl)) with 0 by (rewrite swrap32_small by lia; lia).
      zstep. st1. step. if_cases KK2; zify_cond KK2; [killb KK2|]; try clear KK2. step.
      finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof1 :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_TF2) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 mb) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_test_flags) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_READ) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros CP CL SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_READ, ARD_RA_TF2, P_BIO_test_flags, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    step. st1. step. if_cases K; zify_cond K; [killb K|]; try clear K.
    (* [comment removed for export] *)
    step. step. step. step.
    finish.
    all: match goal with |- ?G => idtac "EOF1-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof1b :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s9 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DF) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 enc) (Z_to_bv 64 0) (Z_to_bv 64 nump) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (ctx + 32)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_TF2) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_TF2, ARD_RA_DF, P_EVP_DecodeFinal, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    st1. step. if_cases K; zify_cond K; [killb K|]; try clear K.
    (* [comment removed for export] *)
    ck8_check ACC (ctx + 8). st1. rewrite ?(sx32_lit 0) by lia. st1. step. if_cases K; zify_cond K; [killb K|]; try clear K.
    (* [comment removed for export] *)
    st1. ck8_load ACC (ctx + 32). st1. step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    st1. step. st1. step. step.
    finish.
    all: match goal with |- ?G => idtac "EOF1B-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof2 :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump rv bl bo c enc lo : Z),
      (rv = -1 \/ rv = 1) ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DI2) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 enc) (Z_to_bv 64 enc) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (ctx + 32)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 (if rv <? 0 then -1 else 0)) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeInit) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 (ctx + 32)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DF) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros RV CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DF, ARD_RA_DI2, P_EVP_DecodeInit, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    ck8_check ACC (ctx + 32). st1.
    (* [comment removed for export] *)
    destruct RV as [-> | ->].
    - zstep. st1. zstep. step. step. step. replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity). finish.
    - zstep. st1. zstep. step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof3 :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump rc bl bo c enc lo : Z),
      (rc = -1 \/ rc = 0) ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                       (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 rc) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx fbase ff vret mb a nump w104 w128 j136 j152 w216 w224 (Z_to_bv 64 0) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 rc enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB))
                 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) (Z_to_bv 64 rc) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DI2) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros RC CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DI2, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD |- *.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    st1. ck8_check ACC (ctx + 24). st1. st1.
    reacc ACC MU NSW0 ACC1.
    (* [comment removed for export] *)
    ck8_check ACC1 (ctx + 8). st1. rewrite ?(sx32_lit 0) by lia. step. if_cases K; zify_cond K; [| killb K]; try clear K.
    finish.
    all: match goal with |- ?G => idtac "EOF3-LEFT:" G end.
  Qed.
End S.
