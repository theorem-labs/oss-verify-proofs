(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_iface2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fa_auto STOPS :=
  lazymatch goal with
  | b0 : Z, b1 : Z, b2 : Z, b3 : Z, b4 : Z, b5 : Z |- evt _ (fast_args_post2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?SPV ?ARGS ?DST ?dsz ?SRC ?n ?DT _ _ _) _ =>
      kx_auto STOPS 200%nat
        [KZRange (n - (b0 + 256 * b1) - (b2 + 256 * b3) - (b4 + 256 * b5) - 6) 8 (2^32);
         KZRange (n - (b0 + 256 * b1) - (b2 + 256 * b3) - 6) 16 (2^32);
         KZRange (n - (b0 + 256 * b1) - 6) 24 (2^32);
         KZRange (b0 + 256 * b1) 8 65535; KZRange (b2 + 256 * b3) 8 65535; KZRange (b4 + 256 * b5) 8 65535;
         KZRange b0 0 255; KZRange b1 0 255; KZRange b2 0 255; KZRange b3 0 255; KZRange b4 0 255; KZRange b5 0 255;
         KZRange SPV 4096 (2^47); KZRange ARGS 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 30 (2^32); KZRange (SRC + n) 4096 (2^47);
         KZRange DT 4096 (2^47); KZRange DST 0 (2^47); KZRange dsz 1 (2^32); KZRange (DST + dsz) 0 (2^47);
         KZWr ARGS 152; KZWr (SPV - 16) 16;
         KZDisj ARGS 152 SRC n; KZDisj ARGS 152 DT 4; KZDisj (SPV - 16) 16 SRC n; KZDisj (SPV - 16) 16 DT 4; KZDisj (SPV - 16) 16 ARGS 152]
        [(SRC, n); (DT, 4)]
  end.

(* [comment removed for export] *)
Lemma land_ff0000 : forall x, 0 <= x -> Z.land x 16711680 = ((x / 65536) mod 256) * 65536.
Proof.
  intros x Hx.
  change 16711680 with (Z.shiftl (Z.ones 8) 16).
  change 256 with (2^8). rewrite <- (Z.land_ones (x / 65536) 8) by lia.
  change 65536 with (2^16). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  destruct (Z_lt_le_dec k 16) as [L|L].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. replace (k - 16 + 16) with k by lia. reflexivity.
Qed.

Lemma hdr_log11 : forall dth : list byte, Z.of_nat (length dth) = 4 ->
  Z.land (bv_unsigned (Z_to_bv 64 (extz true 4 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat 0) dth)))))) 16711680 = 720896 ->
  nth_error dth 2 = Some (Z_to_bv 8 11).
Proof.
  intros dth HL H.
  destruct dth as [|d0 [|d1 [|d2 [|d3 [|? ?]]]]]; cbn [length] in HL; try lia.
  change (Z.to_nat 0) with 0%nat in H. cbn [skipn firstn] in H.
  rewrite Bytes.bytes_le_to_Z_le_val in H. cbn [map Bytes.le_val] in H.
  pose proof (bv_unsigned_in_range 8 d0) as R0. pose proof (bv_unsigned_in_range 8 d1) as R1.
  pose proof (bv_unsigned_in_range 8 d2) as R2. pose proof (bv_unsigned_in_range 8 d3) as R3.
  unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  set (u := bv_unsigned d0 + 256 * (bv_unsigned d1 + 256 * (bv_unsigned d2 + 256 * (bv_unsigned d3 + 256 * 0)))) in *.
  assert (HU : 0 <= u < 2^32) by (unfold u; lia).
  unfold extz in H. change (8 * N.of_nat 4)%N with 32%N in H.
  rewrite Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod in H.
  assert (E : exists k, 0 <= bv_swrap 32 u mod 2^64 /\ bv_swrap 32 u mod 2^64 = u + k * 2^32).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
    change (2^32 / 2) with (2^31).
    destruct (Z_lt_le_dec u (2^31)) as [S|S].
    - exists 0. rewrite (Z.mod_small (u + 2^31) (2^32)) by lia. rewrite Z.mod_small by lia. lia.
    - exists (2^32 - 1).
      replace ((u + 2^31) mod 2^32) with (u - 2^31)
        by (rewrite <- (Z.mod_add (u + 2^31) (-1) (2^32)) by lia; rewrite Z.mod_small by lia; lia).
      replace (u - 2^31 - 2^31) with (u - 2^32) by lia.
      replace ((u - 2^32) mod 2^64) with (u - 2^32 + 2^64)
        by (rewrite <- (Z.mod_add (u - 2^32) 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia).
      lia. }
  destruct E as (k & E0 & E). rewrite land_ff0000 in H by exact E0. rewrite E in H.
  assert (D2 : bv_unsigned d2 = 11).
  { assert (((u + k * 2^32) / 65536) mod 256 = bv_unsigned d2).
    { replace (u + k * 2^32) with (bv_unsigned d0 + 256 * bv_unsigned d1 + (bv_unsigned d2 + 256 * (bv_unsigned d3 + k * 256)) * 65536) by (unfold u; lia).
      rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned d0 + 256 * bv_unsigned d1)) by lia.
      rewrite Z.add_0_l. rewrite Z.mul_comm with (n := 256), Z.mod_add by lia. apply Z.mod_small. lia. }
    lia. }
  cbn [nth_error]. f_equal. apply bv_eq. rewrite D2. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma fast_args_proof2 : fast_args_stmt2.
Proof.
  unfold fast_args_stmt2, PHUF_FASTARGS.
  intros until junk. intros MI STK LO0 LO SPB AC SRCB SRCL DTB DTL A0 A1 A2 S0 S1 S2 N32 D0 D1 D2 O0 O1 O2 DJ1 DJ2.
  assert (MU : munch [(ARGS, ARGS + 152); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono psegs m m) by apply wmono_refl.
  pose proof STK as STK0.
  carve_frame 16%nat STK.
  Time kx_autoLx [0x24440] 400%nat
    [KZRange SPV 4096 (2^47); KZRange ARGS 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^32); KZRange (SRC + n) 4096 (2^47);
     KZRange DT 4096 (2^47); KZRange DST 0 (2^47); KZRange dsz 0 (2^32); KZRange (DST + dsz) 0 (2^47);
     KZWr ARGS 152; KZWr (SPV - 16) 16;
     KZDisj ARGS 152 SRC n; KZDisj ARGS 152 DT 4; KZDisj (SPV - 16) 16 SRC n; KZDisj (SPV - 16) 16 DT 4; KZDisj (SPV - 16) 16 ARGS 152]
    [(SRC, n); (DT, 4)].
  (* [comment removed for export] *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 149604) _ _ _ _) =>
           kx_mem; zstep; release_frame FR STK SPV;
           apply evt_done; unfold fast_args_post2; repeat (lazymatch goal with |- ex _ => eexists end);
           split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]; split; [exact STK|];
           right; split; [first [left; reflexivity | right; vm_compute; reflexivity]|]; split; [lia|];
           destruct (rw_cells_forget psegs _ _ _ AC) as [bs Hbs]; exists bs; exact Hbs
       | _ => idtac
       end.
  (* [comment removed for export] *)
  kx_read_eq 31%nat RDH.
  rewrite (rdval_bytes_at psegs m DT dth 0 4 true DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)) in RDH.
  assert (HLOG : nth_error dth 2 = Some (Z_to_bv 8 11)).
  { apply (hdr_log11 dth DTL). rewrite <- RDH.
    lazymatch goal with KB : Z.land (bv_unsigned (ev KXE 31)) 16711680 = 720896 |- _ => exact KB end. }
  clear RDH.
  (* [comment removed for export] *)
  kx_read_ranges. kx_mem.
  remember (bv_unsigned (ev KXE 32)) as b0 eqn:E0. remember (bv_unsigned (ev KXE 33)) as b1 eqn:E1.
  remember (bv_unsigned (ev KXE 34)) as b2 eqn:E2. remember (bv_unsigned (ev KXE 35)) as b3 eqn:E3.
  remember (bv_unsigned (ev KXE 36)) as b4 eqn:E4. remember (bv_unsigned (ev KXE 37)) as b5 eqn:E5.
  clear E0 E1 E2 E3 E4 E5.
  assert (L1 : 8 <= b0 + 256 * b1 <= 65535) by lia.
  assert (L2 : 8 <= b2 + 256 * b3 <= 65535) by lia.
  assert (L3 : 8 <= b4 + 256 * b5 <= 65535) by lia.
  assert (L4 : 8 <= n - (b0 + 256 * b1) - (b2 + 256 * b3) - (b4 + 256 * b5) - 6) by lia.
  assert (DZ : 1 <= dsz) by lia.
  clear KXBR KXBR0 KXBR1 KXBR2 KXBR3 KXBR4 KXBR5 KXBR6 KXRD KXA KXK.
  (* [comment removed for export] *)
  kx_join_begin HJ1.
  { Time fa_auto [0x24528].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149624) _ _ _ _) =>       (* [comment removed for export] *)
             kx_mem; zstep; release_frame FR STK SPV;
             apply evt_done; unfold fast_args_post2; repeat (lazymatch goal with |- ex _ => eexists end);
             split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact STK|];
             right; split; [left; reflexivity|]; split; [lia|];
             destruct (rw_cells_forget psegs _ _ _ AC) as [bs Hbs]; exists bs; exact Hbs
         | _ => idtac
         end.
    all: kx_fact KF (DST + 3 * ((dsz + 3) / 4) < DST + dsz).
    Time all: kx_join HJ1 [11%nat; 29%nat; 30%nat]. }
  kx_join_end.
  (* [comment removed for export] *)
  kx_join_begin HJ2.
  { Time fa_auto [0x2460c].
    Time all: kx_join HJ2 [11%nat; 7%nat; 28%nat]. }
  kx_join_end.
  kx_join_begin HJ3.
  { Time fa_auto [0x246f0].
    Time all: kx_join HJ3 [11%nat; 5%nat; 6%nat]. }
  kx_join_end.
  kx_join_begin HJ4.
  { Time fa_auto [0x247d8].
    Time all: kx_join HJ4 [11%nat; 16%nat; 17%nat]. }
  kx_join_end.
  (* [comment removed for export] *)
  Time fa_auto (@nil Z).
  kx_mem. zstep.
  rewrite (Z.mod_small (dsz + 3) (2^64)) in * by lia.
  match goal with FRx : rw_cells psegs ?mm (SPV + -16) _, STx : stk psegs ?mm lo (SPV + -16) |- _ => release_frame FRx STx SPV end.
  apply evt_done; unfold fast_args_post2; repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  left. split; [reflexivity|].
  exists (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5). do 4 eexists.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact KF|].
  split; [|exact HLOG].
  match goal with H : rw_cells psegs ?mm ARGS ?cs |- rw_cells psegs ?mm ARGS ?cs' =>
    replace cs' with cs; [exact H|]; unfold fast_args_cells;
    repeat (apply f_equal2; [first [reflexivity | (do 2 apply f_equal; lia)]|]); reflexivity end.
Time Qed.

Lemma fast_args_proof : fast_args_stmt.
Proof. exact (fast_args_stmt2_weaken fast_args_proof2). Qed.
