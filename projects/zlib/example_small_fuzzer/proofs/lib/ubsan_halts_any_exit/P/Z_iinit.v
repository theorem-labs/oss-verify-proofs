(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Drv_kit F_fwrite Z_kit Zlib_iface Zh_kit.

Module Z_img.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Zlib_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac zl_range_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells psegs m A cs);
  [ apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha;
        unfold ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
Ltac zl_relro_chunk ZS m A cs H := let N := fresh "NONE" in pose proof (proj1 ZS) as N; zl_range_chunk N m A cs H; clear N.
Ltac zl_got_chunk ZS m A cs H := let N := fresh "NONE" in pose proof (proj1 (proj2 ZS)) as N; zl_range_chunk N m A cs H; clear N.

Section Examples.
Context {CE__ : Ceiling.Ceiling} {RN__ : Rnd.RunRnd}.

Lemma config6_cells : forall m, zl_statics m ->
  rw_cells psegs m 0x28f78 [C2 (Z_to_bv 64 8); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 128); C2 (Z_to_bv 64 128); C8 (Z_to_bv 64 0x194dc)].
Proof.
  intros m ZS.
  zl_relro_chunk ZS m 0x28f78%Z [C2 (Z_to_bv 64 8); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 128); C2 (Z_to_bv 64 128); C8 (Z_to_bv 64 0x194dc)] H.
  exact H.
Qed.

(* 1.4: zcalloc / zcfree are file-static; inflateInit_ takes their addresses pc-relative, so no GOT slot is read
   (the 1.3.1 lemma got_zcalloc_cells, slots 0x28fc0 / 0x28fc8, is gone). *)
End Examples.
End Z_img.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Startup_glue.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Rnd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_iinit.Z_img OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_dinit_kit Z_irep Z_ikit Z_iinit_kit.

Module Z_ireset14.
(* inflateReset2 is gone. inflateInit_ zeroes the new state (memset(state + 8, 0, 7168)),
   stores strm, mode = HEAD, wrap = reqwrap = 5 and reqbits = wbits = 15, then calls the new inflateReset. With
   wbits = reqbits, inflateReset sets wrap := reqwrap, clears wsize / whave / wnext, then does inflateResetKeep's work.
   Every byte it does not store is 0, so the head's pre and post cells are concrete. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Zlib_iface Zh_kit Z_ikit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition Z_INFLATERESET : Z := 0x1cbf0.

(* [the head (168 bytes) as inflateInit_ leaves it: strm, mode HEAD, last 0, wrap 5, reqwrap 5, reqbits 15, wbits 15,
    every other byte 0; one cell per access width of inflateReset] *)
Definition ireset14_pre (S : Z) : list cell :=
  [C8 (wz S); C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
(* [after inflateReset: mode + last as one word, havedict 0 + flags -1 as one word, dmax 32768, lencode = distcode =
    next = the codes array] *)
Definition ireset14_post (S As : Z) : list cell :=
  [C8 (wz S); C8 (wz 16180); C4 (wz 5); C4 (wz 5); C8 (wz (-4294967296)); C4 (wz 32768); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (As + 1384)); C8 (wz (As + 1384));
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (As + 1384))].

Definition ireset14_post_st (S As lo : Z) (ni ai no ao : Z) (p1 p2 jdt jrs : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (S, S + 112); (As, As + 168); (As + 7160, As + 7168)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2 ++ [C8 (wz 0); C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz 0); CB 4 jdt; C8 (wz 1); CB 8 jrs])
    /\ rw_cells psegs m' As (ireset14_post S As)
    /\ rw_cells psegs m' (As + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)].

Lemma ireset14_spec : forall (S As lo : Z) (ni ai ti no ao to : Z) (p1 p2 jdt0 jdt jad jrs : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x5b000 <= lo ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 4 jdt0; CB 4 jdt; CB 8 jad; CB 8 jrs]) ->
  rw_cells psegs m As (ireset14_pre S) ->
  rw_cells psegs m (As + 7160) [C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  bv_unsigned sp <= S -> S + 112 < 2^63 -> 0 < As -> As + 7176 <= lo ->
  mem_inv psegs m ->
  evt psegs (ireset14_post_st S As lo ni ai no ao p1 p2 jdt jrs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATERESET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZS GA GT SPS S63 As0 As1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112); (As, As + 168); (As + 7160, As + 7168)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS. unfold ireset14_pre in GA. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  unfold Z_INFLATERESET. carve_frame 32%nat STK.
  do 8 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_true.
  do 6 zs. br_false. do 3 zs. br_true.
  do 4 zs.
  do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 4 zs. br_false.
  do 10 zs. br_false.
  do 3 zs.
  do 11 zs.
  apply (rw_cells_merge psegs _ As [C8 (wz S)] [C4 (wz 16180); C4 (wz 0)]) in GA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in GA.
  zs.
  do 5 zs.
  do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  zs.
  apply evt_done. unfold ireset14_post_st. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  split; [unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|]. split; [exact GA| exact GT].
Qed.
End Z_ireset14.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_irep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_iinit_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_iinit.Z_ireset14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateUpdw_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZApiInst ZTaintI.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateUpdw_run.RefInflateInit_run OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZTaintI.

Module Z_iend.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep Arr Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Drv_kit F_fwrite Z_kit Zlib_iface Zh_kit Startup_glue.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Rnd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_irep Z_ikit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState RefInflateSafeD RefInflateSafeTY ZApiInst ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition PC_IE_RET1 : Z := 0x1ee50.
Definition PC_IE_RET2 : Z := 0x1ee68.

Definition ie_at_free (S lo ret ptr : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz ret) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz S) s1 a0 (wz ptr) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz Z_ZCFREE) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -16)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma iend_to_free : forall (L : ilay) (s : inflate_state) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x5b000 <= lo ->
  rw_cells psegs m (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) -> isA m L s ->
  bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 -> 0 < il_As L -> il_As L + 7176 <= lo ->
  16180 <= is_mode s <= 16211 -> (is_window_blk s <> None -> 0 < il_Aw L < 2^63) ->
  mem_inv psegs m ->
  evt psegs (ie_at_free (il_S L) lo (if is_window_blk s then PC_IE_RET1 else PC_IE_RET2) (if is_window_blk s then il_Aw L else il_As L)
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATEEND) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZQ GA SPS S63 As0 As1 RM RW MI.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in ZQ. open_isA GA.
  unfold Z_INFLATEEND. carve_frame 16%nat STK.
  do 3 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_true.
  do 4 zs. rewrite (swrap32_sub _ 16180) by (try reflexivity; lia). do 2 zs. br_false.
  do 4 zs.
  destruct (is_window_blk s) as [wb|] eqn:EW; cbn [win_addr].
  - specialize (RW ltac:(discriminate)). zs. br_false. do 4 zs.
    apply evt_done. unfold ie_at_free. do 15 eexists. split; [reflexivity|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  - zs. br_true. do 3 zs.
    apply evt_done. unfold ie_at_free. do 15 eexists. split; [reflexivity|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma iend_to_free2 : forall (L : ilay) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk psegs m lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 32 -> 0x5b000 <= lo ->
  rw_cells psegs m (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
  bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
               ms' = MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 (wz (il_As L)) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz Z_ZCFREE) fc None m (seg_rom psegs))
    (MS (mkR (wz PC_IE_RET1) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_IE_RET1) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZQ SPS S63 MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in ZQ.
  unfold PC_IE_RET1. do 6 zs.
  apply evt_done. do 14 eexists. reflexivity.
Qed.

Lemma iend_tail : forall (L : ilay) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk psegs m lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 32 -> 0x5b000 <= lo ->
  rw_cells psegs m (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
  bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom psegs)
               /\ munch [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
               /\ exists j, rw_cells psegs m' (il_S L + 48) [CB 64 j])
    (MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_IE_RET2) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZQ SPS S63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in ZQ.
  unfold PC_IE_RET2. do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  zs.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  destruct (rw_cells_forget psegs _ _ _ ZQ) as (j & Hj). exists j. exact Hj.
Qed.

Section ZFREE.
  Hypothesis FREE : rfree_stmt.

  Lemma izfree : forall {A : Type} (K : unit -> Monad.M PState A) (POST : A -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (p : bptr) (Ab n lo B : Z) (errv : word),
    RHEAP s LBc m -> In (p, Ab, n) LBc ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz Ab ->
    (forall (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv] -> rauxv_ok m' B ->
       rheap_pres (lb_remove p LBc) (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       RHEAP s' (lb_remove p LBc) m' ->
       implM psegs (K tt) s' POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (bind lops (lib_free lops (Some p)) K) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP HIN AUX SPB STK CEIL LOSP ERRC MI TP -> KONT.
    cbn [bind lops Target.ops lib_free].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCFREE. zstep. zstep. apply evt_done.
    lazymatch goal with |- ITree.impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_bind.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc p Ab n lo B errv);
        [ exact HP | exact HIN | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity ]. }
    cbv beta. intros [] s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
    exact (KONT s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MI' ST' ERR' AUX' HPR' EFA' ESO' HP').
  Qed.

  Lemma izfree_last : forall (POST : unit -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (p : bptr) (Ab n lo B : Z) (errv : word),
    RHEAP s LBc m -> In (p, Ab, n) LBc ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz Ab ->
    (forall (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv] -> rauxv_ok m' B ->
       rheap_pres (lb_remove p LBc) (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       RHEAP s' (lb_remove p LBc) m' ->
       evt psegs (POST tt s')
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (lib_free lops (Some p)) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP HIN AUX SPB STK CEIL LOSP ERRC MI TP -> KONT.
    cbn [lops Target.ops lib_free].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCFREE. zstep. zstep. apply evt_done.
    lazymatch goal with |- ITree.impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_post_evt''.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc p Ab n lo B errv);
        [ exact HP | exact HIN | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity ]. }
    intros [] s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
    exact (KONT s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MI' ST' ERR' AUX' HPR' EFA' ESO' HP').
  Qed.
End ZFREE.

Lemma iblocks_inv' : forall (w w' : option bptr) Aw Aw' (sp_ sp' : bptr) As As',
  Zlib_iface.iblocks w Aw sp_ As = iblk_list w' Aw' sp' As' -> w' = w /\ sp' = sp_ /\ As' = As /\ (w <> None -> Aw' = Aw).
Proof.
  intros w w' Aw Aw' sp_ sp' As As'. unfold Zlib_iface.iblocks, iblk_list, the_zapi. cbn [z_wsize z_isize zinst].
  destruct w as [wp|]; destruct w' as [wp'|]; cbn [app]; intros E; try discriminate E.
  - injection E as E1 E2 E3 E4. subst. repeat split; reflexivity.
  - injection E as E1 E2. subst. repeat split; try reflexivity. intros NE. exfalso. apply NE. reflexivity.
Qed.

Section IEND.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.

  Lemma iend_second : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
      (s st1 : PState) (LB : list block) (L : ilay) (sp_ : bptr) (lo B : Z) (errv1 canary : word)
      (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word)
      (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    lx_env m1 st1 [(sp_, il_As L, 7176)] LB (wz (bv_unsigned sp + -16)) tp B lo errv1 canary ->
    rw_cells psegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells psegs m1 (il_S L) (zs_pub ni ai ti no ao to p1 p2) ->
    rw_cells psegs m1 (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
    lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m1 -> ps_so st1 = ps_so s -> ps_fa st1 = ps_fa s ->
    strm_in_frame sp (il_S L) B -> lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> frm0 fc ->
    implM psegs (lib_free lops (Some sp_)) st1
      (inflateEnd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (il_S L) lo B canary m)
      (MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 (wz (il_As L)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m1 (seg_rom psegs)).
  Proof.
    intros until t6. intros ENV1 FR PUB ZQ PRES1 ESO1 EFA1 SIF LOSP FRM0.
    pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & B63 & ST1 & LOC1 & LOG1 & ERR1 & TP1 & MI1).
    destruct SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. unfold Z_INFLATEEND_STACK, RFREE_STACK in LOSP. unfold GLOBALS_TOP in LOG1.
    pose proof alloc_ceiling_range as CR.
    assert (E16 : bv_unsigned (wz (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    eapply (izfree_last FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 _ sp_ (il_As L) 7176 lo B errv1);
      [ exact HP1 | left; reflexivity | exact AUX1 | exact SPB1 | exact ST1 | exact LOC1 | rewrite E16; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
      | exact TP1 | reflexivity | ].
    intros st2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MI2 ST2 ERR2 AUX2 HPR2 EFA2 ESO2 HP2.
    cbn [app] in HPR2, HP2. rewrite (lb_remove_head sp_ _ _ _ (HND _ _ _ HP1)) in HPR2, HP2. rewrite E16 in HPR2, ST2.
    assert (ENV2 : lx_env m2 st2 [] LB (wz (bv_unsigned sp + -16)) tp B lo errv1 canary).
    { eapply (lx_env_heap m1 m2 st1 st2); [exact ENV1| rewrite E16; exact HPR2| exact HP2| exact MI2| rewrite E16; exact ST2| exact ERR2| exact AUX2]. }
    assert (AGC : forall A0 n, bv_unsigned sp + -16 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3 a Ha. apply HPR2; [lia|]. left. lia. }
    apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in PUB; [|apply AGC; unfold zs_pub; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in ZQ; [|apply AGC; unfold izs_priv_cells; cbn [cells_size csize Nat.add]; lia].
    replace (ret_pc (wz PC_IE_RET2)) with (wz PC_IE_RET2) by (symmetry; apply ret_pc_even; [unfold PC_IE_RET2; lia| reflexivity]).
    eapply evt_mono; [exact (iend_tail L msg adler dt p3 resv lo ra sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                                FR ST2 ltac:(lia) ltac:(lia) ZQ SF1 ltac:(lia) MI2)|].
    intros ms' (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & STK' & (j & ZQ')).
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= lo /\ 0 < blk_addr b).
    { intros b Hb. pose proof (HBR _ _ _ b HP2 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    unfold inflateEnd_post. exists v0, v1, v2, (wz 0), c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, F, fc, m'.
    split; [reflexivity|]. split; [|split].
    - unfold lx_post_env. split.
      { exists errv1. eapply (lx_env_munch [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m2 m' st2 [] LB (wz (bv_unsigned sp + -16)) sp tp B lo errv1 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
        - constructor; [|constructor; [|constructor]]; unfold rclient_write_ok; cbn [fst snd]; left; lia.
        - intros a Ha. cbn [outside]. repeat split; lia. }
      split; [exact FRM0|]. split; [|split; congruence].
      eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans.
      { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| auto]. }
      apply (lx_pres_of_munch LB (bv_unsigned sp) _ _ m2 m' MU' WM').
      intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia.
    - unfold wint, Z_OK. reflexivity.
    - apply (rw_cells_transport psegs [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m2 m') in PUB; [| exact MU'| exact WM'| unfold zs_pub; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
      assert (HJ : rw_cells psegs m' (il_S L) (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j])).
      { apply rw_cells_app. split; [exact PUB|]. unfold zs_pub. cbn [cells_size csize Nat.add]. exact ZQ'. }
      destruct (rw_cells_forget psegs m' _ _ HJ) as (j' & Hj'). exists j'. exact Hj'.
  Qed.

  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.

  Theorem inflateEnd_ok : inflateEnd_stmt R.
  Proof.
    unfold inflateEnd_stmt. intros until canary. intros ENV PUB ZR HEND SIF LOSP SP16 FRM0 ->.
    rewrite ER in ZR. destruct ZR as (s_a & L & w' & sp' & ES & EL & HW & [HZQ HIST] & HI & HA & HPq).
    destruct (iblocks_inv' _ _ _ _ _ _ _ _ EL) as (-> & -> & EAs & EAw). subst S.
    destruct HZQ as (dt & p3 & resv & ZQ). destruct HIST as [GA GT Gl Gw Gc Gwin ARRS LAY].
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & STK & LOC & LOG & ERR & TP & MI).
    pose proof SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. pose proof LOSP as LOSP'. unfold Z_INFLATEEND_STACK, RFREE_STACK in LOSP'. unfold GLOBALS_TOP in LOG.
    pose proof alloc_ceiling_range as CR.
    destruct HI as (_ & _ & HINV & _). destruct HINV as (_ & _ & HMF).
    pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.MF_mode_range _ _ _ _ HMF) as RM. unfold HEAD, MEM, SYNC in RM.
    assert (RB : forall b, In b (Zlib_iface.iblocks w Aw sp_ As ++ LB) -> 0 < blk_addr b /\ blk_addr b + blk_size b <= lo).
    { intros b Hb. pose proof (HBR _ _ _ b HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    assert (RAs : 0 < il_As L /\ il_As L + 7176 <= lo).
    { rewrite EAs. apply (RB (sp_, As, 7176)). apply in_or_app. left. unfold Zlib_iface.iblocks. apply in_or_app. right. left. reflexivity. }
    assert (RW : is_window_blk s_a <> None -> 0 < il_Aw L < 2 ^ 63).
    { intros NE. destruct w as [wp|]; [|exfalso; apply NE; apply HW; reflexivity].
      rewrite (EAw ltac:(discriminate)). pose proof (RB (wp, Aw, 32768) ltac:(apply in_or_app; left; left; reflexivity)) as Q. cbn [blk_addr blk_size fst snd] in Q. lia. }
    assert (E16 : bv_unsigned (wz (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    eapply implM_evt; [exact (iend_to_free L s_a (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv lo ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               STK ltac:(lia) ltac:(lia) ZQ GA SF1 ltac:(lia) (proj1 RAs) (proj2 RAs) ltac:(lia) RW MI)|].
    intros ms1 (t0' & t1' & t2' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & FR & STK1 & MU1 & WM1 & MI1).
    assert (ENV1 : lx_env m1 s (Zlib_iface.iblocks w Aw sp_ As) LB (wz (bv_unsigned sp + -16)) tp B lo errv canary).
    { eapply (lx_env_munch [(lo, bv_unsigned sp)] m m1 s _ LB sp (wz (bv_unsigned sp + -16)) tp B lo errv canary HFRAME ENV MU1 WM1 MI1);
        [rewrite E16; exact STK1| rewrite E16; lia| |].
      - constructor; [|constructor]. unfold rclient_write_ok; cbn [fst snd]; left; lia.
      - intros a Ha. cbn [outside]. repeat split; lia. }
    apply (rw_cells_transport psegs [(lo, bv_unsigned sp)] m m1) in PUB; [| exact MU1| exact WM1| unfold zs_pub; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
    apply (rw_cells_transport psegs [(lo, bv_unsigned sp)] m m1) in ZQ; [| exact MU1| exact WM1| unfold izs_priv_cells; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m1).
    { apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp)] m m1 MU1 WM1).
      intros a (NX & HC). cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (RB b ltac:(apply in_or_app; right; exact Hb))|]; repeat split; lia. }
    destruct w as [wp|].
    -
      destruct (is_window_blk s_a) as [wb|] eqn:EW; [|exfalso; pose proof (proj2 HW eq_refl) as Q; discriminate Q].
      rewrite (EAw ltac:(discriminate)) in *.
      pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & ST1 & LOC1 & _ & ERR1 & TP1 & _).
      eapply (izfree FREE (fun _ => lib_free lops (Some sp_)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s _ wp Aw 32768 lo B errv);
        [ exact HP1 | left; reflexivity | exact AUX1 | exact SPB1 | exact ST1 | exact LOC1 | rewrite E16; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
        | exact TP1 | reflexivity | ].
      intros st2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MI2 ST2 ERR2 AUX2 HPR2 EFA2 ESO2 HP2.
      unfold Zlib_iface.iblocks, the_zapi in HPR2, HP2, HP1. cbn [z_wsize z_isize zinst app] in HPR2, HP2, HP1.
      rewrite (lb_remove_head wp _ _ _ (HND _ _ _ HP1)) in HPR2, HP2. rewrite E16 in HPR2, ST2.
      assert (ENV2 : lx_env m2 st2 [(sp_, il_As L, 7176)] LB (wz (bv_unsigned sp + -16)) tp B lo errv canary).
      { eapply (lx_env_heap m1 m2 s st2); [exact ENV1| rewrite E16; eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; right; exact Hb]| rewrite EAs; exact HP2| exact MI2
          | rewrite E16; exact ST2| exact ERR2| exact AUX2]. }
      assert (AGC : forall A0 n, bv_unsigned sp + -16 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
      { intros A0 n H1 H2 H3 a Ha. apply HPR2; [lia|]. left. lia. }
      apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
      apply (Z_dview.rw_cells_agree m1 m2) in PUB; [|apply AGC; unfold zs_pub; cbn [cells_size csize Nat.add]; lia].
      apply (Z_dview.rw_cells_agree m1 m2) in ZQ; [|apply AGC; unfold izs_priv_cells; cbn [cells_size csize Nat.add]; lia].
      assert (PRES2 : lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; right; exact Hb]. }
      replace (ret_pc (wz PC_IE_RET1)) with (wz PC_IE_RET1) by (symmetry; apply ret_pc_even; [unfold PC_IE_RET1; lia| reflexivity]).
      eapply implM_evt; [exact (iend_to_free2 L (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv lo ra sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                                 FR ST2 ltac:(lia) ltac:(lia) ZQ SF1 ltac:(lia) MI2)|].
      intros ms3 (v0 & v1 & v2 & c0 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->).
      exact (iend_second ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m2 s st2 LB L sp_ lo B errv canary ni ai ti no ao to p1 p2
               (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv v0 v1 v2 c0 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6
               ENV2 FR PUB ZQ PRES2 ESO2 EFA2 SIF LOSP FRM0).
    -
      destruct (is_window_blk s_a) as [wb|] eqn:EW; [exfalso; pose proof (proj1 HW eq_refl) as Q; discriminate Q|].
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      rewrite <- EAs in ENV1.
      exact (iend_second ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s s LB L sp_ lo B errv canary ni ai ti no ao to p1 p2
               (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
               ENV1 FR PUB ZQ PRES1 eq_refl eq_refl SIF LOSP FRM0).
  Qed.
End IEND.
End WithCeiling0.
End Z_iend.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition PC_II_RET : Z := 0x1cdd4.

Definition ii_at_malloc (S lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jstate : word) (jrest : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (wz S) (wz 7176) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x20790) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells psegs m' S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 jstate; C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 24 jrest])
    /\ munch [(lo, bv_unsigned sp); (S, S + 112)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma iinit_to_malloc : forall (S lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x5b000 <= lo ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  bv_unsigned sp <= S -> S + 112 < 2^63 ->
  mem_inv psegs m ->
  evt psegs (ii_at_malloc S lo ni ai ti no ao to p1 p2 jstate jrest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz A_ZVERSION) (wz ZS_SIZEOF) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATEINIT_) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZS SPS S63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS.
  unfold Z_INFLATEINIT_, A_ZVERSION, ZS_SIZEOF. carve_frame 32%nat STK.
  do 2 zs. br_false. do 2 zs. br_false. do 3 zs. br_false. zs. br_false.
  do 3 zs. br_true. (* 1.4: the frame is carved after the zalloc / zfree checks *)
  do 6 zs. br_false. do 4 zs.
  do 5 zs.
  do 6 zs.
  do 4 zs.
  apply evt_done. unfold ii_at_malloc. do 15 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact STK|]. split; [unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|].
  split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma iinit_null : forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 x9 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 64 -> 0x5b000 <= lo -> bv_unsigned sp < 2^63 ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-4)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom psegs)
               /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp))
    (MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_II_RET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 SP63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold PC_II_RET. zs. br_true. do 2 zs. do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  do 2 zs.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact STK].
Qed.

(* 1.4: after the zalloc, inflateInit_ zeroes the state past its first 8 bytes (memset(state + 8, 0, 7168)), stores
   strm, mode = HEAD, strm->state and the packed words wrap | reqwrap = 5 | 5 and reqbits | wbits = 15 | 15, and calls
   inflateReset. hz_tail = the head's bytes 8..168 right after the memset, one cell per access width of those stores
   and of inflateReset. *)
Definition hz_tail : list cell :=
  [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].

Definition ii_block_post14 (S A lo : Z) (ni ai no ao : Z) (p1 p2 jrest : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (S, S + 112); (A, A + 7176)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2 ++ [C8 (wz 0); C8 (wz A); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
                                                           C4 (wz 0); CB 4 (firstn 4 (skipn 4 jrest)); C8 (wz 1);
                                                           CB 8 (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest))))])
    /\ rw_cells psegs m' A (ireset14_post S A)
    /\ rw_cells psegs m' (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)]
    /\ rw_cells psegs m' (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]
    /\ rw_cells psegs m' (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))]
    /\ rw_cells psegs m' (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))].

Lemma iinit_block14 : forall (S A lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jstate : word) (jrest junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 128 -> 0x5b000 <= lo ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 jstate; C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 24 jrest]) ->
  rw_cells psegs m A [CB (Z.to_nat 7176) junk] ->
  bv_unsigned sp <= S -> S + 112 < 2^63 -> 0 < A -> A + 7176 <= lo ->
  mem_inv psegs m ->
  evt psegs (ii_block_post14 S A lo ni ai no ao p1 p2 jrest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (wz S) (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_II_RET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZS WJ SPS S63 A0 A1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112); (A, A + 7176)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  (* [the strm's last 24 bytes: data_type (inflateReset stores it), its pad, adler, reserved] *)
  apply (rw_cells_split_CB psegs m S [C8 (wz ni); C4 (wz ai); CB 4 p1; C8 (wz ti); C8 (wz no); C4 (wz ao); CB 4 p2; C8 (wz to); C8 (wz 0); C8 jstate; C8 (wz 106364); C8 (wz 106380); C8 (wz 0)]
           24 jrest [] [4; 4; 8; 8]%nat) in ZS; [|reflexivity]. cbn [app mk_CB_cells] in ZS.
  (* [the fresh block: its first 8 bytes (strm goes there) and the 7168 the memset clears] *)
  assert (LJ : length junk = Z.to_nat 7176) by exact (proj1 (proj1 (proj1 WJ))).
  assert (WJ' : rw_cells psegs m A [CB (length junk) junk]) by (rewrite LJ; exact WJ).
  pose proof (cb_subZ m A junk 8 7168 WJ' ltac:(lia) ltac:(lia) ltac:(rewrite LJ; lia)) as C8r.
  pose proof (cb_subZ m A junk 0 8 WJ' ltac:(lia) ltac:(lia) ltac:(rewrite LJ; lia)) as C8l. rewrite Z.add_0_r in C8l. change (Z.to_nat 8) with 8%nat in C8l.
  clear WJ WJ'.
  assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  unfold PC_II_RET. zs. br_false.
  do 6 zs.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset.memset_callZ with (D := A + 8) (C := 0) (N := 7168); [exact C8r| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
  change (0 mod 256) with 0 in POST.
  lazymatch type of POST with rw_cells _ ?mm _ _ => rename mm into mz end.
  (* [the cleared bytes: head 8..168, lens, work, codes, tail] *)
  assert (POST' : rw_cells psegs mz (A + 8) [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 7168))) (repeat (Z_to_bv 8 0) (Z.to_nat 7168))])
    by (rewrite repeat_length; exact POST).
  pose proof (cb_subZ mz (A + 8) _ 0 160 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as HZ.
  pose proof (cb_subZ mz (A + 8) _ 160 640 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZL0.
  pose proof (cb_subZ mz (A + 8) _ 800 576 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZW0.
  pose proof (cb_subZ mz (A + 8) _ 1376 5776 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZC0.
  pose proof (cb_subZ mz (A + 8) _ 7152 16 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZT.
  clear POST POST'.
  rewrite Z.add_0_r in HZ.
  replace (A + 8 + 160) with (A + 168) in ZL0 by lia. replace (A + 8 + 800) with (A + 808) in ZW0 by lia.
  replace (A + 8 + 1376) with (A + 1384) in ZC0 by lia. replace (A + 8 + 7152) with (A + 7160) in ZT by lia.
  assert (HZ8 : rw_cells psegs mz (A + 8) hz_tail).
  { eapply rw_cells_recast; [exact HZ| unfold hz_tail; cbn [cells_wf cell_wf]; repeat split| vm_compute; reflexivity]. }
  assert (ZL : rw_cells psegs mz (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]).
  { eapply rw_cells_recast; [exact ZL0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (ZW : rw_cells psegs mz (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))]).
  { eapply rw_cells_recast; [exact ZW0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (ZC : rw_cells psegs mz (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))]).
  { eapply rw_cells_recast; [exact ZC0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (GT : rw_cells psegs mz (A + 7160) [C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { eapply rw_cells_recast; [exact ZT| cbn [cells_wf cell_wf]; repeat split| vm_compute; reflexivity]. }
  clear HZ ZL0 ZW0 ZC0 ZT.
  unfold hz_tail in HZ8.
  (* [inflateInit_'s stores: strm, mode, strm->state, the zalloc check, wrap | reqwrap, reqbits | wbits; then
      mv a0,a1 and the jal to inflateReset] *)
  do 7 zs. zs. br_false.
  do 8 zs.
  (* [the head as inflateReset reads it] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (GA : rw_cells psegs mm A (ireset14_pre S)) end.
  { unfold ireset14_pre.
    change [C8 (wz S); C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
            C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)]
      with ([C8 (wz S)] ++ [C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
            C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)]).
    apply rw_cells_app. split; [exact C8l|]. cbn [cells_size csize]. replace (A + Z.of_nat (8 + 0)) with (A + 8) by lia.
    eapply rw_cells_recast; [exact HZ8| cbn [cells_wf cell_wf]; repeat split|
      vm_compute; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity]. }
  clear C8l HZ8.
  do 2 zs.
  eapply evt_cut.
  { eapply (ireset14_spec S A lo ni ai ti no ao to p1 p2 (firstn 4 jrest) (firstn 4 (skipn 4 jrest))
              (firstn 8 (skipn 4 (skipn 4 jrest))) (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest)))));
      [rewrite E32; exact STK| rewrite E32; lia| exact LO2| unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS| exact GA| exact GT
      | rewrite E32; lia| exact S63| exact A0| exact A1| eassumption]. }
  intros ms' PO. unfold ireset14_post_st in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & ZS' & GA' & GT').
  rewrite E32 in *. clear ZS GA GT STK.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m' MUc WMc end. clear MUc WMc.
  replace (ret_pc (wz 118328)) with (wz 118328) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zs. br_true. zs. do 5 zs.
  release_frame FR STK' (bv_unsigned sp).
  do 2 zs.
  apply evt_done. unfold ii_block_post14. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK'|].
  split; [exact ZS'|]. split; [exact GA'|]. split; [exact GT'|]. split; [exact ZL|]. split; [exact ZW| exact ZC].
Qed.


Lemma le8_mode_last : le8 (wz 16180) = le4 (wz 16180) ++ le4 (wz 0).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_hd_flags : le8 (wz (-4294967296)) = le4 (wz 0) ++ le4 (wz (-1)).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_00 : le8 (wz 0) = le4 (wz 0) ++ le4 (wz 0).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_sane_back : le8 (wz 18446744069414584321) = le4 (wz 1) ++ le4 (wz (-1)).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.

(* zl14infl-r2: Z_ikit's ired does not know the two new fields reqwrap / reqbits; s_pre sets them *)
Ltac ired14 := cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk is_reqwrap is_reqbits ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler icset_data_type icset_msg irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret wset_s wset_c wset_r].
Ltac iinit_red :=
  unfold iinit_of, ireset_s, s_pre, is_of_oracle, lay_ref;
  cbn [lay_mode lay_last lay_wrap lay_havedict lay_flags lay_dmax lay_check lay_total lay_head lay_wbits lay_wsize lay_whave lay_wnext lay_window lay_hold lay_bits
       lay_length lay_offset lay_extra lay_lencode lay_distcode lay_lenbits lay_distbits lay_ncode lay_nlen lay_ndist lay_have lay_next lay_lens lay_work lay_codes
       lay_sane lay_back lay_was il_S il_As il_Aw il_NI il_NO win_addr cp_addr];
  ired14; change (ir2_wrap MAX_WBITS) with 5; change (ir2_wb MAX_WBITS) with 15.

(* [1.4: the oracle reads zeros past byte 8 (the memset), whatever 1.3.1 offset the model reads them at] *)
Section Zeros.
Variable junk : list byte.
Hypothesis HZ : forall k, 8 <= Z.of_nat k < 7176 -> nth k junk (Z_to_bv 8 0) = Z_to_bv 8 0.

Lemma orc_zero : forall k, 8 <= k < 7176 -> orc junk k = 0.
Proof. intros k Hk. unfold orc. rewrite HZ by lia. reflexivity. Qed.
Lemma izero16 : forall b i, 8 <= b + 2 * i -> b + 2 * i + 2 <= 7176 -> init_u16 (orc junk) b i = 0.
Proof.
  intros b i H1 H2. rewrite (init_u16_ole (orc junk) (orc_range junk)). apply ole_zero.
  intros k Hk. apply orc_zero. cbn in Hk. lia.
Qed.
Lemma izero32 : forall b i, 8 <= b + 4 * i -> b + 4 * i + 4 <= 7176 -> init_u32 (orc junk) b i = 0.
Proof.
  intros b i H1 H2. rewrite (init_u32_ole (orc junk) (orc_range junk)). apply ole_zero.
  intros k Hk. apply orc_zero. cbn in Hk. lia.
Qed.
Lemma izero64 : forall b i, 8 <= b + 8 * i -> b + 8 * i + 8 <= 7176 -> init_u64 (orc junk) b i = 0.
Proof.
  intros b i H1 H2. rewrite (init_u64_ole (orc junk) (orc_range junk)). apply ole_zero.
  intros k Hk. apply orc_zero. cbn in Hk. lia.
Qed.
End Zeros.

Local Transparent zseq.
Lemma u32s_zero_seq : forall (f : Z -> Z) n s, (forall i, Z.of_nat s <= i < Z.of_nat (s + n) -> f i = 0) ->
  u32s (map (fun i => wz (f i)) (map Z.of_nat (seq s n))) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  intros f n. induction n as [|n IH]; intros s Hf; [reflexivity|].
  cbn [seq map u32s]. rewrite Hf by lia. rewrite (IH (S s)) by (intros i Hi; apply Hf; lia).
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.
Lemma av32_zero : forall (a : arr) n, 0 <= n -> (forall i, 0 <= i < n -> arr_get a i = 0) ->
  u32s (av32 a n) = repeat (Z_to_bv 8 0) (Z.to_nat (4 * n)).
Proof.
  intros a n Hn Hf. unfold av32, zseq. rewrite (u32s_zero_seq (arr_get a) (Z.to_nat n) 0) by (intros i Hi; apply Hf; lia).
  f_equal. lia.
Qed.

Lemma iinit_IST14 : forall m S A NI NO (junk : list byte),
  (forall k, 8 <= Z.of_nat k < 7176 -> nth k junk (Z_to_bv 8 0) = Z_to_bv 8 0) ->
  rw_cells psegs m A (ireset14_post S A) ->
  rw_cells psegs m (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)] ->
  rw_cells psegs m (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))] ->
  rw_cells psegs m (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))] ->
  rw_cells psegs m (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))] ->
  blk_ok A 7176 ->
  IST m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros m S A NI NO junk HZ GA GT ZL ZW ZC BOK.
  unfold ireset14_post in GA.
  apply (cells_split8_0 m A [C8 (wz S); C8 (wz 16180); C4 (wz 5); C4 (wz 5); C8 (wz (-4294967296)); C4 (wz 32768); C4 (wz 0);
                            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15)]) in GA. cbn [app] in GA.
  constructor.
  - unfold isA. eapply rw_cells_recast; [exact GA| |].
    + unfold isA_cells. cbn [cells_wf cell_wf]. repeat split.
    + unfold isA_cells. iinit_red. cbn [win_addr cp_addr il_As il_Aw].
      rewrite ?(izero32 junk HZ), ?(izero64 junk HZ) by lia.
      cbn [cells_bytes cbytes]. unfold HEAD. rewrite le8_mode_last, le8_hd_flags.
      rewrite <- !app_assoc. rewrite !Z.mul_0_r, !Z.add_0_r. reflexivity.
  - exists (le4 (wz 0)). eapply rw_cells_recast; [exact GT| |].
    + unfold isT_cells. cbn [cells_wf cell_wf]. repeat split; try apply length_le4.
    + unfold isT_cells. iinit_red. rewrite ?(izero32 junk HZ) by lia. cbn [cells_bytes cbytes]. rewrite le8_sane_back.
      rewrite <- !app_assoc. reflexivity.
  - unfold ilens, u16arr. iinit_red. apply u8arr_of_rw_cells in ZL.
    rewrite (av16_zero _ 320) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init; first [reflexivity | apply (izero16 junk HZ); lia]).
    exact ZL.
  - unfold iwork, u16arr. iinit_red. apply u8arr_of_rw_cells in ZW.
    rewrite (av16_zero _ 288) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init; first [reflexivity | apply (izero16 junk HZ); lia]).
    exact ZW.
  - unfold icodes, u32arr. iinit_red. apply u8arr_of_rw_cells in ZC. destruct ZC as [ZB ZW']. split.
    + rewrite (av32_zero _ 1444) by (try lia; intros i Hi; unfold iarr_u32_of; rewrite arr_get_init; first [reflexivity | apply (izero32 junk HZ); lia]).
      exact ZB.
    + replace (4 * Z.of_nat (length (av32 (iarr_u32_of (orc junk) 1368 1444) 1444)))
        with (Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 5776)))) by (rewrite av32_length, repeat_length; lia).
      exact ZW'.
  - unfold iwin. iinit_red. exact I.
  - unfold iarrs. iinit_red. unfold iarr_u16_of, iarr_u32_of. rewrite !arr_len_init. repeat split; try reflexivity. intros NE. exfalso. apply NE. reflexivity.
  - unfold ilay_ok. iinit_red. split; [exact BOK|]. intros NE. exfalso. apply NE. reflexivity.
Qed.

Lemma zi_init_z : zs_msg (iz_z zi_init) = MSG_NULL /\ zs_adler (iz_z zi_init) = 1 /\ zs_total_in (iz_z zi_init) = 0 /\ zs_total_out (iz_z zi_init) = 0.
Proof.
  unfold zi_init, iz0, iinit0. cbn [iz_z]. rewrite iinit_run_of. cbn [zr_strm zret0]. unfold ireset_z, z_pre.
  change (is_wrap (s_pre HarnessSmall.g0 5%N MAX_WBITS)) with 5. cbn. repeat split; reflexivity.
Qed.

Section INIT.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.

  Theorem inflateInit_ok : inflateInit_stmt R.
  Proof.
    unfold inflateInit_stmt. intros until canary. intros ENV ZS SIF LOSP SP16 FRM0 -> -> ->.
    change (lib_malloc lops (z_isize the_zapi)) with (raw_malloc 7176).
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & STK & LOC & LOG & ERR & TP & MI).
    destruct SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. unfold Z_INFLATEINIT_STACK, RMALLOC_STACK in LOSP. unfold GLOBALS_TOP in LOG.
    pose proof alloc_ceiling_range as CR.
    eapply implM_evt; [exact (iinit_to_malloc S lo ni ai ti no ao to p1 p2 jmsg jstate jrest ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               STK ltac:(lia) ltac:(lia) ZS SF1 ltac:(lia) MI)|].
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & FR & STK1 & ZS1 & MU1 & WM1 & MI1).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (wz (bv_unsigned sp + -32)) tp B lo errv canary).
    { eapply (lx_env_munch [(lo, bv_unsigned sp); (S, S + 112)] m m1 s [] LB sp (wz (bv_unsigned sp + -32)) tp B lo errv canary HFRAME ENV MU1 WM1 MI1);
        [rewrite E32; exact STK1| rewrite E32; lia| |].
      - constructor; [|constructor; [|constructor]]; unfold rclient_write_ok; cbn [fst snd]; left; lia.
      - intros a Ha. cbn [outside]. repeat split; lia. }
    pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & ST1 & LOC1 & _ & ERR1 & TP1 & _).
    eapply implM_post_evt''.
    { eapply (MALLOC (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' _ _ (wz 7176) a1' a2' a3' a4' a5' a6' a7' _ _ _ _ _ _ _ _ _ _ t3' t4' t5' t6' F fc m1 s LB 7176 lo B errv);
        [exact HP1| exact AUX1| exact SPB1| exact ST1| exact LOC1| rewrite E32; unfold RMALLOC_STACK; lia| exact ERR1| exact MI1| exact TP1| reflexivity| lia]. }
    intros r st' ms2 PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & errv2 & -> & MI2 & STK2 & ERR2 & AUX2 & HPR & EFA & ESO & HR).
    rewrite E32 in STK2, HPR.
    replace (ret_pc (wz PC_II_RET)) with (wz PC_II_RET) by (symmetry; apply ret_pc_even; [unfold PC_II_RET; lia| reflexivity]).
    assert (HPRc : rheap_pres LB (bv_unsigned (wz (bv_unsigned sp + -32))) m1 m2) by (rewrite E32; exact HPR).
    assert (AGC : forall A0 n, bv_unsigned sp + -32 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3 a Ha. apply HPR; [lia|]. left. lia. }
    apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in ZS1; [|apply AGC; unfold zs_pub; cbn [app cells_size csize Nat.add]; lia].
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= lo /\ 0 < blk_addr b).
    { intros b Hb. pose proof (HBR _ _ _ b HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF)] m m1).
    { apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp); (S, S + 112)] m m1 MU1 WM1).
      intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia. }
    assert (PRES2 : lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF)] m1 m2).
    { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR| lia| auto]. }
    destruct r as [p|].
    -
      destruct HR as (A & junk & -> & RBR & HP2 & WJ & _).
      destruct RBR as (RB1 & RB2 & RB3 & RB4 & RB5).
      assert (BOK : blk_ok A 7176) by (unfold blk_ok; repeat split; try assumption; lia).
      assert (A1 : A + 7176 <= lo) by lia.
      assert (SEPB : forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + 7176 <= blk_addr b).
      { intros b Hb. pose proof (heap_sep st' [(p, A, 7176)] LB m2 (p, A, 7176) b HND HBD HP2 (or_introl eq_refl) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
      assert (ENV2 : lx_env m2 st' [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 s st' [] [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E32; exact STK2| exact ERR2| exact AUX2]. }
      assert (LJ' : length junk = Z.to_nat 7176) by exact (proj1 (proj1 (proj1 WJ))).
      (* 1.4: inflateInit_ zeroes the state past byte 8 and calls inflateReset (iinit_block14); the model state is read
         from jkz = the block's first 8 junk bytes followed by zeros *)
      eapply evt_mono; [exact (iinit_block14 S A lo ni ai ti no ao to p1 p2 jstate jrest junk ra sp gp tp t0'' t1'' t2'' s0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                  t3'' t4'' t5'' t6'' s1 F fc m2 FR STK2 ltac:(lia) ltac:(lia) ZS1 WJ SF1 ltac:(lia) RB1 A1 MI2)|].
      clear WJ.
      intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & STK' & ZS' & GA' & GT' & ZL & ZW & ZC).
      remember (sub junk (Z.to_nat 0) (Z.to_nat 8) ++ repeat (Z_to_bv 8 0) (Z.to_nat 7168)) as jkz eqn:Ejkz.
      assert (HZz : forall k, 8 <= Z.of_nat k < 7176 -> nth k jkz (Z_to_bv 8 0) = Z_to_bv 8 0).
      { intros k Hk. subst jkz. rewrite app_nth2.
        - apply nth_repeat.
        - rewrite sub_length; [lia| rewrite LJ'; lia]. }
      pose proof (iinit_IST14 m' S A 0 0 jkz HZz GA' GT' ZL ZW ZC BOK) as HIST.
      apply rw_cells_app in ZS'. destruct ZS' as [ZPUB ZPRIV]. unfold zs_pub in ZPRIV. cbn [cells_size csize Nat.add] in ZPRIV.
      unfold inflateInit_post. exists u0, u1, u2, (wz 0), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m'.
      split; [reflexivity|]. exists A. change (Zlib_iface.iblocks None 0 p A) with [(p, A, 7176)].
      split; [|split; [|split]].
      + unfold lx_post_env. split.
        { exists errv2. eapply (lx_env_munch _ m2 m' st' [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) sp tp B lo errv2 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
          - constructor; [|constructor; [|constructor; [|constructor]]]; unfold rclient_write_ok; cbn [fst snd].
            + left; lia.
            + left; lia.
            + right; right. exists (p, A, 7176). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
          - intros a Ha. cbn [outside]. repeat split; lia. }
        split; [exact FRM0|]. split; [|split; assumption].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [exact PRES2|].
        apply (lx_pres_of_munch LB (bv_unsigned sp) _ _ m2 m' MU' WM').
        intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
        destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb); pose proof (SEPB _ Hb)|]; repeat split; lia.
      + unfold wint, Z_OK. reflexivity.
      + exact ZPUB.
      + rewrite ER. destruct zi_init_z as (EMSG & EADL & _ & _).
        exists (iinit_of (orc jkz)), (Z_irep.mkIL S A 0 0 0), None, p. cbn [il_S il_As il_Aw].
        split; [reflexivity|]. split; [reflexivity|]. split; [split; intros _; reflexivity|].
        split; [split; [|exact HIST]|].
        { (* [1.4: inflateReset stores data_type = 0; its pad and reserved stay the strm's junk] *)
          pose proof (proj1 (proj1 ZPRIV)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & _ & _ & _ & _ & _ & L1 & _ & L2 & _).
          destruct (le8_of_bytes (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest))))) as (zrs & _ & Ers); [exact L2|].
          exists (wz 0), (firstn 4 (skipn 4 jrest)), (wz zrs). cbn [il_S].
          eapply rw_cells_recast; [exact ZPRIV| |].
          - unfold izs_priv_cells. cbn [cells_wf cell_wf]. repeat split. exact L1.
          - unfold izs_priv_cells. cbn [cells_bytes cbytes il_As]. rewrite EMSG, EADL. change (imsg_ptr MSG_NULL) with 0.
            rewrite Ers. reflexivity. }
        change (i_init the_zapi) with zi_init.
        split; [apply IREL_init|]. split.
        { unfold ATY. iinit_red. split; [apply ty16_init|]. split; [apply ty16_init| apply ty32_init]. }
        unfold PATIq. iinit_red. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [right; split; [reflexivity| left; reflexivity]|]. split; [unfold HEAD, FLAGS, HCRC; lia|]. split; [left; reflexivity|]. split; [left; reflexivity|].
        intros i Hi. unfold arr_make in Hi. rewrite arr_len_init in Hi. lia.
    -
      destruct HR as (-> & HP2).
      assert (ENV2 : lx_env m2 st' [] LB (wz (bv_unsigned sp + -32)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 s st' [] [] LB (wz (bv_unsigned sp + -32)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E32; exact STK2| exact ERR2| exact AUX2]. }
      eapply evt_mono; [exact (iinit_null lo ra sp gp tp t0'' t1'' t2'' s0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'' s1 (wz S) F fc m2
                                  FR STK2 ltac:(lia) ltac:(lia) ltac:(lia) MI2)|].
      intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & STK').
      unfold inflateInit_post. exists u0, u1, u2, (wz (-4)), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m'.
      split; [reflexivity|]. split; [|split].
      + unfold lx_post_env. split.
        { exists errv2. eapply (lx_env_munch [(lo, bv_unsigned sp)] m2 m' st' [] LB (wz (bv_unsigned sp + -32)) sp tp B lo errv2 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
          - constructor; [|constructor]. unfold rclient_write_ok; cbn [fst snd]; left; lia.
          - intros a Ha. cbn [outside]. repeat split; lia. }
        split; [exact FRM0|]. split; [|split; assumption].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [exact PRES2|].
        apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp)] m2 m' MU' WM').
        intros a (NX & HC). cbn [outside].
        destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia.
      + unfold wint, Z_MEM_ERROR. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia. reflexivity.
      + apply (rw_cells_transport psegs [(lo, bv_unsigned sp)] m2 m') in ZS1; [| exact MU'| exact WM'| unfold zs_pub; cbn [app cells_size csize Nat.add disjoint_from]; split; [lia| exact I]].
        destruct (rw_cells_forget psegs m' _ _ ZS1) as (j & Hj). exists j. exact Hj.
  Qed.
End INIT.
End WithCeiling0.
