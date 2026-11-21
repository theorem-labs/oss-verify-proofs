(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ITree Nodes MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Malloc Monad ZApi ZInst ZTarget Target Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Zlib_iface Zh_kit Z_kit Z_dview Z_drep Z_zrd Zg_dinit_modelG.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Local Notation MP := (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.Monad.M PState).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition dinit_progG : MP (option (bptr * bptr * bptr * bptr * bptr)) :=
  bind lops (lib_malloc lops 5968) (fun s =>
  match s with
  | None => ret lops None
  | Some sp =>
      bind lops (lib_malloc lops 65536) (fun w =>
      bind lops (lib_malloc lops 65536) (fun p =>
      bind lops (lib_malloc lops 65536) (fun h =>
      bind lops (lib_malloc lops 65536) (fun b =>
      match w, p, h, b with
      | Some wp, Some pp, Some hp, Some bp => ret lops (Some (sp, wp, pp, hp, bp))
      | _, _, _, _ =>
          bind lops (lib_free lops b) (fun _ => bind lops (lib_free lops h) (fun _ => bind lops (lib_free lops p) (fun _ =>
          bind lops (lib_free lops w) (fun _ => bind lops (lib_free lops (Some sp)) (fun _ => ret lops None)))))
      end))))
  end).

Section Small.
  Local Transparent the_zapi.

End Small.

Definition deflateInit_postG (lv : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S ni ai no ao : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : option (bptr * bptr * bptr * bptr * bptr)) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ match r with
       | Some b => exists (As Aw Ap Ah Ab : Z) (G : N -> Z -> Z),
           lx_post_env m m' s s' (blk5_blocks b As Aw Ap Ah Ab) LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_OK
           /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2)
           /\ DREPq m' (Z_drep.mkDL S As Aw Ap Ah Ab 0 0) (dinitG_of G lv) zsG
           /\ dlay_ceil (Z_drep.mkDL S As Aw Ap Ah Ab 0 0)
       | None =>
           lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_MEM_ERROR
           /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j])
       end.

Definition deflateInit_stmtG (lv : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
         (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wint lv -> a2 = wz A_ZVERSION -> a3 = wz ZS_SIZEOF ->
  implM psegs dinit_progG s
        (deflateInit_postG lv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEINIT_) fc None m (seg_rom psegs)).

End WithCeiling0.
