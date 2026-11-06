(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.punycode.lib.U Require Import Layout Exit Printf_wfile.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition lops : target_ops (M PState) bptr := Target.ops raw_malloc raw_free ps_so set_so_ps.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LX_FUZZ : Z := 0xe1a7c.            (* [comment removed for export] *)
Definition FZ_FUZZ : Z := 0xe1a88.            (* [comment removed for export] *)
Definition FZ_CRYPTO_MALLOC : Z := 0xe1b4c.
Definition FZ_CRYPTO_ZALLOC : Z := 0xe1c1c.
Definition FZ_CRYPTO_FREE : Z := 0xe1ef4.

(* [comment removed for export] *)
Definition LX_GOT_STDERR : Z := 0x31d888.   (* [comment removed for export] *)
Definition LX_STDERR_PTR : Z := 0x31d830.   (* [comment removed for export] *)
Definition LX_STDERR_FILE : Z := 0x31f468.  (* [comment removed for export] *)
Definition LX_GOT_FLAGS : Z := 0x31da30.    (* [comment removed for export] *)
Definition LX_STORAGE_FN : Z := 0x31ee88.   (* [comment removed for export] *)
Definition LX_FLAGS : Z := 0x32f7d0.        (* [comment removed for export] *)
Definition LX_EMPTY : Z := 0x32f7b0.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LX_DEBUG_STRICT : Z := LX_FLAGS.
Definition LX_MESSAGE_BUF : Z := LX_FLAGS.
Definition P11_MESSAGE_MAX_N : nat := 0.
Definition FZ_LATCH : Z := LX_FLAGS.

(* [comment removed for export] *)
Definition LX_PRINTF_STACK : Z := 8192.
Definition LX_MESSAGE_STACK : Z := 8192.
Definition LX_MSG_STACK : Z := 8192.
Definition LX_NEXT_STACK : Z := 8192.
Definition LX_FUZZ_STACK : Z := 32768.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_statics (m : mem) : Prop :=
  rw_cells usegs m LX_GOT_STDERR [C8 (wz LX_STDERR_PTR)]
  /\ rw_cells usegs m LX_STDERR_PTR [C8 (wz LX_STDERR_FILE)]
  /\ rw_cells usegs m LX_GOT_FLAGS [C8 (wz FZ_CRYPTO_MALLOC)]              (* [comment removed for export] *)
  /\ rw_cells usegs m LX_STORAGE_FN [C8 (wz FZ_CRYPTO_MALLOC)]             (* [comment removed for export] *)
  /\ rw_cells usegs m (LX_GOT_FLAGS + 16) [C8 (wz FZ_CRYPTO_FREE)]         (* [comment removed for export] *)
  /\ rw_cells usegs m (LX_STORAGE_FN + 16) [C8 (wz FZ_CRYPTO_FREE)].       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_flags (m : mem) (v : word) : Prop := exists b : byte, rw_cells usegs m LX_FLAGS [C1 b].
Definition lx_flags0 (m : mem) : Prop := lx_flags m (wz 0).

(* [comment removed for export] *)
Definition LXW_FLAGS : Z * Z := (LX_FLAGS, LX_FLAGS + 1).
Definition LXW_MSGBUF : Z * Z := (LX_MESSAGE_BUF, LX_MESSAGE_BUF).        (* [comment removed for export] *)
Definition LXW_STDERR : Z * Z := (LX_STDERR_FILE, LX_STDERR_FILE + 232).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition lx_client (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  ~ rin_ivs X a /\ (SP <= a \/ in_block LB a \/ (0x2c1000 <= a < 0x354000 /\ ~ ralloc_static a)).

Definition lx_pres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> lx_client LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma lx_pres_refl : forall LB SP X m, lx_pres LB SP X m m.
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma lx_pres_trans : forall LB SP X m1 m2 m3,
  lx_pres LB SP X m1 m2 -> lx_pres LB SP X m2 m3 -> lx_pres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

(* [comment removed for export] *)
Lemma lx_pres_weaken : forall LB LB' SP SP' X X' m m',
  lx_pres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
  lx_pres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha [Hx Hc]. apply H; [exact Ha|].
  split; [intros Hx'; apply Hx; apply HX; exact Hx'|].
  destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left| right; right; exact Hc].
  exists b. split; [apply HL; exact Hb|exact Hr].
Qed.

(* [comment removed for export] *)
Lemma lx_pres_of_heap_pres : forall LB SP X m m', rheap_pres LB SP m m' -> lx_pres LB SP X m m'.
Proof.
  intros LB SP X m m' H a Ha [_ Hc]. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; right; exact Hc| right; left; exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition payload_ok (m : mem) (LB : list block) (D : Z) (d : list Z) : Prop :=
  bytes_at usegs m D (to_bytes d) /\ Forall (fun c => 0 <= c < 256) d
  /\ 0 < D /\ D + zlength d < 2^63 /\ zlength d < 2^31       (* [comment removed for export] *)
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_env (m : mem) (s : PState) (OW LB : list block) (sp tp : word) (B lo : Z) (errv canary : word) : Prop :=
  RHEAP s (OW ++ LB) m /\ lx_statics m /\ lx_flags0 m /\ stderr_wfile m /\ ssp_cells m canary
  /\ rauxv_ok m B /\ bv_unsigned sp <= B /\ B < 2^63
  /\ stk usegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
  /\ rw_cells usegs m (errno_addr tp) [C4 errv] /\ tp = wz RATP
  /\ mem_inv usegs m.

(* [comment removed for export] *)
Definition lx_post_env (m m' : mem) (s s' : PState) (OW' LB : list block) (sp tp : word) (B lo : Z) (canary : word)
    (X : list (Z * Z)) (fc' : bv 32) : Prop :=
  (exists errv' : word, lx_env m' s' OW' LB sp tp B lo errv' canary)
  /\ frm0 fc'
  /\ lx_pres LB (bv_unsigned sp) X m m'
  /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rfuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [LXW_FLAGS; LXW_MSGBUF; LXW_STDERR] fc'
    /\ r = 0 /\ a0 = wz 0
    /\ payload_ok m' LB D d.

Definition rfuzz_one_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (D : Z) (d : list Z) (flags : word) (lo B : Z) (errv canary : word),
  RHEAP s LB m -> lx_statics m -> lx_flags m flags -> stderr_wfile m -> ssp_cells m canary ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv usegs m ->
  bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d ->
  frm0 fc ->
  a0 = wz D -> a1 = wz (zlength d) ->
  implM usegs (fuzz_one lops d) s
        (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_FUZZ) fc None m (seg_rom usegs)).
End WithCeiling0.
