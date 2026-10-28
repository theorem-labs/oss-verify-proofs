(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Printf_wfile.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation ctusegs := ImageCt.ctusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Class LibSpec {LM : LibModel} : Type := {
  lib_pristine : mem -> Prop;
  lib_inv : LS -> mem -> list block -> Prop;
  LIBW : list (Z * Z);
  LIB_STACK : Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LX_INIT : Z := 0xe24d8.            (* [comment removed for export] *)
Definition LX_FUZZ : Z := 0xe24dc.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LX_GOT_STDERR : Z := 0x31e788.   (* [comment removed for export] *)
Definition LX_STDERR_PTR : Z := 0x31e730.   (* [comment removed for export] *)
Definition LX_STDERR_FILE : Z := 0x320370.  (* [comment removed for export] *)
Definition LX_EMPTY : Z := 0x3306c0.        (* [comment removed for export] *)
Definition LX_AEF_ARGC : Z := 0x31fd78.     (* [comment removed for export] *)
Definition LX_AEF_ARGV : Z := 0x31fd80.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition OSSL_BASE_INITED : Z := 0x3306e0.          (* [comment removed for export] *)
Definition OSSL_DO_GLOBAL_CLEANUP : Z := 0x3306e4.    (* [comment removed for export] *)

Section WithLib. Context {LM : LibModel} {LSP : LibSpec}.
(* [comment removed for export] *)
Definition LX_FUZZ_STACK : Z := LIB_STACK.

(* [comment removed for export] *)
Definition ossl_exit_cells (m : mem) : Prop :=
  exists b0 : byte, rw_cells ctusegs m OSSL_BASE_INITED [C1 b0] /\ rw_cells ctusegs m OSSL_DO_GLOBAL_CLEANUP [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_statics (m : mem) : Prop :=
  rw_cells ctusegs m LX_GOT_STDERR [C8 (wz LX_STDERR_PTR)]
  /\ rw_cells ctusegs m LX_STDERR_PTR [C8 (wz LX_STDERR_FILE)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition lx_client (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  ~ rin_ivs X a /\ (SP <= a \/ in_block LB a \/ (0x2c2000 <= a < 0x355000 /\ ~ ralloc_static a)).

Definition lx_pres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> lx_client LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m' (wa a) <> None).

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
  bytes_at ctusegs m D (to_bytes d) /\ Forall (fun c => 0 <= c < 256) d
  /\ 0 < D /\ D + zlength d < 2^63 /\ zlength d < 2^30       (* [comment removed for export] *)
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_env (m : mem) (s : PState) (OW LB : list block) (sp tp : word) (B lo : Z) (errv canary : word) : Prop :=
  RHEAP s (OW ++ LB) m /\ lx_statics m /\ stderr_wfile m /\ ssp_cells m canary
  /\ rauxv_ok m B /\ bv_unsigned sp <= B /\ B < 2^63
  /\ stk ctusegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
  /\ rw_cells ctusegs m (errno_addr tp) [C4 errv] /\ tp = wz RATP
  /\ mem_inv ctusegs m.

(* [comment removed for export] *)
Definition lx_post_env (m m' : mem) (s s' : PState) (OW' LB : list block) (sp tp : word) (B lo : Z) (canary : word)
    (X : list (Z * Z)) (fc' : bv 32) : Prop :=
  (exists errv' : word, lx_env m' s' OW' LB sp tp B lo errv' canary)
  /\ frm0 fc'
  /\ lx_pres LB (bv_unsigned sp) X m m'
  /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rlib_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (lo B : Z) (canary : word) (m : mem) (ls' : LS) (s' : PState) (r0 : option word) (PM : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' OW',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ lx_post_env m m' s s' OW' LB sp tp B lo canary LIBW fc'
    /\ lib_inv ls' m' OW'
    /\ ossl_exit_cells m'
    /\ match r0 with Some v => a0 = v | None => True end
    /\ PM m'.

(* [comment removed for export] *)
Definition rinit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B : Z) (errv canary : word),
  RHEAP s LB m -> lx_statics m -> stderr_wfile m -> ssp_cells m canary ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv ctusegs m ->
  bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  lib_pristine m ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 (wz LX_AEF_ARGV)] ->
  a0 = wz LX_AEF_ARGC -> a1 = sp ->
  implM ctusegs lib_init_prog s
        (fun ls' s' => rlib_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B canary m ls' s' None (fun _ => True))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_INIT) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition rfuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : LS * Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => rlib_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B canary m (fst r) s' (Some (wz 0))
                       (fun m' => payload_ok m' LB D d) ms'
             /\ snd r = 0.

Definition rfuzz_one_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (ls : LS) (OW LB : list block) (D : Z) (d : list Z) (lo B : Z) (errv canary : word),
  RHEAP s (OW ++ LB) m -> lib_inv ls m OW -> lx_statics m -> stderr_wfile m -> ssp_cells m canary ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv ctusegs m ->
  bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d ->
  frm0 fc ->
  a0 = wz D -> a1 = wz (zlength d) ->
  implM ctusegs (lib_one_prog ls d) s
        (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_FUZZ) fc None m (seg_rom ctusegs)).
End WithLib.
End WithCeiling0.
