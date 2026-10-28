(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Pj_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition ser_need (d : nat) : Z := 256 + 29 * Z.of_nat d + PJ_GROW_STACK.

Definition cont_need (d : nat) : Z := 208 + ser_need d.

Definition PJ_SER_STACK : Z := 256 + 64 * 464 + PJ_GROW_STACK.
Lemma ser_need_root : ser_need 1024 = PJ_SER_STACK.
Proof. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition DOCREP (m : mem) (LB0 : list block) (DOC TAPE SBUF len : Z) (tws sbs : list Z) : Prop :=
  rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF)]
  /\ bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) /\ bytes_at usegs m SBUF (map (Z_to_bv 8) sbs)
  /\ tape_wfS (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any (Z.of_nat (length tws))
  /\ Forall (fun c => 0 <= c < 256) sbs
  /\ 8 * Z.of_nat (length tws) <= SJ_TAPE len /\ Z.of_nat (length sbs) <= SJ_SBUF len
  /\ (exists bt, In bt LB0 /\ blk_addr bt <= TAPE /\ TAPE + 8 * Z.of_nat (length tws) <= blk_addr bt + blk_size bt)
  /\ (exists bs, In bs LB0 /\ blk_addr bs <= SBUF /\ SBUF + Z.of_nat (length sbs) <= blk_addr bs + blk_size bs).

Definition sb_acc (st : sbst) (i c : Z) : Prop := sb_size st <= 41 * (i - 1) + 6 * c + 2.
Definition sb_acc1 (st : sbst) (i c : Z) : Prop := sb_size st <= 41 * (i - 1) + 6 * c + 3.

Lemma sb_acc_out : forall m LB0 DOC TAPE SBUF len tws sbs st i c,
  0 <= len <= SJ_PADMAX -> DOCREP m LB0 DOC TAPE SBUF len tws sbs -> 1 <= i <= Z.of_nat (length tws) -> 0 <= c <= Z.of_nat (length sbs) ->
  sb_acc st i c -> sb_size st <= PJ_OUTMAX len.
Proof.
  intros m LB0 DOC TAPE SBUF len tws sbs st i c HL (_ & _ & _ & _ & _ & HT & HS & _) Hi Hc HA.
  eapply (pj_out_bound len (Z.of_nat (length tws)) (Z.of_nat (length sbs)) i c); try eassumption.
Qed.

Definition ser_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB0 : list block) (lo B : Z) (SB len : Z) (j c' : Z) (m : mem)
    (ch : @chst bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' (errv' : word) (st' : sbst),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B /\ frm0 fc'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ ch = sb_ch st'
    /\ RHEAP s' (sbblocks st' ++ LB0) m'
    /\ SBINV m' SB len st'
    /\ sb_acc st' j c'
    /\ lx_pres LB0 q [(SB, SB + 88)] m m'.

Definition ser_stmt (d : nat) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (SB len : Z) (st : sbst) (DOC TAPE SBUF : Z) (tws sbs : list Z) (i j c c' : Z),
  RHEAP s (sbblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - ser_need d ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
  q <= SB -> SB + 88 <= B -> q <= DOC -> DOC + 16 <= B -> (SB + 88 <= DOC \/ DOC + 16 <= SB) ->
  0 <= len <= SJ_PADMAX -> SBINV m SB len st -> DOCREP m LB0 DOC TAPE SBUF len tws sbs ->
  DOC mod 8 = 0 -> TAPE mod 8 = 0 ->
  elemS (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any d i j c c' ->
  1 <= i -> j <= Z.of_nat (length tws) -> 0 <= c -> c' <= Z.of_nat (length sbs) ->
  sb_acc1 st i c ->
  implM usegs (pj_part raw_malloc raw_free ps_so set_so_ps (sb_fuel st) len (sb_cap st) (sb_blk st)) s
        (ser_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 lo B SB len j c' m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 DOC) (Z_to_bv 64 i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PJ_APPEND_ELEM) fc None m (seg_rom usegs)).

Definition cont_stmt (k : bool) (d : nat) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (SB len : Z) (st : sbst) (DOC TAPE SBUF : Z) (tws sbs : list Z) (i e n c c' : Z),
  RHEAP s (sbblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - cont_need d ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
  q <= SB -> SB + 88 <= B -> q <= DOC -> DOC + 16 <= B -> (SB + 88 <= DOC \/ DOC + 16 <= SB) ->
  0 <= len <= SJ_PADMAX -> SBINV m SB len st -> DOCREP m LB0 DOC TAPE SBUF len tws sbs ->
  DOC mod 8 = 0 -> TAPE mod 8 = 0 ->
  ty (Tf tws) i = (if k then t_obj else t_arr) -> tnext (Tf tws i) = e + 1 -> ty (Tf tws) e = end_ty k ->
  tilesS (itemS (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) k d) (i + 1) e n c c' ->
  1 <= i -> e + 1 <= Z.of_nat (length tws) -> 0 <= c -> c' <= Z.of_nat (length sbs) ->
  sb_acc1 st i c ->
  implM usegs (pj_part raw_malloc raw_free ps_so set_so_ps (sb_fuel st) len (sb_cap st) (sb_blk st)) s
        (ser_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 lo B SB len (e + 1) c' m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 DOC) (Z_to_bv 64 i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if k then PJ_APPEND_OBJ else PJ_APPEND_ARR)) fc None m (seg_rom usegs)).

End WithCeiling0.
