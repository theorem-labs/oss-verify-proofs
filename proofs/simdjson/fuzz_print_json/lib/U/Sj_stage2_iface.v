(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeInv SjTapeTile SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Sj_iface Sj_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition SJ_STAGE2 : Z := 0x43550.

Definition SJ_S2_FRAMES : Z := 7168.
Definition SJ_S2_STACK : Z := SJ_S2_FRAMES + 32 + RMALLOC_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition s2_root_phase (bs idxs : list Z) : M PState unit :=
  match SjAlloc.root_copy bs 0 (hd 0 idxs) with
  | Some c => mbind (newnt lops c) (fun r => del lops r)
  | None => mret tt
  end.

Definition region_in (LB : list block) (X n : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= X /\ X + n <= blk_addr b + blk_size b.

Definition ivl_disj (a b : Z * Z) : Prop := fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Fixpoint pairwise_disj (l : list (Z * Z)) : Prop :=
  match l with [] => True | x :: r => Forall (ivl_disj x) r /\ pairwise_disj r end.

Definition s2_impl_cells (n IDX cap OC IA BUF len : Z) (nxt docv : word) (p12 p28 p50 : list byte) : list cell :=
  [C8 (wz SJ_DPI_VPTR); C4 (wz n); CB 4 p12; C8 (wz IDX); C4 nxt; CB 4 p28; C8 (wz cap); C8 (wz 1024);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 p50; C8 (wz OC); C8 (wz IA); C8 (wz BUF); C8 (wz len); C8 docv].

Definition s2_X (THIS TAPE SBUF OC IA tcap scap : Z) : list (Z * Z) :=
  [(THIS, THIS + 96); (TAPE, TAPE + 8 * tcap); (SBUF, SBUF + scap); (OC, OC + 8192); (IA, IA + 1024)].

Definition stage2_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (lo B : Z) (m : mem)
    (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (n cap len tcap scap : Z) (p12 p28 p50 : list byte)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' nxt' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ RHEAP s' LB m' /\ rauxv_ok m' B /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ mem_inv usegs m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ lx_pres LB (bv_unsigned sp) (s2_X THIS TAPE SBUF OC IA tcap scap) m m'
    /\ rw_cells usegs m' THIS (s2_impl_cells n IDX cap OC IA BUF len nxt' (wz DOC) p12 p28 p50)
    /\ bv_unsigned a0 < 64.

Definition stage2_stmt : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv : word)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs idxs : list Z) (iws : list word) (cap tcap scap : Z)
         (nxt docv dcap : word) (p12 p28 p50 : list byte),

  S1OUT bs idxs -> bytes_ok bs -> blen bs <= 1048512 ->
  firstn (length idxs + 3) iws = map wz (idxs ++ [blen bs; blen bs; 0]) ->

  blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 ->
  blen bs + 3 <= Z.of_nat (length iws) ->

  RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SJ_S2_STACK ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
  rw_cells usegs m SJ_GOT_NOTHROW [C8 (wz SJ_NOTHROW_TAG)] ->

  region_in LB THIS 96 -> region_in LB IDX (4 * Z.of_nat (length iws)) -> region_in LB BUF (blen bs + 64) ->
  region_in LB TAPE (8 * tcap) -> region_in LB SBUF scap -> region_in LB OC 8192 -> region_in LB IA 1024 ->
  pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length iws)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
  bv_unsigned sp <= DOC -> DOC + 24 <= B ->
  THIS mod 8 = 0 -> DOC mod 8 = 0 -> IDX mod 4 = 0 -> TAPE mod 8 = 0 -> OC mod 8 = 0 ->
  rw_cells usegs m THIS (s2_impl_cells (Z.of_nat (length idxs)) IDX cap OC IA BUF (blen bs) nxt docv p12 p28 p50) ->
  rw_cells usegs m DOC [C8 (wz TAPE); C8 (wz SBUF); C8 dcap] ->
  u32arr usegs m IDX iws ->
  bytes_at usegs m BUF (padded_bytes bs) ->
  wr_at usegs m TAPE (8 * tcap) -> wr_at usegs m SBUF scap ->
  (exists ocs, u32arr usegs m OC ocs /\ length ocs = 2048%nat) ->
  (exists ias, u8arr usegs m IA ias /\ length ias = 1024%nat) ->
  implM usegs (s2_root_phase bs idxs) s
        (stage2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B m
                     THIS DOC IDX BUF TAPE SBUF OC IA (Z.of_nat (length idxs)) cap (blen bs) tcap scap p12 p28 p50)
        (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz THIS) (wz DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz SJ_STAGE2) fc None m (seg_rom usegs)).

Definition s2_okres (TAPE SBUF tcap scap : Z) (a0 : word) (m' : mem) : Prop :=
  (1 <= bv_unsigned a0 < 64) \/
  (a0 = wz 0 /\
   exists tws sbs : list Z,
     bytes_at usegs m' TAPE (u64s (map (Z_to_bv 64) tws)) /\ bytes_at usegs m' SBUF (map (Z_to_bv 8) sbs) /\
     tape_wfS (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any (Z.of_nat (length tws)) /\
     Forall (fun c => 0 <= c < 256) sbs /\
     Z.of_nat (length tws) <= tcap /\ Z.of_nat (length sbs) <= scap).

Definition stage2t_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (lo B : Z) (m : mem)
    (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (n cap len tcap scap : Z) (p12 p28 p50 : list byte)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' nxt' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ RHEAP s' LB m' /\ rauxv_ok m' B /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ mem_inv usegs m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ lx_pres LB (bv_unsigned sp) (s2_X THIS TAPE SBUF OC IA tcap scap) m m'
    /\ rw_cells usegs m' THIS (s2_impl_cells n IDX cap OC IA BUF len nxt' (wz DOC) p12 p28 p50)
    /\ s2_okres TAPE SBUF tcap scap a0 m'.

Definition stage2t_stmt : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv : word)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs idxs : list Z) (iws : list word) (cap tcap scap : Z)
         (nxt docv dcap : word) (p12 p28 p50 : list byte),

  S1OUT bs idxs -> bytes_ok bs -> blen bs <= 1048512 ->
  firstn (length idxs + 3) iws = map wz (idxs ++ [blen bs; blen bs; 0]) ->

  blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 ->
  blen bs + 3 <= Z.of_nat (length iws) ->

  RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SJ_S2_STACK ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
  rw_cells usegs m SJ_GOT_NOTHROW [C8 (wz SJ_NOTHROW_TAG)] ->

  region_in LB THIS 96 -> region_in LB IDX (4 * Z.of_nat (length iws)) -> region_in LB BUF (blen bs + 64) ->
  region_in LB TAPE (8 * tcap) -> region_in LB SBUF scap -> region_in LB OC 8192 -> region_in LB IA 1024 ->
  pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length iws)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
  bv_unsigned sp <= DOC -> DOC + 24 <= B ->
  THIS mod 8 = 0 -> DOC mod 8 = 0 -> IDX mod 4 = 0 -> TAPE mod 8 = 0 -> OC mod 8 = 0 ->
  rw_cells usegs m THIS (s2_impl_cells (Z.of_nat (length idxs)) IDX cap OC IA BUF (blen bs) nxt docv p12 p28 p50) ->
  rw_cells usegs m DOC [C8 (wz TAPE); C8 (wz SBUF); C8 dcap] ->
  u32arr usegs m IDX iws ->
  bytes_at usegs m BUF (padded_bytes bs) ->
  wr_at usegs m TAPE (8 * tcap) -> wr_at usegs m SBUF scap ->
  (exists ocs, u32arr usegs m OC ocs /\ length ocs = 2048%nat) ->
  (exists ias, u8arr usegs m IA ias /\ length ias = 1024%nat) ->
  implM usegs (s2_root_phase bs idxs) s
        (stage2t_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B m
                     THIS DOC IDX BUF TAPE SBUF OC IA (Z.of_nat (length idxs)) cap (blen bs) tcap scap p12 p28 p50)
        (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz THIS) (wz DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz SJ_STAGE2) fc None m (seg_rom usegs)).

Lemma stage2t_post_weaken : forall ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B m THIS DOC IDX BUF TAPE SBUF OC IA n cap len tcap scap p12 p28 p50 r s' ms',
  stage2t_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B m THIS DOC IDX BUF TAPE SBUF OC IA n cap len tcap scap p12 p28 p50 r s' ms' ->
  stage2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B m THIS DOC IDX BUF TAPE SBUF OC IA n cap len tcap scap p12 p28 p50 r s' ms'.
Proof.
  intros until ms'. intros H. unfold stage2t_post in H. unfold stage2_post.
  destruct H as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & m' & errv' & nxt' & H).
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m', errv', nxt'.
  assert (R64 : bv_unsigned a0 < 64).
  { destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [K | [E _]]); [lia | subst a0; vm_compute; reflexivity]. }
  tauto.
Qed.

Lemma stage2_of_stage2t : stage2t_stmt -> stage2_stmt.
Proof.
  intros H. unfold stage2_stmt.
  intros ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws cap tcap scap nxt docv dcap p12 p28 p50. intros.
  eapply implM_mono.
  { eapply (H ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws cap tcap scap nxt docv dcap p12 p28 p50); eassumption. }
  intros [] s' ms'. apply stage2t_post_weaken.
Qed.
End WithCeiling0.

