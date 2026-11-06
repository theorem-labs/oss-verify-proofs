(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim LJ PEnv.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition t_none : itree nodeL (exc unit) := Ret (Ok tt).
Definition t_opt (b : bool) (addr len : Z) : itree nodeL (exc unit) := if b then t_commit addr len else t_none.

Section T.
Context {HC : HasCeiling}.
Variable AL : alayout.

Definition t_efa (c : Z) (k : pclass) (total : Z) : itree nodeL (exc unit) :=
  t_opt (negb (efa_new k total =? p_mfa k)) (fa_base AL c + p_mfa k) (efa_new k total - p_mfa k).

Definition t_populate (c : Z) (k : pclass) (r : Z) : itree nodeL (exc unit) :=
  let mu' := pop_mu k c r in
  let k1 := mkPCL (p_nf k) (p_mfa k) (p_au k) mu' (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k) in
  ebind (t_opt (negb (mu' =? p_mu k)) (region AL c + p_mu k) (mu' - p_mu k))
        (fun _ => t_efa c k1 (p_nf k + pop_new k c r)).

Definition t_gfa (c : Z) (k : pclass) (n : Z) : itree nodeL (exc unit) :=
  if p_nf k <? n then ebind (t_populate c k (n - p_nf k)) (fun _ => t_none) else t_none.

Definition t_refill (c : Z) (k : pclass) : itree nodeL (exc unit) := ebind (t_gfa c k (max_count c / 2)) (fun _ => t_none).

Definition t_cdealloc (c : Z) (k : pclass) : itree nodeL (exc unit) :=
  if p_cnt k =? max_count c then ebind (ebind (t_efa c k (p_nf k + max_count c / 2)) (fun _ => t_none)) (fun _ => t_none) else t_none.

Definition H_commit (addr len : Z) (H : word -> bool) : word -> bool :=
  unhide_range (swlo addr) (swhi addr len) (unhide_range addr (addr + len) H).
Definition H_opt (b : bool) (addr len : Z) (H : word -> bool) : word -> bool := if b then H_commit addr len H else H.
Definition H_efa (c : Z) (k : pclass) (total : Z) (H : word -> bool) : word -> bool :=
  H_opt (negb (efa_new k total =? p_mfa k)) (fa_base AL c + p_mfa k) (efa_new k total - p_mfa k) H.
Definition H_populate (c : Z) (k : pclass) (r : Z) (H : word -> bool) : word -> bool :=
  let mu' := pop_mu k c r in
  let k1 := mkPCL (p_nf k) (p_mfa k) (p_au k) mu' (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k) in
  H_efa c k1 (p_nf k + pop_new k c r) (H_opt (negb (mu' =? p_mu k)) (region AL c + p_mu k) (mu' - p_mu k) H).
Definition H_gfa (c : Z) (k : pclass) (n : Z) (H : word -> bool) : word -> bool :=
  if p_nf k <? n then H_populate c k (n - p_nf k) H else H.
End T.

Definition MF_STACK : Z := 400.

Definition populate_entry : Z := 0x38850.
Definition POP_STACK : Z := 64 + 48 + MF_STACK + 64.

Section POP.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation THR := (at_thr (al_thread AL)).

Definition cls_open (m : mem) (inited : bool) (c : Z) (k : pclass) : Prop :=
  pclass_wf c k
  /\ (exists j8 j64 j88 j96 j104 j112 jpad, rw_cells asegs m (ri_addr AL c) (ri_cells KWL k j8 j64 j88 j96 j104 j112 jpad))
  /\ pcl_rep AL m inited c k /\ fa_rep AL m c k /\ tail_rep AL m c k
  /\ (forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m c v).

Definition stats_rep (m : mem) (calloc cmapped : Z) : Prop :=
  rw_cells asegs m (at_thr (al_thread AL) + CSTATS_OFF + 16) [C8 (wz calloc); C8 (wz cmapped)]
  /\ (exists ts, rw_cells asegs m (at_thr (al_thread AL) + TSTATS_OFF) [CB 368 ts]).

Definition populate_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo c r : Z) (k : pclass) (inited : bool) (calloc cmapped : Z) (H : word -> bool) (m : mem)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let k' := populate k c r in
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = H_populate AL c k r H
    /\ munch [(lo, q); (ri_addr AL c, ri_addr AL c + 128); (fa_base AL c + 4 * p_nf k, fa_base AL c + p_mfa k');
              (region AL c + p_mu k, region AL c + p_mu k'); (fa_base AL c + p_mfa k, fa_base AL c + p_mfa k');
              (sh (region AL c + p_mu k), sh (region AL c + p_mu k')); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa k'));
              (at_thr (al_thread AL) + CSTATS_OFF + 16, at_thr (al_thread AL) + CSTATS_OFF + 32);
              (at_thr (al_thread AL) + TSTATS_OFF, at_thr (al_thread AL) + TSTATS_OFF + 368)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
    /\ cls_open m' inited c k' /\ stats_rep m' calloc (cmapped + (p_mu k' - p_mu k)).

Definition populate_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo c r : Z) (k : pclass) (inited : bool) (calloc cmapped : Z),
  alayout_ok AL ->
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m -> prim_env AL m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - POP_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  1 <= c <= 31 -> 1 <= r <= 8 -> cls_open m inited c k -> stats_rep m calloc cmapped ->

  p_mu k + r * class_size c + K_MAP <= FA_OFF -> 4 * (p_nf k + (p_mu k + r * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE ->
  0 <= calloc -> 0 <= cmapped -> cmapped + K_REGION < 2^63 ->
  implA H (t_populate AL c k r)
        (populate_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo c r k inited calloc cmapped H m)
        (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz (at_thr (al_thread AL) + CSTATS_OFF)) (wz c) (wz (ri_addr AL c)) (wz r) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz populate_entry) fc None m (seg_rom asegs)).
End POP.
