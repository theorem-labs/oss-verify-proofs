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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim LJ PEnv APrimSpec.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition refill_entry : Z := 0x38430.
Definition cache_alloc_entry : Z := 0x37ce0.
Definition cache_dealloc_entry : Z := 0x35c9c.

Definition REFILL_STACK : Z := 32 + 128 + POP_STACK.
Definition CALLOC_STACK : Z := 48 + REFILL_STACK.
Definition CDEALLOC_STACK : Z := 48 + 64 + 128 + 48 + MF_STACK + 64.

Definition prim_ok (P : prim) : Prop := pr_inited P = false -> forall c, 1 <= c <= 31 -> p_cnt (get_cls P c) = 0.

Definition refill_budget (c : Z) (k : pclass) : Prop :=
  p_mu k + 8 * class_size c + K_MAP <= FA_OFF
  /\ 4 * (p_nf k + (p_mu k + 8 * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE.

Definition drain_budget (c : Z) (k : pclass) : Prop := 4 * (p_nf k + max_count c / 2) + K_MAP <= K_FA_SIZE.

Definition refill_prim (P : prim) (c : Z) : prim :=
  let k := get_cls P c in let k' := refill k c in
  mkPRIM (set_nth (Z.to_nat c) k' (pr_cls P)) true (pr_calloc P) (pr_cmapped P + (p_mu k' - p_mu k)).

Section S2.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation THR := (at_thr (al_thread AL)).
Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

Definition prim_W (lo q c : Z) (k k' : pclass) : list (Z * Z) :=
  [(lo, q); (ri_addr AL c, ri_addr AL c + 128);
   (fa_base AL c + 4 * Z.min (p_nf k) (p_nf k'), fa_base AL c + p_mfa k');
   (region AL c + p_mu k, region AL c + p_mu k');
   (sh (region AL c + p_mu k), sh (region AL c + p_mu k')); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa k'));
   (CACHE, CACHE + 2592); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)].

Definition refill_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo c : Z) (P : prim) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let k := get_cls P c in
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = H_gfa AL c k (max_count c / 2) H
    /\ munch (prim_W lo q c k (refill k c)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ shvis H' m'
    /\ RPRIM AL (refill_prim P c) m' /\ prim_ok (refill_prim P c).

Definition refill_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo c : Z) (P : prim),
  alayout_ok AL ->
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - REFILL_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  1 <= c <= 31 -> RPRIM AL P m -> prim_ok P -> p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c) ->
  0 <= pr_calloc P -> 0 <= pr_cmapped P -> pr_cmapped P + K_REGION < 2^63 ->
  implA H (t_refill AL c (get_cls P c))
        (refill_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo c P H m)
        (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz CACHE) (wz (pcl_addr AL c)) (wz INSTANCE) (wz c) a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz refill_entry) fc None m (seg_rom asegs)).

Definition RPRIM_pop_stmt : Prop :=
  forall (P : prim) (m : mem) (c : Z),
  RPRIM AL P m -> prim_ok P -> 1 <= c <= 31 -> 0 < p_cnt (get_cls P c) ->
  let k := get_cls P c in let cnt := p_cnt k in let v := nth (Z.to_nat (cnt - 1)) (p_chunks k) 0 in
  pr_inited P = true
  /\ 0 <= v /\ 16 * v + class_size c <= p_au k /\ (16 * v) mod class_size c = 0 /\ p_au k <= FA_OFF
  /\ prim_env AL m
  /\ rw_cells asegs m (pcl_addr AL c) [C4 (wz cnt); C4 (wz (max_count c)); C8 (wz (class_size c))]
  /\ (exists ws, u32arr asegs m (pcl_addr AL c + 16) ws /\ length ws = 16%nat /\ nth (Z.to_nat (cnt - 1)) ws (wz 0) = wz v)
  /\ rw_cells asegs m (THR + CSTATS_OFF + 16) [C8 (wz (pr_calloc P)); C8 (wz (pr_cmapped P))]
  /\ free_chunk AL m c v
  /\ (forall m', munch [(pcl_addr AL c, pcl_addr AL c + 4); (THR + CSTATS_OFF + 16, THR + CSTATS_OFF + 24)] m m' -> wmono asegs m m' ->
        rw_cells asegs m' (pcl_addr AL c) [C4 (wz (cnt - 1)); C4 (wz (max_count c)); C8 (wz (class_size c))] ->
        rw_cells asegs m' (THR + CSTATS_OFF + 16) [C8 (wz (pr_calloc P + class_size c)); C8 (wz (pr_cmapped P))] ->
        RPRIM AL (fst (cache_alloc P c)) m' /\ prim_ok (fst (cache_alloc P c)) /\ snd (cache_alloc P c) = v).

Definition class_of (size : Z) : Z :=
  if size <=? 512 then (size + 31) / 32
  else let l := Z.log2 size in
       Z.lor (2 * l) (Z.land (Z.shiftr size (l - 1)) 1) + Z.b2z (0 <? Z.land size (2 ^ (l - 1) - 1)) - 2.

Definition cache_alloc_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo c : Z) (P : prim) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let k := get_cls P c in let P' := fst (cache_alloc P c) in let v := snd (cache_alloc P c) in
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (region AL c + 16 * v)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = (if p_cnt k =? 0 then H_gfa AL c k (max_count c / 2) H else H)
    /\ munch (prim_W lo q c k (get_cls P' c)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ shvis H' m'
    /\ RPRIM AL P' m' /\ prim_ok P' /\ free_chunk AL m' c v
    /\ 0 <= v /\ 16 * v + class_size c <= p_au (get_cls P' c) /\ (16 * v) mod class_size c = 0.

Definition cache_alloc_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo size : Z) (P : prim),
  alayout_ok AL ->
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - CALLOC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  1 <= size <= 0x10000 -> RPRIM AL P m -> prim_ok P -> refill_budget (class_of size) (get_cls P (class_of size)) ->
  0 <= pr_calloc P -> 0 <= pr_cmapped P -> pr_cmapped P + K_REGION < 2^63 ->
  let c := class_of size in
  implA H (if p_cnt (get_cls P c) =? 0 then t_refill AL c (get_cls P c) else t_none)
        (cache_alloc_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo c P H m)
        (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz CACHE) (wz size) (wz 8) a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz cache_alloc_entry) fc None m (seg_rom asegs)).

Definition cache_dealloc_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo c v : Z) (P : prim) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let k := get_cls P c in let P' := cache_dealloc P c v in
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = (if p_cnt k =? max_count c then H_efa AL c k (p_nf k + max_count c / 2) H else H)
    /\ munch (prim_W lo q c k (get_cls P' c)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ shvis H' m'
    /\ RPRIM AL P' m' /\ prim_ok P'.

Definition cache_dealloc_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo c v : Z) (P : prim),
  alayout_ok AL ->
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - CDEALLOC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  1 <= c <= 31 -> RPRIM AL P m -> prim_ok P ->

  0 <= v -> 16 * v + class_size c <= p_au (get_cls P c) -> (16 * v) mod class_size c = 0 ->
  ~ In v (p_fa (get_cls P c) ++ p_chunks (get_cls P c)) -> free_chunk AL m c v ->
  implA H (t_cdealloc AL c (get_cls P c))
        (cache_dealloc_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo c v P H m)
        (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz CACHE) (wz INSTANCE) (wz c) (wz (region AL c + 16 * v)) a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz cache_dealloc_entry) fc None m (seg_rom asegs)).
End S2.
