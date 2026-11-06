(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AInv ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocA AMallocI.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA.AMalrao OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition malloc_key (top bot fp : Z) (ra : word) : list Z :=
  if unwind_depth2 top bot fp then [0x58c14; bv_unsigned ra] else [0x58c14].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition malloc_hit_W (sp : word) (thr c AB n q r8 d e n0 f0 : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 2128 - 224, bv_unsigned sp); (thr + 3168, thr + 3168 + 1)]
  ++ alloc_hit_W (Z_to_bv 64 (bv_unsigned sp + -2144)) thr c AB n q r8 d e n0 f0.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MallocHit.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n tsd ctx thr top bot c cnt maxc sb AB q r8 d e n0 f0 : Z).
  Variables (ks : list word) (b0w b1w : byte) (kw statv h2 w4 d8 j0 j1 v0 v1 v2 : word) (vs : list word)
            (D : list (list Z)) (olds uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 3168.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58c14.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  (* [comment removed for export] *)
  Hypothesis UNW : unwind_stmt.
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.
  (* [comment removed for export] *)
  Hypothesis INI : ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)].
  Hypothesis RZm : ro_cells rsegs m 0xb2b80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis MUM : ro_cells rsegs m 0xb2b78 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis CMCS : ro_cells rsegs m 0xb60bc [C4 (Z_to_bv 64 30)].                 (* [comment removed for export] *)
  Hypothesis CFU : ro_cells rsegs m (0x146ee8 + 34) [C1 (Z_to_bv 8 1)].             (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  (* [comment removed for export] *)
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis PC : rw_cells rsegs m (thr + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis CNT : 1 <= cnt <= 16.
  Hypothesis KW : nth_error ks (Z.to_nat (cnt - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis STA : rw_cells rsegs m (thr + 208 + 2576) [C8 statv].
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STA2 : u64arr rsegs m (thr + 2912) vs.
  Hypothesis LVS : length vs = 32%nat.
  (* [comment removed for export] *)
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis ABH : rz_size n <> 16 -> rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis SHA : ro_cells rsegs m (q + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)].
  Hypothesis SHU : u8arr rsegs m (q + r8 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + r8 + d + kShadowOffset) [C1 oldp].
  Hypothesis USR : rw_cells rsegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
  (* [comment removed for export] *)
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : apart n0 kDepotNodesBlock sb (2^37).
  Hypothesis SEP_f0 : apart f0 kStackStoreBlockBytes sb (2^37).
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pasan rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pasan n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pasan rsegs D' n0 f0 m2.

  Definition malloc_hit_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' : word) (m' md : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (AB + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (malloc_hit_W sp thr c AB n q r8 d e n0 f0) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)]
    /\ rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0'; C8 v1'; C8 v2']
    /\ u64arr rsegs m' (thr + 2912) (upd vs (Z.to_nat c) vc')
    /\ rw_cells rsegs m' (AB + rz_size n + -16)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land (b1_mid (bv_unsigned b1w)) 243) 0));
          C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 (snd (depot_putC D (malloc_key top bot (bv_unsigned sp) ra))))]
    /\ (rz_size n <> 16 -> rw_cells rsegs m' AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + rz_size n + -16))])
    /\ bytes_at rsegs m' (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))
    /\ wr_at rsegs m' (q + r8 + kShadowOffset) d
    /\ (e <> 0 -> rw_cells rsegs m' (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)])
    /\ rw_cells rsegs m' (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) (fill_result 1 uj (Z.to_nat (Z.min n 4096)))]
    /\ dr AL_pasan rsegs (fst (depot_putC D (malloc_key top bot (bv_unsigned sp) ra))) n0 f0 md
    /\ munch (alloc_hit_W2 (Z_to_bv 64 (bv_unsigned sp + -2144)) thr c AB n q r8 d e) md m' /\ wmono rsegs md m'.

  (* [comment removed for export] *)
End MallocHit.
