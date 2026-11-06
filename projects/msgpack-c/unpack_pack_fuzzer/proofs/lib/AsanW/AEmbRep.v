(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition AEMB : Z := 0xd9328.

Definition emb_cells (st : astate) (m : amem) : Prop :=
  let '(d, cap, sz) := a_emb st in
  rw_cells asegs m (AEMB + 16) [C8 (Z_to_bv 64 0)]
  /\ (if cap =? 0
      then rw_cells asegs m AEMB [C8 (Z_to_bv 64 0)] /\ sz = 0
           /\ rw_cells asegs m (AEMB + 32) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
      else rw_cells asegs m AEMB [C8 (Z_to_bv 64 (AEMB + 32))]
           /\ rw_cells asegs m (AEMB + 32) [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)]
           /\ 0 <= sz <= cap /\ EMB_INIT <= cap /\ cap mod 4096 = 0 /\ d mod 4096 = 0 /\ AIMG_HI <= d /\ d + cap <= ATOP
           /\ exists junk, rw_cells asegs m d [CB (Z.to_nat cap) junk]).

Definition emb_rng (st : astate) (RNG : footprint) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ rng RNG d cap.

Definition EXH_STACK : Z := 1280.

Definition exh_cells (m : amem) : Prop :=
     rmap_cells m
  /\ rw_cells asegs m 0xd3470 [C8 (Z_to_bv 64 0x22004)]
  /\ rw_cells asegs m 0x16b628 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x16b7d0 [C8 (Z_to_bv 64 0x60de8)].

Definition emb_prov (RESV : list (Z * Z)) (st : astate) (d0 cap0 d cap : Z) : Prop :=
  (d = d0 /\ cap = cap0) \/ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true.

Definition exh_first_ret (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ (exists e2, st2 = set_emb e2 (exh_set c st))
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m'
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 1)]

  /\ (exists d1 cap1,
        munch [(bv_unsigned sp - EXH_STACK, bv_unsigned sp); (RI + 68, RI + 69); (AEMB, AEMB + 56);
               (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z m m'
        /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2
        /\ (cap1 = 0 \/ d1 + cap1 <= ATOP))
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Definition exh_first_stmt : Prop :=
  forall RNG (R : Type) (RESV : list (Z * Z)) (k' : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z),
  let RI := aregion_info L c in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EXH_STACK ->
  bv_unsigned sp < 2 ^ 63 ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  arelro m ->
  bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m ->
  (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  aresv_ok L RESV ->
  AIMG_HI <= RI -> RI + 128 <= ATOP ->
  pcov RESV RI (RI + 128) ->
  (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  1 <= c < K_NUM_CLASSES -> exh_mem c st = false ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> emb_rng st RNG ->
  (forall st2 RNG' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      exh_first_ret L RESV RNG sp st c lo m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k' st2)) (epostF Q)
            (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 c) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x422d8) fc None m' (seg_rom asegs))) ->
  implS asegs RNG
        (aembed ATOP (emb_append ATOP RESV (exh_set c st) EXH_LEN1 (fun st1 => emb_append ATOP RESV st1 (exh_len2 c) k'))) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RI) s1 a0 a1 (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42240) fc None m (seg_rom asegs)).

End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import AMalloc_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition AEMB : Z := 0xdb4e8.

Definition emb_cells (st : astate) (m : amem) : Prop :=
  let '(d, cap, sz) := a_emb st in
  rw_cells bsegs m (AEMB + 16) [C8 (Z_to_bv 64 0)]
  /\ (if cap =? 0
      then rw_cells bsegs m AEMB [C8 (Z_to_bv 64 0)] /\ sz = 0
           /\ rw_cells bsegs m (AEMB + 32) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
      else rw_cells bsegs m AEMB [C8 (Z_to_bv 64 (AEMB + 32))]
           /\ rw_cells bsegs m (AEMB + 32) [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)]
           /\ 0 <= sz <= cap /\ EMB_INIT <= cap /\ cap mod 4096 = 0 /\ d mod 4096 = 0 /\ AIMG_HI <= d /\ d + cap <= ATOP
           /\ exists junk, rw_cells bsegs m d [CB (Z.to_nat cap) junk]).

Definition emb_rng (st : astate) (RNG : footprint) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ rng RNG d cap.

Definition EXH_STACK : Z := 1280.

Definition exh_cells (m : amem) : Prop :=
     rmap_cells m
  /\ rw_cells bsegs m 0xd5588 [C8 (Z_to_bv 64 0x220a2)]
  /\ rw_cells bsegs m 0x16d7e8 [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x16d990 [C8 (Z_to_bv 64 0x61778)].

Definition emb_prov (RESV : list (Z * Z)) (st : astate) (d0 cap0 d cap : Z) : Prop :=
  (d = d0 /\ cap = cap0) \/ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true.

Definition exh_first_ret (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ (exists e2, st2 = set_emb e2 (exh_set c st))
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m'
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 1)]

  /\ (exists d1 cap1,
        munch [(bv_unsigned sp - EXH_STACK, bv_unsigned sp); (RI + 68, RI + 69); (AEMB, AEMB + 56);
               (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z m m'
        /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2
        /\ (cap1 = 0 \/ d1 + cap1 <= ATOP))
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Definition exh_first_stmt : Prop :=
  forall RNG (R : Type) (RESV : list (Z * Z)) (k' : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z),
  let RI := aregion_info L c in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EXH_STACK ->
  bv_unsigned sp < 2 ^ 63 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  arelro m ->
  bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m ->
  (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  aresv_ok L RESV ->
  AIMG_HI <= RI -> RI + 128 <= ATOP ->
  pcov RESV RI (RI + 128) ->
  (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  1 <= c < K_NUM_CLASSES -> exh_mem c st = false ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> emb_rng st RNG ->
  (forall st2 RNG' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      exh_first_ret L RESV RNG sp st c lo m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k' st2)) (epostF Q)
            (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 c) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x42c68) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG
        (aembed ATOP (emb_append ATOP RESV (exh_set c st) EXH_LEN1 (fun st1 => emb_append ATOP RESV st1 (exh_len2 c) k'))) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RI) s1 a0 a1 (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42bd0) fc None m (seg_rom bsegs)).

End CANSEC.
End TwinB.
