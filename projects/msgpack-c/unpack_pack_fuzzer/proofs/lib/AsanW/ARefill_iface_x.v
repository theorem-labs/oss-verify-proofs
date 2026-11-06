(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP ARefill_iface AMalloc_iface AEmbRep AEmbFrame. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Export AExh.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSECX. Context {rc : runConstT} {ov : annOV}.

Definition axg (RESV : list (Z * Z)) (RNG : footprint) (st : astate) (m : amem) : Prop :=
  exh_cells m /\ emb_cells st m /\ emb_rng st RNG /\ emb_clr RESV st.

Notation AREFILL_STACK_X := 2048 (only parsing).

Notation arefill_Wx L st c sp :=
  ([(sp - AREFILL_STACK_X, sp);
    (al_t L + 208, al_t L + 3168);
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

Definition refill_ret_xt (H : aholes) (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')

    /\ a_emb st_r = a_emb st /\ (a_exh st_r = a_exh st \/ a_exh st_r = a_exh (exh_clear c st))
    /\ axflag L st_r m' c /\ axg RESV RNG' st_r m'.

Definition aret_xf (H : aholes) (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (XS : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ ((exh_mem c st = true /\ st2 = init_cache st) \/ (exh_mem c st = false /\ exists e2, st2 = set_emb e2 (exh_set c (init_cache st))))
    /\ AREP H L st2 X m' /\ arng L RNG' st2
    /\ axflag L st2 m' c /\ axg RESV RNG' st2 m'
    /\ (exists d1 cap1,
          munch ([(bv_unsigned sp - XS, bv_unsigned sp); (al_t L + 208, al_t L + 2768);
                  (RI, RI + 8); (RI + 68, RI + 69); (AEMB, AEMB + 56);
                  (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z) m m'
          /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2 /\ (cap1 = 0 \/ d1 + cap1 <= ATOP)).
Definition refill_ret_xf (H : aholes) (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) :=
  aret_xf H L RESV RNG AREFILL_STACK_X.

Definition refill_stmt_x (H : aholes) : Prop :=
  forall {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> bv_unsigned fc < 32 ->
  axflag L st m c -> axg RESV RNG st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->

  (forall st2 RNG' ms', refill_ret_xf H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st2 RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q) ms') ->
  (forall st_r X' RNG' ms', refill_ret_xt H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_refill_tree_x RESV st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41b70) fc None m (seg_rom asegs)).
End CANSECX.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB ARefill_iface.TwinB AMalloc_iface.TwinB AEmbRep.TwinB AEmbFrame.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x.
Export AExh.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSECX. Context {rc : runConstT} {ov : annOV}.

Definition axg (RESV : list (Z * Z)) (RNG : footprint) (st : astate) (m : amem) : Prop :=
  exh_cells m /\ emb_cells st m /\ emb_rng st RNG /\ emb_clr RESV st.

Notation AREFILL_STACK_X := 2048 (only parsing).

Notation arefill_Wx L st c sp :=
  ([(sp - AREFILL_STACK_X, sp);
    (al_t L + 208, al_t L + 3168);
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

Definition refill_ret_xt (H : aholes) (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')

    /\ a_emb st_r = a_emb st /\ (a_exh st_r = a_exh st \/ a_exh st_r = a_exh (exh_clear c st))
    /\ axflag L st_r m' c /\ axg RESV RNG' st_r m'.

Definition aret_xf (H : aholes) (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (XS : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ((exh_mem c st = true /\ st2 = init_cache st) \/ (exh_mem c st = false /\ exists e2, st2 = set_emb e2 (exh_set c (init_cache st))))
    /\ AREP H L st2 X m' /\ arng L RNG' st2
    /\ axflag L st2 m' c /\ axg RESV RNG' st2 m'
    /\ (exists d1 cap1,
          munch ([(bv_unsigned sp - XS, bv_unsigned sp); (al_t L + 208, al_t L + 2768);
                  (RI, RI + 8); (RI + 68, RI + 69); (AEMB, AEMB + 56);
                  (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z) m m'
          /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2 /\ (cap1 = 0 \/ d1 + cap1 <= ATOP)).
Definition refill_ret_xf (H : aholes) (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) :=
  aret_xf H L RESV RNG AREFILL_STACK_X.

Definition refill_stmt_x (H : aholes) : Prop :=
  forall {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> bv_unsigned fc < 32 ->
  axflag L st m c -> axg RESV RNG st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->

  (forall st2 RNG' ms', refill_ret_xf H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st2 RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q) ms') ->
  (forall st_r X' RNG' ms', refill_ret_xt H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree_x RESV st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42500) fc None m (seg_rom bsegs)).
End CANSECX.
End TwinB.
