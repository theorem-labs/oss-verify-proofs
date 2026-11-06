(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ARepQR ARepQD ALayout AHeapP ARepKit ARepFrame AKit AKit2 AModelFacts ASec AFreeModel AFreeRep AFreeGeo. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_afree_tail F_afree_icpt. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afreeC_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_afree_arep ARecGeo F_adorec AQrecP AFreeC_kit_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_adealloc_icpt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_icpt.F_adealloc_icptC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).
Notation AHc := (AFreeC_kit_iface.AHc DI AFK).

Definition storeC_post_D (L : alayout) (RNG : footprint) (ek : enq_kind) (g : gqd)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (stT : astate) (LB' : list ablock) (t lo : Z) (m0 : amem) (ms1 : machine_state) : Prop :=
  exists (X' : aconc) (R : qrconc) (m1 : amem) (id : Z)
         (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let spP := bv_unsigned sp in
    ms1 = MS (mkR (Z_to_bv 64 0x41168) (Z_to_bv 64 (spP - 80)) gp (Z_to_bv 64 ATP) t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3eb38) fc None m1 (seg_rom asegs)

    /\ AREP (AHc R 0 1 (csx stT R)) L stT X' m1
    /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []
    /\ arng L RNG stT /\ ablocks L stT X' LB' /\ AFK L LB' m1
    /\ a_qglob_bytes stT < 2^56 /\ a_qloc stT = [] /\ a_qloc_bytes stT = 0

    /\ mem_inv asegs m1 /\ stk asegs m1 lo (spP - 80)
    /\ aheap_pres CI LB' (bv_unsigned sp) m0 m1
    /\ 0 < id < 2^31

    /\ rw_cells asegs m1 (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra).

Definition store_freeC_stmt_D : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post_D DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post_D L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

Definition afree_back_stmt_D : Prop :=
  forall (L : alayout) (RNG0 RNG RNG1 : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 mR : amem) (st stR : astate) (XR : aconc) (R : qrconc) (LB : list ablock) (p : aptr) (t lo : Z)
         (st1 : astate) (X1 : aconc) (ms2 : machine_state),
  let spP := bv_unsigned sp in
  let LB' := lb_remove p LB in
  alayout_ok L -> ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1ab988 \/ 0x5fb9d0 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xd6730 \/ 0xd67f0 <= fst iv) /\ (snd iv <= 0xdacc0 \/ 0x15bcf0 <= fst iv) /\ (snd iv <= 0x169548 \/ 0x16954c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  fp_le RNG0 RNG ->

  awf L stR XR -> ablocks L stR XR LB' -> aheap_pres CI LB' (bv_unsigned sp) m0 mR ->
  rw_cells asegs mR (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  aqrec_ret ASECc (ADEPOT DI) AFK L RNG LB' (Z_to_bv 64 0x41168) (Z_to_bv 64 (spP - 80)) gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 F fc
            stR R lo Q_MIN mR st1 X1 RNG1 ms2 ->
  a_qloc stR = [] -> a_qloc_bytes stR = 0 ->
  implS asegs RNG1 (aembed ATOP (aret st1))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG0 ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m0))
        ms2.
End S.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AQConst.TwinB AKitQ.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB ARep.TwinB ARepQ.TwinB ARepQP.TwinB ARepQR.TwinB ARepQD.TwinB ALayout.TwinB AHeapP.TwinB ARepKit.TwinB ARepFrame.TwinB AKit.TwinB AKit2.TwinB AModelFacts.TwinB ASec.TwinB AFreeModel.TwinB AFreeRep.TwinB AFreeGeo.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead. Import F_afree_tail.TwinB F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afreeC_iface. Import F_afree_arep.TwinB ARecGeo.TwinB F_adorec.TwinB AQrecP.TwinB AFreeC_kit_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_icpt.TwinB.F_adealloc_icptC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).
Notation AHc := (AFreeC_kit_iface.TwinB.AHc DI AFK).

Definition storeC_post_D (L : alayout) (RNG : footprint) (ek : enq_kind) (g : gqd)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (stT : astate) (LB' : list ablock) (t lo : Z) (m0 : amem) (ms1 : machine_state) : Prop :=
  exists (X' : aconc) (R : qrconc) (m1 : amem) (id : Z)
         (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let spP := bv_unsigned sp in
    ms1 = MS (mkR (Z_to_bv 64 0x41af8) (Z_to_bv 64 (spP - 80)) gp (Z_to_bv 64 ATP) t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f4c8) fc None m1 (seg_rom bsegs)

    /\ AREP (AHc R 0 1 (csx stT R)) L stT X' m1
    /\ qr_tmp R = [] /\ qr_pendb R = [] /\ qr_pend R = []
    /\ arng L RNG stT /\ ablocks L stT X' LB' /\ AFK L LB' m1
    /\ a_qglob_bytes stT < 2^56 /\ a_qloc stT = [] /\ a_qloc_bytes stT = 0

    /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (spP - 80)
    /\ aheap_pres CI LB' (bv_unsigned sp) m0 m1
    /\ 0 < id < 2^31

    /\ rw_cells bsegs m1 (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra).

Definition store_freeC_stmt_D : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post_D DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post_D L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

Definition afree_back_stmt_D : Prop :=
  forall (L : alayout) (RNG0 RNG RNG1 : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 mR : amem) (st stR : astate) (XR : aconc) (R : qrconc) (LB : list ablock) (p : aptr) (t lo : Z)
         (st1 : astate) (X1 : aconc) (ms2 : machine_state),
  let spP := bv_unsigned sp in
  let LB' := lb_remove p LB in
  alayout_ok L -> ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1adb48 \/ 0x5fdb90 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xd88f0 \/ 0xd89b0 <= fst iv) /\ (snd iv <= 0xdce80 \/ 0x15deb0 <= fst iv) /\ (snd iv <= 0x16b708 \/ 0x16b70c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  fp_le RNG0 RNG ->

  awf L stR XR -> ablocks L stR XR LB' -> aheap_pres CI LB' (bv_unsigned sp) m0 mR ->
  rw_cells bsegs mR (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  aqrec_ret ASECc (ADEPOT DI) AFK L RNG LB' (Z_to_bv 64 0x41af8) (Z_to_bv 64 (spP - 80)) gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 F fc
            stR R lo Q_MIN mR st1 X1 RNG1 ms2 ->
  a_qloc stR = [] -> a_qloc_bytes stR = 0 ->
  implS bsegs RNG1 (aembed ATOP (aret st1))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG0 ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m0))
        ms2.
End S.
End CANSEC2.
End TwinB.
