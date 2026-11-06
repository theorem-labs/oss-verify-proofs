(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ARep AHeapP AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AInstance AInstanceM AInstanceF AInstanceD ADepot_iface ARepQ F_adepot ASec F_apoison_remap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1_16. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aaligned_iseg AEmbRep AExh ARefill_iface_x ARefillP_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.AMallocPG_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.AAlignedPG_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section Stmt.
Context {rc : runConstT} {ov : annOV}.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition aaligned16_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  is_primary16 n = true -> n mod 16 = 0 ->
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AALIGNED_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AALIGNED_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (aaligned16x ATOP RESV st n))
        (epostF (amalloc_post_h CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom asegs)).
End Stmt.

Section Inst.
Context {rc : runConstT} {ov : annOV} {gb : GcBit}.

Lemma aci_ok3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15bd20 \/ 0x15bd21 <= fst iv)) aci_I.
Proof. unfold aci_I, msg_img_ranges, AEMB. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Section X.
Hypothesis EXHW : exh_first_stmt.

Theorem AHI_malloc_h : amalloc_stmt_h aci_I AHEAP_I.
Proof. exact (amalloc_all_h adepot_iface AQUAR AFAKE AH_laws AH_lawsD EXHW poison_remap_proof aci_I aci_ok aci_ok2 aci_ok3). Qed.

Theorem AHI_allocate_h : aallocate_stmt_h aci_I AHEAP_I.
Proof. exact (aallocate_all_h adepot_iface AQUAR AFAKE AH_laws AH_lawsD EXHW poison_remap_proof aci_I aci_ok aci_ok2 aci_ok3). Qed.

Theorem AHI_aligned16_h : aaligned16_stmt_h aci_I AHEAP_I.
Proof.
  unfold aaligned16_stmt_h. intros until RESV. intros OVF PRIM N16 AHP MI ST BOT LO TP A0 A1 NR AUNW S0NE RA4 RANE SP16 RSTK ARV FCB [ER ECL] CAPB ERRC.
  destruct (aheap_c6 adepot_iface AQUAR AFAKE AH_lawsD _ _ _ _ _ AHP) as (XC & EC & AXF & _ & _).
  eapply implF_epost_mono.
  { eapply (aaligned_prim16_x adepot_iface AQUAR ASEC_of AFAKE AH_laws AH_lawsD EXHW aci_I aci_ok aci_ok2 aci_ok3
              L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV); try eassumption.
    split; [exact XC|]. split; [exact EC|]. split; [exact ER| exact ECL]. }
  intros r RNG' ms' [_ M]. exact M.
Qed.
End X.
End Inst.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB ARep.TwinB AHeapP.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB AInstanceD.TwinB ADepot_iface.TwinB ARepQ.TwinB F_adepot.TwinB ASec.TwinB F_apoison_remap.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1_16. Import F_aaligned_iseg.TwinB AEmbRep.TwinB AExh.TwinB ARefill_iface_x.TwinB ARefillP_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.TwinB.AMallocPG_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.TwinB.AAlignedPG_x. Import AMalloc_x.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section Stmt.
Context {rc : runConstT} {ov : annOV}.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition aaligned16_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  is_primary16 n = true -> n mod 16 = 0 ->
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AALIGNED_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AALIGNED_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (aaligned16x ATOP RESV st n))
        (epostF (amalloc_post_h CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom bsegs)).
End Stmt.

Section Inst.
Context {rc : runConstT} {ov : annOV} {gb : GcBit}.

Lemma aci_ok3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15dee0 \/ 0x15dee1 <= fst iv)) aci_I.
Proof. unfold aci_I, msg_img_ranges, AEMB. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Section X.
Hypothesis EXHW : exh_first_stmt.

Theorem AHI_malloc_h : amalloc_stmt_h aci_I AHEAP_I.
Proof. exact (amalloc_all_h adepot_iface AQUAR AFAKE AH_laws AH_lawsD EXHW poison_remap_proof aci_I aci_ok aci_ok2 aci_ok3). Qed.

Theorem AHI_allocate_h : aallocate_stmt_h aci_I AHEAP_I.
Proof. exact (aallocate_all_h adepot_iface AQUAR AFAKE AH_laws AH_lawsD EXHW poison_remap_proof aci_I aci_ok aci_ok2 aci_ok3). Qed.

Theorem AHI_aligned16_h : aaligned16_stmt_h aci_I AHEAP_I.
Proof.
  unfold aaligned16_stmt_h. intros until RESV. intros OVF PRIM N16 AHP MI ST BOT LO TP A0 A1 NR AUNW S0NE RA4 RANE SP16 RSTK ARV FCB [ER ECL] CAPB ERRC.
  destruct (aheap_c6 adepot_iface AQUAR AFAKE AH_lawsD _ _ _ _ _ AHP) as (XC & EC & AXF & _ & _).
  eapply implF_epost_mono.
  { eapply (aaligned_prim16_x adepot_iface AQUAR ASEC_of AFAKE AH_laws AH_lawsD EXHW aci_I aci_ok aci_ok2 aci_ok3
              L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV); try eassumption.
    split; [exact XC|]. split; [exact EC|]. split; [exact ER| exact ECL]. }
  intros r RNG' ms' [_ M]. exact M.
Qed.
End X.
End Inst.
End TwinB.
