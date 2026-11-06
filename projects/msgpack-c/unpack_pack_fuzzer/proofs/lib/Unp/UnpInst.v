(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Cells Step Frame Omono.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Ops ClientX GLib
     G0 G1 G2 G2Z G2B G3 G3P G4 GRoom G6 GCap GNz GShr GCur GBnd VDestroy GSplit GName GVEnd GInv GPerm PkOps.
From Stdlib Require Import Permutation.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG CX CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module UnpInst.
Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs (XTP segs)) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis OPS_plain : plain_table OPS.

Theorem g0_sound : forall pc, contract_sound segs OPS MP PB (G0.g0_contract pc).
Proof. intros pc. exact (G0.g0_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g2z_sound : forall pc, contract_sound segs OPS MP PB (G2Z.g2z_contract pc).
Proof. intros pc. exact (G2Z.g2z_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g2_sound : forall pc, contract_sound segs OPS MP PB (G2.g2_contract pc).
Proof. intros pc. exact (G2.g2_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g2b_sound : forall pc, contract_sound segs OPS MP PB (G2B.g2b_contract pc).
Proof. intros pc. exact (G2B.g2b_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g3p_sound : forall pc, contract_sound segs OPS MP PB (G3P.g3p_contract pc).
Proof. intros pc. exact (G3P.g3p_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem groom_sound : forall pc isV, contract_sound segs OPS MP PB (GRoom.groom_contract pc isV).
Proof. intros pc isV. exact (GRoom.groom_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g3r_sound : forall pc, contract_sound segs OPS MP PB (G3.g3r_contract pc).
Proof. intros pc. exact (G3.g3r_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g4_sound : forall pc rR rSZ, contract_sound segs OPS MP PB (G4.g4_contract pc rR rSZ).
Proof. intros pc rR rSZ. exact (G4.g4_sound pc rR rSZ segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem g1_sound : forall pc, contract_sound segs OPS MP PB (G1.g1_contract pc).
Proof. intros pc. exact (G1.g1_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gshr_sound : forall pc isV, contract_sound segs OPS MP PB (GShr.gshr_contract pc isV).
Proof. intros pc isV. exact (GShr.gshr_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gcap_sound : forall pc isV, contract_sound segs OPS MP PB (GCap.gcap_contract pc isV).
Proof. intros pc isV. exact (GCap.gcap_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gnz_sound : forall pc r, contract_sound segs OPS MP PB (GNz.gnz_contract pc r).
Proof. intros pc r. exact (GNz.gnz_sound pc r segs OPS MP PB). Qed.

Theorem gcur_sound : forall pc, contract_sound segs OPS MP PB (GCur.gcur_contract pc).
Proof. intros pc. exact (GCur.gcur_sound pc segs OPS MP PB). Qed.

Theorem gbnd_sound : forall pc r, contract_sound segs OPS MP PB (GBnd.gbnd_contract pc r).
Proof. intros pc r. exact (GBnd.gbnd_sound pc r segs OPS MP PB). Qed.

Theorem vd_sound : forall pc cur beg lim s ng, contract_sound segs OPS MP PB (VD.vd_contract segs pc cur beg lim s ng).
Proof. intros pc cur beg lim s ng. exact (VD.vd_sound segs pc cur beg lim s ng OPS OPS_plain MP PB). Qed.

Theorem gsplit_sound : forall pc idx n, contract_sound segs OPS MP PB (GSplit.gsplit_contract pc idx n).
Proof. intros pc idx n. exact (GSplit.gsplit_sound pc idx n segs OPS MP PB). Qed.

Theorem gname_sound : forall pc idx, contract_sound segs OPS MP PB (GName.gname_contract pc idx).
Proof. intros pc idx. exact (GName.gname_sound pc idx segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS MP PB). Qed.

Theorem ginv_sound : forall pc, contract_sound segs OPS MP PB (GInv.ginv_contract pc).
Proof. intros pc. exact (GInv.ginv_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Lemma xtp_perm3 : forall ca LB ws ws' m, Permutation ws ws' ->
  cw_holds (XTP segs) 3 ca LB ws m -> cw_holds (XTP segs) 3 ca LB ws' m.
Proof.
  intros ca LB ws ws' m HP H. change (PK.cw_pk_holds segs ca LB ws' m). change (PK.cw_pk_holds segs ca LB ws m) in H.
  unfold PK.cw_pk_holds in *. destruct (PK.decode_pk ca) as [u|]; [| exact H].
  destruct H as (g & ls & L & P & O & Wk & M & [SE EP] & CO). exists g, ls. split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [| split; [exact M| split]].
  3: { apply (PK.cost_pk_sub _ g ls ws); [exact CO|]. intros w Hw. exact (Permutation_in w (Permutation_sym HP) Hw). }
  2: { split.
       - apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw _. exact (Permutation_in w (Permutation_sym HP) Hw).
       - intros VB. destruct (EP VB) as (w & Hw & EW). exists w. split; [exact (Permutation_in w HP Hw)| exact EW]. }
  unfold PK.wins_pk in *. exact (Permutation_Forall HP Wk).
Qed.
Theorem gperm_sound : forall pc P1 P2, contract_sound segs OPS MP PB (GPerm.gperm_contract pc P1 P2).
Proof. intros pc P1 P2. exact (GPerm.gperm_sound pc P1 P2 segs IMGX AW (XTP segs) OPS HOPS MP PB xtp_perm3). Qed.
Theorem gperm_kinds_sound : forall pc k1 k2, contract_sound segs OPS MP PB (GPerm.gperm_kinds_contract pc k1 k2).
Proof. intros pc k1 k2. exact (gperm_sound pc (GPerm.is_kind k1) (GPerm.is_kind k2)). Qed.

Theorem gve_sound : forall pc k nf, contract_sound segs OPS MP PB (GVE.gve_contract pc k nf).
Proof. intros pc k nf. exact (GVE.gve_sound pc k nf segs OPS MP PB). Qed.

Section G6.
Variable MEMCPY_PC : int.
Hypothesis MEMCPY :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (mo : Model) (d s n : Z) (src junk : list byte) (K : TSet),
    PropExec.getr R 10%bv = Z_to_bv 64 d -> PropExec.getr R 11%bv = Z_to_bv 64 s -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    0 <= d < 2 ^ 64 -> 0 <= s < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    MState.ret_pc (PropExec.getr R 1%bv) = PropExec.getr R 1%bv ->
    Lib.Mem.bytes_at segs M s src -> length src = Z.to_nat n ->
    rw_cells segs M d [CB (Z.to_nat n) junk] ->
    (s + n <= d \/ d + n <= s) ->
    Lib.Mem.mem_inv segs M -> m_halted mo = None -> m_vm_lazy mo = [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte),
        (forall r, In r (G6.kept_regs) -> PropExec.getr R' r = PropExec.getr R r) -> PropExec.getr R' 10%bv = Z_to_bv 64 d ->
        munch [(d, d + n)] M M' -> wmono segs M M' -> Lib.Mem.mem_inv segs M' ->
        rw_cells segs M' d [CB (Z.to_nat n) src] -> Lib.Mem.bytes_at segs M' s src ->
        omono M M' ->
        realizes segs (mkCfg (MS R' F (PropExec.getr R 1%bv) fc None M' (seg_rom segs)) mo) K) ->
    realizes segs (mkCfg (MS R F (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None M (seg_rom segs)) mo) K.

Theorem g6_sound : forall isV, contract_sound segs OPS MP PB (G6.g6_contract MEMCPY_PC isV).
Proof. intros isV. exact (G6.g6_sound MEMCPY_PC isV segs IMGX AW (XTP segs) OPS HOPS MP PB OPS_plain MEMCPY). Qed.
End G6.

End Sound.
End UnpInst.
