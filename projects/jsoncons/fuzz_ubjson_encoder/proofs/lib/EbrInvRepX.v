(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA HeapIfaceAEx As0Tables ArtMem EbtInitCache EbtPopulate1 ArtRuns EbtCls EbtFp EbtClsRep ArtBridge EbrInv EbtFxQ EbrInvFreePure.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EbrInvRepX () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv6art_gs00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EbrInvFreePure?art_alloc_rep_bC13~~~I35stdpp4base5NoDup00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7art_run00C13~~~K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_alloc_repC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).

Section X.
Variable FSG : Type.
Definition art_rt_quar_x (bt bg : Z) (rn : art_run) (G : art_gs FSG) (M : word -> option byte) : Prop :=
  (exists f l, cellA M (rn_t rn + 80) 8 (Z.of_nat (length (g_qt FSG G))) /\ cellA M (rn_t rn + 88) 8 f /\ cellA M (rn_t rn + 96) 8 l
               /\ cellA M (rn_t rn + 104) 8 (art_batches_bytes (g_qt FSG G)) /\ art_batch_list M (g_qt FSG G) f l)
  /\ (exists f l, cellA M (0x142d70 + 160) 8 (Z.of_nat (length (g_qg FSG G))) /\ cellA M (0x142d70 + 168) 8 f /\ cellA M (0x142d70 + 176) 8 l
               /\ cellA M (0x142d70 + 184) 8 (art_batches_bytes (g_qg FSG G)) /\ art_batch_list M (g_qg FSG G) f l)
  /\ art_batches_bytes (g_qt FSG G) <= bt /\ art_batches_bytes (g_qg FSG G) <= bg
  /\ cellA M (0x142d70 + 152) 4 0
  /\ NoDup (map bt_addr (g_qt FSG G ++ g_qg FSG G))
  /\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) -> bt_items b <> [])
  /\ (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) ->
        (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CQuar (fst it + 16) (snd it))
        \/ (exists s, In s (g_sec FSG G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it))
  /\ NoDup (map fst (flat_map bt_items (g_qt FSG G ++ g_qg FSG G)))
  /\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) ->
        exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls FSG G 24)) w /\ g_st FSG G 24 w = CBatch).
Definition art_alloc_rep_x (bt bg : Z) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary FSG rn G M /\ art_rt_chunks FSG rn G LB M
  /\ art_rt_sec FSG rn G LB M /\ art_rt_quar_x bt bg rn G M /\ art_rt_depot FSG rn G M /\ art_rt_ia FSG G M /\ art_rt_blocks FSG rn G LB
  /\ art_rt_ghost FSG rn G M.

#[using="Type"] Lemma art_alloc_rep_x_b : forall b rn G LB M, art_alloc_rep_x b (2 ^ 28) rn G LB M = art_alloc_rep_b FSG b rn G LB M.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrInvRepX ()) ["X"] "h01Gh12LBh21Mh31bh42rnp;1p;2p;6p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@R1p4p710R2p8P0P1p4p7210R1p8P0p1001Tp4p710R0p8p,3FSGR3p4p300R4g0020R5p4p710p8P4g003:R4p4p710p8p1004Sp4p710R6P2p8P6P1p8P6P0p8P5j18Tg004hj27Tg005Hj13Tg005hj10Tg006Mj12Tg006kj11Tg007Nj16TP4j64Tg0080j25Tg008JR4g008h%831744#3g00:3#0#0#0R4#0#0#0#2#1%24#1#6[p-0P3f4f3f2f1f0E4'5W2W1W0W4W3o"). Qed.
#[using="Type"] Lemma art_alloc_rep_x_closed : forall rn G LB M, art_alloc_rep_x (2 ^ 20) (2 ^ 28) rn G LB M = art_alloc_rep FSG rn G LB M.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrInvRepX ()) ["X"] "h01Gh12LBh21Mh32rnp;1p;2p;5g0020j18Tg004hj27Tg005Hj13Tg005hj10Tg006Mj12Tg006kj11Tg007Nj16Tg00:Xj54Tg0080j25Tg008hp,3FSGR0#8g008JR1/71#3g00:3#0#0#0R1#0#0#0#2#1%21#1#6[p-0P0f3f2f1f0D4'5W2W1W0W3o"). Qed.

End X.
