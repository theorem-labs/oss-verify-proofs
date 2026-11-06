(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/Reusable/YL0i.v (posts, contracts), lib/Reusable/YL05.v (lib_post_state) and lib/Reusable/YL06.v (call site) for a return value of the fuzz target of 0 or -1 *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRetD1.v, with its module paths changed; 76 of its 245 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs: the twin of lib/U/Reusable/YL0i_cfw.v (lib_contract_x_Rc), lib/U/Reusable/YL06_cfw.v (lib_site_x_R_cf) and lib/U/AgreeZlib.v (lib_contract_x_Rc_of_cg) (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/U/Prog/AgreeRetD1.v, with its module paths changed; 54 of its 69 lines of code are new or changed and 230 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/FrameSlotO.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import
  YK11 YK0i YM05 YO0d YO05 YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33 DriverSlots.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import
  ZTraceSpec ZComplete ZAllocator SlotTopG Contract FrameAPI OutForm FrameSlotG AllocSlots.
Import ListNotations.
Open Scope Z_scope.
Section BridgeO.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_pre_x_fd : forall stk empty L A regs mem md ra p n pl b,
  lib_pre_x B API stk empty L A regs mem md ra p n pl b -> fdchan (Z_to_bv 64 2) ch_stderr md.
Proof using.
  intros stk empty L A regs mem md ra p n pl b
    (_ & _ & _ & _ & _ & _ & _ & _ & Hfd & _). exact Hfd.
Qed.
Lemma lib_post_x_G_of_o : forall out G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_o B API out G stk L A regs mem md p n b l L' A' regs' mem' md' ->
  lib_post_x_G B API G out stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof using.
  intros out G stk L A regs mem md p n b l L' A' regs' mem' md'
    ((H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H11 & H12 & H13 & _ & H15 & H16 & _ & H17 & H18) & Ho).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 (conj Ho (conj H15 (conj H16 (conj H17 H18))))))))))))))))).
Qed.
Lemma lib_contract_x_G_of_o : forall f G R GI j pc ra empty stk,
  lib_contract_o B API f G R GI j pc ra empty stk -> lib_contract_x_G B API G R GI f j pc ra empty stk.
Proof using TBL.
  intros f G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre (lib_pre_x_fd stk empty L A regs mem md ra p n pl b Hpre) HGI HR
    (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_G_of_o (f pl) G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | exact HGI'].
Qed.
End BridgeO.
Lemma out_permitted : forall f, shape_permitted (out_shape f).
Proof. intros f pl fs K HK. exact (permitted_out_LIBK zallowed f pl fs K HK). Qed.
Lemma out_room_calls : forall f n k, @room_calls (out_shape f) n k SBD.
Proof.
  intros f n k. induction k as [|k IH]; cbn [room_calls lib_room lib_delta out_shape]; [exact I|].
  split; [first [exact I | unfold SBD, CAPMAX; cbn [sb_live sb_bytes sb_cap]; lia] | exact IH].
Qed.
Theorem plain_halts_of_frame_slot_o : forall (f : list byte -> list byte) (G : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_o fx rc (out_shape f) src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       f G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.ubsan_halts.
Proof.
  intros f G GI HG GIL GI0 H.
  apply (plain_halts_from_slot_G (out_shape f) G frame_RELRO GI f (out_permitted f)
    (fun data => out_room_calls f _ _) (fun a h => frame_G_src0 a (HG a h))).
  - exact frame_RELRO_src0.
  - exact GIL.
  - exact GI0.
  - intros rc fx j Hj.
    exact (lib_contract_x_G_of_o src0_msyms (@zlib_API rc) (zlib_tables rc) f G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
