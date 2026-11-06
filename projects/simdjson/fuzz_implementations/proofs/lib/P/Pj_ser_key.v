(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_key_a Pj_ser_key_b.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable isobj : list byte.
  Variables (i dp c l A : Z).
  Variable F : bvmap 5 word.
  Variable fc : bv 32.
  Hypothesis FRM : frm0 fc.
  Hypothesis OK : senv_ok E.
  Hypothesis HI : 1 <= i < e_n E.
  Hypothesis HT : e_T E i = tword t_str c.
  Hypothesis HSTR : str_at (e_S E) (e_sn E) c l.
  Hypothesis BUD : A + (3 + 6 * l) <= PJ_OUTMAX (e_len E).
  Hypothesis HK : disp_K E Q isobj (i + 1) dp (A + (3 + 6 * l)).

  Notation ESC := (Z_to_bv 64 PJ_ESC_TAB).
  Notation SPILL := (Z_to_bv 64 (e_SBUF E)).
  Notation DATA := (e_SBUF E + c + 4).
  Notation NET := (Z_to_bv 64 PJ_NE_TAB).

  Notation key_scan8 := (Pj_ser_key_b.key_scan8 HM HF E Q isobj i dp c l A F fc FRM OK HSTR BUD HK).

  Lemma key_head : forall (st : sbst) (s : PState) (m : mem) (spill0 : word)
      (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 : word),
    SERM E ESC spill0 isobj st s m -> sb_size st <= A ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3ff38 i dp (Z_to_bv 64 125) xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (e_TAPE E)) xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 NET
             xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HI HT HSTR BUD HK FRM.
    intros st s m spill0 xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof HSTR as (C0 & L0 & CL & LE & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & SB0 & SB1).
    pose proof (S_range E c OK) as BR0. pose proof (S_range E (c + 1) OK) as BR1.
    pose proof (S_range E (c + 2) OK) as BR2. pose proof (S_range E (c + 3) OK) as BR3.
    unfold le32 in LE.
    set (b0 := e_S E c) in *. set (b1 := e_S E (c + 1)) in *. set (b2 := e_S E (c + 2)) in *. set (b3 := e_S E (c + 3)) in *.

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3ff8c yra yt0 yt1 yt2 (Z_to_bv 64 (size + 1)) (Z_to_bv 64 size) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (e_SBUF E + c)) (Z_to_bv 64 b0)
               (Z_to_bv 64 b3) (Z_to_bv 64 c) NET (Z_to_bv 64 dp) (Z_to_bv 64 b1) (Z_to_bv 64 b2) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      zstep. zstep. zstep. zstep. step. step. zstep.

      zstep. zstep. zstep. zstep.
      assert (EL : Z.lor (Z.lor (Z.land (Z.shiftl b3 24) 18446744073709551615) (Z.land (Z.shiftl b2 16) 18446744073709551615))
                         (Z.lor (Z.land (Z.shiftl b1 8) 18446744073709551615) b0) = l).
      { rewrite !pj_land64 by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite lor4_le32 by lia. lia. }
      rewrite !EL.
      pose proof (land_m8_range l ltac:(lia)) as K8R. set (k8 := Z.land l 18446744073709551608) in *.

      zstep. step. step. pj_store_done. step. zstep. step.
      ser_close HSM6 OK.
      eapply evt_eq; [| eapply (key_scan8 (S (Z.to_nat l)) 0 k8 (mkSb buf5 (size + 1) cap5 blk5 fuel5))];
        [pj_st_eq| lia| lia| lia| lia| exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RDT. rewrite HT in RDT.
    assert (EA : Z.land (Z.land (tword t_str c) 18446744073709551615) 72057594037927935 = c).
    { pose proof (tword_range t_str c ltac:(unfold t_str; lia) ltac:(lia)) as TR.
      rewrite pj_land64 by lia. rewrite land_mask56 by lia. apply tval_tword. lia. }

    zstep. pjnorm. zstep. step. step. step. step. step. zstep. rewrite EA.

    step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (sbuf_read_mu E _ _ _ _ (c + 0) OK HREF MU WM ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0; fold b0 in RD0;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 1) OK HREF MU WM ltac:(lia)) as RD1; fold b1 in RD1;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 2) OK HREF MU WM ltac:(lia)) as RD2; fold b2 in RD2;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 3) OK HREF MU WM ltac:(lia)) as RD3; fold b3 in RD3 end.

    zstep. zstep. zstep. zstep. pjnorm. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      ser_close HSM3 OK.
      eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3ff84); [exact OK| exact HSM3| | lia| reflexivity|].
      { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      ser_open HSM4 OK.

      step. zstep.
      ser_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

End Proofs.

  Theorem key_proof : rmalloc_stmt -> rfree_stmt -> key_stmt.
  Proof.
    intros HM HF. unfold key_stmt.
    intros E Q spill isobj st s m F fc i c l dp A xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 OK HSM FRM HI HT HSTR ACC BUD HK.
    eapply (key_head HM HF E Q isobj i dp c l A F fc FRM OK HI HT HSTR BUD HK); [exact HSM| exact ACC].
  Qed.

End WithCeiling0.
