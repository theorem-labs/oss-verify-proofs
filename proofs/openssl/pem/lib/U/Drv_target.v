(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Exit Printf_stdio_iface Fz_iface Driver_iface Drv_kit Drv_cli.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_ax Drv_facts.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require F_memcpy.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
(* [comment removed for export] *)
Ltac fix_sb :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call usegs m mm MU WM end end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma swrap32_id : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap. rewrite bv_wrap_small; [lia|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N (32 - 1)%N) with (2^31). change (2 ^ Z.of_N 32) with (2^32). lia.
Qed.

Lemma wz_eqb0 : forall z, 0 <= z < 2^64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = true -> z = 0.
Proof.
  intros z Hz H. apply bv_eqb_eq in H. apply (f_equal bv_unsigned) in H. rewrite !unsigned_lit in H by lia. exact H.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) : forall n (l : list A), Forall P l -> Forall P (skipn n l).
Proof. induction n as [|n IH]; intros [|x l] H; cbn; auto. inversion H; subst. apply IH. assumption. Qed.

(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

Section TR.
  (* [comment removed for export] *)
  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (B lo : Z).
  Notation usp := (bv_unsigned sp).
  Hypothesis INB : In (p, A, cap) LB.
  Hypothesis CR : Forall (fun c => 0 <= c < 256) content.
  Hypothesis LEN1 : zlength content <= cap.
  Hypothesis CAP : cap <= 2^26.
  Hypothesis L0 : 0 <= L.
  Hypothesis L6 : 6 + L <= zlength content.
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - RTARGET_RUN_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FREE0 : rfree_null_stmt.
  Variable C : cli_sig.                      (* [comment removed for export] *)
  Hypothesis INIT : rfuzz_init_stmt C.
  Hypothesis FUZZ : rfuzz_one_stmt C.
  Hypothesis EMIT : @emit_printf_stmt PState ps_so set_so_ps.
  Hypothesis FWXO : fwritex_stdout_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  (* [comment removed for export] *)
  Variable m0 : mem.

  Definition plen : Z := zlength content - 6 - L.
  Definition PAY : Z := A + 6 + L.
  Definition payload : list Z := skipn (Z.to_nat (6 + L)) content.
  Definition cfg : Z := if 0 <? L then znth content 2 else 0.
  Definition calls : Z := Z.land cfg 3 + 1.

  Lemma facts : 0 <= plen /\ plen + 6 <= 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4.
  Proof.
    unfold calls, cfg, plen, payload, zlength. rewrite length_skipn.
    assert (Hc : 0 <= (if 0 <? L then znth content 2 else 0) < 256).
    { destruct (0 <? L); [| lia]. pose proof (znth_range content 2 ltac:(unfold zlength in *; lia)) as Hin.
      exact (proj1 (Forall_forall _ _) CR _ Hin). }
    assert (0 <= Z.land (if 0 <? L then znth content 2 else 0) 3 <= 3).
    { set (c := if 0 <? L then znth content 2 else 0) in *. split; [apply Z.land_nonneg; lia|].
      replace (Z.land c 3) with (c mod 2^2) by (rewrite <- Z.land_ones by lia; reflexivity). pose proof (Z.mod_pos_bound c (2^2)); lia. }
    unfold zlength in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition FRAME (mm : mem) (j0 : list byte) : Prop :=
    rw_cells usegs mm (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  (* [comment removed for export] *)
  Definition PREW : list (Z * Z) :=
    [(usp + -128, usp); (RINIT_FLAG, RINIT_FLAG + 1); (RATEXIT, RATEXIT + 40); (RATEXIT_A0, RATEXIT_A0 + 8)].

  (* [comment removed for export] *)
  Lemma tr_pre : forall (Q : machine_state -> Prop) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (cdt thr sec : byte) (tm1 : word),
    stk usegs m lo usp -> mem_inv usegs m ->
    rw_cells usegs m RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells usegs m RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
    AXSTAT false m -> rw_cells usegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    (forall (m' : mem) (j0 : list byte) (t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        FRAME m' j0 -> stk usegs m' lo (usp + -80) ->
        munch PREW m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        rw_cells usegs m' RINIT_FLAG [C1 (Z_to_bv 8 1)] -> rw_cells usegs m' RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
        AXSTAT true m' -> rw_cells usegs m' RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
        evt usegs Q (MS (mkR (wz 0xe1a28) (wz (usp + -80)) gp tp t0' t1' t2' (wz plen) (wz PAY) a0' (wz (usp + -80)) a2' a3' a4' a5' a6' a7'
                              (wz L) (wz (A + 2)) (wz RINIT_FLAG) S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6')
                        F (wz LX_INIT) fc None m' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz (A + 2)) (wz L) (wz PAY) (wz plen) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (wz 0xe18c4) fc None m (seg_rom usegs)).
  Proof.
    intros until tm1. intros ST MI FLAG GOT [INCB [AX AX0]] LCH K. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, LX_INIT_STACK, LX_NEXT_STACK, LX_MSG_STACK, LX_MESSAGE_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *.
    unfold FRAME, PREW, RINIT_FLAG, RGOT_LLVMINIT, LX_INIT, RATEXIT, RATEXIT_A0, RAEF_INCB, RLIBC_HEAD, ax_cells in *. cbn [Z.add] in INCB, AX, AX0, K. cbv beta delta [MallocRep.wz] in *.
    pose proof (munch_refl [(usp + -128, usp); (3333616, 3333616 + 1); (0x3509b8, 0x3509b8 + 40); (0x350ad8, 0x350ad8 + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. carve_frame 80%nat ST.
    zidle_begin sp 80%Z MUz WMz.
    do 10 zstep.
    zidle_end MUz WMz.
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. if_true.
    zstep. zstep; fix_sb.                 (* [comment removed for export] *)
    zstep. zstep.                         (* [comment removed for export] *)
    zstep.                                (* [comment removed for export] *)
    name_sp sp (-80)%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut;
      [ eapply (atexit_guard_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo cdt thr sec tm1);
        [ match goal with Hs : bv_unsigned _ = usp + -80 |- _ => rewrite Hs end; hyp_by_addr
        | unfold RLIBC_HEAD; hyp_by_addr
        | unfold AXSTAT, RATEXIT, RATEXIT_A0, RAEF_INCB, ax_cells; cbn [Z.add]; split; [hyp_by_addr| split; hyp_by_addr]
        | hyp_by_addr
        | reflexivity
        | match goal with Hs : bv_unsigned _ = usp + -80 |- _ => rewrite Hs end; lia
        | lia ]
      | cbv beta delta [atexit_guard_post RATEXIT RATEXIT_A0]; cbn [Z.add]; post_call usegs mq ]
    end.
    all: unname_sp.
    match goal with H : AXSTAT true _ |- _ => destruct H as [INCB1 [AXC1 AXA1]] end.
    unfold RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells in INCB1, AXC1, AXA1. cbn [Z.add] in INCB1, AXC1, AXA1.
    (* [comment removed for export] *)
    zstep. if_true.
    zstep. zstep. zstep. if_false.        (* [comment removed for export] *)
    do 3 zstep.                           (* [comment removed for export] *)
    zstep.                                (* [comment removed for export] *)
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
        change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
    end.
    zstep. zstep.   (* [comment removed for export] *)
    lazymatch goal with FR0 : rw_cells usegs ?mq (usp + -80) (C8 ?w :: ?rest) |- _ =>
      assert (FR' : rw_cells usegs mq (usp + -80) (CB 8 (le8 w) :: rest))
        by (destruct FR0 as [[FRw FRb] FRr]; split; [split; [cbn; repeat split| exact FRb]| exact FRr]);
      clear FR0
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; try eassumption; try hyp_by_addr.
    unfold AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells. cbn [Z.add].
    split; [hyp_by_addr| split; hyp_by_addr].
  Qed.

  (* [comment removed for export] *)
  Lemma tr_mid : forall (Q : machine_state -> Prop) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    FRAME m j0 -> mem_inv usegs m -> bytes_at usegs m A (to_bytes content) ->
    (forall a0' : word, plen <> 0 ->
     evt usegs Q (MS (mkR (wz 0xe192c) (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz PAY) (wz plen) a1 a2 a3 a4 a5 a6 a7
                           (wz L) (wz (A + 2)) (wz RINIT_FLAG) (wz calls) S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                     F (wz RMALLOC_SYM) fc None m (seg_rom usegs))) ->
    (forall a0' : word, plen = 0 ->
     evt usegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz REMPTY) a0' a1 a2 a3 a4 a5 a6 a7
                           (wz 0) (wz (A + 2)) (wz RINIT_FLAG) (wz calls) S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                     F (wz 0xe1980) fc None m (seg_rom usegs))) ->
    evt usegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz PAY) a0 a1 a2 a3 a4 a5 a6 a7
                          (wz L) (wz (A + 2)) (wz RINIT_FLAG) S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (wz 0xe190c) fc None m (seg_rom usegs)).
  Proof.
    intros until j0. intros FR MI CT K1 K0. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    unfold FRAME, RINIT_FLAG, REMPTY, LX_EMPTY, RMALLOC_SYM in *. cbv beta delta [MallocRep.wz] in *.
    assert (RD : ov_read_bytes usegs m (wa (A + 2)) 1 = Some [Z_to_bv 8 (znth content 2)]).
    { eapply (bytes_at_read1 m A (to_bytes content) 2); [exact CT| lia| apply to_bytes_nth; apply znth_nth_error; lia| reflexivity]. }
    assert (HC3 : 0 <= Z.land cfg 3 <= 3).
    { split; [apply Z.land_nonneg; lia|]. replace (Z.land cfg 3) with (cfg mod 2^2) by (rewrite <- Z.land_ones by lia; reflexivity).
      pose proof (Z.mod_pos_bound cfg (2^2)); lia. }
    zstep. if_cases HL; zify_cond HL.
    - (* [comment removed for export] *)
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      rewrite EC in K1, K0.
      zstep. zstep. if_cases HP; zify_cond HP.
      + (* [comment removed for export] *) do 2 zstep. apply (K1 a0). lia.
      + do 2 zstep. apply (K0 a0). lia.
    - (* [comment removed for export] *)
      assert (EC : calls = Z.land (znth content 2) 3 + 1) by (unfold calls, cfg; replace (0 <? L) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      pose proof (proj1 (Forall_forall _ _) CR _ (znth_range content 2 ltac:(lia))) as C2. cbv beta in C2.
      do 3 zstep.
      replace (bv_unsigned (Z_to_bv 8 (znth content 2))) with (znth content 2) in * by (rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
      rewrite <- EC. zstep. if_cases HP; zify_cond HP.
      + do 2 zstep. apply (K0 (Z_to_bv 64 (Z.land (znth content 2) 3))). lia.
      + do 2 zstep. apply (K1 a0). lia.
  Qed.

  Lemma ps_get_set : forall (x : PState) so, ps_so (set_so_ps so x) = so. Proof. intros [? ? ? ?] so; reflexivity. Qed.
  Lemma ps_set_set : forall (x : PState) so so', set_so_ps so' (set_so_ps so x) = set_so_ps so' x. Proof. intros [? ? ? ?] so so'; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition TENVO (CLB X : list block) (D : Z) (st : PState) (m : mem) : Prop :=
    RHEAP st (CLB ++ X ++ LB) m /\ lx_statics m /\ (exists fl, lx_flags m fl) /\ stderr_wfile m
    /\ rauxv_ok m B /\ (exists errv : word, rw_cells usegs m (errno_addr tp) [C4 errv])
    /\ stdout_file m (ps_so st) /\ rdrv_pres LB usp m0 m /\ payload_ok m (X ++ LB) D payload /\ CLI C m CLB.
  Definition TENV (CLB X : list block) (D : Z) (st : PState) (m : mem) : Prop :=
    TENVO CLB X D st m /\ stk usegs m lo (usp + -80) /\ mem_inv usegs m /\ (exists ib : byte, rw_cells usegs m RINIT_FLAG [C1 ib])
    /\ AXSTAT true m                                                   (* [comment removed for export] *)
    /\ (exists j0, FRAME m j0).

  (* [comment removed for export] *)
  Lemma cli_agree : forall (P : Z -> Prop) m m' CLB, agree_on P m m' -> (forall a, cli_fp CLB a -> P a) -> CLI C m CLB -> CLI C m' CLB.
  Proof. intros P m m' CLB AG HP H. eapply (cli_stable C); [exact H|]. intros a Ha Hc. apply AG; [exact Ha| apply HP; exact Hc]. Qed.
  Lemma cli0_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, rin_ivs LXW_CLIENT a -> P a) -> CLI0 C m -> CLI0 C m'.
  Proof. intros P m m' AG HP H. eapply (cli0_stable C); [exact H|]. intros a Ha Hc. apply AG; [exact Ha| apply HP; exact Hc]. Qed.
  (* [comment removed for export] *)
  Lemma cliw_facts : forall a, rin_ivs LXW_CLIENT a ->
    0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ ~ stdout_addr a /\ ~ (3333616 <= a < 3333617)
    /\ ~ (3333620 <= a < 3333621) /\ ~ (3475896 <= a < 3475936) /\ ~ (3476184 <= a < 3476192).
  Proof.
    intros a Ha. unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in Ha. cbn in Ha.
    unfold ralloc_static, stdout_addr, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
  Qed.

  (* [comment removed for export] *)
  Definition S7L : word := wz (-2).

  (* [comment removed for export] *)
  Definition OWNED (X : list block) (D owned : Z) (o : option bptr) : Prop :=
    match o with
    | None => X = [] /\ owned = 0
    | Some pb => X = [(pb, D, plen)] /\ owned = D
    end.

  Notation POST := (rtarget_run_post C ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB B lo m0).

  (* [comment removed for export] *)
  Lemma tr_tail : forall CLB X D owned o st (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    TENV CLB X D st m -> OWNED X D owned o -> lx_flags0 m -> frm0 fc ->
    implM usegs (lib_free_opt raw_free o ;;; mret (if 0 =? 0 then 0 else 1)) st POST
      (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
               (wz owned) s3v (wz RINIT_FLAG) (wz 0) (wz 0) S7L S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz 0xe19c0) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros TE OW FL0 FRM. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    destruct TE as ((HP & LXS & [fl LXF] & SEW & AUX & [errv ERR] & SOF & PRES & POK & CLIm) & ST & MI & [ib FLAG] & AXT & [j0 FR]).
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, LX_NEXT_STACK, LX_MSG_STACK, LX_MESSAGE_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *.
    unfold FRAME, RINIT_FLAG, S7L in *. cbv beta delta [MallocRep.wz] in *.
    destruct o as [pb|]; cbn [OWNED] in OW; destruct OW as [-> ->]; cbn [lib_free_opt]; cbn [app] in HP.
    - (* [comment removed for export] *)
      unfold implM. iprefix. do 2 zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st POST msx) end.
      eapply implM_bind.
      { unfold RFREE_SYM in FREE. eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m st (CLB ++ (pb, D, plen) :: LB) pb D plen lo B errv);
          [exact HP| apply in_or_app; right; left; reflexivity| exact AUX| rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; exact ST| exact LOC| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
          | exact ERR| exact MI| exact TP| reflexivity]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & HP2).
      rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0xe19cc)) with (Z_to_bv 64 0xe19cc) by (symmetry; rpc).
      rewrite (lb_remove_mid pb D plen CLB LB (HND _ _ _ HP)) in HPR, HP2.
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG.
      (* [comment removed for export] *)
      assert (FR2 : rw_cells usegs m2 (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      { eapply rw_cells_agree; [exact AG| exact FR| intros a Ha; left; cbn in Ha; lia]. }
      apply implM_ret. do 3 zstep. do 9 zstep. zstep. zstep.
      replace (Z.land (Z.land (Z.b2z (0 <? 1) + -1) 18446744073709551615) 78) with 0 by reflexivity.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z].
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m2, errv, ib, CLB.
      split; [reflexivity|]. split; [lia|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HP2|].
      split; [eapply lx_statics_agree; [exact AG| | exact LXS]; intros a Ha; right; left; unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT in *; lia|].
      split; [exists (Z_to_bv 64 0); eapply lx_flags_agree; [exact AG| | exact FL0]; intros a Ha; right; left; unfold flags_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS in *; lia|].
      split; [eapply stderr_wfile_agree; [exact AG| | exact SEW]; intros a Ha; right; left; unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia|].
      split; [exact (RHEAP_ssp _ _ _ HP2)|].
      split; [rewrite ESO; eapply stdout_file_agree; [exact AG| | exact SOF]; intros a Ha; right; left; unfold stdout_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia|].
      split; [eapply rw_cells_agree; [exact AG| exact FLAG|]; intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
      split; [eapply (AXSTAT_agree _ _ _ _ AG); [| exact AXT]; intros a Ha; right; left; unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia|].
      split; [eapply rdrv_pres_trans; [exact PRES|]; apply rdrv_pres_of_heap; eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; apply in_or_app; right; exact Hb]|].
      eapply cli_agree; [exact AG| | exact CLIm]. intros a [(b & Hb & Hr)|Hw].
      + right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr].
      + right; left. pose proof (cliw_facts a Hw) as (W1 & W2 & _). split; [exact W1| exact W2].
    - (* [comment removed for export] *)
      apply implM_ret_bind. apply implM_ret. do 2 zstep.
      eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms1 ->.
      replace (ret_pc (Z_to_bv 64 0xe19cc)) with (Z_to_bv 64 0xe19cc) by (symmetry; rpc).
      do 3 zstep. do 9 zstep. zstep. zstep.
      replace (Z.land (Z.land (Z.b2z (0 <? 1) + -1) 18446744073709551615) 78) with 0 by reflexivity.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z app] in HP |- *.
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m, errv, ib, CLB.
      split; [reflexivity|]. split; [lia|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
      split; [exact ERR|]. split; [exact AUX|]. split; [exact HP|].
      split; [exact LXS|]. split; [exists (Z_to_bv 64 0); exact FL0|]. split; [exact SEW|]. split; [exact (RHEAP_ssp _ _ _ HP)|].
      split; [exact SOF|]. split; [exact FLAG|]. split; [exact AXT|]. split; [exact PRES| exact CLIm].
  Qed.

  (* [comment removed for export] *)
  Lemma lx_pres_of_munch : forall LB' SP X W m m',
    munch W m m' -> wmono usegs m m' -> (forall a, lx_client LB' SP X a -> outside W a) -> lx_pres LB' SP X m m'.
  Proof. intros LB' SP X W m m' MU WM HW. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| exact HW]. Qed.

  Notation KF o := (fun rc : Z => lib_free_opt raw_free o ;;; mret (if rc =? 0 then 0 else 1)).

  (* [comment removed for export] *)
  Ltac if_lit :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
    end.

  (* [comment removed for export] *)
  Lemma TENVO_incb : forall CLB X D st m m',
    TENVO CLB X D st m -> munch [(3333620, 3333620 + 1)] m m' -> wmono usegs m m' -> TENVO CLB X D st m'.
  Proof.
    intros CLB X D st m m' (HP & LXS & [fl LXF] & SEW & AUX & [errv ERR] & SOF & PRES & POK & CLIm) MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, LX_NEXT_STACK, LX_MSG_STACK, LX_MESSAGE_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, a <> 3333620 -> outside [(3333620, 3333620 + 1)] a) by (intros a Ha; cbn; lia).
    split. { eapply HFRAME; [exact HP| exact MU| exact WM|]. constructor; [| constructor]. right; left. cbn [fst snd].
             unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. apply OUT. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha. lia. }
    split. { exists fl. eapply lx_flags_agree; [exact AG| | exact LXF]. intros a Ha. apply OUT. unfold flags_addr, LX_FLAGS in Ha. lia. }
    split. { eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. apply OUT. unfold stderr_addr in Ha. lia. }
    split. { eapply rauxv_ok_agree; [exact AG| | | exact AUX]; intros a Ha; apply OUT; [lia|]. unfold RAUXV_CELL in Ha. lia. }
    split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply OUT. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. cbv delta [MallocRep.wz] in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia. }
    split. { eapply stdout_file_agree; [exact AG| | exact SOF]. intros a Ha. apply OUT. unfold stdout_addr in Ha. lia. }
    split. { eapply rdrv_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
             intros a [HX _]. apply OUT. intros ->. apply HX. unfold DRVW, RAEF_INCB. cbn. lia. }
    split.
    { destruct POK as (PB & PF & PD & PD2 & PD3 & PIN). split; [| split; [exact PF| split; [exact PD| split; [exact PD2| split; [exact PD3| exact PIN]]]]].
      eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. rewrite to_bytes_length in Ha. apply OUT.
      destruct PIN as [EP|(b & Hb & Hr1 & Hr2)]; [rewrite EP in Ha; cbn in Ha; lia|].
      pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_intror Hb))) as (R1 & R2 & R3 & R4 & R5). unfold zlength, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    (* [comment removed for export] *)
    eapply cli_agree; [exact AG| | exact CLIm]. intros a [(b & Hb & Hr)|Hw]; apply OUT.
    - pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_introl Hb))) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
    - pose proof (cliw_facts a Hw) as (_ & _ & _ & _ & W5 & _). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_loop : forall (k : nat) (rc0 : Z) CLB Lm X D owned o st (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (1 <= k)%nat -> Z.of_nat k <= 4 -> cl_rel CLB Lm ->
    TENV CLB X D st m -> OWNED X D owned o -> frm0 fc ->
    implM usegs (rc <- run_calls lops payload k rc0 Lm ;; (lib_free_opt raw_free o ;;; mret (if rc =? 0 then 0 else 1))) st POST
      (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
               (wz owned) s3v (wz RINIT_FLAG) (wz (Z.of_nat k)) (wz 0) S7L S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz 0xe1988) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until m; intros K1 K4 CLR TE OW FRM; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    destruct TE as (TO & ST & MI & [ib FLAG] & [INCB [AXC AXA]] & [j0 FR]).
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, LX_NEXT_STACK, LX_MSG_STACK, LX_MESSAGE_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    unfold FRAME, RINIT_FLAG, S7L in FR, FLAG |- *. unfold RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells in INCB, AXC, AXA. cbn [Z.add] in INCB, AXC, AXA.
    cbv beta delta [MallocRep.wz] in TP |- *.
    cbn [run_calls]. cbn [bind ret lops Target.ops out_stdout].
    apply implM_bind_assoc.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    pose proof (munch_refl [(3333620, 3333620 + 1)] m) as MUs. pose proof (wmono_refl usegs m) as WMs.
    zstep. zstep; fix_sb.
    lazymatch type of MUs with munch _ _ ?mq => pose proof (TENVO_incb CLB X D st m mq TO MUs WMs) as TO1 end. clear MUs WMs TO.
    destruct TO1 as (HP & LXS & [fl LXF] & SEW & AUX & [errv ERR] & SOF & PRES & POK & CLIm).
    do 3 zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st POST msx) end.
    eapply implM_bind.
    { unfold LX_FUZZ in FUZZ.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply (FUZZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq st CLB (X ++ LB) D payload fl lo B errv rr_guard Lm) end;
        [exact HP| exact LXS| exact LXF| exact SEW| exact (RHEAP_ssp _ _ _ HP)| exact AUX
        | rewrite unsigned_lit by lia; lia| exact B63| rewrite unsigned_lit by lia; exact ST| exact LOC| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; unfold LX_FUZZ_STACK, LX_NEXT_STACK, LX_MSG_STACK, LX_MESSAGE_STACK, LX_PRINTF_STACK; lia
        | exact ERR| exact TP| exact MI
        | rewrite unsigned_lit by lia; replace (usp + -80) with (usp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
        | exact POK| exact FRM| reflexivity| rewrite F3; reflexivity| exact CLIm| exact CLR]. }
    cbv beta. intros rc st1 ms1 PO.
    destruct PO as (CLB1 & ER1 & ER2 & (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1' & fc1 & mf & -> & LPE & -> & CLI1 & POK1)).
    destruct rc as [rcv L1]. cbn [fst snd] in ER1, ER2 |- *. subst rcv.
    destruct LPE as ((errv1 & ENV1) & FRM1 & LXP & ESO & EFA).
    destruct ENV1 as (HP1 & LXS1 & LXF1 & SEW1 & SSP1 & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1).
    rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in LXP by lia.
    replace (ret_pc (Z_to_bv 64 0xe199c)) with (Z_to_bv 64 0xe199c) by (symmetry; rpc).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP) as AG1.
    Ltac lxcli := split; [ unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY, LXW_STDERR, LX_STDERR_FILE; cbn; lia
                         | right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia ].
    assert (FR1 : rw_cells usegs mf (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG1| hyp_by_addr|]. intros a Ha. apply stack_client; [cbn in Ha; lia|].
      cbn in Ha. unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY, LXW_STDERR, LX_STDERR_FILE. cbn. lia. }
    assert (SOF1 : stdout_file mf (ps_so st1)).
    { rewrite ESO. eapply stdout_file_agree; [exact AG1| | exact SOF]. intros a Ha. apply stdout_addr_client; [exact Ha|].
      unfold stdout_addr in Ha. unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY, LXW_STDERR, LX_STDERR_FILE. cbn. lia. }
    assert (FLAG1 : rw_cells usegs mf 3333616 [C1 ib]).
    { eapply rw_cells_agree; [exact AG1| hyp_by_addr|]. intros a Ha. cbn in Ha. lxcli. }
    assert (INCB1 : rw_cells usegs mf 3333620 [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_agree; [exact AG1| hyp_by_addr|]. intros a Ha. cbn in Ha. lxcli. }
    assert (AXC1 : rw_cells usegs mf 3475896 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (repeat (Z_to_bv 8 0) 4);
                                            C8 (Z_to_bv 64 3475920); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2819748)]).
    { eapply rw_cells_agree; [exact AG1| hyp_by_addr|]. intros a Ha. cbn in Ha. lxcli. }
    assert (AXA1 : rw_cells usegs mf 3476184 [C8 (Z_to_bv 64 924204)]).
    { eapply rw_cells_agree; [exact AG1| hyp_by_addr|]. intros a Ha. cbn in Ha. lxcli. }
    assert (PRES1 : rdrv_pres LB usp m0 mf).
    { eapply rdrv_pres_trans; [exact PRES|]. apply rdrv_pres_of_lx. eapply lx_pres_weaken; [exact LXP| lia| intros b Hb; apply in_or_app; right; exact Hb| auto]. }
    assert (TO1 : TENVO CLB1 X D st1 mf).
    { split; [exact HP1|]. split; [exact LXS1|]. split; [exists (Z_to_bv 64 0); exact LXF1|]. split; [exact SEW1|]. split; [exact AUX1|].
      split; [exists errv1; exact ERR1|]. split; [exact SOF1|]. split; [exact PRES1|]. split; [exact POK1| exact CLI1]. }
    clear HP LXS LXF SEW AUX ERR SOF PRES POK CLIm FLAG INCB AXC AXA FR AG1 LXP.
    (* [comment removed for export] *)
    replace (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0 by reflexivity.
    apply implM_bind_assoc.
    unfold implM. iprefix.
    pose proof (munch_refl [(3333620, 3333620 + 1)] mf) as MUs. pose proof (wmono_refl usegs mf) as WMs.
    zstep. zstep; fix_sb.
    lazymatch type of MUs with munch _ _ ?mq => pose proof (TENVO_incb CLB1 X D st1 mf mq TO1 MUs WMs) as TO2 end. clear MUs WMs TO1.
    destruct TO2 as (HP & LXS & [fl' LXF] & SEW & AUX & [errv2 ERR] & SOF & PRES & POK & CLI2).
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 POST msx) end.
    eapply implM_bind.
    { eapply implM_keepsf; [| apply stdout_vprintf_keeps].
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply (EMIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1' fc1 mq st1 lo rr_guard) end;
        [apply ps_get_set| apply ps_set_set| exact FWXO| exact SOF| rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; hyp_by_addr| rewrite unsigned_lit by lia; unfold EMIT_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; lia| exact (RHEAP_ssp _ _ _ HP)| hyp_by_addr| exact FRM1]. }
    cbv beta. intros [] st2 ms2 [PO EBS].
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2' & fc2 & me & -> & MU2 & WM2 & MI2 & FRM2 & HF2 & ST2 & SOF2 & SSP2).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0xe19ac)) with (Z_to_bv 64 0xe19ac) by (symmetry; rpc).
    destruct (but_so_eq _ _ EBS) as (EM2 & EBRK2 & EFA2).
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
    assert (OUT2 : forall a, (usp + -80 <= a \/ (0x2c0000 <= a < 0x353000 /\ ~ stdout_addr a) \/ (a < lo /\ (a < 0x10000 \/ 0x353000 <= a))) ->
                             outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a).
    { intros a Ha. unfold stdout_addr in Ha. cbn. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (TE2 : TENV CLB1 X D st2 me).
    { unfold TENV, TENVO, FRAME, RINIT_FLAG, AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells. cbn [Z.add].
      repeat match goal with |- _ /\ _ => split end.
      - eapply RHEAP_ext; [| exact EM2| exact EBRK2].
        eapply HFRAME; [exact HP| exact MU2| exact WM2|].
        constructor; [left; cbn [fst]; exact LOC|]. constructor; [| constructor; [| constructor]];
          right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
      - eapply lx_statics_agree; [exact AG2| | exact LXS]. intros a Ha. apply OUT2. right; left.
        unfold lxs_addr, stdout_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT in *. lia.
      - exists (Z_to_bv 64 0). eapply lx_flags_agree; [exact AG2| | exact LXF]. intros a Ha. apply OUT2. right; left. unfold flags_addr, stdout_addr, LX_FLAGS in *. lia.
      - eapply stderr_wfile_agree; [exact AG2| | exact SEW]. intros a Ha. apply OUT2. right; left. unfold stderr_addr, stdout_addr in *. lia.
      - eapply rauxv_ok_agree; [exact AG2| | | exact AUX]; intros a Ha; apply OUT2; [left; lia| right; left]. unfold RAUXV_CELL, stdout_addr in *. lia.
      - exists errv2. eapply rw_cells_agree; [exact AG2| exact ERR|]. intros a Ha. apply OUT2. right; left. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. unfold stdout_addr. lia.
      - exact SOF2.
      - eapply rdrv_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU2| exact WM2|].
        intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUT2.
        + left. lia.
        + right; right. pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb))))) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
        + right; left. split; [exact Ha|]. intros Hso. apply HX. unfold stdout_addr in Hso. unfold DRVW, LXW_CLIENT. cbn. lia.
      - destruct POK as (PB & PF & PD & PD2 & PD3 & PIN). split; [| split; [exact PF| split; [exact PD| split; [exact PD2| split; [exact PD3| exact PIN]]]]].
        eapply bytes_at_agree; [exact AG2| exact PB|]. intros a Ha. rewrite to_bytes_length in Ha.
        destruct PIN as [EP|(b & Hb & Hr1 & Hr2)]; [rewrite EP in Ha; cbn in Ha; lia|].
        apply OUT2. right; right. pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_intror Hb))) as (R1 & R2 & R3 & R4 & R5). unfold zlength, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      - eapply cli_agree; [exact AG2| | exact CLI2]. intros a [(b & Hb & Hr)|Hw]; apply OUT2.
        + right; right. pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_introl Hb))) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
        + right; left. pose proof (cliw_facts a Hw) as (W1 & _ & W3 & _). split; [exact W1| exact W3].
      - exact ST2.
      - exact MI2.
      - exists ib. eapply rw_cells_agree; [exact AG2| exact FLAG1|]. intros a Ha. apply OUT2. right; left. cbn in Ha. unfold stdout_addr. lia.
      - eapply rw_cells_agree; [exact AG2| hyp_by_addr|]. intros a Ha. apply OUT2. right; left. cbn in Ha. unfold stdout_addr. lia.
      - eapply rw_cells_agree; [exact AG2| exact AXC1|]. intros a Ha. apply OUT2. right; left. cbn in Ha. unfold stdout_addr. lia.
      - eapply rw_cells_agree; [exact AG2| exact AXA1|]. intros a Ha. apply OUT2. right; left. cbn in Ha. unfold stdout_addr. lia.
      - exists j0. eapply rw_cells_agree; [exact AG2| exact FR1|]. intros a Ha. apply OUT2. left. cbn in Ha. lia. }
    assert (FL02 : lx_flags0 me).
    { eapply lx_flags_agree; [exact AG2| | exact LXF]. intros a Ha. apply OUT2. right; left. unfold flags_addr, stdout_addr, LX_FLAGS in *. lia. }
    (* [comment removed for export] *)
    unfold implM. iprefix. zstep.
    replace (bv_swrap 32 (bv_unsigned (wz 0) + -1)) with (-1) by (vm_compute; reflexivity).
    zstep. if_lit.
    zstep. rewrite swrap32_id by lia. replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    zstep. if_cases HK; zify_cond HK.
    - (* [comment removed for export] *)
      apply evt_done. apply (IH 0 CLB1 L1 X D owned o st2); [lia| lia| exact ER2| exact TE2| exact OW| exact FRM2].
    - (* [comment removed for export] *)
      apply evt_done. cbn [run_calls ret lops Target.ops]. apply implM_ret_bind.
      replace k with 0%nat by lia. cbn [Z.of_nat].
      eapply (tr_tail CLB1 X D owned o st2); [exact TE2| exact OW| exact FL02| exact FRM2].
  Qed.

  (* [comment removed for export] *)
  Lemma payload_bytes : forall m, bytes_at usegs m A (to_bytes content) -> bytes_at usegs m PAY (to_bytes payload).
  Proof.
    intros m H. unfold PAY, payload, to_bytes in *. rewrite <- (firstn_skipn (Z.to_nat (6 + L)) content) in H.
    rewrite map_app in H. apply bytes_at_app in H as [_ H]. rewrite length_map, length_firstn in H.
    replace (A + Z.of_nat (Init.Nat.min (Z.to_nat (6 + L)) (length content))) with (A + 6 + L) in H by (unfold zlength in L6; lia). exact H.
  Qed.

  (* [comment removed for export] *)
  Theorem tr_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (errv flags : word),
    RHEAP s LB m0 -> bytes_at usegs m0 A (to_bytes content) ->
    lx_statics m0 -> lx_flags m0 flags -> stderr_wfile m0 -> stdout_file m0 (ps_so s) ->
    rw_cells usegs m0 RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells usegs m0 RGOT_LLVMINIT [C8 (wz LX_INIT)] -> CLI0 C m0 ->
    AXSTAT false m0 ->
    rauxv_ok m0 B -> stk usegs m0 lo usp -> rw_cells usegs m0 (errno_addr tp) [C4 errv] -> mem_inv usegs m0 -> frm0 fc ->
    implM usegs (run cfg payload) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz (A + 2)) (wz L) (wz PAY) (wz plen) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz RTARGET_RUN) fc None m0 (seg_rom usegs)).
  Proof.
    intros until flags. intros HP0 CT0 LXS0 LXF0 SEW0 SOF0 FLAG0 GOT0 CLI00 AX0 AUX0 ST0 ERR0 MI0 FRM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOC as LOC'. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in LOC'; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    destruct (RHEAP_libc_head _ _ _ HP0) as (cdt & thr & sec & tm1 & LCH0).
    unfold run, Target.target_run, Harness.target_run. cbn [bind ret lib_malloc lib_free Target.ops].
    change (Target.ops raw_malloc raw_free ps_so set_so_ps) with lops. rewrite F3.
    change (Z.to_nat (Z.land cfg 3 + 1)) with (Z.to_nat calls).
    unfold RTARGET_RUN. apply implM_from_evt.
    eapply tr_pre; [exact ST0| exact MI0| exact FLAG0| exact GOT0| exact AX0| unfold RLIBC_HEAD; exact LCH0|].
    intros mi j0i t0' t1' t2' a0i a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FRi STi MUi WMi MIi FLAGi GOTi AXTi LCHi.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, LX_INIT_STACK, LX_NEXT_STACK, LX_MSG_STACK, LX_MESSAGE_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    unfold PREW, RINIT_FLAG, RATEXIT, RATEXIT_A0 in *. cbn [Z.add] in MUi. cbv beta delta [MallocRep.wz] in TP |- *.
    pose proof (agree_on_of_munch _ _ _ MUi WMi) as AGi.
    assert (OUTi : forall a, (usp <= a \/ (0x2c0000 <= a < 0x353000 /\ ~ (3333616 <= a < 3333617) /\ ~ (3475896 <= a < 3475936) /\ ~ (3476184 <= a < 3476192))
                              \/ (a < lo /\ (a < 0x10000 \/ 0x353000 <= a))) ->
                             outside [(usp + -128, usp); (3333616, 3333616 + 1); (3475896, 3475896 + 40); (3476184, 3476184 + 8)] a).
    { intros a Ha. cbn. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (HPi : RHEAP s LB mi).
    { eapply HFRAME; [exact HP0| exact MUi| exact WMi|]. constructor; [left; cbn [fst]; unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia|].
      constructor; [| constructor; [| constructor; [| constructor]]]; right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia. }
    pose proof (HBR _ _ _ _ HP0 INB) as BRA. cbn [blk_addr blk_size fst snd] in BRA. unfold rblock_range, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in BRA; try (pose proof alloc_ceiling_range as CEIL_RANGE__). destruct BRA as (BRA1 & BRA2 & BRA3 & BRA4 & BRA5).
    assert (CTi : bytes_at usegs mi A (to_bytes content)).
    { eapply bytes_at_agree; [exact AGi| exact CT0|]. intros a Ha. rewrite to_bytes_length in Ha. apply OUTi. right; right.
      pose proof (HBR _ _ _ _ HP0 INB) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R4, R5. unfold zlength, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (LXSi : lx_statics mi).
    { eapply lx_statics_agree; [exact AGi| | exact LXS0]. intros a Ha. apply OUTi. right; left.
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT in *. lia. }
    assert (LXFi : lx_flags mi flags).
    { eapply lx_flags_agree; [exact AGi| | exact LXF0]. intros a Ha. apply OUTi. right; left. unfold flags_addr, LX_FLAGS in *. lia. }
    assert (SEWi : stderr_wfile mi).
    { eapply stderr_wfile_agree; [exact AGi| | exact SEW0]. intros a Ha. apply OUTi. right; left. unfold stderr_addr in *. lia. }
    assert (SOFi : stdout_file mi (ps_so s)).
    { eapply stdout_file_agree; [exact AGi| | exact SOF0]. intros a Ha. apply OUTi. right; left. unfold stdout_addr in *. lia. }
    assert (AUXi : rauxv_ok mi B).
    { eapply rauxv_ok_agree; [exact AGi| | | exact AUX0]; intros a Ha; apply OUTi; [left; lia| right; left]. unfold RAUXV_CELL in *. lia. }
    assert (ERRi : rw_cells usegs mi (errno_addr tp) [C4 errv]).
    { eapply rw_cells_agree; [exact AGi| exact ERR0|]. intros a Ha. apply OUTi. right; left. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia. }
    assert (PRESi : rdrv_pres LB usp m0 mi).
    { eapply lx_pres_of_munch; [exact MUi| exact WMi|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUTi.
      - left. lia.
      - right; right. pose proof (HBR _ _ _ _ HP0 Hb) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      - right; left. split; [exact Ha|]. repeat split; intros Hi; apply HX; unfold DRVW, LXW_CLIENT, RINIT_FLAG, RAEF_INCB, RATEXIT, RATEXIT_A0; cbn; lia. }
    assert (CLI0i : CLI0 C mi).
    { eapply cli0_agree; [exact AGi| | exact CLI00]. intros a Hw. apply OUTi. right; left. pose proof (cliw_facts a Hw) as (W1 & _ & _ & W4 & _ & W6 & W7). split; [exact W1|]. split; [exact W4|]. split; [exact W6| exact W7]. }
    clear AGi OUTi HP0 CT0 LXS0 LXF0 SEW0 SOF0 FLAG0 GOT0 AX0 AUX0 ST0 ERR0 MI0 LCH0 CLI00.
    (* [comment removed for export] *)
    apply evt_done. cbv beta.
    eapply implM_bind.
    { unfold LX_INIT in INIT.
      eapply (INIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mi s LB flags lo B errv rr_guard);
        [exact HPi| exact LXSi| exact LXFi| exact SEWi| exact (RHEAP_ssp _ _ _ HPi)| exact AUXi
        | rewrite unsigned_lit by lia; lia| exact B63| rewrite unsigned_lit by lia; exact STi| exact LOC| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; unfold LX_INIT_STACK; lia
        | exact ERRi| exact TP| exact MIi
        | rewrite unsigned_lit by lia; replace (usp + -80) with (usp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
        | exact FRM| exact CLI0i]. }
    cbv beta. intros Lc st0 msi PO.
    destruct PO as (CLB & ECL & (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & Fi & fc1 & m1 & -> & LPE & _ & CLI1 & _)).
    destruct LPE as ((errv1 & ENV1) & FRM1 & LXP & ESO0 & EFA0).
    destruct ENV1 as (HP1 & LXS1 & LXF1z & SEW1 & SSP1 & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1).
    assert (LXF1 : lx_flags m1 flags) by exact LXF1z.
    rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in LXP by lia.
    replace (ret_pc (Z_to_bv 64 0xe1a28)) with (Z_to_bv 64 0xe1a28) by (symmetry; rpc).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP) as AG1.
    assert (NX : forall a, (usp + -80 <= a \/ 0x10000 <= a < 0x2c0000 \/ (3333616 <= a < 3333617) \/ (3333620 <= a < 3333621)
                            \/ (3475896 <= a < 3475936) \/ (3476184 <= a < 3476192) \/ stdout_addr a) -> ~ rin_ivs (LXW_CLIENT ++ [LXW_STDERR]) a).
    { intros a Ha. unfold stdout_addr in Ha. unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY, LXW_STDERR, LX_STDERR_FILE. cbn. lia. }
    assert (FR1 : FRAME m1 j0i).
    { unfold FRAME in *. eapply rw_cells_agree; [exact AG1| exact FRi|]. intros a Ha. apply stack_client; [cbn in Ha; lia|]. apply NX. cbn in Ha. lia. }
    assert (SOF1 : stdout_file m1 (ps_so st0)).
    { rewrite ESO0. eapply stdout_file_agree; [exact AG1| | exact SOFi]. intros a Ha. apply stdout_addr_client; [exact Ha|]. apply NX. right; right; right; right; right; right. exact Ha. }
    Ltac lxcli1 NX := split; [apply NX; lia| right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    assert (FLAG1 : rw_cells usegs m1 3333616 [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_agree; [exact AG1| exact FLAGi|]. intros a Ha. cbn in Ha. lxcli1 NX. }
    assert (AXT1 : AXSTAT true m1).
    { eapply (AXSTAT_agree _ _ _ _ AG1); [| exact AXTi]. intros a Ha. unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0 in Ha. lxcli1 NX. }
    assert (CT1 : bytes_at usegs m1 A (to_bytes content)).
    { eapply bytes_at_agree; [exact AG1| exact CTi|]. intros a Ha. rewrite to_bytes_length in Ha.
      apply (block_client LB _ _ (p, A, cap)); [exact INB| cbn [blk_addr blk_size fst snd]; unfold zlength in *; lia|].
      unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY, LXW_STDERR, LX_STDERR_FILE. cbn. unfold zlength in *. lia. }
    assert (PRES1 : rdrv_pres LB usp m0 m1).
    { eapply rdrv_pres_trans; [exact PRESi|]. apply rdrv_pres_of_lx. eapply lx_pres_weaken; [exact LXP| lia| auto| auto]. }
    assert (INB1 : In (p, A, cap) (CLB ++ LB)) by (apply in_or_app; right; exact INB).
    clear AG1 NX LXP FRi STi MUi WMi MIi FLAGi GOTi AXTi LCHi HPi CTi LXSi LXFi SEWi SOFi AUXi ERRi PRESi CLI0i.
    (* [comment removed for export] *)
    unfold implM. iprefix. zstep.
    eapply tr_mid; [exact FR1| exact MI1| exact CT1| |].
    - (* [comment removed for export] *)
      intros a0'' NZ. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
      cbv beta delta [MallocRep.wz]. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st0 POST msx) end.
      apply implM_bind_assoc. eapply implM_bind.
      { unfold RMALLOC_SYM in MALLOC.
        eapply (MALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fi fc1 m1 st0 (CLB ++ LB) plen lo B errv1);
          [exact HP1| exact AUX1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact LOC
          | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| exact ERR1| exact MI1| exact TP| reflexivity| lia]. }
      cbv beta. intros r st1 ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & RES).
      rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0xe192c)) with (Z_to_bv 64 0xe192c) by (symmetry; rpc).
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG2.
      Ltac cli := right; left; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP.
      assert (FR2 : rw_cells usegs m2 (usp + -80) [CB 8 j0i; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      { eapply rw_cells_agree; [exact AG2| exact FR1| intros a Ha; left; cbn in Ha; lia]. }
      assert (LXS2 : lx_statics m2).
      { eapply lx_statics_agree; [exact AG2| | exact LXS1]. intros a Ha. cli. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT in *. lia. }
      assert (LXF2 : lx_flags m2 flags).
      { eapply lx_flags_agree; [exact AG2| | exact LXF1]. intros a Ha. cli. unfold flags_addr, LX_FLAGS in *. lia. }
      assert (SEW2 : stderr_wfile m2).
      { eapply stderr_wfile_agree; [exact AG2| | exact SEW1]. intros a Ha. cli. unfold stderr_addr in *. lia. }
      assert (SOF2 : stdout_file m2 (ps_so st1)).
      { rewrite ESO. eapply stdout_file_agree; [exact AG2| | exact SOF1]. intros a Ha. cli. unfold stdout_addr in *. lia. }
      assert (FLAG2 : rw_cells usegs m2 3333616 [C1 (Z_to_bv 8 1)]).
      { eapply rw_cells_agree; [exact AG2| exact FLAG1|]. intros a Ha. cli. cbn in Ha. lia. }
      assert (AXT2 : AXSTAT true m2).
      { eapply (AXSTAT_agree _ _ _ _ AG2); [| exact AXT1]. intros a Ha. cli. unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0 in Ha. lia. }
      assert (CT2 : bytes_at usegs m2 A (to_bytes content)).
      { eapply bytes_at_agree; [exact AG2| exact CT1|]. intros a Ha. rewrite to_bytes_length in Ha. right; right. exists (p, A, cap). split; [exact INB1|]. cbn [blk_addr blk_size fst snd]. unfold zlength in *. lia. }
      assert (PRES2 : rdrv_pres LB usp m0 m2).
      { eapply rdrv_pres_trans; [exact PRES1|]. apply rdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; apply in_or_app; right; exact Hb]. }
      assert (CLI2 : CLI C m2 CLB).
      { eapply cli_agree; [exact AG2| | exact CLI1]. intros a [(b & Hb & Hr)|Hw].
        - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr].
        - right; left. pose proof (cliw_facts a Hw) as (W1 & W2 & _). split; [exact W1| exact W2]. }
      destruct r as [pb|].
      + (* [comment removed for export] *)
        destruct RES as (A' & junk & -> & BR & HP2 & BLK & _).
        pose proof BR as BR0. unfold rblock_range, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in BR0; try (pose proof alloc_ceiling_range as CEIL_RANGE__). destruct BR0 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
        unfold implM. iprefix. zstep. if_cases HA; [apply wz_eqb0 in HA; lia|].
        do 3 zstep. zstep.
        pose proof (payload_bytes _ CT2) as PB2.
        assert (SEP : PAY + plen <= A' \/ A' + plen <= PAY).
        { pose proof (HBD _ _ _ _ _ HP2 (or_intror _ INB1) (or_introl eq_refl)) as D. cbn [blk_id blk_addr blk_size fst snd] in D.
          pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
          assert (NE : p <> pb) by (intros E; apply NI; rewrite <- E; apply in_map_iff; exists (p, A, cap); split; [reflexivity| exact INB1]).
          specialize (D NE). unfold PAY, plen in *. unfold zlength in *. lia. }
        destruct AXT2 as [INCB2 [AXC2 AXA2]]. unfold RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells in INCB2, AXC2, AXA2. cbn [Z.add] in INCB2, AXC2, AXA2.
        eapply evt_cut.
        { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (to_bytes payload) junk);
            rewrite ?unsigned_lit by (unfold PAY, zlength in *; lia);
            [exact PB2| rewrite to_bytes_length; unfold zlength in F3; lia| exact BLK| exact SEP| exact MI2]. }
        cbv beta. intros ms3 PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & BLK3 & PB3).
        rewrite !unsigned_lit in MU3 by (unfold PAY, zlength in *; lia). rewrite !unsigned_lit in BLK3 by lia. rewrite !unsigned_lit in PB3 by (unfold PAY, zlength in *; lia).
        replace (ret_pc (Z_to_bv 64 0xe1944)) with (Z_to_bv 64 0xe1944) by (symmetry; rpc).
        pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
        assert (OUT3 : forall a, (0x10000 <= a < 0x353000 \/ lo <= a \/ in_block (CLB ++ LB) a) -> outside [(A', A' + plen)] a).
        { intros a Ha. cbn. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| lia|].
          pose proof (HBD _ _ _ _ _ HP2 (or_intror _ Hb) (or_introl eq_refl)) as D. cbn [blk_id blk_addr blk_size fst snd] in D.
          pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
          assert (NE : blk_id b <> pb) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
          specialize (D NE). lia. }
        Ltac cl3 OUT3 := apply OUT3; left.
        assert (TE3 : TENV CLB [(pb, A', plen)] A' st1 m3).
        { unfold TENV, TENVO, FRAME, RINIT_FLAG, AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells. cbn [app Z.add].
          repeat match goal with |- _ /\ _ => split end.
          - eapply RHEAP_perm; [eapply HFRAME; [exact HP2| exact MU3| exact WM3|]; constructor; [| constructor]; right; right; exists (pb, A', plen); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| apply Permutation_middle].
          - eapply lx_statics_agree; [exact AG3| | exact LXS2]. intros a Ha. cl3 OUT3. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT in *. lia.
          - exists flags. eapply lx_flags_agree; [exact AG3| | exact LXF2]. intros a Ha. cl3 OUT3. unfold flags_addr, LX_FLAGS in *. lia.
          - eapply stderr_wfile_agree; [exact AG3| | exact SEW2]. intros a Ha. cl3 OUT3. unfold stderr_addr in *. lia.
          - eapply rauxv_ok_agree; [exact AG3| | | exact AUX2]; intros a Ha; apply OUT3; [right; left; unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia| left]. unfold RAUXV_CELL in *. lia.
          - exists errv2. eapply rw_cells_agree; [exact AG3| exact ERR2|]. intros a Ha. cl3 OUT3. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia.
          - eapply stdout_file_agree; [exact AG3| | exact SOF2]. intros a Ha. cl3 OUT3. unfold stdout_addr in *. lia.
          - eapply rdrv_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU3| exact WM3|].
            intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUT3; [right; left; unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]| left; lia].
          - unfold payload_ok. destruct BLK3 as [[_ PBD] _]. cbn [cells_bytes cbytes] in PBD. rewrite app_nil_r in PBD.
            split; [exact PBD|]. split; [unfold payload; apply Forall_skipn; exact CR|]. split; [lia|]. split; [lia|]. split; [lia|].
            right. exists (pb, A', plen). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
          - eapply cli_agree; [exact AG3| | exact CLI2]. intros a [(b & Hb & Hr)|Hw]; apply OUT3.
            + right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr].
            + left. pose proof (cliw_facts a Hw) as (W1 & _). lia.
          - eapply stk_agree; [exact AG3| exact ST2| intros a Ha; apply OUT3; right; left; lia].
          - exact MI3.
          - exists (Z_to_bv 8 1). eapply rw_cells_agree; [exact AG3| exact FLAG2|]. intros a Ha. cl3 OUT3. cbn in Ha. lia.
          - eapply rw_cells_agree; [exact AG3| exact INCB2|]. intros a Ha. cl3 OUT3. cbn in Ha. lia.
          - eapply rw_cells_agree; [exact AG3| exact AXC2|]. intros a Ha. cl3 OUT3. cbn in Ha. lia.
          - eapply rw_cells_agree; [exact AG3| exact AXA2|]. intros a Ha. cl3 OUT3. cbn in Ha. lia.
          - exists j0i. eapply rw_cells_agree; [exact AG3| exact FR2|]. intros a Ha. apply OUT3. right; left. cbn in Ha. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
        zstep. zstep. zstep. zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 POST msx) end.
        apply implM_ret_bind. replace calls with (Z.of_nat (Z.to_nat calls)) at 2 by lia.
        apply (tr_loop (Z.to_nat calls) 0 CLB Lc [(pb, A', plen)] A' A' (Some pb) st1); [lia| lia| exact ECL| exact TE3| split; reflexivity| exact FRM1].
      + (* [comment removed for export] *)
        destruct RES as [-> HP2].
        apply implM_ret_bind. apply implM_ret. zstep. if_true. zstep. zstep. do 9 zstep. zstep. zstep.
        release_frame FR2 ST2 (bv_unsigned sp).
        apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z].
        exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, Fi, fc1, m2, errv2, (Z_to_bv 8 1), CLB.
        split; [reflexivity|]. split; [lia|]. split; [exact MI2|]. split; [exact FRM1|]. split; [exact ST2|].
        split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HP2|].
        split; [exact LXS2|]. split; [exists flags; exact LXF2|]. split; [exact SEW2|]. split; [exact (RHEAP_ssp _ _ _ HP2)|]. split; [exact SOF2|]. split; [exact FLAG2|]. split; [exact AXT2|]. split; [exact PRES2| exact CLI2].
    - (* [comment removed for export] *)
      intros a0'' EZ. rewrite (proj2 (Z.eqb_eq _ _) EZ).
      cbv beta delta [MallocRep.wz]. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st0 POST msx) end.
      apply implM_ret_bind.
      assert (EP : payload = []) by (destruct payload; [reflexivity| unfold zlength in F3; cbn in F3; lia]).
      replace calls with (Z.of_nat (Z.to_nat calls)) at 2 by lia.
      apply (tr_loop (Z.to_nat calls) 0 CLB Lc [] REMPTY 0 None st0); [lia| lia| exact ECL| | split; reflexivity| exact FRM1].
      unfold TENV, TENVO, FRAME, RINIT_FLAG. cbn [app].
      split; [| split; [exact ST1| split; [exact MI1| split; [exists (Z_to_bv 8 1); exact FLAG1| split; [exact AXT1| exists j0i; exact FR1]]]]].
      split; [exact HP1|]. split; [exact LXS1|]. split; [exists flags; exact LXF1|]. split; [exact SEW1|]. split; [exact AUX1|].
      split; [exists errv1; exact ERR1|]. split; [exact SOF1|]. split; [exact PRES1|]. split; [| exact CLI1].
      rewrite EP. unfold payload_ok, REMPTY, LX_EMPTY, zlength. cbn [to_bytes map length Z.of_nat].
      split; [apply bytes_at_nil; lia|]. split; [constructor|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
  Qed.
End TR.

(* [comment removed for export] *)
Theorem rtarget_run_proof : forall C : cli_sig,
  rmalloc_stmt -> rfree_stmt -> rfree_null_stmt -> rfuzz_init_stmt C -> rfuzz_one_stmt C -> @emit_printf_stmt PState ps_so set_so_ps -> fwritex_stdout_stmt ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtarget_run_stmt C.
Proof.
  intros C MALLOC FREE FREE0 INIT FUZZ EMIT FWXO HFRAME HBR HND HBD.
  unfold rtarget_run_stmt. intros until flags.
  intros HP INB CT CR LEN1 CAP L0 L6 LXS LXF SEW SSP SOF FLAG GOT CLI00 AX AUX SPB B63 ST LOC LOG LOSP ERR TP MI FRM SP16 -> -> -> ->.
  eapply (tr_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB p A cap L content B lo
            INB CR LEN1 CAP L0 L6 SPB B63 LOC LOG LOSP TP SP16 MALLOC FREE FREE0 C INIT FUZZ EMIT FWXO HFRAME HBR HND HBD m);
    eassumption.
Qed.
End WithCeiling0.
