(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit X_atexit Exit_defs Printf_stdio_iface Lib_iface Driver_iface Drv_kit Drv_facts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require F_memcpy Lib_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ctusegs := ImageCt.ctusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
(* [comment removed for export] *)
Ltac fix_sb :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
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
      unfold zidle in *; transport_after_call ctusegs m mm MU WM end end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
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
  Hypothesis INIT : rinit_stmt.
  Hypothesis FUZZ : rfuzz_one_stmt.
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
    rw_cells ctusegs mm (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  (* [comment removed for export] *)
  Definition FRAME_INIT (mm : mem) : Prop :=
    rw_cells ctusegs mm (usp + -80) [C8 (wz LX_AEF_ARGV); C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  (* [comment removed for export] *)
  Definition WPRE : list (Z * Z) := [(usp + -128, usp); (RINIT_FLAG, RINIT_FLAG + 1); (0x353278, 0x3532a0); (0x353398, 0x3533a0)].

  (* [comment removed for export] *)
  Lemma tr_pre : forall (Q : machine_state -> Prop) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
    stk ctusegs m lo usp -> mem_inv ctusegs m ->
    rw_cells ctusegs m RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells ctusegs m RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
    rw_cells ctusegs m 0x353278 (atexit_cells (Z_to_bv 8 0) p1 p2 0 0 0 0) -> rw_cells ctusegs m 0x353398 [C8 (wz 0)] ->
    rw_cells ctusegs m 0x3534b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    (forall (m' : mem) t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        FRAME_INIT m' -> stk ctusegs m' lo (usp + -80) ->
        munch WPRE m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' ->
        rw_cells ctusegs m' RINIT_FLAG [C1 (Z_to_bv 8 1)] -> rw_cells ctusegs m' RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
        rw_cells ctusegs m' 0x353278 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x353290 0 0x2b2ef0) -> rw_cells ctusegs m' 0x353398 [C8 (wz 0xe2454)] ->
        evt ctusegs Q (MS (mkR (wz 0xe2450) (wz (usp + -80)) gp tp t0' t1' t2' (wz plen) (wz PAY) (wz LX_AEF_ARGC) (wz (usp + -80)) a2' a3' a4' a5' a6' a7'
                              (wz L) (wz (A + 2)) (wz RINIT_FLAG) S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6')
                        F (wz LX_INIT) fc None m' (seg_rom ctusegs))) ->
    evt ctusegs Q (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz (A + 2)) (wz L) (wz PAY) (wz plen) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (wz 0xe22ec) fc None m (seg_rom ctusegs)).
  Proof.
    intros until tm1. intros ST MI FLAG GOT ATX ATA LCH K. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LIB_STACK_lo as LSL. pose proof LIB_STACK_hi as LSH.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    unfold FRAME_INIT, WPRE, RINIT_FLAG, RGOT_LLVMINIT, LX_INIT, LX_AEF_ARGC, LX_AEF_ARGV, atexit_cells in *. cbv beta delta [MallocRep.wz] in *.
    pose proof (munch_refl [(usp + -128, usp); (3344048, 3344048 + 1); (0x353278, 0x3532a0); (0x353398, 0x3533a0)] m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    zstep. carve_frame 80%nat ST.
    zidle_begin sp 80%Z MUz WMz.
    do 10 zstep.
    zidle_end MUz WMz.
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. if_true.
    (* [comment removed for export] *)
    zstep. zstep; fix_sb. do 4 zstep.
    call_sp (atexit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p1 p2 0 0 (Z_to_bv 64 0) cdt thr sec tm1);
      [exact ST| exact ATX| exact ATA| exact LCH| exact MI| lia| lia|].
    rename PC into ST. rename PC0 into ATX. rename POST into ATA. unfold atexit_cells in ATX.

    (* [comment removed for export] *)
    zstep. if_true.
    do 2 zstep. zstep. if_false.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
                  change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store end).      (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma tr_mid : forall (Q : machine_state -> Prop) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    FRAME m j0 -> mem_inv ctusegs m -> bytes_at ctusegs m A (to_bytes content) ->
    (forall a0' : word, plen <> 0 ->
     evt ctusegs Q (MS (mkR (wz 0xe2354) (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz PAY) (wz plen) a1 a2 a3 a4 a5 a6 a7
                           (wz L) (wz (A + 2)) (wz RINIT_FLAG) (wz calls) S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                     F (wz RMALLOC_SYM) fc None m (seg_rom ctusegs))) ->
    (forall a0' : word, plen = 0 ->
     evt ctusegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz REMPTY) a0' a1 a2 a3 a4 a5 a6 a7
                           (wz 0) (wz (A + 2)) (wz RINIT_FLAG) (wz calls) S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                     F (wz 0xe23a8) fc None m (seg_rom ctusegs))) ->
    evt ctusegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz PAY) a0 a1 a2 a3 a4 a5 a6 a7
                          (wz L) (wz (A + 2)) (wz RINIT_FLAG) S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (wz 0xe2334) fc None m (seg_rom ctusegs)).
  Proof.
    intros until j0. intros FR MI CT K1 K0. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    unfold FRAME, RINIT_FLAG, REMPTY, LX_EMPTY, RMALLOC_SYM in *. cbv beta delta [MallocRep.wz] in *.
    assert (RD : ov_read_bytes ctusegs m (wa (A + 2)) 1 = Some [Z_to_bv 8 (znth content 2)]).
    { eapply (bytes_at_read1 m A (to_bytes content) 2); [exact CT| lia| apply to_bytes_nth; apply znth_nth_error; lia| reflexivity]. }
    assert (HC3 : 0 <= Z.land cfg 3 <= 3).
    { split; [apply Z.land_nonneg; lia|]. replace (Z.land cfg 3) with (cfg mod 2^2) by (rewrite <- Z.land_ones by lia; reflexivity).
      pose proof (Z.mod_pos_bound cfg (2^2)); lia. }
    zstep. if_cases HL; zify_cond HL.
    - (* [comment removed for export] *)
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      rewrite EC in K1, K0.
      zstep. zstep. if_cases HP; zify_cond HP.
      + (* [comment removed for export] *) do 3 zstep. apply (K1 a0). lia.
      + do 2 zstep. apply (K0 a0). lia.
    - (* [comment removed for export] *)
      assert (EC : calls = Z.land (znth content 2) 3 + 1) by (unfold calls, cfg; replace (0 <? L) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      pose proof (proj1 (Forall_forall _ _) CR _ (znth_range content 2 ltac:(lia))) as C2. cbv beta in C2.
      do 3 zstep.
      replace (bv_unsigned (Z_to_bv 8 (znth content 2))) with (znth content 2) in * by (rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
      rewrite <- EC. zstep. if_cases HP; zify_cond HP.
      + do 2 zstep. apply (K0 (Z_to_bv 64 (Z.land (znth content 2) 3))). lia.
      + do 3 zstep. apply (K1 a0). lia.
  Qed.

  Lemma ps_get_set : forall (x : PState) so, ps_so (set_so_ps so x) = so. Proof. intros [? ? ? ?] so; reflexivity. Qed.
  Lemma ps_set_set : forall (x : PState) so so', set_so_ps so' (set_so_ps so x) = set_so_ps so' x. Proof. intros [? ? ? ?] so so'; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ATBL (m : mem) : Prop :=
    exists p1 p2 : list byte,
      rw_cells ctusegs m 0x353278 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x353290 0 0x2b2ef0)
      /\ rw_cells ctusegs m 0x353398 [C8 (wz 0xe2454)].
  Definition atbl_addr (a : Z) : Prop := (0x353278 <= a < 0x3532a0) \/ (0x353398 <= a < 0x3533a0).

  Lemma ATBL_st : forall m, ATBL m -> rw_cells ctusegs m RAEF_INCB [C1 (Z_to_bv 8 0)] -> atexit_cells_st true m.
  Proof.
    intros m (p1 & p2 & H1 & H2) H3. exists p1, p2, 1, 0x353290, 0x2b2ef0, 0xe2454. unfold RAEF_INCB in H3. cbv delta [MallocRep.wz] in H2.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. cbn. repeat split; reflexivity.
  Qed.

  Lemma ATBL_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, atbl_addr a -> P a) -> ATBL m -> ATBL m'.
  Proof.
    intros P m m' AG HP (p1 & p2 & H1 & H2). exists p1, p2. unfold atbl_addr in HP.
    split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; unfold atexit_cells in Ha; cbn in Ha; lia]).
  Qed.

  (* [comment removed for export] *)
  Definition TENV (icb : byte) (ls : LS) (LW X : list block) (D : Z) (st : PState) (m : mem) : Prop :=
    RHEAP st (X ++ LW ++ LB) m /\ lib_inv ls m LW /\ ossl_exit_cells m /\ lx_statics m /\ stderr_wfile m
    /\ rauxv_ok m B /\ stk ctusegs m lo (usp + -80) /\ (exists errv : word, rw_cells ctusegs m (errno_addr tp) [C4 errv])
    /\ mem_inv ctusegs m /\ stdout_file m (ps_so st) /\ (exists ib : byte, rw_cells ctusegs m RINIT_FLAG [C1 ib])
    /\ (exists j0, FRAME m j0) /\ rdrv_pres LB usp m0 m /\ payload_ok m (X ++ LB) D payload
    /\ ATBL m /\ rw_cells ctusegs m RAEF_INCB [C1 icb].

  (* [comment removed for export] *)
  Definition OWNED (X : list block) (D owned : Z) (o : option bptr) : Prop :=
    match o with
    | None => X = [] /\ owned = 0
    | Some pb => X = [(pb, D, plen)] /\ owned = D
    end.

  Notation POST := (rtarget_run_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB B lo m0).

  (* [comment removed for export] *)
  Lemma tr_tail : forall ls LW X D owned o st (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s5v s7v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    TENV (Z_to_bv 8 0) ls LW X D st m -> OWNED X D owned o -> frm0 fc ->
    implM ctusegs (lib_free_optG o ;;; mret (if 0 =? 0 then 0 else 1)) st POST
      (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
               (wz owned) s3v (wz RINIT_FLAG) s5v (wz 0) s7v S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz 0xe23e8) fc None m (seg_rom ctusegs)).
  Proof.
    intros until m. intros TE OW FRM. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    destruct TE as (HP & LINV & OSC & LXS & SEW & AUX & ST & [errv ERR] & MI & SOF & [ib FLAG] & [j0 FR] & PRES & POK & ATB & INCB).
    pose proof LIB_STACK_lo as LSL. pose proof LIB_STACK_hi as LSH.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    unfold FRAME, RINIT_FLAG in *. cbv beta delta [MallocRep.wz] in *.
    destruct o as [pb|]; cbn [OWNED] in OW; destruct OW as [-> ->]; cbn [lib_free_optG].
    - (* [comment removed for export] *)
      unfold implM. iprefix. do 3 zstep. apply evt_done.      (* [comment removed for export] *)
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm st POST msx) end.
      eapply implM_bind.
      { unfold RFREE_SYM in FREE. eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m st ([(pb, D, plen)] ++ LW ++ LB) pb D plen lo B errv);
          [exact HP| left; reflexivity| exact AUX| rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; exact ST| exact LOC| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
          | exact ERR| exact MI| exact TP| reflexivity]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & HP2).
      rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0xe23f4)) with (Z_to_bv 64 0xe23f4) by (symmetry; rpc).
      rewrite (lb_remove_head pb D plen (LW ++ LB) (HND _ _ _ HP)) in HPR, HP2.
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG.
      (* [comment removed for export] *)
      assert (FR2 : rw_cells ctusegs m2 (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      { eapply rw_cells_agree; [exact AG| exact FR| intros a Ha; left; cbn in Ha; lia]. }
      assert (ATS2 : atexit_cells_st true m2).
      { apply ATBL_st.
        - eapply ATBL_agree; [exact AG| | exact ATB]. intros a Ha. right; left. unfold atbl_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
        - eapply rw_cells_agree; [exact AG| exact INCB|]. intros a Ha. right; left. unfold RAEF_INCB in Ha. cbn in Ha. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
      apply implM_ret. do 3 zstep. do 9 zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z].
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m2, errv, ib.
      split; [reflexivity|]. split; [lia|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|]. split; [exists LW; exact HP2|].
      split; [eapply ossl_exit_cells_agree; [exact AG| | exact OSC]; intros a Ha; right; left; apply ossl_exit_addr_client; exact Ha|].
      split; [eapply lx_statics_agree; [exact AG| | exact LXS]; intros a Ha; right; left; unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_GOT_STDERR, LX_STDERR_PTR in *; lia|].
      split; [eapply stderr_wfile_agree; [exact AG| | exact SEW]; intros a Ha; right; left; unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia|].
      split; [exact (RHEAP_ssp _ _ _ HP2)|].
      split; [rewrite ESO; eapply stdout_file_agree; [exact AG| | exact SOF]; intros a Ha; right; left; unfold stdout_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *; lia|].
      split; [eapply rw_cells_agree; [exact AG| exact FLAG|]; intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
      split; [exact ATS2|].
      eapply rdrv_pres_trans; [exact PRES|]. apply rdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; apply in_or_app; right; exact Hb].
    - (* [comment removed for export] *)
      apply implM_ret_bind. apply implM_ret. do 3 zstep.      (* [comment removed for export] *)
      eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms1 ->.
      replace (ret_pc (Z_to_bv 64 0xe23f4)) with (Z_to_bv 64 0xe23f4) by (symmetry; rpc).
      do 3 zstep. do 9 zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z app] in HP |- *.
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m, errv, ib.
      split; [reflexivity|]. split; [lia|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
      split; [exact ERR|]. split; [exact AUX|]. split; [exists LW; exact HP|].
      split; [exact OSC|].
      split; [exact LXS|]. split; [exact SEW|]. split; [exact (RHEAP_ssp _ _ _ HP)|].
      split; [exact SOF|]. split; [exact FLAG|]. split; [apply ATBL_st; [exact ATB| exact INCB]|]. exact PRES.
  Qed.

  (* [comment removed for export] *)
  Lemma lx_pres_of_munch : forall LB' SP X W m m',
    munch W m m' -> wmono ctusegs m m' -> (forall a, lx_client LB' SP X a -> outside W a) -> lx_pres LB' SP X m m'.
  Proof. intros LB' SP X W m m' MU WM HW. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| exact HW]. Qed.

  (* [comment removed for export] *)
  Lemma TENV_frame : forall W icb icb' ls LW X D st st' m m',
    TENV icb ls LW X D st m ->
    munch W m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' ->
    (forall a, (usp + -80 <= a \/ (0x2c2000 <= a < 0x355000 /\ ~ stdout_addr a /\ ~ (0x3306b4 <= a < 0x3306b5))
                \/ (a < lo /\ (a < 0x10000 \/ 0x355000 <= a))) -> outside W a) ->
    RHEAP st' (X ++ LW ++ LB) m' -> stk ctusegs m' lo (usp + -80) -> stdout_file m' (ps_so st') -> rw_cells ctusegs m' RAEF_INCB [C1 icb'] ->
    TENV icb' ls LW X D st' m'.
  Proof.
    intros W icb icb' ls LW X D st st' m m' TE MU2 WM2 MI2 OUT2 HP2 ST2 SOF2 INCB2.
    destruct TE as (HP1 & LINV1 & OSC1 & LXS1 & SEW1 & AUX1 & ST1 & [errv1 ERR1] & MI1 & SOF1 & [ib FLAG1] & [j0 FR1] & PRES1 & POK1 & ATB1 & INCB1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (NLW : forall a, rin_ivs LIBW a -> 0x2c2000 <= a < 0x355000 /\ ~ ralloc_static a /\ ~ drv_addr a) by (exact LIBW_img).
    pose proof LIB_STACK_lo as LSL. pose proof LIB_STACK_hi as LSH.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
    unfold TENV, FRAME, RINIT_FLAG in *.
    split; [exact HP2|].
    split. { (* [comment removed for export] *)
      eapply lib_inv_agree; [exact LINV1|]. eapply agree_on_mono; [exact AG2|]. intros a [Hi|(b & Hb & Hr)]; apply OUT2.
      + right; left. destruct (NLW _ Hi) as (Hr & _ & Hd). split; [exact Hr|]. split; [intros Hso; apply Hd; left; exact Hso|].
        intros Hf. apply Hd. unfold drv_addr, RINIT_FLAG. do 5 right. left. lia.
      + right; right. pose proof (HBR _ _ _ _ HP1 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb))))) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    split. { eapply ossl_exit_cells_agree; [exact AG2| | exact OSC1]. intros a Ha. apply OUT2. right; left.
             unfold ossl_exit_addr, OSSL_BASE_INITED, stdout_addr in *. lia. }
    split. { eapply lx_statics_agree; [exact AG2| | exact LXS1]. intros a Ha. apply OUT2. right; left.
             unfold lxs_addr, stdout_addr, LX_GOT_STDERR, LX_STDERR_PTR in *. lia. }
    split. { eapply stderr_wfile_agree; [exact AG2| | exact SEW1]. intros a Ha. apply OUT2. right; left. unfold stderr_addr, stdout_addr in *. lia. }
    split. { eapply rauxv_ok_agree; [exact AG2| | | exact AUX1]; intros a Ha; apply OUT2; [left; lia| right; left]. unfold RAUXV_CELL, stdout_addr in *. lia. }
    split; [exact ST2|].
    split. { exists errv1. eapply rw_cells_agree; [exact AG2| exact ERR1|]. intros a Ha. apply OUT2. right; left. rewrite TP in Ha. cbv delta [MallocRep.wz] in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. unfold stdout_addr. lia. }
    split; [exact MI2|].
    split; [exact SOF2|].
    split. { exists ib. eapply rw_cells_agree; [exact AG2| exact FLAG1|]. intros a Ha. apply OUT2. right; left. cbn in Ha. unfold stdout_addr. lia. }
    split. { exists j0. eapply rw_cells_agree; [exact AG2| exact FR1|]. intros a Ha. apply OUT2. left. cbn in Ha. lia. }
    split. { eapply rdrv_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU2| exact WM2|].
      intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUT2.
      + left. lia.
      + right; right. pose proof (HBR _ _ _ _ HP1 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb))))) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      + right; left. split; [exact Ha|]. split; [intros Hso; apply HX; unfold stdout_addr in Hso; unfold DRVW; cbn; lia|].
        intros Hf. apply HX. unfold DRVW, RINIT_FLAG. cbn. lia. }
    split. { destruct POK1 as (PB & PF & PD & PD2 & PD3 & PIN). split; [| split; [exact PF| split; [exact PD| split; [exact PD2| split; [exact PD3| exact PIN]]]]].
      eapply bytes_at_agree; [exact AG2| exact PB|]. intros a Ha. rewrite to_bytes_length in Ha.
      destruct PIN as [EP|(b & Hb & Hr1 & Hr2)]; [rewrite EP in Ha; cbn in Ha; lia|].
      assert (Hb' : In b (X ++ LW ++ LB)) by (apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb]).
      apply OUT2. right; right. pose proof (HBR _ _ _ _ HP1 Hb') as (R1 & R2 & R3 & R4 & R5). unfold zlength, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    split. { eapply ATBL_agree; [exact AG2| | exact ATB1]. intros a Ha. apply OUT2. right; left. unfold atbl_addr, stdout_addr in *. lia. }
    exact INCB2.
  Qed.

  (* [comment removed for export] *)
  Lemma TENV_flag : forall icb icb' ls LW X D st m m',
    TENV icb ls LW X D st m ->
    munch [(0x3306b4, 0x3306b5)] m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' ->
    stk ctusegs m' lo (usp + -80) -> rw_cells ctusegs m' 0x3306b4 [C1 icb'] ->
    TENV icb' ls LW X D st m'.
  Proof.
    intros icb icb' ls LW X D st m m' TE MU WM MI' ST' INCB'.
    pose proof TE as (HP1 & _ & _ & _ & _ & _ & _ & _ & _ & SOF1 & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LIB_STACK_lo as LSL. pose proof LIB_STACK_hi as LSH.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    eapply (TENV_frame _ icb icb' ls LW X D st st m m' TE MU WM MI'); [| | exact ST'| | exact INCB'].
    - intros a Ha. cbn. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
    - eapply HFRAME; [exact HP1| exact MU| exact WM|]. constructor; [| constructor].
      right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
    - eapply stdout_file_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SOF1]. intros a Ha. unfold stdout_addr in Ha. cbn. lia.
  Qed.

  Notation KF o := (fun rc : Z => lib_free_optG o ;;; mret (if rc =? 0 then 0 else 1)).

  (* [comment removed for export] *)
  Lemma tr_loop : forall (k : nat) (rc0 : Z) ls LW X D owned o st (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (1 <= k)%nat -> Z.of_nat k <= 4 ->
    TENV (Z_to_bv 8 0) ls LW X D st m -> OWNED X D owned o -> frm0 fc ->
    implM ctusegs (rc <- run_callsG payload k ls rc0 ;; (lib_free_optG o ;;; mret (if rc =? 0 then 0 else 1))) st POST
      (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
               (wz owned) s3v (wz RINIT_FLAG) (wz (Z.of_nat k)) (wz 0) (wz (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz 0xe23b0) fc None m (seg_rom ctusegs)).
  Proof.
    induction k as [|k IH]; intros until m; intros K1 K4 TE OW FRM; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    pose proof LIB_STACK_lo as LSL. pose proof LIB_STACK_hi as LSH.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    cbv beta delta [MallocRep.wz] in TP |- *. unfold RINIT_FLAG.
    cbn [run_callsG].
    apply implM_bind_assoc.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    pose proof TE as (_ & _ & _ & _ & _ & _ & ST & _ & MI & _ & _ & _ & _ & _ & _ & INCB). unfold RAEF_INCB in INCB.
    pose proof (munch_refl [(0x3306b4, 0x3306b5)] m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    zstep. zstep; fix_sb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (TENV_flag _ (Z_to_bv 8 1) ls LW X D st m mx TE MU WM MI ST INCB) as TEa end.
    clear MU WM ST MI INCB TE.
    destruct TEa as (HP & LINV & OSC & LXS & SEW & AUX & ST & [errv ERR] & MI & SOF & [ib FLAG] & [j0 FR] & PRES & POK & ATB & INCB).
    unfold FRAME, RINIT_FLAG, RAEF_INCB in FR, FLAG, INCB.
    (* [comment removed for export] *)
    do 3 zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm st POST msx) end.
    eapply implM_bind.
    { unfold LX_FUZZ in FUZZ.
      lazymatch goal with |- implM _ _ _ _ (MS _ ?Fx _ ?fcx _ ?mx _) =>
      eapply (FUZZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fcx mx st ls LW (X ++ LB) D payload lo B errv rr_guard);
        [exact (RHEAP_perm _ _ _ _ HP (Permutation_app_swap_app X LW LB))| exact LINV| exact LXS| exact SEW| exact (RHEAP_ssp _ _ _ HP)| exact AUX
        | rewrite unsigned_lit by lia; lia| exact B63| rewrite unsigned_lit by lia; exact ST| exact LOC| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; unfold LX_FUZZ_STACK; lia
        | exact ERR| exact TP| exact MI
        | rewrite unsigned_lit by lia; replace (usp + -80) with (usp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
        | exact POK| exact FRM| reflexivity| rewrite F3; reflexivity] end. }
    cbv beta. intros [ls1 rc] st1 ms1 [PO RC0]. cbn [fst snd] in PO, RC0 |- *. subst rc.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1' & fc1 & mF & LW1 & -> & LPE & LINV1 & OSC1 & -> & POK1).
    assert (NLW : forall a, rin_ivs LIBW a -> 0x2c2000 <= a < 0x355000 /\ ~ ralloc_static a /\ ~ drv_addr a) by (exact LIBW_img).
    destruct LPE as ((errv1 & ENV1) & FRM1 & LXP & ESO & EFA).
    destruct ENV1 as (HP1 & LXS1 & SEW1 & SSP1 & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1).
    rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in LXP by lia.
    replace (ret_pc (Z_to_bv 64 0xe23c4)) with (Z_to_bv 64 0xe23c4) by (symmetry; rpc).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP) as AG1.
    assert (DRVC : forall a, 0x2c2000 <= a < 0x355000 -> ~ ralloc_static a -> drv_addr a -> lx_client (X ++ LB) (usp + -80) LIBW a).
    { intros a Hr Hs Hd. split; [intros Hi; destruct (NLW _ Hi) as (_ & _ & Hn); exact (Hn Hd)| right; right; split; [exact Hr| exact Hs]]. }
    assert (FR1 : rw_cells ctusegs mF (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG1| exact FR|]. intros a Ha. apply stack_client; [cbn in Ha; lia|].
      cbn in Ha. intros Hi. destruct (NLW _ Hi) as (Hr & _). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (SOF1 : stdout_file mF (ps_so st1)).
    { rewrite ESO. eapply stdout_file_agree; [exact AG1| | exact SOF]. intros a Ha. apply stdout_addr_client; [exact Ha|].
      intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. left. exact Ha. }
    assert (FLAG1 : rw_cells ctusegs mF 3344048 [C1 ib]).
    { eapply rw_cells_agree; [exact AG1| exact FLAG|]. intros a Ha. cbn in Ha. split.
      - intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. unfold drv_addr, RINIT_FLAG. do 5 right. left. lia.
      - right; right. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (INCB1 : rw_cells ctusegs mF 3344052 [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_agree; [exact AG1| exact INCB|]. intros a Ha. cbn in Ha. split.
      - intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. unfold drv_addr, RINIT_FLAG. do 5 right. left. lia.
      - right; right. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (ATB1 : ATBL mF).
    { eapply ATBL_agree; [exact AG1| | exact ATB]. intros a Ha. unfold atbl_addr in Ha. split.
      - intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. unfold drv_addr, LIB_TCB. cbn [rin_ivs fst snd]. do 9 right. lia.
      - right; right. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (PRES1 : rdrv_pres LB usp m0 mF).
    { eapply rdrv_pres_trans; [exact PRES|]. apply rdrv_pres_of_lx. eapply lx_pres_weaken; [exact LXP| lia| intros b Hb; apply in_or_app; right; exact Hb| auto]. }
    assert (TE1 : TENV (Z_to_bv 8 1) ls1 LW1 X D st1 mF).
    { unfold TENV, FRAME, RINIT_FLAG, RAEF_INCB.
      split; [exact (RHEAP_perm _ _ _ _ HP1 (Permutation_app_swap_app LW1 X LB))|].
      split; [exact LINV1|]. split; [exact OSC1|]. split; [exact LXS1|]. split; [exact SEW1|]. split; [exact AUX1|]. split; [exact ST1|].
      split; [exists errv1; exact ERR1|]. split; [exact MI1|]. split; [exact SOF1|]. split; [exists ib; exact FLAG1|]. split; [exists j0; exact FR1|].
      split; [exact PRES1|]. split; [exact POK1|]. split; [exact ATB1|]. exact INCB1. }
    clear DRVC AG1 LXP HP LINV OSC LXS SEW AUX ST ERR MI SOF FLAG FR PRES POK ATB INCB.
    clear HP1 LXS1 SEW1 AUX1 ERR1 SOF1 FLAG1 FR1 PRES1 POK1 ATB1 LINV1 OSC1.
    (* [comment removed for export] *)
    replace (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0 by reflexivity.
    apply implM_bind_assoc.
    unfold implM. iprefix.
    pose proof (munch_refl [(0x3306b4, 0x3306b5)] mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
    zstep. zstep; fix_sb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (TENV_flag _ (Z_to_bv 8 0) ls1 LW1 X D st1 mF mx TE1 MU WM MI1 ST1 INCB1) as TEb end.
    clear MU WM ST1 MI1 INCB1 TE1 SSP1.
    destruct TEb as (HP1 & LINV1 & OSC1 & LXS1 & SEW1 & AUX1 & ST1 & [errv1' ERR1] & MI1 & SOF1 & [ib1 FLAG1] & [j1 FR1] & PRES1 & POK1 & ATB1 & INCB1).
    pose proof (RHEAP_ssp _ _ _ HP1) as SSP1.
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm st1 POST msx) end.
    eapply implM_bind.
    { eapply implM_keepsf; [| apply stdout_vprintf_keeps].
      lazymatch goal with |- implM _ _ _ _ (MS _ ?Fx _ ?fcx _ ?mx _) =>
      eapply (EMIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fcx mx st1 lo rr_guard);
        [apply ps_get_set| apply ps_set_set| exact FWXO| exact SOF1| rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; unfold EMIT_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; lia| exact SSP1| exact MI1| exact FRM1] end. }
    cbv beta. intros [] st2 ms2 [PO EBS].
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2' & fc2 & mE & -> & MU2 & WM2 & MI2 & FRM2 & HF2 & ST2 & SOF2 & SSP2).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0xe23d4)) with (Z_to_bv 64 0xe23d4) by (symmetry; rpc).
    destruct (but_so_eq _ _ EBS) as (EM2 & EBRK2 & EFA2).
    assert (TE2 : TENV (Z_to_bv 8 0) ls1 LW1 X D st2 mE).
    { lazymatch type of MU2 with munch _ ?mx _ =>
      eapply (TENV_frame _ (Z_to_bv 8 0) (Z_to_bv 8 0) ls1 LW1 X D st1 st2 mx mE); [| exact MU2| exact WM2| exact MI2| | | exact ST2| exact SOF2|] end.
      - unfold TENV, FRAME, RINIT_FLAG, RAEF_INCB.
        split; [exact HP1|]. split; [exact LINV1|]. split; [exact OSC1|]. split; [exact LXS1|]. split; [exact SEW1|]. split; [exact AUX1|]. split; [exact ST1|].
        split; [exists errv1'; exact ERR1|]. split; [exact MI1|]. split; [exact SOF1|]. split; [exists ib1; exact FLAG1|]. split; [exists j1; exact FR1|].
        split; [exact PRES1|]. split; [exact POK1|]. split; [exact ATB1|]. exact INCB1.
      - intros a Ha. unfold stdout_addr in Ha. cbn. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      - eapply RHEAP_ext; [| exact EM2| exact EBRK2].
        eapply HFRAME; [exact HP1| exact MU2| exact WM2|].
        constructor; [left; cbn [fst]; exact LOC|]. constructor; [| constructor; [| constructor]];
          right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
      - eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU2 WM2)| exact INCB1|]. intros a Ha. unfold RAEF_INCB in Ha. cbn in Ha. cbn.
        unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    (* [comment removed for export] *)
    unfold implM. iprefix. zstep.
    replace (bv_swrap 32 (bv_unsigned (wz 0) + -1)) with (-1) by (vm_compute; reflexivity).
    zstep. if_true.
    zstep. rewrite swrap32_id by lia. replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    zstep. if_cases HK; zify_cond HK.
    - (* [comment removed for export] *)
      apply evt_done. apply (IH 0 ls1 LW1 X D owned o st2); [lia| lia| exact TE2| exact OW| exact FRM2].
    - (* [comment removed for export] *)
      apply evt_done. cbn [run_callsG]. apply implM_ret_bind.
      replace k with 0%nat by lia. cbn [Z.of_nat].
      apply (tr_tail ls1 LW1 X D owned o st2); [exact TE2| exact OW| exact FRM2].
  Qed.

  (* [comment removed for export] *)
  Lemma payload_bytes : forall m, bytes_at ctusegs m A (to_bytes content) -> bytes_at ctusegs m PAY (to_bytes payload).
  Proof.
    intros m H. unfold PAY, payload, to_bytes in *. rewrite <- (firstn_skipn (Z.to_nat (6 + L)) content) in H.
    rewrite map_app in H. apply bytes_at_app in H as [_ H]. rewrite length_map, length_firstn in H.
    replace (A + Z.of_nat (Init.Nat.min (Z.to_nat (6 + L)) (length content))) with (A + 6 + L) in H by (unfold zlength in L6; lia). exact H.
  Qed.

  (* [comment removed for export] *)
  Theorem tr_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc_ : bv 32) (errv_ : word),
    RHEAP s LB m0 -> bytes_at ctusegs m0 A (to_bytes content) ->
    lx_statics m0 -> stderr_wfile m0 -> stdout_file m0 (ps_so s) ->
    rw_cells ctusegs m0 RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells ctusegs m0 RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
    atexit_cells_st false m0 ->
    lib_pristine m0 ->
    rauxv_ok m0 B -> stk ctusegs m0 lo usp -> rw_cells ctusegs m0 (errno_addr tp) [C4 errv_] -> mem_inv ctusegs m0 -> frm0 fc_ ->
    implM ctusegs (runG cfg payload) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz (A + 2)) (wz L) (wz PAY) (wz plen) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F_ (wz RTARGET_RUN) fc_ None m0 (seg_rom ctusegs)).
  Proof.
    intros until errv_. intros HP0 CT0 LXS0 SEW0 SOF0 FLAG0 GOT0 ATS0 PRI0 AUX0 ST0 ERR0 MI0 FRM_.
    destruct ATS0 as (p1 & p2 & slot_ & head_ & f0_ & a0v_ & ATX0 & ATA0 & INCB0 & ATV0). cbn [atexit_vals] in ATV0. destruct ATV0 as (-> & -> & -> & ->).
    destruct (RHEAP_libc_head _ _ _ HP0) as (cdt & thr & sec & tm1 & LCH0).
    pose proof LIB_STACK_lo as LSL. pose proof LIB_STACK_hi as LSH.
    assert (NLW : forall a, rin_ivs LIBW a -> 0x2c2000 <= a < 0x355000 /\ ~ ralloc_static a /\ ~ drv_addr a) by (exact LIBW_img).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOC as LOC'. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in LOC'; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    unfold runG, target_runG. rewrite F3.
    change (Z.to_nat (Z.land cfg 3 + 1)) with (Z.to_nat calls).
    unfold RTARGET_RUN. unfold implM. iprefix.
    eapply (tr_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p1 p2 cdt thr sec tm1); [exact ST0| exact MI0| exact FLAG0| exact GOT0| exact ATX0| exact ATA0| exact LCH0|].
    intros mp t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FRp STp MUp WMp MIp FLAGp GOTp ATXp ATAp. unfold WPRE in MUp.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    unfold RINIT_FLAG, RAEF_INCB in *. cbv beta delta [MallocRep.wz] in TP |- *.
    pose proof (agree_on_of_munch _ _ _ MUp WMp) as AGp.
    assert (OUTp : forall a, (usp <= a \/ (0x2c2000 <= a < 0x355000 /\ ~ (3344048 <= a < 3344049) /\ ~ atbl_addr a) \/ (a < lo /\ (a < 0x10000 \/ 0x355000 <= a))) ->
                             outside [(usp + -128, usp); (3344048, 3344048 + 1); (0x353278, 0x3532a0); (0x353398, 0x3533a0)] a).
    { intros a Ha. unfold atbl_addr in Ha. cbn. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (HPp : RHEAP s LB mp).
    { eapply HFRAME; [exact HP0| exact MUp| exact WMp|]. constructor; [left; cbn [fst]; unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia|].
      constructor; [| constructor; [| constructor; [| constructor]]]; right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia. }
    assert (INCBp : rw_cells ctusegs mp 3344052 [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_agree; [exact AGp| exact INCB0|]. intros a Ha. apply OUTp. right; left. unfold atbl_addr. cbn in Ha. lia. }
    assert (ATBp : ATBL mp) by (exists p1, p2; unfold atexit_cells; cbv delta [MallocRep.wz]; split; [exact ATXp| exact ATAp]).
    pose proof (HBR _ _ _ _ HP0 INB) as BRA. cbn [blk_addr blk_size fst snd] in BRA. unfold rblock_range, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in BRA; try (pose proof alloc_ceiling_range as CEIL_RANGE__). destruct BRA as (BRA1 & BRA2 & BRA3 & BRA4 & BRA5).
    assert (CTp : bytes_at ctusegs mp A (to_bytes content)).
    { eapply bytes_at_agree; [exact AGp| exact CT0|]. intros a Ha. rewrite to_bytes_length in Ha. apply OUTp. right; right.
      pose proof (HBR _ _ _ _ HP0 INB) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R4, R5. unfold zlength, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (LXSp : lx_statics mp).
    { eapply lx_statics_agree; [exact AGp| | exact LXS0]. intros a Ha. apply OUTp. right; left.
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, atbl_addr in *. lia. }
    assert (SEWp : stderr_wfile mp).
    { eapply stderr_wfile_agree; [exact AGp| | exact SEW0]. intros a Ha. apply OUTp. right; left. unfold stderr_addr, atbl_addr in *. lia. }
    assert (SOFp : stdout_file mp (ps_so s)).
    { eapply stdout_file_agree; [exact AGp| | exact SOF0]. intros a Ha. apply OUTp. right; left. unfold stdout_addr, atbl_addr in *. lia. }
    assert (AUXp : rauxv_ok mp B).
    { eapply rauxv_ok_agree; [exact AGp| | | exact AUX0]; intros a Ha; apply OUTp; [left; lia| right; left]. unfold RAUXV_CELL, atbl_addr in *. lia. }
    assert (ERRp : rw_cells ctusegs mp (errno_addr tp) [C4 errv_]).
    { eapply rw_cells_agree; [exact AGp| exact ERR0|]. intros a Ha. apply OUTp. right; left. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. unfold atbl_addr. lia. }
    assert (PRESp : rdrv_pres LB usp m0 mp).
    { eapply lx_pres_of_munch; [exact MUp| exact WMp|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUTp.
      - left. lia.
      - right; right. pose proof (HBR _ _ _ _ HP0 Hb) as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      - right; left. split; [exact Ha|]. split; [intros Hi; apply HX; unfold DRVW, RINIT_FLAG; cbn; lia| intros Hi; apply HX; unfold atbl_addr in Hi; unfold DRVW, RINIT_FLAG; cbn; lia]. }
    assert (PRIp : lib_pristine mp).
    { eapply lib_pristine_agree; [exact PRI0|]. eapply agree_on_mono; [exact AGp|]. intros a Hi. apply OUTp. right; left.
      destruct (NLW _ Hi) as (Hr & _ & Hd). split; [exact Hr|]. split; [intros Hf; apply Hd; unfold drv_addr, RINIT_FLAG; do 5 right; left; lia|].
      intros Hf. apply Hd. unfold atbl_addr in Hf. unfold drv_addr, LIB_TCB. cbn [rin_ivs fst snd]. do 9 right. lia. }
    (* [comment removed for export] *)
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s POST msx) end.
    eapply implM_bind.
    { unfold LX_INIT, LX_AEF_ARGC in INIT. unfold FRAME_INIT in FRp.
      pose proof (proj1 (Malloc_ifaceP.rw_cells_app ctusegs mp (usp + -80) [C8 (wz LX_AEF_ARGV)] _) FRp) as [SLOT _].
      eapply (INIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc_ mp s LB lo B errv_ rr_guard);
        [exact HPp| exact LXSp| exact SEWp| exact (RHEAP_ssp _ _ _ HPp)| exact AUXp
        | rewrite unsigned_lit by lia; lia| exact B63| rewrite unsigned_lit by lia; exact STp| exact LOC| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; unfold LX_FUZZ_STACK; lia
        | exact ERRp| exact TP| exact MIp
        | rewrite unsigned_lit by lia; replace (usp + -80) with (usp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
        | exact FRM_| exact PRIp| rewrite unsigned_lit by lia; exact SLOT| reflexivity| reflexivity]. }
    cbv beta. intros ls0 s0i msi PO.
    destruct PO as (i0 & i1 & i2 & ia0 & ia1 & ia2 & ia3 & ia4 & ia5 & ia6 & ia7 & i3 & i4 & i5 & i6 & F & fc & m1 & LW0 & -> & LPE & LINV1 & OSC1 & _ & _).
    destruct LPE as ((errv & ENV1) & FRM & LXPi & ESOi & EFAi).
    destruct ENV1 as (HP1 & LXS1 & SEW1 & SSP1 & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1).
    rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in LXPi by lia.
    replace (ret_pc (Z_to_bv 64 0xe2450)) with (Z_to_bv 64 0xe2450) by (symmetry; rpc).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXPi) as AGi.
    assert (NST : forall a, usp + -80 <= a -> ~ rin_ivs LIBW a).
    { intros a Ha Hi. destruct (NLW _ Hi) as (Hr & _). lia. }
    assert (FR1 : FRAME m1 (le8 (wz LX_AEF_ARGV))).
    { unfold FRAME. eapply rw_cells_agree; [exact AGi| | intros a Ha; apply stack_client; [cbn in Ha; lia| apply NST; cbn in Ha; lia]].
      unfold FRAME_INIT in FRp. eapply (Lib_kit.rw_cells_recast mp _ _ _ FRp); [cbn; repeat split; exact I| reflexivity| reflexivity]. }
    assert (CT1 : bytes_at ctusegs m1 A (to_bytes content)).
    { eapply bytes_at_agree; [exact AGi| exact CTp|]. intros a Ha. rewrite to_bytes_length in Ha.
      apply (block_client LB _ _ (p, A, cap)); [exact INB| cbn [blk_addr blk_size fst snd]; unfold zlength in *; lia|].
      intros Hi. destruct (NLW _ Hi) as (Hr & _).
      pose proof (HBR _ _ _ _ HP0 INB) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R4, R5. unfold zlength in *. lia. }
    assert (SOF1 : stdout_file m1 (ps_so s0i)).
    { rewrite ESOi. eapply stdout_file_agree; [exact AGi| | exact SOFp]. intros a Ha. apply stdout_addr_client; [exact Ha|].
      intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. left. exact Ha. }
    assert (FLAG1 : rw_cells ctusegs m1 3344048 [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_agree; [exact AGi| exact FLAGp|]. intros a Ha. cbn in Ha. split.
      - intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. unfold drv_addr, RINIT_FLAG. do 5 right. left. lia.
      - right; right. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (INCB1 : rw_cells ctusegs m1 3344052 [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_agree; [exact AGi| exact INCBp|]. intros a Ha. cbn in Ha. split.
      - intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. unfold drv_addr, RINIT_FLAG. do 5 right. left. lia.
      - right; right. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (ATB1 : ATBL m1).
    { eapply ATBL_agree; [exact AGi| | exact ATBp]. intros a Ha. unfold atbl_addr in Ha. split.
      - intros Hi. destruct (NLW _ Hi) as (_ & _ & Hd). apply Hd. unfold drv_addr, LIB_TCB. cbn [rin_ivs fst snd]. do 9 right. lia.
      - right; right. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (PRES1 : rdrv_pres LB usp m0 m1).
    { eapply rdrv_pres_trans; [exact PRESp|]. apply rdrv_pres_of_lx. eapply lx_pres_weaken; [exact LXPi| lia| auto| auto]. }
    clear AGp OUTp HPp CTp LXSp SEWp SOFp AUXp ERRp PRESp PRIp MUp WMp FLAGp GOTp STp MIp FRp INCBp ATBp ATXp ATAp.
    set (ib' := Z_to_bv 8 1) in FLAG1. set (j0 := le8 (wz LX_AEF_ARGV)) in FR1.
    unfold implM. iprefix.
    zstep.        (* [comment removed for export] *)
    eapply (tr_mid _ (Z_to_bv 64 0xe2450)); [exact FR1| exact MI1| exact CT1| |].
    - (* [comment removed for export] *)
      intros a0'' NZ. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
      cbv beta delta [MallocRep.wz]. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s0i POST msx) end.
      apply implM_bind_assoc. eapply implM_bind.
      { unfold RMALLOC_SYM in MALLOC.
        eapply (MALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s0i (LW0 ++ LB) plen lo B errv);
          [exact HP1| exact AUX1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact LOC
          | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| exact ERR1| exact MI1| exact TP| reflexivity| lia]. }
      cbv beta. intros r st1 ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & RES).
      rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0xe2354)) with (Z_to_bv 64 0xe2354) by (symmetry; rpc).
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG2.
      Ltac cli := right; left; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP.
      assert (FR2 : rw_cells ctusegs m2 (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      { eapply rw_cells_agree; [exact AG2| exact FR1| intros a Ha; left; cbn in Ha; lia]. }
      assert (LXS2 : lx_statics m2).
      { eapply lx_statics_agree; [exact AG2| | exact LXS1]. intros a Ha. cli. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR in *. lia. }
      assert (SEW2 : stderr_wfile m2).
      { eapply stderr_wfile_agree; [exact AG2| | exact SEW1]. intros a Ha. cli. unfold stderr_addr in *. lia. }
      assert (SOF2 : stdout_file m2 (ps_so st1)).
      { rewrite ESO. eapply stdout_file_agree; [exact AG2| | exact SOF1]. intros a Ha. cli. unfold stdout_addr in *. lia. }
      assert (FLAG2 : rw_cells ctusegs m2 3344048 [C1 ib']).
      { eapply rw_cells_agree; [exact AG2| exact FLAG1|]. intros a Ha. cli. cbn in Ha. lia. }
      assert (CT2 : bytes_at ctusegs m2 A (to_bytes content)).
      { eapply bytes_at_agree; [exact AG2| exact CT1|]. intros a Ha. rewrite to_bytes_length in Ha. right; right. exists (p, A, cap). split; [apply in_or_app; right; exact INB|]. cbn [blk_addr blk_size fst snd]. unfold zlength in *. lia. }
      assert (LINV2 : lib_inv ls0 m2 LW0).
      { eapply lib_inv_agree; [exact LINV1|]. eapply agree_on_mono; [exact AG2|]. intros a [Hi|(b & Hb & Hr)].
        - right; left. destruct (NLW _ Hi) as (Hr & Hs & _). split; [exact Hr| exact Hs].
        - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr]. }
      assert (OSC2 : ossl_exit_cells m2).
      { eapply ossl_exit_cells_agree; [exact AG2| | exact OSC1]. intros a Ha. right; left. apply ossl_exit_addr_client. exact Ha. }
      assert (PRES2 : rdrv_pres LB usp m0 m2).
      { eapply rdrv_pres_trans; [exact PRES1|]. apply rdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; apply in_or_app; right; exact Hb]. }
      assert (INCB2 : rw_cells ctusegs m2 3344052 [C1 (Z_to_bv 8 0)]).
      { eapply rw_cells_agree; [exact AG2| exact INCB1|]. intros a Ha. cli. cbn in Ha. lia. }
      assert (ATB2 : ATBL m2).
      { eapply ATBL_agree; [exact AG2| | exact ATB1]. intros a Ha. cli. unfold atbl_addr in Ha. lia. }
      destruct r as [pb|].
      + (* [comment removed for export] *)
        destruct RES as (A' & junk & -> & BR & HP2 & BLK & _).
        pose proof BR as BR0. unfold rblock_range, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in BR0; try (pose proof alloc_ceiling_range as CEIL_RANGE__). destruct BR0 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
        unfold implM. iprefix. zstep. if_cases HA; [apply wz_eqb0 in HA; lia|].
        do 3 zstep. zstep. zstep.      (* [comment removed for export] *)
        pose proof (payload_bytes _ CT2) as PB2.
        assert (SEP : PAY + plen <= A' \/ A' + plen <= PAY).
        { pose proof (HBD _ _ _ _ _ HP2 (or_intror _ (in_or_app _ _ _ (or_intror INB))) (or_introl eq_refl)) as D. cbn [blk_id blk_addr blk_size fst snd] in D.
          pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
          assert (NE : p <> pb) by (intros E; apply NI; rewrite <- E; apply in_map_iff; exists (p, A, cap); split; [reflexivity| apply in_or_app; right; exact INB]).
          specialize (D NE). unfold PAY, plen in *. unfold zlength in *. lia. }
        eapply evt_cut.
        { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (to_bytes payload) junk);
            rewrite ?unsigned_lit by (unfold PAY, zlength in *; lia);
            [exact PB2| rewrite to_bytes_length; unfold zlength in F3; lia| exact BLK| exact SEP| exact MI2]. }
        cbv beta. intros ms3 PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & BLK3 & PB3).
        rewrite !unsigned_lit in MU3 by (unfold PAY, zlength in *; lia). rewrite !unsigned_lit in BLK3 by lia. rewrite !unsigned_lit in PB3 by (unfold PAY, zlength in *; lia).
        replace (ret_pc (Z_to_bv 64 0xe236c)) with (Z_to_bv 64 0xe236c) by (symmetry; rpc).
        pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
        assert (OUT3 : forall a, (0x10000 <= a < 0x355000 \/ lo <= a \/ in_block (LW0 ++ LB) a) -> outside [(A', A' + plen)] a).
        { intros a Ha. cbn. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| lia|].
          pose proof (HBD _ _ _ _ _ HP2 (or_intror _ Hb) (or_introl eq_refl)) as D. cbn [blk_id blk_addr blk_size fst snd] in D.
          pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
          assert (NE : blk_id b <> pb) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
          specialize (D NE). lia. }
        Ltac cl3 OUT3 := apply OUT3; left.
        assert (TE3 : TENV (Z_to_bv 8 0) ls0 LW0 [(pb, A', plen)] A' st1 m3).
        { unfold TENV, FRAME, RINIT_FLAG, RAEF_INCB. cbn [app].
          split. { eapply HFRAME; [exact HP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (pb, A', plen). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
          split. { eapply lib_inv_agree; [exact LINV2|]. eapply agree_on_mono; [exact AG3|]. intros a [Hi|(b & Hb & Hr)]; apply OUT3.
                   - left. destruct (NLW _ Hi) as (Hr & _). lia.
                   - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr]. }
          split. { eapply ossl_exit_cells_agree; [exact AG3| | exact OSC2]. intros a Ha. cl3 OUT3. unfold ossl_exit_addr, OSSL_BASE_INITED in *. lia. }
          split. { eapply lx_statics_agree; [exact AG3| | exact LXS2]. intros a Ha. cl3 OUT3. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR in *. lia. }
          split. { eapply stderr_wfile_agree; [exact AG3| | exact SEW2]. intros a Ha. cl3 OUT3. unfold stderr_addr in *. lia. }
          split. { eapply rauxv_ok_agree; [exact AG3| | | exact AUX2]; intros a Ha; apply OUT3; [right; left; unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia| left]. unfold RAUXV_CELL in *. lia. }
          split. { eapply stk_agree; [exact AG3| exact ST2| intros a Ha; apply OUT3; right; left; lia]. }
          split. { exists errv2. eapply rw_cells_agree; [exact AG3| exact ERR2|]. intros a Ha. cl3 OUT3. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia. }
          split; [exact MI3|].
          split. { eapply stdout_file_agree; [exact AG3| | exact SOF2]. intros a Ha. cl3 OUT3. unfold stdout_addr in *. lia. }
          split. { exists ib'. eapply rw_cells_agree; [exact AG3| exact FLAG2|]. intros a Ha. cl3 OUT3. cbn in Ha. lia. }
          split. { exists j0. eapply rw_cells_agree; [exact AG3| exact FR2|]. intros a Ha. apply OUT3. right; left. cbn in Ha. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
          split. { eapply rdrv_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU3| exact WM3|].
                   intros a [HX [Ha|[Hb|[Ha Hs]]]]; apply OUT3; [right; left; unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia| right; right; destruct Hb as (b & Hb & Hr); exists b; split; [apply in_or_app; right; exact Hb| exact Hr]| left; lia]. }
          split. { unfold payload_ok. destruct BLK3 as [[_ PBD] _]. cbn [cells_bytes cbytes] in PBD. rewrite app_nil_r in PBD.
          split; [exact PBD|]. split; [unfold payload; apply Forall_skipn; exact CR|]. split; [lia|]. split; [lia|]. split; [lia|].
          right. exists (pb, A', plen). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
          split. { eapply ATBL_agree; [exact AG3| | exact ATB2]. intros a Ha. cl3 OUT3. unfold atbl_addr in Ha. lia. }
          eapply rw_cells_agree; [exact AG3| exact INCB2|]. intros a Ha. cl3 OUT3. cbn in Ha. lia. }
        zstep. zstep. zstep. zstep. apply evt_done.      (* [comment removed for export] *)
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm st1 POST msx) end.
        apply implM_ret_bind. replace calls with (Z.of_nat (Z.to_nat calls)) at 2 by lia.
        apply (tr_loop (Z.to_nat calls) 0 ls0 LW0 [(pb, A', plen)] A' A' (Some pb) st1); [lia| lia| exact TE3| split; reflexivity| exact FRM].
      + (* [comment removed for export] *)
        destruct RES as [-> HP2].
        apply implM_ret_bind. apply implM_ret. zstep. if_true. zstep. zstep. do 9 zstep. zstep. zstep.
        release_frame FR2 ST2 (bv_unsigned sp).
        apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z].
        exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m2, errv2, ib'.
        split; [reflexivity|]. split; [lia|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
        split; [exact ERR2|]. split; [exact AUX2|]. split; [exists LW0; exact HP2|]. split; [exact OSC2|].
        split; [exact LXS2|]. split; [exact SEW2|]. split; [exact (RHEAP_ssp _ _ _ HP2)|]. split; [exact SOF2|]. split; [exact FLAG2|].
        split; [apply ATBL_st; [exact ATB2| exact INCB2]|]. exact PRES2.
    - (* [comment removed for export] *)
      intros a0'' EZ. rewrite (proj2 (Z.eqb_eq _ _) EZ).
      cbv beta delta [MallocRep.wz]. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s0i POST msx) end.
      apply implM_ret_bind.
      assert (EP : payload = []) by (destruct payload; [reflexivity| unfold zlength in F3; cbn in F3; lia]).
      replace calls with (Z.of_nat (Z.to_nat calls)) at 2 by lia.
      unfold implM. iprefix. zstep. zstep. apply evt_done.      (* [comment removed for export] *)
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM ctusegs tm s0i POST msx) end.
      apply (tr_loop (Z.to_nat calls) 0 ls0 LW0 [] REMPTY 0 None s0i); [lia| lia| | split; reflexivity| exact FRM].
      unfold TENV, FRAME, RINIT_FLAG, RAEF_INCB. cbn [app].
      split; [exact HP1|]. split; [exact LINV1|]. split; [exact OSC1|]. split; [exact LXS1|]. split; [exact SEW1|]. split; [exact AUX1|].
      split; [exact ST1|]. split; [exists errv; exact ERR1|]. split; [exact MI1|]. split; [exact SOF1|]. split; [exists ib'; exact FLAG1|].
      split; [exists j0; exact FR1|]. split; [exact PRES1|].
      split. { rewrite EP. unfold payload_ok, REMPTY, LX_EMPTY, zlength. cbn [to_bytes map length Z.of_nat].
      split; [apply bytes_at_nil; lia|]. split; [constructor|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity. }
      split; [exact ATB1| exact INCB1].
  Qed.
End TR.

(* [comment removed for export] *)
Theorem rtarget_run_proof :
  rmalloc_stmt -> rfree_stmt -> rfree_null_stmt -> rinit_stmt -> rfuzz_one_stmt -> @emit_printf_stmt PState ps_so set_so_ps -> fwritex_stdout_stmt ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtarget_run_stmt.
Proof.
  intros MALLOC FREE FREE0 INIT FUZZ EMIT FWXO HFRAME HBR HND HBD.
  unfold rtarget_run_stmt. intros until errv.
  intros HP INB CT CR LEN1 CAP L0 L6 LXS SEW SSP SOF FLAG GOT ATS PRI AUX SPB B63 ST LOC LOG LOSP ERR TP MI FRM SP16 -> -> -> ->.
  eapply (tr_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB p A cap L content B lo
            INB CR LEN1 CAP L0 L6 SPB B63 LOC LOG LOSP TP SP16 MALLOC FREE FREE0 INIT FUZZ EMIT FWXO HFRAME HBR HND HBD m);
    eassumption.
Qed.
End WithCeiling0.
