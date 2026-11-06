(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Driver Prog StrFun.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit F_atexit Printf_stdio_iface Sj_iface Driver_iface Drv_kit Drv_facts Drv_aex.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require F_memcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Ltac fix_sb :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.

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

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call usegs m mm MU WM end end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

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

Definition atexit1_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x115598, 0x11559c); (0x1155b8, 0x1155c0); (0x1156b8, 0x1156c0)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ aex_tbl m' 2.
Lemma atexit1_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m 0x1157d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] -> aex_tbl m 1 -> mem_inv usegs m ->
  a0 = Z_to_bv 64 RAEF_GUARD -> (lo <= bv_unsigned sp - 48)%Z -> (0x117000 <= lo)%Z ->
  evt usegs (atexit1_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RATEXIT) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH AEXT MI Ha0 LO LOLO. eapply evt_mono; [eapply atexit_tbl1; eassumption|].
  intros ms' P. unfold atexit_tbl1_post, atexit1_postZ, AEX1 in *. exact P.
Qed.

Section TR.

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
  Hypothesis B63 : B < 2^62.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - RTARGET_RUN_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.

  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FREE0 : rfree_null_stmt.
  Hypothesis FUZZ : rfuzz_one_stmt.
  Hypothesis EMIT : @emit_printf_stmt PState ps_so set_so_ps.
  Hypothesis FWXO : fwritex_stdout_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

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

  Definition FRAME (mm : mem) (j0 : list byte) : Prop :=
    rw_cells usegs mm (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  Lemma tr_pre : forall (Q : machine_state -> Prop) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (cdt thr sec : byte) (tm1 : word),
    stk usegs m lo usp -> mem_inv usegs m ->
    aex_cells m 0 -> rw_cells usegs m RGOT_LLVMINIT [C8 (wz 0)] ->
    rw_cells usegs m RLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    (forall (m' : mem) (j0 : list byte) (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        FRAME m' j0 -> stk usegs m' lo (usp + -80) ->
        munch [(usp + -128, usp); (RINIT_FLAG, RINIT_FLAG + 5); (0x115590, 0x1156c8)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        aex_tbl m' 2 -> rw_cells usegs m' RLATCH [C1 (Z_to_bv 8 1)] -> rw_cells usegs m' RINCB [C1 (Z_to_bv 8 0)] -> rw_cells usegs m' RGOT_LLVMINIT [C8 (wz 0)] ->
        evt usegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0' t1' t2' (wz plen) (wz PAY) a0' a1' a2' a3' a4' a5' a6' a7'
                              (wz L) (wz (A + 2)) (wz RINIT_FLAG) S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6')
                        F (wz 0x3eaa4) fc None m' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz (A + 2)) (wz L) (wz PAY) (wz plen) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (wz 0x3ea5c) fc None m (seg_rom usegs)).
  Proof.
    intros until tm1. intros ST MI ((X1 & X2 & X3 & X4) & X5 & X6) GOT LCH K. unfold AEX, RLATCH, RINCB in *. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    unfold FRAME, RINIT_FLAG, RGOT_LLVMINIT, RAEX_CALL, RAEF_GUARD, RMallocRep.RLIBC in *. cbv beta delta [MallocRep.wz] in *.
    pose proof (munch_refl [(usp + -128, usp); (0xf32a0, 0xf32a0 + 5); (0x115590, 0x1156c8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    repeat match goal with H : rw_cells _ _ (?a + ?b)%Z _ |- _ => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v in H end.
    zstep. carve_frame 80%nat ST.
    zidle_begin sp 80%Z MUz WMz.
    do 9 zstep.
    zidle_end MUz WMz.
    steps_to 0x3eaa0%Z.

    change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
    zstep. if_true.
    zstep. zstep; fix_sb.      steps_to 0xc4bd0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (AT1 : aex_tbl mx 1);
      [unfold aex_tbl, AEX; split; [| split; [| split]];
       (try (lazymatch goal with |- rw_cells _ _ (?a + ?b)%Z _ => let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v end); hyp_by_addr) |] end.
    call_sp (atexit1_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo cdt thr sec tm1);
      [ first [hyp_by_addr | eassumption | reflexivity | lia] .. | ].
    rename POST into AT2. clear AT1.
    zstep. if_true.
    steps_to 0x3eb94%Z. zstep. if_true.      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; try eassumption; hyp_by_addr.
  Qed.

  Lemma tr_mid : forall (Q : machine_state -> Prop) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    FRAME m j0 -> mem_inv usegs m -> bytes_at usegs m A (to_bytes content) ->
    (forall a0' : word, plen <> 0 ->
     evt usegs Q (MS (mkR (wz 0x3eac0) (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz PAY) (wz plen) a1 a2 a3 a4 a5 a6 a7
                           (wz L) (wz (A + 2)) (wz RINIT_FLAG) (wz calls) S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                     F (wz RMALLOC_SYM) fc None m (seg_rom usegs))) ->
    (forall a0' : word, plen = 0 ->
     evt usegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz REMPTY) a0' a1 a2 a3 a4 a5 a6 a7
                           (wz 0) (wz (A + 2)) (wz RINIT_FLAG) (wz calls) S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                     F (wz 0x3eb0c) fc None m (seg_rom usegs))) ->
    evt usegs Q (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz PAY) a0 a1 a2 a3 a4 a5 a6 a7
                          (wz L) (wz (A + 2)) (wz RINIT_FLAG) S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (wz 0x3eaa4) fc None m (seg_rom usegs)).
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
    -
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      rewrite EC in K1, K0.
      zstep. zstep. if_cases HP; zify_cond HP.
      +   do 2 zstep. apply (K1 a0). lia.
      + do 2 zstep. apply (K0 a0). lia.
    -
      assert (EC : calls = Z.land (znth content 2) 3 + 1) by (unfold calls, cfg; replace (0 <? L) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      pose proof (proj1 (Forall_forall _ _) CR _ (znth_range content 2 ltac:(lia))) as C2. cbv beta in C2.
      do 3 zstep.
      replace (bv_unsigned (Z_to_bv 8 (znth content 2))) with (znth content 2) in * by (rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
      rewrite <- EC. zstep. if_cases HP; zify_cond HP.
      + do 2 zstep. apply (K0 (Z_to_bv 64 (Z.land (znth content 2) 3))). lia.
      + do 2 zstep. apply (K1 a0). lia.
  Qed.

  Lemma ps_get_set : forall (x : PState) so, ps_so (set_so_ps so x) = so. Proof. intros [? ? ? ? ?] so; reflexivity. Qed.
  Lemma ps_set_set : forall (x : PState) so so', set_so_ps so' (set_so_ps so x) = set_so_ps so' x. Proof. intros [? ? ? ? ?] so so'; reflexivity. Qed.

  Lemma lx_pres_of_munch : forall LB' SP X W m m',
    munch W m m' -> wmono usegs m m' -> (forall a, lx_client LB' SP X a -> outside W a) -> lx_pres LB' SP X m m'.
  Proof. intros LB' SP X W m m' MU WM HW. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| exact HW]. Qed.

  Definition aexb (m : mem) (b : Z) : Prop :=
    rw_cells usegs m 0xf32a0 [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m 0xf32a4 [C1 (Z_to_bv 8 b)].

  Definition xok (v : option bptr) (xb : list block) : Prop := match v with None => xb = [] | Some q => exists Av, xb = [(q, Av, 8)] end.
  Definition vN (v : option bptr) : Z := match v with Some _ => 3 | None => 2 end.
  Definition vB (v : option bptr) : bool := match v with Some _ => true | None => false end.

  Lemma payload_ok_app' : forall mm OW X0 D0 d0, payload_ok mm X0 D0 d0 -> payload_ok mm (OW ++ X0) D0 d0.
  Proof.
    intros mm OW X0 D0 d0 (P1 & P2 & P3 & P4 & P5 & P6). repeat (split; [assumption|]).
    destruct P6 as [E|(bb & Hb & R)]; [left; exact E| right; exists bb; split; [apply in_or_app; right; exact Hb| exact R]].
  Qed.
  Lemma imp_vec_agree' : forall (P : Z -> Prop) mm mm' X0 v, agree_on P mm mm' -> (forall a, 0xf32d0 <= a < 0xf32d0 + 32 -> P a) -> (forall a, in_block X0 a -> P a) ->
    imp_vec mm X0 v -> imp_vec mm' X0 v.
  Proof.
    intros P mm mm' X0 [q|] AG HP HB H; unfold imp_vec, IMP_VEC_LO in *.
    - destruct H as (Av & IN & VC & HW). exists Av. split; [exact IN|]. split.
      + eapply rw_cells_agree; [exact AG| exact VC|]. intros a Ha. apply HP. unfold imp_vec_cells in Ha. cbn in Ha. lia.
      + eapply rw_cells_agree; [exact AG| exact HW|]. intros a Ha. apply HB. exists (q, Av, 8). split; [exact IN|]. cbn in Ha |- *. lia.
    - eapply rw_cells_agree; [exact AG| exact H|]. intros a Ha. apply HP. cbn in Ha. lia.
  Qed.
  Lemma aex_tbl_agree' : forall (P : Z -> Prop) mm mm' n, agree_on P mm mm' -> (forall a, 0x115590 <= a < 0x115590 + 312 -> P a) -> aex_tbl mm n -> aex_tbl mm' n.
  Proof. intros P mm mm' n AG HP H. eapply aex_tbl_agree; [exact AG| | exact H]. intros a Ha. apply HP. unfold aex_tbl_addr, AEX in Ha. lia. Qed.

  Definition TENVb (xb X : list block) (v : option bptr) (D : Z) (st : PState) (m : mem) (b : Z) : Prop :=
    RHEAP st (xb ++ X ++ LB) m /\ lx_statics m /\ sj_statics m (vB v) /\ imp_vec m (xb ++ X ++ LB) v /\ aex_tbl m (vN v) /\ stderr_wfile m
    /\ rauxv_ok m B /\ stk usegs m lo (usp + -80) /\ (exists errv : word, rw_cells usegs m (errno_addr tp) [C4 errv])
    /\ mem_inv usegs m /\ stdout_file m (ps_so st) /\ aexb m b
    /\ (exists j0, FRAME m j0) /\ rdrv_pres LB usp m0 m /\ payload_ok m (xb ++ X ++ LB) D payload /\ xok v xb.
  Definition TENV (xb X : list block) (v : option bptr) (D : Z) (st : PState) (m : mem) : Prop := TENVb xb X v D st m 0.

  Lemma blocks_below : forall st X0 mm a, RHEAP st X0 mm -> in_block X0 a -> 0 < a /\ a < alloc_ceiling /\ (a < 0x10000 \/ 0x117000 <= a).
  Proof.
    intros st X0 mm a HP (bb & Hb & Hr). pose proof (HBR _ _ _ _ HP Hb) as (R1 & R2 & R3 & R4 & R5).
    unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
  Qed.

  Lemma TENV_incb : forall xb X v D st m m' (b b' : Z),
    TENVb xb X v D st m b -> munch [(0xf32a4, 0xf32a5)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
    rw_cells usegs m' 0xf32a4 [C1 (Z_to_bv 8 b')] -> TENVb xb X v D st m' b'.
  Proof.
    intros xb X v D st m m' b b' TE MU WM MI' X6'. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct TE as (HP & LXS & LXF & VEC & AEXT & SEW & AUX & ST & [errv ERR] & MI & SOF & (X5 & X6) & [j0 FR] & PRES & POK & XOK).
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, a <> 0xf32a4 -> outside [(0xf32a4, 0xf32a5)] a) by (intros a Ha; cbn; lia).
    unfold TENVb, aexb, FRAME in *.
    split. { eapply HFRAME; [exact HP| exact MU| exact WM|]. constructor; [| constructor]. right; left. cbn [fst snd].
             unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia. }
    split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. apply OUT. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *. lia. }
    split. { eapply sj_statics_agree; [exact AG| | exact LXF]. intros a Ha. apply OUT. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *. lia. }
    split. { eapply imp_vec_agree'; [exact AG| | | exact VEC]; intros a Ha; apply OUT; [lia|]. pose proof (blocks_below _ _ _ _ HP Ha). lia. }
    split. { eapply aex_tbl_agree'; [exact AG| | exact AEXT]. intros a Ha. apply OUT. lia. }
    split. { eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. apply OUT. unfold stderr_addr in *. lia. }
    split. { eapply rauxv_ok_agree; [exact AG| | | exact AUX]; intros a Ha; apply OUT; unfold RAUXV_CELL in *; unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia. }
    split. { eapply stk_agree; [exact AG| exact ST| intros a Ha; apply OUT; lia]. }
    split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply OUT. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. cbv delta [MallocRep.wz] in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia. }
    split; [exact MI'|].
    split. { eapply stdout_file_agree; [exact AG| | exact SOF]. intros a Ha. apply OUT. unfold stdout_addr in *. lia. }
    split. { split; [| exact X6']. eapply rw_cells_agree; [exact AG| exact X5| intros a Ha; apply OUT; cbn in Ha; lia]. }
    split. { exists j0. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. apply OUT. cbn in Ha. lia. }
    split. { eapply rdrv_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
             intros a [HX _]. apply OUT. intros ->. apply HX. unfold DRVW, RINIT_FLAG. cbn. lia. }
    split; [| exact XOK].
    destruct POK as (PB & PF & PD & PD2 & PD3 & PIN). split; [| split; [exact PF| split; [exact PD| split; [exact PD2| split; [exact PD3| exact PIN]]]]].
    eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. rewrite to_bytes_length in Ha.
    destruct PIN as [EP|(bb & Hb & Hr1 & Hr2)]; [rewrite EP in Ha; cbn in Ha; lia|].
    apply OUT. pose proof (HBR _ _ _ _ HP Hb) as (R1 & R2 & R3 & R4 & R5). unfold zlength in *. lia.
  Qed.

  Definition OWNED (X : list block) (D owned : Z) (o : option bptr) : Prop :=
    match o with
    | None => X = [] /\ owned = 0
    | Some pb => X = [(pb, D, plen)] /\ owned = D
    end.

  Notation POST := (rtarget_run_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB B lo m0).

  Definition KF (o : option bptr) (r : Z * option bptr) : M PState Z :=
    mbind (mbind (lib_free_opt raw_free o) (fun _ => mret ((if fst r =? 0 then 0 else 1), snd r)))
          (fun r2 => mbind (mupd (set_x_ps (snd r2))) (fun _ => mret (fst r2))).

  Lemma nodup_map_unique : forall (l : list block) x y, List.NoDup (map blk_id l) -> In x l -> In y l -> blk_id x = blk_id y -> x = y.
  Proof.
    induction l as [|b l IH]; intros x y ND Hx Hy E; [destruct Hx|].
    cbn [map] in ND. inversion ND as [|b' l' NI ND']; subst.
    destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | exact (IH x y ND' Hx Hy E)].
    - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
    - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  Qed.
  Lemma vec_block_unique : forall st LL mm q A0 Av, RHEAP st LL mm -> In (q, A0, 8) LL -> In (q, Av, 8) LL -> A0 = Av.
  Proof.
    intros st LL mm q A0 Av HP H1 H2. pose proof (nodup_map_unique LL _ _ (HND _ _ _ HP) H1 H2 eq_refl) as E. inversion E. reflexivity.
  Qed.

  Lemma tr_tail : forall xb X (pv : bptr) (Av : Z) D owned o st (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s7v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    TENV xb X (Some pv) D st m -> OWNED X D owned o -> xb = [(pv, Av, 8)] -> frm0 fc ->
    implM usegs (KF o (0, Some pv)) st POST
      (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
               (wz owned) s3v (wz RINIT_FLAG) (wz 0) (wz 0) s7v S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz 0x3eb4c) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros TE OW -> FRM. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    unfold TENV in TE. destruct TE as (HP & LXS & LXF & VEC & AEXT & SEW & AUX & ST & [errv ERR] & MI & SOF & [X5 X6] & [j0 FR] & PRES & POK & _).
    cbn [vB vN] in LXF, AEXT.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    unfold FRAME, RINIT_FLAG in *. cbv beta delta [MallocRep.wz] in *.

    destruct VEC as (A0 & IN0 & VC & HW).
    assert (EA : A0 = Av) by (eapply (vec_block_unique _ _ _ _ _ _ HP IN0); left; reflexivity). subst A0. clear IN0.
    pose proof (HBR _ _ _ _ HP ltac:(left; reflexivity)) as BRV. cbn [blk_addr blk_size fst snd] in BRV.
    pose proof BRV as (BV1 & _ & _ & BV4 & BV5). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BV4; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    unfold KF. cbn [fst snd Z.eqb].
    destruct o as [pb|]; cbn [OWNED] in OW; destruct OW as [-> ->]; cbn [lib_free_opt app] in HP, POK |- *.
    -
      assert (HPs : RHEAP st ((pb, D, plen) :: (pv, Av, 8) :: LB) m) by (eapply RHEAP_perm; [exact HP| apply Permutation.perm_swap]).
      apply implM_bind_assoc.
      unfold implM. iprefix. do 2 zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st POST msx) end.
      eapply implM_bind.
      { unfold RFREE_SYM in FREE. eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m st ((pb, D, plen) :: (pv, Av, 8) :: LB) pb D plen lo B errv);
          [exact HPs| left; reflexivity| exact AUX| rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; exact ST| exact LOC| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
          | exact ERR| exact MI| exact TP| reflexivity]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & HP2).
      rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x3eb54)) with (Z_to_bv 64 0x3eb54) by (symmetry; rpc).
      rewrite (lb_remove_head pb D plen ((pv, Av, 8) :: LB) (HND _ _ _ HPs)) in HPR, HP2.
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG.
      assert (FR2 : rw_cells usegs m2 (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      { eapply rw_cells_agree; [exact AG| exact FR| intros a Ha; left; cbn in Ha; lia]. }
      apply implM_ret_bind. cbv beta. cbn [fst snd]. apply implM_upd_bind. apply implM_ret.
      steps_to 0x3eb88%Z. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z].
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m2, errv, pv, Av.
      Ltac cliA := right; left; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP.
      split; [reflexivity|]. split; [lia|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|].
      split; [eapply RHEAP_ext; [exact HP2| destruct st'; reflexivity| destruct st'; reflexivity]|].
      split; [destruct st'; reflexivity|].
      split. { exists Av. split; [left; reflexivity|]. split.
               - eapply rw_cells_agree; [exact AG| exact VC|]. intros a Ha. cliA. unfold imp_vec_cells, IMP_VEC_LO in Ha. cbn in Ha. unfold IMP_VEC_LO. lia.
               - eapply rw_cells_agree; [exact AG| exact HW|]. intros a Ha. right; right. exists (pv, Av, 8). split; [left; reflexivity| cbn in Ha |- *; lia]. }
      split; [eapply lx_statics_agree; [exact AG| | exact LXS]; intros a Ha; cliA; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *; lia|].
      split; [eapply sj_statics_agree; [exact AG| | exact LXF]; intros a Ha; cliA; unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *; lia|].
      split; [eapply stderr_wfile_agree; [exact AG| | exact SEW]; intros a Ha; cliA; unfold stderr_addr in *; lia|].
      split; [exact (RHEAP_ssp _ _ _ HP2)|].
      split; [replace (ps_so (set_x_ps (Some pv) st')) with (ps_so st) by (destruct st'; cbn in ESO |- *; symmetry; exact ESO); eapply stdout_file_agree; [exact AG| | exact SOF]; intros a Ha; cliA; unfold stdout_addr in *; lia|].
      split. { split; [| split]; [eapply aex_tbl_agree'; [exact AG| | exact AEXT]; intros a Ha; cliA; lia | ..];
               (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; cliA; cbn in Ha; unfold RLATCH, RINCB in *; lia]). }
      eapply rdrv_pres_trans; [exact PRES|]. apply rdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HPR| lia| intros bb Hb; right; exact Hb].
    -
      apply implM_bind_assoc. apply implM_ret_bind. apply implM_ret_bind. cbv beta. cbn [fst snd]. apply implM_upd_bind. apply implM_ret. do 2 zstep.
      eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms1 ->.
      replace (ret_pc (Z_to_bv 64 0x3eb54)) with (Z_to_bv 64 0x3eb54) by (symmetry; rpc).
      steps_to 0x3eb88%Z. zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold rtarget_run_post, RINIT_FLAG. cbn [Z.eqb Z.ltb Z.b2z app] in HP |- *.
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m, errv, pv, Av.
      split; [reflexivity|]. split; [lia|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
      split; [exact ERR|]. split; [exact AUX|].
      split; [eapply RHEAP_ext; [exact HP| destruct st; reflexivity| destruct st; reflexivity]|].
      split; [destruct st; reflexivity|].
      split; [exists Av; split; [left; reflexivity| split; [exact VC| exact HW]]|].
      split; [exact LXS|]. split; [exact LXF|]. split; [exact SEW|]. split; [exact (RHEAP_ssp _ _ _ HP)|].
      split; [destruct st; exact SOF|]. split; [split; [exact AEXT| split; [exact X5| exact X6]]|]. exact PRES.
  Qed.

  Ltac trX1 AG X := eapply rw_cells_agree; [exact AG| exact X|]; intros a Ha; cbn in Ha; split;
    [ unfold LXW_CLIENT, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI; cbn; lia
    | right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia ].

  Lemma tr_loop : forall (k : nat) (rc0 : Z) xb X v D owned o st (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (1 <= k)%nat -> Z.of_nat k <= 4 ->
    TENV xb X v D st m -> OWNED X D owned o -> frm0 fc ->
    implM usegs (mbind (run_calls lops payload k rc0 v) (fun r => KF o r)) st POST
      (MS (mkR x1 (wz (usp + -80)) gp tp t0 t1 t2 (wz plen) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
               (wz owned) s3v (wz RINIT_FLAG) (wz (Z.of_nat k)) (wz 0) (wz (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz 0x3eb14) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until m; intros K1 K4 TE OW FRM; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    unfold RINIT_FLAG in *. cbv beta delta [MallocRep.wz] in TP |- *.
    cbn [run_calls]. cbn [bind ret lops Target.ops out_stdout].
    apply implM_bind_assoc.

    pose proof TE as TE0. unfold TENV, TENVb, aexb in TE. destruct TE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & (_ & X6) & _).
    pose proof (munch_refl [(0xf32a4, 0xf32a5)] m) as MUa. pose proof (wmono_refl usegs m) as WMa.
    unfold implM. iprefix. zstep. zstep; fix_sb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (TENV_incb xb X v D st m mc 0 1 TE0 MUa WMa MI X6) as TE1 end.
    clear TE0 MUa WMa X6.
    destruct TE1 as (HP & LXS & LXF & VEC & AEXT & SEW & AUX & ST & [errv ERR] & MI1 & SOF & (X5 & X6) & [j0 FR] & PRES & POK & XOK).
    unfold FRAME in FR.

    do 3 zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st POST msx) end.
    eapply implM_bind.
    { unfold LX_FUZZ in FUZZ.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (FUZZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc st (xb ++ X ++ LB) D payload v lo B errv rr_guard);
        [exact HP| exact LXS| exact LXF| exact VEC| exact AEXT| exact SEW| exact (RHEAP_ssp _ _ _ HP)| exact AUX
        | rewrite unsigned_lit by lia; lia| exact B63| rewrite unsigned_lit by lia; exact ST| exact LOC| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia
        | exact ERR| exact TP| exact MI1
        | rewrite unsigned_lit by lia; replace (usp + -80) with (usp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
        | exact POK| exact FRM| reflexivity| rewrite F3; reflexivity] end. }
    cbv beta. intros rc st1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1' & fc1 & m2 & pn & OW' & -> & ESND & EFST & -> & XN & LPE & LXF1 & VEC1 & AEX1 & POK1).
    destruct LPE as ((errv1 & ENV1) & FRM1 & LXP & ESO & EFA).
    destruct ENV1 as (HP1 & LXS1 & _ & SEW1 & SSP1 & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI2).
    rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in LXP by lia.
    replace (ret_pc (Z_to_bv 64 0x3eb28)) with (Z_to_bv 64 0x3eb28) by (symmetry; rpc).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP) as AG1.
    destruct rc as [rcz rcv]. cbn [fst snd] in ESND, EFST |- *. subst rcz rcv.

    assert (TE2 : TENVb (OW' ++ xb) X (Some pn) D st1 m2 1).
    { unfold TENVb, aexb, FRAME. cbn [vB vN]. rewrite <- !app_assoc.
      split; [exact HP1|]. split; [exact LXS1|]. split; [exact LXF1|]. split; [exact VEC1|]. split; [exact AEX1|]. split; [exact SEW1|].
      split; [exact AUX1|]. split; [exact ST1|]. split; [exists errv1; exact ERR1|]. split; [exact MI2|].
      split. { rewrite ESO. eapply stdout_file_agree; [exact AG1| | exact SOF]. intros a Ha. apply stdout_addr_client; [exact Ha|].
               unfold stdout_addr in Ha. unfold LXW_CLIENT, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn. lia. }
      split. { split; [trX1 AG1 X5| trX1 AG1 X6]. }
      split. { exists j0. eapply rw_cells_agree; [exact AG1| exact FR|]. intros a Ha. apply stack_client; [cbn in Ha; lia|].
               cbn in Ha. unfold LXW_CLIENT, LXW_IMP, LXW_SJ, LXW_AEX, LXW_UNW, LXW_TP, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn. lia. }
      split. { eapply rdrv_pres_trans; [exact PRES|]. apply rdrv_pres_of_lx. eapply lx_pres_weaken; [exact LXP| lia| intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb| auto]. }
      split. { apply payload_ok_app'. exact POK1. }
      destruct v as [q0|]; cbn [xok xnew] in XOK, XN |- *.
      - destruct XN as [-> ->]. exact XOK.
      - destruct XN as [Av ->]. subst xb. exists Av. reflexivity. }
    clear HP LXS LXF VEC AEXT SEW AUX ST ERR MI1 SOF X5 FR PRES POK AG1 LXP HP1 LXS1 SEW1 SSP1 AUX1 ST1 ERR1 POK1 LXF1 VEC1 AEX1.

    assert (X6' : rw_cells usegs m2 0xf32a4 [C1 (Z_to_bv 8 1)]) by (destruct TE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & X6') & _); exact X6').
    clear X6.
    pose proof (munch_refl [(0xf32a4, 0xf32a5)] m2) as MUb. pose proof (wmono_refl usegs m2) as WMb.
    apply implM_bind_assoc.
    unfold implM. iprefix. zstep. zstep; fix_sb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (TENV_incb (OW' ++ xb) X (Some pn) D st1 m2 mc 1 0 TE2 MUb WMb MI2 X6') as TE3 end.
    clear TE2 MUb WMb X6'.
    destruct TE3 as (HP3 & LXS3 & LXF3 & VEC3 & AEXT3 & SEW3 & AUX3 & ST3 & [errv3 ERR3] & MI3 & SOF3 & AEX3 & [j3 FR3] & PRES3 & POK3 & XOK3).

    replace (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0 by reflexivity.
    do 2 zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 POST msx) end.
    eapply implM_bind.
    { eapply implM_keepsf; [| apply stdout_vprintf_keeps].
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (EMIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1' fc1 mc st1 lo rr_guard);
        [apply ps_get_set| apply ps_set_set| exact FWXO| exact SOF3| rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST3| rewrite unsigned_lit by lia; unfold EMIT_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; lia| exact (RHEAP_ssp _ _ _ HP3)| exact MI3| exact FRM1] end. }
    cbv beta. intros [] st2 ms2 [PO EBS].
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2' & fc2 & m4 & -> & MU2 & WM2 & MI4 & FRM2 & HF2 & ST4 & SOF4 & SSP4).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in ST4 by lia.
    replace (ret_pc (Z_to_bv 64 0x3eb38)) with (Z_to_bv 64 0x3eb38) by (symmetry; rpc).
    destruct (but_so_eq _ _ EBS) as (EM2 & EBRK2 & EFA2).
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
    assert (OUT2 : forall a, (usp + -80 <= a \/ (0xdb000 <= a < 0x117000 /\ ~ stdout_addr a) \/ (a < lo /\ (a < 0x10000 \/ 0x117000 <= a))) ->
                             outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a).
    { intros a Ha. unfold stdout_addr in Ha. cbn. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    unfold FRAME, aexb in FR3, AEX3. destruct AEX3 as (Y5 & Y6).
    assert (TE4 : TENV (OW' ++ xb) X (Some pn) D st2 m4).
    { unfold TENV, TENVb, aexb, FRAME. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]]]]].
      - eapply RHEAP_ext; [| exact EM2| exact EBRK2].
        eapply HFRAME; [exact HP3| exact MU2| exact WM2|].
        constructor; [left; cbn [fst]; exact LOC|]. constructor; [| constructor; [| constructor]];
          right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
      - eapply lx_statics_agree; [exact AG2| | exact LXS3]. intros a Ha. apply OUT2. right; left.
        unfold lxs_addr, stdout_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *. lia.
      - eapply sj_statics_agree; [exact AG2| | exact LXF3]. intros a Ha. apply OUT2. right; left. unfold sjs_addr, stdout_addr, SJ_STATICS_LO, SJ_STATICS_HI in *. lia.
      - eapply imp_vec_agree'; [exact AG2| | | exact VEC3]; intros a Ha; apply OUT2; [right; left; unfold stdout_addr; lia|].
        right; right. pose proof (blocks_below _ _ _ _ HP3 Ha). lia.
      - eapply aex_tbl_agree'; [exact AG2| | exact AEXT3]. intros a Ha. apply OUT2. right; left. unfold stdout_addr. lia.
      - eapply stderr_wfile_agree; [exact AG2| | exact SEW3]. intros a Ha. apply OUT2. right; left. unfold stderr_addr, stdout_addr in *. lia.
      - eapply rauxv_ok_agree; [exact AG2| | | exact AUX3]; intros a Ha; apply OUT2; [left; lia| right; left]. unfold RAUXV_CELL, stdout_addr in *. lia.
      - exact ST4.
      - exists errv3. eapply rw_cells_agree; [exact AG2| exact ERR3|]. intros a Ha. apply OUT2. right; left. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. unfold stdout_addr. lia.
      - exact MI4.
      - exact SOF4.
      - split; (eapply rw_cells_agree; [exact AG2| eassumption| intros a Ha; apply OUT2; right; left; cbn in Ha; unfold stdout_addr; lia]).
      - exists j3. eapply rw_cells_agree; [exact AG2| exact FR3|]. intros a Ha. apply OUT2. left. cbn in Ha. lia.
      - eapply rdrv_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU2| exact WM2|].
        intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUT2.
        + left. lia.
        + right; right. pose proof (HBR _ _ _ _ HP3 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb))))) as (R1 & R2 & R3 & R4 & R5). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
        + right; left. split; [exact Ha|]. intros Hso. apply HX. unfold stdout_addr in Hso. unfold DRVW. cbn. lia.
      - destruct POK3 as (PB & PF & PD & PD2 & PD3 & PIN). split; [| split; [exact PF| split; [exact PD| split; [exact PD2| split; [exact PD3| exact PIN]]]]].
        eapply bytes_at_agree; [exact AG2| exact PB|]. intros a Ha. rewrite to_bytes_length in Ha.
        destruct PIN as [EP|(b & Hb & Hr1 & Hr2)]; [rewrite EP in Ha; cbn in Ha; lia|].
        apply OUT2. right; right. pose proof (HBR _ _ _ _ HP3 Hb) as (R1 & R2 & R3 & R4 & R5). unfold zlength, OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      - exact XOK3. }

    cbv beta delta [MallocRep.wz].
    unfold implM. iprefix. zstep.
    zstep.
    if_true.
    zstep. rewrite (swrap32_id (Z.of_nat (S k) + -1)) by lia. replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    zstep. if_cases HK; zify_cond HK.
    -
      apply evt_done. apply (IH 0 (OW' ++ xb) X (Some pn) D owned o st2); [lia| lia| exact TE4| exact OW| exact FRM2].
    -
      apply evt_done. cbn [run_calls ret lops Target.ops]. apply implM_ret_bind.
      replace k with 0%nat by lia. cbn [Z.of_nat fst snd].
      pose proof TE4 as TE5. destruct TE5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [Av EXB]).
      eapply (tr_tail (OW' ++ xb) X pn Av D owned o st2); [exact TE4| exact OW| exact EXB| exact FRM2].
  Qed.

  Lemma payload_bytes : forall m, bytes_at usegs m A (to_bytes content) -> bytes_at usegs m PAY (to_bytes payload).
  Proof.
    intros m H. unfold PAY, payload, to_bytes in *. rewrite <- (firstn_skipn (Z.to_nat (6 + L)) content) in H.
    rewrite map_app in H. apply bytes_at_app in H as [_ H]. rewrite length_map, length_firstn in H.
    replace (A + Z.of_nat (Init.Nat.min (Z.to_nat (6 + L)) (length content))) with (A + 6 + L) in H by (unfold zlength in L6; lia). exact H.
  Qed.

  Theorem tr_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (errv : word),
    RHEAP s LB m0 -> bytes_at usegs m0 A (to_bytes content) ->
    lx_statics m0 -> sj_statics m0 false -> imp_vec m0 LB None -> stderr_wfile m0 -> stdout_file m0 (ps_so s) ->
    aex_cells m0 0 -> rw_cells usegs m0 RGOT_LLVMINIT [C8 (wz 0)] ->
    rauxv_ok m0 B -> stk usegs m0 lo usp -> rw_cells usegs m0 (errno_addr tp) [C4 errv] -> mem_inv usegs m0 -> frm0 fc ->
    implM usegs (run cfg payload) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz (A + 2)) (wz L) (wz PAY) (wz plen) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz RTARGET_RUN) fc None m0 (seg_rom usegs)).
  Proof.
    intros until errv. intros HP0 CT0 LXS0 LXF0 VEC0 SEW0 SOF0 AEX0 GOT0 AUX0 ST0 ERR0 MI0 FRM.
    destruct (RHEAP_libc_head _ _ _ HP0) as (cdt & thr & sec & tm1 & LCH0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOC as LOC'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in LOC'; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof facts as (F1 & F2 & F3 & F4 & F5).
    unfold run, Target.target_run, ImpModel.target_run. cbn [bind ret lib_malloc lib_free Target.ops unreachable].
    change (Target.ops raw_malloc raw_free ps_so set_so_ps) with lops. rewrite F3.
    change (Z.to_nat (Z.land cfg 3 + 1)) with (Z.to_nat calls).
    unfold RTARGET_RUN. unfold implM. iprefix.
    eapply tr_pre; [exact ST0| exact MI0| exact AEX0| exact GOT0| exact LCH0|]. clear t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6. intros m1 j0 x1 t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 FR1 ST1 MU1 WM1 MI1 AEX1 LAT1 INCB1 GOT1.
    unfold RTARGET_RUN_STACK, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    unfold RINIT_FLAG, RLATCH, RINCB in *. cbv beta delta [MallocRep.wz] in TP |- *.
    pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
    assert (OUT1 : forall a, (usp <= a \/ (0xdb000 <= a < 0x117000 /\ ~ (996000 <= a < 996005) /\ ~ (0x115590 <= a < 0x1156c8)) \/ (a < lo /\ (a < 0x10000 \/ 0x117000 <= a))) ->
                             outside [(usp + -128, usp); (996000, 996000 + 5); (0x115590, 0x1156c8)] a).
    { intros a Ha. cbn. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in LOC; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
    assert (HP1 : RHEAP s LB m1).
    { eapply HFRAME; [exact HP0| exact MU1| exact WM1|]. constructor; [left; cbn [fst]; unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia|].
      constructor; [| constructor; [| constructor]]; right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia. }
    pose proof (HBR _ _ _ _ HP0 INB) as BRA. cbn [blk_addr blk_size fst snd] in BRA. unfold rblock_range, OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BRA; try (pose proof alloc_ceiling_range as CEIL_RANGE__). destruct BRA as (BRA1 & BRA2 & BRA3 & BRA4 & BRA5).
    assert (CT1 : bytes_at usegs m1 A (to_bytes content)).
    { eapply bytes_at_agree; [exact AG1| exact CT0|]. intros a Ha. rewrite to_bytes_length in Ha. apply OUT1. right; right.
      unfold zlength in *. lia. }
    assert (LXS1 : lx_statics m1).
    { eapply lx_statics_agree; [exact AG1| | exact LXS0]. intros a Ha. apply OUT1. right; left.
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *. lia. }
    assert (LXF1 : sj_statics m1 false).
    { eapply sj_statics_agree; [exact AG1| | exact LXF0]. intros a Ha. apply OUT1. right; left. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *. lia. }
    assert (VEC1 : imp_vec m1 LB None).
    { eapply imp_vec_agree'; [exact AG1| | | exact VEC0]; intros a Ha; apply OUT1; [right; left; lia|]. right; right. pose proof (blocks_below _ _ _ _ HP0 Ha). lia. }
    assert (SEW1 : stderr_wfile m1).
    { eapply stderr_wfile_agree; [exact AG1| | exact SEW0]. intros a Ha. apply OUT1. right; left. unfold stderr_addr in *. lia. }
    assert (SOF1 : stdout_file m1 (ps_so s)).
    { eapply stdout_file_agree; [exact AG1| | exact SOF0]. intros a Ha. apply OUT1. right; left. unfold stdout_addr in *. lia. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_agree; [exact AG1| | | exact AUX0]; intros a Ha; apply OUT1; [left; lia| right; left]. unfold RAUXV_CELL in *. lia. }
    assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_agree; [exact AG1| exact ERR0|]. intros a Ha. apply OUT1. right; left. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia. }
    assert (PRES1 : rdrv_pres LB usp m0 m1).
    { eapply lx_pres_of_munch; [exact MU1| exact WM1|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha Hs]]]]; apply OUT1.
      - left. lia.
      - right; right. pose proof (HBR _ _ _ _ HP0 Hb) as (R1 & R2 & R3 & R4 & R5). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia.
      - right; left. split; [exact Ha|]. split; intros Hi; apply HX; unfold DRVW, RINIT_FLAG; cbn; lia. }
    eapply tr_mid; [exact FR1| exact MI1| exact CT1| |].
    -
      intros a0'' NZ. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
      cbv beta delta [MallocRep.wz]. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POST msx) end.
      apply implM_bind_assoc. apply implM_bind_assoc. eapply implM_bind.
      { unfold RMALLOC_SYM in MALLOC.
        eapply (MALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB plen lo B errv);
          [exact HP1| exact AUX1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact LOC
          | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| exact ERR1| exact MI1| exact TP| reflexivity| lia]. }
      cbv beta. intros r st1 ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & RES).
      rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x3eac0)) with (Z_to_bv 64 0x3eac0) by (symmetry; rpc).
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG2.
      Ltac cli := right; left; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP.
      assert (FR2 : rw_cells usegs m2 (usp + -80) [CB 8 j0; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      { eapply rw_cells_agree; [exact AG2| exact FR1| intros a Ha; left; cbn in Ha; lia]. }
      assert (LXS2 : lx_statics m2).
      { eapply lx_statics_agree; [exact AG2| | exact LXS1]. intros a Ha. cli. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *. lia. }
      assert (LXF2 : sj_statics m2 false).
      { eapply sj_statics_agree; [exact AG2| | exact LXF1]. intros a Ha. cli. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *. lia. }
      assert (VEC2 : imp_vec m2 LB None).
      { eapply imp_vec_agree'; [exact AG2| | | exact VEC1]; intros a Ha; [cli; lia| right; right; exact Ha]. }
      assert (SEW2 : stderr_wfile m2).
      { eapply stderr_wfile_agree; [exact AG2| | exact SEW1]. intros a Ha. cli. unfold stderr_addr in *. lia. }
      assert (SOF2 : stdout_file m2 (ps_so st1)).
      { rewrite ESO. eapply stdout_file_agree; [exact AG2| | exact SOF1]. intros a Ha. cli. unfold stdout_addr in *. lia. }
      assert (AEX2 : aex_tbl m2 2) by (eapply aex_tbl_agree'; [exact AG2| | exact AEX1]; intros a Ha; cli; lia).
      assert (LAT2 : rw_cells usegs m2 996000 [C1 (Z_to_bv 8 1)]) by (eapply rw_cells_agree; [exact AG2| exact LAT1| intros a Ha; cli; cbn in Ha; lia]).
      assert (INCB2 : rw_cells usegs m2 996004 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_agree; [exact AG2| exact INCB1| intros a Ha; cli; cbn in Ha; lia]).
      assert (CT2 : bytes_at usegs m2 A (to_bytes content)).
      { eapply bytes_at_agree; [exact AG2| exact CT1|]. intros a Ha. rewrite to_bytes_length in Ha. right; right. exists (p, A, cap). split; [exact INB|]. cbn [blk_addr blk_size fst snd]. unfold zlength in *. lia. }
      assert (PRES2 : rdrv_pres LB usp m0 m2).
      { eapply rdrv_pres_trans; [exact PRES1|]. apply rdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HPR| lia| auto]. }
      destruct r as [pb|].
      +
        destruct RES as (A' & junk & -> & BR & HP2 & BLK & _).
        pose proof BR as BR0. unfold rblock_range, OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BR0; try (pose proof alloc_ceiling_range as CEIL_RANGE__). destruct BR0 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
        apply implM_ret_bind. cbv beta iota. apply implM_bind_assoc.
        unfold implM. iprefix. zstep. if_cases HA; [apply wz_eqb0 in HA; lia|].
        do 3 zstep. zstep.
        pose proof (payload_bytes _ CT2) as PB2.
        assert (SEP : PAY + plen <= A' \/ A' + plen <= PAY).
        { pose proof (HBD _ _ _ _ _ HP2 (or_intror _ INB) (or_introl eq_refl)) as D. cbn [blk_id blk_addr blk_size fst snd] in D.
          pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
          assert (NE : p <> pb) by (intros E; apply NI; rewrite <- E; apply in_map_iff; exists (p, A, cap); split; [reflexivity| exact INB]).
          specialize (D NE). unfold PAY, plen in *. unfold zlength in *. lia. }
        eapply evt_cut.
        { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (to_bytes payload) junk);
            rewrite ?unsigned_lit by (unfold PAY, zlength in *; lia);
            [exact PB2| rewrite to_bytes_length; unfold zlength in F3; lia| exact BLK| exact SEP| exact MI2]. }
        cbv beta. intros ms3 PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & BLK3 & PB3).
        rewrite !unsigned_lit in MU3 by (unfold PAY, zlength in *; lia). rewrite !unsigned_lit in BLK3 by lia. rewrite !unsigned_lit in PB3 by (unfold PAY, zlength in *; lia).
        replace (ret_pc (Z_to_bv 64 0x3ead4)) with (Z_to_bv 64 0x3ead4) by (symmetry; rpc).
        pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
        assert (OUT3 : forall a, (0x10000 <= a < 0x117000 \/ lo <= a \/ in_block LB a) -> outside [(A', A' + plen)] a).
        { intros a Ha. cbn. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| lia|].
          pose proof (HBD _ _ _ _ _ HP2 (or_intror _ Hb) (or_introl eq_refl)) as D. cbn [blk_id blk_addr blk_size fst snd] in D.
          pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
          assert (NE : blk_id b <> pb) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
          specialize (D NE). lia. }
        Ltac cl3 OUT3 := apply OUT3; left.
        assert (TE3 : TENV [] [(pb, A', plen)] None A' st1 m3).
        { unfold TENV, TENVb, FRAME, RINIT_FLAG, aexb. cbn [app vB vN xok].
          split. { eapply HFRAME; [exact HP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (pb, A', plen). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
          split. { eapply lx_statics_agree; [exact AG3| | exact LXS2]. intros a Ha. cl3 OUT3. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *. lia. }
          split. { eapply sj_statics_agree; [exact AG3| | exact LXF2]. intros a Ha. cl3 OUT3. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *. lia. }
          split. { unfold imp_vec in VEC2 |- *. eapply rw_cells_agree; [exact AG3| exact VEC2|]. intros a Ha. cl3 OUT3. unfold IMP_VEC_LO in Ha. cbn in Ha. lia. }
          split. { eapply aex_tbl_agree'; [exact AG3| | exact AEX2]. intros a Ha. cl3 OUT3. lia. }
          split. { eapply stderr_wfile_agree; [exact AG3| | exact SEW2]. intros a Ha. cl3 OUT3. unfold stderr_addr in *. lia. }
          split. { eapply rauxv_ok_agree; [exact AG3| | | exact AUX2]; intros a Ha; apply OUT3; [right; left; unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia| left]. unfold RAUXV_CELL in *. lia. }
          split. { eapply stk_agree; [exact AG3| exact ST2| intros a Ha; apply OUT3; right; left; lia]. }
          split. { exists errv2. eapply rw_cells_agree; [exact AG3| exact ERR2|]. intros a Ha. cl3 OUT3. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. lia. }
          split; [exact MI3|].
          split. { eapply stdout_file_agree; [exact AG3| | exact SOF2]. intros a Ha. cl3 OUT3. unfold stdout_addr in *. lia. }
          split. { split; (eapply rw_cells_agree; [exact AG3| eassumption| intros a Ha; cl3 OUT3; cbn in Ha; lia]). }
          split. { exists j0. eapply rw_cells_agree; [exact AG3| exact FR2|]. intros a Ha. apply OUT3. right; left. cbn in Ha. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__). lia. }
          split. { eapply rdrv_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU3| exact WM3|].
                   intros a [HX [Ha|[Hb|[Ha Hs]]]]; apply OUT3; [right; left; unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia| right; right; exact Hb| left; lia]. }
          split; [| reflexivity].
          unfold payload_ok. destruct BLK3 as [[_ PBD] _]. cbn [cells_bytes cbytes] in PBD. rewrite app_nil_r in PBD.
          split; [exact PBD|]. split; [unfold payload; apply Forall_skipn; exact CR|]. split; [lia|]. split; [lia|]. split; [lia|].
          right. exists (pb, A', plen). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
        do 4 zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 POST msx) end.
        replace calls with (Z.of_nat (Z.to_nat calls)) at 2 by lia.
        apply (tr_loop (Z.to_nat calls) 0 [] [(pb, A', plen)] None A' A' (Some pb) st1); [lia| lia| exact TE3| split; reflexivity| exact FRM].
      +
        destruct RES as [-> HP2].
        apply implM_ret_bind. cbv beta iota. apply implM_unr.
    -
      intros a0'' EZ. rewrite (proj2 (Z.eqb_eq _ _) EZ).
      cbv beta delta [MallocRep.wz]. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POST msx) end.
      apply implM_bind_assoc. apply implM_ret_bind. cbv beta iota. apply implM_bind_assoc.
      assert (EP : payload = []) by (destruct payload; [reflexivity| unfold zlength in F3; cbn in F3; lia]).
      replace calls with (Z.of_nat (Z.to_nat calls)) at 2 by lia.
      apply (tr_loop (Z.to_nat calls) 0 [] [] None REMPTY 0 None s); [lia| lia| | split; reflexivity| exact FRM].
      unfold TENV, TENVb, FRAME, RINIT_FLAG, aexb. cbn [app vB vN xok].
      split; [exact HP1|]. split; [exact LXS1|]. split; [exact LXF1|]. split; [exact VEC1|]. split; [exact AEX1|]. split; [exact SEW1|]. split; [exact AUX1|].
      split; [exact ST1|]. split; [exists errv; exact ERR1|]. split; [exact MI1|]. split; [exact SOF1|]. split; [split; [exact LAT1| exact INCB1]|].
      split; [exists j0; exact FR1|]. split; [exact PRES1|]. split; [| reflexivity].
      rewrite EP. unfold payload_ok, REMPTY, LX_EMPTY, zlength. cbn [to_bytes map length Z.of_nat].
      split; [apply bytes_at_nil; lia|]. split; [constructor|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
  Qed.
End TR.

Theorem rtarget_run_proof :
  rmalloc_stmt -> rfree_stmt -> rfree_null_stmt -> rfuzz_one_stmt -> @emit_printf_stmt PState ps_so set_so_ps -> fwritex_stdout_stmt ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtarget_run_stmt.
Proof.
  intros MALLOC FREE FREE0 FUZZ EMIT FWXO HFRAME HBR HND HBD.
  unfold rtarget_run_stmt. intros until errv.
  intros HP INB CT CR LEN1 CAP L0 L6 LXS LXF VEC PSX SEW SSP SOF AEX GOT AUX SPB B63 ST LOC LOG LOSP ERR TP MI FRM SP16 -> -> -> ->.
  eapply (tr_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB p A cap L content B lo
            INB CR LEN1 CAP L0 L6 SPB B63 LOC LOG LOSP TP SP16 MALLOC FREE FREE0 FUZZ EMIT FWXO HFRAME HBR HND HBD m);
    eassumption.
Qed.
End WithCeiling0.
