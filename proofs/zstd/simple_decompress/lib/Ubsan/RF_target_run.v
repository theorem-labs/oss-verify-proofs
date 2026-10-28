(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac Amo_tac Keeps F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Adapter Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac clia := atop_facts; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rcT : runConstT}.
Lemma land3_range : forall c, 0 <= c -> 0 <= Z.land c 3 <= 3.
Proof.
  intros c Hc. split; [apply Z.land_nonneg; lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound c 4 ltac:(lia)). change (2^2) with 4. lia.
Qed.

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma snez_norm : forall rc, -2^63 < rc < 2^63 -> Z.b2z (0 <? Z.land rc 18446744073709551615) = (if rc =? 0 then 0 else 1).
Proof.
  intros rc Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eqb_spec rc 0) as [->|NE]; [reflexivity|].
  destruct (Z.ltb_spec0 0 (rc mod 2^64)) as [L|G]; [reflexivity|]. exfalso.
  pose proof (Z.mod_pos_bound rc (2^64) ltac:(lia)). assert (E : rc mod 2^64 = 0) by lia.
  apply Znumtheory.Zmod_divide in E; [| lia]. destruct E as [q E]. assert (q = 0) by lia. subst q. lia.
Qed.

(* [comment removed for export] *)
Lemma rc_ok_iff : forall r, -2^31 <= r < 2^31 ->
  18446744073709551614 <= Z.land (bv_swrap 32 (Z.land r 18446744073709551615 + -1)) 18446744073709551615 <-> (r = 0 \/ r = -1).
Proof.
  intros r Hr. change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31). change (2 ^ Z.of_N 64) with (2^64).
  split.
  - intros H. Z.div_mod_to_equations. lia.
  - intros [-> | ->]; vm_compute; discriminate.
Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; cbn; [constructor|].
  inversion H; subst. apply IH. assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x69000 <= lo ->
  atexit_cells false m ->
  rw_cells usegs m 0x68488 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv usegs m -> a0 = Z_to_bv 64 PAEF_GUARD ->
  evt usegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x68240, 0x68268); (0x68360, 0x68368)]%Z m m'    (* [comment removed for export] *)
      /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ atexit_cells true m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2dfd4) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LO LOLO [ATX ATXA] LCH MI ->.
  unfold atexit_cells, PATEXIT, PATEXIT_CALL, PAEF_GUARD in *. cbv iota beta in ATX. cbv iota beta in ATXA.
  change (426560 + 24)%Z with 426584%Z in *. change (426560 + 288)%Z with 426848%Z in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (426560, 426600); (426848, 426856)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x2e024%Z. replace (sx32 z64) with z64 by (vm_compute; reflexivity).      (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x2e078%Z. replace (sx32 z64) with z64 by (vm_compute; reflexivity).      (* [comment removed for export] *)
  steps_to 0x2e090%Z.
  release_frame FR ST (bv_unsigned sp).
  astep. astep.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact ATX| exact ATXA].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUN.
  (* [comment removed for export] *)
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FUZZ : fuzz_one_stmt.
  Hypothesis EMIT : emit_printf_stmt ps_so set_so_ps.
  Hypothesis FWXO : fwritex_stdout_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem)
            (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z).
  Hypothesis INLB : In (p, A, cap) LB.
  Hypothesis FC : Forall (fun c => 0 <= c < 256) content.
  Hypothesis LC : zlength content <= cap.
  Hypothesis CAP : cap <= 2^26.
  Hypothesis L0 : 0 <= L.
  Hypothesis L6 : 6 + L <= zlength content.
  Hypothesis SPAB : bv_unsigned sp <= AB.
  Hypothesis ABB : AB <= 2^47.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : ATOP <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PTARGET_RUN_STACK.

  Notation usp := (bv_unsigned sp).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).

  (* [comment removed for export] *)
  Definition plen : Z := zlength content - 6 - L.
  Definition PAY : Z := A + 6 + L.
  Definition payload : list Z := skipn (Z.to_nat (6 + L)) content.
  Definition cfg : Z := if 0 <? L then znth content 2 else 0.
  Definition calls : Z := 1 + Z.land cfg 3.

  (* [comment removed for export] *)
  Definition LBT (own : option (bptr * Z)) : list block :=
    match own with None => LB | Some (q, D) => (q, D, plen) :: LB end.
  Definition dptr (own : option (bptr * Z)) : Z := match own with None => PEMPTY | Some (_, D) => D end.
  Definition oreg (own : option (bptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.
  Definition omodel (own : option (bptr * Z)) : option bptr := match own with None => None | Some (q, _) => Some q end.

  (* [comment removed for export] *)
  Definition FRAME (m : mem) : Prop :=
    exists jb : list byte, rw_cells usegs m (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition INV0 (own : option (bptr * Z)) (st : PState) (iv : Z) (m : mem) : Prop :=
    FRAME m /\ bytes_at usegs m (dptr own) (zbytes payload) /\ harness_cells m /\ stderr_file0 m
    /\ (exists errv : word, rw_cells usegs m RERRNO [C4 errv])
    /\ mem_inv usegs m /\ stk usegs m lo (usp + -80) /\ rauxv_ok m AB
    /\ stdout_file m (ps_so st) /\ pdrv_pres LB usp m0 m
    /\ atexit_cells true m /\ rw_cells usegs m PAEF_INCB [C1 (Z_to_bv 8 iv)].      (* [comment removed for export] *)
  Definition INV (own : option (bptr * Z)) (st : PState) (m : mem) : Prop := RHEAP st (LBT own) m /\ INV0 own st 0 m.

  Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3w k bad t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (oreg own)) s3w (wz PINIT_FLAG) (wz k) (wz bad) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition RUNST (own : option (bptr * Z)) (pc : Z) (k bad : Z) (st : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3w t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3w k bad t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ INV own st m /\ (bad = 0 \/ bad = 1).

  (* [comment removed for export] *)
  Lemma facts : 0 <= plen /\ plen < 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + L.
  Proof.
    unfold calls, cfg, plen, payload, PAY. unfold zlength in *. rewrite length_skipn.
    assert (CF : 0 <= (if 0 <? L then znth content 2 else 0) < 256).
    { destruct (0 <? L); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
      assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
      pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
    pose proof (land3_range (if 0 <? L then znth content 2 else 0) ltac:(lia)).
    repeat split; lia.
  Qed.

  Lemma LO' : lo <= usp - 80 - HARNESS_STACK.
  Proof. unfold PTARGET_RUN_STACK in LO. lia. Qed.

  (* [comment removed for export] *)
  Lemma trun_init : forall (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState),
    stk usegs m lo usp -> mem_inv usegs m -> trun_cells0 m -> RHEAP st LB m ->
    (forall (m' : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 : word),
        FRAME m' -> stk usegs m' lo (usp + -80) -> harness_cells m' ->
        munch [(usp - 128, usp); (PINIT_FLAG, PINIT_FLAG + 1); (0x68240, 0x68268); (0x68360, 0x68368)] m m' ->
        wmono usegs m m' -> mem_inv usegs m' ->
        atexit_cells true m' -> rw_cells usegs m' PAEF_INCB [C1 (Z_to_bv 8 0)] ->
        evt usegs Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 x10 x11 x12 x13 x14 x15 x16 x17
                              a1 a0 (wz PINIT_FLAG) x22 x23 x24 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x146c0) fc None m' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 PTARGET_RUN) fc None m (seg_rom usegs)).
  Proof.
    intros until st. intros ST MI TR P K. pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    destruct TR as (PI & GFI & GSE & SEP & DCX & GTR & [ATX0 ATX0A] & INCB).      (* [comment removed for export] *)
    destruct (RHEAP_libc_head _ _ _ P) as (cdt & thr & sec & tm1 & LCH).
    unfold PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, PAEF_INCB, PATEXIT, PATEXIT_CALL, PAEF_GUARD, wz in *.
    cbv iota beta in ATX0. cbv iota beta in ATX0A. change (426560 + 24)%Z with 426584%Z in *. change (426560 + 288)%Z with 426848%Z in *.
    pose proof (munch_refl [(usp - 128, usp); (0x480f0, 0x480f0 + 1); (426560, 426600); (426848, 426856)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold PTARGET_RUN.
    zstep. carve_frame 80%nat ST.
    (* [comment removed for export] *)
    do 17 zstep. if_true.
    (* [comment removed for export] *)
    do 5 zstep.
    call_sp atexit_spec; [exact ST | lia | lia | split; [exact ATX0 | exact ATX0A] | exact LCH | exact MI | reflexivity | ].
    (* [comment removed for export] *)
    zstep. if_true. do 3 zstep. if_true.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
    - lazymatch goal with H : rw_cells usegs _ (usp + -80) _ |- _ => eexists; exact H end.
    - exact PC.
    - unfold harness_cells, PGOT_STDERR, PSTDERR_PTR, wz. repeat match goal with |- _ /\ _ => split end; assumption.
    - exact MU.
    - exact WM.
    - exact MI0.
    - exact POST.
    - exact INCB.
  Qed.

  (* [comment removed for export] *)
  Lemma block_facts : forall st own m, RHEAP st (LBT own) m ->
    0 < A /\ A + cap <= ATOP /\ (A + cap <= 0x10000 \/ 0x69000 <= A)
    /\ match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + plen <= ATOP /\ (D + plen <= 0x10000 \/ 0x69000 <= D) end.
  Proof.
    intros st own m P.
    assert (HB : In (p, A, cap) (LBT own)) by (destruct own as [[q D]|]; [right|]; exact INLB).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
    split; [lia|]. split; [lia|]. split; [lia|].
    destruct own as [[q D]|]; [| exact I].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P ltac:(left; reflexivity)) as (C1 & C2 & C3 & C4 & C5). cbn in C1, C2, C3, C4, C5.
    pose proof facts. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pdrv_pres_of_heap_sub : forall LB' SP' m m',
    rheap_pres LB' SP' m m' -> SP' <= usp -> (forall b, In b LB -> In b LB') -> pdrv_pres LB usp m m'.
  Proof.
    intros LB' SP' m m' HP HS HL. apply pdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HP| exact HS| exact HL].
  Qed.

  (* [comment removed for export] *)
  Definition iv_excluded (iv : Z * Z) : bool :=
    existsb (fun iv' => (fst iv' <=? fst iv) && (snd iv <=? snd iv')) pstdout_ivs.

  Lemma iv_excluded_in : forall iv a, iv_excluded iv = true -> fst iv <= a < snd iv -> rin_ivs pstdout_ivs a.
  Proof.
    intros iv a H Ha. unfold iv_excluded in H. apply existsb_exists in H. destruct H as (iv' & Hin & Hle).
    apply andb_prop in Hle. destruct Hle as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    revert Hin. generalize pstdout_ivs. intros l. induction l as [|[lo' hi'] l IH]; cbn; [tauto|].
    intros [E|Hin]; [left; subst iv'; cbn in *; lia| right; apply IH; exact Hin].
  Qed.

  Lemma pdrv_pres_of_munch : forall m m' W,
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => (snd iv <= usp /\ ATOP <= fst iv) \/ iv_excluded iv = true) W ->
    (forall b, In b LB -> blk_addr b + blk_size b <= ATOP) ->
    pdrv_pres LB usp m m'.
  Proof.
    intros m m' W MU WM HW HLB a Ha Hc Hx.
    destruct (magree_of_munch usegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
    clear MU WM. induction W as [|iv W IH]; cbn; [exact I|].
    inversion HW as [|iv' W' Hiv HW']; subst. destruct iv as [lo' hi']. cbn [fst snd] in Hiv. split; [| apply IH; exact HW'].
    destruct Hiv as [[H1 H2]|Hin].
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
      + lia.
      + atop_facts. lia.
      + pose proof (HLB b Hb). lia.
    - intros Hr. apply Hx. apply (iv_excluded_in (lo', hi') a Hin). cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac ivs_ok := repeat (constructor; [first [left; cbn [fst snd]; atop_facts; lia | right; vm_compute; reflexivity] |]); try constructor.

  Lemma LB_below : forall st own m, RHEAP st (LBT own) m -> forall b, In b LB -> blk_addr b + blk_size b <= ATOP.
  Proof.
    intros st own m P b Hb.
    assert (HB : In b (LBT own)) by (destruct own as [[q D]|]; [right|]; exact Hb).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (_ & _ & _ & B4 & _). exact B4.
  Qed.

  (* [comment removed for export] *)
  Ltac hp HPW C := eapply rheap_pres_rw_cells; [exact HPW| exact C| right; left; cbn; unfold PATEXIT, PAEF_INCB, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia].

  (* [comment removed for export] *)
  Lemma INV0_after_heap : forall own own' st st' iv LX SP' m m' (errv' : word),
    INV0 own st iv m ->
    rheap_pres LX SP' m m' -> SP' <= usp + -80 -> (forall b, In b LB -> In b LX) ->
    bytes_at usegs m' (dptr own') (zbytes payload) -> ps_so st' = ps_so st ->
    rw_cells usegs m' RERRNO [C4 errv'] -> mem_inv usegs m' -> stk usegs m' lo (usp + -80) -> rauxv_ok m' AB ->
    INV0 own' st' iv m'.
  Proof.
    intros own own' st st' iv LX SP' m m' errv' (FR & PB & HC & SE & _ & _ & _ & _ & SO & DP0 & [AX1 AX2] & IC) HP HS HL PB' ESO ERR' MI' ST' AUX'.
    assert (HPW : rheap_pres LB (usp + -80) m m') by (eapply rheap_pres_weaken; [exact HP| exact HS| exact HL]).
    unfold INV0, atexit_cells. unfold PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB in *. cbv iota beta in AX1. cbv iota beta in AX2. cbv iota beta.
    split. { destruct FR as [jb FR]. exists jb. eapply rheap_pres_rw_cells; [exact HPW| exact FR| left; cbn; lia]. }
    split; [exact PB'|].
    split.
    { destruct HC as (C5 & C6 & C7 & C8). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
      split; [hp HPW C5|]. split; [hp HPW C6|]. split; [hp HPW C7| hp HPW C8]. }
    split; [eapply stderr_file0_heap_pres; [exact HPW| exact SE]|].
    split; [exists errv'; exact ERR'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AUX'|]. split.
    { rewrite ESO. eapply stdout_file_heap_pres; [exact HPW| exact SO]. }
    split. { eapply pdrv_pres_trans; [exact DP0|]. eapply pdrv_pres_of_heap_sub; [exact HP| lia| exact HL]. }
    split; [split; [hp HPW AX1| hp HPW AX2]| hp HPW IC].
  Qed.

  (* [comment removed for export] *)
  Lemma INV0_after_harness : forall own st st' iv SP' m m' (errv' : word),
    RHEAP st (LBT own) m -> INV0 own st iv m ->
    harness_pres (LBT own) SP' m m' -> rw_cells usegs m' PDCTX [C8 (wz 0)] -> SP' <= usp + -80 ->
    rclient_range (LBT own) SP' (dptr own) (Z.of_nat (length (zbytes payload))) ->
    (dptr own + Z.of_nat (length (zbytes payload)) <= PDCTX \/ PDCTX + 8 <= dptr own) ->
    ps_so st' = ps_so st ->
    rw_cells usegs m' RERRNO [C4 errv'] -> mem_inv usegs m' -> stk usegs m' lo (usp + -80) -> rauxv_ok m' AB ->
    INV0 own st' iv m'.
  Proof.
    intros own st st' iv SP' m m' errv' P IV (mh & MUh & WMh & HP) DCX HS PBR PBO ESO ERR' MI' ST' AUX'.
    pose proof IV as (FR & PB & HC & SE & _ & _ & _ & _ & SO & DP0 & [AX1 AX2] & IC).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    unfold INV0, atexit_cells. unfold PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB in *. cbv iota beta in AX1. cbv iota beta in AX2. cbv iota beta.
    pose proof (magree_of_munch usegs _ _ _ MUh WMh) as AG.
    assert (OUT : forall a, ~ (PDCTX <= a < PDCTX + 8) -> (fun a0 : Z => outside [(PDCTX, PDCTX + 8)] a0) a) by (intros a Ha; cbn; lia).
    assert (HL : forall b, In b LB -> In b (LBT own)) by (intros b Hb; destruct own as [[q D]|]; [right|]; exact Hb).
    assert (HPW : rheap_pres LB (usp + -80) mh m') by (eapply rheap_pres_weaken; [exact HP| exact HS| exact HL]).
    Ltac hh HPW AG OUT C := eapply rheap_pres_rw_cells; [exact HPW| eapply rw_cells_magree; [exact AG| exact C| intros a Ha; apply OUT; cbn in Ha; lia]|
                              right; left; cbn; unfold PATEXIT, PAEF_INCB, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia].
    split. { destruct FR as [jb FR]. exists jb. eapply rheap_pres_rw_cells; [exact HPW| | left; cbn; lia].
             eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
    split. { eapply rheap_pres_bytes_at; [exact HP| | exact PBR]. eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. lia. }
    split.
    { destruct HC as (C5 & C6 & C7 & C8). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
      split; [hh HPW AG OUT C5|]. split; [hh HPW AG OUT C6|]. split; [exact DCX| hh HPW AG OUT C8]. }
    split. { eapply stderr_file0_heap_pres; [exact HPW|]. eapply (stderr_file0_agree _ _ _ AG); [| exact SE]. intros a Ha. apply OUT. unfold stderr_addr in Ha. lia. }
    split; [exists errv'; exact ERR'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AUX'|]. split.
    { rewrite ESO. eapply stdout_file_heap_pres; [exact HPW|]. eapply (stdout_file_agree _ _ _ _ AG); [| exact SO]. intros a Ha. apply OUT. unfold stdout_addr in Ha. lia. }
    split.
    { eapply pdrv_pres_trans; [exact DP0|]. eapply pdrv_pres_trans; [| eapply pdrv_pres_of_heap_sub; [exact HP| lia| exact HL]].
      eapply pdrv_pres_of_munch; [exact MUh| exact WMh| | apply (LB_below _ _ _ P)]. ivs_ok. }
    split; [split; [hh HPW AG OUT AX1| hh HPW AG OUT AX2]| hh HPW AG OUT IC].
  Qed.

  Lemma unsigned_wz_mod32 : forall r, bv_unsigned (wz r) mod 2^32 = r mod 2^32.
  Proof.
    intros r. unfold wz. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists (2^32). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma INV_incb_store : forall own st iv v m m',
    RHEAP st (LBT own) m -> INV0 own st iv m ->
    munch [(295156, 295157)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' lo (usp + -80) ->
    rw_cells usegs m' 295156 [C1 (Z_to_bv 8 v)] ->
    RHEAP st (LBT own) m' /\ INV0 own st v m'.
  Proof.
    intros own st iv v m m' P IV MU WM MI' ST' IC'.
    pose proof IV as (FR & PB & HC & SE & [errv ERR] & _ & _ & AUX & SO & DP & [AX1 AX2] & _).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN).
    unfold INV0, atexit_cells. unfold PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB, RERRNO in *. cbv iota beta in AX1. cbv iota beta in AX2. cbv iota beta.
    pose proof (magree_of_munch usegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, ~ (295156 <= a < 295157) -> (fun a0 : Z => outside [(295156, 295157)] a0) a) by (intros a Ha; cbn; lia).
    Ltac hm AG OUT C := eapply rw_cells_magree; [exact AG| exact C| intros a Ha; apply OUT; cbn in Ha; lia].
    split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P| exact MU| exact WM|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    split. { destruct FR as [jb FR]. exists jb. hm AG OUT FR. }
    split. { eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
             destruct own as [[q D]|]; cbn [dptr] in Ha, BOWN |- *; [lia| unfold PEMPTY in *; lia]. }
    split. { destruct HC as (C5 & C6 & C7 & C8). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
             split; [hm AG OUT C5|]. split; [hm AG OUT C6|]. split; [hm AG OUT C7| hm AG OUT C8]. }
    split. { eapply (stderr_file0_agree _ _ _ AG); [| exact SE]. intros a Ha. apply OUT. unfold stderr_addr in Ha. lia. }
    split. { exists errv. hm AG OUT ERR. }
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL in *. constructor; [cbn [fst snd]; lia| constructor]. }
    split. { eapply (stdout_file_agree _ _ _ _ AG); [| exact SO]. intros a Ha. apply OUT. unfold stdout_addr in Ha. lia. }
    split. { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_of_munch; [exact MU| exact WM| ivs_ok | apply (LB_below _ _ _ P)]. }
    split; [split; [hm AG OUT AX1| hm AG OUT AX2]| exact IC'].
  Qed.

  Lemma call_body : forall own k bad st ms {B} (K : Z -> @M PState B) (Q : B -> PState -> machine_state -> Prop),
    1 <= k <= 4 -> match own with None => plen = 0 | Some _ => True end -> RUNST own 0x14730 k bad st ms ->
    (forall rc' st' ms', -2^31 <= rc' < 2^31 ->
        RUNST own (if k =? 1 then 0x14768 else 0x14730) (k - 1) (if (rc' =? 0) || (rc' =? -1) then bad else 1) st' ms' ->
        implM usegs (K rc') st' Q ms') ->
    implM usegs (rc' <- Prog.fuzz_one payload ;; io_emit Prog.io rc' ;;; K rc') st Q ms.
  Proof.
    intros own k bad st ms B K Q HK OWNZ R HKONT.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3w & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV] & BAD).
    pose proof IV as (_ & _ & _ & _ & _ & MI & ST & _ & _ & _ & _ & IC).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
    unfold PAEF_INCB in IC.
    unfold wz. unfold implM. iprefix. unfold PINIT_FLAG.
    (* [comment removed for export] *)
    pose proof (munch_refl [(295156, 295157)] m) as MUs. pose proof (wmono_refl usegs m) as WMs.
    zstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (INV_incb_store own st 0 1 m mx P IV MUs WMs MI ST IC) as [P1 IV1] end.
    clear P IV MUs WMs IC.
    pose proof IV1 as (FR & PB & HC & SE & [errv ERR] & _ & _ & AUX & SO & DP & [AX1 AX2] & IC).
    (* [comment removed for export] *)
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st Q msx) end.
    eapply implM_bind.
    { (* [comment removed for export] *)
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      eapply FUZZ with (lo := lo) (AB := AB) (LB := LBT own) (D := dptr own) (payload := payload) (errv := errv) (m := mx) end;
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact P1.
      - exact PB.
      - unfold payload. apply Forall_skipn'. exact FC.
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + right; right. exists (q, D, plen). split; [left; reflexivity|]. cbn. lia.
        + right; left. unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. rewrite PLEN.
          rewrite OWNZ. lia.
      - destruct own as [[q D]|]; cbn [dptr]; [lia| reflexivity].
      - destruct own as [[q D]|]; cbn [dptr]; [lia| unfold PEMPTY; lia].
      - destruct own as [[q D]|]; cbn [dptr]; [atop_facts; lia| unfold PEMPTY; rewrite PLEN, OWNZ; lia].
      - lia.
      - destruct own as [[q D]|]; cbn [dptr] in *; [atop_facts; lia| unfold PEMPTY; rewrite PLEN, OWNZ; lia].
      - exact HC.
      - exact SE.
      - exact AUX.
      - lia.
      - exact ABB.
      - exact ST.
      - exact CEIL.
      - unfold HARNESS_STACK. lia.
      - unfold RATP, RERRNO in *. rewrite (unsigned_lit 295416) by lia. exact ERR.
      - exact MI.
      - exact FRM.
      - reflexivity.
      - clear -SP16 SPR L'. Z.div_mod_to_equations. lia.
      - reflexivity.
      - rewrite PLEN. reflexivity. }
    cbv beta. intros r st1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & errv1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & HPR & DCX1 & P2 & SOE).      (* [comment removed for export] *)
    rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
    unfold RATP in ERR1. rewrite ?(unsigned_lit 295416) in ERR1 by lia. change (295416 + -164) with RERRNO in ERR1.
    replace (ret_pc (Z_to_bv 64 0x14744)) with (Z_to_bv 64 0x14744) by (symmetry; rpc).
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (IV2 : INV0 own st1 1 mx) end.
    { eapply (INV0_after_harness own st st1 1 (usp + -80)); [exact P1| exact IV1| exact HPR| exact DCX1| lia| | | exact SOE| exact ERR1| exact MI1| exact ST1| exact AUX1].
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + right; right. exists (q, D, plen). split; [left; reflexivity|]. cbn. rewrite zbytes_length. unfold zlength in PLEN. lia.
        + right; left. unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. rewrite zbytes_length. unfold zlength in PLEN. rewrite OWNZ in PLEN. lia.
      - rewrite zbytes_length. unfold zlength in PLEN. destruct own as [[q D]|]; cbn [dptr] in *; [lia| unfold PEMPTY; rewrite OWNZ in PLEN; lia]. }
    clear HPR IV1 FR PB HC SE ERR MI ST AUX SO DP AX1 AX2 IC P1.
    pose proof IV2 as (_ & _ & _ & _ & _ & MI & ST & _ & _ & _ & _ & IC). unfold PAEF_INCB in IC.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(295156, 295157)] mx) as MUs; pose proof (wmono_refl usegs mx) as WMs end.
    zstep. lstep.
    lazymatch goal with WMs : wmono _ ?ma ?mb |- _ =>
      destruct (INV_incb_store own st1 1 0 ma mb P2 IV2 MUs WMs MI ST IC) as [P3 IV3] end.
    clear P2 IV2 MUs WMs IC.
    pose proof IV3 as (FR & PB & HC & SE & [errv' ERR] & _ & _ & AUX & SO & DP & [AX1 AX2] & IC).
    (* [comment removed for export] *)
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 Q msx) end.
    eapply implM_bind.
    { eapply implM_keeps with (f := ps_heap); [| apply s_emit_heap].
      unfold io_emit, Prog.io, io_S.
      eapply EMIT with (lo := lo) (canary := CAN) (v := r);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - intros; reflexivity.
      - intros; reflexivity.
      - exact FWXO.
      - exact SO.
      - lia.
      - apply unsigned_wz_mod32.
      - exact ST.
      - unfold EMIT_DEPTH, HARNESS_STACK in *. lia.
      - unfold GLOBALS_TOP. lia.
      - lia.
      - apply (RHEAP_ssp _ _ _ P3).
      - exact MI.
      - exact FRM1. }
    cbv beta. intros [] st2 ms2 [PO EH].
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m4 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SO2 & SSP2).
    rewrite ?(unsigned_lit (usp + -80)) in MUc by lia. rewrite ?(unsigned_lit (usp + -80)) in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x14754)) with (Z_to_bv 64 0x14754) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp + -80 <= a \/ (a < lo /\ (a < 0x10000 \/ 0x69000 <= a)) \/ (0x10000 <= a < 0x69000 /\ ~ (0x37fa8 <= a < 0x37fa8 + 232) /\ ~ (0x688d0 <= a < 0x688d0 + 1024)))
                            -> (fun a0 : Z => outside [(lo, usp + -80); (0x37fa8, 0x37fa8 + 232); (0x688d0, 0x688d0 + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    lazymatch goal with WMc : wmono _ ?ma ?mb |- _ => assert (P4 : RHEAP st2 (LBT own) mb) end.
    { eapply RHEAP_ext with (s := st1); [| | ]; cycle 1.
      - unfold ps_heap in EH. congruence.
      - unfold ps_heap in EH. congruence.
      - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P3| exact MUc| exact WMc|].
        constructor; [left; cbn [fst snd]; atop_facts; lia|].
        constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
        constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    lazymatch goal with WMc : wmono _ ?ma ?mb |- _ => assert (IV4 : INV0 own st2 0 mb) end.
    { unfold INV0, atexit_cells. unfold PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB, RERRNO in *. cbv iota beta in AX1. cbv iota beta in AX2. cbv iota beta.
      Ltac hm4 AG OUT C := eapply rw_cells_magree; [exact AG| exact C| intros a Ha; apply OUT; cbn in Ha; lia].
      split. { destruct FR as [jb FR]. exists jb. hm4 AG OUT FR. }
      split. { eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
               destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; rewrite OWNZ in PLEN; lia]. }
      split. { destruct HC as (C5 & C6 & C7 & C8). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
               split; [hm4 AG OUT C5|]. split; [hm4 AG OUT C6|]. split; [hm4 AG OUT C7| hm4 AG OUT C8]. }
      split. { eapply (stderr_file0_agree _ _ _ AG); [| exact SE]. intros a Ha. apply OUT. unfold stderr_addr in Ha. lia. }
      split. { exists errv'. hm4 AG OUT ERR. }
      split; [exact MI2|]. split; [exact ST2|].
      split. { eapply rauxv_ok_frame; [exact AUX| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *.
               constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      split; [exact SO2|].
      split. { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_of_munch; [exact MUc| exact WMc| ivs_ok | apply (LB_below _ _ _ P3)]. }
      split; [split; [hm4 AG OUT AX1| hm4 AG OUT AX2]| hm4 AG OUT IC]. }
    clear AG OUT MUc WMc FR PB HC SE ERR AUX SO DP AX1 AX2 IC P3 IV3 MI ST.
    eapply implM_evt; [| intros ms' H; exact (HKONT r _ _ RR H)].
    (* [comment removed for export] *)
    zstep. zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      apply (proj1 (rc_ok_iff r RR)) in KK.
      replace ((r =? 0) || (r =? -1)) with true by (symmetry; destruct KK as [-> | ->]; reflexivity).
      zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KN; zify_cond KN.
      + replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evt_done. unfold RUNST. do 17 eexists. exists F2, fc2. eexists.
        split; [reflexivity|]. split; [exact FRM2|]. split; [split; [exact P4| exact IV4]| exact BAD].
      + replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evt_done. unfold RUNST. do 17 eexists. exists F2, fc2. eexists.
        split; [reflexivity|]. split; [exact FRM2|]. split; [split; [exact P4| exact IV4]| exact BAD].
    - (* [comment removed for export] *)
      assert (NB : (r =? 0) || (r =? -1) = false).
      { destruct (Z.eqb_spec r 0) as [E|_]; [exfalso; pose proof (proj2 (rc_ok_iff r RR) (or_introl E)); lia|].
        destruct (Z.eqb_spec r (-1)) as [E|_]; [exfalso; pose proof (proj2 (rc_ok_iff r RR) (or_intror E)); lia|]. reflexivity. }
      rewrite NB.
      zstep. zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KN; zify_cond KN.
      + replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evt_done. unfold RUNST. do 17 eexists. exists F2, fc2. eexists.
        split; [reflexivity|]. split; [exact FRM2|]. split; [split; [exact P4| exact IV4]| right; reflexivity].
      + replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evt_done. unfold RUNST. do 17 eexists. exists F2, fc2. eexists.
        split; [reflexivity|]. split; [exact FRM2|]. split; [split; [exact P4| exact IV4]| right; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma calls_loop : forall (n : nat) own bad st ms,
    (1 <= n <= 4)%nat -> match own with None => plen = 0 | Some _ => True end ->
    RUNST own 0x14730 (Z.of_nat n) bad st ms ->
    implM usegs (run_calls Prog.fuzz_one (io_emit Prog.io) n payload bad) st (fun bad' st' ms' => RUNST own 0x14768 0 bad' st' ms') ms.
  Proof.
    induction n as [|n IH]; intros own bad st ms HN OWNZ R; [lia|].
    cbn [run_calls].
    eapply (call_body own (Z.of_nat (S n)) bad st ms (fun rc' => run_calls Prog.fuzz_one (io_emit Prog.io) n payload (if (rc' =? 0) || (rc' =? -1) then bad else 1)));
      [lia| exact OWNZ| exact R|].
    intros rc' st' ms' RR R'. destruct n as [|n'].
    - cbn [run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implM_ret. apply evt_done.
      replace (Z.of_nat 1 - 1) with 0 in R' by lia. exact R'.
    - replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
      apply (IH own _ st' ms'); [lia| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
  Qed.

  (* [comment removed for export] *)
  Lemma run_tail : forall own bad st ms,
    RUNST own 0x14768 0 bad st ms ->
    implM usegs ((match omodel own with Some q => raw_free q | None => mret tt end) ;;; mret (if bad =? 0 then 0 else 78)) st
          (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB AB lo m0) ms.
  Proof.
    intros own bad st ms R.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3w & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV] & BAD).
    pose proof IV as (FR & PB & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & [AX1 AX2] & IC).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
    unfold PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB in *. cbv iota beta in AX1. cbv iota beta in AX2.
    change (426560 + 24)%Z with 426584%Z in *. change (426560 + 288)%Z with 426848%Z in *.
    unfold wz. destruct FR as [jb FR]. unfold RERRNO in ERR.
    (* [comment removed for export] *)
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB AB lo m0) msx) end.
    eapply implM_bind with (Q1 := fun _ st' ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (errv' : word),
        ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 (oreg own)) s3w (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 0) (Z_to_bv 64 bad) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x14770) fc None m' (seg_rom usegs)
        /\ RHEAP st' LB m' /\ rw_cells usegs m' (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells usegs m' RERRNO [C4 errv'] /\ mem_inv usegs m' /\ stk usegs m' lo (usp + -80) /\ rauxv_ok m' AB
        /\ stdout_file m' (ps_so st') /\ pdrv_pres LB usp m0 m'
        /\ rw_cells usegs m' 426560 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                  C8 (Z_to_bv 64 426584); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 188568)]
        /\ rw_cells usegs m' 426848 [C8 (Z_to_bv 64 83920)] /\ rw_cells usegs m' 295156 [C1 (Z_to_bv 8 0)]).
    { destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
      - (* [comment removed for export] *)
        unfold rfree_stmt in FREE.
        eapply implM_mono.
        { eapply FREE with (lo := lo) (B := AB) (p := q) (A := D) (n := plen); try reflexivity; unfold RATP;
            rewrite ?(unsigned_lit 295416) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | left; reflexivity | exact AUX | lia | exact ST | exact CEIL | unfold RFREE_STACK; lia | exact ERR | exact MI ]. }
        cbv beta. intros [] st' ms' PO.
        destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR3 by lia.
        unfold RATP in ERR3. rewrite ?(unsigned_lit 295416) in ERR3 by lia. change (295416 + -164) with RERRNO in ERR3.
        replace (ret_pc (Z_to_bv 64 0x14770)) with (Z_to_bv 64 0x14770) by (symmetry; rpc).
        pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
        rewrite (lb_remove_head (q, D, plen) LB ND) in HPR3, HEAP3.
        Ltac hp3 HPR3 C := eapply rheap_pres_rw_cells; [exact HPR3| exact C| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia].
        do 16 eexists. exists m3, (Z_to_bv 64 (bv_unsigned errv)).
        split; [reflexivity|]. split; [exact HEAP3|].
        split; [eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia]|].
        split; [replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned); exact ERR3|].
        split; [exact MI3|]. split; [exact ST3|]. split; [exact AUX3|].
        split; [rewrite SOE3; eapply stdout_file_heap_pres; [exact HPR3| exact SO]|].
        split; [eapply pdrv_pres_trans; [exact DP|]; eapply pdrv_pres_of_heap_sub; [exact HPR3| lia| intros b Hb; exact Hb]|].
        split; [hp3 HPR3 AX1|]. split; [hp3 HPR3 AX2| hp3 HPR3 IC].
      - (* [comment removed for export] *)
        apply implM_ret. eapply evt_mono; [apply (rfree_null_spec); reflexivity|].
        cbv beta. intros ms' ->. replace (ret_pc (Z_to_bv 64 0x14770)) with (Z_to_bv 64 0x14770) by (symmetry; rpc).
        do 16 eexists. exists m, errv.
        split; [reflexivity|]. split; [exact P|]. split; [exact FR|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|].
        split; [exact SO|]. split; [exact DP|]. split; [exact AX1|]. split; [exact AX2| exact IC]. }
    cbv beta. intros [] st' ms' (x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & P' & FR' & ERR' & MI' & ST' & AUX' & SO' & DP' & AX1' & AX2' & IC').
    apply implM_ret.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    do 10 zstep. release_frame FR' ST' (bv_unsigned sp). zstep.
    assert (EV : Z.land (Z.land (Z.b2z (bad <? 1) + -1) 18446744073709551615) 78 = (if bad =? 0 then 0 else 78))
      by (destruct BAD as [-> | ->]; reflexivity).
    rewrite EV.
    apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m', errv'.
    split; [reflexivity|].
    split; [destruct BAD as [-> | ->]; cbn; lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR'|].
    split; [exact AUX'|]. split; [exact DP'|]. split; [exact P'|]. split; [exact SO'|].
    unfold atexit_cells, PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB. cbv iota beta.
    split; [split; [exact AX1'| exact AX2']| exact IC'].
  Qed.

  (* [comment removed for export] *)
  Definition PRE1 (s : PState) (m : mem) : Prop :=
    RHEAP s LB m /\ FRAME m /\ bytes_at usegs m A (zbytes content) /\ harness_cells m /\ stderr_file0 m
    /\ (exists errv : word, rw_cells usegs m RERRNO [C4 errv]) /\ mem_inv usegs m /\ stk usegs m lo (usp + -80)
    /\ rauxv_ok m AB /\ stdout_file m (ps_so s) /\ pdrv_pres LB usp m0 m
    /\ atexit_cells true m /\ rw_cells usegs m PAEF_INCB [C1 (Z_to_bv 8 0)].

  Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 x24 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 (Z_to_bv 64 PINIT_FLAG) x22 x23 x24 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation POST s := (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m0).

  (* [comment removed for export] *)
  Lemma trun_empty : forall s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x23 x24 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    plen = 0 -> frm0 fc -> PRE1 s m ->
    implM usegs (Prog.run cfg payload) s (POST s) (EST 0x14720 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 calls) x23 x24 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & FR & CT & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & ATX & IC).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    unfold Prog.run, Adapter.target_run. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implM_retb. cbv beta iota.
    unfold implM. iprefix. unfold PINIT_FLAG. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POST s) msx) end.
    eapply implM_bind.
    { eapply (calls_loop (Z.to_nat calls) None 0); [lia| exact PZ|].
      unfold RUNST. do 17 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold PEMPTY, PINIT_FLAG, wz; reflexivity|].
      split; [exact FRM|]. split; [| left; reflexivity]. split; [exact P|].
      split; [exact FR|].
      assert (PE : payload = []). { unfold payload. apply skipn_all2. unfold plen, zlength in PZ. lia. }
      split; [cbn [dptr]; rewrite PE; cbn [zbytes map]; apply bytes_at_nil; unfold PEMPTY; lia|].
      split; [exact HC|]. split; [exact SE|]. split; [exists errv; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|]. split; [exact SO|].
      split; [exact DP|]. split; [exact ATX| exact IC]. }
    cbv beta. intros bad st' ms' R. apply (run_tail None bad st' ms' R).
  Qed.

  (* [comment removed for export] *)
  Lemma pdrv_pres_of_newblock : forall st q D n m m',
    RHEAP st ((q, D, n) :: LB) m -> munch [(D, D + n)] m m' -> wmono usegs m m' -> pdrv_pres LB usp m m'.
  Proof.
    intros st q D n m m' P MU WM a Ha Hc Hx.
    destruct (magree_of_munch usegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
    cbn. split; [| exact I].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (q, D, n) P ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L', B4. atop_facts.
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (q, D, n) b P ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
    cbn [blk_id blk_addr blk_size fst snd] in DJ.
    assert (NE : q <> blk_id b).
    { cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E. apply in_map. exact Hb. }
    specialize (DJ NE). destruct b as [[bi ba] bs]. cbn [blk_addr blk_size blk_id fst snd] in DJ, Hr. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_copy : forall s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x23 x24 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    plen <> 0 -> frm0 fc -> PRE1 s m ->
    implM usegs (Prog.run cfg payload) s (POST s) (EST 0x146d4 x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 calls) x23 x24 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & FR & CT & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & [AX1 AX2] & IC).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts s None m P) as (BA1 & BA2 & BA3 & _). atop_facts.
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    unfold zlength in LC, L6.
    unfold PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB in *. cbv iota beta in AX1. cbv iota beta in AX2.
    change (426560 + 24)%Z with 426584%Z in *. change (426560 + 288)%Z with 426848%Z in *.
    unfold Prog.run, Adapter.target_run. rewrite !PLEN.
    replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implM_bind_assoc.
    destruct FR as [jb FR]. unfold RERRNO in ERR.
    (* [comment removed for export] *)
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POST s) msx) end.
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := lo) (B := AB); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 295416) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
        first [ exact P | exact AUX | lia | exact ST | exact CEIL | unfold RMALLOC_STACK; lia | exact ERR | exact MI ]. }
    cbv beta. intros r s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit 295416) in ERR1 by lia. rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
    change (295416 + -164) with 295252 in ERR1.
    replace (ret_pc (Z_to_bv 64 0x146dc)) with (Z_to_bv 64 0x146dc) by (symmetry; rpc).
    assert (FR1 : rw_cells usegs m1 (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    assert (CT1 : bytes_at usegs m1 A (zbytes content)).
    { eapply rheap_pres_bytes_at; [exact HPR| exact CT|]. right; right. exists (p, A, cap). split; [exact INLB|]. cbn. rewrite zbytes_length. lia. }
    Ltac hp1 HPR C := eapply rheap_pres_rw_cells; [exact HPR| exact C| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia].
    assert (AX11 : rw_cells usegs m1 426560 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C4 (Z_to_bv 64 1); C4 z64; C8 (Z_to_bv 64 426584); C8 z64; C8 (Z_to_bv 64 188568)]) by (hp1 HPR AX1).
    assert (AX21 : rw_cells usegs m1 426848 [C8 (Z_to_bv 64 83920)]) by (hp1 HPR AX2).
    assert (IC1 : rw_cells usegs m1 295156 [C1 (Z_to_bv 8 0)]) by (hp1 HPR IC).
    destruct r as [nb|].
    2:{ (* [comment removed for export] *)
        destruct RR as [-> HEAP1].
        apply implM_retb. cbv beta iota. apply implM_ret.
        zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity].
        zstep. zstep. do 10 zstep. release_frame FR1 ST1 (bv_unsigned sp). zstep.
        apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m1, errv1.
        split; [reflexivity|]. split; [lia|]. split; [exact MI1|]. split; [exact FRM|]. split; [exact ST1|].
        split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR1|].
        split; [exact AUX1|].
        split; [eapply pdrv_pres_trans; [exact DP| eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros b Hb; exact Hb]]|].
        split; [exact HEAP1|]. split; [rewrite SOE; eapply stdout_file_heap_pres; [exact HPR| exact SO]|].
        unfold atexit_cells, PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB. cbv iota beta. split; [split; [exact AX11| exact AX21]| exact IC1]. }
    (* [comment removed for export] *)
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & _).
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). atop_facts.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + plen <= A \/ A + cap <= A').
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', plen) (p, A, cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E.
      apply (in_map blk_id) in INLB. exact INLB. }
    (* [comment removed for export] *)
    assert (PB : bytes_at usegs m1 PAY (zbytes payload)).
    { rewrite <- (firstn_skipn (Z.to_nat (6 + L)) (zbytes content)) in CT1. apply bytes_at_app in CT1. destruct CT1 as [_ X].
      rewrite length_firstn, zbytes_length in X. unfold payload, zbytes. rewrite <- skipn_map. unfold zbytes in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content))) with PAY in X by (rewrite EPAY; lia). exact X. }
    apply implM_retb. cbv beta iota.
    unfold implM. iprefix.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply memcpy_callv with (src := zbytes payload) (junk := junk');
        [exact PB| rewrite zbytes_length; lia| exact NBLK| unfold plen, zlength in *; lia| lia| unfold plen, zlength in *; lia| lia| exact MI1]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB2 & _).
    transport_after_call usegs m1 m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x146f0)) with (Z_to_bv 64 0x146f0) by (symmetry; rpc).
    assert (P2 : RHEAP s1' ((nb, A', plen) :: LB) m2).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP1| exact MUc| exact WMc|].
      constructor; [| constructor]. right; right. exists (nb, A', plen). split; [left; reflexivity|]. cbn. lia. }
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (a < A' \/ A' + plen <= a) -> (fun a0 : Z => outside [(A', A' + plen)] a0) a) by (intros a Ha; cbn; lia).
    Ltac hq HPR AG OUT C := eapply rw_cells_magree; [exact AG| eapply rheap_pres_rw_cells; [exact HPR| exact C| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia]| intros a Ha; apply OUT; cbn in Ha; lia].
    Ltac hq2 AG OUT C := eapply rw_cells_magree; [exact AG| exact C| intros a Ha; apply OUT; cbn in Ha; lia].
    assert (IV2 : INV0 (Some (nb, A')) s1' 0 m2).
    { unfold INV0, atexit_cells, PATEXIT, PATEXIT_CALL, PAEF_GUARD, PAEF_INCB. cbv iota beta.
      split; [exists jb; exact FR1|].
      split; [cbn [dptr]; apply (rw_cells_bytes_at usegs) in NB2; cbn [cells_bytes cbytes app] in NB2; rewrite app_nil_r in NB2; exact NB2|].
      split. { destruct HC as (C5 & C6 & C7 & C8). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
               split; [hq HPR AG OUT C5|]. split; [hq HPR AG OUT C6|]. split; [hq HPR AG OUT C7| hq HPR AG OUT C8]. }
      split. { eapply (stderr_file0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia|]. eapply stderr_file0_heap_pres; [exact HPR| exact SE]. }
      split; [exists errv1; exact ERR1|]. split; [exact MI2|]. split; [exact ST1|].
      split. { eapply rauxv_ok_frame; [exact AUX1| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
      split. { rewrite SOE. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia|]. eapply stdout_file_heap_pres; [exact HPR| exact SO]. }
      split. { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_trans; [eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros b Hb; exact Hb]|].
               eapply pdrv_pres_of_newblock; [exact HEAP1| exact MUc| exact WMc]. }
      split; [split; [exact AX11| exact AX21]| exact IC1]. }
    clear AG OUT MUc WMc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1' (POST s1') msx) end || idtac.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1' (POST s) msx) end || idtac.
    eapply implM_bind.
    { eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0); [lia| exact I|].
      unfold RUNST. do 17 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold PINIT_FLAG, wz; reflexivity|].
      split; [exact FRM|]. split; [split; [exact P2| exact IV2]| left; reflexivity]. }
    cbv beta. intros bad st' ms'' R. apply (run_tail (Some (nb, A')) bad st' ms'' R).
  Qed.

  (* [comment removed for export] *)
  Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (errv : word),
    RHEAP s LB m0 -> bytes_at usegs m0 A (zbytes content) -> trun_cells0 m0 -> stderr_file0 m0 -> rauxv_ok m0 AB ->
    stk usegs m0 lo usp -> rw_cells usegs m0 RERRNO [C4 errv] -> mem_inv usegs m0 -> frm0 fc ->
    stdout_file m0 (ps_so s) ->
    tp = tpv -> a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 PAY -> a3 = Z_to_bv 64 plen ->
    implM usegs (Prog.run cfg payload) s (POST s)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PTARGET_RUN) fc None m0 (seg_rom usegs)).
  Proof.
    intros until errv. intros P0 CT TR0 SE0 AUX0 ST0 ERR0 MI0 FRM SO0 -> -> -> -> ->.
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts s None m0 P0) as (BA1 & BA2 & BA3 & _). atop_facts.
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    unfold zlength in LC, L6. unfold RERRNO in ERR0.
    unfold implM. eapply impl_evt; [| intros ms' H; exact H].
    eapply trun_init; [exact ST0| exact MI0| exact TR0| exact P0|].
    intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 FR ST1 HC1 MU WM MI1 ATX1 IC1.
    unfold PINIT_FLAG in MU.
    pose proof (magree_of_munch usegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, ((a < lo /\ (a < 0x10000 \/ 0x69000 <= a)) \/ (0x10000 <= a < 0x69000 /\ ~ (0x480f0 <= a < 0x480f0 + 1) /\ ~ (0x68240 <= a < 0x68268) /\ ~ (0x68360 <= a < 0x68368)))
                            -> (fun a0 : Z => outside [(usp - 128, usp); (0x480f0, 0x480f0 + 1); (0x68240, 0x68268); (0x68360, 0x68368)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (CT1 : bytes_at usegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. lia. }
    assert (ERR1 : rw_cells usegs m1 RERRNO [C4 errv]).
    { eapply rw_cells_magree; [exact AG| exact ERR0|]. intros a Ha. apply OUT. right. unfold RERRNO in *. cbn in Ha. lia. }
    assert (SE1 : stderr_file0 m1) by (eapply (stderr_file0_agree _ _ _ AG); [| exact SE0]; intros a Ha; apply OUT; right; unfold stderr_addr in Ha; lia).
    assert (SO1 : stdout_file m1 (ps_so s)) by (eapply (stdout_file_agree _ _ _ _ AG); [| exact SO0]; intros a Ha; apply OUT; right; unfold stdout_addr in Ha; lia).
    assert (AUX1 : rauxv_ok m1 AB).
    { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|]. unfold RAUXV_CELL, RLIBC in *.
      constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (P1 : RHEAP s LB m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MU| exact WM|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (DP1 : pdrv_pres LB usp m0 m1).
    { eapply pdrv_pres_of_munch; [exact MU| exact WM| ivs_ok | apply (LB_below s None m0 P0)]. }
    assert (PRE : PRE1 s m1).
    { split; [exact P1|]. split; [exact FR|]. split; [exact CT1|]. split; [exact HC1|]. split; [exact SE1|]. split; [exists errv; exact ERR1|].
      split; [exact MI1|]. split; [exact ST1|]. split; [exact AUX1|]. split; [exact SO1|]. split; [exact DP1|]. split; [exact ATX1| exact IC1]. }
    clear AG OUT MU WM CT ERR0 SE0 SO0 AUX0 P0 ST0 MI0 TR0.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      zstep. zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        apply evt_done. rewrite <- EC.
        eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evt_done. rewrite <- EC.
        eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
    - (* [comment removed for export] *)
      destruct (nth_error content 2) as [c2|] eqn:EC2; [| exfalso; apply nth_error_None in EC2; lia].
      pose proof (proj1 (Forall_forall _ _) FC c2 (nth_error_In _ _ EC2)) as C2R. cbn beta in C2R.
      pose proof (u8ro_read usegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1 ltac:(unfold zbytes; rewrite nth_error_map, EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD.
      zstep. zstep.
      assert (EC : calls = Z.land c2 3 + 1).
      { unfold calls, cfg. replace (0 <? L) with true by (symmetry; apply Z.ltb_lt; lia). unfold znth.
        destruct (Z.ltb_spec 2 0); [lia|]. change (Z.to_nat 2) with 2%nat. rewrite (nth_error_nth _ _ _ EC2). lia. }
      replace (bv_unsigned (Z_to_bv 8 c2)) with c2
        by (rewrite Z_to_bv_unsigned; unfold bv_wrap; symmetry; apply Z.mod_small; unfold bv_modulus; cbn; lia).
      replace (Z.land c2 3 + 1) with calls by lia.
      zstep. if_cases KP; zify_cond KP.
      + apply evt_done. eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evt_done. eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
  Qed.
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ptarget_run_proof :
  rmalloc_stmt -> rfree_stmt -> fuzz_one_stmt -> emit_printf_stmt ps_so set_so_ps -> fwritex_stdout_stmt ->
  ptarget_run_stmt.
Proof.
  intros MALLOC FREE FUZZ EMIT FWXO.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A cap L content AB lo errv.
  intros P0 INLB CT FC LC CAP L0 L6 TR0 SE0 AUX0 SPAB ABB ST0 CEIL LO ERR0 MI0 FRM SO0 -> SP16 -> -> -> ->.
  eapply (trun_main MALLOC FREE FUZZ EMIT FWXO ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LB p A cap L content AB lo
            INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO);
    [exact P0| exact CT| exact TR0| exact SE0| exact AUX0| exact ST0| | exact MI0| exact FRM| exact SO0| reflexivity| reflexivity| reflexivity| unfold PAY; reflexivity| unfold plen; reflexivity].
  unfold RATP, RERRNO, wz in ERR0 |- *. rewrite (unsigned_lit 295416) in ERR0 by lia. exact ERR0.
Qed.

End CANSEC1.
