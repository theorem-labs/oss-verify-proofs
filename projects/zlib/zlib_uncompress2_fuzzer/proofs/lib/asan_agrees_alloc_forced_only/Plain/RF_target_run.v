(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree Startup_kit STRW_tac Amo_tac Keeps F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg F_syscalls F_memcpy StdioFiles Exit F_printf_iface Stdio_iface Stdio_kit F_atexit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio Driver Adapter Harness Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import CMonad CMonadX ProgC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require AdapterC DriverC HarnessC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac clia := atop_facts; lia.


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

Lemma bad_test : forall r, -2^31 <= r < 2^31 ->
  negb (bv_ltu (Z_to_bv 64 (bv_swrap 32 (Z.land r 18446744073709551615 + -1))) (Z_to_bv 64 (-2))) = ((r =? 0) || (r =? -1))%bool.
Proof.
  intros r Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (4294967296 / 2)%Z with 2147483648%Z. change (2^64) with 18446744073709551616.
  destruct (Z.eqb_spec r 0) as [->|N0]; [vm_compute; reflexivity|].
  destruct (Z.eqb_spec r (-1)) as [->|N1]; [vm_compute; reflexivity|].
  cbn [orb]. apply Bool.negb_false_iff. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; cbn; [constructor|].
  inversion H; subst. apply IH. assumption.
Qed.

Section RUN.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FUZZ : fuzz_one_stmt.
  Hypothesis EMIT : emit_printf_stmt ps_so set_so_ps.
  Hypothesis FWXO : fwritex_stdout_stmt.

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
  Notation M2 := (Z_to_bv 64 (-2)).
  Notation RATP_LIT := 470912.
  Notation RERRNO_LIT := 470748.
  Lemma ratp_lit_ok : RATP = RATP_LIT /\ RERRNO = RERRNO_LIT. Proof. split; reflexivity. Qed.

  Definition plen : Z := zlength content - 6 - L.
  Definition PAY : Z := A + 6 + L.
  Definition payload : list Z := skipn (Z.to_nat (6 + L)) content.
  Definition cfg : Z := if 0 <? L then znth content 2 else 0.
  Definition calls : Z := 1 + Z.land cfg 3.

  Definition LBT (own : option (bptr * Z)) : list block :=
    match own with None => LB | Some (q, D) => (q, D, plen) :: LB end.
  Definition dptr (own : option (bptr * Z)) : Z := match own with None => PEMPTY | Some (_, D) => D end.
  Definition oreg (own : option (bptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.
  Definition omodel (own : option (bptr * Z)) : option bptr := match own with None => None | Some (q, _) => Some q end.

  Definition FRAME (m : mem) : Prop :=
    exists jb : list byte, rw_cells psegs m (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition PIN (i c : Z) (m : mem) : Prop :=
    rw_cells psegs m PINIT_FLAG [C1 (Z_to_bv 8 i); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 c)].
  Definition PINB (m : mem) : Prop := PIN 1 0 m.

  Definition INV0 (own : option (bptr * Z)) (st : PState) (m : mem) : Prop :=
    FRAME m /\ bytes_at psegs m (dptr own) (zbytes payload) /\ harness_cells m /\ stderr_file0 m
    /\ (exists errv : word, rw_cells psegs m RERRNO [C4 errv])
    /\ mem_inv psegs m /\ stk psegs m lo (usp + -80) /\ rauxv_ok m AB
    /\ stdout_file m (ps_so st) /\ pdrv_pres LB usp m0 m
    /\ PINB m /\ atx_cellsA m.
  Definition INV (own : option (bptr * Z)) (st : PState) (m : mem) : Prop := RHEAP st (LBT own) m /\ INV0 own st m.

  Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (oreg own)) rcw (wz PINIT_FLAG) (wz k) (wz b) M2 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Definition RUNST0 (own : option (bptr * Z)) (pc : Z) (k : Z) (rcw : word) (b : Z) (st : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ INV own st m.
  Definition RUNST (own : option (bptr * Z)) (pc : Z) (k : Z) (b : Z) (st : PState) (ms : machine_state) : Prop :=
    (exists rcw, RUNST0 own pc k rcw b st ms) /\ 0 <= b <= 1.

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


  Lemma trun_init : forall (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo usp -> mem_inv psegs m -> trun_cells0 m ->
    rw_cells psegs m RLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    (forall (m' : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FRAME m' -> stk psegs m' lo (usp + -80) -> harness_cells m' -> PINB m' -> atx_cellsA m' ->
        munch [(usp - 128, usp); (PINIT_FLAG, PINIT_FLAG + 5); (PATX, PATX + PATX_N)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
        evt psegs Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 (wz 0) x11 x12 x13 x14 x15 x16 x17
                              a1 a0 (wz PINIT_FLAG) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x14be4) fc None m' (seg_rom psegs))) ->
    evt psegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 PTARGET_RUN) fc None m (seg_rom psegs)).
  Proof.
    intros until tm1. intros ST MI TR LCH K. pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    destruct TR as (PI & GFI & GZA & [AX0a AX0b]). unfold RLIBC in LCH.
    unfold PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_ZALLOC, PZCALLOC, PZCFREE, PATX, PATX_N, wz in *. change (0x92fc0 + 288) with 0x930e0 in AX0b.
    pose proof (munch_refl [(usp - 128, usp); (0x32e80, 0x32e80 + 5); (0x92fc0, 0x92fc0 + 544)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (EPATX : PATX = 0x92fc0) by reflexivity. assert (EPATXN : PATX_N = 544) by reflexivity.
    unfold PTARGET_RUN.
    zstep. carve_frame 80%nat ST.
    do 9 zstep.
    do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    do 5 zstep.
    call_sp atexit_guard_spec; [ exact ST | split; [exact AX0a | exact AX0b] | unfold PLIBC; exact LCH | assumption | unfold PAEF_GUARD; reflexivity | lia | lia | ].
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear; intros K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    do 3 zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; clear; intros K2; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
    - lazymatch goal with H : rw_cells psegs _ (usp + -80) _ |- _ => eexists; exact H end.
    - assumption.
    - unfold harness_cells, PGOT_ZALLOC, PZCALLOC, PZCFREE, wz. assumption.
    - unfold PINB, PIN. assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  Lemma block_facts : forall st own m, RHEAP st (LBT own) m ->
    0 < A /\ A + cap <= ATOP /\ (A + cap <= 0x10000 \/ 0x94000 <= A)
    /\ match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + plen <= ATOP /\ (D + plen <= 0x10000 \/ 0x94000 <= D) end.
  Proof.
    intros st own m P.
    assert (HB : In (p, A, cap) (LBT own)) by (destruct own as [[q D]|]; [right|]; exact INLB).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
    split; [lia|]. split; [lia|]. split; [lia|].
    destruct own as [[q D]|]; [| exact I].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P ltac:(left; reflexivity)) as (C1 & C2 & C3 & C4 & C5). cbn in C1, C2, C3, C4, C5.
    pose proof facts. lia.
  Qed.

  Lemma pdrv_pres_of_heap_sub : forall LB' SP' m m',
    rheap_pres LB' SP' m m' -> SP' <= usp -> (forall b, In b LB -> In b LB') -> pdrv_pres LB usp m m'.
  Proof.
    intros LB' SP' m m' HP HS HL. apply pdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HP| exact HS| exact HL].
  Qed.
  Lemma pdrv_pres_of_harness_sub : forall LB' SP' m m',
    harness_pres LB' SP' m m' -> SP' <= usp -> (forall b, In b LB -> In b LB') -> pdrv_pres LB usp m m'.
  Proof.
    intros LB' SP' m m' HP HS HL a Ha Hc Hx. apply (harness_pres_weaken _ _ _ _ _ _ HP HS HL a Ha Hc).
    intros HB. apply Hx. unfold pstdout_ivs. cbn. do 4 right; left. exact HB.
  Qed.
  Lemma pdrv_pres_of_munch : forall m m' W,
    munch W m m' -> wmono psegs m m' ->
    Forall (fun iv => (snd iv <= usp /\ ATOP <= fst iv) \/ In iv pstdout_ivs) W ->
    (forall b, In b LB -> blk_addr b + blk_size b <= ATOP) ->
    pdrv_pres LB usp m m'.
  Proof.
    intros m m' W MU WM HW HLB a Ha Hc Hx.
    destruct (magree_of_munch psegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
    clear MU WM. induction W as [|iv W IH]; cbn; [exact I|].
    inversion HW as [|iv' W' Hiv HW']; subst. destruct iv as [lo' hi']. cbn [fst snd] in Hiv. split; [| apply IH; exact HW'].
    destruct Hiv as [[H1 H2]|Hin].
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
      + lia.
      + atop_facts. lia.
      + pose proof (HLB b Hb). lia.
    - intros Hr. apply Hx. unfold pstdout_ivs, PINIT_FLAG, HBUF, HBUF_N, PATX in Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E; intros <- <-; cbn; unfold PINIT_FLAG, HBUF, HBUF_N, PATX; lia.
  Qed.

  Lemma LB_below : forall st own m, RHEAP st (LBT own) m -> forall b, In b LB -> blk_addr b + blk_size b <= ATOP.
  Proof.
    intros st own m P b Hb.
    assert (HB : In b (LBT own)) by (destruct own as [[q D]|]; [right|]; exact Hb).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (_ & _ & _ & B4 & _). exact B4.
  Qed.

  Lemma PINB_client : forall LX SP', rclient_range LX SP' PINIT_FLAG 5.
  Proof. intros. right; left. unfold PINIT_FLAG, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. Qed.
  Lemma ATXA_client1 : forall LX SP', rclient_range LX SP' PATX 40.
  Proof. intros. right; left. unfold PATX, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. Qed.
  Lemma ATXA_client2 : forall LX SP', rclient_range LX SP' (PATX + 288) 8.
  Proof. intros. right; left. unfold PATX, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. Qed.
  Lemma PIN_heap_pres : forall i c LX SP' m m', rheap_pres LX SP' m m' -> PIN i c m -> PIN i c m'.
  Proof. intros i c LX SP' m m' HP H. eapply rheap_pres_rw_cells; [exact HP| exact H| apply PINB_client]. Qed.
  Lemma atx_cellsA_heap_pres : forall LX SP' m m', rheap_pres LX SP' m m' -> atx_cellsA m -> atx_cellsA m'.
  Proof.
    intros LX SP' m m' HP [H1 H2]. split.
    - eapply rheap_pres_rw_cells; [exact HP| exact H1| apply ATXA_client1].
    - eapply rheap_pres_rw_cells; [exact HP| exact H2| apply ATXA_client2].
  Qed.
  Lemma PIN_harness_pres : forall i c LX SP' m m', harness_pres LX SP' m m' -> PIN i c m -> PIN i c m'.
  Proof.
    intros i c LX SP' m m' HP H. eapply harness_pres_rw_cells; [exact HP| exact H| apply PINB_client| left; cbn; unfold PINIT_FLAG, HBUF, HBUF_N; lia].
  Qed.
  Lemma atx_cellsA_harness_pres : forall LX SP' m m', harness_pres LX SP' m m' -> atx_cellsA m -> atx_cellsA m'.
  Proof.
    intros LX SP' m m' HP [H1 H2]. split.
    - eapply harness_pres_rw_cells; [exact HP| exact H1| apply ATXA_client1| right; cbn; unfold PATX, HBUF, HBUF_N; lia].
    - eapply harness_pres_rw_cells; [exact HP| exact H2| apply ATXA_client2| right; cbn; unfold PATX, HBUF, HBUF_N; lia].
  Qed.

  Lemma unsigned_wz_mod32 : forall r, bv_unsigned (wz r) mod 2^32 = r mod 2^32.
  Proof.
    intros r. unfold wz. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists (2^32). reflexivity.
  Qed.

  Lemma call_body : forall own k (rcw : word) b st ms {B} (K : Z -> MC PState B) (Q : B -> PState -> machine_state -> Prop),
    1 <= k <= 4 -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => True end -> RUNST0 own 0x14c54 k rcw b st ms ->
    (forall rc' st' ms', RUNST own (if k =? 1 then 0x14c8c else 0x14c54) (k - 1) (AdapterC.bad_upd b rc') st' ms' -> implMC psegs (K rc') st' Q ms') ->
    implMC psegs (cmbind (ProgC.fuzz_oneC payload) (fun rc' => cmbind (clift (io_emit Prog.io rc')) (fun _ => K rc'))) st Q ms.
  Proof.
    intros own k rcw b st ms B K Q HK HB OWNZ R HKONT.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV]).
    pose proof IV as (FR & PB & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & PN & AXA).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
    unfold PINB, PIN in PN. unfold PINIT_FLAG in *.
    pose proof (munch_refl [(PINIT_FLAG, PINIT_FLAG + 5)] m) as MU0. pose proof (wmono_refl psegs m) as WM0. unfold PINIT_FLAG in MU0.
    pose proof (conj PB ERR) as KEEP. clear PB ERR.
    unfold wz. apply implMC_from_evt. zstep. lstep. zstep. zstep. zstep. apply evt_done. destruct KEEP as [PB ERR].
    lazymatch goal with |- implMC _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    pose proof (magree_of_munch psegs _ _ _ MU0 WM0) as AG0.
    assert (OUT0 : forall a, ~ (0x32e80 <= a < 0x32e80 + 5) -> (fun a0 : Z => outside [(0x32e80, 0x32e80 + 5)] a0) a) by (intros a Ha; cbn; lia).
    assert (P' : RHEAP st (LBT own) mA).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P| exact MU0| exact WM0|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (FR' : FRAME mA). { destruct FR as [jb FR]. exists jb. eapply rw_cells_magree; [exact AG0| exact FR| intros a Ha; apply OUT0; cbn in Ha; lia]. }
    assert (PB' : bytes_at psegs mA (dptr own) (zbytes payload)).
    { eapply bytes_at_magree; [exact AG0| exact PB|]. intros a Ha. apply OUT0. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; lia]. }
    assert (HC' : harness_cells mA). { unfold harness_cells, PGOT_ZALLOC in *. eapply rw_cells_magree; [exact AG0| exact HC| intros a Ha; apply OUT0; cbn in Ha; lia]. }
    assert (SE' : stderr_file0 mA). { eapply (stderr_file0_agree _ _ _ AG0); [| exact SE]. intros a Ha. apply OUT0. unfold stderr_addr in Ha. lia. }
    assert (ERR' : rw_cells psegs mA RERRNO [C4 errv]). { eapply rw_cells_magree; [exact AG0| exact ERR| intros a Ha; apply OUT0; unfold RERRNO in Ha; cbn in Ha; lia]. }
    assert (AUX' : rauxv_ok mA AB). { eapply rauxv_ok_frame; [exact AUX| exact MU0| exact WM0|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (SO' : stdout_file mA (ps_so st)). { eapply (stdout_file_agree _ _ _ _ AG0); [| exact SO]. intros a Ha. apply OUT0. unfold stdout_addr in Ha. lia. }
    assert (DP' : pdrv_pres LB usp m0 mA).
    { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_of_munch; [exact MU0| exact WM0| | apply (LB_below st own m P)].
      constructor; [right; unfold pstdout_ivs, PINIT_FLAG; cbn; do 2 right; left; reflexivity| constructor]. }
    assert (AXA' : atx_cellsA mA). { eapply (atx_cellsA_agree _ _ _ AG0); [| exact AXA]. intros a Ha. apply OUT0. unfold atx_addrA, PATX, PATX_N in Ha. lia. }
    lazymatch goal with H : mem_inv psegs mA |- _ => rename H into MI' end.
    lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into ST' end.
    clear AG0 OUT0 MU0 WM0 P FR PB HC SE ERR AUX SO DP AXA IV.
    eapply implMC_bind.
    {
      eapply FUZZ with (lo := lo) (AB := AB) (LB := LBT own) (D := dptr own) (payload := payload) (errv := errv);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact P'.
      - exact PB'.
      - unfold payload. apply Forall_skipn'. exact FC.
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + right; right. exists (q, D, plen). split; [left; reflexivity|]. cbn. lia.
        + right; left. unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. rewrite PLEN.
          rewrite OWNZ. lia.
      - destruct own as [[q D]|]; cbn [dptr]; [lia| reflexivity].
      - destruct own as [[q D]|]; cbn [dptr]; [lia| unfold PEMPTY; lia].
      - destruct own as [[q D]|]; cbn [dptr]; [atop_facts; lia| unfold PEMPTY; rewrite PLEN, OWNZ; lia].
      - lia.
      - exact HC'.
      - exact SE'.
      - exact AUX'.
      - lia.
      - exact ST'.
      - exact CEIL.
      - unfold HARNESS_STACK. lia.
      - unfold RATP, RERRNO in *. rewrite (unsigned_lit RATP_LIT) by lia. exact ERR'.
      - exact MI'.
      - exact FRM.
      - reflexivity.
      - clear -SP16 SPR L'. Z.div_mod_to_equations. lia.
      - reflexivity.
      - rewrite PLEN. reflexivity.
      - rewrite ?unsigned_lit by lia; reflexivity.
      - lia.
      - destruct own as [[q D]|]; cbn [dptr LBT]; [right; exists (q, D, plen); split; [left; reflexivity| cbn; lia]| left; split; [rewrite PLEN; exact OWNZ| reflexivity]]. }
    cbv beta. intros r st1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & HPR & P1 & SOE).
    rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
    unfold RATP in ERR1. rewrite ?(unsigned_lit RATP_LIT) in ERR1 by lia. change (RATP_LIT + -164) with RERRNO in ERR1.
    replace (ret_pc (Z_to_bv 64 0x14c68)) with (Z_to_bv 64 0x14c68) by (symmetry; rpc).
    assert (HPW : harness_pres LB (usp + -80) mA m1) by (eapply harness_pres_weaken; [exact HPR| lia| intros bb Hb; destruct own as [[q D]|]; [right|]; exact Hb]).
    assert (FR1 : FRAME m1).
    { destruct FR' as [jb FR']. exists jb. eapply harness_pres_rw_cells; [exact HPW| exact FR'| left; cbn; lia| right; unfold HBUF, HBUF_N; cbn; lia]. }
    assert (PB1 : bytes_at psegs m1 (dptr own) (zbytes payload)).
    { eapply harness_pres_bytes_at; [exact HPR| exact PB'| |].
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + right; right. exists (q, D, plen). split; [left; reflexivity|]. cbn. rewrite zbytes_length. unfold zlength in PLEN. lia.
        + right; left. unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. rewrite zbytes_length. unfold zlength in PLEN. rewrite OWNZ in PLEN. lia.
      -
        rewrite zbytes_length. unfold zlength in PLEN. unfold HBUF, HBUF_N.
        destruct own as [[q D]|]; cbn [dptr LBT] in *; [lia| unfold PEMPTY; rewrite OWNZ in PLEN; lia]. }
    assert (SO1 : stdout_file m1 (ps_so st1)) by (rewrite SOE; eapply stdout_file_harness_pres; [exact HPW| exact SO']).
    assert (DP1 : pdrv_pres LB usp m0 m1).
    { eapply pdrv_pres_trans; [exact DP'|]. eapply pdrv_pres_of_harness_sub; [exact HPR| lia| intros bb Hb; destruct own as [[q D]|]; [right|]; exact Hb]. }
    assert (PN1 : PIN 1 1 m1) by (eapply PIN_harness_pres; [exact HPW| exact PN]).
    assert (AXA1 : atx_cellsA m1) by (eapply atx_cellsA_harness_pres; [exact HPW| exact AXA']).
    assert (HC1 : harness_cells m1).
    { unfold harness_cells, PGOT_ZALLOC in *. eapply harness_pres_rw_cells; [exact HPW| exact HC'| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia| left; cbn; unfold HBUF; lia]. }
    assert (SE1 : stderr_file0 m1) by (eapply stderr_file0_harness_pres; [exact HPW| exact SE']).
    clear HPR HPW FR' PB' HC' SE' ERR' MI' ST' AUX' SO' DP' PN AXA'.
    unfold PIN, PINIT_FLAG in PN1.
    pose proof (munch_refl [(PINIT_FLAG, PINIT_FLAG + 5)] m1) as MU1. pose proof (wmono_refl psegs m1) as WM1. unfold PINIT_FLAG in MU1.
    pose proof (conj PB1 ERR1) as KEEP. clear PB1 ERR1.
    apply implMC_from_evt. zstep. lstep. zstep. zstep. apply evt_done. destruct KEEP as [PB1 ERR1].
    lazymatch goal with |- implMC _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    pose proof (magree_of_munch psegs _ _ _ MU1 WM1) as AG1.
    assert (OUT1 : forall a, ~ (0x32e80 <= a < 0x32e80 + 5) -> (fun a0 : Z => outside [(0x32e80, 0x32e80 + 5)] a0) a) by (intros a Ha; cbn; lia).
    assert (P1' : RHEAP st1 (LBT own) mB).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P1| exact MU1| exact WM1|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (FR1' : FRAME mB). { destruct FR1 as [jb FR1]. exists jb. eapply rw_cells_magree; [exact AG1| exact FR1| intros a Ha; apply OUT1; cbn in Ha; lia]. }
    assert (PB1' : bytes_at psegs mB (dptr own) (zbytes payload)).
    { eapply bytes_at_magree; [exact AG1| exact PB1|]. intros a Ha. apply OUT1. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; lia]. }
    assert (HC1' : harness_cells mB). { unfold harness_cells, PGOT_ZALLOC in *. eapply rw_cells_magree; [exact AG1| exact HC1| intros a Ha; apply OUT1; cbn in Ha; lia]. }
    assert (SE1' : stderr_file0 mB). { eapply (stderr_file0_agree _ _ _ AG1); [| exact SE1]. intros a Ha. apply OUT1. unfold stderr_addr in Ha. lia. }
    assert (ERR1' : rw_cells psegs mB RERRNO [C4 errv1]). { eapply rw_cells_magree; [exact AG1| exact ERR1| intros a Ha; apply OUT1; unfold RERRNO in Ha; cbn in Ha; lia]. }
    assert (AUX1' : rauxv_ok mB AB). { eapply rauxv_ok_frame; [exact AUX1| exact MU1| exact WM1|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (SO1' : stdout_file mB (ps_so st1)). { eapply (stdout_file_agree _ _ _ _ AG1); [| exact SO1]. intros a Ha. apply OUT1. unfold stdout_addr in Ha. lia. }
    assert (DP1' : pdrv_pres LB usp m0 mB).
    { eapply pdrv_pres_trans; [exact DP1|]. eapply pdrv_pres_of_munch; [exact MU1| exact WM1| | apply (LB_below _ _ _ P1)].
      constructor; [right; unfold pstdout_ivs, PINIT_FLAG; cbn; do 2 right; left; reflexivity| constructor]. }
    assert (AXA1' : atx_cellsA mB). { eapply (atx_cellsA_agree _ _ _ AG1); [| exact AXA1]. intros a Ha. apply OUT1. unfold atx_addrA, PATX, PATX_N in Ha. lia. }
    lazymatch goal with H : mem_inv psegs mB |- _ => rename H into MI1' end.
    lazymatch goal with H : stk psegs mB _ _ |- _ => rename H into ST1' end.
    clear AG1 OUT1 MU1 WM1 P1 FR1 PB1 HC1 SE1 ERR1 AUX1 SO1 DP1 AXA1.
    eapply implMC_lift_bind.
    { eapply implM_keeps with (f := ps_heap); [| apply s_emit_heap].
      unfold io_emit, Prog.io, io_S.
      eapply EMIT with (lo := lo) (canary := CAN) (v := r);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - intros; reflexivity.
      - intros; reflexivity.
      - exact FWXO.
      - exact SO1'.
      - lia.
      - apply unsigned_wz_mod32.
      - exact ST1'.
      - unfold EMIT_DEPTH, HARNESS_STACK in *. lia.
      - unfold GLOBALS_TOP. lia.
      - lia.
      - apply (RHEAP_ssp _ _ _ P1').
      - exact MI1'.
      - exact FRM1. }
    cbv beta. intros [] st2 ms2 [PO EH].
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SO2 & SSP2).
    rewrite ?(unsigned_lit (usp + -80)) in MUc by lia. rewrite ?(unsigned_lit (usp + -80)) in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x14c78)) with (Z_to_bv 64 0x14c78) by (symmetry; rpc).
    pose proof (magree_of_munch psegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp + -80 <= a \/ (a < lo /\ (a < 0x10000 \/ 0x94000 <= a)) \/ (0x10000 <= a < 0x94000 /\ ~ (RSTDOUT <= a < RSTDOUT + 232) /\ ~ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024)))
                            -> (fun a0 : Z => outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (P2 : RHEAP st2 (LBT own) m2).
    { eapply RHEAP_ext with (s := st1); [| | ]; cycle 1.
      - unfold ps_heap in EH. congruence.
      - unfold ps_heap in EH. congruence.
      - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P1'| exact MUc| exact WMc|].
        constructor; [left; cbn [fst snd]; atop_facts; lia|].
        constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
        constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (IV2 : INV0 own st2 m2).
    { split. { destruct FR1' as [jb FR1']. exists jb. eapply rw_cells_magree; [exact AG| exact FR1'| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply bytes_at_magree; [exact AG| exact PB1'|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
               destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; rewrite OWNZ in PLEN; lia]. }
      split. { unfold harness_cells, PGOT_ZALLOC in *. eapply rw_cells_magree; [exact AG| exact HC1'| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply (stderr_file0_agree _ _ _ AG); [| exact SE1']. intros a Ha. apply OUT. unfold stderr_addr in Ha. lia. }
      split. { exists errv1. eapply rw_cells_magree; [exact AG| exact ERR1'| intros a Ha; apply OUT; unfold RERRNO in Ha; cbn in Ha; lia]. }
      split; [exact MI2|]. split; [exact ST2|].
      split. { eapply rauxv_ok_frame; [exact AUX1'| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *.
               constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      split; [exact SO2|].
      split. { eapply pdrv_pres_trans; [exact DP1'|]. eapply pdrv_pres_of_munch; [exact MUc| exact WMc| | apply (LB_below _ _ _ P1')].
               constructor; [left; cbn [fst snd]; lia|]. constructor; [right; cbn; left; reflexivity|]. constructor; [right; cbn; right; left; reflexivity| constructor]. }
      split. { unfold PINB, PIN. eapply rw_cells_magree; [exact AG| exact PN1| intros a Ha; apply OUT; unfold PINIT_FLAG in Ha; cbn in Ha; lia]. }
      eapply (atx_cellsA_agree _ _ _ AG); [| exact AXA1']. intros a Ha. apply OUT. unfold atx_addrA, PATX, PATX_N in Ha. lia. }
    clear AG OUT MUc WMc.
    assert (TAIL : forall (x22 : word) (b' : Z), x22 = Z_to_bv 64 b' -> b' = AdapterC.bad_upd b r ->
      evt psegs (fun ms' => RUNST own (if k =? 1 then 0x14c8c else 0x14c54) (k - 1) (AdapterC.bad_upd b r) st2 ms')
          (MS (mkR (Z_to_bv 64 0x14c78) SPF gp tpv v0 v1 v2 (Z_to_bv 64 plen) (Z_to_bv 64 (dptr own)) c0 c1 c2 c3 c4 c5 c6 c7
                   (Z_to_bv 64 (oreg own)) (Z_to_bv 64 (bv_swrap 32 (Z.land r 18446744073709551615 + -1))) (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 k) x22 M2
                   s8 s9 s10 s11 v3 v4 v5 v6)
              F2 (Z_to_bv 64 0x14c84) fc2 None m2 (seg_rom psegs))).
    { intros x22 b' -> ->.
      assert (HB' : 0 <= AdapterC.bad_upd b r <= 1) by (apply AdapterC.bad_upd_01; exact HB).
      zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KK; zify_cond KK.
      - replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evt_done. split; [| exact HB']. exists (Z_to_bv 64 (bv_swrap 32 (Z.land r 18446744073709551615 + -1))). unfold RUNST0. do 16 eexists. exists F2, fc2, m2.
        split; [unfold wz, PINIT_FLAG; reflexivity|]. split; [exact FRM2|]. split; [exact P2| exact IV2].
      - replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evt_done. split; [| exact HB']. exists (Z_to_bv 64 (bv_swrap 32 (Z.land r 18446744073709551615 + -1))). unfold RUNST0. do 16 eexists. exists F2, fc2, m2.
        split; [unfold wz, PINIT_FLAG; reflexivity|]. split; [exact FRM2|]. split; [exact P2| exact IV2]. }
    eapply implMC_evt; [| intros ms' H; exact (HKONT _ _ _ H)].
    zstep. zstep. rewrite (bad_test r) by lia. if_cases KB.
    -
      apply (TAIL (Z_to_bv 64 b) b); [reflexivity|]. unfold AdapterC.bad_upd. rewrite KB. reflexivity.
    - zstep. apply (TAIL (Z_to_bv 64 1) 1); [reflexivity|]. unfold AdapterC.bad_upd. rewrite KB. reflexivity.
  Qed.

  Lemma calls_loop : forall (n : nat) own b (rcw : word) st ms,
    (1 <= n <= 4)%nat -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => True end ->
    RUNST0 own 0x14c54 (Z.of_nat n) rcw b st ms ->
    implMC psegs (AdapterC.run_calls ProgC.fuzz_oneC (io_emit Prog.io) n payload b) st (fun b' st' ms' => RUNST own 0x14c8c 0 b' st' ms') ms.
  Proof.
    induction n as [|n IH]; intros own b rcw st ms HN HB OWNZ R; [lia|].
    cbn [AdapterC.run_calls].
    eapply (call_body own (Z.of_nat (S n)) rcw b st ms (fun rc' => AdapterC.run_calls ProgC.fuzz_oneC (io_emit Prog.io) n payload (AdapterC.bad_upd b rc'))); [lia| exact HB| exact OWNZ| exact R|].
    intros rc' st' ms' R'. destruct n as [|n'].
    - cbn [AdapterC.run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implMC_ret. apply evt_done.
      replace (Z.of_nat 1 - 1) with 0 in R' by lia. exact R'.
    - replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
      destruct R' as [[rcw' R'] HB'].
      apply (IH own (AdapterC.bad_upd b rc') rcw'); [lia| exact HB'| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
  Qed.

  Definition retv (b : Z) : Z := if b =? 0 then 0 else 78.

  Lemma run_tail : forall own b st ms,
    RUNST own 0x14c8c 0 b st ms ->
    implM psegs ((match omodel own with Some q => raw_free q | None => mret tt end) ;;; mret (retv b)) st
          (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB AB lo m0) ms.
  Proof.
    intros own b st ms [[rcw R] HB].
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV]).
    pose proof IV as (FR & PB & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & PN & AXA).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
    unfold wz. destruct FR as [jb FR]. unfold RERRNO in ERR.
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm st (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB AB lo m0) msx) end.
    eapply implM_bind with (Q1 := fun _ st' ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (errv' : word),
        ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 (oreg own)) rcw (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 0) (Z_to_bv 64 b) M2 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x14c94) fc None m' (seg_rom psegs)
        /\ RHEAP st' LB m' /\ rw_cells psegs m' (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells psegs m' RERRNO [C4 errv'] /\ mem_inv psegs m' /\ stk psegs m' lo (usp + -80) /\ rauxv_ok m' AB
        /\ stdout_file m' (ps_so st') /\ pdrv_pres LB usp m0 m' /\ stderr_file0 m' /\ PINB m' /\ atx_cellsA m').
    { destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
      -
        unfold rfree_stmt in FREE.
        eapply implM_mono.
        { eapply FREE with (lo := lo) (B := AB) (p := q) (A := D) (n := plen); try reflexivity; unfold RATP;
            rewrite ?(unsigned_lit RATP_LIT) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | left; reflexivity | exact AUX | lia | exact ST | exact CEIL | unfold RFREE_STACK; lia | exact ERR | exact MI ]. }
        cbv beta. intros [] st' ms' PO.
        destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR3 by lia.
        unfold RATP in ERR3. rewrite ?(unsigned_lit RATP_LIT) in ERR3 by lia. change (RATP_LIT + -164) with RERRNO in ERR3.
        replace (ret_pc (Z_to_bv 64 0x14c94)) with (Z_to_bv 64 0x14c94) by (symmetry; rpc).
        pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
        rewrite (lb_remove_head (q, D, plen) LB ND) in HPR3, HEAP3.
        do 16 eexists. exists m3, (Z_to_bv 64 (bv_unsigned errv)).
        split; [reflexivity|]. split; [exact HEAP3|].
        split; [eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia]|].
        split; [replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned); exact ERR3|].
        split; [exact MI3|]. split; [exact ST3|]. split; [exact AUX3|].
        split; [rewrite SOE3; eapply stdout_file_heap_pres; [exact HPR3| exact SO]|].
        split; [eapply pdrv_pres_trans; [exact DP|]; eapply pdrv_pres_of_heap_sub; [exact HPR3| lia| intros bb Hb; exact Hb]|].
        split; [eapply stderr_file0_heap_pres; [exact HPR3| exact SE]|].
        split; [eapply PIN_heap_pres; [exact HPR3| exact PN]| eapply atx_cellsA_heap_pres; [exact HPR3| exact AXA]].
      -
        apply implM_ret. eapply evt_mono; [apply (rfree_null_spec); reflexivity|].
        cbv beta. intros ms' ->. replace (ret_pc (Z_to_bv 64 0x14c94)) with (Z_to_bv 64 0x14c94) by (symmetry; rpc).
        do 16 eexists. exists m, errv.
        split; [reflexivity|]. split; [exact P|]. split; [exact FR|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|].
        split; [exact SO|]. split; [exact DP|]. split; [exact SE|]. split; [exact PN| exact AXA]. }
    cbv beta. intros [] st' ms' (x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & P' & FR' & ERR' & MI' & ST' & AUX' & SO' & DP' & SE' & PN' & AXA').
    apply implM_ret.
    zstep. zstep. zstep.
    replace (Z.land (Z.land (Z.b2z (b <? 1) + -1) 18446744073709551615) 78) with (retv b)
      by (unfold retv; assert (Eb : b = 0 \/ b = 1) by lia; destruct Eb as [-> | ->]; reflexivity).
    do 9 zstep. release_frame FR' ST' (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m', errv'.
    split; [reflexivity|].
    split; [unfold retv; destruct (b =? 0); lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR'|].
    split; [exact AUX'|]. split; [exact DP'|]. split; [exact P'|]. split; [exact SO'|].
    split; [exact AXA'|]. unfold PAEF_INCB. unfold PINB, PIN in PN'.
    change ([C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)]) with ([C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)] ++ [C1 (Z_to_bv 8 0)]) in PN'.
    apply (proj1 (rw_cells_app psegs _ _ _ _)) in PN'. destruct PN' as [_ PN']. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PN'.
    unfold PINIT_FLAG in PN'. replace (208512 + 4) with 208516 in PN' by reflexivity. exact PN'.
  Qed.

  Definition PRE1 (s : PState) (m : mem) : Prop :=
    RHEAP s LB m /\ FRAME m /\ bytes_at psegs m A (zbytes content) /\ harness_cells m /\ stderr_file0 m
    /\ (exists errv : word, rw_cells psegs m RERRNO [C4 errv]) /\ mem_inv psegs m /\ stk psegs m lo (usp + -80)
    /\ rauxv_ok m AB /\ stdout_file m (ps_so s) /\ pdrv_pres LB usp m0 m
    /\ PINB m /\ atx_cellsA m.

  Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 calls) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation POST s := (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m0).

  Lemma trun_empty : forall s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    plen = 0 -> frm0 fc -> PRE1 s m ->
    implMC psegs (ProgC.runC cfg payload) s (POST s) (EST 0x14c44 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & FR & CT & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & PN & AXA).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    unfold ProgC.runC, AdapterC.target_run, AdapterC.payload_copy. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMC_liftretb. cbv beta iota.
    apply implMC_from_evt. zstep. zstep. zstep. zstep. apply evt_done.
    eapply implMC_bind.
    { eapply (calls_loop (Z.to_nat calls) None 0 x19); [lia| lia| exact PZ|].
      unfold RUNST0. do 16 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold PEMPTY, PINIT_FLAG, wz; reflexivity|].
      split; [exact FRM|]. split; [exact P|].
      split; [exact FR|].
      assert (PE : payload = []). { unfold payload. apply skipn_all2. unfold plen, zlength in PZ. lia. }
      split; [cbn [dptr]; rewrite PE; cbn [zbytes map]; apply bytes_at_nil; unfold PEMPTY; lia|].
      split; [exact HC|]. split; [exact SE|]. split; [exists errv; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|]. split; [exact SO|].
      split; [exact DP|]. split; [exact PN| exact AXA]. }
    cbv beta. intros b st' ms' R.
    eapply (implMC_of_implM psegs _ ((match omodel None with Some q => raw_free q | None => mret tt end) ;;; mret (retv b))); [unfold retv; clift_eq|].
    apply (run_tail None b st' ms' R).
  Qed.

  Lemma pdrv_pres_of_newblock : forall st q D n m m',
    RHEAP st ((q, D, n) :: LB) m -> munch [(D, D + n)] m m' -> wmono psegs m m' -> pdrv_pres LB usp m m'.
  Proof.
    intros st q D n m m' P MU WM a Ha Hc Hx.
    destruct (magree_of_munch psegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
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

  Lemma trun_copy : forall s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    plen <> 0 -> frm0 fc -> PRE1 s m ->
    implMC psegs (ProgC.runC cfg payload) s (POST s) (EST 0x14bf8 x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & FR & CT & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & PN & AXA).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts s None m P) as (BA1 & BA2 & BA3 & _). atop_facts.
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    unfold zlength in LC, L6.
    unfold ProgC.runC, AdapterC.target_run, AdapterC.payload_copy. rewrite !PLEN.
    replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMC_lift_bind_assoc.
    destruct FR as [jb FR]. unfold RERRNO in ERR.
    apply implMC_from_evt. zstep. zstep. apply evt_done.
    eapply implMC_lift_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := lo) (B := AB); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RATP_LIT) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
        first [ exact P | exact AUX | lia | exact ST | exact CEIL | unfold RMALLOC_STACK; lia | exact ERR | exact MI ]. }
    cbv beta. intros r s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit RATP_LIT) in ERR1 by lia. rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
    change (RATP_LIT + -164) with RERRNO_LIT in ERR1.
    replace (ret_pc (Z_to_bv 64 0x14c00)) with (Z_to_bv 64 0x14c00) by (symmetry; rpc).
    assert (FR1 : rw_cells psegs m1 (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    assert (CT1 : bytes_at psegs m1 A (zbytes content)).
    { eapply rheap_pres_bytes_at; [exact HPR| exact CT|]. right; right. exists (p, A, cap). split; [exact INLB|]. cbn. rewrite zbytes_length. lia. }
    assert (PN1 : PINB m1) by (unfold PINB in *; eapply PIN_heap_pres; [exact HPR| exact PN]).
    assert (AXA1 : atx_cellsA m1) by (eapply atx_cellsA_heap_pres; [exact HPR| exact AXA]).
    destruct r as [nb|].
    2:{
        destruct RR as [-> HEAP1].
        apply implMC_liftretb. cbv beta iota. apply implMC_ret.
        zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity].
        zstep. zstep. do 9 zstep. release_frame FR1 ST1 (bv_unsigned sp). zstep. zstep.
        apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m1, errv1.
        split; [reflexivity|]. split; [lia|]. split; [exact MI1|]. split; [exact FRM|]. split; [exact ST1|].
        split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR1|].
        split; [exact AUX1|].
        split; [eapply pdrv_pres_trans; [exact DP| eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros bb Hb; exact Hb]]|].
        split; [exact HEAP1|]. split; [rewrite SOE; eapply stdout_file_heap_pres; [exact HPR| exact SO]|].
        split; [exact AXA1|]. unfold PAEF_INCB. unfold PINB, PIN in PN1.
        change ([C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)]) with ([C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)] ++ [C1 (Z_to_bv 8 0)]) in PN1.
        apply (proj1 (rw_cells_app psegs _ _ _ _)) in PN1. destruct PN1 as [_ PN1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PN1.
        unfold PINIT_FLAG in PN1. replace (208512 + 4) with 208516 in PN1 by reflexivity. exact PN1. }
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & _).
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). atop_facts.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + plen <= A \/ A + cap <= A').
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', plen) (p, A, cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E.
      apply (in_map blk_id) in INLB. exact INLB. }
    assert (PB : bytes_at psegs m1 PAY (zbytes payload)).
    { rewrite <- (firstn_skipn (Z.to_nat (6 + L)) (zbytes content)) in CT1. apply bytes_at_app in CT1. destruct CT1 as [_ X].
      rewrite length_firstn, zbytes_length in X. unfold payload, zbytes. rewrite <- skipn_map. unfold zbytes in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content))) with PAY in X by (rewrite EPAY; lia). exact X. }
    apply implMC_liftretb. cbv beta iota.
    apply implMC_from_evt.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply memcpy_callv with (src := zbytes payload) (junk := junk');
        [exact PB| rewrite zbytes_length; lia| exact NBLK| unfold plen, zlength in *; lia| lia| unfold plen, zlength in *; lia| lia| exact MI1]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB2 & _).
    unfold PINB, PIN in PN1. destruct AXA1 as [AXA1a AXA1b]. unfold PATX, PATX_CALL, PAEF_GUARD, PINIT_FLAG in AXA1a, AXA1b, PN1.
    transport_after_call psegs m1 m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x14c14)) with (Z_to_bv 64 0x14c14) by (symmetry; rpc).
    assert (P2 : RHEAP s1' ((nb, A', plen) :: LB) m2).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP1| exact MUc| exact WMc|].
      constructor; [| constructor]. right; right. exists (nb, A', plen). split; [left; reflexivity|]. cbn. lia. }
    pose proof (magree_of_munch psegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (a < A' \/ A' + plen <= a) -> (fun a0 : Z => outside [(A', A' + plen)] a0) a) by (intros a Ha; cbn; lia).
    assert (IV2 : INV0 (Some (nb, A')) s1' m2).
    { split; [exists jb; exact FR1|].
      split; [cbn [dptr]; apply (rw_cells_bytes_at psegs) in NB2; cbn [cells_bytes cbytes app] in NB2; rewrite app_nil_r in NB2; exact NB2|].
      split. { unfold harness_cells, PGOT_ZALLOC in *. eapply rw_cells_magree; [exact AG| eapply rheap_pres_rw_cells; [exact HPR| exact HC| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia]| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply (stderr_file0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia|]. eapply stderr_file0_heap_pres; [exact HPR| exact SE]. }
      split; [exists errv1; exact ERR1|]. split; [exact MI2|]. split; [exact ST1|].
      split. { eapply rauxv_ok_frame; [exact AUX1| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
      split. { rewrite SOE. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia|]. eapply stdout_file_heap_pres; [exact HPR| exact SO]. }
      split. { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_trans; [eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros bb Hb; exact Hb]|].
               eapply pdrv_pres_of_newblock; [exact HEAP1| exact MUc| exact WMc]. }
      split; [unfold PINB, PIN, PINIT_FLAG; exact PN1| split; [exact AXA1a| exact AXA1b]]. }
    clear AG OUT MUc WMc.
    zstep. zstep. zstep. zstep. apply evt_done.
    eapply implMC_bind.
    { eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0 x19); [lia| lia| exact I|].
      unfold RUNST0. do 16 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold PINIT_FLAG, wz; reflexivity|].
      split; [exact FRM|]. split; [exact P2| exact IV2]. }
    cbv beta. intros b st' ms'' R.
    eapply (implMC_of_implM psegs _ ((match omodel (Some (nb, A')) with Some q => raw_free q | None => mret tt end) ;;; mret (retv b))); [unfold retv; clift_eq|].
    apply (run_tail (Some (nb, A')) b st' ms'' R).
  Qed.

  Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (errv : word),
    RHEAP s LB m0 -> bytes_at psegs m0 A (zbytes content) -> trun_cells0 m0 -> stderr_file0 m0 -> rauxv_ok m0 AB ->
    stk psegs m0 lo usp -> rw_cells psegs m0 RERRNO [C4 errv] -> mem_inv psegs m0 -> frm0 fc ->
    stdout_file m0 (ps_so s) ->
    tp = tpv -> a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 PAY -> a3 = Z_to_bv 64 plen ->
    implMC psegs (ProgC.runC cfg payload) s (POST s)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PTARGET_RUN) fc None m0 (seg_rom psegs)).
  Proof.
    intros until errv. intros P0 CT TR0 SE0 AUX0 ST0 ERR0 MI0 FRM SO0 -> -> -> -> ->.
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts s None m0 P0) as (BA1 & BA2 & BA3 & _). atop_facts.
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    unfold zlength in LC, L6. unfold RERRNO in ERR0.
    apply implMC_from_evt.
    destruct (RHEAP_libc_head _ _ _ P0) as (cdt & thr & sec & tm1 & LCH).
    eapply trun_init; [exact ST0| exact MI0| exact TR0| exact LCH|].
    intros m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST1 HC1 PN1 AXA1 MU WM MI1.
    unfold PINIT_FLAG, PATX, PATX_N in MU.
    pose proof (magree_of_munch psegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, ((a < lo /\ (a < 0x10000 \/ 0x94000 <= a)) \/ (0x10000 <= a < 0x94000 /\ ~ (0x32e80 <= a < 0x32e80 + 5) /\ ~ (0x92fc0 <= a < 0x92fc0 + 544)))
                            -> (fun a0 : Z => outside [(usp - 128, usp); (0x32e80, 0x32e80 + 5); (0x92fc0, 0x92fc0 + 544)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (CT1 : bytes_at psegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. lia. }
    assert (ERR1 : rw_cells psegs m1 RERRNO [C4 errv]).
    { eapply rw_cells_magree; [exact AG| exact ERR0|]. intros a Ha. apply OUT. right. unfold RERRNO in *. cbn in Ha. lia. }
    assert (SE1 : stderr_file0 m1) by (eapply (stderr_file0_agree _ _ _ AG); [| exact SE0]; intros a Ha; apply OUT; right; unfold stderr_addr in Ha; lia).
    assert (SO1 : stdout_file m1 (ps_so s)) by (eapply (stdout_file_agree _ _ _ _ AG); [| exact SO0]; intros a Ha; apply OUT; right; unfold stdout_addr in Ha; lia).
    assert (AUX1 : rauxv_ok m1 AB).
    { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|]. unfold RAUXV_CELL, RLIBC in *.
      constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (P1 : RHEAP s LB m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MU| exact WM|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (DP1 : pdrv_pres LB usp m0 m1).
    { eapply pdrv_pres_of_munch; [exact MU| exact WM| | apply (LB_below s None m0 P0)].
      constructor; [left; cbn [fst snd]; lia|].
      constructor; [right; unfold pstdout_ivs, PINIT_FLAG; cbn; do 2 right; left; reflexivity|].
      constructor; [right; unfold pstdout_ivs, PATX; cbn; do 3 right; left; reflexivity| constructor]. }
    assert (PRE : PRE1 s m1).
    { split; [exact P1|]. split; [exact FR|]. split; [exact CT1|]. split; [exact HC1|]. split; [exact SE1|]. split; [exists errv; exact ERR1|].
      split; [exact MI1|]. split; [exact ST1|]. split; [exact AUX1|]. split; [exact SO1|]. split; [exact DP1|]. split; [exact PN1| exact AXA1]. }
    clear AG OUT MU WM CT ERR0 SE0 SO0 AUX0 P0 ST0 MI0 TR0.
    zstep. if_cases KL; zify_cond KL.
    -
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      zstep. zstep. if_cases KP; zify_cond KP.
      +
        apply evt_done. rewrite <- EC.
        eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evt_done. rewrite <- EC.
        eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
    -
      destruct (nth_error content 2) as [c2|] eqn:EC2; [| exfalso; apply nth_error_None in EC2; lia].
      pose proof (proj1 (Forall_forall _ _) FC c2 (nth_error_In _ _ EC2)) as C2R. cbn beta in C2R.
      pose proof (u8ro_read psegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1 ltac:(unfold zbytes; rewrite nth_error_map, EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
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
  unfold RATP, RERRNO, wz in ERR0 |- *. rewrite (unsigned_lit 470912) in ERR0 by lia. exact ERR0.
Qed.

End CANSEC1.
