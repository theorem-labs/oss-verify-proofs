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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2 Pj_loc_kit Pj_os_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Pj_kit Imp_oss_defs.
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
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | u8arr _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r end; fail "PROBE".

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma zx8_lit : forall x, 0 <= x < 2^64 -> zx8 (Z_to_bv 64 x) = Z_to_bv 64 (x mod 256).
Proof. intros x H. unfold zx8. f_equal. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma zxb_any : forall x, zxb (Z_to_bv 8 x) = Z_to_bv 64 (x mod 256).
Proof. intros x. unfold zxb. f_equal; rewrite ?Z_to_bv_unsigned; reflexivity. Qed.
Lemma le1_smallZ : forall v, 0 <= v < 256 -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.
Lemma u8_lit : forall x, bv_unsigned (Z_to_bv 8 x) = x mod 256.
Proof. intros x. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma zxb_u : forall x, bv_unsigned (zxb (Z_to_bv 8 x)) = x mod 256.
Proof.
  intros x. rewrite zxb_any. rewrite unsigned_lit; [reflexivity|].
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma pb_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (O len : Z) (D cap : Z) (blk : option bptr) (f : nat) (w : Z) (oldD olda : Z) (src : list byte),
    let st := mkOss D cap blk (S f) w in
    RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo (q + -64) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_PB_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= O -> O + 264 <= B -> 0 <= len <= SJ_PADMAX -> OSNUM len st -> w = os_lim st ->
    2 * cap <= PJ_CAPMAX len ->
    rw_cells usegs m (q + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    lx_pres LB0 q [(O + 72, O + 96)] m0 m ->

    rw_cells usegs m oldD [CB (Z.to_nat (os_lim st)) src] ->
    match blk with
    | None => oldD = O + 73 /\ olda = 23 /\ cap = IMP_SCAP0 /\ (exists j1, rw_cells usegs m (O + 72) [C1 (Z_to_bv 8 44)] /\ rw_cells usegs m (O + 95) [CB 1 j1])
    | Some b => oldD = D /\ olda = cap /\ rblock_range D cap /\ cap mod 16 = 0
                /\ rw_cells usegs m (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 D)]
                /\ (exists jr, rw_cells usegs m (D + (cap - 1)) [CB 1 jr])
    end ->
    implM usegs (pj_grow1 raw_malloc raw_free ps_so set_so_ps (2 * cap) blk) s
          (pb_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B O len st m0)
          (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 0) (Z_to_bv 64 (O + 72)) (Z_to_bv 64 (os_lim st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 oldD) (Z_to_bv 64 (2 * cap)) xs4 (Z_to_bv 64 olda) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 0x80cc4) fc None m (seg_rom usegs)).
  Proof.
    intros until src. cbv zeta. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB HL NUM FULL ZB FR PRES OLD CASE.
    unfold OSS_PB_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (OSNUM_cap24 len _ NUM) as CAP24. cbn [os_cap] in CAP24.
    pose proof (PJ_CAPMAX_bound len HL) as CMB.
    unfold osblocks, os_lim in *. cbn [os_data os_cap os_blk os_fuel os_w] in *.
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    set (n := match blk with Some _ => cap - 1 | None => 22 end) in *.
    assert (NR : 22 <= n /\ n + 1 <= 2 * cap /\ n < cap) by (subst n; destruct blk; unfold IMP_SCAP0 in *; [lia|]; destruct CASE as (_ & _ & -> & _); lia).
    assert (C16 : (2 * cap) mod 16 = 0).
    { destruct blk; [destruct CASE as (_ & _ & _ & M16 & _)| destruct CASE as (_ & _ & EC & _); rewrite EC; unfold IMP_SCAP0]; Z.div_mod_to_equations; lia. }
    assert (OLDR : 0 < oldD /\ oldD + n < 2^63 /\ (forall a, oldD <= a < oldD + n -> outside [(q - 64 - 16 - 8192, q - 64)] a)).
    { destruct blk as [b|].
      - destruct CASE as (-> & _ & (A0 & A16 & _ & AC & AS) & _). split; [lia|]. split; [lia|]. intros a Ha. cbn [outside]. split; [lia| exact I].
      - destruct CASE as (-> & _). split; [lia|]. split; [lia|]. intros a Ha. cbn [outside]. split; [lia| exact I]. }
    hide OLD. hide CASE.
    unfold pj_grow1. unfold implM. iprefix.

    step. step. step.
    ihere. to_implM.
    eapply implM_bind.
    { eapply (opnew_body HM) with (B := B) (lo := lo);
        [exact HEAP| exact AUX| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia]. }
    cbv beta. intros pn s2' ms2 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
    replace (ret_pc (Z_to_bv 64 0x80cd0)) with (Z_to_bv 64 0x80cd0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2.
    pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in NC.
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    unhide OLD. apply (rw_cells_agree _ _ _ _ _ AG) in OLD.
    2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. unhide CASE. destruct blk as [b|].
        - destruct CASE as (-> & _). right; right. exists (b, D, cap). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - destruct CASE as (-> & _). left. lia. }
    assert (CASE2 : match blk with
      | None => oldD = O + 73 /\ olda = 23 /\ cap = IMP_SCAP0 /\ (exists j1, rw_cells usegs m2 (O + 72) [C1 (Z_to_bv 8 44)] /\ rw_cells usegs m2 (O + 95) [CB 1 j1])
      | Some b => oldD = D /\ olda = cap /\ rblock_range D cap /\ cap mod 16 = 0
                  /\ rw_cells usegs m2 (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 D)]
                  /\ (exists jr, rw_cells usegs m2 (D + (cap - 1)) [CB 1 jr])
      end).
    { unhide CASE. destruct blk as [b|].
      - destruct CASE as (E1 & E2 & RB & M16 & R3 & (jr & JR)). split; [exact E1|]. split; [exact E2|]. split; [exact RB|]. split; [exact M16|]. split.
        + eapply rw_cells_agree; [exact AG| exact R3| intros a Ha; left; cbn in Ha; lia].
        + exists jr. eapply rw_cells_agree; [exact AG| exact JR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (b, D, cap). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; subst oldD; destruct RB as (? & ? & ? & ? & ?); lia].
      - destruct CASE as (E1 & E2 & E3 & (j1 & R1 & R2)). split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. exists j1. split.
        + eapply rw_cells_agree; [exact AG| exact R1| intros a Ha; left; cbn in Ha; lia].
        + eapply rw_cells_agree; [exact AG| exact R2| intros a Ha; left; cbn in Ha; lia]. }
    clear CASE. rename CASE2 into CASE.
    assert (PRES2 : lx_pres LB0 q [(O + 72, O + 96)] m0 m2).
    { eapply lx_pres_trans; [exact PRES|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; apply in_or_app; right; exact Hb]. }

    assert (SEPN : oldD + n + 1 <= NEW \/ NEW + 2 * cap <= oldD).
    { unhide CASE. destruct blk as [b|].
      - destruct CASE as (-> & _). pose proof (LH_head_sep _ _ _ _ _ _ b D cap HEAP2 ltac:(left; reflexivity)). lia.
      - destruct CASE as (-> & _). right. lia. }
    clear AG HP.
    hide CASE.
    pose proof (munch_refl [(q - 64, q); (NEW, NEW + 2 * cap); (O + 72, O + 96)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix.

    step. step. step. step.
    destruct (rw_cells_CB_at _ _ _ _ n BLKN ltac:(lia)) as [NPRE NREST].
    pose proof OLD as OLD0. apply rw_cells_bytes_at in OLD0. cbn [cells_bytes cbytes] in OLD0. rewrite app_nil_r in OLD0.
    assert (LSRC : length src = Z.to_nat n) by (destruct OLD as [[[HLn _] _] _]; exact HLn).
    hide NREST. hide OLD.
    eapply evt_cut.
    { eapply memmove_far_callZ with (Dst := NEW) (Src := oldD) (N := n) (src := src) (junk := firstn (Z.to_nat n) jnew);
        [exact OLD0| exact LSRC| exact NPRE| lia| lia| lia| lia| lia| lia| assumption]. }
    intros ms' PO. unfold memcpy_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & NPRE4 & SRC4).
    replace (ret_pc (Z_to_bv 64 0x80ce0)) with (Z_to_bv 64 0x80ce0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    unhide NREST. apply (rw_cells_agree _ _ _ _ _ AG4) in NREST; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
    unhide OLD. apply (rw_cells_agree _ _ _ _ _ AG4) in OLD; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in ERR2; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    assert (HEAP4 : RHEAP s2' ((pn, NEW, 2 * cap) :: match blk with Some b => [(b, D, cap)] | None => [] end ++ LB0) m4).
    { eapply LH_frame; [exact HEAP2| exact MU4| exact WM4|]. constructor; [| constructor].
      eapply (W_ok_block _ (pn, NEW, 2 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (ST4 : stk usegs m4 lo (q + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| cbn [disjoint_from]; lia]).
    assert (PRES4 : lx_pres LB0 q [(O + 72, O + 96)] m0 m4).
    { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [lia| | lia].
      intros Hs. apply (DJN a); [| lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    assert (CASE4 : match blk with
      | None => oldD = O + 73 /\ olda = 23 /\ cap = IMP_SCAP0 /\ (exists j1, rw_cells usegs m4 (O + 72) [C1 (Z_to_bv 8 44)] /\ rw_cells usegs m4 (O + 95) [CB 1 j1])
      | Some b => oldD = D /\ olda = cap /\ rblock_range D cap /\ cap mod 16 = 0
                  /\ rw_cells usegs m4 (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 D)]
                  /\ (exists jr, rw_cells usegs m4 (D + (cap - 1)) [CB 1 jr])
      end).
    { unhide CASE. destruct blk as [b|].
      - destruct CASE as (E1 & E2 & RB & M16 & R3 & (jr & JR)). split; [exact E1|]. split; [exact E2|]. split; [exact RB|]. split; [exact M16|]. split.
        + eapply rw_cells_agree; [exact AG4| exact R3| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        + exists jr. eapply rw_cells_agree; [exact AG4| exact JR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. subst oldD. split; [lia| exact I].
      - destruct CASE as (E1 & E2 & E3 & (j1 & R1 & R2)). split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. exists j1. split.
        + eapply rw_cells_agree; [exact AG4| exact R1| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        + eapply rw_cells_agree; [exact AG4| exact R2| intros a Ha; cbn in Ha; cbn [outside]; subst oldD; split; [lia| exact I]]. }
    clear CASE. rename CASE4 into CASE.

    pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ NPRE4 NREST ltac:(lia)) as NEWC.
    replace (Z.to_nat n + (Z.to_nat (2 * cap) - Z.to_nat n))%nat with (Z.to_nat (2 * cap)) in NEWC by lia.
    clear NPRE4 NREST SRC4 MU4 WM4 AG4 MI2 ST2 AUX2 HEAP2 BLKN MU WM.

    assert (FIN : forall m6 st6 (errv6 : word) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 (ja jb jc bn : list byte),
      RHEAP st6 ((pn, NEW, 2 * cap) :: LB0) m6 -> rauxv_ok m6 B -> mem_inv usegs m6 -> stk usegs m6 lo (q + -64) ->
      rw_cells usegs m6 1004708 [C4 errv6] -> ps_fa st6 = ps_fa s -> ps_so st6 = ps_so s -> lx_pres LB0 q [(O + 72, O + 96)] m0 m6 ->
      rw_cells usegs m6 (O + 72) [CB 8 ja; CB 8 jb; CB 8 jc] ->
      rw_cells usegs m6 NEW [CB (Z.to_nat (2 * cap)) bn] ->
      rw_cells usegs m6 (q + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (mret pn st6)
                                 (epost (fun p => pb_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B O len
                                                          (mkOss D cap blk (S f) w) m0 (fst p) (snd p))) ms')
          (MS (mkR yra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) yt0 yt1 yt2 (Z_to_bv 64 0) (Z_to_bv 64 (O + 72)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   (Z_to_bv 64 oldD) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 n) (Z_to_bv 64 olda) (Z_to_bv 64 NEW) s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
              F (Z_to_bv 64 0x80cf4) fc None m6 (seg_rom usegs))).
    { intros m6 st6 errv6 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 ja jb jc bn HEAP6 AUX6 MI6 ST6 ERR6 FA6 SO6 PRES6 HDR NEWC6 FR6.
      clear OLD CASE FR ERR2 NEWC HEAP4 AUX4 ST4 PRES4 MI4.
      pose proof (munch_refl [(q - 64, q); (O + 72, O + 96); (NEW, NEW + 2 * cap)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      pose proof (munch_refl [(O + 72, O + 96)]%Z m6) as MU1. pose proof (wmono_refl usegs m6) as WM1.
      hide NEWC6.

      step. step. step. step. step. step. step.
      rewrite unsigned_lit in HDR by lia. rewrite lor1_even in HDR by (Z.div_mod_to_equations; lia).

      unhide NEWC6.
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU1 WM1)) in NEWC6; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
      assert (LBN : length bn = Z.to_nat (2 * cap)) by (destruct NEWC6 as [[[HLx _] _] _]; exact HLx).
      apply u8arr_of_rw_cells in NEWC6. rename NEWC6 into BA.
      clear MU1 WM1.
      pose proof (u8arr_store_ok usegs _ _ _ n (Z_to_bv 64 (NEW + n)) BA ltac:(rewrite LBN; lia) ltac:(reflexivity)) as SOK.
      step. first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0] | idtac].
      pose proof (u8arr_write usegs _ _ _ n (Z_to_bv 8 0) BA ltac:(rewrite LBN; lia)) as BA2. clear BA. store_done.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      pose proof (u8arr_store_ok usegs _ _ _ (n + 1) (Z_to_bv 64 (NEW + n + 1)) BA2 ltac:(rewrite upd_length, LBN; lia) ltac:(unfold wa; f_equal; lia)) as SOK2.
      step. first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0] | idtac].
      replace (Z_to_bv 64 (NEW + n + 1)) with (wa (NEW + (n + 1))) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write usegs _ _ _ (n + 1) (Z_to_bv 8 0) BA2 ltac:(rewrite upd_length, LBN; lia)) as BA3. clear BA2. store_done.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
      apply rw_cells_of_u8arr in BA3. rewrite !upd_length, LBN in BA3.

      do 8 step. step. release_frame FR6 ST6 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      ihere. to_implM. apply implM_ret. apply evt_done. unfold pb_post, os_lim, os_cap, os_blk. cbn [os_data os_w os_fuel].
      do 15 eexists. exists m9, errv6, NEW.
      split; [cbv delta [mkR]; reflexivity|].
      split; [assumption|]. split; [exact ST6|]. split; [rewrite ELX; exact ERR6|].
      split. { eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|].
               constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [exact FA6|]. split; [exact SO6|].
      split. { eapply LH_frame; [exact HEAP6| exact MU| exact WM|].
               constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
               eapply (W_ok_block _ (pn, NEW, 2 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
      split; [subst n; exact HDR|].
      split; [eexists; exact BA3|].
      split; [exact BRN|]. split; [exact C16|].
      eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP6) as DJN.
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia|]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| | lia].
        intros Hs. apply (DJN a); [exact HC| lia]. }

    step. step.
    unhide CASE. destruct blk as [b|].
    -
      destruct CASE as (EO & EA & RB & M16 & R3 & (jr & JR)). subst oldD olda.
      destruct RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step. step.
      cbn [app] in HEAP4.
      pose proof (RHEAP_pull _ [(pn, NEW, 2 * cap)] (b, D, cap) LB0 _ HEAP4) as HEAP4'. cbn [app] in HEAP4'.
      assert (ND : List.NoDup (map blk_id ((b, D, cap) :: (pn, NEW, 2 * cap) :: LB0))) by (eapply LH_nodup; exact HEAP4').
      ihere. to_implM. eapply implM_bind.
      { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := D) (n := cap);
          [exact HEAP4'| left; reflexivity| exact AUX4| lia| exact ST4| exact CEIL'| unfold RFREE_STACK; lia| exact ERR2| exact MI4| lia]. }
      cbv beta. intros [] s6' ms6 PO. unfold free_postZ in PO.
      destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                      & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
      replace (ret_pc (Z_to_bv 64 0x80cf4)) with (Z_to_bv 64 0x80cf4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.

      merge_at R3 0%nat 1%nat. merge_at R3 1%nat 1%nat. merge_at R3 2%nat 1%nat.
      unfold implM. iprefix.
      eapply FIN with (errv6 := errv2).
      + exact HEAP6.
      + exact AUX6.
      + exact MI6.
      + exact ST6.
      + exact ERR6.
      + congruence.
      + congruence.
      + eapply lx_pres_trans; [exact PRES4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| intros b0 Hb0; right; exact Hb0].
      + eapply rw_cells_agree; [exact AG6| exact R3| intros a Ha; left; cbn in Ha; lia].
      + eapply rw_cells_agree; [exact AG6| exact NEWC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
        exists (pn, NEW, 2 * cap). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
      + eapply rw_cells_agree; [exact AG6| exact FR| intros a Ha; left; cbn in Ha; lia].
    -
      destruct CASE as (EO & EA & EC & (j1 & R1 & R2)). subst oldD olda.
      if_true.
      ihere. to_implM. apply implM_retb. unfold implM. iprefix. cbn [app] in HEAP4.

      replace (Z.to_nat n) with 22%nat in OLD by (subst n; reflexivity).
      pose proof (rw_cells_join _ _ _ _ _ R1 OLD ltac:(cbn [app cells_size csize Nat.add]; lia)) as R12. cbn [app] in R12.
      pose proof (rw_cells_join _ _ _ _ _ R12 R2 ltac:(cbn [app cells_size csize Nat.add]; lia)) as R3. clear R1 R2 OLD R12. cbn [app] in R3.
      merge_at R3 0%nat 3%nat.
      apply (rw_cells_split_CB usegs _ _ [] 24 _ [] [8;8;8]%nat) in R3; [|reflexivity]. cbn [mk_CB_cells app] in R3.
      eapply FIN with (errv6 := errv2); try eassumption; congruence.
  Qed.
  Theorem push_back_proof : push_back_stmt.
  Proof.
    unfold push_back_stmt. intros until st. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB HL REP NUM FULL OK.
    destruct (OSNUM_fuel _ _ HL NUM) as [f EF].
    unfold OSS_PUSH_BACK, OSS_PB_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (OSNUM_cap24 _ _ NUM) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB. apply chain_ok_spec in OK.
    destruct st as [D cap blk fuel w]. unfold osblocks, os_lim, STRREP in *. cbn [os_data os_cap os_blk os_fuel os_w] in *. subst fuel.
    pose proof NUM as (WB & FU & CB16 & HB). unfold os_lim, os_k in WB, FU, CB16, HB. cbn [os_data os_cap os_blk os_fuel os_w] in WB, FU, CB16, HB.
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }

    destruct blk as [b|].
    -
      destruct REP as (R3 & (bs & BLK) & RB). rename HB into M16. cbn [app] in HEAP.
      pose proof RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
      pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      do 8 step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s ((b, D, cap) :: LB0) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(O + 72, O + 96)] m m1).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      clear MU WM.

      pose proof (rw_cells_C8_read1_g usegs m1 _ _ _ R3) as RD. rewrite unsigned_lit in RD by lia.
      step. step. rewrite zxb_u, long_byte0 by (Z.div_mod_to_equations; lia). step. step. if_true.

      step. step. step. rewrite (unsigned_lit (cap + 1)) by lia. rewrite long_capmask by (Z.div_mod_to_equations; lia). step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

      step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step. step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step.
      rewrite (unsigned_lit (cap + -1)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      rewrite (unsigned_lit ((cap + -1) * 2)) by lia.
      replace (Z.lor ((cap + -1) * 2) 7) with (2 * cap - 1) by (rewrite lor_low3 by lia; Z.div_mod_to_equations; lia).

      step. step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
      step. step. step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
      step. step.
      replace (Z_to_bv 64 (2 * cap - 1 + 1)) with (Z_to_bv 64 (2 * cap)) by (f_equal; lia).
      replace (Z_to_bv 64 (cap + -1 + 1)) with (Z_to_bv 64 cap) by (f_equal; lia).
      replace (Z_to_bv 64 (cap + -1)) with (Z_to_bv 64 (cap - 1)) by (f_equal; lia).
      destruct (rw_cells_CB_at _ _ _ _ (cap - 1) BLK ltac:(lia)) as [OLD JR].
      ihere. to_implM.
      eapply pb_tail with (m0 := m) (LB0 := LB0) (lo := lo) (B := B) (errv := errv) (len := len) (olda := cap) (oldD := D) (w := w)
                         (src := firstn (Z.to_nat (cap - 1)) bs);
        [cbn [osblocks os_blk app]; exact HEAP1| exact AUX1| lia| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_PB_STACK, RMALLOC_STACK; lia
        | exact ERR| assumption| lia| lia| exact HL| exact NUM| exact FULL| lia| exact FR| exact PRES1| exact OLD| ].
      cbn [os_blk]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RB|]. split; [exact M16|]. split; [exact R3|].
      eexists. replace (Z.to_nat cap - Z.to_nat (cap - 1))%nat with 1%nat in JR by lia. exact JR.
    -
      destruct REP as (R1 & (bs & R23) & ED). destruct HB as [EC _]. subst D. cbn [app] in HEAP.
      pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      do 8 step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s LB0 m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(O + 72, O + 96)] m m1).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      clear MU WM.

      step. step. step. step. if_false.

      step. step. if_false. step. step. step. step. step.
      subst cap.
      destruct (rw_cells_CB_at _ _ _ _ 22 R23 ltac:(lia)) as [OLD J1]. replace (O + 73 + 22) with (O + 95) in J1 by lia.
      ihere. to_implM.
      eapply pb_tail with (m0 := m) (LB0 := LB0) (lo := lo) (B := B) (errv := errv) (len := len) (olda := 23) (oldD := O + 73) (w := w)
                         (src := firstn (Z.to_nat 22) bs);
        [cbn [osblocks os_blk app]; exact HEAP1| exact AUX1| lia| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_PB_STACK, RMALLOC_STACK; lia
        | exact ERR| assumption| lia| lia| exact HL| exact NUM| exact FULL| lia| exact FR| exact PRES1| exact OLD| ].
      cbn [os_blk]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists (skipn (Z.to_nat 22) bs). split; [exact R1| exact J1].
  Qed.

End Proofs.
End WithCeiling0.
