(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_defs Atp_kitu Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac br_no := first [if_false | if_lia].

Ltac b2z_false := match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) end.
Ltac b2z_true := match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) end.

Ltac b2z_lit := repeat match goal with |- context [Z.b2z ?c] => let v := eval vm_compute in (Z.b2z c) in change (Z.b2z c) with v end.

Lemma lxor_signbit : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 i) as [<-|NE]; [| apply Bool.andb_false_r].
  rewrite Bool.andb_true_r. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lxor_signbit_high : forall x, 9223372036854775808 <= x < 2^64 -> Z.lxor x 9223372036854775808 = x - 9223372036854775808.
Proof.
  intros x Hx. pose proof (lxor_signbit (x - 9223372036854775808) ltac:(lia)) as E.
  replace (x - 9223372036854775808 + 9223372036854775808) with x in E by lia.
  rewrite <- E at 1. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.
Lemma neg16_sign : forall size, 0 <= size -> 16 * size < 2^63 ->
  (Z.lxor (Z.land (Z.shiftl (Z.land (0 + - size) 18446744073709551615) 4) 18446744073709551615) 9223372036854775808 <? 0 + 9223372036854775808) = (0 <? size).
Proof.
  intros size H0 H1. rewrite !land64_mod. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  destruct (Z.eq_dec size 0) as [->|NZ].
  - cbn. reflexivity.
  - replace ((0 + - size) mod 2 ^ 64) with (2^64 - size) by (apply Z.mod_unique with (q := -1); lia).
    replace (((2 ^ 64 - size) * 16) mod 2 ^ 64) with (2^64 - 16 * size) by (apply Z.mod_unique with (q := 15); lia).
    rewrite lxor_signbit_high by lia.
    replace (0 <? size) with true by (symmetry; apply Z.ltb_lt; lia). apply Z.ltb_lt. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition push_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (V : Z) (xd xl cap size : Z) (els : list (Z * Z)) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (blk' : option bptr) (jr' : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ v' = (cap', size + 1, blk') /\ (cap' = (if size <? cap then cap else vcap_next cap size)) /\ blk' <> None
    /\ mem_inv usegs m' /\ stk usegs m' lo q /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (vblocks blk' A' cap' ++ LB0) m'
    /\ vrep m' V A' v' (els ++ [(xd, xl)]) jr'
    /\ lx_pres LB0 q [(V, V + 24)] m m'.

Lemma signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia. replace (z <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma shiftr_16_4 : forall c, 0 <= c -> Z.shiftr (16 * c) 4 = c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (c * 2^4) by lia. apply Z.div_mul. lia. Qed.
Lemma shiftr_16_3 : forall c, 0 <= c -> Z.shiftr (16 * c) 3 = 2 * c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (2 * c * 2^3) by lia. apply Z.div_mul. lia. Qed.
Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. rewrite <- unsigned_lit_land. apply unsigned_lit. lia. Qed.
Lemma shiftr_small0 : forall x n, 0 <= x < 2^n -> 0 <= n -> Z.shiftr x n = 0.
Proof. intros x n Hx Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma shiftl4_mul : forall c, Z.shiftl c 4 = 16 * c.
Proof. intros c. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Definition alloc_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) A junk,
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range A (16 * n)
    /\ RHEAP s' ((p, A, 16 * n) :: LB) m'
    /\ rw_cells usegs m' A [CB (Z.to_nat (16 * n)) junk].

Definition grow_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n size lo B SB ALLOC : Z) (m : mem)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) A junk,
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ lx_pres LB q [(SB, SB + 40)] m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range A (16 * n)
    /\ RHEAP s' ((p, A, 16 * n) :: LB) m'
    /\ rw_cells usegs m' A [CB (Z.to_nat (16 * n)) junk]
    /\ rw_cells usegs m' SB [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * n)); C8 (Z_to_bv 64 ALLOC)].

Definition sbdtor_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB' : list block) (lo B : Z) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB' q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' LB' m'.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma allocate_spec : forall (ra gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n lo B : Z) (errv : word),
    RHEAP s LB m -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (32 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 -> 1 <= n -> 16 * n < 2^32 ->
    implM usegs (newnt lops (16 * n)) s
          (alloc_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_ALLOCATE) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros HEAP AUX QB ST CEIL LO ERR MI Hq N1 N2.
    unfold ATP_ALLOCATE, RMALLOC_STACK in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. zstep. rewrite (shiftr_small0 n 60) by lia. zstep. if_false. zstep. zstep.
    rewrite ?shiftl4_mul. try replace (Z.shiftl n 4) with (16 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr LB q a -> outside [(q - 16, q)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in B3'. lia. }
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    ihere. to_implM.
    eapply implM_post_evt.
    { eapply (opnew_body HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia]. }
    cbv beta. intros p s' ms' PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
    replace (ret_pc (Z_to_bv 64 0x3e80c)) with (Z_to_bv 64 0x3e80c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    rewrite ELX in ERR2.
    rename MU into MU1. rename WM into WM1. pose proof (munch_refl [(q - 16, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.

    step. step. step. step. release_frame FR ST2 q. step.
    apply evt_done. unfold alloc_post. do 13 eexists. exists m2, errv2, NEW, jnew.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU1| exact WM1| apply CLI]|].
             eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    split; [exact FA2|]. split; [exact SO2|]. split; [exact BRN|]. split; [exact HEAP2| exact BLKN].
  Qed.

  Lemma grow_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n size lo B SB ALLOC : Z) (errv : word) (j0 j8 j16 j24 j32 : list byte),
    RHEAP s LB m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (64 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q ->
    1 <= n -> 16 * n < 2^32 -> 0 <= size -> size + 1 <= n -> 0 <= ALLOC < 2^64 ->
    rw_cells usegs m SB [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32] -> q <= SB -> SB + 40 <= B ->
    implM usegs (newnt lops (16 * n)) s
          (grow_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n size lo B SB ALLOC m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 n) (Z_to_bv 64 size) (Z_to_bv 64 ALLOC) a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_GROW) fc None m (seg_rom usegs)).
  Proof.
    intros until j32. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI Q0 N1 N2 SZ0 SZN AL SBC QSB SBB.
    unfold ATP_GROW, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q [(SB, SB + 40)] a -> outside [(q - 32, q); (SB, SB + 40)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 32, q); (SB, SB + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. step. step. hstep. hstep. step. br_no. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells usegs m1 SB _ |- _ => rename H into SBC1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB q [(SB, SB + 40)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    clear MU WM.
    ihere. to_implM.
    eapply implM_post_evt.
    { eapply allocate_spec with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia| lia]. }
    cbv beta. intros p s' ms' PO. unfold alloc_post in PO.
    destruct PO as (r5 & r6 & r7 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
    replace (ret_pc (Z_to_bv 64 0x3e628)) with (Z_to_bv 64 0x3e628) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in SBC1; [| intros a Ha; left; cbn in Ha; lia].
    rewrite ELX in ERR2.
    pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
    assert (PRES2 : lx_pres LB q [(SB, SB + 40)] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear AG HP PRES1 HEAP1 AUX1.
    pose proof (munch_refl [(q - 32, q); (SB, SB + 40)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.

    step. zstep. rewrite ?shiftl4_mul. zstep. zstep. zstep.
    b2z_true. b2z_false. cbn [Z.b2z]. hstep. step. br_no.

    zstep. zstep. zstep. zstep. b2z_lit.
    try rewrite (shiftr_small0 (size + 576460752303423488) 60) by lia.
    step. br_no. step. br_no.

    zstep. rewrite ?shiftl4_mul. zstep. zstep.
    b2z_false. cbn [Z.b2z]. hstep. hstep. step. br_no.

    zstep. zstep. try rewrite (shiftr_small0 (n + 576460752303423488) 60) by lia. step. br_no. step. br_no. hstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : rw_cells usegs m3 SB _ |- _ => rename H into SBC3 end.

    step. step. step. step. release_frame FR ST2 q. step.
    apply evt_done. unfold grow_post. do 15 eexists. exists m3, errv2, NEW, jnew.
    split; [atp_st_eq_goal|]. split; [assumption|]. split; [assumption|]. split; [exact ERR2|].
    split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    split; [exact FA2|]. split; [exact SO2|]. split; [exact BRN|].
    split. { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split. { first [exact BLKN| eapply rw_cells_transport; [exact BLKN| exact MU| exact WM| cbn; lia]]. }
    lazymatch type of SBC3 with rw_cells _ _ _ [C8 _; C8 (Z_to_bv 64 ?b); C8 _; C8 (Z_to_bv 64 ?d); C8 _] =>
      replace b with (NEW + 16 * size) in SBC3 by lia; replace d with (NEW + 16 * n) in SBC3 by lia end.
    exact SBC3.
  Qed.

  Lemma sbdtor_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (blk : option bptr) (q lo B SB A cap VC ALLOC : Z) (errv : word),
    RHEAP s (vblocks blk A cap ++ LB) m -> (blk = None -> A = 0) -> (blk <> None -> 0 < A) -> VC = A + 16 * cap -> 0 <= cap -> A + 16 * cap < 2^63 ->
    rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - RFREE_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^63 -> 0 < ALLOC < 2^64 ->
    rw_cells usegs m SB [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 VC); C8 (Z_to_bv 64 ALLOC)] -> 0 <= SB -> SB + 40 < 2^63 ->
    implM usegs (match blk with Some b0 => del lops b0 | None => mret tt end) s
          (sbdtor_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_SBDTOR) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros HEAP BN BS EVC C0 ACH AUX QB ST CEIL LO ERR MI Hq HAL SBC SB0 SBH.
    unfold ATP_SBDTOR, RFREE_STACK in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.

    step. step. step. step. if_true. step.
    destruct blk as [b|].
    - assert (A0 : 0 < A) by (apply BS; discriminate).
      step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

      step. br_no. step. zstep. replace (VC + - A) with (16 * cap) by lia. try replace (VC - A) with (16 * cap) by lia. step. step.
      cbn [vblocks app] in HEAP.
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
          [exact HEAP| left; reflexivity| exact AUX| lia| exact ST| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR| exact MI| lia]. }
      cbv beta. intros [] s' ms' PO. unfold free_postZ in PO.
      destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                      & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      assert (ND : List.NoDup (map blk_id ((b, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6. rewrite ELX in ERR6.
      apply evt_done. unfold sbdtor_post. do 15 eexists. exists m6, errv.
      split; [reflexivity|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact ERR6|]. split; [exact AUX6|].
      split; [exact HP6|]. split; [exact FA6|]. split; [exact SO6| exact HEAP6].
    - rewrite (BN eq_refl) in *. step. if_true. step.
      cbn [vblocks app] in HEAP.
      ihere. to_implM. apply implM_ret. apply evt_done. unfold sbdtor_post. do 15 eexists. exists m, errv.
      split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [rewrite ELX; exact ERR|]. split; [exact AUX|].
      split; [apply rheap_pres_refl|]. split; [reflexivity|]. split; [reflexivity| exact HEAP].
  Qed.

  Definition reloc_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo V SB A VC NEW n size ALLOC : Z) (els : list (Z * Z)) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(q - 32, q); (V, V + 24); (SB, SB + 40); (NEW, NEW + 16 * size)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
      /\ rw_cells usegs m' V [C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NEW + 16 * size + 16)); C8 (Z_to_bv 64 (NEW + 16 * n))]
      /\ rw_cells usegs m' SB [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 VC); C8 (Z_to_bv 64 ALLOC)]
      /\ rw_cells usegs m' NEW [CB (Z.to_nat (16 * size)) (cells_bytes (velts els))].

  Lemma reloc_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo V SB A VC NEW n size ALLOC : Z) (els : list (Z * Z)) (jpre : list byte),
    stk usegs m lo q -> 0 <= lo -> lo <= q - 32 -> q < 2^63 -> mem_inv usegs m ->
    rw_cells usegs m V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 VC)] -> q <= V -> V + 24 < 2^63 ->
    rw_cells usegs m SB [C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NEW + 16 * size)); C8 (Z_to_bv 64 (NEW + 16 * size + 16)); C8 (Z_to_bv 64 (NEW + 16 * n)); C8 (Z_to_bv 64 ALLOC)] ->
    q <= SB -> SB + 40 < 2^63 -> (V + 24 <= SB \/ SB + 40 <= V) ->
    bytes_at usegs m A (cells_bytes (velts els)) -> zlength els = size -> 0 <= A -> A mod 8 = 0 -> A + 16 * size <= lo -> 0 <= VC < 2^64 -> 0 <= ALLOC < 2^64 ->
    rw_cells usegs m NEW [CB (Z.to_nat (16 * size)) jpre] -> 0 < NEW -> NEW + 16 * n <= lo -> 0 <= size -> size + 1 <= n ->
    (A + 16 * size <= NEW \/ NEW + 16 * size <= A) ->
    evt usegs (reloc_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo V SB A VC NEW n size ALLOC els m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 SB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_RELOC) fc None m (seg_rom usegs)).
  Proof.
    intros until jpre. intros ST LO0 LOQ QH MI VC0 QV VH SBC QSB SBH VSB SRC ELS A0 A8 ALO VCR ALR NPRE N0 NLO SZ0 SZN SEP.
    unfold ATP_RELOC.
    assert (LBL : length (cells_bytes (velts els)) = Z.to_nat (16 * size)) by (rewrite velts_bytes_length; unfold zlength in ELS; lia).
    pose proof (munch_refl [(q - 32, q); (V, V + 24); (SB, SB + 40); (NEW, NEW + 16 * size)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide SRC.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. step. step. step. step. step. step.

    zstep. try replace (A + 16 * size + - A) with (16 * size) by lia. zstep. try replace (NEW + 16 * size + - (16 * size)) with NEW by lia.
    zstep. zstep. b2z_true. b2z_false. cbn [Z.b2z]. step. br_no.

    zstep. rewrite (signed_small (16 * size)) by lia. rewrite (shiftr_16_4 size) by lia.
    zstep. zstep. zstep. zstep. try rewrite (shiftr_small0 (size + 576460752303423487) 60) by lia. b2z_lit. step. br_no.

    lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) =>
      assert (AT : forall xa0 xa3 xa4 : word,
        evt usegs Q (MS (mkR ra (Z_to_bv 64 (q + -32)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SB) (Z_to_bv 64 V) xa0 (Z_to_bv 64 A) (Z_to_bv 64 (16 * size)) xa3 xa4 a5 a6 a7
                         (Z_to_bv 64 NEW) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x3e720) fc None mx (seg_rom usegs))) end.
    2:{ zstep. zstep. zstep. zstep. rewrite neg16_sign by lia.
        destruct (Z.eq_dec size 0) as [SZ00|SZP].
        - rewrite SZ00. replace (NEW <? NEW + 16 * 0) with false by (symmetry; apply Z.ltb_ge; lia). replace (0 <? 0) with false by reflexivity. cbn [Z.b2z].
          zstep. zstep. b2z_lit. step. br_no. zstep. rewrite (land7_mod8 A) by lia. step. br_no. zstep.
          rewrite ?Z.shiftl_mul_pow2 by lia. rewrite <- SZ00.
          eapply evt_eq; [| eapply AT]. atp_st_eq.
        - replace (NEW <? NEW + 16 * size) with true by (symmetry; apply Z.ltb_lt; lia). replace (0 <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
          zstep. zstep. b2z_lit. step. br_no. zstep. rewrite (land7_mod8 A) by lia. step. br_no. zstep.
          rewrite ?Z.shiftl_mul_pow2 by lia.
          eapply evt_eq; [| eapply AT]. atp_st_eq. }
    intros xa0 xa3 xa4.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : mem_inv usegs m1 |- _ => rename H into MI1 end.
    unhide SRC.
    assert (SRC1 : bytes_at usegs m1 A (cells_bytes (velts els))).
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact SRC|]. intros a Ha. rewrite LBL in Ha. cbn [outside].
      repeat split; try exact I; clear - Ha ALO LOQ QV QSB SEP N0 SZ0; lia. }
    clear SRC.

    step. step.
    eapply evt_cut.
    { eapply (memcpy_callZ) with (Dst := NEW) (Src := A) (N := 16 * size) (src := cells_bytes (velts els)) (junk := jpre);
        [exact SRC1| exact LBL| eassumption| clear - SEP; lia| lia| lia| lia| exact MI1]. }
    intros ms' PO. unfold memcpy_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2 & -> & MU2 & WM2 & MI2 & NPRE2 & SRC2).
    replace (ret_pc (Z_to_bv 64 0x3e728)) with (Z_to_bv 64 0x3e728) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear SRC1 SRC2 MI1.
    transport_after_call usegs m1 m2 MU2 WM2.
    clear MU2 WM2.

    step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : rw_cells usegs m3 V _ |- _ => rename H into VC3 end.
    lazymatch goal with H : rw_cells usegs m3 SB _ |- _ => rename H into SBC3 end.
    lazymatch goal with H : rw_cells usegs m3 NEW _ |- _ => rename H into NPRE3 end.
    lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
    lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.

    step. step. step. step. step. release_frame FR ST3 q. step.
    apply evt_done. unfold reloc_post. do 15 eexists. exists m3.
    split; [atp_st_eq_goal|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact VC3|]. split; [exact SBC3| exact NPRE3].
  Qed.

  Ltac land7 := match goal with |- context [Z.land ?x 7] => rewrite (land7_mod8 x) by lia end.

  Lemma push1_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (V X A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (xd xl : Z),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (128 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= V -> V + 24 <= B -> q <= X -> X + 16 <= B -> (V + 24 <= X \/ X + 16 <= V) ->
    vrep m V A (cap, size, blk) els jr -> cap < 2^26 -> 0 <= xd < 2^64 -> 0 <= xl < 2^64 ->
    rw_cells usegs m X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] ->
    implM usegs (vpush lops (cap, size, blk)) s
          (push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V xd xl cap size els m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_PUSH1) fc None m (seg_rom usegs)).
  Proof.
    intros until xl. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QV VB QX XB VX VR CAPB XD XL XC.
    unfold ATP_PUSH1, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct VR as (ELS & SZ & SV & BLK).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    remember (A + 16 * size) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    unfold vpush. cbn [bind ret lops Target.ops].
    destruct (Z.ltb_spec size cap) as [LT|GE].
    -
      unfold vblk in BLK. rewrite <- EVE in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia].
      destruct BLK as (BE & BJ & BR & C1). pose proof BR as (A0 & A16 & _ & AC & AS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
      hide BE. hide BJ.
      pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      apply implM_ret. unfold push_post.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8; 8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      step. step. step. step. step. step. step. step.
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.

      step. br_no. zstep. step. br_no. zstep. land7. step. br_no.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
      unhide BJ. apply (rw_cells_agree _ _ _ _ _ AG0) in BJ.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. repeat split; clear - Ha EVE EVC AC CEIL LO SZ LT QV; lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      cbn [app] in HEAP.
      assert (HEAP0 : RHEAP s ((b, A, 16 * cap) :: LB0) m0).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX0 : rauxv_ok m0 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES0 : lx_pres LB0 q [(V, V + 24)] m m0).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      clear MU WM. pose proof (munch_refl [(q - 64, q); (VE, VE + 16); (V, V + 24)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
      remember (Z.to_nat (16 * (cap - size - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * (cap - size))) with (8 + (8 + r))%nat in BJ by lia.
      apply (rw_cells_split_CB usegs _ _ [] _ jr [] [8; 8; r]%nat) in BJ; [| cbn; lia]. cbn [mk_CB_cells app] in BJ.

      step. step. step. zstep. step. step. step.

      zstep. step. step. br_no. step. br_no. zstep. zstep. land7. step. br_no.

      step. step. step. step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
      unhide BE. apply (rw_cells_agree _ _ _ _ _ AG0) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT; unfold zlength in ELS; lia].
      apply (rw_cells_agree _ _ _ _ _ AG1) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT QV; unfold zlength in ELS; lia].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP0) as DJB.
      assert (HEAP9 : RHEAP s ((b, A, 16 * cap) :: LB0) m9).
      { eapply LH_frame; [exact HEAP0| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply (W_ok_block _ (b, A, 16 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX9 : rauxv_ok m9 B).
      { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - EVE AC AS CEIL LO SZ LT A0 QB; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES9 : lx_pres LB0 q [(V, V + 24)] m m9).
      { eapply lx_pres_trans; [exact PRES0|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| split; [clear - HX; lia| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC EVE AC CEIL LO SZ LT; lia| | clear - HC EVE AS A0 SZ LT CAPB; lia].
          intros Hs. apply (DJB a HC). clear - Hs EVE SZ LT. lia. }
      lazymatch goal with H : rw_cells usegs m9 VE _ |- _ => rename H into BJ9 end.
      destruct (Sj_stage1_kit.rw_cells_app usegs m9 VE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 jr)))]) as [SPL _].
      destruct (SPL BJ9) as [SLOT TAIL]. clear SPL BJ9. cbn [cells_size csize Nat.add] in TAIL.
      lazymatch goal with H : rw_cells usegs m9 V _ |- _ => rename H into SV9 end.
      apply evt_done. do 15 eexists. exists m9, errv, A, cap, (Some b), (take r (drop 8 (drop 8 jr))).
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT); reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX9|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HEAP9|]. split; [| exact PRES9].

      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { lazymatch type of SV9 with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?e); _] => replace e with (A + 16 * (size + 1)) in SV9 by lia end. rewrite EVC in SV9. exact SV9. }
      split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [exact BE| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia]. }
      split. { replace (A + 16 * (size + 1)) with (VE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap - (size + 1)))) with r by lia. exact TAIL. }
      split; [exact BR| exact C1].
    -
      assert (SC : size = cap) by lia. rewrite SC in *. clear SC GE.
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling /\ (A = 0 \/ A mod 16 = 0) /\ (A + 16 * cap <= 0x10000 \/ 0x111000 <= A)).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & A16 & _ & AC & AS) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      destruct AR as (A0 & AC & A16 & AS).
      hide BLK.
      assert (OLDIN : forall b, blk = Some b -> In (b, A, 16 * cap) (vblocks blk A cap ++ LB0)) by (intros b ->; left; reflexivity).
      pose proof (munch_refl [(q - 96, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8; 8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      step. step. step. step. step. step. step. step.
      replace VE with VC in * by lia. if_true.

      step. zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_4 cap) by lia.
      zstep. zstep. rewrite (shiftr_small0 (cap + 1) 60) by lia.
      step. if_false.

      zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (shiftr_16_3 cap) by lia.
      lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
        assert (REST : evt usegs QQ (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 X)
                               (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 (vcap_next cap cap)) (Z_to_bv 64 cap) (Z_to_bv 64 VC) (Z_to_bv 64 (cap + 1)) a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x3e540) fc None mx (seg_rom usegs))) end.
      2:{ step. if_cases K; zify_cond K.
          - replace (Z_to_bv 64 (2 * cap)) with (Z_to_bv 64 (vcap_next cap cap)) by (f_equal; unfold vcap_next; lia). exact REST.
          - zstep. replace (Z_to_bv 64 (cap + 1)) with (Z_to_bv 64 (vcap_next cap cap)) at 1 by (f_equal; unfold vcap_next; lia).
            eapply evt_eq; [| exact REST]. atp_st_eq. }
      assert (CAP' : cap + 1 <= vcap_next cap cap <= 2 * cap + 1) by (unfold vcap_next; lia).
      set (cap' := vcap_next cap cap) in *.

      zstep. zstep. step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K CAPB SZ; lia].
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s (vblocks blk A cap ++ LB0) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(V, V + 24)] m m1).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| exact SZ].
      clear MU WM.
      apply (proj1 (Sj_stage1_kit.rw_cells_app usegs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [SBC FRH]. cbn [cells_size csize Nat.add] in FRH.
      replace (q - Z.of_nat 64 + Z.of_nat 40) with (q + -24) in FRH by lia.
      replace (q - Z.of_nat 64) with (q + -64) in SBC by lia.
      ihere. to_implM. change VELT with 16.
      eapply implM_bind.
      { eapply grow_spec with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact B63| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia
          | lia| lia| lia| lia| lia| exact SBC| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold grow_post in PO.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & PRESG & FA2 & SO2 & BRN & HEAP2 & BLKN & SBC2).
      replace (ret_pc (Z_to_bv 64 0x3e560)) with (Z_to_bv 64 0x3e560) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESG) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FRH; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in XC; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; split; [cbn [rin_ivs fst snd]; clear - Ha AC CEIL LO; lia| right; left; exists (b, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]
         | exact ELS| exact SZ].
      assert (PRES2 : lx_pres LB0 q [(V, V + 24)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact PRESG| lia| intros b Hb; apply in_or_app; right; exact Hb|].
        intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| unfold GLOBALS_TOP in *; lia]. }

      assert (SEPN : forall b, blk = Some b -> NEW + 16 * cap' <= A \/ A + 16 * cap <= NEW).
      { intros b Hb. exact (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 (OLDIN b Hb)). }
      clear AG PRES1 HEAP1 AUX1 PRESG.

      remember (NEW + 16 * cap) as NE eqn:ENE. remember (Z.to_nat (16 * (cap' - cap - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * cap')) with (Z.to_nat (16 * cap) + (16 + r))%nat in BLKN by lia.
      apply rw_cells_CB_split2 in BLKN. destruct BLKN as [NPRE NREST]. rewrite Z2Nat.id in NREST by lia. rewrite <- ENE in NREST.
      apply (rw_cells_split_CB usegs _ _ [] _ _ [] [8; 8; r]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      hide BLK.
      pose proof (munch_refl [(q - 96, q); (V, V + 24); (NEW, NE + 16)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. try rewrite <- ENE. step. br_no. zstep. land7. step. br_no. step. step. step. step.

      step. step. br_no. zstep. step. br_no. zstep. step.

      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -64) _ |- _ => rename H into SBC3 end.
      lazymatch goal with H : rw_cells usegs m3 V _ |- _ => rename H into SV3 end.
      lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; specialize (SEPN b eq_refl); cbn [outside]; repeat split; clear - Ha SEPN ENE AC CEIL LO CAP' QV SZ; lia
         | exact ELS| exact SZ].
      assert (SRCB : bytes_at usegs m3 A (cells_bytes (velts els))).
      { unfold vblk in BLK. destruct blk as [b|].
        - destruct BLK as ([[_ HB] _] & _). exact HB.
        - destruct BLK as [AZ C0]. assert (els = []) as -> by (destruct els; [reflexivity| unfold zlength in ELS; cbn in ELS; lia]).
          rewrite AZ. unfold bytes_at. rewrite velts_bytes_length. cbn [length Nat.mul Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      assert (SEP : A + 16 * cap <= NEW \/ NEW + 16 * cap <= A).
      { destruct blk as [b|]; [specialize (SEPN b eq_refl); clear - SEPN CAP' SZ; lia|]. unfold vblk in BLK. destruct BLK as [-> C0]. clear - C0 N0. lia. }
      rewrite EVC in SV3.
      lazymatch goal with H : rw_cells usegs m3 NEW _ |- _ => rename H into NPRE3 end.
      lazymatch type of SBC3 with rw_cells _ _ _ [_; _; C8 (Z_to_bv 64 ?e); _; _] => replace e with (NEW + 16 * cap + 16) in SBC3 by lia end.
      rewrite ENE in SBC3.
      eapply evt_cut.
      { eapply reloc_spec with (lo := lo) (els := els);
          [exact ST3| lia| lia| lia| exact MI3| exact SV3| lia| lia| exact SBC3| lia| lia| lia| exact SRCB| symmetry; exact ELS| lia| clear - A16; lia| lia| lia| lia
          | exact NPRE3| lia| lia| lia| lia| exact SEP]. }
      intros ms' PO. unfold reloc_post in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SV4 & SBC4 & NPRE4).
      replace (ret_pc (Z_to_bv 64 0x3e5a4)) with (Z_to_bv 64 0x3e5a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRCB SV3 SBC3 NPRE3 MI3 ST3. hide BLK.
      transport_after_call usegs m3 m4 MU4 WM4.
      clear MU4 WM4 AG23.
      rewrite <- ?ENE in SV4. rewrite <- ?ENE in NPRE4.

      step. step. step.
      assert (HEAP4 : RHEAP s2' ((pn, NEW, 16 * cap') :: vblocks blk A cap ++ LB0) m4).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        eapply (W_ok_block _ (pn, NEW, 16 * cap')); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX4 : rauxv_ok m4 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
        constructor; [cbn; unfold RAUXV_CELL; clear - ENE NC NS N0 CEIL LO SZ CAP' QB; lia| constructor]. }
      assert (PRES4 : lx_pres LB0 q [(V, V + 24)] m m4).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC ENE NC CEIL LO SZ CAP'; lia| | clear - HC ENE NS N0 SZ CAP' CAPB; lia].
          intros Hs. apply (DJN a); [| clear - Hs ENE SZ CAP'; lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      ihere. to_implM.
      eapply implM_bind.
      { eapply sbdtor_spec with (LB := (pn, NEW, 16 * cap') :: LB0) (blk := blk) (A := A) (cap := cap) (B := B) (lo := lo) (ALLOC := V);
          [ destruct blk as [b|]; [cbn [vblocks app]; apply (RHEAP_pull _ [(pn, NEW, 16 * cap')] (b, A, 16 * cap) LB0); cbn [app]; cbn [vblocks app] in HEAP4; exact HEAP4
                                 | cbn [vblocks app] in HEAP4 |- *; exact HEAP4]
          | intros Hn; unhide BLK; rewrite Hn in BLK; unfold vblk in BLK; destruct BLK as [AZ _]; exact AZ
          | intros Hn; destruct blk as [b|]; [| congruence]; unhide BLK; unfold vblk in BLK; destruct BLK as (_ & _ & (AP & _) & _); exact AP
          | reflexivity| lia| lia| exact AUX4| lia| exact ST4| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI4| lia| lia| exact SBC4| lia| lia]. }
      cbv beta. intros [] st5 ms5 PO. unfold sbdtor_post in PO.
      destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5 & errv5
                      & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
      replace (ret_pc (Z_to_bv 64 0x3e5b0)) with (Z_to_bv 64 0x3e5b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR5.
      pose proof (agree_of_heap_pres _ _ _ _ HP5) as AG5.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SBC4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SV4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in NPRE4; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists (pn, NEW, 16 * cap'); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
      lazymatch goal with H : rw_cells usegs m4 NE _ |- _ => rename H into NREST4 end.
      apply (rw_cells_agree _ _ _ _ _ AG5) in NREST4; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists (pn, NEW, 16 * cap'); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
      assert (PRES5 : lx_pres LB0 q [(V, V + 24)] m m5).
      { eapply lx_pres_trans; [exact PRES4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b0 Hb0; right; exact Hb0]. }
      clear AG5 HP5 MU WM.
      pose proof (munch_refl [(q - 64, q); (V, V + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
      unfold implM. iprefix.

      zstep. step. step. br_no. step. br_no. zstep. zstep. land7. step. br_no.
      destruct (rw_cells_forget _ _ _ _ SBC4) as [jsb SBF]. cbn [cells_size csize Nat.add] in SBF.
      pose proof (rw_cells_join _ _ _ _ _ SBF FRH ltac:(cbn [cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR.
      step. step. step. step. release_frame FR ST5 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      lazymatch goal with H : rw_cells usegs m9 V _ |- _ => rename H into SV9 end.
      destruct (Sj_stage1_kit.rw_cells_app usegs m9 NE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))]) as [SPL _].
      destruct (SPL NREST4) as [SLOT TAIL]. clear SPL NREST4. cbn [cells_size csize Nat.add] in TAIL.
      ihere. to_implM. apply implM_ret. apply evt_done. unfold push_post.
      do 15 eexists. exists m9, errv5, NEW, cap', (Some pn), (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew)))).
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [rewrite Z.ltb_irrefl; reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [assumption|]. split; [exact ERR5|].
      split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [rewrite FA5; exact FA2|]. split; [rewrite SO5; exact SO2|].
      split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split.
      2:{ eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
          intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
          destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { lazymatch type of SV9 with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?e); _] => replace e with (NEW + 16 * (cap + 1)) in SV9 by lia end. exact SV9. }
      unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia].
        eapply rw_cells_recast; [exact NPRE4| apply velts_wf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| rewrite velts_size; cbn [cells_size csize]; unfold zlength in ELS; lia]. }
      split. { replace (NEW + 16 * (cap + 1)) with (NE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap' - (cap + 1)))) with r by lia. exact TAIL. }
      split; [exact BRN| lia].
  Qed.

  Lemma push2_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (V X A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (xd xl : Z),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (128 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= V -> V + 24 <= B -> q <= X -> X + 16 <= B -> (V + 24 <= X \/ X + 16 <= V) ->
    vrep m V A (cap, size, blk) els jr -> cap < 2^26 -> 0 <= xd < 2^64 -> 0 <= xl < 2^64 ->
    rw_cells usegs m X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] ->
    implM usegs (vpush lops (cap, size, blk)) s
          (push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V xd xl cap size els m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_PUSH2) fc None m (seg_rom usegs)).
  Proof.
    intros until xl. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QV VB QX XB VX VR CAPB XD XL XC.
    unfold ATP_PUSH2, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct VR as (ELS & SZ & SV & BLK).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    remember (A + 16 * size) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    unfold vpush. cbn [bind ret lops Target.ops].
    destruct (Z.ltb_spec size cap) as [LT|GE].
    -
      unfold vblk in BLK. rewrite <- EVE in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia].
      destruct BLK as (BE & BJ & BR & C1). pose proof BR as (A0 & A16 & _ & AC & AS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
      hide BE. hide BJ.
      pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      apply implM_ret. unfold push_post.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8; 8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      step. step. step. step. step. step. step. step.
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.

      step. br_no. zstep. step. br_no. zstep. land7. step. br_no.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
      unhide BJ. apply (rw_cells_agree _ _ _ _ _ AG0) in BJ.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. repeat split; clear - Ha EVE EVC AC CEIL LO SZ LT QV; lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      cbn [app] in HEAP.
      assert (HEAP0 : RHEAP s ((b, A, 16 * cap) :: LB0) m0).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX0 : rauxv_ok m0 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES0 : lx_pres LB0 q [(V, V + 24)] m m0).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      clear MU WM. pose proof (munch_refl [(q - 64, q); (VE, VE + 16); (V, V + 24)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
      remember (Z.to_nat (16 * (cap - size - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * (cap - size))) with (8 + (8 + r))%nat in BJ by lia.
      apply (rw_cells_split_CB usegs _ _ [] _ jr [] [8; 8; r]%nat) in BJ; [| cbn; lia]. cbn [mk_CB_cells app] in BJ.

      step. step. step. zstep. step. step. step.

      zstep. step. step. br_no. step. br_no. zstep. zstep. land7. step. br_no.

      step. step. step. step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
      unhide BE. apply (rw_cells_agree _ _ _ _ _ AG0) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT; unfold zlength in ELS; lia].
      apply (rw_cells_agree _ _ _ _ _ AG1) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT QV; unfold zlength in ELS; lia].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP0) as DJB.
      assert (HEAP9 : RHEAP s ((b, A, 16 * cap) :: LB0) m9).
      { eapply LH_frame; [exact HEAP0| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply (W_ok_block _ (b, A, 16 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX9 : rauxv_ok m9 B).
      { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - EVE AC AS CEIL LO SZ LT A0 QB; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES9 : lx_pres LB0 q [(V, V + 24)] m m9).
      { eapply lx_pres_trans; [exact PRES0|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| split; [clear - HX; lia| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC EVE AC CEIL LO SZ LT; lia| | clear - HC EVE AS A0 SZ LT CAPB; lia].
          intros Hs. apply (DJB a HC). clear - Hs EVE SZ LT. lia. }
      lazymatch goal with H : rw_cells usegs m9 VE _ |- _ => rename H into BJ9 end.
      destruct (Sj_stage1_kit.rw_cells_app usegs m9 VE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 jr)))]) as [SPL _].
      destruct (SPL BJ9) as [SLOT TAIL]. clear SPL BJ9. cbn [cells_size csize Nat.add] in TAIL.
      lazymatch goal with H : rw_cells usegs m9 V _ |- _ => rename H into SV9 end.
      apply evt_done. do 15 eexists. exists m9, errv, A, cap, (Some b), (take r (drop 8 (drop 8 jr))).
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT); reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX9|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HEAP9|]. split; [| exact PRES9].

      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { lazymatch type of SV9 with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?e); _] => replace e with (A + 16 * (size + 1)) in SV9 by lia end. rewrite EVC in SV9. exact SV9. }
      split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [exact BE| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia]. }
      split. { replace (A + 16 * (size + 1)) with (VE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap - (size + 1)))) with r by lia. exact TAIL. }
      split; [exact BR| exact C1].
    -
      assert (SC : size = cap) by lia. rewrite SC in *. clear SC GE.
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling /\ (A = 0 \/ A mod 16 = 0) /\ (A + 16 * cap <= 0x10000 \/ 0x111000 <= A)).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & A16 & _ & AC & AS) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      destruct AR as (A0 & AC & A16 & AS).
      hide BLK.
      assert (OLDIN : forall b, blk = Some b -> In (b, A, 16 * cap) (vblocks blk A cap ++ LB0)) by (intros b ->; left; reflexivity).
      pose proof (munch_refl [(q - 96, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8; 8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      step. step. step. step. step. step. step. step.
      replace VE with VC in * by lia. if_true.

      step. zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_4 cap) by lia.
      zstep. zstep. rewrite (shiftr_small0 (cap + 1) 60) by lia.
      step. if_false.

      zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (shiftr_16_3 cap) by lia.
      lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
        assert (REST : evt usegs QQ (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 X)
                               (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 (vcap_next cap cap)) (Z_to_bv 64 cap) (Z_to_bv 64 VC) (Z_to_bv 64 (cap + 1)) a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x3e940) fc None mx (seg_rom usegs))) end.
      2:{ step. if_cases K; zify_cond K.
          - replace (Z_to_bv 64 (2 * cap)) with (Z_to_bv 64 (vcap_next cap cap)) by (f_equal; unfold vcap_next; lia). exact REST.
          - zstep. replace (Z_to_bv 64 (cap + 1)) with (Z_to_bv 64 (vcap_next cap cap)) at 1 by (f_equal; unfold vcap_next; lia).
            eapply evt_eq; [| exact REST]. atp_st_eq. }
      assert (CAP' : cap + 1 <= vcap_next cap cap <= 2 * cap + 1) by (unfold vcap_next; lia).
      set (cap' := vcap_next cap cap) in *.

      zstep. zstep. step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K CAPB SZ; lia].
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s (vblocks blk A cap ++ LB0) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(V, V + 24)] m m1).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| exact SZ].
      clear MU WM.
      apply (proj1 (Sj_stage1_kit.rw_cells_app usegs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [SBC FRH]. cbn [cells_size csize Nat.add] in FRH.
      replace (q - Z.of_nat 64 + Z.of_nat 40) with (q + -24) in FRH by lia.
      replace (q - Z.of_nat 64) with (q + -64) in SBC by lia.
      ihere. to_implM. change VELT with 16.
      eapply implM_bind.
      { eapply grow_spec with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact B63| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia
          | lia| lia| lia| lia| lia| exact SBC| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold grow_post in PO.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & PRESG & FA2 & SO2 & BRN & HEAP2 & BLKN & SBC2).
      replace (ret_pc (Z_to_bv 64 0x3e960)) with (Z_to_bv 64 0x3e960) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESG) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FRH; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in XC; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; split; [cbn [rin_ivs fst snd]; clear - Ha AC CEIL LO; lia| right; left; exists (b, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]
         | exact ELS| exact SZ].
      assert (PRES2 : lx_pres LB0 q [(V, V + 24)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact PRESG| lia| intros b Hb; apply in_or_app; right; exact Hb|].
        intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| unfold GLOBALS_TOP in *; lia]. }

      assert (SEPN : forall b, blk = Some b -> NEW + 16 * cap' <= A \/ A + 16 * cap <= NEW).
      { intros b Hb. exact (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 (OLDIN b Hb)). }
      clear AG PRES1 HEAP1 AUX1 PRESG.

      remember (NEW + 16 * cap) as NE eqn:ENE. remember (Z.to_nat (16 * (cap' - cap - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * cap')) with (Z.to_nat (16 * cap) + (16 + r))%nat in BLKN by lia.
      apply rw_cells_CB_split2 in BLKN. destruct BLKN as [NPRE NREST]. rewrite Z2Nat.id in NREST by lia. rewrite <- ENE in NREST.
      apply (rw_cells_split_CB usegs _ _ [] _ _ [] [8; 8; r]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      hide BLK.
      pose proof (munch_refl [(q - 96, q); (V, V + 24); (NEW, NE + 16)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. try rewrite <- ENE. step. br_no. zstep. land7. step. br_no. step. step. step. step.

      step. step. br_no. zstep. step. br_no. zstep. step.

      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -64) _ |- _ => rename H into SBC3 end.
      lazymatch goal with H : rw_cells usegs m3 V _ |- _ => rename H into SV3 end.
      lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; specialize (SEPN b eq_refl); cbn [outside]; repeat split; clear - Ha SEPN ENE AC CEIL LO CAP' QV SZ; lia
         | exact ELS| exact SZ].
      assert (SRCB : bytes_at usegs m3 A (cells_bytes (velts els))).
      { unfold vblk in BLK. destruct blk as [b|].
        - destruct BLK as ([[_ HB] _] & _). exact HB.
        - destruct BLK as [AZ C0]. assert (els = []) as -> by (destruct els; [reflexivity| unfold zlength in ELS; cbn in ELS; lia]).
          rewrite AZ. unfold bytes_at. rewrite velts_bytes_length. cbn [length Nat.mul Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      assert (SEP : A + 16 * cap <= NEW \/ NEW + 16 * cap <= A).
      { destruct blk as [b|]; [specialize (SEPN b eq_refl); clear - SEPN CAP' SZ; lia|]. unfold vblk in BLK. destruct BLK as [-> C0]. clear - C0 N0. lia. }
      rewrite EVC in SV3.
      lazymatch goal with H : rw_cells usegs m3 NEW _ |- _ => rename H into NPRE3 end.
      lazymatch type of SBC3 with rw_cells _ _ _ [_; _; C8 (Z_to_bv 64 ?e); _; _] => replace e with (NEW + 16 * cap + 16) in SBC3 by lia end.
      rewrite ENE in SBC3.
      eapply evt_cut.
      { eapply reloc_spec with (lo := lo) (els := els);
          [exact ST3| lia| lia| lia| exact MI3| exact SV3| lia| lia| exact SBC3| lia| lia| lia| exact SRCB| symmetry; exact ELS| lia| clear - A16; lia| lia| lia| lia
          | exact NPRE3| lia| lia| lia| lia| exact SEP]. }
      intros ms' PO. unfold reloc_post in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SV4 & SBC4 & NPRE4).
      replace (ret_pc (Z_to_bv 64 0x3e9a4)) with (Z_to_bv 64 0x3e9a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRCB SV3 SBC3 NPRE3 MI3 ST3. hide BLK.
      transport_after_call usegs m3 m4 MU4 WM4.
      clear MU4 WM4 AG23.
      rewrite <- ?ENE in SV4. rewrite <- ?ENE in NPRE4.

      step. step. step.
      assert (HEAP4 : RHEAP s2' ((pn, NEW, 16 * cap') :: vblocks blk A cap ++ LB0) m4).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        eapply (W_ok_block _ (pn, NEW, 16 * cap')); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX4 : rauxv_ok m4 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
        constructor; [cbn; unfold RAUXV_CELL; clear - ENE NC NS N0 CEIL LO SZ CAP' QB; lia| constructor]. }
      assert (PRES4 : lx_pres LB0 q [(V, V + 24)] m m4).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC ENE NC CEIL LO SZ CAP'; lia| | clear - HC ENE NS N0 SZ CAP' CAPB; lia].
          intros Hs. apply (DJN a); [| clear - Hs ENE SZ CAP'; lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      ihere. to_implM.
      eapply implM_bind.
      { eapply sbdtor_spec with (LB := (pn, NEW, 16 * cap') :: LB0) (blk := blk) (A := A) (cap := cap) (B := B) (lo := lo) (ALLOC := V);
          [ destruct blk as [b|]; [cbn [vblocks app]; apply (RHEAP_pull _ [(pn, NEW, 16 * cap')] (b, A, 16 * cap) LB0); cbn [app]; cbn [vblocks app] in HEAP4; exact HEAP4
                                 | cbn [vblocks app] in HEAP4 |- *; exact HEAP4]
          | intros Hn; unhide BLK; rewrite Hn in BLK; unfold vblk in BLK; destruct BLK as [AZ _]; exact AZ
          | intros Hn; destruct blk as [b|]; [| congruence]; unhide BLK; unfold vblk in BLK; destruct BLK as (_ & _ & (AP & _) & _); exact AP
          | reflexivity| lia| lia| exact AUX4| lia| exact ST4| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI4| lia| lia| exact SBC4| lia| lia]. }
      cbv beta. intros [] st5 ms5 PO. unfold sbdtor_post in PO.
      destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5 & errv5
                      & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
      replace (ret_pc (Z_to_bv 64 0x3e9b0)) with (Z_to_bv 64 0x3e9b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR5.
      pose proof (agree_of_heap_pres _ _ _ _ HP5) as AG5.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SBC4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SV4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in NPRE4; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists (pn, NEW, 16 * cap'); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
      lazymatch goal with H : rw_cells usegs m4 NE _ |- _ => rename H into NREST4 end.
      apply (rw_cells_agree _ _ _ _ _ AG5) in NREST4; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists (pn, NEW, 16 * cap'); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
      assert (PRES5 : lx_pres LB0 q [(V, V + 24)] m m5).
      { eapply lx_pres_trans; [exact PRES4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b0 Hb0; right; exact Hb0]. }
      clear AG5 HP5 MU WM.
      pose proof (munch_refl [(q - 64, q); (V, V + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
      unfold implM. iprefix.

      zstep. step. step. br_no. step. br_no. zstep. zstep. land7. step. br_no.
      destruct (rw_cells_forget _ _ _ _ SBC4) as [jsb SBF]. cbn [cells_size csize Nat.add] in SBF.
      pose proof (rw_cells_join _ _ _ _ _ SBF FRH ltac:(cbn [cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR.
      step. step. step. step. release_frame FR ST5 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      lazymatch goal with H : rw_cells usegs m9 V _ |- _ => rename H into SV9 end.
      destruct (Sj_stage1_kit.rw_cells_app usegs m9 NE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))]) as [SPL _].
      destruct (SPL NREST4) as [SLOT TAIL]. clear SPL NREST4. cbn [cells_size csize Nat.add] in TAIL.
      ihere. to_implM. apply implM_ret. apply evt_done. unfold push_post.
      do 15 eexists. exists m9, errv5, NEW, cap', (Some pn), (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew)))).
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [rewrite Z.ltb_irrefl; reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [assumption|]. split; [exact ERR5|].
      split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [rewrite FA5; exact FA2|]. split; [rewrite SO5; exact SO2|].
      split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split.
      2:{ eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
          intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
          destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { lazymatch type of SV9 with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?e); _] => replace e with (NEW + 16 * (cap + 1)) in SV9 by lia end. exact SV9. }
      unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia].
        eapply rw_cells_recast; [exact NPRE4| apply velts_wf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| rewrite velts_size; cbn [cells_size csize]; unfold zlength in ELS; lia]. }
      split. { replace (NEW + 16 * (cap + 1)) with (NE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap' - (cap + 1)))) with r by lia. exact TAIL. }
      split; [exact BRN| lia].
  Qed.

End Proofs.
End WithCeiling0.
