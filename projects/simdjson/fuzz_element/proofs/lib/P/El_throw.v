(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem Cells Frame Step Tac RegsEquiv Arr Ceiling ITree Nodes SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Monad Prog.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout InitMem Rnd Sj_iface Sj_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound El_xs_kitP El_xs_adapt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Lemma kn_has_word_sound : forall E M kn a w v,
  know_ok psegs E M kn -> kn_has_word kn a w v = true ->
  rdn psegs M (adenot E a) w = Some (word_to_le_bytes w (edenot E v)) /\ flat E a (Z.of_nat w) /\ (w <= 8)%nat.
Proof.
  intros E M kn a w v HK H. unfold kn_has_word in H. apply existsb_exists in H as (K & HIn & HK1).
  destruct K as [a' w' v'| | | | | | | | |]; try discriminate.
  unfold kentry_eqb_word in HK1. apply andb_prop in HK1 as [HK1 H3]. apply andb_prop in HK1 as [H1 H2].
  unfold saddr_eqb in H1. destruct a as [b k], a' as [b' k']. cbn [a_base a_off] in H1. apply andb_prop in H1 as [H1a H1b].
  apply expr_eqb_eq in H1a. apply Z.eqb_eq in H1b. apply Nat.eqb_eq in H2. apply expr_eqb_eq in H3. subst b' k' w' v'.
  unfold know_ok in HK. rewrite Forall_forall in HK. specialize (HK _ HIn). cbn [kentry_ok] in HK. destruct HK as (Hw & Hfl & Hrd).
  split; [exact Hrd|]. split; [exact Hfl| exact Hw].
Qed.

Lemma bytes_at_of_rdnA : forall E M (a : saddr) w bs,
  rdn psegs M (adenot E a) w = Some bs -> flat E a (Z.of_nat w) -> bytes_at psegs M (estart E a) bs.
Proof.
  intros E M a w bs H Hfl. pose proof (flat_u E a _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
  apply (bytes_at_of_rdn w); [| lia| lia]. rewrite rdn_common. unfold wa. rewrite <- EU, Z_to_bv_bv_unsigned. exact H.
Qed.

Lemma exit_check_sound : forall s, exit_check s = true ->
  s_pc s = 0x705b8 /\ s_log s = []
  /\ sr_get (s_regs s) (Z_to_bv 5 10) = XBLK /\ sr_get (s_regs s) (Z_to_bv 5 1) = ELit 0x7007c
  /\ sr_get (s_regs s) (Z_to_bv 5 2) = EAlu ALU_ADD XSP (ELit (-16)) /\ sr_get (s_regs s) (Z_to_bv 5 3) = EVar 3 /\ sr_get (s_regs s) (Z_to_bv 5 4) = EVar 4
  /\ sr_get (s_regs s) (Z_to_bv 5 25) = EVar 25 /\ sr_get (s_regs s) (Z_to_bv 5 26) = EVar 26 /\ sr_get (s_regs s) (Z_to_bv 5 27) = EVar 27
  /\ kn_has_word (s_know s) (SA (ELit 0) 0xe1c98) 8 (ELit 0) = true
  /\ kn_has_word (s_know s) (SA (ELit 0) 0xe1ca0) 4 (ELit 0) = true
  /\ (forall i, (i < 8)%nat -> kn_has_word (s_know s) (SA (ELit 0) (0xe35b0 + Z.of_nat i)) 1 (ELit (nth i (uw_bytes true) 0)) = true)
  /\ kn_has_word (s_know s) (SA XSP 8) 8 (ELit 0x3bfb4) = true.
Proof.
  intros s H. unfold exit_check in H.
  apply andb_prop in H as [H H10]. apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H27]. apply andb_prop in H as [H H26]. apply andb_prop in H as [H H25].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H6a]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply expr_eqb_eq in H3. apply expr_eqb_eq in H4. apply expr_eqb_eq in H5. apply expr_eqb_eq in H6a. apply expr_eqb_eq in H6.
  apply expr_eqb_eq in H25. apply expr_eqb_eq in H26. apply expr_eqb_eq in H27.
  destruct (s_log s); [|discriminate].
  repeat split; try assumption; try reflexivity.
  intros i Hi. rewrite forallb_forall in H9. apply H9. apply in_seq. lia.
Qed.

Lemma itab_leaf_sound : itab_sound psegs PTLeaf.
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.
Lemma itab_of_ranges_soundP : forall rs, itab_sound psegs (itab_of_ranges psegs rs PTLeaf).
Proof. intros rs. apply itab_of_ranges_sound. apply itab_leaf_sound. Qed.

Lemma exit_ok_some : forall o, exit_ok o = true -> exists sf, o = Some sf /\ exit_check sf = true.
Proof. intros [sf|] H; [exists sf; split; [reflexivity| exact H]| discriminate H]. Qed.

Lemma impl_post_evt : forall {RT : Type} (t : itree node RT) (Q Q' : RT -> machine_state -> Prop) ms,
  impl psegs (at_node psegs) t Q ms -> (forall r ms', Q r ms' -> evt psegs (Q' r) ms') -> impl psegs (at_node psegs) t Q' ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  - destruct H as [z H]. exists z. eapply IHc; eauto.
Qed.
Lemma implM_post_evt : forall {A} (c : M PState A) s Q Q' ms,
  implM psegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt psegs (Q' a s') ms') -> implM psegs c s Q' ms.
Proof.
  intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact H'|]. apply HQ. exact H'.
Qed.

Lemma free_wrap_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
  a0 = wz A -> (A + 144 <= 0x10000 \/ 0x105000 <= A) -> 0 < A -> A + 144 <= 2^47 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists a1' a2' a4',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RFREE_SYM) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x705b8) fc None m (seg_rom psegs)).
Proof.
  intros until A. intros -> HA HA0 HA47 MI. unfold wz, RFREE_SYM.
  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K.
  - zstep. apply evt_done. do 3 eexists. reflexivity.
  - zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia]. zstep. apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma endcatch_epilogue_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (u : Z) (v0 v1 : word),
  sp = wz u -> 16384 <= u -> u + 32 <= 2^62 ->
  rw_cells psegs m (u + 8) [C8 v1; C8 v0; C8 (wz 0x3bfb4)] -> mem_inv psegs m ->
  evt psegs (fun ms' => exists s0' s1',
      ms' = MS (mkR (wz 0x3bfb4) (wz (u + 32)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3bfb4) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x7007c) fc None m (seg_rom psegs)).
Proof.
  intros until v1. intros -> HU1 HU2 RA MI. unfold wz in *.
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. exists v0, v1. reflexivity.
Qed.

Lemma rw_cb8_c8 : forall m A bs, rw_cells psegs m A [CB 8 bs] -> rw_cells psegs m A [C8 (le_bytes_to_word bs)].
Proof.
  intros m A bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hlen _].
  split; [split; [cbn; tauto|]| exact Hw]. cbn [cells_bytes cbytes] in *. rewrite le8_le_bytes_to_word by exact Hlen. exact Hb.
Qed.

Lemma frame3_cells : forall m u (w : word), stk psegs m (u + 8) (u + 32) -> bytes_at psegs m (u + 24) (le8 w) ->
  exists v1 v0, rw_cells psegs m (u + 8) [C8 v1; C8 v0; C8 w].
Proof.
  intros m u w STK BA.
  destruct (stk_carve psegs m (u + 8) (u + 32) 8 STK ltac:(lia)) as [STK2 _].
  replace (u + 32 - Z.of_nat 8) with (u + 24) in STK2 by lia.
  destruct (stk_carve psegs m (u + 8) (u + 24) 8 STK2 ltac:(lia)) as [STK1 [j0 H0]].
  replace (u + 24 - Z.of_nat 8) with (u + 16) in STK1, H0 by lia.
  destruct (stk_carve psegs m (u + 8) (u + 16) 8 STK1 ltac:(lia)) as [_ [j1 H1]].
  replace (u + 16 - Z.of_nat 8) with (u + 8) in H1 by lia.
  apply rw_cb8_c8 in H0. apply rw_cb8_c8 in H1.
  exists (le_bytes_to_word j1), (le_bytes_to_word j0).
  pose proof (proj2 (proj1 H1)) as B1. pose proof (proj2 (proj1 H0)) as B0. cbn [cells_bytes cbytes] in B1, B0. rewrite app_nil_r in B1, B0.
  split; [split; [cbn; tauto|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply (proj2 (bytes_at_app psegs m _ _ _)). split; [exact B1|]. rewrite length_le8. replace (u + 8 + Z.of_nat 8) with (u + 16) by lia.
    apply (proj2 (bytes_at_app psegs m _ _ _)). split; [exact B0|]. rewrite length_le8. replace (u + 16 + Z.of_nat 8) with (u + 24) by lia. exact BA.
  - cbn [cells_size csize Nat.add]. eapply stk_wr_at; [exact STK| lia| lia| lia].
Qed.

Lemma wr_at_wmono : forall (m m' : mem) a n, wr_at psegs m a n -> wmono psegs m m' -> wr_at psegs m' a n.
Proof. intros m m' a n (H1 & H2 & H) W. split; [lia|]. split; [lia|]. intros i Hi. apply W. apply H. exact Hi. Qed.

Lemma bytes_at_pointwise : forall (m : mem) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> bytes_at psegs m (a + Z.of_nat i) [nth i bs (Z_to_bv 8 0)]) -> bytes_at psegs m a bs.
Proof.
  intros m a bs Ha Hb H. split; [lia|]. split; [lia|]. intros i Hi. destruct (H i Hi) as (_ & _ & X).
  specialize (X 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in X. rewrite Z.add_0_r in X. rewrite X. symmetry. apply nth_error_nth'. exact Hi.
Qed.

Lemma in_lb_remove : forall p LB (b : MallocBlocks.block), In b (lb_remove p LB) -> In b LB /\ blk_id b <> p.
Proof.
  intros p LB b H. unfold lb_remove in H. induction LB as [|c LB IH]; [destruct H|].
  rewrite list_basics.list.filter_cons in H. destruct (base.decide _) as [Y|N].
  - destruct H as [<-|H].
    + split; [left; reflexivity|]. intros EQ. rewrite EQ, bptr_eqb_refl in Y. exact Y.
    + destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
  - destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
Qed.

Lemma kn_lit_bytes : forall E M kn a w z,
  know_ok psegs E M kn -> kn_has_word kn (SA (ELit 0) a) w (ELit z) = true ->
  bytes_at psegs M a (word_to_le_bytes w (Z_to_bv 64 z)).
Proof.
  intros E M kn a w z HK H. destruct (kn_has_word_sound E M kn _ _ _ HK H) as (Rd & Fl & _).
  pose proof (bytes_at_of_rdnA E M _ _ _ Rd Fl) as X. rewrite estart_lit in X. exact X.
Qed.

Lemma reg_get_mkR_sel : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  reg_get R (Z_to_bv 5 1) = x1 /\ reg_get R (Z_to_bv 5 2) = x2 /\ reg_get R (Z_to_bv 5 4) = x4 /\ reg_get R (Z_to_bv 5 10) = x10 /\ reg_get R (Z_to_bv 5 3) = x3
  /\ reg_get R (Z_to_bv 5 25) = x25 /\ reg_get R (Z_to_bv 5 26) = x26 /\ reg_get R (Z_to_bv 5 27) = x27.
Proof. intros. vm_compute. repeat split; reflexivity. Qed.

Definition xs_post {CE : Ceiling} {RN : RunRnd} (gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list MallocBlocks.block) (p : bptr) (usp lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F' m',
    ms' = MS (mkR ra (wz (usp + 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (wz 0x3bfb4) fc None m' (seg_rom psegs)
    /\ (forall r : reg, reg_get F' r = reg_get F r)
    /\ mem_inv psegs m' /\ stk psegs m' lo (usp + 16)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ RHEAP s' (lb_remove p LB) m' /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rw_cells psegs m' 0xe1c98 [C8 (wz 0); C4 (wz 0)]
    /\ rw_cells psegs m' 0xe35b0 (uw_cells true)
    /\ (forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove p LB) (usp + 16) a ->
          ~ (0xe1c98 <= a < 0xe1c98 + 12) -> ~ (0xe35b0 <= a < 0xe35b0 + 8) ->
          m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)).

Section ThrowA.
  Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variables (IT : itab) (pc0 raval : Z).
  Hypothesis ITS : itab_sound psegs IT.
  Hypothesis RUN : forall uw : bool, exit_ok (xautoP IT xs_W xs_RW 0x705b8 XS_FUEL XS_K (xs_ss0 pc0 raval uw)) = true.

  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : PState) (LB : list MallocBlocks.block) (p : bptr) (blk lo B : Z) (canary errv w0 : word) (uw : bool).
  Let usp := bv_unsigned sp.
  Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (blk + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  Hypothesis HP : RHEAP s LB m.
  Hypothesis INB : In (p, blk, 144) LB.
  Hypothesis HB : rw_cells psegs m blk [CB 144 (MallocRep.zeros 144)].
  Hypothesis RB : rblock_range blk 144.
  Hypothesis ST : stk psegs m lo (usp + 16).
  Hypothesis LO : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= usp - 16384.
  Hypothesis SPB : usp + 16 <= B.
  Hypothesis B62 : B < 2^62.
  Hypothesis AL : usp mod 16 = 0.
  Hypothesis AUX : rauxv_ok m B.
  Hypothesis MI : mem_inv psegs m.
  Hypothesis RELRO : pj_relro m.
  Hypothesis SSP : ssp_cells m canary.
  Hypothesis XD : rw_cells psegs m EL_XDATA [C8 (wz EL_XDATA_V0); C8 (wz EL_XDATA_V1)].
  Hypothesis HD : rw_cells psegs m EL_HDLR [C8 (wz EL_HDLR_V0); C8 (wz EL_HDLR_V1)].
  Hypothesis EHG : rw_cells psegs m 0xe1c98 [C8 (wz 0); C4 (wz 0)].
  Hypothesis UNW : rw_cells psegs m 0xe35b0 (uw_cells uw).
  Hypothesis W0S : rw_cells psegs m usp [C8 w0].
  Hypothesis RAS : rw_cells psegs m (usp + 8) [C8 (wz raval)].
  Hypothesis RAV : 0 <= raval < 2^64.
  Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
  Hypothesis TP : tp = wz RATP.

  Theorem xs_throw_A :
    implM psegs (raw_free p) s (xs_post gp tp s9 s10 s11 F fc s LB p usp lo B errv m)
          (MS R F (wz pc0) fc None m (seg_rom psegs)).
  Proof.

    destruct (xs_entry ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m blk lo B pc0 raval canary w0 uw
                HB RB ST LO LOW SPB B62 AL AUX MI RELRO SSP XD HD EHG UNW W0S RAS RAV) as (E & HCIX & EREG & E40 & EFP).

    destruct (exit_ok_some _ (RUN uw)) as (sf & HX & RUNu).
    destruct (xauto_soundP IT ITS fc xs_W xs_RW 0x705b8 XS_FUEL XS_K (xs_ss0 pc0 raval uw) sf E m m _ eq_refl eq_refl HX HCIX)
      as (E' & base' & ms' & HAG & _ & HMS & [Hnx HC]).
    destruct (exit_check_sound sf RUNu) as (Hpc & Hlog & H10 & H1 & H2 & H3 & H4 & H25 & H26 & H27 & KE1 & KE2 & KU & KR).
    destruct (HC E' (eagree_refl _ _)) as (R' & F' & Hms' & HR' & HLF' & HK' & HFR' & HFP' & HMI' & HWM' & HBASE & _ & HRD').
    rewrite Hpc, Hlog in Hms'. cbn [mem_denot] in Hms'. rewrite Hms' in HMI', HWM', HRD'. unfold MS in HMI', HWM', HRD'. cbn [ms_mem] in HMI', HWM', HRD'.
    destruct HAG as [HAG _]. cbn [s_next xs_ss0] in HAG.
    pose proof alloc_ceiling_range as CR. destruct RB as (RB1 & RB2 & RB3 & RB4 & RB5).
    destruct (reg_get_mkR_sel ra sp gp tp t0 t1 t2 s0 s1 (wz (blk + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as (G1 & G2 & G4 & G10 & G3 & G25 & G26 & G27).
    assert (E2 : ev E' 2 = sp). { rewrite <- (HAG 2%nat) by lia. etransitivity; [exact (EREG 2 ltac:(lia))| exact G2]. }
    assert (E4 : ev E' 4 = tp). { rewrite <- (HAG 4%nat) by lia. etransitivity; [exact (EREG 4 ltac:(lia))| exact G4]. }
    assert (E3 : ev E' 3 = gp). { rewrite <- (HAG 3%nat) by lia. etransitivity; [exact (EREG 3 ltac:(lia))| exact G3]. }
    assert (E25 : ev E' 25 = s9). { rewrite <- (HAG 25%nat) by lia. etransitivity; [exact (EREG 25 ltac:(lia))| exact G25]. }
    assert (E26 : ev E' 26 = s10). { rewrite <- (HAG 26%nat) by lia. etransitivity; [exact (EREG 26 ltac:(lia))| exact G26]. }
    assert (E27 : ev E' 27 = s11). { rewrite <- (HAG 27%nat) by lia. etransitivity; [exact (EREG 27 ltac:(lia))| exact G27]. }
    assert (E40' : ev E' 40 = wz blk). { rewrite <- (HAG 40%nat) by lia. exact E40. }

    destruct HFR' as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 &
                      y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & ER'). subst R'.
    destruct (reg_get_mkR_sel y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) as (Y1 & Y2 & Y4 & Y10 & Y3 & Y25 & Y26 & Y27).
    assert (V10 : y10 = wz blk). { rewrite <- Y10. change (reg_get _ (Z_to_bv 5 10)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 10)).
      rewrite (HR' (Z_to_bv 5 10)), H10. cbn [edenot XBLK]. exact E40'. }
    assert (V1 : y1 = wz 0x7007c). { rewrite <- Y1. change (reg_get _ (Z_to_bv 5 1)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 1)).
      rewrite (HR' (Z_to_bv 5 1)), H1. reflexivity. }
    assert (V4 : y4 = tp). { rewrite <- Y4. change (reg_get _ (Z_to_bv 5 4)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 4)).
      rewrite (HR' (Z_to_bv 5 4)), H4. cbn [edenot]. exact E4. }
    assert (V25 : y25 = s9). { rewrite <- Y25. change (reg_get _ (Z_to_bv 5 25)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 25)).
      rewrite (HR' (Z_to_bv 5 25)), H25. cbn [edenot]. exact E25. }
    assert (V26 : y26 = s10). { rewrite <- Y26. change (reg_get _ (Z_to_bv 5 26)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 26)).
      rewrite (HR' (Z_to_bv 5 26)), H26. cbn [edenot]. exact E26. }
    assert (V27 : y27 = s11). { rewrite <- Y27. change (reg_get _ (Z_to_bv 5 27)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 27)).
      rewrite (HR' (Z_to_bv 5 27)), H27. cbn [edenot]. exact E27. }
    assert (V3 : y3 = gp). { rewrite <- Y3. change (reg_get _ (Z_to_bv 5 3)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 3)).
      rewrite (HR' (Z_to_bv 5 3)), H3. cbn [edenot]. exact E3. }
    assert (V2 : y2 = wz (usp - 16)). { rewrite <- Y2. change (reg_get _ (Z_to_bv 5 2)) with (getr (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 2)).
      rewrite (HR' (Z_to_bv 5 2)), H2. cbn [edenot XSP]. rewrite E2, PropExec.alu_add. unfold PropExec.v_add, wz. apply bv_eq.
      rewrite !Z_to_bv_unsigned. unfold bv_wrap. subst usp. rewrite Zplus_mod_idemp_r. f_equal; lia. }
    subst y1 y2 y3 y4 y10 y25 y26 y27.

    assert (WIN : forall x : word, ~ Wd E' xs_W x <->
              ~ (usp - 16384 <= bv_unsigned x < usp + 16) /\ ~ (blk <= bv_unsigned x < blk + 144)
              /\ ~ (0xe1c98 <= bv_unsigned x < 0xe1c98 + 12) /\ ~ (0xe35b0 <= bv_unsigned x < 0xe35b0 + 8)).
    { intros x. unfold Wd, xs_W. split.
      - intros NW. repeat split; intros HH; apply NW.
        + exists XSP, (-16384), 16. split; [cbn; tauto|]. cbn [edenot XSP]. rewrite E2. subst usp. lia.
        + exists XBLK, 0, 144. split; [cbn; tauto|]. cbn [edenot XBLK]. rewrite E40'. unfold wz. rewrite unsigned_lit by lia. lia.
        + exists (ELit 0), 0xe1c98, (0xe1c98 + 12). split; [cbn; tauto|]. cbn [edenot]. rewrite unsigned_lit by lia. lia.
        + exists (ELit 0), 0xe35b0, (0xe35b0 + 8). split; [cbn; tauto|]. cbn [edenot]. rewrite unsigned_lit by lia. lia.
      - intros (N1 & N2 & N3 & N4) (wb & wlo & whi & HIn & HH). cbn in HIn.
        destruct HIn as [HIn|[HIn|[HIn|[HIn|[]]]]]; injection HIn as <- <- <-; cbn [edenot XSP XBLK] in HH;
          rewrite ?E2, ?E40' in HH; unfold wz in HH; rewrite ?unsigned_lit in HH by lia; subst usp; lia. }
    assert (MU : munch [(usp - 16384, usp + 16); (blk, blk + 144); (0xe1c98, 0xe1c98 + 12); (0xe35b0, 0xe35b0 + 8)] m base').
    { intros x Hout. cbn [outside] in Hout. apply HBASE. apply (proj2 (WIN x)). tauto. }
    assert (HP' : RHEAP s LB base').
    { eapply RHEAP_frame_proof; [exact HP| exact MU| exact HWM'|].
      repeat apply Forall_cons; [| | | | apply Forall_nil]; unfold rclient_write_ok; cbn [fst snd].
      - left. lia.
      - right. right. exists (p, blk, 144). split; [exact INB|]. cbn. lia.
      - right. left. unfold RMallocRep.RLIBC, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, RMallocRep.RCTX. lia.
      - right. left. unfold RMallocRep.RLIBC, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, RMallocRep.RCTX. lia. }
    assert (AUX' : rauxv_ok base' B).
    { destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AB & ARND & AH).
      eapply rauxv_ok_frame; [exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd; eauto| exact MU| exact HWM'|].
      repeat apply Forall_cons; [| | | | apply Forall_nil]; cbn [fst snd]; unfold RMallocRep.RAUXV_CELL; lia. }
    assert (STF : stk psegs base' lo (usp + 16)).
    { eapply stk_transport; [exact ST| exact MU| exact HWM'|].
      intros x Hx. destruct (Z.lt_ge_cases x (usp - 16384)) as [Lx|Lx].
      - left. cbn [outside]. repeat split; try exact I; lia.
      - right. assert (WD : Wd E' xs_RW (wa x)).
        { exists XSP, (-16384), 16. split; [left; reflexivity|]. cbn [edenot XSP]. rewrite E2. unfold wa. rewrite unsigned_lit by lia. subst usp. lia. }
        destruct (HRD' (wa x) WD) as [D1 _]. destruct (base' (wa x)) as [b|]; [exists b; reflexivity| exfalso; apply D1; reflexivity]. }
    destruct (stk_split psegs base' lo (usp - 16) (usp + 16) STF ltac:(lia)) as [ST' _].
    assert (ERR' : rw_cells psegs base' (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU| exact HWM'|]. subst tp. unfold RMallocRep.RATP. rewrite unsigned_lit by lia.
      cbn [cells_size csize Nat.add disjoint_from]. repeat split; try exact I; lia. }

    assert (B_RA : bytes_at psegs base' (usp + 8) (le8 (wz 0x3bfb4))).
    { destruct (kn_has_word_sound E' base' (s_know sf) _ _ _ HK' KR) as (Rd & Fl & _).
      pose proof (bytes_at_of_rdnA E' base' _ _ _ Rd Fl) as X. unfold estart in X. cbn [a_base a_off edenot XSP] in X. rewrite E2 in X. exact X. }
    assert (EHG' : rw_cells psegs base' 0xe1c98 [C8 (wz 0); C4 (wz 0)]).
    { split; [split; [cbn; tauto|]|].
      - cbn [cells_bytes cbytes]. apply (proj2 (bytes_at_app psegs base' _ _ _)). split; [exact (kn_lit_bytes E' base' (s_know sf) _ _ _ HK' KE1)|].
        rewrite length_le8. apply (proj2 (bytes_at_app psegs base' _ _ _)). split; [exact (kn_lit_bytes E' base' (s_know sf) _ _ _ HK' KE2)|].
        apply bytes_at_nil. cbn. lia.
      - eapply wr_at_wmono; [exact (proj2 EHG)| exact HWM']. }
    assert (UNW' : rw_cells psegs base' 0xe35b0 (uw_cells true)).
    { split; [split; [cbn; tauto|]|].
      - unfold uw_cells. cbn [cells_bytes cbytes app]. apply bytes_at_pointwise; [lia| cbn; lia|].
        intros i Hi. cbn [length] in Hi.
        assert (G : forall k, (k < 8)%nat -> bytes_at psegs base' (0xe35b0 + Z.of_nat k) (word_to_le_bytes 1 (Z_to_bv 64 (nth k (uw_bytes true) 0)))).
        { intros k Hk. exact (kn_lit_bytes E' base' (s_know sf) _ _ _ HK' (KU k Hk)). }
        (destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [exact (G 0%nat ltac:(lia))| exact (G 1%nat ltac:(lia))| exact (G 2%nat ltac:(lia))| exact (G 3%nat ltac:(lia))|
          exact (G 4%nat ltac:(lia))| exact (G 5%nat ltac:(lia))| exact (G 6%nat ltac:(lia))| exact (G 7%nat ltac:(lia))| lia]).
      - eapply wr_at_wmono; [| exact HWM']. pose proof (proj2 UNW) as W8.
        replace (Z.of_nat (cells_size (uw_cells uw))) with 8 in W8 by (destruct uw; reflexivity). exact W8. }

    eapply implM_evt with (P := eq ms'); [exists ms'; split; [exact HMS| reflexivity]|]. intros ms1 <-. rewrite Hms'.
    eapply implM_evt; [apply (free_wrap_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc base' blk eq_refl RB5 RB1 ltac:(lia) HMI')|].
    intros ms2 (a1' & a2' & a4' & ->).

    eapply implM_post_evt.
    { unfold wz. eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc base' s LB p blk 144 lo B errv HP' INB AUX');
        rewrite ?unsigned_lit by lia; [lia| exact ST'| exact LO| unfold RFREE_STACK; lia| exact ERR'| exact HMI'| exact TP| reflexivity]. }

    intros [] s' ms3 POST. unfold rfree_post in POST.
    destruct POST as (z0 & z1 & z2 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & z3 & z4 & z5 & z6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & RP & FA3 & SO3 & HP3).
    rewrite unsigned_lit in ST3, RP by lia.
    assert (STH : stk psegs m3 (usp - 16) (usp + 16)).
    { eapply rheap_pres_stk; [exact RP| | lia]. exact (proj2 (stk_split psegs base' lo (usp - 16) (usp + 16) STF ltac:(lia))). }
    assert (B_RA3 : bytes_at psegs m3 (usp - 16 + 24) (le8 (wz 0x3bfb4))).
    { replace (usp - 16 + 24) with (usp + 8) by lia. eapply rheap_pres_bytes_at; [exact RP| exact B_RA|]. left. lia. }
    destruct (frame3_cells m3 (usp - 16) (wz 0x3bfb4)) as (v1 & v0 & FR3).
    { replace (usp - 16 + 8) with (usp - 8) by lia. replace (usp - 16 + 32) with (usp + 16) by lia.
      exact (proj2 (stk_split psegs m3 (usp - 16) (usp - 8) (usp + 16) STH ltac:(lia))). }
    { exact B_RA3. }
    rewrite ret_pc_even by lia.
    eapply evt_cut; [apply (endcatch_epilogue_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m3 (usp - 16) v0 v1 eq_refl ltac:(lia) ltac:(lia) FR3 MI3)|].
    intros ms4 (s0' & s1' & ->). apply evt_done.
    replace (usp - 16 + 32) with (usp + 16) by lia.
    unfold xs_post. do 25 eexists. exists F', m3.
    split; [reflexivity|].
    split. {   (intros r; reg_cases r;
      lazymatch goal with |- reg_get F' (Z_to_bv 5 ?k) = _ =>
        etransitivity; [symmetry; exact (HFP' (Z.to_nat k) ltac:(lia))|];
        etransitivity; [| exact (EFP (Z.to_nat k) ltac:(lia))]; symmetry; apply HAG; unfold FPB; lia end). }
    split; [exact MI3|].
    split. { eapply stk_merge; [exact ST3| exact STH| lia]. }
    split; [exact ERR3|]. split; [exact AUX3|]. split; [exact HP3|]. split; [exact FA3|]. split; [exact SO3|].
    split. { eapply rheap_pres_rw_cells; [exact RP| exact EHG'|]. right. left. cbn [cells_size csize Nat.add].
             unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    split. { eapply rheap_pres_rw_cells; [exact RP| exact UNW'|]. right. left. unfold uw_cells. cbn [cells_size csize Nat.add].
             unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }

    intros a Ha HCL N1 N2.
    assert (HCL' : rclient_addr (lb_remove p LB) (usp - 16) a).
    { destruct HCL as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]. }
    destruct (RP a Ha HCL') as [EQ3 WV3].
    assert (NW : ~ Wd E' xs_W (wa a)).
    { apply (proj2 (WIN (wa a))). unfold wa. rewrite unsigned_lit by lia.
      destruct HCL as [H|[H|(b & Hb & Hr)]].
      - clear - H Ha LOW LO CR RB4. repeat split; lia.
      - unfold ralloc_static in H. clear - H Ha LOW LO CR RB5 N1 N2. repeat split; lia.
      - apply in_lb_remove in Hb as [Hb NE].
        pose proof (RHEAP_block_range_proof _ _ _ _ HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5).
        pose proof (RHEAP_blocks_disjoint_proof _ _ _ b (p, blk, 144) HP Hb INB NE) as DJ.
        cbn [blk_addr blk_size blk_id fst snd] in DJ, Hr, Q4, Q5. clear - Hr Ha LOW LO CR Q4 Q5 DJ. repeat split; lia. }
    rewrite EQ3, (HBASE (wa a) NW). split; [reflexivity|]. intros W0. apply WV3. apply HWM'. exact W0.
  Qed.
End ThrowA.
