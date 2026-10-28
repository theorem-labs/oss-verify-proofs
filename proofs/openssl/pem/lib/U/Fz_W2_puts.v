(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_bits Fz_W1_bioflags Fz_W1_growc Fz_W1_grows Fz_W1_write Fz_W1_writec Fz_W1_puts Fz_W1_misc Fz_W1_read
     Fz_W3_iface Fz_W2_rep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W1_write_zero_proof :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB fl IN : Z),
    a0 = wz BI -> a1 = wz IN -> a2 = wz 0 -> 0 < BI ->
    rw_cells usegs m (BI + 48) [C4 (wz fl)] -> fl_ok fl -> ro_cells usegs m (BI + 64) [C8 (wz BB)] -> BI mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 80 -> BI + 72 <= lo -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fl' : Z) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (wz fl')])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x1832b0) fc None m (seg_rom usegs)).
Proof.
  intros until IN. intros -> -> -> HBI FLC FLOK PTRC BI8 ST LO0 LO SBI MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (fl_ok_byte1 fl FLOK) as RDO. pose proof FLOK as [FLR FLB].
  apply (proj1 (c4_bytes_view usegs m (BI + 48) fl FLR)) in FLC.
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. ths. if_cases K0; zify_cond K0. { exfalso. apply K0. exact RDO. }
  do 5 ths. ths.
  lazymatch goal with H : rw_cells usegs ?mm (BI + 48) _ |- _ => apply (proj2 (c4_bytes_view usegs mm (BI + 48) fl FLR)) in H end.
  tcallr W1_bio_clear15_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. th_if_lit. ths. ths. do 7 ths. ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. finish. 2: eassumption. eapply fl_ok_land; [exact FLOK| clear; lia].
Qed.

Lemma grow_n_lt : forall len', 0 < len' < 1610612733 -> len' < grow_n len' < 2 ^ 31 - 1.
Proof.
  intros len' H. pose proof (grow_n_bounds len' H) as [G1 G2]. split; [exact G1|].
  assert (M4 : grow_n len' mod 4 = 0) by (unfold grow_n; apply Z_mod_mult). lia.
Qed.

Ltac trw H MUc WMc := eapply rw_cells_transport in H; [| exact MUc| exact WMc| cbn [length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].

Lemma cgrow_same : forall (L : @clist bptr) x, 0 <= x -> cgrow L L (wA (grow_n x)) (wB (grow_n x)) (wBig (grow_n x)).
Proof.
  intros L x Hx. assert (Hg : 0 <= grow_n x) by (unfold grow_n; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  unfold cgrow, wA, wB, wBig. destruct (grow_n x <=? TIER_A_MAX); destruct (TIER_A_MAX <? grow_n x); lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma cframe_weakT : forall (T T' : bptr -> Prop) W SP s LBall L m s' LBall' L' m',
  cframe T W SP s LBall L m s' LBall' L' m' -> (forall q, T q -> T' q) -> cframe T' W SP s LBall L m s' LBall' L' m'.
Proof.
  intros T T' W SP s LBall L m s' LBall' L' m' (CFR & [K1 K2] & SO & FA) HT. split; [| split; [split| split; [exact SO| exact FA]]].
  - eapply agree_on_mono; [exact CFR|]. intros a [X|[(b & IN & NT & Rb)|X]]; [left; exact X| right; left| right; right; exact X].
    exists b. split; [exact IN|]. split; [intros Tb; exact (NT (HT _ Tb))| exact Rb].
  - intros b IN NT. apply K1; [exact IN| intros Tb; exact (NT (HT _ Tb))].
  - intros q nm IN NT. apply K2; [exact IN| intros Tb; exact (NT (HT _ Tb))].
Qed.
Lemma src_loc_weakT : forall LBall (T T' : bptr -> Prop) SP IN n, src_loc LBall T SP IN n -> (forall q, T' q -> T q) -> src_loc LBall T' SP IN n.
Proof.
  intros LBall T T' SP IN n [X|(ps & AS & ns & INS & NT & R1 & R2)] HT; [left; exact X| right]. exists ps, AS, ns. split; [exact INS|]. split; [intros X; exact (NT (HT _ X))| split; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MW_STACK : Z := WRITE_STACK.

Lemma mem_write_spec : W1_grow_null_stmt 0 -> W1_grow_null_stmt 1 -> W1_grow_re_stmt 0 -> W1_grow_re_stmt 1 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI meth len max IN n lo B : Z)
         (src : list byte),
    (2 <= f)%nat -> croom L (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) ->
    cstate st LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - MW_STACK -> mbio_rep m LBall L K BI meth len max 0 -> len + n < 2 ^ 30 -> 0 <= n < 2 ^ 31 ->
    0 < IN -> bytes_at usegs m IN src -> length src = Z.to_nat n -> src_loc LBall (mbio_T K) (bv_unsigned sp) IN n ->
    a0 = wz BI -> a1 = wz IN -> a2 = wz n ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_MEM_WRITE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB0 L f m lo B (mbio_T K) [] 2
             (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) (bio_puts_res K BI meth len max n LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros GN0 GN1 GR0 GR1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB0 L f K BI meth len max IN n lo Bd src
         Hf ROOM CST SLO MB HLIM HN HIN SRC LSRC SLOC Ea0 Ea1 Ea2.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold MW_STACK, WRITE_STACK, GROW_STACK, FZ_MEM_WRITE, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  assert (STK160 : 160 <= 64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)).
  { unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK. clear; lia. }
  destruct MB as [BM MBX]. pose proof MBX as (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DOPT).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb)) as (BB0 & BB16 & _ & BBCe & BBIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm)) as (BM0 & BM16 & _ & BMCe & BMIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp)) as (RP0 & RP16 & _ & RPCe & RPIMG).
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  assert (RP8 : RP mod 8 = 0) by (clear - RP16; Z.div_mod_to_equations; lia).
  unfold bio_head in HEAD. unfold bio_tail in TAIL. unfold M_MEM, M_SECMEM in METH. unfold bio_w1_cells in W1C.
  change ([C8 (wz 4294967297); C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl)] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]) in W1C.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [ISW W1C].
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [FLC W1C].
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [MIDC PTRC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FLC, MIDC, PTRC.
  replace (BI + 40 + 8) with (BI + 48) in FLC by lia. replace (BI + 40 + 8 + 4) with (BI + 52) in MIDC by lia. replace (BI + 40 + 8 + 4 + 12) with (BI + 64) in PTRC by lia.
  change 4294967297 with (1 + 2 ^ 32 * 1) in ISW. apply (proj2 (t_cells_halves usegs m (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in ISW.
  assert (INITC : ro_cells usegs m (BI + 40) [C4 (wz 1)]).
  { pose proof ISW as X. change ([C4 (wz 1); C4 (wz 1)]) with ([C4 (wz 1)] ++ [C4 (wz 1)]) in X. apply (proj1 (rw_cells_app usegs m _ _ _)) in X. exact (proj1 (proj1 X)). }
  (* [comment removed for export] *)
  assert (HD : rw_cells usegs m BI ([C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ++ [C4 (wz 1); C4 (wz 1)])).
  { apply (proj2 (rw_cells_app usegs m _ _ _)). split; [exact HEAD|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ISW. }
  assert (TL : rw_cells usegs m (BI + 52) ([C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)] ++ [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)])).
  { apply (proj2 (rw_cells_app usegs m _ _ _)). split; [exact MIDC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by lia.
    apply (proj2 (rw_cells_app usegs m _ _ _)). split; [exact PTRC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 64 + 8) with (BI + 72) by lia. exact TAIL. }
  cbn [app] in HD, TL.
  assert (GN : W1_grow_null_stmt (msec meth)) by (unfold msec, M_SECMEM; destruct METH as [-> | ->]; cbn; assumption).
  assert (GR : W1_grow_re_stmt (msec meth)) by (unfold msec, M_SECMEM; destruct METH as [-> | ->]; cbn; assumption).
  pose proof (grow_n_lt (len + n)) as GNL.
  (* [comment removed for export] *)
  pose proof NDK as NDK0. unfold mbio_blocks in NDK.
  assert (ND6 : k_bi K <> k_bb K /\ k_bi K <> k_bm K /\ k_bi K <> k_rp K /\ k_bb K <> k_bm K /\ k_bb K <> k_rp K /\ k_bm K <> k_rp K).
  { clear - NDK. apply List.NoDup_app_remove_r in NDK. inversion NDK as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst.
    cbn [In] in N1, N2, N3. repeat split; intros E; rewrite E in *; tauto. }
  destruct ND6 as (N12 & N13 & N14 & N23 & N24 & N34).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbb) N12) as A12.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbm) N13) as A13.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNrp) N14) as A14.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNbm) N23) as A23.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNrp) N24) as A24.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNrp) N34) as A34.
  hide N12. hide N13. hide N14. hide N23. hide N24. hide N34. hide A12. hide A13. hide A14. hide A23. hide A24. hide A34. hide BIIMG. hide BBIMG. hide BMIMG. hide RPIMG.
  assert (INB : In (k_bi K, BI, 128) LBall) by exact (proj1 OWNB). assert (INBB : In (k_bb K, BB, 16) LBall) by exact (proj1 OWNbb). assert (INR : In (k_rp K, RP, 32) LBall) by exact (proj1 OWNrp).
  assert (KDK : mbk_data K (k_d K) = K) by (destruct K; reflexivity).
  destruct (Z.eq_dec n 0) as [N0|NP].
  { (* [comment removed for export] *)
    subst n.
    cprefix. eapply evt_mono.
    { eapply W1_write_zero_proof with (lo := lo) (BI := BI) (BB := BB) (fl := fl) (IN := IN);
        [exact Ea0| exact Ea1| exact Ea2| exact BI0| exact FLC| exact FLOK| exact (proj1 PTRC)| exact BI8| exact ST| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia
        | clear - SLO STK160; lia| clear - BIC LO; lia| exact MI]. }
    cbv beta. intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fl' & m' & -> & MU & WM & MI' & ST' & FLOK' & FLC').
    apply climpl_done. exists (wz 0), m', LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [apply cgrow_same; clear - OFF LENM; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m m' _ sp _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MI'| | clear - SLO SPR STK160; lia| exact SPB| | exact ST'| exact SPB].
      - apply Forall_cons; [apply cwin_stack; clear - SLO SPR STK160; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BIIMG. clear - SLO SPR GLO BIIMG STK160. lia. }
    split. { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| clear - SLO SPR LO STK160; lia|].
      apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO STK160; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
    unfold bio_puts_res. rewrite !Z.add_0_r. exists (k_d K), max. split; [reflexivity|]. split; [left; reflexivity|]. split; [clear - OFF LENM; lia|]. rewrite KDK.
    split. { exists BM, BB, RP, fl', rrw, padw, nr, nw. split; [exact OWNB|]. split; [exact NDK0|]. split; [unfold M_MEM, M_SECMEM; exact METH|].
      trw HEAD MU WM. 2: { clear - SPR BIC LO SLO STK160; lia. } split; [exact HEAD|].
      trw ISW MU WM. 2: { clear - SPR BIC LO SLO STK160; lia. } trw MIDC MU WM. 2: { clear - SPR BIC LO SLO STK160; lia. } trw PTRC MU WM. 2: { clear - SPR BIC LO SLO STK160; lia. }
      split. { unfold bio_w1_cells. change ([C8 (wz 4294967297); C4 (wz fl'); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl')] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]).
        apply rw_cells_app. split; [change 4294967297 with (1 + 2 ^ 32 * 1); apply (proj1 (t_cells_halves usegs m' (BI + 40) 1 1 ltac:(lia) ltac:(lia))); exact ISW|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 40 + 8) with (BI + 48) by (clear; lia).
        apply rw_cells_app. split; [exact FLC'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 48 + 4) with (BI + 52) by (clear; lia).
        apply rw_cells_app. split; [exact MIDC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by (clear; lia). exact PTRC. }
      split; [exact FLOK'|]. trw TAIL MU WM. 2: { clear - SPR BIC LO SLO STK160; lia. } split; [exact TAIL|].
      exists rmaxw. split; [exact OWNbb|]. trw BBC MU WM. 2: { unfold hideP in A12; clear - SPR BBCe LO SLO STK160 A12; lia. } split; [exact BBC|].
      split; [exact OWNbm|]. split; [exact OWNrp|]. split; [exact OFF|]. split; [exact LENM|]. split; [exact MAX31|].
      destruct (k_d K) as [pd|].
      - destruct DOPT as (D & nm & junk0 & OWNd & MAXP & BMC & RPC & LJ & DC). exists D, nm, junk0. split; [exact OWNd|]. split; [exact MAXP|].
        pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNd)) as (D0 & _ & _ & DCe & _).
        assert (N15 : k_bi K <> pd). { clear - NDK. intros E. rewrite E in NDK. cbn [app] in NDK. inversion NDK as [|x1 l1 N1 ND1]; subst. apply N1. cbn [In]. tauto. }
        pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNd) N15) as A15.
        trw BMC MU WM. 2: { unfold hideP in A13; clear - SPR BMCe LO SLO STK160 A13; lia. } split; [exact BMC|].
        unfold readp_cells in RPC. trw RPC MU WM. 2: { unfold hideP in A14; clear - SPR RPCe LO SLO STK160 A14; lia. } split; [exact RPC|]. split; [exact LJ|].
        trw DC MU WM. 2: { clear - SPR DCe LO SLO STK160 A15 MAXP; rewrite ?Z2Nat.id by lia; lia. } exact DC.
      - destruct DOPT as (MAX0 & BMC & RPC). split; [exact MAX0|].
        trw BMC MU WM. 2: { unfold hideP in A13; clear - SPR BMCe LO SLO STK160 A13; lia. } split; [exact BMC|].
        unfold readp_cells in RPC. trw RPC MU WM. 2: { unfold hideP in A14; clear - SPR RPCe LO SLO STK160 A14; lia. } exact RPC. }
    split; [intros b Hb _; exact Hb|]. split; [intros q nm Hq _; exact Hq|]. split; [intros b Hb; left; exact Hb|]. split; [intros q nm Hq; left; exact Hq|].
    left. split; [rewrite ?KDK; reflexivity| split; [reflexivity| split; reflexivity]]. }
  destruct (k_d K) as [pd|] eqn:KD.
  2: { (* [comment removed for export] *)
    destruct DOPT as (MAX0 & BMC & RPC). assert (L0 : len = 0) by (clear - OFF LENM MAX0; lia). subst len. unfold readp_cells in RPC.
    eapply climpl_mono.
    { eapply (W1_write_new_spec (msec meth) GN) with (pbi := k_bi K) (BI := BI) (nbi := 128) (pbb := k_bb K) (BB := BB) (pbm := k_bm K) (BM := BM) (prp := k_rp K) (RP := RP)
                                                   (fl := fl) (inl := n) (IN := IN) (rmaxw := rmaxw) (rflw := wz (msec meth)) (src := src);
        [clear - Hf; lia| exact ROOM| exact CST| exact SLO| exact Ea0| exact Ea1| exact Ea2| clear - NP HN HLIM; lia| exact HIN| exact INB| clear; lia| exact INBB| exact OWNbm| exact INR
        | unfold hideP in N12, N13, N14, N23, N24, N34; clear - N12 N13 N14 N23 N24 N34; repeat split; assumption
        | exact INITC| exact FLC| exact FLOK| exact (proj1 PTRC)| exact HD| reflexivity| exact TL| cbn; clear; lia| exact BBC| unfold bufmem_cells; exact BMC| exact RPC
        | exact SRC| exact LSRC| eapply src_loc_weakT; [exact SLOC| intros q Hq; unfold mbio_T; clear - Hq; tauto]]. }
    cbv beta. intros f' L' s' ms' (v & m' & LBall' & CRET & Hf' & CG & CST' & CFR' & (q & D' & jk & fl' & -> & -> & -> & RNG & FLOK' & FLC' & BMC' & RPC' & LJ' & DC' & HD' & TL')).
    exists (wz n), m', ((q, D', grow_n n) :: LBall). split; [exact CRET|]. split; [clear - Hf' Hf; lia|]. split; [exact CG|]. split; [exact CST'|].
    split; [eapply cframe_weakT; [exact CFR'| intros q0 Hq0; unfold mbio_T; clear - Hq0; cbv beta in Hq0; tauto]|].
    assert (FRESH : forall p A n0, In (p, A, n0) LBall -> p <> q) by (intros p A n0 H; eapply cstate_head_fresh; [exact CST'| exact H]).
    pose proof CFR' as (AGR & _).
    assert (BBC' : rw_cells usegs m' BB [C8 (wz BM); C8 (wz RP)]).
    { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (k_bb K, BB, 16) AGR BBC INBB); [| unfold blk_addr; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; clear; lia].
      unfold blk_id; cbn [fst snd]. unfold hideP in N12, N23, N24. clear - N12 N23 N24. intros [E|[E|E]]; congruence. }
    pose proof (grow_n_lt n ltac:(clear - NP HN HLIM; lia)) as GNn. pose proof RNG as (D'0 & _ & _ & D'Ce & _).
    exists (Some q), (grow_n n). split; [reflexivity|]. split; [right; reflexivity|]. split; [clear - GNn; lia|].
    split. { change ([C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 1)]) with ([C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ++ [C4 (wz 1); C4 (wz 1)]) in HD'.
      apply (proj1 (rw_cells_app usegs m' _ _ _)) in HD'. destruct HD' as [HEAD' ISW']. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ISW'.
      change ([C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB); C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)])
        with ([C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)] ++ [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)]) in TL'.
      apply (proj1 (rw_cells_app usegs m' _ _ _)) in TL'. destruct TL' as [MIDC' TL']. apply (proj1 (rw_cells_app usegs m' _ _ _)) in TL'. destruct TL' as [PTRC' TAIL'].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PTRC', TAIL'. replace (BI + 52 + 12) with (BI + 64) in PTRC' by (clear; lia). replace (BI + 52 + 12 + 8) with (BI + 72) in TAIL' by (clear; lia).
      exists BM, BB, RP, fl', rrw, padw, nr, nw. split; [split; right; [exact INB| exact (proj2 OWNB)]|].
      split. { pose proof (FRESH _ _ _ INB) as Fq1. pose proof (FRESH _ _ _ INBB) as Fq2. pose proof (FRESH _ _ _ (proj1 OWNbm)) as Fq3. pose proof (FRESH _ _ _ INR) as Fq4.
        unfold mbio_blocks; cbn [k_bi k_bb k_bm k_rp k_d mbk_data app].
        constructor. { cbn [In]. intros [E|[E|[E|[E|[]]]]]; [exact (N12 (eq_sym E))| exact (N13 (eq_sym E))| exact (N14 (eq_sym E))| exact (Fq1 (eq_sym E))]. }
        constructor. { cbn [In]. intros [E|[E|[E|[]]]]; [exact (N23 (eq_sym E))| exact (N24 (eq_sym E))| exact (Fq2 (eq_sym E))]. }
        constructor. { cbn [In]. intros [E|[E|[]]]; [exact (N34 (eq_sym E))| exact (Fq3 (eq_sym E))]. }
        constructor. { cbn [In]. intros [E|[]]. exact (Fq4 (eq_sym E)). } constructor; [cbn [In]; intros []| constructor]. }
      split; [unfold M_MEM, M_SECMEM; exact METH|]. split; [exact HEAD'|].
      split. { unfold bio_w1_cells. change ([C8 (wz 4294967297); C4 (wz fl'); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl')] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]).
        apply rw_cells_app. split; [change 4294967297 with (1 + 2 ^ 32 * 1); apply (proj1 (t_cells_halves usegs m' (BI + 40) 1 1 ltac:(lia) ltac:(lia))); exact ISW'|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 40 + 8) with (BI + 48) by (clear; lia).
        apply rw_cells_app. split; [exact FLC'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 48 + 4) with (BI + 52) by (clear; lia).
        apply rw_cells_app. split; [exact MIDC'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by (clear; lia). exact PTRC'. }
      split; [exact FLOK'|]. split; [exact TAIL'|].
      exists (wz (grow_n n)). split; [split; right; [exact INBB| exact (proj2 OWNbb)]|]. split; [exact BBC'|]. split; [split; right; [exact (proj1 OWNbm)| exact (proj2 OWNbm)]|].
      split; [split; right; [exact INR| exact (proj2 OWNrp)]|]. split; [clear - NP HN; lia|]. split; [clear - GNn; lia|]. split; [clear - GNn; lia|].
      cbn [k_d mbk_data]. exists D', (grow_n n), jk. split; [split; left; reflexivity|]. split; [clear - GNn NP HN; lia|].
      split; [unfold bufmem_cells in BMC'; exact BMC'|]. split; [exact RPC'|]. split; [exact LJ'| exact DC']. }
    split; [intros b Hb _; right; exact Hb|]. split; [intros q0 nm Hq _; right; exact Hq|].
    split; [intros b [<-|Hb]; [right; reflexivity| left; exact Hb]|]. split; [intros q0 nm [E|Hq]; [right; congruence| left; exact Hq]|].
    right; left. exists q, D'. split; [reflexivity|]. split; [first [exact KD| reflexivity]|]. split; reflexivity. }
  (* [comment removed for export] *)
  destruct DOPT as (D & nm & junk0 & OWNd & MAXP & BMC & RPC & LJ & DC). unfold readp_cells in RPC.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNd)) as (D0 & _ & _ & DCe & DIMG). hide DIMG.
  assert (ND4 : k_bi K <> pd /\ k_bb K <> pd /\ k_bm K <> pd /\ k_rp K <> pd).
  { clear - NDK. cbn [app] in NDK. inversion NDK as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst. inversion ND3 as [|x4 l4 N4 ND4]; subst.
    cbn [In] in N1, N2, N3, N4. repeat split; intros E; rewrite E in *; tauto. }
  destruct ND4 as (N15 & N25 & N35 & N45). clear NDK.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNd) N15) as A15.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNd) N25) as A25.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNd) N35) as A35.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp) (proj1 OWNd) N45) as A45.
  hide N15. hide N25. hide N35. hide N45. hide A15. hide A25. hide A35. hide A45.
  assert (IND : In (pd, D, max) LBall) by exact (proj1 OWNd).
  destruct (Z_le_dec (len + n) max) as [FIT|GROWc].
  - (* [comment removed for export] *)
    assert (INA : (IN + n <= lo \/ bv_unsigned sp <= IN) /\ (IN + n <= BI \/ BI + 128 <= IN) /\ (IN + n <= D \/ D + max <= IN) /\ (IN + n <= BM \/ BM + 32 <= IN) /\ (IN + n <= RP \/ RP + 32 <= IN)).
    { destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)]; [clear - SL BIC DCe BMCe RPCe LO SLO STK160; repeat split; lia|].
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (_ & _ & _ & SCe & _).
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS INB ltac:(intros E; apply NTS; unfold mbio_T; rewrite E; tauto)) as B1.
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS IND ltac:(intros E; apply NTS; unfold mbio_T; rewrite E, KD; tauto)) as B2.
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS (proj1 OWNbm) ltac:(intros E; apply NTS; unfold mbio_T; rewrite E; tauto)) as B3.
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS INR ltac:(intros E; apply NTS; unfold mbio_T; rewrite E; tauto)) as B4.
      clear - B1 B2 B3 B4 S1 S2 SCe LO. repeat split; lia. }
    destruct INA as (IA0 & IA1 & IA2 & IA3 & IA4).
    cprefix. eapply evt_mono.
    { eapply W1_write_fit_proof with (lo := lo) (BI := BI) (BB := BB) (BM := BM) (RP := RP) (D := D) (len := len) (max := max) (off := 0) (fl := fl) (inl := n) (IN := IN)
                                  (rmaxw := rmaxw) (flw := wz (msec meth)) (junk := junk0) (src := src);
        [exact Ea0| exact Ea1| exact Ea2| exact BI0| exact HIN| clear - NP HN; lia| exact INITC| exact FLC| exact FLOK| exact (proj1 PTRC)| exact BB0| exact (proj1 BBC)
        | exact BM0| unfold bufmem_cells; exact BMC| exact RP0| exact RPC| exact D0| clear - OFF; lia| exact LENM| clear - MAX31; lia| clear - DCe CW; lia| clear - FIT; lia
        | exact LJ| exact DC| exact SRC| exact LSRC| exact BI8| exact BB8| exact BM8| exact RP8| exact ST| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia| clear - SLO STK160; lia
        | clear - BIC LO; lia| clear - BBCe LO; lia| clear - BMCe LO; lia| clear - RPCe LO; lia| clear - DCe LO; lia
        | unfold hideP in A25; clear - A25; lia| unfold hideP in A35; clear - A35; lia| unfold hideP in A45; clear - A45; lia| unfold hideP in A34; clear - A34; lia
        | unfold tbox; unfold hideP in A15, A13, A14, A12, A23, A24; clear - IA0 IA1 IA2 IA3 IA4 A15 A13 A14 A12 A23 A24 MAXP; repeat split; lia
        | exact MI]. }
    cbv beta. intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fl' & junk' & m' & -> & MU & WM & MI' & ST' & FLOK' & FLC' & BMC' & RPC' & LJ' & DC').
    replace (len - 0 + n) with (len + n) in * by (clear; lia).
    apply climpl_done. exists (wz n), m', LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [apply cgrow_same; clear - OFF LENM NP HN; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m m' _ sp _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MI'| | clear - SLO SPR STK160; lia| exact SPB| | exact ST'| exact SPB].
      - apply Forall_cons; [apply cwin_stack; clear - SLO SPR STK160; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (pd, D, max)); [exact IND| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bm K, BM, 32)); [exact (proj1 OWNbm)| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_rp K, RP, 32)); [exact INR| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BIIMG, DIMG, BMIMG, RPIMG. clear - SLO SPR GLO BIIMG DIMG BMIMG RPIMG STK160 MAXP. lia. }
    split. { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| clear - SLO SPR LO STK160; lia|].
      apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO STK160; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pd, D, max)); [exact IND| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; do 4 right; exact KD| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bm K, BM, 32)); [exact (proj1 OWNbm)| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; do 2 right; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_rp K, RP, 32)); [exact INR| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; do 3 right; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
    exists (Some pd), max. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact FIT|]. rewrite KDK.
    split. { exists BM, BB, RP, fl', rrw, padw, nr, nw. split; [exact OWNB|]. split; [exact NDK0|]. split; [unfold M_MEM, M_SECMEM; exact METH|].
      trw HEAD MU WM. 2: { unfold hideP in A15, A13, A14; clear - SPR BIC DCe BMCe RPCe LO SLO STK160 A15 A13 A14 MAXP; lia. } split; [exact HEAD|].
      trw ISW MU WM. 2: { unfold hideP in A15, A13, A14; clear - SPR BIC DCe BMCe RPCe LO SLO STK160 A15 A13 A14 MAXP; lia. }
      trw MIDC MU WM. 2: { unfold hideP in A15, A13, A14; clear - SPR BIC DCe BMCe RPCe LO SLO STK160 A15 A13 A14 MAXP; lia. }
      trw PTRC MU WM. 2: { unfold hideP in A15, A13, A14; clear - SPR BIC DCe BMCe RPCe LO SLO STK160 A15 A13 A14 MAXP; lia. }
      split. { unfold bio_w1_cells. change ([C8 (wz 4294967297); C4 (wz fl'); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl')] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]).
        apply rw_cells_app. split; [change 4294967297 with (1 + 2 ^ 32 * 1); apply (proj1 (t_cells_halves usegs m' (BI + 40) 1 1 ltac:(lia) ltac:(lia))); exact ISW|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 40 + 8) with (BI + 48) by (clear; lia).
        apply rw_cells_app. split; [exact FLC'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 48 + 4) with (BI + 52) by (clear; lia).
        apply rw_cells_app. split; [exact MIDC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by (clear; lia). exact PTRC. }
      split; [exact FLOK'|]. trw TAIL MU WM. 2: { unfold hideP in A15, A13, A14; clear - SPR BIC DCe BMCe RPCe LO SLO STK160 A15 A13 A14 MAXP; lia. } split; [exact TAIL|].
      exists (wz max). split; [exact OWNbb|]. trw BBC MU WM. 2: { unfold hideP in A12, A25, A23, A24; clear - SPR BBCe DCe BMCe RPCe LO SLO STK160 A12 A25 A23 A24 MAXP; lia. } split; [exact BBC|].
      split; [exact OWNbm|]. split; [exact OWNrp|]. split; [clear - OFF NP HN; lia|]. split; [exact FIT|]. split; [exact MAX31|].
      rewrite KD. exists D, nm, junk'. split; [exact OWNd|]. split; [exact MAXP|]. split; [unfold bufmem_cells in BMC'; exact BMC'|]. split; [exact RPC'|]. split; [exact LJ'| exact DC']. }
    split; [intros b Hb _; exact Hb|]. split; [intros q nm0 Hq _; exact Hq|]. split; [intros b Hb; left; exact Hb|]. split; [intros q nm0 Hq; left; exact Hq|].
    left. split; [first [exact (eq_sym KD)| reflexivity]| split; [reflexivity| split; reflexivity]].
  - (* [comment removed for export] *)
    eapply climpl_mono.
    { eapply (W1_write_re_spec (msec meth) GR) with (pbi := k_bi K) (BI := BI) (nbi := 128) (pbb := k_bb K) (BB := BB) (pbm := k_bm K) (BM := BM) (prp := k_rp K) (RP := RP)
                                                  (pd := pd) (D := D) (len := len) (max := max) (nm := nm) (off := 0) (fl := fl) (inl := n) (IN := IN) (rmaxw := rmaxw) (junk := junk0) (src := src);
        [exact Hf| replace (len - 0 + n) with (len + n) by (clear; lia); exact ROOM| exact CST| exact SLO| exact Ea0| exact Ea1| exact Ea2| clear - NP HN; lia| exact HIN
        | exact INB| clear; lia| exact INBB| exact OWNbm| exact INR| exact OWNd
        | unfold hideP in N12, N13, N14, N15, N23, N24, N25, N34, N35, N45; clear - N12 N13 N14 N15 N23 N24 N25 N34 N35 N45; repeat split; assumption
        | exact INITC| exact FLC| exact FLOK| exact (proj1 PTRC)| exact HD| reflexivity| exact TL| cbn; clear; lia| exact BBC| unfold bufmem_cells; exact BMC| exact RPC
        | clear - OFF; lia| exact LENM| exact MAXP| clear - GROWc; lia| clear - HLIM NP HN; lia| exact DC
        | exact SRC| exact LSRC| eapply src_loc_weakT; [exact SLOC| intros q Hq; unfold mbio_T; rewrite KD; clear - Hq; cbv beta in Hq; intuition congruence]]. }
    cbv beta. intros f' L' s' ms' (v & m' & LBall' & CRET & Hf' & CG & CST' & CFR' & (q & D' & jk & i & fl' & -> & -> & HI & -> & RNG & FLOK' & FLC' & BMC' & RPC' & LJ' & DC' & HD' & TL')).
    replace (len - 0 + n) with (len + n) in * by (clear; lia).
    exists (wz n), m', ((q, D', grow_n (len + n)) :: lb_remove pd LBall). split; [exact CRET|]. split; [exact Hf'|]. split; [exact CG|]. split; [exact CST'|].
    split; [eapply cframe_weakT; [exact CFR'| intros q0 Hq0; unfold mbio_T; rewrite KD; unfold write_T in Hq0; clear - Hq0; intuition congruence]|].
    assert (KEEP : forall p A n0, In (p, A, n0) LBall -> p <> pd -> In (p, A, n0) ((q, D', grow_n (len + n)) :: lb_remove pd LBall)).
    { intros p A n0 H NE. right. apply lb_remove_In. split; [exact H| unfold blk_id; cbn [fst snd]; exact NE]. }
    assert (FRESH : forall p A n0, In (p, A, n0) LBall -> p <> pd -> p <> q).
    { intros p A n0 H NE. eapply cstate_head_fresh; [exact CST'| apply lb_remove_In; split; [exact H| unfold blk_id; cbn [fst snd]; exact NE]]. }
    assert (KEEPL : forall p nm0, In (p, nm0) L -> p <> pd -> In (p, nm0) ((q, grow_n (len + n)) :: cremove i L)).
    { intros p nm0 H NE. right. eapply cremove_keep; [exact HI| exact H| exact NE]. }
    unfold hideP in N15, N25, N35, N45.
    pose proof CFR' as (AGR & _).
    assert (BBC' : rw_cells usegs m' BB [C8 (wz BM); C8 (wz RP)]).
    { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (k_bb K, BB, 16) AGR BBC INBB); [| unfold blk_addr; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; clear; lia].
      unfold blk_id, write_T; cbn [fst snd]. unfold hideP in N12, N23, N24. clear - N12 N23 N24 N25. intuition congruence. }
    pose proof RNG as (D'0 & _ & _ & D'Ce & _).
    exists (Some q), (grow_n (len + n)). split; [reflexivity|]. split; [right; reflexivity|]. split; [clear - GNL NP HN HLIM OFF LENM; lia|].
    split. { change ([C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 1)]) with ([C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ++ [C4 (wz 1); C4 (wz 1)]) in HD'.
      apply (proj1 (rw_cells_app usegs m' _ _ _)) in HD'. destruct HD' as [HEAD' ISW']. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ISW'.
      change ([C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB); C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)])
        with ([C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)] ++ [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)]) in TL'.
      apply (proj1 (rw_cells_app usegs m' _ _ _)) in TL'. destruct TL' as [MIDC' TL']. apply (proj1 (rw_cells_app usegs m' _ _ _)) in TL'. destruct TL' as [PTRC' TAIL'].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PTRC', TAIL'. replace (BI + 52 + 12) with (BI + 64) in PTRC' by (clear; lia). replace (BI + 52 + 12 + 8) with (BI + 72) in TAIL' by (clear; lia).
      exists BM, BB, RP, fl', rrw, padw, nr, nw. split; [split; [exact (KEEP _ _ _ INB N15)| exact (KEEPL _ _ (proj2 OWNB) N15)]|].
      split. { pose proof (FRESH _ _ _ INB N15) as Fq1. pose proof (FRESH _ _ _ INBB N25) as Fq2. pose proof (FRESH _ _ _ (proj1 OWNbm) N35) as Fq3. pose proof (FRESH _ _ _ INR N45) as Fq4.
        unfold mbio_blocks; cbn [k_bi k_bb k_bm k_rp k_d mbk_data app].
        constructor. { cbn [In]. intros [E|[E|[E|[E|[]]]]]; [exact (N12 (eq_sym E))| exact (N13 (eq_sym E))| exact (N14 (eq_sym E))| exact (Fq1 (eq_sym E))]. }
        constructor. { cbn [In]. intros [E|[E|[E|[]]]]; [exact (N23 (eq_sym E))| exact (N24 (eq_sym E))| exact (Fq2 (eq_sym E))]. }
        constructor. { cbn [In]. intros [E|[E|[]]]; [exact (N34 (eq_sym E))| exact (Fq3 (eq_sym E))]. }
        constructor. { cbn [In]. intros [E|[]]. exact (Fq4 (eq_sym E)). } constructor; [cbn [In]; intros []| constructor]. }
      split; [unfold M_MEM, M_SECMEM; exact METH|]. split; [exact HEAD'|].
      split. { unfold bio_w1_cells. change ([C8 (wz 4294967297); C4 (wz fl'); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl')] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]).
        apply rw_cells_app. split; [change 4294967297 with (1 + 2 ^ 32 * 1); apply (proj1 (t_cells_halves usegs m' (BI + 40) 1 1 ltac:(lia) ltac:(lia))); exact ISW'|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 40 + 8) with (BI + 48) by (clear; lia).
        apply rw_cells_app. split; [exact FLC'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 48 + 4) with (BI + 52) by (clear; lia).
        apply rw_cells_app. split; [exact MIDC'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by (clear; lia). exact PTRC'. }
      split; [exact FLOK'|]. split; [exact TAIL'|].
      exists (wz (grow_n (len + n))). split; [split; [exact (KEEP _ _ _ INBB N25)| exact (KEEPL _ _ (proj2 OWNbb) N25)]|]. split; [exact BBC'|].
      split; [split; [exact (KEEP _ _ _ (proj1 OWNbm) N35)| exact (KEEPL _ _ (proj2 OWNbm) N35)]|].
      split; [split; [exact (KEEP _ _ _ INR N45)| exact (KEEPL _ _ (proj2 OWNrp) N45)]|]. split; [clear - NP HN OFF; lia|]. split; [clear - GNL NP HN HLIM OFF LENM; lia|]. split; [clear - GNL NP HN HLIM OFF LENM; lia|].
      cbn [k_d mbk_data]. exists D', (grow_n (len + n)), jk. split; [split; left; reflexivity|]. split; [clear - GNL NP HN HLIM OFF LENM; lia|].
      split; [unfold bufmem_cells in BMC'; exact BMC'|]. split; [exact RPC'|]. split; [exact LJ'| exact DC']. }
    split; [intros b Hb NE; destruct b as [[p A] n0]; apply (KEEP _ _ _ Hb); unfold blk_id in NE; cbn [fst snd] in NE; congruence|].
    split; [intros q0 nm0 Hq NE; apply (KEEPL _ _ Hq); congruence|].
    split; [intros b [<-|Hb]; [right; reflexivity| left; exact (proj1 (proj1 (lb_remove_In _ _ _) Hb))]|].
    split. { intros q0 nm0 [E|Hq]; [right; congruence| left]. destruct (cremove_split _ _ _ HI) as (l1 & l2 & -> & _ & EC). rewrite EC in Hq.
      apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; exact Hq| right; right; exact Hq]. }
    right; right. exists q, D', pd, i, nm. split; [reflexivity|]. split; [first [exact KD| reflexivity]|]. split; [reflexivity|]. split; [exact HI| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_puts_spec : W1_grow_null_stmt 0 -> W1_grow_null_stmt 1 -> W1_grow_re_stmt 0 -> W1_grow_re_stmt 1 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (pl : bptr) (BI meth len max LB n lo B : Z)
         (bs : list byte),
    (2 <= f)%nat -> croom L (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) ->
    cstate st LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - (32 + MW_STACK) -> mbio_rep m LBall L K BI meth len max 0 -> len + n < 2 ^ 30 ->
    cown LBall L pl LB 256 256 -> ~ mbio_T K pl -> length bs = 256%nat -> rw_cells usegs m LB [CB 256 bs] ->
    0 <= n <= 255 -> nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0) -> (forall i, (i < Z.to_nat n)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)) ->
    a0 = wz BI -> a1 = wz LB ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x18357c) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB0 L f m lo B (mbio_T K) [] 2
             (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) (bio_puts_res K BI meth len max n LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros GN0 GN1 GR0 GR1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB0 L f K pl BI meth len max LB n lo Bd bs
         Hf ROOM CST SLO MB HLIM OWNL NTL LBS BUF HN NUL NONUL Ea0 Ea1.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO). unfold MW_STACK, WRITE_STACK, GROW_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (STK160 : 160 <= 64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)).
  { unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK. clear; lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (LB00 & LBAL & _ & LBC & _).
  destruct (nth_error_split bs (Z.to_nat n) _ NUL) as (l1 & l2 & EBS & LEN1).
  pose proof (rw_cells_bytes_at usegs m LB _ BUF) as SRC. cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r, EBS in SRC.
  assert (LEN2 : Z.of_nat (length l2) = 255 - n) by (apply (f_equal (@length byte)) in EBS; rewrite length_app in EBS; cbn [length] in EBS; clear - EBS LEN1 LBS HN; lia).
  eapply W1_puts_compose with (STR := LB) (str := l1) (slack := l2);
    [exact CST| clear - SLO STK160; lia| exact Ea1| clear - LB00; lia| exact SRC| | | clear - LEN1 HN; lia| left; clear - LBC LO LEN1 LEN2 HN; lia|].
  { intros IN0. destruct (In_nth_error _ _ IN0) as [i Hi]. assert (Li : (i < length l1)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    apply (NONUL i ltac:(clear - Li LEN1; lia)). rewrite EBS, nth_error_app1 by exact Li. exact Hi. }
  { assert (E8 : LB = 8 * (LB / 8)) by (clear - LBAL; rewrite (Z.div_mod LB 16) at 1 by lia; rewrite LBAL; lia).
    replace (- (LB + Z.of_nat (length l1) + 1)) with ((255 - n) + (- (LB / 8) - 32) * 8) by (clear - E8 LEN1 HN; lia).
    rewrite Z.mod_add by (clear; lia). rewrite LEN2. apply Z.mod_le; clear - HN; lia. }
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM CST' SRC'.
  apply (proj1 (bytes_at_app _ _ _ _ _)) in SRC'. destruct SRC' as [SRC1 _].
  assert (FPD : forall b, In b LBall -> mbio_T K (blk_id b) -> disjoint_from [(bv_unsigned sp - 32, bv_unsigned sp)]%Z (blk_addr b) (blk_size b)).
  { intros [[bp bA] bn] IN _. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST IN) as (_ & _ & _ & RC & _). unfold blk_addr, blk_size. cbn [fst snd disjoint_from]. clear - RC LO SLO STK160. lia. }
  eapply (mem_write_spec GN0 GN1 GR0 GR1) with (K := K) (IN := LB) (src := l1);
    [exact Hf| exact ROOM| exact CST'| unfold MW_STACK, WRITE_STACK, GROW_STACK; clear - SLO; lia| exact (mbio_rep_agree _ _ _ _ _ _ _ _ _ _ MB (munch_mbio_fp _ _ _ _ _ _ _ _ _ _ _ K CST MU WM FPD))| exact HLIM
    | clear - HN; lia| exact LB00| exact SRC1| rewrite LEN1; reflexivity| | exact Ea0| reflexivity| rewrite LEN1, Z2Nat.id by (clear - HN; lia); reflexivity].
  right. exists pl, LB, 256. split; [exact (proj1 OWNL)|]. split; [exact NTL|]. clear - HN; lia.
Qed.

(* [comment removed for export] *)
Lemma meth_bputs : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) -> rw_cells usegs m (meth + 48) [C8 (wz 0x18357c)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM.
  - cimg_cell CIMG m (0x2d3fc8 + 48) [C8 (wz 0x18357c)] H. exact H.
  - cimg_cell CIMG m (0x2d4038 + 48) [C8 (wz 0x18357c)] H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_puts_spec : W1_grow_null_stmt 0 -> W1_grow_null_stmt 1 -> W1_grow_re_stmt 0 -> W1_grow_re_stmt 1 -> bio_puts_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros GN0 GN1 GR0 GR1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f K pl BI meth len max LB n lo Bd bs
         Hf ROOM CST SLO MB HLIM OWNL NTL LBS BUF HN NUL NONUL -> ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO). unfold BPUTS_STACK, FZ_BIO_PUTS, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (WSP : 160 <= WRITE_STACK) by (unfold WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
  pose proof MB as [BM (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER)].
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG). hide BIIMG.
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (LB00 & _ & _ & LBC & LBIMG). hide LBIMG.
  unfold M_MEM, M_SECMEM in METH. pose proof (meth_bputs m meth CIMG MI ltac:(unfold M_MEM, M_SECMEM; exact METH)) as MBP.
  assert (METH8 : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  unfold bio_head in HEAD. unfold bio_w1_cells in W1C.
  change ([C8 (wz 4294967297); C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) in W1C.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [ISW _].
  change 4294967297 with (1 + 2 ^ 32 * 1) in ISW. apply (proj2 (t_cells_halves usegs m (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in ISW. clear TAIL INNER.
  assert (FPD : forall b, In b LBall -> mbio_T K (blk_id b) -> disjoint_from [(bv_unsigned sp - 48, bv_unsigned sp)]%Z (blk_addr b) (blk_size b)).
  { intros [[bp bA] bn] IN _. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST IN) as (_ & _ & _ & RC & _). unfold blk_addr, blk_size. cbn [fst snd disjoint_from]. clear - RC LO SLO WSP. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. ths. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 4 ths. ths. ths.
  ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 BI0 BIC LO CEIL_RANGE__; unfold ceil_window in *; lia. } clear K0.
  ths. ths. ths. ubs_if. ths. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 METH; lia. } clear K1.
  ths. ths. ths. ubs_if. ths. ths. th_if_lit. ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. ths. th_if_lit. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
  lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
  lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
  assert (CSTc : cstate s LBall LB0 L mc0 (wz (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ s LBall LB0 L m mc0 sp _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MUq| exact WMq| exact MIc| | clear - SLO SPR WSP LO; lia| exact SPB| | |].
    - apply Forall_cons; [apply cwin_stack; clear - SLO SPR WSP; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO SPR GLO WSP. lia.
    - rewrite unsigned_lit by lia. exact STc.
    - rewrite unsigned_lit by lia. clear - SPB; lia. }
  assert (FR0 : cframe (mbio_T K) [] (bv_unsigned sp) s LBall L m s LBall L mc0).
  { eapply cframe_seg; [apply cframe_refl| exact MUq| exact WMq| exact HP| clear - SLO SPR LO WSP; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO WSP; lia| apply Forall_nil]. }
  chere. eapply climpl_seq.
  { eapply (mem_puts_spec GN0 GN1 GR0 GR1) with (K := K) (pl := pl) (BI := BI) (meth := meth) (len := len) (max := max) (LB := LB) (n := n) (bs := bs);
      [exact Hf| exact ROOM| exact CSTc| rewrite unsigned_lit by lia; unfold MW_STACK; clear - SLO WSP; lia
      | exact (mbio_rep_agree _ _ _ _ _ _ _ _ _ _ MB (munch_mbio_fp _ _ _ _ _ _ _ _ _ _ _ K CST MUq WMq FPD))| exact HLIM| exact OWNL| exact NTL| exact LBS| exact BUF| exact HN| exact NUL| exact NONUL
      | reflexivity| reflexivity]. }
  cbv beta. intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1' & CST1 & FRM1 & R1).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
  destruct R1 as (pd' & max' & -> & HMAX & HFIT & MB1 & KB & KL & NB & NL & PLS).
  pose proof FRM1 as (CFR1 & _). pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRc ltac:(clear; lia)) as FR1. clear FRc.
  pose proof MB1 as [BM1 (BB1 & RP1 & fl1 & rrw1 & padw1 & nr1 & nw1 & OWNB1 & NDK1 & _ & HEAD1 & W1C1 & FLOK1 & TAIL1 & INNER1)]. unfold bio_head in HEAD1. unfold bio_tail in TAIL1.
  cbn [k_bi k_bb k_bm k_rp k_d mbk_data] in OWNB1, INNER1, NDK1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1)) as (_ & _ & _ & BIC1 & BIIMG1). hide BIIMG1.
  assert (INB1 : In (k_bi K, BI, 128) LB1) by exact (proj1 OWNB1).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (BI + 104, BI + 112)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  assert (FIN : forall m2 (nwX : word) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    stk usegs m2 lo (bv_unsigned sp) -> mem_inv usegs m2 -> munch [(bv_unsigned sp - 48, bv_unsigned sp); (BI + 104, BI + 112)]%Z m1 m2 -> wmono usegs m1 m2 ->
    rw_cells usegs m2 (BI + 72) [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr1; C8 nwX; C8 (wz 0); C8 (wz 0)] ->
    cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo Bd (mbio_T K) [] 2 (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n)))
      (bio_puts_res K BI meth len max n LBall L) f1 L1 st1
      (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz n) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom usegs))).
  { intros m2 nwX y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 ST2 MI2 MU12 WM12 TAIL2.
    exists (wz n), m2, LB1. split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1'|].
    split. { eapply (cstate_seg _ st1 LB1 LB0 L1 m1 m2 _ sp tp lo Bd (bv_unsigned sp)); [exact CST1| exact MU12| exact WM12| exact MI2| | clear - SLO SPR WSP; lia| exact SPB| | exact ST2| exact SPB].
      - apply Forall_cons; [apply cwin_stack; clear - SLO SPR WSP; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB1| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BIIMG1. clear - SLO SPR GLO WSP BIIMG1. lia. }
    split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| clear; lia| intros a X; exact X| intros q _ NT; exact NT]| exact MU12| exact WM12| exact HP1| clear - SLO SPR LO WSP; lia|].
      apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO WSP; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB1| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
    exists pd', max'. split; [reflexivity|]. split; [exact HMAX|]. split; [exact HFIT|]. split; [| split; [exact KB| split; [exact KL| split; [exact NB| split; [exact NL| exact PLS]]]]].
    destruct INNER1 as (rmaxw1 & OWNbb1 & BBC1 & OWNbm1 & OWNrp1 & OFF1 & LENM1 & MAX1 & DOPT1).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNbb1)) as (_ & _ & _ & BBC1e & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNbm1)) as (_ & _ & _ & BMC1e & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNrp1)) as (_ & _ & _ & RPC1e & _).
    pose proof NDK1 as NDK1'. unfold mbio_blocks in NDK1; cbn [k_bi k_bb k_bm k_rp k_d mbk_data] in NDK1.
    assert (ND3 : k_bi K <> k_bb K /\ k_bi K <> k_bm K /\ k_bi K <> k_rp K).
    { clear - NDK1. apply List.NoDup_app_remove_r in NDK1. inversion NDK1 as [|x1 l1 N1 ND1]; subst. cbn [In] in N1. repeat split; intros E; rewrite E in *; tauto. }
    destruct ND3 as (M12 & M13 & M14).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNbb1) M12) as C12.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNbm1) M13) as C13.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNrp1) M14) as C14.
    exists BM1, BB1, RP1, fl1, rrw1, padw1, nr1, nwX. split; [exact OWNB1|]. split; [exact NDK1'|]. split; [unfold M_MEM, M_SECMEM; exact METH|].
    trw HEAD1 MU12 WM12. 2: { clear - SPR BIC1 LO SLO WSP; lia. } split; [exact HEAD1|].
    trw W1C1 MU12 WM12. 2: { unfold bio_w1_cells. cbn [length cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR BIC1 LO SLO WSP; lia. } split; [exact W1C1|].
    split; [exact FLOK1|]. split; [exact TAIL2|].
    exists rmaxw1. split; [exact OWNbb1|]. trw BBC1 MU12 WM12. 2: { clear - SPR BBC1e LO SLO WSP C12; lia. } split; [exact BBC1|].
    split; [exact OWNbm1|]. split; [exact OWNrp1|]. split; [exact OFF1|]. split; [exact LENM1|]. split; [exact MAX1|].
    destruct pd' as [pd1|]; cbn [k_d mbk_data] in DOPT1; cbn [k_d mbk_data].
    - destruct DOPT1 as (D1 & nm1 & jk1 & OWNd1 & MAXP1 & BMC2 & RPC2 & LJ1 & DC1). exists D1, nm1, jk1. split; [exact OWNd1|]. split; [exact MAXP1|].
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNd1)) as (_ & _ & _ & DC1e & _).
      assert (M15 : k_bi K <> pd1). { clear - NDK1. intros E. rewrite E in NDK1. cbn [app] in NDK1. inversion NDK1 as [|x1 l1 N1 ND1]; subst. apply N1. cbn [In]. tauto. }
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNd1) M15) as C15.
      trw BMC2 MU12 WM12. 2: { clear - SPR BMC1e LO SLO WSP C13; lia. } split; [exact BMC2|].
      unfold readp_cells in RPC2. trw RPC2 MU12 WM12. 2: { clear - SPR RPC1e LO SLO WSP C14; lia. } split; [exact RPC2|]. split; [exact LJ1|].
      trw DC1 MU12 WM12. 2: { clear - SPR DC1e LO SLO WSP C15 MAXP1; rewrite ?Z2Nat.id by lia; lia. } exact DC1.
    - destruct DOPT1 as (MAX0 & BMC2 & RPC2). split; [exact MAX0|].
      trw BMC2 MU12 WM12. 2: { clear - SPR BMC1e LO SLO WSP C13; lia. } split; [exact BMC2|].
      unfold readp_cells in RPC2. trw RPC2 MU12 WM12. 2: { clear - SPR RPC1e LO SLO WSP C14; lia. } exact RPC2. }
  clear INNER1.
  assert (NR : 0 <= n < 2 ^ 31) by (clear - HN; lia).
  cprefix. ths. ths. if_cases Kn; zify_cond Kn.
  - (* [comment removed for export] *)
    assert (N0 : n = 0) by (rewrite ?unsigned_lit in Kn by lia; clear - Kn HN; lia).
    ths. ths. th_if_lit. ths. ths. th_if_lit. ths. rewrite (t_sextw_small n) by (clear - NR; lia). subst n. ths. th_if_lit.
    ths. change (bv_swrap 32 (bv_unsigned (Z_to_bv 64 0) + 0)) with 0. do 4 ths. ths. th_release FR1 (bv_unsigned sp). ths.
    chere. apply climpl_done. eapply (FIN _ nw1); [assumption| assumption| exact MU1| exact WM1| exact TAIL1].
  - (* [comment removed for export] *)
    ths. ths. ths. ths. ths. ths. ths. th_if_lit. ths. ths. th_if_lit. ths. ths. th_if_lit. ths.
    ths. ths. if_cases K3; zify_cond K3. 2: { exfalso. rewrite ?unsigned_lit in K3 by lia. rewrite Z.shiftr_div_pow2 in K3 by lia. apply K3. apply Z.div_small. clear - NR; lia. }
    ths. rewrite (t_sextw_small n) by (clear - NR; lia). do 4 ths. ths. th_release FR1 (bv_unsigned sp). ths.
    chere. apply climpl_done. eapply FIN; [assumption| assumption| eassumption| eassumption| eassumption].
Qed.
End WithCeiling0.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Theorem bio_puts_specM : crypto_clear_realloc_null_stmt -> crypto_clear_realloc_grow_stmt -> crypto_secure_malloc_stmt -> crypto_secure_clear_free_stmt -> bio_puts_stmt.
Proof. intros A B C D. apply bio_puts_spec; [exact (W1_grow_null_spec A)| exact (W1_grow_null_sec_spec C)| exact (W1_grow_re_spec B)| exact (W1_grow_re_sec_spec C D)]. Qed.
Theorem mem_write_specM : crypto_clear_realloc_null_stmt -> crypto_clear_realloc_grow_stmt -> crypto_secure_malloc_stmt -> crypto_secure_clear_free_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI meth len max IN n lo B : Z)
         (src : list byte),
    (2 <= f)%nat -> croom L (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) ->
    cstate st LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - MW_STACK -> mbio_rep m LBall L K BI meth len max 0 -> len + n < 2 ^ 30 -> 0 <= n < 2 ^ 31 ->
    0 < IN -> bytes_at usegs m IN src -> length src = Z.to_nat n -> src_loc LBall (mbio_T K) (bv_unsigned sp) IN n ->
    a0 = wz BI -> a1 = wz IN -> a2 = wz n ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_MEM_WRITE) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB0 L f m lo B (mbio_T K) [] 2
             (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n))) (bio_puts_res K BI meth len max n LBall L)).
Proof. intros A B C D. apply mem_write_spec; [exact (W1_grow_null_spec A)| exact (W1_grow_null_sec_spec C)| exact (W1_grow_re_spec B)| exact (W1_grow_re_sec_spec C D)]. Qed.
End WithCeiling1.
