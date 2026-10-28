(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Drv_facts.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import CtxKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma u32s_exists : forall k (bs : list byte), length bs = (4 * k)%nat -> exists ws : list word, length ws = k /\ u32s ws = bs.
Proof.
  induction k as [|k IH]; intros bs H.
  - exists []. destruct bs; [split; reflexivity| cbn in H; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 bs]]]]; try (cbn in H; lia).
    destruct (IH bs ltac:(cbn in H; lia)) as (ws & Hl & E). destruct (Drv_facts.le4_of_bytes b0 b1 b2 b3) as (w & Ew).
    exists (w :: ws). split; [cbn; lia|]. cbn [u32s]. rewrite Ew, E. reflexivity.
Qed.

Lemma upd_app_mid : forall {X} (l1 : list X) x l2 v, Arr.upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|y l1 IH]; intros x l2 v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_CTX_START : Z := 0x100c14.
Definition BN_CTX_START_STACK : Z := 64 + 8400.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_CTX_start_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_CTX_START_STACK -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_start (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' _ => PL' = PL /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_START) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> EC ->.
    unfold BN_CTX_START_STACK, BN_CTX_START, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof WFS as (EL & BOK & EONE & (CE1 & CE2 & CE3 & CE4 & CE5 & CE6 & CE7 & CE8)).
    destruct (lib_state_cx_open [] bs m OW PL EA LS) as (Hs & IX & CV & LSC).
    apply (cx_view_some _ _ _ _ _ _ _ _ EC) in CV. destruct CV as (BC & LHs & CX & STK & HItems & HLinks). change BN_CTX_SZ with 72 in BC.
    pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
    set (c := st_ctx bs) in *.
    unfold ctx_cells in CX. rewrite CE1, CE2 in CX. change (Z.of_nat 0) with 0 in CX. change (Z.b2z false) with 0 in CX.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_CTX_start, bbind, bgetctx, bret, bunr, bmalloc, bfree_opt, bsetctx, bfree.
    cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
    rewrite CE1, CE2. cbn [Nat.eqb negb orb].
    unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (ac, ac + 72)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (CA8 : ac mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
    carve_frame 64%nat ST. do 9 step.
    chk ltac:(fun C => rewrite ?land64_small in C by (clear - CA0 CAC; lia); clear - C CA0 CAC; lia).
    step. step. rewrite (land7_wrap _ CA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_false.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_true.

    assert (SSZ : gx_ssize c = 0%nat \/ gx_ssize c = 32%nat) by (unfold BG_DEPTH in CE8; lia).
    assert (DEP : (length (gx_frames c) <= 32)%nat) by (unfold BG_DEPTH in CE8; destruct CE8 as [(_ & -> & _)|(_ & _ & ?)]; cbn; lia).
    assert (U48 : (gx_used c <= 48)%nat) by (unfold BN_CTX_POOL_SIZE in CE4; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (gx_frames c)))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (gx_ssize c))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (gx_used c))) by lia.
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
    -
      replace (length (gx_frames c) =? gx_ssize c)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      unfold stack_rep in STK. destruct (gx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & E1 & E2); rewrite E2 in KD; cbn in KD; lia].
      destruct STK as (HinI & SZ32 & stale & LEN & ARR). change FRAMES_SZ with 128 in HinI. unfold BN_CTX_START_FRAMES in SZ32, LEN.
      pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
      assert (NEI : qc <> q) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply idx_in_m; exact EI]).
      pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
      remember (map (fun k : nat => wz (Z.of_nat k)) (gx_frames c) ++ stale) as ws eqn:Ews.
      assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of MU with munch ?W0 _ _ =>
          apply (u32arr_transport bgusegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
      apply (munch_weaken _ [(bv_unsigned sp + -64, bv_unsigned sp); (ac, ac + 72); (IX, IX + 128)]%Z) in MU;
        [| intros x Hx; cbn [outside] in *; tauto].
      do 5 step.
      rewrite (unsigned_lit (Z.of_nat (length (gx_frames c)))) by lia. rewrite shl32_shr30 by lia.
      step. step.
      chkw ltac:(fun C => clear - C IA0 IAC KD DEP; lia).
      step. rewrite (snez_pos_wz IX) by (clear - IA0 IAC; lia).
      step. rewrite (seqz_pos (IX + 4 * Z.of_nat (length (gx_frames c)))) by (clear - IA0 IAC KD DEP; lia).
      step.
      chk ltac:(fun C => clear - C; lia).
      chkw ltac:(fun C => clear - C IA0 IAC; lia).
      step. rewrite (land3_wrap (IX + 4 * Z.of_nat (length (gx_frames c)))) by (clear - IA16; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      pose proof (u32arr_store_ok bgusegs _ IX ws (Z.of_nat (length (gx_frames c))) (wa (IX + 4 * Z.of_nat (length (gx_frames c)))) ARR ltac:(lia) eq_refl) as SOKW.
      step.
      pose proof (u32arr_write bgusegs _ IX ws (Z.of_nat (length (gx_frames c))) (Z_to_bv 64 (Z.of_nat (gx_used c))) ARR ltac:(lia)) as ARR2.
      store_done.
      step. do 7 step. step. release_frame FR ST (bv_unsigned sp). step.
      ihere. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      set (c' := mkGx (gx_items c) (gx_current c) (gx_pused c) (Some q) (gx_frames c ++ [gx_used c]) (gx_ssize c) (gx_used c) 0%nat false).
      assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ac, ac + 72); (IX, IX + 128)]).
      { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
        constructor; [right; left; exists (q, IX, 128); cbn; auto with zarith| constructor]. }
      assert (LKF : links mF Hs).
      { eapply (links_keep s OW LB m mF bs PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|]. constructor; [|constructor].
        right; right. exists q, IX, 128. split; [apply in_or_app; left; exact HinI|]. cbn [fst snd]. split; [lia|]. split; [lia|].
        fold c. intros Hq. eapply (ids_item_idx_neq bs q q); eauto using ids_m_nodup. }
      assert (LSF : lib_state (set_ctx c' bs) mF OW PL EA).
      { unfold lib_state. eapply (lib_state_cx_close [] bs (set_ctx c' bs) mF OW PL EA Hs IX); [| exact ND| reflexivity| reflexivity| reflexivity| reflexivity| | |].
        - eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSC| exact MU| exact WM| exact FROK|].
          constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
          constructor; [apply w_cx; [reflexivity| intros x Hx; right; right; exists q, IX; cbn in Hx; auto]| constructor].
        - apply st_wf_set_ctx; [exact WFS| reflexivity|]. unfold ctx_wf, c'. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
          split; [reflexivity|]. split; [reflexivity|]. split; [exact CE3|]. split; [exact CE4|]. split; [exact CE5|]. split; [exact CE6|].
          split; [rewrite <- app_assoc; apply BnMInv.nondecr_snoc; [exact CE7| lia]|].
          right. subst c'. cbn [gx_indexes gx_ssize gx_frames]. split; [unfold BG_DEPTH; lia|]. split; [discriminate|]. rewrite length_app. cbn [length]. unfold BG_DEPTH in *. lia.
        - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| subst c'; cbn [gx_indexes]; fold c; symmetry; exact EI].
        - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC|]. split; [exact LHs|]. split; [|split; [|split; [| exact LKF]]].
          + unfold ctx_cells, cur_addr, c'. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
            rewrite length_app. cbn [length]. replace (Z.of_nat (length (gx_frames c) + 1)) with (Z.of_nat (length (gx_frames c)) + 1) by lia.
            unfold cur_addr in CX. exact CX.
          + unfold stack_rep. subst c'. cbn [gx_indexes gx_ssize gx_frames]. split; [exact HinI|]. split; [exact SZ32|].
            destruct stale as [|x0 stale']; [exfalso; cbn in LEN; lia|]. exists stale'. split; [rewrite length_app; cbn [length] in *; unfold BN_CTX_START_FRAMES; lia|].
            rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
            rewrite Ews in ARR2. rewrite Nat2Z.id in ARR2. rewrite <- (length_map (fun k : nat => wz (Z.of_nat k)) (gx_frames c)) in ARR2 at 1.
            rewrite upd_app_mid in ARR2. exact ARR2.
          + apply item_blocks_set_ctx; [reflexivity| exact HItems]. }
      unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact ST|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [apply refs_stable_ow; [reflexivity| auto]|]. split; [reflexivity| intros q0 A0 n0 Hq0; exact Hq0].
    -
      replace (length (gx_frames c) =? gx_ssize c)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
      { replace (gx_ssize c =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [negb].
        ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      replace (gx_ssize c =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). cbn [negb].
      assert (EF : gx_frames c = []) by (destruct (gx_frames c); [reflexivity| cbn in KZ; lia]).
      unfold stack_rep in STK. destruct (gx_indexes c) as [q|] eqn:EI; [exfalso; destruct STK as (_ & E1 & _); unfold BN_CTX_START_FRAMES in E1; lia|].
      destruct STK as (-> & _ & _).
      do 8 step.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ac, ac + 72)]).
      { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
      assert (HEAP1 : RHEAP s (OW ++ LB) m1) by (exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)).
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      assert (LSC1 : lib_state_hc true [] bs m1 OW PL EA).
      { eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSC| exact MU| exact WM| exact FROK|].
        constructor; [apply w_stack; cbn; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor]. }
      assert (PM1 : links m1 Hs).
      { eapply (links_keep s OW LB m m1 bs PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      ihere. to_implM. cbn [embed]. change (4 * Z.of_nat BN_CTX_START_FRAMES) with (32 * 4).
      eapply (CRYPTO_malloc_array_walk HM) with (B := B) (lo := lo) (errv := errv) (num := 32) (size := 4);
        [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
        | exact (proj1 LSC1) | reflexivity | reflexivity | lia | lia | lia | reflexivity | ].
      intros pn st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & An & errv2
                      & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkA & BLK)).
      replace (ret_pc (Z_to_bv 64 1051856)) with (Z_to_bv 64 1051856) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AGP.
      apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros x Hx; left; cbn in Hx; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP) in CX; [| intros x Hx; right; right; exists (qc, ac, 72); split; [apply in_or_app; left; exact BC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] bs m3 OW PL EA).
      { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [exact LSC1| exact FROK| | exact HP|]; [lia|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (PM3 : links m3 Hs).
      { eapply (links_heap_pres bs OW); [exact LHs| exact HItems| | exact PM1| exact HP]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (ND3 : List.NoDup (map blk_id ((pn, An, 32 * 4) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
      assert (FRESH : ~ In pn (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
      assert (FRESHA : ~ In pn (all_ids bs PL EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 32 * 4 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (LH_disjoint _ _ _ (pn, An, 32 * 4) (q, A, n) HEAP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      set (OW1 := (pn, An, 32 * 4) :: OW).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSC3) as PARTS3.
      assert (LSC3' : lib_state_hc true [] bs m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSC3') as PARTS1.
      assert (LXP3 : lx_pres LB (bv_unsigned sp) (XW PL) m m3).
      { eapply lx_pres_trans; [exact LXP1|]. apply lx_pres_of_heap_pres.
        eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.

      destruct (u32s_exists 32 junkA) as (ws & LWS & EWS).
      { destruct BLK as [[[HL _] _] _]. cbn in HL. exact HL. }
      assert (ARR : u32arr bgusegs m3 An ws).
      { apply u8arr_of_rw_cells in BLK. destruct BLK as [B1 B2]. split; [rewrite EWS; exact B1|].
        rewrite LWS. replace (Z.of_nat (length junkA)) with (4 * Z.of_nat 32) in B2; [exact B2|].
        rewrite <- EWS, u32s_length, LWS. lia. }
      clear BLK.
      cbn [tbind embed interp fst snd]. unfold bret. cbn [ret tree_ops tbind embed interp fst snd]. apply implM_ret.
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ac, ac + 72); (An, An + 128)]%Z m3) as MU3.
      pose proof (wmono_refl bgusegs m3) as WM3.
      clear MU WM LSC LSC1 LSC3 HEAP1 AUX1 HLinks PM1.
      unfold MallocRep.wz in *.
      step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
      step. step. rewrite EF. cbn [length]. change (Z.of_nat 0) with 0. rewrite (zx32_small 0) by lia.
      step. step. if_true.
      do 4 step. step.
      eapply evt_cut.
      { eapply (CRYPTO_free_null_spec) with (lo := lo); rewrite ?ESP;
          [exact ST3| unfold GLOBALS_TOP; lia| lia| exact MI3| exact (proj1 LSC3')| reflexivity]. }
      rewrite ?ESP. post_call bgusegs m3.
      step. replace (sx32 (Z_to_bv 64 (Z.of_nat (length (gx_frames c))))) with (Z_to_bv 64 0) by (rewrite EF; reflexivity).
      do 7 step.
      chk ltac:(fun C => clear - C; lia).
      step. rewrite (snez_pos An) by (clear - BA0 BAC; lia).
      step. rewrite (seqz_pos An) by (clear - BA0 BAC; lia).
      step.
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?land64_small in C by (clear - BA0 BAC; lia); clear - C BA0 BAC; lia).
      step. rewrite (land3_wrap An) by (clear - BA16; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (u32arr_store_ok bgusegs m5 An ws 0 (wa An) ARR ltac:(lia) ltac:(f_equal; lia)) as SOKW.
      pose proof (u32arr_write bgusegs m5 An ws 0 (Z_to_bv 64 (Z.of_nat (gx_used c))) ARR ltac:(lia)) as ARR2.
      rewrite Z.mul_0_r, Z.add_0_r in ARR2. change (Z.to_nat 0) with 0%nat in ARR2.
      step. store_done.
      step. do 7 step. step. release_frame FR POST (bv_unsigned sp). step.
      apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch goal with |- context [set_ctx ?cc bs] => set (c' := cc) end.
      assert (HinN : In (pn, An, 32 * 4) OW1) by (left; reflexivity).
      assert (BC1 : In (qc, ac, 72) OW1) by (right; exact BC).
      assert (ND1 : List.NoDup (map blk_id OW1)) by (eapply (RH_nodup_l st1 OW1 LB m3); exact HEAP3).
      assert (HWL3 : Forall (w_lib bs OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (ac, ac + 72); (An, An + 128)]).
      { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
        constructor; [right; left; exists (pn, An, 32 * 4); cbn; auto with zarith| constructor]. }
      assert (HItems1 : item_blocks bs OW1 Hs) by (eapply item_blocks_ow; [exact HItems| intros b0 Hb0; right; exact Hb0]).
      assert (LKF : links mF Hs).
      { eapply (links_keep st1 OW1 LB m3 mF bs PL EA ac qc Hs); [exact HEAP3| exact PARTS1| exact EC| exact LHs| exact HItems1| exact PM3| exact MU3| exact WM3|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|]. constructor; [|constructor].
        right; right. exists pn, An, (32 * 4). split; [left; reflexivity|]. cbn [fst snd]. split; [lia|]. split; [lia|].
        fold c. intros Hq. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply item_in_m. exact Hq. }
      assert (LSF : lib_state (set_ctx c' bs) mF OW1 PL EA).
      { unfold lib_state. eapply (lib_state_cx_close [] bs (set_ctx c' bs) mF OW1 PL EA Hs An); [| exact ND1| reflexivity| reflexivity| reflexivity| reflexivity| | |].
        - eapply (lib_state_frame st1 LB (bv_unsigned sp) B); [exact HEAP3| exact LSC3'| exact MU3| exact WM3| exact FROK|].
          constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB bs PL EA (bv_unsigned sp) true [] _ pn An (32 * 4)); [left; reflexivity| exact FRESHA| cbn; lia| cbn; lia].
        - apply st_wf_set_ctx; [exact WFS| reflexivity|]. unfold ctx_wf, c'. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many app].
          split; [reflexivity|]. split; [reflexivity|]. split; [exact CE3|]. split; [exact CE4|]. split; [exact CE5|]. split; [exact CE6|].
          split; [cbn; lia|]. right. split; [reflexivity|]. split; [discriminate|]. cbn [length]. unfold BG_DEPTH. lia.
        - eapply (ids_ok_set_ctx_new_idx bs PL EA c' pn); [exact IDS| reflexivity| exact EI| reflexivity| exact FRESHA].
        - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC1|]. split; [exact LHs|]. split; [|split; [|split; [| exact LKF]]].
          + unfold ctx_cells, cur_addr, c'. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z app length]. unfold cur_addr in CX. exact CX.
          + unfold stack_rep, c'. cbn [gx_indexes gx_ssize gx_frames app]. split; [exact HinN|]. split; [reflexivity|].
            destruct ws as [|w0 ws']; [cbn in LWS; lia|]. exists ws'. split; [cbn [length] in *; unfold BN_CTX_START_FRAMES; lia|]. cbn [map app Arr.upd] in *. exact ARR2.
          + apply item_blocks_set_ctx; [reflexivity| exact HItems1]. }
      unfold bn_post. do 15 eexists. exists mF, OW1, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ HEAP3 PARTS1 FROK MU3 WM3 HWL3 CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ B HEAP3 PARTS1 FROK AUX3 MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact POST|].
      split; [unfold LX_ERRNO, RATP; exact ERR3|]. split; [exact MI0|].
      split. { eapply lx_pres_trans; [exact LXP3|]. apply (seg_lx_pres st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ HEAP3 PARTS1 FROK MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA|]. split; [exact SO|].
      split. { apply refs_stable_ow; [reflexivity|]. intros q H0 _ Hq. right. exact Hq. }
      split; [reflexivity|]. intros q0 A0 n0 Hq0. right. exact Hq0.
  Qed.
End Proofs.
End WithCeiling0.
