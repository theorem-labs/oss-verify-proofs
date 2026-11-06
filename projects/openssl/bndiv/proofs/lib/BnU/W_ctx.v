(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Drv_facts.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface BnUAlign BnUKit W_crypto.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
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

Lemma pool_mem_heap_pres : forall (OW : list block) L SP m m' ls H Cu,
  match cx_head (ls_ctx ls) with Some p => In (p, H, 400) OW | None => H = 0 end -> (forall b, In b OW -> In b L) ->
  pool_mem m H Cu (ls_ctx ls) -> rheap_pres L SP m m' -> pool_mem m' H Cu (ls_ctx ls).
Proof.
  intros OW L SP m m' ls H Cu HH HI PM HP. unfold pool_mem in *. destruct (cx_head (ls_ctx ls)) as [p|]; [|exact PM].
  destruct PM as [Hpn Hcur]. split; [|exact Hcur].
  eapply rw_cells_agree; [apply agree_of_heap_pres; exact HP| exact Hpn|]. intros x Hx. cbn in Hx.
  right; right. exists (p, H, 400). split; [apply HI; exact HH|]. cbn [blk_addr blk_size fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma pool_mem_keep : forall s OW LB m m' ls AD EA H Cu W,
  RHEAP s (OW ++ LB) m -> ids_ok ls AD EA -> ad_blocks OW AD ->
  match cx_head (ls_ctx ls) with Some p => In (p, H, 400) OW | None => H = 0 end ->
  pool_mem m H Cu (ls_ctx ls) -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv \/ (ad_ctx AD <= fst iv /\ snd iv <= ad_ctx AD + 72)
                            \/ (exists q A n, In (q, A, n) (OW ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> cx_head (ls_ctx ls))) W ->
  pool_mem m' H Cu (ls_ctx ls).
Proof.
  intros s OW LB m m' ls AD EA H Cu W HEAP IDS ADB HH PM MU WM HW. unfold pool_mem in *.
  destruct (cx_head (ls_ctx ls)) as [p|] eqn:Eh; [|exact PM]. destruct PM as [Hpn Hcur]. split; [|exact Hcur].
  eapply rw_cells_transport; [exact Hpn| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HH) as (_ & _ & _ & HC & _).
  destruct ADB as (_ & _ & _ & _ & _ & BC).
  assert (NEc : ad_pc AD <> p) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply head_in_m; exact Eh]).
  pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HH NEc) as DJc. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  cbn [fst snd] in Hiv. destruct Hiv as [Hs|[Hc|(q & A & n & Hq & H1 & H2 & NE)]]; [lia| lia|].
  assert (NEq : q <> p) by congruence.
  pose proof (LH_disjoint _ _ _ (q, A, n) (p, H, 400) HEAP Hq ltac:(apply in_or_app; left; exact HH) NEq) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

Definition BN_CTX_START : Z := 0x1151f0.
Definition BN_CTX_START_STACK : Z := 64 + 8400.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_CTX_start_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_CTX_START_STACK -> tp = wz RATP -> a0 = wz (ad_ctx AD) ->
    implM usegs (interp (embed (BN_CTX_start (tree_ops bptr) ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun _ _ OW' _ => forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_START) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) -> ->.
    unfold BN_CTX_START_STACK, BN_CTX_START, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof SOK as (_ & _ & _ & _ & _ & POK & (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7)).
    destruct (lib_state_cx_open [] ls m OW AD EA LS) as (H & Cu & IX & CX & STK & PM & HH & LSC).
    pose proof ADB as (_ & _ & _ & _ & _ & BC). pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
    set (c := ls_ctx ls) in *.
    unfold ctx_cells in CX. rewrite CK7 in CX. change (Z.of_nat 0) with 0 in CX.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    unfold BN_CTX_start, bbind, bgetctx, bret, bunr, bmalloc, bfree_opt, bsetctx, bfree.
    cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
    rewrite CK7. cbn [Nat.eqb negb orb].
    unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CA8 : ad_ctx AD mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
    carve_frame 64%nat ST. do 9 step.
    chk ltac:(fun C => clear - C CA0 CAC; lia).
    step. step. rewrite (land7_wrap _ CA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_false.
    step.
    destruct (cx_too_many c) eqn:ETM.
    { ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    cbn [Z.b2z] in *. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_true.
    (* [comment removed for export] *)
    assert (SSZ : cx_ssize c = 0%nat \/ cx_ssize c = 32%nat).
    { unfold stack_rep in STK. destruct (cx_indexes c); [right; exact (proj1 (proj2 STK))| left; exact (proj1 (proj2 STK))]. }
    assert (DEP : (length (cx_frames c) <= 32)%nat) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (cx_frames c)))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_ssize c))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_used c))) by lia.
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
    - (* [comment removed for export] *)
      replace (length (cx_frames c) =? cx_ssize c)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      unfold stack_rep in STK. destruct (cx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & E1 & E2); rewrite E2 in KD; cbn in KD; lia].
      destruct STK as (HinI & SZ32 & stale & LEN & ARR).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
      assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply idx_in_m; exact EI]).
      pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
      remember (map (fun k : nat => wz (Z.of_nat k)) (cx_frames c) ++ stale) as ws eqn:Ews.
      assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of MU with munch ?W0 _ _ =>
          apply (u32arr_transport usegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
      apply (munch_weaken _ [(bv_unsigned sp + -64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (IX, IX + 128)]%Z) in MU;
        [| intros x Hx; cbn [outside] in *; tauto].
      do 5 step.
      rewrite (unsigned_lit (Z.of_nat (length (cx_frames c)))) by lia. rewrite shl32_shr30 by lia.
      step. step.
      chkw ltac:(fun C => clear - C IA0 IAC KD DEP; lia).
      step. rewrite (snez_pos_wz IX) by (clear - IA0 IAC; lia).
      step. rewrite (seqz_pos (IX + 4 * Z.of_nat (length (cx_frames c)))) by (clear - IA0 IAC KD DEP; lia).
      step.
      chk ltac:(fun C => clear - C; lia).
      chkw ltac:(fun C => clear - C IA0 IAC; lia).
      step. rewrite (land3_wrap (IX + 4 * Z.of_nat (length (cx_frames c)))) by (clear - IA16; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      pose proof (u32arr_store_ok usegs _ IX ws (Z.of_nat (length (cx_frames c))) (wa (IX + 4 * Z.of_nat (length (cx_frames c)))) ARR ltac:(lia) eq_refl) as SOKW.
      step.
      pose proof (u32arr_write usegs _ IX ws (Z.of_nat (length (cx_frames c))) (Z_to_bv 64 (Z.of_nat (cx_used c))) ARR ltac:(lia)) as ARR2.
      store_done.
      step. do 7 step. step. release_frame FR ST (bv_unsigned sp). step.
      ihere. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      set (c' := {| cx_head := cx_head c; cx_current := cx_current c; cx_vals := cx_vals c; cx_pused := cx_pused c; cx_psize := cx_psize c;
                    cx_indexes := Some q; cx_frames := cx_frames c ++ [cx_used c]; cx_ssize := cx_ssize c; cx_used := cx_used c;
                    cx_err_stack := 0; cx_too_many := false |}).
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (IX, IX + 128)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith|].
        constructor; [right; exists (q, IX, 128); cbn; auto with zarith| constructor]. }
      assert (LSF : lib_state (set_ctx c' ls) mF OW AD EA).
      { unfold lib_state. eapply (lib_state_cx_close [] ls mF OW AD EA c' H Cu IX); [| exact ND| reflexivity| reflexivity| exact HH| | | | |].
        - eapply (lib_state_frame s LB); [exact HEAP| exact LSC| exact MU| exact WM|].
          constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]|].
          constructor; [apply w_cx; [reflexivity| intros x Hx; right; right; exists q, IX; cbn in Hx; auto]| constructor].
        - unfold ctx_cells, c'. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z].
          rewrite length_app. cbn [length]. replace (Z.of_nat (length (cx_frames c) + 1)) with (Z.of_nat (length (cx_frames c)) + 1) by lia. exact CX.
        - unfold stack_rep, c'. cbn [cx_indexes cx_ssize cx_frames]. split; [exact HinI|]. split; [exact SZ32|].
          destruct stale as [|x0 stale']; [exfalso; cbn in LEN; lia|]. exists stale'. split; [rewrite length_app; cbn [length] in *; lia|].
          rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
          rewrite Ews in ARR2. rewrite Nat2Z.id in ARR2. rewrite <- (length_map (fun k : nat => wz (Z.of_nat k)) (cx_frames c)) in ARR2 at 1.
          rewrite upd_app_mid in ARR2. exact ARR2.
        - eapply (pool_mem_keep s OW LB m mF ls AD EA H Cu); [exact HEAP| exact IDS| exact ADB| exact HH| exact PM| exact MU| exact WM|].
          constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
          right; right. exists q, IX, 128. split; [apply in_or_app; left; exact HinI|]. cbn [fst snd]. split; [lia|]. split; [lia|].
          fold c. intros E. destruct (cx_head c) as [ph|] eqn:Eh; [|discriminate]. injection E as ->.
          eapply (ids_head_idx_neq ls ph ph); eauto using ids_m_nodup.
        - unfold ctx_okm, c'. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack].
          split; [exact CK1|]. split; [exact CK2|]. split; [exact CK3|]. split; [rewrite <- app_assoc; apply nondecr_snoc; [exact CK4| lia]|].
          split; [rewrite length_app; cbn [length]; lia|]. split; [exact CK6| reflexivity].
        - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| symmetry; exact EI| reflexivity]. }
      unfold bn_post. do 15 eexists. exists mF, OW, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia|]. split; [exact ST|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros r' a' HA'; exact HA'| intros q0 A0 n0 Hq0; exact Hq0].
    - (* [comment removed for export] *)
      replace (length (cx_frames c) =? cx_ssize c)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
      { replace (cx_ssize c =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [negb].
        ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      replace (cx_ssize c =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). cbn [negb].
      assert (EF : cx_frames c = []) by (destruct (cx_frames c); [reflexivity| cbn in KZ; lia]).
      unfold stack_rep in STK. destruct (cx_indexes c) as [q|] eqn:EI; [exfalso; destruct STK as (_ & E1 & _); lia|].
      destruct STK as (-> & _ & _).
      do 8 step.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
      assert (HEAP1 : RHEAP s (OW ++ LB) m1) by (exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)).
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) LIBW_bn m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      assert (LSC1 : lib_state_hc true [] ls m1 OW AD EA).
      { eapply (lib_state_frame s LB); [exact HEAP| exact LSC| exact MU| exact WM|].
        constructor; [apply w_stack; cbn; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor]. }
      assert (PM1 : pool_mem m1 H Cu c).
      { eapply (pool_mem_keep s OW LB m m1 ls AD EA H Cu); [exact HEAP| exact IDS| exact ADB| exact HH| exact PM| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia| constructor]. }
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
      replace (ret_pc (Z_to_bv 64 1135276)) with (Z_to_bv 64 1135276) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AGP.
      apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros x Hx; left; cbn in Hx; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP) in CX; [| intros x Hx; right; right; exists (ad_pc AD, ad_ctx AD, 72); split; [apply in_or_app; left; exact BC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] ls m3 OW AD EA).
      { eapply lib_state_h_heap_pres; [exact LSC1| exact HP|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (PM3 : pool_mem m3 H Cu c).
      { eapply (pool_mem_heap_pres OW); [exact HH| | exact PM1| exact HP]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (ND3 : List.NoDup (map blk_id ((pn, An, 32 * 4) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
      assert (FRESH : ~ In pn (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
      assert (FRESHA : ~ In pn (all_ids ls AD EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 32 * 4 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (LH_disjoint _ _ _ (pn, An, 32 * 4) (q, A, n) HEAP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      set (OW1 := (pn, An, 32 * 4) :: OW).
      assert (LSC3' : lib_state_hc true [] ls m3 OW1 AD EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      assert (LXP3 : lx_pres LB (bv_unsigned sp) LIBW_bn m m3).
      { eapply lx_pres_trans; [exact LXP1|]. apply lx_pres_of_heap_pres.
        eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      unfold LX_ERRNO, RATP in ERR3. change (3353240 - 164) with 3353076 in ERR3.
      (* [comment removed for export] *)
      destruct (u32s_exists 32 junkA) as (ws & LWS & EWS).
      { destruct BLK as [[[HL _] _] _]. cbn in HL. exact HL. }
      assert (ARR : u32arr usegs m3 An ws).
      { apply u8arr_of_rw_cells in BLK. destruct BLK as [B1 B2]. split; [rewrite EWS; exact B1|].
        rewrite LWS. replace (Z.of_nat (length junkA)) with (4 * Z.of_nat 32) in B2; [exact B2|].
        rewrite <- EWS, u32s_length, LWS. lia. }
      clear BLK.
      cbn [tbind embed interp fst snd]. unfold bret. cbn [ret tree_ops tbind embed interp fst snd]. apply implM_ret.
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 128)]%Z m3) as MU3.
      pose proof (wmono_refl usegs m3) as WM3.
      clear MU WM LSC LSC1 LSC3 HEAP1 AUX1 PM PM1.
      unfold MallocRep.wz in *.
      step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
      step. step. rewrite EF. cbn [length]. change (Z.of_nat 0) with 0. rewrite (zx32_small 0) by lia.
      step. step. if_true.
      do 4 step. step.
      eapply evt_cut.
      { eapply (CRYPTO_free_null_spec) with (lo := lo); rewrite ?ESP;
          [exact ST3| unfold GLOBALS_TOP; lia| lia| exact MI3| exact (proj1 LSC3')| reflexivity]. }
      rewrite ?ESP. post_call usegs m3.
      step. replace (sx32 (Z_to_bv 64 (Z.of_nat (length (cx_frames c))))) with (Z_to_bv 64 0) by (rewrite EF; reflexivity).
      do 7 step.
      chk ltac:(fun C => clear - C; lia).
      step. rewrite (snez_pos An) by (clear - BA0 BAC; lia).
      step. rewrite (seqz_pos An) by (clear - BA0 BAC; lia).
      step.
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => clear - C BA0 BAC; lia).
      step. rewrite (land3_wrap An) by (clear - BA16; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (u32arr_store_ok usegs m5 An ws 0 (wa An) ARR ltac:(lia) ltac:(f_equal; lia)) as SOKW.
      pose proof (u32arr_write usegs m5 An ws 0 (Z_to_bv 64 (Z.of_nat (cx_used c))) ARR ltac:(lia)) as ARR2.
      rewrite Z.mul_0_r, Z.add_0_r in ARR2. change (Z.to_nat 0) with 0%nat in ARR2.
      step. store_done.
      step. do 7 step. step. release_frame FR POST (bv_unsigned sp). step.
      apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch goal with |- context [set_ctx ?cc ls] => set (c' := cc) end.
      assert (HinN : In (pn, An, 32 * 4) OW1) by (left; reflexivity).
      assert (BC1 : In (ad_pc AD, ad_ctx AD, 72) OW1) by (right; exact BC).
      assert (ND1 : List.NoDup (map blk_id OW1)) by (eapply (RH_nodup_l st1 OW1 LB m3); exact HEAP3).
      assert (HH1 : match cx_head c' with Some p => In (p, H, 400) OW1 | None => H = 0 end).
      { subst c'. cbn [cx_head]. fold c in HH. destruct (cx_head c); [right; exact HH| exact HH]. }
      assert (HWL3 : Forall (w_lib OW1 lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 128)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith|].
        constructor; [right; exists (pn, An, 32 * 4); cbn; auto with zarith| constructor]. }
      assert (LSF : lib_state (set_ctx c' ls) mF OW1 AD EA).
      { unfold lib_state. eapply (lib_state_cx_close [] ls mF OW1 AD EA c' H Cu An); [| exact ND1| reflexivity| reflexivity| exact HH1| | | | |].
        - eapply (lib_state_frame st1 LB); [exact HEAP3| exact LSC3'| exact MU3| exact WM3|].
          constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; cbn in Hx; lia]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB ls AD EA true [] _ pn An (32 * 4)); [left; reflexivity| exact FRESHA| cbn; lia| cbn; lia].
        - unfold ctx_cells, c'. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z app length]. exact CX.
        - unfold stack_rep, c'. cbn [cx_indexes cx_ssize cx_frames app]. split; [exact HinN|]. split; [reflexivity|].
          destruct ws as [|w0 ws']; [cbn in LWS; lia|]. exists ws'. split; [cbn [length] in *; lia|]. cbn [map app Arr.upd] in *. exact ARR2.
        - eapply (pool_mem_keep st1 OW1 LB m3 mF ls AD EA H Cu); [exact HEAP3| exact IDS| | | exact PM3| exact MU3| exact WM3|].
          + destruct ADB as (B1 & B2 & B3 & B4 & B5 & B6). unfold ad_blocks. repeat split; right; assumption.
          + fold c. destruct (cx_head c); [right; exact HH| exact HH].
          + constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
            right; right. exists pn, An, (32 * 4). split; [left; reflexivity|]. cbn [fst snd]. split; [lia|]. split; [lia|].
            fold c. intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply head_in_m. symmetry. exact E.
        - unfold ctx_okm, c'. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack app length].
          split; [exact CK1|]. split; [exact CK2|]. split; [exact CK3|]. split; [cbn; lia|].
          split; [unfold BN_CTX_START_FRAMES; lia|]. split; [exact CK6| reflexivity].
        - eapply (ids_ok_set_ctx_new_idx ls AD EA c' pn); [exact IDS| reflexivity| reflexivity| exact EI| reflexivity| exact FRESHA]. }
      unfold bn_post. do 15 eexists. exists mF, OW1, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap st1 OW1 LB m3 mF _ lo _ HEAP3 MU3 WM3 HWL3 CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv st1 OW1 LB m3 mF _ lo _ B HEAP3 AUX3 MU3 WM3 HWL3 SPB); unfold GLOBALS_TOP; lia|]. split; [exact POST|].
      split; [unfold LX_ERRNO, RATP; exact ERR3|]. split; [exact MI0|].
      split. { eapply lx_pres_trans; [exact LXP3|]. apply (seg_lx_pres st1 OW1 LB m3 mF _ lo _ _ HEAP3 MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA|]. split; [exact SO|].
      split. { intros r' a' HA'. destruct r' as [| | | | |i]; cbn [ref_at] in HA' |- *; try exact HA'.
               destruct HA' as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [exact E0|]. split; [right; exact I0| exact R0]. }
      intros q0 A0 n0 Hq0. right. exact Hq0.
  Qed.
End Proofs.
End WithCeiling0.
