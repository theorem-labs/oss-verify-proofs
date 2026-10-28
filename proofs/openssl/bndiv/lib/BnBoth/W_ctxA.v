(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require W_ctx.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2408180 => 2
  | 2408184 => 1
  | 2408188 => 2
  | 2408264 => 2
  | 2408516 => 1
  | 2408520 => 1
  | 2408524 => 2
  | 2408644 => 2
  | 2408648 => 1
  | 2408652 => 1
  | 2408656 => 1
  | 2408660 => 2
  | 2408664 => 2
  | 2408668 => 1
  | 2408672 => 2
  | 2408760 => 2
  | 2409064 => 1
  | 2409068 => 2
  | 2409116 => 2
  | 2409204 => 2
  | 2409208 => 1
  | 2409212 => 1
  | 2409216 => 1
  | 2409220 => 2
  | 2409224 => 2
  | 2409228 => 1
  | 2409232 => 2
  | 2409368 => 2
  | 2409372 => 1
  | 2409376 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_CTX_START : Z := 0x24beb8.
Definition BN_CTX_START_STACK : Z := 112 + CRYPTO_MALLOC_ARRAY_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_cs_marr := (E_BN_CTX_start_249b7c : uk_call BN_CTX_START 0x24c01c CRYPTO_MALLOC_ARRAY).
Local Notation E_cs_free := (E_BN_CTX_start_249bd0 : uk_call BN_CTX_START 0x24c07c CRYPTO_FREE).

(* [comment removed for export] *)
Lemma pool_mem_agree : forall (OW : list block) L SP (P : Z -> Prop) m m' ls H Cu,
  match cx_head (ls_ctx ls) with Some p => In (p, H, 400) OW | None => H = 0 end -> (forall b, In b OW -> In b L) ->
  pool_mem m H Cu (ls_ctx ls) -> agree_on P m m' -> (forall x, aclient_addr L SP x -> (forall q, cx_head (ls_ctx ls) = Some q -> H + 384 <= x < H + 400) -> P x) ->
  pool_mem m' H Cu (ls_ctx ls).
Proof.
  intros OW L SP P m m' ls H Cu HH HI PM HP HPx. unfold pool_mem in *. destruct (cx_head (ls_ctx ls)) as [p|]; [|exact PM].
  destruct PM as [Hpn Hcur]. split; [|exact Hcur].
  eapply rw_cells_agree; [exact HP| exact Hpn|]. intros x Hx. cbn in Hx. apply HPx; [|intros q _; lia].
  right; right. exists (p, H, 400). split; [apply HI; exact HH|]. cbn [blk_addr blk_size fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma pool_mem_keep : forall Σ OW LB m m' ls AD EA H Cu W,
  AHEAP Σ OW LB m -> ids_ok ls AD EA -> ad_blocks OW AD ->
  match cx_head (ls_ctx ls) with Some p => In (p, H, 400) OW | None => H = 0 end ->
  pool_mem m H Cu (ls_ctx ls) -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => ACEIL <= fst iv \/ (ad_ctx AD <= fst iv /\ snd iv <= ad_ctx AD + 72)
                            \/ (exists q A n, In (q, A, n) (OW ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> cx_head (ls_ctx ls))) W ->
  pool_mem m' H Cu (ls_ctx ls).
Proof.
  intros Σ OW LB m m' ls AD EA H Cu W HEAP IDS ADB HH PM MU WM HW. unfold pool_mem in *.
  destruct (cx_head (ls_ctx ls)) as [p|] eqn:Eh; [|exact PM]. destruct PM as [Hpn Hcur]. split; [|exact Hcur].
  eapply rw_cells_transport; [exact Hpn| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HH) as (_ & _ & _ & HC & _).
  destruct ADB as (_ & _ & _ & _ & _ & BC).
  assert (NEc : ad_pc AD <> p) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply head_in_m; exact Eh]).
  pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HH NEc) as DJc. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  cbn [fst snd] in Hiv. destruct Hiv as [Hs|[Hc|(q & A & n & Hq & H1 & H2 & NE)]]; [lia| lia|].
  assert (NEq : q <> p) by congruence.
  pose proof (AH_disjoint_gen _ _ _ _ (q, A, n) (p, H, 400) HEAP Hq ltac:(apply in_or_app; left; exact HH) NEq) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

Lemma BN_CTX_start_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_CTX_START_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_START (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> a0 = wz (ad_ctx AD) ->
  implA (BN_CTX_start (tree_ops bptr) ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
              (fun _ _ OW' _ => forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_START) fc None m (seg_rom bsegs)).
Proof.
  intros until ras. intros (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) UW CTX -> ->.
  unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_CTX_START, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof SOK as (_ & _ & _ & _ & _ & POK & (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7)).
  destruct (lib_state_cx_open [] ls m OW AD EA LS) as (H & Cu & IX & CX & STK & PM & HH & LSC).
  pose proof ADB as (_ & _ & _ & _ & _ & BC). pose proof (AH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
  set (c := ls_ctx ls) in *.
  unfold ctx_cells in CX. rewrite CK7 in CX. change (Z.of_nat 0) with 0 in CX.
  assert (INC : In (ad_pc AD, ad_ctx AD, 72) (OW ++ LB)) by (apply in_or_app; left; exact BC).
  pose proof (AH_acc_in _ _ _ _ (ad_pc AD, ad_ctx AD, 72) (ad_ctx AD) 72 HEAP INC ltac:(cbn; lia) ltac:(cbn; lia)) as ACC.
  assert (AL : ad_ctx AD mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold BN_CTX_start, bbind, bgetctx, bret, bunr, bmalloc, bfree_opt, bsetctx, bfree.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
  rewrite CK7. cbn [Nat.eqb negb orb].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
  { pose proof (AH_offsh _ _ _ _ (ad_pc AD, ad_ctx AD, 72) HEAP INC) as O. cbn [blk_addr blk_size fst snd] in O.
    cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  apply implA_from_evt.
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 (ub; step). do 3 (ub; step). do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_false.
  do 3 (ub; step). ub; shl. ub; chk0.
  ub; step.
  destruct (cx_too_many c) eqn:ETM.
  { apply evt_done. apply implA_unr. }
  cbn [Z.b2z] in *. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_true.
  (* [comment removed for export] *)
  assert (SSZ : cx_ssize c = 0%nat \/ cx_ssize c = 32%nat).
  { unfold stack_rep in STK. destruct (cx_indexes c); [right; exact (proj1 (proj2 STK))| left; exact (proj1 (proj2 STK))]. }
  assert (DEP : (length (cx_frames c) <= 32)%nat) by lia.
  do 3 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_used c))) by lia. ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (cx_frames c)))) by lia. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_ssize c))) by lia.
  do 2 (ub; step). rewrite (unsigned_lit (ad_ctx AD + 32)) by (unfold BnHeapA.ACEIL in *; lia).
  ub; step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
  - (* [comment removed for export] *)
    replace (length (cx_frames c) =? cx_ssize c)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold stack_rep in STK. destruct (cx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & E1 & E2); rewrite E2 in KD; cbn in KD; lia].
    destruct STK as (HinI & SZ32 & stale & LEN & ARR).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
    assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply idx_in_m; exact EI]).
    pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
    assert (INI : In (q, IX, 128) (OW ++ LB)) by (apply in_or_app; left; exact HinI).
    pose proof (AH_acc_in _ _ _ _ (q, IX, 128) IX 128 HEAP INI ltac:(cbn; lia) ltac:(cbn; lia)) as ACCI.
    assert (ALI : IX mod 8 = 0) by (clear - IA16; Z.div_mod_to_equations; lia).
    pose proof (AH_offsh _ _ _ _ (q, IX, 128) HEAP INI) as OI. cbn [blk_addr blk_size fst snd] in OI. unfold SHLO, SHHI in OI.
    remember (map (fun k : nat => wz (Z.of_nat k)) (cx_frames c) ++ stale) as ws eqn:Ews.
    assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of MU with munch ?W0 _ _ =>
        apply (u32arr_transport bsegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
    apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (IX, IX + 128)]%Z) in MU;
      [| intros x Hx; cbn [outside] in *; tauto].
    clear OFF.
    assert (OFF : offshW [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (IX, IX + 128)]).
    { pose proof (AH_offsh _ _ _ _ (ad_pc AD, ad_ctx AD, 72) HEAP INC) as O. cbn [blk_addr blk_size fst snd] in O.
      cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
    ub; step.
    ub; shl. ub; chk0. ub; shl. ub; step. ub; chk0.
    ub; step. unfold MallocRep.wz at 1. rewrite (zx32_small (Z.of_nat (length (cx_frames c)))) by lia.
    do 2 (ub; step). rewrite ?(unsigned_lit (Z.of_nat (length (cx_frames c)))) by lia.
    replace (Z.shiftl (Z.of_nat (length (cx_frames c))) 2) with (4 * Z.of_nat (length (cx_frames c))) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ub; step. ub; step.
    do 2 (ub; step). ub; shl. ub; chk0.
    pose proof (u32arr_store_ok bsegs _ IX ws (Z.of_nat (length (cx_frames c))) (wa (IX + 4 * Z.of_nat (length (cx_frames c)))) ARR ltac:(lia) eq_refl) as SOKW.
    ub; step.
    pose proof (u32arr_write bsegs _ IX ws (Z.of_nat (length (cx_frames c))) (Z_to_bv 64 (Z.of_nat (cx_used c))) ARR ltac:(lia)) as ARR2.
    store_done.
    ub; step. do 13 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    apply evt_done. apply implA_ret.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
    set (c' := {| cx_head := cx_head c; cx_current := cx_current c; cx_vals := cx_vals c; cx_pused := cx_pused c; cx_psize := cx_psize c;
                  cx_indexes := Some q; cx_frames := cx_frames c ++ [cx_used c]; cx_ssize := cx_ssize c; cx_used := cx_used c;
                  cx_err_stack := 0; cx_too_many := false |}).
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (IX, IX + 128)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith|].
      constructor; [right; exists (q, IX, 128); cbn; auto with zarith| constructor]. }
    assert (LSF : lib_state (set_ctx c' ls) mF OW AD EA).
    { unfold lib_state. eapply (lib_state_cx_close [] ls mF OW AD EA c' H Cu IX); [| exact ND| reflexivity| reflexivity| exact HH| | | | |].
      - eapply (lib_state_frame Σ LB); [exact HEAP| exact LSC| exact MU| exact WM|].
        constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; right; right; exists q, IX; cbn in Hx; auto]| constructor].
      - unfold ctx_cells, c'. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z].
        rewrite length_app. cbn [length]. replace (Z.of_nat (length (cx_frames c) + 1)) with (Z.of_nat (length (cx_frames c)) + 1) by lia. exact CX.
      - unfold stack_rep, c'. cbn [cx_indexes cx_ssize cx_frames]. split; [exact HinI|]. split; [exact SZ32|].
        destruct stale as [|x0 stale']; [exfalso; cbn in LEN; lia|]. exists stale'. split; [rewrite length_app; cbn [length] in *; lia|].
        rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
        rewrite Ews in ARR2. rewrite Nat2Z.id in ARR2. rewrite <- (length_map (fun k : nat => wz (Z.of_nat k)) (cx_frames c)) in ARR2 at 1.
        rewrite W_ctx.upd_app_mid in ARR2. exact ARR2.
      - eapply (pool_mem_keep Σ OW LB m mF ls AD EA H Cu); [exact HEAP| exact IDS| exact ADB| exact HH| exact PM| exact MU| exact WM|].
        constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
        right; right. exists q, IX, 128. split; [apply in_or_app; left; exact HinI|]. cbn [fst snd]. split; [lia|]. split; [lia|].
        fold c. intros E. destruct (cx_head c) as [ph|] eqn:Eh; [|discriminate]. injection E as ->.
        eapply (ids_head_idx_neq ls ph ph); eauto using ids_m_nodup.
      - unfold ctx_okm, c'. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack].
        split; [exact CK1|]. split; [exact CK2|]. split; [exact CK3|]. split; [rewrite <- app_assoc; apply nondecr_snoc; [exact CK4| lia]|].
        split; [rewrite length_app; cbn [length]; lia|]. split; [exact CK6| reflexivity].
      - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| symmetry; exact EI| reflexivity]. }
    unfold bn_postA. do 17 eexists. exists mF, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [unfold MC; lia|].
    split. { unfold cnt_eq, cnt_bal. rewrite (blocks_of_set_ctx c' ls); [reflexivity | reflexivity | reflexivity | symmetry; exact EI]. }
    split; [intros r' a' HA'; exact HA'| intros q0 A0 n0 Hq0; exact Hq0].
  - (* [comment removed for export] *)
    replace (length (cx_frames c) =? cx_ssize c)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    ub; step.
    ub; step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
    { replace (cx_ssize c =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [negb].
      apply evt_done. apply implA_unr. }
    replace (cx_ssize c =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). cbn [negb].
    assert (EF : cx_frames c = []) by (destruct (cx_frames c); [reflexivity| cbn in KZ; lia]).
    unfold stack_rep in STK. destruct (cx_indexes c) as [q|] eqn:EI; [exfalso; destruct STK as (_ & E1 & _); lia|].
    destruct STK as (-> & _ & _).
    do 2 (ub; step). do 6 (ub; step).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
    assert (HEAP1 : AHEAP Σ OW LB m1) by (exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))).
    assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))).
    assert (LSC1 : lib_state_hc true [] ls m1 OW AD EA).
    { eapply (lib_state_frame Σ LB); [exact HEAP| exact LSC| exact MU| exact WM|].
      constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
      constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor]. }
    assert (PM1 : pool_mem m1 H Cu c).
    { eapply (pool_mem_keep Σ OW LB m m1 ls AD EA H Cu); [exact HEAP| exact IDS| exact ADB| exact HH| exact PM| exact MU| exact WM|].
      constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; lia| constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [C8 (Z_to_bv 64 (Z.of_nat (cx_used c))); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                              (bv_unsigned ra) (bv_unsigned s0) ras);
        [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
      - rewrite !Z_to_bv_bv_unsigned. exact FR.
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia |]. constructor; [|constructor].
        cbn. unfold BnHeapA.ACEIL in *. lia. }
    apply evt_done. change (4 * Z.of_nat BN_CTX_START_FRAMES) with (32 * 4).
    eapply (CRYPTO_malloc_array_walkA) with (num := 32) (size := 4) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
    + rewrite ESP. unfold USTACK_TOP. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact (proj1 LSC1).
    + pose proof (cnt_ok_live ls OW LB OW 0 SOK CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
    + exact CRED.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cs_marr CTX).
    + intros pn Σ1 ms1 FRESH PO. unfold calloc_postA in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & (junkA & BLK)).
      rewrite (ret_pc_even 2408476) by lia.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in CX; [| intros x Hx; right; right; exists (ad_pc AD, ad_ctx AD, 72); split; [exact INC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] ls m3 OW AD EA).
      { eapply lib_state_h_heap_pres; [exact LSC1| exact AG3|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (PM3 : pool_mem m3 H Cu c).
      { eapply (pool_mem_agree OW (OW ++ LB) (bv_unsigned sp + -112)); [exact HH| | exact PM1| exact AG3|].
        - intros b0 Hb0. apply in_or_app. left. exact Hb0.
        - intros x Hx _. exact Hx. }
      assert (UW3 : uw_chain USTACK_TOP m3 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { eapply uw_chain_agree; [exact UW1|]. eapply agree_on_mono; [exact AG3|]. intros x Hx. left. exact Hx. }
      assert (AXP3 : ax_pres LB (bv_unsigned sp) LIBW_A m m3).
      { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      set (OW1 := (pn, An, 32 * 4) :: OW) in *.
      assert (ND1 : List.NoDup (map blk_id OW1)) by (exact (AH_nodup_l _ _ _ _ HEAP3)).
      assert (FRESHA : ~ In pn (all_ids ls AD EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 32 * 4 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      assert (LSC3' : lib_state_hc true [] ls m3 OW1 AD EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      assert (INC1 : In (ad_pc AD, ad_ctx AD, 72) (OW1 ++ LB)) by (apply in_or_app; left; right; exact BC).
      assert (INN1 : In (pn, An, 32 * 4) (OW1 ++ LB)) by (apply in_or_app; left; left; reflexivity).
      pose proof (AH_acc_in _ _ _ _ (ad_pc AD, ad_ctx AD, 72) (ad_ctx AD) 72 HEAP3 INC1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACC3.
      clear ACC MU WM OFF.
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl bsegs m3) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp + -112, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
      cbn [tbind fst snd]. unfold bret. cbn [ret tree_ops tbind fst snd].
      unfold MallocRep.wz in *.
      apply implA_from_evt.
      ub; step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; lia|]. clear KA.
      ub; step. ub; shl. ub; chk0.
      ub; step. rewrite EF. cbn [length]. change (Z.of_nat 0) with 0. rewrite (zx32_small 0) by lia.
      ub; step. if_true.
      ub; step. ub; shl. ub; chk0.
      do 4 (ub; step). ub; step.
      apply evt_done.
      eapply implA_step_same.
      { eapply (CRYPTO_free_null_cpsA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB); try reflexivity.
        - exact HEAP3.
        - rewrite ESP. exact ST3.
        - exact CEIL.
        - rewrite ESP. unfold CRYPTO_FREE_STACK, RT_STACK. lia.
        - rewrite ESP. unfold USTACK_TOP. lia.
        - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MI3.
        - exact (proj1 LSC3').
        - rewrite ESP. exact UW3.
        - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cs_free CTX). }
      intros ms5 PO. unfold cfree_null_post in PO. rewrite ?ESP in PO.
      destruct PO as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & m5 & -> & MI5 & ST5 & HEAP5 & AG5).
      rewrite (ret_pc_even 2408572) by lia. unfold MallocRep.wz.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in CX; [| intros x Hx; right; right; exists (ad_pc AD, ad_ctx AD, 72); split; [exact INC1| cbn in Hx |- *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in BLK; [| intros x Hx; right; right; exists (pn, An, 32 * 4); split; [exact INN1| cbn in Hx |- *; lia]].
      assert (LSC5 : lib_state_hc true [] ls m5 OW1 AD EA).
      { eapply lib_state_h_heap_pres; [exact LSC3'| exact AG5|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (HH1 : match cx_head (ls_ctx ls) with Some p => In (p, H, 400) OW1 | None => H = 0 end).
      { fold c in HH |- *. destruct (cx_head c); [right; exact HH| exact HH]. }
      assert (PM5 : pool_mem m5 H Cu c).
      { eapply (pool_mem_agree OW1 (OW1 ++ LB) (bv_unsigned sp + -112)); [exact HH1| | exact PM3| exact AG5|].
        - intros b0 Hb0. apply in_or_app. left. exact Hb0.
        - intros x Hx _. exact Hx. }
      assert (AXP5 : ax_pres LB (bv_unsigned sp) LIBW_A m m5).
      { eapply ax_pres_trans; [exact AXP3|]. eapply agree_on_mono; [exact AG5|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
      (* [comment removed for export] *)
      destruct (W_ctx.u32s_exists 32 junkA) as (ws & LWS & EWS).
      { destruct BLK as [[[HL _] _] _]. cbn in HL. exact HL. }
      assert (ARR : u32arr bsegs m5 An ws).
      { apply u8arr_of_rw_cells in BLK. destruct BLK as [B1 B2]. split; [rewrite EWS; exact B1|].
        rewrite LWS. replace (Z.of_nat (length junkA)) with (4 * Z.of_nat 32) in B2; [exact B2|].
        rewrite <- EWS, u32s_length, LWS. lia. }
      clear BLK.
      pose proof (AH_acc_in _ _ _ _ (ad_pc AD, ad_ctx AD, 72) (ad_ctx AD) 72 HEAP5 INC1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACC5.
      pose proof (AH_acc_in _ _ _ _ (pn, An, 32 * 4) An 128 HEAP5 INN1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACCN5.
      assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
      pose proof (AH_offsh _ _ _ _ (pn, An, 32 * 4) HEAP5 INN1) as ON. cbn [blk_addr blk_size fst snd] in ON. unfold SHLO, SHHI in ON.
      clear ACC3 MU3 WM3 OFF3.
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 128)]%Z m5) as MU5.
      pose proof (wmono_refl bsegs m5) as WM5.
      assert (OFF5 : offshW [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 128)]).
      { pose proof (AH_offsh _ _ _ _ (ad_pc AD, ad_ctx AD, 72) HEAP5 INC1) as O. cbn [blk_addr blk_size fst snd] in O.
        cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
      apply implA_from_evt.
      ub; shl. ub; chk0. ub; step. ub; shl. ub; step. ub; chk0. ub; step.
      (* [comment removed for export] *)
      ub; step. ub; shl. ub; chk0. ub; shl. ub; step. ub; chk0.
      ub; step. rewrite EF. cbn [length]. change (Z.of_nat 0) with 0. rewrite (zx32_small 0) by lia.
      do 2 (ub; step). ub; step. ub; step.
      do 2 (ub; step). ub; shl. ub; chk0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      pose proof (u32arr_store_ok bsegs m6 An ws 0 (wa An) ARR ltac:(lia) ltac:(f_equal; lia)) as SOKW.
      pose proof (u32arr_write bsegs m6 An ws 0 (Z_to_bv 64 (Z.of_nat (cx_used c))) ARR ltac:(lia)) as ARR2.
      rewrite Z.mul_0_r, Z.add_0_r in ARR2. change (Z.to_nat 0) with 0%nat in ARR2.
      ub; step. store_done.
      ub; step. do 13 (ub; step). release_frame FR ST5 (bv_unsigned sp). ub; step. ub; step.
      apply evt_done. apply implA_ret.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
      lazymatch goal with |- context [set_ctx ?cc ls] => set (c' := cc) end.
      assert (HinN : In (pn, An, 32 * 4) OW1) by (left; reflexivity).
      assert (BC1 : In (ad_pc AD, ad_ctx AD, 72) OW1) by (right; exact BC).
      assert (HH1' : match cx_head c' with Some p => In (p, H, 400) OW1 | None => H = 0 end).
      { subst c'. cbn [cx_head]. exact HH1. }
      assert (HWL5 : Forall (w_lib OW1 lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 128)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith|].
        constructor; [right; exists (pn, An, 32 * 4); cbn; auto with zarith| constructor]. }
      assert (LSF : lib_state (set_ctx c' ls) mF OW1 AD EA).
      { unfold lib_state. eapply (lib_state_cx_close [] ls mF OW1 AD EA c' H Cu An); [| exact ND1| reflexivity| reflexivity| exact HH1'| | | | |].
        - eapply (lib_state_frame Σ1 LB); [exact HEAP5| exact LSC5| exact MU5| exact WM5|].
          constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; cbn in Hx; lia]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB ls AD EA true [] _ pn An (32 * 4)); [exact INN1| exact FRESHA| cbn; lia| cbn; lia].
        - unfold ctx_cells, c'. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z app length]. rewrite ?EF. cbn [app length]. exact CX.
        - unfold stack_rep, c'. cbn [cx_indexes cx_ssize cx_frames app]. split; [exact HinN|]. split; [reflexivity|]. rewrite ?EF. cbn [app length map].
          destruct ws as [|w0 ws']; [cbn in LWS; lia|]. exists ws'. split; [cbn [length] in *; lia|]. cbn [map app Arr.upd] in *. exact ARR2.
        - eapply (pool_mem_keep Σ1 OW1 LB m5 mF ls AD EA H Cu); [exact HEAP5| exact IDS| | exact HH1| exact PM5| exact MU5| exact WM5|].
          + destruct ADB as (B1 & B2 & B3 & B4 & B5 & B6). unfold ad_blocks. repeat split; right; assumption.
          + constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
            right; right. exists pn, An, (32 * 4). split; [exact INN1|]. cbn [fst snd]. split; [lia|]. split; [lia|].
            fold c. intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply head_in_m. symmetry. exact E.
        - unfold ctx_okm, c'. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack app length]. rewrite ?EF. cbn [app length].
          split; [exact CK1|]. split; [exact CK2|]. split; [exact CK3|]. split; [cbn; lia|].
          split; [unfold BN_CTX_START_FRAMES; lia|]. split; [exact CK6| reflexivity].
        - eapply (ids_ok_set_ctx_new_idx ls AD EA c' pn); [exact IDS| reflexivity| reflexivity| exact EI| reflexivity| exact FRESHA]. }
      unfold bn_postA. do 17 eexists. exists mF, OW1. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap Σ1 OW1 LB m5 mF _ lo _ HEAP5 MU5 WM5 HWL5 CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
      split; [exact ST5|]. split; [assumption|].
      split. { eapply ax_pres_trans; [exact AXP5|]. exact (seg_ax_pres' Σ1 OW1 LB m5 mF _ lo _ _ HEAP5 MU5 HWL5 CEIL ltac:(lia)). }
      split; [exact CR3|].
      split. { unfold cnt_eq, cnt_bal. unfold blocks_of. cbn [set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]. fold c. unfold c'.
               cbn [cx_vals cx_head cx_indexes]. rewrite EI. cbn [opt_block]. unfold OW1. rewrite !length_app. cbn [length]. lia. }
      split. { intros r' a' HA'. destruct r' as [| | | | |i]; cbn [ref_at] in HA' |- *; try exact HA'.
               destruct HA' as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [exact E0|]. split; [right; exact I0| exact R0]. }
      intros q0 A0 n0 Hq0. right. exact Hq0.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BN_CTX_END : Z := 0x24c254.
Definition BN_CTX_END_STACK : Z := 16.

(* [comment removed for export] *)
Lemma end_loopA : forall (k : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (off j : Z),
  Z.of_nat k < j -> Z.of_nat k <= off -> off <= 15 -> j <= 16 ->
  evt bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (off - Z.of_nat k)) a4 a5 a6 (Z_to_bv 64 (- (j - Z.of_nat k)))
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24c380) fc None m (seg_rom bsegs)) ->
  evt bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 off) a4 a5 a6 (Z_to_bv 64 (- j))
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24c380) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until j; intros HJ HO HO15 HJ16 K.
  - change (Z.of_nat 0) with 0 in K. rewrite !Z.sub_0_r in K. exact K.
  - rewrite Nat2Z.inj_succ in *.
    ub; step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    ub; step. ub; step. ub; step.
    rewrite (swrap32_wrap64 (- j) 1) by lia. rewrite (swrap32_wrap64 off (-1)) by lia.
    ub; step. if_cases K1; zify_cond K1.
    + eapply evt_eq; [| eapply (IH POST ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (off + -1) (j - 1));
                        [lia| lia| lia| lia|] ].
      * replace (- j + 1) with (- (j - 1)) by lia. reflexivity.
      * replace (j - 1 - Z.of_nat k) with (j - Z.succ (Z.of_nat k)) by lia.
        replace (off + -1 - Z.of_nat k) with (off - Z.succ (Z.of_nat k)) by lia. exact K.
    + exfalso. change 18446744073709551615 with (Z.ones 64) in K1. rewrite ?Z.land_ones in K1 by lia.
      clear - K1 HJ HJ16. change (2 ^ 64) with 18446744073709551616 in K1. Z.div_mod_to_equations. lia.
Qed.

End WithRT.
