(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApBridge.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit3 ApIface W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sk_leaves W_sk_new W_realloc_array.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Definition OPENSSL_SK_PUSH : Z := 0xe75c8.
Definition OPENSSL_SK_INSERT : Z := 0xe6de0.
Definition SK_RESERVE : Z := 0xe6b64.

(* [comment removed for export] *)
Definition sk_raw (num D sorted na : Z) : list cell :=
  [C4 (wz num); C4 (wz 0); C8 (wz D); C4 (wz sorted); C4 (wz na); C8 (wz 0); C8 (wz SK_SCT_CMP_THUNK); C8 (wz SK_SCT_FREEFUNC_THUNK); C8 (wz SK_SCT_COPY_THUNK)].

Lemma sk_cells_raw : forall adr k sorted, sk_cells adr k sorted = sk_raw (sk_num k) (optr adr (sk_data k)) sorted (olen (sk_data k)).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma magic_div5 : forall x, 0 <= x < 2^31 -> (x * 1717986919) / 2^33 = x / 5.
Proof.
  intros x Hx. pose proof (Z.div_mod x 5 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 5 ltac:(lia)) as R.
  set (q := x / 5) in *. set (r := x mod 5) in *.
  symmetry. apply Z.div_unique with (r := 3 * q + r * 1717986919); [left; nia| nia].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

  (* [comment removed for export] *)
  Definition SK_PUSH_STACK : Z := 96 + CRYPTO_REALLOC_NN_STACK.

  (* [comment removed for export] *)
  Lemma push_prefix : forall (P : machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA X num D sorted na : Z),
    stk ctusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv ctusegs m ->
    rblock_range SA STACK_SIZE -> SA + STACK_SIZE <= lo -> rw_cells ctusegs m SA (sk_raw num D sorted na) -> 0 <= num < 2^22 ->
    a0 = wz SA -> a1 = wz X ->
    (forall m1 (j8 : list byte) (a3' a4' : word),
       munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 -> stk ctusegs m1 lo (bv_unsigned sp + -96) ->
       rw_cells ctusegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       rw_cells ctusegs m1 (bv_unsigned sp + -96) [CB 8 j8; C8 (wz X); C8 (wz num); C8 (wz SA); C8 sp; C8 (wz 0xe6e98)] ->
       rw_cells ctusegs m1 SA (sk_raw num D sorted na) ->
       evt ctusegs P
         (MS (mkR (wz 0xe6e98) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (wz SA)
                 (wz D) (wz 1) (wz 0) a3' a4' a5 a6 a7 (wz (Z.max (num + 1) 4)) (wz X) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0xe6c00) fc None m1 (seg_rom ctusegs))) ->
    evt ctusegs P
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz OPENSSL_SK_PUSH) fc None m (seg_rom ctusegs)).
  Proof.
    intros until na. intros ST GLO LO MI BR SAL HC Hnum -> -> K.
    unfold OPENSSL_SK_PUSH, STACK_SIZE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    destruct BR as (B0 & B16 & _ & BC & BI).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (SEPA : SA + 56 <= bv_unsigned sp - 96) by lia.
    unfold sk_raw, MallocRep.wz in HC.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 step.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. uchk. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    setreg 12%Z (Z_to_bv 64 num) ltac:(symmetry; apply sx32_small; lia).
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 8 step.
    step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step. step. uchk. step. step. setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply sx32_small; lia).
    step. step.
    step. if_cases K2; zify_cond K2; [| exfalso; lia]. clear K2.
    do 5 step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step.
    step. step. uchk. step. setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply sx32_small; lia).
    step. step. ub. step. setreg 13%Z (Z_to_bv 64 (2147483647 - num)) ltac:(rewrite (unsigned_lit (2147483647 + - num)) by lia; rewrite swrap32_small by lia; f_equal; lia).
    step. if_cases K3; zify_cond K3; [| exfalso; revert K3; rewrite ?signed_small, ?unsigned_lit by lia; lia]. clear K3.
    step. step. setreg 10%Z (Z_to_bv 64 (num + 1)) ltac:(rewrite ?(unsigned_lit num), ?(unsigned_lit 1), ?swrap32_small by lia; f_equal; lia).
    uchk. step. setreg 18%Z (Z_to_bv 64 (num + 1)) ltac:(rewrite ?(unsigned_lit (num + 1)), ?swrap32_small by lia; f_equal; lia).
    step.
    step. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      rewrite signed_small in K4 by lia.
      step. setreg 18%Z (Z_to_bv 64 (Z.max (num + 1) 4)) ltac:(rewrite Z.max_l by lia; reflexivity).
      eapply K; [exact MU| exact WM| exact MI| exact ST| exact FR| exact FR0| unfold sk_raw, MallocRep.wz; exact HC].
    - (* [comment removed for export] *)
      rewrite signed_small in K4 by lia.
      step. step. setreg 18%Z (Z_to_bv 64 (Z.max (num + 1) 4)) ltac:(rewrite Z.max_r by lia; reflexivity).
      eapply K; [exact MU| exact WM| exact MI| exact ST| exact FR| exact FR0| unfold sk_raw, MallocRep.wz; exact HC].
  Qed.

  (* [comment removed for export] *)
  Definition sorted_after (sorted num : Z) : Z := if negb (sorted =? 0) && (0 <? num) then 0 else sorted.

  Lemma insert_tail : forall (P : machine_state -> Prop)
      (ra sp gp tp s0 s1 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA X num D sorted na : Z) (wl : list word) (jb : list byte),
    stk ctusegs m lo (bv_unsigned sp + -48) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv ctusegs m ->
    rblock_range SA STACK_SIZE -> SA + STACK_SIZE <= lo -> rblock_range D (8 * na) -> D + 8 * na <= lo ->
    (SA + STACK_SIZE <= D \/ D + 8 * na <= SA) ->
    rw_cells ctusegs m SA (sk_raw num D sorted na) -> 0 <= num -> num + 1 <= na -> na < 2^23 -> 0 <= sorted <= 1 -> 0 <= X < 2^64 ->
    rw_cells ctusegs m D (map C8 wl ++ [CB (length jb) jb]) -> zlength wl = num -> Z.of_nat (length jb) = 8 * (na - num) ->
    rw_cells ctusegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall m2 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       munch [(bv_unsigned sp - 48, bv_unsigned sp); (SA, SA + STACK_SIZE); (D + 8 * num, D + 8 * num + 8)] m m2 -> wmono ctusegs m m2 -> mem_inv ctusegs m2 ->
       stk ctusegs m2 lo (bv_unsigned sp) ->
       rw_cells ctusegs m2 SA (sk_raw (num + 1) D (sorted_after sorted num) na) ->
       rw_cells ctusegs m2 D (map C8 (wl ++ [wz X]) ++ [CB (length jb - 8) (skipn 8 jb)]) ->
       evt ctusegs P
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (num + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m2 (seg_rom ctusegs))) ->
    evt ctusegs P
      (MS (mkR (wz 0xe6e98) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 x8 (wz SA) (wz 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz num) (wz X) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (wz 0xe6e98) fc None m (seg_rom ctusegs)).
  Proof.
    intros until jb. intros ST GLO LO MI BR SAL BD DL SEP HC Hn0 Hna Hna2 Hs HX HD WL JB FR K.
    unfold STACK_SIZE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    destruct BR as (B0 & B16 & _ & BC & BI). destruct BD as (D0 & D16 & _ & DC & DI).
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (SA, SA + 56); (D + 8 * num, D + 8 * num + 8)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold sk_raw, MallocRep.wz in HC.
    (* [comment removed for export] *)
    apply rw_cells_app in HD. destruct HD as [HDL HDR].
    assert (EL : Z.of_nat (cells_size (map C8 wl)) = 8 * num).
    { unfold zlength in WL. rewrite <- WL. clear. induction wl as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia. }
    rewrite EL in HDR. remember (D + 8 * num) as Dn eqn:EDn.
    assert (DNR : D <= Dn /\ Dn + 8 <= D + 8 * na) by lia.
    assert (HDR2 : rw_cells ctusegs m Dn ([CB 8%nat (firstn 8 jb)] ++ [CB (length jb - 8)%nat (skipn 8 jb)])).
    { eapply rw_cells_recast; [exact HDR| | |].
      - cbn. rewrite firstn_length_le, length_skipn by lia. auto.
      - cbn. rewrite !app_nil_r. apply firstn_skipn.
      - cbn. lia. }
    clear HDR. apply rw_cells_app in HDR2. destruct HDR2 as [HDR HDT].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDT. change (frozen (rw_cells ctusegs m (Dn + 8) [CB (length jb - 8)%nat (skipn 8 jb)])) in HDT.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    step. setreg 12%Z (Z_to_bv 64 num) ltac:(symmetry; apply sx32_small; lia).
    step.
    step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?signed_small by lia; lia|]. clear K1.
    step. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?signed_small by lia; lia]. clear K2.
    (* [comment removed for export] *)
    step. step. setreg 10%Z (Z_to_bv 64 Dn) ltac:(subst Dn; symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    ub.
    step. step. setreg 18%Z (Z_to_bv 64 num) ltac:(idtac; reflexivity).
    (* [comment removed for export] *)
    step. setreg 10%Z (Z_to_bv 64 (num + 1)) ltac:(rewrite ?(unsigned_lit num), ?(unsigned_lit 1), ?swrap32_small by lia; f_equal; lia).
    uchk. step. step.
    assert (JOIN : forall (x10 x11 x12 x13 x14 : word) mj,
      munch [(bv_unsigned sp - 48, bv_unsigned sp); (SA, SA + 56); (Dn, Dn + 8)] m mj -> wmono ctusegs m mj -> mem_inv ctusegs mj ->
      stk ctusegs mj lo (bv_unsigned sp + -48) ->
      rw_cells ctusegs mj SA [C4 (Z_to_bv 64 (num + 1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sorted_after sorted num)); C4 (Z_to_bv 64 na); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 SK_SCT_CMP_THUNK); C8 (Z_to_bv 64 SK_SCT_FREEFUNC_THUNK); C8 (Z_to_bv 64 SK_SCT_COPY_THUNK)] ->
      rw_cells ctusegs mj D (map C8 wl) -> rw_cells ctusegs mj Dn [C8 (Z_to_bv 64 X)] ->
      rw_cells ctusegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt ctusegs P
        (MS (mkR (Z_to_bv 64 0xe6e98) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 x8 (Z_to_bv 64 SA) x10 x11 x12 x13 x14 xa5 xa6 xa7
                  (Z_to_bv 64 num) (Z_to_bv 64 X) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xe7064) fc None mj (seg_rom ctusegs))).
    { intros x10 x11 x12 x13 x14 mj MUj WMj MIj STj HCj HDLj HDRj FRj.
      step. setreg 10%Z (Z_to_bv 64 (num + 1)) ltac:(symmetry; apply sx32_small; lia).
      do 6 step. release_frame FRj STj (bv_unsigned sp). step. step.
      eapply K; [exact MUj| exact WMj| exact MIj| exact STj| unfold sk_raw, MallocRep.wz; exact HCj|].
      rewrite map_app, <- app_assoc. apply rw_cells_app. split; [exact HDLj|]. rewrite EL. cbn [map app]. unfold MallocRep.wz.
      change (C8 (Z_to_bv 64 X) :: [CB (length jb - 8)%nat (skipn 8 jb)]) with ([C8 (Z_to_bv 64 X)] ++ [CB (length jb - 8)%nat (skipn 8 jb)]).
      apply rw_cells_app. rewrite <- EDn. split; [exact HDRj|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold frozen in HDT.
      eapply rw_cells_transport; [exact HDT| exact MUj| exact WMj|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    step. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      eapply JOIN; [exact MU| exact WM| exact MI| exact ST| | exact HDL| exact HDR| exact FR].
      assert (S0 : sorted = 0) by (revert KS; rewrite ?sx32_small, ?unsigned_lit by lia; lia). subst sorted. unfold sorted_after. cbn. exact HC.
    - step. step. if_cases KN; zify_cond KN.
      + (* [comment removed for export] *)
        eapply JOIN; [exact MU| exact WM| exact MI| exact ST| | exact HDL| exact HDR| exact FR].
        unfold sorted_after. replace (0 <? num) with false by (symmetry; apply Z.ltb_ge; revert KN; rewrite ?sx32_small, ?signed_small, ?unsigned_lit by lia; lia).
        rewrite Bool.andb_false_r. exact HC.
      + (* [comment removed for export] *)
        step. step. if_cases KC; zify_cond KC; [| exfalso; apply KC; reflexivity].
        step.
        eapply JOIN; [exact MU| exact WM| exact MI| exact ST| | exact HDL| exact HDR| exact FR].
        unfold sorted_after. replace (negb (sorted =? 0) && (0 <? num)) with true; [exact HC|].
        symmetry. apply andb_true_iff. split; [apply Bool.negb_true_iff; apply Z.eqb_neq| apply Z.ltb_lt];
          revert KS KN; rewrite ?sx32_small, ?signed_small, ?unsigned_lit by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lb_remove_notin : forall p L, ~ In p (map blk_id L) -> lb_remove p L = L.
  Proof.
    intros p L H. induction L as [|c L IH]; [reflexivity|]. rewrite lb_remove_cons. cbn in H.
    rewrite (bptr_eqb_neq (blk_id c) p) by (intros E; apply H; left; exact E). rewrite IH; [reflexivity|]. intros X; apply H; right; exact X.
  Qed.
  Lemma perm_readd : forall (b : block) L, List.NoDup (map blk_id L) -> In b L -> Permutation L (b :: lb_remove (blk_id b) L).
  Proof.
    intros b L. induction L as [|c L IH]; intros ND IN; [destruct IN|]. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
    rewrite lb_remove_cons. destruct IN as [->|IN].
    - rewrite bptr_eqb_refl. rewrite lb_remove_notin by exact NI. apply Permutation_refl.
    - rewrite (bptr_eqb_neq (blk_id c) (blk_id b)) by (intros E; apply NI; rewrite E; apply in_map; exact IN).
      apply Permutation_trans with (c :: b :: lb_remove (blk_id b) L); [apply perm_skip; apply IH; assumption| apply perm_swap].
  Qed.

  (* [comment removed for export] *)
  Definition push_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L : list block) (lo B : Z) (m : mem) (k : skr bptr) (x : sctr bptr) (SA X sorted : Z) (ws : list word) (st : ap_st bptr)
      (r : skr bptr * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (q' : bptr) (D' na' : Z) (jb' : list byte),
      let num := sk_num k in
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz (num + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ r = (mkSK (sk_blk k) (Some (q', na')) (sk_items k ++ [x]), st)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
      /\ rheap_pres (lb_remove (sk_blk k) (lremove (sk_data k) L)) (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ rblock_range D' (8 * na') /\ RHEAP s' ((q', D', 8 * na') :: lremove (sk_data k) L) m'
      /\ rw_cells ctusegs m' SA (sk_raw (num + 1) D' (sorted_after sorted num) na')
      /\ rw_cells ctusegs m' D' (map C8 (ws ++ [wz X]) ++ [CB (length jb') jb']) /\ Z.of_nat (length jb') = 8 * (na' - num - 1)
      /\ num + 1 <= na' /\ SK_MIN_NODES <= na' < 2^23.

  Section Proofs.
    Hypothesis HM : rmalloc_stmt.
    Hypothesis HR : rrealloc_stmt.

    Theorem OPENSSL_sk_push_walk : forall
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
        (k : skr bptr) (x : sctr bptr) (st : ap_st bptr) (SA X D sorted : Z) (ws : list word) (jb : list byte),
      let num := sk_num k in
      RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
      stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SK_PUSH_STACK ->
      rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
      crypto_statics m -> realloc_statics m ->
      In (sk_blk k, SA, STACK_SIZE) L -> rw_cells ctusegs m SA (sk_raw num D sorted (olen (sk_data k))) -> 0 <= sorted <= 1 -> num < 2^22 ->
      match sk_data k with
      | Some (q, na) => In (q, D, 8 * na) L /\ q <> sk_blk k /\ num <= na /\ SK_MIN_NODES <= na < 2^23
                        /\ rw_cells ctusegs m D (map C8 ws ++ [CB (length jb) jb]) /\ Z.of_nat (length jb) = 8 * (na - num)
      | None => sk_items k = [] /\ D = 0 /\ jb = []
      end -> zlength ws = num ->
      0 <= X < 2^64 -> a0 = wz SA -> a1 = wz X ->
      implM ctusegs (interp (ap_embed (sk_push k x st))) s
            (push_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m k x SA X sorted ws st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz OPENSSL_SK_PUSH) fc None m (seg_rom ctusegs)).
    Proof using HM HR.
      intros until jb. cbn zeta. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS RS HSIN HC Hs Hnum HD WS HX -> ->.
      pose proof (Zle_0_nat (length (sk_items k))) as NUM0. change (Z.of_nat (length (sk_items k))) with (sk_num k) in NUM0.
      unfold sk_push.
      destruct (sk_data k) as [[q na]|] eqn:EDATA.
      - destruct HD as (HDIN & NQS & Hna & Hna4 & HD & JB).
        destruct (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) eqn:ROOM.
        + (* [comment removed for export] *)
          cbn [abind apbind amalloc aret ap_embed fst snd interp]. apply implM_ret.
          apply Z.leb_le in ROOM.
          unfold SK_PUSH_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK, STACK_SIZE, SK_MIN_NODES, GLOBALS_TOP, MallocRep.wz in *.
          pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
          pose proof (LH_block_range _ _ _ _ HEAP HSIN) as BRS. pose proof (LH_block_range _ _ _ _ HEAP HDIN) as BRD. cbn [blk_addr blk_size fst snd] in BRS, BRD.
          pose proof BRS as (B0 & B16 & _ & BC & BI). pose proof BRD as (D0 & D16 & _ & DC & DI).
          pose proof (LH_nodup _ _ _ HEAP) as NDL.
          pose proof (LH_disjoint _ _ _ (q, D, 8 * na) (sk_blk k, SA, 56) HEAP HDIN HSIN NQS) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
          unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
          eapply push_prefix with (lo := lo) (D := D) (sorted := sorted) (na := na) (num := sk_num k);
            [exact ST| unfold GLOBALS_TOP; lia| lia| exact MI| exact BRS| unfold STACK_SIZE; lia| exact HC| lia| reflexivity| reflexivity|].
          intros m1 j8 a3' a4' MU WM MI1 ST1 FR FR0 HC1. unfold sk_raw, MallocRep.wz in HC1. unfold MallocRep.wz in FR0 |- *.
          assert (EW : Z.of_nat (cells_size (map C8 ws ++ [CB (length jb) jb])) = 8 * na).
          { rewrite cells_size_app. cbn [cells_size csize]. unfold zlength in WS.
            replace (cells_size (map C8 ws)) with (8 * length ws)%nat; [lia|].
            clear. induction ws as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia. }
          assert (HD1 : rw_cells ctusegs m1 D (map C8 ws ++ [CB (length jb) jb])) by (eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn [disjoint_from]; rewrite EW; lia]).
          change (frozen (rw_cells ctusegs m1 D (map C8 ws ++ [CB (length jb) jb]))) in HD1. clear HD.
          (* [comment removed for export] *)
          step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
          step. step. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
          step. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?sx32_small, ?signed_small, ?unsigned_lit by lia; lia]. clear K2.
          step. do 5 step. release_frame FR0 ST1 (bv_unsigned sp + -48). step. step.
          unfold frozen in HD1.
          assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove (sk_blk k) (lb_remove q L)) (bv_unsigned sp) a ->
                        outside [(bv_unsigned sp - 48, bv_unsigned sp); (SA, SA + 56); (D + 8 * sk_num k, D + 8 * sk_num k + 8)] a
                        /\ outside [(bv_unsigned sp - 96, bv_unsigned sp)] a).
          { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]]; [lia| lia|].
            apply lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hns]. apply lb_remove_In in Hb1. destruct Hb1 as [Hb' Hnq].
            pose proof (LH_disjoint _ _ _ (sk_blk k, SA, 56) b' HEAP HSIN Hb' ltac:(intros E; apply Hns; symmetry; exact E)) as DJ1.
            pose proof (LH_disjoint _ _ _ (q, D, 8 * na) b' HEAP HDIN Hb' ltac:(intros E; apply Hnq; symmetry; exact E)) as DJ2.
            cbn [blk_addr blk_size blk_id fst snd] in DJ1, DJ2.
            pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
          eapply insert_tail with (lo := lo) (D := D) (sorted := sorted) (na := na) (wl := ws) (jb := jb);
            [exact ST1| unfold GLOBALS_TOP; lia| lia| exact MI1| exact BRS| unfold STACK_SIZE; lia| exact BRD| lia| unfold STACK_SIZE; lia
            | exact HC1| lia| lia| lia| lia| lia| exact HD1| exact WS| exact JB| exact FR|].
          intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MU2 WM2 MI2 ST2 HC2 HD2. unfold STACK_SIZE in MU2.
          apply evt_done. unfold push_post. cbn zeta. unfold MallocRep.wz. rewrite EDATA. cbn [lremove].
          exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2, errv, q, D, na, (skipn 8 jb).
          split; [reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
          split. { unfold LX_ERRNO, RATP. eapply rw_cells_transport; [| exact MU2| exact WM2| cbn; lia]. eapply rw_cells_transport; [exact ERR| exact MU| exact WM| cbn; lia]. }
          split. { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]| exact MU2| exact WM2|].
                   - constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
                   - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
          split. { cbn [lremove]. eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM|]| eapply heap_pres_of_munch; [exact MU2| exact WM2|]];
                     intros a Ha Hc; [exact (proj2 (CLI a Ha Hc))| exact (proj1 (CLI a Ha Hc))]. }
          split; [reflexivity|]. split; [reflexivity|]. split; [exact BRD|].
          split. { cbn [lremove]. eapply RHEAP_perm; [| apply (perm_readd (q, D, 8 * na)); [exact NDL| exact HDIN]].
                   eapply LH_frame; [eapply LH_frame; [exact HEAP| exact MU| exact WM|]| exact MU2| exact WM2|].
                   - constructor; [apply W_ok_stack; cbn; lia| constructor].
                   - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (sk_blk k, SA, 56)); [exact HSIN| cbn; lia| cbn; lia]|].
                     constructor; [eapply (W_ok_block _ (q, D, 8 * na)); [exact HDIN| cbn; lia| cbn; lia]| constructor]. }
          split; [exact HC2|]. split; [rewrite length_skipn; exact HD2|].
          split; [rewrite length_skipn; lia|].
          split; [lia|]. unfold SK_MIN_NODES; lia.
        + (* [comment removed for export] *)
          cbn [abind apbind amalloc arealloc aret ap_embed fst snd].
          apply Z.leb_gt in ROOM.
          unfold SK_PUSH_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK, STACK_SIZE, SK_MIN_NODES, GLOBALS_TOP, MallocRep.wz in *.
          assert (EN : na = sk_num k) by lia.
          replace (Z.max (sk_num k + 1) 4) with (na + 1) by lia. rewrite (sk_grow_once na) by lia.
          pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
          pose proof (LH_block_range _ _ _ _ HEAP HSIN) as BRS. pose proof (LH_block_range _ _ _ _ HEAP HDIN) as BRD. cbn [blk_addr blk_size fst snd] in BRS, BRD.
          pose proof BRS as (B0 & B16 & _ & BC & BI). pose proof BRD as (D0 & D16 & _ & DC & DI).
          pose proof (LH_nodup _ _ _ HEAP) as NDL.
          pose proof (LH_disjoint _ _ _ (q, D, 8 * na) (sk_blk k, SA, 56) HEAP HDIN HSIN NQS) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
          unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
          unfold implM. iprefix. eapply push_prefix with (lo := lo) (D := D) (sorted := sorted) (na := na) (num := sk_num k);
            [exact ST| unfold GLOBALS_TOP; lia| lia| exact MI| exact BRS| unfold STACK_SIZE; lia| exact HC| lia| reflexivity| reflexivity|].
          intros m1 j8 a3' a4' MU WM MI1 ST1 FR FR0 HC1. unfold sk_raw, MallocRep.wz in HC1. unfold MallocRep.wz in FR0 |- *.
          assert (EW : Z.of_nat (cells_size (map C8 ws ++ [CB (length jb) jb])) = 8 * na).
          { rewrite cells_size_app. cbn [cells_size csize]. unfold zlength in WS.
            replace (cells_size (map C8 ws)) with (8 * length ws)%nat; [lia|].
            clear. induction ws as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia. }
          assert (HD1 : rw_cells ctusegs m1 D (map C8 ws ++ [CB (length jb) jb])) by (eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn [disjoint_from]; rewrite EW; lia]).
          clear HD.
          (* [comment removed for export] *)
          step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
          step. setreg 14%Z (Z_to_bv 64 na) ltac:(symmetry; apply sx32_small; lia).
          step. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
          step. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?sx32_small, ?signed_small, ?unsigned_lit by lia; lia|]. clear K2.
          do 5 step.
          (* [comment removed for export] *)
          step. step.
          setreg 14%Z (Z_to_bv 64 7)
            ltac:(f_equal; symmetry; rewrite Z.shiftr_div_pow2 by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap;
                  change (bv_modulus 64) with (4294967296 * 4294967296); change (bv_modulus 32) with 4294967296;
                  rewrite Z.mod_mod_divide by (exists 4294967296; lia);
                  replace ((na + -268435456) mod 4294967296) with (na + 4026531840) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia);
                  replace ((na + 4026531840) / 2 ^ 29) with 7 by (apply Z.div_unique with (r := na + 4026531840 - 7 * 2^29); lia);
                  apply swrap32_small; lia).
          uchk.
          (* [comment removed for export] *)
          step. step. step. step. step.
          setreg 19%Z (Z_to_bv 64 (na * 8 / 5))
            ltac:(f_equal; symmetry; rewrite (unsigned_lit na) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8;
                  rewrite swrap32_small by lia; rewrite (unsigned_lit (na * 8)) by lia; rewrite signed_small by nia;
                  rewrite (unsigned_lit (na * 8 * 1717986919)) by nia; rewrite !Z.shiftr_div_pow2 by lia; rewrite magic_div5 by lia;
                  rewrite (Z.div_small _ (2 ^ 63)) by nia; rewrite Z.add_0_r; reflexivity).
          assert (GR : na + 1 <= na * 8 / 5) by (apply Z.div_le_lower_bound; lia).
          assert (GR2 : na * 8 / 5 < 2 ^ 23) by (apply Z.div_lt_upper_bound; lia).
          replace (Z.max (sk_num k + 1) 4) with (na + 1) by lia.
          (* [comment removed for export] *)
          step. if_cases K4; zify_cond K4; [exfalso; revert K4; rewrite ?signed_small by lia; lia|]. clear K4.
          step. step. step. step. step. step.
          (* [comment removed for export] *)
          pose proof (rw_cells_CB_of _ _ _ HD1) as HDB.
          replace (cells_size (map C8 ws ++ [CB (length jb) jb])) with (Z.to_nat (8 * na)) in HDB by lia.
          set (old := cells_bytes (map C8 ws ++ [CB (length jb) jb])) in HDB.
          replace (8 * (na * 8 / 5)) with (na * 8 / 5 * 8) by lia.
          assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
          assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 96, bv_unsigned sp)] a).
          { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
            pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
          assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
          ihere.
          lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?E) ?ms =>
            lazymatch E with (fun p0 => ?Q0 (fst p0) (snd p0)) => change (implM segs c stt Q0 ms) end end.
          eapply (CRYPTO_realloc_array_grow_walk HR) with (B := B) (lo := lo) (errv := errv) (A := D) (n0 := 8 * na) (old := old) (L := L);
            [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
            | exact HDIN
            | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
            | rewrite ESP; lia | rewrite ESP; exact ST1 | exact CEIL | unfold GLOBALS_TOP; lia | rewrite ESP; unfold CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK; lia
            | unfold LX_ERRNO, RATP; eapply rw_cells_transport; [exact ERR| exact MU| exact WM| cbn; lia]
            | exact HDB | exact MI1 | reflexivity
            | eapply (realloc_statics_agree []); [exact RS| eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]];
              intros a Ha; cbn; split; [| exact I]; destruct Ha as [Ha|(b' & Hb' & Hr)]; [| destruct Hb'];
              unfold LIBW_HX, rin_ivs in Ha; cbn [fst snd] in Ha; lia
            | reflexivity | reflexivity | reflexivity | lia | lia | nia | reflexivity | ].
          intros q' st1 ms1 PO. unfold crealloc_post in PO. rewrite ?ESP in PO.
          destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A' & errv2
                          & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR' & HEAP3 & (junk & BLK & GROW)).
          replace (ret_pc (Z_to_bv 64 945300)) with (Z_to_bv 64 945300) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          set (na' := na * 8 / 5) in *.
          pose proof BR' as (A0 & A16 & _ & AC & AI).
          pose proof (LH_nodup _ _ _ HEAP3) as ND3. cbn [map blk_id fst snd] in ND3. apply NoDup_cons_iff in ND3. destruct ND3 as [NQ' ND3'].
          assert (HSIN' : In (sk_blk k, SA, 56) (lb_remove q L)) by (apply lb_remove_In; split; [exact HSIN| cbn; intros E; apply NQS; symmetry; exact E]).
          assert (NQS' : q' <> sk_blk k) by (intros E; apply NQ'; rewrite E; apply in_map_iff; exists (sk_blk k, SA, 56); split; [reflexivity| exact HSIN']).
          pose proof (LH_disjoint _ _ _ (q', A', na' * 8) (sk_blk k, SA, 56) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HSIN') NQS') as DJ'.
          cbn [blk_addr blk_size blk_id fst snd] in DJ'.
          (* [comment removed for export] *)
          pose proof (agree_of_heap_pres _ _ _ _ HP) as AG3.
          apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; left; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros a Ha; left; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG3) in HC1; [| intros a Ha; right; right; exists (sk_blk k, SA, 56); split; [exact HSIN'| cbn; cbn in Ha; lia]].
          (* [comment removed for export] *)
          pose proof (proj1 (proj1 BLK)) as WFB. cbn in WFB. destruct WFB as (LOLD & LJUNK & _).
          assert (JB0 : jb = []) by (destruct jb; [reflexivity| exfalso; cbn [length] in JB; lia]). subst jb.
          assert (HDN : rw_cells ctusegs m3 A' (map C8 ws ++ [CB (length junk) junk])).
          { eapply rw_cells_recast; [exact BLK| | |].
            - clear. induction ws as [|w t IH]; cbn; [auto| split; [exact I| exact IH]].
            - subst old. rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
            - rewrite cells_size_app. cbn [cells_size csize]. rewrite cells_size_app in EW. cbn [cells_size csize length] in EW. lia. }
          clear BLK. unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
          pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 56)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
          assert (SEPA' : A' + na' * 8 <= bv_unsigned sp - 96) by lia.
          change (frozen (rw_cells ctusegs m3 A' (map C8 ws ++ [CB (length junk) junk]))) in HDN.
          (* [comment removed for export] *)
          cbn [ap_embed apbind fst snd interp]. apply implM_ret.
          step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
          step. step. step.
          do 5 step. release_frame FR0 ST3 (bv_unsigned sp + -48). step. step.
          name_mem m4. unfold frozen in HDN. unfold MallocRep.wz in HC1.
          replace (na' * 8) with (8 * na') in BR' by lia.
          eapply insert_tail with (lo := lo) (D := A') (sorted := sorted) (na := na') (wl := ws) (jb := junk);
            [exact ST3| unfold GLOBALS_TOP; lia| lia| exact MI3| exact BRS| unfold STACK_SIZE; lia| exact BR'| lia| unfold STACK_SIZE; lia
            | exact HC1| lia| lia| lia| lia| lia| | exact WS| lia| exact FR|].
          { eapply rw_cells_transport; [exact HDN| exact MU3| exact WM3|]. rewrite cells_size_app. cbn [disjoint_from cells_size csize].
            rewrite cells_size_app in EW. cbn [cells_size csize length] in EW. lia. }
          intros m5 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MU5 WM5 MI5 ST5 HC5 HD5. unfold STACK_SIZE in MU5.
          apply evt_done. unfold push_post. cbn zeta. unfold MallocRep.wz. rewrite EDATA. cbn [lremove].
          exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m5, errv2, q', A', na', (skipn 8 junk).
          assert (CLI5 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove (sk_blk k) (lb_remove q L)) (bv_unsigned sp) a ->
                         outside [(bv_unsigned sp - 48, bv_unsigned sp); (SA, SA + 56); (A' + 8 * sk_num k, A' + 8 * sk_num k + 8)] a
                         /\ outside [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 56)] a).
          { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]]; [lia| lia|].
            apply lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hns].
            pose proof (proj1 (proj1 (lb_remove_In _ _ _) Hb1)) as Hb'.
            pose proof (LH_disjoint _ _ _ (sk_blk k, SA, 56) b' HEAP HSIN Hb' ltac:(intros E; apply Hns; symmetry; exact E)) as DJ1.
            assert (NB : q' <> blk_id b') by (intros E; apply NQ'; rewrite E; apply in_map; exact Hb1).
            pose proof (LH_disjoint _ _ _ (q', A', 8 * na') b' HEAP3 ltac:(left; f_equal; lia) ltac:(right; exact Hb1) NB) as DJ2.
            cbn [blk_addr blk_size blk_id fst snd] in DJ1, DJ2.
            pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
          split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|].
          split. { unfold LX_ERRNO, RATP. eapply rw_cells_transport; [exact ERR3| exact MU5| exact WM5| cbn; lia]. }
          split. { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]| exact MU5| exact WM5|].
                   - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
                   - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
          split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; exact (proj1 (proj1 (lb_remove_In _ _ _) (proj1 (proj1 (lb_remove_In _ _ _) Hb))))]|].
                   eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; exact (proj1 (proj1 (lb_remove_In _ _ _) Hb))]|].
                   eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU3| exact WM3|]| eapply heap_pres_of_munch; [exact MU5| exact WM5|]];
                     intros a Ha Hc; [exact (proj2 (CLI5 a Ha Hc))| exact (proj1 (CLI5 a Ha Hc))]. }
          split; [exact FA|]. split; [exact SO|]. split; [exact BR'|].
          split. { replace (8 * na') with (na' * 8) by lia.
                   eapply LH_frame; [eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|]| exact MU5| exact WM5|].
                   - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (sk_blk k, SA, 56)); [right; exact HSIN'| cbn; lia| cbn; lia]| constructor].
                   - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (sk_blk k, SA, 56)); [right; exact HSIN'| cbn; lia| cbn; lia]|].
                     constructor; [eapply (W_ok_block _ (q', A', na' * 8)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
          split; [exact HC5|]. split; [rewrite length_skipn; exact HD5|].
          split; [rewrite length_skipn; lia|].
          split; [lia|]. unfold SK_MIN_NODES; lia.
      - (* [comment removed for export] *)
        destruct HD as (HIT & HD0 & HJB). subst D jb.
        assert (N0 : sk_num k = 0) by (unfold sk_num; rewrite HIT; reflexivity).
        assert (WS0 : ws = []) by (destruct ws; [reflexivity| exfalso; unfold zlength in WS; cbn [length] in WS; lia]). subst ws.
        cbn [abind apbind amalloc aret ap_embed fst snd]. rewrite !N0 in HC |- *. change (8 * Z.max (0 + 1) SK_MIN_NODES) with (4 * 8). change (Z.max (0 + 1) SK_MIN_NODES) with 4.
        unfold SK_PUSH_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK, STACK_SIZE, SK_MIN_NODES, GLOBALS_TOP, MallocRep.wz in *. cbn [olen] in HC.
        pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
        pose proof (LH_block_range _ _ _ _ HEAP HSIN) as BRS. cbn [blk_addr blk_size fst snd] in BRS. pose proof BRS as (B0 & B16 & _ & BC & BI).
        pose proof (LH_nodup _ _ _ HEAP) as NDL.
        unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
        unfold implM. iprefix. eapply push_prefix with (lo := lo) (D := 0) (sorted := sorted) (na := 0) (num := 0);
          [exact ST| unfold GLOBALS_TOP; lia| lia| exact MI| exact BRS| unfold STACK_SIZE; lia| exact HC| lia| reflexivity| reflexivity|].
        intros m1 j8 a3' a4' MU WM MI1 ST1 FR FR0 HC1. unfold sk_raw, MallocRep.wz in HC1. unfold MallocRep.wz in FR0 |- *.
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
        assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 96, bv_unsigned sp)] a).
        { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
          pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
        assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
        (* [comment removed for export] *)
        step. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
        do 6 step.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?E) ?ms =>
          lazymatch E with (fun p0 => ?Q0 (fst p0) (snd p0)) => change (implM segs c stt Q0 ms) end end.
        eapply (CRYPTO_calloc_walk HM) with (B := B) (lo := lo) (errv := errv) (num := 4) (size := 8) (L := L);
          [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
          | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
          | rewrite ESP; lia | rewrite ESP; exact ST1 | exact CEIL | unfold GLOBALS_TOP; lia
          | rewrite ESP; unfold CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
          | unfold LX_ERRNO, RATP; eapply rw_cells_transport; [exact ERR| exact MU| exact WM| cbn; lia]
          | exact MI1 | reflexivity
          | eapply BnRep.crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS];
            intros a Ha; cbn; split; [| exact I]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia
          | reflexivity | reflexivity | lia | lia | lia | reflexivity | ].
        intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
        destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A' & errv2
                        & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR' & HEAP3 & BLK).
        replace (ret_pc (Z_to_bv 64 945200)) with (Z_to_bv 64 945200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        change (Z.to_nat (4 * 8)) with 32%nat in BLK. change (4 * 8) with 32 in BR', HEAP3.
        pose proof BR' as (A0 & A16 & _ & AC & AI).
        pose proof (LH_nodup _ _ _ HEAP3) as ND3. cbn [map blk_id fst snd] in ND3. apply NoDup_cons_iff in ND3. destruct ND3 as [NQ' ND3'].
        assert (NQS' : p <> sk_blk k) by (intros E; apply NQ'; rewrite E; apply in_map_iff; exists (sk_blk k, SA, 56); split; [reflexivity| exact HSIN]).
        pose proof (LH_disjoint _ _ _ (p, A', 32) (sk_blk k, SA, 56) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HSIN) NQS') as DJ'.
        cbn [blk_addr blk_size blk_id fst snd] in DJ'.
        (* [comment removed for export] *)
        pose proof (agree_of_heap_pres _ _ _ _ HP) as AG3.
        apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG3) in HC1; [| intros a Ha; right; right; exists (sk_blk k, SA, 56); split; [exact HSIN| cbn; cbn in Ha; lia]].
        unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
        pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 56)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
        assert (SEPA' : A' + 32 <= bv_unsigned sp - 96) by lia.
        change (frozen (rw_cells ctusegs m3 A' [CB 32%nat (repeat (Z_to_bv 8 0) 32%nat)])) in BLK.
        (* [comment removed for export] *)
        cbn [ap_embed apbind fst snd interp]. apply implM_ret. unfold MallocRep.wz.
        step.
        step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
        step. step. step.
        do 5 step. release_frame FR0 ST3 (bv_unsigned sp + -48). step. step.
        name_mem m4. unfold frozen in BLK. change (Z.max (0 + 1) 4) with 4 in HC1.
        replace 32 with (8 * 4) in BR' by reflexivity.
        eapply insert_tail with (lo := lo) (D := A') (sorted := sorted) (na := 4) (wl := []) (jb := repeat (Z_to_bv 8 0) 32%nat);
          [exact ST3| unfold GLOBALS_TOP; lia| lia| exact MI3| exact BRS| unfold STACK_SIZE; lia| exact BR'| lia| unfold STACK_SIZE; lia
          | exact HC1| lia| lia| lia| lia| lia| | reflexivity| reflexivity| exact FR|].
        { cbn [map app length repeat]. eapply rw_cells_transport; [exact BLK| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
        intros m5 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MU5 WM5 MI5 ST5 HC5 HD5. unfold STACK_SIZE in MU5.
        apply evt_done. unfold push_post. cbn zeta. unfold MallocRep.wz. rewrite EDATA. cbn [lremove]. rewrite !N0.
        exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m5, errv2, p, A', 4, (skipn 8 (repeat (Z_to_bv 8 0) 32%nat)).
        assert (CLI5 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove (sk_blk k) L) (bv_unsigned sp) a ->
                       outside [(bv_unsigned sp - 48, bv_unsigned sp); (SA, SA + 56); (A' + 8 * 0, A' + 8 * 0 + 8)] a
                       /\ outside [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 56)] a).
        { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]]; [lia| lia|].
          apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hns].
          pose proof (LH_disjoint _ _ _ (sk_blk k, SA, 56) b' HEAP HSIN Hb' ltac:(intros E; apply Hns; symmetry; exact E)) as DJ1.
          assert (NB : p <> blk_id b') by (intros E; apply NQ'; rewrite E; apply in_map; exact Hb').
          pose proof (LH_disjoint _ _ _ (p, A', 32) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb') NB) as DJ2.
          cbn [blk_addr blk_size blk_id fst snd] in DJ1, DJ2.
          pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
        split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|].
        split. { unfold LX_ERRNO, RATP. eapply rw_cells_transport; [exact ERR3| exact MU5| exact WM5| cbn; lia]. }
        split. { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]| exact MU5| exact WM5|].
                 - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
                 - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; exact (proj1 (proj1 (lb_remove_In _ _ _) Hb))]|].
                 eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; exact (proj1 (proj1 (lb_remove_In _ _ _) Hb))]|].
                 eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU3| exact WM3|]| eapply heap_pres_of_munch; [exact MU5| exact WM5|]];
                   intros a Ha Hc; [exact (proj2 (CLI5 a Ha Hc))| exact (proj1 (CLI5 a Ha Hc))]. }
        split; [exact FA|]. split; [exact SO|]. split; [exact BR'|].
        split. { change (8 * 4) with 32.
                 eapply LH_frame; [eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|]| exact MU5| exact WM5|].
                 - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (sk_blk k, SA, 56)); [right; exact HSIN| cbn; lia| cbn; lia]| constructor].
                 - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (sk_blk k, SA, 56)); [right; exact HSIN| cbn; lia| cbn; lia]|].
                   constructor; [eapply (W_ok_block _ (p, A', 32)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
        split; [exact HC5|]. split; [rewrite length_skipn; exact HD5|].
        split; [rewrite length_skipn; cbn; lia|].
        split; [lia|]. unfold SK_MIN_NODES; lia.
    Qed.
  End Proofs.
End WithCeiling0.
