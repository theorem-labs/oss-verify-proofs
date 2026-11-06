(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_strlen ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C5_stmt ECH_C12_stmt ECH_C12_hnpart ECH_C12_vsn ECH_C12_vpmfree ECH_C12_addstr ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AH_R1 : Z := 0x216740.   (* [comment removed for export] *)
Definition AH_BR : Z := 0x2167a0.   (* [comment removed for export] *)
Definition AH_R2 : Z := 0x21678c.   (* [comment removed for export] *)

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma ah_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a name lo : Z) (ns slk : list byte),
      0 < a -> a mod 16 = 0 -> a + VPM_SIZE <= lo -> 0 < name -> name + zlength ns + 1 <= lo -> 1 <= zlength ns <= 255 ->
      bv_unsigned sp mod 16 = 0 ->
      rw_cells usegs m a (vpm_cells_h 0) ->
      bytes_at usegs m name ns -> bytes_at usegs m (name + zlength ns) [Z_to_bv 8 0] -> bytes_at usegs m (name + zlength ns + 1) slk ->
      ~ In (Z_to_bv 8 0) ns -> zlength slk < 8 -> (- (name + zlength ns + 1)) mod 8 <= zlength slk ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 176 -> mem_inv usegs m ->   (* [comment removed for export] *)
      evt usegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AH_BR) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 sp (Z_to_bv 64 name)
                       (Z_to_bv 64 (if hostname_ok ns then 1 else 0)) b1 b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 a) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 AH_BR) fc None m1 (seg_rom usegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48) [C8 (wz (zlength ns))]
          /\ rw_cells usegs m1 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells usegs m1 a (vpm_cells_h 0) /\ bytes_at usegs m1 name ns)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 name) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_X509_VERIFY_PARAM_add1_host) fc None m (seg_rom usegs)).
  Proof.
    intros until slk. intros AP AAL AL NP NL LR SPAL BLK STRa STRb STRc NONUL SLK PAD ST CEIL LO MI.
    unfold P_X509_VERIFY_PARAM_add1_host, AH_BR. unfold zlength in *.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *.
    pose proof (bytes_at_bound _ _ _ _ STRa) as STRB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 7 step. st1. step.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. step. try if_lit. step. step.
    eapply evt_cut.
    { pose proof strlen_spec as Q; hnf in Q; eapply Q with (str := ns) (slack := slk); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia.
      match goal with Ka : bytes_at _ _ _ ?l1, Kb : bytes_at _ _ _ [_], Kc : bytes_at _ _ _ ?l3 |- _ =>
          apply (proj2 (bytes_at_app usegs _ _ _ _)); split; [exact Ka|];
          apply (proj2 (bytes_at_app usegs _ _ [Z_to_bv 8 0] _)); split; [exact Kb| cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; eapply bytes_at_ext_addr; [exact Kc| lia]] end. }
    land MU WM.
    repeat match goal with K : bytes_at _ _ _ (ns ++ _) |- _ => clear K end.
    (* [comment removed for export] *)
    st1. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with K : rw_cells _ mx (bv_unsigned sp + -48) _ |- _ =>
        lazymatch type of K with rw_cells _ _ ?ax _ =>
          change (rw_cells usegs mx ax ([C8 (Z_to_bv 64 (Z.of_nat (length ns)))] ++ [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in K end;
        apply (proj1 (rw_cells_app usegs _ _ _ _)) in K; destruct K as [LEN FR]; cbn [cells_size csize Nat.add] in FR;
        replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FR by lia end end.
    eapply evt_cut.
    { pose proof vsn_spec as Q; hnf in Q; eapply Q with (lo := lo) (ns := ns) (rest := []); clear Q; unfold zlength;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia.
      all: try (unfold VSN_STACK, FR_validate_string_name; lia).
      all: try (apply (proj2 (bytes_at_app usegs _ _ _ _)); split; assumption).
      all: cbn [length Z.of_nat]; lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. try if_lit.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). step. ubal_by AAL. step. if_lit.
    step. step. step. try if_lit. do 3 step.
    eapply evt_cut.
    { pose proof hnpart_spec as Q; hnf in Q; eapply Q with (lo := lo) (ns := ns) (rest := []); clear Q; unfold zlength; rewrite ?app_nil_r;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia.
      all: try (unfold HNPART_STACK, FR_validate_hostname_part, CTYPE_STACK, FR_ossl_ctype_check; lia).
      all: cbn [length Z.of_nat]; lia. }
    land MU WM.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ah_segR :
    forall (sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : Z),
      rw_cells usegs m (bv_unsigned sp + -48) [C8 (wz L)] ->
      rw_cells usegs m (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 AH_BR) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AH_BR) fc None m (seg_rom usegs)).
  Proof.
    intros until L. intros LEN FR MI. unfold AH_BR. unfold wz in LEN.
    pose proof (word_range sp) as SPR.
    step. try if_lit. step. step. do 5 st1. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ah_segT :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a name L : Z),
      0 <= a -> a + VPM_SIZE < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -48) [C8 (wz L)] ->
      rw_cells usegs m (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AH_R2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 name) (Z_to_bv 64 (a + O_VPM_HOSTS)) (Z_to_bv 64 name) (Z_to_bv 64 L) a3 a4 a5 a6 a7
                       (Z_to_bv 64 a) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_add_string_to_buffer_stack) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 AH_BR) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 name) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 a) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AH_BR) fc None m (seg_rom usegs)).
  Proof.
    intros until L. intros AP AL LEN FR MI. unfold AH_BR, AH_R2, P_add_string_to_buffer_stack, O_VPM_HOSTS. unfold wz in LEN. unfold VPM_SIZE in AL.
    pose proof (word_range sp) as SPR.
    step. try if_lit. st1. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ah_segE :
    forall (sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 rv : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : Z),
      rw_cells usegs m (bv_unsigned sp + -48) [C8 (wz L)] ->
      rw_cells usegs m (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 AH_R2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1x rv a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AH_R2)) fc None m (seg_rom usegs)).
  Proof.
    intros until L. intros LEN FR MI. unfold AH_R2. unfold wz in LEN.
    replace (ret_pc (Z_to_bv 64 0x21678c)) with (Z_to_bv 64 0x21678c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR.
    step. step. step. do 5 st1. step. step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HX.

  Lemma add1host_spec : add1host_stmt H.
  Proof.
    unfold add1host_stmt. intros until errv.
    intros A0 A1 A2 VO VH VHO AL NIN STR NONUL LR PAD HP KREL BUD BUDC BUDB AUX SPB SPAL ST CEIL LO ERR MI TP MF IM GM RAE. subst a0 a1 a2.
    unfold ADD1HOST_STACK, FR_X509_VERIFY_PARAM_add1_host, HNPART_STACK, FR_validate_hostname_part, CTYPE_STACK, FR_ossl_ctype_check,
      ADDSTR_STACK, FR_add_string_to_buffer_stack, CSTRNDUP_STACK, SKNEW_STACK, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK,
      CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK, FR_sk_new, FR_sk_insert, FR_sk_reserve,
      CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    unfold ADD1HOST_BYTES, SK_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB. unfold zlength in *.
    set (L := Z.of_nat (length ns)) in *.
    destruct VO as (VC & VIN & HOS). rewrite vpm_cells_h_eq, VH in VC.
    pose proof (HB _ VIN) as PBL. cbn [blk_addr blk_size fst snd] in PBL. unfold VPM_SIZE in PBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP VIN) as PBR. cbn [blk_addr blk_size fst snd] in PBR. unfold VPM_SIZE in PBR.
    destruct PBR as (PPOS & PAL & _ & _ & POFF). box POFF.
    pose proof (HB _ NIN) as NBL. cbn [blk_addr blk_size fst snd] in NBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP NIN) as NBR. cbn [blk_addr blk_size fst snd] in NBR. destruct NBR as (NPOS & _ & _ & _ & NOFF). box NOFF.
    subst tp. rewrite errno_RATP in ERR.
    (* [comment removed for export] *)
    set (k := (- (name + L + 1)) mod 8) in *.
    assert (KR : 0 <= k < 8) by (unfold k; apply Z.mod_pos_bound; lia).
    assert (STRk : bytes_at usegs m name (ns ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack)).
    { replace (ns ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack) with ((ns ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat k) slack) by (rewrite <- app_assoc; reflexivity).
      replace (ns ++ Z_to_bv 8 0 :: slack) with ((ns ++ [Z_to_bv 8 0]) ++ slack) in STR by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in STR. destruct STR as [S1 S2]. apply bytes_at_app. split; [exact S1|].
      rewrite <- (firstn_skipn (Z.to_nat k) slack) in S2. apply bytes_at_app in S2. exact (proj1 S2). }
    assert (SLK : Z.of_nat (length (firstn (Z.to_nat k) slack)) = k) by (rewrite length_firstn; lia).
    pose proof (proj1 (proj1 (bytes_at_app usegs _ _ (ns ++ [Z_to_bv 8 0]) (firstn (Z.to_nat k) slack))
                  ltac:(rewrite <- app_assoc; exact STRk))) as STR0.
    clear STR. set (slk := firstn (Z.to_nat k) slack) in *.
    (* [comment removed for export] *)
    apply bytes_at_app in STRk. destruct STRk as [STRa STRbc].
    change (Z_to_bv 8 0 :: slk) with ([Z_to_bv 8 0] ++ slk) in STRbc. apply bytes_at_app in STRbc. destruct STRbc as [STRb STRc].
    cbn [length] in STRc. replace (name + Z.of_nat (length ns) + Z.of_nat 1) with (name + L + 1) in STRc by (unfold L; lia). fold L in STRb.
    eapply (sr_evt_krel H HH); [exact KREL| eapply ah_segA with (lo := lo) (ns := ns) (slk := slk); unfold zlength, VPM_SIZE; fold L;
      try first [exact VC| exact STRa| exact STRb| exact STRc| exact NONUL| exact PAL| exact SPAL| exact ST| exact CEIL| exact MI]; try lia|].
    intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & LEN1 & FR1 & VC1 & BS1).
    fold L in LEN1.
    assert (XP1 : xpres LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    pose proof (stk_release usegs m1 lo _ _ ST1 LEN1 ltac:(lia)) as ST1a. cbn [cells_size csize Nat.add] in ST1a.
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in ST1a by lia.
    pose proof (stk_release usegs m1 lo _ _ ST1a FR1 ltac:(lia)) as ST1b. cbn [cells_size csize Nat.add] in ST1b.
    replace (bv_unsigned sp + -40 + Z.of_nat 40) with (bv_unsigned sp) in ST1b by lia.
    destruct (hostname_ok ns) eqn:HOK.
    - (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL| eapply ah_segT with (a := a); [lia| unfold VPM_SIZE; lia| exact LEN1| exact FR1| exact MI1]|].
      intros ms2 ->.
      pose proof (addstr_spec H HX) as ASP. unfold addstr_stmt in ASP.
      eapply (sr_seq H HH).
      { eapply ASP with (lo := lo) (B := B) (LB := LB) (s := s) (v := 1) (a := a) (pa := vp_id V) (pn := pn) (ns := ns);
          unfold zlength; fold L; rewrite ?unsigned_lit by lia; try reflexivity.
        all: try first [exact VC1| exact VIN| exact NIN| exact BS1| exact NONUL| exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL
                        | exact MI1| exact MF1| exact IM1| exact GM1].
        all: lazymatch goal with
             | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR1
             | |- lb_bytes _ + _ <= _ => unfold ADDSTR_BYTES, XBUF_SIZE, SK_SIZE, zlength; fold L; lia
             | |- _ <= _ - ADDSTR_STACK =>
                 unfold ADDSTR_STACK, FR_add_string_to_buffer_stack, CSTRNDUP_STACK, SKNEW_STACK, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK,
                   CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK, FR_sk_new, FR_sk_insert, FR_sk_reserve,
                   CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia
             | |- _ mod 2 = 0 => unfold AH_R2; reflexivity
             | |- _ => try lia
             end.
        }
      clear ASP. intros [ms3 mo3] PO. unfold addstr_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & s3' & st & K & X & NB &
                      -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & XP3 & HEAP3 & VC3 & HOS3 & XL & PNB & LNB & BNB & GNB & MF3 & IM3 & GM3).
      rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST3, XP3 by lia.
      assert (LEN3 : rw_cells usegs m3 (bv_unsigned sp + -48) [C8 (wz L)]).
      { eapply xpres_rw_cells'; [exact XP3| exact LEN1| left; cbn; lia| unfold memflag_foot, A_mem_inited; repeat (apply Forall_cons; [cbn; blia1 POFF|]); apply Forall_nil]. }
      assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply xpres_rw_cells'; [exact XP3| exact FR1| left; cbn; lia| unfold memflag_foot, A_mem_inited; repeat (apply Forall_cons; [cbn; blia1 POFF|]); apply Forall_nil]. }
      eapply (sr_evt_krel H HH); [exact KREL3| eapply ah_segE; [exact LEN3| exact FR3| exact MI3]|].
      intros ms4 ->.
      pose proof (stk_release usegs m3 lo _ _ ST3 LEN3 ltac:(lia)) as ST3a. cbn [cells_size csize Nat.add] in ST3a.
      replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in ST3a by lia.
      pose proof (stk_release usegs m3 lo _ _ ST3a FR3 ltac:(lia)) as ST3b. cbn [cells_size csize Nat.add] in ST3b.
      replace (bv_unsigned sp + -40 + Z.of_nat 40) with (bv_unsigned sp) in ST3b by lia.
      apply (sr_done H HH). unfold add1host_post. cbn [cfg_ms cfg_model]. rewrite HOK.
      exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m3, errv3, s3', (mkVPM st (Some (K, [X])) (vp_id V)), NB.
      split; [reflexivity|]. split; [exact KREL3|]. split; [exact MP3|]. split; [exact MI3|]. split; [exact ST3b|]. split; [exact ERR3|]. split; [exact AUX3|].
      split; [eapply xpres_trans; [exact XP1| eapply xpres_weaken; [exact XP3| lia| auto| auto]]|].
      split; [exact HEAP3|].
      split. { unfold VPMobj. cbn [vp_hosts vp_hosts_o vp_id]. rewrite vpm_cells_h_eq. cbn [vp_hosts]. split; [exact VC3|]. split; [apply in_or_app; right; exact VIN| exact HOS3]. }
      split; [reflexivity|].
      split. { unfold blocks_VPM. cbn [vp_hosts vp_hosts_o vp_id]. apply perm_skip. exact PNB. }
      split; [intros; discriminate|].
      split; [intros _; exists K, X; split; [reflexivity| exact XL]|].
      split; [lia|]. split; [unfold ADD1HOST_BYTES; rewrite BNB; unfold ADDSTR_BYTES, XBUF_SIZE, SK_SIZE, zlength; fold L; lia|]. split; [exact GNB|].
      split; [exact MF3|]. split; [exact IM3| exact GM3].
    - (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL| eapply ah_segR; [exact LEN1| exact FR1| exact MI1]|].
      intros ms2 ->.
      apply (sr_done H HH). unfold add1host_post. cbn [cfg_ms cfg_model]. rewrite HOK.
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, errv, s, V, (@nil block).
      split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI1|]. split; [exact ST1b|].
      split; [rewrite errno_RATP; exact ERR1|]. split; [exact AUX1|].
      split; [exact XP1|]. cbn [app].
      split; [exact HP1|].
      split. { unfold VPMobj. rewrite vpm_cells_h_eq, VH. split; [exact VC1|]. split; [exact VIN|]. rewrite VHO. reflexivity. }
      split; [reflexivity|].
      split. { unfold blocks_VPM. rewrite VH, VHO. cbn. apply Permutation_refl. }
      split; [intros _; split; reflexivity|]. split; [intros; discriminate|].
      split; [cbn; lia|]. split; [unfold ADD1HOST_BYTES, SK_SIZE; cbn; lia|]. split; [reflexivity|].
      split; [exact MF1|]. split; [exact IM1| exact GM1].
  Qed.
End W.
