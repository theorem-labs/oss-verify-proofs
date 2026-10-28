(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 SecLazy ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AKit ECH_AsKit N6_iface
  ECH_AC1_malloc ECH_AC1_zalloc ECH_AC1_free ECH_AC1_dup ECH_AC5_small ECH_AC5_new ECH_AC5_push ECH_AC13_small ECH_AC13_ext ECH_AC13_entry ECH_AC12_xbuf ECH_AC12_vpmfree.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AAS_R1 : Z := 0x432968.
Definition AAS_R2 : Z := 0x43298c.   Definition AAS_R3 : Z := 0x432a0c.   Definition AAS_R4 : Z := 0x432a20.
Definition AAS_R6 : Z := 0x432a54.   Definition AAS_R10 : Z := 0x432aac.
Definition AVPMS_FILE : Z := 0xc3200.
Definition ASHB12s : Z := 0x7fff8000.
Definition aas_frame (j : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition ahosts_fresh (id did : bptr) : skrep :=
  mkSK [] 0 0 1 P_buffer_cmp P_sk_X509_BUFFER_cmp_thunk P_sk_X509_BUFFER_freefunc_thunk P_sk_X509_BUFFER_copy_thunk id did.
Lemma ahosts_fresh_eq : forall id did,
  sk_with_thunk (sk_with_thunk (sk_with_thunk (sk_fresh P_buffer_cmp id did) O_SK_CMPTH P_sk_X509_BUFFER_cmp_thunk)
                               O_SK_COPYTH P_sk_X509_BUFFER_copy_thunk) O_SK_FREETH P_sk_X509_BUFFER_freefunc_thunk
  = ahosts_fresh id did.
Proof. intros. reflexivity. Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Local Ltac reacc ACC0 MU NSW n :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let A := fresh "ACC" in
      assert (A : accessible mx _ n) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]) end.
  Local Ltac reAC AC0 MU WM AW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let A := fresh "ACN" in
      assert (A : ACONST mx) by (unfold id in AC0; eapply ACONST_frame; [exact AC0| exact MU| exact WM| exact AW]) end.
  Local Ltac null_call SPEC ST CEIL ACN MU WM :=
    eapply evt_cut;
    [ eapply SPEC; rewrite ?unsigned_lit by lia; [exact ST| exact CEIL| unfold FR_sk_pop_free; lia| | exact ACN];
      lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
    | ];
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; unfold sknull_post in PO;
    let m' := fresh "m" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI" in let AC' := fresh "ACN" in let ST' := fresh "ST" in
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU' & WM' & MI' & AC' & ST');
    retpc; rewrite ?unsigned_lit in MU', ST' by lia;
    clear ST ACN; lazymatch goal with H : mem_inv _ ?mx |- _ => lazymatch type of MU' with munch _ mx _ => clear H | _ => idtac end end;
    carry MU' WM'; extend_munch MU WM MU' WM'; rename ST' into ST; rename AC' into ACN.

  (* [comment removed for export] *)
  Lemma aas_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ph name L lo : Z),
      0 <= ph < 2^64 -> 0 <= name < 2^64 -> 0 <= L < 2^64 ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 AAS_R1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 16) (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 59) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ph) (Z_to_bv 64 L) (Z_to_bv 64 name) (Z_to_bv 64 ASHB12s) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells asegs m1 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ph) (Z_to_bv 64 name) (Z_to_bv 64 L) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_add_string_to_buffer_stack) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros PHR NR LR GSB SHB0 ST CEIL LO MI. unfold P_add_string_to_buffer_stack, P_CRYPTO_zalloc, AAS_R1, AVPMS_FILE, ASHB12s.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    do 9 step. do 12 step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma aas_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3w s4w s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A1 name L : Z),
      0 < A1 < 2^64 -> s4w = Z_to_bv 64 name -> s3w = Z_to_bv 64 L ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AAS_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1)
                       s4w s3w (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 62) a4 a5 a6 a7
                       s2 s3w s4w s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AAS_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3w s4w s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AAS_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until L. intros A1R -> ->. unfold AAS_R1, AAS_R2, AVPMS_FILE, P_CRYPTO_strndup. retpc.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 8 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aas_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A1 A2 lo : Z) (ns slack : list byte),
      0 < A1 -> A1 mod 16 = 0 -> A1 + XBUF_SIZE <= lo -> aapp A1 XBUF_SIZE -> accessible m A1 XBUF_SIZE ->
      0 < A2 -> A2 + zlength ns + 1 + zlength slack <= lo ->
      rw_cells asegs m A1 [C8 (wz 0); C8 (wz 0)] ->
      bytes_at asegs m A2 (ns ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) ns -> (- (A2 + zlength ns + 1)) mod 8 <= zlength slack ->
      accessible m A2 (zlength ns + 1) -> shvis m A2 (A2 + zlength ns + 1) -> in_app_mem A2 (A2 + zlength ns + 1) ->
      1 <= zlength ns <= 255 -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AAS_R3) sp gp tp u0 u1 u2 s0 (Z_to_bv 64 A1)
                       (Z_to_bv 64 0) (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 75) b3 b4 b5 b6 b7
                       s2 (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 0) (Z_to_bv 64 ASHB12s) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (A1, A1 + XBUF_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 A1 [C8 (wz A2); C8 (wz (zlength ns))])
        (MS (mkR (Z_to_bv 64 AAS_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1) (Z_to_bv 64 A2) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (zlength ns)) s4x (Z_to_bv 64 ASHB12s) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AAS_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until slack. intros A1P A1AL A1L AP1 ACC1 A2P A2L XB STR NONUL PAD ACC2 SHV2 IAM2 LR AC0 ST CEIL LO MI.
    unfold AAS_R2, AAS_R3, AVPMS_FILE, ASHB12s, P_CRYPTO_free. retpc.
    unfold wz in XB. unfold XBUF_SIZE in *. unfold zlength in *.
    pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold AINTRIN_STACK in LO.
    pose proof ACC1 as (_ & AHI1 & _). pose proof ACC2 as (_ & AHI2 & _). unfold AAPP_HI in AHI1, AHI2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (A1, A1 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (A1, A1 + 16)]).
    { constructor; [cbn; unfold AHI_LO; lia|]. constructor; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP1)| constructor]. }
    assert (AW : Forall aconst_ok [(lo, bv_unsigned sp); (A1, A1 + 16)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      constructor; [eapply aconst_ok_aapp; [exact AP1| cbn; lia| cbn; lia]| constructor]. }
    change (id (accessible m A1 16)) in ACC1.
    (* [comment removed for export] *)
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). step. step. step.
    eapply evt_cut.
    { eapply strlen_icpt_ok with (str := ns) (slack := slack) (lo := lo); rewrite ?unsigned_lit by lia;
        first [exact STR| exact NONUL| exact PAD| exact ACC2| exact SHV2| exact ST| exact CEIL| exact AC0| exact IAM2| lia | unfold AINTRIN_STACK; lia
              | lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
              | match goal with |- ?G => idtac "LEFTS:" G end]. }
    unfold astrlen_post. intros ms' PO.
    destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mc & -> & MU' & WM' & MI' & ST' & STR' & AC').
    retpc. rewrite ?unsigned_lit in MU', ST', STR' by lia. unfold AINTRIN_STACK in MU'. clear ST STR'. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI. rename ST' into ST.
    (* [comment removed for export] *)
    step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
            replace c with false by (symmetry; rewrite bv_eqb_refl; reflexivity); cbv iota | _ => idtac end.
    (* [comment removed for export] *)
    step. ubal_by A1AL. step. if_lit. zstep. zstep. reacc ACC1 MU NSW 16. ck8_check ACC A1. clear ACC. st1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. reacc ACC1 MU NSW 16. ck8_check ACC (A1 + 8). clear ACC. step. st1.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    reAC AC0 MU WM AW.
    finish. all: try exact ACN.
  Qed.

  (* [comment removed for export] *)
  Lemma aas_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AAS_R4) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 0) (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 76) a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AAS_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 AVPMS_FILE) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AAS_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. unfold AAS_R3, AAS_R4, AVPMS_FILE, P_CRYPTO_free. retpc.
    do 5 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aas_seg5 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a A1 : Z),
      0 < A1 < 2^64 -> 0 < a -> a mod 16 = 0 -> a + VPM_SIZE < 2^64 -> rw_cells asegs m a (vpm_cells_h 0) -> accessible m a VPM_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AAS_R6) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1)
                       (Z_to_bv 64 P_buffer_cmp) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (a + O_VPM_HOSTS)) (Z_to_bv 64 0) s4 (Z_to_bv 64 (Z.shiftr (a + O_VPM_HOSTS) 3 + ASHB12s)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_new) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AAS_R4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (a + O_VPM_HOSTS)) s3 s4 (Z_to_bv 64 ASHB12s) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AAS_R4)) fc None m (seg_rom asegs)).
  Proof.
    intros until A1. intros A1R AP AAL AH BLK ACC MI. unfold AAS_R4, AAS_R6, ASHB12s, P_buffer_cmp, P_OPENSSL_sk_new, O_VPM_HOSTS. retpc.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    (* [comment removed for export] *)
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. ubal_by AAL. step. if_lit. zstep. zstep. ck8_check ACC (a + 56).
    (* [comment removed for export] *)
    step. step. try if_lit.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
            replace c with false by (symmetry; rewrite bv_eqb_refl; reflexivity); cbv iota | _ => idtac end.
    do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aas_seg7 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s1x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a st lo : Z) (j : list byte),
      0 < a -> a + VPM_SIZE <= lo -> aapp a VPM_SIZE -> accessible m a VPM_SIZE -> 0 <= st < 2^64 ->
      rw_cells asegs m a (vpm_cells_h 0) ->
      rw_cells asegs m (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra) -> ACONST m ->
      stk asegs m lo (bv_unsigned sp + -64) -> aceil <= lo -> lo <= bv_unsigned sp + -64 - FR_sk_pop_free -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR ra sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (a, a + VPM_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 a (vpm_cells_h st))
        (MS (mkR (Z_to_bv 64 AAS_R10) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1x
                 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (a + O_VPM_HOSTS)) (Z_to_bv 64 st) s4x (Z_to_bv 64 (Z.shiftr (a + O_VPM_HOSTS) 3 + ASHB12s))
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AAS_R10)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros AP AL AAP ACC0 STR BLK FR AC0 ST CEIL LO MI.
    unfold AAS_R10, ASHB12s, O_VPM_HOSTS, P_OPENSSL_sk_set_thunks, P_OPENSSL_sk_pop_free, P_sk_X509_BUFFER_freefunc_thunk, P_buffer_free. retpc.
    unfold vpm_cells_h, wz in BLK |- *. unfold VPM_SIZE in *. unfold aas_frame in FR.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold FR_sk_pop_free in LO.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 136)]).
    { constructor; [cbn; unfold AHI_LO; lia|]. constructor; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AAP)| constructor]. }
    assert (AW : Forall aconst_ok [(lo, bv_unsigned sp); (a, a + 136)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      constructor; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]| constructor]. }
    change (id (accessible m a 136)) in ACC0. change (id (ACONST m)) in AC0.
    (* [comment removed for export] *)
    step. try if_lit.
    reacc ACC0 MU NSW 136. ck8_load ACC (a + 56). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    step. st1. step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step.
    reAC AC0 MU WM AW. null_call (askset_thunks_null_spec) ST CEIL ACN MU WM.
    (* [comment removed for export] *)
    step. step. step. step. null_call (ask_pop_free_null_spec) ST CEIL ACN MU WM.
    (* [comment removed for export] *)
    step. step.
    carve_frame 32%nat ST.
    do 5 st1. step. step. try if_lit. do 4 step. step. step.
    lazymatch goal with FRb : rw_cells _ _ (bv_unsigned sp + -96) _ |- _ => release_frame FRb ST (bv_unsigned sp + -64) end.
    (* [comment removed for export] *)
    step. do 7 st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    clear ACN. reAC AC0 MU WM AW.
    finish. all: try exact ACN.
  Qed.
End S.

Section S6.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Lemma sk_shad_transport0 : forall W m m' st K K', SK_shad m st K -> sk_cap K' = 0 -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W (sh st) (nsh SK_SIZE) -> SK_shad m' st K'.
  Proof.
    intros W m m' st K K' [SKH SKD] C0 MU WM DJ. split; [| intros NC; exfalso; exact (NC C0)].
    eapply addressable_transport; [exact SKH| exact MU| exact WM| exact DJ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac set_call SPEC ST CEIL ACN SKO SKSH SKR BEL MU WM DJ :=
    eapply evt_cut;
    [ eapply SPEC; rewrite ?unsigned_lit by lia;
        [reflexivity| reflexivity| unfold P_sk_X509_BUFFER_cmp_thunk, P_sk_X509_BUFFER_copy_thunk, P_sk_X509_BUFFER_freefunc_thunk; lia
        | exact SKO| exact BEL| exact SKSH| exact SKR| exact ACN| exact ST| exact CEIL| lia| ];
      lazymatch goal with Hm : mem_inv _ ?mx |- mem_inv _ ?my => exact Hm end
    | ];
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; unfold skset_post in PO;
    let m' := fresh "m" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI" in let AC' := fresh "ACN" in let ST' := fresh "ST" in let SO' := fresh "SKO" in
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU' & WM' & MI' & AC' & ST' & SO');
    retpc; rewrite ?unsigned_lit in MU', ST' by lia; unfold SK_SIZE in MU';
    (let SKSH' := fresh "SKSH" in
     lazymatch type of SO' with SKobj _ _ ?stv ?Kv =>
       assert (SKSH' : SK_shad m' stv Kv)
         by (eapply sk_shad_transport0; [exact SKSH| reflexivity| exact MU'| exact WM'| exact DJ]) end;
     clear SKSH; rename SKSH' into SKSH);
    clear ST ACN SKO; lazymatch goal with Hm : mem_inv _ ?mx |- _ => lazymatch type of MU' with munch _ mx _ => clear Hm | _ => idtac end end;
    carry MU' WM'; extend_munch MU WM MU' WM'; rename ST' into ST; rename AC' into ACN; rename SO' into SKO.

  (* [comment removed for export] *)
  Lemma aas_seg6 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (A1 st lo : Z) (id did : bptr),
      SKobj LB m st (sk_fresh P_buffer_cmp id did) -> SK_shad m st (sk_fresh P_buffer_cmp id did) -> SK_ranges H st (sk_fresh P_buffer_cmp id did) ->
      st + SK_SIZE <= aceil -> aapp st SK_SIZE -> 0 <= A1 < 2^64 -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AAS_R10) sp gp tp u0 u1 u2 s0 (Z_to_bv 64 A1)
                       (Z_to_bv 64 st) (Z_to_bv 64 A1) b2 b3 b4 b5 b6 b7
                       s2 (Z_to_bv 64 st) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (st, st + SK_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ SKobj LB m1 st (ahosts_fresh id did) /\ SK_shad m1 st (ahosts_fresh id did))
        (MS (mkR (Z_to_bv 64 AAS_R6) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
                 s2 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AAS_R6)) fc None m (seg_rom asegs)).
  Proof.
    intros until did. intros SKO SKSH SKR BL AAP A1R ACN ST CEIL LO MI.
    unfold AAS_R6, AAS_R10, P_OPENSSL_sk_push. retpc.
    pose proof SKO as SO'. destruct SO' as (_ & POS & _).
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (sh_aapp_range st 56 AAP ltac:(lia)) as (HS1 & HS2 & HS3). unfold AHI_LO in HS3. assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in HS1.
    pose proof (munch_refl [(lo, bv_unsigned sp); (st, st + SK_SIZE)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold SK_SIZE in MU. unfold SK_SIZE in BL.
    assert (BEL : SK_below st (sk_fresh P_buffer_cmp id did) lo) by (split; [unfold SK_SIZE; lia| left; reflexivity]).
    assert (DJ : disjoint_from [(lo, bv_unsigned sp); (st, st + 56)] (sh st) (nsh SK_SIZE)).
    { clear - AAP CEIL LO0 SPR ACEILB LO. unfold SK_SIZE, nsh in *. cbn. destruct AAP as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO, AIMG_TOP, sh in *; rewrite ?ASHADOW_BASE_val in *; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    do 6 step.
    set_call (askset_cmp_thunks_spec H) ST CEIL ACN SKO SKSH SKR BEL MU WM DJ.
    (* [comment removed for export] *)
    do 5 step.
    assert (BEL2 : SK_below st (sk_with_thunk (sk_fresh P_buffer_cmp id did) O_SK_CMPTH P_sk_X509_BUFFER_cmp_thunk) lo) by exact BEL.
    assert (SKR2 : SK_ranges H st (sk_with_thunk (sk_fresh P_buffer_cmp id did) O_SK_CMPTH P_sk_X509_BUFFER_cmp_thunk)) by exact SKR.
    set_call (askset_copy_thunks_spec H) ST CEIL ACN SKO SKSH SKR2 BEL2 MU WM DJ.
    (* [comment removed for export] *)
    do 5 step.
    assert (BEL3 : SK_below st (sk_with_thunk (sk_with_thunk (sk_fresh P_buffer_cmp id did) O_SK_CMPTH P_sk_X509_BUFFER_cmp_thunk) O_SK_COPYTH P_sk_X509_BUFFER_copy_thunk) lo) by exact BEL.
    assert (SKR3 : SK_ranges H st (sk_with_thunk (sk_with_thunk (sk_fresh P_buffer_cmp id did) O_SK_CMPTH P_sk_X509_BUFFER_cmp_thunk) O_SK_COPYTH P_sk_X509_BUFFER_copy_thunk)) by exact SKR.
    set_call (askset_thunks_spec H) ST CEIL ACN SKO SKSH SKR3 BEL3 MU WM DJ.
    (* [comment removed for export] *)
    step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 4 step.
    finish. all: rewrite <- ?ahosts_fresh_eq; try assumption.
  Qed.
End S6.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac blia1 H1 := let T1 := fresh "T_" in pose proof H1 as T1; unfold boxed in T1; cbn; lia.
Ltac blia2 H1 H2 := let T1 := fresh "T_" in let T2 := fresh "T_" in pose proof H1 as T1; pose proof H2 as T2; unfold boxed in T1, T2; cbn; lia.

Lemma strnlen_full : forall ns, ~ In (Z_to_bv 8 0) ns -> strnlen ns = length ns.
Proof.
  induction ns as [|b ns IH]; intros NI; [reflexivity|]. cbn [strnlen length].
  destruct (bv_unsigned b =? 0) eqn:E.
  - exfalso. apply NI. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
  - f_equal. apply IH. intros K. apply NI. right. exact K.
Qed.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis ASLACK : as_slack_law H.

  Definition AADDSTR_BYTES (ns : list byte) : Z := XBUF_SIZE + (zlength ns + 1) + SK_SIZE + 32.
  Definition AADDSTR_COST (ns : list byte) : Z := as_Cm H XBUF_SIZE + as_Cm H (zlength ns + 1) + as_Cm H SK_SIZE + as_Cm H 32 + 3 * as_Cf H 0.

  Definition aaddstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (a : Z) (ns : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (st : Z) (K : skrep) (X : xbufrep) (NB : list block),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m'
      /\ as_RHEAP H s' (NB ++ LB) m'
      /\ rw_cells asegs m' a (vpm_cells_h st) /\ HOSTS (NB ++ LB) m' st (Some (K, [X])) /\ xb_len X = zlength ns
      /\ HOSTS_shad m' st (Some (K, [X]))
      /\ Permutation (blocks_HOSTS st (Some (K, [X]))) NB
      /\ Z.of_nat (length NB) = 4 /\ lb_bytes NB = AADDSTR_BYTES ns
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ addressable m' a VPM_SIZE
      /\ as_AL H s' >= as_AL H s - AADDSTR_COST ns.
  Definition aaddstr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
           (a name v lo B : Z) (pa : bptr) (bN : block) (ns : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_add_string_to_buffer_stack) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 (a + O_VPM_HOSTS) -> a1 = Z_to_bv 64 name -> a2 = Z_to_bv 64 (zlength ns) ->
      rw_cells asegs m a (vpm_cells_h 0) -> In (pa, a, VPM_SIZE) LB -> addressable m a VPM_SIZE ->
      bytes_at asegs m name ns -> In bN LB -> blk_addr bN <= name -> name + zlength ns <= blk_addr bN + blk_size bN ->
      accessible m name (zlength ns) -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns <= 255 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + AADDSTR_BYTES ns <= as_LIVE_MAX H -> Z.of_nat (length LB) + 4 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADDSTR_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_addstr (bv_unsigned ra) CH ->
      AADDSTR_COST ns <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      as_SR H (aaddstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a ns lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Lemma awr_at_bytes : forall m A n,
    wr_at asegs m A n -> 0 <= n -> AIMG_TOP <= A -> exists junk, Z.of_nat (length junk) = n /\ bytes_at asegs m A junk.
  Proof.
    intros m A n (HA & HN & W) Hn OFF. unfold AIMG_TOP in OFF.
    exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
    rewrite length_map, length_seq. split; [lia|].
    split; [exact HA|]. split; [rewrite length_map, length_seq; lia|].
    intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite nth_error_map, nth_error_seq. destruct (PeanoNat.Nat.ltb_spec0 i (Z.to_nat n)); [| lia]. cbn [option_map Nat.add].
    specialize (W (Z.of_nat i) ltac:(lia)). unfold wview in W. unfold mrd, wa in *.
    destruct (m (Z_to_bv 64 (A + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
    exfalso. apply W. unfold seg_rom, memory_read. rewrite unsigned_lit by lia. rewrite asegs_find_segment_none_high by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afresh_sh_outside : forall s' LB m' p A n SP q,
    as_RHEAP H s' ((p, A, n) :: LB) m' -> aceil <= SP -> aclient_addr H LB SP q -> sh A <= q < sh A + nsh n -> False.
  Proof.
    intros s' LB m' p A n SP q RH CE HC Hq. acb.
    pose proof (ah_blocks H HH _ _ _ _ RH (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof (sh_aapp_range A n B7 B3) as (S1 & S2 & S3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (A8 : A mod 8 = 0) by (clear - B2; Z.div_mod_to_equations; lia).
    unfold aclient_addr, in_block, in_block_sh in HC.
    destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]].
    - unfold AHI_LO in *. lia.
    - unfold aimg_client, AIMG_TOP in *. lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH (or_intror Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      unfold aapp, aapp_lo, aapp_hi in C7. unfold sh, nsh, ALOWSH_LO, AHI_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      destruct C7 as [[P1 P2]|[P1 P2]]; Z.div_mod_to_equations; lia.
    - pose proof (ah_nodup H HH _ _ _ RH) as ND. cbn [map blk_id fst snd] in ND. inversion ND as [|x l NI ND']; subst.
      assert (NE : blk_id (p, A, n) <> blk_id b) by (cbn [blk_id fst snd]; intros E; apply NI; rewrite E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ _ _ RH (or_introl eq_refl) (or_intror Hb) NE) as D. cbn [blk_addr blk_size fst snd] in D.
      pose proof (ah_blocks H HH _ _ _ _ RH (or_intror Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      assert (C8 : blk_addr b mod 8 = 0) by (clear - C2; Z.div_mod_to_equations; lia).
      clear - D Hr Hq A8 C8 B3 C3 B1 C1. unfold sh, nsh in *. Z.div_mod_to_equations. nia.
    - rewrite S0 in S1. destruct F4 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *; lia.
    - assert (F8 : as_FSB H mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
      clear - HC Hq B6 A8 F8 B1 B3 F1. unfold sh, nsh, AFS_SIZE, AIMG_TOP in *. Z.div_mod_to_equations. nia.
    - lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_drop_windows : forall (LB LBx : list block) SP X Y m m',
    xpres H LBx SP (X ++ Y) m m' -> (forall b, In b LB -> In b LBx) ->
    (forall q, rin_ivs Y q -> aclient_addr H LB SP q -> False) -> xpres H LB SP X m m'.
  Proof.
    intros LB LBx SP X Y m m' XP SUB HY q Hq [C NX]. apply XP; [exact Hq|]. split.
    - eapply aclient_addr_weaken; [exact C| lia| exact SUB].
    - rewrite rin_ivs_app. intros [K|K]; [exact (NX K)| exact (HY q K C)].
  Qed.

  (* [comment removed for export] *)
  Lemma addressable_xpres_blkX : forall LB2 m m' SP X p A n,
    In (p, A, n) LB2 -> A + n <= AAPP_HI -> addressable m A n -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => sh A + nsh n <= fst iv \/ snd iv <= sh A) X -> addressable m' A n.
  Proof.
    intros LB2 m m' SP X p A n IN Htop (Hn & A0 & A8 & (B0 & B1 & BA) & (W0 & W1 & WA)) XP FX. acb.
    assert (CL : forall i, 0 <= i < nsh n -> m' (wa (sh A + i)) = m (wa (sh A + i)) /\ (wview asegs m (wa (sh A + i)) <> None -> wview asegs m' (wa (sh A + i)) <> None)).
    { intros i Hi. apply XP.
      - unfold nsh in Hi. unfold sh, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
      - split.
        + right; right; right; left. exists (p, A, n). split; [exact IN|]. cbn [blk_addr blk_size fst snd]. lia.
        + clear - FX Hi. induction X as [|[l h] X IH]; [intros K; exact K|]. cbn. intros [K|K].
          * pose proof (Forall_inv FX) as F1. cbn in F1. lia.
          * exact (IH (Forall_inv_tail FX) K). }
    split; [exact Hn|]. split; [exact A0|]. split; [exact A8|]. split.
    - split; [exact B0|]. split; [exact B1|].
      intros i Hi. rewrite <- (BA i Hi). unfold mrd. destruct (CL (Z.of_nat i) ltac:(pose proof (shadow_of_length n Hn); lia)) as [E _]. rewrite E. reflexivity.
    - split; [exact W0|]. split; [exact W1|].
      intros i Hi. destruct (CL i ltac:(pose proof (shadow_of_length n Hn); lia)) as [_ Wp]. apply Wp. apply WA. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma chain_via_xpres : forall LB SP X m m' cur CH,
    as_chain H m cur CH -> xpres H LB SP X m m' -> (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) ->
    Forall (fun iv : Z * Z => snd iv <= aceil) X -> as_chain H m' cur CH.
  Proof.
    intros LB SP X m m' cur CH C XP HS FX. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3).
    apply XP; [acb; lia|]. split; [left; lia|].
    clear - FX Ha R1. induction X as [|[l h] X IH]; [intros K; exact K|]. cbn. intros [K|K].
    - pose proof (Forall_inv FX) as F1. cbn in F1. lia.
    - exact (IH (Forall_inv_tail FX) K).
  Qed.

  (* [comment removed for export] *)
  Lemma app_sh_disjoint : forall lo hi B k A0 n,
    aapp B k -> 0 <= k -> aapp A0 n -> 0 <= n -> aceil <= lo -> disjoint_from [(lo, hi); (B, B + k)] (sh A0) (nsh n).
  Proof.
    intros lo hi B k A0 n APB Hk AP0 Hn CE. acb. unfold nsh. cbn. pose proof (sh_aapp_range A0 n AP0 Hn) as (X1 & X2 & X3).
    clear AP0. destruct APB as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO, AIMG_TOP, sh, nsh in *; rewrite ?ASHADOW_BASE_val in *; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memflag_below_sh : forall A0 n, aapp A0 n -> 0 <= n ->
    Forall (fun iv : Z * Z => sh A0 + nsh n <= fst iv \/ snd iv <= sh A0) memflag_foot.
  Proof.
    intros A0 n AP Hn. pose proof (sh_aapp_range A0 n AP Hn) as (X1 & X2 & X3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in X1.
    unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma sh_disjoint_blocks : forall A n B k, A mod 8 = 0 -> B mod 8 = 0 -> 0 <= n -> 0 <= k ->
    (A + n + 16 <= B \/ B + k + 16 <= A) -> sh A + nsh n <= sh B \/ sh B + nsh k <= sh A.
  Proof. intros A n B k HA HB Hn Hk D. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Lemma app_vs_sh : forall A n B k, aapp A n -> 0 <= n -> aapp B k -> 0 <= k -> A + n <= sh B \/ sh B + nsh k <= A.
  Proof.
    intros A n B k APA Hn APB Hk. acb. pose proof (sh_aapp_range B k APB Hk) as (X1 & X2 & X3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in X1.
    clear APB. destruct APA as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sh_vs_app : forall A n B k, aapp A n -> 0 <= n -> aapp B k -> 0 <= k -> sh A + nsh n <= B \/ B + k <= sh A.
  Proof. intros A n B k APA Hn APB Hk. pose proof (app_vs_sh B k A n APB Hk APA Hn). lia. Qed.

  Lemma aaddstr_spec : aaddstr_stmt.
  Proof.
    unfold aaddstr_stmt. intros until CH.
    intros VIS A0 A1 A2 BLK PIN SHA BS NIN NB1 NB2 ACCN NONUL LR HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM RAE. subst a0 a1 a2.
    unfold ADDSTR_STACK, FR_add_string_to_buffer_stack, CSTRNDUP_STACK, SKNEW_STACK, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK,
      CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, AREALLOC_STACK, FR_sk_new, FR_sk_insert, FR_sk_reserve,
      CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK in LO.
    unfold AADDSTR_BYTES, XBUF_SIZE, SK_SIZE in BUD. unfold AADDSTR_COST, XBUF_SIZE, SK_SIZE in HAL.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -64) by lia.
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _). exact Q5. }
    pose proof (bytes_at_bound _ _ _ _ BS) as BSB. unfold zlength in *. set (L := Z.of_nat (length ns)) in *.
    pose proof (ah_blocks H HH _ _ _ _ HP PIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. unfold VPM_SIZE in K3, K5, K7. clear K6.
    pose proof (ah_blocks H HH _ _ _ _ HP NIN) as (N1 & N2 & N3 & N4 & N5 & N6 & N7). unfold AIMG_TOP in N4.
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0. pose proof (proj1 (ah_costs H HH)) as CM0.
    pose proof (CF0 0 ltac:(lia)) as CFZ. pose proof (CM0 16 ltac:(lia)) as CM16. pose proof (CM0 (L + 1) ltac:(lia)) as CML. pose proof (CM0 56 ltac:(lia)) as CM56. pose proof (CM0 32 ltac:(lia)) as CM32.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aas_seg1 with (lo := lo);
      [unfold O_VPM_HOSTS; lia| lia| unfold L; lia| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -64, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m1)
      by (eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold aas_frame in FR2.
      change ([CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul Pos.add] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -64 + 48) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -64 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -64) mod 16 = 0) by (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW AW.
    assert (BLK1 : rw_cells asegs m1 a (vpm_cells_h 0)) by (eapply rw_cells_transport; [exact BLK| exact MU1| exact WM1| unfold vpm_cells_h; cbn; lia]).
    assert (BS1 : bytes_at asegs m1 name ns) by (eapply bytes_at_transport; [exact BS| exact MU1| cbn; lia]).
    pose proof (sh_aapp_range a 136 K7 ltac:(lia)) as (SR1 & SR2 & SR3). unfold AHI_LO in SR3. pose proof aceil_range as ACR.
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in SR1.
    assert (SHA1 : addressable m1 a 136).
    { unfold VPM_SIZE in SHA. eapply addressable_transport; [exact SHA| exact MU1| exact WM1|]. cbn. destruct K7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    assert (ACCN1 : accessible m1 name L).
    { eapply accessible_across; [exact ACCN| exact MU1|]. constructor; [cbn; unfold AHI_LO; lia| constructor]. }
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 16) (size := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold AAS_R1; lia).
      all: first [exact HP1| exact KREL1| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                 | exact MF1| exact IM1| exact GM1| lia | unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                 | unfold AAS_R1; eapply pf_ok_call; [exact PF|]; unfold PF_addstr; intros y Hy; apply in_app_iff; left; exact Hy
                 | match goal with |- ?G => idtac "LEFTZ:" G end]. }
    clear CZ. intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A1 & p1 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR1 & HEAP2 & XB2 & ADDR1 & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, XP2 by lia.
    pose proof BR1 as (A1P & A1M16 & _ & A1TOP & A1C & _ & A1AP). unfold AIMG_TOP in A1TOP.
    pose proof (aapp_bounds A1 16 A1AP ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    set (LB1 := (p1, A1, 16) :: LB) in *.
    assert (SUB01 : forall b, In b LB -> In b LB1) by (intros b Hb; right; exact Hb).
    assert (XB2' : rw_cells asegs m2 A1 [C8 (wz 0); C8 (wz 0)]).
    { eapply arw_cells_recut; [exact XB2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact FR1| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. }
    assert (BLK2 : rw_cells asegs m2 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact BLK1| | unfold memflag_foot, A_mem_inited; constructor; [unfold vpm_cells_h; cbn; lia| constructor]].
      right; right; left. exists (pa, a, VPM_SIZE). split; [exact PIN| unfold vpm_cells_h; cbn; unfold VPM_SIZE; lia]. }
    assert (BS2 : bytes_at asegs m2 name ns).
    { eapply (xpres_bytes_at' H); [exact XP2| exact BS1| | unfold memflag_foot, A_mem_inited; constructor; [cbn; unfold L in *; lia| constructor]].
      right; right; left. exists bN. split; [exact NIN| unfold L in *; lia]. }
    assert (SHA2 : addressable m2 a 136).
    { eapply addressable_xpres_blkX; [exact PIN| unfold AAPP_HI; lia| exact SHA1| exact XP2| exact (memflag_below_sh _ _ K7 ltac:(lia))]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply aas_seg2; [lia| reflexivity| reflexivity]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    assert (FXM : Forall (fun iv : Z * Z => snd iv <= aceil) memflag_foot).
    { unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor]. }
    assert (CH2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply chain_via_xpres; [exact CH1| exact XP2| exact CHS1| exact FXM]).
    assert (NSWM : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) memflag_foot).
    { unfold memflag_foot, A_mem_inited. constructor; [cbn; unfold ALOWSH_LO; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (OBN : ashobj H LB (bv_unsigned sp + -64) name L) by (left; exists bN; split; [exact NIN| split; [exact NB1| exact NB2]]).
    assert (ACCN2 : accessible m2 name L).
    { eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBN| exact ACCN1| exact XP2| exact NSWM]. }
    (* [comment removed for export] *)
    pose proof (acstrndup_spec H HH) as SD. unfold cstrndup_stmt in SD.
    eapply (ah_seq H HH).
    { eapply SD with (lo := lo) (B := B) (LB := LB1) (s := s2') (v := 1) (bs := ns) (bS := bN) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS3| reflexivity| ..]; unfold zlength; fold L; rewrite ?unsigned_lit by (unfold AAS_R2; lia).
      all: first [exact HEAP2| exact KREL3| exact BS2| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16'| exact AC2| exact CH2| exact CHS1
                 | exact MF2| exact IM2| exact GM2| apply SUB01; exact NIN| exact NB1| exact NB2| exact ACCN2 | lia
                 | unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd]; lia
                 | unfold LB1; cbn [length]; lia
                 | unfold CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                 | unfold AAS_R2; eapply pf_ok_call; [exact PF|]; unfold PF_addstr; intros y Hy; apply in_app_iff; right; apply in_app_iff; left; exact Hy
                 | match goal with |- ?G => idtac "LEFTD:" G end]. }
    clear SD. intros [msF4 mo4] PO. unfold cstrndup_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & A2 & p2 & s4' &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & BR2 & HEAP4 & CP4 & ADDR2 & MF4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST4, XP4 by lia.
    pose proof (strnlen_full ns NONUL) as SL.
    cbv zeta in BR2, HEAP4, CP4, ADDR2, AL4. rewrite ?SL in BR2. rewrite ?SL in HEAP4. rewrite ?SL, ?firstn_all in CP4. rewrite ?SL in ADDR2. rewrite ?SL in AL4. fold L in BR2, HEAP4, ADDR2, AL4.
    pose proof BR2 as (A2P & A2M16 & _ & A2TOP & A2C & _ & A2AP). unfold AIMG_TOP in A2TOP.
    pose proof (aapp_bounds A2 (L + 1) A2AP ltac:(lia)) as (AB21 & AB22 & AB23 & AB24 & AB25). unfold AAPP_HI in AB23.
    set (LB2 := (p2, A2, L + 1) :: LB1) in *.
    assert (SUB12 : forall b, In b LB1 -> In b LB2) by (intros b Hb; right; exact Hb).
    assert (XB4 : rw_cells asegs m4 A1 [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H); [exact XP4| exact XB2'| | unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      right; right; left. exists (p1, A1, 16). split; [unfold LB1; left; reflexivity| cbn; lia]. }
    assert (BLK4 : rw_cells asegs m4 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' H); [exact XP4| exact BLK2| | unfold memflag_foot, A_mem_inited; constructor; [unfold vpm_cells_h; cbn; lia| constructor]].
      right; right; left. exists (pa, a, VPM_SIZE). split; [apply SUB01; exact PIN| unfold vpm_cells_h; cbn; unfold VPM_SIZE; lia]. }
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP4| exact FR2| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. }
    assert (SHA4 : addressable m4 a 136).
    { eapply addressable_xpres_blkX; [apply SUB01; exact PIN| unfold AAPP_HI; lia| exact SHA2| exact XP4| exact (memflag_below_sh _ _ K7 ltac:(lia))]. }
    assert (ADDR1_4 : addressable m4 A1 16).
    { eapply addressable_xpres_blkX with (LB2 := LB1) (p := p1); [unfold LB1; left; reflexivity| unfold AAPP_HI; lia| exact ADDR1| exact XP4| exact (memflag_below_sh _ _ A1AP ltac:(lia))]. }
    pose proof (ah_disj H HH _ _ _ (p2, A2, L + 1) (p1, A1, 16) HEAP4 (or_introl eq_refl) (or_intror (or_introl eq_refl))
                  (afresh_id_ne H HH _ _ _ _ _ _ p1 HEAP4 (or_introl eq_refl))) as DJ12.
    cbn [blk_addr blk_size fst snd] in DJ12.
    pose proof (ah_disj H HH _ _ _ (p2, A2, L + 1) (pa, a, VPM_SIZE) HEAP4 (or_introl eq_refl) (or_intror (or_intror PIN))
                  (afresh_id_ne H HH _ _ _ _ _ _ pa HEAP4 (or_intror (in_map blk_id _ _ PIN)))) as DJa2.
    cbn [blk_addr blk_size fst snd] in DJa2.
    pose proof (ah_disj H HH _ _ _ (p1, A1, 16) (pa, a, VPM_SIZE) HEAP2 (or_introl eq_refl) (or_intror PIN)
                  (afresh_id_ne H HH _ _ _ _ _ _ pa HEAP2 (in_map blk_id _ _ PIN))) as DJa1.
    cbn [blk_addr blk_size fst snd] in DJa1. unfold VPM_SIZE in DJa1, DJa2. box DJ12. box DJa1. box DJa2.
    (* [comment removed for export] *)
    pose proof (ASLACK _ _ _ _ _ _ HEAP4 (or_introl eq_refl)) as SLK.
    destruct (awr_at_bytes _ _ _ SLK ltac:(apply Z.mod_pos_bound; lia) ltac:(unfold AIMG_TOP; lia)) as (slack & SLL & SLB). clear SLK.
    assert (STR4 : bytes_at asegs m4 A2 (ns ++ Z_to_bv 8 0 :: slack)).
    { replace (ns ++ Z_to_bv 8 0 :: slack) with ((ns ++ [b8 0]) ++ slack) by (unfold b8; rewrite <- app_assoc; reflexivity).
      apply (proj2 (bytes_at_app asegs m4 A2 (ns ++ [b8 0]) slack)). split.
      - pose proof (proj2 (proj1 CP4)) as CPB. cbn [cells_bytes cbytes app] in CPB. rewrite ?app_nil_r in CPB.
        first [exact CPB| rewrite <- app_assoc in CPB; exact CPB| match type of CPB with ?T => idtac "CPB?" T end].
      - rewrite length_app. cbn [length]. replace (A2 + Z.of_nat (length ns + 1)) with (A2 + (L + 1)) by (unfold L; lia). exact SLB. }
    assert (SLK8 : Z.of_nat (length slack) <= 7 /\ A2 + L + 1 + Z.of_nat (length slack) <= aceil).
    { rewrite SLL. clear - A2C ACEILB. Z.div_mod_to_equations. lia. }
    assert (ACCA1 : accessible m4 A1 16) by (eapply addressable_accessible; [exact ADDR1_4| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCA2 : accessible m4 A2 (L + 1)) by (eapply addressable_accessible; [exact ADDR2| lia| lia| unfold AAPP_HI; lia]).
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ HEAP4 (or_introl eq_refl)) as SHV2. replace (A2 + (L + 1)) with (A2 + L + 1) in SHV2 by lia.
    assert (IAM2 : in_app_mem A2 (A2 + L + 1)) by (eapply aapp_in_app_mem; [exact A2AP| lia| lia]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply aas_seg3 with (lo := lo) (ns := ns) (slack := slack);
      unfold XBUF_SIZE, zlength; fold L; rewrite ?unsigned_lit by lia;
      first [exact XB4| exact STR4| exact NONUL| exact ACCA1| exact ACCA2| exact SHV2| exact IAM2| exact A1AP| exact AC4| exact ST4| exact CEIL| exact MI4| exact A1M16
            | rewrite SLL; exact (Z.le_refl _) | lia | unfold AINTRIN_STACK; lia | match goal with |- ?G => idtac "LEFT3:" G end]|].
    intros msF5 mo5 KREL5 MP5 (w0 & w1 & w2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m5 & VIS5 & MU5 & WM5 & MI5 & AC5 & ST5 & XB5).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in MU5, ST5 by lia. unfold XBUF_SIZE in MU5. unfold zlength in XB5. fold L in XB5.
    assert (CW5 : Forall (aclient_write_ok H LB2) [(lo, bv_unsigned sp + -64); (A1, A1 + 16)]).
    { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (p1, A1, 16). split; [unfold LB2, LB1; right; left; reflexivity| cbn; lia]. }
    assert (HP5 : as_RHEAP H s4' LB2 m5) by (eapply (ah_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5| exact CW5]).
    assert (AUX5 : as_rauxv_ok H m5 B) by (eapply (ah_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5| exact CW5]).
    assert (ERR5 : rw_cells asegs m5 (ATP + -164) [C4 errv4]) by (eapply errno_across; [exact ERR4| exact MU5| exact WM5| unfold ATP; cbn; lia]).
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]).
    assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]).
    assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]).
    assert (FR5 : rw_cells asegs m5 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR4| exact MU5| exact WM5| unfold aas_frame; cbn; lia]).
    assert (BLK5 : rw_cells asegs m5 a (vpm_cells_h 0)) by (eapply rw_cells_transport; [exact BLK4| exact MU5| exact WM5| unfold vpm_cells_h; blia1 DJa1]).
    assert (CP5 : rw_cells asegs m5 A2 [CB (length ns) ns; C1 (b8 0)]) by (eapply rw_cells_transport; [exact CP4| exact MU5| exact WM5| unfold L in *; blia1 DJ12]).
    assert (XP5' : xpres H LB (bv_unsigned sp + -64) (memflag_foot ++ [(a, a + VPM_SIZE)]) m4 m5).
    { eapply (xpres_of_munch_fresh H HH) with (p := p1) (A := A1) (n := 16); [exact HEAP2| exact CSP| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    assert (XP5 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m4 m5)
      by (eapply (xpres_weaken H); [exact XP5'| lia| auto| auto]). clear XP5'.
    assert (AWS : forall A0 k, aapp A0 k -> 0 <= k -> A0 + k <= aceil -> disjoint_from [(lo, bv_unsigned sp + -64); (A1, A1 + 16)] (sh A0) (nsh k) ->
                  forall mx my, munch [(lo, bv_unsigned sp + -64); (A1, A1 + 16)] mx my -> wmono asegs mx my -> addressable mx A0 k -> addressable my A0 k).
    { intros A0 k _ _ _ DJ mx my MUx WMx AD. eapply addressable_transport; [exact AD| exact MUx| exact WMx| exact DJ]. }
    assert (DJSa : disjoint_from [(lo, bv_unsigned sp + -64); (A1, A1 + 16)] (sh a) (nsh 136)) by (apply app_sh_disjoint; [exact A1AP| lia| exact K7| lia| exact CEIL]).
    assert (DJS2 : disjoint_from [(lo, bv_unsigned sp + -64); (A1, A1 + 16)] (sh A2) (nsh (L + 1))) by (apply app_sh_disjoint; [exact A1AP| lia| exact A2AP| lia| exact CEIL]).
    assert (SHA5 : addressable m5 a 136) by (eapply addressable_transport; [exact SHA4| exact MU5| exact WM5| exact DJSa]).
    assert (ADDR2_5 : addressable m5 A2 (L + 1)) by (eapply addressable_transport; [exact ADDR2| exact MU5| exact WM5| exact DJS2]).
    assert (CH5 : as_chain H m5 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (chain_via_munch H HH); [| exact MU5|].
      - eapply chain_via_xpres; [exact CH2| exact XP4| exact CHS1| exact FXM].
      - intros fp' ra' IN. specialize (CHS1 _ _ IN). cbn. lia. }
    clear AWS.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (lo := lo) (B := B) (LB := LB2) (s := s4') (errv := errv4) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS5| ..]; rewrite ?unsigned_lit by (unfold AAS_R3; lia).
      all: first [exact HP5| exact KREL5| exact AUX5| exact ST5| exact CEIL| exact ERR5| exact MI5| reflexivity| exact SP16'| exact AC5| exact CH5| exact CHS1
                 | exact IM5| exact GM5| unfold CFREE_STACK, AFREE_STACK; lia | lia | match goal with |- ?G => idtac "LEFTN1:" G end]. }
    intros [msF6 mo6] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m6 & s6' &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & HEAP6 & IM6 & GM6 & AL6).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST6, XP6 by lia.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply aas_seg4|].
    intros msF7 mo7 KREL7 MP7 VIS7.
    assert (CH6 : as_chain H m6 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH5| apply (xpres_nil_apres H); exact XP6| exact CHS1]).
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (lo := lo) (B := B) (LB := LB2) (s := s6') (errv := errv4) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS7| ..]; rewrite ?unsigned_lit by (unfold AAS_R4; lia).
      all: first [exact HEAP6| exact KREL7| exact AUX6| exact ST6| exact CEIL| exact ERR6| exact MI6| reflexivity| exact SP16'| exact AC6| exact CH6| exact CHS1
                 | exact IM6| exact GM6| unfold CFREE_STACK, AFREE_STACK; lia | lia | match goal with |- ?G => idtac "LEFTN2:" G end]. }
    intros [msF8 mo8] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m8 & s8' &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & IM8 & GM8 & AL8).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST8, XP8 by lia.
    pose proof (xpres_trans H _ _ _ _ _ _ XP6 XP8) as XP68.
    assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP68| exact FR5| left; cbn; lia| constructor]).
    assert (BLK8 : rw_cells asegs m8 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' H); [exact XP68| exact BLK5| | constructor]. right; right; left. exists (pa, a, VPM_SIZE). split; [apply SUB12, SUB01; exact PIN| unfold vpm_cells_h; cbn; unfold VPM_SIZE; lia]. }
    assert (XB8 : rw_cells asegs m8 A1 [C8 (wz A2); C8 (wz L)]).
    { eapply (xpres_rw_cells' H); [exact XP68| exact XB5| | constructor]. right; right; left. exists (p1, A1, 16). split; [apply SUB12; unfold LB1; left; reflexivity| cbn; lia]. }
    assert (CP8 : rw_cells asegs m8 A2 [CB (length ns) ns; C1 (b8 0)]).
    { eapply (xpres_rw_cells' H); [exact XP68| exact CP5| | constructor]. right; right; left. exists (p2, A2, L + 1). split; [unfold LB2; left; reflexivity| cbn; unfold L; lia]. }
    assert (DJS1 : disjoint_from [(lo, bv_unsigned sp + -64); (A1, A1 + 16)] (sh A1) (nsh 16)) by (apply app_sh_disjoint; [exact A1AP| lia| exact A1AP| lia| exact CEIL]).
    assert (ADDR1_5 : addressable m5 A1 16) by (eapply addressable_transport; [exact ADDR1_4| exact MU5| exact WM5| exact DJS1]).
    assert (SHA8 : addressable m8 a 136).
    { eapply addressable_xpres_blkX with (LB2 := LB2) (p := pa); [apply SUB12, SUB01; exact PIN| unfold AAPP_HI; lia| exact SHA5| exact XP68| apply Forall_nil]. }
    assert (ADDR1_8 : addressable m8 A1 16).
    { eapply addressable_xpres_blkX with (LB2 := LB2) (p := p1); [apply SUB12; unfold LB1; left; reflexivity| unfold AAPP_HI; lia| exact ADDR1_5| exact XP68| apply Forall_nil]. }
    assert (ADDR2_8 : addressable m8 A2 (L + 1)).
    { eapply addressable_xpres_blkX with (LB2 := LB2) (p := p2); [unfold LB2; left; reflexivity| unfold AAPP_HI; lia| exact ADDR2_5| exact XP68| apply Forall_nil]. }
    assert (MF8 : MEMFLAG m8 1) by (eapply (MEMFLAG_apres H); [apply (xpres_nil_apres H); exact XP68| exact MF5]).
    assert (XP08 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m5 m8).
    { eapply (xpres_weaken H); [exact XP68| lia| intros b Hb; apply SUB12, SUB01; exact Hb| intros q Hq; destruct Hq]. }
    assert (CH8 : as_chain H m8 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH6| apply (xpres_nil_apres H); exact XP8| exact CHS1]).
    assert (ACCa8 : accessible m8 a 136) by (eapply addressable_accessible; [exact SHA8| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply aas_seg5; unfold VPM_SIZE; [lia| lia| exact K2| lia| exact BLK8| exact ACCa8| exact MI8]|].
    intros msF9 mo9 KREL9 MP9 VIS9.
    (* [comment removed for export] *)
    pose proof (asknew_spec H HH) as SN. unfold sknew_stmt, sknew_stmt_gen in SN.
    eapply (ah_seq H HH).
    { eapply SN with (lo := lo) (B := B) (LB := LB2) (s := s8') (c := P_buffer_cmp) (v := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS9| split; [reflexivity| unfold P_buffer_cmp; lia]| ..]; rewrite ?unsigned_lit by (unfold AAS_R6; lia).
      all: first [exact HEAP8| exact KREL9| exact AUX8| exact ST8| exact CEIL| exact ERR8| exact MI8| reflexivity| exact SP16'| exact AC8| exact CH8| exact CHS1
                 | split; [exact MF8| split; [exact IM8| exact GM8]]
                 | unfold LB2, LB1; rewrite !lb_bytes_cons; cbn [blk_size snd]; unfold SK_SIZE; lia
                 | unfold LB2, LB1; cbn [length]; lia
                 | unfold SKNEW_STACK, FR_sk_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                 | unfold SK_SIZE; lia | lia
                 | unfold AAS_R6; eapply pf_ok_call; [exact PF|]; unfold PF_addstr; intros y Hy; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hy
                 | match goal with |- ?G => idtac "LEFTK:" G end]. }
    clear SN. intros [msF10 mo10] PO. unfold sknew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0' & x1' & x2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3' & x4' & x5' & x6' & m9 & errv9 & st & id & did & s9' &
                    VIS10 & KREL10 & MP10 & MI9 & AC9 & ST9 & ERR9 & AUX9 & XP9 & STP & HEAP9 & SO9 & SKSH9 & (MF9 & IM9 & GM9) & AL9).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST9, XP9 by lia.
    set (LB3 := (id, st, SK_SIZE) :: LB2) in *.
    assert (SUB23 : forall b, In b LB2 -> In b LB3) by (intros b Hb; right; exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HEAP9 (or_introl eq_refl)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). cbn [blk_addr blk_size fst snd] in T1, T2, T3, T4, T5, T6, T7.
    unfold SK_SIZE in T3, T5, T7. unfold AIMG_TOP in T4. clear T6.
    pose proof (aapp_bounds st 56 T7 ltac:(lia)) as (TB1 & TB2 & TB3 & TB4 & TB5). unfold AAPP_HI in TB3.
    pose proof (ah_disj H HH _ _ _ (id, st, SK_SIZE) (pa, a, VPM_SIZE) HEAP9 (or_introl eq_refl) (or_intror (SUB12 _ (SUB01 _ PIN)))
                  (afresh_id_ne H HH _ _ _ _ _ _ pa HEAP9 (in_map blk_id _ _ (SUB12 _ (SUB01 _ PIN))))) as DJta.
    pose proof (ah_disj H HH _ _ _ (id, st, SK_SIZE) (p1, A1, 16) HEAP9 (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl)))
                  (afresh_id_ne H HH _ _ _ _ _ _ p1 HEAP9 (in_map blk_id LB2 (p1, A1, 16) (or_intror (or_introl eq_refl))))) as DJt1.
    pose proof (ah_disj H HH _ _ _ (id, st, SK_SIZE) (p2, A2, L + 1) HEAP9 (or_introl eq_refl) (or_intror (or_introl eq_refl))
                  (afresh_id_ne H HH _ _ _ _ _ _ p2 HEAP9 (in_map blk_id LB2 (p2, A2, L + 1) (or_introl eq_refl)))) as DJt2.
    cbn [blk_addr blk_size fst snd] in DJta, DJt1, DJt2. unfold SK_SIZE, VPM_SIZE in DJta, DJt1, DJt2. box DJta. box DJt1. box DJt2.
    assert (FR9 : rw_cells asegs m9 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP9| exact FR8| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. }
    assert (BLK9 : rw_cells asegs m9 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' H); [exact XP9| exact BLK8| | unfold memflag_foot, A_mem_inited; constructor; [unfold vpm_cells_h; cbn; lia| constructor]].
      right; right; left. exists (pa, a, VPM_SIZE). split; [apply SUB12, SUB01; exact PIN| unfold vpm_cells_h; cbn; unfold VPM_SIZE; lia]. }
    assert (XB9 : rw_cells asegs m9 A1 [C8 (wz A2); C8 (wz L)]).
    { eapply (xpres_rw_cells' H); [exact XP9| exact XB8| | unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      right; right; left. exists (p1, A1, 16). split; [apply SUB12; unfold LB1; left; reflexivity| cbn; lia]. }
    assert (CP9 : rw_cells asegs m9 A2 [CB (length ns) ns; C1 (b8 0)]).
    { eapply (xpres_rw_cells' H); [exact XP9| exact CP8| | unfold memflag_foot, A_mem_inited; constructor; [cbn; unfold L in *; lia| constructor]].
      right; right; left. exists (p2, A2, L + 1). split; [unfold LB2; left; reflexivity| cbn; unfold L; lia]. }
    pose proof (memflag_below_sh _ _ K7 ltac:(lia)) as FXM2.
    assert (SHA9 : addressable m9 a 136).
    { eapply addressable_xpres_blkX with (LB2 := LB2) (p := pa); [apply SUB12, SUB01; exact PIN| unfold AAPP_HI; lia| exact SHA8| exact XP9| exact FXM2]. }
    assert (ADDR1_9 : addressable m9 A1 16).
    { eapply addressable_xpres_blkX with (LB2 := LB2) (p := p1); [apply SUB12; unfold LB1; left; reflexivity| unfold AAPP_HI; lia| exact ADDR1_8| exact XP9| exact (memflag_below_sh _ _ A1AP ltac:(lia))]. }
    assert (ADDR2_9 : addressable m9 A2 (L + 1)).
    { eapply addressable_xpres_blkX with (LB2 := LB2) (p := p2); [unfold LB2; left; reflexivity| unfold AAPP_HI; lia| exact ADDR2_8| exact XP9| exact (memflag_below_sh _ _ A2AP ltac:(lia))]. }
    assert (SKR9 : SK_ranges H st (sk_fresh P_buffer_cmp id did)).
    { split; [exact (ah_blocks H HH _ _ _ _ HEAP9 (or_introl eq_refl))|]. intros NC. exfalso. apply NC. reflexivity. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL10| exact VIS10| eapply (aas_seg6 H) with (lo := lo) (LB := LB3); rewrite ?unsigned_lit by lia;
      [exact SO9| exact SKSH9| exact SKR9| unfold SK_SIZE; lia| exact T7| lia| exact AC9| exact ST9| exact CEIL| lia| exact MI9]|].
    intros msF11 mo11 KREL11 MP11 (y0' & y1' & y2' & h2 & h3 & h4 & h5 & h6 & h7 & y3' & y4' & y5' & y6' & m10 & VIS11 & MU10 & WM10 & MI10 & AC10 & ST10 & SO10 & SKSH10).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in MU10, ST10 by lia. unfold SK_SIZE in MU10.
    assert (CW10 : Forall (aclient_write_ok H LB3) [(lo, bv_unsigned sp + -64); (st, st + 56)]).
    { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (id, st, SK_SIZE). split; [unfold LB3; left; reflexivity| cbn; unfold SK_SIZE; lia]. }
    assert (HP10 : as_RHEAP H s9' LB3 m10) by (eapply (ah_RHEAP_frame H HH); [exact HEAP9| exact MU10| exact WM10| exact CW10]).
    assert (AUX10 : as_rauxv_ok H m10 B) by (eapply (ah_rauxv_frame H HH); [exact AUX9| exact MU10| exact WM10| exact CW10]).
    assert (ERR10 : rw_cells asegs m10 (ATP + -164) [C4 errv9]) by (eapply errno_across; [exact ERR9| exact MU10| exact WM10| unfold ATP; cbn; lia]).
    assert (MF10 : MEMFLAG m10 1) by (eapply MEMFLAG_across; [exact MU10| exact WM10| unfold A_mem_inited; cbn; lia| exact MF9]).
    assert (IM10 : IMPL_mem m10) by (eapply IMPL_across; [exact MU10| exact WM10| unfold A_malloc_impl; cbn; lia| exact IM9]).
    assert (GM10 : GOT_mem m10) by (eapply GOT_across; [exact MU10| exact WM10| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM9]).
    assert (FR10 : rw_cells asegs m10 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR9| exact MU10| exact WM10| unfold aas_frame; cbn; lia]).
    assert (BLK10 : rw_cells asegs m10 a (vpm_cells_h 0)) by (eapply rw_cells_transport; [exact BLK9| exact MU10| exact WM10| unfold vpm_cells_h; blia1 DJta]).
    assert (XB10 : rw_cells asegs m10 A1 [C8 (wz A2); C8 (wz L)]) by (eapply rw_cells_transport; [exact XB9| exact MU10| exact WM10| blia1 DJt1]).
    assert (CP10 : rw_cells asegs m10 A2 [CB (length ns) ns; C1 (b8 0)]) by (eapply rw_cells_transport; [exact CP9| exact MU10| exact WM10| unfold L in *; blia1 DJt2]).
    assert (SHA10 : addressable m10 a 136) by (eapply addressable_transport; [exact SHA9| exact MU10| exact WM10| apply app_sh_disjoint; [exact T7| lia| exact K7| lia| exact CEIL]]).
    assert (ADDR1_10 : addressable m10 A1 16) by (eapply addressable_transport; [exact ADDR1_9| exact MU10| exact WM10| apply app_sh_disjoint; [exact T7| lia| exact A1AP| lia| exact CEIL]]).
    assert (ADDR2_10 : addressable m10 A2 (L + 1)) by (eapply addressable_transport; [exact ADDR2_9| exact MU10| exact WM10| apply app_sh_disjoint; [exact T7| lia| exact A2AP| lia| exact CEIL]]).
    assert (XP10 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m9 m10).
    { assert (XP10' : xpres H LB2 (bv_unsigned sp + -64) (memflag_foot ++ [(a, a + VPM_SIZE)]) m9 m10).
      { eapply (xpres_of_munch_fresh H HH) with (p := id) (A := st) (n := SK_SIZE); [exact HEAP9| exact CSP| exact MU10| exact WM10|].
        apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold SK_SIZE; lia| apply Forall_nil]. }
      eapply (xpres_weaken H); [exact XP10'| lia| intros b Hb; apply SUB12, SUB01; exact Hb| auto]. }
    assert (CH9 : as_chain H m9 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply chain_via_xpres; [exact CH8| exact XP9| exact CHS1| exact FXM]).
    assert (CH10 : as_chain H m10 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (chain_via_munch H HH); [exact CH9| exact MU10|]. intros fp' ra' IN. specialize (CHS1 _ _ IN). cbn. lia. }
    (* [comment removed for export] *)
    pose proof (askpush_spec H HHx) as PS. unfold skpush_stmt in PS.
    eapply (ah_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := LB3) (s := s9') (a := st) (p := A1) (v := 1) (K := ahosts_fresh id did) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS11| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AAS_R10; lia).
      all: first [exact SO10| exact HP10| exact KREL11| exact AUX10| exact ST10| exact CEIL| exact ERR10| exact MI10| reflexivity| exact SP16'| exact AC10| exact CH10| exact CHS1| exact SKSH10
                 | split; [exact MF10| split; [exact IM10| exact GM10]]
                 | lazymatch goal with |- sk_push_nocmp _ => right; left; reflexivity end
                 | lazymatch goal with |- sk_cap _ <= SK_CAP_MAX => cbn; unfold SK_CAP_MAX; lia end
                 | lazymatch goal with |- lb_bytes _ + _ <= _ => unfold SKPUSH_COST, sk_grow, LB3, LB2, LB1; cbn [sk_cap ahosts_fresh]; rewrite !lb_bytes_cons; cbn [blk_size snd]; unfold SK_SIZE; lia end
                 | lazymatch goal with |- Z.of_nat (length _) + _ <= _ => unfold LB3, LB2, LB1; cbn [length]; lia end
                 | lazymatch goal with |- _ <= bv_unsigned _ + -64 - SKPUSH_STACK =>
                     unfold SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, AREALLOC_STACK,
                       FR_sk_insert, FR_sk_reserve, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia end
                 | lazymatch goal with |- _ + as_Cf _ _ <= as_AL _ _ => unfold SKPUSH_COST, sk_grow; cbn; replace (8 * (0 * 8 / 5) + 32) with 32 by reflexivity; replace (8 * 0) with 0 by reflexivity; clear - HAL AL2 AL4 AL6 AL8 AL9 CM16 CML CM56 CM32 CFZ; unfold SK_SIZE in *; lia end
                 | lia
                 | unfold AAS_R10; eapply pf_ok_call; [exact PF|]; unfold PF_addstr; intros y Hy; do 3 (apply in_app_iff; right); exact Hy
                 | match goal with |- ?G => idtac "LEFTP:" G end]. }
    clear PS. intros [msF12 mo12] PO. unfold skpush_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & m11 & errv11 & s11' & LB4 & K' & data' & cap' & did' &
                    VIS12 & KREL12 & MP12 & MI11 & AC11 & ST11 & ERR11 & AUX11 & KEQ & PLB & HEAP11 & SO11 & SKSH11 & XP11 & (v11 & (MF11 & IM11 & GM11) & VLE) & AL11).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST11, XP11 by lia.
    assert (V11 : v11 = 1) by (destruct MF11 as (fb11 & _ & _ & V01); lia). subst v11.
    destruct PLB as [(N1' & _)|[(_ & CAP4 & LB4E)|(C4 & _)]];
      [exfalso; unfold sk_num, sk_cap, ahosts_fresh, zlength in N1'; cbn in N1'; lia| | exfalso; unfold sk_cap, ahosts_fresh in C4; cbn in C4; lia].
    assert (ECAP : cap' = 4) by (rewrite KEQ in CAP4; unfold sk_cap, sk_after_push in CAP4; cbn in CAP4; exact CAP4). subst cap'.
    assert (EDAT : sk_data K' = data') by (rewrite KEQ; reflexivity).
    assert (EDID : sk_did K' = did') by (rewrite KEQ; reflexivity).
    rewrite EDAT, EDID in LB4E. subst LB4.
    assert (SFE : ASK_foot st K' = [(st, st + SK_SIZE); (data', data' + 32); (sh data', sh data' + nsh 32)]) by (rewrite KEQ; reflexivity). rewrite SFE in XP11. clear SFE.
    unfold SKPUSH_COST, sk_grow in AL11. cbn [sk_cap ahosts_fresh] in AL11. replace (8 * (0 * 8 / 5) + 32) with 32 in AL11 by reflexivity. replace (8 * 0) with 0 in AL11 by reflexivity. unfold SK_SIZE in AL9.
    pose proof (ah_blocks H HH _ _ _ _ HEAP11 (or_introl eq_refl)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). cbn [blk_addr blk_size fst snd] in D1, D2, D3, D4, D5, D6, D7.
    unfold AIMG_TOP in D4. clear D6.
    pose proof (aapp_bounds data' 32 D7 ltac:(lia)) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
    pose proof (sh_aapp_range data' 32 D7 ltac:(lia)) as (DS1 & DS2 & DS3). rewrite S0 in DS1. unfold AHI_LO in DS3.
    assert (SUB34 : forall b, In b LB3 -> In b ((did', data', 32) :: LB3)) by (intros b Hb; right; exact Hb).
    pose proof (ah_disj H HH _ _ _ (did', data', 32) (pa, a, VPM_SIZE) HEAP11 (or_introl eq_refl) (or_intror (SUB23 _ (SUB12 _ (SUB01 _ PIN))))
                  (afresh_id_ne H HH _ _ _ _ _ _ pa HEAP11 (in_map blk_id _ _ (SUB23 _ (SUB12 _ (SUB01 _ PIN)))))) as DJda.
    pose proof (ah_disj H HH _ _ _ (did', data', 32) (p1, A1, 16) HEAP11 (or_introl eq_refl) (or_intror (SUB23 _ (SUB12 _ (or_introl eq_refl))))
                  (afresh_id_ne H HH _ _ _ _ _ _ p1 HEAP11 (in_map blk_id LB3 (p1, A1, 16) (SUB23 _ (SUB12 _ (or_introl eq_refl)))))) as DJd1.
    pose proof (ah_disj H HH _ _ _ (did', data', 32) (p2, A2, L + 1) HEAP11 (or_introl eq_refl) (or_intror (SUB23 _ (or_introl eq_refl)))
                  (afresh_id_ne H HH _ _ _ _ _ _ p2 HEAP11 (in_map blk_id LB3 (p2, A2, L + 1) (SUB23 _ (or_introl eq_refl))))) as DJd2.
    pose proof (ah_disj H HH _ _ _ (did', data', 32) (id, st, SK_SIZE) HEAP11 (or_introl eq_refl) (or_intror (or_introl eq_refl))
                  (afresh_id_ne H HH _ _ _ _ _ _ id HEAP11 (in_map blk_id LB3 (id, st, SK_SIZE) (or_introl eq_refl)))) as DJdt.
    cbn [blk_addr blk_size fst snd] in DJda, DJd1, DJd2, DJdt. unfold SK_SIZE, VPM_SIZE in DJda, DJd1, DJd2, DJdt.
    assert (A8a : a mod 8 = 0) by (clear - K2; Z.div_mod_to_equations; lia).
    assert (A8d : data' mod 8 = 0) by (clear - D2; Z.div_mod_to_equations; lia).
    assert (A81 : A1 mod 8 = 0) by (clear - A1M16; Z.div_mod_to_equations; lia).
    assert (A82 : A2 mod 8 = 0) by (clear - A2M16; Z.div_mod_to_equations; lia).
    assert (A8t : st mod 8 = 0) by (clear - T2; Z.div_mod_to_equations; lia).
    pose proof (sh_disjoint_blocks data' 32 a 136 A8d A8a ltac:(lia) ltac:(lia) DJda) as SDa.
    pose proof (sh_disjoint_blocks data' 32 A1 16 A8d A81 ltac:(lia) ltac:(lia) DJd1) as SD1.
    pose proof (sh_disjoint_blocks data' 32 A2 (L + 1) A8d A82 ltac:(lia) ltac:(lia) DJd2) as SD2.
    pose proof (sh_disjoint_blocks data' 32 st 56 A8d A8t ltac:(lia) ltac:(lia) DJdt) as SDt.
    box DJda. box DJd1. box DJd2. box DJdt. box SDa. box SD1. box SD2. box SDt.
    (* [comment removed for export] *)
    assert (FXa : Forall (fun iv : Z * Z => sh a + nsh 136 <= fst iv \/ snd iv <= sh a) (memflag_foot ++ [(st, st + SK_SIZE); (data', data' + 32); (sh data', sh data' + nsh 32)])).
    { apply Forall_app. split; [exact (memflag_below_sh _ _ K7 ltac:(lia))|]. unfold SK_SIZE.
      apply Forall_cons; [cbn [fst snd]; apply sh_vs_app; [exact K7| lia| exact T7| lia]|].
      apply Forall_cons; [cbn [fst snd]; apply sh_vs_app; [exact K7| lia| exact D7| lia]|].
      apply Forall_cons; [cbn [fst snd]; clear - SDa; unfold boxed in SDa; lia| apply Forall_nil]. }
    assert (FX1 : Forall (fun iv : Z * Z => sh A1 + nsh 16 <= fst iv \/ snd iv <= sh A1) (memflag_foot ++ [(st, st + SK_SIZE); (data', data' + 32); (sh data', sh data' + nsh 32)])).
    { apply Forall_app. split; [exact (memflag_below_sh _ _ A1AP ltac:(lia))|]. unfold SK_SIZE.
      apply Forall_cons; [cbn [fst snd]; apply sh_vs_app; [exact A1AP| lia| exact T7| lia]|].
      apply Forall_cons; [cbn [fst snd]; apply sh_vs_app; [exact A1AP| lia| exact D7| lia]|].
      apply Forall_cons; [cbn [fst snd]; clear - SD1; unfold boxed in SD1; lia| apply Forall_nil]. }
    assert (FX2 : Forall (fun iv : Z * Z => sh A2 + nsh (L + 1) <= fst iv \/ snd iv <= sh A2) (memflag_foot ++ [(st, st + SK_SIZE); (data', data' + 32); (sh data', sh data' + nsh 32)])).
    { apply Forall_app. split; [exact (memflag_below_sh _ _ A2AP ltac:(lia))|]. unfold SK_SIZE.
      apply Forall_cons; [cbn [fst snd]; apply sh_vs_app; [exact A2AP| lia| exact T7| lia]|].
      apply Forall_cons; [cbn [fst snd]; apply sh_vs_app; [exact A2AP| lia| exact D7| lia]|].
      apply Forall_cons; [cbn [fst snd]; clear - SD2; unfold boxed in SD2; lia| apply Forall_nil]. }
    assert (SHA11 : addressable m11 a 136).
    { eapply addressable_xpres_blkX with (LB2 := (did', data', 32) :: LB3) (p := pa); [apply SUB34, SUB23, SUB12, SUB01; exact PIN| unfold AAPP_HI; lia| exact SHA10| exact XP11| exact FXa]. }
    assert (ADDR1_11 : addressable m11 A1 16).
    { eapply addressable_xpres_blkX with (LB2 := (did', data', 32) :: LB3) (p := p1); [apply SUB34, SUB23, SUB12; unfold LB1; left; reflexivity| unfold AAPP_HI; lia| exact ADDR1_10| exact XP11| exact FX1]. }
    assert (ADDR2_11 : addressable m11 A2 (L + 1)).
    { eapply addressable_xpres_blkX with (LB2 := (did', data', 32) :: LB3) (p := p2); [apply SUB34, SUB23; unfold LB2; left; reflexivity| unfold AAPP_HI; lia| exact ADDR2_10| exact XP11| exact FX2]. }
    assert (BLK11 : rw_cells asegs m11 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' H); [exact XP11| exact BLK10| |].
      - right; right; left. exists (pa, a, VPM_SIZE). split; [apply SUB34, SUB23, SUB12, SUB01; exact PIN| unfold vpm_cells_h; cbn; unfold VPM_SIZE; lia].
      - unfold vpm_cells_h, memflag_foot, A_mem_inited, SK_SIZE. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Nat.mul].
        apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 DJta|]. apply Forall_cons; [blia1 DJda|].
        apply Forall_cons; [cbn [fst snd]; apply app_vs_sh; [exact K7| lia| exact D7| lia]| apply Forall_nil]. }
    assert (XB11 : rw_cells asegs m11 A1 [C8 (wz A2); C8 (wz L)]).
    { eapply (xpres_rw_cells' H); [exact XP11| exact XB10| |].
      - right; right; left. exists (p1, A1, 16). split; [apply SUB34, SUB23, SUB12; unfold LB1; left; reflexivity| cbn; lia].
      - unfold memflag_foot, A_mem_inited, SK_SIZE. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Nat.mul].
        apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 DJt1|]. apply Forall_cons; [blia1 DJd1|].
        apply Forall_cons; [cbn [fst snd]; apply app_vs_sh; [exact A1AP| lia| exact D7| lia]| apply Forall_nil]. }
    assert (CP11 : rw_cells asegs m11 A2 [CB (length ns) ns; C1 (b8 0)]).
    { eapply (xpres_rw_cells' H); [exact XP11| exact CP10| |].
      - right; right; left. exists (p2, A2, L + 1). split; [apply SUB34, SUB23; unfold LB2; left; reflexivity| cbn; unfold L; lia].
      - unfold memflag_foot, A_mem_inited, SK_SIZE. cbn [cells_size csize Nat.add].
        apply Forall_cons; [cbn; unfold L in *; lia|]. apply Forall_cons; [unfold L in *; blia1 DJt2|]. apply Forall_cons; [unfold L in *; blia1 DJd2|].
        apply Forall_cons; [cbn [fst snd]; try replace (Z.of_nat (length ns + (1 + 0))) with (L + 1) by (unfold L; lia); try replace (Z.of_nat (length ns + 1)) with (L + 1) by (unfold L; lia);
                            apply app_vs_sh; [exact A2AP| lia| exact D7| lia]| apply Forall_nil]. }
    assert (FR11 : rw_cells asegs m11 (bv_unsigned sp + -64) (aas_frame j s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP11| exact FR10| left; cbn; lia|].
      unfold memflag_foot, A_mem_inited, SK_SIZE, aas_frame. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Nat.mul].
      apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DS2 DS3 CSP ACEILB SPR; lia| apply Forall_nil]. }
    assert (ACCa11 : accessible m11 a 136) by (eapply addressable_accessible; [exact SHA11| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL12| exact VIS12| eapply aas_seg7 with (lo := lo) (a := a) (st := st); unfold VPM_SIZE;
      [lia| lia| exact K7| exact ACCa11| lia| exact BLK11| exact FR11| exact AC11| exact ST11| exact CEIL| unfold FR_sk_pop_free; lia| exact MI11]|].
    intros msF13 mo13 KREL13 MP13 (q0 & q1 & q2 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & q3 & q4 & q5 & q6 & m12 & VIS13 & MU12 & WM12 & MI12 & AC12 & ST12 & BLK12).
    unfold VPM_SIZE in MU12.
    assert (CW12 : Forall (aclient_write_ok H ((did', data', 32) :: LB3)) [(lo, bv_unsigned sp); (a, a + 136)]).
    { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (pa, a, VPM_SIZE).
      split; [apply SUB34, SUB23, SUB12, SUB01; exact PIN| cbn; unfold VPM_SIZE; lia]. }
    assert (HP12 : as_RHEAP H s11' ((did', data', 32) :: LB3) m12) by (eapply (ah_RHEAP_frame H HH); [exact HEAP11| exact MU12| exact WM12| exact CW12]).
    assert (AUX12 : as_rauxv_ok H m12 B) by (eapply (ah_rauxv_frame H HH); [exact AUX11| exact MU12| exact WM12| exact CW12]).
    assert (ERR12 : rw_cells asegs m12 (ATP + -164) [C4 errv11]) by (eapply errno_across; [exact ERR11| exact MU12| exact WM12| unfold ATP; cbn; lia]).
    assert (MF12 : MEMFLAG m12 1) by (eapply MEMFLAG_across; [exact MU12| exact WM12| unfold A_mem_inited; cbn; lia| exact MF11]).
    assert (IM12 : IMPL_mem m12) by (eapply IMPL_across; [exact MU12| exact WM12| unfold A_malloc_impl; cbn; lia| exact IM11]).
    assert (GM12 : GOT_mem m12) by (eapply GOT_across; [exact MU12| exact WM12| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM11]).
    assert (XB12 : rw_cells asegs m12 A1 [C8 (wz A2); C8 (wz L)]) by (eapply rw_cells_transport; [exact XB11| exact MU12| exact WM12| blia1 DJa1]).
    assert (CP12 : rw_cells asegs m12 A2 [CB (length ns) ns; C1 (b8 0)]) by (eapply rw_cells_transport; [exact CP11| exact MU12| exact WM12| unfold L in *; blia1 DJa2]).
    assert (SHA12 : addressable m12 a 136) by (eapply addressable_transport; [exact SHA11| exact MU12| exact WM12| apply app_sh_disjoint; [exact K7| lia| exact K7| lia| exact CEIL]]).
    assert (ADDR1_12 : addressable m12 A1 16) by (eapply addressable_transport; [exact ADDR1_11| exact MU12| exact WM12| apply app_sh_disjoint; [exact K7| lia| exact A1AP| lia| exact CEIL]]).
    assert (ADDR2_12 : addressable m12 A2 (L + 1)) by (eapply addressable_transport; [exact ADDR2_11| exact MU12| exact WM12| apply app_sh_disjoint; [exact K7| lia| exact A2AP| lia| exact CEIL]]).
    assert (SKSH12 : SK_shad m12 st K').
    { destruct SKSH11 as [SKH SKD]. rewrite KEQ in SKD |- *. cbn [sk_cap sk_data sk_after_push] in SKD |- *. split.
      - eapply addressable_transport; [exact SKH| exact MU12| exact WM12| unfold SK_SIZE; apply app_sh_disjoint; [exact K7| lia| exact T7| lia| exact CEIL]].
      - intros NC. pose proof (SKD NC) as SKD'. cbn [sk_cap sk_data sk_after_push ahosts_fresh] in SKD' |- *. replace (8 * 4) with 32 in SKD' |- * by reflexivity.
        eapply addressable_transport; [exact SKD'| exact MU12| exact WM12| apply app_sh_disjoint; [exact K7| lia| exact D7| lia| exact CEIL]]. }
    assert (XP12r : xpres H (as_lb_remove H pa ((did', data', 32) :: LB3)) (bv_unsigned sp) [] m11 m12).
    { eapply (xpres_of_munch_listed H HH); [exact HEAP11| apply SUB34, SUB23, SUB12, SUB01; exact PIN| exact CSP0| exact MU12| exact WM12|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold VPM_SIZE; lia| apply Forall_nil]. }
    assert (NDL4 := ah_nodup H HH _ _ _ HEAP11).
    assert (KEEPsk : forall b, In b (blocks_SK st K') -> In b (as_lb_remove H pa ((did', data', 32) :: LB3))).
    { intros b Hb. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ NDL4 (SUB34 _ (SUB23 _ (SUB12 _ (SUB01 _ PIN)))))) b)).
      unfold blocks_SK in Hb. rewrite KEQ in Hb. cbn [sk_id sk_cap sk_did sk_data sk_after_push ahosts_fresh Z.eqb] in Hb.
      destruct Hb as [<-|[<-|[]]]; cbn [blk_id fst snd].
      - split; [right; left; reflexivity|]. intros E. apply (afresh_id_ne H HH _ _ _ _ _ _ pa HEAP9 (in_map blk_id _ _ (SUB12 _ (SUB01 _ PIN)))). exact E.
      - split; [left; reflexivity|]. intros E. apply (afresh_id_ne H HH _ _ _ _ _ _ pa HEAP11 (in_map blk_id _ _ (SUB23 _ (SUB12 _ (SUB01 _ PIN))))). exact E. }
    assert (SO12 : SKobj ((did', data', 32) :: LB3) m12 st K').
    { eapply SKobj_LB_mono; [| intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb].
      eapply (SKobj_frame H); [exact SO11| exact KEEPsk| exact XP12r]. }
    assert (XP12 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m11 m12).
    { eapply (xpres_of_munch H s LB); [exact HH| exact HP| exact MU12| exact WM12|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; intros q Hq; apply rin_ivs_app; right; left; cbn in Hq |- *; unfold VPM_SIZE; lia| apply Forall_nil]. }
    assert (XP0_11 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m10 m11).
    { eapply xpres_drop_windows with (LBx := (did', data', 32) :: LB3); [| intros b Hb; apply SUB34, SUB23, SUB12, SUB01; exact Hb|].
      - eapply (xpres_weaken H); [exact XP11| lia| auto|]. intros q Hq. apply rin_ivs_app. apply rin_ivs_app in Hq.
        destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq| right; exact Hq].
      - intros q Hq C. cbn in Hq. destruct Hq as [Hq|[Hq|[Hq|[]]]].
        + eapply (afresh_outside H HH); [exact HEAP9| exact CSP0| eapply (aclient_addr_weaken H); [exact C| lia| intros b Hb; apply SUB12, SUB01; exact Hb]| unfold SK_SIZE in *; lia].
        + eapply (afresh_outside H HH); [exact HEAP11| exact CSP0| eapply (aclient_addr_weaken H); [exact C| lia| intros b Hb; apply SUB23, SUB12, SUB01; exact Hb]| lia].
        + eapply afresh_sh_outside; [exact HEAP11| exact CSP0| eapply (aclient_addr_weaken H); [exact C| lia| intros b Hb; apply SUB23, SUB12, SUB01; exact Hb]| lia]. }
    (* [comment removed for export] *)
    apply (ah_done H HH). unfold aaddstr_post. cbn [cfg_ms cfg_model].
    exists q0, q1, q2, n1, n2, n3, n4, n5, n6, n7, q3, q4, q5, q6, m12, errv11, s11', st, K', (mkXB A2 L p1 p2),
           [(did', data', 32); (id, st, SK_SIZE); (p2, A2, L + 1); (p1, A1, 16)].
    split; [exact VIS13|]. split; [exact KREL13|].
    split. { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); [exact MP2|]. eapply (ah_mpres_trans H HH); [exact MP3|].
             eapply (ah_mpres_trans H HH); [exact MP4|]. eapply (ah_mpres_trans H HH); [exact MP5|]. eapply (ah_mpres_trans H HH); [exact MP6|].
             eapply (ah_mpres_trans H HH); [exact MP7|]. eapply (ah_mpres_trans H HH); [exact MP8|]. eapply (ah_mpres_trans H HH); [exact MP9|].
             eapply (ah_mpres_trans H HH); [exact MP10|]. eapply (ah_mpres_trans H HH); [exact MP11|]. eapply (ah_mpres_trans H HH); [exact MP12| exact MP13]. }
    split; [exact MI12|]. split; [exact AC12|]. split; [exact ST12|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR12|]. split; [exact AUX12|].
    split.
    { eapply (xpres_trans H); [exact XP1|]. eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP2| lia| auto| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP4| lia| exact SUB01| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply (xpres_trans H); [exact XP5|]. eapply (xpres_trans H); [exact XP08|].
      eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP9| lia| intros b Hb; apply SUB12, SUB01; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply (xpres_trans H); [exact XP10|]. eapply (xpres_trans H); [exact XP0_11| exact XP12]. }
    split; [cbn [app]; unfold LB3, LB2, LB1 in HP12; exact HP12|].
    split; [exact BLK12|].
    split.
    { cbn [app HOSTS]. unfold LB3, LB2, LB1 in SO12. split; [exact STP|]. split; [exact SO12|].
      rewrite KEQ. cbn [sk_elems sk_after_push ahosts_fresh app length]. split; [reflexivity|].
      constructor; [| constructor]. unfold XBUFobj. cbn [xb_data xb_len xb_id xb_did].
      split; [exact XB12|]. split; [right; right; right; left; reflexivity|]. split; [lia|]. split; [unfold L; lia|]. right; right; left; reflexivity. }
    split; [reflexivity|].
    split.
    { cbn [HOSTS_shad]. split.
      - split; [exact SKSH12|]. rewrite KEQ. cbn [sk_cap sk_data sk_after_push]. unfold SK_SIZE, AAPP_HI. split; [lia| intros _; lia].
      - rewrite KEQ. cbn [sk_elems sk_after_push ahosts_fresh app]. constructor; [| constructor]. unfold XBUF_shad. cbn [xb_data xb_len].
        unfold XBUF_SIZE, AAPP_HI. split; [lia|]. split; [exact ADDR1_12|]. split; [lia|]. split; [exact ADDR2_12|].
        pose proof (rw_cells_flatten _ _ _ _ CP12) as CPF. cbn [cells_size csize cells_bytes cbytes Nat.add] in CPF. rewrite ?app_nil_r in CPF.
        replace (Z.to_nat (L + 1)) with (length ns + (1 + 0))%nat by (unfold L; lia). eexists. exact CPF. }
    split.
    { unfold blocks_HOSTS, blocks_SK. rewrite KEQ. cbn -[Z.add Z.mul]. unfold SK_SIZE.
      replace (8 * 4) with 32 by reflexivity.
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_skip. apply perm_swap. }
    split; [reflexivity|]. split; [unfold AADDSTR_BYTES; rewrite !lb_bytes_cons; cbn [blk_size snd lb_bytes fold_right]; unfold XBUF_SIZE, SK_SIZE, zlength; fold L; lia|].
    split; [exact MF12|]. split; [exact IM12|]. split; [exact GM12|]. split; [unfold VPM_SIZE; exact SHA12|].
    unfold AADDSTR_COST, XBUF_SIZE, SK_SIZE, zlength. fold L. clear - HAL AL2 AL4 AL6 AL8 AL9 AL11 CM16 CML CM56 CM32 CFZ. lia.
  Qed.
End W.
