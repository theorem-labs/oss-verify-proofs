(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition al3_words : list (option (bv 32)) :=
  [Some W_4cc74; Some W_4cc78; Some W_4cc7c; Some W_4cc80; Some W_4cc84; Some W_4cc88; Some W_4cc8c; Some W_4cc90;
   Some W_4cc94; Some W_4cc98; Some W_4cc9c; Some W_4cca0; Some W_4cca4; None; None; Some W_4ccb0; Some W_4ccb4;
   Some W_4ccb8; Some W_4ccbc; Some W_4ccc0; Some W_4ccc4; Some W_4ccc8; Some W_4cccc; Some W_4ccd0; Some W_4ccd4;
   Some W_4ccd8; Some W_4ccdc; Some W_4cce0; Some W_4cce4; Some W_4cce8; Some W_4ccec; Some W_4ccf0; Some W_4ccf4;
   Some W_4ccf8; Some W_4ccfc; Some W_4cd00; Some W_4cd04]%list.
Definition am2_words : list (option (bv 32)) :=
  [Some W_4c564; Some W_4c568; Some W_4c56c; Some W_4c570; Some W_4c574]%list.

(* [comment removed for export] *)
Definition hb2w (h : word) : word := v_or (v_andi h 243) (Z_to_bv 64 0).

Section AME.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL3 : code_ato segs rb 0x4cc74 al3_words.
  Hypothesis HAM2 : code_ato segs rb 0x4c564 am2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variables (g_lsan gMAG : Z).
  Hypothesis HLSN : code_ato segs rb 0x9c9f0 lsn_words.
  Hypothesis GLSN : gload segs rb 0x9c9f0 10 g_lsan.
  Hypothesis GMAG : gload segs rb 0x4cca8 10 gMAG.
  Hypothesis Gg : (AIMGLO <= g_lsan /\ g_lsan + 8 <= AIMGHI)%Z /\ (AIMGLO <= gMAG /\ gMAG + 8 <= AIMGHI)%Z.   (* [comment removed for export] *)

  Lemma L67bb0 : fetch_word segs (at_ rb 0x4cc74) = Some W_4cc74.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 0 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bb4 : fetch_word segs (at_ rb 0x4cc78) = Some W_4cc78.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 1 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bb8 : fetch_word segs (at_ rb 0x4cc7c) = Some W_4cc7c.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 2 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bbc : fetch_word segs (at_ rb 0x4cc80) = Some W_4cc80.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 3 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67000 : fetch_word segs (at_ rb 0x4cc84) = Some W_4cc84.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 4 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bc4 : fetch_word segs (at_ rb 0x4cc88) = Some W_4cc88.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 5 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bc8 : fetch_word segs (at_ rb 0x4cc8c) = Some W_4cc8c.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 6 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bcc : fetch_word segs (at_ rb 0x4cc90) = Some W_4cc90.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 7 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bd0 : fetch_word segs (at_ rb 0x4cc94) = Some W_4cc94.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 8 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bd4 : fetch_word segs (at_ rb 0x4cc98) = Some W_4cc98.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 9 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bd8 : fetch_word segs (at_ rb 0x4cc9c) = Some W_4cc9c.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 10 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bdc : fetch_word segs (at_ rb 0x4cca0) = Some W_4cca0.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 11 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67be0 : fetch_word segs (at_ rb 0x4cca4) = Some W_4cca4.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 12 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bec : fetch_word segs (at_ rb 0x4ccb0) = Some W_4ccb0.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 15 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bf0 : fetch_word segs (at_ rb 0x4ccb4) = Some W_4ccb4.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 16 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bf4 : fetch_word segs (at_ rb 0x4ccb8) = Some W_4ccb8.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 17 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bf8 : fetch_word segs (at_ rb 0x4ccbc) = Some W_4ccbc.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 18 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67bfc : fetch_word segs (at_ rb 0x4ccc0) = Some W_4ccc0.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 19 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c00 : fetch_word segs (at_ rb 0x4ccc4) = Some W_4ccc4.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 20 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c04 : fetch_word segs (at_ rb 0x4ccc8) = Some W_4ccc8.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 21 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c08 : fetch_word segs (at_ rb 0x4cccc) = Some W_4cccc.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 22 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c0c : fetch_word segs (at_ rb 0x4ccd0) = Some W_4ccd0.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 23 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c10 : fetch_word segs (at_ rb 0x4ccd4) = Some W_4ccd4.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 24 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c14 : fetch_word segs (at_ rb 0x4ccd8) = Some W_4ccd8.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 25 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c18 : fetch_word segs (at_ rb 0x4ccdc) = Some W_4ccdc.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 26 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c1c : fetch_word segs (at_ rb 0x4cce0) = Some W_4cce0.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 27 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c20 : fetch_word segs (at_ rb 0x4cce4) = Some W_4cce4.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 28 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c24 : fetch_word segs (at_ rb 0x4cce8) = Some W_4cce8.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 29 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c28 : fetch_word segs (at_ rb 0x4ccec) = Some W_4ccec.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 30 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c2c : fetch_word segs (at_ rb 0x4ccf0) = Some W_4ccf0.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 31 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c30 : fetch_word segs (at_ rb 0x4ccf4) = Some W_4ccf4.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 32 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c34 : fetch_word segs (at_ rb 0x4ccf8) = Some W_4ccf8.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 33 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c38 : fetch_word segs (at_ rb 0x4ccfc) = Some W_4ccfc.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 34 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c3c : fetch_word segs (at_ rb 0x4cd00) = Some W_4cd00.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 35 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67c40 : fetch_word segs (at_ rb 0x4cd04) = Some W_4cd04.  Proof using HAL3. exact (code_ato_get segs rb 0x4cc74 al3_words 36 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)

  Lemma N674a0 : fetch_word segs (at_ rb 0x4c564) = Some W_4c564.  Proof using HAM2. exact (code_ato_get segs rb 0x4c564 am2_words 0 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N674a4 : fetch_word segs (at_ rb 0x4c568) = Some W_4c568.  Proof using HAM2. exact (code_ato_get segs rb 0x4c564 am2_words 1 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N674a8 : fetch_word segs (at_ rb 0x4c56c) = Some W_4c56c.  Proof using HAM2. exact (code_ato_get segs rb 0x4c564 am2_words 2 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N674ac : fetch_word segs (at_ rb 0x4c570) = Some W_4c570.  Proof using HAM2. exact (code_ato_get segs rb 0x4c564 am2_words 3 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N674b0 : fetch_word segs (at_ rb 0x4c574) = Some W_4c574.  Proof using HAM2. exact (code_ato_get segs rb 0x4c564 am2_words 4 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)


  Variables (rom : word -> option byte) (sp m tp : word) (n off : Z) (h1 : byte).
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis Gm : (U m mod 16 = 0)%Z /\ (0x10007fff8000 <= U m)%Z /\ (U m + 2 ^ 17 <= 2 ^ 47)%Z.   (* [comment removed for export] *)
  Hypothesis Gsp : (2 ^ 32 <= U sp)%Z /\ (U sp + 144 <= 2 ^ 47)%Z.
  Hypothesis Goff : (0 <= off)%Z /\ (U tp + off + 4 <= 2 ^ 64)%Z.

  Lemma RETe : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using Gm m RB. intros d Hd Hdr. pose proof RB as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.
  Lemma rz_facts : (16 <= rz n <= 1024)%Z /\ (rz n mod 16 = 0)%Z /\ (rz n = 16 <-> rz_log n = 0)%Z.
  Proof using Hn m rb.
    pose proof (rz_log_range n). (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end).
    destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E;
      (split; [lia | split; [reflexivity | lia]]).
  Qed.

  (* [comment removed for export] *)
  Definition amE3_mem (M : word -> option byte) : word -> option byte :=
    let M2 := wbytes (wbytes M (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1))))]) (at_ m (rz n - 16)) [Z_to_bv 8 2] in
    if (rz_log n =? 0)%Z then M2 else wbytes (wbytes M2 (at_ m 8) (LE8 (at_ m (rz n - 16)))) m (LE8 (Z_to_bv 64 MAGIC)).

  (* [comment removed for export] *)
  Theorem amE3 : forall (M : word -> option byte) r0,
    getr r0 2 = sp -> getr r0 4 = tp -> getr r0 9 = Z_to_bv 64 n -> getr r0 18 = m -> getr r0 20 = at_ m (rz n) -> getr r0 21 = at_ m (rz n - 16) ->
    rdn segs M (Z_to_bv 64 g_lsan) 8 = Some (LE8 (Z_to_bv 64 off)) -> rdn segs M (at_ tp off) 4 = Some (LE4 0) ->
    rdn segs M (at_ m (rz n - 15)) 1 = Some [h1] ->
    store_ok segs M (at_ m (rz n - 16)) 16 = true -> store_ok segs M m 16 = true ->
    (rz_log n <> 0%Z -> rdn segs M (Z_to_bv 64 gMAG) 8 = Some (LE8 (Z_to_bv 64 MAGIC))) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4cc74) M rom) (mkst r (at_ rb 0x7d600) (amE3_mem M) rom)
      /\ getr r 1 = at_ rb 0x4ccc8 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x [1; 10; 11; 13]) r0 r.
  Proof using Goff Gsp Gm Hn Gg GMAG GLSN HLSN RB HAL3.
    intros M r0 R2 R4 R9 R18 R20 R21 Rgl Rtls Rh1 SOKh SOKm Rmag.
    pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htp. destruct Gm as (Gm1 & Gm2 & Gm3). destruct Goff as [Go1 Go2].
    destruct rz_facts as (Hrz2 & Hrz16 & Hrz0). pose proof (u8_range h1) as Hh1.
    (* [comment removed for export] *)
    destruct (lsan_run segs rb g_lsan HLSN GLSN M rom (regupd r0 1 (at_ rb 0x4cc78)) (at_ rb 0x4cc78) tp off Rgl Go1 Go2 Rtls
                (RETe 0x4cc78 eq_refl ltac:(lia))) as (r1 & RUN1 & A10 & AG1).
    { apply getr_same. intros E; discriminate E. }
    { rewrite getr_other by (intros E; discriminate E). exact R4. }
    Ltac r1f AG1 r H := rewrite (AG1 r) by notin_list; gres; exact H.
    assert (B9 : getr r1 9 = Z_to_bv 64 n) by r1f AG1 (9:reg) R9.
    assert (B18 : getr r1 18 = m) by r1f AG1 (18:reg) R18.
    assert (B20 : getr r1 20 = at_ m (rz n)) by r1f AG1 (20:reg) R20.
    assert (B21 : getr r1 21 = at_ m (rz n - 16)) by r1f AG1 (21:reg) R21.
    set (M1 := wbytes M (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1))))]).
    set (M2 := wbytes M1 (at_ m (rz n - 16)) [Z_to_bv 8 2]).
    assert (SOK1 : store_ok segs M1 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOKh]).
    assert (SOKm2 : store_ok segs M2 m 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M2, M1 in G in change_no_check G' end); do 2 (eapply store_ok_mono; [apply wbytes_grows|]); exact SOKm).
    Ltac sok16 SOK := eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    (* [comment removed for export] *)
    assert (W2 : exists r2, msteps segs (mkst r0 (at_ rb 0x4cc74) M rom) (mkst r2 (at_ rb 0x4cc9c) M2 rom)
               /\ getr r2 11 = Z_to_bv 64 2 /\ (forall i : reg, In i [2; 4; 9; 18; 20; 21] -> getr r2 i = getr r1 i)
               /\ regs_agree (fun x => In x [1; 10; 11]) r0 r2).
    { wd_eexists. split.
      - an L67bb0 D_4cc74.                                 (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        chain_step; [reflexivity
          | eapply step_lbu with (b := h1); [exact L67bb4 | reflexivity | exact D_4cc78
            | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rh1; f_equal; f_equal; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        an L67bb8 D_4cc7c. an L67bbc D_4cc80.             (* [comment removed for export] *)
        an L67000 D_4cc84. an L67bc4 D_4cc88.             (* [comment removed for export] *)
        change (v_or (v_andi (Z_to_bv 64 (U h1)) 243) (Z_to_bv 64 0)) with (hb2w (Z_to_bv 64 (U h1))).
        an L67bc8 D_4cc8c.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1)))));
            [exact L67bcc | reflexivity | exact D_4cc90 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes M _ _) with M1.
        afence L67bd0 D_4cc94.                             (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := at_ m (rz n - 16)) (b := Z_to_bv 8 2);
            [exact L67bd4 | reflexivity | exact D_4cc98 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | reflexivity | sok16 SOK1]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes M1 _ _) with M2.
        wd_refl.
      - post; [|ra_chain]. intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi. }
    destruct W2 as (r2 & RUN2 & C11 & CK & AG2).
    assert (C18 : getr r2 18 = m) by (rewrite (CK 18) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B18).
    assert (C21 : getr r2 21 = at_ m (rz n - 16)) by (rewrite (CK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B21).
    assert (C20 : getr r2 20 = at_ m (rz n)) by (rewrite (CK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B20).
    assert (C9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (CK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B9).
    (* [comment removed for export] *)
    destruct (Z.eqb_spec (rz_log n) 0) as [E0|E0].
    - assert (E16 : rz n = 16%Z) by (apply Hrz0; exact E0).
      wd_eexists. split.
      + eapply msteps_trans; [exact RUN2|].
        ab_tk L67bd8 D_4cc9c ltac:(rewrite E16; condz).  (* [comment removed for export] *)
        an L67bf8 D_4ccbc. an L67bfc D_4ccc0.             (* [comment removed for export] *)
        an L67c00 D_4ccc4.                                 (* [comment removed for export] *)
        replace (amE3_mem M) with M2 by ((lazymatch goal with |- ?G => let G' := eval unfold amE3_mem in G in change_no_check G' end); rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
        wd_refl.
      + post. all: try (rewrite ?at_add_0_r; reflexivity). all: ra_chain.
    - assert (E16 : (32 <= rz n)%Z).
      { unfold rz in *. pose proof (rz_log_range n). assert (1 <= rz_log n)%Z by lia.
        replace 32%Z with (16 * 2 ^ 1)%Z by reflexivity. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
      specialize (Rmag E0).
      assert (Rmag2 : rdn segs M2 (Z_to_bv 64 gMAG) 8 = Some (LE8 (Z_to_bv 64 MAGIC))).
      { rewrite <- Rmag. (lazymatch goal with |- ?G => let G' := eval unfold M2, M1 in G in change_no_check G' end). apply rdn_ext; [wd_ulia_c | intros x Hx].
        rewrite !wbytes_outside; [reflexivity | ..]; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite ?at_u by lia; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      wd_eexists. split.
      + eapply msteps_trans; [exact RUN2|].
        ab_ft L67bd8 D_4cc9c ltac:(condz).                (* [comment removed for export] *)
        an L67bdc D_4cca0.                                 (* [comment removed for export] *)
        ab_ft L67be0 D_4cca4 ltac:(condz).                (* [comment removed for export] *)
        eapply msteps_trans; [apply (GMAG _ M2 rom (Z_to_bv 64 MAGIC) Rmag2)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ m 8);
            [exact L67bec | reflexivity | exact D_4ccb0 | gres; rwH; imm_norm; rewrite ?at_addi; fold_at_vars; reflexivity | gres; rwH; reflexivity
            | do 2 (eapply store_ok_mono; [apply wbytes_grows|]); eapply (store_ok_sub segs _ m _ 16); [lia | exact SOKm | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        afence L67bf0 D_4ccb4.                             (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := m);
            [exact L67bf4 | reflexivity | exact D_4ccb8 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity
            | do 3 (eapply store_ok_mono; [apply wbytes_grows|]); eapply (store_ok_sub segs _ m _ 16); [lia | exact SOKm | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        an L67bf8 D_4ccbc. an L67bfc D_4ccc0.             (* [comment removed for export] *)
        an L67c00 D_4ccc4.                                 (* [comment removed for export] *)
        replace (amE3_mem M) with (wbytes (wbytes M2 (at_ m 8) (LE8 (at_ m (rz n - 16)))) m (LE8 (Z_to_bv 64 MAGIC)))
          by ((lazymatch goal with |- ?G => let G' := eval unfold amE3_mem in G in change_no_check G' end); rewrite (proj2 (Z.eqb_neq _ _) E0); reflexivity).
        wd_refl.
      + post. all: try (rewrite ?at_add_0_r; reflexivity). all: ra_chain.
  Qed.
  (* [comment removed for export] *)
  Definition amE4_slots (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' : word) : list (Z * word) :=
    [(120, at_ rb 0x4c564); (112, s0); (104, s1); (96, s2); (88, s3); (80, s4); (72, s5); (64, s6); (56, s7); (48, s8); (40, s9);
     (32, s10); (24, s11); (136, at_ rb 0x6f070); (128, s0')]%Z.
  Theorem amE4 : forall (M : word -> option byte) r0 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' : word),
    getr r0 2 = sp -> getr r0 20 = at_ m (rz n) ->
    (forall (k : Z) (v : word), In (k, v) (amE4_slots s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0') -> rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4ccc8) M rom) (mkst r (at_ rb 0x6f070) M rom)
      /\ getr r 10 = at_ m (rz n) /\ getr r 2 = at_ sp 144 /\ getr r 1 = at_ rb 0x6f070
      /\ getr r 8 = s0' /\ getr r 9 = s1 /\ getr r 18 = s2 /\ getr r 19 = s3 /\ getr r 20 = s4 /\ getr r 21 = s5
      /\ getr r 22 = s6 /\ getr r 23 = s7 /\ getr r 24 = s8 /\ getr r 25 = s9 /\ getr r 26 = s10 /\ getr r 27 = s11
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) r0 r.
  Proof using Goff Gsp Gm Hn off tp Gg gMAG g_lsan RB HAM2 HAL3.
    intros M r0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' R2 R20 SL.
    pose proof (u64_range sp) as Hspr. destruct Gsp as [Gs1 Gs2]. pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). destruct rz_facts as (Hrz2 & Hrz16 & Hrz0).
    unfold amE4_slots in SL.
    Ltac fld F D vv SL :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; fold_at_vars; rewrite ?at_addi; zlit_at; apply SL; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    pose proof (RETe 0x4c564 eq_refl ltac:(lia)) as RT1. pose proof (RETe 0x6f070 eq_refl ltac:(lia)) as RT2.
    wd_eexists. split.
    - an L67c04 D_4ccc8.                                   (* [comment removed for export] *)
      fld L67c08 D_4cccc (at_ rb 0x4c564) SL.              (* [comment removed for export] *)
      fld L67c0c D_4ccd0 s0 SL. fld L67c10 D_4ccd4 s1 SL. fld L67c14 D_4ccd8 s2 SL. fld L67c18 D_4ccdc s3 SL.
      fld L67c1c D_4cce0 s4 SL. fld L67c20 D_4cce4 s5 SL. fld L67c24 D_4cce8 s6 SL. fld L67c28 D_4ccec s7 SL.
      fld L67c2c D_4ccf0 s8 SL. fld L67c30 D_4ccf4 s9 SL. fld L67c34 D_4ccf8 s10 SL. fld L67c38 D_4ccfc s11 SL.
      an L67c3c D_4cd00.                                   (* [comment removed for export] *)
      aret L67c40 D_4cd04 (at_ rb 0x4c564).                (* [comment removed for export] *)
      ab_ft N674a0 D_4c564 ltac:(condz).                  (* [comment removed for export] *)
      fld N674a4 D_4c568 (at_ rb 0x6f070) SL.              (* [comment removed for export] *)
      fld N674a8 D_4c56c s0' SL.                           (* [comment removed for export] *)
      an N674ac D_4c570.                                   (* [comment removed for export] *)
      aret N674b0 D_4c574 (at_ rb 0x6f070).                (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AME.
End FPGen1.
