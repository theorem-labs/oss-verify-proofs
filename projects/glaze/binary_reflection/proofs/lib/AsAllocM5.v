(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0.
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
  [Some W_4c1fc; Some W_4c200; Some W_4c204; Some W_4c208; Some W_4c20c; Some W_4c210; Some W_4c214; Some W_4c218;
   Some W_4c21c; Some W_4c220; Some W_4c224; Some W_4c228; Some W_4c22c; None; None; Some W_4c238; Some W_4c23c;
   Some W_4c240; Some W_4c244; Some W_4c248; Some W_4c24c; Some W_4c250; Some W_4c254; Some W_4c258; Some W_4c25c;
   Some W_4c260; Some W_4c264; Some W_4c268; Some W_4c26c; Some W_4c270; Some W_4c274; Some W_4c278; Some W_4c27c;
   Some W_4c280; Some W_4c284; Some W_4c288; Some W_4c28c]%list.
Definition am2_words : list (option (bv 32)) :=
  [Some W_4baec; Some W_4baf0; Some W_4baf4; Some W_4baf8; Some W_4bafc]%list.

(* [comment removed for export] *)
Definition hb2w (h : word) : word := v_or (v_andi h 243) (Z_to_bv 64 0).

Section AME.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL3 : code_ato segs rb 0x4c204 al3_words.
  Hypothesis HAM2 : code_ato segs rb 0x4baf4 am2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variables (g_lsan gMAG : Z).
  Hypothesis HLSN : code_ato segs rb 0x9bf80 lsn_words.
  Hypothesis GLSN : gload segs rb 0x9bf80 10 g_lsan.
  Hypothesis GMAG : gload segs rb 0x4c238 10 gMAG.
  Hypothesis Gg : (AIMGLO <= g_lsan /\ g_lsan + 8 <= AIMGHI)%Z /\ (AIMGLO <= gMAG /\ gMAG + 8 <= AIMGHI)%Z.   (* [comment removed for export] *)

  Lemma L67138 : fetch_word segs (at_ rb 0x4c204) = Some W_4c1fc.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 0 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L6713c : fetch_word segs (at_ rb 0x4c208) = Some W_4c200.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 1 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67140 : fetch_word segs (at_ rb 0x4c20c) = Some W_4c204.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 2 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67144 : fetch_word segs (at_ rb 0x4c210) = Some W_4c208.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 3 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67000 : fetch_word segs (at_ rb 0x4c214) = Some W_4c20c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 4 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L6714c : fetch_word segs (at_ rb 0x4c218) = Some W_4c210.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 5 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67150 : fetch_word segs (at_ rb 0x4c21c) = Some W_4c214.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 6 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67154 : fetch_word segs (at_ rb 0x4c220) = Some W_4c218.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 7 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67158 : fetch_word segs (at_ rb 0x4c224) = Some W_4c21c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 8 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L6715c : fetch_word segs (at_ rb 0x4c228) = Some W_4c220.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 9 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67160 : fetch_word segs (at_ rb 0x4c22c) = Some W_4c224.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 10 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67164 : fetch_word segs (at_ rb 0x4c230) = Some W_4c228.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 11 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67168 : fetch_word segs (at_ rb 0x4c234) = Some W_4c22c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 12 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67174 : fetch_word segs (at_ rb 0x4c240) = Some W_4c238.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 15 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67178 : fetch_word segs (at_ rb 0x4c244) = Some W_4c23c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 16 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L6717c : fetch_word segs (at_ rb 0x4c248) = Some W_4c240.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 17 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67180 : fetch_word segs (at_ rb 0x4c24c) = Some W_4c244.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 18 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67184 : fetch_word segs (at_ rb 0x4c250) = Some W_4c248.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 19 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67188 : fetch_word segs (at_ rb 0x4c254) = Some W_4c24c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 20 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L6718c : fetch_word segs (at_ rb 0x4c258) = Some W_4c250.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 21 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67190 : fetch_word segs (at_ rb 0x4c25c) = Some W_4c254.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 22 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67194 : fetch_word segs (at_ rb 0x4c260) = Some W_4c258.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 23 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L67198 : fetch_word segs (at_ rb 0x4c264) = Some W_4c25c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 24 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L6719c : fetch_word segs (at_ rb 0x4c268) = Some W_4c260.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 25 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671a0 : fetch_word segs (at_ rb 0x4c26c) = Some W_4c264.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 26 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671a4 : fetch_word segs (at_ rb 0x4c270) = Some W_4c268.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 27 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671a8 : fetch_word segs (at_ rb 0x4c274) = Some W_4c26c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 28 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671ac : fetch_word segs (at_ rb 0x4c278) = Some W_4c270.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 29 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671b0 : fetch_word segs (at_ rb 0x4c27c) = Some W_4c274.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 30 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671b4 : fetch_word segs (at_ rb 0x4c280) = Some W_4c278.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 31 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671b8 : fetch_word segs (at_ rb 0x4c284) = Some W_4c27c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 32 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671bc : fetch_word segs (at_ rb 0x4c288) = Some W_4c280.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 33 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671c0 : fetch_word segs (at_ rb 0x4c28c) = Some W_4c284.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 34 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671c4 : fetch_word segs (at_ rb 0x4c290) = Some W_4c288.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 35 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma L671c8 : fetch_word segs (at_ rb 0x4c294) = Some W_4c28c.  Proof using HAL3. exact (code_ato_get segs rb 0x4c204 al3_words 36 _ HAL3 eq_refl). Qed.   (* [comment removed for export] *)

  Lemma N66a28 : fetch_word segs (at_ rb 0x4baf4) = Some W_4baec.  Proof using HAM2. exact (code_ato_get segs rb 0x4baf4 am2_words 0 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N66a2c : fetch_word segs (at_ rb 0x4baf8) = Some W_4baf0.  Proof using HAM2. exact (code_ato_get segs rb 0x4baf4 am2_words 1 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N66a30 : fetch_word segs (at_ rb 0x4bafc) = Some W_4baf4.  Proof using HAM2. exact (code_ato_get segs rb 0x4baf4 am2_words 2 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N66a34 : fetch_word segs (at_ rb 0x4bb00) = Some W_4baf8.  Proof using HAM2. exact (code_ato_get segs rb 0x4baf4 am2_words 3 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma N66a38 : fetch_word segs (at_ rb 0x4bb04) = Some W_4bafc.  Proof using HAM2. exact (code_ato_get segs rb 0x4baf4 am2_words 4 _ HAM2 eq_refl). Qed.   (* [comment removed for export] *)


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
    exists r, msteps segs (mkst r0 (at_ rb 0x4c204) M rom) (mkst r (at_ rb 0x7cb90) (amE3_mem M) rom)
      /\ getr r 1 = at_ rb 0x4c258 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x [1; 10; 11; 13]) r0 r.
  Proof using Goff Gsp Gm Hn Gg GMAG GLSN HLSN RB HAL3.
    intros M r0 R2 R4 R9 R18 R20 R21 Rgl Rtls Rh1 SOKh SOKm Rmag.
    pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htp. destruct Gm as (Gm1 & Gm2 & Gm3). destruct Goff as [Go1 Go2].
    destruct rz_facts as (Hrz2 & Hrz16 & Hrz0). pose proof (u8_range h1) as Hh1.
    (* [comment removed for export] *)
    destruct (lsan_run segs rb g_lsan HLSN GLSN M rom (regupd r0 1 (at_ rb 0x4c208)) (at_ rb 0x4c208) tp off Rgl Go1 Go2 Rtls
                (RETe 0x4c208 eq_refl ltac:(lia))) as (r1 & RUN1 & A10 & AG1).
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
    assert (W2 : exists r2, msteps segs (mkst r0 (at_ rb 0x4c204) M rom) (mkst r2 (at_ rb 0x4c22c) M2 rom)
               /\ getr r2 11 = Z_to_bv 64 2 /\ (forall i : reg, In i [2; 4; 9; 18; 20; 21] -> getr r2 i = getr r1 i)
               /\ regs_agree (fun x => In x [1; 10; 11]) r0 r2).
    { wd_eexists. split.
      - an L67138 D_4c1fc.                                 (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        chain_step; [reflexivity
          | eapply step_lbu with (b := h1); [exact L6713c | reflexivity | exact D_4c200
            | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rh1; f_equal; f_equal; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        an L67140 D_4c204. an L67144 D_4c208.             (* [comment removed for export] *)
        an L67000 D_4c20c. an L6714c D_4c210.             (* [comment removed for export] *)
        change (v_or (v_andi (Z_to_bv 64 (U h1)) 243) (Z_to_bv 64 0)) with (hb2w (Z_to_bv 64 (U h1))).
        an L67150 D_4c214.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1)))));
            [exact L67154 | reflexivity | exact D_4c218 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes M _ _) with M1.
        afence L67158 D_4c21c.                             (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := at_ m (rz n - 16)) (b := Z_to_bv 8 2);
            [exact L6715c | reflexivity | exact D_4c220 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | reflexivity | sok16 SOK1]
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
        ab_tk L67160 D_4c224 ltac:(rewrite E16; condz).  (* [comment removed for export] *)
        an L67180 D_4c244. an L67184 D_4c248.             (* [comment removed for export] *)
        an L67188 D_4c24c.                                 (* [comment removed for export] *)
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
        ab_ft L67160 D_4c224 ltac:(condz).                (* [comment removed for export] *)
        an L67164 D_4c228.                                 (* [comment removed for export] *)
        ab_ft L67168 D_4c22c ltac:(condz).                (* [comment removed for export] *)
        eapply msteps_trans; [apply (GMAG _ M2 rom (Z_to_bv 64 MAGIC) Rmag2)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ m 8);
            [exact L67174 | reflexivity | exact D_4c238 | gres; rwH; imm_norm; rewrite ?at_addi; fold_at_vars; reflexivity | gres; rwH; reflexivity
            | do 2 (eapply store_ok_mono; [apply wbytes_grows|]); eapply (store_ok_sub segs _ m _ 16); [lia | exact SOKm | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        afence L67178 D_4c23c.                             (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := m);
            [exact L6717c | reflexivity | exact D_4c240 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity
            | do 3 (eapply store_ok_mono; [apply wbytes_grows|]); eapply (store_ok_sub segs _ m _ 16); [lia | exact SOKm | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        an L67180 D_4c244. an L67184 D_4c248.             (* [comment removed for export] *)
        an L67188 D_4c24c.                                 (* [comment removed for export] *)
        replace (amE3_mem M) with (wbytes (wbytes M2 (at_ m 8) (LE8 (at_ m (rz n - 16)))) m (LE8 (Z_to_bv 64 MAGIC)))
          by ((lazymatch goal with |- ?G => let G' := eval unfold amE3_mem in G in change_no_check G' end); rewrite (proj2 (Z.eqb_neq _ _) E0); reflexivity).
        wd_refl.
      + post. all: try (rewrite ?at_add_0_r; reflexivity). all: ra_chain.
  Qed.
  (* [comment removed for export] *)
  Definition amE4_slots (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' : word) : list (Z * word) :=
    [(120, at_ rb 0x4baf4); (112, s0); (104, s1); (96, s2); (88, s3); (80, s4); (72, s5); (64, s6); (56, s7); (48, s8); (40, s9);
     (32, s10); (24, s11); (136, at_ rb 0x6e600); (128, s0')]%Z.
  Theorem amE4 : forall (M : word -> option byte) r0 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' : word),
    getr r0 2 = sp -> getr r0 20 = at_ m (rz n) ->
    (forall (k : Z) (v : word), In (k, v) (amE4_slots s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0') -> rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c258) M rom) (mkst r (at_ rb 0x6e600) M rom)
      /\ getr r 10 = at_ m (rz n) /\ getr r 2 = at_ sp 144 /\ getr r 1 = at_ rb 0x6e600
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
    pose proof (RETe 0x4baf4 eq_refl ltac:(lia)) as RT1. pose proof (RETe 0x6e600 eq_refl ltac:(lia)) as RT2.
    wd_eexists. split.
    - an L6718c D_4c250.                                   (* [comment removed for export] *)
      fld L67190 D_4c254 (at_ rb 0x4baf4) SL.              (* [comment removed for export] *)
      fld L67194 D_4c258 s0 SL. fld L67198 D_4c25c s1 SL. fld L6719c D_4c260 s2 SL. fld L671a0 D_4c264 s3 SL.
      fld L671a4 D_4c268 s4 SL. fld L671a8 D_4c26c s5 SL. fld L671ac D_4c270 s6 SL. fld L671b0 D_4c274 s7 SL.
      fld L671b4 D_4c278 s8 SL. fld L671b8 D_4c27c s9 SL. fld L671bc D_4c280 s10 SL. fld L671c0 D_4c284 s11 SL.
      an L671c4 D_4c288.                                   (* [comment removed for export] *)
      aret L671c8 D_4c28c (at_ rb 0x4baf4).                (* [comment removed for export] *)
      ab_ft N66a28 D_4baec ltac:(condz).                  (* [comment removed for export] *)
      fld N66a2c D_4baf0 (at_ rb 0x6e600) SL.              (* [comment removed for export] *)
      fld N66a30 D_4baf4 s0' SL.                           (* [comment removed for export] *)
      an N66a34 D_4baf8.                                   (* [comment removed for export] *)
      aret N66a38 D_4bafc (at_ rb 0x6e600).                (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AME.
End FPGen1.
