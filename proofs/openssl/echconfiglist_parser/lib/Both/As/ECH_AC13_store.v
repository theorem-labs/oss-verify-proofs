(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_free ECH_AC5_small ECH_AC5_popfree ECH_AC13_small ECH_AC13_ext ECH_AC13_entry.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ASF_R1 : Z := R_OSSL_ECHSTORE_free_sk_set_thunks.   (* [comment removed for export] *)
Definition ASF_R2 : Z := R_OSSL_ECHSTORE_free_sk_pop_free.     (* [comment removed for export] *)
Definition ASF_R3 : Z := R_OSSL_ECHSTORE_free_CRYPTO_free.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_cells_h (h : Z) : list cell := [C8 (wz h); C8 (wz 0); C8 (wz 0)].
(* [comment removed for export] *)
Definition blocks_ENTRIES {HCEIL : HeapCeil} (P : Z) (xs : option (skrep * list entrep)) : list block :=
  match xs with
  | None => []
  | Some (K, es) => blocks_SK P K ++ concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es))
  end.
Lemma blocks_STORE_eq {HCEIL : HeapCeil} : forall a S,
  blocks_STORE a S = (es_id S, a, STORE_SIZE) :: blocks_ENTRIES (es_entries S) (es_entries_o S).
Proof. intros a [h [[K es]|] i]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XN.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma ENTRYobj_LB_mono : forall LB LB' m p X, ENTRYobj LB m p X -> (forall b, In b LB -> In b LB') -> ENTRYobj LB' m p X.
  Proof.
    intros LB LB' m p X (HC & HIN & O1 & O2 & O3 & O4 & XS) SUB. split; [exact HC|]. split; [apply SUB; exact HIN|].
    split; [eapply ofield_LB_mono; eauto|]. split; [eapply ofield_LB_mono; eauto|].
    split; [eapply ofield_LB_mono; eauto|]. split; [eapply ofield_LB_mono; eauto|].
    revert XS. unfold EXTS. destruct (en_exts_o X) as [[K es]|]; intros XS; [| exact XS].
    destruct XS as (X1 & SO & LEN & F2). split; [exact X1|]. split; [eapply SKobj_LB_mono; eauto|]. split; [exact LEN|].
    clear - F2 SUB. induction F2 as [|q E qs Es HE HF IH]; constructor; [eapply EXTobj_LB_mono; eauto| exact IH].
  Qed.

  Lemma ENTRYs_owned : forall LB m ps es b,
    Forall2 (fun p X => ENTRYobj LB m p X) ps es -> In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> In b LB.
  Proof.
    intros LB m ps es b F2. induction F2 as [|p X ps' es' E F IH]; cbn [concat map combine fst snd]; [intros []|].
    intros Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
    exact (ENTRYobj_owned_law LB m p X E b Hb).
  Qed.

  Lemma ENTRYs_frame : forall LB LB1 LB' SP m m' ps es,
    Forall2 (fun p X => ENTRYobj LB m p X) ps es ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> In b LB1) ->
    (forall b, In b LB1 -> In b LB') ->
    xpres H LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => ENTRYobj LB' m' p X) ps es.
  Proof.
    intros LB LB1 LB' SP m m' ps es F2. induction F2 as [|p X ps' es' E F IH]; intros KEEP SUB XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply ENTRYobj_LB_mono; [| exact SUB]. eapply (ENTRYobj_frame_law H); [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact SUB| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  Lemma ENTRYs_shad_frame : forall LB1 SP m m' ps es,
    Forall2 (fun p X => ENTRY_shad m p X) ps es ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> In b LB1) ->
    xpres H LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => ENTRY_shad m' p X) ps es.
  Proof.
    intros LB1 SP m m' ps es F2. induction F2 as [|p X ps' es' E F IH]; intros KEEP XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply (ENTRY_shad_frame_law H); [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  Lemma ENTRIES_keep : forall LB LB' SP m m' P xs,
    ENTRIES LB m P xs -> (forall b, In b (blocks_ENTRIES P xs) -> In b LB') -> xpres H LB' SP [] m m' ->
    (forall b, In b (blocks_ENTRIES P xs) -> blk_addr b + blk_size b <= SP) -> ENTRIES LB' m' P xs.
  Proof.
    intros LB LB' SP m m' P xs XS KEEP XP BEL. revert XS KEEP BEL. unfold ENTRIES, blocks_ENTRIES.
    destruct xs as [[K es]|]; intros XS KEEP BEL; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply (SKobj_frame H); [exact SO| intros b Hb; apply KEEP; apply in_or_app; left; exact Hb| exact XP].
    - split; [exact LEN|]. eapply (ENTRYs_frame LB LB' LB' SP m m'); [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| auto| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
  Lemma ENTRIES_owned : forall LB m P xs b, ENTRIES LB m P xs -> In b (blocks_ENTRIES P xs) -> In b LB.
  Proof.
    intros LB m P xs b. unfold ENTRIES, blocks_ENTRIES. destruct xs as [[K es]|]; intros XS Hb; [| destruct Hb].
    destruct XS as (_ & SO & _ & F2). apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [eapply SKobj_owned; eauto| eapply ENTRYs_owned; eauto].
  Qed.
  Lemma ENTRIES_shad_keep : forall LB' SP m m' P xs,
    ENTRIES_shad m P xs -> (forall b, In b (blocks_ENTRIES P xs) -> In b LB') -> xpres H LB' SP [] m m' ->
    (forall b, In b (blocks_ENTRIES P xs) -> blk_addr b + blk_size b <= SP) -> ENTRIES_shad m' P xs.
  Proof.
    intros LB' SP m m' P xs XSH KEEP XP BEL. revert XSH KEEP BEL. unfold ENTRIES_shad, blocks_ENTRIES.
    destruct xs as [[K es]|]; intros XSH KEEP BEL; [| exact I].
    destruct XSH as ((SH & T1 & T2) & F2). split.
    - split; [| split; [exact T1| exact T2]]. destruct SH as [SHH SHD]. split.
      + eapply (addressable_xpres_blk H); [apply KEEP; apply in_or_app; left; left; reflexivity| exact T1| exact SHH| exact XP].
      + intros NC. eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SHD NC)| exact XP].
        apply KEEP. apply in_or_app. left. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; exact NC). right. left. reflexivity.
    - eapply ENTRYs_shad_frame; [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
End XN.

(* [comment removed for export] *)
Section LAWS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma STOREobj_owned_law : EP_owned storerep STOREobj blocks_STORE.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & ENS) b Hb.
    rewrite blocks_STORE_eq in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    eapply ENTRIES_owned; [exact ENS| exact Hb].
  Qed.

  Lemma STOREobj_frame_law : EP_frame H storerep STOREobj blocks_STORE.
  Proof.
    unfold EP_frame. intros LB LB' m m' p x SP SO KEEP XP BEL.
    pose proof SO as (HC & HIN & ENS).
    rewrite blocks_STORE_eq in KEEP, BEL.
    unfold STOREobj. split.
    { eapply (xpres_rw_cells' H); [exact XP| exact HC| | constructor].
      right; right; left. exists (es_id x, p, STORE_SIZE). split; [apply KEEP; left; reflexivity|].
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia. }
    split; [apply KEEP; left; reflexivity|].
    eapply (ENTRIES_keep H); [exact ENS| intros b Hb; apply KEEP; right; exact Hb| exact XP| intros b Hb; apply BEL; right; exact Hb].
  Qed.

  Lemma STORE_shad_frame_law : eshad_frame H storerep blocks_STORE STORE_shad.
  Proof.
    unfold eshad_frame. intros LB' m m' p x SP (TOP & SH & XSH) KEEP XP BEL.
    rewrite blocks_STORE_eq in KEEP, BEL.
    split; [exact TOP|]. split.
    { eapply (addressable_xpres_blk H); [apply KEEP; left; reflexivity| exact TOP| exact SH| exact XP]. }
    eapply (ENTRIES_shad_keep H); [exact XSH| intros b Hb; apply KEEP; right; exact Hb| exact XP| intros b Hb; apply BEL; right; exact Hb].
  Qed.

  Lemma entries_cost_pos : forall xs, 0 <= entries_cost H xs.
  Proof.
    intros [[K es]|]; cbn [entries_cost]; [| lia].
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0.
    assert (E0 : 0 <= ecost_sum entrep (entry_cost H) es).
    { induction es as [|e es IH]; cbn [ecost_sum fold_right]; [lia|]. pose proof (entry_cost_pos H HH e). unfold ecost_sum in IH. lia. }
    pose proof (CF0 SK_SIZE ltac:(unfold SK_SIZE; lia)). pose proof (CF0 (Z.max (8 * sk_cap K) 0) ltac:(lia)). lia.
  Qed.
  Lemma store_cost_pos : ecost_pos storerep (store_cost H).
  Proof.
    unfold ecost_pos, store_cost. intros x. pose proof (entries_cost_pos (es_entries_o x)).
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 0 ltac:(lia)). pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) STORE_SIZE ltac:(unfold STORE_SIZE; lia)). lia.
  Qed.
End LAWS.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma as_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z),
      rw_cells asegs m p (store_cells_h h) -> 0 < p -> p mod 16 = 0 -> p + STORE_SIZE <= lo -> 0 <= h < 2^64 -> accessible m p STORE_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 (a0x : word),
          ms' = MS (mkR (Z_to_bv 64 ASF_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 p)
                       a0x (Z_to_bv 64 P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m1 (seg_rom asegs)
          /\ a0x = Z_to_bv 64 h
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)
          /\ rw_cells asegs m1 p (store_cells_h h))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_ECHSTORE_free) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BLK POS AL16 BL HR ACC0 GSB SHB0 ST CEIL LO MI.
    unfold P_OSSL_ECHSTORE_free, P_OPENSSL_sk_set_thunks, P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk, ASF_R1, R_OSSL_ECHSTORE_free_sk_set_thunks, ASHB13.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    unfold store_cells_h, wz in BLK. unfold STORE_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m p 24)) in ACC'.
    carve_frame 32%nat ST.
    do 6 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx p 24) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]) end.
    clear ACC'.
    (* [comment removed for export] *)
    step. step. ubal_by AL16. step. if_lit. step. step. step. zstep. zstep. ck8_check ACC p.
    (* [comment removed for export] *)
    step. step. step. step. step.
    finish.
    all: try reflexivity; unfold store_cells_h, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      GOT_echfree m -> mem_inv asegs m ->
      evt asegs (fun ms' => exists ra',
          ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 P_ossl_echstore_entry_free) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs) /\ ra' = Z_to_bv 64 ASF_R2)
        (MS (mkR (Z_to_bv 64 ASF_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASF_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros GG MI. unfold ASF_R1, ASF_R2, R_OSSL_ECHSTORE_free_sk_set_thunks, R_OSSL_ECHSTORE_free_sk_pop_free, P_OPENSSL_sk_pop_free.
    unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz in GG |- *.
    replace (ret_pc (Z_to_bv 64 0x5529b4)) with (Z_to_bv 64 0x5529b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. apply evt_done. eexists. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg3 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h : Z),
      rw_cells asegs m p (store_cells_h h) -> 0 < p -> p + STORE_SIZE < 2^64 -> accessible m p STORE_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ASF_R3) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 p)
                       (Z_to_bv 64 0) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 678) a3 a4 a5 a6 a7
                       (Z_to_bv 64 AECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ASF_R2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASF_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until h. intros BLK POS AB ACC MI. unfold ASF_R2, ASF_R3, R_OSSL_ECHSTORE_free_sk_pop_free, R_OSSL_ECHSTORE_free_CRYPTO_free, P_CRYPTO_free, AECHS_FILE, ASHB13.
    unfold store_cells_h, wz in BLK. unfold STORE_SIZE in *. pose proof (aword_range sp) as SPR. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    replace (ret_pc (Z_to_bv 64 0x5529c4)) with (Z_to_bv 64 0x5529c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. zstep. ck8_check ACC (p + 16). step. do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg4 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u1,
          ms' = MS (mkR ra sp gp tp t0 u1 t2 s0 s1
                       (Z_to_bv 64 p) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 679) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ASF_R3) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASF_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until p. intros FR MI. unfold ASF_R3, R_OSSL_ECHSTORE_free_CRYPTO_free, AECHS_FILE, P_CRYPTO_free. unfold aef_frame in FR.
    replace (ret_pc (Z_to_bv 64 0x5529f4)) with (Z_to_bv 64 0x5529f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR.
    step. step. step. do 4 step. step. step. step. apply evt_done. eexists. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma astorefree_spec : storefree_stmt H.
  Proof.
    unfold storefree_stmt, efree_stmt_at. intros until CH.
    intros VIS A0 SO SSH ND HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM GG RAE. subst a0.
    unfold STOREFREE_STACK, FR_OSSL_ECHSTORE_free, SKPOPFREE_STACK, ENTRYFREE_STACK, EXTFREE_STACK, FR_ossl_echstore_entry_free,
      FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, AFREE_STACK, FR_EVP_PKEY_free in LO.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -32) by lia.
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    assert (SUBL : forall q L b, In b (as_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    pose proof SO as (SC & SIN & ENS). change (rw_cells asegs m p (store_cells_h (es_entries x))) in SC.
    pose proof SSH as (TOP & SH & XSH).
    pose proof (ah_blocks H HH _ _ _ _ HP SIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. unfold STORE_SIZE in K3, K5, K7, TOP. unfold AAPP_HI in TOP. clear K6.
    pose proof (aapp_bounds p 24 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    pose proof (sh_aapp_range p 24 K7 ltac:(lia)) as (SR1 & SR2 & SR3). unfold AHI_LO in SR3. pose proof aceil_range as ACR.
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _). exact Q5. }
    rewrite blocks_STORE_eq in ND.
    set (BX := blocks_ENTRIES (es_entries x) (es_entries_o x)) in *.
    assert (OWN : forall b, In b ((es_id x, p, STORE_SIZE) :: BX) -> In b LB).
    { intros b Hb. apply (STOREobj_owned_law LB m p x SO). rewrite blocks_STORE_eq. exact Hb. }
    assert (BELX : forall b, In b BX -> blk_addr b + blk_size b <= bv_unsigned sp + -32) by (intros b Hb; pose proof (HB b (OWN b (or_intror Hb))); lia).
    assert (RXS : 0 <= es_entries x < 2^64).
    { revert ENS. unfold ENTRIES. destruct (es_entries_o x) as [[K es]|]; intros ENS; [| lia].
      destruct ENS as (X1 & SKO & _). destruct SKO as (_ & _ & KIN & _). pose proof (ah_blocks H HH _ _ _ _ HP KIN) as (Q1 & _ & Q3 & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q1, Q3, Q5. unfold SK_SIZE in *. lia. }
    assert (ACC0 : accessible m p STORE_SIZE) by (unfold STORE_SIZE; eapply addressable_accessible; [exact SH| lia| unfold STORE_SIZE; lia| unfold STORE_SIZE, AAPP_HI; lia]).
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0.
    pose proof (entries_cost_pos H HH (es_entries_o x)) as CPX. pose proof (CF0 0 ltac:(lia)) as CFZ. pose proof (CF0 24 ltac:(lia)) as CF24.
    unfold store_cost, STORE_SIZE in HAL.
    pose proof ND as ND0. cbn [map] in ND0. inversion ND0 as [|i0 l0 NI NDt]; subst i0 l0. clear ND0.
    assert (NOTHD : forall Fr, (forall b, In b Fr -> In b BX) -> ~ In (es_id x, p, STORE_SIZE) Fr).
    { intros Fr SUB K. apply NI. rewrite in_map_iff. exists (es_id x, p, STORE_SIZE). split; [reflexivity| apply SUB; exact K]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply as_seg1 with (lo := lo);
      [exact SC| exact K1| exact K2| unfold STORE_SIZE; lia| exact RXS| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & a0x & VIS1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SC1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (GG1 : GOT_echfree m1) by (eapply GOT_echfree_across; [exact MU1| exact WM1| unfold A_got_ossl_echext_free; cbn; lia| exact GG]).
    assert (XP1 : xpres H LB (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold aef_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -32 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW AW.
    assert (SHH1 : addressable m1 p 24).
    { unfold STORE_SIZE in SH. eapply addressable_transport; [exact SH| exact MU1| exact WM1|]. cbn. lia. }
    assert (ENS1 : ENTRIES LB m1 (es_entries x) (es_entries_o x)).
    { eapply (ENTRIES_keep H); [exact ENS| intros b Hb; eapply ENTRIES_owned; [exact ENS| exact Hb]| exact XP1| intros b Hb; specialize (BELX b Hb); lia]. }
    assert (XSH1 : ENTRIES_shad m1 (es_entries x) (es_entries_o x)).
    { eapply (ENTRIES_shad_keep H); [exact XSH| intros b Hb; eapply ENTRIES_owned; [exact ENS| exact Hb]| exact XP1| intros b Hb; specialize (BELX b Hb); lia]. }
    (* [comment removed for export] *)
    assert (MID : as_SR H (fun c => exists (w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 : word) m6 (st6 : as_St H) LB6,
                 as_VIS H st6 (cfg_ms c) = MS (mkR (Z_to_bv 64 ASF_R2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 ATP) w0 w1 w2 sp (Z_to_bv 64 p)
                                    c0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                               F (ret_pc (Z_to_bv 64 ASF_R2)) fc None m6 (seg_rom asegs)
                 /\ as_AKREL H st6 c /\ as_MPRES H mo1 (cfg_model c) /\ mem_inv asegs m6 /\ ACONST m6 /\ stk asegs m6 lo (bv_unsigned sp + -32)
                 /\ rw_cells asegs m6 (ATP + -164) [C4 errv] /\ as_rauxv_ok H m6 B
                 /\ as_RHEAP H st6 LB6 m6 /\ In (es_id x, p, STORE_SIZE) LB6
                 /\ Permutation (BX ++ LB6) LB /\ (forall b, In b LB6 -> In b LB)
                 /\ xpres H LB6 (bv_unsigned sp + -32) [] m1 m6 /\ IMPL_mem m6 /\ GOT_mem m6 /\ GOT_echfree m6
                 /\ rw_cells asegs m6 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)
                 /\ rw_cells asegs m6 p (store_cells_h (es_entries x)) /\ addressable m6 p 24
                 /\ as_AL H st6 >= as_AL H s - entries_cost H (es_entries_o x))
             (mkCfg msF1 mo1)).
    { pose proof ENS1 as EN'. unfold ENTRIES in EN'. pose proof XSH1 as XSH1'. unfold ENTRIES_shad in XSH1'.
      pose proof NDt as NDX.
      destruct (es_entries_o x) as [[K es]|] eqn:EXO.
      - (* [comment removed for export] *)
        destruct EN' as (HPOS & SKO & LEN & F2). destruct XSH1' as ((SKSH & T1 & T2) & F2SH).
        set (h := es_entries x) in *.
        set (EB := concat (map (fun px : Z * entrep => blocks_ENTRY (fst px) (snd px)) (combine (sk_elems K) es))) in *.
        assert (BXE : BX = blocks_SK h K ++ EB) by (unfold BX, blocks_ENTRIES; reflexivity).
        rewrite BXE in NDX.
        pose proof SKO as SO0. destruct SO0 as (_ & _ & KIN & KNC & KCAP & _ & _ & KDAT).
        pose proof (ah_blocks H HH _ _ _ _ HP1 KIN) as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6 & KB7). cbn [blk_addr blk_size fst snd] in KB1, KB2, KB3, KB4, KB5, KB6, KB7.
        unfold AIMG_TOP in KB4. unfold SK_SIZE in KB3, KB5, KB7. clear KB6.
        pose proof (sh_aapp_range h 56 KB7 ltac:(lia)) as (HS1 & HS2 & HS3). unfold AHI_LO in HS3.
        assert (PK : blk_id (es_id x, p, STORE_SIZE) <> blk_id (sk_id K, h, SK_SIZE)).
        { intros E. apply NI. rewrite in_map_iff. exists (sk_id K, h, SK_SIZE). split; [symmetry; exact E|].
          rewrite BXE. apply in_or_app. left. left. reflexivity. }
        pose proof (ah_disj H HH _ _ _ _ _ HP1 SIN KIN PK) as DPK. cbn [blk_addr blk_size fst snd] in DPK. unfold STORE_SIZE, SK_SIZE in DPK.
        assert (DBEL : sk_cap K = 0 \/ (In (sk_did K, sk_data K, 8 * sk_cap K) LB /\ sk_data K + 8 * sk_cap K <= aceil /\ 4 <= sk_cap K)).
        { destruct KDAT as [[C0 _]|(C4 & _ & _ & DIN & _)]; [left; exact C0| right].
          pose proof (ah_blocks H HH _ _ _ _ HP1 DIN) as (_ & _ & _ & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q5. split; [exact DIN| split; [exact Q5| exact C4]]. }
        assert (BEL : SK_below h K lo).
        { split; [unfold SK_SIZE; lia|]. destruct DBEL as [C0|(DIN & DB & _)]; [left; exact C0| right; lia]. }
        assert (SKR : SK_ranges H h K).
        { split; [exact (ah_blocks H HH _ _ _ _ HP1 KIN)|]. intros NC. destruct DBEL as [C0|(DIN & _ & _)]; [exfalso; exact (NC C0)|].
          exact (ah_blocks H HH _ _ _ _ HP1 DIN). }
        eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply (askset_thunks_spec H) with (lo := lo) (LB := LB) (K := K); rewrite ?unsigned_lit by lia;
          [reflexivity| reflexivity| unfold P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk; lia| exact SKO| exact BEL| exact SKSH| exact SKR| exact AC1| exact ST1| exact CEIL| lia| exact MI1]|].
        intros msF6a mo6a KREL6a MP6a PO. unfold skset_post in PO.
        destruct PO as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & VIS6a & MU6a & WM6a & MI6a & AC6a & ST6a & SO6a).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU6a, ST6a by lia. unfold SK_SIZE in MU6a.
        assert (XPh : xpres H (as_lb_remove H (sk_id K) LB) (bv_unsigned sp + -32) [] m1 m6a).
        { eapply (xpres_of_munch_listed H HH); [exact HP1| exact KIN| exact CSP| exact MU6a| exact WM6a|].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold SK_SIZE; lia| apply Forall_nil]. }
        assert (CW6 : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp + -32); (h, h + 56)]).
        { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil].
          right; right; left. exists (sk_id K, h, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; lia]. }
        assert (HP6a : as_RHEAP H s LB m6a) by (eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU6a| exact WM6a| exact CW6]).
        assert (AUX6a : as_rauxv_ok H m6a B) by (eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU6a| exact WM6a| exact CW6]).
        assert (ERR6a : rw_cells asegs m6a (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR1| exact MU6a| exact WM6a| unfold ATP; cbn; lia]).
        assert (IM6a : IMPL_mem m6a) by (eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; cbn; lia| exact IM1]).
        assert (GM6a : GOT_mem m6a) by (eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]).
        assert (GG6a : GOT_echfree m6a) by (eapply GOT_echfree_across; [exact MU6a| exact WM6a| unfold A_got_ossl_echext_free; cbn; lia| exact GG1]).
        assert (FR6a : rw_cells asegs m6a (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU6a| exact WM6a| cbn; lia]).
        assert (SC6a : rw_cells asegs m6a p (store_cells_h h)).
        { eapply rw_cells_transport; [exact SC1| exact MU6a| exact WM6a|]. unfold store_cells_h. cbn. lia. }
        assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
        assert (SHH6a : addressable m6a p 24).
        { eapply addressable_transport; [exact SHH1| exact MU6a| exact WM6a|]. cbn. rewrite S0 in SR1.
          destruct KB7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
        assert (SKSH6a : SK_shad m6a h K).
        { destruct SKSH as [SKH SKD]. split.
          - eapply addressable_transport; [exact SKH| exact MU6a| exact WM6a|]. unfold SK_SIZE. cbn. rewrite S0 in HS1.
            destruct KB7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia.
          - intros NC. destruct DBEL as [C0|(DIN & DB & C4)]; [exfalso; exact (NC C0)|].
            eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SKD NC)| exact XPh].
            apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP1) KIN)) _)). split; [exact DIN|].
            cbn [blk_id fst snd]. intros E.
            assert (ND2 : List.NoDup (map blk_id (blocks_SK h K))) by (rewrite map_app in NDX; apply NoDup_app_remove_r in NDX; exact NDX).
            unfold blocks_SK in ND2. replace (sk_cap K =? 0) with false in ND2 by (symmetry; apply Z.eqb_neq; exact NC).
            cbn [map blk_id fst snd] in ND2. inversion ND2 as [|i1 l1 NI1 _]; subst. apply NI1. left. exact E. }
        assert (KEB : forall b, In b EB -> In b (as_lb_remove H (sk_id K) LB)).
        { intros b Hb. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP1) KIN)) b)).
          split; [apply OWN; right; rewrite BXE; apply in_or_app; right; exact Hb|].
          intros E. eapply (nodup_ids_app_ne (blocks_SK h K) EB); [exact NDX| left; reflexivity| exact Hb| symmetry; exact E]. }
        assert (BELE : forall b, In b EB -> blk_addr b + blk_size b <= bv_unsigned sp + -32) by (intros b Hb; apply BELX; rewrite BXE; apply in_or_app; right; exact Hb).
        assert (F26a : Forall2 (fun q X => ENTRYobj LB m6a q X) (sk_elems K) es).
        { eapply (ENTRYs_frame H LB (as_lb_remove H (sk_id K) LB) LB (bv_unsigned sp + -32) m1 m6a); [exact F2| exact KEB| exact (SUBL _ _)| exact XPh| exact BELE]. }
        assert (F2SH6a : Forall2 (fun q X => ENTRY_shad m6a q X) (sk_elems K) es).
        { eapply (ENTRYs_shad_frame H (as_lb_remove H (sk_id K) LB) (bv_unsigned sp + -32) m1 m6a); [exact F2SH| exact KEB| exact XPh| exact BELE]. }
        assert (CH6a : as_chain H m6a (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
          by (eapply (chain_via_apres H HH); [exact CH1| apply (xpres_nil_apres H); exact XPh| exact CHS1]).
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL6a| exact VIS6a| eapply as_seg2; [exact GG6a| exact MI6a]|].
        intros msF6b mo6b KREL6b MP6b (rax6 & VIS6b & ->).
        (* [comment removed for export] *)
        pose proof (apopfree_entries_spec H HH) as PFX. unfold popfree_entries_stmt, skpopfree_stmt_gen in PFX.
        specialize (PFX (aentryfree_spec H HH) (ENTRYobj_frame_law H) ENTRYobj_owned_law (GOT_echfree_frame H) (ENTRY_shad_frame_law H) (entry_cost_pos H HH)
                        ltac:(unfold P_ossl_echstore_entry_free; lia) ltac:(reflexivity)).
        pose proof (CF0 56 ltac:(lia)) as CF56. pose proof (CF0 (8 * sk_cap K) ltac:(lia)) as CFD.
        assert (E0 : 0 <= ecost_sum entrep (entry_cost H) es).
        { clear - HH. induction es as [|e es IH]; cbn [ecost_sum fold_right]; [lia|]. pose proof (entry_cost_pos H HH e). unfold ecost_sum in IH. lia. }
        assert (CX : entries_cost H (Some (K, es)) = ecost_sum entrep (entry_cost H) es + as_Cf H (8 * sk_cap K) + as_Cf H SK_SIZE).
        { cbn [entries_cost]. rewrite (Z.max_l (8 * sk_cap K) 0) by lia. reflexivity. }
        rewrite CX in CPX |- *. unfold SK_SIZE in CPX, CX |- *.
        eapply (ah_seq H HH).
        { eapply PFX with (a := h) (K := sk_with_thunk K O_SK_FREETH P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) (xs := es) (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv)
                          (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
            rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?e_sk_cap_with_thunk;
            [exact VIS6b| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ASF_R2, R_OSSL_ECHSTORE_free_sk_pop_free; lia).
          all: first [exact SO6a| exact LEN| exact F26a| exact F2SH6a| exact NDX| exact HP6a| exact KREL6b| exact AUX6a| exact ST6a| exact CEIL| exact ERR6a| exact MI6a
                     | reflexivity| exact SP16'| exact AC6a| exact CH6a| exact CHS1| exact IM6a| exact GM6a| exact GG6a
                     | unfold SK_shad; rewrite ?e_sk_cap_with_thunk, ?e_sk_data_with_thunk; exact SKSH6a
                     | unfold is_sk_freefunc_thunk; right; left; reflexivity
                     | unfold SKPOPFREE_STACK, ENTRYFREE_STACK, EXTFREE_STACK, FR_ossl_echstore_entry_free, FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, AFREE_STACK, FR_EVP_PKEY_free; lia
                     | unfold ASF_R2; eapply pf_ok_call; [exact PF|]; unfold PF_storefree; intros y Hy; apply in_app_iff; left; exact Hy
                     | unfold SK_SIZE; lia | match goal with |- ?G => idtac "LEFTP:" G end]. }
        clear PFX. intros [msF6 mo6] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m6 & st6 & LB6 &
                        VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & PERM6 & HP6 & XP6 & IM6 & GM6 & GG6 & AL6).
        rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM6. fold EB in PERM6. cbn [sk_cap sk_with_thunk] in AL6.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST6, XP6 by lia.
        pose proof PERM6 as P6. rewrite app_assoc in P6.
        assert (SUB6 : forall b, In b LB6 -> In b LB) by (intros b Hb; eapply Permutation_in; [exact P6| apply in_or_app; right; exact Hb]).
        assert (SIN6 : In (es_id x, p, STORE_SIZE) LB6).
        { eapply perm_in_rest; [exact P6| exact SIN|]. apply NOTHD. intros b Hb. rewrite BXE. exact Hb. }
        assert (SUBR : forall b, In b LB6 -> In b (as_lb_remove H (sk_id K) LB)).
        { eapply (perm_rest_sub_remove H HH); [exact HP1| exact P6|]. apply in_or_app. left. left. reflexivity. }
        apply (ah_done H HH). cbn [cfg_ms cfg_model].
        exists v0, v1, v2, e0, e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m6, st6, LB6.
        split; [exact VIS6|]. split; [exact KREL6|]. split; [eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [exact MP6a| exact MP6b]|].
        split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
        split; [rewrite unsigned_lit in ERR6 by (unfold ATP; lia); exact ERR6|]. split; [exact AUX6|]. split; [exact HP6|]. split; [exact SIN6|].
        split; [rewrite BXE; first [exact P6| rewrite app_assoc; exact P6| rewrite <- app_assoc; exact P6]|]. split; [exact SUB6|].
        split.
        { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPh| lia| exact SUBR| auto]| exact XP6]. }
        split; [exact IM6|]. split; [exact GM6|]. split; [exact GG6|].
        split; [eapply (xpres_rw_cells' H); [exact XP6| exact FR6a| left; cbn; lia| constructor]|].
        split.
        { eapply (xpres_rw_cells' H); [exact XP6| exact SC6a| | constructor]. right; right; left. exists (es_id x, p, STORE_SIZE). split; [exact SIN6|].
          unfold store_cells_h. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia. }
        split; [eapply (addressable_xpres_blk H); [exact SIN6| unfold AAPP_HI; lia| exact SHH6a| exact XP6]|].
        unfold SK_SIZE in AL6. lia.
      - (* [comment removed for export] *)
        assert (BXE : BX = []) by (unfold BX, blocks_ENTRIES; reflexivity).
        assert (H0 : es_entries x = 0) by exact EN'. rewrite H0 in VIS1.
        eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply askset_thunks_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
          [exact ST1| exact CEIL| lia| exact MI1| exact AC1]|].
        intros msF6a mo6a KREL6a MP6a PO. unfold sknull_post in PO.
        destruct PO as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & VIS6a & MU6a & WM6a & MI6a & AC6a & ST6a).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU6a, ST6a by lia.
        assert (GG6a : GOT_echfree m6a) by (eapply GOT_echfree_across; [exact MU6a| exact WM6a| unfold A_got_ossl_echext_free; cbn; lia| exact GG1]).
        eapply (ahh_evt_then H HH); [exact KREL6a| exact VIS6a| eapply as_seg2; [exact GG6a| exact MI6a]|].
        intros msF6b mo6b KREL6b MP6b (rax6 & VIS6b & ->).
        eapply (ahh_evt H HH); [exact KREL6b| exact VIS6b| eapply ask_pop_free_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
          [exact ST6a| exact CEIL| unfold FR_sk_pop_free; lia| exact MI6a| exact AC6a]|].
        intros msF6 mo6 KREL6 MP6 PO. unfold sknull_post in PO.
        destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m6 & VIS6 & MU6 & WM6 & MI6 & AC6 & ST6).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU6, ST6 by lia.
        assert (CW6 : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp + -32)]) by (constructor; [left; cbn; lia| constructor]).
        assert (XPa : xpres H LB (bv_unsigned sp + -32) [] m1 m6a)
          by (eapply (xpres_of_munch H s LB _ [] _ m1 m1 m6a); [exact HH| exact HP1| exact MU6a| exact WM6a|]; constructor; [left; cbn; lia| constructor]).
        assert (HP6a : as_RHEAP H s LB m6a) by (eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU6a| exact WM6a| exact CW6]).
        assert (XPb : xpres H LB (bv_unsigned sp + -32) [] m6a m6)
          by (eapply (xpres_of_munch H s LB _ [] _ m6a m6a m6); [exact HH| exact HP6a| exact MU6| exact WM6|]; constructor; [left; cbn; lia| constructor]).
        assert (XPab : xpres H LB (bv_unsigned sp + -32) [] m1 m6) by (eapply xpres_trans; [exact XPa| exact XPb]).
        cbn [cfg_ms cfg_model].
        exists v0, v1, v2, (Z_to_bv 64 0), e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m6, s, LB.
        split; [exact VIS6|]. split; [exact KREL6|].
        split; [eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [exact MP6a| exact MP6b]|].
        split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
        split; [eapply rw_cells_transport; [| exact MU6| exact WM6| unfold ATP; cbn; lia]; eapply rw_cells_transport; [exact ERR1| exact MU6a| exact WM6a| unfold ATP; cbn; lia]|].
        split. { eapply (ah_rauxv_frame H HH); [| exact MU6| exact WM6| exact CW6]. eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU6a| exact WM6a| exact CW6]. }
        split. { eapply (ah_RHEAP_frame H HH); [exact HP6a| exact MU6| exact WM6| exact CW6]. }
        split; [exact SIN|]. rewrite BXE. cbn [app]. split; [apply Permutation_refl|]. split; [auto|].
        split; [exact XPab|].
        split; [eapply IMPL_across; [exact MU6| exact WM6| unfold A_malloc_impl; cbn; lia|]; eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; cbn; lia| exact IM1]|].
        split; [eapply GOT_across; [exact MU6| exact WM6| unfold A_got_CRYPTO_malloc; cbn; lia|]; eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]|].
        split; [eapply GOT_echfree_across; [exact MU6| exact WM6| unfold A_got_ossl_echext_free; cbn; lia| exact GG6a]|].
        split; [eapply (xpres_rw_cells' H); [exact XPab| exact FR1| left; cbn; lia| constructor]|].
        split.
        { eapply (xpres_rw_cells' H); [exact XPab| exact SC1| | constructor]. right; right; left. exists (es_id x, p, STORE_SIZE). split; [exact SIN|].
          unfold store_cells_h. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia. }
        split; [eapply (addressable_xpres_blk H); [exact SIN| unfold AAPP_HI; lia| exact SHH1| exact XPab]|].
        cbn [entries_cost]. lia. }
    (* [comment removed for export] *)
    eapply (ah_seq H HH); [exact MID|]. clear MID.
    intros [msF6 mo6] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (k0 & k1 & k2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & k3 & k4 & k5 & k6 & m6 & st6 & LB6 &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & HP6 & SIN6 & PERMX & SUB6 & XPM1 & IM6 & GM6 & GG6 & FR6 & SC6 & SHH6 & AL6).
    assert (MPA6 := ah_mpres_trans H HH _ _ _ MP1 MP6). clear MP1 MP6.
    assert (ACC6 : accessible m6 p STORE_SIZE) by (unfold STORE_SIZE; eapply addressable_accessible; [exact SHH6| lia| lia| unfold AAPP_HI; lia]).
    assert (CH6 : as_chain H m6 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH1| apply (xpres_nil_apres H); exact XPM1| exact CHS1]).
    assert (XPM : xpres H LB6 (bv_unsigned sp) [] m m6).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XP1| lia| exact SUB6| auto]| eapply (xpres_weaken H); [exact XPM1| lia| auto| auto]]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply as_seg3; [exact SC6| exact K1| unfold STORE_SIZE; lia| exact ACC6| exact MI6]|].
    intros msF7 mo7 KREL7 MP7 VIS7.
    assert (MPA7 := ah_mpres_trans H HH _ _ _ MPA6 MP7). clear MPA6 MP7.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (lo := lo) (B := B) (LB := LB6) (s := st6) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS7| ..]; rewrite ?unsigned_lit by (unfold ASF_R3, R_OSSL_ECHSTORE_free_CRYPTO_free; lia).
      all: first [exact HP6| exact KREL7| exact AUX6| exact ST6| exact CEIL| exact ERR6| exact MI6| reflexivity| exact SP16'| exact AC6| exact CH6| exact CHS1
                 | exact IM6| exact GM6| unfold CFREE_STACK, AFREE_STACK; lia | lia | match goal with |- ?G => idtac "LEFTN:" G end]. }
    intros [msF7b mo7b] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m7 & st7 &
                    VIS7b & KREL7b & MP7b & MI7 & AC7 & ST7 & ERR7 & AUX7 & XP7 & HEAP7 & IM7 & GM7 & AL7).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST7, XP7 by lia.
    assert (MPA7b := ah_mpres_trans H HH _ _ _ MPA7 MP7b). clear MPA7 MP7b.
    assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP7| exact FR6| left; cbn; lia| constructor]).
    assert (SC7 : rw_cells asegs m7 p (store_cells_h (es_entries x))).
    { eapply (xpres_rw_cells' H); [exact XP7| exact SC6| | constructor]. right; right; left. exists (es_id x, p, STORE_SIZE). split; [exact SIN6|].
      unfold store_cells_h. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia. }
    assert (SHH7 : addressable m7 p 24) by (eapply (addressable_xpres_blk H); [exact SIN6| unfold AAPP_HI; lia| exact SHH6| exact XP7]).
    assert (GG7 : GOT_echfree m7) by (eapply (GOT_echfree_xpres H); [exact XP7| exact CSP| constructor| exact GG6]).
    assert (XPM7 : xpres H LB6 (bv_unsigned sp) [] m m7).
    { eapply xpres_trans; [exact XPM| eapply (xpres_weaken H); [exact XP7| lia| auto| auto]]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL7b| exact VIS7b| eapply as_seg4; [exact FR7| exact MI7]|].
    intros msF8 mo8 KREL8 MP8 (u1x & VIS8).
    assert (MPA8 := ah_mpres_trans H HH _ _ _ MPA7b MP8). clear MPA7b MP8.
    unfold aef_frame in FR7. release_frame FR7 ST7 (bv_unsigned sp). rename ST7 into ST8.
    pose proof (rw_cells_flatten _ _ _ _ SC7) as SCB. unfold store_cells_h in SCB. cbn [cells_size csize Nat.add] in SCB.
    assert (CH8 : as_chain H m7 (bv_unsigned s0) CH).
    { eapply (chain_via_apres H HH); [exact CHN| apply (xpres_nil_apres H); exact XPM7| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia]. }
    (* [comment removed for export] *)
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB6) (s := st7) (p := es_id x) (n := STORE_SIZE) (errv := errv) (CH := CH);
        [exact VIS8| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ATP; lia).
      all: first [exact HEAP7| exact KREL8| exact SIN6| exact AUX7| exact SPB| exact ST8| exact CEIL| exact ERR7| exact MI7| reflexivity| exact SP16| exact AC7| exact CH8| exact CHS
                 | unfold STORE_SIZE; exact SCB| unfold STORE_SIZE; exact SHH7| exact IM7| exact GM7| exact RAE| unfold CFREE_STACK, AFREE_STACK; lia
                 | eapply pf_ok_incl; [exact PF|]; unfold PF_storefree; intros y Hy; do 2 (apply in_app_iff; right); exact Hy
                 | unfold STORE_SIZE; lia | match goal with |- ?G => idtac "LEFTT:" G end]. }
    intros [msF9 mo9] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m9 & st9 &
                    VIS9 & KREL9 & MP9 & MI9 & AC9 & ST9 & ERR9 & AUX9 & XP9 & HEAP9 & IM9 & GM9 & AL9).
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, e0, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, m9, st9, (as_lb_remove H (es_id x) LB6).
    split; [exact VIS9|]. split; [exact KREL9|]. split; [eapply (ah_mpres_trans H HH); [exact MPA8| exact MP9]|].
    split; [exact MI9|]. split; [exact AC9|]. split; [exact ST9|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); rewrite unsigned_lit in ERR9 by (unfold ATP; lia); exact ERR9|]. split; [exact AUX9|].
    split.
    { rewrite blocks_STORE_eq. fold BX. cbn [app]. eapply Permutation_trans; [| exact PERMX].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
      eapply (alb_remove_perm H HH); [exact HEAP7| exact SIN6]. }
    split; [exact HEAP9|].
    split. { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPM7| lia| exact (SUBL _ _)| auto]| exact XP9]. }
    split; [exact IM9|]. split; [exact GM9|].
    split; [eapply (GOT_echfree_xpres H); [exact XP9| exact CSP0| constructor| exact GG7]|].
    unfold store_cost, STORE_SIZE. unfold STORE_SIZE in AL9. lia.
  Qed.
End W.
