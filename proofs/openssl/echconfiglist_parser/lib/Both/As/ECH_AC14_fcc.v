(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 SecLazy ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C10 ECH_AStmt_C11 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AStmt_C14 ECH_ALibMF ECH_ALibMid ECH_AKit ECH_AKitSeg ECH_AsKit
  ECH_AC1_malloc ECH_AC1_zalloc ECH_AC1_free ECH_AC1_dup ECH_AC5_small ECH_AC5_popfree ECH_AC11_find ECH_AC11_suitebad
  ECH_AC4_rep ECH_AC13_small ECH_AC13_ext ECH_AC13_entry ECH_AC12_new ECH_AC12_xbuf ECH_AC12_vpmfree ECH_AC12_addstr ECH_AC12_add1host ECH_ARostr ECH_AC11_fail
  F_strrchr N6_strrchr F_strspn N6_strspn N6_iface ECH_AC14_kit ECH_AC14_fcc_seg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section SC.
  Context {HCEIL : HeapCeil}.
  Lemma suite_cells_app : forall r1 r2, suite_cells (r1 ++ r2) = suite_cells r1 ++ suite_cells r2.
  Proof. induction r1 as [|[[k d] a] r1 IH]; intros r2; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma suite_cells_size : forall rows, Z.of_nat (cells_size (suite_cells rows)) = 6 * zlength rows.
  Proof. unfold zlength. induction rows as [|[[k d] a] rows IH]; [reflexivity|]. cbn [suite_cells cells_size csize length]. rewrite Nat2Z.inj_succ. cbn [cells_size csize] in IH. lia. Qed.
  (* [comment removed for export] *)
  Lemma suite_row_at : forall m S rows i kem kdf aead,
    rw_cells asegs m S (suite_cells rows) -> nth_error rows (Z.to_nat i) = Some (kem, kdf, aead) -> 0 <= i ->
    rw_cells asegs m (S + 6 * i) [C2 (wz kem); C2 (wz kdf); C2 (wz aead)].
  Proof.
    intros m S rows i kem kdf aead RC NTH I0.
    destruct (@nth_error_split _ rows (Z.to_nat i) (kem, kdf, aead) NTH) as (l1 & l2 & EQ & L1). subst rows.
    rewrite suite_cells_app in RC. apply rw_cells_app in RC. destruct RC as [_ RC]. cbn [suite_cells app] in RC.
    change (C2 (wz kem) :: C2 (wz kdf) :: C2 (wz aead) :: suite_cells l2) with ([C2 (wz kem); C2 (wz kdf); C2 (wz aead)] ++ suite_cells l2) in RC.
    apply rw_cells_app in RC. destruct RC as [RC _]. pose proof (suite_cells_size l1) as SZ. unfold zlength in SZ. rewrite L1, Z2Nat.id in SZ by lia.
    replace (S + 6 * i) with (S + Z.of_nat (cells_size (suite_cells l1))) by lia. exact RC.
  Qed.
End SC.

(* [comment removed for export] *)
Lemma newlib_err_bounds {HCEIL : HeapCeil} : forall M M' LBN x, mid_ctx M = CtxReady x -> mid_step M M' -> mid_newlib_ok M M' LBN ->
  lb_bytes LBN + errph_bytes (mid_err M') <= errph_bytes (mid_err M) /\ Z.of_nat (length LBN) + errph_cnt (mid_err M') <= errph_cnt (mid_err M)
  /\ (forall c, mid_err M = ErrReady c -> LBN = []).
Proof.
  intros [f cph eph E v] [f' cph' eph' E' v'] LBN x CX ST NW. unfold mid_step, mid_newlib_ok in *.
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. subst cph. destruct ST as (_ & SC & SE & _). destruct NW as (LA & LE & P & C & R).
  assert (LA0 : LA = []) by (destruct cph' as [|b']; [exact C| pose proof (SC x eq_refl) as K; injection K as <-; exact C]).
  subst LA. cbn [app] in P.
  rewrite (lb_bytes_perm _ _ P), (Permutation_length P).
  destruct eph as [|c].
  - destruct eph' as [|c']; cbn [errph_delta errph_bytes errph_cnt] in R |- *.
    + subst LE. cbn. unfold ERRINIT_BYTES, ERRINIT_CNT. split; [lia|]. split; [lia|]. intros c Hc; discriminate Hc.
    + split; [lia|]. split; [lia|]. intros c Hc; discriminate Hc.
  - cbn in R. subst LE. rewrite (SE c eq_refl). cbn. split; [lia|]. split; [lia|]. intros c' Hc. exact (Permutation_nil (Permutation_sym P)).
Qed.

(* [comment removed for export] *)
Lemma le2_wz_mod : forall t, le2 (wz t) = le2 (wz (t mod 65536)).
Proof.
  intros t. unfold le2, wz. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  transitivity (Z_to_le_bytes 2 t); [apply Z_to_le_bytes_mod; cbn; lia|].
  transitivity (Z_to_le_bytes 2 (t mod 65536)); [| symmetry; apply Z_to_le_bytes_mod; cbn; lia].
  change 65536 with (2^16). symmetry. apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma rw_cells_C2_le2 : forall m A v v' cs, le2 v = le2 v' -> rw_cells asegs m A (C2 v :: cs) -> rw_cells asegs m A (C2 v' :: cs).
Proof.
  intros m A v v' cs E RC. unfold rw_cells, cells_at in *. cbn [cells_bytes cbytes cells_wf cells_size csize] in *. rewrite <- E. exact RC.
Qed.
Lemma Forall2_nth_error {X Y} (R : X -> Y -> Prop) : forall xs ys i x y,
  Forall2 R xs ys -> nth_error xs i = Some x -> nth_error ys i = Some y -> R x y.
Proof.
  intros xs ys i x y F2. revert i. induction F2 as [|a b xs' ys' Rab F IH]; intros i Hx Hy; [destruct i; discriminate Hx|].
  destruct i as [|i]; cbn in Hx, Hy; [congruence| exact (IH i Hx Hy)].
Qed.
Lemma rfind_hit_nth : forall l c i, rfind l c = Some i -> exists x, nth_error l i = Some x /\ bv_unsigned x = bv_unsigned c.
Proof.
  induction l as [|y l IH]; intros c i H; cbn in H; [discriminate|].
  destruct (rfind l c) as [j|] eqn:R.
  - injection H as <-. destruct (IH c j R) as (x & N & E). exists x. cbn. auto.
  - destruct (Z.eqb_spec (bv_unsigned y) (bv_unsigned c)); [| discriminate]. injection H as <-. exists y. cbn. auto.
Qed.
Lemma cstr_suffix : forall m A ns sl i, bytes_at asegs m A (ns ++ Z_to_bv 8 0 :: sl) -> (i <= length ns)%nat ->
  bytes_at asegs m (A + Z.of_nat i) (skipn i ns ++ Z_to_bv 8 0 :: sl).
Proof.
  intros m A ns sl i BS IL. rewrite <- (firstn_skipn i ns) in BS. rewrite <- app_assoc in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
  rewrite firstn_length_le in BS by exact IL. exact BS.
Qed.
Lemma nth_error_skipn' : forall {X} (l : list X) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof. intros X l n. revert l. induction n as [|n IH]; intros l i; [reflexivity|]. destruct l as [|x l]; cbn; [destruct i; reflexivity| apply IH]. Qed.

(* [comment removed for export] *)
Definition S_AFC_FILE : list byte := Eval vm_compute in img_cstr AA_ECHS_FILE 64.
Definition K_AFC_FILE : list byte := Eval vm_compute in img_slack AA_ECHS_FILE (length S_AFC_FILE).
Definition S_AFC_FUNC : list byte := Eval vm_compute in img_cstr AA_FCC_FUNC 64.
Definition K_AFC_FUNC : list byte := Eval vm_compute in img_slack AA_FCC_FUNC (length S_AFC_FUNC).
Definition S_DIGITS : list byte := Eval vm_compute in img_cstr AA_DIGITS 64.
Definition K_DIGITS : list byte := Eval vm_compute in img_slack AA_DIGITS (length S_DIGITS).
Definition S_HEXDIGITS : list byte := Eval vm_compute in img_cstr AA_HEXDIGITS 64.
Definition K_HEXDIGITS : list byte := Eval vm_compute in img_slack AA_HEXDIGITS (length S_HEXDIGITS).
Section RO.
  Context {HCEIL : HeapCeil}.
  Lemma R_AFC_FILE : ROSTR AA_ECHS_FILE S_AFC_FILE K_AFC_FILE.   Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_AFC_FUNC : ROSTR AA_FCC_FUNC S_AFC_FUNC K_AFC_FUNC.    Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_DIGITS : ROSTR AA_DIGITS S_DIGITS K_DIGITS.            Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_HEXDIGITS : ROSTR AA_HEXDIGITS S_HEXDIGITS K_HEXDIGITS. Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma S_AFC_FILE_len : Z.of_nat (length S_AFC_FILE) = 19. Proof. reflexivity. Qed.
  Lemma S_AFC_FUNC_len : Z.of_nat (length S_AFC_FUNC) = 23. Proof. reflexivity. Qed.
  Lemma S_DIGITS_len : length S_DIGITS = 10%nat. Proof. reflexivity. Qed.
  Lemma S_HEXDIGITS_len : length S_HEXDIGITS = 22%nat. Proof. reflexivity. Qed.
  Lemma AR_AFC_FILE : AROSTR AA_ECHS_FILE S_AFC_FILE K_AFC_FILE.
  Proof. eapply AROSTR_intro_hull; [exact R_AFC_FILE| unfold aglobals; cbn; do 52 right; left; reflexivity| ..];
    vm_compute; intros X; discriminate X. Qed.
  Lemma AR_AFC_FUNC : AROSTR AA_FCC_FUNC S_AFC_FUNC K_AFC_FUNC.
  Proof. eapply AROSTR_intro; [exact R_AFC_FUNC| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma AR_DIGITS : AROSTR AA_DIGITS S_DIGITS K_DIGITS.
  Proof. eapply AROSTR_intro; [exact R_DIGITS| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma AR_HEXDIGITS : AROSTR AA_HEXDIGITS S_HEXDIGITS K_HEXDIGITS.
  Proof. eapply AROSTR_intro; [exact R_HEXDIGITS| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
End RO.

(* [comment removed for export] *)
Lemma pf_shift_mono : forall r A B, incl A B -> incl (pf_shift r A) (pf_shift r B).
Proof. intros r A B I. unfold pf_shift. apply incl_map. exact I. Qed.
Section PFM.
  Context {HCEIL : HeapCeil}.
  Lemma PF_errnew_mstep : forall M M', mid_step M M' -> incl (PF_errnew (mid_err M')) (PF_errnew (mid_err M)).
  Proof.
    intros M M' (_ & _ & SE & _). unfold PF_errnew. apply incl_app_app; [| apply incl_refl]. apply pf_shift_mono.
    destruct (mid_err M) as [|c0] eqn:E0; destruct (mid_err M') as [|c1] eqn:E1; cbn [PF_egs]; try apply incl_refl; [apply incl_nil_l|].
    exfalso. specialize (SE _ eq_refl). discriminate SE.
  Qed.
  Lemma PF_hfind_mstep : forall f M M', mid_step M M' -> incl (PF_hfind f (mid_err M')) (PF_hfind f (mid_err M)).
  Proof. intros f M M' ST. unfold PF_hfind. apply incl_app_app; [apply pf_shift_mono; apply (PF_errnew_mstep _ _ ST)| apply incl_refl]. Qed.
  Lemma PF_suitebad_mstep : forall M M', mid_step M M' -> incl (PF_suitebad (mid_err M')) (PF_suitebad (mid_err M)).
  Proof. intros M M' ST. unfold PF_suitebad. repeat (apply incl_app_app; [apply pf_shift_mono; apply (PF_hfind_mstep _ _ _ ST)|]). apply pf_shift_mono; apply (PF_hfind_mstep _ _ _ ST). Qed.
  Lemma pf_raise_mstep : forall r1 r2 r3 M M', mid_step M M' -> incl (pf_raise r1 r2 r3 (mid_err M')) (pf_raise r1 r2 r3 (mid_err M)).
  Proof. intros r1 r2 r3 M M' ST. unfold pf_raise. apply incl_app_app; [apply pf_shift_mono; apply (PF_errnew_mstep _ _ ST)| apply incl_refl]. Qed.
End PFM.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis RAISE : araise_stmt H.
  Hypothesis SPN : strspn_icpt_stmt.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma CANL : forall s LBc m, as_RHEAP H s LBc m -> exists can, rw_cells asegs m ACANARY_CELL [C8 (wz can)] /\ 0 <= can < 2^64.
  Proof. intros s1 LBc m1 HP1. destruct (HHx_canary H HHx s1 LBc m1 HP1) as (can & _ & CC & CR). exists can. split; [exact CC| exact CR]. Qed.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (mo : Model)
            (LIB LB : list block) (LF : list fframe) (M : libmid) (x : ctxinfo) (ee lo B : Z) (E : entrep)
            (rows : list (Z * Z * Z)) (ps : bptr) (sn : Z) (pn : bptr) (ns : list byte) (CH : list (Z * Z)) (A : Z) (p : bptr) (s00 : as_St H).
  Let spq : Z := bv_unsigned sp + -128.
  Let VB : block := (p, A, VPM_SIZE).
  Hypothesis NSR : 1 <= en_nsuites E < 2^31.
  Hypothesis SUO : en_suites_o E = Some (ps, sn).
  Hypothesis ROWS : zlength rows = en_nsuites E.
  Hypothesis SNR : 6 * en_nsuites E <= sn.
  Hypothesis ROK : Forall row_ok rows.
  Hypothesis PNO : en_pname_o E = Some (pn, zlength ns + 1).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) ns.
  Hypothesis NSL : 1 <= zlength ns <= 255.
  Hypothesis BEL : Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E).
  Hypothesis IDS : forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b'.
  Hypothesis LIBSUB : forall b, In b LIB -> In b LB.
  Hypothesis CX : mid_ctx M = CtxReady x.
  Hypothesis MF0 : mid_flag M = 1.
  Hypothesis BY : lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + FCC_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H.
  Hypothesis CN : Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + FCC_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis BHI : B < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - FCC_STACK M.
  Let LO8K : lo + 8768 <= bv_unsigned sp.
  Proof.
    clear - LO. unfold FCC_STACK, FR_ech_final_config_checks in LO.
    pose proof (Z.le_max_l ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) as K1.
    pose proof (Z.le_max_l (Z.max ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) (Z.max (SUITECHECK_STACK (mid_err M)) FCC_ICPT_STACK)) as K2.
    assert (A1 : ADD1HOST_STACK = 8640) by reflexivity. lia.
  Qed.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis CLOSED : mid_closed_ok H M.
  Hypothesis LFB : (length LF + mid_LF M <= AFS_MAXLIVE)%nat.
  Hypothesis CHS : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp'.
  Hypothesis PF : pf_ok (as_TR H) (PF_fcc (mid_err M)) (bv_unsigned ra) CH.
  Hypothesis CHN0 : as_chain H m0 (bv_unsigned s0) CH.
  Hypothesis HAL0 : FCC_COST H M (en_nsuites E) <= as_AL H s00.
  Hypothesis VBR : ablock_range H A VPM_SIZE.
  Hypothesis LBE0 : 0 <= lb_bytes (mid_errblocks M).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let RC : Z := RAISE_COST H (mid_err M).

  (* [comment removed for export] *)
  Definition fworld (m : mem) (s' : as_St H) (M' : libmid) (LBN : list block) (errv' : word) (V : vpmrep) (NB : list block) (XS : list (Z * Z)) (spent : Z) : Prop :=
       mem_inv asegs m /\ ACONST m /\ stk asegs m lo spq /\ rw_cells asegs m spq (afcc_frame ee (Z_to_bv 64 A) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ as_RHEAP H s' (mid_errblocks M' ++ LBN ++ NB ++ VB :: LB) m
    /\ LIBMID (LBN ++ LIB) m M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M /\ mid_vdso M' = mid_vdso M
    /\ ENTRYobj LB m ee E /\ ENTRY_shad m ee E /\ rw_cells asegs m (en_suites E) (suite_cells rows) /\ bytes_at asegs m (en_pname E) (ns ++ [Z_to_bv 8 0])
    /\ VPMobj (NB ++ VB :: LB) m A V /\ VPM_shad m A V /\ vp_id V = p /\ Permutation (blocks_VPM A V) (VB :: NB)
    /\ Z.of_nat (length NB) <= 4 /\ lb_bytes NB <= ADD1HOST_BYTES
    /\ stack0 m lo (bv_unsigned sp) /\ as_RFS H LF m /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ errph_foot (mid_err M)) m0 m
    /\ (0 <= spent /\ as_AL H s' + spent >= as_AL H s00).

  Lemma mid_step_trans' : forall M0 M1 M2, mid_step M0 M1 -> mid_step M1 M2 -> mid_step M0 M2.
  Proof.
    clear. intros M0 M1 M2 (F1 & C1 & E1 & V1) (F2 & C2 & E2 & V2). unfold mid_step.
    split; [exact F2|]. split; [intros b Hb; exact (C2 b (C1 b Hb))|]. split; [intros c Hc; exact (E2 c (E1 c Hc))| intros Hv; exact (V2 (V1 Hv))].
  Qed.
  Lemma RC_pos : 0 <= RC.
  Proof.
    cbv delta [RC]. unfold RAISE_COST. pose proof (errph_nonneg (mid_err M)) as [B0 _].
    pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)).
    pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma RC_mono : forall M', mid_step M M' -> RAISE_COST H (mid_err M') <= RC.
  Proof.
    intros M' (_ & _ & SE & _). cbv delta [RC]. unfold RAISE_COST, raise_bytes.
    destruct (mid_err M) as [|c0] eqn:PH; destruct (mid_err M') as [|c1] eqn:PH'.
    - lia.
    - cbn [errph_bytes]. pose proof (aCm_mono H HH (0 + ERRDEBUG_BYTES) (ERRINIT_BYTES + ERRDEBUG_BYTES) ltac:(unfold ERRINIT_BYTES, ERRDEBUG_BYTES; lia)).
      pose proof (aCf_mono H HH (0 + ERRDEBUG_BYTES) (ERRINIT_BYTES + ERRDEBUG_BYTES) ltac:(unfold ERRINIT_BYTES, ERRDEBUG_BYTES; lia)). lia.
    - exfalso. specialize (SE _ eq_refl). discriminate SE.
    - specialize (SE _ eq_refl). injection SE as <-. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma RCR_pos : 0 <= RCR H.
  Proof. unfold RCR. pose proof (aCm_pos H HH ERRDEBUG_BYTES ltac:(unfold ERRDEBUG_BYTES; lia)). pose proof (aCf_pos H HH ERRDEBUG_BYTES ltac:(unfold ERRDEBUG_BYTES; lia)). lia. Qed.
  Lemma RCp_pos : forall ph, 0 <= RAISE_COST H ph.
  Proof.
    intros ph. unfold RAISE_COST. pose proof (errph_nonneg ph) as [B0 _].
    pose proof (aCm_pos H HH (raise_bytes ph) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)). pose proof (aCf_pos H HH (errph_bytes ph + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia.
  Qed.
  Lemma RCp_ge : forall ph, RCR H <= RAISE_COST H ph.
  Proof.
    intros ph. unfold RAISE_COST, RCR, raise_bytes. pose proof (errph_nonneg ph) as [B0 _].
    pose proof (aCm_mono H HH ERRDEBUG_BYTES (errph_bytes ph + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)).
    pose proof (aCf_mono H HH ERRDEBUG_BYTES (errph_bytes ph + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia.
  Qed.
  Lemma RC_ready : forall c, RAISE_COST H (ErrReady c) = RCR H.
  Proof. intros c. unfold RAISE_COST, RCR, raise_bytes. cbn [errph_bytes]. rewrite Z.add_0_l. reflexivity. Qed.
  Lemma RCd_ready : forall ph c, RAISE_COSTd H ph (ErrReady c) = RAISE_COST H ph.
  Proof. intros ph c. unfold RAISE_COSTd, RAISE_COST, raise_bytes. cbn [errph_bytes]. rewrite Z.sub_0_r. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma RCd_eq : forall M', mid_step M M' -> RAISE_COSTd H (mid_err M) (mid_err M') = RC - RAISE_COST H (mid_err M') + RCR H.
  Proof.
    intros M' (_ & _ & SE & _). cbv delta [RC]. unfold RAISE_COSTd, RAISE_COST, RCR, raise_bytes.
    destruct (mid_err M) as [|c0] eqn:PH; destruct (mid_err M') as [|c1] eqn:PH'; cbn [errph_bytes].
    - rewrite Z.sub_diag, !Z.add_0_l. lia.
    - rewrite Z.sub_0_r, !Z.add_0_l. lia.
    - exfalso. specialize (SE _ eq_refl). discriminate SE.
    - rewrite Z.sub_diag, !Z.add_0_l. lia.
  Qed.
  Lemma SPENT_le_COST : forall M' k, mid_step M M' -> FCC_SPENT H M M' k <= FCC_COST H M k.
  Proof. intros M' k ST. unfold FCC_SPENT, FCC_COST. rewrite (RCd_eq M' ST). pose proof (RCp_ge (mid_err M')). lia. Qed.

  (* [comment removed for export] *)
  Lemma fworld_entry : forall m s' M' LBN errv' V NB XS spent,
    fworld m s' M' LBN errv' V NB XS spent ->
    exists pad1 pad2 pad3 pad4, rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) /\ 0 < ee /\ ee + ENTRY_SIZE <= aceil /\ ee + ENTRY_SIZE <= AAPP_HI /\ accessible m ee ENTRY_SIZE
      /\ 0 < en_suites E /\ en_suites E + 6 * en_nsuites E <= aceil /\ In (ps, en_suites E, sn) LB /\ en_suites E + sn <= AAPP_HI /\ accessible m (en_suites E) (6 * en_nsuites E)
      /\ 0 < en_pname E /\ en_pname E + zlength ns + 1 <= aceil /\ In (pn, en_pname E, zlength ns + 1) LB /\ en_pname E + zlength ns + 1 <= AAPP_HI /\ accessible m (en_pname E) (zlength ns + 1)
      /\ aapp (en_pname E) (zlength ns + 1) /\ en_pname E mod 16 = 0
      /\ 0 < A /\ A + VPM_SIZE <= aceil /\ AIMG_TOP <= A /\ aapp A VPM_SIZE /\ 0 <= en_exts E < 2^64.
  Proof.
    intros m s' M' LBN errv' V NB XS spent (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & _).
    cbv delta [spq VB] in *. acb.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XT).
    pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & _).
    rewrite SUO in O3, ES3. rewrite PNO in O1, ES1. cbn [ofield] in O1, O3. cbn [oshad] in ES1, ES3.
    destruct O1 as (PNP & _ & PNIN). destruct O3 as (SUP & _ & SUIN). destruct ES1 as (PT & PAD & _). destruct ES3 as (SUT & SAD & _).
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (intros b Hb; do 3 (apply in_or_app; right); right; exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ EIN)) as (K1 & _ & _ & _ & E5 & _). pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ SUIN)) as (_ & _ & _ & _ & S5 & _).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ PNIN)) as (_ & P2 & _ & _ & P5 & _ & P7).
    pose proof (ah_blocks H HH _ _ _ _ HP ltac:(do 3 (apply in_or_app; right); left; reflexivity)) as (V1 & _ & _ & V4 & V5 & _ & V7).
    cbn [blk_addr blk_size fst snd] in K1, E5, S5, P2, P5, P7, V1, V4, V5, V7.
    assert (XR : 0 <= en_exts E < 2^64).
    { revert XT. unfold EXTS. destruct (en_exts_o E) as [[K es]|]; intros XT; [| rewrite XT; lia].
      destruct XT as (XP0 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ KIN)) as (_ & _ & _ & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q5. unfold SK_SIZE in Q5. lia. }
    exists pad1, pad2, pad3, pad4. unfold ENTRY_SIZE, zlength in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - eapply addressable_accessible; [exact EAD| lia| lia| exact ETOP].
    - eapply addressable_accessible; [exact SAD| lia| lia| exact SUT].
    - eapply addressable_accessible; [exact PAD| lia| lia| exact PT].
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_stk : forall m m1 s' M' LBN errv' V NB XS spent W,
    fworld m s' M' LBN errv' V NB XS spent -> munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> ACONST m1 -> stk asegs m1 lo spq ->
    Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= spq) W ->
    fworld m1 s' M' LBN errv' V NB XS spent.
  Proof.
    intros m m1 s' M' LBN errv' V NB XS spent W FW MU WM MI1 AC1 ST1 FWW.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    unfold fworld. cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR.
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & SUP & SUH & SUIN & SUT & ACCS & PNP & PNH & PNIN & PT & ACCP & PAP & P16 & AP & AH & A4 & AAP & XRG).
    assert (HB : forall b, In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB) -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & B5 & _). exact B5. }
    assert (FWc : Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= bv_unsigned sp + -128) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (@nil (Z * Z)) a)) W).
    { eapply Forall_impl; [| exact FWW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. lia. }
    assert (XP : xpres H (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp + -128) [] m m1) by (eapply (xpres_of_munch H); [exact HH| exact HP| exact MU| exact WM| exact FWc]).
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (intros b Hb; do 3 (apply in_or_app; right); right; exact Hb).
    assert (XPL : xpres H LB (bv_unsigned sp + -128) [] m m1) by (eapply (xpres_weaken H); [exact XP| lia| exact SUBLB| auto]).
    assert (XPV : xpres H (NB ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp + -128) [] m m1) by (eapply (xpres_weaken H); [exact XP| lia| intros b Hb; do 2 (apply in_or_app; right); exact Hb| auto]).
    assert (DJ : forall a n, a + n <= aceil -> disjoint_from W a n).
    { intros a n Hn. clear - FWW Hn CEIL. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K.
      split; [lia| apply IH; eapply Forall_inv_tail; exact FWW]. }
    assert (CW : Forall (aclient_write_ok H (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) W).
    { eapply Forall_impl; [| exact FWW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. lia. }
    assert (WE : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W).
    { eapply Forall_impl; [| exact FWW]. cbn beta. intros [u v] [K1 K2]. right. cbn in *. unfold AHI_LO. clear - K1 CEIL ACEILB. lia. }
    pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ. pose proof (bytes_at_bound _ _ _ _ PN) as PNB. rewrite length_app in PNB. cbn [length] in PNB. unfold zlength in *.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. clear - FWW CEIL SPR ACEILB. unfold afcc_frame. cbn [cells_size csize Nat.add].
      induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact FWW].
    - rewrite TP in ERR |- *. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. rewrite unsigned_lit by (unfold ATP; lia). apply DJ. cbn. unfold ATP. clear - ACEILB. lia.
    - eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact CW].
    - eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM| exact CW].
    - eapply (LIBMID_xpres0 H); [exact LM| rewrite CXE; exact CX| exact XP| |].
      + intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUBLB; apply LIBSUB; exact Hb].
      + intros b Hb. apply in_or_app. left. exact Hb.
    - eapply (ENTRYobj_frame_law H LB LB m m1); [exact EO| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact XPL|].
      intros b Hb. pose proof (HB _ (SUBLB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))). clear - H0 CEIL LO8K. lia.
    - eapply (ENTRY_shad_frame_law H LB m m1); [exact ESH| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact XPL|].
      intros b Hb. pose proof (HB _ (SUBLB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))). clear - H0 CEIL LO8K. lia.
    - eapply rw_cells_transport; [exact SU| exact MU| exact WM|]. apply DJ. lia.
    - eapply bytes_at_transport; [exact PN| exact MU|]. apply DJ. rewrite length_app. cbn [length]. lia.
    - eapply (VPMobj_frame_law H _ _ m m1); [exact VO| intros b Hb; exact (VPMobj_owned_law _ _ _ _ VO _ Hb)| exact XPV|].
      intros b Hb. pose proof (HB _ ltac:(do 2 (apply in_or_app; right); exact (VPMobj_owned_law _ _ _ _ VO _ Hb))). clear - H0 CEIL LO8K. lia.
    - eapply (VPM_shad_frame_law H _ m m1); [exact VSH| intros b Hb; exact (VPMobj_owned_law _ _ _ _ VO _ Hb)| exact XPV|].
      intros b Hb. pose proof (HB _ ltac:(do 2 (apply in_or_app; right); exact (VPMobj_owned_law _ _ _ _ VO _ Hb))). clear - H0 CEIL LO8K. lia.
    - eapply stack0_transport; [exact SK0| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. unfold AHI_LO. clear - K1 CEIL ACEILB. lia.
    - eapply (RFS_via_xpres H HH); [exact RFS| exact XPL| apply Forall_nil].
    - eapply (xpres_trans H); [exact XP0|].
      assert (XPs : xpres H (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp) [] m m1).
      { eapply (xpres_of_munch H); [exact HH| exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. clear - K1 K2 CEIL SPR; lia. }
      eapply (xpres_weaken H); [exact XPs| apply Z.le_refl| exact SUBLB| intros q Hq; destruct Hq].
  Qed.

  (* [comment removed for export] *)
  Lemma ENTRYobj_frameX : forall L0 SP X m m',
    ENTRYobj L0 m ee E -> xpres H L0 SP X m m' -> (forall b, In b (blocks_ENTRY ee E) -> avoids X (blk_addr b) (blk_size b)) -> ENTRYobj L0 m' ee E.
  Proof.
    clear - SUO PNO. intros L0 SP X m m' EO XP AV. pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XT).
    unfold ENTRYobj. split; [| split; [exact EIN| split; [exact O1| split; [exact O2| split; [exact O3| split; [exact O4|]]]]]].
    - exists pad1, pad2, pad3, pad4. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
      eapply (xpres_rw_cells' H); [exact XP| exact HC| |].
      + right; right; left. exists (en_id E, ee, ENTRY_SIZE). split; [exact EIN|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia.
      + unfold entry_cells. cbn [cells_size csize Nat.add length]. exact (AV _ ltac:(left; reflexivity)).
    - revert XT. unfold EXTS. destruct (en_exts_o E) as [[K es]|] eqn:XO; intros XT; [| exact XT].
      destruct XT as (PP & SO & LEN & F2).
      assert (SUBX : forall b, In b (blocks_EXTS (en_exts E) (Some (K, es))) -> In b (blocks_ENTRY ee E)).
      { intros b Hb. unfold blocks_ENTRY. right. do 4 (apply in_or_app; right). rewrite XO. exact Hb. }
      rewrite blocks_EXTS_some in SUBX.
      split; [exact PP|]. split; [| split; [exact LEN|]].
      + eapply (SKobj_frameX H); [exact SO| exact XP| |].
        * exact (AV _ (SUBX _ ltac:(apply in_or_app; left; left; reflexivity))).
        * intros NC. exact (AV _ (SUBX _ ltac:(apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity))).
      + eapply (EXTs_frameX H); [exact F2| exact XP|]. intros b Hb. exact (AV _ (SUBX _ ltac:(apply in_or_app; right; exact Hb))).
  Qed.
  Lemma ENTRY_shad_frameX : forall L0 SP X m m',
    ENTRY_shad m ee E -> ENTRYobj LB m ee E -> xpres H L0 SP X m m' ->
    (forall b, In b (blocks_ENTRY ee E) -> In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> ENTRY_shad m' ee E.
  Proof.
    clear - SUO PNO. intros L0 SP X m m' ESH EO XP AV. pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & XSH). pose proof EO as (_ & _ & O1 & O2 & O3 & O4 & XT).
    assert (OSH : forall Pf o, ofield LB Pf o -> (forall b, In b (blocks_of Pf o) -> In b (blocks_ENTRY ee E)) -> oshad m Pf o -> oshad m' Pf o).
    { intros Pf o OFo INE OSo. eapply (oshad_xpresX H); [| exact OSo| exact XP]. destruct o as [[i1 n1]|]; [| exact I].
      pose proof (AV (i1, Pf, n1) (INE _ ltac:(left; reflexivity))) as (I1' & A1' & S1'). cbn [blk_addr blk_size fst snd] in A1', S1'. split; [exact I1'|]. split; [exact A1'| exact S1']. }
    pose proof (AV _ ltac:(left; reflexivity)) as (EIN' & AVE & SAVE). cbn [blk_addr blk_size fst snd] in AVE, SAVE.
    unfold ENTRY_shad. split; [exact ETOP|]. split; [eapply (addressable_xpres_blkX H); [exact EIN'| exact ETOP| exact EAD| exact XP| exact SAVE]|].
    split; [apply (OSH _ _ O1); [intros b Hb; right; apply in_or_app; left; exact Hb| exact ES1]|].
    split; [apply (OSH _ _ O2); [intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb| exact ES2]|].
    split; [apply (OSH _ _ O3); [intros b Hb; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES3]|].
    split; [apply (OSH _ _ O4); [intros b Hb; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES4]|].
    revert XSH XT. unfold EXTS_shad, EXTS. destruct (en_exts_o E) as [[K es]|] eqn:XO; intros XSH XT; [| exact I].
    destruct XSH as ((SKSH & T1 & T2) & F2SH). destruct XT as (PP & SO & LEN & F2).
    assert (SUBX : forall b, In b (blocks_SK (en_exts E) K ++ EBof K es) -> In b (blocks_ENTRY ee E)).
    { intros b Hb. unfold blocks_ENTRY. right. do 4 (apply in_or_app; right). rewrite XO, blocks_EXTS_some. exact Hb. }
    split.
    - split; [| split; [exact T1| exact T2]]. destruct SKSH as [SKH SKD]. split.
      + pose proof (AV _ (SUBX _ ltac:(apply in_or_app; left; left; reflexivity))) as (I1 & _ & S1). eapply (addressable_xpres_blkX H); [exact I1| exact T1| exact SKH| exact XP| exact S1].
      + intros NC. pose proof (AV _ (SUBX _ ltac:(apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity))) as (I1 & _ & S1).
        eapply (addressable_xpres_blkX H); [exact I1| exact (T2 NC)| exact (SKD NC)| exact XP| exact S1].
    - eapply (EXTs_shad_xpresX H); [exact F2SH| exact XP|]. intros b Hb. exact (AV _ (SUBX _ ltac:(apply in_or_app; right; exact Hb))).
  Qed.
  (* [comment removed for export] *)
  Lemma VPMobj0_frameX : forall L0 SP X m m', VPMobj L0 m A (vpm_empty p) -> xpres H L0 SP X m m' -> avoids X A VPM_SIZE -> VPMobj L0 m' A (vpm_empty p).
  Proof.
    clear. intros L0 SP X m m' (VC & VIN & HO) XP AV. split; [| split; [exact VIN| exact HO]].
    eapply (xpres_rw_cells' H); [exact XP| exact VC| |].
    - right; right; left. exists (p, A, VPM_SIZE). split; [exact VIN|]. unfold vpm_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold VPM_SIZE. lia.
    - unfold vpm_cells. cbn [cells_size csize Nat.add]. exact AV.
  Qed.
  Lemma VPM_shad0_frameX : forall L0 SP X m m', VPM_shad m A (vpm_empty p) -> In (p, A, VPM_SIZE) L0 -> xpres H L0 SP X m m' -> shavoids X A VPM_SIZE -> VPM_shad m' A (vpm_empty p).
  Proof.
    clear. intros L0 SP X m m' (TOP & AD & _) IN XP SAV. split; [exact TOP|]. split; [| exact I].
    eapply (addressable_xpres_blkX H); [exact IN| exact TOP| exact AD| exact XP| exact SAV].
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_es_apart : forall m s' M' LBN errv' V NB XS spent c,
    fworld m s' M' LBN errv' V NB XS spent -> mid_err M' = ErrReady c ->
    In (ec_es c) (LBN ++ LIB) /\ blk_size (ec_es c) = ERRST_SIZE /\ blk_addr (ec_es c) + ERRST_SIZE <= aceil
    /\ (forall b', In b' (VB :: blocks_ENTRY ee E) -> blk_id (ec_es c) <> blk_id b').
  Proof.
    intros m s' M' LBN errv' V NB XS spent c (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & _) ME.
    pose proof LM as (_ & _ & _ & EPm & _). rewrite CXE, CX, ME in EPm. cbn [ERRPH_mid ERRPH] in EPm. destruct EPm as [_ ECH].
    pose proof ECH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (I5' : In (ec_es c) (mid_errblocks M' ++ LBN ++ NB ++ VB :: LB)).
    { apply in_app_or in I5. apply in_or_app. right. destruct I5 as [K|K]; [apply in_or_app; left; exact K| do 2 (apply in_or_app; right); right; apply LIBSUB; exact K]. }
    pose proof (ah_blocks H HH _ _ _ _ HP I5') as (_ & _ & _ & _ & E5 & _). rewrite Z5 in E5.
    pose proof (ah_nodup H HH _ _ _ HP) as ND.
    split; [exact I5|]. split; [exact Z5|]. split; [exact E5|].
    intros b' Hb'. apply in_app_or in I5. destruct I5 as [K|K].
    - (* [comment removed for export] *)
      rewrite app_assoc in ND. apply (nodup_ids_app_ne _ _ _ _ ND); [apply in_or_app; right; exact K|].
      destruct Hb' as [<-|Hb']; apply in_or_app; right; [left; reflexivity| right; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb')].
    - destruct Hb' as [<-|Hb'].
      + (* [comment removed for export] *)
        destruct (nd_app _ _ ND) as [_ ND1]. destruct (nd_app _ _ ND1) as [_ ND2]. destruct (nd_app _ _ ND2) as [_ ND3].
        apply not_eq_sym. cbn [map] in ND3. inversion ND3 as [|i1 l1 NI1 _]; subst. intros EQ. apply NI1. rewrite EQ. apply in_map. apply LIBSUB. exact K.
      + exact (IDS _ _ K Hb').
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_xp_raise : forall m m' s' M' LBN errv' V NB XS spent XS' Lx,
    fworld m s' M' LBN errv' V NB XS spent -> (forall b, In b LB -> In b Lx) ->
    xpres H Lx spq (XS' ++ ERR_XE ++ errph_foot (mid_err M')) m m' ->
    xpres H LB (bv_unsigned sp) ((XS' ++ XS) ++ ERR_XE ++ errph_foot (mid_err M)) m m'.
  Proof.
    intros m m' s' M' LBN errv' V NB XS spent XS' Lx FW SUBL XP.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & _).
    cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR. pose proof STP as (_ & _ & SE & _).
    assert (GOAL : xpres H LB (bv_unsigned sp) (XS' ++ ERR_XE ++ errph_foot (mid_err M)) m m').
    { destruct (mid_err M) as [|c0] eqn:PH0.
      - (* [comment removed for export] *)
        cbn [errph_foot]. rewrite (app_nil_r ERR_XE).
        eapply (xpres_drop_windows H LB Lx (bv_unsigned sp) (XS' ++ ERR_XE) (errph_foot (mid_err M'))); [| exact SUBL|].
        + rewrite <- app_assoc. eapply (xpres_weaken H); [exact XP| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; exact Hq].
        + intros q Hq HC. destruct (mid_err M') as [|c] eqn:PH1; cbn [errph_foot rin_ivs fst snd] in Hq; [exact Hq|]. destruct Hq as [Hq|[]].
          destruct (fworld_es_apart _ _ _ _ _ _ _ _ _ c FW PH1) as (EIN & ESZ & EH & ENE).
          assert (ELBN : In (ec_es c) LBN).
          { clear - NW CXE CX PH0 PH1 EIN. destruct M as [f cph eph E0 v]. destruct M' as [f' cph' eph' E1 v']. cbn [mid_err mid_ctx] in *. subst eph eph'.
            unfold mid_newlib_ok in NW. cbn [mid_ctx mid_err] in NW. destruct NW as (LA & LE & P & _ & D). cbn [errph_delta] in D.
            destruct D as (_ & _ & HF). eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_or_app. right.
            eapply (proj1 (Forall_forall _ _) HF). unfold chain_blocks. do 3 right. left. reflexivity. }
          assert (EIN' : In (ec_es c) (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (apply in_or_app; right; apply in_or_app; left; exact ELBN).
          pose proof (ah_blocks H HH _ _ _ _ HP EIN') as (B1 & B2 & B3 & B4 & B5 & B6 & B7). rewrite ESZ in *.
          pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
          unfold aclient_addr, aimg_client, in_block, in_block_sh in HC. unfold AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO, ERRST_SIZE in *.
          destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]].
          * clear - HC B5 CEIL LO8K Hq. lia.
          * clear - HC B4 Hq. lia.
          * pose proof (ah_nodup H HH _ _ _ HP) as ND.
            assert (NE : blk_id (ec_es c) <> blk_id b).
            { destruct (nd_app _ _ ND) as [_ ND1]. apply (nodup_ids_app_ne _ _ _ _ ND1); [exact ELBN|]. apply in_or_app. right. right. exact Hb. }
            pose proof (ah_disj H HH _ _ _ _ _ HP EIN' ltac:(do 3 (apply in_or_app; right); right; exact Hb) NE) as DJ. clear - DJ Hq Hr ESZ. lia.
          * pose proof (ah_blocks H HH _ _ _ _ HP ltac:(do 3 (apply in_or_app; right); right; exact Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
            pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4).
            assert (SH0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; pose proof (Z.div_pos (blk_addr b) 8 ltac:(lia) ltac:(lia)); lia). rewrite ASHADOW_BASE_val in SH0.
            pose proof (aapp_not_shadowland _ _ B7) as NS. unfold ALOWSH_LO, AHI_LO in NS, S4. clear - Hq Hr S3 S4 SH0 NS. lia.
          * clear - HC B6 Hq. unfold AFS_SIZE in *. lia.
          * pose proof (aapp_not_shadowland _ _ B7) as NS. unfold ALOWSH_LO, AHI_LO in NS.
            unfold sh in HC. rewrite ?ASHADOW_BASE_val in HC. clear - HC Hq NS F1 F2 F3 ACEILB. unfold AFS_SIZE in *. Z.div_mod_to_equations. lia.
          * pose proof (aapp_not_shadowland _ _ B7) as NS. unfold ALOWSH_LO, AHI_LO in NS.
            unfold sh in HC. rewrite ?ASHADOW_BASE_val in HC. clear - HC Hq NS ACEILB. Z.div_mod_to_equations. lia.
      - (* [comment removed for export] *)
        rewrite (SE c0 eq_refl) in XP. eapply (xpres_weaken H); [exact XP| clear - SPR; lia| exact SUBL| intros q Hq; exact Hq]. }
    eapply (xpres_X_mono H); [exact GOAL|]. intros q Hq. apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq| right; exact Hq].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_stack_raise : forall M', mid_step M M' -> lo <= spq - SUITECHECK_STACK (mid_err M') /\ 0 <= RAISE_STACK (mid_err M').
  Proof.
    intros M' (_ & _ & SE & _). cbv delta [spq]. clear - LO SE. unfold FCC_STACK, FR_ech_final_config_checks, SUITECHECK_STACK, FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id in *.
    assert (RF : RAISE_STACK ErrFresh = 9328) by reflexivity.
    assert (RR : forall c, RAISE_STACK (ErrReady c) = 8336) by (intros c; reflexivity).
    pose proof (Z.le_max_r (Z.max ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) (Z.max (16 + 80 + 32 + RAISE_STACK (mid_err M)) FCC_ICPT_STACK)) as K2.
    pose proof (Z.le_max_l (16 + 80 + 32 + RAISE_STACK (mid_err M)) FCC_ICPT_STACK) as K3.
    destruct (mid_err M) as [|c0] eqn:E0; destruct (mid_err M') as [|c1] eqn:E1.
    - rewrite RF in *. lia.
    - rewrite RF, (RR c1) in *. lia.
    - exfalso. specialize (SE _ eq_refl). discriminate SE.
    - rewrite (RR c0), (RR c1) in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_raise_pre : forall m s' M' LBN errv' XS spent,
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent -> spent + RAISE_COST H (mid_err M') <= FCC_COST H M (en_nsuites E) ->
    let Lx := LBN ++ [] ++ VB :: LB in let ph := mid_err M' in let E0 := mid_E M' in
       as_RHEAP H s' (blocks_ERRST E0 ++ Lx) m
    /\ lb_bytes (blocks_ERRST E0 ++ Lx) + raise_bytes ph <= as_LIVE_MAX H
    /\ Z.of_nat (length (blocks_ERRST E0 ++ Lx)) + raise_cnt ph <= as_LIVE_CNT_MAX H
    /\ MEMFLAG m 1 /\ IMPL_mem m /\ GOT_mem m /\ arelro_lib m
    /\ ERRPH Lx m ph /\ ERRX m ph E0 /\ errph_below ph aceil /\ errph_shad m ph /\ CTXPH Lx m (CtxReady x) /\ HPKE_tabs m
    /\ (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat
    /\ as_chain H m (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)
    /\ (forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> spq + 16 <= fp')
    /\ errph_closed_ok H ph /\ RAISE_COST H ph <= as_AL H s'
    /\ lo <= spq - SUITECHECK_STACK ph /\ lo <= spq - RAISE_STACK ph /\ errph_sh0 ph m lo (Z_to_bv 64 spq)
    /\ (forall b, In b LB -> In b Lx) /\ (forall b, In b (LBN ++ LIB) -> In b Lx).
  Proof.
    intros m s' M' LBN errv' XS spent FW SPENT.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    cbv zeta. cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL).
    pose proof STP as (F1 & _ & SE & _). rewrite F1 in MF.
    assert (CX' : mid_ctx M' = CtxReady x) by (rewrite CXE; exact CX). rewrite CX' in CP, EPm. cbn [ERRPH_mid] in EPm.
    assert (SUBL : forall b, In b (LBN ++ LIB) -> In b (LBN ++ [] ++ (p, A, VPM_SIZE) :: LB)).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; apply LIBSUB; exact Hb]. }
    (* [comment removed for export] *)
    assert (LEN16 : length (es_slots (mid_E M')) = 16%nat).
    { destruct (mid_err M') as [|c0]; cbn [ERRX] in EX; [rewrite EX; reflexivity| exact (proj1 (proj1 EX))]. }
    pose proof (errst_fits_bounds _ LEN16 FIT) as [EC EB].
    pose proof (newlib_err_bounds _ _ _ _ CX STP NW) as (NB_ & NC_ & _).
    pose proof (fcc_stack_raise M' STP) as [LOS RS0].
    pose proof (ah_blocks H HH _ _ _ _ HP ltac:(do 3 (apply in_or_app; right); left; reflexivity)) as (_ & _ & _ & _ & E5 & _). cbn [blk_addr blk_size fst snd] in E5.
    repeat match goal with |- _ /\ _ => split end.
    - exact HP.
    - rewrite !lb_bytes_app, lb_bytes_cons in *. cbn [blk_size snd lb_bytes fold_right] in *. unfold raise_bytes. change (mid_errblocks M') with (blocks_ERRST (mid_E M')) in *.
      pose proof (errph_nonneg (mid_err M')) as [P0 _]. unfold FCC_BYTES, ERRSTR_BYTES, ERRDEBUG_BYTES, VPM_SIZE, SK_SIZE, ADD1HOST_BYTES in *.
      clear - BY EB NB_ P0 LBE0. lia.
    - rewrite !length_app in *. cbn [length] in *. rewrite !Nat2Z.inj_add, ?Nat2Z.inj_succ in *. unfold raise_cnt. change (mid_errblocks M') with (blocks_ERRST (mid_E M')) in *.
      pose proof (errph_nonneg (mid_err M')) as [_ P0]. clear - CN EC NC_ P0. unfold FCC_CNT, ERRSTR_CNT in *. lia.
    - exact MF.
    - exact IM.
    - exact G1.
    - exact RL.
    - eapply ERRPH_mono; [exact EPm| exact SUBL].
    - exact EX.
    - exact EBL.
    - exact ESHD.
    - exact (CTXPH_mono _ _ SUBL _ _ CP).
    - exact HT.
    - clear - LFB SE. unfold mid_LF in LFB. destruct (mid_err M) as [|c0]; destruct (mid_err M') as [|c1]; cbn [ERRPH_LF] in *; try lia. exfalso. specialize (SE _ eq_refl). discriminate SE.
    - (* [comment removed for export] *)
      assert (C0 : as_chain H m (bv_unsigned s0) CH).
      { eapply (chain_via_xpres_off H HH); [exact CHN0| exact XP0| exact CHS|].
        apply Forall_app. split; [eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RFS FXS)]; cbn beta; intros iv K; left; lia|].
        apply Forall_app. split.
        + unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
            A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
          cbn [app]. clear - ACEILB. repeat (apply Forall_cons; [left; cbn; lia|]). apply Forall_nil.
        + destruct (mid_err M) as [|c0] eqn:PH0; cbn [errph_foot]; [apply Forall_nil|].
          rewrite (SE c0 eq_refl) in *. destruct (fworld_es_apart _ _ _ _ _ _ _ _ _ c0 FW (SE c0 eq_refl)) as (_ & _ & EH & _).
          apply Forall_cons; [left; cbn [fst snd]; exact EH| apply Forall_nil]. }
      eapply (ah_chain_cons H HH); [exact C0| lia| lia| exact SPA| clear - CEIL LO8K; lia| lia|].
      unfold afcc_frame in FR.
      apply (proj1 (rw_cells_app asegs _ _ [C8 (wz (Z.land (ee + 32) 7 + 3)); C8 (Z_to_bv 64 A); C8 (wz ee); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FR.
      destruct FR as [_ FR2]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -128 + 112) by lia. rewrite !Z_to_bv_bv_unsigned. exact FR2.
    - intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia].
    - unfold mid_closed_ok in CLOSED. destruct (mid_err M) as [|c0] eqn:PH0; destruct (mid_err M') as [|c1] eqn:PH1; cbn [errph_closed_ok]; [exact CLOSED| exact I| exfalso; specialize (SE _ eq_refl); discriminate SE| exact I].
    - clear - AL0 AL1 HAL0 SPENT. lia.
    - exact LOS.
    - clear - LOS RS0. unfold SUITECHECK_STACK in LOS. unfold FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id in LOS. lia.
    - (* [comment removed for export] *)
      eapply (errph_sh0_sub _ m lo sp); [unfold errph_sh0; destruct (mid_err M'); [exact SK0| exact I]
        | rewrite unsigned_lit by (clear - SPR CEIL LO8K ACEILB; lia); clear - SPR CEIL LO8K ACEILB; lia
        | rewrite unsigned_lit by (clear - SPR CEIL LO8K ACEILB; lia); clear - SPA SPR; Z.div_mod_to_equations; lia].
    - intros b Hb. apply in_or_app. right. right. exact Hb.
    - exact SUBL.
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_after_raise : forall m m' s' s'' M' LBN errv' errv'' XS spent LE c A1 p1 n1 line A2 p2 n2 lib reason XS',
    let Lx := LBN ++ [] ++ VB :: LB in
    let E' := errst_raise (mid_E M') A1 p1 n1 line A2 p2 n2 lib reason in
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent ->
    mem_inv asegs m' -> ACONST m' -> stk asegs m' lo spq -> as_rauxv_ok H m' B ->
    as_RHEAP H s'' (blocks_ERRST E' ++ LE ++ Lx) m' ->
    MEMFLAG m' 1 -> rw_cells asegs m' (errno_addr tp) [C4 errv''] ->
    errph_delta (mid_err M') LE c -> raise_sizes A1 n1 A2 n2 ->
    ERRPH (LE ++ Lx) m' (ErrReady c) -> CTXPH (LE ++ Lx) m' (CtxReady x) -> ERRXR m' c E' -> lib_shad (chain_blocks c) m' ->
    Forall (fs_scratch H LF) XS' -> xpres H Lx spq (XS' ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M')) m m' -> as_RFS H LF m' ->
    as_AL H s'' >= as_AL H s' - RAISE_COST H (mid_err M') ->
    fworld m' s'' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M')) (LE ++ LBN) errv'' (vpm_empty p) [] (XS' ++ XS) (spent + RAISE_COST H (mid_err M')).
  Proof.
    intros m m' s' s'' M' LBN errv' errv'' XS spent LE c A1 p1 n1 line A2 p2 n2 lib reason XS' Lx E' FW
      MI' AC' ST' AUX' HP' MF' ERR' DL RSZ EP' CP' EXR' LSH' FXS' XP' RFS' AL'.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof LM as (_ & MF1 & _ & EPm1 & _ & _ & _ & FIT & _ & _ & _ & _ & _ & _ & _ & _ & EBL1). pose proof STP as (F1 & _ & SE & _). rewrite F1 in MF1.
    assert (CX' : mid_ctx M' = CtxReady x) by (rewrite CXE; exact CX). rewrite CX' in EPm1. cbn [ERRPH_mid] in EPm1.
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & SUP & SUH & SUIN & SUT & ACCS & PNP & PNH & PNIN & PT & ACCP & PAP & P16 & AP & AH & A4 & AAP & XRG).
    assert (SUBL : forall b, In b LB -> In b Lx) by (intros b Hb; subst Lx; apply in_or_app; right; right; exact Hb).
    assert (SUBLL : forall b, In b (LBN ++ LIB) -> In b Lx).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [subst Lx; apply in_or_app; left; exact Hb| apply SUBL; apply LIBSUB; exact Hb]. }
    set (L2 := blocks_ERRST E' ++ LE ++ Lx) in HP'.
    assert (SUBX2 : forall b, In b Lx -> In b L2) by (intros b Hb; subst L2; do 2 (apply in_or_app; right); exact Hb).
    (* [comment removed for export] *)
    assert (FIT' : errst_fits E') by (apply errst_fits_raise; [exact FIT| exact RSZ]).
    assert (LM' : LIBMID ((LE ++ LBN) ++ LIB) m' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M'))).
    { rewrite <- app_assoc. cbn [app] in HP.
      eapply (LIBMID_errcall H HH s' m s'' (LBN ++ LIB) Lx (bv_unsigned sp + -128) XS' LF LE m m' M' x c E');
        [subst Lx; cbn [app]; exact HP| exact SUBLL| exact LM| exact CX'| exact RFS| exact FXS'| exact XP'| subst L2; exact HP'| exact CP'| exact EP'| exact DL| exact EXR'| exact FIT'| exact LSH'| exact MF']. }
    (* [comment removed for export] *)
    assert (HESb : forall b', In b' ((p, A, VPM_SIZE) :: blocks_ENTRY ee E) ->
              forall c0, mid_err M' = ErrReady c0 -> In (ec_es c0) L2 /\ blk_id (ec_es c0) <> blk_id b' /\ blk_size (ec_es c0) = ERRST_SIZE).
    { intros b' Hb' c0 Hc0. destruct (fworld_es_apart _ _ _ _ _ _ _ _ _ c0 FW Hc0) as (EIN & ESZ & EH & ENE). split; [apply SUBX2, SUBLL; exact EIN|]. split; [exact (ENE _ Hb')| exact ESZ]. }
    assert (HES' : forall c0, mid_err M' = ErrReady c0 -> In (ec_es c0) L2 /\ blk_size (ec_es c0) = ERRST_SIZE).
    { intros c0 Hc0. destruct (fworld_es_apart _ _ _ _ _ _ _ _ _ c0 FW Hc0) as (EIN & ESZ & _). split; [apply SUBX2, SUBLL; exact EIN| exact ESZ]. }
    assert (OWNx : forall b', In b' ((p, A, VPM_SIZE) :: blocks_ENTRY ee E) -> In b' Lx).
    { intros b' [<-|Hb']; [subst Lx; apply in_or_app; right; left; reflexivity| apply SUBL; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb')]. }
    assert (AVX : forall b', In b' ((p, A, VPM_SIZE) :: blocks_ENTRY ee E) ->
              avoids (XR (mid_err M') XS') (blk_addr b') (blk_size b') /\ shavoids (XR (mid_err M') XS') (blk_addr b') (blk_size b')).
    { intros b' Hb'. eapply (XR_block H HHx (mid_err M') s'' L2 m' LF m' XS' b'); [exact HP'| exact RFS'| exact FXS'| apply SUBX2, OWNx; exact Hb'| exact (HESb _ Hb')]. }
    assert (SPQC : aceil <= bv_unsigned sp + -128) by (clear - CEIL LO8K; lia).
    assert (XPL : xpres H LB (bv_unsigned sp + -128) (XR (mid_err M') XS') m m') by (eapply (xpres_weaken H); [exact XP'| apply Z.le_refl| exact SUBL| intros q Hq; exact Hq]).
    assert (XPV : xpres H ([] ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp + -128) (XR (mid_err M') XS') m m').
    { eapply (xpres_weaken H); [exact XP'| apply Z.le_refl| intros b Hb; subst Lx; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]. }
    assert (AVF : avoids (XR (mid_err M') XS') (bv_unsigned sp + -128) 128) by (eapply (XR_stack H HHx (mid_err M') LF m' XS'); [exact RFS'| exact FXS'| exact SPQC| exact EBL1]).
    (* [comment removed for export] *)
    assert (STP2 : mid_step M' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M'))).
    { unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; rewrite CX' in Hb; exact Hb|].
      split; [| auto]. intros c0 Hc0. rewrite Hc0 in DL. cbn [errph_delta] in DL. destruct DL as [-> _]. reflexivity. }
    assert (NW2 : mid_newlib_ok M' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M')) LE).
    { unfold mid_newlib_ok. cbn [mid_ctx mid_err]. exists [], LE. split; [reflexivity|]. rewrite CX'. split; [reflexivity|].
      destruct (mid_err M') as [|c0] eqn:PH; [exact DL|]. cbn [errph_delta] in DL. destruct DL as [_ ->]. reflexivity. }
    assert (INS : In (ps, en_suites E, sn) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. do 2 (apply in_or_app; right). apply in_or_app. left. rewrite SUO. left. reflexivity. }
    assert (INP : In (pn, en_pname E, Z.of_nat (length ns) + 1) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. apply in_or_app. left. rewrite PNO. left. reflexivity. }
    pose proof (bytes_at_bound _ _ _ _ PN) as PNB. rewrite length_app in PNB. cbn [length] in PNB. unfold zlength in *.
    unfold fworld. cbv delta [spq VB]. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
      | |- rw_cells _ _ (bv_unsigned sp + -128) _ => eapply (xpres_rw_cells' H); [exact XP'| exact FR| left; lia| unfold afcc_frame; cbn [cells_size csize Nat.add]; exact AVF]
      | |- as_RHEAP _ _ _ _ => cbn [mid_errblocks mid_E]; rewrite <- (app_assoc LE LBN); subst L2 Lx; cbn [app] in HP'; exact HP'
      | |- LIBMID _ _ _ => exact LM'
      | |- mid_step _ _ => eapply mid_step_trans'; [exact STP| exact STP2]
      | |- mid_newlib_ok _ _ _ => eapply mid_newlib_ok_trans; [exact STP| exact NW| exact STP2| exact NW2]
      | |- mid_ctx _ = _ => cbn [mid_ctx]; symmetry; exact CX
      | |- mid_vdso _ = _ => cbn [mid_vdso]; exact VDE
      | |- ENTRYobj _ _ _ _ => eapply (ENTRYobj_frameX LB); [exact EO| exact XPL|]; intros b Hb; exact (proj1 (AVX _ ltac:(right; exact Hb)))
      | |- ENTRY_shad _ _ _ => eapply (ENTRY_shad_frameX LB); [exact ESH| exact EO| exact XPL|]; intros b Hb; split; [exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact (AVX _ ltac:(right; exact Hb))]
      | |- rw_cells _ _ (en_suites E) _ =>
          eapply (xpres_rw_cells' H); [exact XPL| exact SU| |];
          [ right; right; left; exists (ps, en_suites E, sn); split; [exact SUIN|]; cbn [blk_addr blk_size fst snd]; pose proof (suite_cells_size rows) as SSZ; unfold zlength in SSZ; lia
          | eapply avoids_sub; [exact (proj1 (AVX _ ltac:(right; exact INS)))| cbn; lia| cbn [blk_addr blk_size fst snd]; pose proof (suite_cells_size rows) as SSZ; unfold zlength in SSZ; lia] ]
      | |- bytes_at _ _ (en_pname E) _ =>
          eapply (xpres_bytes_at' H); [exact XPL| exact PN| |];
          [ right; right; left; exists (pn, en_pname E, Z.of_nat (length ns) + 1); split; [exact PNIN|]; cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia
          | eapply avoids_sub; [exact (proj1 (AVX _ ltac:(right; exact INP)))| cbn; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia] ]
      | |- VPMobj _ _ _ _ => eapply (VPMobj0_frameX ([] ++ (p, A, VPM_SIZE) :: LB)); [exact VO| exact XPV| exact (proj1 (AVX (p, A, VPM_SIZE) ltac:(left; reflexivity)))]
      | |- VPM_shad _ _ _ => eapply (VPM_shad0_frameX ([] ++ (p, A, VPM_SIZE) :: LB)); [exact VSH| cbn [app]; left; reflexivity| exact XPV| exact (proj2 (AVX (p, A, VPM_SIZE) ltac:(left; reflexivity)))]
      | |- stack0 _ _ _ => eapply (stack0_xpres H); [exact XP'| exact SK0|]; eapply (XR_stack0 H HHx (mid_err M') s'' L2 m' LF m' XS'); [exact HP'| exact RFS'| exact FXS'| exact HES']
      | |- Forall (fs_scratch _ _) _ => apply Forall_app; split; [exact FXS'| exact FXS]
      | |- xpres H LB _ _ m0 _ =>
          eapply (xpres_trans H); [eapply (xpres_X_mono H); [exact XP0| intros q Hq; apply rin_ivs_app in Hq; apply rin_ivs_app; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; right; exact Hq| right; exact Hq]]|];
          eapply fworld_xp_raise; [exact FW| exact SUBL|];
          pose proof XP' as XPq; rewrite (app_assoc XS' ERR_XE (memflag_foot ++ errph_foot (mid_err M'))) in XPq;
          pose proof (axpres_drop_memflag H Lx (bv_unsigned sp + -128) (XS' ++ ERR_XE) (errph_foot (mid_err M')) m m' MF1 MF' XPq) as XPd;
          rewrite <- app_assoc in XPd; exact XPd
      | |- 0 <= _ + RAISE_COST _ _ => pose proof (RCp_pos (mid_err M')); clear - AL0 H0; lia
      | |- as_AL _ _ + _ >= _ => clear - AL1 AL'; lia
      | |- ?G => idtac "FAR" G
      end.
    all: fail "FAR".
  Qed.

  (* [comment removed for export] *)
  Definition L1ms (i : Z) (rax s2x w a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
    MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) a0 a1 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB)
             (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
       F (Z_to_bv 64 AFC_HEAD) fc None m (seg_rom asegs).
  Definition L1exit (k : config) : Prop :=
    exists (w a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (aead j : Z) m s' M' LBN errv' XS spent,
      fworld m s' M' LBN errv' (vpm_empty p) [] XS spent /\ spent + RAISE_COST H (mid_err M') <= as_Cm H VPM_SIZE + RC + en_nsuites E * RCR H
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k) /\
      (  as_VIS H s' (cfg_ms k)
           = MS (mkR (Z_to_bv 64 AFC_RA1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 (en_nsuites E)) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 j) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                     (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
                F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs)
      \/ as_VIS H s' (cfg_ms k)
           = MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 j) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                     (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
                F (Z_to_bv 64 AFC_GOOD) fc None m (seg_rom asegs)).

  Lemma L1_loop : forall (k : nat) (i : Z) (rax s2x w a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) m s' M' LBN errv' XS spent msF mo',
    Z.of_nat k = en_nsuites E - i -> 0 <= i < en_nsuites E ->
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent -> spent + RAISE_COST H (mid_err M') <= as_Cm H VPM_SIZE + RC + i * RCR H ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF = L1ms i rax s2x w a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m ->
    as_SR H L1exit (mkCfg msF mo').
  Proof.
    induction k as [|k IH]; intros i rax s2x w a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m s' M' LBN errv' XS spent msF mo' HK IR FW SPI KREL MP VIS; [lia|].
    unfold L1ms in VIS. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof (aword_range w) as WR.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & SUP & SUH & SUIN & SUT & ACCS & PNP & PNH & PNIN & PT & ACCP & PAP & P16 & AP & AH & A4 & AAP & XRG).
    unfold ENTRY_SIZE in EEH, ETOP, ACCE. unfold VPM_SIZE in AH.
    (* [comment removed for export] *)
    destruct (nth_error rows (Z.to_nat i)) as [[[kem kdf] aead]|] eqn:NTH.
    2:{ exfalso. apply nth_error_None in NTH. unfold zlength in ROWS. lia. }
    pose proof (proj1 (Forall_forall _ _) ROK _ (nth_error_In _ _ NTH)) as RR. unfold row_ok in RR. cbn [fst snd] in RR. destruct RR as (KR & DR & AR).
    pose proof (suite_row_at _ _ _ _ _ _ _ SU NTH ltac:(lia)) as ROW.
    assert (ACCR : accessible m (en_suites E + 6 * i) 6) by (eapply accessible_sub; [exact ACCS| lia| lia| lia]).
    (* [comment removed for export] *)
    assert (SPR1 : spent + RAISE_COST H (mid_err M') <= FCC_COST H M (en_nsuites E)).
    { unfold FCC_COST. cbv delta [RC] in SPI |- *. pose proof RC_pos as RP. cbv delta [RC] in RP.
      pose proof (aCf_pos H HH (VPM_SIZE + ADD1HOST_BYTES) ltac:(unfold VPM_SIZE, ADD1HOST_BYTES, SK_SIZE; lia)) as CF0'.
      assert (AC0 : 0 <= ADD1HOST_COST H).
      { unfold ADD1HOST_COST. pose proof (aCm_pos H HH XBUF_SIZE ltac:(unfold XBUF_SIZE; lia)). pose proof (aCm_pos H HH 256 ltac:(lia)). pose proof (aCm_pos H HH SK_SIZE ltac:(unfold SK_SIZE; lia)).
        pose proof (aCm_pos H HH 32 ltac:(lia)). rewrite (aCf0 H HH). lia. }
      pose proof RCR_pos as RRP. clear - SPI RP CF0' AC0 IR RRP. nia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_seg3 with (V := A) (i := i) (kem := kem) (kdf := kdf) (aead := aead); try eassumption; try lia|].
    intros msF1 mo1 KREL1 MP1 (a1' & a2' & a3' & a4' & a5' & VIS1). pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    set (hi := bv_unsigned w / 2 ^ 48) in VIS1. assert (HR : 0 <= hi < 2^16) by (subst hi; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof LM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _).
    destruct (suite_fail kem kdf aead) as [[reason line]|] eqn:SF.
    - (* [comment removed for export] *)
      pose proof (fworld_raise_pre _ _ _ _ _ _ _ FW SPR1) as PRE. cbv zeta in PRE. cbv delta [spq VB] in PRE.
      destruct PRE as (HPx & BYx & CNx & MFx & IMx & GMx & RLx & EPx & EXx & EBx & ESx & CPx & HTx & LFx & CHx & CHSx & CLx & ALx & LOSx & LORx & SH0x & SUBx & SUBLx).
      eapply (ah_seq H HH).
      { eapply (asuitebad_spec H HH RAISE) with (lo := lo) (B := B) (LB := LBN ++ [] ++ (p, A, VPM_SIZE) :: LB) (s := s') (ph := mid_err M') (E := mid_E M') (x := x)
           (kem := kem) (kdf := kdf) (aead := aead) (hi := hi) (reason := reason) (line := line) (errv := errv') (LF := LF) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
          [exact VIS1| ..]; try reflexivity; try eassumption; try lia.
        all: lazymatch goal with
          | |- bv_unsigned (Z_to_bv 64 _) <= B => rewrite unsigned_lit by lia; clear - SPB SPR; lia
          | |- bv_unsigned (Z_to_bv 64 _) mod 16 = 0 => rewrite unsigned_lit by lia; clear - SPA SPR; replace (bv_unsigned sp + -128) with (bv_unsigned sp - 8 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
          | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST
          | |- _ <= _ - SUITECHECK_STACK _ => rewrite unsigned_lit by lia; exact LOSx
          | |- errph_sh0 _ _ _ _ => exact SH0x
          | |- _ mod 2 = 0 => unfold AFC_R2; rewrite unsigned_lit by lia; reflexivity
          | |- forall fp' ra', In _ _ -> _ => rewrite unsigned_lit by lia; exact CHSx
          | |- pf_ok _ _ _ _ => unfold AFC_R2; rewrite unsigned_lit by lia; eapply pf_ok_incl; [| apply (PF_suitebad_mstep _ _ STP)]; eapply pf_ok_call; [exact PF|]; unfold PF_fcc, R_fcc_suite_check; intros y Hy; apply in_app_iff; right; apply in_app_iff; left; exact Hy
          | |- ?G => idtac "SBPRE" G
          end.
        all: fail "SBPRE". }
      intros [ms2 mo2] PO. unfold hfind_fail_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LE & c & p1 & p2 & A1 & n1 & A2 & n2 & XS' &
                      VIS2 & MP2 & (KREL2 & MI2 & AC2 & ST2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & ERR2 & DL & RSZ & EP2 & CP2 & EXR2 & LSH2 & TB2 & FXS2 & XP2 & RFS2 & AL2).
      rewrite unsigned_lit in ST2, XP2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
      pose proof (fworld_after_raise _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW MI2 AC2 ST2 AUX2 HP2 MF2 ERR2 DL RSZ EP2 CP2 EXR2 LSH2 FXS2 XP2 RFS2 AL2) as FW2.
      set (M2 := mkMID 1 (CtxReady x) (ErrReady c) _ (mid_vdso M')) in FW2.
      destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW2) as (qad1 & qad2 & qad3 & qad4 & EC2 & _ & _ & _ & ACCE2 & _).
      destruct (Z.lt_ge_cases (i + 1) (en_nsuites E)) as [NX|NX].
      + eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_seg4n with (V := A) (i := i) (rv := 0); try eassumption; try lia|].
        intros msF3 mo3 KREL3 MP3 VIS3. eapply (IH (i + 1)); [lia| lia| exact FW2| subst M2; cbn [mid_err]; rewrite RC_ready; clear - SPI; lia| exact KREL3| exact (ah_mpres_trans H HH _ _ _ MPc2 MP3)| exact VIS3].
      + eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_seg4e with (V := A) (i := i) (rv := 0); try eassumption; try lia|].
        intros msF3 mo3 KREL3 MP3 VIS3. apply (ah_done H HH). unfold L1exit. cbn [cfg_ms cfg_model].
        do 15 eexists. exists aead, (i + 1), m2, s2', M2, (LE ++ LBN), errv2, (XS' ++ XS), (spent + RAISE_COST H (mid_err M')).
        split; [exact FW2|]. split; [replace (en_nsuites E) with (i + 1) by (clear - NX IR; lia); subst M2; cbn [mid_err]; rewrite RC_ready; clear - SPI; lia|]. split; [exact KREL3|]. split; [exact (ah_mpres_trans H HH _ _ _ MPc2 MP3)|]. left. exact VIS3.
    - (* [comment removed for export] *)
      pose proof (fcc_stack_raise M' STP) as [LOS RS0].
      eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1|..].
      { eapply asuiteok_spec with (lo := lo) (kem := kem) (kdf := kdf) (aead := aead) (hi := hi); try reflexivity; try eassumption; try lia.
        all: lazymatch goal with
          | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST
          | |- _ <= _ - SUITECHECK_OK_STACK => rewrite unsigned_lit by lia; unfold SUITECHECK_OK_STACK, SUITECHECK_STACK in *; clear - LOS RS0; lia
          | |- _ mod 2 = 0 => unfold AFC_R2; rewrite unsigned_lit by lia; reflexivity
          | |- ?G => idtac "SOPRE" G
          end.
        all: fail "SOPRE". }
      intros msF2 mo2 KREL2 MP2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2 & TB2).
      rewrite unsigned_lit in MU2, ST2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
      assert (FW2 : fworld m2 s' M' LBN errv' (vpm_empty p) [] XS spent).
      { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact AC2| exact ST2|]. constructor; [cbn; lia| constructor]. }
      destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW2) as (qad1 & qad2 & qad3 & qad4 & EC2 & _ & _ & _ & ACCE2 & _).
      destruct (Z.eq_dec aead 65535) as [A65|A65].
      + (* [comment removed for export] *)
        destruct (Z.lt_ge_cases (i + 1) (en_nsuites E)) as [NX|NX].
        * eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_seg4n with (V := A) (i := i) (rv := 1); try eassumption; try lia|].
          intros msF3 mo3 KREL3 MP3 VIS3. eapply (IH (i + 1)); [lia| lia| exact FW2| pose proof RCR_pos as RP; clear - SPI RP IR; lia| exact KREL3| exact (ah_mpres_trans H HH _ _ _ MPc2 MP3)| exact VIS3].
        * eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_seg4e with (V := A) (i := i) (rv := 1); try eassumption; try lia|].
          intros msF3 mo3 KREL3 MP3 VIS3. apply (ah_done H HH). unfold L1exit. cbn [cfg_ms cfg_model].
          do 15 eexists. exists aead, (i + 1), m2, s', M', LBN, errv', XS, spent.
          split; [exact FW2|]. split; [replace (en_nsuites E) with (i + 1) by (clear - NX IR; lia); pose proof RCR_pos as RP; clear - SPI RP; lia|]. split; [exact KREL3|]. split; [exact (ah_mpres_trans H HH _ _ _ MPc2 MP3)|]. left. exact VIS3.
      + eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_seg4g; [exact A65| lia| exact MI2]|].
        intros msF3 mo3 KREL3 MP3 VIS3. apply (ah_done H HH). unfold L1exit. cbn [cfg_ms cfg_model].
        do 15 eexists. exists aead, i, m2, s', M', LBN, errv', XS, spent.
        split; [exact FW2|]. split; [pose proof RCR_pos as RP; clear - SPI IR RP; nia|]. split; [exact KREL3|]. split; [exact (ah_mpres_trans H HH _ _ _ MPc2 MP3)|]. right. exact VIS3.
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_chain : forall m s' M' LBN errv' V NB XS spent,
    fworld m s' M' LBN errv' V NB XS spent -> as_chain H m (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH).
  Proof.
    intros m s' M' LBN errv' V NB XS spent FW.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R. pose proof STP as (_ & _ & SE & _).
    assert (C0 : as_chain H m (bv_unsigned s0) CH).
    { eapply (chain_via_xpres_off H HH); [exact CHN0| exact XP0| exact CHS|].
      apply Forall_app. split; [eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RFS FXS)]; cbn beta; intros iv K; left; lia|].
      apply Forall_app. split.
      + unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - ACEILB. repeat (apply Forall_cons; [left; cbn; lia|]). apply Forall_nil.
      + destruct (mid_err M) as [|c0] eqn:PH0; cbn [errph_foot]; [apply Forall_nil|].
        destruct (fworld_es_apart _ _ _ _ _ _ _ _ _ c0 FW (SE c0 eq_refl)) as (_ & _ & EH & _).
        apply Forall_cons; [left; cbn [fst snd]; exact EH| apply Forall_nil]. }
    eapply (ah_chain_cons H HH); [exact C0| lia| lia| exact SPA| clear - CEIL LO8K; lia| lia|].
    unfold afcc_frame in FR.
    apply (proj1 (rw_cells_app asegs _ _ [C8 (wz (Z.land (ee + 32) 7 + 3)); C8 (Z_to_bv 64 A); C8 (wz ee); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FR.
    destruct FR as [_ FR2]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -128 + 112) by lia. rewrite !Z_to_bv_bv_unsigned. exact FR2.
  Qed.

  (* [comment removed for export] *)
  Lemma hosts_cost_bytes : forall L m P xs,
    HOSTS L m P xs -> hosts_cost H xs <= as_Cf H (lb_bytes (blocks_HOSTS P xs)) /\ 0 <= lb_bytes (blocks_HOSTS P xs).
  Proof.
    intros L m P [[K bs]|] HO; cbn [hosts_cost blocks_HOSTS]; [| cbn; rewrite (aCf0 H HH); lia].
    destruct HO as (_ & SO & LEN & F2). pose proof SO as (_ & _ & _ & KNC & _ & _ & _ & KDAT).
    assert (EXS : ecost_sum xbufrep (xbuf_cost H) bs <= as_Cf H (lb_bytes (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs))))
                  /\ 0 <= lb_bytes (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs)))).
    { clear - F2 HH. induction F2 as [|q X ps' bs' HX FF2 IH]; [cbn; rewrite (aCf0 H HH); lia|].
      destruct IH as [IH1 IH2]. unfold ecost_sum in IH1 |- *. cbn [fold_right combine map concat fst snd]. rewrite lb_bytes_app.
      set (R := lb_bytes (concat (map (fun px : Z * xbufrep => blocks_XBUF (fst px) (snd px)) (combine ps' bs')))) in *.
      pose proof HX as (_ & _ & _ & XL & _). unfold blocks_XBUF. rewrite !lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right]. rewrite Z.add_0_r.
      unfold xbuf_cost in IH1 |- *. rewrite (Z.max_l (xb_len X + 1) 0) by lia.
      pose proof (aCf_super H HH XBUF_SIZE (xb_len X + 1) ltac:(unfold XBUF_SIZE; lia) ltac:(lia)) as S1.
      pose proof (aCf_super H HH (XBUF_SIZE + (xb_len X + 1)) R ltac:(unfold XBUF_SIZE; lia) IH2) as S2. unfold XBUF_SIZE in *. lia. }
    destruct EXS as [E1 E2]. rewrite lb_bytes_app.
    set (R := lb_bytes (concat (map (fun px : Z * xbufrep => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs)))) in *.
    pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & _ & _ & SK0).
    destruct KDAT as [[C0 _]|(C4 & _)].
    - rewrite C0. rewrite (SK0 C0). cbn [Z.mul Z.max]. rewrite (aCf0 H HH). pose proof (aCf_super H HH SK_SIZE R ltac:(unfold SK_SIZE; lia) E2). unfold SK_SIZE in *. lia.
    - rewrite (Z.max_l (8 * sk_cap K) 0) by lia.
      assert (SKE : lb_bytes (blocks_SK P K) = SK_SIZE + 8 * sk_cap K).
      { unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite !lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right]. lia. }
      rewrite SKE. pose proof (aCf_super H HH (8 * sk_cap K) SK_SIZE ltac:(lia) ltac:(unfold SK_SIZE; lia)) as S1.
      pose proof (aCf_super H HH (SK_SIZE + 8 * sk_cap K) R ltac:(unfold SK_SIZE; lia) E2) as S2. rewrite (Z.add_comm (8 * sk_cap K) SK_SIZE) in S1. unfold SK_SIZE in *. lia.
  Qed.
  Lemma vpm_cost_bound : forall L m V NB,
    VPMobj L m A V -> vp_id V = p -> Permutation (blocks_VPM A V) (VB :: NB) -> lb_bytes NB <= ADD1HOST_BYTES -> vpm_cost H V <= as_Cf H (VPM_SIZE + ADD1HOST_BYTES).
  Proof.
    intros L m V NB (_ & _ & HO) VID P NBB. unfold vpm_cost. pose proof (hosts_cost_bytes _ _ _ _ HO) as [C1 C2].
    unfold blocks_VPM in P. cbv delta [VB] in P. rewrite VID in P. pose proof (Permutation_cons_inv P) as P2. rewrite (lb_bytes_perm _ _ P2) in C1, C2.
    rewrite (aCf0 H HH). pose proof (aCf_super H HH VPM_SIZE (lb_bytes NB) ltac:(unfold VPM_SIZE; lia) C2) as S1.
    pose proof (aCf_mono H HH (VPM_SIZE + lb_bytes NB) (VPM_SIZE + ADD1HOST_BYTES) ltac:(unfold VPM_SIZE; lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_tail : forall m s' M' LBN errv' V NB XS spent rv msF mo' (t0 t1 t2 x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x6 x7 x8 x9 x10 x11 : word),
    fworld m s' M' LBN errv' V NB XS spent -> (rv = 0 \/ rv = 1) -> spent + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 x2 x3 (Z_to_bv 64 rv) (Z_to_bv 64 A) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' M' LBN errv' V NB XS spent rv msF mo' t0 t1 t2 x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x6 x7 x8 x9 x10 x11 FW RV SPT KREL MP VIS.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    pose proof (fworld_chain _ _ _ _ _ _ _ _ _ FW) as CHN. cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & _).
    set (Lcur := mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB) in *.
    pose proof (ah_nodup H HH _ _ _ HP) as ND.
    assert (SUBV : forall b, In b (NB ++ (p, A, VPM_SIZE) :: LB) -> In b Lcur) by (intros b Hb; subst Lcur; do 2 (apply in_or_app; right); exact Hb).
    (* [comment removed for export] *)
    assert (NDV : List.NoDup (map blk_id (blocks_VPM A V))).
    { eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact VP|].
      destruct (nd_app _ _ ND) as [_ ND1]. destruct (nd_app _ _ ND1) as [_ ND2].
      change (NB ++ (p, A, VPM_SIZE) :: LB) with (NB ++ [(p, A, VPM_SIZE)] ++ LB) in ND2. rewrite app_assoc, map_app in ND2.
      apply NoDup_app_remove_r in ND2. eapply Permutation_NoDup; [| exact ND2]. rewrite map_app. cbn [map app]. apply Permutation_sym. apply Permutation_cons_append. }
    assert (PL : Permutation Lcur ((NB ++ [(p, A, VPM_SIZE)]) ++ (mid_errblocks M' ++ LBN ++ LB))).
    { subst Lcur. transitivity (((mid_errblocks M' ++ LBN) ++ (NB ++ [(p, A, VPM_SIZE)])) ++ LB).
      - rewrite <- !app_assoc. cbn [app]. apply Permutation_refl.
      - transitivity (((NB ++ [(p, A, VPM_SIZE)]) ++ (mid_errblocks M' ++ LBN)) ++ LB).
        + apply Permutation_app_tail. apply Permutation_app_comm.
        + rewrite <- !app_assoc. apply Permutation_refl. }
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) ND) as NDP.
    assert (NOTV : forall b, In b (mid_errblocks M' ++ LBN ++ LB) -> ~ In b (blocks_VPM A V)).
    { intros b Hb K. pose proof (Permutation_in _ VP K) as K'.
      assert (K2 : In b (NB ++ [(p, A, VPM_SIZE)])) by (destruct K' as [<-|K']; apply in_or_app; [right; left; reflexivity| left; exact K']).
      exact (nodup_ids_app_ne _ _ _ _ NDP K2 Hb eq_refl). }
    assert (LEN16 : length (es_slots (mid_E M')) = 16%nat).
    { destruct (mid_err M') as [|c0]; cbn [ERRX] in EX; [rewrite EX; reflexivity| exact (proj1 (proj1 EX))]. }
    pose proof (errst_fits_bounds _ LEN16 FIT) as [EC EB].
    pose proof (vpm_cost_bound _ _ _ _ VO VID VP NB2) as VCB.
    (* [comment removed for export] *)
    pose proof (avpmfree_spec H HH) as VF. unfold vpmfree_stmt, efree_stmt_at in VF.
    eapply (ah_seq H HH).
    { eapply VF with (lo := lo) (B := B) (LB := Lcur) (s := s') (p := A) (x := V) (errv := errv') (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact NDV| exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact IM| exact G1| exact G3| exact TP| exact AC| exact VSH| exact CHN].
      all: lazymatch goal with
           | |- VPMobj _ _ _ _ => eapply (VPMobj_frame_law H _ Lcur m m A V (bv_unsigned sp + -128)); [exact VO| intros b Hb; apply SUBV; exact (VPMobj_owned_law _ _ _ _ VO _ Hb)| apply (xpres_refl H)| intros b Hb; pose proof (ah_blocks H HH _ _ _ _ HP (SUBV _ (VPMobj_owned_law _ _ _ _ VO _ Hb))) as (_ & _ & _ & _ & B5 & _); clear - B5 CEIL LO8K; lia]
           | |- rw_cells _ _ _ [C4 _] => exact ERR
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -128) with (bv_unsigned sp - 8 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ <= _ - VPMFREE_STACK => clear - LO; unfold FCC_STACK, FR_ech_final_config_checks in LO; pose proof (Z.le_max_r VPMNEW_STACK VPMFREE_STACK); pose proof (Z.le_max_r ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK));
                                          pose proof (Z.le_max_l (Z.max ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) (Z.max (SUITECHECK_STACK (mid_err M)) FCC_ICPT_STACK)); lia
           | |- _ mod 2 = 0 => unfold AFC_R4; rewrite unsigned_lit by lia; reflexivity
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => unfold AFC_R4; eapply pf_ok_call; [exact PF|]; unfold PF_fcc, R_fcc_X509_VERIFY_PARAM_free; intros y Hy; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hy
           | |- vpm_cost _ _ <= as_AL _ _ => pose proof (SPENT_le_COST M' (en_nsuites E) STP) as SLC; clear - SPT HAL0 AL0 AL1 VCB SLC; lia
           | |- ?G => idtac "VFPRE" G
           end.
      all: fail "VFPRE". }
    clear VF. intros [ms2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m2 & s2' & LB2 &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & PERM2 & HP2 & XP2 & IM2 & GM2 & GX2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST2, XP2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MP MP2) as MPc2.
    assert (KEEP : forall b, In b (mid_errblocks M' ++ LBN ++ LB) -> In b LB2).
    { intros b Hb. eapply perm_in_rest; [exact PERM2| | exact (NOTV _ Hb)]. subst Lcur.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. do 2 (apply in_or_app; right). right. exact Hb. }
    assert (PL2 : Permutation LB2 (mid_errblocks M' ++ LBN ++ LB)).
    { apply (Permutation_app_inv_l (blocks_VPM A V)). transitivity Lcur; [exact PERM2|].
      transitivity ((NB ++ [(p, A, VPM_SIZE)]) ++ (mid_errblocks M' ++ LBN ++ LB)); [exact PL|]. apply Permutation_app_tail.
      transitivity ((p, A, VPM_SIZE) :: NB); [apply Permutation_sym; apply Permutation_cons_append| apply Permutation_sym; exact VP]. }
    assert (HP2' : as_RHEAP H s2' (mid_errblocks M' ++ LBN ++ LB) m2) by (eapply (HHx_rheap_perm H HHx); [exact HP2| exact PL2]).
    assert (SUBL2 : forall b, In b LB -> In b LB2) by (intros b Hb; apply KEEP; do 2 (apply in_or_app; right); exact Hb).
    assert (XPL : xpres H LB (bv_unsigned sp + -128) [] m m2) by (eapply (xpres_weaken H); [exact XP2| lia| exact SUBL2| auto]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 A) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact FR| left; cbn; lia| apply Forall_nil]. }
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP (SUBV _ ltac:(apply in_or_app; right; right; exact Hb))) as (_ & _ & _ & _ & B5 & _). exact B5. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_segE with (lo := lo); [exact FR2| exact ST2| exact CEIL| clear - LO8K; lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 [VIS3 ST3]. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    apply (ah_done H HH). unfold fcc_post. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, m2, errv', s2', rv, M', LBN, XS.
    split; [exact VIS3|]. split; [exact RV|]. split; [exact KREL3|]. split; [exact MPc3|].
    split; [exact MI2|]. split; [exact AC2|]. split; [exact ST3|]. split; [eapply (stack0_xpres H); [exact XPL| exact SK0| apply Forall_nil]|].
    split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HP2'|].
    split; [eapply (LIBMID_xpres0 H); [exact LM| rewrite CXE; exact CX| exact XP2| intros b Hb; apply KEEP; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| do 2 (apply in_or_app; right); apply LIBSUB; exact Hb]| intros b Hb; apply KEEP; apply in_or_app; left; exact Hb]|].
    split; [exact STP|]. split; [exact NW|]. split; [exact CXE|]. split; [exact VDE|].
    split; [exact EC|]. split; [exact EB|].
    assert (XPN : xpres H (LBN ++ LB) (bv_unsigned sp + -128) [] m m2).
    { eapply (xpres_weaken H); [exact XP2| lia| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| auto]. }
    split; [eapply (ENTRYobj_frame_law H LB (LBN ++ LB) m m2); [exact EO| intros b Hb; apply in_or_app; right; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact XPN| intros b Hb; pose proof (HB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb)); clear - H0 CEIL LO8K; lia]|].
    split; [eapply (ENTRY_shad_frame_law H LB m m2); [exact ESH| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact XPL| intros b Hb; pose proof (HB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb)); clear - H0 CEIL LO8K; lia]|].
    split; [exact FXS|]. split; [eapply (RFS_via_xpres H HH); [exact RFS| exact XPL| apply Forall_nil]|]. split; [eapply (ah_thr H HH); exact HP2|].
    split.
    - eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [exact XP2| clear - SPR; lia| exact SUBL2| intros q Hq; destruct Hq].
    - clear - SPT AL0 AL1 AL2 VCB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_raise_fail : forall (raA line : Z) m s' M' LBN errv' XS spent msF mo'
                                (t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word),
    (raA = AFC_RA1 /\ line = 275) \/ (raA = AFC_RA4 /\ line = 284) ->
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent -> spent + RAISE_COST H (mid_err M') + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_COST H M (en_nsuites E) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 raA) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros raA line m s' M' LBN errv' XS spent msF mo' t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 WHICH FW SPT KREL MP VIS.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    assert (SPR1 : spent + RAISE_COST H (mid_err M') <= FCC_COST H M (en_nsuites E)).
    { pose proof (aCf_pos H HH (VPM_SIZE + ADD1HOST_BYTES) ltac:(unfold VPM_SIZE, ADD1HOST_BYTES, SK_SIZE; lia)). clear - SPT H0. lia. }
    pose proof (fworld_raise_pre _ _ _ _ _ _ _ FW SPR1) as PRE. cbv zeta in PRE. cbv delta [spq VB] in PRE.
    destruct PRE as (HPx & BYx & CNx & MFx & IMx & GMx & RLx & EPx & EXx & EBx & ESx & CPx & HTx & LFx & CHx & CHSx & CLx & ALx & LOSx & LORx & SH0x & SUBx & SUBLx).
    cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR.
    assert (RAR : 0 <= raA < 2^64 /\ raA mod 2 = 0) by (destruct WHICH as [[-> _]|[-> _]]; unfold AFC_RA1, AFC_RA4; (split; [lia| reflexivity])).
    assert (LNR : 0 <= line < 2^31) by (destruct WHICH as [[_ ->]|[_ ->]]; lia).
    eapply RAISE with (lo := lo) (B := B) (LB := LBN ++ [] ++ (p, A, VPM_SIZE) :: LB) (s := s') (ph := mid_err M') (E := mid_E M') (x := x) (errv := errv') (LF := LF)
      (CH := (bv_unsigned sp, bv_unsigned ra) :: CH)
      (file := AA_ECHS_FILE) (fs := S_AFC_FILE) (fsl := K_AFC_FILE) (func := AA_FCC_FUNC) (gs := S_AFC_FUNC) (gsl := K_AFC_FUNC)
      (line := line) (lib := ERR_LIB_SSL) (reason := R_PASSED_INVALID_ARGUMENT) (ra2 := AFC_RA2) (ra3 := AFC_RA3);
      [exact VIS| ..]; try (rewrite unsigned_lit by lia).
    all: try exact LNR; try exact (proj1 RAR); try exact (proj2 RAR).
    all: lazymatch goal with
         | |- as_RHEAP _ _ _ _ => exact HPx
         | |- as_AKREL _ _ _ => exact KREL
         | |- lb_bytes _ + _ <= _ => exact BYx
         | |- Z.of_nat (length _) + _ <= _ => exact CNx
         | |- as_rauxv_ok _ _ _ => exact AUX
         | |- _ <= B => clear - SPB SPR; lia
         | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -128) with (bv_unsigned sp - 8 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
         | |- stk _ _ _ _ => exact ST
         | |- aceil <= lo => exact CEIL
         | |- _ <= _ - RAISE_STACK _ => exact LORx
         | |- errph_sh0 _ _ _ _ => exact SH0x
         | |- rw_cells _ _ (errno_addr _) _ => exact ERR
         | |- mem_inv _ _ => exact MI
         | |- tp = _ => exact TP
         | |- ACONST _ => exact AC
         | |- MEMFLAG _ _ => exact MFx
         | |- IMPL_mem _ => exact IMx
         | |- GOT_mem _ => exact GMx
         | |- arelro_lib _ => exact RLx
         | |- ERRPH _ _ _ => exact EPx
         | |- ERRX _ _ _ => exact EXx
         | |- errph_below _ _ => exact EBx
         | |- errph_shad _ _ => exact ESx
         | |- CTXPH _ _ _ => exact CPx
         | |- as_RFS _ _ _ => exact RFS
         | |- (_ <= AFS_MAXLIVE)%nat => exact LFx
         | |- as_chain _ _ _ _ => exact CHx
         | |- forall fp' ra', In _ _ -> _ => exact CHSx
         | |- pf_ok _ (PF_errnew _) _ _ =>
             eapply pf_ok_incl; [| apply (PF_errnew_mstep _ _ STP)]; eapply pf_ok_call; [exact PF|]; unfold PF_fcc, pf_raise, R_fcc_ERR_new, R_fcc_ERR_new_3; intros y Hy;
             destruct WHICH as [[-> _]|[-> _]]; unfold AFC_RA1, AFC_RA4;
             [ do 4 (apply in_app_iff; right); apply in_app_iff; left; apply in_app_iff; left; exact Hy
             | do 6 (apply in_app_iff; right); apply in_app_iff; left; exact Hy ]
         | |- pf_ok _ PF_errdebug _ _ =>
             eapply pf_ok_call; [exact PF|]; unfold PF_fcc, pf_raise, R_fcc_ERR_set_debug, AFC_RA2; intros y Hy;
             do 4 (apply in_app_iff; right); apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hy
         | |- pf_ok _ PF_errseterr _ _ =>
             eapply pf_ok_call; [exact PF|]; unfold PF_fcc, pf_raise, R_fcc_ERR_set_error, AFC_RA3; intros y Hy;
             do 4 (apply in_app_iff; right); apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; right; exact Hy
         | |- errph_closed_ok _ _ => exact CLx
         | |- RAISE_COST _ _ <= _ => exact ALx
         | |- AROSTR AA_ECHS_FILE _ _ => exact AR_AFC_FILE
         | |- AROSTR AA_FCC_FUNC _ _ => exact AR_AFC_FUNC
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_AFC_FILE) < 24 => rewrite S_AFC_FILE_len; lia
         | |- Z.of_nat (length S_AFC_FUNC) < 32 => rewrite S_AFC_FUNC_len; lia
         | |- 0 < AA_ECHS_FILE => unfold AA_ECHS_FILE; lia
         | |- 0 < AA_FCC_FUNC => unfold AA_FCC_FUNC; lia
         | |- 0 < ERR_LIB_SSL < 256 => unfold ERR_LIB_SSL; lia
         | |- ERR_LIB_SSL <> 2 => unfold ERR_LIB_SSL; lia
         | |- 0 < R_PASSED_INVALID_ARGUMENT < _ => unfold R_PASSED_INVALID_ARGUMENT; lia
         | |- 0 <= AFC_RA2 < _ => unfold AFC_RA2; lia
         | |- AFC_RA2 mod 2 = 0 => reflexivity
         | |- 0 <= AFC_RA3 < _ => unfold AFC_RA3; lia
         | |- AFC_RA3 mod 2 = 0 => reflexivity
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; destruct WHICH as [[-> ->]|[-> ->]]; [eapply afcc_glue275| eapply afcc_glue284]; assumption
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply afcc_glue2; assumption
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo'' s'' errv'' LE c0 p1 p2 A1 A2 en1 en2 E'
           VIS' KREL' MP' MI' AC' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EXR' LSH' XS' FXS' XP' RFS' AL'.
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in XP' by lia.
    pose proof (ah_mpres_trans H HH _ _ _ MP MP') as MPc.
    pose proof (fworld_after_raise _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW MI' AC' ST' AUX' HP' MF' ERR' DL RSZ EP' CP' EXR' LSH' FXS' XP' RFS' AL') as FW2.
    pose proof FW2 as (_ & _ & _ & FR2 & _). cbv delta [spq] in FR2.
    pose proof VBR as (A1' & _ & _ & _ & A5' & _).
    eapply (ahh_evt_then H HH); [exact KREL'| exact VIS'| eapply afcc_segRA3; [exact FR2| clear - LO8K CEIL ACEILB; lia| clear - A1' A5' ACEILB; unfold VPM_SIZE in *; lia| exact MI']|].
    intros msF3 mo3 KREL3 MP3 VIS3. eapply fcc_tail; [exact FW2| left; reflexivity| unfold FCC_SPENT; cbn [mid_err]; rewrite RCd_ready; unfold FCC_COST in SPT; clear - SPT; lia| exact KREL3| exact (ah_mpres_trans H HH _ _ _ MPc MP3)| exact VIS3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition NAMEexit (k : config) : Prop :=
    exists (rax x1 x2 a0 a1 a2 a3 a4 a5 a6 a7 x3 x4 x5 x7 x8 x9 x10 x11 t0 t1 t2 t3 t4 t5 t6 : word) m s' M' LBN errv' XS spent,
      fworld m s' M' LBN errv' (vpm_empty p) [] XS spent /\ spent + RAISE_COST H (mid_err M') <= as_Cm H VPM_SIZE + RC + en_nsuites E * RCR H
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k) /\
      (  as_VIS H s' (cfg_ms k) = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 (Z_to_bv 64 ASHB) x7 x8 x9 x10 x11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 AFC_NAME) fc None m (seg_rom asegs)
      \/ as_VIS H s' (cfg_ms k) = MS (mkR (Z_to_bv 64 AFC_RA4) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 (Z_to_bv 64 ASHB) x7 x8 x9 x10 x11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma fworld_exts : forall m s' M' LBN errv' V NB XS spent,
    fworld m s' M' LBN errv' V NB XS spent -> 0 < en_exts E ->
    exists K xs, en_exts_o E = Some (K, xs) /\ SKobj LB m (en_exts E) K /\ length xs = length (sk_elems K)
      /\ Forall2 (fun q X => EXTobj LB m q X) (sk_elems K) xs /\ Forall2 (fun q X => EXT_shad m q X) (sk_elems K) xs
      /\ SK_below (en_exts E) K lo /\ SK_shad m (en_exts E) K /\ SK_ranges H (en_exts E) K /\ 0 <= sk_num K < 2^31.
  Proof.
    intros m s' M' LBN errv' V NB XS spent (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & _) XP0.
    cbv delta [spq VB] in *. acb. pose proof EO as (_ & _ & _ & _ & _ & _ & XT). pose proof ESH as (_ & _ & _ & _ & _ & _ & XSH).
    revert XT XSH. unfold EXTS, EXTS_shad. destruct (en_exts_o E) as [[K xs]|]; intros XT XSH; [| lia].
    destruct XT as (_ & SO & LEN & F2). destruct XSH as ((SKSH & _ & _) & F2SH). exists K, xs. split; [reflexivity|]. split; [exact SO|]. split; [exact LEN|]. split; [exact F2|]. split; [exact F2SH|].
    pose proof SO as (_ & _ & KIN & NC & CAP & _ & _ & DAT).
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (intros b Hb; do 3 (apply in_or_app; right); right; exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ KIN)) as KB. pose proof KB as (_ & _ & _ & _ & K5 & _). cbn [blk_addr blk_size fst snd] in K5.
    split; [| split; [exact SKSH| split; [| unfold sk_num, zlength in *; lia]]].
    - unfold SK_below. split; [unfold SK_SIZE in *; lia|]. destruct DAT as [[D0 _]|(D1 & D2 & D3 & DIN & _)]; [left; exact D0| right].
      pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ DIN)) as (_ & _ & _ & _ & D5 & _). cbn [blk_addr blk_size fst snd] in D5. lia.
    - split; [exact KB|]. intros NCZ. destruct DAT as [[D0 _]|(D1 & D2 & D3 & DIN & _)]; [exfalso; exact (NCZ D0)|]. exact (ah_blocks H HH _ _ _ _ HP (SUBLB _ DIN)).
  Qed.

  Lemma L2_loop : forall (k : nat) (j : Z) K xs (rax xe a0 a1 a2 a3 a4 a5 a6 a7 x7 x8 x9 x10 x11 t0 t1 t2 t3 t4 t5 t6 : word) m s' M' LBN errv' XS spent msF mo',
    en_exts_o E = Some (K, xs) -> Z.of_nat k = sk_num K - j -> 0 <= j < sk_num K -> 0 < en_exts E ->
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent -> spent + RAISE_COST H (mid_err M') <= as_Cm H VPM_SIZE + RC + en_nsuites E * RCR H ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) a0 a1 a2 a3 a4 a5 a6 a7
                xe (Z_to_bv 64 (ee + 56)) (Z_to_bv 64 (sk_num K)) (Z_to_bv 64 j) (Z_to_bv 64 ASHB) x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFC_XHEAD) fc None m (seg_rom asegs) ->
    as_SR H NAMEexit (mkCfg msF mo').
  Proof.
    induction k as [|k IH]; intros j K xs rax xe a0 a1 a2 a3 a4 a5 a6 a7 x7 x8 x9 x10 x11 t0 t1 t2 t3 t4 t5 t6 m s' M' LBN errv' XS spent msF mo' XO HK JR XP FW SPI KREL MP VIS; [lia|].
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AP & AH & A4 & AAP & XRG).
    destruct (fworld_exts _ _ _ _ _ _ _ _ _ FW XP) as (K' & xs' & XO' & SO & LEN & F2 & F2SH & SKB & SKSH & SKR & NUMR). rewrite XO in XO'. injection XO' as <- <-.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segXH; [exact EC| lia| exact ETOP| exact XRG| exact ACCE| exact MI]|].
    intros msF1 mo1 KREL1 MP1 VIS1. pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    (* [comment removed for export] *)
    destruct (nth_error (sk_elems K) (Z.to_nat j)) as [q|] eqn:NTH.
    2:{ exfalso. apply nth_error_None in NTH. unfold sk_num, zlength in JR. lia. }
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1|..].
    { eapply askvalue_spec with (lo := lo) (i := j) (K := K); try reflexivity; try eassumption; rewrite ?unsigned_lit by lia; [exact ST| clear - LO8K CEIL; lia]. }
    intros msF2 mo2 KREL2 MP2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2).
    rewrite unsigned_lit in MU2, ST2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    assert (FW2 : fworld m2 s' M' LBN errv' (vpm_empty p) [] XS spent).
    { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact AC2| exact ST2|]. constructor; [cbn; lia| constructor]. }
    (* [comment removed for export] *)
    destruct (fworld_exts _ _ _ _ _ _ _ _ _ FW2 XP) as (K' & xs' & XO' & SO2 & _ & F22 & F22SH & _). rewrite XO in XO'. injection XO' as <- <-.
    destruct (nth_error xs (Z.to_nat j)) as [X|] eqn:NTHX.
    2:{ exfalso. apply nth_error_None in NTHX. pose proof (nth_error_lt _ _ _ NTH). lia. }
    pose proof (Forall2_nth_error _ _ _ _ _ _ F22 NTH NTHX) as XJ. pose proof (Forall2_nth_error _ _ _ _ _ _ F22SH NTH NTHX) as (XTOP & XAD & _).
    pose proof XJ as ((pad & PL & XC) & XIN & _).
    pose proof FW2 as (_ & _ & _ & _ & _ & _ & HP2 & _).
    pose proof (ah_blocks H HH _ _ _ _ HP2 ltac:(do 3 (apply in_or_app; right); right; exact XIN)) as (K1 & QAL16 & _ & _ & K5 & _). cbn [blk_addr blk_size fst snd] in K1, QAL16, K5. unfold EXT_SIZE in K5.
    assert (QAL : q mod 8 = 0) by (clear - QAL16; Z.div_mod_to_equations; lia).
    set (X' := mkEXT (ex_type X mod 65536) (ex_len X) (ex_val X) (ex_val_o X) (ex_id X)).
    assert (XC' : rw_cells asegs m2 q (ext_cells X' pad)) by (unfold ext_cells; cbn [ex_type ex_len ex_val X']; eapply rw_cells_C2_le2; [apply le2_wz_mod| exact XC]).
    assert (TR : 0 <= ex_type X' < 2^16) by (cbn [ex_type X']; pose proof (Z.mod_pos_bound (ex_type X) 65536); lia).
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply (afcc_segX3) with (X := X') (num := sk_num K); [exact XC'| exact TR| lia| exact XTOP| eapply addressable_accessible; [exact XAD| lia| lia| exact XTOP]| exact JR| lia| lia| exact QAL| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (a0' & a1' & a2' & [[_ VIS3]|[[_ [NX VIS3]]|[_ [NX VIS3]]]]); pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    - apply (ah_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. exists (Z_to_bv 64 AFC_RA4). do 25 eexists. exists m2, s', M', LBN, errv', XS, spent.
      split; [exact FW2|]. split; [exact SPI|]. split; [exact KREL3|]. split; [exact MPc3|]. right. exact VIS3.
    - eapply (IH (j + 1)); [exact XO| lia| lia| exact XP| exact FW2| exact SPI| exact KREL3| exact MPc3| exact VIS3].
    - apply (ah_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. do 26 eexists. exists m2, s', M', LBN, errv', XS, spent.
      split; [exact FW2|]. split; [exact SPI|]. split; [exact KREL3|]. split; [exact MPc3|]. left. exact VIS3.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_good : forall (w a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (aead jj : Z) m s' M' LBN errv' XS spent msF mo',
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent -> spent + RAISE_COST H (mid_err M') <= as_Cm H VPM_SIZE + RC + en_nsuites E * RCR H ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 jj) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
           F (Z_to_bv 64 AFC_GOOD) fc None m (seg_rom asegs) ->
    as_SR H NAMEexit (mkCfg msF mo').
  Proof.
    intros w a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 aead jj m s' M' LBN errv' XS spent msF mo' FW SPI KREL MP VIS.
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AP & AH & A4 & AAP & XRG).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segX1; [exact EC| lia| exact ETOP| exact XRG| exact ACCE| exact FR| clear - LO8K CEIL ACEILB; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 [[X0 VIS1]|[XP VIS1]]; pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    { apply (ah_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. do 26 eexists. exists m, s', M', LBN, errv', XS, spent.
      split; [exact FW|]. split; [exact SPI|]. split; [exact KREL1|]. split; [exact MPc1|]. left. exact VIS1. }
    destruct (fworld_exts _ _ _ _ _ _ _ _ _ FW XP) as (K & xs & XO & SO & LEN & F2 & F2SH & SKB & SKSH & SKR & NUMR).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1|..].
    { eapply asknum_spec with (lo := lo) (K := K); try reflexivity; try eassumption; rewrite ?unsigned_lit by lia; [exact ST| clear - LO8K CEIL; lia]. }
    intros msF2 mo2 KREL2 MP2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2).
    rewrite unsigned_lit in MU2, ST2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    assert (FW2 : fworld m2 s' M' LBN errv' (vpm_empty p) [] XS spent).
    { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact AC2| exact ST2|]. constructor; [cbn; lia| constructor]. }
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_segX2; [exact NUMR| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 [[N0 VIS3]|[NP VIS3]]; pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    { apply (ah_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. do 26 eexists. exists m2, s', M', LBN, errv', XS, spent.
      split; [exact FW2|]. split; [exact SPI|]. split; [exact KREL3|]. split; [exact MPc3|]. left. exact VIS3. }
    eapply (L2_loop (Z.to_nat (sk_num K)) 0); [exact XO| rewrite Z2Nat.id by lia; lia| lia| exact XP| exact FW2| exact SPI| exact KREL3| exact MPc3| exact VIS3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fworld_cstr : forall m s' M' LBN errv' V NB XS spent,
    fworld m s' M' LBN errv' V NB XS spent ->
    exists slack, bytes_at asegs m (en_pname E) (ns ++ Z_to_bv 8 0 :: slack)
      /\ (- (en_pname E + zlength ns + 1)) mod 8 <= zlength slack /\ en_pname E + zlength ns + 1 + zlength slack <= aceil
      /\ shvis m (en_pname E) (en_pname E + zlength ns + 1) /\ in_app_mem (en_pname E) (en_pname E + zlength ns + 1).
  Proof.
    intros m s' M' LBN errv' V NB XS spent FW. pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & _).
    cbv delta [spq VB] in *. acb.
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PNP & PNH & PNIN & PT & ACCP & PAP & P16 & _).
    assert (PNIN' : In (pn, en_pname E, zlength ns + 1) (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (do 3 (apply in_or_app; right); right; exact PNIN).
    pose proof (HHx_slack_law H HHx _ _ _ _ _ _ HP PNIN') as WR. pose proof (ah_blocks H HH _ _ _ _ HP PNIN') as (_ & _ & _ & P4 & _). cbn [blk_addr blk_size fst snd] in P4.
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ HP PNIN') as SV. cbn [blk_addr blk_size fst snd] in SV.
    set (e := en_pname E + (zlength ns + 1)) in *. set (k := (- e) mod 8) in *.
    assert (KR : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    pose proof (Z.div_mod (- e) 8 ltac:(lia)) as DM. fold k in DM. set (q := - e / 8) in DM.
    destruct (awr_at_bytes _ _ _ WR ltac:(lia) ltac:(clearbody k q; clear - P4 PNP; subst e; unfold zlength in *; lia)) as (slack & SL & SB).
    exists slack. unfold zlength in *. rewrite SL. split; [| split; [subst k e; lia| split; [| split; [replace (en_pname E + Z.of_nat (length ns) + 1) with e by (subst e; lia); exact SV| eapply aapp_in_app_mem; [exact PAP| lia| lia]]]]].
    - change (ns ++ Z_to_bv 8 0 :: slack) with (ns ++ [Z_to_bv 8 0] ++ slack). rewrite app_assoc. apply bytes_at_app. split; [exact PN|].
      rewrite length_app. cbn [length]. replace (en_pname E + Z.of_nat (length ns + 1)) with e by (subst e; lia). exact SB.
    - (* [comment removed for export] *)
      clearbody k q. destruct ACEILB as (A1 & AM & _). clear - PNH KR DM AM A1. subst e. Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_canary : forall m s' M' LBN errv' V NB XS spent,
    fworld m s' M' LBN errv' V NB XS spent ->
    exists can, rw_cells asegs m AGOT_SSP_CELL [C8 (wz ACANARY_CELL)] /\ rw_cells asegs m ACANARY_CELL [C8 (wz can)] /\ 0 <= can < 2^64.
  Proof.
    intros m s' M' LBN errv' V NB XS spent (_ & _ & _ & _ & _ & _ & HP & LM & _). destruct (CANL _ _ _ HP) as (can & CC & CR).
    pose proof LM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RL & _).
    exists can. split; [| split; [exact CC| exact CR]].
    eapply relro_cell; [exact RL| unfold AGOT_SSP_CELL; lia| unfold AGOT_SSP_CELL; cbn; lia| repeat constructor| vm_compute; reflexivity].
  Qed.

  Local Ltac retpc_in RA := replace (Z_to_bv 64 RA) with (ret_pc (Z_to_bv 64 RA)) by (apply ret_pc_even; [unfold RA; lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma fcc_failF : forall m s' M' LBN errv' V NB XS spent msF mo' (rax t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x4 x6 x7 x8 x9 x10 x11 : word),
    fworld m s' M' LBN errv' V NB XS spent -> spent + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 A) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFC_FAIL) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' M' LBN errv' V NB XS spent msF mo' rax t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x4 x6 x7 x8 x9 x10 x11 FW SPT KREL MP VIS.
    pose proof FW as (MI & _).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segF; exact MI|]. intros msF1 mo1 KREL1 MP1 VIS1.
    eapply fcc_tail; [exact FW| left; reflexivity| exact SPT| exact KREL1| exact (ah_mpres_trans H HH _ _ _ MP MP1)| exact VIS1].
  Qed.
  Lemma fcc_tailT : forall m s' M' LBN errv' V NB XS spent rv msF mo' (rax t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x6 x7 x8 x9 x10 x11 : word),
    fworld m s' M' LBN errv' V NB XS spent -> (rv = 0 \/ rv = 1) -> spent + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 (Z_to_bv 64 rv) (Z_to_bv 64 A) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFC_TAIL) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' M' LBN errv' V NB XS spent rv msF mo' rax t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x6 x7 x8 x9 x10 x11 FW RV SPT KREL MP VIS.
    pose proof FW as (MI & _).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segT; exact MI|]. intros msF1 mo1 KREL1 MP1 VIS1.
    eapply fcc_tail; [exact FW| exact RV| exact SPT| exact KREL1| exact (ah_mpres_trans H HH _ _ _ MP MP1)| exact VIS1].
  Qed.
  Lemma fcc_ok1 : forall m s' M' LBN errv' V NB XS spent msF mo' (rax t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x4 x6 x7 x8 x9 x10 x11 : word),
    fworld m s' M' LBN errv' V NB XS spent -> spent + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 A) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFC_OK) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' M' LBN errv' V NB XS spent msF mo' rax t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x2 x3 x4 x6 x7 x8 x9 x10 x11 FW SPT KREL MP VIS.
    pose proof FW as (MI & _ & _ & FR & _). cbv delta [spq] in FR. acb.
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segOK; [exact FR| clear - LO8K CEIL ACEILB; lia| exact MI]|]. intros msF1 mo1 KREL1 MP1 VIS1.
    eapply fcc_tail; [exact FW| right; reflexivity| exact SPT| exact KREL1| exact (ah_mpres_trans H HH _ _ _ MP MP1)| exact VIS1].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_name2 : forall m s' M' LBN errv' V NB XS spent r msF mo' (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x3 x4 x7 x8 x9 x10 x11 : word),
    fworld m s' M' LBN errv' V NB XS spent -> (r = 0 \/ r = 1) -> spent + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 AFC_R8) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + ASHB)) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 (ee + 8)) x3 x4 (Z_to_bv 64 A) (Z_to_bv 64 ASHB) x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (ret_pc (Z_to_bv 64 AFC_R8)) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' M' LBN errv' V NB XS spent r msF mo' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x3 x4 x7 x8 x9 x10 x11 FW RR SPT KREL MP VIS.
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & _ & _ & _ & _ & _ & PNP & PNH & PNIN & PT & ACCP & PAP & P16 & AP & AH & A4 & AAP & XRG).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segN3 with (r := r); [exact EC| lia| exact ETOP| exact ACCE| exact RR| exact MI]|].
    intros msF1 mo1 KREL1 MP1 [[-> VIS1]|[-> VIS1]]; pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1; [eapply fcc_failF; [exact FW| exact SPT| exact KREL1| exact MPc1| exact VIS1]|].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ _ FW) as (slack & CS & PAD & CEND & SHV & IAM). unfold zlength in *.
    pose proof (ACONST_icpt m AC) as (RSR & _ & _ & _ & CFS & _).
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1|..].
    { eapply strrchr_icpt_ok with (str := ns) (slack := slack) (lo := lo); rewrite ?unsigned_lit by lia; try eassumption.
      all: lazymatch goal with
           | |- accessible _ _ _ => exact ACCP
           | |- shvis _ _ _ => exact SHV
           | |- in_app_mem _ _ => exact IAM
           | |- _ <= _ - ASTRRCHR_STACK => unfold ASTRRCHR_STACK; clear - LO8K; lia
           | |- _ + 1 <= 2 ^ 40 => clear - NSL; lia
           | |- _ \/ _ => left; clear - CEND CEIL LO8K; lia
           | |- ?G => idtac "SRPRE" G
           end.
      all: fail "SRPRE". }
    intros msF2 mo2 KREL2 MP2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & _ & AC2).
    rewrite !unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite (unsigned_lit 46) in VIS2 by lia. unfold ASTRRCHR_STACK in MU2.
    pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    pose proof ST2 as ST2q.
    assert (FW2 : fworld m2 s' M' LBN errv' V NB XS spent).
    { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact AC2| exact ST2q|]. constructor; [cbn; clear - LO8K; lia| constructor]. }
    (* [comment removed for export] *)
    rewrite (unsigned_lit (en_pname E)) in VIS2 by lia.
    assert (RF : exists i0 b0 q, rfind_ret (en_pname E) (rfind (ns ++ [Z_to_bv 8 0]) (Z_to_bv 8 46)) = q
                 /\ (if q =? 0 then en_pname E else q) = en_pname E + Z.of_nat i0 /\ 0 <= q < 2^64
                 /\ (i0 < length ns)%nat /\ nth_error ns i0 = Some b0 /\ (i0 = 0%nat \/ bv_unsigned b0 = 46)).
    { rewrite (rfind_app_miss ns [Z_to_bv 8 0]) by reflexivity.
      destruct (rfind ns (Z_to_bv 8 46)) as [i|] eqn:RFD.
      - destruct (rfind_hit_nth _ _ _ RFD) as (b0 & N0 & E0). pose proof (rfind_lt _ _ _ RFD) as IL. exists i, b0, (en_pname E + Z.of_nat i). cbn [rfind_ret].
        split; [reflexivity|]. split; [destruct (Z.eqb_spec (en_pname E + Z.of_nat i) 0); lia|]. split; [clear - PNP PNH IL ACEILB; lia|].
        split; [exact IL|]. split; [exact N0| right; rewrite E0; reflexivity].
      - destruct (nth_error ns 0) as [b0|] eqn:N0; [| apply nth_error_None in N0; lia]. exists 0%nat, b0, 0. cbn [rfind_ret]. rewrite Z.eqb_refl.
        repeat split; try lia; auto. }
    destruct RF as (i0 & b0 & q & RFE & LLE & QR & IL & NTH0 & DOT). rewrite RFE in VIS2.
    set (LL := en_pname E + Z.of_nat i0) in *.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_segN4 with (q := q); [exact QR| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3. cbv zeta in VIS3. rewrite LLE in VIS3. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    assert (NN : forall i, ~ In (Z_to_bv 8 0) (skipn i ns)) by (intros i K; apply NONUL; eapply in_skipn_in; exact K).
    assert (LLR : 0 < LL /\ LL + Z.of_nat (length (skipn i0 ns)) = en_pname E + Z.of_nat (length ns)) by (subst LL; rewrite length_skipn; lia).
    destruct LLR as [LLP LLN].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ _ FW2) as (sl2 & CS2 & PAD2 & CEND2 & SHV2 & IAM2). unfold zlength in CS2, PAD2, CEND2, SHV2, IAM2.
    pose proof (cstr_suffix _ _ _ _ i0 CS2 ltac:(lia)) as CS2'. fold LL in CS2'.
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW2) as (qad1 & qad2 & qad3 & qad4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ACCP2 & _). unfold zlength in ACCP2.
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3|..].
    { eapply strlen_icpt_ok with (str := skipn i0 ns) (slack := sl2) (lo := lo); rewrite ?unsigned_lit by lia;
        [exact CS2'| apply NN| rewrite LLN; exact PAD2| | | exact ST2q| exact CEIL| unfold AINTRIN_STACK; clear - LO8K; lia| exact MI2| exact AC2| rewrite length_skipn; clear - NSL IL; lia| | left; rewrite LLN; clear - CEND2 CEIL LO8K; lia].
      - eapply accessible_sub; [exact ACCP2| subst LL; lia| rewrite length_skipn; subst LL; lia| rewrite length_skipn; lia].
      - eapply shvis_sub; [exact SHV2| lia| subst LL; lia| rewrite LLN; lia| rewrite length_skipn; lia| lia].
      - eapply in_app_mem_sub; [exact IAM2| subst LL; lia| rewrite LLN; lia]. }
    intros msF4 mo4 KREL4 MP4 (v0 & v1 & v2 & c1_ & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & VIS4 & MU3 & WM3 & MI3 & ST3 & _ & AC3).
    rewrite !unsigned_lit in MU3 by lia. unfold AINTRIN_STACK in MU3. pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4.
    rewrite unsigned_lit in ST3 by lia.
    assert (FW3 : fworld m3 s' M' LBN errv' V NB XS spent) by (eapply fworld_stk; [exact FW2| exact MU3| exact WM3| exact MI3| exact AC3| exact ST3| constructor; [cbn; clear - LO8K; lia| constructor]]).
    set (L2 := Z.of_nat (length (skipn i0 ns))) in *.
    assert (L2R : 1 <= L2 <= 255) by (subst L2; rewrite length_skipn; clear - IL NSL; lia).
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ _ FW3) as (sl3 & CS3 & PAD3 & CEND3 & SHV3 & IAM3). unfold zlength in CS3, PAD3, CEND3, SHV3, IAM3.
    pose proof (cstr_suffix _ _ _ _ i0 CS3 ltac:(lia)) as CS3'. fold LL in CS3'.
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW3) as (rad1 & rad2 & rad3 & rad4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ACCP3 & _). unfold zlength in ACCP3.
    assert (ACCL3 : accessible m3 LL (L2 + 1)) by (eapply accessible_sub; [exact ACCP3| subst LL; lia| subst LL L2; rewrite length_skipn; lia| lia]).
    assert (NTHL : nth_error (skipn i0 ns) 0 = Some b0) by (rewrite nth_error_skipn', Nat.add_0_r; exact NTH0).
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply afcc_segN5 with (LL := LL) (L2 := L2) (ls := skipn i0 ns) (rest := Z_to_bv 8 0 :: sl3) (c0 := b0) (nn := L2 + 1);
      [exact CS3'| exact NTHL| lia| exact LLP| clear - PT LLN; lia| exact ACCL3| lia| exact MI3]|].
    set (d := if bv_unsigned b0 =? 46 then 1 else 0). intros msF5 mo5 KREL5 MP5 (a2' & [[L2S VIS5]|[L2B VIS5]]); pose proof (ah_mpres_trans H HH _ _ _ MPc4 MP5) as MPc5;
      [eapply fcc_failF; [exact FW3| exact SPT| exact KREL5| exact MPc5| exact VIS5]|].
    assert (DR : 0 <= d <= 1 /\ d < L2) by (subst d; destruct (bv_unsigned b0 =? 46); lia).
    set (ls' := skipn (Z.to_nat d) (skipn i0 ns)).
    assert (LS'L : Z.of_nat (length ls') = L2 - d) by (subst ls' L2; rewrite length_skipn; lia).
    assert (CSX : forall mm sl, bytes_at asegs mm LL (skipn i0 ns ++ Z_to_bv 8 0 :: sl) -> bytes_at asegs mm (LL + d) (ls' ++ Z_to_bv 8 0 :: sl)).
    { intros mm sl BS. replace d with (Z.of_nat (Z.to_nat d)) at 1 by lia. subst ls'. apply cstr_suffix; [exact BS| lia]. }
    (* [comment removed for export] *)
    destruct (fworld_canary _ _ _ _ _ _ _ _ _ FW3) as (can & CG3 & CC3 & CANR).
    pose proof (proj2 (proj2 R_DIGITS) m3 MI3) as (DB3 & DN3 & _). pose proof AR_DIGITS as (_ & DACC & DLO & DHI). rewrite S_DIGITS_len in DHI. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in DHI.
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5|..].
    { eapply SPN with (str := ls') (sslack := sl3) (acc := S_DIGITS) (aslack := K_DIGITS) (lo := lo) (can := can).
      all: lazymatch goal with
           | |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 AA_DIGITS)) _ => unfold AA_DIGITS; rewrite unsigned_lit by lia; exact DB3
           | |- bytes_at _ _ _ _ => rewrite unsigned_lit by lia; exact (CSX _ _ CS3')
           | |- ~ In _ S_DIGITS => exact DN3
           | |- ~ In _ _ => subst ls'; rewrite skipn_skipn; apply NN
           | |- (2 <= length S_DIGITS)%nat => rewrite S_DIGITS_len; lia
           | |- accessible _ (bv_unsigned (Z_to_bv 64 AA_DIGITS)) _ => unfold AA_DIGITS in *; rewrite unsigned_lit by lia; rewrite S_DIGITS_len; exact (DACC _ AC3)
           | |- accessible _ _ _ => rewrite unsigned_lit by lia; rewrite LS'L; eapply accessible_sub; [exact ACCL3| lia| lia| lia]
           | |- shvis _ (bv_unsigned (Z_to_bv 64 AA_DIGITS)) _ => unfold AA_DIGITS in *; rewrite !unsigned_lit by lia; rewrite S_DIGITS_len; apply ACONST_shvis; [exact AC3| unfold AIMG_LO in *; cbn; lia| cbn; lia| unfold AIMG_TOP in *; cbn in DHI |- *; lia]
           | |- shvis _ _ _ => rewrite !unsigned_lit by lia; rewrite LS'L; eapply shvis_sub; [exact SHV3| lia| subst LL; lia| rewrite <- LLN; lia| lia| lia]
           | |- in_app_mem (bv_unsigned (Z_to_bv 64 AA_DIGITS)) _ => unfold AA_DIGITS; rewrite !unsigned_lit by lia; unfold in_app_mem; left; rewrite ASHADOW_BASE_val; cbn; lia
           | |- in_app_mem _ _ => rewrite !unsigned_lit by lia; rewrite LS'L; eapply in_app_mem_sub; [exact IAM3| subst LL; lia| rewrite <- LLN; lia]
           | |- Z.of_nat (length S_DIGITS) + 1 <= _ => rewrite S_DIGITS_len; cbn; lia
           | |- Z.of_nat (length _) + 1 <= _ => rewrite LS'L; clear - L2R DR; lia
           | |- bv_unsigned (Z_to_bv 64 AA_DIGITS) + _ + _ + _ <= lo => unfold AA_DIGITS; rewrite !unsigned_lit by lia; rewrite S_DIGITS_len; cbn; clear - LO8K CEIL ACEILB; lia
           | |- bv_unsigned _ + _ + _ + _ <= lo => rewrite !unsigned_lit by lia; rewrite LS'L; cbn [length]; clear - CEND3 LLN LO8K CEIL DR; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST3
           | |- aceil <= lo => exact CEIL
           | |- lo <= _ - ASTRSPN_STACK => rewrite unsigned_lit by lia; unfold ASTRSPN_STACK; clear - LO8K; lia
           | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by lia; clear - SPR LO8K CEIL ACEILB; lia
           | |- mem_inv _ _ => exact MI3
           | |- ACONST _ => exact AC3
           | |- rw_cells _ _ AGOT_SSP_CELL _ => exact CG3
           | |- rw_cells _ _ ACANARY_CELL _ => exact CC3
           | |- 0 <= _ < 2 ^ 64 => exact CANR
           | |- ?G => idtac "SP1PRE" G
           end.
      all: fail "SP1PRE". }
    intros msF6 mo6 KREL6 MP6 (x0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m4 & VIS6 & MU4 & WM4 & MI4 & ST4 & AC4).
    rewrite !unsigned_lit in MU4 by lia. rewrite unsigned_lit in ST4 by lia. unfold ASTRSPN_STACK in MU4. pose proof (ah_mpres_trans H HH _ _ _ MPc5 MP6) as MPc6.
    assert (FW4 : fworld m4 s' M' LBN errv' V NB XS spent).
    { eapply fworld_stk; [exact FW3| exact MU4| exact WM4| exact MI4| exact AC4| exact ST4|]. constructor; [cbn; clear - LO8K; lia| constructor]. }
    set (n1 := Z.of_nat (spn ls' S_DIGITS)) in *.
    assert (N1R : 0 <= n1 <= L2 - d) by (subst n1; pose proof (spn_le ls' S_DIGITS); lia).
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ _ FW4) as (sl4 & CS4 & PAD4 & CEND4 & SHV4 & IAM4). unfold zlength in CS4, PAD4, CEND4, SHV4, IAM4.
    pose proof (CSX _ _ (cstr_suffix _ _ _ _ i0 CS4 ltac:(lia))) as CS4'. fold LL in CS4'.
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW4) as (sad1 & sad2 & sad3 & sad4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ACCP4 & _). unfold zlength in ACCP4.
    assert (ACCL4 : accessible m4 (LL + d) (L2 - d + 1)) by (eapply accessible_sub; [exact ACCP4| subst LL; lia| subst LL L2; rewrite length_skipn; lia| lia]).
    set (c0 := match nth_error ls' 0 with Some b => b | None => b0 end). set (c1 := match nth_error ls' 1 with Some b => b | None => b0 end).
    assert (C01 : 3 <= L2 - d -> nth_error ls' 0 = Some c0 /\ nth_error ls' 1 = Some c1).
    { intros L3B. subst c0 c1. destruct (nth_error ls' 0) as [xb|] eqn:E0; [| apply nth_error_None in E0; lia].
      destruct (nth_error ls' 1) as [yb|] eqn:E1; [| apply nth_error_None in E1; lia]. split; reflexivity. }
    assert (NTHc0 : nth_error ls' 0 = Some c0) by (subst c0; destruct (nth_error ls' 0) as [xb|] eqn:E0; [reflexivity| apply nth_error_None in E0; lia]).
    pose proof FW4 as (_ & _ & _ & FR4 & _).
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply afcc_segN6 with (LL := LL + d) (L3 := L2 - d) (n1 := n1) (ls := ls') (rest := Z_to_bv 8 0 :: sl4) (c0 := c0) (c1 := c1) (nn := L2 - d + 1);
      [exact CS4'| exact NTHc0| intros L3B; exact (proj2 (C01 L3B))| lia| lia| lia| clear - PT LLN DR; lia| exact ACCL4| lia| lia| exact FR4| clear - LO8K CEIL ACEILB; lia| exact MI4]|].
    intros msF7 mo7 KREL7 MP7 (a0' & a1' & a2'' & [[_ VIS7]|[[_ VIS7]|(_ & L3B & _ & _ & VIS7)]]); pose proof (ah_mpres_trans H HH _ _ _ MPc6 MP7) as MPc7;
      [eapply fcc_failF; [exact FW4| exact SPT| exact KREL7| exact MPc7| exact VIS7]| eapply fcc_ok1; [exact FW4| exact SPT| exact KREL7| exact MPc7| exact VIS7]|].
    (* [comment removed for export] *)
    destruct (fworld_canary _ _ _ _ _ _ _ _ _ FW4) as (can4 & CG4 & CC4 & CANR4).
    pose proof (proj2 (proj2 R_HEXDIGITS) m4 MI4) as (HB4 & HN4 & _). pose proof AR_HEXDIGITS as (_ & HACC & HLO & HHI). rewrite S_HEXDIGITS_len in HHI. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HHI.
    set (ls'' := skipn 2 ls').
    assert (LS''L : Z.of_nat (length ls'') = L2 - d - 2) by (subst ls''; rewrite length_skipn; lia).
    assert (CS4'' : bytes_at asegs m4 (LL + d + 2) (ls'' ++ Z_to_bv 8 0 :: sl4)) by (subst ls''; change 2 with (Z.of_nat 2) at 1; apply cstr_suffix; [exact CS4'| lia]).
    eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7|..].
    { eapply SPN with (str := ls'') (sslack := sl4) (acc := S_HEXDIGITS) (aslack := K_HEXDIGITS) (lo := lo) (can := can4).
      all: lazymatch goal with
           | |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 AA_HEXDIGITS)) _ => unfold AA_HEXDIGITS; rewrite unsigned_lit by lia; exact HB4
           | |- bytes_at _ _ _ _ => rewrite unsigned_lit by lia; exact CS4''
           | |- ~ In _ S_HEXDIGITS => exact HN4
           | |- ~ In _ _ => subst ls'' ls'; rewrite !skipn_skipn; apply NN
           | |- (2 <= length S_HEXDIGITS)%nat => rewrite S_HEXDIGITS_len; lia
           | |- accessible _ (bv_unsigned (Z_to_bv 64 AA_HEXDIGITS)) _ => unfold AA_HEXDIGITS in *; rewrite unsigned_lit by lia; rewrite S_HEXDIGITS_len; exact (HACC _ AC4)
           | |- accessible _ _ _ => rewrite unsigned_lit by lia; rewrite LS''L; eapply accessible_sub; [exact ACCL4| lia| lia| lia]
           | |- shvis _ (bv_unsigned (Z_to_bv 64 AA_HEXDIGITS)) _ => unfold AA_HEXDIGITS in *; rewrite !unsigned_lit by lia; rewrite S_HEXDIGITS_len; apply ACONST_shvis; [exact AC4| unfold AIMG_LO in *; cbn; lia| cbn; lia| unfold AIMG_TOP in *; cbn in HHI |- *; lia]
           | |- shvis _ _ _ => rewrite !unsigned_lit by lia; rewrite LS''L; eapply shvis_sub; [exact SHV4| lia| subst LL; lia| rewrite <- LLN; lia| lia| lia]
           | |- in_app_mem (bv_unsigned (Z_to_bv 64 AA_HEXDIGITS)) _ => unfold AA_HEXDIGITS; rewrite !unsigned_lit by lia; unfold in_app_mem; left; rewrite ASHADOW_BASE_val; cbn; lia
           | |- in_app_mem _ _ => rewrite !unsigned_lit by lia; rewrite LS''L; eapply in_app_mem_sub; [exact IAM4| subst LL; lia| rewrite <- LLN; lia]
           | |- Z.of_nat (length S_HEXDIGITS) + 1 <= _ => rewrite S_HEXDIGITS_len; cbn; lia
           | |- Z.of_nat (length _) + 1 <= _ => rewrite LS''L; clear - L2R DR L3B; lia
           | |- bv_unsigned (Z_to_bv 64 AA_HEXDIGITS) + _ + _ + _ <= lo => unfold AA_HEXDIGITS; rewrite !unsigned_lit by lia; rewrite S_HEXDIGITS_len; cbn; clear - LO8K CEIL ACEILB; lia
           | |- bv_unsigned _ + _ + _ + _ <= lo => rewrite !unsigned_lit by lia; rewrite LS''L; cbn [length]; clear - CEND4 LLN LO8K CEIL DR L3B; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST4
           | |- aceil <= lo => exact CEIL
           | |- lo <= _ - ASTRSPN_STACK => rewrite unsigned_lit by lia; unfold ASTRSPN_STACK; clear - LO8K; lia
           | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by lia; clear - SPR LO8K CEIL ACEILB; lia
           | |- mem_inv _ _ => exact MI4
           | |- ACONST _ => exact AC4
           | |- rw_cells _ _ AGOT_SSP_CELL _ => exact CG4
           | |- rw_cells _ _ ACANARY_CELL _ => exact CC4
           | |- 0 <= _ < 2 ^ 64 => exact CANR4
           | |- ?G => idtac "SP2PRE" G
           end.
      all: fail "SP2PRE". }
    intros msF8 mo8 KREL8 MP8 (y0 & z1 & z2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m5 & VIS8 & MU5 & WM5 & MI5 & ST5 & AC5).
    rewrite !unsigned_lit in MU5 by lia. rewrite unsigned_lit in ST5 by lia. unfold ASTRSPN_STACK in MU5. pose proof (ah_mpres_trans H HH _ _ _ MPc7 MP8) as MPc8.
    assert (FW5 : fworld m5 s' M' LBN errv' V NB XS spent).
    { eapply fworld_stk; [exact FW4| exact MU5| exact WM5| exact MI5| exact AC5| exact ST5|]. constructor; [cbn; clear - LO8K; lia| constructor]. }
    (* [comment removed for export] *)
    pose proof FW5 as (_ & _ & _ & FR5 & _).
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply afcc_segN7 with (L3 := L2 - d) (n2 := Z.of_nat (spn ls'' S_HEXDIGITS)); [lia| pose proof (spn_le ls'' S_HEXDIGITS); lia| exact FR5| clear - LO8K CEIL ACEILB; lia| exact MI5]|].
    intros msF9 mo9 KREL9 MP9 [[_ VIS9]|[_ VIS9]]; pose proof (ah_mpres_trans H HH _ _ _ MPc8 MP9) as MPc9;
      [eapply fcc_tail; [exact FW5| left; reflexivity| exact SPT| exact KREL9| exact MPc9| exact VIS9]| eapply fcc_ok1; [exact FW5| exact SPT| exact KREL9| exact MPc9| exact VIS9]].
  Qed.

  Lemma M_eq1' : forall M', mid_step M M' -> mkMID 1 (mid_ctx M') (mid_err M') (mid_E M') (mid_vdso M') = M'.
  Proof. clear. intros [f c e E0 v] (F1 & _). cbn in *. subst. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fworld_after_add1host : forall m m' s' s'' M' LBN errv' errv'' XS spent V' NB,
    let Lcur := mid_errblocks M' ++ LBN ++ [] ++ VB :: LB in
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent ->
    mem_inv asegs m' -> ACONST m' -> stk asegs m' lo spq -> as_rauxv_ok H m' B ->
    rw_cells asegs m' (errno_addr tp) [C4 errv''] ->
    xpres H Lcur spq (memflag_foot ++ [(A, A + VPM_SIZE)]) m m' ->
    as_RHEAP H s'' (NB ++ Lcur) m' -> VPMobj (NB ++ Lcur) m' A V' -> vp_id V' = p ->
    Permutation (blocks_VPM A V') (VB :: NB) ->
    Z.of_nat (length NB) <= 4 -> lb_bytes NB <= ADD1HOST_BYTES -> VPM_shad m' A V' -> MEMFLAG m' 1 ->
    as_AL H s'' >= as_AL H s' - ADD1HOST_COST H ->
    fworld m' s'' M' LBN errv'' V' NB XS (spent + ADD1HOST_COST H).
  Proof.
    intros m m' s' s'' M' LBN errv' errv'' XS spent V' NB Lcur FW MI' AC' ST' AUX' ERR' XP' HP' VO' VID' VP' NB1' NB2' VSH' MF' AL'.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    cbv delta [spq VB] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof LM as (_ & MF1 & _). pose proof STP as (F1 & _). rewrite F1 in MF1.
    assert (CX' : mid_ctx M' = CtxReady x) by (rewrite CXE; exact CX).
    pose proof (ah_nodup H HH _ _ _ HP) as ND.
    pose proof VBR as (AP & _ & _ & A4' & AH' & AFS' & AAP').
    assert (VBIN : In (p, A, VPM_SIZE) Lcur) by (subst Lcur; do 3 (apply in_or_app; right); left; reflexivity).
    assert (SPQC : aceil <= bv_unsigned sp + -128) by (clear - CEIL LO8K; lia).
    (* [comment removed for export] *)
    assert (IDV : forall b, In b (mid_errblocks M' ++ LBN ++ LB) -> blk_id b <> blk_id (p, A, VPM_SIZE)).
    { intros b Hb.
      assert (CASE : In b (mid_errblocks M' ++ LBN) \/ In b LB).
      { apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; exact Hb]. }
      destruct CASE as [Hb'|Hb'].
      - pose proof ND as ND'. subst Lcur. rewrite app_assoc in ND'. exact (nodup_ids_app_ne _ _ _ _ ND' Hb' ltac:(apply in_or_app; right; left; reflexivity)).
      - subst Lcur. destruct (nd_app _ _ ND) as [_ ND1]. destruct (nd_app _ _ ND1) as [_ ND2]. cbn [app map] in ND2. inversion ND2 as [|i1 l1 NI1 X2]; subst.
        intros EQ. apply NI1. rewrite <- EQ. apply in_map. exact Hb'. }
    assert (NCL : forall L q, (forall b, In b L -> In b (mid_errblocks M' ++ LBN ++ LB)) -> rin_ivs [(A, A + VPM_SIZE)] q -> aclient_addr H L (bv_unsigned sp + -128) q -> False).
    { intros L q SUBL0 Hq C. cbn [rin_ivs fst snd] in Hq. destruct Hq as [Hq|[]].
      eapply (blk_not_client H HHx s' Lcur m L (bv_unsigned sp + -128) (p, A, VPM_SIZE) q); [exact HP| exact VBIN| | intros b Hb; exact (IDV _ (SUBL0 _ Hb))| exact SPQC| cbn [blk_addr blk_size fst snd]; exact Hq| exact C].
      intros b Hb. subst Lcur. pose proof (SUBL0 _ Hb) as Hb'. apply in_app_or in Hb'. destruct Hb' as [K|K]; [apply in_or_app; left; exact K|].
      apply in_app_or in K. destruct K as [K|K]; [apply in_or_app; right; apply in_or_app; left; exact K| do 3 (apply in_or_app; right); right; exact K]. }
    (* [comment removed for export] *)
    assert (APV : forall b, In b (mid_errblocks M' ++ LBN ++ LB) -> blk_addr b + blk_size b + 16 <= A \/ A + VPM_SIZE + 16 <= blk_addr b).
    { intros b Hb.
      assert (BIN : In b Lcur).
      { subst Lcur. apply in_app_or in Hb. destruct Hb as [K|K]; [apply in_or_app; left; exact K|].
        apply in_app_or in K. destruct K as [K|K]; [apply in_or_app; right; apply in_or_app; left; exact K| do 3 (apply in_or_app; right); right; exact K]. }
      pose proof (ah_disj H HH _ _ _ _ _ HP BIN VBIN (IDV _ Hb)) as DJ. cbn [blk_addr blk_size fst snd] in DJ. exact DJ. }
    assert (AVX : forall b', In b' (blocks_ENTRY ee E) -> avoids (memflag_foot ++ [(A, A + VPM_SIZE)]) (blk_addr b') (blk_size b') /\ shavoids (memflag_foot ++ [(A, A + VPM_SIZE)]) (blk_addr b') (blk_size b')).
    { intros b' Hb'. pose proof (ENTRYobj_owned_law _ _ _ _ EO _ Hb') as IN'.
      pose proof (ah_blocks H HH _ _ _ _ HP ltac:(subst Lcur; do 3 (apply in_or_app; right); right; exact IN')) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      pose proof (APV b' ltac:(do 2 (apply in_or_app; right); exact IN')) as DJ.
      split; (apply Forall_app; split; [| constructor; [cbn [fst snd]| constructor]]).
      - apply avoids_memflag. exact C4.
      - clear - DJ. lia.
      - apply shavoids_memflag; [exact C7| exact C3].
      - exact (sh_vs_app _ _ _ _ C7 C3 AAP' ltac:(unfold VPM_SIZE; lia)). }
    assert (SUBL : forall b, In b LB -> In b Lcur) by (intros b Hb; subst Lcur; do 3 (apply in_or_app; right); right; exact Hb).
    assert (XPL : xpres H LB (bv_unsigned sp + -128) (memflag_foot ++ [(A, A + VPM_SIZE)]) m m') by (eapply (xpres_weaken H); [exact XP'| lia| exact SUBL| auto]).
    pose proof EO as (_ & EIN & O1 & O2 & O3 & O4 & XT). rewrite SUO in O3. rewrite PNO in O1. cbn [ofield] in O1, O3.
    destruct O1 as (PNP & _ & PNIN). destruct O3 as (SUP & _ & SUIN).
    pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ. unfold zlength in *.
    assert (INS : In (ps, en_suites E, sn) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. do 2 (apply in_or_app; right). apply in_or_app. left. rewrite SUO. left. reflexivity. }
    assert (INP : In (pn, en_pname E, Z.of_nat (length ns) + 1) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. apply in_or_app. left. rewrite PNO. left. reflexivity. }
    pose proof (bytes_at_bound _ _ _ _ PN) as PNB. rewrite length_app in PNB. cbn [length] in PNB.
    assert (AVF : avoids (memflag_foot ++ [(A, A + VPM_SIZE)]) (bv_unsigned sp + -128) 128).
    { unfold avoids. apply Forall_app. split.
      - apply avoids_memflag. unfold AIMG_TOP. clear - CEIL LO8K ACEILB. lia.
      - constructor; [cbn; clear - AH' CEIL LO8K; unfold VPM_SIZE in *; lia| constructor]. }
    assert (XPLB : xpres H LB (bv_unsigned sp) [] m m').
    { eapply (xpres_weaken H LB LB (bv_unsigned sp + -128) (bv_unsigned sp) [] []); [| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq].
      eapply (xpres_drop_windows H LB Lcur (bv_unsigned sp + -128) [] [(A, A + VPM_SIZE)] m m'); [| exact SUBL| intros q Hq C; exact (NCL LB q ltac:(intros b Hb; do 2 (apply in_or_app; right); exact Hb) Hq C)].
      cbn [app]. eapply (axpres_drop_memflag H Lcur _ [] [(A, A + VPM_SIZE)]); [exact MF1| exact MF'| cbn [app]; exact XP']. }
    unfold fworld. cbv delta [spq VB]. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
      | |- rw_cells _ _ (bv_unsigned sp + -128) _ =>
          eapply (xpres_rw_cells' H); [exact XP'| exact FR| left; lia|]; unfold afcc_frame; cbn [cells_size csize Nat.add]; exact AVF
      | |- as_RHEAP _ _ _ _ => eapply (HHx_rheap_perm H HHx); [exact HP'|]; subst Lcur; cbn [app]; rewrite (app_assoc (mid_errblocks M') LBN); etransitivity; [apply Permutation_app_swap_app|]; rewrite <- app_assoc; apply Permutation_refl
      | |- LIBMID _ _ _ =>
          rewrite <- (M_eq1' M' STP);
          eapply (LIBMID_mfX H HH s' m (LBN ++ LIB) Lcur (bv_unsigned sp + -128) [(A, A + VPM_SIZE)] m m' M' x); [exact HP| exact LM| exact CX'| exact XP'| | | | | | | | exact MF'|];
          [ intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [subst Lcur; apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUBL; apply LIBSUB; exact Hb]
          | intros b Hb; subst Lcur; apply in_or_app; left; exact Hb
          | intros q Hq HX; pose proof (LIBX_below q HX) as QL; cbn [rin_ivs fst snd] in Hq; unfold AIMG_TOP in *; clear - QL Hq A4'; lia
          | intros q Hq R; cbn [rin_ivs fst snd] in Hq; unfold AIMG_TOP in *; clear - R Hq A4'; lia
          | intros q Hq K0; eapply (NCL (LBN ++ LIB) q); [intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| do 2 (apply in_or_app; right); apply LIBSUB; exact Hb]| exact Hq| right; right; left; exact K0]
          | intros q Hq K0; eapply (NCL (LBN ++ LIB) q); [intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| do 2 (apply in_or_app; right); apply LIBSUB; exact Hb]| exact Hq| right; right; right; left; exact K0]
          | intros q Hq K0; eapply (NCL (mid_errblocks M') q); [intros b Hb; apply in_or_app; left; exact Hb| exact Hq| right; right; right; left; exact K0]
          | intros q Hq K0; eapply (NCL (mid_errblocks M') q); [intros b Hb; apply in_or_app; left; exact Hb| exact Hq| right; right; left; exact K0] ]
      | |- ENTRYobj _ _ _ _ => eapply (ENTRYobj_frameX LB); [exact EO| exact XPL|]; intros b Hb; exact (proj1 (AVX _ Hb))
      | |- ENTRY_shad _ _ _ => eapply (ENTRY_shad_frameX LB); [exact ESH| exact EO| exact XPL|]; intros b Hb; split; [exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact (AVX _ Hb)]
      | |- rw_cells _ _ (en_suites E) _ =>
          eapply (xpres_rw_cells' H); [exact XPL| exact SU| |];
          [ right; right; left; exists (ps, en_suites E, sn); split; [exact SUIN|]; cbn [blk_addr blk_size fst snd]; lia
          | eapply avoids_sub; [exact (proj1 (AVX _ INS))| cbn; lia| cbn [blk_addr blk_size fst snd]; lia] ]
      | |- bytes_at _ _ (en_pname E) _ =>
          eapply (xpres_bytes_at' H); [exact XPL| exact PN| |];
          [ right; right; left; exists (pn, en_pname E, Z.of_nat (length ns) + 1); split; [exact PNIN|]; cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia
          | eapply avoids_sub; [exact (proj1 (AVX _ INP))| cbn; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia] ]
      | |- VPMobj _ _ _ _ =>
          eapply (VPMobj_frame_law H _ (NB ++ (p, A, VPM_SIZE) :: LB) m' m' A V' (bv_unsigned sp + -128)); [exact VO'| | apply (xpres_refl H)|];
          [ intros b Hb; pose proof (Permutation_in _ VP' Hb) as Hb'; destruct Hb' as [<-|Hb']; [apply in_or_app; right; left; reflexivity| apply in_or_app; left; exact Hb']
          | intros b Hb; pose proof (ah_blocks H HH _ _ _ _ HP' (VPMobj_owned_law _ _ _ _ VO' _ Hb)) as (_ & _ & _ & _ & B5 & _); clear - B5 CEIL LO8K; lia ]
      | |- stack0 _ _ _ =>
          eapply (stack0_xpres H); [exact XPL| exact SK0|]; apply Forall_app; split;
          [ unfold memflag_foot, A_mem_inited; apply Forall_cons; [right; cbn [fst snd]; unfold sh; rewrite ASHADOW_BASE_val; clear - ACEILB; Z.div_mod_to_equations; lia| apply Forall_nil]
          | apply Forall_cons; [eapply stack0_ok_aapp; [exact AAP'| lia| lia]| apply Forall_nil] ]
      | |- as_RFS _ _ _ =>
          eapply (RFS_via_xpresX H HHx s' Lcur m); [exact RFS| exact HP| exact XP'|]; apply Forall_app; split;
          [ unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
          | apply Forall_cons; [right; left; exists (p, A, VPM_SIZE); split; [exact VBIN| cbn [blk_addr blk_size fst snd]; lia]| apply Forall_nil] ]
      | |- xpres H LB _ _ m0 _ => eapply (xpres_trans H); [exact XP0|]; eapply (xpres_X_mono H); [exact XPLB| intros q Hq; destruct Hq]
      | |- 0 <= _ + ADD1HOST_COST _ =>
          unfold ADD1HOST_COST; pose proof (aCm_pos H HH XBUF_SIZE ltac:(unfold XBUF_SIZE; lia)); pose proof (aCm_pos H HH 256 ltac:(lia)); pose proof (aCm_pos H HH SK_SIZE ltac:(unfold SK_SIZE; lia));
          pose proof (aCm_pos H HH 32 ltac:(lia)); rewrite (aCf0 H HH); clear - AL0 H0 H1 H2 H3; lia
      | |- as_AL _ _ + _ >= _ => clear - AL1 AL'; lia
      | |- ?G => idtac "AHPOST" G
      end.
    all: fail "AHPOST".
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_name1 : forall m s' M' LBN errv' XS spent msF mo' (rax x1 x2 a0 a1 a2 a3 a4 a5 a6 a7 x3 x4 x5 x7 x8 x9 x10 x11 t0 t1 t2 t3 t4 t5 t6 : word),
    fworld m s' M' LBN errv' (vpm_empty p) [] XS spent -> spent + RAISE_COST H (mid_err M') <= as_Cm H VPM_SIZE + RC + en_nsuites E * RCR H ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 (Z_to_bv 64 ASHB) x7 x8 x9 x10 x11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFC_NAME) fc None m (seg_rom asegs) ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' M' LBN errv' XS spent msF mo' rax x1 x2 a0 a1 a2 a3 a4 a5 a6 a7 x3 x4 x5 x7 x8 x9 x10 x11 t0 t1 t2 t3 t4 t5 t6 FW SPI KREL MP VIS.
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & STP & NW & CXE & VDE & EO & ESH & SU & PN & VO & VSH & VID & VP & NB1 & NB2 & SK0 & RFS & FXS & XP0 & AL0 & AL1).
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & ETOP & ACCE & _ & _ & _ & _ & _ & PNP & PNH & PNIN & PT & ACCP & PAP & P16 & AP & AH & A4 & AAP & XRG).
    unfold zlength in *.
    (* [comment removed for export] *)
    assert (SPT0 : spent + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E) /\ spent + ADD1HOST_COST H + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) <= FCC_SPENT H M M' (en_nsuites E)).
    { unfold FCC_SPENT. rewrite (RCd_eq M' STP). pose proof RCR_pos as RP.
      assert (AC0 : 0 <= ADD1HOST_COST H).
      { unfold ADD1HOST_COST. pose proof (aCm_pos H HH XBUF_SIZE ltac:(unfold XBUF_SIZE; lia)). pose proof (aCm_pos H HH 256 ltac:(lia)). pose proof (aCm_pos H HH SK_SIZE ltac:(unfold SK_SIZE; lia)).
        pose proof (aCm_pos H HH 32 ltac:(lia)). rewrite (aCf0 H HH). lia. }
      clear - SPI RP AC0 NSR. nia. }
    destruct SPT0 as [SPT SPT1].
    (* [comment removed for export] *)
    destruct (nth_error ns 0) as [b0|] eqn:NTH0; [| apply nth_error_None in NTH0; lia].
    assert (B0 : bv_unsigned b0 <> 0).
    { intros K. apply NONUL. replace (Z_to_bv 8 0) with b0 by (apply bv_eq; rewrite K; reflexivity). eapply nth_error_In. exact NTH0. }
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_segN1 with (rest := [Z_to_bv 8 0]) (b0 := b0) (E := E) (ns := ns) (nn := Z.of_nat (length ns) + 1);
      [exact EC| lia| exact ETOP| exact ACCE| exact PN| exact NTH0| exact B0| exact PNP| clear - PT; lia| exact ACCP| lia| exact FR| clear - LO8K CEIL ACEILB; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (a0' & a1' & [[_ VIS1]|[B46 VIS1]]); pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1; [eapply fcc_tailT; [exact FW| left; reflexivity| exact SPT| exact KREL1| exact MPc1| exact VIS1]|].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ _ FW) as (sl1 & CS1 & PAD1 & CEND1 & SHV1 & IAM1). unfold zlength in CS1, PAD1, CEND1, SHV1, IAM1.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1|..].
    { eapply strlen_icpt_ok with (str := ns) (slack := sl1) (lo := lo); rewrite ?unsigned_lit by lia;
        [exact CS1| exact NONUL| exact PAD1| exact ACCP| exact SHV1| exact ST| exact CEIL| unfold AINTRIN_STACK; clear - LO8K; lia| exact MI| exact AC| clear - NSL; lia| exact IAM1| left; clear - CEND1 CEIL LO8K; lia]. }
    intros msF2 mo2 KREL2 MP2 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & _ & AC2).
    rewrite !unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. unfold AINTRIN_STACK in MU2. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    assert (FW2 : fworld m2 s' M' LBN errv' (vpm_empty p) [] XS spent) by (eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact AC2| exact ST2| constructor; [cbn; clear - LO8K; lia| constructor]]).
    pose proof FW2 as (_ & _ & _ & FR2 & ERR2 & AUX2 & HP2 & LM2 & _ & _ & _ & _ & EO2 & ESH2 & SU2 & PN2 & VO2 & VSH2 & _ & _ & _ & _ & SK02 & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ _ FW2) as (qad1 & qad2 & qad3 & qad4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ACCP2 & _). unfold zlength in ACCP2.
    (* [comment removed for export] *)
    destruct (nth_error ns (Z.to_nat (Z.of_nat (length ns) - 1))) as [bl|] eqn:NTHL; [| apply nth_error_None in NTHL; lia].
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_segN2 with (rest := [Z_to_bv 8 0]) (bl := bl) (ns := ns) (nn := Z.of_nat (length ns) + 1);
      [exact PN2| unfold zlength; exact NSL| unfold zlength; exact NTHL| exact PNP| clear - PT; lia| exact ACCP2| unfold zlength; lia| exact FR2| clear - LO8K CEIL ACEILB; lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (a2' & a3' & [[_ VIS3]|[BL46 VIS3]]); pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3; [eapply fcc_tailT; [exact FW2| left; reflexivity| exact SPT| exact KREL3| exact MPc3| exact VIS3]|].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ _ FW2) as (sl2 & CS2 & PAD2 & CEND2 & _). unfold zlength in CS2, PAD2, CEND2.
    pose proof (fworld_chain _ _ _ _ _ _ _ _ _ FW2) as CHN2. cbv delta [spq] in CHN2.
    pose proof LM2 as (IM2 & MFx & _ & _ & EX2 & _ & _ & FIT2 & GM2 & _). pose proof STP as (F1 & _). rewrite F1 in MFx.
    assert (LEN16 : length (es_slots (mid_E M')) = 16%nat) by (destruct (mid_err M') as [|c0]; cbn [ERRX] in EX2; [rewrite EX2; reflexivity| exact (proj1 (proj1 EX2))]).
    pose proof (errst_fits_bounds _ LEN16 FIT2) as [EC_ EB_]. pose proof (newlib_err_bounds _ _ _ _ CX STP NW) as (NB_ & NC_ & _).
    pose proof (errph_nonneg (mid_err M')) as [EHB EHC].
    set (Lcur := mid_errblocks M' ++ LBN ++ [] ++ (p, A, VPM_SIZE) :: LB) in *.
    eapply (ah_seq H HH).
    { eapply (aadd1host_spec H HHx (HHx_slack_law H HHx)) with (lo := lo) (B := B) (LB := Lcur) (s := s') (a := A) (name := en_pname E) (V := vpm_empty p) (pn := pn) (ns := ns) (slack := sl2) (errv := errv')
        (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS3| ..]; try reflexivity.
      all: lazymatch goal with
           | |- VPMobj _ _ _ _ => destruct VO2 as (VC & VIN & HO); split; [exact VC| split; [subst Lcur; do 3 (apply in_or_app; right); left; reflexivity| exact HO]]
           | |- A + VPM_SIZE <= lo => clear - AH CEIL; lia
           | |- In _ _ => subst Lcur; do 3 (apply in_or_app; right); right; unfold zlength; exact PNIN
           | |- bytes_at _ _ _ _ => exact CS2
           | |- ~ In _ _ => exact NONUL
           | |- 1 <= zlength ns <= 255 => exact NSL
           | |- _ mod 8 <= zlength _ => unfold zlength; exact PAD2
           | |- VPM_shad _ _ _ => exact VSH2
           | |- accessible _ _ _ => unfold zlength; exact ACCP2
           | |- as_RHEAP _ _ _ _ => subst Lcur; exact HP2
           | |- as_AKREL _ _ _ => exact KREL3
           | |- lb_bytes _ + _ <= _ => subst Lcur; change (mid_errblocks M') with (blocks_ERRST (mid_E M')); rewrite !lb_bytes_app, lb_bytes_cons in *; cbn [blk_size snd lb_bytes fold_right] in *;
                                       clear - BY EB_ NB_ EHB LBE0; unfold FCC_BYTES, ADD1HOST_BYTES, ERRSTR_BYTES, VPM_SIZE, SK_SIZE in *; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lcur; change (mid_errblocks M') with (blocks_ERRST (mid_E M')); rewrite !length_app in *; cbn [length app] in *; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ, ?Nat2Z.inj_add in *;
                                               clear - CN EC_ NC_ EHC; unfold FCC_CNT, ERRSTR_CNT in *; change (@length (bptr * Z * Z) LB) with (@length block LB) in *; lia
           | |- as_rauxv_ok _ _ _ => exact AUX2
           | |- bv_unsigned _ <= B => rewrite ?unsigned_lit by lia; clear - SPB SPR; lia
           | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST2
           | |- aceil <= lo => exact CEIL
           | |- _ <= _ - ADD1HOST_STACK => rewrite ?unsigned_lit by lia; clear - LO; unfold FCC_STACK, FR_ech_final_config_checks in LO;
                                          pose proof (Z.le_max_l ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)); pose proof (Z.le_max_l (Z.max ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) (Z.max (SUITECHECK_STACK (mid_err M)) FCC_ICPT_STACK)); lia
           | |- stack0 _ _ _ => rewrite ?unsigned_lit by lia; eapply stack0_sub; [exact SK02| lia| clear - LO8K SPR; lia| clear - SPA SPR; Z.div_mod_to_equations; lia]
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR2
           | |- mem_inv _ _ => exact MI2
           | |- tp = _ => exact TP
           | |- _ mod 16 = 0 => rewrite ?unsigned_lit by lia; clear - SPA SPR; replace (bv_unsigned sp + -128) with (bv_unsigned sp - 8 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- ACONST _ => exact AC2
           | |- as_chain _ _ _ _ => rewrite ?unsigned_lit by lia; exact CHN2
           | |- forall fp' ra', In _ _ -> _ => rewrite ?unsigned_lit by lia; intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => unfold AFC_R8; rewrite ?unsigned_lit by lia; eapply pf_ok_call; [exact PF|]; unfold PF_fcc, R_fcc_add1_host; intros y Hy; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hy
           | |- ADD1HOST_COST _ <= as_AL _ _ => pose proof (aCf_pos H HH (VPM_SIZE + ADD1HOST_BYTES) ltac:(unfold VPM_SIZE, ADD1HOST_BYTES, SK_SIZE; lia)); pose proof (SPENT_le_COST M' (en_nsuites E) STP) as SLC; clear - SPT1 HAL0 AL0 AL1 H0 SLC; lia
           | |- MEMFLAG _ _ => exact MFx
           | |- IMPL_mem _ => exact IM2
           | |- GOT_mem _ => exact GM2
           | |- _ mod 2 = 0 => unfold AFC_R8; rewrite ?unsigned_lit by lia; reflexivity
           | |- ?G => idtac "A1HPRE" G
           end.
      all: fail "A1HPRE". }
    intros [ms4 mo4] PO. unfold add1host_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & errv4 & s4' & V' & NB &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & VO4 & VID4 & VP4 & _ & _ & NB1' & NB2' & VSH4 & SK04 & MF4 & _ & _ & AL4).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in XP4 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4.
    cbn [vp_id vpm_empty] in VID4, VP4.
    pose proof (fworld_after_add1host _ _ _ _ _ _ _ _ _ _ _ _ FW2 MI4 AC4 ST4 AUX4 ERR4 XP4 HP4 VO4 VID4 VP4 NB1' NB2' VSH4 MF4 AL4) as FW4.
    (* [comment removed for export] *)
    eapply fcc_name2 with (r := if hostname_ok ns then 1 else 0); [exact FW4| destruct (hostname_ok ns); [right| left]; reflexivity| exact SPT1| exact KREL4| exact MPc4| exact VIS4].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_main : forall (rax s2x a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) m s' errv msF mo',
    fworld m s' M [] errv (vpm_empty p) [] [] (as_Cm H VPM_SIZE) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF = L1ms 0 rax s2x (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m ->
    as_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee E lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros rax s2x a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m s' errv msF mo' FW KREL MP VIS.
    pose proof RC_pos as RP.
    assert (AC0 : 0 <= ADD1HOST_COST H).
    { unfold ADD1HOST_COST. pose proof (aCm_pos H HH XBUF_SIZE ltac:(unfold XBUF_SIZE; lia)). pose proof (aCm_pos H HH 256 ltac:(lia)). pose proof (aCm_pos H HH SK_SIZE ltac:(unfold SK_SIZE; lia)).
      pose proof (aCm_pos H HH 32 ltac:(lia)). rewrite (aCf0 H HH). lia. }
    eapply (ah_seq H HH); [eapply (L1_loop (Z.to_nat (en_nsuites E)) 0); [rewrite Z2Nat.id by lia; lia| lia| exact FW| cbv delta [RC]; clear; lia| exact KREL| exact MP| exact VIS]|].
    intros [ms2 mo2] EX. unfold L1exit in EX. cbn [cfg_ms cfg_model] in EX.
    destruct EX as (w & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & aead & j & m2 & s2' & M2 & LBN2 & errv2 & XS2 & spent2 & FW2 & SP2 & KREL2 & MP2 & [VIS2 | VIS2]).
    - (* [comment removed for export] *)
      eapply fcc_raise_fail; [left; split; reflexivity| exact FW2| unfold FCC_COST; clear - SP2 AC0; lia| exact KREL2| exact MP2| exact VIS2].
    - (* [comment removed for export] *)
      eapply (ah_seq H HH); [eapply fcc_good; [exact FW2| exact SP2| exact KREL2| exact MP2| exact VIS2]|].
      intros [ms3 mo3] EX. unfold NAMEexit in EX. cbn [cfg_ms cfg_model] in EX.
      destruct EX as (rax3 & x1 & x2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x3 & x4 & x5 & x7 & x8 & x9 & x10 & x11 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & m3 & s3' & M3 & LBN3 & errv3 & XS3 & spent3 & FW3 & SP3 & KREL3 & MP3 & [VIS3 | VIS3]).
      + eapply fcc_name1; [exact FW3| exact SP3| exact KREL3| exact MP3| exact VIS3].
      + eapply fcc_raise_fail; [right; split; reflexivity| exact FW3| unfold FCC_COST; clear - SP3 AC0; lia| exact KREL3| exact MP3| exact VIS3].
  Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Hypothesis SPN : strspn_icpt_stmt.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Theorem afcc_spec : fcc_stmt H.
  Proof using HHx RAISE SPN.
    unfold fcc_stmt. intros until slack.
    intros VIS A0 EO NSR SUO SU ROWS SNR ROK PNO PN NONUL NSL PAD BEL ESH LM LIBSUB CX MF0 IDS HP KREL BY CN AUX SPB BHI SPA ST CEIL LO SK0 ERR MI TP AC CLOSED RFS LFB ATHR CHN0 CHS PF HAL0 RAE.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO8K : lo + 8768 <= bv_unsigned sp).
    { clear - LO. unfold FCC_STACK, FR_ech_final_config_checks in LO.
      pose proof (Z.le_max_l ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) as K1.
      pose proof (Z.le_max_l (Z.max ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) (Z.max (SUITECHECK_STACK (mid_err M)) FCC_ICPT_STACK)) as K2.
      assert (A1 : ADD1HOST_STACK = 8640) by reflexivity. lia. }
    set (L0 := mid_errblocks M ++ LB) in *.
    assert (HB : forall b, In b L0 -> 0 < blk_addr b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    assert (SUBLB : forall b, In b LB -> In b L0) by (intros b Hb; subst L0; apply in_or_app; right; exact Hb).
    assert (SUB0 : forall b, In b LIB -> In b L0) by (intros b Hb; apply SUBLB, LIBSUB; exact Hb).
    assert (LBE0 : 0 <= lb_bytes (mid_errblocks M)).
    { subst L0. clear - HB. induction (mid_errblocks M) as [|b bs IH]; [cbn; lia|]. rewrite lb_bytes_cons. pose proof (HB b ltac:(left; reflexivity)) as (_ & _ & _ & B4 & _).
      specialize (IH ltac:(intros b' Hb'; apply HB; right; exact Hb')). lia. }
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC) & EIN & O1 & O2 & O3 & O4 & XT).
    pose proof (HB _ (SUBLB _ EIN)) as (EP0 & _ & EH & _). cbn [blk_addr blk_size fst snd] in EP0, EH. unfold ENTRY_SIZE in EH.
    assert (EAL : ee mod 8 = 0).
    { pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ EIN)) as (_ & AL16 & _). cbn [blk_addr blk_size fst snd] in AL16. clear - AL16. Z.div_mod_to_equations. lia. }
    pose proof ESH as (ETOP & EAD & _). pose proof (ACONST_shbase m AC) as [GSB SHB0].
    pose proof LM as (IM0 & MFL0 & _ & _ & _ & _ & _ & _ & GM0 & _). rewrite MF0 in MFL0.
    pose proof PN as PNq. change (ns ++ Z_to_bv 8 0 :: slack) with (ns ++ [Z_to_bv 8 0] ++ slack) in PNq. rewrite app_assoc in PNq. apply bytes_at_app in PNq. destruct PNq as [PN1 _].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afcc_seg1 with (lo := lo); [exact A0| exact GSB| exact SHB0| exact ST| exact CEIL| clear - LO8K; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & junk & a1' & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW1 : Forall (aclient_write_ok H L0) [(bv_unsigned sp + -128, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn; clear - CEIL LO8K; lia| apply Forall_nil]).
    assert (XP1 : forall X, xpres H L0 (bv_unsigned sp) X m m1).
    { intros X. eapply (xpres_of_munch H); [exact HH| exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; clear - CEIL LO8K SPR; lia| apply Forall_nil]. }
    assert (XPL1 : forall X, xpres H LB (bv_unsigned sp) X m m1) by (intros X; eapply (xpres_weaken H); [apply XP1| apply Z.le_refl| exact SUBLB| intros q Hq; exact Hq]).
    assert (HP1 : as_RHEAP H s L0 m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
    { rewrite TP in ERR |- *. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite unsigned_lit by (unfold ATP; lia). cbn. unfold ATP. clear - CEIL LO8K ACEILB. lia. }
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]; apply Forall_cons; [apply aconst_ok_hi; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]).
    assert (LM1 : LIBMID LIB m1 M) by (eapply (LIBMID_xpres0 H); [exact LM| exact CX| apply (XP1 [])| exact SUB0| intros b Hb; subst L0; apply in_or_app; left; exact Hb]).
    pose proof LM1 as (IM1 & MF1 & _ & _ & _ & _ & _ & _ & GM1 & _). rewrite MF0 in MF1.
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { assert (C0 : as_chain H m1 (bv_unsigned s0) CH) by (eapply (chain_via_xpres_off H HH); [exact CHN0| apply (XPL1 [])| exact CHS| apply Forall_nil]).
      eapply (ah_chain_cons H HH); [exact C0| lia| lia| exact SPA| clear - CEIL LO8K; lia| lia|].
      apply (proj1 (rw_cells_app asegs _ _ ([CB 24 junk] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]) _)) in FR1.
      destruct FR1 as [_ FR2]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ app] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -128 + 112) by lia. rewrite !Z_to_bv_bv_unsigned. exact FR2. }
    (* [comment removed for export] *)
    pose proof (avpmnew_spec H HH) as VN. unfold vpmnew_stmt in VN.
    eapply (ah_seq H HH).
    { eapply VN with (lo := lo) (B := B) (LB := L0) (s := s) (v := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP1| exact KREL1| exact AUX1| exact ST1| exact CEIL| exact MI1| exact MF1| exact IM1| exact GM1| exact ERR1| exact TP| exact AC1| exact CHN1].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => subst L0; unfold FCC_BYTES, VPM_SIZE, SK_SIZE, ERRSTR_BYTES in *; pose proof (errph_nonneg (mid_err M)) as [EB0 _]; clear - BY EB0; lia
           | |- Z.of_nat (length _) + _ <= _ => subst L0; unfold FCC_CNT, ERRSTR_CNT in *; pose proof (errph_nonneg (mid_err M)) as [_ EC0]; clear - CN EC0; lia
           | |- _ + -128 <= _ => clear - SPB SPR; lia
           | |- _ <= _ - VPMNEW_STACK => change VPMNEW_STACK with 8304; clear - LO8K; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -128) with (bv_unsigned sp - 8 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => unfold AFC_R1; eapply pf_ok_call; [exact PF|]; unfold PF_fcc, R_fcc_X509_VERIFY_PARAM_new; intros y Hy; apply in_app_iff; left; exact Hy
           | |- as_Cm _ _ <= as_AL _ _ => unfold FCC_COST in HAL0; pose proof (aCf_pos H HH (VPM_SIZE + ADD1HOST_BYTES) ltac:(unfold VPM_SIZE, ADD1HOST_BYTES, SK_SIZE; lia));
                                        pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; pose proof (errph_nonneg (mid_err M)); lia));
                                        pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; pose proof (errph_nonneg (mid_err M)); lia));
                                        assert (AC0 : 0 <= ADD1HOST_COST H) by (unfold ADD1HOST_COST; pose proof (aCm_pos H HH XBUF_SIZE ltac:(unfold XBUF_SIZE; lia)); pose proof (aCm_pos H HH 256 ltac:(lia)); pose proof (aCm_pos H HH SK_SIZE ltac:(unfold SK_SIZE; lia));
                                          pose proof (aCm_pos H HH 32 ltac:(lia)); rewrite (aCf0 H HH); lia);
                                        unfold RAISE_COST in HAL0; assert (RRP : 0 <= RCR H) by (unfold RCR; pose proof (aCm_pos H HH ERRDEBUG_BYTES ltac:(unfold ERRDEBUG_BYTES; lia)); pose proof (aCf_pos H HH ERRDEBUG_BYTES ltac:(unfold ERRDEBUG_BYTES; lia)); lia); clear - HAL0 H0 H1 H2 AC0 NSR RRP; nia
           | |- _ mod 2 = 0 => unfold AFC_R1; reflexivity
           | |- ?G => idtac "VNPRE" G
           end.
      all: fail "VNPRE". }
    clear VN. intros [ms2 mo2] PO. unfold vpmnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & VBR & HP2 & VO2 & VSH2 & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST2, XP2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MP1 MP2) as MPc2.
    pose proof VBR as (AP & _ & _ & A4 & AH & AFS & AAP).
    (* [comment removed for export] *)
    assert (AVM : forall b, In b L0 -> avoids memflag_foot (blk_addr b) (blk_size b) /\ shavoids memflag_foot (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (HB _ Hb) as (_ & B4 & _ & B3 & B7). split; [apply avoids_memflag; exact B4| apply shavoids_memflag; [exact B7| exact B3]]. }
    assert (XPL2 : xpres H LB (bv_unsigned sp + -128) memflag_foot m1 m2) by (eapply (xpres_weaken H); [exact XP2| lia| exact SUBLB| auto]).
    assert (EO1 : ENTRYobj LB m1 ee E).
    { eapply (ENTRYobj_frame_law H LB LB m m1); [exact EO| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| apply (XPL1 [])|].
      intros b Hb. pose proof (HB _ (SUBLB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))) as (_ & _ & K5 & _). clear - K5 CEIL LO8K. lia. }
    assert (ESH1 : ENTRY_shad m1 ee E).
    { eapply (ENTRY_shad_frame_law H LB m m1); [exact ESH| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| apply (XPL1 [])|].
      intros b Hb. pose proof (HB _ (SUBLB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))) as (_ & _ & K5 & _). clear - K5 CEIL LO8K. lia. }
    assert (EO2 : ENTRYobj LB m2 ee E) by (eapply ENTRYobj_frameX with (L0 := LB); [exact EO1| exact XPL2| intros b Hb; exact (proj1 (AVM _ (SUBLB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))))]).
    assert (ESH2 : ENTRY_shad m2 ee E).
    { eapply ENTRY_shad_frameX with (L0 := LB); [exact ESH1| exact EO1| exact XPL2|]. intros b Hb. split; [exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact (AVM _ (SUBLB _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb)))]. }
    pose proof EO2 as ((qad1 & qad2 & qad3 & qad4 & _ & _ & _ & _ & EC2) & _). pose proof ESH2 as (_ & EAD2 & _).
    assert (FR1' : rw_cells asegs m2 (bv_unsigned sp + -128) ([CB 24 junk] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { eapply (xpres_rw_cells' H); [exact XP2| exact FR1| left; lia|]. unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]. }
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afcc_seg2 with (ee := ee) (E := E);
      [exact EC2| exact NSR| clear - AP AH ACEILB; unfold VPM_SIZE in *; lia| lia| exact EAL| exact ETOP| eapply addressable_accessible; [exact EAD2| lia| lia| exact ETOP]| exact FR1'| clear - CEIL LO8K; lia| clear - EH CEIL LO8K; unfold ENTRY_SIZE; lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & FR3). pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    (* [comment removed for export] *)
    set (L2v := (p, A, VPM_SIZE) :: L0) in HP2.
    assert (HB2 : forall b, In b L2v -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP2 Hb) as (_ & _ & _ & _ & B5 & _). exact B5. }
    assert (W3 : Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= bv_unsigned sp) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (@nil (Z * Z)) a)) [(bv_unsigned sp + -128, bv_unsigned sp + -104)]).
    { apply Forall_cons; [left; cbn; clear - CEIL LO8K SPR; lia| apply Forall_nil]. }
    assert (XP3 : xpres H L2v (bv_unsigned sp) [] m2 m3) by (eapply (xpres_of_munch H); [exact HH| exact HP2| exact MU3| exact WM3| exact W3]).
    assert (SUBL2 : forall b, In b LB -> In b L2v) by (intros b Hb; subst L2v; right; apply SUBLB; exact Hb).
    assert (XPL3 : xpres H LB (bv_unsigned sp) [] m2 m3) by (eapply (xpres_weaken H); [exact XP3| apply Z.le_refl| exact SUBL2| auto]).
    assert (CW3 : Forall (aclient_write_ok H L2v) [(bv_unsigned sp + -128, bv_unsigned sp + -104)]) by (apply Forall_cons; [left; cbn; clear - CEIL LO8K; lia| apply Forall_nil]).
    assert (WE3 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned sp + -128, bv_unsigned sp + -104)]).
    { apply Forall_cons; [right; cbn; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]. }
    pose proof O1 as O1'. pose proof O3 as O3'. rewrite SUO in O3'. rewrite PNO in O1'. cbn [ofield] in O1', O3'.
    destruct O1' as (PNP & _ & PNIN). destruct O3' as (SUP & _ & SUIN). pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ.
    pose proof (HB _ (SUBLB _ SUIN)) as (_ & _ & S5 & _). pose proof (HB _ (SUBLB _ PNIN)) as (_ & _ & P5 & _). cbn [blk_addr blk_size fst snd] in S5, P5.
    pose proof (bytes_at_bound _ _ _ _ PN1) as PNB. rewrite length_app in PNB. cbn [length] in PNB. unfold zlength in *.
    eapply (fcc_main H HHx RAISE SPN); try eassumption; try exact LBE0.
    all: lazymatch goal with |- as_MPRES _ _ _ => exact MPc3 | |- as_AKREL _ _ _ => exact KREL3 | |- as_VIS _ _ _ = _ => exact VIS3 | |- _ => idtac end.
    { unfold fworld. repeat match goal with |- _ /\ _ => split end.
      all: lazymatch goal with
           | |- mem_inv _ _ => exact MI3
           | |- ACONST _ => eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|]; apply Forall_cons; [apply aconst_ok_hi; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]
           | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]
           | |- rw_cells _ _ (bv_unsigned _ + -128) _ => exact FR3
           | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in ERR2 |- *; eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; rewrite unsigned_lit by (unfold ATP; lia); cbn; unfold ATP; clear - CEIL LO8K ACEILB; lia
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]
           | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [| exact MU3| exact WM3|]; [eapply (HHx_rheap_perm H HHx); [exact HP2| subst L2v L0; cbn [app]; apply Permutation_middle]|];
                                  apply Forall_cons; [left; cbn; clear - CEIL LO8K; lia| apply Forall_nil]
           | |- LIBMID _ _ _ => cbn [app]; assert (MS0 : mid_step M M) by (unfold mid_step; split; [exact MF0|]; split; [auto|]; split; auto);
                                rewrite <- (M_eq1' M M MS0);
                                eapply (LIBMID_xpres0 H); [| exact CX| exact XP3| intros b Hb; subst L2v; right; apply SUB0; exact Hb| intros b Hb; subst L2v L0; right; apply in_or_app; left; exact Hb];
                                eapply (LIBMID_mf H HH s m LIB L0 (bv_unsigned sp + -128) m1 m2 M x); [exact HP| exact LM1| exact CX| exact XP2| exact SUB0| intros b Hb; subst L0; apply in_or_app; left; exact Hb| exact MF2]
           | |- mid_step _ _ => unfold mid_step; split; [exact MF0|]; split; [auto|]; split; auto
           | |- mid_newlib_ok _ _ _ => unfold mid_newlib_ok; exists [], []; split; [apply Permutation_refl|]; rewrite CX; split; [reflexivity|]; destruct (mid_err M); reflexivity
           | |- mid_ctx _ = _ => reflexivity
           | |- mid_vdso _ = _ => reflexivity
           | |- ENTRYobj _ _ _ _ => eapply (ENTRYobj_frame_law H LB LB m2 m3); [exact EO2| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact XPL3| intros b Hb; pose proof (HB2 _ (SUBL2 _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))) as K5; clear - K5 CEIL LO8K; lia]
           | |- ENTRY_shad _ _ _ => eapply (ENTRY_shad_frame_law H LB m2 m3); [exact ESH2| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| exact XPL3| intros b Hb; pose proof (HB2 _ (SUBL2 _ (ENTRYobj_owned_law _ _ _ _ EO _ Hb))) as K5; clear - K5 CEIL LO8K; lia]
           | |- rw_cells _ _ (en_suites _) _ =>
               eapply rw_cells_transport; [| exact MU3| exact WM3| cbn; clear - S5 SSZ SNR CEIL LO8K; lia];
               eapply (xpres_rw_cells' H); [exact XPL2| eapply rw_cells_transport; [exact SU| exact MU1| exact WM1| cbn; clear - S5 SSZ SNR CEIL LO8K; lia]| |];
               [ right; right; left; exists (ps, en_suites E, sn); split; [exact SUIN|]; cbn [blk_addr blk_size fst snd]; lia
               | eapply avoids_sub; [exact (proj1 (AVM _ (SUBLB _ SUIN)))| cbn; lia| cbn [blk_addr blk_size fst snd]; lia] ]
           | |- bytes_at _ _ (en_pname _) _ =>
               eapply bytes_at_transport; [| exact MU3| rewrite length_app; cbn; clear - P5 CEIL LO8K; lia];
               eapply (xpres_bytes_at' H); [exact XPL2| eapply bytes_at_transport; [exact PN1| exact MU1| rewrite length_app; cbn; clear - P5 CEIL LO8K; lia]| |];
               [ right; right; left; exists (pn, en_pname E, Z.of_nat (length ns) + 1); split; [exact PNIN|]; cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia
               | eapply avoids_sub; [exact (proj1 (AVM _ (SUBLB _ PNIN)))| cbn; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia] ]
           | |- VPMobj _ _ _ _ => destruct VO2 as (VC & VIN & HO); split; [eapply rw_cells_transport; [exact VC| exact MU3| exact WM3| unfold vpm_cells; cbn [cells_size csize Nat.add]; cbn; clear - AH CEIL LO8K; unfold VPM_SIZE in *; lia]| split; [left; reflexivity| exact HO]]
           | |- VPM_shad _ _ _ => destruct VSH2 as (VT & VAD & VHS); split; [exact VT|]; split; [eapply addressable_acrossW; [exact VAD| exact MU3| exact WM3| clear - AP VT; unfold AAPP_HI, VPM_SIZE in *; lia| exact VT| exact WE3]| exact VHS]
           | |- vp_id _ = _ => reflexivity
           | |- Permutation _ _ => apply Permutation_refl
           | |- Z.of_nat (length []) <= _ => cbn; lia
           | |- lb_bytes [] <= _ => unfold ADD1HOST_BYTES, SK_SIZE; cbn; lia
           | |- stack0 _ _ _ =>
               eapply stack0_transport; [| exact MU3| exact WM3| apply Forall_cons; [left; cbn [fst snd]; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]];
               eapply (stack0_xpres H); [exact XPL2| | unfold memflag_foot, A_mem_inited; apply Forall_cons; [right; cbn [fst snd]; unfold sh; rewrite ASHADOW_BASE_val; clear - ACEILB; Z.div_mod_to_equations; lia| apply Forall_nil]];
               eapply stack0_transport; [exact SK0| exact MU1| exact WM1| apply Forall_cons; [left; cbn [fst snd]; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]]
           | |- as_RFS _ _ _ => eapply (RFS_via_xpres H HH); [| exact XPL3| apply Forall_nil]; eapply (RFS_via_xpres H HH); [| exact XPL2| unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP; apply Forall_cons; [cbn; lia| apply Forall_nil]];
                                 eapply (RFS_via_xpres H HH); [exact RFS| apply (XPL1 [])| apply Forall_nil]
           | |- Forall (fs_scratch _ _) _ => apply Forall_nil
           | |- xpres _ _ _ _ _ _ =>
               eapply (xpres_X_mono H LB (bv_unsigned sp) []); [| intros q Hq; destruct Hq];
               eapply (xpres_trans H); [apply (XPL1 [])|]; eapply (xpres_trans H); [| exact XPL3];
               eapply (xpres_weaken H LB LB (bv_unsigned sp + -128) (bv_unsigned sp) [] []); [| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; exact Hq];
               change (@nil (Z * Z)) with (@nil (Z * Z) ++ @nil (Z * Z)); eapply (axpres_drop_memflag H LB _ [] []); [exact MF1| exact MF2| cbn [app]; exact XPL2]
           | |- 0 <= as_Cm _ _ => apply (aCm_pos H HH); unfold VPM_SIZE; lia
           | |- as_AL _ _ + _ >= _ => clear - AL2; lia
           | |- ?G => idtac "FW0" G
           end.
      all: fail "FW0". }
  Qed.
End WS.
