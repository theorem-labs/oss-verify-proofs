(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_LibMid ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_frame2
     ECH_C4_egs ECH_C4_raise ECH_Rostr ECH_C5_stmt ECH_C5_small ECH_C11_stmt ECH_C11_find ECH_C11_suitebad ECH_C12_stmt ECH_C12_new ECH_C12_vpmfree ECH_C12_add1host
     ECH_C13_stmt ECH_C13_ext ECH_C13_entry ECH_C13_store ECH_C14_stmt ECH_KitSeg F_strlen F_strrchr F_strspn ECH_C14_fcc_seg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma suite_cells_app : forall r1 r2, suite_cells (r1 ++ r2) = suite_cells r1 ++ suite_cells r2.
Proof. induction r1 as [|[[k d] a] r1 IH]; intros r2; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
(* [comment removed for export] *)
Lemma suite_row_at : forall m S rows i kem kdf aead,
  rw_cells rsegs m S (suite_cells rows) -> nth_error rows (Z.to_nat i) = Some (kem, kdf, aead) -> 0 <= i ->
  rw_cells rsegs m (S + 6 * i) [C2 (wz kem); C2 (wz kdf); C2 (wz aead)].
Proof.
  intros m S rows i kem kdf aead RC NTH I0.
  destruct (@nth_error_split _ rows (Z.to_nat i) (kem, kdf, aead) NTH) as (l1 & l2 & EQ & L1). subst rows.
  rewrite suite_cells_app in RC. apply rw_cells_app in RC. destruct RC as [_ RC]. cbn [suite_cells app] in RC.
  change (C2 (wz kem) :: C2 (wz kdf) :: C2 (wz aead) :: suite_cells l2) with ([C2 (wz kem); C2 (wz kdf); C2 (wz aead)] ++ suite_cells l2) in RC.
  apply rw_cells_app in RC. destruct RC as [RC _]. pose proof (suite_cells_size l1) as SZ. unfold zlength in SZ. rewrite L1, Z2Nat.id in SZ by lia.
  replace (S + 6 * i) with (S + Z.of_nat (cells_size (suite_cells l1))) by lia. exact RC.
Qed.

(* [comment removed for export] *)
Lemma newlib_err_bounds : forall M M' LBN x, mid_ctx M = CtxReady x -> mid_step M M' -> mid_newlib_ok M M' LBN ->
  lb_bytes LBN + errph_bytes (mid_err M') <= errph_bytes (mid_err M) /\ Z.of_nat (length LBN) + errph_cnt (mid_err M') <= errph_cnt (mid_err M)
  /\ lb_big LBN + errph_big (mid_err M') <= errph_big (mid_err M) /\ lb_big LBN <= 1.
Proof.
  intros [f cph eph E v] [f' cph' eph' E' v'] LBN x CX ST NW. unfold mid_step, mid_newlib_ok in *.
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. subst cph. destruct ST as (_ & SC & SE & _). destruct NW as (LA & LE & P & C & R).
  assert (LA0 : LA = []) by (destruct cph' as [|b']; [exact C| pose proof (SC x eq_refl) as K; injection K as <-; exact C]).
  subst LA. cbn [app] in P.
  rewrite (lb_bytes_perm _ _ P), (lb_big_perm _ _ P), (Permutation_length P).
  destruct eph as [|c].
  - destruct eph' as [|c']; cbn [errph_delta errph_bytes errph_cnt errph_big] in R |- *.
    + subst LE. cbn. unfold ERRINIT_BYTES, ERRINIT_CNT, ERRINIT_BIG. lia.
    + unfold ERRINIT_BIG. lia.
  - cbn in R. subst LE. rewrite (SE c eq_refl). cbn. lia.
Qed.

(* [comment removed for export] *)
Definition avoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) X.
Lemma avoids_sub : forall X a n a' n', avoids X a n -> a <= a' -> a' + n' <= a + n -> avoids X a' n'.
Proof. intros X a n a' n' AV H1 H2. unfold avoids in *. eapply Forall_impl; [| exact AV]. cbn beta. intros [u v] K. cbn in *. lia. Qed.
Lemma avoids_nil : forall a n, avoids [] a n.
Proof. intros. constructor. Qed.

Section FX.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma xpres_drop_memflag : forall L SP X1 X2 m m',
    MEMFLAG m 1 -> MEMFLAG m' 1 -> xpres L SP (X1 ++ memflag_foot ++ X2) m m' -> xpres L SP (X1 ++ X2) m m'.
  Proof.
    intros L SP X1 X2 m m' MF MF' XP a Ha [HC HX].
    destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; assumption|].
    apply XP; [exact Ha|]. split; [exact HC|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [apply HX; apply rin_ivs_app; left; exact K|].
    apply rin_ivs_app in K. destruct K as [K|K]; [| apply HX; apply rin_ivs_app; right; exact K].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia.
  Qed.

  (* [comment removed for export] *)
  Definition EF (ph : errphase) : list (Z * Z) := ERR_X ++ errph_foot ph.

  Lemma avoids_EF : forall ph a n,
    (a + n <= IMG_LO \/ IMG_HI <= a) ->
    (forall c, ph = ErrReady c -> a + n <= blk_addr (ec_es c) \/ blk_addr (ec_es c) + ERRST_SIZE <= a) ->
    avoids (EF ph) a n.
  Proof.
    intros ph a n OFF ES. unfold avoids, EF. apply Forall_app. split.
    - unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      unfold IMG_LO, IMG_HI in OFF. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - destruct ph as [|c]; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn. pose proof (ES c eq_refl). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_shrink : forall L L' SP SP' X Y m m',
    xpres L SP (X ++ Y) m m' -> SP <= SP' -> (forall b, In b L' -> In b L) ->
    (forall a, rin_ivs Y a -> xclient L' SP' X a -> False) -> xpres L' SP' X m m'.
  Proof.
    intros L L' SP SP' X Y m m' XP HS HL HY a Ha HC. apply XP; [exact Ha|]. destruct HC as [HR HX]. split.
    - destruct HR as [K|[K|(b & Hb & Hr)]]; [left; lia| right; left; exact K| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
    - intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (HX K)|]. apply (HY a K). split; [exact HR| exact HX].
  Qed.

  (* [comment removed for export] *)
  Lemma EXTobj_frameX : forall L0 SP X m m' p E,
    EXTobj L0 m p E -> xpres L0 SP X m m' -> (forall b, In b (blocks_EXT p E) -> avoids X (blk_addr b) (blk_size b)) -> EXTobj L0 m' p E.
  Proof.
    intros L0 SP X m m' p E ((pad & PL & HC) & HIN & OF) XP K.
    pose proof (K _ ltac:(left; reflexivity)) as A1. cbn [blk_addr blk_size fst snd] in A1.
    split; [| split; [exact HIN| exact OF]]. exists pad. split; [exact PL|].
    eapply xpres_rw_cells'; [exact XP| exact HC| |].
    - right; right. exists (ex_id E, p, EXT_SIZE). split; [exact HIN|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold EXT_SIZE. lia.
    - unfold ext_cells. cbn [cells_size csize Nat.add]. exact A1.
  Qed.
  Lemma EXTs_frameX : forall L0 SP X m m' ps es,
    Forall2 (fun p E => EXTobj L0 m p E) ps es -> xpres L0 SP X m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> avoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun p E => EXTobj L0 m' p E) ps es.
  Proof.
    intros L0 SP X m m' ps es F2. induction F2 as [|p E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply EXTobj_frameX; [exact HE| exact XP|]. intros b Hb. apply K. apply in_or_app. left. exact Hb.
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.
  (* [comment removed for export] *)
  Lemma ENTRYobj_frameX : forall L0 SP X m m' a E,
    ENTRYobj L0 m a E -> xpres L0 SP X m m' -> (forall b, In b (blocks_ENTRY a E) -> avoids X (blk_addr b) (blk_size b)) -> ENTRYobj L0 m' a E.
  Proof.
    intros L0 SP X m m' a E EO XP K.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & HIN & O1 & O2 & O3 & O4 & XS).
    pose proof (K _ ltac:(left; reflexivity)) as A0. cbn [blk_addr blk_size fst snd] in A0.
    unfold ENTRYobj. split.
    { exists pad1, pad2, pad3, pad4. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
      eapply xpres_rw_cells'; [exact XP| exact HC| |].
      - right; right. exists (en_id E, a, ENTRY_SIZE). split; [exact HIN|]. unfold entry_cells.
        cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia.
      - unfold entry_cells. cbn [cells_size csize Nat.add]. exact A0. }
    split; [exact HIN|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
    assert (KX : forall b, In b (blocks_EXTS (en_exts E) (en_exts_o E)) -> avoids X (blk_addr b) (blk_size b))
      by (intros b Hb; apply K; unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb).
    clear K. revert XS KX. unfold EXTS, blocks_EXTS. destruct (en_exts_o E) as [[K es]|]; intros XS KX; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply SKobj_frameX; [exact SO| intros b Hb; eapply SKobj_owned; [exact SO| exact Hb]| exact XP|].
      intros b Hb. apply KX. apply in_or_app. left. exact Hb.
    - split; [exact LEN|]. eapply EXTs_frameX; [exact F2| exact XP|]. intros b Hb. apply KX. apply in_or_app. right. exact Hb.
  Qed.
  (* [comment removed for export] *)
  Lemma VPMobj_frameX : forall L0 SP X m m' a pid,
    VPMobj L0 m a (vpm_empty pid) -> xpres L0 SP X m m' -> avoids X a VPM_SIZE -> VPMobj L0 m' a (vpm_empty pid).
  Proof.
    intros L0 SP X m m' a pid (VC & VIN & HOS) XP AV. split; [| split; [exact VIN| exact HOS]].
    eapply xpres_rw_cells'; [exact XP| exact VC| |].
    - right; right. exists (pid, a, VPM_SIZE). split; [exact VIN|]. unfold vpm_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold VPM_SIZE. lia.
    - unfold vpm_cells. cbn [cells_size csize Nat.add]. exact AV.
  Qed.
  (* [comment removed for export] *)
  Lemma SKobj_relist : forall L L' m a K, SKobj L m a K -> (forall b, In b (blocks_SK a K) -> In b L') -> SKobj L' m a K.
  Proof.
    intros L L' m a K (HC & POS & HIN & NC & CAP & SRT & EL & DAT) KEEP. unfold SKobj.
    split; [exact HC|]. split; [exact POS|]. split; [apply KEEP; left; reflexivity|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & JK)]; [left; exact D0| right].
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [| split; [exact AR| exact JK]].
    apply KEEP. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  Qed.
  Lemma XBUFobj_relist : forall L L' m a X, XBUFobj L m a X -> (forall b, In b (blocks_XBUF a X) -> In b L') -> XBUFobj L' m a X.
  Proof.
    intros L L' m a X (HC & HIN & P1 & P2 & DIN) KEEP. split; [exact HC|]. split; [apply KEEP; left; reflexivity|]. split; [exact P1|]. split; [exact P2|].
    apply KEEP. right. left. reflexivity.
  Qed.
  Lemma VPMobj_relist : forall L L' m a V, VPMobj L m a V -> (forall b, In b (blocks_VPM a V) -> In b L') -> VPMobj L' m a V.
  Proof.
    intros L L' m a V (VC & VIN & HOS) KEEP. split; [exact VC|]. split; [apply KEEP; left; reflexivity|].
    assert (KH : forall b, In b (blocks_HOSTS (vp_hosts V) (vp_hosts_o V)) -> In b L') by (intros b Hb; apply KEEP; right; exact Hb).
    clear KEEP. revert HOS KH. unfold HOSTS, blocks_HOSTS. destruct (vp_hosts_o V) as [[K bs]|]; intros HOS KH; [| exact HOS].
    destruct HOS as (HP0 & SO & LEN & F2). split; [exact HP0|]. split; [eapply SKobj_relist; [exact SO| intros b Hb; apply KH; apply in_or_app; left; exact Hb]|].
    split; [exact LEN|].
    assert (KX : forall b, In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs))) -> In b L') by (intros b Hb; apply KH; apply in_or_app; right; exact Hb).
    clear - F2 KX. induction F2 as [|q X qs bs' HX F IH]; constructor.
    - eapply XBUFobj_relist; [exact HX|]. intros b Hb. apply KX. cbn [combine map concat fst snd]. apply in_or_app. left. exact Hb.
    - apply IH. intros b Hb. apply KX. cbn [combine map concat fst snd]. apply in_or_app. right. exact Hb.
  Qed.

End FX.

Lemma le2_wz_mod : forall t, le2 (wz t) = le2 (wz (t mod 65536)).
Proof.
  intros t. unfold le2, wz. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  transitivity (Z_to_le_bytes 2 t); [apply Z_to_le_bytes_mod; cbn; lia|].
  transitivity (Z_to_le_bytes 2 (t mod 65536)); [| symmetry; apply Z_to_le_bytes_mod; cbn; lia].
  change 65536 with (2^16). symmetry. apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma rw_cells_C2_le2 : forall m A v v' cs, le2 v = le2 v' -> rw_cells rsegs m A (C2 v :: cs) -> rw_cells rsegs m A (C2 v' :: cs).
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

Lemma cstr_suffix : forall m A ns sl i, bytes_at rsegs m A (ns ++ Z_to_bv 8 0 :: sl) -> (i <= length ns)%nat ->
  bytes_at rsegs m (A + Z.of_nat i) (skipn i ns ++ Z_to_bv 8 0 :: sl).
Proof.
  intros m A ns sl i BS IL. rewrite <- (firstn_skipn i ns) in BS. rewrite <- app_assoc in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
  rewrite firstn_length_le in BS by exact IL. exact BS.
Qed.
Lemma nth_error_skipn' : forall {X} (l : list X) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof. intros X l n. revert l. induction n as [|n IH]; intros l i; [reflexivity|]. destruct l as [|x l]; cbn; [destruct i; reflexivity| apply IH]. Qed.

(* [comment removed for export] *)
Definition S_ECHS_FILE : list byte := Eval vm_compute in img_cstr A_ECHS_FILE 64.
Definition K_ECHS_FILE : list byte := Eval vm_compute in img_slack A_ECHS_FILE (length S_ECHS_FILE).
Definition S_FCC_FUNC : list byte := Eval vm_compute in img_cstr A_FCC_FUNC 64.
Definition K_FCC_FUNC : list byte := Eval vm_compute in img_slack A_FCC_FUNC (length S_FCC_FUNC).
Definition S_DIGITS : list byte := Eval vm_compute in img_cstr A_DIGITS 64.
Definition K_DIGITS : list byte := Eval vm_compute in img_slack A_DIGITS (length S_DIGITS).
Definition S_HEXDIGITS : list byte := Eval vm_compute in img_cstr A_HEXDIGITS 64.
Definition K_HEXDIGITS : list byte := Eval vm_compute in img_slack A_HEXDIGITS (length S_HEXDIGITS).
Section RO.
  Context {HCEIL : HeapCeil}.
  Lemma R_DIGITS : ROSTR A_DIGITS S_DIGITS K_DIGITS.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_HEXDIGITS : ROSTR A_HEXDIGITS S_HEXDIGITS K_HEXDIGITS.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma S_DIGITS_len : length S_DIGITS = 10%nat. Proof. reflexivity. Qed.
  Lemma S_HEXDIGITS_len : length S_HEXDIGITS = 22%nat. Proof. reflexivity. Qed.
  Lemma R_ECHS_FILE : ROSTR A_ECHS_FILE S_ECHS_FILE K_ECHS_FILE.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_FCC_FUNC : ROSTR A_FCC_FUNC S_FCC_FUNC K_FCC_FUNC.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma S_ECHS_FILE_len : Z.of_nat (length S_ECHS_FILE) = 19. Proof. reflexivity. Qed.
  Lemma S_FCC_FUNC_len : Z.of_nat (length S_FCC_FUNC) = 23. Proof. reflexivity. Qed.
End RO.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let SLACK : RHEAP_slack_law H := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let STATICS : statics_of_RHEAP H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (mo : Model)
            (LIB LB : list block) (M : libmid) (x : ctxinfo) (ee lo B : Z) (E : entrep)
            (rows : list (Z * Z * Z)) (ps : bptr) (sn : Z) (pn : bptr) (ns : list byte) (A : Z) (p : bptr).
  Let spq : Z := bv_unsigned sp + -80.
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
  Hypothesis BY : lb_bytes LB + errph_bytes (mid_err M) + FCC_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H.
  Hypothesis CN : Z.of_nat (length LB) + errph_cnt (mid_err M) + FCC_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H.
  Hypothesis BG : lb_big LB + errph_big (mid_err M) <= hs_LIVE_BIG_MAX H.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis BHI : B < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : hceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - FCC_STACK M.
  Let LO80 : lo + 80 <= bv_unsigned sp.
  Proof. clear - LO. unfold FCC_STACK, FR_ech_final_config_checks in LO. change RREALLOC_STACK with 8256 in LO. lia. Qed.
  Let LO8K : lo + 8656 <= bv_unsigned sp.
  Proof. clear - LO. unfold FCC_STACK, FR_ech_final_config_checks in LO. change RREALLOC_STACK with 8256 in LO. lia. Qed.
  Hypothesis TP : tp = Z_to_bv 64 RATP.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis VBR : rblock_range A VPM_SIZE.

  (* [comment removed for export] *)
  Definition fworld (m : mem) (mo' : Model) (s' : PState) (M' : libmid) (LBN : list block) (errv' : word) (V : vpmrep) (NB : list block) : Prop :=
       mem_inv rsegs m /\ stk rsegs m lo spq /\ rw_cells rsegs m spq (fcc_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells rsegs m (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m B
    /\ hs_KREL H s' mo' /\ hs_MPRES H mo mo'
    /\ hs_RHEAP H s' (mid_errblocks M' ++ LBN ++ NB ++ VB :: LB) m
    /\ LIBMID (LBN ++ LIB) m M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M /\ mid_vdso M' = mid_vdso M
    /\ ENTRYobj LB m ee E /\ rw_cells rsegs m (en_suites E) (suite_cells rows) /\ bytes_at rsegs m (en_pname E) (ns ++ [Z_to_bv 8 0])
    /\ VPMobj (NB ++ VB :: LB) m A V /\ vp_id V = p /\ Permutation (blocks_VPM A V) (VB :: NB)
    /\ Z.of_nat (length NB) <= 4 /\ lb_bytes NB <= ADD1HOST_BYTES /\ lb_big NB = 0
    /\ xpres LB (bv_unsigned sp) (EF (mid_err M)) m0 m.


  (* [comment removed for export] *)
  Lemma fworld_stk : forall m m1 mo' s' M' LBN errv' V NB W,
    fworld m mo' s' M' LBN errv' V NB -> munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo spq ->
    Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= spq) W ->
    fworld m1 mo' s' M' LBN errv' V NB.
  Proof.
    intros m m1 mo' s' M' LBN errv' V NB W
      (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & VID & VP & NB1 & NB2 & NB3 & XP0) MU WM MI1 ST1 FW.
    unfold fworld. cbv delta [spq VB] in *. hcb. pose proof (word_range sp) as SPR.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (XP : xpres (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp + -80) [] m m1).
    { eapply xpres_of_munch; [exact MU| exact WM| | exact HB]. eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. lia. }
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB))
      by (intros b Hb; do 3 (apply in_or_app; right); right; exact Hb).
    assert (XPL : xpres LB (bv_unsigned sp + -80) [] m m1) by (eapply xpres_weaken; [exact XP| lia| exact SUBLB| auto]).
    assert (XPV : xpres (NB ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp + -80) [] m m1)
      by (eapply xpres_weaken; [exact XP| lia| intros b Hb; do 2 (apply in_or_app; right); exact Hb| auto]).
    assert (DJ : forall a n, a + n <= hceil -> disjoint_from W a n).
    { intros a n Hn. clear - FW Hn CEIL. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
      split; [lia| apply IH; eapply Forall_inv_tail; exact FW]. }
    pose proof EO as (_ & EIN & O1 & O2 & O3 & O4 & XS). rewrite SUO in O3. rewrite PNO in O1. cbn [ofield] in O1, O3.
    destruct O1 as (PNP & _ & PNIN). destruct O3 as (SUP & _ & SUIN).
    pose proof (HB _ (SUBLB _ SUIN)) as SUH. pose proof (HB _ (SUBLB _ PNIN)) as PNH. cbn [blk_addr blk_size fst snd] in SUH, PNH.
    pose proof (rw_cells_bound _ _ _ _ SU) as SUB0. pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ.
    pose proof (bytes_at_bound _ _ _ _ PN) as PNB. rewrite length_app in PNB. cbn [length] in PNB. unfold zlength in *.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. clear - FW CEIL SPR HCEILB. unfold fcc_frame. cbn [cells_size csize Nat.add].
      induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact FW].
    - subst tp. rewrite errno_RATP in *. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. apply DJ. unfold RERRNO. cbn. lia.
    - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [K1 K2]. unfold RAUXV_CELL. cbn in *. lia.
    - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. lia.
    - eapply LIBMID_xpres0; [exact LM| exact XP|]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUBLB; apply LIBSUB; exact Hb].
    - eapply ENTRYobj_frameX; [exact EO| exact XPL| intros b Hb; apply avoids_nil].
    - eapply rw_cells_transport; [exact SU| exact MU| exact WM|]. apply DJ. lia.
    - eapply bytes_at_transport; [exact PN| exact MU|]. apply DJ. rewrite length_app. cbn [length]. lia.
    - (* [comment removed for export] *)
      destruct VO as (VC & VIN & HOS). split; [| split; [exact VIN|]].
      + eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. apply DJ. assert (K := HB (p, A, VPM_SIZE) ltac:(do 3 (apply in_or_app; right); left; reflexivity)).
        cbn [blk_addr blk_size fst snd] in K. unfold vpm_cells. cbn [cells_size csize Nat.add]. unfold VPM_SIZE in K. lia.
      + revert HOS. unfold HOSTS. destruct (vp_hosts_o V) as [[K bs]|]; intros HOS; [| exact HOS].
        destruct HOS as (HP0 & SO & LEN & F2).
        assert (OWN : forall b, In b (blocks_VPM A V) -> In b (NB ++ (p, A, VPM_SIZE) :: LB)).
        { intros b Hb. pose proof (Permutation_in _ VP Hb) as Hb'. destruct Hb' as [<-|Hb']; [apply in_or_app; right; left; reflexivity| apply in_or_app; left; exact Hb']. }
        split; [exact HP0|]. split.
        * eapply SKobj_frame; [exact SO| intros b Hb; eapply SKobj_owned; [exact SO| exact Hb]| exact XPV].
        * split; [exact LEN|]. eapply (XBUFs_frame _ (NB ++ (p, A, VPM_SIZE) :: LB)); [exact F2| | auto| exact XPV|].
          -- intros b Hb. eapply XBUFs_owned; [exact F2| exact Hb].
          -- intros b Hb. pose proof (HB b ltac:(do 2 (apply in_or_app; right); exact Hb)) as K2. clear - K2 CEIL LO80. lia.
    - eapply xpres_trans; [exact XP0|]. eapply xpres_of_munch; [exact MU| exact WM| |].
      + eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [K1 K2]. left. cbn in *. lia.
      + intros b Hb. apply HB. apply SUBLB. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_es_apart : forall m mo' s' M' LBN errv' V NB c,
    fworld m mo' s' M' LBN errv' V NB -> mid_err M' = ErrReady c ->
    (forall b', In b' (VB :: blocks_ENTRY ee E) -> blk_addr b' + blk_size b' <= blk_addr (ec_es c) \/ blk_addr (ec_es c) + ERRST_SIZE <= blk_addr b')
    /\ blk_addr (ec_es c) + ERRST_SIZE <= hceil /\ In (ec_es c) (LBN ++ LIB) /\ blk_size (ec_es c) = ERRST_SIZE.
  Proof.
    intros m mo' s' M' LBN errv' V NB c (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & _) ME.
    pose proof LM as (_ & _ & _ & EPm & _). rewrite CXE, CX, ME in EPm. cbn [ERRPH_mid ERRPH] in EPm. destruct EPm as [_ CH].
    pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (I5' : In (ec_es c) (mid_errblocks M' ++ LBN ++ NB ++ VB :: LB)).
    { apply in_app_or in I5. apply in_or_app. right. destruct I5 as [K|K]; [apply in_or_app; left; exact K| do 2 (apply in_or_app; right); right; apply LIBSUB; exact K]. }
    pose proof (HB _ I5') as EH. rewrite Z5 in EH.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
    split; [| split; [exact EH| split; [exact I5| exact Z5]]].
    intros b' Hb'.
    assert (IN' : In b' (mid_errblocks M' ++ LBN ++ NB ++ VB :: LB)).
    { destruct Hb' as [<-|Hb']; do 3 (apply in_or_app; right); [left; reflexivity| right]. eapply ENTRYobj_owned_law; [exact EO| exact Hb']. }
    assert (NE : blk_id (ec_es c) <> blk_id b').
    { apply in_app_or in I5. destruct I5 as [K|K].
      - (* [comment removed for export] *)
        rewrite app_assoc in ND. apply (nodup_ids_app_ne _ _ _ _ ND); [apply in_or_app; right; exact K|].
        destruct Hb' as [<-|Hb']; apply in_or_app; right; [left; reflexivity| right; eapply ENTRYobj_owned_law; [exact EO| exact Hb']].
      - destruct Hb' as [<-|Hb'].
        + (* [comment removed for export] *)
          destruct (nd_app _ _ ND) as [_ ND1]. destruct (nd_app _ _ ND1) as [_ ND2]. destruct (nd_app _ _ ND2) as [_ ND3].
          apply not_eq_sym. apply (nodup_ids_cons_ne _ _ _ ND3). apply LIBSUB. exact K.
        + exact (IDS _ _ K Hb'). }
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP I5' IN' NE) as DJ. rewrite Z5 in DJ. lia.
  Qed.

  Lemma mid_step_trans' : forall M0 M1 M2, mid_step M0 M1 -> mid_step M1 M2 -> mid_step M0 M2.
  Proof.
    intros M0 M1 M2 (F1 & C1 & E1 & V1) (F2 & C2 & E2 & V2). unfold mid_step.
    split; [exact F2|]. split; [intros b Hb; exact (C2 b (C1 b Hb))|]. split; [intros c Hc; exact (E2 c (E1 c Hc))| intros Hv; exact (V2 (V1 Hv))].
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_xp_raise : forall m m' mo' s' M' LBN errv' V NB,
    fworld m mo' s' M' LBN errv' V NB -> xpres (LBN ++ NB ++ VB :: LB) spq (EF (mid_err M')) m m' ->
    xpres LB (bv_unsigned sp) (EF (mid_err M)) m m'.
  Proof.
    intros m m' mo' s' M' LBN errv' V NB FW XP.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & _).
    cbv delta [spq VB] in *. hcb. pose proof (word_range sp) as SPR.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall b, In b LB -> In b (LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (intros b Hb; do 2 (apply in_or_app; right); right; exact Hb).
    pose proof STP as (_ & _ & SE & _).
    destruct (mid_err M) as [|c0] eqn:PH0.
    - (* [comment removed for export] *)
      unfold EF in XP |- *. cbn [errph_foot].
      apply (xpres_weaken LB LB (bv_unsigned sp) (bv_unsigned sp) ERR_X (ERR_X ++ [])); [| lia| auto| intros a Ha; apply rin_ivs_app; left; exact Ha].
      eapply (xpres_shrink _ LB _ (bv_unsigned sp) ERR_X); [exact XP| lia| exact SUBL|].
      intros a Ha [HR _]. destruct (mid_err M') as [|c] eqn:PH1; cbn [errph_foot rin_ivs fst snd] in Ha; [exact Ha|].
      destruct Ha as [Ha|Ha]; [| exact Ha].
      (* [comment removed for export] *)
      destruct (fworld_es_apart _ _ _ _ _ _ _ _ c FW PH1) as (_ & EH & EIN & ESZ).
      assert (ELBN : In (ec_es c) LBN).
      { destruct M as [f cph eph E0 v]. destruct M' as [f' cph' eph' E1 v']. cbn [mid_err mid_ctx] in *. subst eph eph'.
        unfold mid_newlib_ok in NW. cbn [mid_ctx mid_err] in NW. destruct NW as (LA & LE & P & _ & D). cbn [errph_delta] in D.
        destruct D as (_ & _ & _ & HF). eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_or_app. right.
        eapply (proj1 (Forall_forall _ _) HF). unfold chain_blocks. do 3 right. left. reflexivity. }
      assert (EIN' : In (ec_es c) (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (apply in_or_app; right; apply in_or_app; left; exact ELBN).
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP EIN') as (_ & _ & _ & _ & EOFF). rewrite ESZ in EOFF.
      destruct HR as [K|[K|(b & Hb & Hr)]].
      + clear - K EH CEIL LO80 Ha. lia.
      + clear - K EOFF Ha HCEILB EH. unfold ERRST_SIZE in *. lia.
      + pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
        assert (NE : blk_id (ec_es c) <> blk_id b).
        { destruct (nd_app _ _ ND) as [_ ND1]. apply (nodup_ids_app_ne _ _ _ _ ND1); [exact ELBN|]. apply in_or_app. right. right. exact Hb. }
        assert (BIN : In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (apply in_or_app; right; apply SUBL; exact Hb).
        pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP EIN' BIN NE) as DJ.
        rewrite ESZ in DJ. clear - DJ Ha Hr. lia.
    - (* [comment removed for export] *)
      rewrite (SE c0 eq_refl) in XP. eapply xpres_weaken; [exact XP| lia| exact SUBL| auto].
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_after_raise : forall m m' mo' mo'' s' s'' M' LBN errv' errv'' LE c A1 p1 n1 line A2 p2 n2 lib reason,
    let Lx := LBN ++ [] ++ VB :: LB in
    let E' := errst_raise (mid_E M') A1 p1 n1 line A2 p2 n2 lib reason in
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_KREL H s'' mo'' -> hs_MPRES H mo' mo'' -> mem_inv rsegs m' -> stk rsegs m' lo spq -> hs_rauxv_ok H m' B ->
    hs_RHEAP H s'' (blocks_ERRST E' ++ LE ++ Lx) m' ->
    MEMFLAG m' 1 -> rw_cells rsegs m' (errno_addr tp) [C4 errv''] ->
    errph_delta (mid_err M') LE c -> raise_sizes A1 n1 A2 n2 ->
    ERRPH (LE ++ Lx) m' (ErrReady c) -> CTXPH (LE ++ Lx) m' (CtxReady x) -> ERRST (blocks_ERRST E') m' (blk_addr (ec_es c)) E' ->
    xpres Lx spq (ERR_X ++ memflag_foot ++ errph_foot (mid_err M')) m m' ->
    fworld m' mo'' s'' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M')) (LE ++ LBN) errv'' (vpm_empty p) [].
  Proof.
    intros m m' mo' mo'' s' s'' M' LBN errv' errv'' LE c A1 p1 n1 line A2 p2 n2 lib reason Lx E' FW
      KREL' MP' MI' ST' AUX' HP' MF' ERR' DL RSZ EP' CP' EST' XP'.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & VID & VP & NB1 & NB2 & NB3 & XP0).
    cbv delta [spq VB] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (_ & MF1 & _ & _ & _ & _ & _ & FIT & _). pose proof STP as (F1 & _). rewrite F1 in MF1.
    pose proof (xpres_drop_memflag _ _ _ _ _ _ MF1 MF' XP') as XPd. fold (EF (mid_err M')) in XPd.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall b, In b LB -> In b Lx) by (intros b Hb; subst Lx; apply in_or_app; right; right; exact Hb).
    assert (XPL : xpres LB (bv_unsigned sp + -80) (EF (mid_err M')) m m') by (eapply xpres_weaken; [exact XPd| lia| exact SUBL| auto]).
    assert (XPV : xpres ([] ++ (p, A, VPM_SIZE) :: LB) (bv_unsigned sp + -80) (EF (mid_err M')) m m')
      by (eapply xpres_weaken; [exact XPd| lia| intros b Hb; subst Lx; apply in_or_app; right; exact Hb| auto]).
    (* [comment removed for export] *)
    assert (AVB : forall b', In b' ((p, A, VPM_SIZE) :: blocks_ENTRY ee E) -> avoids (EF (mid_err M')) (blk_addr b') (blk_size b')).
    { intros b' Hb'.
      assert (IN' : In b' (mid_errblocks M' ++ LBN ++ [] ++ (p, A, VPM_SIZE) :: LB)).
      { destruct Hb' as [<-|Hb']; do 3 (apply in_or_app; right); [left; reflexivity| right]. eapply ENTRYobj_owned_law; [exact EO| exact Hb']. }
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IN') as (_ & _ & _ & _ & OFF).
      apply avoids_EF; [unfold IMG_LO, IMG_HI; exact OFF|]. intros c0 Hc0. exact (proj1 (fworld_es_apart _ _ _ _ _ _ _ _ c0 FW Hc0) b' Hb'). }
    assert (AVF : avoids (EF (mid_err M')) (bv_unsigned sp + -80) 80).
    { apply avoids_EF; [unfold IMG_LO, IMG_HI; lia|]. intros c0 Hc0. pose proof (proj1 (proj2 (fworld_es_apart _ _ _ _ _ _ _ _ c0 FW Hc0))). lia. }
    pose proof EO as (_ & EIN & O1 & O2 & O3 & O4 & XS). rewrite SUO in O3. rewrite PNO in O1. cbn [ofield] in O1, O3.
    destruct O1 as (PNP & _ & PNIN). destruct O3 as (SUP & _ & SUIN).
    pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ. unfold zlength in *.
    assert (INS : In (ps, en_suites E, sn) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. do 2 (apply in_or_app; right). apply in_or_app. left. rewrite SUO. left. reflexivity. }
    assert (INP : In (pn, en_pname E, Z.of_nat (length ns) + 1) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. apply in_or_app. left. rewrite PNO. left. reflexivity. }
    (* [comment removed for export] *)
    assert (CX' : mid_ctx M' = CtxReady x) by (rewrite CXE; exact CX).
    assert (FIT' : errst_fits E') by (apply errst_fits_raise; [exact FIT| exact RSZ]).
    assert (LM' : LIBMID ((LE ++ LBN) ++ LIB) m' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M'))).
    { rewrite <- app_assoc. eapply (LIBMID_errcall (LBN ++ LIB) Lx (LE ++ Lx) LE); [exact LM| exact CX'| exact XPd| | exact CP'| exact EP'| exact DL| exact EST'| exact FIT'| exact MF'].
      intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [subst Lx; apply in_or_app; left; exact Hb| apply SUBL; apply LIBSUB; exact Hb]. }
    assert (STP2 : mid_step M' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M'))).
    { unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; rewrite CX' in Hb; exact Hb|].
      split; [| auto]. intros c0 Hc0. rewrite Hc0 in DL. cbn [errph_delta] in DL. destruct DL as [-> _]. reflexivity. }
    assert (NW2 : mid_newlib_ok M' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M')) LE).
    { unfold mid_newlib_ok. cbn [mid_ctx mid_err]. exists [], LE. split; [reflexivity|]. rewrite CX'. split; [reflexivity|].
      destruct (mid_err M') as [|c0] eqn:PH; [exact DL|]. cbn [errph_delta] in DL. destruct DL as [_ ->]. reflexivity. }
    unfold fworld. cbv delta [spq VB]. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
      | |- rw_cells _ _ (bv_unsigned sp + -80) _ => eapply xpres_rw_cells'; [exact XPd| exact FR| left; lia| unfold fcc_frame; cbn [cells_size csize Nat.add]; exact AVF]
      | |- hs_MPRES _ _ _ => eapply (mpres_trans H HH); [exact MP| exact MP']
      | |- hs_RHEAP _ _ _ _ => cbn [mid_errblocks mid_E]; rewrite <- app_assoc; exact HP'
      | |- mid_step _ _ => eapply mid_step_trans'; [exact STP| exact STP2]
      | |- mid_newlib_ok _ _ _ => eapply mid_newlib_ok_trans; [exact STP| exact NW| exact STP2| exact NW2]
      | |- mid_ctx _ = _ => cbn [mid_ctx]; symmetry; exact CX
      | |- mid_vdso _ = _ => cbn [mid_vdso]; exact VDE
      | |- ENTRYobj _ _ _ _ => eapply ENTRYobj_frameX; [exact EO| exact XPL|]; intros b Hb; apply AVB; right; exact Hb
      | |- rw_cells _ _ (en_suites E) _ =>
          eapply xpres_rw_cells'; [exact XPL| exact SU| |];
          [ right; right; exists (ps, en_suites E, sn); split; [exact SUIN|]; cbn [blk_addr blk_size fst snd]; lia
          | eapply avoids_sub; [apply AVB; right; exact INS| cbn; lia| cbn [blk_addr blk_size fst snd]; lia] ]
      | |- bytes_at _ _ (en_pname E) _ =>
          eapply xpres_bytes_at; [exact XPL| exact PN|]; split;
          [ right; right; exists (pn, en_pname E, Z.of_nat (length ns) + 1); split; [exact PNIN|]; cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia
          | eapply avoids_sub; [apply AVB; right; exact INP| cbn; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia] ]
      | |- VPMobj _ _ _ _ => eapply VPMobj_frameX; [exact VO| exact XPV|]; apply (AVB (p, A, VPM_SIZE)); left; reflexivity
      | |- xpres LB _ _ m0 _ => eapply xpres_trans; [exact XP0| eapply fworld_xp_raise; [exact FW| subst Lx; exact XPd]]
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_stack_raise : forall M', mid_step M M' -> lo <= spq - (96 + RAISE_STACK (mid_err M')).
  Proof.
    intros M' (_ & _ & SE & _). cbv delta [spq]. clear - LO SE.
    unfold FCC_STACK, FR_ech_final_config_checks in LO. change RREALLOC_STACK with 8256 in LO.
    destruct (mid_err M) as [|c0] eqn:E0; destruct (mid_err M') as [|c1] eqn:E1.
    - change (RAISE_STACK ErrFresh) with 9360. change (errph_stack ErrFresh) with 9328 in LO. lia.
    - change (RAISE_STACK (ErrReady c1)) with 8304. change (errph_stack ErrFresh) with 9328 in LO. lia.
    - exfalso. specialize (SE _ eq_refl). discriminate SE.
    - change (RAISE_STACK (ErrReady c1)) with 8304. change (errph_stack (ErrReady c0)) with 144 in LO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_raise_pre : forall m mo' s' M' LBN errv',
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    let Lx := LBN ++ [] ++ VB :: LB in let ph := mid_err M' in let E0 := mid_E M' in
       hs_RHEAP H s' (blocks_ERRST E0 ++ Lx) m
    /\ lb_bytes (blocks_ERRST E0 ++ Lx) + raise_bytes ph <= hs_LIVE_MAX H
    /\ Z.of_nat (length (blocks_ERRST E0 ++ Lx)) + raise_cnt ph <= hs_LIVE_CNT_MAX H
    /\ lb_big (blocks_ERRST E0 ++ Lx) + errph_big ph <= hs_LIVE_BIG_MAX H
    /\ MEMFLAG m 1 /\ IMPL_mem m /\ GOT_mem m /\ relro_lib m
    /\ ERRPH Lx m ph /\ ERRX m ph E0 /\ errph_below ph lo /\ CTXPH Lx m (CtxReady x) /\ HPKE_tabs m
    /\ lo <= spq - (96 + RAISE_STACK ph)
    /\ (forall b, In b LB -> In b Lx).
  Proof.
    intros m mo' s' M' LBN errv' FW.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & VID & VP & NB1 & NB2 & NB3 & XP0).
    cbv zeta. cbv delta [spq VB] in *. hcb.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
    pose proof STP as (F1 & _). rewrite F1 in MF.
    assert (CX' : mid_ctx M' = CtxReady x) by (rewrite CXE; exact CX). rewrite CX' in CP, EPm. cbn [ERRPH_mid] in EPm.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall b, In b (LBN ++ LIB) -> In b (LBN ++ [] ++ (p, A, VPM_SIZE) :: LB)).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; apply LIBSUB; exact Hb]. }
    assert (SUBH : forall b, In b (LBN ++ LIB) -> In b (mid_errblocks M' ++ LBN ++ [] ++ (p, A, VPM_SIZE) :: LB)) by (intros b Hb; apply in_or_app; right; apply SUBL; exact Hb).
    (* [comment removed for export] *)
    assert (LEN16 : length (es_slots (mid_E M')) = 16%nat).
    { destruct (mid_err M') as [|c0]; cbn [ERRX] in EX; [rewrite EX; reflexivity| exact (proj1 EX)]. }
    pose proof (errst_fits_bounds _ LEN16 FIT) as (EC & EB & EG).
    pose proof (newlib_err_bounds _ _ _ _ CX STP NW) as (NB_ & NC_ & NG_ & _).
    pose proof VBR as (_ & _ & _ & _ & VOFF).
    repeat match goal with |- _ /\ _ => split end.
    - exact HP.
    - rewrite !lb_bytes_app, lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right]. unfold raise_bytes. change (mid_errblocks M') with (blocks_ERRST (mid_E M')) in *.
      clear - BY EB NB_. unfold FCC_BYTES, ERRSTR_BYTES, ERRDEBUG_BYTES, VPM_SIZE, SK_SIZE in *. lia.
    - rewrite !length_app. cbn [length]. rewrite !Nat2Z.inj_add, Nat2Z.inj_succ. unfold raise_cnt. clear - CN EC NC_. unfold FCC_CNT, ERRSTR_CNT in *. lia.
    - rewrite !lb_big_app, lb_big_cons. cbn [blk_size snd lb_big fold_right]. rewrite (big1_small VPM_SIZE) by (unfold VPM_SIZE, BIGB; lia).
      clear - BG EG NG_. lia.
    - exact MF.
    - exact IM.
    - exact G1.
    - exact RL.
    - eapply ERRPH_mono; [exact EPm| exact SUBL].
    - exact EX.
    - destruct (mid_err M') as [|c0]; [exact I|]. cbn [errph_below]. cbn [ERRPH] in EPm. destruct EPm as [_ CH].
      pose proof CH as (I2 & _ & _ & I3 & _ & _ & I4 & _ & _ & I5 & _ & I6 & _).
      pose proof (HB _ (SUBH _ I2)) as K2. pose proof (HB _ (SUBH _ I3)) as K3. pose proof (HB _ (SUBH _ I4)) as K4. pose proof (HB _ (SUBH _ I5)) as K5.
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ I2)) as (P2 & _). pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ I3)) as (P3 & _).
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ I4)) as (P4 & _). pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ I5)) as (P5 & _).
      pose proof CH as (_ & Z2 & _ & _ & Z3 & _ & _ & Z4 & _ & _ & Z5 & _). rewrite Z2 in K2. rewrite Z3 in K3. rewrite Z4 in K4. rewrite Z5 in K5.
      unfold chain_below. clear - K2 K3 K4 K5 P2 P3 P4 P5 CEIL. lia.
    - eapply CTXPH_mono; [exact CP| exact SUBL].
    - exact HT.
    - exact (fcc_stack_raise M' STP).
    - intros b Hb. apply in_or_app. right. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Definition L1cfg (i : Z) (rax w3 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (mo' : Model) : config :=
    mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3
                   (Z_to_bv 64 (6 * i)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FCC_HEAD) fc None m (seg_rom rsegs)) mo'.
  Definition L1exit (k : config) : Prop :=
    exists (w3 w4 w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m mo' s' M' LBN errv',
      fworld m mo' s' M' LBN errv' (vpm_empty p) [] /\ cfg_model k = mo' /\
      (  cfg_ms k = MS (mkR (Z_to_bv 64 FCC_RA1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3 w4 w5
                           (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)
      \/ cfg_ms k = MS (mkR (Z_to_bv 64 FCC_R2) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3 w4 w5
                           (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FCC_GOOD) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Lemma fworld_entry : forall m mo' s' M' LBN errv' V NB,
    fworld m mo' s' M' LBN errv' V NB ->
    exists pad1 pad2 pad3 pad4, rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) /\ 0 < ee /\ ee + ENTRY_SIZE <= hceil
      /\ 0 < en_suites E /\ en_suites E + 6 * en_nsuites E <= hceil /\ In (ps, en_suites E, sn) LB
      /\ 0 < en_pname E /\ en_pname E + zlength ns + 1 <= hceil /\ In (pn, en_pname E, zlength ns + 1) LB
      /\ 0 < A /\ A + VPM_SIZE <= hceil /\ 0 <= en_exts E < 2^64.
  Proof.
    intros m mo' s' M' LBN errv' V NB (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & _).
    cbv delta [spq VB] in *. hcb.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XS).
    rewrite SUO in O3. rewrite PNO in O1. cbn [ofield] in O1, O3. destruct O1 as (PNP & _ & PNIN). destruct O3 as (SUP & _ & SUIN).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (intros b Hb; do 3 (apply in_or_app; right); right; exact Hb).
    pose proof (HB _ (SUBLB _ EIN)) as K1. pose proof (HB _ (SUBLB _ SUIN)) as K2. pose proof (HB _ (SUBLB _ PNIN)) as K3.
    assert (K4 := HB (p, A, VPM_SIZE) ltac:(do 3 (apply in_or_app; right); left; reflexivity)).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBLB _ EIN)) as (EP0 & _).
    cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, EP0. pose proof VBR as (AP & _).
    pose proof (rw_cells_bound _ _ _ _ HC) as HCB.
    assert (XR : 0 <= en_exts E < 2^64).
    { revert XS. unfold EXTS. destruct (en_exts_o E) as [[K es]|]; intros XS; [| rewrite XS; lia].
      destruct XS as (XP0 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (HB _ (SUBLB _ KIN)) as K5. cbn [blk_addr blk_size fst snd] in K5. unfold SK_SIZE in K5. lia. }
    exists pad1, pad2, pad3, pad4. unfold ENTRY_SIZE, zlength in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.

  Lemma L1_loop : forall (k : nat) (i : Z) (rax w3 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m mo' s' M' LBN errv',
    Z.of_nat k = en_nsuites E - i -> 0 <= i < en_nsuites E ->
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_SR H L1exit (L1cfg i rax w3 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo').
  Proof.
    induction k as [|k IH]; intros i rax w3 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo' s' M' LBN errv' HK IR FW; [lia|].
    unfold L1cfg. cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR. pose proof (word_range w3) as W3R.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & SUP & SUH & SUIN & PNP & PNH & PNIN & AP & AH & XR).
    unfold ENTRY_SIZE in EEH. unfold VPM_SIZE in AH.
    (* [comment removed for export] *)
    destruct (nth_error rows (Z.to_nat i)) as [[[kem kdf] aead]|] eqn:NTH.
    2:{ exfalso. apply nth_error_None in NTH. unfold zlength in ROWS. lia. }
    pose proof (proj1 (Forall_forall _ _) ROK _ (nth_error_In _ _ NTH)) as RR. unfold row_ok in RR. cbn [fst snd] in RR. destruct RR as (KR & DR & AR).
    pose proof (suite_row_at _ _ _ _ _ _ _ SU NTH ltac:(lia)) as ROW.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_seg3 with (i := i) (kem := kem) (kdf := kdf) (aead := aead); try eassumption; unfold ENTRY_SIZE; lia|].
    cbv beta. intros ms1 ->.
    set (hi := bv_unsigned w3 / 2 ^ 48). assert (HR : 0 <= hi < 2^16) by (subst hi; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof LM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _).
    destruct (suite_fail kem kdf aead) as [[reason line]|] eqn:SF.
    - (* [comment removed for export] *)
      pose proof (fworld_raise_pre _ _ _ _ _ _ FW) as PRE. cbv zeta in PRE. cbv delta [spq VB] in PRE.
      destruct PRE as (HPx & BYx & CNx & BGx & MFx & IMx & GMx & RLx & EPx & EXx & EBx & CPx & HTx & LOx & SUBx).
      eapply (sr_seq H HH).
      { eapply (suitebad_spec H HX EGS) with (lo := lo) (B := B) (LB := LBN ++ [] ++ (p, A, VPM_SIZE) :: LB) (s := s') (ph := mid_err M') (E := mid_E M') (x := x)
           (kem := kem) (kdf := kdf) (aead := aead) (hi := hi) (reason := reason) (line := line) (errv := errv');
          try reflexivity; try eassumption; try lia.
        all: lazymatch goal with
          | |- bv_unsigned (Z_to_bv 64 _) <= B => rewrite unsigned_lit by lia; lia
          | |- bv_unsigned (Z_to_bv 64 _) mod 16 = 0 => rewrite unsigned_lit by lia; clear - SPA SPR; lia
          | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST
          | |- _ <= _ - SUITECHECK_STACK _ => rewrite unsigned_lit by lia; unfold SUITECHECK_STACK, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id; clear - LOx; lia
          | |- _ mod 2 = 0 => unfold FCC_R2; rewrite unsigned_lit by lia; reflexivity
          end. }
      intros [ms2 mo2] PO. unfold hfind_fail_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LE & c & p1 & p2 & A1 & n1 & A2 & n2 &
                      -> & MP2 & (KREL2 & MI2 & ST2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & ERR2 & DL & RSZ & EP2 & CP2 & EST2 & TB2 & XP2).
      rewrite unsigned_lit in ST2, XP2 by lia.
      pose proof (fworld_after_raise _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW KREL2 MP2 MI2 ST2 AUX2 HP2 MF2 ERR2 DL RSZ EP2 CP2 EST2 XP2) as FW2.
      set (M2 := mkMID 1 (CtxReady x) (ErrReady c) _ (mid_vdso M')) in FW2.
      destruct (fworld_entry _ _ _ _ _ _ _ _ FW2) as (qad1 & qad2 & qad3 & qad4 & EC2 & _).
      destruct (Z.lt_ge_cases (i + 1) (en_nsuites E)) as [NX|NX].
      + eapply (sr_evt_krel H HH); [exact KREL2| eapply fcc_seg4n with (i := i) (rv := 0); try eassumption; try lia; unfold ENTRY_SIZE; lia|].
        cbv beta. intros ms3 ->. eapply (IH (i + 1)); [lia| lia| exact FW2].
      + eapply (sr_evt_krel H HH); [exact KREL2| eapply fcc_seg4e with (i := i) (rv := 0); try eassumption; try lia; unfold ENTRY_SIZE; lia|].
        cbv beta. intros ms3 ->. apply (sr_done H HH). unfold L1exit. cbn [cfg_ms cfg_model].
        do 19 eexists. exists m2, mo2, s2', M2, (LE ++ LBN), errv2. split; [exact FW2|]. split; [reflexivity|]. left. reflexivity.
    - (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL|..].
      { eapply (suiteok_spec) with (lo := lo) (kem := kem) (kdf := kdf) (aead := aead) (hi := hi); try reflexivity; try eassumption; try lia.
        all: lazymatch goal with
          | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST
          | |- _ <= _ - SUITECHECK_OK_STACK =>
              rewrite unsigned_lit by lia; unfold SUITECHECK_OK_STACK, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id; pose proof (fcc_stack_raise M' STP) as K; cbv delta [spq] in K;
              assert (RS0 : 0 <= RAISE_STACK (mid_err M')) by (destruct (mid_err M'); [change (RAISE_STACK ErrFresh) with 9360| change (RAISE_STACK (ErrReady _)) with 8304]; lia);
              clear - CEIL K RS0; lia
          | |- _ mod 2 = 0 => unfold FCC_R2; rewrite unsigned_lit by lia; reflexivity
          end. }
      cbv beta. intros ms2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & TB2).
      rewrite unsigned_lit in MU2, ST2 by lia.
      assert (FW2 : fworld m2 mo' s' M' LBN errv' (vpm_empty p) []).
      { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact ST2|]. constructor; [cbn; lia| constructor]. }
      destruct (fworld_entry _ _ _ _ _ _ _ _ FW2) as (qad1 & qad2 & qad3 & qad4 & EC2 & _).
      destruct (Z.eq_dec aead 65535) as [A65|A65].
      + (* [comment removed for export] *)
        destruct (Z.lt_ge_cases (i + 1) (en_nsuites E)) as [NX|NX].
        * eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_seg4n with (i := i) (rv := 1); try eassumption; try lia; unfold ENTRY_SIZE; lia|].
          cbv beta. intros ms3 ->. eapply (IH (i + 1)); [lia| lia| exact FW2].
        * eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_seg4e with (i := i) (rv := 1); try eassumption; try lia; unfold ENTRY_SIZE; lia|].
          cbv beta. intros ms3 ->. apply (sr_done H HH). unfold L1exit. cbn [cfg_ms cfg_model].
          do 19 eexists. exists m2, mo', s', M', LBN, errv'. split; [exact FW2|]. split; [reflexivity|]. left. reflexivity.
      + eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_seg4g; [exact A65| lia| exact MI2]|].
        cbv beta. intros ms3 ->. apply (sr_done H HH). unfold L1exit. cbn [cfg_ms cfg_model].
        do 19 eexists. exists m2, mo', s', M', LBN, errv'. split; [exact FW2|]. split; [reflexivity|]. right. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma VPMobj_LB_mono : forall L L' m a V, VPMobj L m a V -> (forall b, In b L -> In b L') -> VPMobj L' m a V.
  Proof.
    intros L L' m a V (VC & VIN & HOS) SUB. split; [exact VC|]. split; [apply SUB; exact VIN|].
    revert HOS. unfold HOSTS. destruct (vp_hosts_o V) as [[K bs]|]; intros HOS; [| exact HOS].
    destruct HOS as (HP0 & SO & LEN & F2). split; [exact HP0|]. split; [eapply SKobj_LB_mono; [exact SO| exact SUB]|]. split; [exact LEN|].
    clear - F2 SUB. induction F2 as [|q X qs bs' HX F IH]; constructor; [eapply XBUFobj_LB_mono; [exact HX| exact SUB]| exact IH].
  Qed.

  Lemma fcc_tail : forall m mo' s' M' LBN errv' V NB rv s_ (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w4 w5 w6 w7 w8 : word),
    fworld m mo' s' M' LBN errv' V NB -> (rv = 0 \/ rv = 1) ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 FCC_R4) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                        w2 (Z_to_bv 64 rv) w4 w5 w6 w7 w8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' M' LBN errv' V NB rv s_ t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w4 w5 w6 w7 w8 FW RV.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & VID & VP & NB1 & NB2 & NB3 & XP0).
    cbv delta [spq VB] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
    set (Lcur := mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB) in *.
    assert (HB := HH_blocks_below H HH _ _ _ HP). pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
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
    { destruct (mid_err M') as [|c0]; cbn [ERRX] in EX; [rewrite EX; reflexivity| exact (proj1 EX)]. }
    pose proof (errst_fits_bounds _ LEN16 FIT) as (EC & EB & EG).
    (* [comment removed for export] *)
    pose proof (vpmfree_spec H HH) as VF. unfold vpmfree_stmt, efree_stmt_at in VF.
    eapply (sr_seq H HH).
    { eapply VF with (lo := lo) (B := B) (LB := Lcur) (s := s') (p := A) (x := V) (errv := errv'); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact NDV| exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact IM| exact G1| exact G3| exact TP].
      all: lazymatch goal with
           | |- VPMobj _ _ _ _ => eapply VPMobj_LB_mono; [exact VO| exact SUBV]
           | |- rw_cells _ _ _ [C4 _] => exact ERR
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ <= _ - VPMFREE_STACK => change VPMFREE_STACK with 8352; clear - LO; unfold FCC_STACK, FR_ech_final_config_checks in LO; change RREALLOC_STACK with 8256 in LO; lia
           | |- _ mod 2 = 0 => unfold FCC_R4; rewrite unsigned_lit by lia; reflexivity
           end. }
    clear VF. intros [ms2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m2 & s2' & LB2 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & PERM2 & HP2 & XP2 & IM2 & GM2 & GX2).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia.
    assert (KEEP : forall b, In b (mid_errblocks M' ++ LBN ++ LB) -> In b LB2).
    { intros b Hb. eapply perm_in_rest; [exact PERM2| | exact (NOTV _ Hb)]. subst Lcur.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. do 2 (apply in_or_app; right). right. exact Hb. }
    assert (PL2 : Permutation LB2 (mid_errblocks M' ++ LBN ++ LB)).
    { apply (Permutation_app_inv_l (blocks_VPM A V)). transitivity Lcur; [exact PERM2|].
      transitivity ((NB ++ [(p, A, VPM_SIZE)]) ++ (mid_errblocks M' ++ LBN ++ LB)); [exact PL|]. apply Permutation_app_tail.
      transitivity ((p, A, VPM_SIZE) :: NB); [apply Permutation_sym; apply Permutation_cons_append| apply Permutation_sym; exact VP]. }
    assert (HP2' : hs_RHEAP H s2' (mid_errblocks M' ++ LBN ++ LB) m2) by (eapply PERM; [exact HP2| exact PL2]).
    assert (XPL : xpres LB (bv_unsigned sp + -80) [] m m2) by (eapply xpres_weaken; [exact XP2| lia| intros b Hb; apply KEEP; do 2 (apply in_or_app; right); exact Hb| auto]).
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -80) (fcc_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact FR| left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply fcc_segE with (lo := lo); [exact FR2| exact ST2| exact CEIL| clear - LO80; lia| exact MI2]|].
    cbv beta. intros ms3 [-> ST3].
    apply (sr_done H HH). unfold fcc_post. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, m2, errv', s2', rv, M', LBN.
    split; [reflexivity|]. split; [exact RV|]. split; [exact KREL2|]. split; [eapply (mpres_trans H HH); [exact MP| exact MP2]|].
    split; [exact MI2|]. split; [exact ST3|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HP2'|].
    split; [eapply LIBMID_xpres0; [exact LM| exact XP2| intros b Hb; apply KEEP; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| do 2 (apply in_or_app; right); apply LIBSUB; exact Hb]]|].
    split; [exact STP|]. split; [exact NW|]. split; [exact CXE|]. split; [exact VDE|].
    split; [exact EC|]. split; [exact EB|]. split; [exact EG|].
    split.
    - eapply ENTRYobj_LB_mono; [| intros b Hb; apply in_or_app; right; exact Hb]. eapply ENTRYobj_frameX; [exact EO| exact XPL| intros b Hb; apply avoids_nil].
    - eapply xpres_trans; [exact XP0|]. unfold EF. eapply xpres_weaken; [exact XP2| clear - LO80; lia| intros b Hb; apply KEEP; do 2 (apply in_or_app; right); exact Hb| intros a Ha; destruct Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_raise_fail : forall (raA line : Z) m mo' s' M' LBN errv' s_ (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w3 w4 w5 w8 : word),
    (raA = FCC_RA1 /\ line = 275) \/ (raA = FCC_RA4 /\ line = 284) ->
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 raA) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 ee) w3 w4 w5 (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros raA line m mo' s' M' LBN errv' s_ t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w3 w4 w5 w8 WHICH FW.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & _).
    pose proof (fworld_raise_pre _ _ _ _ _ _ FW) as PRE. cbv zeta in PRE.
    destruct PRE as (HPx & BYx & CNx & BGx & MFx & IMx & GMx & RLx & EPx & EXx & EBx & CPx & HTx & LOx & SUBx).
    cbv delta [spq VB] in *. hcb. pose proof (word_range sp) as SPR.
    assert (RAR : 0 <= raA < 2^64 /\ raA mod 2 = 0) by (destruct WHICH as [[-> _]|[-> _]]; unfold FCC_RA1, FCC_RA4; (split; [lia| reflexivity])).
    assert (LNR : 0 <= line < 2^31) by (destruct WHICH as [[_ ->]|[_ ->]]; lia).
    eapply (raise_spec H HX EGS) with (lo := lo) (B := B) (LB := LBN ++ [] ++ (p, A, VPM_SIZE) :: LB) (s := s') (ph := mid_err M') (E := mid_E M') (x := x) (errv := errv')
      (file := A_ECHS_FILE) (fs := S_ECHS_FILE) (fsl := K_ECHS_FILE) (func := A_FCC_FUNC) (gs := S_FCC_FUNC) (gsl := K_FCC_FUNC)
      (line := line) (lib := ERR_LIB_SSL) (reason := R_PASSED_INVALID_ARGUMENT) (ra2 := FCC_RA2) (ra3 := FCC_RA3);
      try eassumption; try (rewrite unsigned_lit by lia); try eassumption.
    all: try exact LNR; try exact (proj1 RAR); try exact (proj2 RAR).
    all: lazymatch goal with
         | |- ROSTR A_ECHS_FILE _ _ => apply R_ECHS_FILE
         | |- ROSTR A_FCC_FUNC _ _ => apply R_FCC_FUNC
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_ECHS_FILE) < 24 => rewrite S_ECHS_FILE_len; lia
         | |- Z.of_nat (length S_FCC_FUNC) < 32 => rewrite S_FCC_FUNC_len; lia
         | |- 0 < A_ECHS_FILE => unfold A_ECHS_FILE; lia
         | |- 0 < A_FCC_FUNC => unfold A_FCC_FUNC; lia
         | |- 0 < ERR_LIB_SSL < 256 => unfold ERR_LIB_SSL; lia
         | |- ERR_LIB_SSL <> 2 => unfold ERR_LIB_SSL; lia
         | |- 0 < R_PASSED_INVALID_ARGUMENT < _ => unfold R_PASSED_INVALID_ARGUMENT; lia
         | |- 0 <= FCC_RA2 < _ => unfold FCC_RA2; lia
         | |- FCC_RA2 mod 2 = 0 => reflexivity
         | |- 0 <= FCC_RA3 < _ => unfold FCC_RA3; lia
         | |- FCC_RA3 mod 2 = 0 => reflexivity
         | |- _ <= B => clear - SPB SPR; lia
         | |- _ mod 16 = 0 => clear - SPA SPR; lia
         | |- _ <= _ - RAISE_STACK _ => clear - LOx; lia
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; destruct WHICH as [[-> ->]|[-> ->]]; [eapply fcc_glue275| eapply fcc_glue284]; assumption
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply fcc_glue2; assumption
         | |- ?G => idtac "RFPRE" G
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' mo'' s'' errv'' LE c p1 p2 A1 A2 n1 n2 E'
           KREL' MP' MI' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' XP'.
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in XP' by lia.
    pose proof (fworld_after_raise _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW KREL' MP' MI' ST' AUX' HP' MF' ERR' DL RSZ EP' CP' EST' XP') as FW2.
    eapply (sr_evt_krel H HH); [exact KREL'| eapply fcc_segF0; exact MI'|].
    cbv beta. intros ms3 ->. eapply fcc_tail; [exact FW2| left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition NAMEexit (k : config) : Prop :=
    exists (rax w3 w4 w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m mo' s' M' LBN errv',
      fworld m mo' s' M' LBN errv' (vpm_empty p) [] /\ cfg_model k = mo' /\
      (  cfg_ms k = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3 w4 w5
                           (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FCC_NAME) fc None m (seg_rom rsegs)
      \/ cfg_ms k = MS (mkR (Z_to_bv 64 FCC_RA4) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3 w4 w5
                           (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Lemma fworld_exts : forall m mo' s' M' LBN errv' V NB,
    fworld m mo' s' M' LBN errv' V NB -> 0 < en_exts E ->
    exists K xs, en_exts_o E = Some (K, xs) /\ SKobj LB m (en_exts E) K /\ length xs = length (sk_elems K)
      /\ Forall2 (fun q X => EXTobj LB m q X) (sk_elems K) xs /\ SK_below (en_exts E) K lo /\ 0 <= sk_num K < 2^31.
  Proof.
    intros m mo' s' M' LBN errv' V NB (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & _) XP0.
    cbv delta [spq VB] in *. hcb. pose proof EO as (_ & _ & _ & _ & _ & _ & XS).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    revert XS. unfold EXTS. destruct (en_exts_o E) as [[K xs]|]; intros XS; [| lia].
    destruct XS as (_ & SO & LEN & F2). exists K, xs. split; [reflexivity|]. split; [exact SO|]. split; [exact LEN|]. split; [exact F2|].
    pose proof SO as (_ & _ & KIN & NC & CAP & _ & _ & DAT).
    assert (K1 := HB (sk_id K, en_exts E, SK_SIZE) ltac:(do 3 (apply in_or_app; right); right; exact KIN)). cbn [blk_addr blk_size fst snd] in K1.
    split; [| unfold sk_num, zlength in *; lia]. unfold SK_below. split; [unfold SK_SIZE in *; lia|].
    destruct DAT as [[D0 _]|(D1 & D2 & D3 & DIN & _)]; [left; exact D0| right].
    assert (K2 := HB (sk_did K, sk_data K, 8 * sk_cap K) ltac:(do 3 (apply in_or_app; right); right; exact DIN)). cbn [blk_addr blk_size fst snd] in K2. lia.
  Qed.

  Lemma L2_loop : forall (k : nat) (j : Z) K xs (rax w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m mo' s' M' LBN errv',
    en_exts_o E = Some (K, xs) -> Z.of_nat k = sk_num K - j -> 0 <= j < sk_num K -> 0 < en_exts E ->
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_SR H NAMEexit
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee)
                        (Z_to_bv 64 (sk_num K)) (Z_to_bv 64 j) w5 (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FCC_XHEAD) fc None m (seg_rom rsegs)) mo').
  Proof.
    induction k as [|k IH]; intros j K xs rax w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo' s' M' LBN errv' XO HK JR XP FW; [lia|].
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & _ & _ & _ & _ & _ & _ & AP & AH & XR).
    unfold ENTRY_SIZE in EEH.
    destruct (fworld_exts _ _ _ _ _ _ _ _ FW XP) as (K' & xs' & XO' & SO & LEN & F2 & SKB & NUMR). rewrite XO in XO'. injection XO' as <- <-.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segXH; [exact EC| exact EEP| unfold ENTRY_SIZE; lia| exact XR| exact MI]|].
    cbv beta. intros ms1 ->.
    (* [comment removed for export] *)
    destruct (nth_error (sk_elems K) (Z.to_nat j)) as [q|] eqn:NTH.
    2:{ exfalso. apply nth_error_None in NTH. unfold sk_num, zlength in JR. lia. }
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { eapply skvalue_spec with (lo := lo) (i := j) (K := K); try reflexivity; try eassumption; rewrite ?unsigned_lit by lia; [exact ST| clear - LO8K CEIL; lia]. }
    cbv beta. intros ms2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite unsigned_lit in MU2, ST2 by lia.
    assert (FW2 : fworld m2 mo' s' M' LBN errv' (vpm_empty p) []).
    { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact ST2|]. constructor; [cbn; lia| constructor]. }
    (* [comment removed for export] *)
    destruct (fworld_exts _ _ _ _ _ _ _ _ FW2 XP) as (K' & xs' & XO' & SO2 & _ & F22 & _). rewrite XO in XO'. injection XO' as <- <-.
    destruct (nth_error xs (Z.to_nat j)) as [X|] eqn:NTHX.
    2:{ exfalso. apply nth_error_None in NTHX. pose proof (nth_error_lt _ _ _ NTH). lia. }
    pose proof (Forall2_nth_error _ _ _ _ _ _ F22 NTH NTHX) as XJ.
    pose proof XJ as ((pad & PL & XC) & XIN & _).
    pose proof FW2 as (_ & _ & _ & _ & _ & _ & _ & HP2 & _). assert (HB2 := HH_blocks_below H HH _ _ _ HP2).
    assert (K3 := HB2 (ex_id X, q, EXT_SIZE) ltac:(do 3 (apply in_or_app; right); right; exact XIN)). cbn [blk_addr blk_size fst snd] in K3. unfold EXT_SIZE in K3.
    pose proof SO2 as (_ & _ & _ & _ & _ & _ & EL & _). pose proof (proj1 (Forall_forall _ _) EL _ (nth_error_In _ _ NTH)) as QR. cbn beta in QR.
    set (X' := mkEXT (ex_type X mod 65536) (ex_len X) (ex_val X) (ex_val_o X) (ex_id X)).
    assert (XC' : rw_cells rsegs m2 q (ext_cells X' pad)) by (unfold ext_cells; cbn [ex_type ex_len ex_val X']; eapply rw_cells_C2_le2; [apply le2_wz_mod| exact XC]).
    assert (TR : 0 <= ex_type X' < 2^16) by (cbn [ex_type X']; pose proof (Z.mod_pos_bound (ex_type X) 65536); lia).
    eapply (sr_evt_krel H HH); [exact KREL| eapply (fcc_segX3) with (X := X') (num := sk_num K); [exact XC'| exact TR| lia| unfold EXT_SIZE; lia| exact JR| lia| exact MI2]|].
    cbv beta. intros ms3 (a0' & [[_ ->]|[[_ [NX ->]]|[_ [NX ->]]]]).
    - apply (sr_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. exists (Z_to_bv 64 FCC_RA4). do 19 eexists. exists m2, mo', s', M', LBN, errv'.
      split; [exact FW2|]. split; [reflexivity|]. right. reflexivity.
    - eapply (IH (j + 1)); [exact XO| lia| lia| exact XP| exact FW2].
    - apply (sr_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. do 20 eexists. exists m2, mo', s', M', LBN, errv'.
      split; [exact FW2|]. split; [reflexivity|]. left. rewrite NX. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_good : forall (w3 w4 w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m mo' s' M' LBN errv',
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_SR H NAMEexit
      (mkCfg (MS (mkR (Z_to_bv 64 FCC_R2) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3 w4 w5
                        (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FCC_GOOD) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros w3 w4 w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo' s' M' LBN errv' FW.
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & _ & _ & _ & _ & _ & _ & AP & AH & XR).
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segX1; [exact EC| exact EEP| unfold ENTRY_SIZE in *; lia| exact XR| exact MI]|].
    cbv beta. intros ms1 [[X0 ->]|[XP ->]].
    { apply (sr_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. do 20 eexists. exists m, mo', s', M', LBN, errv'.
      split; [exact FW|]. split; [reflexivity|]. left. reflexivity. }
    destruct (fworld_exts _ _ _ _ _ _ _ _ FW XP) as (K & xs & XO & SO & LEN & F2 & SKB & NUMR).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { eapply sknum_spec with (lo := lo) (K := K); try reflexivity; try eassumption; rewrite ?unsigned_lit by lia; [exact ST| clear - LO8K CEIL; lia]. }
    cbv beta. intros ms2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite unsigned_lit in MU2, ST2 by lia.
    assert (FW2 : fworld m2 mo' s' M' LBN errv' (vpm_empty p) []).
    { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact ST2|]. constructor; [cbn; lia| constructor]. }
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segX2; [exact NUMR| exact MI2]|].
    cbv beta. intros ms3 [[N0 ->]|[NP ->]].
    { apply (sr_done H HH). unfold NAMEexit. cbn [cfg_ms cfg_model]. do 20 eexists. exists m2, mo', s', M', LBN, errv'.
      split; [exact FW2|]. split; [reflexivity|]. left. reflexivity. }
    eapply (L2_loop (Z.to_nat (sk_num K)) 0); [exact XO| rewrite Z2Nat.id by lia; lia| lia| exact XP| exact FW2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fworld_cstr : forall m mo' s' M' LBN errv' V NB,
    fworld m mo' s' M' LBN errv' V NB ->
    exists slack, bytes_at rsegs m (en_pname E) (ns ++ Z_to_bv 8 0 :: slack)
      /\ (- (en_pname E + zlength ns + 1)) mod 8 <= zlength slack /\ en_pname E + zlength ns + 1 + zlength slack <= hceil + 7.
  Proof.
    intros m mo' s' M' LBN errv' V NB FW. pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & _).
    cbv delta [spq VB] in *. hcb.
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & _ & _ & _ & _ & _ & _ & PNP & PNH & PNIN & _).
    assert (PNIN' : In (pn, en_pname E, zlength ns + 1) (mid_errblocks M' ++ LBN ++ NB ++ (p, A, VPM_SIZE) :: LB)) by (do 3 (apply in_or_app; right); right; exact PNIN).
    pose proof (SLACK _ _ _ _ _ _ HP PNIN') as WR. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP PNIN') as (_ & P16 & _ & PH & POFF). cbn [blk_addr blk_size fst snd] in *.
    set (e := en_pname E + (zlength ns + 1)) in *. set (k := (- e) mod 8) in *.
    assert (KR : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    pose proof (Z.div_mod (- e) 8 ltac:(lia)) as DM. fold k in DM. set (q := - e / 8) in DM.
    assert (OFF : e + k <= 0x10000 \/ 0x311000 <= e).
    { clearbody k q. clear - POFF KR DM PNP. subst e. unfold zlength in *. lia. }
    destruct (wr_at_bytes_off_image _ _ _ WR ltac:(lia) OFF) as (slack & SL & SB).
    exists slack. unfold zlength in *. rewrite SL. split; [| split; [subst k e; lia| clearbody k q; clear - PH KR DM HCEILB; subst e; lia]].
    change (ns ++ Z_to_bv 8 0 :: slack) with (ns ++ [Z_to_bv 8 0] ++ slack). rewrite app_assoc. apply bytes_at_app. split; [exact PN|].
    rewrite length_app. cbn [length]. replace (en_pname E + Z.of_nat (length ns + 1)) with e by (subst e; lia). exact SB.
  Qed.

  Lemma fworld_canary : forall m mo' s' M' LBN errv' V NB,
    fworld m mo' s' M' LBN errv' V NB ->
    rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)] /\ rw_cells rsegs m RSSP_GUARD [C8 (wz (hs_canary H))] /\ 0 <= hs_canary H < 2^64.
  Proof. intros m mo' s' M' LBN errv' V NB (_ & _ & _ & _ & _ & _ & _ & HP & _). destruct (STATICS _ _ _ HP) as (_ & G & R & C). auto. Qed.

  Local Ltac retpc_in RA := replace (Z_to_bv 64 RA) with (ret_pc (Z_to_bv 64 RA)) by (apply ret_pc_even; [unfold RA; lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma fcc_fail0 : forall m mo' s' M' LBN errv' V NB s_ (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w3 w4 w5 w6 w7 w8 : word),
    fworld m mo' s' M' LBN errv' V NB ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 w2 w3 w4 w5 w6 w7 w8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FCC_RA3) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' M' LBN errv' V NB s_ rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w3 w4 w5 w6 w7 w8 FW.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & _). retpc_in FCC_RA3.
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segF0; exact MI|]. cbv beta. intros ms1 ->. eapply fcc_tail; [exact FW| left; reflexivity].
  Qed.
  Lemma fcc_failF : forall m mo' s' M' LBN errv' V NB s_ (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w4 w5 w6 w7 w8 : word),
    fworld m mo' s' M' LBN errv' V NB ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 w2 (Z_to_bv 64 0) w4 w5 w6 w7 w8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FCC_FAIL) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' M' LBN errv' V NB s_ rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w4 w5 w6 w7 w8 FW.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & _).
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segF; exact MI|]. cbv beta. intros ms1 ->. eapply fcc_tail; [exact FW| left; reflexivity].
  Qed.
  Lemma fcc_ok1 : forall m mo' s' M' LBN errv' V NB s_ (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w3 w4 w5 w6 w7 w8 : word),
    fworld m mo' s' M' LBN errv' V NB ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 w2 w3 w4 w5 w6 w7 w8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FCC_OK) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' M' LBN errv' V NB s_ rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w2 w3 w4 w5 w6 w7 w8 FW.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & _).
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segOK; exact MI|]. cbv beta. intros ms1 ->. eapply fcc_tail; [exact FW| right; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_name2 : forall m mo' s' M' LBN errv' V NB r s_ (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w3 w4 w5 w6 w7 w8 : word),
    fworld m mo' s' M' LBN errv' V NB -> (r = 0 \/ r = 1) ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 FCC_R8) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 ee) w3 w4 w5 w6 w7 w8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc (Z_to_bv 64 FCC_R8)) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' M' LBN errv' V NB r s_ t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w3 w4 w5 w6 w7 w8 FW RR.
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & _ & _ & _ & PNP & PNH & PNIN & AP & AH & XR). unfold ENTRY_SIZE in EEH.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN3 with (r := r); [exact EC| exact EEP| unfold ENTRY_SIZE; lia| exact RR| exact MI]|].
    cbv beta. intros ms1 [[-> ->]|[-> ->]]; [eapply fcc_fail0; exact FW|].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ FW) as (slack & CS & PAD & CEND). unfold zlength in *.
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { eapply strrchr_spec with (str := ns) (slack := slack) (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; try (clear - CEND CEIL LO8K; lia); clear - SPR LO8K CEIL HCEILB; lia. }
    cbv beta. intros ms2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & _).
    rewrite !unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite (unsigned_lit 46) by lia.
    assert (FW2 : fworld m2 mo' s' M' LBN errv' V NB).
    { eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact ST2|]. constructor; [cbn; clear - LO8K; lia| constructor]. }
    (* [comment removed for export] *)
    rewrite (unsigned_lit (en_pname E)) by lia.
    assert (RF : exists i0 b0 q, rfind_ret (en_pname E) (rfind (ns ++ [Z_to_bv 8 0]) (Z_to_bv 8 46)) = q
                 /\ (if q =? 0 then en_pname E else q) = en_pname E + Z.of_nat i0 /\ 0 <= q < 2^64
                 /\ (i0 < length ns)%nat /\ nth_error ns i0 = Some b0 /\ (i0 = 0%nat \/ bv_unsigned b0 = 46)).
    { rewrite (rfind_app_miss ns [Z_to_bv 8 0]) by reflexivity.
      destruct (rfind ns (Z_to_bv 8 46)) as [i|] eqn:RFD.
      - destruct (rfind_hit_nth _ _ _ RFD) as (b0 & N0 & E0). pose proof (rfind_lt _ _ _ RFD) as IL. exists i, b0, (en_pname E + Z.of_nat i). cbn [rfind_ret].
        split; [reflexivity|]. split; [destruct (Z.eqb_spec (en_pname E + Z.of_nat i) 0); lia|]. split; [clear - PNP PNH IL HCEILB; lia|].
        split; [exact IL|]. split; [exact N0| right; rewrite E0; reflexivity].
      - destruct (nth_error ns 0) as [b0|] eqn:N0; [| apply nth_error_None in N0; lia]. exists 0%nat, b0, 0. cbn [rfind_ret]. rewrite Z.eqb_refl.
        repeat split; try lia; auto. }
    destruct RF as (i0 & b0 & q & RFE & LLE & QR & IL & NTH0 & DOT). rewrite RFE.
    set (LL := en_pname E + Z.of_nat i0) in *.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN4 with (q := q); [exact QR| exact MI2]|].
    cbv beta. intros ms3 ->. rewrite LLE.
    assert (NN : forall i, ~ In (Z_to_bv 8 0) (skipn i ns)) by (intros i K; apply NONUL; eapply in_skipn_in; exact K).
    assert (LLR : 0 < LL /\ LL + Z.of_nat (length (skipn i0 ns)) = en_pname E + Z.of_nat (length ns)) by (subst LL; rewrite length_skipn; lia).
    destruct LLR as [LLP LLN].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ FW2) as (sl2 & CS2 & PAD2 & CEND2). unfold zlength in CS2, PAD2, CEND2.
    pose proof (cstr_suffix _ _ _ _ i0 CS2 ltac:(lia)) as CS2'. fold LL in CS2'.
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { pose proof strlen_spec as Q; hnf in Q; eapply Q with (str := skipn i0 ns) (slack := sl2); clear Q; rewrite ?unsigned_lit by lia;
        [exact CS2'| apply NN| rewrite LLN; exact PAD2| exact MI2]. }
    cbv beta. intros ms4 (v0 & v1 & v2 & c1_ & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & _).
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -80)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| exact I]).
    assert (FW3 : fworld m3 mo' s' M' LBN errv' V NB) by (eapply fworld_stk; [exact FW2| exact MU3| exact WM3| exact MI3| exact ST3| constructor]).
    set (L2 := Z.of_nat (length (skipn i0 ns))) in *.
    assert (L2R : 1 <= L2 <= 255) by (subst L2; rewrite length_skipn; clear - IL NSL; unfold zlength in NSL; lia).
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ FW3) as (sl3 & CS3 & PAD3 & CEND3). unfold zlength in CS3, PAD3, CEND3.
    pose proof (cstr_suffix _ _ _ _ i0 CS3 ltac:(lia)) as CS3'. fold LL in CS3'.
    assert (NTHL : nth_error (skipn i0 ns) 0 = Some b0) by (rewrite nth_error_skipn', Nat.add_0_r; exact NTH0).
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN5 with (LL := LL) (L2 := L2) (ls := skipn i0 ns) (rest := Z_to_bv 8 0 :: sl3) (c0 := b0);
      [exact CS3'| exact NTHL| lia| exact LLP| exact MI3]|].
    cbv beta. set (d := if bv_unsigned b0 =? 46 then 1 else 0). intros ms5 [[L2S ->]|[L2B ->]]; [eapply fcc_fail0; exact FW3|].
    assert (DR : 0 <= d <= 1 /\ d < L2) by (subst d; destruct (bv_unsigned b0 =? 46); lia).
    set (ls' := skipn (Z.to_nat d) (skipn i0 ns)).
    assert (LS'L : Z.of_nat (length ls') = L2 - d) by (subst ls' L2; rewrite length_skipn; lia).
    assert (CSX : forall mm sl, bytes_at rsegs mm LL (skipn i0 ns ++ Z_to_bv 8 0 :: sl) -> bytes_at rsegs mm (LL + d) (ls' ++ Z_to_bv 8 0 :: sl)).
    { intros mm sl BS. replace d with (Z.of_nat (Z.to_nat d)) at 1 by lia. subst ls'. apply cstr_suffix; [exact BS| lia]. }
    (* [comment removed for export] *)
    destruct (fworld_canary _ _ _ _ _ _ _ _ FW3) as (CG3 & CC3 & CANR).
    pose proof (proj2 (proj2 R_DIGITS) m3 MI3) as (DB3 & DN3 & _).
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { eapply strspn_spec with (str := ls') (sslack := sl3) (acc := S_DIGITS) (aslack := K_DIGITS) (lo := lo) (can := hs_canary H).
      all: lazymatch goal with
           | |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 A_DIGITS)) _ => unfold A_DIGITS; rewrite unsigned_lit by lia; exact DB3
           | |- bytes_at _ _ _ _ => rewrite unsigned_lit by lia; exact (CSX _ _ CS3')
           | |- ~ In _ S_DIGITS => exact DN3
           | |- ~ In _ _ => subst ls'; rewrite skipn_skipn; apply NN
           | |- (2 <= length S_DIGITS)%nat => rewrite S_DIGITS_len; lia
           | |- rw_cells _ _ _ [C8 _] => first [exact CG3| exact CC3]
           | |- 0 <= hs_canary H < _ => exact CANR
           | |- bv_unsigned (Z_to_bv 64 A_DIGITS) + _ <= _ => unfold A_DIGITS; rewrite !unsigned_lit by lia; rewrite ?length_app, ?S_DIGITS_len; cbn; clear - LO8K CEIL HCEILB; lia
           | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by lia; clear - SPR LO8K CEIL HCEILB; lia
           | |- bv_unsigned _ + _ <= _ => rewrite !unsigned_lit by lia; rewrite ?length_app; cbn [length]; clear - LS'L CEND3 LLN LO8K CEIL DR; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST3
           | |- 3215360 <= lo => clear - CEIL HCEILB; lia
           | |- lo <= _ => rewrite unsigned_lit by lia; clear - LO8K; lia
           | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by lia; clear - SPR LO8K CEIL HCEILB; lia
           | |- mem_inv _ _ => exact MI3
           end. }
    cbv beta. intros ms6 (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m4 & -> & MU4 & WM4 & MI4 & ST4).
    rewrite !unsigned_lit in MU4 by lia. rewrite unsigned_lit in ST4 by lia.
    assert (FW4 : fworld m4 mo' s' M' LBN errv' V NB).
    { eapply fworld_stk; [exact FW3| exact MU4| exact WM4| exact MI4| exact ST4|]. constructor; [cbn; clear - LO8K; lia| constructor]. }
    set (n1 := Z.of_nat (spn ls' S_DIGITS)) in *.
    assert (N1R : 0 <= n1 <= L2 - d) by (subst n1; pose proof (spn_le ls' S_DIGITS); lia).
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ FW4) as (sl4 & CS4 & PAD4 & CEND4). unfold zlength in CS4, PAD4, CEND4.
    pose proof (CSX _ _ (cstr_suffix _ _ _ _ i0 CS4 ltac:(lia))) as CS4'. fold LL in CS4'.
    set (c0 := match nth_error ls' 0 with Some b => b | None => b0 end). set (c1 := match nth_error ls' 1 with Some b => b | None => b0 end).
    assert (C01 : 3 <= L2 - d -> nth_error ls' 0 = Some c0 /\ nth_error ls' 1 = Some c1).
    { intros L3B. subst c0 c1. destruct (nth_error ls' 0) as [xb|] eqn:E0; [| apply nth_error_None in E0; lia].
      destruct (nth_error ls' 1) as [yb|] eqn:E1; [| apply nth_error_None in E1; lia]. split; reflexivity. }
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN6 with (LL := LL + d) (L3 := L2 - d) (n1 := n1) (ls := ls') (rest := Z_to_bv 8 0 :: sl4) (c0 := c0) (c1 := c1);
      [exact CS4'| exact C01| lia| lia| lia| exact MI4]|].
    cbv beta. intros ms7 (a0' & a1' & [[_ ->]|[[_ ->]|(_ & L3B & _ & _ & ->)]]); [eapply fcc_fail0; exact FW4| eapply fcc_ok1; exact FW4|].
    (* [comment removed for export] *)
    destruct (fworld_canary _ _ _ _ _ _ _ _ FW4) as (CG4 & CC4 & _).
    pose proof (proj2 (proj2 R_HEXDIGITS) m4 MI4) as (HB4 & HN4 & _).
    set (ls'' := skipn 2 ls').
    assert (LS''L : Z.of_nat (length ls'') = L2 - d - 2) by (subst ls''; rewrite length_skipn; lia).
    assert (CS4'' : bytes_at rsegs m4 (LL + d + 2) (ls'' ++ Z_to_bv 8 0 :: sl4)) by (subst ls''; change 2 with (Z.of_nat 2) at 1; apply cstr_suffix; [exact CS4'| lia]).
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { eapply strspn_spec with (str := ls'') (sslack := sl4) (acc := S_HEXDIGITS) (aslack := K_HEXDIGITS) (lo := lo) (can := hs_canary H).
      all: lazymatch goal with
           | |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 A_HEXDIGITS)) _ => unfold A_HEXDIGITS; rewrite unsigned_lit by lia; exact HB4
           | |- bytes_at _ _ _ _ => rewrite unsigned_lit by lia; exact CS4''
           | |- ~ In _ S_HEXDIGITS => exact HN4
           | |- ~ In _ _ => subst ls'' ls'; rewrite !skipn_skipn; apply NN
           | |- (2 <= length S_HEXDIGITS)%nat => rewrite S_HEXDIGITS_len; lia
           | |- rw_cells _ _ _ [C8 _] => first [exact CG4| exact CC4]
           | |- 0 <= hs_canary H < _ => exact CANR
           | |- bv_unsigned (Z_to_bv 64 A_HEXDIGITS) + _ <= _ => unfold A_HEXDIGITS; rewrite !unsigned_lit by lia; rewrite ?length_app, ?S_HEXDIGITS_len; cbn; clear - LO8K CEIL HCEILB; lia
           | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by lia; clear - SPR LO8K CEIL HCEILB; lia
           | |- bv_unsigned _ + _ <= _ => rewrite !unsigned_lit by lia; rewrite ?length_app; cbn [length]; clear - LS''L CEND4 LLN LO8K CEIL DR; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST4
           | |- 3215360 <= lo => clear - CEIL HCEILB; lia
           | |- lo <= _ => rewrite unsigned_lit by lia; clear - LO8K; lia
           | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by lia; clear - SPR LO8K CEIL HCEILB; lia
           | |- mem_inv _ _ => exact MI4
           end. }
    cbv beta. intros ms8 (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m5 & -> & MU5 & WM5 & MI5 & ST5).
    rewrite !unsigned_lit in MU5 by lia. rewrite unsigned_lit in ST5 by lia.
    assert (FW5 : fworld m5 mo' s' M' LBN errv' V NB).
    { eapply fworld_stk; [exact FW4| exact MU5| exact WM5| exact MI5| exact ST5|]. constructor; [cbn; clear - LO8K; lia| constructor]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN7 with (L3 := L2 - d) (n2 := Z.of_nat (spn ls'' S_HEXDIGITS)); [lia| pose proof (spn_le ls'' S_HEXDIGITS); lia| exact MI5]|].
    cbv beta. intros ms9 [[_ ->]|[_ ->]]; [eapply fcc_fail0; exact FW5| eapply fcc_ok1; exact FW5].
  Qed.

  (* [comment removed for export] *)
  Lemma fworld_after_add1host : forall m m' mo' mo'' s' s'' M' LBN errv' errv'' V' NB,
    let Lcur := mid_errblocks M' ++ LBN ++ [] ++ VB :: LB in
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_KREL H s'' mo'' -> hs_MPRES H mo' mo'' -> mem_inv rsegs m' -> stk rsegs m' lo spq -> hs_rauxv_ok H m' B ->
    rw_cells rsegs m' (errno_addr tp) [C4 errv''] ->
    xpres Lcur spq (memflag_foot ++ [(A, A + VPM_SIZE)]) m m' ->
    hs_RHEAP H s'' (NB ++ Lcur) m' -> VPMobj (NB ++ Lcur) m' A V' -> vp_id V' = p ->
    Permutation (blocks_VPM A V') (VB :: NB) ->
    Z.of_nat (length NB) <= 4 -> lb_bytes NB <= ADD1HOST_BYTES -> lb_big NB = 0 -> MEMFLAG m' 1 ->
    fworld m' mo'' s'' M' LBN errv'' V' NB.
  Proof.
    intros m m' mo' mo'' s' s'' M' LBN errv' errv'' V' NB Lcur FW KREL' MP' MI' ST' AUX' ERR' XP' HP' VO' VID' VP' NB1' NB2' NB3' MF'.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & VID & VP & NB1 & NB2 & NB3 & XP0).
    cbv delta [spq VB] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (_ & MF1 & _). pose proof STP as (F1 & _). rewrite F1 in MF1.
    assert (HB := HH_blocks_below H HH _ _ _ HP). pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
    pose proof VBR as (AP & _ & _ & AH' & AOFF).
    assert (VBIN : In (p, A, VPM_SIZE) Lcur) by (subst Lcur; do 3 (apply in_or_app; right); left; reflexivity).
    pose proof (HB _ VBIN) as VBH. cbn [blk_addr blk_size fst snd] in VBH.
    (* [comment removed for export] *)
    assert (APV : forall b, In b (mid_errblocks M' ++ LBN) \/ In b LB -> blk_addr b + blk_size b <= A \/ A + VPM_SIZE <= blk_addr b).
    { intros b Hb.
      assert (BIN : In b Lcur) by (subst Lcur; destruct Hb as [Hb|Hb]; [rewrite app_assoc; apply in_or_app; left; exact Hb| do 3 (apply in_or_app; right); right; exact Hb]).
      assert (NE : blk_id (p, A, VPM_SIZE) <> blk_id b).
      { subst Lcur. destruct Hb as [Hb|Hb].
        - rewrite app_assoc in ND. apply not_eq_sym. apply (nodup_ids_app_ne _ _ _ _ ND Hb). apply in_or_app. right. left. reflexivity.
        - destruct (nd_app _ _ ND) as [_ ND1]. destruct (nd_app _ _ ND1) as [_ ND2]. cbn [app] in ND2. exact (nodup_ids_cons_ne _ _ _ ND2 Hb). }
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP VBIN BIN NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. lia. }
    assert (AVB : forall b', In b' (blocks_ENTRY ee E) -> avoids (memflag_foot ++ [(A, A + VPM_SIZE)]) (blk_addr b') (blk_size b')).
    { intros b' Hb'. pose proof (ENTRYobj_owned_law _ _ _ _ EO _ Hb') as IN'.
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP ltac:(subst Lcur; do 3 (apply in_or_app; right); right; exact IN')) as (_ & _ & _ & _ & OFF).
      unfold avoids. apply Forall_app. split.
      - unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      - constructor; [cbn| constructor]. apply APV. right. exact IN'. }
    assert (SUBL : forall b, In b LB -> In b Lcur) by (intros b Hb; subst Lcur; do 3 (apply in_or_app; right); right; exact Hb).
    assert (XPL : xpres LB (bv_unsigned sp + -80) (memflag_foot ++ [(A, A + VPM_SIZE)]) m m') by (eapply xpres_weaken; [exact XP'| lia| exact SUBL| auto]).
    pose proof EO as (_ & EIN & O1 & O2 & O3 & O4 & XS). rewrite SUO in O3. rewrite PNO in O1. cbn [ofield] in O1, O3.
    destruct O1 as (PNP & _ & PNIN). destruct O3 as (SUP & _ & SUIN).
    pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ. unfold zlength in *.
    assert (INS : In (ps, en_suites E, sn) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. do 2 (apply in_or_app; right). apply in_or_app. left. rewrite SUO. left. reflexivity. }
    assert (INP : In (pn, en_pname E, Z.of_nat (length ns) + 1) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. apply in_or_app. left. rewrite PNO. left. reflexivity. }
    assert (AVF : avoids (memflag_foot ++ [(A, A + VPM_SIZE)]) (bv_unsigned sp + -80) 80).
    { unfold avoids. apply Forall_app. split.
      - unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      - constructor; [cbn; clear - VBH CEIL LO80; unfold VPM_SIZE in *; lia| constructor]. }
    unfold fworld. cbv delta [spq VB]. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
      | |- rw_cells _ _ (bv_unsigned sp + -80) _ =>
          eapply xpres_rw_cells'; [exact XP'| exact FR| left; lia|]; unfold fcc_frame; cbn [cells_size csize Nat.add]; exact AVF
      | |- hs_MPRES _ _ _ => eapply (mpres_trans H HH); [exact MP| exact MP']
      | |- hs_RHEAP _ _ _ _ => eapply PERM; [exact HP'|]; subst Lcur; cbn [app]; rewrite (app_assoc (mid_errblocks M') LBN); etransitivity; [apply Permutation_app_swap_app|]; rewrite <- app_assoc; apply Permutation_refl
      | |- LIBMID _ _ _ =>
          destruct M' as [f' cph' eph' E1 v']; cbn [mid_flag] in F1; subst f';
          apply (LIBMID_mf_X (LBN ++ LIB) Lcur (bv_unsigned sp + -80) [(A, A + VPM_SIZE)] m m' (mkMID 1 cph' eph' E1 v')); [exact LM| exact XP'| | exact MF'| |];
          [ intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [subst Lcur; apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUBL; apply LIBSUB; exact Hb]
          | intros a Ha; cbn [rin_ivs fst snd] in Ha; unfold IMG_LO, IMG_HI; clear - Ha AOFF; unfold VPM_SIZE in *; lia
          | intros a b Ha Hb K; cbn [rin_ivs fst snd] in Ha;
            pose proof (APV b ltac:(apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply LIBSUB; exact Hb])) as DJ; clear - Ha K DJ; lia ]
      | |- ENTRYobj _ _ _ _ => eapply ENTRYobj_frameX; [exact EO| exact XPL| exact AVB]
      | |- rw_cells _ _ (en_suites E) _ =>
          eapply xpres_rw_cells'; [exact XPL| exact SU| |];
          [ right; right; exists (ps, en_suites E, sn); split; [exact SUIN|]; cbn [blk_addr blk_size fst snd]; lia
          | eapply avoids_sub; [apply AVB; exact INS| cbn; lia| cbn [blk_addr blk_size fst snd]; lia] ]
      | |- bytes_at _ _ (en_pname E) _ =>
          eapply xpres_bytes_at; [exact XPL| exact PN|]; split;
          [ right; right; exists (pn, en_pname E, Z.of_nat (length ns) + 1); split; [exact PNIN|]; cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia
          | eapply avoids_sub; [apply AVB; exact INP| cbn; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia] ]
      | |- VPMobj _ _ _ _ =>
          eapply VPMobj_relist; [exact VO'|]; intros b Hb; pose proof (Permutation_in _ VP' Hb) as Hb'; destruct Hb' as [<-|Hb']; [apply in_or_app; right; left; reflexivity| apply in_or_app; left; exact Hb']
      | |- xpres LB _ _ m0 _ =>
          eapply xpres_trans; [exact XP0|];
          apply (xpres_weaken LB LB (bv_unsigned sp) (bv_unsigned sp) [] (EF (mid_err M))); [| lia| auto| intros a Ha; destruct Ha];
          eapply (xpres_shrink _ LB _ (bv_unsigned sp) [] [(A, A + VPM_SIZE)]);
          [ change ([] ++ [(A, A + VPM_SIZE)]) with ([] ++ [(A, A + VPM_SIZE)]); eapply (xpres_drop_memflag _ _ [] [(A, A + VPM_SIZE)]); [exact MF1| exact MF'| cbn [app]; exact XP']
          | lia | exact SUBL
          | intros a Ha [HR _]; cbn [rin_ivs fst snd] in Ha; destruct Ha as [Ha|Ha]; [| exact Ha];
            destruct HR as [K|[K|(b & Hb & Hr)]]; [clear - K Ha VBH CEIL LO80; unfold VPM_SIZE in *; lia| clear - K Ha AOFF; unfold VPM_SIZE in *; lia|];
            pose proof (APV b (or_intror Hb)) as DJ; clear - DJ Ha Hr; lia ]
      | |- ?G => idtac "AHPOST" G
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_name1 : forall (rax w3 w4 w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m mo' s' M' LBN errv' s_,
    fworld m mo' s' M' LBN errv' (vpm_empty p) [] ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) w3 w4 w5
                        (Z_to_bv 64 1) (Z_to_bv 64 65535) w8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FCC_NAME) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros rax w3 w4 w5 w8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo' s' M' LBN errv' s_ FW.
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & STP & NW & CXE & VDE & EO & SU & PN & VO & VID & VP & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & _ & _ & _ & PNP & PNH & PNIN & AP & AH & XR). unfold ENTRY_SIZE in EEH. unfold zlength in *.
    (* [comment removed for export] *)
    destruct (nth_error ns 0) as [b0|] eqn:NTH0; [| apply nth_error_None in NTH0; lia].
    assert (B0 : bv_unsigned b0 <> 0).
    { intros K. apply NONUL. replace (Z_to_bv 8 0) with b0 by (apply bv_eq; rewrite K; reflexivity). eapply nth_error_In. exact NTH0. }
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN1 with (rest := [Z_to_bv 8 0]) (b0 := b0) (E := E) (ns := ns); first [exact EC| exact PN| exact NTH0| exact B0| exact MI| exact EEP| exact PNP| unfold ENTRY_SIZE; lia| exact sp]|].
    cbv beta. intros ms1 [[_ ->]|[B46 ->]]; [eapply fcc_failF; exact FW|].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ FW) as (sl1 & CS1 & PAD1 & CEND1). unfold zlength in CS1, PAD1, CEND1.
    eapply (sr_evt_krel H HH); [exact KREL|..].
    { pose proof strlen_spec as Q; hnf in Q; eapply Q with (str := ns) (slack := sl1); clear Q; rewrite ?unsigned_lit by lia; [exact CS1| exact NONUL| exact PAD1| exact MI]. }
    cbv beta. intros ms2 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & _).
    assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -80)) by (eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| exact I]).
    assert (FW2 : fworld m2 mo' s' M' LBN errv' (vpm_empty p) []) by (eapply fworld_stk; [exact FW| exact MU2| exact WM2| exact MI2| exact ST2| constructor]).
    pose proof FW2 as (_ & _ & FR2 & ERR2 & AUX2 & _ & _ & HP2 & LM2 & _ & _ & _ & _ & EO2 & SU2 & PN2 & VO2 & _).
    (* [comment removed for export] *)
    destruct (nth_error ns (Z.to_nat (Z.of_nat (length ns) - 1))) as [bl|] eqn:NTHL; [| apply nth_error_None in NTHL; lia].
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_segN2 with (rest := [Z_to_bv 8 0]) (bl := bl) (ns := ns); first [exact PN2| exact NTHL| exact PNP| exact MI2| unfold zlength; exact NSL| unfold zlength; exact NTHL| exact sp]|].
    cbv beta. intros ms3 [[_ ->]|[BL46 ->]]; [eapply fcc_failF; exact FW2|].
    (* [comment removed for export] *)
    destruct (fworld_cstr _ _ _ _ _ _ _ _ FW2) as (sl2 & CS2 & PAD2 & CEND2). unfold zlength in CS2, PAD2, CEND2.
    pose proof (fworld_raise_pre _ _ _ _ _ _ FW2) as PRE. cbv zeta in PRE. cbv delta [spq VB] in PRE.
    destruct PRE as (HPx & BYx & CNx & BGx & MFx & IMx & GMx & RLx & _).
    pose proof LM2 as (_ & _ & _ & _ & EX2 & _ & _ & FIT2 & _).
    assert (LEN16 : length (es_slots (mid_E M')) = 16%nat) by (destruct (mid_err M') as [|c0]; cbn [ERRX] in EX2; [rewrite EX2; reflexivity| exact (proj1 EX2)]).
    pose proof (errst_fits_bounds _ LEN16 FIT2) as (EC_ & EB_ & EG_). pose proof (newlib_err_bounds _ _ _ _ CX STP NW) as (NB_ & NC_ & NG_ & _).
    pose proof (errph_nonneg (mid_err M')) as (EHB & EHC & EHG).
    set (Lcur := mid_errblocks M' ++ LBN ++ [] ++ (p, A, VPM_SIZE) :: LB) in *.
    eapply (sr_seq H HH).
    { eapply (add1host_spec H HX) with (lo := lo) (B := B) (LB := Lcur) (s := s') (a := A) (name := en_pname E) (V := vpm_empty p) (pn := pn) (ns := ns) (slack := sl2) (errv := errv');
        try reflexivity; try eassumption.
      all: lazymatch goal with
           | |- VPMobj _ _ _ _ => eapply VPMobj_LB_mono; [exact VO2| intros b Hb; subst Lcur; do 2 (apply in_or_app; right); exact Hb]
           | |- A + VPM_SIZE <= lo => clear - AH CEIL; lia
           | |- In _ _ => subst Lcur; do 3 (apply in_or_app; right); right; unfold zlength; exact PNIN
           | |- 1 <= zlength ns <= 255 => exact NSL
           | |- _ mod 8 <= zlength _ => unfold zlength; exact PAD2
           | |- lb_bytes _ + _ <= _ => subst Lcur; change (mid_errblocks M') with (blocks_ERRST (mid_E M')); rewrite !lb_bytes_app, lb_bytes_cons; cbn [blk_size snd lb_bytes fold_right];
                                       clear - BY EB_ NB_ EHB; unfold FCC_BYTES, ADD1HOST_BYTES, ERRSTR_BYTES, VPM_SIZE, SK_SIZE in *; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lcur; change (mid_errblocks M') with (blocks_ERRST (mid_E M')); rewrite !length_app; cbn [length app]; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ, ?Nat2Z.inj_add;
                                               clear - CN EC_ NC_ EHC; unfold FCC_CNT, ERRSTR_CNT in *; change (@length (bptr * Z * Z) LB) with (@length block LB); lia
           | |- lb_big _ <= _ => subst Lcur; change (mid_errblocks M') with (blocks_ERRST (mid_E M')); rewrite !lb_big_app, lb_big_cons; cbn [blk_size snd lb_big fold_right];
                                 rewrite (big1_small VPM_SIZE) by (unfold VPM_SIZE, BIGB; lia); clear - BG EG_ NG_ EHG; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by lia; clear - SPB SPR; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST2
           | |- _ <= _ - ADD1HOST_STACK => rewrite unsigned_lit by lia; change ADD1HOST_STACK with 8544; clear - LO; unfold FCC_STACK, FR_ech_final_config_checks in LO; change RREALLOC_STACK with 8256 in LO; lia
           | |- _ mod 2 = 0 => unfold FCC_R8; rewrite unsigned_lit by lia; reflexivity
           | |- ?G => idtac "A1HPRE" G
           end. }
    intros [ms4 mo4] PO. unfold add1host_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & errv4 & s4' & V' & NB &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & VO4 & VID4 & VP4 & _ & _ & NB1 & NB2 & NB3 & MF4 & _).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in XP4 by lia.
    cbn [vp_id vpm_empty] in VID4, VP4.
    pose proof (fworld_after_add1host _ _ _ _ _ _ _ _ _ _ _ _ FW2 KREL4 MP4 MI4 ST4 AUX4 ERR4 XP4 HP4 VO4 VID4 VP4 NB1 NB2 NB3 MF4) as FW4.
    (* [comment removed for export] *)
    eapply fcc_name2; [exact FW4| destruct (hostname_ok ns); [right| left]; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_main : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 mo1 s1' errv1 s_,
    fworld m1 mo1 s1' M [] errv1 (vpm_empty p) [] ->
    hs_SR H (fcc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee E lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 FCC_R1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee)
                        s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FCC_R1)) fc None m1 (seg_rom rsegs)) mo1).
  Proof.
    intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 mo1 s1' errv1 s_ FW.
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & _).
    destruct (fworld_entry _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & EC & EEP & EEH & _ & _ & _ & _ & _ & _ & AP & AH & _). unfold ENTRY_SIZE in EEH. unfold VPM_SIZE in AH.
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_seg2; [exact EC| exact NSR| clear - AP AH HCEILB; lia| exact EEP| unfold ENTRY_SIZE; lia| exact MI]|].
    cbv beta. intros ms1 ->.
    eapply (sr_seq H HH); [eapply (L1_loop (Z.to_nat (en_nsuites E)) 0); [rewrite Z2Nat.id by lia; lia| lia| exact FW]|].
    intros [ms2 mo2] EX. unfold L1exit in EX. cbn [cfg_ms cfg_model] in EX.
    destruct EX as (w3 & w4 & w5 & w8 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & mo2' & s2' & M2 & LBN2 & errv2 & FW2 & <- & [-> | ->]).
    - (* [comment removed for export] *)
      eapply fcc_raise_fail; [left; split; reflexivity| exact FW2].
    - (* [comment removed for export] *)
      eapply (sr_seq H HH); [eapply fcc_good; exact FW2|].
      intros [ms3 mo3] EX. unfold NAMEexit in EX. cbn [cfg_ms cfg_model] in EX.
      destruct EX as (rax & x3 & x4 & x5 & x8 & u0' & u1' & u2' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3' & u4' & u5' & u6' & m3 & mo3' & s3' & M3 & LBN3 & errv3 & FW3 & <- & [-> | ->]).
      + eapply fcc_name1. exact FW3.
      + eapply fcc_raise_fail; [right; split; reflexivity| exact FW3].
  Qed.
End W.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section WS.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  Theorem fcc_spec : fcc_stmt H.
  Proof using HX EGS.
    unfold fcc_stmt. intros until ns.
    intros A0 EO NSR SUO SU ROWS SNR ROK PNO PN NONUL NSL BEL LM LIBSUB CX MF0 IDS HP KREL BY CN BG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE. subst a0.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO80 : lo + 8656 <= bv_unsigned sp) by (clear - LO; unfold FCC_STACK, FR_ech_final_config_checks in LO; change RREALLOC_STACK with 8256 in LO; lia).
    set (L0 := mid_errblocks M ++ LB) in *.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUB0 : forall b, In b LIB -> In b L0) by (intros b Hb; subst L0; apply in_or_app; right; apply LIBSUB; exact Hb).
    assert (SUBLB : forall b, In b LB -> In b L0) by (intros b Hb; subst L0; apply in_or_app; right; exact Hb).
    pose proof LM as (IM0 & MFL0 & _ & _ & _ & _ & _ & _ & GM0 & _). rewrite MF0 in MFL0.
    subst tp. rewrite errno_RATP in ERR.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fcc_seg1 with (lo := lo); [exact ST| exact CEIL| clear - LO80; lia| exact MI]|].
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : forall X, xpres L0 (bv_unsigned sp) X m m1).
    { intros X. eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : hs_RHEAP H s L0 m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (ERR1 : rw_cells rsegs m1 (errno_addr (Z_to_bv 64 RATP)) [C4 errv]).
    { rewrite errno_RATP. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. unfold RERRNO. cbn. lia. }
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM (XP1 []) SUB0) as LM1. pose proof LM1 as (IM1 & MF1 & _ & _ & _ & _ & _ & _ & GM1 & _). rewrite MF0 in MF1.
    (* [comment removed for export] *)
    pose proof (vpmnew_spec H HH) as VN. unfold vpmnew_stmt in VN.
    eapply (sr_seq H HH).
    { eapply VN with (lo := lo) (B := B) (LB := L0) (s := s) (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL| exact MI1| exact MF1| exact IM1| exact GM1| exact ERR1].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => subst L0; rewrite lb_bytes_app in *; unfold FCC_BYTES, VPM_SIZE, SK_SIZE, ERRSTR_BYTES in *; pose proof (errph_nonneg (mid_err M)) as (EB0 & _); clear - BY EB0; lia
           | |- Z.of_nat (length _) + _ <= _ => subst L0; rewrite length_app, Nat2Z.inj_add in *; unfold FCC_CNT, ERRSTR_CNT in *; pose proof (errph_nonneg (mid_err M)) as (_ & EC0 & _); clear - CN EC0; lia
           | |- lb_big _ <= _ => subst L0; rewrite lb_big_app in *; pose proof (errph_nonneg (mid_err M)) as (_ & _ & EG0); clear - BG EG0; lia
           | |- _ + -80 <= _ => clear - SPB SPR; lia
           | |- _ <= _ - VPMNEW_STACK => change VPMNEW_STACK with 8288; clear - LO80; lia
           | |- _ mod 2 = 0 => unfold FCC_R1; rewrite unsigned_lit by lia; reflexivity
           | |- ?G => idtac "VNPRE" G
           end. }
    clear VN. intros [ms2 mo2] PO. unfold vpmnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & VBR & HP2 & VO2 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia.
    pose proof VBR as (AP & _ & _ & AH & AOFF).
    (* [comment removed for export] *)
    assert (AVM : forall b, In b L0 -> avoids memflag_foot (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & OFF). unfold avoids, memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor]. }
    pose proof EO as (_ & EIN & O1 & O2 & O3 & O4 & XS). pose proof O1 as O1'. pose proof O3 as O3'. rewrite SUO in O3'. rewrite PNO in O1'. cbn [ofield] in O1', O3'.
    destruct O1' as (PNP & _ & PNIN). destruct O3' as (SUP & _ & SUIN).
    pose proof (suite_cells_size rows) as SSZ. rewrite ROWS in SSZ.
    assert (INS : In (ps, en_suites E, sn) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. do 2 (apply in_or_app; right). apply in_or_app. left. rewrite SUO. left. reflexivity. }
    assert (INP : In (pn, en_pname E, zlength ns + 1) (blocks_ENTRY ee E)).
    { unfold blocks_ENTRY. right. apply in_or_app. left. rewrite PNO. left. reflexivity. }
    assert (XPL1 : xpres LB (bv_unsigned sp) [] m m1) by (eapply xpres_weaken; [exact (XP1 [])| lia| exact SUBLB| auto]).
    assert (XPL2 : xpres LB (bv_unsigned sp + -80) memflag_foot m1 m2) by (eapply xpres_weaken; [exact XP2| lia| exact SUBLB| auto]).
    assert (AVF : avoids memflag_foot (bv_unsigned sp + -80) 80) by (unfold avoids, memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]).
    assert (FW : fworld H ra sp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 m mo LIB LB M ee lo B E rows ns A p m2 mo2 s2' M [] errv2 (vpm_empty p) []).
    { unfold fworld. unfold zlength in *. repeat match goal with |- _ /\ _ => split end.
      all: lazymatch goal with
           | |- mem_inv _ _ => exact MI2
           | |- stk _ _ _ _ => exact ST2
           | |- rw_cells _ _ (bv_unsigned _ + -80) _ => eapply xpres_rw_cells'; [exact XP2| exact FR1| left; lia| exact AVF]
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR2
           | |- hs_rauxv_ok _ _ _ => exact AUX2
           | |- hs_KREL _ _ _ => exact KREL2
           | |- hs_MPRES _ _ _ => exact MP2
           | |- hs_RHEAP _ _ _ _ => eapply PERM; [exact HP2|]; subst L0; cbn [app]; apply Permutation_middle
           | |- LIBMID _ _ _ => cbn [app]; destruct M as [f cph eph E0 v]; cbn [mid_flag] in MF0; subst f; exact (LIBMID_mf _ _ _ _ _ _ LM1 XP2 SUB0 MF2)
           | |- mid_step _ _ => unfold mid_step; split; [exact MF0|]; split; [auto|]; split; auto
           | |- mid_newlib_ok _ _ _ => unfold mid_newlib_ok; exists [], []; split; [apply Permutation_refl|]; rewrite CX; split; [reflexivity|]; destruct (mid_err M); reflexivity
           | |- mid_ctx _ = _ => reflexivity
           | |- mid_vdso _ = _ => reflexivity
           | |- ENTRYobj _ _ _ _ => eapply ENTRYobj_frameX; [eapply ENTRYobj_frameX; [exact EO| exact XPL1| intros b Hb; apply avoids_nil]| exact XPL2| intros b Hb; apply AVM; apply SUBLB; eapply ENTRYobj_owned_law; [exact EO| exact Hb]]
           | |- rw_cells _ _ (en_suites _) _ =>
               eapply xpres_rw_cells'; [exact XPL2| eapply rw_cells_transport; [exact SU| exact MU1| exact WM1| pose proof (HB _ (SUBLB _ SUIN)) as K; cbn [blk_addr blk_size fst snd] in K; cbn; clear - K SSZ SNR CEIL LO80; lia]| |];
               [ right; right; exists (ps, en_suites E, sn); split; [exact SUIN|]; cbn [blk_addr blk_size fst snd]; lia
               | eapply avoids_sub; [apply AVM; apply SUBLB; exact SUIN| cbn; lia| cbn [blk_addr blk_size fst snd]; lia] ]
           | |- bytes_at _ _ (en_pname _) _ =>
               eapply xpres_bytes_at; [exact XPL2| eapply bytes_at_transport; [exact PN| exact MU1| pose proof (HB _ (SUBLB _ PNIN)) as K; cbn [blk_addr blk_size fst snd] in K; rewrite length_app; cbn; clear - K CEIL LO80; lia]|]; split;
               [ right; right; exists (pn, en_pname E, Z.of_nat (length ns) + 1); split; [exact PNIN|]; cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia
               | eapply avoids_sub; [apply AVM; apply SUBLB; exact PNIN| cbn; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; lia] ]
           | |- VPMobj _ _ _ _ => eapply VPMobj_relist; [exact VO2|]; intros b Hb; cbn in Hb; destruct Hb as [<-|[]]; left; reflexivity
           | |- vp_id _ = _ => reflexivity
           | |- Permutation _ _ => apply Permutation_refl
           | |- Z.of_nat (length []) <= _ => cbn; lia
           | |- lb_bytes [] <= _ => unfold ADD1HOST_BYTES, SK_SIZE; cbn; lia
           | |- lb_big [] = _ => reflexivity
           | |- xpres _ _ _ _ _ =>
               eapply xpres_trans; [eapply xpres_weaken; [eapply (xpres_of_munch LB (bv_unsigned sp) (EF (mid_err M))); [exact MU1| exact WM1| constructor; [left; cbn; lia| constructor]| intros b Hb; apply HB; apply SUBLB; exact Hb]| lia| auto| auto]|];
               apply (xpres_weaken LB LB (bv_unsigned sp + -80) (bv_unsigned sp) ([] ++ []) (EF (mid_err M))); [| lia| auto| intros a Ha; destruct Ha];
               eapply xpres_drop_memflag; [exact MF1| exact MF2| cbn [app]; exact XPL2]
           | |- ?G => idtac "FW0" G
           end. }
    eapply (fcc_main H HX EGS); try eassumption.
    all: lazymatch goal with
         | |- lb_bytes _ + _ + _ + _ <= _ => subst L0; rewrite lb_bytes_app in BY; pose proof (lb_bytes_nonneg (mid_errblocks M) ltac:(apply Forall_forall; intros b Hb; pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & K & _); exact K)); clear - BY H0; lia
         | |- Z.of_nat (length _) + _ + _ + _ <= _ => subst L0; rewrite length_app, Nat2Z.inj_add in CN; clear - CN; lia
         | |- lb_big _ + _ <= _ => subst L0; rewrite lb_big_app in BG; pose proof (lb_big_nonneg (mid_errblocks M)); clear - BG H0; lia
         | |- _ = _ => reflexivity
         end.
  Qed.
End WS.
