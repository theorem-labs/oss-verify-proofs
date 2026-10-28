(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Lemma live_remove_app : forall p (l1 l2 : list (Z * Z)), live_remove p (l1 ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof. intros p l1 l2. unfold live_remove. apply list_basics.list.filter_app. Qed.
Lemma live_remove_all_app : forall ps (l1 l2 : list (Z * Z)), live_remove_all ps (l1 ++ l2) = live_remove_all ps l1 ++ live_remove_all ps l2.
Proof. intros ps. induction ps as [|p ps IH]; intros l1 l2; cbn; [reflexivity|]. rewrite IH. apply live_remove_app. Qed.
Lemma live_remove_all_id : forall ps (l : list (Z * Z)), (forall e, In e l -> ~ In (fst e) ps) -> live_remove_all ps l = l.
Proof.
  intros ps. induction ps as [|p ps IH]; intros l H; cbn; [reflexivity|].
  rewrite (IH l) by (intros e He X; apply (H e He); right; exact X).
  apply live_remove_notin. intros e He X. apply (H e He). left. symmetry. exact X.
Qed.
Lemma live_remove_all_nil : forall ps (l : list (Z * Z)), (forall e, In e l -> In (fst e) ps) -> live_remove_all ps l = [].
Proof.
  intros ps l H. destruct (live_remove_all ps l) as [|e r] eqn:E; [reflexivity|].
  exfalso. pose proof (live_remove_all_sub ps l e ltac:(rewrite E; left; reflexivity)) as [H1 H2]. exact (H2 (H _ H1)).
Qed.
Lemma live_remove_length_le : forall p (l : list (Z * Z)), (length (live_remove p l) <= length l)%nat.
Proof. intros p l. unfold live_remove. apply list_basics.list.length_filter. Qed.
Lemma live_remove_all_length_le : forall ps (l : list (Z * Z)), (length (live_remove_all ps l) <= length l)%nat.
Proof. intros ps. induction ps as [|p ps IH]; intros l; cbn; [lia|]. pose proof (live_remove_length_le p (live_remove_all ps l)). pose proof (IH l). lia. Qed.
Lemma live_remove_perm1 : forall p (l l' : list (Z * Z)), Permutation l l' -> Permutation (live_remove p l) (live_remove p l').
Proof.
  intros p l l' HP. unfold live_remove. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - apply perm_nil.
  - destruct (decide _); [apply perm_skip; exact IH| exact IH].
  - destruct (decide _), (decide _); try apply perm_swap; try apply Permutation_refl; apply perm_skip; apply Permutation_refl.
  - exact (Permutation_trans IH1 IH2).
Qed.
Lemma live_remove_all_perm : forall ps (l l' : list (Z * Z)), Permutation l l' -> Permutation (live_remove_all ps l) (live_remove_all ps l').
Proof. intros ps. induction ps as [|p ps IH]; intros l l' HP; cbn; [exact HP|]. apply live_remove_perm1. apply IH. exact HP. Qed.
(* [comment removed for export] *)
Lemma live_remove_all_split : forall ps (l l1 l2 : list (Z * Z)), Permutation l (l1 ++ l2) ->
  (forall e, In e l1 -> In (fst e) ps) -> (forall e, In e l2 -> ~ In (fst e) ps) -> Permutation (live_remove_all ps l) l2.
Proof.
  intros ps l l1 l2 HP H1 H2. eapply Permutation_trans; [apply live_remove_all_perm; exact HP|].
  rewrite live_remove_all_app, (live_remove_all_nil ps l1 H1), (live_remove_all_id ps l2 H2). apply Permutation_refl.
Qed.
Lemma live_remove_split : forall p n (l l2 : list (Z * Z)), Permutation l ((p, n) :: l2) ->
  (forall e, In e l2 -> fst e <> p) -> Permutation (live_remove p l) l2.
Proof.
  intros p n l l2 HP H2. change (live_remove p l) with (live_remove_all [p] l). apply (live_remove_all_split [p] l [(p, n)] l2 HP).
  - intros e [<-|[]]. left. reflexivity.
  - intros e He [X|[]]. exact (H2 e He (eq_sym X)).
Qed.
(* [comment removed for export] *)
Lemma outside_app_l : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x.
Proof. intros W1 W2 x. induction W1 as [|[lo hi] W1 IH]; cbn; [intros _; exact I|]. intros [H1 H2]. split; [exact H1| exact (IH H2)]. Qed.
Lemma outside_app_r : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W2 x.
Proof. intros W1 W2 x. induction W1 as [|[lo hi] W1 IH]; cbn; [intros H; exact H|]. intros [_ H2]. exact (IH H2). Qed.
Lemma outside_elim : forall (W : list (Z * Z)) x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv).
Proof. intros W x iv. induction W as [|[lo hi] W IH]; cbn; [intros _ []|]. intros [H1 H2] [<-|Hin]; [exact H1| exact (IH H2 Hin)]. Qed.

Section W3X.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable GOBJ : Z -> Z -> Prop.
  Hypothesis AFP : art_facts_pem RT GOBJ.
  Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
  Variable libenv_fp : list (Z * Z) -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
  Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
  Variables FZ_SITES FZ_CALLS : list (Z * Z).

  Local Notation pem_entry := (pem_entry RT).
  Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
  Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
  Local Notation pem_frame := (pem_frame RT).
  Local Notation pem_ms := (pem_ms RT).

  Lemma outside_LIB_W : forall x, (x < 0x5a9f20 \/ 0xbc5698 <= x) -> outside LIB_W x.
  Proof. intros x Hx. unfold LIB_W. cbn. repeat split; try exact I; lia. Qed.

  (* [comment removed for export] *)
  Definition rng (e : Z * Z) : Z * Z := (fst e, fst e + snd e).
  Definition w_ok (en : pem_entry) (Σ : rts RT) (XL W : list (Z * Z)) : Prop :=
       (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside W x)
    /\ (forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside W x)
    /\ (forall x, e_f RT en <= x < e_f RT en + 120 -> outside W x)
    /\ (forall x, shad (e_f RT en) <= x < shad (e_f RT en) + 16 -> outside W x)
    /\ (forall p n x, In (p, n) (rt_live RT Σ) -> ~ In (p, n) XL -> p <= x < p + n -> outside W x)
    /\ (forall a, aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a -> outside (pem_W RT en) a -> outside W a).

  Lemma com_W_ok_gen : forall (en : pem_entry) Σ (m : mem) off crem lrem cur (pre : list (Z * Z)),
    pem_com en Σ m off crem lrem cur -> (pre = [] \/ pre = [(e_E RT en, 904)]) -> w_ok en Σ (pre ++ e_LBL RT en) (map rng pre ++ lib_W (e_LBL RT en)).
  Proof using AF AFP.
    intros en Σ m off crem lrem cur pre COM HPRE.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV].
    assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
    pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 INF) as [SF4 _]. change (fs_size 1) with (64 * 2) in SF4. rewrite (shad_add64 _ 2 F64) in SF4.
    (* [comment removed for export] *)
    set (named := fun p n => In (p, n) (pre ++ e_LBL RT en)).
    assert (NLV : forall p n, named p n -> In (p, n) (rt_live RT Σ)).
    { intros p n H. apply in_app_iff in H. destruct H as [H|H]; [| exact (ELV _ (INCL _ H))]. destruct HPRE as [-> | ->]; [destruct H| destruct H as [H|[]]]. injection H; intros E1 E2; rewrite <- E1, <- E2; exact (ELV _ INE). }
    assert (GEN : forall x, (x < 0x5a9f20 \/ 0xbc5698 <= x) -> (forall p n, named p n -> ~ (p <= x < p + n)) -> outside (map rng pre ++ lib_W (e_LBL RT en)) x).
    { intros x Hx HL. apply outside_app_intro.
      - destruct HPRE as [-> | ->]; cbn; [exact I|]. split; [| exact I]. apply (HL (e_E RT en) 904). apply in_or_app; left; left; reflexivity.
      - unfold lib_W. apply outside_app_intro; [exact (outside_LIB_W x Hx)|]. apply outside_intro. intros iv Hiv. apply in_map_iff in Hiv.
        destruct Hiv as ([p n] & <- & Hin). cbn [fst snd]. apply (HL p n). apply in_or_app; right; exact Hin. }
    split. { intros x Hx. apply GEN; [clear - Hx HLOS LOR; unfold e_sp1, RT_STACK, PEM_CALLEE_STACK in *; lia|]. intros p n Hn.
             pose proof (af_live_range RT AF Σ m p n ART0 (NLV p n Hn)) as (_ & X & _). clear - X Hx LOR LOW. unfold e_sp1, RT_STACK, PEM_CALLEE_STACK in *. lia. }
    assert (FRG : forall f k x, In (f, k) (rt_frames RT Σ) -> f <= x < f + fs_size k - 8 -> outside (map rng pre ++ lib_W (e_LBL RT en)) x).
    { intros f k x Hin Hx. pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & FS & FR4). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). unfold fs_size in *.
      apply GEN; [clear - FS Hx H; unfold SEGTOP_A in FS; lia|]. intros p n Hn. destruct (FR4 p n (NLV p n Hn)) as [Q|Q]; clear - Q Hx H; lia. }
    split; [intros f k x Hin Hx; exact (FRG f k x ltac:(rewrite FRS; right; exact Hin) Hx)|].
    split; [intros x Hx; exact (FRG (e_f RT en) 1%nat x INF ltac:(change (fs_size 1) with 128; clear - Hx; lia))|].
    split. { intros x Hx. apply GEN; [clear - Hx F0; unfold shad, SHB in *; Z.div_mod_to_equations; lia|]. intros p n Hn. destruct (SF4 p n (NLV p n Hn)) as [Q|Q]; clear - Q Hx; lia. }
    split. { intros p n x Hin NIN Hx. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & _ & Y). apply GEN; [clear - Y Hx; unfold SEGTOP_A in Y; lia|].
             intros p' n' Hn' R. assert (NE' : (p, n) <> (p', n')) by (intros E; rewrite E in NIN; exact (NIN Hn')).
             destruct (live_ne_apart RT AF Σ m p n p' n' ART0 Hin (NLV _ _ Hn') NE') as [Q|Q]; clear - Q Hx R; lia. }
    intros a _ Ha. unfold pem_W in Ha. apply outside_app_intro; [| exact (outside_app_r _ _ _ (outside_app_r _ _ _ Ha))].
    destruct HPRE as [-> | ->]; cbn; [exact I|]. split; [| exact I]. apply outside_app_l in Ha.
    exact (outside_elim _ a (e_E RT en, e_E RT en + 904) Ha ltac:(do 4 right; left; reflexivity)).
  Qed.
  Lemma com_W_ok : forall (en : pem_entry) Σ (m : mem) off crem lrem cur, pem_com en Σ m off crem lrem cur -> w_ok en Σ (e_LBL RT en) (lib_W (e_LBL RT en)).
  Proof using AF AFP. intros en Σ m off crem lrem cur COM. exact (com_W_ok_gen en Σ m off crem lrem cur [] COM (or_introl eq_refl)). Qed.
  Lemma com_WE_ok : forall (en : pem_entry) Σ (m : mem) off crem lrem cur,
    pem_com en Σ m off crem lrem cur -> w_ok en Σ ((e_E RT en, 904) :: e_LBL RT en) ((e_E RT en, e_E RT en + 904) :: lib_W (e_LBL RT en)).
  Proof using AF AFP. intros en Σ m off crem lrem cur COM. exact (com_W_ok_gen en Σ m off crem lrem cur [(e_E RT en, 904)] COM (or_intror eq_refl)). Qed.
  (* [comment removed for export] *)
  Lemma com_WB_ok : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL,
    pem_com en Σ m off crem lrem cur -> (forall e, In e XL -> (In e cur /\ 0 < snd e) \/ In e (mbio_ent (e_K RT en) (e_bmax RT en))) -> w_ok en Σ XL (map rng XL).
  Proof using AF AFP.
    intros en Σ m off crem lrem cur XL COM HXL.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV].
    assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
    pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 INF) as [SF4 _]. change (fs_size 1) with (64 * 2) in SF4. rewrite (shad_add64 _ 2 F64) in SF4.
    assert (NLV : forall p n, In (p, n) XL -> In (p, n) (rt_live RT Σ)).
    { intros p n H. destruct (HXL _ H) as [[H1 _]|H1]; [exact (CLV _ H1)| exact (ELV _ (KLV _ H1))]. }
    assert (GEN : forall x, (forall p n, In (p, n) XL -> ~ (p <= x < p + n)) -> outside (map rng XL) x).
    { intros x HL. apply outside_intro. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as ([p n] & <- & Hin). cbn [rng fst snd]. exact (HL p n Hin). }
    split. { intros x Hx. apply GEN. intros p n Hn. pose proof (af_live_range RT AF Σ m p n ART0 (NLV p n Hn)) as (_ & X & _). clear - X Hx LOR LOW. unfold e_sp1, RT_STACK, PEM_CALLEE_STACK in *. lia. }
    assert (FRG : forall f k x, In (f, k) (rt_frames RT Σ) -> f <= x < f + fs_size k - 8 -> outside (map rng XL) x).
    { intros f k x Hin Hx. pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & FS & FR4). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). unfold fs_size in *.
      apply GEN. intros p n Hn. destruct (FR4 p n (NLV p n Hn)) as [Q|Q]; clear - Q Hx H; lia. }
    split; [intros f k x Hin Hx; exact (FRG f k x ltac:(rewrite FRS; right; exact Hin) Hx)|].
    split; [intros x Hx; exact (FRG (e_f RT en) 1%nat x INF ltac:(change (fs_size 1) with 128; clear - Hx; lia))|].
    split. { intros x Hx. apply GEN. intros p n Hn. destruct (SF4 p n (NLV p n Hn)) as [Q|Q]; clear - Q Hx; lia. }
    split. { intros p n x Hin NIN Hx. apply GEN. intros p' n' Hn' R. assert (NE' : (p, n) <> (p', n')) by (intros E; rewrite E in NIN; exact (NIN Hn')).
             destruct (live_ne_apart RT AF Σ m p n p' n' ART0 Hin (NLV _ _ Hn') NE') as [Q|Q]; clear - Q Hx R; lia. }
    intros a Ha Ho. apply GEN. intros p n Hn R. destruct (HXL _ Hn) as [[H1 H2]|H1].
    - exact (proj2 (proj2 (proj2 (proj2 (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur (p, n) COM H1 H2)))) a R Ha).
    - unfold pem_W in Ho. apply outside_app_r, outside_app_l in Ho. apply (outside_elim _ a (p, p + n) Ho); [| exact R].
      unfold mbio_W. apply in_map_iff. exists (p, n). split; [reflexivity| exact H1].
  Qed.
  (* [comment removed for export] *)
  Lemma com_E_out : forall (en : pem_entry) Σ (m : mem) off crem lrem cur,
    pem_com en Σ m off crem lrem cur -> forall x, e_E RT en <= x < e_E RT en + 904 -> outside (lib_W (e_LBL RT en)) x.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur COM x Hx.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & REST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV].
    pose proof (af_live_range RT AF Σ m _ _ ART0 (ELV _ INE)) as (_ & _ & Y).
    unfold lib_W. apply outside_app_intro; [apply outside_LIB_W; clear - Y Hx; unfold SEGTOP_A in Y; lia|]. apply outside_intro. intros iv Hiv. apply in_map_iff in Hiv.
    destruct Hiv as ([p n] & <- & Hin). cbn [fst snd]. intros R. assert (NE : (e_E RT en, 904) <> (p, n)) by (intros E; rewrite <- E in Hin; exact (NLE Hin)).
    destruct (live_ne_apart RT AF Σ m (e_E RT en) 904 p n ART0 (ELV _ INE) (ELV _ (INCL _ Hin)) NE) as [Q|Q]; clear - Q Hx R; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition w_live (Σ : rts RT) (XL W : list (Z * Z)) : Prop :=
    forall p n x, In (p, n) (rt_live RT Σ) -> ~ In (p, n) XL -> p <= x < p + n -> outside W x.
  Lemma com_cur_out : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL W,
    pem_com en Σ m off crem lrem cur -> w_live Σ XL W -> (forall e, In e XL -> In e ((e_E RT en, 904) :: e_LBL RT en)) ->
    forall e x, In e cur -> fst e <= x < fst e + snd e -> outside W x.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur XL W COM WL HXL e x He Hx.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & REST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV]. destruct e as [p n]. cbn [fst snd] in Hx.
    apply (WL p n x (CLV _ He)); [| exact Hx]. intros X. destruct (HXL _ X) as [E|X2].
    - pose proof (nd_split _ _ ND) as (_ & _ & DJ). apply (DJ p (in_map fst _ _ He)). left. injection E. intros _ ->. reflexivity.
    - apply (CFR _ He). cbn [fst]. apply (in_map fst _ _ (INCL _ X2)).
  Qed.
  Lemma com_klv_out : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL W,
    pem_com en Σ m off crem lrem cur -> w_live Σ XL W -> (forall e, In e XL -> In e ((e_E RT en, 904) :: e_LBL RT en)) ->
    forall e x, In e (mbio_ent (e_K RT en) (e_bmax RT en)) -> fst e <= x < fst e + snd e -> outside W x.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur XL W COM WL HXL e x He Hx.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & REST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV]. destruct e as [p n]. cbn [fst snd] in Hx.
    assert (HB : In p (mbio_blocks (e_K RT en))) by (rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)); apply (in_map fst _ _ He)).
    apply (WL p n x (ELV _ (KLV _ He))); [| exact Hx]. intros X. pose proof (HXL _ X) as X2.
    apply (NTL (p, n) X2). apply in_or_app; left. exact HB.
  Qed.
  Lemma com_ff_out : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL W,
    pem_com en Σ m off crem lrem cur -> w_ok en Σ XL W -> forall x, e_f RT en <= x < e_f RT en + 120 -> outside W x.
  Proof using AF AFP. intros en Σ m off crem lrem cur XL W COM (WS & WFR & WFF & WSH & WL & WP) x Hx. exact (WFF x Hx). Qed.
  (* [comment removed for export] *)
  Lemma pem_frame_keep : forall (en : pem_entry) (m m' : mem) KEEP fr W j0 lH lF endv hBv dBv x1 x2 gap,
    pem_frame en m j0 lH lF endv hBv dBv x1 x2 gap -> rt_pres_fp KEEP fr (e_sp1 RT en) W m m' ->
    (e_pd RT en = 0 \/ e_pd RT en = 16) -> e_PL RT en + 16 <= USTACK_TOP ->
    (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside W x) -> pem_frame en m' j0 lH lF endv hBv dBv x1 x2 gap.
  Proof.
    intros en m m' KEEP fr W j0 lH lF endv hBv dBv x1 x2 gap (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE & FR224 & FRG) PR PD TOP HWS.
    assert (G : forall A cs, rw_cells asegs m A cs -> e_sp1 RT en <= A -> A + Z.of_nat (cells_size cs) <= e_PL RT en -> rw_cells asegs m' A cs).
    { intros A cs C H1 H2. eapply stack_keep; [exact C| exact PR| exact H1| lia|]. intros x Hx. apply HWS. lia. }
    unfold e_sp1 in *.
    split; [apply (G _ _ FR0); cbn [cells_size csize Nat.add]; lia|]. split; [apply (G _ _ FRH); [lia| rewrite SZH; lia]|]. split; [exact SZH|].
    split; [apply (G _ _ FRF); [lia| rewrite SZF; lia]|]. split; [exact SZF|]. split; [apply (G _ _ FR104); cbn [cells_size csize Nat.add]; lia|].
    split; [apply (G _ _ FRE); [lia| unfold loc_E; cbn [cells_size csize Nat.add]; lia]|]. split; [apply (G _ _ FR224); cbn [cells_size csize Nat.add]; lia|].
    apply (G _ _ FRG); cbn [cells_size csize Nat.add]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ff_keep : forall (m m' : mem) f KEEP fr sp W hj lenv j1 tav j2 bmv j3,
    rw_cells asegs m f (ff_cells hj lenv j1 tav j2 bmv j3) -> rt_pres_fp KEEP fr sp W m m' -> In (f, 1%nat) fr ->
    (forall x, f <= x < f + 120 -> outside W x) -> rw_cells asegs m' f (ff_cells hj lenv j1 tav j2 bmv j3).
  Proof.
    intros m m' f KEEP fr sp W hj lenv j1 tav j2 bmv j3 C PR INF HWF. eapply frame_keep; [exact C| exact PR| exact INF| lia| unfold ff_cells; cbn [cells_size csize Nat.add]; lia|].
    intros x Hx. apply HWF. unfold ff_cells in Hx. cbn [cells_size csize Nat.add] in Hx. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma pem_out_agree : forall ret (m m' : mem) PN PH PD PL news,
    pem_out ret m PN PH PD PL news ->
    (forall P, In P [PN; PH; PD; PL] -> agree_on (fun x => P <= x < P + 8) m m') ->
    (forall e, In e news -> agree_on (fun x => fst e <= x < fst e + snd e) m m') ->
    pem_out ret m' PN PH PD PL news.
  Proof.
    intros ret m m' PN PH PD PL news PO AGP AGN.
    assert (G8 : forall P v, In P [PN; PH; PD; PL] -> rw_cells asegs m P [C8 v] -> rw_cells asegs m' P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    assert (GB : forall p n bs, In (p, n) news -> length bs = Z.to_nat n -> 0 <= n -> rw_cells asegs m p [CB (Z.to_nat n) bs] -> rw_cells asegs m' p [CB (Z.to_nat n) bs]).
    { intros p n bs Hin L N C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact N. exact (AGN (p, n) Hin). }
    destruct PO as [(R & N & C1 & C2 & C3 & (lw & C4))|(R & NM & HD & DT & nn & nh & dlen & bn & bh & bd & N & B1 & B2 & B3 & C1 & C2 & C3 & C4 & L1 & D1 & Z1 & L2 & D2 & Z2 & L3 & D3)].
    - left. split; [exact R|]. split; [exact N|]. split; [apply G8; [cbn; tauto| exact C1]|]. split; [apply G8; [cbn; tauto| exact C2]|].
      split; [apply G8; [cbn; tauto| exact C3]|]. exists lw. apply G8; [cbn; tauto| exact C4].
    - right. split; [exact R|]. exists NM, HD, DT, nn, nh, dlen, bn, bh, bd. split; [exact N|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      split; [apply G8; [cbn; tauto| exact C1]|]. split; [apply G8; [cbn; tauto| exact C2]|]. split; [apply G8; [cbn; tauto| exact C3]|]. split; [apply G8; [cbn; tauto| exact C4]|].
      subst news. split; [exact L1|]. split; [apply GB; [cbn; tauto| exact L1| lia| exact D1]|]. split; [exact Z1|].
      split; [exact L2|]. split; [apply GB; [cbn; tauto| exact L2| lia| exact D2]|]. split; [exact Z2|]. split; [exact L3|]. apply GB; [cbn; tauto| exact L3| lia| exact D3].
  Qed.

  (* [comment removed for export] *)
  Lemma com_out_agree : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP W,
    pem_com en Σ m off crem lrem cur -> (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside W x) ->
    (forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside W x) ->
    rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
    forall P, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> agree_on (fun x => P <= x < P + 8) m m'.
  Proof using AF AFP.
    intros en Σ m m' off crem lrem cur KEEP W COM WS WFR PR P HP a Ha. cbv beta in Ha.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    assert (HL : pp_loc (e_frames RT en) (e_m RT en) USTACK_TOP P) by exact (proj2 (proj1 (Forall_forall _ _) OUTS P HP)).
    destruct HL as [ [H1 H2] | (f & k & Hin & H1 & H2 & _) ].
    - apply PR; [apply acl_stack; unfold e_sp1; clear - H1 H2 Ha PD; lia| apply WS; unfold e_sp1; clear - H1 H2 Ha PD; lia].
    - assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
      apply PR; [apply (acl_frame _ _ _ f k); [exact Hin'| clear - H1 H2 Ha; lia]| apply (WFR f k _ Hin); clear - H1 H2 Ha; lia].
  Qed.
  Lemma com_cur_agree : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP XL W e,
    pem_com en Σ m off crem lrem cur -> w_live Σ XL W -> (forall e, In e XL -> In e ((e_E RT en, 904) :: e_LBL RT en)) ->
    rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
    In e cur -> In e KEEP -> agree_on (fun x => fst e <= x < fst e + snd e) m m'.
  Proof using AF AFP.
    intros en Σ m m' off crem lrem cur KEEP XL W e COM WL HXL PR He HK a Ha. cbv beta in Ha. pose proof (com_cur_out en Σ m off crem lrem cur XL W COM WL HXL e _ He Ha) as HO.
    destruct e as [p n]. cbn [fst snd] in Ha. apply PR; [apply (acl_live _ _ _ p n); [exact HK| exact Ha]| exact HO].
  Qed.
  Lemma com_err_keep : forall (en : pem_entry) Σ Σ' (m m' : mem) off crem lrem cur strs,
    pem_com en Σ m off crem lrem cur -> pem_err en Σ strs m -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
    (forall e, In e strs -> In e cur) -> In (e_E RT en, 904) (rt_live RT Σ') -> (forall e, In e strs -> In e (rt_live RT Σ')) -> pem_err en Σ' strs m'.
  Proof using AF AFP errst_rest_agree errst_live_agree errst_fp_where.
    intros en Σ Σ' m m' off crem lrem cur strs COM PE PR SC INE' SL'.
    eapply (pem_err_keep RT errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where en Σ Σ' strs m m');
      [exact PE| exact PR| exact INE'| exact SL'| exact (com_E_out en Σ m off crem lrem cur COM)| | exact SL'].
    intros e x He Hx. pose proof (com_W_ok en Σ m off crem lrem cur COM) as (_ & _ & _ & _ & WL & _). exact (com_cur_out en Σ m off crem lrem cur _ _ COM WL (fun e H => or_intror H) e x (SC _ He) Hx).
  Qed.
  (* [comment removed for export] *)
  Lemma pem_site_in : forall r, In r PEM_RAS -> In (r, FZ_PEM_READ_BIO) PEM_SITES.
  Proof. intros r Hr. unfold PEM_SITES. apply in_map_iff. exists r. split; [reflexivity| exact Hr]. Qed.

  (* [comment removed for export] *)
  Lemma com_call_pre : forall (en : pem_entry) Σ (m : mem) off crem lrem cur site G,
    pem_com en Σ m off crem lrem cur -> In (site, FZ_PEM_READ_BIO) PEM_SITES -> In (site, G) PEM_CALLS -> 0 <= site < 2 ^ 64 ->
       bv_unsigned (wz (e_sp1 RT en)) = e_sp1 RT en
    /\ call_ok RT Σ m (wz (e_sp1 RT en)) (e_lo RT en)
    /\ cg_ctx (rt_cg RT Σ) G (bv_unsigned (wz site) :: bv_unsigned (e_ra RT en) :: e_outer RT en)
    /\ uw_chain m (wz (e_sp1 RT en)) (e_sp RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en)
    /\ incl_live (e_LBL RT en) (rt_live RT Σ)
    /\ (length (rt_frames RT Σ) < FRAMES_MAX)%nat /\ crem <= rt_credit RT Σ
    /\ e_lo RT en <= e_sp1 RT en /\ e_sp1 RT en + 352 <= e_PL RT en.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur site G COM HS HC SR.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV].
    assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
    assert (EU : bv_unsigned (wz (e_sp1 RT en)) = e_sp1 RT en) by (apply unsigned_lit; clear - HLO HLOS TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
    split; [exact EU|].
    split. { unfold call_ok. rewrite EU. split; [exact ST|]. split; [exact LOW|]. split; [clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia|].
             split; [clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia|]. clear - PDM PD. unfold e_sp1 in *. Z.div_mod_to_equations. lia. }
    assert (HS' : In (site, FZ_PEM_READ_BIO) (cg_site (rt_cg RT Σ))) by exact (proj1 CGH _ (proj1 CGS _ HS)).
    assert (HC' : In (site, G) (cg_call (rt_cg RT Σ))) by exact (proj2 CGH _ (proj2 CGS _ HC)).
    assert (FRR : rw_cells asegs m (bv_unsigned (e_sp RT en) - 16) [C8 (e_s0 RT en); C8 (e_ra RT en)]).
    { unfold pem_saved in SAVED. replace (bv_unsigned (e_sp RT en) - 16) with (e_PL RT en + -104 + Z.of_nat (cells_size
        [C8 (e_s11 RT en); C8 (e_s10 RT en); C8 (e_s9 RT en); C8 (e_s8 RT en); C8 (e_s7 RT en); C8 (e_s6 RT en); C8 (e_s5 RT en); C8 (e_s4 RT en); C8 (e_s3 RT en); C8 (e_s2 RT en); C8 (e_s1 RT en)]))
        by (cbn [cells_size csize Nat.add]; unfold e_PL; lia).
      exact (rw_cells_skip m _ [C8 (e_s11 RT en); C8 (e_s10 RT en); C8 (e_s9 RT en); C8 (e_s8 RT en); C8 (e_s7 RT en); C8 (e_s6 RT en); C8 (e_s5 RT en); C8 (e_s4 RT en); C8 (e_s3 RT en); C8 (e_s2 RT en); C8 (e_s1 RT en)] _ SAVED). }
    destruct (cl_chain_call (rt_cg RT Σ) FZ_PEM_READ_BIO G site m m (e_ra RT en) (e_s0 RT en) (e_sp RT en) (wz (e_sp1 RT en)) (e_outer RT en) CTX HS' HC' UWC
                ltac:(intros a _; reflexivity) FRR ltac:(rewrite EU; unfold e_sp1, e_PL in *; clear - PD; lia) ltac:(unfold e_PL in TOP; exact TOP)) as [CTX1 UWC1].
    split; [rewrite (unsigned_lit site) by exact SR; exact CTX1|]. split; [exact UWC1|].
    split; [intros e He; exact (ELV _ (INCL _ He))|].
    split; [rewrite FRS; cbn [length]; clear - FRN; lia|]. split; [clear - CR CRE; lia|].
    split; [exact HLO|]. unfold e_sp1. clear - PD; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_bfree : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem rest K BIv BM blw meth len max offK site
           (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem (mbio_ent K max ++ rest) ->
    mbio_repx (rt_live RT Σ) m K BIv BM blw meth len max offK ->
    1 <= crem -> In site PEM_RAS_bfree ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_FREE m F fc (wz site) t0 t1 t2 (wz BIv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off (crem - 1) lrem rest ->
       rt_live RT Σ' = live_remove_all (mbio_blocks K) (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
       (forall e, In e (rest ++ e_live RT en) -> In e (rt_live RT Σ')) ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BF T en Σ m off crem lrem rest K BIv BM blw meth len max offK site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c
           COM MBX CRM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_W_ok en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_bfree in HSI; cbn in HSI; lia).
    assert (HC : In (site, FZ_BIO_FREE) PEM_CALLS).
    { unfold PEM_CALLS. rewrite !in_app_iff. right; right; right; left. apply in_map_iff. exists site. split; [reflexivity| exact HSI]. }
    destruct (com_call_pre en Σ m off crem lrem _ site FZ_BIO_FREE COM (pem_site_in _ HSR) HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    (* [comment removed for export] *)
    assert (KIDS : forall q, In q (mbio_blocks K) -> ~ In q (map fst rest) /\ ~ In q (map fst (e_live RT en)) /\ ~ In q (e_E RT en :: mbio_blocks (e_K RT en))).
    { intros q Hq. rewrite map_app, mbio_ent_fst, <- app_assoc in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ).
      split; [intros X; exact (DJ q Hq ltac:(apply in_or_app; left; exact X))|].
      split; [| intros X; exact (DJ q Hq ltac:(apply in_or_app; right; exact X))].
      rewrite <- (mbio_ent_fst K max) in Hq. apply in_map_iff in Hq. destruct Hq as (e & <- & He). exact (CFR e ltac:(apply in_or_app; left; exact He)). }
    assert (NTLK : forall e, In e (e_LBL RT en) -> ~ In (fst e) (mbio_blocks K)).
    { intros e He X. apply (NTL e ltac:(right; exact He)). apply in_or_app; right. rewrite map_app, mbio_ent_fst. apply in_or_app; left; exact X. }
    apply (C_BF Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz BIv) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) K (e_E RT en) BIv BM meth len max offK blw FDO MST eq_refl eq_refl LE INCL1 NTLK MBX ART0 MI COK
             ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BFREE_STACK in *; lia) CLE SEC CTX1 UWC1 CGH FRMAX ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & LV' & FRS' & SP' & CR' & CG'). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & LE1 & SEC1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_bfree in HSI; cbn in HSI; lia).
    (* [comment removed for export] *)
    assert (KP : incl_live (e_live RT en) (live_remove_all (mbio_blocks K) (rt_live RT Σ))).
    { intros e He. apply live_remove_all_keep; [exact (ELV _ He)|]. intros X. apply (proj1 (proj2 (KIDS _ X))). apply in_map. exact He. }
    assert (PERM1 : Permutation (rt_live RT Σ') (rest ++ e_live RT en)).
    { rewrite LV'. apply (live_remove_all_split _ _ (mbio_ent K max)); [rewrite app_assoc; exact PERM| intros e He; rewrite <- (mbio_ent_fst K max); apply in_map; exact He|].
      intros e He X. apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (KIDS _ X) (in_map fst _ _ He))| exact (proj1 (proj2 (KIDS _ X)) (in_map fst _ _ He))]. }
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| intros e He; exact (Permutation_in _ (Permutation_sym PERM1) He)| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - 1) lrem lrem _ rest _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| exact LR0
       | rewrite LV'; pose proof (live_remove_all_length_le (mbio_blocks K) (rt_live RT Σ)); clear - H; lia
       | exact KP| exact HWP| exact HWS| exact HWF| exact PERM1
       | intros e He; exact (CFR e ltac:(apply in_or_app; right; exact He))
       | rewrite map_app, mbio_ent_fst, <- app_assoc in ND; exact (proj1 (proj2 (nd_split _ _ ND)))
       | intros e He; apply LPOS; rewrite LV' in He; exact (proj1 (live_remove_all_sub _ _ _ He))
       | intros e He X; apply (NTL e He); apply in_app_iff in X; apply in_or_app; destruct X as [X|X]; [left; exact X| right; rewrite map_app; apply in_or_app; right; exact X]].
    (* [comment removed for export] *)
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| |].
    - intros e He. pose proof (ELV _ (KLV _ He)) as He2.
      assert (NK : ~ In (fst e) (mbio_blocks K)).
      { intros X. apply (proj2 (proj2 (KIDS _ X))). right. rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)). apply in_map. exact He. }
      split; [exact (live_remove_all_keep _ _ _ He2 NK)| rewrite LV'; exact (live_remove_all_keep _ _ _ He2 NK)].
    - intros e x He Hx. exact (com_klv_out en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma com_perm : forall (en : pem_entry) Σ (m : mem) off crem lrem cur cur',
    pem_com en Σ m off crem lrem cur -> Permutation cur cur' -> pem_com en Σ m off crem lrem cur'.
  Proof.
    intros en Σ m off crem lrem cur cur' COM HP.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & REST).
    pose proof (Permutation_map fst HP) as HPM.
    split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|].
    split; [exact HLOS|]. split; [exact CLE|]. split; [exact SEC|]. split; [exact LE|]. split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|].
    split. { intros e He X. apply (NTL e He). apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right; exact (Permutation_in _ (Permutation_sym HPM) X)]. }
    split; [exact MB|]. split; [exact OFF|]. split; [exact BLT|]. split; [exact KLV|].
    split; [exact (Permutation_trans PERM (Permutation_app_tail _ HP))|].
    split; [intros e He; exact (CFR e (Permutation_in _ (Permutation_sym HP) He))|].
    split; [exact (Permutation_NoDup (Permutation_app_tail _ HPM) ND)| exact REST].
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_pfree : pem_free_stmt RT libenv FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem rest p n num site
           (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem ((p, n) :: rest) -> (0 <= num <= n /\ num < 2 ^ 40) -> In site PEM_RAS_pfree ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_PEM_FREE m F fc (wz site) t0 t1 t2 (wz p) (wz (e_flags RT en)) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off crem lrem rest ->
       rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
       (forall e, In e (rest ++ e_live RT en) -> In e (rt_live RT Σ')) ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_PF T en Σ m off crem lrem rest p n num site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM NUM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_W_ok en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_pfree in HSI; cbn in HSI; lia).
    assert (HC4 : forall G, In G [FZ_PEM_FREE; e_CRYPTO_free; e_free; e_CRYPTO_secure_clear_free] -> In (site, G) PEM_CALLS).
    { intros G HG. unfold PEM_CALLS. rewrite !in_app_iff. right; right; left. apply in_concat. exists [(site, FZ_PEM_FREE); (site, e_CRYPTO_free); (site, e_free); (site, e_CRYPTO_secure_clear_free)].
      split; [apply in_map_iff; exists site; split; [reflexivity| exact HSI]|]. cbn in HG |- *. destruct HG as [<-|[<-|[<-|[<-|[]]]]]; tauto. }
    destruct (com_call_pre en Σ m off crem lrem _ site FZ_PEM_FREE COM (pem_site_in _ HSR) (HC4 FZ_PEM_FREE ltac:(cbn; tauto)) SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (HCG : forall G, In G [FZ_PEM_FREE; e_CRYPTO_free; e_free; e_CRYPTO_secure_clear_free] -> In (bv_unsigned (wz site), G) (cg_call (rt_cg RT Σ))).
    { intros G HG. rewrite (unsigned_lit site) by exact SR. exact (proj2 CGH _ (proj2 CGS _ (HC4 G HG))). }
    (* [comment removed for export] *)
    pose proof (nd_split [p] _ ND) as (_ & ND1 & DJ). cbn [map fst app] in DJ.
    assert (PE : ~ In p (map fst (e_live RT en))) by exact (CFR (p, n) ltac:(left; reflexivity)).
    assert (INP : In (p, n) (rt_live RT Σ)) by exact (CLV _ ltac:(left; reflexivity)).
    assert (NLP : ~ In (p, n) (e_LBL RT en)) by (intros X; apply PE; apply (in_map fst _ _ (INCL _ X))).
    apply (C_PF Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz p) (wz (e_flags RT en)) (wz num) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) p n num (e_flags RT en) FDO MST eq_refl eq_refl eq_refl eq_refl (proj1 NUM) (proj2 NUM) ltac:(pose proof (LPOS _ (CLV _ (or_introl eq_refl))) as XP; cbn [snd] in XP; clear - XP; lia) ltac:(clear - FLR; lia) INP NLP LE INCL1 ART0 MI COK
             ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, PFREE_STACK in *; lia) CLE SEC CTX1 UWC1 CGH
             (HCG e_CRYPTO_free ltac:(cbn; tauto)) (HCG e_free ltac:(cbn; tauto)) (HCG e_CRYPTO_secure_clear_free ltac:(cbn; tauto)) T c HA).
    intros c' (Σ' & AP & LV' & FRS' & SP' & CR' & CG'). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (LE1 & SEC1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_pfree in HSI; cbn in HSI; lia).
    assert (KP : incl_live (e_live RT en) (live_remove p (rt_live RT Σ))).
    { intros e He. apply live_remove_keep; [exact (ELV _ He)|]. intros X. apply PE. rewrite <- X. apply in_map. exact He. }
    assert (PERM1 : Permutation (rt_live RT Σ') (rest ++ e_live RT en)).
    { rewrite LV'. apply (live_remove_split p n); [exact PERM|]. intros e He X. apply in_app_iff in He. destruct He as [He|He].
      - exact (DJ p ltac:(left; reflexivity) ltac:(apply in_or_app; left; rewrite <- X; apply in_map; exact He)).
      - apply PE. rewrite <- X. apply in_map. exact He. }
    eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| intros e He; exact (Permutation_in _ (Permutation_sym PERM1) He)| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem crem lrem lrem _ rest _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| rewrite CR'; clear; lia| exact CR0| clear; lia| exact LR0
       | rewrite LV'; pose proof (live_remove_length_le p (rt_live RT Σ)); clear - H; lia
       | exact KP| exact HWP| exact HWS| exact HWF| exact PERM1
       | intros e He; exact (CFR e ltac:(right; exact He))
       | exact ND1
       | intros e He; apply LPOS; rewrite LV' in He; exact (live_remove_sub _ _ _ He)
       | intros e He X; apply (NTL e He); apply in_app_iff in X; apply in_or_app; destruct X as [X|X]; [left; exact X| right; right; exact X]].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| |].
    - intros e He. pose proof (ELV _ (KLV _ He)) as He2.
      assert (NK : fst e <> p) by (intros X; apply PE; rewrite <- X; apply in_map; exact (KLV _ He)).
      split; [exact (live_remove_keep _ _ _ He2 NK)| rewrite LV'; exact (live_remove_keep _ _ _ He2 NK)].
    - intros e x He Hx. exact (com_klv_out en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_pfree_null : pem_free_null_stmt RT libenv FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur num site
           (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> 0 <= num < 2 ^ 64 -> In site PEM_RAS_pfree ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_PEM_FREE m F fc (wz site) t0 t1 t2 (wz 0) (wz (e_flags RT en)) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off crem lrem cur ->
       rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_PFN T en Σ m off crem lrem cur num site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM NUM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_W_ok en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_pfree in HSI; cbn in HSI; lia).
    assert (HC4 : forall G, In G [FZ_PEM_FREE; e_CRYPTO_free; e_free; e_CRYPTO_secure_clear_free] -> In (site, G) PEM_CALLS).
    { intros G HG. unfold PEM_CALLS. rewrite !in_app_iff. right; right; left. apply in_concat. exists [(site, FZ_PEM_FREE); (site, e_CRYPTO_free); (site, e_free); (site, e_CRYPTO_secure_clear_free)].
      split; [apply in_map_iff; exists site; split; [reflexivity| exact HSI]|]. cbn in HG |- *. destruct HG as [<-|[<-|[<-|[<-|[]]]]]; tauto. }
    destruct (com_call_pre en Σ m off crem lrem _ site FZ_PEM_FREE COM (pem_site_in _ HSR) (HC4 FZ_PEM_FREE ltac:(cbn; tauto)) SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (HCG : forall G, In G [FZ_PEM_FREE; e_CRYPTO_free; e_free; e_CRYPTO_secure_clear_free] -> In (bv_unsigned (wz site), G) (cg_call (rt_cg RT Σ))).
    { intros G HG. rewrite (unsigned_lit site) by exact SR. exact (proj2 CGH _ (proj2 CGS _ (HC4 G HG))). }
    apply (C_PFN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz 0) (wz (e_flags RT en)) (wz num) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) num (e_flags RT en) FDO MST eq_refl eq_refl eq_refl eq_refl NUM ltac:(clear - FLR; lia) LE INCL1 ART0 MI COK
             ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, PFREE_STACK in *; lia) CLE SEC CTX1 UWC1 CGH
             (HCG e_CRYPTO_free ltac:(cbn; tauto)) (HCG e_free ltac:(cbn; tauto)) (HCG e_CRYPTO_secure_clear_free ltac:(cbn; tauto)) T c HA).
    intros c' (Σ' & AP & LV' & FRS' & SP' & CR' & CG'). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (_ & LE1 & SEC1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_pfree in HSI; cbn in HSI; lia).
    eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| exact CR0| clear; lia| exact LR0| rewrite LV'; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_out en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_cfree : evp_ctx_free_stmt RT FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem rest p site
           (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem ((p, ECTX) :: rest) -> In site PEM_RAS_cfree ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_EVP_CTX_FREE m F fc (wz site) t0 t1 t2 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off crem lrem rest ->
       rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) [] m m' ->
       (forall e, In e (rest ++ e_live RT en) -> In e (rt_live RT Σ')) ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_CF T en Σ m off crem lrem rest p site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_cfree in HSI; cbn in HSI; lia).
    assert (HC3 : forall G, In G [FZ_EVP_CTX_FREE; e_CRYPTO_free; e_free] -> In (site, G) PEM_CALLS).
    { intros G HG. unfold PEM_CALLS. rewrite !in_app_iff. do 9 right. apply in_concat. exists [(site, FZ_EVP_CTX_FREE); (site, e_CRYPTO_free); (site, e_free)].
      split; [apply in_map_iff; exists site; split; [reflexivity| exact HSI]|]. cbn in HG |- *. destruct HG as [<-|[<-|[<-|[]]]]; tauto. }
    destruct (com_call_pre en Σ m off crem lrem _ site FZ_EVP_CTX_FREE COM (pem_site_in _ HSR) (HC3 FZ_EVP_CTX_FREE ltac:(cbn; tauto)) SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (HCG : forall G, In G [FZ_EVP_CTX_FREE; e_CRYPTO_free; e_free] -> In (bv_unsigned (wz site), G) (cg_call (rt_cg RT Σ))).
    { intros G HG. rewrite (unsigned_lit site) by exact SR. exact (proj2 CGH _ (proj2 CGS _ (HC3 G HG))). }
    pose proof (nd_split [p] _ ND) as (_ & ND1 & DJ). cbn [map fst app] in DJ.
    assert (PE : ~ In p (map fst (e_live RT en))) by exact (CFR (p, ECTX) ltac:(left; reflexivity)).
    assert (INP : In (p, ECTX) (rt_live RT Σ)) by exact (CLV _ ltac:(left; reflexivity)).
    apply (C_CF Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en) p
             FDO MST eq_refl eq_refl INP ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK in *; lia) CLE CTX1 UWC1 CGH
             (HCG e_CRYPTO_free ltac:(cbn; tauto)) (HCG e_free ltac:(cbn; tauto)) T c HA).
    intros c' (Σ' & AP & LV' & FRS' & SP' & CR' & CG'). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & _) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_cfree in HSI; cbn in HSI; lia).
    assert (KP : incl_live (e_live RT en) (live_remove p (rt_live RT Σ))).
    { intros e He. apply live_remove_keep; [exact (ELV _ He)|]. intros X. apply PE. rewrite <- X. apply in_map. exact He. }
    assert (PERM1 : Permutation (rt_live RT Σ') (rest ++ e_live RT en)).
    { rewrite LV'. apply (live_remove_split p ECTX); [exact PERM|]. intros e He X. apply in_app_iff in He. destruct He as [He|He].
      - exact (DJ p ltac:(left; reflexivity) ltac:(apply in_or_app; left; rewrite <- X; apply in_map; exact He)).
      - apply PE. rewrite <- X. apply in_map. exact He. }
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (KP _ (INCL _ He))| intros x _; exact I]. }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply PR; [| exact I]. apply acl_static. rewrite Ea. apply client_static_intro. unfold SEC_INIT. clear; lia. }
    eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| intros e He; exact (Permutation_in _ (Permutation_sym PERM1) He)| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem crem lrem lrem _ rest _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| rewrite CR'; clear; lia| exact CR0| clear; lia| exact LR0
       | rewrite LV'; pose proof (live_remove_length_le p (rt_live RT Σ)); clear - H; lia
       | exact KP| intros a _ _; exact I| intros x _; exact I| intros x _; exact I| exact PERM1
       | intros e He; exact (CFR e ltac:(right; exact He))
       | exact ND1
       | intros e He; apply LPOS; rewrite LV' in He; exact (live_remove_sub _ _ _ He)
       | intros e He X; apply (NTL e He); apply in_app_iff in X; apply in_or_app; destruct X as [X|X]; [left; exact X| right; right; exact X]].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| | intros e x _ _; exact I].
    intros e He. pose proof (ELV _ (KLV _ He)) as He2.
    assert (NK : fst e <> p) by (intros X; apply PE; rewrite <- X; apply in_map; exact (KLV _ He)).
    split; [exact (live_remove_keep _ _ _ He2 NK)| rewrite LV'; exact (live_remove_keep _ _ _ He2 NK)].
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_cfree_null : evp_ctx_free_null_stmt RT FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur site
           (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> In site PEM_RAS_cfree ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_EVP_CTX_FREE m F fc (wz site) t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_CFN T en Σ m off crem lrem cur site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_cfree in HSI; cbn in HSI; lia).
    assert (HC3 : forall G, In G [FZ_EVP_CTX_FREE; e_CRYPTO_free; e_free] -> In (site, G) PEM_CALLS).
    { intros G HG. unfold PEM_CALLS. rewrite !in_app_iff. do 9 right. apply in_concat. exists [(site, FZ_EVP_CTX_FREE); (site, e_CRYPTO_free); (site, e_free)].
      split; [apply in_map_iff; exists site; split; [reflexivity| exact HSI]|]. cbn in HG |- *. destruct HG as [<-|[<-|[<-|[]]]]; tauto. }
    destruct (com_call_pre en Σ m off crem lrem _ site FZ_EVP_CTX_FREE COM (pem_site_in _ HSR) (HC3 FZ_EVP_CTX_FREE ltac:(cbn; tauto)) SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (HCG : forall G, In G [FZ_EVP_CTX_FREE; e_CRYPTO_free; e_free] -> In (bv_unsigned (wz site), G) (cg_call (rt_cg RT Σ))).
    { intros G HG. rewrite (unsigned_lit site) by exact SR. exact (proj2 CGH _ (proj2 CGS _ (HC3 G HG))). }
    apply (C_CFN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             FDO MST eq_refl eq_refl ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK in *; lia) CLE CTX1 UWC1 CGH
             (HCG e_CRYPTO_free ltac:(cbn; tauto)) (HCG e_free ltac:(cbn; tauto)) T c HA).
    intros c' AP. unfold apost in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & WM1) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_cfree in HSI; cbn in HSI; lia).
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (ELV _ (INCL _ He))| intros x _; exact I]. }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply PR; [| exact I]. apply acl_static. rewrite Ea. apply client_static_intro. unfold SEC_INIT. clear; lia. }
    eapply (Hk m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact PR| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| reflexivity| reflexivity| reflexivity| clear; lia| exact CR0| clear; lia| exact LR0| clear; lia
       | exact ELV| intros a _ _; exact I| intros x _; exact I| intros x _; exact I| exact PERM| exact CFR| exact ND| exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; exact (ELV _ (KLV _ He))| intros e x _ _; exact I].
  Qed.
  (* [comment removed for export] *)
  Lemma pem_call_bfree_null : bio_free_null_stmt RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur site
           (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> In site PEM_RAS_bfree ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_FREE m F fc (wz site) t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz 0) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BFN T en Σ m off crem lrem cur site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_bfree in HSI; cbn in HSI; lia).
    assert (HC : In (site, FZ_BIO_FREE) PEM_CALLS).
    { unfold PEM_CALLS. rewrite !in_app_iff. right; right; right; left. apply in_map_iff. exists site. split; [reflexivity| exact HSI]. }
    destruct (com_call_pre en Σ m off crem lrem _ site FZ_BIO_FREE COM (pem_site_in _ HSR) HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_BFN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (e_canary RT en)
             FDO MST eq_refl eq_refl ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK in *; lia) CLE T c HA).
    intros c' AP. unfold apost in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & -> & WM1) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_bfree in HSI; cbn in HSI; lia).
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (ELV _ (INCL _ He))| intros x _; exact I]. }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply PR; [| exact I]. apply acl_static. rewrite Ea. apply client_static_intro. unfold SEC_INIT. clear; lia. }
    eapply (Hk m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact PR| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| reflexivity| reflexivity| reflexivity| clear; lia| exact CR0| clear; lia| exact LR0| clear; lia
       | exact ELV| intros a _ _; exact I| intros x _; exact I| intros x _; exact I| exact PERM| exact CFR| exact ND| exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; exact (ELV _ (KLV _ He))| intros e x _ _; exact I].
  Qed.
End W3X.
