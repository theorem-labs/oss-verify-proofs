(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require SeqExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word
  MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw
  MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_vmops MallocInv_auxv
  MallocInv_ameta_base MallocInv_ameta_iface MallocInv_ameta1 MallocInv_ameta2 MallocInv_ameta3
  MallocInv_budget MallocInv_ameta4.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
Ltac treassoc :=
  lazymatch goal with
  | |- tsall ?W (mbind (mbind ?m ?f) ?g ?s) ?P => apply (tsall_assoc W m f g s P)
  end.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PZ : word := wlit 4096.

Definition am_commit (p : word) : M word :=
  aac3 <- m_ld A_AVAIL_AREA_CNT ;;
  tl <- m_ld A_AREA_TAIL ;;
  m_sd A_AVAIL_AREA_CNT (v_addi aac3 (-1)) ;;
  m_sd A_AVAIL_AREAS (v_add p (wlit 4096)) ;;
  (if is0 tl then m_sd A_AREA_HEAD p
   else m_sd (at_ tl 8) p) ;;
  sec <- m_ld A_CTX ;;
  m_sd A_AREA_TAIL p ;;
  m_sd p sec ;;
  t1 <- m_ld A_AREA_TAIL ;;
  m_sw (at_ t1 16) (wlit 101) ;;
  t2 <- m_ld A_AREA_TAIL ;;
  let m := at_ t2 24 in
  m_sd A_AVAIL_META (at_ m 40) ;;
  m_sd A_AVAIL_META_CNT (wlit 100) ;;
  m_sd (at_ m 8) w0 ;; m_sd m w0 ;;
  mret m.

Definition am_unprot (p : word) (test : bool) : M bool :=
  if test && is0 (v_and (v_addi PZ (-1)) p)
  then pg2 <- m_ld A_PAGE_SIZE ;;
       massert (c_eq pg2 (wlit 4096)) ;;
       r <- sys_mprotect_rw p PZ ;;
       if is0 r then mret true
       else e <- m_lw A_ERRNO ;; mret (c_eq e (wlit 38))
  else mret true.

Definition am_tail (r : option (word * bool)) : M word :=
  match r with
  | None => mret w0
  | Some (p, test) =>
    ok <- am_unprot p test ;;
    if negb ok then mret w0
    else am_commit p
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tools.
  Context {R : Type}.
  Variable W : wmode.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  (* [comment removed for export] *)
  Lemma tw_bind_post : forall {B} (piece : M B) (rest : B -> M R) s (Q : B -> mstate -> Prop) P,
    tsall W (piece s) Q -> (forall x s', Q x s' -> tsall W (rest x s') P) ->
    tsall W ((x <- piece ;; rest x) s) P.
  Proof. intros B piece rest s Q P H1 H2. unfold mbind at 1. eapply tsall_bind; [exact H1 | exact H2]. Qed.

  (* [comment removed for export] *)
  Lemma tw_det : forall {B} (op : M B) s (k : B -> M R) P (x : B) s',
    (forall (K' : B -> M B) (P' : B -> mstate -> Prop), tsafe (K' x s') P' -> tsafe ((y <- op ;; K' y) s) P') ->
    tsall W (k x s') P -> tsall W ((y <- op ;; k y) s) P.
  Proof.
    intros B op s k P x s' Hop Hk.
    eapply (tw_lift W op s (fun y s'' => y = x /\ s'' = s')).
    - intros K' P' HK'. apply Hop. apply HK'. auto.
    - intros y s'' [-> ->]. exact Hk.
  Qed.

  Lemma tw_ret' : forall (v : R) s P, P v s -> tsall W (mret v s) P.
  Proof. intros v s P H. exact H. Qed.

  Lemma tw_bind_ret : forall {B} (x : B) (k : B -> M R) s P,
    tsall W (k x s) P -> tsall W ((y <- mret x ;; k y) s) P.
  Proof. intros B x k s P H. exact H. Qed.

  Lemma tw_assert : forall b (k : unit -> M R) s P,
    b = true -> tsall W (k tt s) P -> tsall W ((x <- massert b ;; k x) s) P.
  Proof. intros b k s P -> H. exact H. Qed.

  Lemma tw_ld : forall a bs (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 8 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 8 = Some bs ->
    tsall W (k (le_val bs) s) P -> tsall W ((x <- m_ld (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros a bs k s P Hacc Hrd H. unfold mbind, m_ld, m_rd, mbind, mret.
    change (Z.of_nat 8) with 8%Z. rewrite Hacc, Hrd. exact H.
  Qed.

  Lemma tw_lw : forall a bs (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 4 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 4 = Some bs ->
    tsall W (k (v_lw (le_val bs)) s) P -> tsall W ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros a bs k s P Hacc Hrd H. unfold mbind, m_lw, m_rd, mbind, mret.
    change (Z.of_nat 4) with 4%Z. rewrite Hacc, Hrd. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma tw_ld_ctx : forall A s ck (k : word -> M R) P,
    WF A -> Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 -> 0 <= a_ctx A ck < 2^64 ->
    tsall W (k (Z_to_bv 64 (a_ctx A ck)) s) P ->
    tsall W ((x <- m_ld (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros A s ck k P HW HR HWn Hk Hlen Hv Hk'.
    eapply (tw_det (m_ld (Z_to_bv 64 (caddr ck))) s k P (Z_to_bv 64 (a_ctx A ck)) s); [| exact Hk'].
    intros K' P' HK'. eapply (ts_ld_ctx A); [exact HR | exact HWn | exact Hk | exact Hlen | exact Hv | exact HK'].
  Qed.

  (* [comment removed for export] *)
  Lemma at_libc48 : at_ A_LIBC 48 = Z_to_bv 64 PGA.
  Proof. unfold PGA. rewrite (mlo_page_size (ML:=ML)). rewrite <- (Z_to_bv_bv_unsigned 64 A_LIBC) at 1. apply at_Z. Qed.

  Lemma A_PAGE_SIZE_eq : A_PAGE_SIZE = Z_to_bv 64 PGA.
  Proof. unfold PGA. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma le_val_4096 : le_val (Z_to_le_bytes 8 4096) = Z_to_bv 64 4096.
  Proof. apply le_val_Z. reflexivity. Qed.

  Lemma tw_ld_pagesize : forall sp0 argv envp cb A s (k : word -> M R) P,
    IS sp0 argv envp cb A s ->
    tsall W (k (Z_to_bv 64 4096) s) P ->
    tsall W ((x <- m_ld (Z_to_bv 64 PGA) ;; k x) s) P.
  Proof.
    intros sp0 argv envp cb A s k P HI Hk. pose proof HI as [HW HR HC HWIN HE HG]. pose proof layout_statics.
    eapply tw_ld; [apply acc_ok_heap; [exact HWIN | lia | lia | llia] | exact (envok_pagesize _ _ _ _ HE) |].
    rewrite le_val_4096. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma tw_set_errno : forall e s (k : unit -> M R) P, WIN s ->
    tsall W (k tt (upd s (errno_mem (ms_mem s) e) (ms_vm s))) P ->
    tsall W ((x <- set_errno e ;; k x) s) P.
  Proof.
    intros e s k P HWn Hk.
    eapply (tw_det (set_errno e) s k P tt); [| exact Hk].
    intros K' P' HK'. apply ts_set_errno; [exact HWn | exact HK'].
  Qed.

  (* [comment removed for export] *)
  Lemma tw_lw_errno12 : forall s m0 (k : word -> M R) P, WIN s ->
    ms_mem s = errno_mem m0 ENOMEM ->
    tsall W (k (Z_to_bv 64 12) s) P ->
    tsall W ((x <- m_lw A_ERRNO ;; k x) s) P.
  Proof.
    intros s m0 k P HWn Hm Hk. pose proof layout_nums as LN. rewrite A_ERRNO_eq.
    eapply tw_lw.
    - apply acc_ok_heap; [exact HWn | llia | lia | unfold ERRNO; llia].
    - rewrite Hm. unfold errno_mem. rewrite A_ERRNO_eq.
      pose proof (SeqExec.rdn_wbytes_hit ml_segs (word_to_le_bytes 4 (Z_to_bv 64 ENOMEM)) m0 (Z_to_bv 64 ERRNO)) as X.
      rewrite length_N_to_le_bytes in X. apply X. rewrite uZ by (unfold ERRNO; llia). unfold ERRNO; llia.
    - exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma tw_sys_mprotect_none : forall (addr len : word) s (K : word -> M R) P,
    WIN s -> 0 < u len -> u addr mod 4096 = 0 ->
    u addr + page_round_up_Z (u len) <= alloc_top (ms_vm s) ->
    map_contains (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    map_contains (vm_noaccess (ms_vm s)) addr (page_round_up len) = true ->
    ((W <> WOk \/ mprot_ok_vm (ms_vm s) addr (page_round_up len) = false) ->
       tsall W (K MAP_FAILED (upd s (errno_mem (ms_mem s) ENOMEM) (ms_vm s))) P) ->
    (W <> WFail -> mprot_ok_vm (ms_vm s) addr (page_round_up len) = true ->
     tsall W (K (Z_to_bv 64 0) (upd s (zfill addr (page_round_up len) (ms_mem s)) (vm_unprotect addr (page_round_up len) (ms_vm s)))) P) ->
    tsall W ((x <- sys_mprotect_rw addr len ;; K x) s) P.
  Proof.
    intros addr len s K P HWn Hlen Hal Hce Hmc Hna Hf Hok. unfold mbind, sys_mprotect_rw. unfold page_size.
    rewrite (proj2 (Z.ltb_lt 0 (u len))) by lia. rewrite Hal. rewrite (proj2 (Z.leb_le _ _)) by exact Hce.
    rewrite Hmc, Hna. cbn - [tsall].
    apply tw_sys_mprotect_node.
    - intros HW'. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). cbn - [tsall].
      pose proof (tw_set_errno ENOMEM s (fun _ s' => K MAP_FAILED s') P HWn) as X. unfold mbind in X. apply X. exact (Hf HW').
    - exact Hok.
  Qed.
  (* [comment removed for export] *)
  Lemma tw_sys_mprotect_none04 : forall (addr len : word) s (K : word -> M R) P,
    WIN s -> 0 < u len -> u addr mod 4096 = 0 ->
    u addr + page_round_up_Z (u len) <= alloc_top (ms_vm s) ->
    map_contains (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    map_contains (vm_noaccess (ms_vm s)) addr (page_round_up len) = true ->
    (mprot_ok_vm (ms_vm s) addr (page_round_up len) = false ->
       tsall W (K MAP_FAILED (upd s (errno_mem (ms_mem s) ENOMEM) (ms_vm s))) P) ->
    (W <> WFail -> mprot_ok_vm (ms_vm s) addr (page_round_up len) = true ->
     tsall W (K (Z_to_bv 64 0) (upd s (zfill addr (page_round_up len) (ms_mem s)) (vm_unprotect addr (page_round_up len) (ms_vm s)))) P) ->
    tsall W ((x <- sys_mprotect_rw addr len ;; K x) s) P.
  Proof.
    intros addr len s K P HWn Hlen Hal Hce Hmc Hna Hf Hok. unfold mbind, sys_mprotect_rw. unfold page_size.
    rewrite (proj2 (Z.ltb_lt 0 (u len))) by lia. rewrite Hal. rewrite (proj2 (Z.leb_le _ _)) by exact Hce.
    rewrite Hmc, Hna. cbn - [tsall].
    apply tw_mprot04.
    - intros HW'. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). cbn - [tsall].
      pose proof (tw_set_errno ENOMEM s (fun _ s' => K MAP_FAILED s') P HWn) as X. unfold mbind in X. apply X. exact (Hf HW').
    - exact Hok.
  Qed.
End Tools.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record AMK (k : Z) (A A' : astate) (s s' : mstate) : Prop := {
  amk_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s'));
  amk_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true;
  amk_newdom : forall x, dom A' x -> dom A x \/
    (forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> region_free (vm_noaccess (ms_vm s)) b sz = true ->
       ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned sz));
  amk_live : a_areas A = [] -> vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) + k
}.

Lemma AMK_vm : forall k A A' s s', ms_vm s' = ms_vm s -> (forall x, dom A' x -> dom A x) -> 0 <= k -> AMK k A A' s s'.
Proof.
  intros k A A' s s' E Hd Hk. constructor; rewrite ?E; auto. intros; lia.
Qed.

Lemma AMK_refl : forall A s, AMK 0 A A s s.
Proof. intros A s. apply AMK_vm; auto. lia. Qed.

Lemma AMK_trans : forall k1 k2 A B C s t r,
  AMK k1 A B s t -> AMK k2 B C t r -> a_areas B = a_areas A -> AMK (k1 + k2) A C s r.
Proof.
  intros k1 k2 A B C s t r [M1 A1 N1 L1] [M2 A2 N2 L2] Ea. constructor.
  - intros b sz H. apply M2. apply M1. exact H.
  - intros b sz H Hf. apply A2; [apply M1; exact H | apply A1; assumption].
  - intros x Hd. destruct (N2 x Hd) as [HB | HB].
    + exact (N1 x HB).
    + right. intros b sz Hin Hf. apply HB; [apply M1; exact Hin | apply A1; assumption].
  - intros H0. specialize (L1 H0). specialize (L2 ltac:(rewrite Ea; exact H0)). lia.
Qed.

Lemma AMK_weaken : forall k k' A A' s s', AMK k A A' s s' -> k <= k' -> AMK k' A A' s s'.
Proof. intros k k' A A' s s' [M1 A1 N1 L1] Hk. constructor; auto. intros H0. specialize (L1 H0). lia. Qed.

Lemma AMvm_of_AMK : forall k A A' s s', AMK k A A' s s' -> k <= 12288 -> AMvm A A' s s'.
Proof.
  intros k A A' s s' [M1 A1 N1 L1] Hk. constructor; auto.
  - intros x b sz Hd Hn Hin Hf. destruct (N1 x Hd) as [H | H]; [exfalso; exact (Hn H) | exact (H b sz Hin Hf)].
  - intros H0. specialize (L1 H0). lia.
Qed.

(* [comment removed for export] *)
Record FRH (H : Z -> Prop) (A : astate) (s : mstate) (A' : astate) (s' : mstate) : Prop := {
  fh_lo : ms_lo s' = ms_lo s;
  fh_hi : ms_hi s' = ms_hi s;
  fh_owned : forall x, owned_of A x -> owned_of A' x;
  fh_mem : forall a : word, ~ owned_of A' (bv_unsigned a) -> ~ (ERRNO <= bv_unsigned a < ERRNO + 4) ->
           ~ H (bv_unsigned a) -> ms_mem s' a = ms_mem s a;
  fh_live : forall p n, a_live A p = Some n -> a_live A' p = Some n;
  fh_livemem : forall p n (a : word), a_live A p = Some n -> p <= bv_unsigned a < p + n ->
               ms_mem s' a = ms_mem s a;
  fh_mapped : forall a : word, ms_mem s a <> None -> ms_mem s' a <> None;
  fh_limit : vm_limit (ms_vm s') = vm_limit (ms_vm s)
}.

Lemma FRH_of_FR : forall H A s A' s', FR A s A' s' -> FRH H A s A' s'.
Proof. intros H A s A' s' [F1 F2 F3 F4 F5 F6 F7 F8]. constructor; auto. Qed.

Lemma FRH_mono : forall (H H' : Z -> Prop) A s A' s', FRH H A s A' s' -> (forall x, H x -> H' x) -> FRH H' A s A' s'.
Proof. intros H H' A s A' s' [F1 F2 F3 F4 F5 F6 F7 F8] HH. constructor; auto. Qed.

(* [comment removed for export] *)
Lemma FR_of_FRH : forall (H : Z -> Prop) A s A' s', FRH H A s A' s' ->
  (forall x, H x -> owned_of A' x) -> FR A s A' s'.
Proof.
  intros H A s A' s' [F1 F2 F3 F4 F5 F6 F7 F8] HC. constructor; auto.
Qed.

Lemma FRH_FR : forall (H : Z -> Prop) A s A' s' A'' s'', FRH H A s A' s' -> FR A' s' A'' s'' -> FRH H A s A'' s''.
Proof.
  intros H A s A' s' A'' s'' [F1 F2 F3 F4 F5 F6 F7 F8] [G1 G2 G3 G4 G5 G6 G7 G8]. constructor.
  - rewrite G1. exact F1.
  - rewrite G2. exact F2.
  - intros x Hx. apply G3. apply F3. exact Hx.
  - intros a Ho He Hh. rewrite G4 by assumption. apply F4; [| exact He | exact Hh]. intros Ho'. exact (Ho (G3 _ Ho')).
  - intros p n Hp. apply G5. apply F5. exact Hp.
  - intros p n a Hp Hi. rewrite (G6 p n a (F5 p n Hp) Hi). exact (F6 p n a Hp Hi).
  - intros a Ha. apply G7. apply F7. exact Ha.
  - rewrite G8. exact F8.
Qed.

(* [comment removed for export] *)
Lemma FRH_extend : forall (H H' : Z -> Prop) A0 s0 A1 s1 A2 s2,
  FRH H A0 s0 A1 s1 -> WF A1 ->
  ms_lo s2 = ms_lo s1 -> ms_hi s2 = ms_hi s1 -> vm_limit (ms_vm s2) = vm_limit (ms_vm s1) ->
  (forall x, owned_of A1 x -> owned_of A2 x) -> a_live A2 = a_live A1 ->
  (forall a : word, ms_mem s2 a = ms_mem s1 a \/
     ((owned_of A2 (u a) /\ forall p n, a_live A1 p = Some n -> ~ (p <= u a < p + n)) \/
      (ERRNO <= u a < ERRNO + 4) \/
      (H' (u a) /\ ~ dom A1 (u a)))) ->
  (forall a : word, ms_mem s1 a <> None -> ms_mem s2 a <> None) ->
  FRH (fun x => H x \/ H' x) A0 s0 A2 s2.
Proof.
  intros H H' A0 s0 A1 s1 A2 s2 [F1 F2 F3 F4 F5 F6 F7 F8] HW L1 L2 L3 HO HL HM HK. constructor.
  - rewrite L1. exact F1.
  - rewrite L2. exact F2.
  - intros x Hx. apply HO. apply F3. exact Hx.
  - intros a Ho He Hh. destruct (HM a) as [E | [[Ho2 _] | [Herr | [Hh' _]]]].
    + rewrite E. apply F4; [intros Ho1; exact (Ho (HO _ Ho1)) | exact He | intros Hx; apply Hh; left; exact Hx].
    + exfalso. exact (Ho Ho2).
    + exfalso. exact (He Herr).
    + exfalso. apply Hh. right. exact Hh'.
  - intros p n Hp. rewrite HL. apply F5. exact Hp.
  - intros p n a Hp Hi. pose proof (F5 p n Hp) as Hp1.
    destruct (live_heap A1 p n HW Hp1) as (N0 & P1 & P2 & P3 & PD). pose proof (MallocInv_live.round16_ge n). pose proof layout_nums as LN.
    destruct (HM a) as [E | [[_ Hnl] | [Herr | [_ Hnd]]]].
    + rewrite E. exact (F6 p n a Hp Hi).
    + exfalso. exact (Hnl p n Hp1 Hi).
    + exfalso. unfold ERRNO in Herr. llia.
    + exfalso. apply Hnd. apply PD. lia.
  - intros a Ha. apply HK. apply F7. exact Ha.
  - rewrite L3. exact F8.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma II_errno : forall sp0 argv envp cb D A s e,
  II sp0 argv envp cb D A s -> II sp0 argv envp cb D A (upd s (errno_mem (ms_mem s) e) (ms_vm s)).
Proof. intros sp0 argv envp cb D A s e [I1 I2 I3 I4 I5]. constructor; cbn; auto. apply IS_errno. exact I1. Qed.

Lemma map_contains_sub : forall l (a n a' n' : word),
  map_contains l a n = true -> u a <= u a' -> u a' + u n' <= u a + u n -> map_contains l a' n' = true.
Proof.
  intros l a n a' n' H H1 H2. apply (proj2 (map_contains_mcov l a' n')).
  apply (mcov_sub l (u a) (u n)); [exact (proj1 (map_contains_mcov l a n) H) | exact H1 | exact H2].
Qed.

Lemma PZ_u : u PZ = 4096. Proof. reflexivity. Qed.
Lemma pru_PZ : page_round_up PZ = Z_to_bv 64 4096. Proof. reflexivity. Qed.
Lemma pruZ_PZ : page_round_up_Z (u PZ) = 4096. Proof. reflexivity. Qed.

Lemma am_unprot_false : forall pw, am_unprot pw false = mret true.
Proof. intros pw. reflexivity. Qed.

Lemma am_unprot_true : forall p, 0 <= p < 2^64 -> page_aligned p ->
  am_unprot (Z_to_bv 64 p) true =
  (pg2 <- m_ld A_PAGE_SIZE ;;
   massert (c_eq pg2 (wlit 4096)) ;;
   r <- sys_mprotect_rw (Z_to_bv 64 p) PZ ;;
   if is0 r then mret true
   else e <- m_lw A_ERRNO ;; mret (c_eq e (wlit 38))).
Proof.
  intros p Hp Hal. unfold am_unprot. unfold PZ at 1. unfold wlit. rewrite v_addi_Z. change (4096 + -1) with 4095.
  rewrite v_and_Z by lia. rewrite Z.land_comm. change 4095 with (2^12 - 1). rewrite land_ones_low by lia.
  unfold page_aligned in Hal. change (2^12) with 4096. rewrite Hal. reflexivity.
Qed.

Section Tail.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A0 : astate) (s0 : mstate).

  Definition FailPost (s' : mstate) : Prop :=
    exists A', II sp0 argv envp cb D A' s' /\ FR A0 s0 A' s' /\ gsame A0 A' /\ AMvm A0 A' s0 s' /\
               spare A0 = 0 /\ a_areas A' = a_areas A0 /\ (W = WOk -> ~ am_budget A0 s0).
  Definition SuccPost (m : Z) (s' : mstate) : Prop :=
    exists A', II sp0 argv envp cb (m :: D) A' s' /\ FR A0 s0 A' s' /\ got_meta A0 D A' m /\ AMvm A0 A' s0 s' /\
       ((0 < spare A0 /\ ms_vm s' = ms_vm s0 /\ a_areas A' = a_areas A0 /\ spare A' = spare A0 - 1)
        \/ (spare A0 = 0 /\ a_areas A' = a_areas A0 ++ [m - 24] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])).
  Definition BodyPost (res : word) (s' : mstate) : Prop :=
    (res = Z_to_bv 64 0 /\ FailPost s') \/ (exists m, res = Z_to_bv 64 m /\ SuccPost m s').

  (* [comment removed for export] *)
  Definition apart0 (p : Z) : Prop :=
    forall b sz, In (b, sz) (vm_maps (ms_vm s0)) -> region_free (vm_noaccess (ms_vm s0)) b sz = true ->
      p + 4096 <= u b \/ u b + u sz <= p.

  (* [comment removed for export] *)
  Record PreT (k : Z) (A : astate) (s : mstate) (p : Z) : Prop := {
    pt_ii : II sp0 argv envp cb D A s;
    pt_fr : FR A0 s0 A s;
    pt_gs : gsame A0 A;
    pt_areas : a_areas A = a_areas A0;
    pt_amk : AMK k A0 A s0 s;
    pt_k : 0 <= k <= 12288;
    pt_spare0 : spare A0 = 0;
    pt_init : a_ctx A KInit = 1;
    pt_amc : a_ctx A KAmc = 0;
    pt_fl : a_freelist A = [];
    pt_aac : 1 <= a_ctx A KAac;
    pt_p : a_ctx A KAareas = p;
    pt_apart : apart0 p;
    pt_budget : am_budget A0 s0 -> vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) }.

  (* [comment removed for export] *)
  Record PreF (k : Z) (A : astate) (s : mstate) (p : Z) : Prop := {
    pf_is : IS sp0 argv envp cb A s;
    pf_vc : VMcore A (ms_vm s);
    pf_va : VMall A (ms_vm s);
    pf_av : AvOK A;
    pf_us : UsOK A;
    pf_dd : deads A D;
    pf_frh : FRH (fun x => p <= x < p + 4096) A0 s0 A s;
    pf_gs : gsame A0 A;
    pf_areas : a_areas A = a_areas A0;
    pf_amk : AMK k A0 A s0 s;
    pf_k : 0 <= k <= 12288;
    pf_spare0 : spare A0 = 0;
    pf_init : a_ctx A KInit = 1;
    pf_amc : a_ctx A KAmc = 0;
    pf_fl : a_freelist A = [];
    pf_brk : a_ctx A KBrk <> 0;
    pf_aac : a_ctx A KAac = 1;
    pf_al : page_aligned p;
    pf_heap : heap_range p (p + 4096);
    pf_pdom : forall x, p <= x < p + 4096 -> ~ dom A x;
    pf_zero : forall x, p <= x < p + 4096 -> ms_mem s (Z_to_bv 64 x) = Some (Z_to_bv 8 0);
    pf_cov : mcov (vm_maps (ms_vm s)) p 4096;
    pf_nafree : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true;
    pf_brkok : a_ctx A KBrk = u (vm_brk (ms_vm s)) /\ 0 < u (vm_brk (ms_vm s)) /\
               u (vm_start_brk (ms_vm s)) <= u (vm_brk (ms_vm s)) /\ page_aligned (u (vm_brk (ms_vm s)));
    pf_span : u (vm_brk (ms_vm s)) - u (vm_start_brk (ms_vm s)) <= 4096 * (Z.of_nat (length (a_areas A)) + 2);
    pf_apart : apart0 p }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma commit_leaf : forall k A s p,
    IS sp0 argv envp cb A s -> VMcore A (ms_vm s) -> VMall A (ms_vm s) -> AvOK A -> UsOK A -> deads A D ->
    a_ctx A KInit = 1 -> a_ctx A KAmc = 0 -> a_freelist A = [] -> a_ctx A KBrk <> 0 -> 1 <= a_ctx A KAac ->
    page_aligned p -> heap_range p (p + 4096) ->
    (forall x, p <= x < p + 4096 -> ~ dom A x) ->
    (forall x, p <= x < p + 4096 -> ms_mem s (Z_to_bv 64 x) = Some (Z_to_bv 8 0)) ->
    mcov (vm_maps (ms_vm s)) p 4096 ->
    region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true ->
    (a_ctx A KBrk = 2^64 - 1 \/
     (a_ctx A KBrk = u (vm_brk (ms_vm s)) /\ 0 < u (vm_brk (ms_vm s)) /\
      u (vm_start_brk (ms_vm s)) <= u (vm_brk (ms_vm s)) /\ page_aligned (u (vm_brk (ms_vm s))))) ->
    (a_ctx A KAac - 1 > 0 ->
     (p + 4096) + 4096 * (a_ctx A KAac - 1) <= alloc_ceiling /\
     map_contains (vm_maps (ms_vm s)) (Z_to_bv 64 (p + 4096)) (Z_to_bv 64 (4096 * (a_ctx A KAac - 1))) = true /\
     map_contains (vm_noaccess (ms_vm s)) (Z_to_bv 64 (p + 4096)) (Z_to_bv 64 (4096 * (a_ctx A KAac - 1))) = true) ->
    u (vm_brk (ms_vm s)) - u (vm_start_brk (ms_vm s)) <= 4096 * (Z.of_nat (length (a_areas A)) + 2) ->
    (* [comment removed for export] *)
    FRH (fun x => p <= x < p + 4096) A0 s0 A s -> gsame A0 A -> a_areas A = a_areas A0 ->
    AMK k A0 A s0 s -> 0 <= k <= 12288 -> spare A0 = 0 -> apart0 p ->
    tsall W (am_commit (Z_to_bv 64 p) s) BodyPost.
  Proof.
    intros k A s p HI HVc HVa HAV HUS HD Hinit Hamc Hfl Hbrk Haac Hal Hheap Hpdom Hzero Hcov Hnafree HbrkOK Hres Hspan
           HFRH HGS Hareas HAMK Hk Hsp0 Hapart.
    pose proof (is_wf _ _ _ _ _ _ HI) as HW.
    apply tsall_of_tsafe. apply (tsafe_leaves_of_cps (am_commit (Z_to_bv 64 p)) s BodyPost).
    intros K' P' HK'. unfold am_commit.
    apply (commit_ok sp0 argv envp cb D A s p HI HVc HVa HAV HUS HD Hinit Hamc Hbrk Haac Hal Hheap Hpdom Hzero Hcov Hnafree HbrkOK Hres Hspan K' P').
    intros s' HII HFR HGM Hvm. apply HK'.
    right. exists (p + 24). split; [reflexivity|]. exists (cmA A p).
    assert (Hdisj : forall pg, In pg (a_areas A) -> pg + 4096 <= p \/ p + 4096 <= pg).
    { intros pg Hpg. destruct (wf_areas_al A HW pg Hpg) as [Hpal _]. unfold page_aligned in *.
      destruct (Z.eq_dec pg p) as [-> | Hne].
      - exfalso. apply (Hpdom p); [lia|]. left. exists p. split; [exact Hpg | lia].
      - pose proof (Z_div_mod_eq_full pg 4096). pose proof (Z_div_mod_eq_full p 4096). lia. }
    assert (Hdom' : forall x, dom (cmA A p) x <-> dom A x \/ p <= x < p + 4096).
    { intros x. unfold cmA. apply (dom_aaA A HW p _ _ Hdisj x). }
    split; [exact HII|]. split; [| split; [| split]].
    - apply (FR_of_FRH (fun x => p <= x < p + 4096)); [apply (FRH_FR _ A0 s0 A s); [exact HFRH | exact HFR] |].
      intros x Hx. right. apply (proj2 (Hdom' x)). right. exact Hx.
    - apply (got_meta_pre A0 A); assumption.
    - destruct HAMK as [M1 A1 N1 L1]. constructor; rewrite ?Hvm.
      + exact M1.
      + exact A1.
      + intros x b sz Hd Hn Hin Hf. destruct (proj1 (Hdom' x) Hd) as [HdA | Hpg].
        * destruct (N1 x HdA) as [H0 | Hap]; [exfalso; exact (Hn H0) | exact (Hap b sz Hin Hf)].
        * pose proof (Hapart b sz Hin Hf). lia.
      + intros H0. specialize (L1 H0). lia.
    - right. split; [exact Hsp0|]. split; [| split].
      + unfold cmA, aaA. cbn [a_areas]. rewrite Hareas. replace (p + 24 - 24) with p by lia. reflexivity.
      + rewrite cmA_ctx. reflexivity.
      + unfold cmA, aaA. cbn [a_freelist]. exact Hfl.
  Qed.
  Theorem tailF_ok : forall k A s p, PreF k A s p -> tsall W (am_tail (Some (Z_to_bv 64 p, false)) s) BodyPost.
  Proof.
    intros k A s p PF. destruct PF.
    cbn [am_tail]. rewrite am_unprot_false. apply tw_bind_ret. cbn [negb].
    apply (commit_leaf k A s p); try assumption.
    - rewrite pf_aac0. lia.
    - right. exact pf_brkok0.
    - rewrite pf_aac0. intros H. exfalso. lia.
  Qed.
  Theorem tailT_ok : forall k A s p, PreT k A s p -> tsall W (am_tail (Some (Z_to_bv 64 p, true)) s) BodyPost.
  Proof.
    intros k A s p PT. destruct PT as [HII HFR HGS Hareas HAMK Hk Hsp0 Hinit Hamc Hfl Haac Hp Hapart Hbud].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (VMok_core A _ HVo) as HVc. pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    destruct (Va ltac:(lia)) as (R1 & R2 & R3 & R4). rewrite Hp in R1, R2, R3, R4.
    ceil. pose proof (wf_ctx_nonneg A HW KAareas) as Hp0. rewrite Hp in Hp0.
    set (aac := a_ctx A KAac) in *.
    assert (Hbrk : a_ctx A KBrk <> 0).
    { intros H0. destruct (wf_brk0 A HW H0) as (_ & _ & X). unfold aac in *. lia. }
    pose proof (na_nw A _ HVc) as NW. pose proof (maps_nw_of A _ HVc) as NWM.
    assert (Hcovp : mcov (vm_maps (ms_vm s)) p 4096).
    { apply (mcov_sub _ (u (Z_to_bv 64 p)) (u (Z_to_bv 64 (4096 * aac)))); [apply map_contains_mcov; exact R3 | rewrite uZ by lia; lia | rewrite !uZ by lia; lia]. }
    assert (Hnap : mcov (vm_noaccess (ms_vm s)) p 4096).
    { apply (mcov_sub _ (u (Z_to_bv 64 p)) (u (Z_to_bv 64 (4096 * aac)))); [apply map_contains_mcov; exact R4 | rewrite uZ by lia; lia | rewrite !uZ by lia; lia]. }
    cbn [am_tail]. rewrite (am_unprot_true p) by first [lia | exact R1].
    treassoc. rewrite A_PAGE_SIZE_eq. eapply (tw_ld_pagesize W sp0 argv envp cb A); [exact HI|].
    treassoc. apply tw_assert; [reflexivity|].
    treassoc.
    eapply tw_sys_mprotect_none;
      [exact HWIN | rewrite PZ_u; lia | rewrite uZ by lia; exact R1 | rewrite pruZ_PZ, uZ, Vtop by lia; lia
      | rewrite pru_PZ; apply (map_contains_sub _ _ _ _ _ R3); rewrite !uZ by lia; lia
      | rewrite pru_PZ; apply (map_contains_sub _ _ _ _ _ R4); rewrite !uZ by lia; lia | |].
    - (* [comment removed for export] *)
      intros HWf. cbv beta. change (is0 MAP_FAILED) with false. cbv iota.
      treassoc. eapply (tw_lw_errno12 W _ (ms_mem s)); [apply WIN_upd; exact HWIN | reflexivity |].
      apply tw_bind_ret. unfold wlit. rewrite c_eq_Z by lia. cbn [Z.eqb Pos.eqb negb].
      apply tw_ret'. left. split; [reflexivity|].
      exists A. split; [apply II_errno; exact HII|]. split; [| split; [exact HGS | split; [| split; [exact Hsp0 | split; [exact Hareas|]]]]].
      + apply (FR_trans A0 s0 A s); [exact HFR | apply FR_errno; exact HW].
      + apply (AMvm_of_AMK k); [| lia]. replace k with (k + 0) by lia.
        apply (AMK_trans k 0 A0 A A s0 s); [exact HAMK | apply AMK_vm; [reflexivity | auto | lia] | exact Hareas].
      + intros HWk Hb. destruct HWf as [HWf | HWf]; [exact (HWf HWk)|].
        destruct Hcovp as (B & SZ & HinB & B1 & B2).
        rewrite (mprot_ok_vm_intro (ms_vm s) (Z_to_bv 64 p) (page_round_up PZ) B SZ) in HWf; [discriminate | exact NWM | exact NW | exact Vpw | exact HinB | rewrite uZ by lia; lia | rewrite pru_PZ, !uZ by lia; lia |].
        rewrite pru_PZ, uZ by lia. exact (Hbud Hb).
    - (* [comment removed for export] *)
      intros HWs Hmp. cbv beta. unfold is0 at 1. rewrite w0_eq, c_eq_Z by lia. cbn [Z.eqb].
      apply tw_bind_ret. cbn [negb]. rewrite pru_PZ.
      pose proof (mprotect_page_state sp0 argv envp cb A s (Z_to_bv 64 p) HI HVc ltac:(rewrite uZ by lia; exact Hnap) ltac:(rewrite uZ by lia; lia))
        as (HI' & HVc' & Emaps & Ena & Hcov' & Hlo & Himg & NODOM & ZIN & ZOUT).
      rewrite !uZ in * by lia.
      set (n := Z_to_bv 64 4096) in *. set (m' := zfill (Z_to_bv 64 p) n (ms_mem s)) in *. set (h' := vm_unprotect (Z_to_bv 64 p) n (ms_vm s)) in *.
      assert (En : u n = 4096) by (unfold n; apply uZ; lia).
      apply (commit_leaf k A (upd s m' h') p); cbn [ms_mem ms_vm upd]; try assumption.
      + split; [lia|]. split; [lia|]. split; [lia | exact Himg].
      + intros x Hx. rewrite <- (uZ x) in Hx by lia. exact (ZIN (Z_to_bv 64 x) Hx).
      + rewrite Ena. apply (maps_subtract_free_self _ _ _ _ _ NW); rewrite ?uZ by lia; lia.
      + destruct Vb as [H0 | [H1 | H2]]; [exfalso; exact (Hbrk H0) | left; exact H1 | right; exact H2].
      + intros Hgt. split; [unfold aac in *; lia|]. split.
        * rewrite Emaps. apply (map_contains_sub _ _ _ _ _ R3); rewrite !uZ by lia; unfold aac in *; lia.
        * rewrite Ena. apply (proj2 (map_contains_mcov _ _ _)). rewrite !uZ by (unfold aac in *; lia).
          apply (maps_subtract_cover _ _ _ _ _ NW); [| unfold aac in *; lia | lia].
          apply (mcov_sub _ (u (Z_to_bv 64 p)) (u (Z_to_bv 64 (4096 * aac)))); [apply map_contains_mcov; exact R4 | rewrite uZ by lia; lia | rewrite !uZ by lia; unfold aac in *; lia].
      + pose proof (proj2 Vspan). unfold h'. cbn. rewrite Hareas in *. lia.
      + (* [comment removed for export] *)
        eapply FRH_mono.
        * apply (FRH_extend (fun _ => False) (fun x => p <= x < p + 4096) A0 s0 A s A (upd s m' h')); cbn [ms_mem ms_vm ms_lo ms_hi upd].
          -- apply FRH_of_FR. exact HFR.
          -- exact HW.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- auto.
          -- reflexivity.
          -- intros a. pose proof (u64_range a).
             assert (CASE : p <= u a < p + 4096 \/ ~ (p <= u a < p + 4096)) by lia.
             destruct CASE as [IN | NI]; [right; right; right; split; [exact IN | apply NODOM; exact IN] | left; apply ZOUT; exact NI].
          -- intros a Ha. pose proof (u64_range a). assert (CASE : p <= u a < p + 4096 \/ ~ (p <= u a < p + 4096)) by lia.
             destruct CASE as [IN | NI]; [rewrite (ZIN a IN); discriminate | rewrite (ZOUT a NI); exact Ha].
        * intros x [F | Hx]; [destruct F | exact Hx].
      + (* [comment removed for export] *)
        apply (AMK_weaken (k + 0)); [| lia].
        apply (AMK_trans k 0 A0 A A s0 s); [exact HAMK | | exact Hareas].
        constructor; cbn [ms_vm upd].
        * rewrite Emaps. auto.
        * intros b sz Hin Hf. rewrite Ena. apply maps_subtract_free; [exact NW | exact Hf].
        * intros x Hx. left. exact Hx.
        * intros _. unfold vm_live_bytes. rewrite Emaps. lia.
  Qed.
End Tail.

End WithLayout.
