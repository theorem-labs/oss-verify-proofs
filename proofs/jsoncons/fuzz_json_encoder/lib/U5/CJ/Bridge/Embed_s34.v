(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim MmapSim AllocSim Scfg ShapeAlg SpinAlg AgentLib RefNodes VmLimitFrame.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes Decode.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim Monad STree Malloc Prog KInv KStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrNodes KLink BrRes.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition XLIM : Z := 2 ^ 34.   (* [comment removed for export] *)
Definition NONEMAX : Z := 2 ^ 27.   (* [comment removed for export] *)
Definition NMAX : Z := 2^34 + 2^16.     (* [comment removed for export] *)
Definition CAPKMAX : Z := 4000.         (* [comment removed for export] *)
Definition CAPBMAX : Z := 2^33.         (* [comment removed for export] *)

Lemma NMAX_facts : 0 < NMAX /\ NMAX mod page_size = 0 /\ 2 * PGSZ <= NMAX.
Proof. unfold NMAX, PGSZ, page_size. split; [lia|]. split; [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Lemma NMAX_band : forall h, sp_window_lo <= bv_unsigned (vm_init_sp h) -> 2 ^ 32 + CAPKMAX * (2 * NMAX) + NMAX <= alloc_top h.
Proof. intros h H. pose proof (alloc_top_ge_window h H). unfold CAPKMAX, NMAX. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section IMPL.
Variable segs : list Segment.
Context {St : Type}.

Lemma implM_ret_inv : forall {A} (a : A) (s : St) Q ms,
  implM segs (mret a) s Q ms -> evt segs (Q a s) ms.
Proof. intros A a s Q ms H. exact H. Qed.

Lemma implM_bind_inv : forall {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s Q ms,
  implM segs (mbind m f) s Q ms ->
  implM segs m s (fun a s' ms' => implM segs (f a) s' Q ms') ms.
Proof.
  intros A B m f s Q ms H. unfold implM, mbind in *. apply impl_ebind_inv in H.
  eapply impl_mono; [exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.

Lemma implM_msys_inv : forall {A} n (dec : resp -> option A) (s : St) Q ms,
  implM segs (msys n dec) s Q ms ->
  evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms.
Proof.
  intros A n dec s Q ms H. unfold implM, msys in H. apply impl_enode_inv in H.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp a E. apply (Hk rsp (a, s)). rewrite E. reflexivity.
Qed.

Lemma mbind_mget : forall {A} (f : St -> Monad.M St A) s, mbind mget f s = f s s.
Proof. reflexivity. Qed.
Lemma implM_mget_inv : forall {A} (f : St -> Monad.M St A) s Q ms,
  implM segs (mbind mget f) s Q ms -> implM segs (f s) s Q ms.
Proof. intros A f s Q ms H. exact H. Qed.
Lemma implM_mupd_inv : forall {A} g (m : Monad.M St A) s Q ms,
  implM segs (mbind (mupd g) (fun _ => m)) s Q ms -> implM segs m (g s) Q ms.
Proof. intros A g m s Q ms H. exact H. Qed.
Lemma mbind_mupd : forall {A} g (m : Monad.M St A) s, mbind (mupd g) (fun _ => m) s = m (g s).
Proof. reflexivity. Qed.
Lemma mbind_mret_l : forall {A B} (a : A) (f : A -> Monad.M St B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.

End IMPL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vmmaps_twice : forall h1 h2 m, with_vmmaps h2 (with_vmmaps h1 m) = with_vmmaps h2 m.
Proof. intros h1 h2 m. reflexivity. Qed.

Lemma with_vmmaps_mat : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.

Lemma live_bytes_cons' : forall e l, live_bytes (e :: l) = bv_unsigned (snd e) + live_bytes l.
Proof. intros [a n] l. reflexivity. Qed.

Lemma Forall_app_cons_mid : forall {A} (P : A -> Prop) l1 x l2,
  Forall P (l1 ++ l2) -> P x -> Forall P (l1 ++ x :: l2).
Proof.
  intros A P l1 x l2 H Hx. apply Forall_app in H as [H1 H2]. apply Forall_app. split; [exact H1|]. constructor; assumption.
Qed.

Lemma length_app_cons_mid : forall {A} (l1 : list A) x l2, length (l1 ++ x :: l2) = S (length (l1 ++ l2)).
Proof. intros. rewrite !length_app. cbn. lia. Qed.

Lemma Forall_filter : forall {A} (P : A -> Prop) f l, Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. induction H; cbn; [constructor|]. destruct (f x); [constructor|]; auto. Qed.

Lemma length_filter_le : forall {A} f (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. intros. apply List.filter_length_le. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RI (CAPK CAPB : Z) (ne : nat) (bb : Z) (h : VmMaps) : Prop :=
     Z.of_nat (length (vm_reserved h ++ vm_maps h)) + Z.of_nat ne <= CAPK
  /\ Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_reserved h ++ vm_maps h)
  /\ live_bytes (vm_maps h) + bb <= CAPB
  /\ 0 <= bb
  /\ sp_window_lo <= bv_unsigned (vm_init_sp h)
  /\ vm_limit h <= XLIM      (* [comment removed for export] *)      (* [comment removed for export] *)
  /\ Forall (fun p => bv_unsigned (snd p) <= NONEMAX \/ bv_unsigned (snd p) <= vm_limit h) (vm_maps h).   (* [comment removed for export] *)

Lemma RI_weaken : forall CAPK CAPB ne ne' bb bb' h,
  RI CAPK CAPB ne bb h -> (ne' <= ne)%nat -> 0 <= bb' <= bb -> RI CAPK CAPB ne' bb' h.
Proof. intros CAPK CAPB ne ne' bb bb' h (R1 & R2 & R3 & R4 & R6 & R7 & R8) Hne Hbb. unfold RI. splits; auto; lia. Qed.

(* [comment removed for export] *)
Lemma RI_add : forall CAPK CAPB ne bb h (a : word) (n : Z) na sb br,
  RI CAPK CAPB (S ne) bb h -> 0 <= n <= NMAX -> n <= bb -> bv_unsigned (Z_to_bv 64 n) = n ->
  (n <= NONEMAX \/ n <= vm_limit h) ->                                  (* [comment removed for export] *)
  RI CAPK CAPB ne (bb - n)
     (mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros CAPK CAPB ne bb h a n na sb br (R1 & R2 & R3 & R4 & R6 & R7 & R8) Hn Hnb Hu Hfit. unfold RI.
  cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
  rewrite length_app_cons_mid, live_bytes_cons'. cbn [snd]. rewrite Hu. splits; auto; try lia.
  - apply Forall_app_cons_mid; [exact R2| cbn [snd]; rewrite Hu; lia].
  - constructor; [cbn [snd]; rewrite Hu; exact Hfit| exact R8].
Qed.

(* [comment removed for export] *)
Lemma RI_tick : forall CAPK CAPB ne bb bb' h na sb br,
  RI CAPK CAPB (S ne) bb h -> 0 <= bb' <= bb ->
  RI CAPK CAPB ne bb' (mkVmMapsFull (vm_reserved h) (vm_maps h) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros CAPK CAPB ne bb bb' h na sb br (R1 & R2 & R3 & R4 & R6 & R7 & R8) Hbb. unfold RI.
  cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp]. splits; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma RI_remove : forall CAPK CAPB ne bb bb' h (aw : word) na sb br,
  RI CAPK CAPB (S ne) bb h -> 0 <= bb' <= bb ->
  RI CAPK CAPB ne bb' (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros CAPK CAPB ne bb bb' h aw na sb br (R1 & R2 & R3 & R4 & R6 & R7 & R8) Hbb. unfold RI.
  cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
  pose proof (RefNodes.live_bytes_map_remove_le (vm_maps h) aw) as Hlb.
  unfold map_remove in *. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) aw)) (vm_maps h)) as Hlen.
  rewrite length_app in R1 |- *. splits; auto; try lia.
  - apply Forall_app in R2 as [R2a R2b]. apply Forall_app. split; [exact R2a| apply Forall_filter; exact R2b].
  - apply Forall_filter. exact R8.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RI_budget : forall CAPK CAPB ne bb (mo : Model) (n : Z),
  RI CAPK CAPB ne bb (m_vmmaps mo) ->
  nbr_limit <= vm_limit (m_vmmaps mo) ->
  vm_backing_used mo + n <= vm_limit (m_vmmaps mo).
Proof. intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R6 & R7 & R8) Hbig. exfalso. unfold XLIM, nbr_limit in *. lia. Qed.

Lemma RI_grant_rw : forall CAPK CAPB ne bb (mo : Model) (n : Z),
  RI CAPK CAPB ne bb (m_vmmaps mo) -> CAPK <= CAPKMAX ->
  nbr_limit <= vm_limit (m_vmmaps mo) ->
  exists a, grant_ok (Z_to_bv 64 0) mo a n = true.
Proof. intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R6 & R7 & R8) HK Hbig. exfalso. unfold XLIM, nbr_limit in *. lia. Qed.

Lemma RI_grant_na : forall CAPK CAPB ne bb (mo : Model) (n : Z),
  RI CAPK CAPB ne bb (m_vmmaps mo) -> CAPK <= CAPKMAX ->
  0 <= n <= NMAX ->
  exists a, grant_ok_na (Z_to_bv 64 0) mo a n = true.
Proof.
  intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R6 & R7 & R8) HK Hn.
  pose proof NMAX_facts as (N1 & N2 & N3). pose proof (NMAX_band _ R6) as HB.
  apply (grant_exists_na_gen (Z_to_bv 64 0) mo NMAX n CAPKMAX (2 ^ 32)); [exact N1 | exact N2 | exact Hn | exact R2 | lia | reflexivity | lia |].
  assert (0 <= NMAX) by lia. unfold CAPKMAX in *. nia.
Qed.

Lemma RI_live_limit : forall CAPK CAPB ne bb h, RI CAPK CAPB ne bb h ->
  nbr_limit <= vm_limit h -> live_bytes (vm_maps h) + bb <= vm_limit h.
Proof. intros CAPK CAPB ne bb h (R1 & R2 & R3 & R4 & R6 & R7 & R8) Hbig. exfalso. unfold XLIM, nbr_limit in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_grow_ok_aligned_elim : forall (m : Model) (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  bv_unsigned b mod page_size = 0 -> d mod page_size = 0 -> 0 < d -> 0 < bv_unsigned b ->
  bv_unsigned b + d < 2 ^ 64 ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  bv_unsigned b + d <= alloc_top h
  /\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true
  /\ vm_backing_used m + d <= vm_limit h.                               (* [comment removed for export] *)
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hnw H.
  enough (G : (bv_unsigned b + d <= alloc_top h /\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true) /\ vm_backing_used m + d <= vm_limit h) by tauto.
  split.
  2:{ assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = bv_unsigned b + d) by (apply u64_lit; lia).
      unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H.
      rewrite (proj2 (Z.ltb_lt 0 _) Hb0) in H. rewrite Hureq in H. rewrite (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
      apply andb_prop in H as [_ H]. apply Z.leb_le in H.
      replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d in H; [exact H|].
      rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = bv_unsigned b + d) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H. rewrite Hureq in H.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in H by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in H
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in H by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b) with (d + page_size) in H by lia.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
  (* [comment removed for export] *)
  assert (Hb4 : page_size <= bv_unsigned b) by (clear - Hbal Hb0; unfold page_size in *; Z.div_mod_to_equations; lia).
  eapply AllocSim.region_free_prefix; [| exact H2]. rewrite !u64_lit by (unfold page_size in *; lia). unfold page_size; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EVENTS.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.                 (* [comment removed for export] *)
Hypothesis Halloc : sc_alloc scfg = false.   (* [comment removed for export] *)
Variable resv_img : list (word * word).
Variable img_hi : Z.

(* [comment removed for export] *)

Variable CAPK CAPB : Z.
Hypothesis HCAPK : CAPK <= CAPKMAX.
(* [comment removed for export] *)

Local Notation KL := (KL2 resv_img img_hi).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_brk0 : forall L pbrk ms mo K,
  KL L pbrk (m_vmmaps mo) -> ld_brk L = BPUntried ->
  m_halted mo = None -> m_vm_lazy mo = [] ->
  Nodes.at_node segs (NBrk 0) ms ->
  (let r := bv_unsigned (vm_brk (m_vmmaps mo)) in
   let rsp := mkEffectU (vm_brk (m_vmmaps mo)) [] [] [] [] [] in
   dec_brk0 rsp = Some r ->
   brk0_answer_ok r = true ->
   KL (set_brkph (BPQueried r) L) r (m_vmmaps mo) ->
   srealizes segs scfg (mkCfg (nret ms rsp) mo) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo K HK Hph Hh Hl Hat HC.
  destruct (KL2_brk0 resv_img img_hi L pbrk (m_vmmaps mo) HK Hph) as [Hans HK'].
  eapply (bn_brk_query segs scfg); [exact Hh| exact Hl| exact Hat|].
  apply HC; [reflexivity| exact Hans| exact HK'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_brk_same : forall cur req (b : word), bv_unsigned b = cur ->
  dec_brk cur req (mkEffectU b [] [] [] [] []) = Some BrkSame.
Proof. intros cur req b Hb. unfold dec_brk. rewrite Hb, Z.eqb_refl. reflexivity. Qed.

Lemma dec_brk_grown : forall cur d (b : word), bv_unsigned b = cur ->
  cur mod page_size = 0 -> d mod page_size = 0 -> 0 < d -> 0 <= cur -> cur + d < 2 ^ 64 ->
  dec_brk cur (cur + d) (mkEffectU (Z_to_bv 64 (cur + d)) [] [(b, Z_to_bv 64 d)] [] [] []) = Some BrkGrown.
Proof.
  intros cur d b Hb Hcal Hdal Hd Hc Hnw. unfold dec_brk.
  rewrite u64_lit by lia. replace (cur + d =? cur) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
  rewrite Z.eqb_refl. unfold brk_new_pages.
  rewrite (page_round_up_Z_aligned cur) by (first [lia | exact Hcal]).
  rewrite (page_round_up_Z_aligned (cur + d)) by (first [lia | rewrite Z.add_mod, Hcal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [zeros_of]. replace (cur + d - cur) with d by lia.
  unfold wa. rewrite <- Hb, Z_to_bv_bv_unsigned. cbn [listNN_eqb]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_brk_grow : forall L pbrk ms mo (d : Z) ne bb K (e := EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + d)),
  let h := m_vmmaps mo in let b := vm_brk h in let req := bv_unsigned b + d in
  KL L pbrk h ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h -> d <= bb -> 0 < d <= NMAX -> d mod page_size = 0 ->
  pbrk = bv_unsigned b -> bv_unsigned b mod PGSZ = 0 -> 0 < bv_unsigned b -> bv_unsigned b + d < 2 ^ 64 ->
  bv_unsigned (vm_start_brk h) <= bv_unsigned b + d ->
  (answer_ok L e pbrk = true /\ KL (event_post L e pbrk) pbrk h) ->
  (region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true -> bv_unsigned b + d <= alloc_ceiling ->
   answer_ok L e req = true /\
   KL (event_post L e req) req
      (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                    (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))) ->
  Nodes.at_node segs (NBrk req) ms ->
  (* [comment removed for export] *)
  (let rsp := mkEffectU b [] [] [] [] [] in
   dec_brk pbrk req rsp = Some BrkSame ->
   answer_ok L e pbrk = true ->
   KL (event_post L e pbrk) pbrk h ->
   RI CAPK CAPB ne bb h ->
   srealizes segs scfg (mkCfg (nret ms rsp) mo) K) ->
  (* [comment removed for export] *)
  (let rsp := mkEffectU (Z_to_bv 64 req) [] [(b, Z_to_bv 64 d)] [] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                          (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_brk pbrk req rsp = Some BrkGrown ->
   answer_ok L e req = true ->
   KL (event_post L e req) req h' ->
   RI CAPK CAPB ne (bb - d) h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo d ne bb K e h b req HK Hh Hl Hm HRI Hdb Hd Hdal Hpb Hbal Hb0 Hnw Hsb [HansR HKR] HG Hat HREF HGRANT.
  pose proof (u64_range b) as Hbr.
  assert (Hbal' : bv_unsigned b mod page_size = 0) by (unfold page_size; unfold PGSZ in Hbal; exact Hbal).
  eapply (bn_brk_grow segs scfg Halloc ms mo d K Hh Hl); [exact Hat| exact Hbal'| exact Hdal| lia| exact Hb0| exact Hnw| exact Hsb| |].
  - (* [comment removed for export] *)
    apply HREF; [apply dec_brk_same; symmetry; exact Hpb| exact HansR| exact HKR|].
    eapply (RI_weaken CAPK CAPB (S ne) ne bb bb); [| lia| pose proof HRI as (_ & _ & _ & R4 & _ & _ & _); lia].
    subst h. rewrite <- (vmmaps_eta (m_vmmaps mo)) in HRI. exact HRI.
  - (* [comment removed for export] *)
    intros Hadm.
    destruct (brk_grow_ok_aligned_elim mo d Hbal' Hdal ltac:(lia) Hb0 Hnw Hadm) as (Hce & Hrf & Hbud).
    change (m_vmmaps mo) with h in Hce. rewrite (KL2_alloc_top _ _ _ _ _ HK) in Hce.
    destruct (HG Hrf Hce) as [HansG HKG].
    assert (Hused : 0 <= vm_backing_used mo).
    { unfold vm_backing_used. pose proof (RefNodes.live_bytes_nonneg (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo))). unfold page_size. lia. }
    apply HGRANT; [| exact HansG| exact HKG|].
    + rewrite Hpb. apply dec_brk_grown; first [reflexivity| assumption| lia].
    + apply RI_add; [exact HRI| lia| exact Hdb| apply u64_lit; lia| right; change (vm_limit h) with (vm_limit (m_vmmaps mo)); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_MAPF : (Z.land MAPF MAP_FIXED =? 0) = true.
Proof. reflexivity. Qed.

Lemma answer_ok_mmap : forall L a len prot z,
  answer_ok L (EMmap a len prot MAPF) z = mmap_answer_ok (lranges L) len z.
Proof. intros. unfold answer_ok. rewrite land_MAPF. reflexivity. Qed.

Lemma event_post_mmap_rw : forall L len z, is_err z = false ->
  event_post L (EMmap 0 len PROT_RW MAPF) z = set_groups ((z, len) :: ld_groups L) L.
Proof. intros L len z Hz. unfold event_post. rewrite land_MAPF, Hz. reflexivity. Qed.

Lemma event_post_mmap_none : forall L len z, is_err z = false ->
  event_post L (EMmap 0 len PROT_NONE MAPF) z = set_metas ((z, len, 0) :: ld_metas L) L.
Proof. intros L len z Hz. unfold event_post. rewrite land_MAPF, Hz. reflexivity. Qed.

Lemma mmap_addr_ok_nil : forall len (a : word),
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  mmap_addr_ok len [] (bv_unsigned a) = true.
Proof.
  intros len a H1 H2 H3. unfold mmap_addr_ok. rewrite H1, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) H2).
  rewrite (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.

Lemma dec_mmap_ok : forall len (a : word),
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  dec_mmap len [] (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []) = Some (MmOk (bv_unsigned a)).
Proof.
  intros len a H1 H2 H3. unfold dec_mmap. rewrite !bv_eqb_refl, (mmap_addr_ok_nil len a H1 H2 H3). reflexivity.
Qed.

Lemma dec_mmap_none_ok : forall len (a : word),
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  dec_mmap_none len [] (mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] []) = Some (MmOk (bv_unsigned a)).
Proof.
  intros len a H1 H2 H3. unfold dec_mmap_none. rewrite !bv_eqb_refl, (mmap_addr_ok_nil len a H1 H2 H3). reflexivity.
Qed.


Lemma step_mmap_rw : forall L pbrk ms mo len ne bb K (e := EMmap 0 len PROT_RW MAPF),
  let h := m_vmmaps mo in let n := mmap_len len in
  KL L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h -> n <= bb -> K [] ->      (* [comment removed for export] *)
  Nodes.at_node segs (NMmap 0 len 3 34) ms ->
  (forall a : word,
     let z := bv_unsigned a in
     let rsp := mkEffectU a [] [(a, Z_to_bv 64 n)] [] [] [] in
     let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                            (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
     dec_mmap len [] rsp = Some (MmOk z) ->
     answer_ok L e z = true -> is_err z = false ->
     KL (event_post L e z) pbrk h' ->
     RI CAPK CAPB ne (bb - n) h' ->
     srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo len ne bb K e h n HK Hq Hlen Hh Hl Hm HRI Hnb HK0 Hat HC. subst e.
  destruct (Z_le_gt_dec n NMAX) as [HnN | Hhuge].
  2: { pose proof HRI as (_ & _ & _ & _ & _ & R7 & _).
       eapply (bn_mmap_rw_huge segs scfg ms mo len K Hh Hat); [unfold LEN_MAX in Hlen; lia | | | exact HK0].
       - change (page_round_up_Z len) with n. fold h. unfold XLIM, NMAX in *. lia.
       - fold h. unfold XLIM, nbr_limit in *. lia. }
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. fold n in Hn1.
  assert (HnA : n mod page_size = 0) by (unfold n; apply mmap_len_aligned).
  assert (Hun : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; unfold NMAX in HnN; lia).
  eapply (bn_mmap_rw_nbr segs scfg Halloc ms mo len K Hh Hl Hat); [unfold LEN_MAX in Hlen; lia| | | exact HK0|].
  - change (page_round_up_Z len) with n. eapply (RI_grant_na CAPK CAPB (S ne) bb mo n HRI HCAPK); lia.
  - change (page_round_up_Z len) with n. intros Hbig. exact (RI_budget CAPK CAPB (S ne) bb mo n HRI Hbig).
  - intros a Hg Hfit. change (page_round_up_Z len) with n in Hg, Hfit |- *.
    assert (Hused : 0 <= vm_backing_used mo).
    { unfold vm_backing_used. pose proof (RefNodes.live_bytes_nonneg (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo))). unfold page_size. lia. }
    destruct (grant_ok_na_unpack _ _ _ _ Hg) as (G1 & G2 & G3 & G4).
    fold h in G3. rewrite (KL2_alloc_top _ _ _ _ _ HK) in G3.
    destruct (KL2_mmap_new resv_img img_hi L pbrk h a len false HK Hq Hlen
                ltac:(unfold PGSZ; unfold page_size in G1; exact G1) G2 G3 G4) as (HK' & Hans & Herr).
    unfold mmap_model. fold h. apply HC.
    + apply dec_mmap_ok; [exact G1| exact G2| exact G3].
    + rewrite answer_ok_mmap. exact Hans.
    + exact Herr.
    + rewrite (event_post_mmap_rw L len _ Herr). exact HK'.
    + apply RI_add; [exact HRI| lia| exact Hnb| exact Hun| right; change (vm_limit h) with (vm_limit (m_vmmaps mo)); lia].
Qed.

Lemma step_mmap_none : forall L pbrk ms mo len ne bb K (e := EMmap 0 len PROT_NONE MAPF),
  let h := m_vmmaps mo in let n := mmap_len len in
  KL L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h -> n <= bb -> n <= NONEMAX ->      (* [comment removed for export] *)
  Nodes.at_node segs (NMmap 0 len 0 34) ms ->
  (forall a : word,
     let z := bv_unsigned a in
     let rsp := mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] [] in
     let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) ((a, Z_to_bv 64 n) :: vm_noaccess h)
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
     dec_mmap_none len [] rsp = Some (MmOk z) ->
     answer_ok L e z = true -> is_err z = false ->
     KL (event_post L e z) pbrk h' ->
     RI CAPK CAPB ne (bb - n) h' ->
     srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo len ne bb K e h n HK Hq Hlen Hh Hl Hm HRI Hnb HnN Hat HC. subst e.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. fold n in Hn1.
  assert (HnA : n mod page_size = 0) by (unfold n; apply mmap_len_aligned).
  assert (Hun : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; unfold NONEMAX in HnN; lia).
  eapply (bn_mmap_none segs scfg Halloc ms mo len K Hh Hl Hat); [unfold LEN_MAX in Hlen; lia| |].
  - change (page_round_up_Z len) with n. eapply (RI_grant_na CAPK CAPB (S ne) bb mo n HRI HCAPK); unfold NONEMAX, NMAX in *; lia.
  - intros a Hg. change (page_round_up_Z len) with n in Hg |- *.
    destruct (grant_ok_na_unpack _ _ _ _ Hg) as (G1 & G2 & G3 & G4).
    fold h in G3. rewrite (KL2_alloc_top _ _ _ _ _ HK) in G3.
    destruct (KL2_mmap_new resv_img img_hi L pbrk h a len true HK Hq Hlen
                ltac:(unfold PGSZ; unfold page_size in G1; exact G1) G2 G3 G4) as (HK' & Hans & Herr).
    unfold noaccess_model. fold h. apply HC.
    + apply dec_mmap_none_ok; [exact G1| exact G2| exact G3].
    + rewrite answer_ok_mmap. exact Hans.
    + exact Herr.
    + rewrite (event_post_mmap_none L len _ Herr). exact HK'.
    + apply RI_add; [exact HRI| unfold NONEMAX, NMAX in *; lia| exact Hnb| exact Hun| left; exact HnN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_mmap_fixed_ok : forall addr (aw : word), aw = Z_to_bv 64 addr -> 0 <= addr <= 2^64 - 4096 ->
  dec_mmap_fixed addr PGSZ (mkEffectU aw [] [] [(aw, Z_to_bv 64 PGSZ)] [] []) = Some FxDone.
Proof.
  intros addr aw -> Ha. unfold dec_mmap_fixed.
  rewrite (mmap_len_of_aligned PGSZ) by (unfold PGSZ; first [lia| reflexivity]).
  rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by lia. reflexivity.
Qed.

Lemma step_mmap_fixed : forall L pbrk ms mo cur ne bb K,
  let h := m_vmmaps mo in
  let a := round_up_pg cur in
  let e := EMmap a PGSZ PROT_NONE MAPFX in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  KL L pbrk h -> ld_brk L = BPGuard cur ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h ->
  Nodes.at_node segs (NMmap a PGSZ 0 50) ms ->
  (let rsp := mkEffectU aw [] [] [(aw, nw)] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_mmap_fixed a PGSZ rsp = Some FxDone ->
   answer_ok L e a = true ->
   KL (event_post L e a) pbrk h' ->
   RI CAPK CAPB ne bb h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo cur ne bb K h a e aw nw HK Hph Hh Hl Hm HRI Hat HC. subst e aw nw. subst a.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_mmap_fixed resv_img img_hi L pbrk h cur HK Hph) as (Ea & Hcal & Hc0 & Hce & Hrf & Hmc & Hans & HK').
  rewrite !Ea in Hrf. rewrite !Ea in Hmc. rewrite !Ea in Hans. rewrite !Ea in HK'. rewrite !Ea in Hat. rewrite !Ea in HC. rewrite ?Ea.
  set (aw := Z_to_bv 64 cur) in *. set (nw := Z_to_bv 64 PGSZ) in *.
  assert (HprP : page_round_up_Z PGSZ = PGSZ) by reflexivity.
  eapply (bn_mmap_fixed segs scfg Halloc ms mo cur PGSZ K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hcal. exact Hcal.
  - lia.
  - unfold PGSZ; lia.
  - rewrite HprP. fold h. rewrite (KL2_alloc_top _ _ _ _ _ HK). lia.
  - rewrite HprP. exact Hrf.
  - rewrite HprP. exact Hmc.
  - rewrite HprP. fold nw. fold aw.
    rewrite (fixed_noaccess_model_simple aw nw mo Hl Hm). fold h.
    assert (Ua : bv_unsigned aw = cur) by (subst aw; apply u64_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply u64_lit; unfold PGSZ; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_mmap_fixed_ok; [reflexivity| unfold PGSZ in *; lia].
    + unfold answer_ok. change (Z.land MAPFX MAP_FIXED =? 0) with false. exact Hans.
    + exact HK'.
    + eapply RI_tick; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _ & _ & _); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_munmap_ok : forall a len (aw nw : word), aw = Z_to_bv 64 a -> nw = Z_to_bv 64 (mmap_len len) ->
  dec_munmap a len (mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []) = Some (RgDone true).
Proof. intros a len aw nw -> ->. unfold dec_munmap. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma step_munmap : forall L pbrk ms mo a l0 len ne bb K (e := EMunmap a len),
  let h := m_vmmaps mo in
  let n := mmap_len l0 in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  KL L pbrk h -> brk_quiet L -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h ->
  Nodes.at_node segs (NMunmap a len) ms ->
  (let rsp := mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_munmap a len rsp = Some (RgDone true) ->
   answer_ok L e 0 = true ->
   KL (event_post L e 0) pbrk h' ->
   RI CAPK CAPB ne bb h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo a l0 len ne bb K e h n aw nw HK Hq Hin Hlen Hh Hl Hm HRI Hat HC. subst e.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_munmap resv_img img_hi L pbrk h a l0 len HK Hq Hin Hlen)
    as (Hlen1 & Hlen2 & Hal & Ha0 & Hn0 & Hce & Hhas & Hans & HK' & Hcnt & Hlb).
  fold n aw nw in Hhas, HK', Hcnt, Hlb, Hlen2, Hn0, Hce.
  assert (Hpr : page_round_up_Z len = n) by (rewrite <- Hlen2; reflexivity).
  eapply (bn_munmap segs scfg ms mo a len K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hal. exact Hal.
  - lia.
  - lia.
  - rewrite Hpr. unfold TASK_SIZE. pose_ceil. lia.
  - rewrite Hpr. exact Hhas.
  - rewrite Hpr. fold aw nw. rewrite (munmap_model_simple aw nw mo Hl Hm). fold h.
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply u64_lit; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_munmap_ok; [reflexivity| rewrite Hlen2; reflexivity].
    + exact Hans.
    + exact HK'.
    + eapply RI_remove; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _ & _ & _); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_mprotect_rw_ok : forall a (aw nw : word), aw = Z_to_bv 64 a -> nw = Z_to_bv 64 (mmap_len PGSZ) ->
  dec_mprotect_rw a PGSZ (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] []) = Some (RgDone true).
Proof. intros a aw nw -> ->. unfold dec_mprotect_rw, dec_mprotect. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma step_mprotect : forall L pbrk ms mo b l k ne bb K,
  let h := m_vmmaps mo in
  let a := b + (1 + k) * PGSZ in
  let e := EMprotect a PGSZ PROT_RW in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  KL L pbrk h -> brk_quiet L -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h ->
  Nodes.at_node segs (NMprotect a PGSZ 3) ms ->
  (let rsp := mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_mprotect_rw a PGSZ rsp = Some (RgDone true) ->
   answer_ok L e 0 = true ->
   KL (event_post L e 0) pbrk h' ->
   RI CAPK CAPB ne bb h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo b l k ne bb K h a e aw nw HK Hq Hin Hk Hh Hl Hm HRI Hat HC. subst e.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_mprotect resv_img img_hi L pbrk h b l k HK Hq Hin Hk) as (Hal & Ha0 & Hce & Hcn & Hcm & Hans & HK').
  fold a in Hal, Ha0, Hce, Hcn, Hcm, HK', Hans |- *. fold aw nw in Hcn, Hcm, HK'.
  assert (HprP : page_round_up_Z PGSZ = PGSZ) by reflexivity.
  eapply (bn_mprotect_nbr segs scfg Halloc ms mo a PGSZ K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hal. exact Hal.
  - unfold PGSZ; lia.
  - lia.
  - rewrite HprP. unfold two_pow_64. lia.
  - rewrite HprP. exact Hcn.
  - rewrite HprP. exact Hcm.
  - rewrite HprP. fold nw. intros Hbig. apply RefNodes.mprotect_budget_ok_intro; [exact Hl| exact Hm|].
    pose proof (RI_live_limit _ _ _ _ _ HRI Hbig). pose proof HRI as (_ & _ & _ & R4 & _ & _ & _). unfold vm_live_bytes. fold h. lia.
  - rewrite HprP. fold aw nw. unfold mprotect_model. fold h.
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply u64_lit; unfold PGSZ; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_mprotect_rw_ok; [reflexivity|]. rewrite (mmap_len_of_aligned PGSZ) by (unfold PGSZ; first [lia| reflexivity]). reflexivity.
    + exact Hans.
    + exact HK'.
    + eapply RI_tick; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _ & _ & _); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ev_step_brk0 : ev_step (EBrk 0) = (mbind (msys (NBrk 0) dec_brk0) (fun r => mbind (mupd (set_brk_ps r)) (fun _ => mret r))).
Proof. reflexivity. Qed.

Lemma ev_step_brk : forall req, req <> 0 ->
  ev_step (EBrk req) =
  mbind mget (fun s => mbind (msys (NBrk req) (dec_brk (ps_brk s) req))
     (fun a => match a with BrkGrown => mbind (mupd (set_brk_ps req)) (fun _ => mret req) | BrkSame => mret (ps_brk s) end)).
Proof. intros req H. unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma ev_step_mmap_rw : forall len,
  ev_step (EMmap 0 len PROT_RW MAPF) =
  mbind (msys (NMmap 0 len PROT_RW MAPF) (dec_mmap len [])) (fun a => mret match a with MmErr e => neg_errno e | MmOk x => x end).
Proof. reflexivity. Qed.

Lemma ev_step_mmap_none : forall len,
  ev_step (EMmap 0 len PROT_NONE MAPF) =
  mbind (msys (NMmap 0 len PROT_NONE MAPF) (dec_mmap_none len [])) (fun a => mret match a with MmErr e => neg_errno e | MmOk x => x end).
Proof. reflexivity. Qed.

Lemma ev_step_mmap_fixed : forall a len,
  ev_step (EMmap a len PROT_NONE MAPFX) =
  mbind (msys (NMmap a len PROT_NONE MAPFX) (dec_mmap_fixed a len))
        (fun x => mret match x with FxKept e => neg_errno e | FxDone => a | FxLost e => neg_errno e end).
Proof. reflexivity. Qed.

Lemma ev_step_munmap : forall a len,
  ev_step (EMunmap a len) =
  mbind (msys (NMunmap a len) (dec_munmap a len)) (fun x => mret match x with RgErr e => neg_errno e | RgDone _ => 0 end).
Proof. reflexivity. Qed.

Lemma ev_step_mprotect : forall a len prot,
  ev_step (EMprotect a len prot) =
  mbind (msys (NMprotect a len prot) (dec_mprotect_rw a len)) (fun x => mret match x with RgErr e => neg_errno e | RgDone _ => 0 end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma machine_event : forall {A B} n (dec : resp -> option A) (f : A -> Monad.M PState B) (s : PState) Qm ms,
  implM segs (mbind (msys n dec) f) s Qm ms ->
  exists ms1, Exec.msteps segs ms ms1 /\ Nodes.at_node segs n ms1 /\
    forall rsp a, dec rsp = Some a -> exists ms2, Exec.msteps segs (nret ms1 rsp) ms2 /\ implM segs (f a) s Qm ms2.
Proof.
  intros A B n dec f s Qm ms H. apply implM_bind_inv, implM_msys_inv in H.
  destruct H as (ms1 & Hms & Hat & Hk). exists ms1. split; [exact Hms|]. split; [exact Hat|].
  intros rsp a E. destruct (Hk rsp a E) as (ms2 & Hms2 & H2). exists ms2. auto.
Qed.

Lemma srz_cj_msteps : forall ms ms' mo mo0 K,
  mo = with_vmmaps (m_vmmaps mo) mo0 -> m_halted mo0 = None -> m_vm_lazy mo0 = [] ->
  Exec.msteps segs ms ms' -> srealizes segs scfg (mkCfg ms' mo) K -> srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros ms ms' mo mo0 K Emo Hh Hl Hms Hc.
  eapply srz_msteps; [rewrite Emo, with_vmmaps_halted; exact Hh| rewrite Emo, with_vmmaps_lazy'; exact Hl| apply cj_msteps_cat; exact Hms| exact Hc].
Qed.

Theorem embed : forall {R} (t : M R) L Post (E : ev -> Prop) (ne : nat) (bb : Z) (Q : R -> Prop)
    (s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) K,
  ctree_ok L t Post ->
  gtree E ne bb t Q ->
  (forall a len prot flags, E (EMmap a len prot flags) -> is_fixed flags = false -> prot = PROT_NONE -> mmap_len len <= NONEMAX) ->      (* [comment removed for export] *)
  implM segs (membed t) s Qm ms ->
  KL L (ps_brk s) (m_vmmaps mo) ->
  mo = with_vmmaps (m_vmmaps mo) mo0 ->
  m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
  K [] ->      (* [comment removed for export] *)
  RI CAPK CAPB ne bb (m_vmmaps mo) ->
  (forall r s' ms' mo' L',
     Qm r s' ms' -> cpath L t L' r -> Post L' r -> Q r ->
     KL L' (ps_brk s') (m_vmmaps mo') ->
     mo' = with_vmmaps (m_vmmaps mo') mo0 ->
     RI CAPK CAPB 0 0 (m_vmmaps mo') ->
     ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
     srealizes segs scfg (mkCfg ms' mo') K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros R t. induction t as [r|e k IH]; intros L Post E ne bb Q s Qm ms mo mo0 K Hct Hgt HE Himpl HK Emo Hh Hl Hm HK0 HRI CONT.
  - (* [comment removed for export] *)
    cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
    eapply (CONT r s ms' mo L HQ (cpath_ret L r) Hct Hgt HK Emo); try reflexivity.
    eapply RI_weaken; [exact HRI| lia| pose proof HRI as (_ & _ & _ & R4 & _ & _ & _); lia].
  - (* [comment removed for export] *)
    cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
    assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    destruct (gtree_vis_inv E ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
    cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
    assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
    assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
    pose proof HRI as (_ & _ & _ & Hbb0 & _).
    (* [comment removed for export] *)
    assert (KONT : forall z (s1 : PState) ms2 (mo1 : Model) (bb1 : Z),
              answer_ok L e z = true -> good e z ->
              implM segs (membed (k z)) s1 Qm ms2 ->
              KL (event_post L e z) (ps_brk s1) (m_vmmaps mo1) ->
              mo1 = with_vmmaps (m_vmmaps mo1) mo0 ->
              RI CAPK CAPB ne' bb1 (m_vmmaps mo1) -> 0 <= bb - ecost e <= bb1 ->
              ps_m s1 = ps_m s -> ps_fa s1 = ps_fa s -> ps_so s1 = ps_so s ->
              srealizes segs scfg (mkCfg ms2 mo1) K).
    { intros z s1 ms2 mo1 bb1 Hans Hgood Hi1 HK1 Emo1 HRI1 Hbb1 E1 E2 E3.
      eapply (IH z (event_post L e z) Post E ne' (bb - ecost e) Q s1 Qm ms2 mo1 mo0 K (Hk z Hans) (Hg z Hgood) HE Hi1 HK1 Emo1 Hh Hl Hm HK0).
      - eapply RI_weaken; [exact HRI1| lia| lia].
      - intros r s' ms' mo' L' HQ' Hcp HP HQr HK' Emo' HRI' E1' E2' E3'.
        eapply (CONT r s' ms' mo' L' HQ'); [eapply cpath_vis; [exact Hans| exact Hcp]| exact HP| exact HQr| exact HK'| exact Emo'| exact HRI'| congruence| congruence| congruence]. }
    clear IH CONT Hk Hg.
    destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [event_pre] in Hpre; try contradiction.
    + (* [comment removed for export] *)
      destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
      * (* [comment removed for export] *)
        rewrite ev_step_brk0 in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        eapply step_brk0; [exact HK| exact Hph| exact Hh'| exact Hl'| exact Hat|].
        intros r0 rsp Hdec Hans HK'.
        destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
        destruct Hi2 as (ms3 & Hms3 & Hi3).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
        eapply (KONT r0 (set_brk_ps r0 s) ms3 mo bb);
          [exact Hans| exact I| exact Hi3| exact HK'| exact Emo| eapply RI_weaken; [exact HRI| lia| lia]| cbn [ecost Z.eqb]; lia
          | reflexivity| reflexivity| reflexivity].
      * (* [comment removed for export] *)
        destruct (KL2_brk_grow1 resv_img img_hi L (ps_brk s) (m_vmmaps mo) cur HK Hph)
          as (Ecur & Epbrk & Ereq & Hbal & Hb0 & Hnw & Hsb & Hne0 & HREF & HGR).
        rewrite (ev_step_brk _ Hne0) in Himpl. apply implM_mget_inv in Himpl.
        rewrite Ereq in *. rewrite <- Epbrk in HREF.
        destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        assert (Hc2 : ecost (EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + 2 * PGSZ)) = 2 * PGSZ).
        { cbn [ecost]. rewrite (proj2 (Z.eqb_neq _ _) Hne0). reflexivity. }
        rewrite Hc2 in *.
        eapply (step_brk_grow L (ps_brk s) ms1 mo (2 * PGSZ) ne' bb K HK Hh' Hl' Hm' HRI);
          [lia| pose proof NMAX_facts; unfold PGSZ in *; lia| unfold PGSZ, page_size; reflexivity| lia| exact Hbal| exact Hb0| exact Hnw| exact Hsb
          | exact HREF| exact HGR| exact Hat| |].
        -- (* [comment removed for export] *)
           intros rsp Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT (ps_brk s) s ms3 mo bb);
             [exact Hans| exact I| exact Hi3| exact HK'| exact Emo| exact HRI'| lia
             | reflexivity| reflexivity| reflexivity].
        -- (* [comment removed for export] *)
           intros rsp h' Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
           destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT _ (set_brk_ps _ s) ms3 _ (bb - 2 * PGSZ));
             [exact Hans| exact I| exact Hi3| cbn [ps_brk set_brk_ps]; rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
             | reflexivity| reflexivity| reflexivity].
      * (* [comment removed for export] *)
        destruct (KL2_brk_grow2 resv_img img_hi L (ps_brk s) (m_vmmaps mo) b l HK Hph Hreg)
          as (Epbrk & Ebrk & Ereq & Hbal & Hb0 & Hnw & Hsb & Hne0 & HREF & HGR).
        rewrite (ev_step_brk _ Hne0) in Himpl. apply implM_mget_inv in Himpl.
        rewrite Ereq in *. rewrite <- Epbrk in HREF.
        assert (Epbrk' : ps_brk s = bv_unsigned (vm_brk (m_vmmaps mo))) by lia.
        destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        assert (Hc2 : ecost (EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + PGSZ)) = 2 * PGSZ).
        { cbn [ecost]. rewrite (proj2 (Z.eqb_neq _ _) Hne0). reflexivity. }
        rewrite Hc2 in *.
        eapply (step_brk_grow L (ps_brk s) ms1 mo PGSZ ne' bb K HK Hh' Hl' Hm' HRI);
          [unfold PGSZ in *; lia| pose proof NMAX_facts; unfold PGSZ in *; lia| unfold PGSZ, page_size; reflexivity| exact Epbrk'| exact Hbal| exact Hb0| exact Hnw| exact Hsb
          | exact HREF| exact HGR| exact Hat| |].
        -- (* [comment removed for export] *)
           intros rsp Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT (ps_brk s) s ms3 mo bb);
             [exact Hans| exact I| exact Hi3| exact HK'| exact Emo| exact HRI'| unfold PGSZ in *; lia
             | reflexivity| reflexivity| reflexivity].
        -- (* [comment removed for export] *)
           intros rsp h' Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
           destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT _ (set_brk_ps _ s) ms3 _ (bb - PGSZ));
             [exact Hans| exact I| exact Hi3| cbn [ps_brk set_brk_ps]; rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| unfold PGSZ in *; lia
             | reflexivity| reflexivity| reflexivity].
    + (* [comment removed for export] *)
      destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
      * (* [comment removed for export] *)
        assert (Hc2 : ecost (EMmap 0 len prot MAPF) = mmap_len len) by reflexivity. rewrite Hc2 in *.
        destruct Hprot as [-> | ->].
        -- (* [comment removed for export] *)
           pose proof (HE 0 len PROT_NONE MAPF HEe eq_refl eq_refl) as HnN.
           rewrite ev_step_mmap_none in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
           eapply (step_mmap_none L (ps_brk s) ms1 mo len ne' bb K HK Hq Hlen Hh' Hl' Hm' HRI Hcost HnN Hat).
           intros aw z rsp h' Hdec Hans Herr HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT z s ms3 _ (bb - mmap_len len));
             [exact Hans| cbn [good]; right; exact Herr| exact Hi3| rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
             | reflexivity| reflexivity| reflexivity].
        -- (* [comment removed for export] *)
           rewrite ev_step_mmap_rw in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
           eapply (step_mmap_rw L (ps_brk s) ms1 mo len ne' bb K HK Hq Hlen Hh' Hl' Hm' HRI Hcost HK0 Hat).
           intros aw z rsp h' Hdec Hans Herr HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT z s ms3 _ (bb - mmap_len len));
             [exact Hans| cbn [good]; right; exact Herr| exact Hi3| rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
             | reflexivity| reflexivity| reflexivity].
      * (* [comment removed for export] *)
        assert (Hc2 : ecost (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) = 0) by reflexivity. rewrite Hc2 in *.
        rewrite ev_step_mmap_fixed in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        eapply (step_mmap_fixed L (ps_brk s) ms1 mo cur ne' bb K HK Hph Hh' Hl' Hm' HRI Hat).
        intros rsp h' Hdec Hans HK' HRI'.
        destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
        eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
        eapply (KONT (round_up_pg cur) s ms3 _ bb);
          [exact Hans| cbn [good]; left; reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
          | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
          | reflexivity| reflexivity| reflexivity].
    + (* [comment removed for export] *)
      destruct Hpre as (Hq & l0 & Hin & Hlen).
      assert (Hc2 : ecost (EMunmap a len) = 0) by reflexivity. rewrite Hc2 in *.
      rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
      eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
      eapply (step_munmap L (ps_brk s) ms1 mo a l0 len ne' bb K HK Hq Hin Hlen Hh' Hl' Hm' HRI Hat).
      intros rsp h' Hdec Hans HK' HRI'.
      destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
      eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
      eapply (KONT 0 s ms3 _ bb);
        [exact Hans| reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
        | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
        | reflexivity| reflexivity| reflexivity].
    + (* [comment removed for export] *)
      destruct Hpre as (Hq & -> & -> & b & l & kk & Hin & -> & Hk2).
      assert (Hc2 : ecost (EMprotect (b + (1 + kk) * PGSZ) PGSZ PROT_RW) = 0) by reflexivity. rewrite Hc2 in *.
      rewrite ev_step_mprotect in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
      eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
      eapply (step_mprotect L (ps_brk s) ms1 mo b l kk ne' bb K HK Hq Hin Hk2 Hh' Hl' Hm' HRI Hat).
      intros rsp h' Hdec Hans HK' HRI'.
      destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
      eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
      eapply (KONT 0 s ms3 _ bb);
        [exact Hans| reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
        | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
        | reflexivity| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_shrunk (h0 h : VmMaps) : Prop :=
     vm_reserved h = vm_reserved h0
  /\ (length (vm_maps h) <= length (vm_maps h0))%nat
  /\ live_bytes (vm_maps h) <= live_bytes (vm_maps h0)
  /\ (Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_maps h0) -> Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_maps h))
  /\ vm_limit h = vm_limit h0 /\ vm_mmap_base h = vm_mmap_base h0
  /\ incl (vm_maps h) (vm_maps h0).                                     (* [comment removed for export] *)

Lemma vm_shrunk_refl : forall h, vm_shrunk h h.
Proof. intros h. unfold vm_shrunk. repeat split; auto; try lia. apply incl_refl. Qed.

Lemma vm_shrunk_remove : forall h0 h aw na sb br,
  vm_shrunk h0 h ->
  vm_shrunk h0 (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros h0 h aw na sb br (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold vm_shrunk. cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
  pose proof (RefNodes.live_bytes_map_remove_le (vm_maps h) aw) as Hlb.
  unfold map_remove in *. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) aw)) (vm_maps h)) as Hlen.
  splits; auto; try lia.
  - intros HF. apply Forall_filter. apply S4. exact HF.
  - intros e He. apply S7. apply filter_In in He. exact (proj1 He).
Qed.

Lemma step_munmap_free : forall L pbrk ms mo a l0 len K (e := EMunmap a len),
  let h := m_vmmaps mo in
  let n := mmap_len l0 in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  KL L pbrk h -> brk_quiet L -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  Nodes.at_node segs (NMunmap a len) ms ->
  (let rsp := mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_munmap a len rsp = Some (RgDone true) ->
   answer_ok L e 0 = true ->
   KL (event_post L e 0) pbrk h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo a l0 len K e h n aw nw HK Hq Hin Hlen Hh Hl Hm Hat HC. subst e.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_munmap resv_img img_hi L pbrk h a l0 len HK Hq Hin Hlen)
    as (Hlen1 & Hlen2 & Hal & Ha0 & Hn0 & Hce & Hhas & Hans & HK' & Hcnt & Hlb).
  fold n aw nw in Hhas, HK', Hcnt, Hlb, Hlen2, Hn0, Hce.
  assert (Hpr : page_round_up_Z len = n) by (rewrite <- Hlen2; reflexivity).
  eapply (bn_munmap segs scfg ms mo a len K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hal. exact Hal.
  - lia.
  - lia.
  - rewrite Hpr. unfold TASK_SIZE. pose_ceil. lia.
  - rewrite Hpr. exact Hhas.
  - rewrite Hpr. fold aw nw. rewrite (munmap_model_simple aw nw mo Hl Hm). fold h.
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply u64_lit; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_munmap_ok; [reflexivity| rewrite Hlen2; reflexivity].
    + exact Hans.
    + exact HK'.
Qed.

Theorem embed_free : forall {R} (t : M R) L Post (ne : nat) (bb : Z) (Q : R -> Prop)
    (s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) (h0 : VmMaps) K,
  ctree_ok L t Post ->
  gtree efree_ok ne bb t Q ->
  implM segs (membed t) s Qm ms ->
  KL L (ps_brk s) (m_vmmaps mo) ->
  mo = with_vmmaps (m_vmmaps mo) mo0 ->
  m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
  vm_shrunk h0 (m_vmmaps mo) ->
  (forall r s' ms' mo' L',
     Qm r s' ms' -> cpath L t L' r -> Post L' r -> Q r ->
     KL L' (ps_brk s') (m_vmmaps mo') ->
     mo' = with_vmmaps (m_vmmaps mo') mo0 ->
     vm_shrunk h0 (m_vmmaps mo') ->
     ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
     srealizes segs scfg (mkCfg ms' mo') K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros R t. induction t as [r|e k IH]; intros L Post ne bb Q s Qm ms mo mo0 h0 K Hct Hgt Himpl HK Emo Hh Hl Hm HS CONT.
  - cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
    eapply (CONT r s ms' mo L HQ (cpath_ret L r) Hct Hgt HK Emo HS); reflexivity.
  - cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
    assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    destruct (gtree_vis_inv efree_ok ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
    cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
    assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
    assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
    destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [efree_ok] in HEe; try contradiction.
    cbn [event_pre] in Hpre. destruct Hpre as (Hq & l0 & Hin & Hlen).
    rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    eapply (step_munmap_free L (ps_brk s) ms1 mo a l0 len K HK Hq Hin Hlen Hh' Hl' Hm' Hat).
    intros rsp h' Hdec Hans HK'.
    destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
    eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
    eapply (IH 0 (event_post L (EMunmap a len) 0) Post ne' (bb - ecost (EMunmap a len)) Q s Qm ms3 _ mo0 h0 K
              (Hk 0 Hans) (Hg 0 eq_refl) Hi3).
    + rewrite with_vmmaps_vm. exact HK'.
    + rewrite Emo, with_vmmaps_twice, with_vmmaps_vm. reflexivity.
    + exact Hh. + exact Hl. + exact Hm.
    + rewrite with_vmmaps_vm. apply vm_shrunk_remove. exact HS.
    + intros r s' ms' mo' L' HQ' Hcp HP HQr HK'' Emo' HS' E1 E2 E3.
      eapply (CONT r s' ms' mo' L' HQ'); [eapply cpath_vis; [exact Hans| exact Hcp]| exact HP| exact HQr| exact HK''| exact Emo'| exact HS'| exact E1| exact E2| exact E3].
Qed.

End EVENTS.
End CEIL_WRAP_1.

