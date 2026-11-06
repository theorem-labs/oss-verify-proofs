(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] -> vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma with_vmmaps_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.

Lemma minv_with_vmmaps : forall h m, minv m -> minv (with_vmmaps h m).
Proof. intros h m [A B]. split; assumption. Qed.

Lemma halted_with_vmmaps : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.

Lemma vm_only_with_vmmaps' : forall h m, vm_only m (with_vmmaps h m).
Proof. intros h m. unfold vm_only, with_vmmaps. destruct m; cbn. repeat split; reflexivity. Qed.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros mo. unfold vm_only. repeat split; reflexivity. Qed.

Definition is_mm (n : node) : Prop :=
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end.

Lemma kfixna_model_minv : forall a n m, minv m ->
  kfixna_model a n m = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((a, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros a n m [Hl Hm]. unfold kfixna_model. apply vm_forget_range_id; assumption. Qed.

Lemma kfixlost_model_minv : forall a n m, minv m ->
  kfixlost_model a n m = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros a n m [Hl Hm]. unfold kfixlost_model. apply vm_forget_range_id; assumption. Qed.

Lemma kmunmap_model_minv : forall a n m, minv m ->
  kmunmap_model a n m = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) a)
               (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros a n m [Hl Hm]. unfold kmunmap_model, with_mmap_destroyed. apply vm_forget_range_id; assumption. Qed.

Lemma nstep_mm_facts : forall n mo rsp mo' evs,
  minv mo -> nstep n mo rsp mo' evs ->
  evs = [] /\ minv mo' /\ m_halted mo' = m_halted mo /\ vm_only mo mo' /\ exists h, mo' = with_vmmaps h mo.
Proof.
  intros n mo rsp mo' evs Hmi [-> Hn]. split; [reflexivity|].
  assert (G : forall h, mo' = with_vmmaps h mo ->
             minv mo' /\ m_halted mo' = m_halted mo /\ vm_only mo mo' /\ exists h, mo' = with_vmmaps h mo).
  { intros h ->. split; [apply minv_with_vmmaps; exact Hmi|]. split; [reflexivity|].
    split; [apply vm_only_with_vmmaps'|]. exists h; reflexivity. }
  assert (G0 : mo' = mo -> minv mo' /\ m_halted mo' = m_halted mo /\ vm_only mo mo' /\ exists h, mo' = with_vmmaps h mo).
  { intros ->. apply (G (m_vmmaps mo)). unfold with_vmmaps. destruct mo as [? [? ? ?] ? ? ? ?]; reflexivity. }
  destruct n; try (exfalso; exact Hn); cbv zeta in Hn.
  - destruct (req =? 0).
    + destruct Hn as [_ E]. exact (G0 E).
    + destruct Hn as [[_ E] | (_ & _ & E)]; [exact (G0 E) | exact (G _ E)].
  - destruct ((flags =? MAP_ANON_PRIV) && (prot =? PROT_RW_Z)).
    { destruct Hn as [(e & _ & _ & E) | (a & _ & _ & E)]; [exact (G0 E) | exact (G _ E)]. }
    destruct ((flags =? MAP_ANON_PRIV) && (prot =? 0)).
    { destruct Hn as [(e & _ & _ & E) | (a & _ & _ & E)]; [exact (G0 E) | exact (G _ E)]. }
    destruct ((flags =? MAP_ANON_PRIV_FIXED) && (prot =? 0)); [|exfalso; exact Hn].
    destruct Hn as [(e & _ & _ & E) | [(_ & E) | (e & _ & _ & E)]]; [exact (G0 E) | |].
    + rewrite kfixna_model_minv in E by exact Hmi. exact (G _ E).
    + rewrite kfixlost_model_minv in E by exact Hmi. exact (G _ E).
  - destruct Hn as [_ E]. rewrite kmunmap_model_minv in E by exact Hmi. exact (G _ E).
  - destruct Hn as [(e & _ & _ & E) | (_ & _ & E)]; [exact (G0 E) | exact (G _ E)].
Qed.

Lemma minv_preserved : forall n mo rsp mo' evs,
  minv mo -> m_halted mo = None -> nstep n mo rsp mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo rsp mo' evs Hmi Hh H. destruct (nstep_mm_facts n mo rsp mo' evs Hmi H) as (_ & A & B & _). rewrite B. auto.
Qed.

Lemma nstep_brk0_inv : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs -> evs = [] /\ rsp = eff0 (vm_brk (m_vmmaps mo)) /\ mo' = mo.
Proof. intros mo rsp mo' evs [-> H]. cbv zeta in H. cbn [Z.eqb] in H. destruct H as [-> ->]. auto. Qed.

Lemma nstep_brk_grow_inv : forall req mo rsp mo' evs, req <> 0 ->
  nstep (NBrk req) mo rsp mo' evs ->
  let h := m_vmmaps mo in let b := vm_brk h in
  evs = [] /\
  ((rsp = eff0 b /\ mo' = mo)
   \/ (kbrk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true
       /\ rsp = mkEffect (Z_to_bv 64 req) [] [(b, Z_to_bv 64 (req - bv_unsigned b))]
       /\ mo' = kbrk_grow_model (req - bv_unsigned b) mo)).
Proof.
  intros req mo rsp mo' evs Hr [-> H]. cbv zeta in H. rewrite (proj2 (Z.eqb_neq _ _) Hr) in H. split; [reflexivity | exact H].
Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H. destruct (nstep_brk0_inv _ _ _ _ H) as (-> & -> & ->).
  split; [reflexivity|]. split; [reflexivity|]. split; [apply vm_only_refl | reflexivity].
Qed.

Lemma region_free_shrink : forall maps (lo n n' : word),
  bv_unsigned n' <= bv_unsigned n -> region_free maps lo n = true -> region_free maps lo n' = true.
Proof.
  intros maps lo n n' Hle H. apply State.region_free_intro. intros a sz Hin.
  pose proof (State.region_free_In maps lo n a sz H Hin) as Ho. unfold iv_overlap in *.
  apply andb_false_iff in Ho as [Ho|Ho]; apply andb_false_iff; [left; exact Ho | right].
  apply Z.ltb_ge in Ho. apply Z.ltb_ge. lia.
Qed.

Lemma brk_grow_ok_facts : forall mo req,
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 - 4096 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  kbrk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  req <= alloc_ceiling /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true
  /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req + 4096 - b)) = true.
Proof.
  intros mo req h b Hb Hreq Hba Hra H. unfold kbrk_grow_ok in H. rewrite unsigned_lit in H by lia. fold h b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. change page_size with 4096 in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  split; [exact H1 |]. split; [| exact H2].
  eapply region_free_shrink; [| exact H2]. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma page_round_up_Z_id : forall z, z mod 4096 = 0 -> page_round_up_Z z = z.
Proof.
  intros z Hz. unfold page_round_up_Z. change page_size with 4096.
  pose proof (Z_div_mod_eq_full z 4096). pose proof (Z_div_mod_eq_full (z+4096-1) 4096). pose proof (Z.mod_pos_bound (z+4096-1) 4096). nia.
Qed.

Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  0 < bv_unsigned (vm_brk h) ->
  bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h) ->
  bv_unsigned (vm_brk h) < req < 2^64 ->
  bv_unsigned (vm_brk h) mod 4096 = 0 -> req mod 4096 = 0 ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h /\ mo' = mo
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req /\ bv_unsigned (vm_brk h) < req
      /\ kbrk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true
      /\ mo' = kbrk_grow_model (req - bv_unsigned (vm_brk h)) mo
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq Hbal Hral H. subst h.
  assert (Hr0 : req <> 0) by lia.
  destruct (nstep_brk_grow_inv req mo rsp mo' evs Hr0 H) as [-> Hcase]. split; [reflexivity|].
  cbv zeta in Hcase.
  destruct Hcase as [[-> ->] | (Hg & -> & ->)].
  - split; [apply vm_only_refl|]. exists BrkSame. split; [|auto].
    unfold dec_brk, eff0. rewrite Z.eqb_refl. reflexivity.
  - split; [apply vm_only_with_vmmaps'|].
    + exists BrkGrown. split.
      * unfold dec_brk. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
        rewrite unsigned_lit by lia.
        replace (req =? bv_unsigned (vm_brk (m_vmmaps mo))) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
        rewrite Z.eqb_refl. unfold brk_new_pages, zeros_of.
        rewrite (page_round_up_Z_id _ Hbal), (page_round_up_Z_id _ Hral).
        replace (bv_unsigned (vm_brk (m_vmmaps mo)) <? req) with true by (symmetry; apply Z.ltb_lt; lia).
        unfold wa. rewrite Z_to_bv_bv_unsigned.
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
      * unfold kbrk_grow_model. cbv zeta. rewrite with_vmmaps_vmmaps. cbn [vm_brk].
        split; [f_equal; lia|]. split; [lia|]. auto.
Qed.

Lemma ENOMEM_range : 1 <= ENOMEM <= 4095.
Proof. unfold ENOMEM. lia. Qed.

Lemma In_mmap_errnos : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.
Lemma In_mprotect_errnos : forall e, In e mprotect_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma kgrant_ok_na_facts : forall hint mo a n,
  kgrant_ok_na hint mo a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_ceiling
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true
  /\ True.
Proof.
  intros hint mo a n H. unfold kgrant_ok_na in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto 10.
Qed.

Lemma kgrant_ok_facts : forall hint mo a n,
  kgrant_ok hint mo a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_ceiling
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true
  /\ vm_backing_used mo + n <= vm_limit (m_vmmaps mo)
  /\ True.
Proof.
  intros hint mo a n H. unfold kgrant_ok in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H5. auto 10.
Qed.

Lemma mmap_addr_ok_of_grant : forall len avoid (a : word) mo,
  0 < len -> mmap_len len < 2^64 ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 (mmap_len len)) = true ->
  Forall (covered (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) avoid ->
  mmap_addr_ok len avoid (bv_unsigned a) = true.
Proof.
  intros len avoid a mo Hlen Hlen2 H1 H2 H3 H4 Hcov. pose proof (mmap_len_bound len Hlen) as Hb.
  unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3). cbn [andb].
  rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))); [exact H4 | exact Hcov].
Qed.

Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ kgrant_ok (Z_to_bv 64 0) mo (Z_to_bv 64 a) (mmap_len len) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hcov [-> H]. subst h. split; [reflexivity|].
  cbv zeta in H. change ((MAP_PRIVATE + MAP_ANONYMOUS =? MAP_ANON_PRIV) && (PROT_READ + PROT_WRITE =? PROT_RW_Z)) with true in H. cbv iota in H.
  fold (mmap_len len) in H.
  destruct H as [(e & He & -> & ->) | (a & Hg & -> & ->)].
  - split; [apply vm_only_refl|]. apply In_mmap_errnos in He. subst e. exists (MmErr ENOMEM). split; [|auto].
    unfold dec_mmap, efferr, eff0. rewrite errno_of_errno_ret by apply ENOMEM_range. reflexivity.
  - split; [apply vm_only_with_vmmaps'|].
    destruct (kgrant_ok_facts _ _ _ _ Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
    pose proof (mmap_addr_ok_of_grant len avoid a mo Hlen Hlen2 G1 G2 G3 G4 Hcov) as Hok.
    exists (MmOk (bv_unsigned a)). rewrite Z_to_bv_bv_unsigned. split.
    + unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + split; [exact Hok|]. split; [exact G4|]. split; [exact Hg|]. reflexivity.
Qed.

Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_none len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ kgrant_ok_na (Z_to_bv 64 0) mo (Z_to_bv 64 a) (mmap_len len) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hcov [-> H]. subst h. split; [reflexivity|].
  cbv zeta in H. change ((MAP_PRIVATE + MAP_ANONYMOUS =? MAP_ANON_PRIV) && (PROT_NONE =? PROT_RW_Z)) with false in H.
  change ((MAP_PRIVATE + MAP_ANONYMOUS =? MAP_ANON_PRIV) && (PROT_NONE =? 0)) with true in H. cbv iota in H.
  fold (mmap_len len) in H.
  destruct H as [(e & He & -> & ->) | (a & Hg & -> & ->)].
  - split; [apply vm_only_refl|]. apply In_mmap_errnos in He. subst e. exists (MmErr ENOMEM). split; [|auto].
    unfold dec_mmap_none, efferr, eff0. rewrite errno_of_errno_ret by apply ENOMEM_range. reflexivity.
  - split; [apply vm_only_with_vmmaps'|].
    destruct (kgrant_ok_na_facts _ _ _ _ Hg) as (G1 & G2 & G3 & G4 & G5).
    pose proof (mmap_addr_ok_of_grant len avoid a mo Hlen Hlen2 G1 G2 G3 G4 Hcov) as Hok.
    exists (MmOk (bv_unsigned a)). rewrite Z_to_bv_bv_unsigned. split.
    + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + split; [exact Hok|]. split; [exact G4|]. split; [exact Hg|]. reflexivity.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  minv mo ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  dec_munmap addr len rsp = Some (RgDone true) /\
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                   (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros addr len mo rsp mo' evs h a n Hmi [-> H]. subst h a n. split; [reflexivity|].
  cbv zeta in H. fold (mmap_len len) in H. destruct H as [-> ->].
  rewrite kmunmap_model_minv by exact Hmi.
  split; [apply vm_only_with_vmmaps'|]. split; [|reflexivity].
  unfold dec_munmap. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => e = ENOMEM /\ mo' = mo
  | RgDone false => False
  | RgDone true => mprotect_budget_ok mo a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n [-> H]. subst h a n. split; [reflexivity|].
  cbv zeta in H. fold (mmap_len len) in H.
  destruct H as [(e & He & -> & ->) | (Hbud & -> & ->)].
  - split; [apply vm_only_refl|]. apply In_mprotect_errnos in He. subst e. exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect, efferr, eff0. rewrite errno_of_errno_ret by apply ENOMEM_range. reflexivity.
  - split; [apply vm_only_with_vmmaps'|]. exists (RgDone true). split; [|auto].
    unfold dec_mprotect. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma nstep_mmap_fixed_inv : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  minv mo ->
  nstep (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  ((rsp = efferr ENOMEM /\ mo' = mo)
   \/ (rsp = mkEffectU aw [] [] [(aw, n)] [] []
       /\ mo' = with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                   ((aw, n) :: maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)
   \/ (rsp = mkEffectU (errno_ret ENOMEM) [] [] [(aw, n)] [] []
       /\ mo' = with_vmmaps (mkVmMapsFull (vm_reserved h)
                   (maps_subtract (vm_maps h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                   (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
Proof.
  intros addr len mo rsp mo' evs h aw n Hmi [-> H]. subst h aw n. split; [reflexivity|].
  cbv zeta in H.
  change ((MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED =? MAP_ANON_PRIV) && (PROT_NONE =? PROT_RW_Z)) with false in H.
  change ((MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED =? MAP_ANON_PRIV) && (PROT_NONE =? 0)) with false in H.
  change ((MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED =? MAP_ANON_PRIV_FIXED) && (PROT_NONE =? 0)) with true in H.
  cbv iota in H. fold (mmap_len len) in H.
  destruct H as [(e & He & -> & ->) | [(-> & ->) | (e & He & -> & ->)]].
  - split; [apply vm_only_refl|]. left. apply In_mmap_errnos in He. subst e. auto.
  - rewrite kfixna_model_minv by exact Hmi. split; [apply vm_only_with_vmmaps'|]. right; left. auto.
  - rewrite kfixlost_model_minv by exact Hmi. split; [apply vm_only_with_vmmaps'|]. right; right.
    apply In_mmap_errnos in He. subst e. auto.
Qed.

End AC_1.
