(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import RelSpec MmapSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import SysNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_KReach () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "kres"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "Corelib.Init.Datatypes.S"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_brk_next"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Nodes.nstep"; "OSSVerify.KrLib.Lib.Nodes.NBrk"; "OSSVerify.KrLib.Lib.Nodes.eff0"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Logic.or"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.Nodes.NMmap"; "MAPF_Z"; "OSSVerify.KrLib.Lib.Nodes.efferr"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.Nodes.NMprotect"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Sys.SysNodes.mprotect_model"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kmaps (mo : Model) : list (word * word) := vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo).

(* [comment removed for export] *)
Record kres (N : nat) (B : Z) (mo : Model) : Prop := mkKR {
  kr_mat : m_vm_materialized mo = [];
  kr_len : Z.of_nat (length (kmaps mo)) + Z.of_nat N <= 1000;
  kr_size : Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (kmaps mo);
  kr_B : 0 <= B;
  kr_bud : vm_live_bytes (m_vmmaps mo) + B <= vm_limit (m_vmmaps mo)
}.

Lemma kres_mono N B N' B' mo : kres N B mo -> (N' <= N)%nat -> 0 <= B' <= B -> kres N' B' mo.
Proof. intros [M L S B0 U] HN HB. constructor; auto; lia. Qed.

Lemma kres_vm_eq N B mo mo' : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "P,(0.$1.(2.O1.)(2.O2.))P,(0.(3.(4.&40.))(5.O1.)(5.O2.))P,(6.O4.O3.O2.)(6.O4.O3.O1.)")
(* [comment removed for export] *).
Proof. intros E1 E2 [M L S B0 U]. constructor; unfold kmaps in *; rewrite ?E1, ?E2; auto. Qed.

Lemma m_vmmaps_with_vmmaps h mo : m_vmmaps (with_vmmaps h mo) = h.
Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps h mo : m_vm_materialized (with_vmmaps h mo) = m_vm_materialized mo.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps h mo : m_vm_lazy (with_vmmaps h mo) = m_vm_lazy mo.
Proof. reflexivity. Qed.
Lemma mkVmMapsFull_eta h : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "(0.$1.(7.(8.O1.)(9.O1.)(:.O1.)(;.O1.)(<.O1.)(=.O1.)(>.O1.)(?.O1.))O1.)")
(* [comment removed for export] *).
Proof. destruct h; reflexivity. Qed.

(* [comment removed for export] *)
Lemma kres_new_map N B mo mo' (a n : word) noacc : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "P,(6.(10.O7.)O6.O5.)P,(11.(12.&40.O2.)(13.+2.+23.))P,(11.(12.&40.O2.)O6.)P,(0.$1.(2.O4.)(7.(8.(2.O5.))(14.(15.(4.&40.)(4.&40.))(16.(4.&40.)(4.&40.)O3.O2.)(9.(2.O5.)))O1.(;.(2.O5.))(<.(2.O5.))(=.(2.O5.))(>.(2.O5.))(?.(2.O5.))))P,(0.(3.(4.&40.))(5.O4.)(5.O5.))(6.O7.(17.O6.(12.&40.O2.))O4.)")
(* [comment removed for export] *).
Proof.
  intros [M L S B0 U] Hn HnB E Em. constructor; unfold kmaps in *; rewrite ?E, ?Em; cbn [vm_reserved vm_maps vm_limit].
  - exact M.
  - rewrite length_app in *. cbn [length]. lia.
  - apply Forall_app in S as [S1 S2]. apply Forall_app. split; [exact S1|]. constructor; [cbn; lia| exact S2].
  - lia.
  - unfold vm_live_bytes in *. cbn [vm_maps live_bytes]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w_is0_false z : 0 < z < 2 ^ 64 -> w_is0 (Z_to_bv 64 z) = false.
Proof. intros Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. Qed.

Lemma in_sysno_pure no args : in_sysno (pure_input no args) = Z_to_bv 64 no.
Proof. reflexivity. Qed.

Ltac sys_dispatch L :=
  lazymatch goal with
  | |- syscall_spec ?i ?m ?o => apply (proj2 (L i m o ltac:(rewrite in_sysno_pure; apply unsigned_lit; lia))); cbn [in_arg pure_input in_args nth]
  end.

Lemma nstep_mm_iff n i mo eff mo' evs :
  node_input n = Some i ->
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end ->
  nstep n mo eff mo' evs <-> (evs = [] /\ syscall_spec i mo (Monad.Ok eff mo' evs)).
Proof. intros Hi Hn. destruct n; try destruct Hn; cbn [nstep node_input] in *; injection Hi as <-; tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_r_ok_same mo req : brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  unfold brk_r_ok. rewrite bv_eqb_refl.
  destruct (w_is0 req || _); [reflexivity|]. destruct (_ <? _); rewrite ?orb_true_r; [reflexivity|].
  cbn [andb]. unfold brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_zeros_same req b : brk_zeros req b b = [].
Proof. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. Qed.

Lemma brk_grants_same req b : brk_grants req b b = [].
Proof. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. Qed.

Lemma brk_unmaps_same b : brk_unmaps b b = [].
Proof. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _); reflexivity. Qed.

Lemma with_brk_next_same mo req : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "Zb,(4.&40.)(<.(2.O2.))(18.(0.$1.(2.(19.O2.O1.R1.))(2.O2.))(18.(0.(3.(4.&40.))(5.(19.O2.O1.R1.))(5.O2.))(18.(0.(3.(15.(4.&40.)(4.&40.)))(1:.(19.O2.O1.R1.))(1:.O2.))(0.(1;.(4.&40.))(1<.(19.O2.O1.R1.))(1<.O2.)))))")
(* [comment removed for export] *).
Proof.
  cbv zeta. unfold with_brk_next. rewrite brk_unmaps_same. cbn [forget_vm_ranges].
  unfold brk_model_next. rewrite brk_unmaps_same. cbn [maps_subtract_ranges fold_left].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r, brk_grants_same. cbn [app].
  rewrite mkVmMapsFull_eta. repeat split; reflexivity.
Qed.

Lemma kcan_brk_same req mo : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "P,(18.(11.=O2.)(1=.O2.(13.+2.+40.)))Zb,(4.&40.)(<.(2.O1.))(1>.(1?.O2.)O1.(20.R1.)(19.O1.(21.&40.O2.)R1.)(22.$23.))")
(* [comment removed for export] *).
Proof.
  intros Hreq b. eapply (proj2 (nstep_mm_iff (NBrk req) _ mo _ _ _ eq_refl I)). split; [reflexivity|].
  sys_dispatch syscall_spec_214. apply (proj2 (brk_outcome _ _ _ _)).
  exists b. split; [apply brk_r_ok_same|]. subst b. rewrite brk_zeros_same, brk_unmaps_same. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MAPF_Z : Z := 34.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_modeled_rw : mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 MAPF_Z) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_modeled_none : mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 MAPF_Z) (Z_to_bv 64 0) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noaccess_none : mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 MAPF_Z) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_MAPF : mmap_noreserve_b (Z_to_bv 64 MAPF_Z) = false.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma mmap_off0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_anon_MAPF : mmap_anon_b (Z_to_bv 64 MAPF_Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kcan_mmap_fail len prot mo : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "P,(18.(1=.=O3.)(1=.O3.(13.+2.+40.)))P,(24.(0.$25.O2.=)(0.$25.O2.+3.))(1>.(26.=O3.O2.$27.)O1.(28.$29.)O1.(22.$23.))")
(* [comment removed for export] *).
Proof.
  intros Hlen Hprot. eapply (proj2 (nstep_mm_iff (NMmap 0 len prot MAPF_Z) _ mo _ _ _ eq_refl I)). split; [reflexivity|].
  sys_dispatch syscall_spec_222.
  destruct Hprot as [-> | ->].
  - apply (proj2 (mmap_noaccess_outcome _ _ _ _ _ _ _ mo _ (w_is0_false len Hlen) mmap_off0 mmap_anon_MAPF mmap_modeled_none mmap_noaccess_none)).
    left. exists ENOMEM. split; [left; reflexivity| reflexivity].
  - apply (proj2 (mmap_rw_outcome _ _ _ _ _ _ _ mo _ (w_is0_false len Hlen) mmap_off0 mmap_anon_MAPF mmap_modeled_rw)).
    left. exists ENOMEM. split; [left; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma kcan_mmap_ok len prot mo N B :
  0 < len -> mmap_len len <= 2 ^ 35 -> (prot = 0 \/ prot = 3) ->
  m_vm_lazy mo = [] -> kres (S N) B mo -> mmap_len len <= B ->
  alloc_top_min <= alloc_top (m_vmmaps mo) ->    (* [comment removed for export] *)
  exists (a : word) rsp mo',
    nstep (NMmap 0 len prot MAPF_Z) mo rsp mo' []
    /\ rsp = (if prot =? 0 then mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] []
              else mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))])
    /\ 0 < bv_unsigned a /\ bv_unsigned a + mmap_len len <= alloc_top (m_vmmaps mo)
    /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                       (if prot =? 0 then (a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))
    /\ m_vm_materialized mo' = m_vm_materialized mo /\ m_vm_lazy mo' = m_vm_lazy mo /\ m_halted mo' = m_halted mo
    /\ kres N (B - mmap_len len) mo'.
Proof.
  intros Hlen Hlen35 Hprot Hlazy KR HB Htop.
  pose proof (mmap_len_bound len Hlen) as Hml.
  pose proof KR as [M L S B0 U].
  destruct (grant_exists_big (Z_to_bv 64 0) mo (mmap_len len) ltac:(lia) S ltac:(unfold kmaps in L; lia) Htop
              ltac:(pose proof (vm_backing_used_le_live mo Hlazy M); lia)) as [a Hg].
  destruct (grant_ok_unpack _ _ _ _ Hg) as (Gal & Gpos & Gce & Grf & Gbud).
  set (n := Z_to_bv 64 (mmap_len len)).
  set (h' := fun noacc => mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((a, n) :: vm_maps (m_vmmaps mo)) noacc
                 (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))).
  assert (Hn : bv_unsigned n = mmap_len len) by (subst n; apply unsigned_lit; lia).
  assert (Hlenw : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  exists a.
  destruct Hprot as [-> | ->].
  - dexists (mkEffectU a [] [] [(a, n)] [] []), (with_vmmaps (h' ((a, n) :: vm_noaccess (m_vmmaps mo))) mo).
    assert (ST : nstep (NMmap 0 len 0 MAPF_Z) mo (mkEffectU a [] [] [(a, n)] [] []) (with_vmmaps (h' ((a, n) :: vm_noaccess (m_vmmaps mo))) mo) []).
    { eapply (proj2 (nstep_mm_iff (NMmap 0 len 0 MAPF_Z) _ mo _ _ _ eq_refl I)). split; [reflexivity|].
      sys_dispatch syscall_spec_222.
      apply (proj2 (mmap_noaccess_outcome _ _ _ _ _ _ _ mo _ (w_is0_false len ltac:(lia)) mmap_off0 mmap_anon_MAPF mmap_modeled_none mmap_noaccess_none)).
      right. exists a. rewrite Hlenw. fold (mmap_len len). fold n. split; [repeat split; assumption|].
      unfold with_mmap_backing. rewrite mmap_noreserve_MAPF. reflexivity. }
    cbn [Z.eqb]. split; [exact ST|]. split; [reflexivity|]. split; [exact Gpos|]. split; [exact Gce|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite <- Hn. eapply (kres_new_map N B mo _ a n); [exact KR| lia| lia| reflexivity| reflexivity].
  - dexists (mkEffect a [] [(a, n)]), (with_vmmaps (h' (vm_noaccess (m_vmmaps mo))) mo).
    assert (ST : nstep (NMmap 0 len 3 MAPF_Z) mo (mkEffect a [] [(a, n)]) (with_vmmaps (h' (vm_noaccess (m_vmmaps mo))) mo) []).
    { eapply (proj2 (nstep_mm_iff (NMmap 0 len 3 MAPF_Z) _ mo _ _ _ eq_refl I)). split; [reflexivity|].
      sys_dispatch syscall_spec_222.
      apply (proj2 (mmap_rw_outcome _ _ _ _ _ _ _ mo _ (w_is0_false len ltac:(lia)) mmap_off0 mmap_anon_MAPF mmap_modeled_rw)).
      right. exists a. rewrite Hlenw. fold (mmap_len len). fold n. split.
      + repeat split; try assumption. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_MAPF. apply Z.leb_le. exact Gbud.
      + unfold with_mmap_backing. rewrite mmap_noreserve_MAPF. reflexivity. }
    cbn [Z.eqb]. split; [exact ST|]. split; [reflexivity|]. split; [exact Gpos|]. split; [exact Gce|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite <- Hn. eapply (kres_new_map N B mo _ a n); [exact KR| lia| lia| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kcan_mprotect_ok (a : Z) mo N B : ltac2:(CDefT.buildp (gd_tbl_KReach ()) "P,(11.=O4.)P,(0.$25.(2:.O4.+1000.)=)P,(1=.(2;.O4.+1000.)(13.+2.+40.))Zaw,(4.&40.)(21.&40.O4.)Znw,(4.&40.)(21.&40.+1000.)P,(0.$2<.(2=.(:.(2.O3.))R2.R1.)$2>.)P,(0.$2<.(2=.(9.(2.O3.))R3.R2.)$2>.)P,(0.(3.(15.(4.&40.)(4.&40.)))(1:.O3.)(22.(15.(4.&40.)(4.&40.))))P,(6.O2.O1.O3.)(2?.$30.Lmo',$30.(18.(1>.(31.O4.+1000.+3.)O3.(32.(21.&40.=)(22.(15.(4.&40.)(3.(4.&8.))))(14.(15.(4.&40.)(4.&40.))(16.(4.&40.)(4.&40.)R7.R6.)(22.(15.(4.&40.)(4.&40.))))(22.(15.(4.&40.)(4.&40.)))(22.$33.)(22.(15.(4.&40.)$34.)))R1.(22.$23.))(18.(0.$30.R1.(35.R7.R6.O3.))(18.(6.O2.O1.R1.)(18.(0.(3.(15.(4.&40.)(4.&40.)))(1:.R1.)(1:.O3.))(0.(1;.(4.&40.))(1<.R1.)(1<.O3.)))))))")
(* [comment removed for export] *).
Proof.
  intros Ha Hal Hhi aw nw Hna Hma Hlazy KR. pose proof KR as [M L S B0 U].
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = 4096) by (subst nw; apply unsigned_lit; lia).
  exists (mprotect_model aw nw mo).
  split; [| split; [reflexivity| split; [| split; reflexivity]]].
  - eapply (proj2 (nstep_mm_iff (NMprotect a 4096 3) _ mo _ _ _ eq_refl I)). split; [reflexivity|].
    sys_dispatch syscall_spec_226. fold aw nw.
    assert (E4 : Z_to_bv 64 (page_round_up_Z (bv_unsigned nw)) = nw) by (rewrite Un; reflexivity).
    apply (proj2 (mprotect_expose_outcome aw nw (Z_to_bv 64 3) _ mo _ ltac:(vm_compute; reflexivity)
             ltac:(rewrite Ua; unfold page_size; exact Hal) ltac:(subst nw; apply w_is0_false; lia)
             ltac:(rewrite Ua, Un; change (page_round_up_Z 4096) with 4096; unfold two_pow_64; lia)
             ltac:(vm_compute; reflexivity) ltac:(rewrite E4; exact Hna) ltac:(rewrite E4; exact Hma))).
    right. rewrite E4, mprotect_model_next_eq. split; [| reflexivity].
    apply mprotect_budget_ok_intro; [exact Hlazy| exact M| lia].
  - constructor; unfold kmaps, mprotect_model in *; rewrite ?m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_limit]; auto.
Qed.
