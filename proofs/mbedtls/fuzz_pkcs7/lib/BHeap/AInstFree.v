(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AW_FreeK. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ AVm AVst AKinvM AVmScar AInstDepot AVstT.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Ltac2 gd_tbl_AInstFree () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.False"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.hull64"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "ARUN_1.Inst.fCS"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.Inst.fK"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.WFK"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaSlice"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_fagrow"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.faa"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserLimit"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_ugrow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.uaa"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinvM.scar_site"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.SH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.SHADOW_OFFSET"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.BHeap.AVstT.shpb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVstT.shpe"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.madvise_model"; "RocqVerifyHarness.AgentSubmission.BHeap.AVstT.R_secrm"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_rec_sec"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.munmap_model"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.dgrow"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.cb_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hdep"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "ARUN_1.Inst.ztag"; "ARUN_1.Inst.ZT"; "ARUN_1.Inst.ZPA"; "ARUN_1.Inst.ZPRIM"; "ARUN_1.Inst.ZSTK"; "ARUN_1.Inst.ZBAND"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.sec_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.emb_tr"; "ARUN_1.Inst.zfix"].

Section ARUN_1. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L29569726087.12L36118953207.15L37460197393.14L54249950512.14L5865451773.12 L59308586248.6 00000>00R00c01401B01GS1A1l1i1L1r2LLS1A1l1i1L1r2LL2GE2EIS1A1l1i1r1L2LL2LTS1A1l1i1L1r2LL2GES1A1l1i1L1r2LLS1i1L". (* [comment removed for export] *)
#[using="Type"] Lemma swap_remove_perm : forall {A} (l : list A) i x, nth_error l i = Some x -> Permutation (x :: swap_remove i l) l.
Proof.
  intros A l i x Hi. unfold swap_remove.
  assert (L : (i < length l)%nat) by (apply nth_error_Some; congruence).
  assert (NE : l <> []) by (intros ->; cbn in L; lia).
  set (r := removelast l). set (lst := last l x).
  assert (DL : l = r ++ [lst]) by (subst r lst; apply app_removelast_last; exact NE).
  pose proof (f_equal (@length A) DL) as LL. rewrite length_app in LL. cbn [length] in LL.
  assert (EL : nth_error l (length l - 1) = Some lst) by (rewrite DL at 1; rewrite nth_error_app2 by lia; replace (length l - 1 - length r)%nat with 0%nat by lia; reflexivity).
  rewrite EL. destruct (Nat.ltb_spec i (length l - 1)) as [LT|GE].
  - assert (Hi' : nth_error r i = Some x) by (rewrite DL, nth_error_app1 in Hi by lia; exact Hi).
    rewrite Nat.add_1_r. transitivity (r ++ [lst]); [| rewrite <- DL; apply Permutation_refl].
    rewrite <- (firstn_skipn_middle i r Hi') at 3. rewrite <- app_assoc. cbn [app].
    eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append.
  - assert (EI : i = (length l - 1)%nat) by lia. rewrite EI, EL in Hi. injection Hi as E. rewrite app_nil_r.
    rewrite firstn_all2 by lia. transitivity (r ++ [lst]); [| rewrite <- DL; apply Permutation_refl]. rewrite E. apply Permutation_cons_append.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma NoDup_somes_inj : forall {A} (l : list (option A)) i j x,
  List.NoDup (flat_map (fun o => match o with Some a => [a] | None => [] end) l) ->
  nth_error l i = Some (Some x) -> nth_error l j = Some (Some x) -> i = j.
Proof.
  intros A l. induction l as [|o l IH]; intros i j x ND Hi Hj; [destruct i; discriminate|].
  cbn [flat_map] in ND.
  assert (INS : forall k, nth_error l k = Some (Some x) -> In x (flat_map (fun o => match o with Some a => [a] | None => [] end) l)).
  { intros k Hk. apply in_flat_map. exists (Some x). split; [eapply nth_error_In; exact Hk| left; reflexivity]. }
  destruct i as [|i], j as [|j]; cbn [nth_error] in Hi, Hj.
  - reflexivity.
  - exfalso. injection Hi as ->. cbn [app] in ND. inversion ND as [|? ? NI _]; subst. exact (NI (INS j Hj)).
  - exfalso. injection Hj as ->. cbn [app] in ND. inversion ND as [|? ? NI _]; subst. exact (NI (INS i Hi)).
  - f_equal. apply (IH i j x); [| exact Hi| exact Hj]. destruct o; cbn [app] in ND; [inversion ND; assumption| exact ND].
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308762863.700000CS1a1n2N01e2X12X22CL". (* [comment removed for export] *)
#[using="Type"] Lemma map_contains_not_free : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "PR,(0.(1.(2.&40.)(2.&40.)))PM,(0.(1.(2.&40.)(2.&40.)))Pa,(2.&40.)Pn,(2.&40.)P,(3.=(4.&40.R1.))P,(5.$6.(7.R4.R3.R2.)$8.)P,(5.$6.(9.(:.(1.(2.&40.)(2.&40.))R6.R5.)R4.R3.)$8.)$;.")
(* [comment removed for export] *).
Proof.
  intros R M a n N0 MC RF. unfold map_contains in MC. apply existsb_exists in MC. ddestruct MC as (e & Hin & X).
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
  pose proof (region_free_clear _ a n N0 RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CL].
  specialize (CL e Hin). cbn zeta in X1, X2. clear - X1 X2 CL N0. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IMLE : al_img_lo AL = 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.
  Hypothesis GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0.
  Hypothesis GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51846756110.8000004S2AL". (* [comment removed for export] *)
  #[using="IMLE"] Lemma IML : al_img_lo AL <= 0x10000. Proof. rewrite IMLE. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition gaddr (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "(<.(<.(=.=O1.)(3.O1.(>.+2.+2?.)))(<.(?.(=.(10.O1.+1.)+7???7000.)(=.+10007???8000.O1.))(<.(11.(<.(=.(12.(13.VAL,))O1.)(3.O1.(10.(12.(10.(13.VAL,)+7.))+40.))))(11.(<.(=.(12.(14.VAL,))O1.)(3.O1.(10.(12.(10.(14.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Definition fCS (h : ahst) (x : Z) : Prop := vcs AL (vst_of h) x /\ gaddr x.
  Definition fK (h : ahst) (mo : Model) : Prop := HK AL h mo.

  #[using="ALWF IMLE IMH GOT64 GSB64"] Lemma vcs_gaddr : forall h mo x, HK AL h mo -> vcs AL (vst_of h) x -> gaddr x.
  Proof. intros h mo x K Hx. exact (vcs0_range AL ALWF (Z.eq_le_incl _ _ IMLE) IMH GOT64 GSB64 (vst_of h) (HK_vwf AL h mo K) x Hx). Qed.
  #[using="ALWF IMLE IMH GOT64 GSB64"] Lemma fCS_iff : forall h mo x, HK AL h mo -> fCS h x <-> vcs AL (vst_of h) x.
  Proof. intros h mo x K. unfold fCS. split; [intros [A _]; exact A| intros A; split; [exact A| exact (vcs_gaddr h mo x K A)]]. Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26939986706.1500000gS2AL5GOT645GSB641a1n2A02A13BND3A681x2Hx3HG13HS13HG33HS3". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Lemma fcrange : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pa,$16.Pn,$16.P,(17.(18.VAL,(19.R3.))R2.R1.)P,(=.=R3.)P,(=.(10.R4.R3.)(>.+2.+2?.))P,(?.(=.(10.R5.R4.)+7???7000.)(=.+10007???8000.R5.))P,(?.(=.(10.R6.R5.)+10000.)(=.+65?000.R6.))(17.(1:.R8.)R7.R6.)")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Proof.
    intros h a n C A0 A1 BND A68 x Hx. split; [apply C; exact Hx|]. unfold gaddr. pose proof GOT64 as GOT64'. pose proof GSB64 as GSB64'. rewrite IMH, IMLE in *. (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *). clear - Hx A0 A1 BND A68 GOT64 GSB64 HG1 HG3 HS1 HS3. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L29745426632.24L31961702792.2400000=00MS2AL1h1c4MFABS2AL1h1c2AU4MFAB". (* [comment removed for export] *)
  #[using="AL IMLE GOT64 GSB64"] Lemma WFK_bwf : forall h, WFK h -> bwf h.
  Proof.
    (intros h dd_H; ddestruct dd_H as (WL & WR & WS & WD & WB & WBIG & WG & HV)). split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB WBIG)))].
    intros c Hc. pose proof (WR c Hc) as X. cbn zeta in X. ddestruct X as (_ & AU & MUAL & MULIM & MFAL & MFAB & _). repeat split; try assumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma WFK_L : forall h, WFK h -> wf_L (h_L h). Proof. (intros h dd_H; ddestruct dd_H as ((WL & _) & _)). exact WL. Qed.
  #[using="Type"] Lemma WFK_havol : forall h, WFK h -> h_havol h <= AVOL_MAX. Proof. intros h W. unfold WFK in W. decompose [and] W. assumption. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L24113840227.22L34213488210.22L35078968259.26L55345831366.22L59309005527.21L59309021649.24L59579064880.15L63368414506.20L63370277801.25L63374621462.21L68388212000.25L68390599587.20L9840393242.21 00000800A00^00g01a02U02Y02]02e02k03803A03JS2AL1c1HS2AL1c2H0S2AL5GOT645GSB641c1i2Hi3AW11HS2AL1c2R1S2AL3IMH5GOT645GSB643HG13HS13HG33HS33HG21i2Hi2R12R33HS22R4S2AL3IMH5GOT645GSB643HG13HS13HG33HS31c2R12R21H2S12S2S2ALS2ALS2AL3AW1S2AL1cS2AL1c2R13AW1S2AL1c2R1S2AL1c2R1". (* [comment removed for export] *)
  #[using="ALWF ASB IMLE IMH GOT64 GSB64"] Theorem F_csok : forall h, cs_ok AL (fCS h).
  Proof.
    intros h. split; [| split; [| split]].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    - intros c [_ (R1 & R2 & R3 & R4)]. unfold shadow_of. rewrite ASB.
      pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). assert (c / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47 / 8) with 17592186044416 in *.
      split; [lia|]. split; [lia|]. split; [lia|]. intros [_ (S1 & S2 & _)]. lia.
    - intros i Hi. split; intros [_ (R1 & R2 & R3 & R4)]; lia.
    - intros c i [_ (R1 & _)] Hi. dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). rewrite IMH in *.
      unfold shadow_of. rewrite ASB. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). lia.
    - rewrite ASB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Theorem F_kinv : forall h, kinv AL (fCS h) (fK h).
  Proof.
    intros h. split.
    - intros mo [K _]. exact (proj1 K).
    - intros mo [K _]. exact (HKv_top AL (vst_of h) mo K).
    - intros mo acc [K VR] OK.
      destruct (ki_mat (HKv_kinv AL (vst_of h) VR) mo acc K (acc_ok_mono AL _ _ acc (fun x H => proj1 H) OK)) as (mo' & E & K' & MM).
      exists mo'. split; [exact E|]. split; [exact (conj K' VR)| exact MM].
  Qed.
  #[using="Type"] Lemma kview_vst : forall h h', kview_eq h h' -> vst_of h' = vst_of h.
  Proof.
    (intros h h' dd_H; ddestruct dd_H as (EL & ER & ENB & EBL & ESC & EPA & EGH & EEM & _)). apply vst_of_ext; try assumption; intros c; [exact (proj1 (ER c))| exact (proj2 (ER c))].
  Qed.
  #[using="Type"] Theorem F_view_K : forall h h' mo, kview_eq h h' -> fK h mo -> fK h' mo.
  Proof. intros h h' mo V K. unfold fK, HK. rewrite (kview_vst h h' V). exact K. Qed.
  #[using="Type"] Theorem F_view_CS : forall h h' x, kview_eq h h' -> fCS h x -> fCS h' x.
  Proof. intros h h' x V C. unfold fCS. rewrite (kview_vst h h' V). exact C. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2510930669.11000008S2AL1x1R". (* [comment removed for export] *)
  #[using="Type"] Theorem F_noshadow : forall h x, fCS h x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Proof. intros h x [_ (_ & R & _)]. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Theorem F_halted : forall h mo, fK h mo -> m_halted mo = None.
  Proof. intros h mo [K _]. exact (proj1 K). Qed.
  #[using="Type"] Theorem F_apart : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pmo,$1;.Pa,(2.&40.)Pn,(2.&40.)P,(1<.R4.R3.)P,(5.$6.(9.(:.(1.(2.&40.)(2.&40.))(1=.(1>.R4.))(1?.(1>.R4.)))R3.R2.)$8.)P,(=.+10000.(4.&40.R3.))P,(=.(10.(4.&40.R5.)(4.&40.R4.))(20.VhAR,))Px,$16.P,(?.(1:.R9.R1.)(<.(=.(21.VAL,)R1.)(3.R1.(22.VAL,))))(11.(<.(=.(4.&40.R8.)R2.)(3.R2.(10.(4.&40.R8.)(4.&40.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros h mo a n K RF N16 CE x Hx. apply (HK_apart AL h mo a n K RF N16 CE x). destruct Hx as [[Hx _]|Hx]; [left; exact Hx| right; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Ltac wfl W := pose proof (WFK_L _ W) as WL; unfold wf_L in WL;
                let rec go H := lazymatch type of H with _ /\ _ => let H1 := fresh "WL" in let H2 := fresh "WL" in destruct H as [H1 H2]; go H2 | _ => idtac end in go WL.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L50326211852.45L56134313758.45L59742162472.4500000I00X011S3hAR2AL1h4WL224WL244WL29S3hAR2AL1h4WL23S3hAR2AL1h4WL224WL244WL29". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_T : forall h, WFK h -> crange (fCS h) (l_T (h_L h)) 4096.
  Proof. intros h W. wfl W. apply fcrange; [apply crange_T| | | |]; unfold lowhigh, kHighMemBeg in *; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L3963832648.45 L51268740182.45L59742162472.4500000?01m02AS3hAR2AL1h4WL25S3hAR2AL4IMLE5GOT645GSB641h3WL02WL3WL33WL73WL83WL94WL104WL114WL134WL144WL154WL174WL194WL224WL244WL264WL274WL29S3hAR2AL1h4WL244WL29". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_ctx : forall h, WFK h -> crange (fCS h) (l_ctx (h_L h)) (l_ctxlen (h_L h)).
  Proof. intros h W. wfl W. apply fcrange; [apply crange_ctx| | | |]; unfold lowhigh, kHighMemBeg in *; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L50326211852.45L56134313758.45L59742162472.4500000I00X011S3hAR2AL1h4WL194WL244WL29S3hAR2AL1h4WL20S3hAR2AL1h4WL194WL244WL29". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_fs : forall h, WFK h -> crange (fCS h) (l_fs (h_L h)) kFakeBytes.
  Proof. intros h W. wfl W. apply fcrange; [apply (crange_of_tr AL h _ (tr_of_fs h) eq_refl)| | | |]; unfold lowhigh, kHighMemBeg, kFakeBytes in *; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L14332186304.46L54278235689.46L59077622227.4600000A00S00dS3hAR2AL1h2WL3WL3S3hAR2AL1h3WL43WL5S3hAR2AL1h2WL3WL3". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_ri : forall h, WFK h -> crange (fCS h) (ri_base (h_L h)) 4096.
  Proof.
    intros h W. wfl W.
    assert (IN : In (ri_tr (h_L h)) (tr_of h)) by (unfold tr_of; rewrite !in_app_iff; do 4 right; left; left; reflexivity).
    apply fcrange; [apply (crange_of_tr AL h _ IN eq_refl)| | | |]; unfold ri_base, space_end, kSpaceSize, kHighMemBeg in *; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L25020636567.52L26939986706.18L35497640934.5100000B01:01DS3hAR2AL1h2lo2H01HS3hAR2AL5GOT645GSB641h2lo1n2H02H14WL154WL161x2Hx3HG13HS1S3hAR2AL1h". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_stack : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Plo,$16.Pn,$16.P,(23.VhAR,R3.)P,(=.(24.(25.R4.))R3.)P,(=.(10.R4.R3.)(26.(25.R5.)))(17.(1:.R6.)R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros h lo n W H0 H1. wfl W. intros x Hx. split.
    - apply (crange_stack AL h lo n); [| exact H1| exact Hx]. unfold stk64. pose proof (Z.mod_pos_bound (l_stk_lo (h_L h)) 64 ltac:(lia)). lia.
    - unfold gaddr. rewrite IMH in *. unfold kHighMemBeg in *. (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *). clear - Hx H0 H1 GOT64 GSB64 WL15 WL16 WL17 HG1 HG3 HS1 HS3. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma wfL_hull_hi : forall L, wf_L L -> l_b6 L + 0x2000011000 <= ACEIL /\ l_pa L + 0x800000 <= ACEIL.
  Proof. intros L WL. unfold wf_L in WL. decompose [and] WL. split; assumption. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L18854321447.10L41368026125.13L5524754601.10 L5556855671.10 L649842043.27  L65648985371.2700000B00K00c01501E01US3hAR1h1c2Hc2F12F5S2AL1c2HcS3hAR1h1c2Hc5MULIM2F22F8S3hAR1h1c2Hc2F12F5S3hAR2AL1h1c3MU0S3hAR2AL1h1c3MU0". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_user : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pc,$16.P,(23.VhAR,R2.)P,(<.(=.+1.R2.)(=.R2.+1?.))(17.(1:.R4.)(27.(25.R4.)R3.)(28.(29.R4.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros h c W Hc. pose proof (WFK_bwf h W) as B. dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    pose proof (wfL_facts _ (WFK_L h W)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof (wfL_hull_hi _ (WFK_L h W)) as [F8 F9].
    apply fcrange; [apply (crange_user AL h c); [exact Hc| exact MUAL| lia| exact MU0| lia]| | | |]; unfold region_beg, kRegionSize, kUserLimit, kHighMemBeg in *; clear - Hc MU0 MULIM F1 F2 F5 F8; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L15723083765.21L15724635037.22L20764631855.23L2882358902.22 L2882472187.22 L31897157794.23L64523629069.2200000?00L00_00n01;01W024S2AL1h1c2FB1x1jS2AL1h1c2FB1xS2AL1h1c2FB1x2DM2MBS2AL1h1c2FB1x1jS2AL1h1c2FB1xS2AL1h1c1a1n2MF2FB2A11x2Hx1HS2AL1h1c1a1n2FB2A01x2Hx2DM2MB". (* [comment removed for export] *)
  #[using="IMLE GOT64 GSB64"] Lemma crange_fa : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pc,$16.Pa,$16.Pn,$16.P,(<.(=.+1.R3.)(=.R3.+1?.))P,(5.$16.(2:.(2;.(29.R5.R4.))$2<.)=)P,(=.(2=.(25.R6.)R5.)R4.)P,(=.=R4.)P,(=.(10.R6.R5.)(10.(2=.(25.R8.)R7.)(2;.(29.R8.R7.))))(17.(18.VAL,(19.R9.))R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros h c a n Hc MF A0 N0 A1 x Hx. set (FB := fa_beg (h_L h) c) in *. set (j := (x - FB) / kUserMapSize). unfold kUserMapSize in *.
    pose proof (Z.div_mod (x - FB) (2^18) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - FB) (2^18) ltac:(lia)) as MB.
    assert (Hj : 0 <= j < r_mapped_fa (h_reg h c) / 2^18).
    { subst j. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (r_mapped_fa (h_reg h c)) (2^18) ltac:(lia)). lia. }
    apply (vcs_of_tr AL h (funit_tr (h_L h) c j)); [apply tr_of_funit; [exact Hc| exact Hj]| reflexivity|].
    unfold t_hi, funit_tr, kUserMapSize. cbn [t_lo t_len]. fold FB. subst j. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L24240726097.9 L25986690013.9 L31974366641.27L41368026125.13L63637383484.9 L649842043.27  L65648985371.2700000G00Y00n01701I01Y01iS3hAR1h1c2Hc4MFAB2F22F8S3hAR1h1c2Hc2F12F5S3hAR2AL1h1c3MU04MFABS2AL1c2HcS3hAR1h1c2Hc2F12F5S3hAR2AL1h1c3MU0S3hAR2AL1h1c3MU0". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_fa : forall h c, WFK h -> 1 <= c <= 31 -> crange (fCS h) (fa_beg (h_L h) c) (r_mapped_fa (h_reg h c)).
  Proof.
    intros h c W Hc. pose proof (WFK_bwf h W) as B. dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    pose proof (wfL_facts _ (WFK_L h W)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof (wfL_hull_hi _ (WFK_L h W)) as [F8 F9].
    apply fcrange; [apply (crange_fa h c); [exact Hc| exact MFAL| lia| lia| lia]| | | |]; unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kHighMemBeg in *; clear - Hc MFAB F1 F2 F5 F8; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="ALWF IMLE IMH GOT64 GSB64"] Theorem F_cs_node : forall h mo b, fK h mo -> In b (d_nb (h_dep h)) -> crange (fCS h) b (2^20).
  Proof.
    intros h mo b K Hb x Hx. pose proof (crange_of_tr AL h _ (tr_of_node h b Hb) eq_refl x Hx) as C. exact (conj C (vcs_gaddr h mo x K C)).
  Qed.
  #[using="ALWF IMLE IMH GOT64 GSB64"] Theorem F_cs_store : forall h mo b, fK h mo -> In b (d_bl (h_dep h)) -> crange (fCS h) b (2^23).
  Proof.
    intros h mo b K Hb x Hx. pose proof (crange_of_tr AL h _ (tr_of_store h b Hb) eq_refl x Hx) as C. exact (conj C (vcs_gaddr h mo x K C)).
  Qed.
  #[using="ALWF IMLE IMH GOT64 GSB64"] Theorem F_cs_sec : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pmo,$1;.Psh,$2>.P,(1<.R3.R2.)P,(2?.$2>.R2.(30.(31.R4.)))(17.(1:.R5.)(32.R3.)(33.R3.))")
(* [comment removed for export] *).
  Proof.
    intros h mo sh K Hs x Hx. pose proof (crange_of_tr AL h _ (tr_of_sec h sh Hs) eq_refl x Hx) as C. exact (conj C (vcs_gaddr h mo x K C)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926671814.21L18928663569.21L18928777884.21L18932548526.20L19371106965.23L3396781391.22 L8786211341.21 00000?00P00_01001E01d02CS2AL1h3PA02PB1xS2AL1h3PA02PB1x1jS2AL1h3PA02PB1xS2AL1h3PA02PB1x1jS2AL1h3PA02PB1x2DM2MBS2AL1h1a1n3PA03PAL2PB2A11x2Hx1HS2AL1h1a1n3PA02PB2A01x2Hx2DM2MB". (* [comment removed for export] *)
  #[using="IMLE GOT64 GSB64"] Lemma crange_pa : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pa,$16.Pn,$16.P,(=.=(34.R3.))P,(5.$16.(2:.(34.R4.)$35.)=)P,(=.(36.(25.R5.))R4.)P,(=.=R4.)P,(=.(10.R6.R5.)(10.(36.(25.R7.))(34.R7.)))(17.(18.VAL,(19.R8.))R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros h a n PA0 PAL A0 N0 A1 x Hx. set (PB := l_pa (h_L h)) in *. set (j := (x - PB) / kPaSlice). unfold kPaSlice in *.
    pose proof (Z.div_mod (x - PB) 131072 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - PB) 131072 ltac:(lia)) as MB.
    assert (Hj : 0 <= j < h_pa_committed h / 131072).
    { subst j. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)). lia. }
    assert (IN : In (pa_tr (h_L h) j) (tr_of h)).
    { unfold tr_of. rewrite !in_app_iff. do 5 right. left. apply in_map. apply in_zseq. exact Hj. }
    apply (vcs_of_tr AL h (pa_tr (h_L h) j) x IN eq_refl). unfold t_hi, pa_tr, kPaSlice. cbn [t_lo t_len]. fold PB. subst j. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L12229924057.22L43579072885.22L51256402777.5 L59729856807.5 L64133256131.22L6818632143.5  00000:00H00V00d00n01<S3hAR2AL1hS3hAR2AL1h3PABS3hAR1h3PAB2F6S3hAR1h3PAB2F6S3hAR2AL1hS3hAR1h3PAB2F9". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_pa : forall h, WFK h -> crange (fCS h) (l_pa (h_L h)) (h_pa_committed h).
  Proof.
    intros h W. pose proof (WFK_bwf h W) as B. pose proof (bwf_pa h B) as [PAB PAL]. pose proof (wfL_facts _ (WFK_L h W)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    pose proof (wfL_hull_hi _ (WFK_L h W)) as [F8 F9].
    apply fcrange; [apply crange_pa; [lia| exact PAL| lia| lia| lia]| | | |]; unfold kPaHullLen, lowhigh, kHighMemBeg in *; clear - PAB F6 F9; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L26939986706.13L63502493192.1300000Y01BS2AL1a1n2A02A12G12G21x2Hx3HG13HS13HG33HS3S2AL1a1n2A02A12G12G21x2Hx3HG13HS13HG33HS3". (* [comment removed for export] *)
  #[using="IMLE IMH GOT64 GSB64"] Theorem F_cs_img : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pa,$16.Pn,$16.P,(23.VhAR,R3.)P,(=.(21.VAL,)R3.)P,(=.(10.R4.R3.)(22.VAL,))P,(?.(=.(10.R5.R4.)(37.(13.VAL,)+3?.))(=.(10.(13.VAL,)+40.)R5.))P,(?.(=.(10.R6.R5.)(37.(14.VAL,)+3?.))(=.(10.(14.VAL,)+40.)R6.))(17.(1:.R8.)R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros h a n W A0 A1 G1 G2 x Hx. rewrite IMLE, IMH in *. split.
    - unfold vcs, vst_of. cbn [v_stk v_img fst snd]. right. left. (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *). clear - A0 A1 G1 G2 Hx HG1 HG3 HS1 HS3. lia.
    - unfold gaddr. (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *). clear - A0 A1 G1 G2 Hx HG1 HG3 HS1 HS3. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma R_fgrow_fagrow : forall h c, R_fgrow h c (h_fagrow h c).
  Proof.
    intros h c. unfold R_fgrow, h_fagrow, set_reg. cbn. unfold fupd. rewrite Z.eqb_refl. cbn.
    repeat split; try reflexivity; intros c'; destruct (Z.eqb_spec c' c) as [->|NE]; cbn; try reflexivity. intros X; exfalso; exact (X eq_refl).
  Qed.
  #[using="Type"] Lemma R_ugrow_ugrow : forall h c, R_ugrow h c (h_ugrow h c).
  Proof.
    intros h c. unfold R_ugrow, h_ugrow, set_reg. cbn. unfold fupd. rewrite Z.eqb_refl. cbn.
    split; [reflexivity|]. split; [intros c' NE; destruct (Z.eqb_spec c' c) as [->|]; [exfalso; exact (NE eq_refl)| reflexivity]|].
    split; [reflexivity|]. split; [intros c'; destruct (Z.eqb_spec c' c) as [->|]; reflexivity|]. repeat split; reflexivity.
  Qed.

  #[using="ASB IMLE IMH GOT64 GSB64"] Theorem F_fa_all : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pc,$16.Pmo,$1;.P,(23.VhAR,R3.)P,(<.(=.+1.R3.)(=.R3.+1?.))P,(=.(10.(2;.(29.R5.R4.))$38.)$39.)P,(1<.R6.R4.)(<.(1<.(3:.R7.R6.)(3;.+32.(3<.R7.R6.)(>.+2.+12.)R5.))(<.(5.$6.(7.(1?.(1>.R5.))(3=.&40.(3<.R7.R6.))(3=.&40.(>.+2.+12.)))$8.)(<.(5.$6.(9.(1=.(1>.R5.))(3=.&40.(3<.R7.R6.))(3=.&40.(>.+2.+12.)))$8.)(3>.+32.(3<.R7.R6.)(>.+2.+12.)R5.))))")
(* [comment removed for export] *).
  Proof.
    intros h c mo W Hc ROOM K.
    exact (HK_fgrow AL ASB IMH h mo c (h_fagrow h c) K (WFK_bwf h W) (WFK_havol h W) Hc ROOM (R_fgrow_fagrow h c)).
  Qed.
  #[using="ASB IMLE IMH GOT64 GSB64"] Theorem F_u_all : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pc,$16.Pmo,$1;.P,(23.VhAR,R3.)P,(<.(=.+1.R3.)(=.R3.+1?.))P,(=.(10.(28.(29.R5.R4.))$2<.)$3?.)P,(1<.R6.R4.)(<.(1<.(40.R7.R6.)(3;.+32.(41.R7.R6.)(>.+2.+12.)R5.))(<.(5.$6.(7.(1?.(1>.R5.))(3=.&40.(41.R7.R6.))(3=.&40.(>.+2.+12.)))$8.)(<.(5.$6.(9.(1=.(1>.R5.))(3=.&40.(41.R7.R6.))(3=.&40.(>.+2.+12.)))$8.)(3>.+32.(41.R7.R6.)(>.+2.+12.)R5.))))")
(* [comment removed for export] *).
  Proof.
    intros h c mo W Hc ROOM K.
    exact (HK_ugrow AL ASB IMH h mo c (h_ugrow h c) K (WFK_bwf h W) (WFK_havol h W) Hc ROOM (R_ugrow_ugrow h c)).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L13548183227.6 L23500749772.7 L31961702792.3 L41368026125.14L51854933546.27L66438843739.0 00000C00[00e00n01:01;S1h1c2Hc4MFAB2F12F5S1h1c2Hc4ROOM4MFAB2F12F2S1h1c4MFABS2AL1c2HcS2AL1h1c3MU0S". (* [comment removed for export] *)
  #[using="ASB IMLE IMH GOT64 GSB64"] Theorem F_fa_scar : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pc,$16.P,(23.VhAR,R2.)P,(<.(=.+1.R2.)(=.R2.+1?.))P,(=.(10.(2;.(29.R4.R3.))$38.)$39.)(42.VhAR,VAL,(1:.R5.)(1<.R5.)(3<.R5.R4.)(>.+2.+12.))")
(* [comment removed for export] *).
  Proof.
    intros h c W Hc ROOM. pose proof (WFK_bwf h W) as B. dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    pose proof (wfL_facts _ (WFK_L h W)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    set (P := vranges_ok AL (vst_of h) /\ forall t, In t (v_tr (vst_of h)) -> faa h c + 2^18 <= t_lo t \/ t_hi t <= faa h c).
    eapply scar_site_iff with (K := fun mo => P /\ HKv AL (vst_of h) mo).
    2:{ intros mo. subst P. unfold fK, HK. split; [intros [[VR _] K]; exact (conj K VR)| intros [K VR]; split; [split; [exact VR|]| exact K]].
        intros t Ht. exact (funit_new_apart AL h mo c t (conj K VR) (WFK_L h W) (bwf_breg h B) (proj1 (bwf_pa h B)) Hc ROOM Ht). }
    eapply scar_site_mono; [| intros x [Hx _]; exact Hx].
    apply (HKv_scar_site_guard AL ASB ltac:(rewrite IMH; lia) P (vst_of h) (faa h c) (2^18)).
    - intros [VR _]. exact VR.
    - intros _. cbn [vst_of v_unit]. unfold faa. apply (funit_unit (h_L h) c _ (WFK_L h W) Hc); [clear - MFAB; lia| exact MFAL| exact ROOM].
    - unfold faa, fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kHighMemBeg in *. clear - F1 F5 Hc MFAB. lia.
    - right. unfold faa, fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kHighMemBeg in *. clear - F1 F5 Hc MFAB. lia.
    - unfold JW. clear. lia.
    - intros [_ APT]. exact APT.
    - exists (l_b6 (h_L h), kPrimHullLen). split; [cbn [vst_of v_cover]; unfold cover_of, hulls_of; apply in_app_iff; left; left; reflexivity|].
      cbn [fst snd]. unfold faa, fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kPrimHullLen in *. clear - F1 F2 Hc MFAB ROOM. lia.
    - exists (l_b6 (h_L h), kPrimHullLen). split; [cbn [vst_of v_hulls]; unfold hulls_of; left; reflexivity|].
      cbn [fst snd]. unfold faa, fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kPrimHullLen in *. clear - F1 F2 Hc MFAB ROOM. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L19664136986.3 L23500749772.7 L41368026125.14L51854933546.27L5352207925.6  L66438843739.0 00000:00Q00Z00f018019S1h1c4ROOMS1h1c2Hc4ROOM3MU02F12F2S2AL1c2HcS2AL1h1c3MU0S1h1c2Hc3MU02F12F5S". (* [comment removed for export] *)
  #[using="ASB IMLE IMH GOT64 GSB64"] Theorem F_u_scar : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pc,$16.P,(23.VhAR,R2.)P,(<.(=.+1.R2.)(=.R2.+1?.))P,(=.(10.(28.(29.R4.R3.))$2<.)$3?.)(42.VhAR,VAL,(1:.R5.)(1<.R5.)(41.R5.R4.)(>.+2.+12.))")
(* [comment removed for export] *).
  Proof.
    intros h c W Hc ROOM. pose proof (WFK_bwf h W) as B. dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    pose proof (wfL_facts _ (WFK_L h W)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    set (P := vranges_ok AL (vst_of h) /\ forall t, In t (v_tr (vst_of h)) -> uaa h c + 2^18 <= t_lo t \/ t_hi t <= uaa h c).
    eapply scar_site_iff with (K := fun mo => P /\ HKv AL (vst_of h) mo).
    2:{ intros mo. subst P. unfold fK, HK. split; [intros [[VR _] K]; exact (conj K VR)| intros [K VR]; split; [split; [exact VR|]| exact K]].
        intros t Ht. exact (uunit_new_apart AL h mo c t (conj K VR) (WFK_L h W) (bwf_breg h B) (proj1 (bwf_pa h B)) Hc ROOM Ht). }
    eapply scar_site_mono; [| intros x [Hx _]; exact Hx].
    apply (HKv_scar_site_guard AL ASB ltac:(rewrite IMH; lia) P (vst_of h) (uaa h c) (2^18)).
    - intros [VR _]. exact VR.
    - intros _. cbn [vst_of v_unit]. unfold uaa. apply (uunit_unit (h_L h) c _ (WFK_L h W) Hc MU0 MUAL). unfold kUserMapSize, kUserLimit, kRegionSize in *. clear - ROOM. lia.
    - unfold uaa, region_beg, kRegionSize, kHighMemBeg in *. clear - F1 F5 Hc MU0. lia.
    - right. unfold uaa, region_beg, kRegionSize, kHighMemBeg in *. clear - F1 F5 Hc MU0. lia.
    - unfold JW. clear. lia.
    - intros [_ APT]. exact APT.
    - exists (l_b6 (h_L h), kPrimHullLen). split; [cbn [vst_of v_cover]; unfold cover_of, hulls_of; apply in_app_iff; left; left; reflexivity|].
      cbn [fst snd]. unfold uaa, region_beg, kRegionSize, kUserMapSize, kUserLimit, kPrimHullLen in *. clear - F1 F2 Hc MU0 ROOM. lia.
    - exists (l_b6 (h_L h), kPrimHullLen). split; [cbn [vst_of v_hulls]; unfold hulls_of; left; reflexivity|].
      cbn [fst snd]. unfold uaa, region_beg, kRegionSize, kUserMapSize, kUserLimit, kPrimHullLen in *. clear - F1 F2 Hc MU0 ROOM. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L49158800547.2L49158801317.2000001007FS1k2W0". (* [comment removed for export] *)
  #[using="Type"] Lemma sec_facts : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pmo,$1;.Pk,$43.Pi,$44.P,(1<.R4.R3.)P,(5.(45.$2>.)(46.$2>.(30.(31.R5.))R2.)(47.$2>.(48.(49.R3.)(4:.R3.)(4;.(4<.R3.)))))(<.(2?.$2>.(48.(49.R4.)(4:.R4.)(4;.(4<.R4.)))(30.(31.R6.)))(<.(=.=(49.R4.))(<.(3.=(4:.R4.))(<.(=.(10.(49.R4.)(4:.R4.))(20.VhAR,))(<.(5.$16.(2:.(4:.R4.)+1000.)=)(?.(=.(10.(49.R4.)(4:.R4.))(37.$4=.+1000.))(=.$4>.(49.R4.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h mo k i K NTH. pose proof (nth_error_In _ _ NTH) as IN. split; [exact IN|].
    pose proof (tr_wf AL h mo _ K (tr_of_sec h _ IN)) as (W0 & W1 & W2 & W3 & W4 & W5 & W6). specialize (W6 eq_refl).
    unfold sec_tr, t_hi in *. cbn [t_lo t_len s_map_beg s_map_size] in *. unfold SHADOW_OFFSET, kHighMemBeg. aceilb. 
    repeat split; try assumption; try (clear - W6; lia); try (clear - W0; lia).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L16676088553.3L22370497053.200000:00BS3hAR1k2BES1k4BAND". (* [comment removed for export] *)
  #[using="Type"] Theorem F_madv_all : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pk,$43.Pi,$44.Pmo,$1;.P,(23.VhAR,R4.)P,(5.(45.$2>.)(46.$2>.(30.(31.R5.))R3.)(47.$2>.(48.(49.R4.)(4:.R4.)(4;.(4<.R4.)))))P,(3.(4?.(49.R5.))(50.(49.R5.)(4:.R5.)))P,(1<.R7.R4.)ZPB,$16.(4?.(49.R7.))ZnZ,$16.(37.(50.(49.R8.)(4:.R8.))R1.)(<.(5.$6.(51.(1>.R7.)(3=.&40.R2.)(3=.&40.R1.))$8.)(1<.R:.(52.R2.R1.R7.)))")
(* [comment removed for export] *).
  Proof.
    intros h k i mo W NTH NE K. dpose (sec_facts h mo k i K NTH) as (IN & B0 & S0 & BE & SM & BAND).
    exact (HK_madvise AL h mo (ck_map_beg k) (ck_map_size k) K B0 S0 ltac:(clear - BE; lia) ltac:(unfold SHADOW_OFFSET in BAND; clear - BAND; lia) NE).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma R_secrm_rec : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pk,$43.Pi,$44.P,(5.(45.$2>.)(46.$2>.(30.(31.R3.))R1.)(47.$2>.(48.(49.R2.)(4:.R2.)(4;.(4<.R2.)))))(53.R4.(48.(49.R3.)(4:.R3.)(4;.(4<.R3.)))(54.R4.R3.R2.))")
(* [comment removed for export] *).
  Proof.
    intros h k i NTH. unfold R_secrm, h_rec_sec, set_acct, set_sec, set_chunks. cbn.
    repeat split; try reflexivity. apply swap_remove_perm. exact NTH.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18926555467.22L18939236800.21L24525729024.2 L66111114473.2 00000:00D00J00PS3hAR2AL1kS3hAR2AL1kS1k2DMS1k2DM". (* [comment removed for export] *)
  #[using="ASB"] Theorem F_unmap_all : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pk,$43.Pi,$44.Pmo,$1;.P,(23.VhAR,R4.)P,(5.(45.$2>.)(46.$2>.(30.(31.R5.))R3.)(47.$2>.(48.(49.R4.)(4:.R4.)(4;.(4<.R4.)))))P,(1<.R6.R3.)(<.(5.$6.(55.(1?.(1>.R4.))(3=.&40.(49.R6.))(3=.&40.(56.(4:.R6.))))$8.)(1<.(54.R7.R6.R5.)(57.(49.R6.)(56.(4:.R6.))R4.)))")
(* [comment removed for export] *).
  Proof.
    intros h k i mo W NTH K. dpose (sec_facts h mo k i K NTH) as (IN & B0 & S0 & BE & SM & BAND).
    assert (PR : page_round_up_Z (ck_map_size k) = ck_map_size k).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod (ck_map_size k) 4096 ltac:(lia)) as DM. rewrite SM in DM.
      replace (ck_map_size k + 4096 - 1) with (4095 + (ck_map_size k / 4096) * 4096) by (clear - DM; lia). rewrite Z.div_add by lia. change (4095 / 4096) with 0. clear - DM; lia. }
    rewrite PR. destruct (HK_secrm AL ASB h mo _ (h_rec_sec h k i) K IN (R_secrm_rec h k i NTH)) as [K' MH]. exact (conj MH K').
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma hdep_same : forall h, vst_of (hdep h (d_nb (h_dep h)) (d_bl (h_dep h))) = vst_of h.
  Proof. intros h. apply vst_of_ext; reflexivity. Qed.
  #[using="Type"] Lemma hdep_node : forall h x, dgrow h [x] [] (hdep h (d_nb (h_dep h) ++ [x]) (d_bl (h_dep h))).
  Proof. intros h x. unfold dgrow, hdep, set_dep. cbn. repeat split; try reflexivity. rewrite app_nil_r. reflexivity. Qed.
  #[using="Type"] Lemma hdep_grow : forall h nb bl sn sb, dgrow (hdep h nb bl) sn sb (hdep h (nb ++ sn) (bl ++ sb)).
  Proof. intros. unfold dgrow, hdep, set_dep. cbn. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L26256253677.14L41777011757.1400000<00BS2AL1h2h12EBS2AL1h". (* [comment removed for export] *)
  #[using="AL IMLE GOT64 GSB64"] Lemma node_numbers : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Px,$16.Ph1,$15.P,(58.R3.(59.$16.R2.(5:.$16.))(5:.$16.)R1.)(<.(5.$16.(5;.(19.R2.))(10.(5;.(19.R4.))(>.+2.+14.)))(<.(5.$16.(5<.(19.R2.))(10.(5<.(19.R4.))(10.(5=.(>.+2.+14.)+8000.)+3.)))(<.(5.$16.(5>.(>.+2.+14.)R2.)(10.(5>.(>.+2.+14.)R4.)+3.))(5.$16.(5>.(>.+2.+17.)R2.)(10.(5>.(>.+2.+17.)R4.)+2.)))))")
(* [comment removed for export] *).
  Proof.
    intros h x h1 DG. pose proof (vst_of_grow h h1 [x] [] DG) as P. cbn [fold_right] in P.
    dpose P as (_ & _ & _ & _ & _ & _ & EB & _). cbn [v_eb v_add_eager] in EB.
    split; [unfold vst_of in EB |- *; cbn [v_eb] in EB |- *; lia|].
    split; [rewrite (vnb_perm _ _ P), vnb_add_eager; reflexivity|].
    rewrite !(cb_of_grow _ h [x] [] h1 DG). cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L33099671509.2 L38106990475.3 L48103380298.2 L50308331596.1800000700B00H00RS1a3BNDS3hAR1a3ACES1a2A0S3hAR2AL1a". (* [comment removed for export] *)
  #[using="ASB IMLE IMH GOT64 GSB64"] Theorem F_node : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pnb,(0.$16.)Pbl,(0.$16.)Pmo,$1;.Pa,(2.&40.)P,(23.VhAR,R5.)P,(<.(5.(0.$16.)R5.(5?.(60.R6.)))(5.(0.$16.)R4.(61.(60.R6.))))P,(1<.(62.R7.R6.R5.)R4.)P,(5.$16.(2:.(4.&40.R4.)+1000.)=)P,(3.=(4.&40.R5.))P,(=.(10.(4.&40.R6.)(>.+2.+14.))(20.VhAR,))P,(5.$6.(9.(:.(1.(2.&40.)(2.&40.))(1=.(1>.R8.))(1?.(1>.R8.)))R7.(3=.&40.(>.+2.+14.)))$8.)(<.(1<.(62.R<.(:.$16.R;.(59.$16.(4.&40.R8.)(5:.$16.)))R:.)(63.+22.R8.(>.+2.+14.)R9.))(17.(1:.(62.R<.(:.$16.R;.(59.$16.(4.&40.R8.)(5:.$16.)))R:.))(4.&40.R8.)(>.+2.+14.)))")
(* [comment removed for export] *).
  Proof.
    intros h nb bl mo a W [-> ->] K AAL A0 ACE RF. pose proof (WFK_bwf h W) as B.
    assert (SL : v_eb (vst_of (hdep h (d_nb (h_dep h)) (d_bl (h_dep h)))) + 4096 * vnb (vst_of (hdep h (d_nb (h_dep h)) (d_bl (h_dep h)))) + CN <= VLIMIT).
    { rewrite hdep_same. apply vst_slack; [exact B| exact (WFK_havol h W)| unfold CN, npg_shadow, kDepotBlockBytes; cbn; lia]. }
    destruct (HK_node AL ASB IML IMH _ mo a _ K AAL A0 ACE RF SL (hdep_grow h _ _ [bv_unsigned a] [])) as (K' & C' & A68 & BND).
    rewrite app_nil_r in K', C'. split; [exact K'|].
    apply fcrange; [exact C'| clear - A0; lia| clear - ACE; lia| clear - BND; lia| right; exact A68].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L19576226618.20L33099671509.2 L48103380298.2 L66300325492.2 L9930400379.3  00000:00A00G00N00YS3hAR2AL1aS1a3BNDS1a2A0S1h3SL0S3hAR1a3ACE". (* [comment removed for export] *)
  #[using="ASB IMLE IMH GOT64 GSB64"] Theorem F_store : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pnb,(0.$16.)Pbl,(0.$16.)Pmo,$1;.Pa,(2.&40.)P,(23.VhAR,R5.)P,(<.(5.(0.$16.)R4.(61.(60.R6.)))(?.(5.(0.$16.)R5.(5?.(60.R6.)))(64.$16.Lx,$16.(5.(0.$16.)R6.(:.$16.(5?.(60.R7.))(59.$16.R1.(5:.$16.)))))))P,(1<.(62.R7.R6.R5.)R4.)P,(5.$16.(2:.(4.&40.R4.)+1000.)=)P,(3.=(4.&40.R5.))P,(=.(10.(4.&40.R6.)(>.+2.+17.))(20.VhAR,))P,(5.$6.(9.(:.(1.(2.&40.)(2.&40.))(1=.(1>.R8.))(1?.(1>.R8.)))R7.(3=.&40.(>.+2.+17.)))$8.)(<.(1<.(62.R<.R;.(:.$16.R:.(59.$16.(4.&40.R8.)(5:.$16.))))(63.+4022.R8.(>.+2.+17.)R9.))(17.(1:.(62.R<.R;.(:.$16.R:.(59.$16.(4.&40.R8.)(5:.$16.)))))(4.&40.R8.)(>.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    intros h nb bl mo a W [-> NB] K AAL A0 ACE RF. pose proof (WFK_bwf h W) as B.
    assert (SL : v_eb (vst_of (hdep h nb (d_bl (h_dep h)))) + 4096 * vnb (vst_of (hdep h nb (d_bl (h_dep h)))) + CSB <= VLIMIT).
    { pose proof (vst_slack h (CN + CSB) B (WFK_havol h W) ltac:(unfold CN, CSB, npg_shadow, kDepotBlockBytes, kStoreBlockBytes; cbn; lia)) as SL0.
      destruct NB as [-> |(x & ->)]; [rewrite hdep_same; clear - SL0; unfold CN, npg_shadow, kDepotBlockBytes in *; lia|].
      destruct (node_numbers h x _ (hdep_node h x)) as (E1 & E2 & _). rewrite E1, E2. unfold CN, npg_shadow, kDepotBlockBytes in SL0. clear - SL0. lia. }
    destruct (HK_store AL ASB IML IMH _ mo a _ K AAL A0 ACE RF SL (hdep_grow h _ _ [] [bv_unsigned a])) as (K' & C' & A68 & BND).
    rewrite app_nil_r in K', C'. split; [exact K'|].
    apply fcrange; [exact C'| clear - A0; lia| clear - ACE; lia| clear - BND; lia| right; exact A68].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L35926918365.13L58309232050.1300000600:S2AL1hS2AL". (* [comment removed for export] *)
  #[using="IMLE GOT64 GSB64"] Theorem F_room_n : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pnb,(0.$16.)Pbl,(0.$16.)Pmo,$1;.P,(23.VhAR,R4.)P,(<.(5.(0.$16.)R4.(5?.(60.R5.)))(5.(0.$16.)R3.(61.(60.R5.))))P,(1<.(62.R6.R5.R4.)R3.)(64.(2.&40.)La,(2.&40.)(65.VhAR,+22.(>.+2.+14.)R5.R1.))")
(* [comment removed for export] *).
  Proof.
    intros h nb bl mo W [-> ->] K. pose proof (WFK_bwf h W) as B.
    apply (HK_room20 AL h _ mo B (WFK_havol h W) K).
    - unfold cb_of, cover_of, hdep, set_dep, emb_tr. cbn. lia.
    - rewrite hdep_same. apply vst_slack; [exact B| exact (WFK_havol h W)| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L17072457027.15L35926918365.1300000600<S2AL1hS2AL1h". (* [comment removed for export] *)
  #[using="IMLE GOT64 GSB64"] Theorem F_room_s : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pnb,(0.$16.)Pbl,(0.$16.)Pmo,$1;.P,(23.VhAR,R4.)P,(<.(5.(0.$16.)R3.(61.(60.R5.)))(?.(5.(0.$16.)R4.(5?.(60.R5.)))(64.$16.Lx,$16.(5.(0.$16.)R5.(:.$16.(5?.(60.R6.))(59.$16.R1.(5:.$16.)))))))P,(1<.(62.R6.R5.R4.)R3.)(64.(2.&40.)La,(2.&40.)(65.VhAR,+4022.(>.+2.+17.)R5.R1.))")
(* [comment removed for export] *).
  Proof.
    intros h nb bl mo W [-> NB] K. pose proof (WFK_bwf h W) as B.
    apply (HK_room23 AL h _ mo B (WFK_havol h W) K).
    destruct NB as [-> |(x & ->)].
    - unfold cb_of, cover_of, hdep, set_dep, emb_tr. cbn. lia.
    - destruct (node_numbers h x _ (hdep_node h x)) as (_ & _ & _ & E). rewrite E. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L11949540184.2300000GS2AL1h2h'2c'2MU1j2Hj2MF". (* [comment removed for export] *)
  #[using="AL IMLE GOT64 GSB64"] Lemma tr_of_mono : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Ph',$15.Pt,$66.P,(5.$67.(25.R2.)(25.R3.))P,(5.(0.$16.)(5?.(60.R3.))(5?.(60.R4.)))P,(5.(0.$16.)(61.(60.R4.))(61.(60.R5.)))P,(5.(0.$2>.)(30.(31.R5.))(30.(31.R6.)))P,(5.$16.(34.R6.)(34.R7.))P,(5.$16.(68.(69.R7.))(68.(69.R8.)))P,Pc,$16.P,(<.(=.+1.R1.)(=.R1.+1?.))(=.(5=.(28.(29.R;.R2.))$2<.)(5=.(28.(29.R:.R2.))$2<.))P,Pc,$16.P,(<.(=.+1.R1.)(=.R1.+1?.))(=.(5=.(2;.(29.R<.R2.))$2<.)(5=.(2;.(29.R;.R2.))$2<.))P,(2?.$66.R9.(6:.R;.))(2?.$66.R:.(6:.R;.))")
(* [comment removed for export] *).
  Proof.
    intros h h' t EL ENB EBL ESC EPA EEM MU MF Ht.
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c' & j & Hc' & Hj & ->)|[(c' & j & Hc' & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]].
    - apply tr_of_node. rewrite ENB. exact Hb.
    - apply tr_of_store. rewrite EBL. exact Hb.
    - apply tr_of_sec. rewrite ESC. exact Hsh.
    - rewrite <- EL. apply tr_of_uunit; [exact Hc'|]. specialize (MU c' Hc'). lia.
    - rewrite <- EL. apply tr_of_funit; [exact Hc'|]. specialize (MF c' Hc'). lia.
    - rewrite <- EL. unfold tr_of. rewrite !in_app_iff. do 4 right. left. left. reflexivity.
    - rewrite <- EL. unfold tr_of. rewrite !in_app_iff. do 5 right. left. apply in_map. apply in_zseq. rewrite EPA. exact Hj.
    - unfold tr_of. rewrite !in_app_iff. do 6 right. rewrite EL, (emb_tr_ext h h' EEM). apply in_app_iff in HF. exact HF.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma vcs_mono : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Ph',$15.Px,$16.P,(5.$67.(25.R2.)(25.R3.))P,Pt,$66.P,(2?.$66.R1.(6:.R5.))(2?.$66.R2.(6:.R5.))P,(18.VAL,(19.R5.)R3.)(18.VAL,(19.R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros h h' x EL TR Hx. unfold vcs, vst_of in *. cbn [v_stk v_img v_tr fst snd] in *. rewrite EL.
    destruct Hx as [A|[A|(t & Ht & TC & R)]]; [left; exact A| right; left; exact A| right; right; exists t; auto].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2882427805.11L7955182579.1100000400?S2ALS2AL1a1d2Hd". (* [comment removed for export] *)
  #[using="AL"] Lemma div_mono_add : forall a d, 0 <= d -> a / kUserMapSize <= (a + d) / kUserMapSize.
  Proof. intros a d Hd. apply Z.div_le_mono; unfold kUserMapSize; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2879476621.13 L56472808140.13L56472905686.1500000400<00ES2ALS2AL1h1cS2AL1h2c'". (* [comment removed for export] *)
  #[using="IMLE GOT64 GSB64"] Theorem F_cs_mono_fa : forall h c x, fCS h x -> fCS (h_fagrow h c) x.
  Proof.
    intros h c x [V G]. split; [| exact G]. revert V. apply vcs_mono; [reflexivity|]. intros t. apply tr_of_mono; try reflexivity.
    - intros c' _. unfold h_fagrow, set_reg. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|]; cbn; lia.
    - intros c' _. unfold h_fagrow, set_reg. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|]; cbn; [apply div_mono_add; unfold kFreeArrayMapSize; lia| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2879476621.13 L56472808140.13L56472905686.1500000400<00ES2ALS2AL1h1cS2AL1h2c'". (* [comment removed for export] *)
  #[using="IMLE GOT64 GSB64"] Theorem F_cs_mono_u : forall h c x, fCS h x -> fCS (h_ugrow h c) x.
  Proof.
    intros h c x [V G]. split; [| exact G]. revert V. apply vcs_mono; [reflexivity|]. intros t. apply tr_of_mono; try reflexivity.
    - intros c' _. unfold h_ugrow, set_reg. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|]; cbn; [apply div_mono_add; unfold kUserMapSize; lia| lia].
    - intros c' _. unfold h_ugrow, set_reg. cbn. unfold fupd. destruct (Z.eqb_spec c' c) as [->|]; cbn; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Theorem F_cs_mono_dep : forall h nb bl sn sb x, fCS (hdep h nb bl) x -> fCS (hdep h (nb ++ sn) (bl ++ sb)) x.
  Proof. intros h nb bl sn sb x [V G]. exact (conj (vcs_grow AL _ _ sn sb x (hdep_grow h nb bl sn sb) V) G). Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma vcs_transfer : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Ph',$15.Px,$16.P,(5.$67.(25.R2.)(25.R3.))P,Pt,$66.P,(2?.$66.R1.(6:.R5.))P,(5.$6.(6;.R2.)$8.)P,(<.(=.(6<.R3.)R5.)(3.R5.(6=.R3.)))(2?.$66.R4.(6:.R7.))P,(18.VAL,(19.R5.)R3.)(18.VAL,(19.R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros h h' x EL TR Hx. unfold vcs, vst_of in *. cbn [v_stk v_img v_tr fst snd] in *. rewrite EL.
    destruct Hx as [A|[A|(t & Ht & TC & R)]]; [left; exact A| right; left; exact A| right; right; exists t; auto].
  Qed.
  #[using="Type"] Theorem F_cs_rec_sec : ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "Ph,$15.Pk,$43.Pi,$44.Px,$16.P,(5.(45.$2>.)(46.$2>.(30.(31.R4.))R2.)(47.$2>.(48.(49.R3.)(4:.R3.)(4;.(4<.R3.)))))P,(1:.R5.R2.)P,(11.(<.(=.(49.R5.)R3.)(3.R3.(10.(49.R5.)(4:.R5.)))))(1:.(54.R7.R6.R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros h k i x NTH [V G] NH. split; [| exact G]. pose proof (swap_remove_perm _ _ _ NTH) as P.
    revert V. apply vcs_transfer; [reflexivity|]. intros t Ht TC R.
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c' & j & Hc' & Hj & ->)|[(c' & j & Hc' & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]].
    - apply tr_of_node. exact Hb.
    - apply tr_of_store. exact Hb.
    - assert (IN : In sh (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k)) :: swap_remove i (s_chunks (h_sec h)))) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hsh]).
      destruct IN as [<-|IN]; [| apply tr_of_sec; exact IN].
      exfalso. apply NH. unfold sec_tr, t_hi in R. cbn [t_lo t_len s_map_beg s_map_size] in R. exact R.
    - exact (tr_of_uunit (h_rec_sec h k i) c' j Hc' Hj).
    - exact (tr_of_funit (h_rec_sec h k i) c' j Hc' Hj).
    - unfold tr_of. rewrite !in_app_iff. do 4 right. left. left. reflexivity.
    - unfold tr_of. rewrite !in_app_iff. do 5 right. left. apply in_map. apply in_zseq. exact Hj.
    - unfold tr_of. rewrite !in_app_iff. do 6 right. apply in_app_iff in HF. exact HF.
  Qed.

  (* [comment removed for export] *)
  Inductive ztag := ZT (t : trange) | ZPA | ZPRIM | ZSTK | ZBAND.
  Definition zval (L : alayout) (g : ztag) : Z * Z :=
    match g with
    | ZT t => (t_lo t, t_len t) | ZPA => (l_pa L, 0x800000) | ZPRIM => (l_b6 L, 0x2000011000)
    | ZSTK => (l_stk_lo L, l_stk_hi L - l_stk_lo L) | ZBAND => (0x7fff7000, 0x10007fff8000 - 0x7fff7000)
    end.
  Definition zfix (L : alayout) : list trange := ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "(59.$66.(6>.(6?.O1.)+1000.$70.$8.$8.)(59.$66.(6>.(71.O1.)(72.O1.)$70.$8.$8.)(59.$66.(6>.(73.O1.)$74.$70.$8.$8.)(59.$66.(6>.(75.O1.)+1000.$70.$8.$8.)(5:.$66.)))))")
(* [comment removed for export] *).
  Definition ztags (h : ahst) : list ztag := ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "ZL,$67.(25.O1.)(:.$76.(59.$76.(77.(6>.(6?.R1.)+1000.$70.$8.$8.))(59.$76.(77.(6>.(71.R1.)(72.R1.)$70.$8.$8.))(59.$76.(77.(6>.(73.R1.)$74.$70.$8.$8.))(59.$76.$78.(59.$76.$79.(59.$76.$7:.(59.$76.$7;.(59.$76.(77.(6>.(75.R1.)+1000.$70.$8.$8.))(5:.$76.)))))))))(:.$76.(7<.$16.$76.Lb,$16.(77.(7=.R1.))(5?.(60.O1.)))(:.$76.(7<.$16.$76.Lb,$16.(77.(7>.R1.))(61.(60.O1.)))(:.$76.(7<.$2>.$76.Lsh,$2>.(77.(7?.R1.))(30.(31.O1.)))(7<.$66.$76.Lt,$66.(77.R1.)(80.O1.))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition zsomes (h : ahst) : list trange := ltac2:(CDefT.buildp (gd_tbl_AInstFree ()) "(:.$66.(81.(25.O1.))(:.$66.(7<.$16.$66.$7=.(5?.(60.O1.)))(:.$66.(7<.$16.$66.$7>.(61.(60.O1.)))(:.$66.(7<.$2>.$66.$7?.(30.(31.O1.)))(80.O1.)))))")
(* [comment removed for export] *).
  Definition zproj (g : ztag) : option trange := match g with ZT t => Some t | _ => None end.

  #[using="Type"] Lemma hzones_eq : forall h, hzones h = map (zval (h_L h)) (ztags h).
  Proof.
    intros h. unfold hzones, ztags. rewrite !map_app, !map_map. cbn [zval]. do 4 f_equal.
    unfold emb_tr. destruct (a_emb (h_acct h) =? 0); reflexivity.
  Qed.
  #[using="Type"] Lemma zsomes_eq : forall h, flat_map (fun o => match o with Some a => [a] | None => [] end) (map zproj (ztags h)) = zsomes h.
  Proof.
    intros h. unfold ztags, zsomes, zfix. rewrite !map_app, !flat_map_app, !map_map. cbn [map flat_map zproj app].
    assert (E : forall (A : Type) (f : A -> trange) (l : list A), flat_map (fun o => match o with Some a => [a] | None => [] end) (map (fun x => Some (f x)) l) = map f l)
      by (intros A f l; induction l as [|a l IH]; [reflexivity| cbn; rewrite IH; reflexivity]).
    rewrite !E. rewrite ?map_id. reflexivity.
  Qed.
  #[using="Type"] Lemma zsomes_in : forall h t, In t (zsomes h) -> In t (tr_of h) /\ t_cs t = true /\ t_lit t = true.
  Proof.
    intros h t Ht. unfold zsomes, zfix in Ht. rewrite !in_app_iff in Ht. destruct Ht as [Ht|[Ht|[Ht|[Ht|Ht]]]].
    - destruct Ht as [<-|[<-|[<-|[<-|[]]]]]; (split; [| split; reflexivity]); [apply tr_of_T| apply tr_of_ctx| apply tr_of_fs| apply tr_of_dtls].
    - apply in_map_iff in Ht. ddestruct Ht as (b & <- & Hb). split; [apply tr_of_node; exact Hb| split; reflexivity].
    - apply in_map_iff in Ht. ddestruct Ht as (b & <- & Hb). split; [apply tr_of_store; exact Hb| split; reflexivity].
    - apply in_map_iff in Ht. ddestruct Ht as (b & <- & Hb). split; [apply tr_of_sec; exact Hb| split; reflexivity].
    - split; [unfold tr_of; rewrite !in_app_iff; do 7 right; exact Ht|]. unfold emb_tr in Ht. destruct (a_emb (h_acct h) =? 0); [destruct Ht| destruct Ht as [<-|[]]; split; reflexivity].
  Qed.
  #[using="Type"] Lemma zsomes_NoDup : forall h mo, HK AL h mo -> List.NoDup (zsomes h).
  Proof.
    intros h mo K. pose proof (tr_of_NoDup AL h mo K) as ND.
    assert (P : Permutation (tr_of h) (zsomes h ++ (units_of h ++ [ri_tr (h_L h)] ++ map (pa_tr (h_L h)) (zseq (h_pa_committed h / kPaSlice))
                                                     ++ map (fun r => TR (fst r) (snd r) (xkind (snd r)) true false) (l_extra (h_L h))
                                                     ++ [TR 0x7fff7000 0x10000000 KLazy true false; TR 0x8fff7000 0x20000000000 KNoacc true false; TR 0x2008fff7000 0xdfff0001000 KLazy true false]))).
    { unfold tr_of, zsomes, fixed_of, zfix.
      set (A := map node_tr (d_nb (h_dep h))). set (B := map store_tr (d_bl (h_dep h))). set (C := map sec_tr (s_chunks (h_sec h))).
      set (U := units_of h). set (R1 := [ri_tr (h_L h)]). set (P := map (pa_tr (h_L h)) (zseq (h_pa_committed h / kPaSlice))).
      set (F4 := [TR (l_T (h_L h)) 4096 KEager true true; TR (l_ctx (h_L h)) (l_ctxlen (h_L h)) KEager true true; TR (l_fs (h_L h)) kFakeBytes KEager true true; TR (l_dtls (h_L h)) 4096 KEager true true]).
      set (E := map (fun r => TR (fst r) (snd r) (xkind (snd r)) true false) (l_extra (h_L h))).
      set (B3 := [TR 0x7fff7000 0x10000000 KLazy true false; TR 0x8fff7000 0x20000000000 KNoacc true false; TR 0x2008fff7000 0xdfff0001000 KLazy true false]).
      set (EM := emb_tr h).
      replace (A ++ B ++ C ++ U ++ R1 ++ P ++ (F4 ++ E ++ B3) ++ EM) with ((A ++ B ++ C ++ U ++ R1 ++ P) ++ F4 ++ (E ++ B3 ++ EM)) by (rewrite <- !app_assoc; reflexivity).
      eapply Permutation_trans; [apply Permutation_app_swap_app|].
      replace ((F4 ++ A ++ B ++ C ++ EM) ++ U ++ R1 ++ P ++ E ++ B3) with (F4 ++ A ++ B ++ C ++ (EM ++ (U ++ R1 ++ P ++ E ++ B3))) by (rewrite <- !app_assoc; reflexivity).
      replace (F4 ++ (A ++ B ++ C ++ U ++ R1 ++ P) ++ E ++ B3 ++ EM) with (F4 ++ A ++ B ++ C ++ ((U ++ R1 ++ P ++ E ++ B3) ++ EM)) by (rewrite <- !app_assoc; reflexivity).
      do 4 apply Permutation_app_head. apply Permutation_app_comm. }
    exact (NoDup_app_remove_r _ _ (Permutation_NoDup P ND)).
  Qed.

  #[using="Type"] Lemma ztags_cases : forall h i g, nth_error (ztags h) i = Some g ->
    match g with ZT _ => True | ZPA => i = 3%nat | ZPRIM => i = 4%nat | ZSTK => i = 5%nat | ZBAND => i = 6%nat end.
  Proof.
    intros h i g Hi. unfold ztags in Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error app] in Hi; try (injection Hi as <-; first [exact I| reflexivity]).
    change (nth_error (map (fun b => ZT (node_tr b)) (d_nb (h_dep h)) ++ map (fun b => ZT (store_tr b)) (d_bl (h_dep h)) ++ map (fun sh => ZT (sec_tr sh)) (s_chunks (h_sec h))
                       ++ map (fun t => ZT t) (emb_tr h)) i = Some g) in Hi.
    apply nth_error_In in Hi. rewrite !in_app_iff in Hi.
    destruct Hi as [Hi|[Hi|[Hi|Hi]]]; apply in_map_iff in Hi; ddestruct Hi as (? & <- & _); exact I.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L10849413773.5 L10993833172.8 L12227859414.66L12556379338.8 L14150666894.8 L14868644532.8 L29180805324.8 L33597898641.3 L39536019396.8 L50261556747.3 L59584000500.8 00000@00Q00e01601A01R01]01c02402;02LS3hAR1h3SLO1t2W2S3hAR1h2F63SLO2F5S3hAR2AL1h2H82H93H10S3hAR1h2F93SLO2F8S3hAR1h3SLOS3hAR1h2F63SLO2HAS3hAR1h3SLOS1t2W6S3hAR1h2F63SLO2F5S1h1t1XS3hAR1h2F93SLO2F8". (* [comment removed for export] *)
  #[using="Type"] Theorem F_geom : forall h mo, WFK h -> fK h mo -> hgeom h.
  Proof.
    intros h mo W K i j z z' Hi Hj NE.
    rewrite hzones_eq in Hi, Hj. rewrite nth_error_map in Hi, Hj.
    destruct (nth_error (ztags h) i) as [gi|] eqn:Ei; [| discriminate Hi]. destruct (nth_error (ztags h) j) as [gj|] eqn:Ej; [| discriminate Hj].
    cbn [option_map] in Hi, Hj. injection Hi as <-. injection Hj as <-.
    pose proof (ztags_cases h i gi Ei) as Ci. pose proof (ztags_cases h j gj Ej) as Cj.
    pose proof (WFK_L h W) as WL. pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof (wfL_hull_hi _ WL) as [F8 F9].
    assert (SLO : ACEIL <= l_stk_lo (h_L h) - l_stk_lo (h_L h) mod 64 /\ l_stk_lo (h_L h) <= l_stk_hi (h_L h)).
    { unfold wf_L in WL. decompose [and] WL. split; [apply ACEIL_le_hull64; assumption| lia]. }
    pose proof (hulls_apart AL h mo K) as HA.
    (* [comment removed for export] *)
    assert (ZIN : forall k t, nth_error (ztags h) k = Some (ZT t) -> In t (tr_of h) /\ t_cs t = true /\ t_lit t = true).
    { intros k t Hk. apply zsomes_in. rewrite <- zsomes_eq. apply in_flat_map. exists (Some t). split; [| left; reflexivity].
      apply in_map_iff. exists (ZT t). split; [reflexivity|]. eapply nth_error_In. exact Hk. }
    assert (ZINJ : forall k k' t, nth_error (ztags h) k = Some (ZT t) -> nth_error (ztags h) k' = Some (ZT t) -> k = k').
    { intros k k' t Hk Hk'. apply (NoDup_somes_inj (map zproj (ztags h)) k k' t); [rewrite zsomes_eq; exact (zsomes_NoDup h mo K)| |];
        rewrite nth_error_map; [rewrite Hk| rewrite Hk']; reflexivity. }
    (* [comment removed for export] *)
    assert (TF : forall t g, In t (tr_of h) -> t_cs t = true -> t_lit t = true -> match g with ZT _ => False | _ => True end ->
                 zapart (zval (h_L h) (ZT t)) (zval (h_L h) g)).
    { intros t g Ht TC TL Hg. dpose (tr_wf AL h mo t K Ht) as (W0 & W1 & W2 & W3 & W4 & W5 & W6). specialize (W6 TC).
      aceilb. 
      unfold zapart. destruct g as [| | | |]; [destruct Hg| | | |]; cbn [zval fst snd]; unfold t_hi in *.
      - destruct (lit_apart_hull AL h mo t (l_pa (h_L h), kPaHullLen) K Ht TL ltac:(right; left; reflexivity)) as [X|X]; cbn [fst snd] in X; unfold kPaHullLen, t_hi in X; clear - X; lia.
      - destruct (lit_apart_hull AL h mo t (l_b6 (h_L h), kPrimHullLen) K Ht TL ltac:(left; reflexivity)) as [X|X]; cbn [fst snd] in X; unfold kPrimHullLen, t_hi in X; clear - X; lia.
      - left. clear - W2 SLO. lia.
      - clear - W6 W1. lia. }
    assert (ZS : forall a b, zapart a b -> zapart b a) by (intros a b [X|X]; [right| left]; exact X).
    destruct gi as [t1| | | |], gj as [t2| | | |].
    { (* [comment removed for export] *)
      ddestruct (ZIN i t1 Ei) as (I1 & C1 & L1). ddestruct (ZIN j t2 Ej) as (I2 & C2 & L2).
      destruct (tr_apart AL h mo t1 t2 K I1 I2) as [E|X]; [exfalso; subst t2; exact (NE (ZINJ i j t1 Ei Ej))|].
      unfold zapart. cbn [zval fst snd]. unfold t_hi in X. exact X. }
    all: try (destruct (ZIN _ _ Ei) as (I1 & C1 & L1); apply TF; [exact I1| exact C1| exact L1| exact I]).
    all: try (destruct (ZIN _ _ Ej) as (I2 & C2 & L2); apply ZS; apply TF; [exact I2| exact C2| exact L2| exact I]).
    all: try (exfalso; apply NE; cbn in Ci, Cj; congruence).
    all: unfold zapart; cbn [zval fst snd]; unfold kPrimHullLen, kPaHullLen, lowhigh, kHighMemBeg in *; clear - HA F5 F6 F8 F9 SLO; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L16521679723.17L2882472828.17 000004008S2ALS2AL". (* [comment removed for export] *)
  Definition ffam_i : ffam AL.
  Proof.
    unshelve refine (FF AL fCS fK F_csok F_kinv F_view_K F_view_CS F_noshadow F_halted F_geom F_apart
                       F_cs_T F_cs_ctx F_cs_ri F_cs_fs F_cs_stack F_cs_user F_cs_fa F_cs_node F_cs_store F_cs_sec F_cs_pa F_cs_img
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_node F_store F_room_n F_room_s F_cs_mono_fa F_cs_mono_u F_cs_rec_sec F_cs_mono_dep).
    - intros h c mo W Hc ROOM K. ddestruct (F_fa_all h c mo W Hc ROOM K) as (_ & MC & RF & _). exact (conj RF (or_introl MC)).
    - intros h c mo W Hc ROOM K _. exact (proj1 (F_fa_all h c mo W Hc ROOM K)).
    - intros h c mo W Hc ROOM K RF. exfalso. ddestruct (F_fa_all h c mo W Hc ROOM K) as (_ & MC & _).
      refine (map_contains_not_free _ _ _ _ _ MC RF). rewrite u64_lit by lia. lia.
    - intros h c mo W Hc ROOM K. exact (proj2 (proj2 (proj2 (F_fa_all h c mo W Hc ROOM K)))).
    - (* [comment removed for export] *) intros h c W Hc ROOM. exact (F_fa_scar h c W Hc ROOM).
    - intros h c mo W Hc ROOM K. ddestruct (F_u_all h c mo W Hc ROOM K) as (_ & MC & RF & _). exact (conj RF (or_introl MC)).
    - intros h c mo W Hc ROOM K _. exact (proj1 (F_u_all h c mo W Hc ROOM K)).
    - intros h c mo W Hc ROOM K RF. exfalso. ddestruct (F_u_all h c mo W Hc ROOM K) as (_ & MC & _).
      refine (map_contains_not_free _ _ _ _ _ MC RF). rewrite u64_lit by lia. lia.
    - intros h c mo W Hc ROOM K. exact (proj2 (proj2 (proj2 (F_u_all h c mo W Hc ROOM K)))).
    - (* [comment removed for export] *) intros h c W Hc ROOM. exact (F_u_scar h c W Hc ROOM).
    - intros h k i mo W NTH NE K. cbn zeta. exact (proj1 (F_madv_all h k i mo W NTH NE K)).
    - intros h k i mo W NTH NE K. cbn zeta. exact (proj2 (F_madv_all h k i mo W NTH NE K)).
    - intros h k i mo W NTH K. exact (proj1 (F_unmap_all h k i mo W NTH K)).
    - intros h k i mo W NTH K. exact (proj2 (F_unmap_all h k i mo W NTH K)).
  Defined.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Inst.

End ARUN_1.
