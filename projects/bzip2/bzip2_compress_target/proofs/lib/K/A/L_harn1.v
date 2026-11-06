(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2 L_harnw1 L_harnw2.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw2.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section Body.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.

(* [comment removed for export] *)
Variables (Σ0 : rts RT) (PMc : Model -> Prop) (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m0 : mem) (d : Z) (bs : list byte)
          (p0 n0 spa Fr : Z).
Local Notation n := (Z.of_nat (length bs)).
Local Notation live0 := (rt_live RT Σ0).

Record hz_ok : Prop := mkHZ {
  hz_FDO : fdfs_only PMc; hz_MST : mat_stable PMc;
  hz_TP : tp = Z_to_bv 64 0x6094d8; hz_RAH : cra = Z_to_bv 64 RA_HARN; hz_S0F : fp_stop usp (bv_unsigned c0);
  hz_FRS0 : rt_frames RT Σ0 = []; hz_POS : forall p k, In (p, k) live0 -> 0 < k;
  hz_LVB : Z.of_nat (length live0) + FUZZ_LIVE <= LIVE_MAX; hz_CRB : FUZZ_COST <= rt_credit RT Σ0;
  hz_LOW : rt_sp0 RT Σ0 - STACK_WIN <= lo; hz_LOR : lo + FUZZ_STACK <= usp; hz_SPT : usp + 16 <= USTACK_TOP; hz_SPS : usp <= rt_sp0 RT Σ0;
  hz_SPA : usp mod 16 = 0; hz_SPA1 : spa = usp + -128 \/ spa = usp + -144; hz_SPA2 : spa mod 32 = 0;
  hz_SP0R : SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ0 <= USTACK_TOP; hz_SP0W : 0x7fff80000000 <= rt_sp0 RT Σ0;
  hz_D0 : 0 < d; hz_DHI : d + n <= rt_sp0 RT Σ0 - STACK_WIN; hz_NB : n < 2^26; hz_INB : bytes_at bsegs m0 d bs;
  hz_INP : bs = [] \/ (In (p0, n0) live0 /\ p0 <= d /\ d + n <= p0 + n0);
  hz_LIB0 : LIB m0;
  hz_F64 : Fr mod 64 = 0; hz_FSEG : SEGTOP_A <= Fr; hz_FPL : Fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr; hz_FLO : Fr + 64 <= lo;
  hz_FAP : forall x, aclient live0 [] usp x -> ~ (Fr <= x < Fr + 64) /\ ~ (shad Fr <= x < shad (Fr + 64))
}.

(* [comment removed for export] *)
Definition ACL (x : Z) : Prop := aclient live0 [] usp x.
Definition CORE (x : Z) : Prop := spa <= x < usp \/ Fr <= x < Fr + 8 \/ shad Fr <= x < shad Fr + 8 \/ ACL x.

(* [comment removed for export] *)
Definition HM (Σ : rts RT) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv bsegs m /\ stk bsegs m lo spa /\ agree_on ACL m0 m
  /\ (exists (z0 : word) (j8 : list byte), rw_cells bsegs m (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
  /\ (spa = usp + -128 \/ (spa = usp + -144 /\ exists jg : list byte, rw_cells bsegs m (usp + -144) [CB 16 jg]))
  /\ (exists h0 : word, rw_cells bsegs m Fr [C8 h0]) /\ rw_cells bsegs m (shad Fr) hz_sh0.
(* [comment removed for export] *)
Definition HS (Σ : rts RT) (new : list (Z * Z)) : Prop :=
  rt_live RT Σ = new ++ live0 /\ rt_frames RT Σ = [(Fr, 0%nat)] /\ rt_sp0 RT Σ = rt_sp0 RT Σ0.

(* [comment removed for export] *)
Definition HQ : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st cra (Z_to_bv 64 usp) gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 (Z_to_bv 64 0) m' ms
       /\ rt_after_f RT Σ' usp lo m0 m' /\ rt_pres_fp live0 [] usp LIB_FP m0 m' /\ LIB m') c
    /\ rt_live RT Σ' = live0 /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0
    /\ rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ'.

Hypothesis OK : hz_ok.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX, B2B_STACK in *; lia.

Lemma hz_geo : lo <= spa /\ spa + 128 <= usp /\ usp <= spa + 144 /\ 0x7fff7f800000 <= lo /\ usp < 2^47 /\ 0 < spa.
Proof using OK. destruct OK. ul. Qed.

Lemma hz_EU : bv_unsigned (Z_to_bv 64 spa) = spa.
Proof using OK. pose proof hz_geo. apply unsigned_lit. lia. Qed.
Lemma hz_EUS : bv_unsigned (Z_to_bv 64 usp) = usp.
Proof using OK. pose proof hz_geo. apply unsigned_lit. lia. Qed.

Lemma shad_F64 : shad (Fr + 64) = shad Fr + 8.
Proof using OK. destruct OK. unfold shad. Z.div_mod_to_equations. lia. Qed.

Lemma shad_F_lo : shad Fr + 8 <= lo.
Proof using OK. pose proof hz_geo. destruct OK. unfold shad, SHB. Z.div_mod_to_equations. ul. Qed.

Lemma acl_core : forall x, ACL x -> CORE x.
Proof. intros x H. right; right; right. exact H. Qed.

(* [comment removed for export] *)
Lemma core_client : forall live, (forall e, In e live0 -> In e live) -> forall x, CORE x -> aclient live [(Fr, 0%nat)] spa x.
Proof using OK.
  intros live HL x [H|[H|[H|H]]].
  - left. destruct OK. ul.
  - right; right; right; left. exists Fr, 0%nat. split; [left; reflexivity|]. change (fs_size 0) with 64. lia.
  - right; right; right; right. exists Fr, 0%nat. split; [left; reflexivity|]. change (fs_size 0) with 64. rewrite shad_F64. lia.
  - apply (aclient_mono _ _ _ _ _ _ _ H); [exact HL| intros e []|]. pose proof hz_geo. lia.
Qed.

(* [comment removed for export] *)
Lemma core_not_cells : forall x, CORE x -> ~ (Fr + 8 <= x < Fr + 64).
Proof using OK.
  intros x [H|[H|[H|H]]] Hx.
  - pose proof hz_geo. destruct OK. lia.
  - lia.
  - destruct OK. unfold shad, SHB in H. Z.div_mod_to_equations. lia.
  - destruct (hz_FAP OK x H) as (A1 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma core_not_chunk : forall Σ (m : mem) new p k, ART RT Σ m -> HS Σ new -> In (p, k) new -> forall x, CORE x -> ~ (p <= x < p + k).
Proof using OK AF.
  intros Σ m new p k ART1 (LV & FRS & SP0) Hin x Hc Hx.
  assert (INL : In (p, k) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; left; exact Hin).
  assert (INF : In (Fr, 0%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_live_range RT AF Σ m p k ART1 INL) as (R0 & R1 & R2). rewrite SP0 in R1.
  pose proof (af_frames_range RT AF Σ m Fr 0 ART1 INF) as (_ & _ & _ & R3). specialize (R3 p k INL). change (fs_size 0) with 64 in R3.
  pose proof (af_fshadow_apart RT AF Σ m Fr 0 ART1 INF) as (SL & _). specialize (SL p k INL). change (fs_size 0) with 64 in SL. rewrite shad_F64 in SL.
  pose proof hz_geo as G.
  destruct Hc as [H|[H|[H|H]]].
  - destruct OK. lia.
  - lia.
  - lia.
  - destruct H as [H|[H|[H|[H|H]]]].
    + destruct OK. lia.
    + pose proof (client_static_range x H). unfold SEGTOP_A in *. lia.
    + destruct H as (q & j & Hq & Hj). destruct (in_split _ _ Hin) as (l1 & l2 & E).
      assert (LV' : rt_live RT Σ = l1 ++ (p, k) :: (l2 ++ live0)) by (rewrite LV, E, <- app_assoc; reflexivity).
      pose proof (af_live_disj RT AF Σ m p k q j l1 (l2 ++ live0) ART1 LV' ltac:(apply in_or_app; right; apply in_or_app; right; exact Hq)) as D. lia.
    + destruct H as (f & k' & [] & _).
    + destruct H as (f & k' & [] & _).
Qed.

(* [comment removed for export] *)
Lemma hs_fresh : forall Σ (m : mem) new q k, ART RT Σ m -> HS Σ new -> In (q, k) new -> 0 < k -> forall e, In e live0 -> fst e <> q.
Proof using OK AF.
  intros Σ m new q k ART1 (LV & _) Hin K0 (q' & k') He E. cbn [fst] in E. subst q'. destruct (in_split _ _ Hin) as (l1 & l2 & EN).
  assert (LV' : rt_live RT Σ = l1 ++ (q, k) :: (l2 ++ live0)) by (rewrite LV, EN, <- app_assoc; reflexivity).
  pose proof (af_live_disj RT AF Σ m q k q k' l1 (l2 ++ live0) ART1 LV' ltac:(apply in_or_app; right; apply in_or_app; right; exact He)) as D.
  pose proof (hz_POS OK q k' He). lia.
Qed.

(* [comment removed for export] *)
Lemma hz_sh0_parts : forall (m : mem) a, rw_cells bsegs m a hz_sh0 -> ro_cells bsegs m (a + 4) [C1 (Z_to_bv 8 4)] /\ ro_cells bsegs m (a + 6) [C1 (Z_to_bv 8 4)].
Proof.
  intros m a H. unfold hz_sh0 in H.
  change [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13))]
    with ([C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] ++ [C1 (Z_to_bv 8 4)] ++ [C1 (Z_to_bv 8 (-14))] ++ [C1 (Z_to_bv 8 4)]
          ++ [C1 (Z_to_bv 8 (-13))]) in H.
  apply rw_cells_app in H as (_ & H). apply rw_cells_app in H as (H4 & H). apply rw_cells_app in H as (_ & H). apply rw_cells_app in H as (H6 & _).
  cbn [cells_size csize Nat.add] in H4, H6. split; [exact (proj1 H4)|]. replace (a + 6) with (a + Z.of_nat 4 + Z.of_nat 1 + Z.of_nat 1) by lia. exact (proj1 H6).
Qed.

(* [comment removed for export] *)
Lemma hs_chunk_frame : forall Σ (m : mem) new q k, ART RT Σ m -> HS Σ new -> In (q, k) new -> Fr + 64 <= q \/ q + k <= Fr.
Proof using AF.
  intros Σ m new q k ART1 (LV & FRS & _) Hin.
  pose proof (af_frames_range RT AF Σ m Fr 0 ART1 ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & R3). change (fs_size 0) with 64 in R3.
  apply R3. rewrite LV. apply in_or_app. left. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma hm_step : forall Σ Σ' (m m' : mem), HM Σ m -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo spa -> agree_on CORE m m' -> HM Σ' m'.
Proof using OK.
  intros Σ Σ' m m' (_ & _ & _ & PR & (z0 & j8 & FR) & GAP & (h0 & HDR) & SH) ART1 MI1 ST1 AG. pose proof hz_geo as G.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
  split; [apply (agree_trans _ m0 m m' PR); apply (agree_sub _ _ _ _ AG); exact acl_core|].
  split; [exists z0, j8; apply (rw_cells_agree_nw bsegs m m' _ _ FR); apply (agree_sub _ _ _ _ AG); intros x Hx;
          cbn [cells_size hz_frame csize Nat.add] in Hx; left; lia|].
  split; [destruct GAP as [E|(E & jg & GP)]; [left; exact E| right; split; [exact E|]; exists jg; apply (rw_cells_agree_nw bsegs m m' _ _ GP);
          apply (agree_sub _ _ _ _ AG); intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia]|].
  split; [exists h0; apply (rw_cells_agree_nw bsegs m m' _ _ HDR); apply (agree_sub _ _ _ _ AG); intros x Hx; cbn [cells_size csize Nat.add] in Hx;
          right; left; lia|].
  apply (rw_cells_agree_nw bsegs m m' _ _ SH). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size hz_sh0 csize Nat.add] in Hx. right; right; left. lia.
Qed.

(* [comment removed for export] *)
Lemma core_of_pres_fp : forall live W (m m' : mem), rt_pres_fp live [(Fr, 0%nat)] spa W m m' -> (forall e, In e live0 -> In e live) ->
  (forall x, CORE x -> outside W x) -> agree_on CORE m m'.
Proof using OK. intros live W m m' PR HL HW. apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x Hx. split; [exact (core_client live HL x Hx)| exact (HW x Hx)]. Qed.

Lemma core_of_pres : forall live (m m' : mem), rt_pres live [(Fr, 0%nat)] spa m m' -> (forall e, In e live0 -> In e live) -> agree_on CORE m m'.
Proof using OK. intros live m m' PR HL. apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. exact (core_client live HL x Hx). Qed.

(* [comment removed for export] *)
Lemma hs_art_munch : forall Σ new W (m m' : mem), ART RT Σ m -> HS Σ new -> munch W m m' -> wmono bsegs m m' ->
  (forall x, ~ (Fr <= x < Fr + 56) -> ~ (shad Fr <= x < shad Fr + 8) -> ~ (spa <= x < usp) -> outside W x) -> ART RT Σ m'.
Proof using OK AF.
  intros Σ new W m m' ART1 (LV & FRS & SP0) MU WM HW. pose proof hz_geo as G.
  apply (af_frame RT AF Σ m m' lo ART1 ltac:(rewrite SP0; exact (hz_LOW OK))); [| exact WM].
  intros a Ha. apply MU. apply HW; intros Hin; apply Ha.
  - right; right; right; left. exists Fr, 0%nat. split; [rewrite FRS; left; reflexivity|]. change (fs_size 0) with 64. lia.
  - right; right; right; right. exists Fr, 0%nat. split; [rewrite FRS; left; reflexivity|]. change (fs_size 0) with 64. rewrite shad_F64. lia.
  - left. destruct OK. ul.
Qed.

(* [comment removed for export] *)
Lemma hm_payload : forall Σ (m : mem), HM Σ m -> bytes_at bsegs m d bs.
Proof using OK.
  intros Σ m (_ & _ & _ & PR & _). apply (bytes_at_agree bsegs m0 m _ _ (hz_INB OK)). apply (agree_sub _ _ _ _ PR). intros x Hx.
  destruct (hz_INP OK) as [E|(IN & P0 & P1)]; [rewrite E in Hx; cbn [length Z.of_nat] in Hx; lia|].
  right; right; left. exists p0, n0. split; [exact IN| lia].
Qed.

Lemma hm_lib : forall Σ (m : mem), HM Σ m -> LIB m.
Proof using OK LIB_loc.
  intros Σ m (_ & _ & _ & PR & _). apply (LIB_loc m0 m (hz_LIB0 OK)). intros a Ha. apply PR. right; left. exact (proj1 (LIB_img _ Ha)).
Qed.

(* [comment removed for export] *)
Lemma hm_record : forall Σ (m : mem), HM Σ m -> harn_record m (Z_to_bv 64 spa) (Z_to_bv 64 usp).
Proof using OK.
  intros Σ m (_ & _ & _ & _ & (z0 & j8 & FR) & _). unfold harn_record. rewrite hz_EU, hz_EUS. pose proof hz_geo as G. cbn [uw_chain].
  split; [lia|]. split; [destruct OK; Z.div_mod_to_equations; lia|]. split; [destruct OK; ul|].
  exists (bv_unsigned c0). split; [pose proof (bv_unsigned_in_range 64 c0) as R; change (bv_modulus 64) with (2^64) in R; lia|].
  split; [| exact (hz_S0F OK)].
  rewrite Z_to_bv_bv_unsigned, <- (hz_RAH OK). unfold hz_frame in FR.
  change [C8 z0; CB 24 j8; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra]
    with ([C8 z0; CB 24 j8; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1] ++ [C8 c0; C8 cra]) in FR.
  apply rw_cells_app in FR as (_ & FR). cbn [cells_size csize Nat.add] in FR. replace (usp + -128 + Z.of_nat 112) with (usp + -16) in FR by lia. exact FR.
Qed.

Lemma hm_unwind : forall Σ (m : mem) r, HM Σ m -> In r [0x81434; 0x814c8; 0x8150c; 0x81514] -> unwind_ch m (Z_to_bv 64 r) (Z_to_bv 64 usp) (Z_to_bv 64 spa).
Proof using OK.
  intros Σ m r H Hr. exists [RA_HARN]. split.
  - replace (bv_unsigned (Z_to_bv 64 r)) with r; [exact (harn_site r Hr)|]. symmetry. apply unsigned_lit. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; lia.
  - exact (hm_record Σ m H).
Qed.

Lemma hm_call_ok : forall Σ (m : mem) new, HM Σ m -> HS Σ new -> call_ok RT Σ m (Z_to_bv 64 spa) lo.
Proof using OK.
  intros Σ m new (_ & _ & ST & _) (_ & _ & SP0). unfold call_ok. rewrite hz_EU, SP0. pose proof hz_geo as G. destruct OK.
  split; [exact ST|]. split; [lia|]. split; [ul|]. split; [ul|]. Z.div_mod_to_equations. lia.
Qed.

End Body.

(* [comment removed for export] *)
Arguments hz_geo {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hz_EU {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hz_EUS {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments shad_F64 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments shad_F_lo {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_client {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_not_cells {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_of_pres_fp {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_of_pres {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_not_chunk {RT LIB} AF {Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hs_fresh {RT LIB} AF {Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hs_art_munch {RT LIB} AF {Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_step {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_payload {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_record {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_unwind {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_call_ok {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_lib {RT LIB} LIB_loc {Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hz_FDO {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_MST {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_TP {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_RAH {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_S0F {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FRS0 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_POS {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LVB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_CRB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LOW {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LOR {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPT {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPS {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPA {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPA1 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPA2 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SP0R {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SP0W {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_D0 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_DHI {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_NB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_INB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_INP {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LIB0 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_F64 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FSEG {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FPL {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FLO {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FAP {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hs_chunk_frame {RT} AF {Σ0 Fr Σ m new q k}.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2
  L_harnw1 L_harnw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section Body.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.

(* [comment removed for export] *)
Variables (Σ0 : rts RT) (PMc : Model -> Prop) (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m0 : mem) (d : Z) (bs : list byte)
          (p0 n0 spa Fr : Z).
Local Notation n := (Z.of_nat (length bs)).
Local Notation live0 := (rt_live RT Σ0).

Record hz_ok : Prop := mkHZ {
  hz_FDO : fdfs_only PMc; hz_MST : mat_stable PMc;
  hz_TP : tp = Z_to_bv 64 0x5fc0d8; hz_RAH : cra = Z_to_bv 64 RA_HARN; hz_S0F : fp_stop usp (bv_unsigned c0);
  hz_FRS0 : rt_frames RT Σ0 = []; hz_POS : forall p k, In (p, k) live0 -> 0 < k;
  hz_LVB : Z.of_nat (length live0) + FUZZ_LIVE <= LIVE_MAX; hz_CRB : FUZZ_COST <= rt_credit RT Σ0;
  hz_LOW : rt_sp0 RT Σ0 - STACK_WIN <= lo; hz_LOR : lo + FUZZ_STACK <= usp; hz_SPT : usp + 16 <= USTACK_TOP; hz_SPS : usp <= rt_sp0 RT Σ0;
  hz_SPA : usp mod 16 = 0; hz_SPA1 : spa = usp + -128 \/ spa = usp + -144; hz_SPA2 : spa mod 32 = 0;
  hz_SP0R : SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ0 <= USTACK_TOP; hz_SP0W : 0x7fff80000000 <= rt_sp0 RT Σ0;
  hz_D0 : 0 < d; hz_DHI : d + n <= rt_sp0 RT Σ0 - STACK_WIN; hz_NB : n < 2^26; hz_INB : bytes_at asegs m0 d bs;
  hz_INP : bs = [] \/ (In (p0, n0) live0 /\ p0 <= d /\ d + n <= p0 + n0);
  hz_LIB0 : LIB m0;
  hz_F64 : Fr mod 64 = 0; hz_FSEG : SEGTOP_A <= Fr; hz_FPL : Fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr; hz_FLO : Fr + 64 <= lo;
  hz_FAP : forall x, aclient live0 [] usp x -> ~ (Fr <= x < Fr + 64) /\ ~ (shad Fr <= x < shad (Fr + 64))
}.

(* [comment removed for export] *)
Definition ACL (x : Z) : Prop := aclient live0 [] usp x.
Definition CORE (x : Z) : Prop := spa <= x < usp \/ Fr <= x < Fr + 8 \/ shad Fr <= x < shad Fr + 8 \/ ACL x.

(* [comment removed for export] *)
Definition HM (Σ : rts RT) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ stk asegs m lo spa /\ agree_on ACL m0 m
  /\ (exists (z0 : word) (j8 : list byte), rw_cells asegs m (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
  /\ (spa = usp + -128 \/ (spa = usp + -144 /\ exists jg : list byte, rw_cells asegs m (usp + -144) [CB 16 jg]))
  /\ (exists h0 : word, rw_cells asegs m Fr [C8 h0]) /\ rw_cells asegs m (shad Fr) hz_sh0.
(* [comment removed for export] *)
Definition HS (Σ : rts RT) (new : list (Z * Z)) : Prop :=
  rt_live RT Σ = new ++ live0 /\ rt_frames RT Σ = [(Fr, 0%nat)] /\ rt_sp0 RT Σ = rt_sp0 RT Σ0.

(* [comment removed for export] *)
Definition HQ : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st cra (Z_to_bv 64 usp) gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 (Z_to_bv 64 0) m' ms
       /\ rt_after_f RT Σ' usp lo m0 m' /\ rt_pres_fp live0 [] usp LIB_FP m0 m' /\ LIB m') c
    /\ rt_live RT Σ' = live0 /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0
    /\ rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ'.

Hypothesis OK : hz_ok.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX, B2B_STACK in *; lia.

Lemma hz_geo : lo <= spa /\ spa + 128 <= usp /\ usp <= spa + 144 /\ 0x7fff7f800000 <= lo /\ usp < 2^47 /\ 0 < spa.
Proof using OK. destruct OK. ul. Qed.

Lemma hz_EU : bv_unsigned (Z_to_bv 64 spa) = spa.
Proof using OK. pose proof hz_geo. apply unsigned_lit. lia. Qed.
Lemma hz_EUS : bv_unsigned (Z_to_bv 64 usp) = usp.
Proof using OK. pose proof hz_geo. apply unsigned_lit. lia. Qed.

Lemma shad_F64 : shad (Fr + 64) = shad Fr + 8.
Proof using OK. destruct OK. unfold shad. Z.div_mod_to_equations. lia. Qed.

Lemma shad_F_lo : shad Fr + 8 <= lo.
Proof using OK. pose proof hz_geo. destruct OK. unfold shad, SHB. Z.div_mod_to_equations. ul. Qed.

Lemma acl_core : forall x, ACL x -> CORE x.
Proof. intros x H. right; right; right. exact H. Qed.

(* [comment removed for export] *)
Lemma core_client : forall live, (forall e, In e live0 -> In e live) -> forall x, CORE x -> aclient live [(Fr, 0%nat)] spa x.
Proof using OK.
  intros live HL x [H|[H|[H|H]]].
  - left. destruct OK. ul.
  - right; right; right; left. exists Fr, 0%nat. split; [left; reflexivity|]. change (fs_size 0) with 64. lia.
  - right; right; right; right. exists Fr, 0%nat. split; [left; reflexivity|]. change (fs_size 0) with 64. rewrite shad_F64. lia.
  - apply (aclient_mono _ _ _ _ _ _ _ H); [exact HL| intros e []|]. pose proof hz_geo. lia.
Qed.

(* [comment removed for export] *)
Lemma core_not_cells : forall x, CORE x -> ~ (Fr + 8 <= x < Fr + 64).
Proof using OK.
  intros x [H|[H|[H|H]]] Hx.
  - pose proof hz_geo. destruct OK. lia.
  - lia.
  - destruct OK. unfold shad, SHB in H. Z.div_mod_to_equations. lia.
  - destruct (hz_FAP OK x H) as (A1 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma core_not_chunk : forall Σ (m : mem) new p k, ART RT Σ m -> HS Σ new -> In (p, k) new -> forall x, CORE x -> ~ (p <= x < p + k).
Proof using OK AF.
  intros Σ m new p k ART1 (LV & FRS & SP0) Hin x Hc Hx.
  assert (INL : In (p, k) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; left; exact Hin).
  assert (INF : In (Fr, 0%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_live_range RT AF Σ m p k ART1 INL) as (R0 & R1 & R2). rewrite SP0 in R1.
  pose proof (af_frames_range RT AF Σ m Fr 0 ART1 INF) as (_ & _ & _ & R3). specialize (R3 p k INL). change (fs_size 0) with 64 in R3.
  pose proof (af_fshadow_apart RT AF Σ m Fr 0 ART1 INF) as (SL & _). specialize (SL p k INL). change (fs_size 0) with 64 in SL. rewrite shad_F64 in SL.
  pose proof hz_geo as G.
  destruct Hc as [H|[H|[H|H]]].
  - destruct OK. lia.
  - lia.
  - lia.
  - destruct H as [H|[H|[H|[H|H]]]].
    + destruct OK. lia.
    + pose proof (client_static_range x H). unfold SEGTOP_A in *. lia.
    + destruct H as (q & j & Hq & Hj). destruct (in_split _ _ Hin) as (l1 & l2 & E).
      assert (LV' : rt_live RT Σ = l1 ++ (p, k) :: (l2 ++ live0)) by (rewrite LV, E, <- app_assoc; reflexivity).
      pose proof (af_live_disj RT AF Σ m p k q j l1 (l2 ++ live0) ART1 LV' ltac:(apply in_or_app; right; apply in_or_app; right; exact Hq)) as D. lia.
    + destruct H as (f & k' & [] & _).
    + destruct H as (f & k' & [] & _).
Qed.

(* [comment removed for export] *)
Lemma hs_fresh : forall Σ (m : mem) new q k, ART RT Σ m -> HS Σ new -> In (q, k) new -> 0 < k -> forall e, In e live0 -> fst e <> q.
Proof using OK AF.
  intros Σ m new q k ART1 (LV & _) Hin K0 (q' & k') He E. cbn [fst] in E. subst q'. destruct (in_split _ _ Hin) as (l1 & l2 & EN).
  assert (LV' : rt_live RT Σ = l1 ++ (q, k) :: (l2 ++ live0)) by (rewrite LV, EN, <- app_assoc; reflexivity).
  pose proof (af_live_disj RT AF Σ m q k q k' l1 (l2 ++ live0) ART1 LV' ltac:(apply in_or_app; right; apply in_or_app; right; exact He)) as D.
  pose proof (hz_POS OK q k' He). lia.
Qed.

(* [comment removed for export] *)
Lemma hz_sh0_parts : forall (m : mem) a, rw_cells asegs m a hz_sh0 -> ro_cells asegs m (a + 4) [C1 (Z_to_bv 8 4)] /\ ro_cells asegs m (a + 6) [C1 (Z_to_bv 8 4)].
Proof.
  intros m a H. unfold hz_sh0 in H.
  change [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13))]
    with ([C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] ++ [C1 (Z_to_bv 8 4)] ++ [C1 (Z_to_bv 8 (-14))] ++ [C1 (Z_to_bv 8 4)]
          ++ [C1 (Z_to_bv 8 (-13))]) in H.
  apply rw_cells_app in H as (_ & H). apply rw_cells_app in H as (H4 & H). apply rw_cells_app in H as (_ & H). apply rw_cells_app in H as (H6 & _).
  cbn [cells_size csize Nat.add] in H4, H6. split; [exact (proj1 H4)|]. replace (a + 6) with (a + Z.of_nat 4 + Z.of_nat 1 + Z.of_nat 1) by lia. exact (proj1 H6).
Qed.

(* [comment removed for export] *)
Lemma hs_chunk_frame : forall Σ (m : mem) new q k, ART RT Σ m -> HS Σ new -> In (q, k) new -> Fr + 64 <= q \/ q + k <= Fr.
Proof using AF.
  intros Σ m new q k ART1 (LV & FRS & _) Hin.
  pose proof (af_frames_range RT AF Σ m Fr 0 ART1 ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & R3). change (fs_size 0) with 64 in R3.
  apply R3. rewrite LV. apply in_or_app. left. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma hm_step : forall Σ Σ' (m m' : mem), HM Σ m -> ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo spa -> agree_on CORE m m' -> HM Σ' m'.
Proof using OK.
  intros Σ Σ' m m' (_ & _ & _ & PR & (z0 & j8 & FR) & GAP & (h0 & HDR) & SH) ART1 MI1 ST1 AG. pose proof hz_geo as G.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
  split; [apply (agree_trans _ m0 m m' PR); apply (agree_sub _ _ _ _ AG); exact acl_core|].
  split; [exists z0, j8; apply (rw_cells_agree_nw asegs m m' _ _ FR); apply (agree_sub _ _ _ _ AG); intros x Hx;
          cbn [cells_size hz_frame csize Nat.add] in Hx; left; lia|].
  split; [destruct GAP as [E|(E & jg & GP)]; [left; exact E| right; split; [exact E|]; exists jg; apply (rw_cells_agree_nw asegs m m' _ _ GP);
          apply (agree_sub _ _ _ _ AG); intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia]|].
  split; [exists h0; apply (rw_cells_agree_nw asegs m m' _ _ HDR); apply (agree_sub _ _ _ _ AG); intros x Hx; cbn [cells_size csize Nat.add] in Hx;
          right; left; lia|].
  apply (rw_cells_agree_nw asegs m m' _ _ SH). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size hz_sh0 csize Nat.add] in Hx. right; right; left. lia.
Qed.

(* [comment removed for export] *)
Lemma core_of_pres_fp : forall live W (m m' : mem), rt_pres_fp live [(Fr, 0%nat)] spa W m m' -> (forall e, In e live0 -> In e live) ->
  (forall x, CORE x -> outside W x) -> agree_on CORE m m'.
Proof using OK. intros live W m m' PR HL HW. apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x Hx. split; [exact (core_client live HL x Hx)| exact (HW x Hx)]. Qed.

Lemma core_of_pres : forall live (m m' : mem), rt_pres live [(Fr, 0%nat)] spa m m' -> (forall e, In e live0 -> In e live) -> agree_on CORE m m'.
Proof using OK. intros live m m' PR HL. apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. exact (core_client live HL x Hx). Qed.

(* [comment removed for export] *)
Lemma hs_art_munch : forall Σ new W (m m' : mem), ART RT Σ m -> HS Σ new -> munch W m m' -> wmono asegs m m' ->
  (forall x, ~ (Fr <= x < Fr + 56) -> ~ (shad Fr <= x < shad Fr + 8) -> ~ (spa <= x < usp) -> outside W x) -> ART RT Σ m'.
Proof using OK AF.
  intros Σ new W m m' ART1 (LV & FRS & SP0) MU WM HW. pose proof hz_geo as G.
  apply (af_frame RT AF Σ m m' lo ART1 ltac:(rewrite SP0; exact (hz_LOW OK))); [| exact WM].
  intros a Ha. apply MU. apply HW; intros Hin; apply Ha.
  - right; right; right; left. exists Fr, 0%nat. split; [rewrite FRS; left; reflexivity|]. change (fs_size 0) with 64. lia.
  - right; right; right; right. exists Fr, 0%nat. split; [rewrite FRS; left; reflexivity|]. change (fs_size 0) with 64. rewrite shad_F64. lia.
  - left. destruct OK. ul.
Qed.

(* [comment removed for export] *)
Lemma hm_payload : forall Σ (m : mem), HM Σ m -> bytes_at asegs m d bs.
Proof using OK.
  intros Σ m (_ & _ & _ & PR & _). apply (bytes_at_agree asegs m0 m _ _ (hz_INB OK)). apply (agree_sub _ _ _ _ PR). intros x Hx.
  destruct (hz_INP OK) as [E|(IN & P0 & P1)]; [rewrite E in Hx; cbn [length Z.of_nat] in Hx; lia|].
  right; right; left. exists p0, n0. split; [exact IN| lia].
Qed.

Lemma hm_lib : forall Σ (m : mem), HM Σ m -> LIB m.
Proof using OK LIB_loc.
  intros Σ m (_ & _ & _ & PR & _). apply (LIB_loc m0 m (hz_LIB0 OK)). intros a Ha. apply PR. right; left. exact (proj1 (LIB_img _ Ha)).
Qed.

(* [comment removed for export] *)
Lemma hm_record : forall Σ (m : mem), HM Σ m -> harn_record m (Z_to_bv 64 spa) (Z_to_bv 64 usp).
Proof using OK.
  intros Σ m (_ & _ & _ & _ & (z0 & j8 & FR) & _). unfold harn_record. rewrite hz_EU, hz_EUS. pose proof hz_geo as G. cbn [uw_chain].
  split; [lia|]. split; [destruct OK; Z.div_mod_to_equations; lia|]. split; [destruct OK; ul|].
  exists (bv_unsigned c0). split; [pose proof (bv_unsigned_in_range 64 c0) as R; change (bv_modulus 64) with (2^64) in R; lia|].
  split; [| exact (hz_S0F OK)].
  rewrite Z_to_bv_bv_unsigned, <- (hz_RAH OK). unfold hz_frame in FR.
  change [C8 z0; CB 24 j8; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra]
    with ([C8 z0; CB 24 j8; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1] ++ [C8 c0; C8 cra]) in FR.
  apply rw_cells_app in FR as (_ & FR). cbn [cells_size csize Nat.add] in FR. replace (usp + -128 + Z.of_nat 112) with (usp + -16) in FR by lia. exact FR.
Qed.

Lemma hm_unwind : forall Σ (m : mem) r, HM Σ m -> In r [0x819e8; 0x81a7c; 0x81ac0; 0x81ac8] -> unwind_ch m (Z_to_bv 64 r) (Z_to_bv 64 usp) (Z_to_bv 64 spa).
Proof using OK.
  intros Σ m r H Hr. exists [RA_HARN]. split.
  - replace (bv_unsigned (Z_to_bv 64 r)) with r; [exact (harn_site r Hr)|]. symmetry. apply unsigned_lit. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; lia.
  - exact (hm_record Σ m H).
Qed.

Lemma hm_call_ok : forall Σ (m : mem) new, HM Σ m -> HS Σ new -> call_ok RT Σ m (Z_to_bv 64 spa) lo.
Proof using OK.
  intros Σ m new (_ & _ & ST & _) (_ & _ & SP0). unfold call_ok. rewrite hz_EU, SP0. pose proof hz_geo as G. destruct OK.
  split; [exact ST|]. split; [lia|]. split; [ul|]. split; [ul|]. Z.div_mod_to_equations. lia.
Qed.

End Body.

(* [comment removed for export] *)
Arguments hz_geo {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hz_EU {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hz_EUS {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments shad_F64 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments shad_F_lo {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_client {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_not_cells {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_of_pres_fp {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_of_pres {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments core_not_chunk {RT LIB} AF {Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hs_fresh {RT LIB} AF {Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hs_art_munch {RT LIB} AF {Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_step {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_payload {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_record {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_unwind {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_call_ok {RT LIB Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hm_lib {RT LIB} LIB_loc {Σ0 PMc cra tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 d bs p0 n0 spa Fr} OK.
Arguments hz_FDO {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_MST {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_TP {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_RAH {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_S0F {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FRS0 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_POS {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LVB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_CRB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LOW {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LOR {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPT {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPS {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPA {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPA1 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SPA2 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SP0R {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_SP0W {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_D0 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_DHI {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_NB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_INB {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_INP {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_LIB0 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_F64 {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FSEG {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FPL {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FLO {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hz_FAP {RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr}.
Arguments hs_chunk_frame {RT} AF {Σ0 Fr Σ m new q k}.
