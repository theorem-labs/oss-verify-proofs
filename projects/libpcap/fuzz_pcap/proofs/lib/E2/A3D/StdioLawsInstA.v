(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto RtCells MonadF AMalloc_iface AFake_iface AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA I_ahm I_fflush StdioLawsA StdioCompA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ExitHeapA GStatKit DrvStatA StaticsA TlsObjA HarnCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section StdioInst.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_ST1 : exists iv, In iv (aci AI) /\ fst iv <= 0xa9ab0 /\ 0xa9d80 <= snd iv.
  Hypothesis CI_ST2 : exists iv, In iv (aci AI) /\ fst iv <= 0x601ca8 /\ 0x6024d0 <= snd iv.

  (* [comment removed for export] *)
  Definition fb_geo (b : cblk) : Prop :=
    0x603000 <= cb_addr b /\ 0 <= cb_size b /\ cb_addr b + cb_size b <= ATOP
    /\ (cb_addr b + cb_size b <= ATP + -200 \/ ATP + -200 + 504 <= cb_addr b).
  Definition files_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := STDIOR (ps_libc s) FB m /\ Forall fb_geo FB.
  (* [comment removed for export] *)
  Definition nonimg (a : Z) : Prop := 0x603000 <= a /\ ~ (ATP + -200 <= a < ATP + -200 + 504).
  #[using="Type"] Lemma nonimg_not_drv : forall a, nonimg a -> ~ drv_static a.
  Proof. intros a [N1 N2] [D|D]; unfold READ_STAGE in *; lia. Qed.
  Definition files_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := stdio_static a \/ (in_block FB a /\ nonimg a).
  Definition files_comp : gcomp := mkGC files_P files_dom.

  #[using="AI_block_tls"] Lemma fb_geo_of_heap : forall L RNG st CL FB FL (m : mem) b, AHEAP AI L RNG st (LBof CL FB FL) m -> In b (CL ++ FB) -> fb_geo b.
  Proof.
    intros L RNG st CL FB FL m b AH Hb. pose proof (In_hb CL FB FL b Hb) as HI.
    (nd_pre (AI_block_bounds AI _ _ _ _ _ _ AH HI) 3%nat; intros B1 B2 B3; nd_post). pose proof (AI_block_tls _ _ _ _ _ _ AH HI) as T.
    unfold hb_of, AIMG_HI in *. cbn [ab_addr ab_size] in *. unfold fb_geo. split; [exact B1|]. split; [exact B2|]. split; [exact B3| exact T].
  Qed.
  #[using="Type"] Lemma fb_geo_nonimg : forall (FB : list cblk) a, Forall fb_geo FB -> in_block FB a -> nonimg a.
  Proof.
    intros FB a GEO K. apply in_block_In in K as (b & Hb & Rb). (nd_pre (proj1 (Forall_forall _ _) GEO b Hb) 4%nat; intros G1 G2 G3 G4; nd_post).
    split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fb_block_band : forall L RNG st CL FB FL (m : mem) a, AHEAP AI L RNG st (LBof CL FB FL) m -> in_block FB a ->
    (0x603000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP).
  Proof.
    intros L RNG st CL FB FL m a AH K. apply in_block_In in K as (b & Hb & Rb).
    (nd_pre (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) 3%nat; intros _ BR _; nd_post).
    destruct BR as (BAND & _). unfold ablk, AIMG_HI, KLS in BAND. destruct BAND as [[B1 B2]|[B1 B2]]; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma STDIOR_agree : forall l (FB : list cblk) (m m' : mem), STDIOR l FB m -> agrees_on (fun a => stdio_static a \/ in_block FB a) m m' -> STDIOR l FB m'.
  Proof. intros l FB m m' ST AG. eapply STDIOR_agree_dom; [exact ST|]. exact AG. Qed.

  #[using="AF CI_ST1 CI_ST2"] Lemma files_ok : gcomp_ok AI files_comp.
  Proof.
    constructor; cbn [gc_P gc_dom files_comp]; unfold files_P, files_dom.
    - intros L RNG RNG' s s' FB m m' [ST GEO] _ AG EL _ _. rewrite EL. split; [| exact GEO].
      eapply STDIOR_agree; [exact ST|]. intros a Ha [K|K]; apply AG; [exact Ha| left; exact K| exact Ha| right; split; [exact K| exact (fb_geo_nonimg FB a GEO K)]].
    - intros L RNG s FB m LB SP a _ HFB _ _ [K|[K _]].
      + left. right. left. destruct K as [K|K]; [destruct CI_ST1 as (iv & Hiv & I1 & I2)| destruct CI_ST2 as (iv & Hiv & I1 & I2)]; exists iv; (split; [exact Hiv| lia]).
      + left. right. right. left. apply in_block_In in K as (b & Hb & Rb). exists (hb_of b). split; [exact (HFB b Hb)|]. unfold hb_of. cbn [ab_addr ab_size]. exact Rb.
    - intros L RNG s CL FB FL m a AH [_ GEO] Ha [K|[K _]] REG.
      + eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. destruct K; lia.
      + pose proof K as K0. apply in_block_In in K as (b & Hb & Rb). (nd_pre (proj1 (Forall_forall _ _) GEO b Hb) 4%nat; intros G1 G2 G3 G4; nd_post).
        unfold client_reg, client_keeps in REG. destruct REG as [R|[R|[R|R]]].
        * lia.
        * apply in_block_In in R as (b' & Hb' & Rb').
          pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. unfold LBof in ND. apply NoDup_app_remove_r in ND.
          assert (NE : hb_of b' <> hb_of b).
          { intros E. apply hb_of_inj in E. subst b'. rewrite map_app in ND. eapply (NoDup_app_disj _ _ (hb_of b) ND); apply in_map; assumption. }
          destruct (AI_blocks_disjoint AI _ _ _ _ _ (hb_of b') (hb_of b) AH (In_hb CL FB FL b' ltac:(apply in_or_app; left; exact Hb'))
                      (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb)) NE) as [D|D]; unfold hb_of in D; cbn [ab_addr ab_size] in D; lia.
        * apply in_frames_In in R as (fr & Hf & Rf).
          destruct (AI_blocks_disjoint AI _ _ _ _ _ (fkb_of fr) (hb_of b) AH (In_fkb CL FB FL fr Hf) (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))
                      ltac:(unfold fkb_of, hb_of; discriminate)) as [D|D]; unfold fkb_of, hb_of in D; cbn [ab_addr ab_size] in D; lia.
        * destruct (fb_block_band _ _ _ _ _ _ _ _ AH K0) as [X|X]; pose proof atop_range as AR;
          apply in_frame_sh_In in R as (fr & Hf & Rf);
          (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post);
          (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post); unfold AIMG_HI in IMG;
          rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia; rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia; change (2^3) with 8 in Rf;
          clear - Rf IMG TOP X AR F64; Z.div_mod_to_equations; lia.
    - intros L s FB a [K|[_ K]] D; [| exact (nonimg_not_drv a K D)]. destruct D as [D|D]; unfold READ_STAGE in D; [destruct K; lia|].
      pose proof ATPv_img as TI. unfold ATP in D. destruct K; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CI_ENV : Forall (fun k => exists iv, In iv (aci AI) /\ fst iv <= fst k /\ snd k <= snd iv) STDIO_ENV_CELLS.
  Hypothesis AI_block_ahm : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB -> ab_addr b + ab_size b <= AAHMv \/ AAHMv + AAHM_SZ <= ab_addr b.

  Definition ahm_geo : Prop := sclr AAHMv AAHM_SZ /\ (AAHMv + AAHM_SZ <= ATP + -200 \/ ATP + -200 + 504 <= AAHMv).
  (* [comment removed for export] *)
  Definition env_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := stdio_env_P (Z_to_bv 64 (al_V L 45%nat)) RNG m /\ ahm_geo.
  Definition env_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop :=
    in_ranges STDIO_ENV_CELLS a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN) \/ ((AAHMv <= a < AAHMv + AAHM_SZ) /\ nonimg a).
  Definition env_comp : gcomp := mkGC env_P env_dom.

  #[using="Type"] Lemma env_cell_img : forall a, in_ranges STDIO_ENV_CELLS a -> 0xa71e8 <= a < 0x60184c /\ ~ (0x5d0c50 <= a < 0x6015f8) /\ ~ stdio_static a.
  Proof.
    intros a (k & Hk & Rk). unfold STDIO_ENV_CELLS in Hk. unfold stdio_static.
    repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
  Qed.

  #[using="AF CI_ENV AI_block_ahm"] Lemma env_ok : gcomp_ok AI env_comp.
  Proof.
    constructor; cbn [gc_P gc_dom env_comp]; unfold env_P, env_dom.
    - intros L RNG RNG' s s' FB m m' [EP GEO] FP AG _ _ _. split; [| exact GEO].
      eapply stdio_env_agree; [exact EP| exact FP|]. intros a Ha Da. apply AG; [exact Ha|]. unfold stdio_env_dom in Da.
      destruct Da as [D|[D|D]]; [left; exact D| right; left; exact D|]. right. right. split; [exact D|].
      (nd_pre EP 4%nat; intros _ _ (_ & _ & _ & A4 & _) _; nd_post). destruct GEO as [_ G2]. unfold AAHM_SZ in *. split; [lia|]. lia.
    - intros L RNG s FB m LB SP a _ _ _ _ [K|[K|[K _]]].
      + left. right. left. (nd_pre K 3%nat; intros k Hk Rk; nd_post). (nd_pre (proj1 (Forall_forall _ _) CI_ENV k Hk) 4%nat; intros iv Hiv I1 I2; nd_post). exists iv. split; [exact Hiv| lia].
      + right. right. left. exact K.
      + right. right. right. exact K.
    - intros L RNG s CL FB FL m a AH [EP [G1 G2]] Ha [K|[K|[K _]]] REG.
      + destruct (env_cell_img a K) as (B & _). eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      + eapply (imsh_not_client AI AF); [exact AH| exact K| exact REG].
      + (nd_pre EP 4%nat; intros _ _ (_ & _ & _ & A4 & A5 & _) _; nd_post). unfold AHM_BYTES, AAHM_SZ in *.
        unfold client_reg, client_keeps in REG. destruct REG as [R|[R|[R|R]]].
        * lia.
        * apply in_block_In in R as (b & Hb & Rb).
          pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) as D. unfold hb_of, AAHM_SZ in D. cbn [ab_addr ab_size] in D. lia.
        * apply in_frames_In in R as (fr & Hf & Rf).
          pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) as D. unfold fkb_of, AAHM_SZ in D. cbn [ab_addr ab_size] in D. lia.
        * apply in_frame_sh_In in R as (fr & Hf & Rf).
          (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post).
          (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post). unfold AIMG_HI in IMG. pose proof atop_range as AR.
          rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
          unfold sclr, KLS in G1. clear - Rf IMG TOP G1 K AR F64. Z.div_mod_to_equations. lia.
    - intros L s FB a [K|[K|[_ K]]] D.
      + (nd_pre (env_cell_img a K) 3%nat; intros B1 B2 _; nd_post). destruct D as [D|D]; unfold READ_STAGE in D; [lia|]. pose proof ATPv_img as TI. unfold ATP in D. lia.
      + exact (imsh_not_drv a K D).
      + exact (nonimg_not_drv a K D).
  Qed.

  (* [comment removed for export] *)
  Record stdio_indep (c : gcomp) : Prop := mkSI {
    si_P : forall L RNG (s s' : PS) FB FB' (m : mem), gc_P c L RNG s FB m -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s ->
             (forall q A n, ps_outfile s = Some q -> In (q, A, n) FB -> In (q, A, n) FB') -> gc_P c L RNG s' FB' m;
    si_dom : forall L (s s' : PS) FB FB' a, gc_dom c L s' FB' a -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> gc_dom c L s FB a;
    si_static : forall L RNG (s : PS) FB (m : mem) a, gc_P c L RNG s FB m -> gc_dom c L s FB a -> ~ stdio_static a;
    si_blocks : forall L RNG (s : PS) CL FB FL (m : mem) a,
        AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gc_P c L RNG s FB m -> 0 <= a < 2^64 -> gc_dom c L s FB a -> ~ in_block FB a }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CI_ST1 CI_ST2"] Lemma stdio_iv_arange : forall L RNG st CL FB FL (m : mem) (BL : list cblk) SP iv, AHEAP AI L RNG st (LBof CL FB FL) m ->
    (forall b, In b BL -> In b (CL ++ FB)) -> stdio_ivA BL SP iv ->
    aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
    \/ aahm_client (fst iv) (snd iv - fst iv).
  Proof.
    intros L RNG st CL FB FL m BL SP [lo hi] AH HBL K. cbn [fst snd] in *. unfold stdio_ivA in K. cbn [fst snd] in K.
    destruct K as [[K1 K2]|[K|[[K1 K2]|[[K1 K2]|[K1 K2]]]]].
    - left. left. left. exact K1.
    - left. right. left. unfold iv_in_block in K. apply Exists_exists in K as (b & Hb & H1 & H2). cbn [fst snd] in H1, H2.
      exists (hb_of b). split; [apply In_hb; apply HBL; exact Hb|]. unfold hb_of. cbn [ab_addr ab_size]. lia.
    - left. left. right. left. destruct CI_ST1 as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - left. left. right. left. destruct CI_ST2 as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - right. left. unfold atls_client, ATP in *. left. lia.
  Qed.

  #[using="Type"] Lemma cloc_iv_client : forall FL (CL : list cblk) iv, clocA FL CL (fst iv) (snd iv - fst iv) -> client_ivA FL CL iv.
  Proof.
    intros FL CL [lo hi] K. cbn [fst snd] in *. destruct K as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - right. left. unfold iv_in_block. apply Exists_exists. exists b. split; [exact Hb|]. cbn [fst snd]. lia.
    - right. right. left. unfold iv_in_frames. apply Exists_exists. exists fr. split; [exact Hf|]. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma indep_outside : forall c, gcomp_ok AI c -> stdio_indep c -> forall L RNG (s : PS) CL FB FL (m : mem) (X : list cblk) SP W WX a,
    AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gc_P c L RNG s FB m -> 0 <= a < 2^64 -> gc_dom c L s FB a ->
    incl X CL -> Forall (stdio_ivA (X ++ FB) SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX -> outside (W ++ WX) a.
  Proof.
    intros c OK SI L RNG s CL FB FL m X SP W WX a AH PC Ha Da HX FW FX.
    pose proof (gk_client AI c OK _ _ _ _ _ _ _ _ AH PC Ha Da) as NC.
    apply outside_app2; apply outside_of; intros iv Hi Ra.
    - pose proof (proj1 (Forall_forall _ _) FW iv Hi) as K. unfold stdio_ivA in K.
      destruct K as [[K1 K2]|[K|[[K1 K2]|[[K1 K2]|[K1 K2]]]]].
      + apply NC. left. lia.
      + unfold iv_in_block in K. apply Exists_app in K as [K|K]; apply Exists_exists in K as (b & Hb & H1 & H2).
        * apply NC. right. left. apply in_block_In. exists b. split; [apply HX; exact Hb| lia].
        * apply (si_blocks c SI _ _ _ _ _ _ _ _ AH PC Ha Da). apply in_block_In. exists b. split; [exact Hb| lia].
      + apply (si_static c SI _ _ _ _ _ _ PC Da). left. lia.
      + apply (si_static c SI _ _ _ _ _ _ PC Da). right. lia.
      + apply (gk_drv AI c OK _ _ _ _ Da). right. lia.
    - apply NC. eapply client_iv_reg; [apply cloc_iv_client; exact (proj1 (Forall_forall _ _) FX iv Hi)| exact Ra].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma comps_step : forall cs, Forall (gcomp_ok AI) cs -> Forall stdio_indep cs -> forall L RNG (s s' : PS) CL FB FB' FL (m m' : mem) (X : list cblk) SP W WX,
    AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gconj cs L RNG s FB m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
    incl X CL -> Forall (stdio_ivA (X ++ FB) SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX ->
    ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> (forall q A n, ps_outfile s = Some q -> In (q, A, n) FB -> In (q, A, n) FB') ->
    gconj cs L RNG s' FB' m'.
  Proof.
    intros cs OKs SIs L RNG s s' CL FB FB' FL m m' X SP W WX AH GC MU WM HX FW FX E1 E2 HFB.
    eapply gconj_map; [exact GC|]. intros c Hc PC.
    pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. pose proof (proj1 (Forall_forall _ _) SIs c Hc) as SI.
    apply (si_P c SI L RNG s s' FB FB' m'); [| exact E1| exact E2| exact HFB].
    eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
    apply (agrees_on_of_munch _ (W ++ WX)); [exact MU| exact WM|]. intros a Ha Da.
    eapply (indep_outside c OK SI); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Laws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis INDEP : Forall stdio_indep (cs1 ++ cs2).
    #[local] Notation GSTAT := (GSTAT_of (cs1 ++ files_comp :: cs2)).
    #[local] Notation GIOA := (GIOA_real AI GSTAT).

    #[using="Type"] Lemma gs_stdio_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> STDIOR (ps_libc s) FB m.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 (proj1 GC)). Qed.

    #[using="Type"] Lemma gs_errno_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> exists e : word, rw_cells asegs m (ATP + -164) [C4 e].
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (ERR & _)). exact ERR. Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Lemma stdio_core : forall L RNG (s : PS) CL FB FB' FL (m m' : mem) (X : list cblk) W WX SP l',
      GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
      incl X CL -> Forall (stdio_ivA (X ++ FB) SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX ->
      (forall q A n, ps_outfile s = Some q -> In (q, A, n) FB -> In (q, A, n) FB') ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) -> STDIOR l' FB' m' -> (forall b, In b FB' -> In b (CL ++ FB)) ->
      AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m' /\ GSTAT L RNG (set_libc l' s) FB' m'.
    Proof.
      intros L RNG s CL FB FB' FL m m' X W WX SP l' G MU WM HX FW FX HFB ERR' ST' HIN.
      (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [_ GC2].
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in INDEP as [IN1 IN2].
      split.
      - eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. apply Forall_app. split.
        + eapply Forall_impl; [| exact FW]. intros iv K. eapply (stdio_iv_arange _ _ _ CL FB FL m (X ++ FB)); [exact AH| | exact K].
          intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; apply HX; exact Hb| right; exact Hb].
        + eapply Forall_impl; [| exact FX]. intros iv K. left. eapply (client_iv_arange AI AF); [exact G| apply cloc_iv_client; exact K].
      - split; [exact ERR'|]. apply gconj_app. split.
        + eapply (comps_step cs1 OK1 IN1 L RNG s (set_libc l' s) CL FB FB' FL m m' X SP W WX); try eassumption; reflexivity.
        + cbn [gconj]. split; [cbn [gc_P files_comp]; unfold files_P; cbn [ps_libc set_libc]; split; [exact ST'|];
                                apply Forall_forall; intros b Hb; exact (fb_geo_of_heap _ _ _ _ _ _ _ b AH (HIN b Hb))|].
          eapply (comps_step cs2 OK2 IN2 L RNG s (set_libc l' s) CL FB FB' FL m m' X SP W WX); try eassumption; reflexivity.
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Theorem gs_step_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W WX SP l',
      GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
      Forall (stdio_ivA FB SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX -> ATOP + 4096 <= SP ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
      STDIOR l' FB m' -> GIOA L RNG (set_libc l' s) CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W WX SP l' G MU WM FW FX HSP ERR' ST'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND _; nd_post).
      destruct (stdio_core L RNG s CL FB FB FL m m' [] W WX SP l' G MU WM ltac:(intros b []) FW FX ltac:(intros q A n _ H; exact H) ERR' ST' ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [AH' GS'].
      split; [exact AH'|]. split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS'].
    Qed.

    #[using="Type"] Lemma perm_adopt : forall (b0 : cblk) CL FB FL, Permutation (LBof (b0 :: CL) FB FL) (LBof CL (b0 :: FB) FL).
    Proof.
      intros b0 CL FB FL. unfold LBof. apply Permutation_app_tail. apply Permutation_map. cbn [app]. apply Permutation_middle.
    Qed.
    #[using="Type"] Lemma perm_release : forall (b0 : cblk) CL F1 F2 FL, Permutation (LBof CL (F1 ++ b0 :: F2) FL) (LBof (b0 :: CL) (F1 ++ F2) FL).
    Proof.
      intros b0 CL F1 F2 FL. unfold LBof. apply Permutation_app_tail. apply Permutation_map. cbn [app].
      rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Theorem gs_adopt_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W SP l' (q : aptr) A,
      GIOA L RNG s ((q, A, FILE_ALLOC) :: CL) FB FL m -> munch W m m' -> wmono asegs m m' ->
      Forall (stdio_ivA ((q, A, FILE_ALLOC) :: FB) SP) W -> ATOP + 4096 <= SP ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
      STDIOR l' ((q, A, FILE_ALLOC) :: FB) m' ->
      GIOA L RNG (set_libc l' s) CL ((q, A, FILE_ALLOC) :: FB) FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W SP l' q A G MU WM FW HSP ERR' ST'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND _; nd_post).
      destruct (stdio_core L RNG s ((q, A, FILE_ALLOC) :: CL) FB ((q, A, FILE_ALLOC) :: FB) FL m m' [(q, A, FILE_ALLOC)] W [] SP l' G
                  ltac:(rewrite app_nil_r; exact MU) WM ltac:(intros b [<-|[]]; left; reflexivity) FW ltac:(constructor)
                  ltac:(intros q0 A0 n0 _ H; right; exact H) ERR' ST'
                  ltac:(intros b [<-|Hb]; [left; reflexivity| right; apply in_or_app; right; exact Hb])) as [AH' GS'].
      split. { cbn [ps_heap set_libc]. eapply (AI_perm AI); [apply perm_adopt| exact AH']. }
      split; [exact RV|]. split.
      { intros b Hb. apply AD. apply in_app_or in Hb as [Hb|[<-|Hb]]; [right; apply in_or_app; left; exact Hb| left; reflexivity| right; apply in_or_app; right; exact Hb]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS'].
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Theorem gs_release_real : forall L RNG (s : PS) CL F1 F2 FL (m m' : mem) W SP l' (q : aptr) A,
      GIOA L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) FL m -> munch W m m' -> wmono asegs m m' ->
      Forall (stdio_ivA (F1 ++ (q, A, FILE_ALLOC) :: F2) SP) W -> ATOP + 4096 <= SP ->
      ps_outfile s <> Some q ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
      STDIOR l' (F1 ++ F2) m' ->
      GIOA L RNG (set_libc l' s) ((q, A, FILE_ALLOC) :: CL) (F1 ++ F2) FL m'.
    Proof.
      intros L RNG s CL F1 F2 FL m m' W SP l' q A G MU WM FW HSP NQ ERR' ST'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND _; nd_post).
      destruct (stdio_core L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) (F1 ++ F2) FL m m' [] W [] SP l' G
                  ltac:(rewrite app_nil_r; exact MU) WM ltac:(intros b []) FW ltac:(constructor)
                  ltac:(intros q0 A0 n0 EQ H; apply in_app_or in H as [H|[H|H]]; [apply in_or_app; left; exact H| exfalso; apply NQ; rewrite EQ; congruence| apply in_or_app; right; exact H])
                  ERR' ST' ltac:(intros b Hb; apply in_or_app; right; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb])) as [AH' GS'].
      split. { cbn [ps_heap set_libc]. eapply (AI_perm AI); [apply perm_release| exact AH']. }
      split; [exact RV|]. split.
      { intros b Hb. apply AD. destruct Hb as [<-|Hb]; [apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
        apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
        apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS'].
    Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls"] Theorem gs_keeps_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W WX SP,
      GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
      Forall (stdio_ivA FB SP) W -> ATOP + 4096 <= SP ->
      agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m m'.
    Proof.
      intros L RNG s CL FB FL m m' W WX SP G MU WM FW HSP.
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [K OX]. apply outside_app2; [| exact OX]. clear MU OX WX.
      pose proof G as (AH & _).
      pose proof (gr_apart AI GSTAT _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (_ & _ & BX).
      assert (GB : forall b, In b (CL ++ FB) -> ablk (cb_addr b) (cb_addr b + cb_size b))
        by (intros b Hb; exact (proj1 (geo_block AI GSTAT _ _ _ _ _ _ _ _ G Hb))).
      assert (GF : forall fr, In fr FL -> ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr mod 64 = 0 /\ fb_size fr mod 64 = 0 /\ 64 <= fb_size fr)
        by (intros fr Hf; exact (geo_frame AI AF GSTAT _ _ _ _ _ _ _ _ G Hf)).
      assert (REG : client_reg FL CL a).
      { unfold client_reg, client_keeps in *. destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
      atop_facts.
      apply outside_of. intros [lo hi] Hi Hin. cbn [fst snd] in Hin.
      pose proof (proj1 (Forall_forall _ _) FW _ Hi) as Hiv. unfold stdio_ivA in Hiv. cbn [fst snd] in Hiv.
      assert (KA : SP <= a
                   \/ (exists b, In b CL /\ cb_addr b <= a < cb_addr b + cb_size b)
                   \/ (exists fr, In fr FL /\ fb_addr fr <= a < fb_addr fr + fb_size fr)
                   \/ (exists fr, In fr FL /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3)).
      { destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; apply in_block_In; exact K| right; right; left; apply in_frames_In; exact K
                                     | right; right; right; apply in_frame_sh_In; exact K]. }
      assert (BANDa : forall F n, ablk F (F + n) -> F <= a < F + n -> ~ (KLS <= a < 0x10007fff8000)) by (intros F n B R X; exact (ablk_clear_band _ _ a B X R)).
      destruct Hiv as [[I1 I2]|[Hiv|[[I1 I2]|[[I1 I2]|[I1 I2]]]]].
      - (* [comment removed for export] *)
        destruct KA as [KK|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
        + (pose proof (ablk_lin _ _ (GB b ltac:(apply in_or_app; left; exact Hb))) as ndP__; nd_pre ndP__ 4%nat; intros _ _ T _; nd_post). lia.
        + destruct (GF fr Hf) as (B & _). (pose proof (ablk_lin _ _ B) as ndP__; nd_pre ndP__ 4%nat; intros _ _ T _; nd_post). lia.
        + (nd_pre (GF fr Hf) 4%nat; intros B A64 N64 N0; nd_post).
          pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R). lia.
      - (* [comment removed for export] *)
        unfold iv_in_block in Hiv. apply Exists_exists in Hiv as (b' & Hb' & H1 & H2). cbn [fst snd] in H1, H2.
        pose proof (GB b' ltac:(apply in_or_app; right; exact Hb')) as B'. (pose proof (ablk_lin _ _ B') as ndP__; nd_pre ndP__ 4%nat; intros _ _ T' _; nd_post).
        destruct KA as [KK|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
        + pose proof (BX b b' Hb Hb') as AP. unfold apart in AP. lia.
        + apply (gr_fr_apart AI GSTAT _ _ _ _ _ _ _ a G); [apply in_frames_In; exists fr; split; [exact Hf| exact R]|].
          apply in_block_In. exists b'. split; [apply in_or_app; right; exact Hb'| lia].
        + (nd_pre (GF fr Hf) 4%nat; intros B A64 N64 N0; nd_post).
          pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R) as SB.
          apply (BANDa _ _ B' ltac:(lia)). exact SB.
      - (* [comment removed for export] *)
        eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      - (* [comment removed for export] *)
        eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      - (* [comment removed for export] *)
        eapply (tls_not_client AI AF AI_block_tls); [exact AH| | exact REG]. lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis IN_ENV : In env_comp (cs1 ++ cs2).
    Hypothesis IN_GLOBALS : In globals_comp (cs1 ++ cs2).
    Hypothesis IN_STACKSH : In stacksh_comp (cs1 ++ cs2).
    (* [comment removed for export] *)
    Hypothesis AI_ssc : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rt_ssc m.

    #[using="Type"] Lemma in_cs : forall c, In c (cs1 ++ cs2) -> In c (cs1 ++ files_comp :: cs2).
    Proof. intros c Hc. apply in_app_or in Hc as [Hc|Hc]; apply in_or_app; [left; exact Hc| right; right; exact Hc]. Qed.
    #[using="IN_ENV"] Lemma g_env : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> stdio_env_P (Z_to_bv 64 (al_V L 45%nat)) RNG m.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). exact (proj1 (gconj_In _ _ _ _ _ _ _ GC (in_cs _ IN_ENV))). Qed.
    #[using="IN_GLOBALS"] Lemma g_win : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> wr_at asegs m 0x7fffa000 779776.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). exact (proj1 (gconj_In _ _ _ _ _ _ _ GC (in_cs _ IN_GLOBALS))). Qed.

    #[using="IN_ENV"] Lemma gs_ssp_real : forall L, exists canary : word, forall RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> ssp_cells m canary.
    Proof.
      intros L. exists (Z_to_bv 64 (al_V L 45%nat)). intros RNG s CL FB FL m G. pose proof G as (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      eapply stdio_env_ssp; [exact (g_env _ _ _ _ _ _ _ G)|].
      apply (relro_word m _ _ RO); [unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.got_ssp, ARELRO_LO; lia| unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.got_ssp, ARELRO_HI; lia| vm_compute; reflexivity].
    Qed.

    #[using="IN_ENV AI_ssc"] Lemma gs_env_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> icptenv m.
    Proof.
      intros L RNG s CL FB FL m G. pose proof G as (AH & _). pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. pose proof (AI_ssc _ _ _ _ _ AH) as SSC.
      (nd_pre RT 22%nat; intros _ R2 R3 R4 R5 _ R7 R8 _ _ _ _ _ R14 R15 R16 R17 R18 R19 R20 R21 _; nd_post).
      eapply stdio_env_icptenv; [exact (g_env _ _ _ _ _ _ _ G)| exact R2| exact R3| exact R5| exact R7| exact R8| exact R4| exact R16| exact R14
                               | exact R15| exact R19| exact R17| exact R18| exact R21| exact SSC].
    Qed.

    #[using="Type"] Lemma gs_ckpf_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> rw_cells asegs m 0x140178 [C8 (Z_to_bv 64 4294967296)].
    Proof.
      intros L RNG s CL FB FL m (AH & _). pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
      (nd_pre RT 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R20 _; nd_post). exact R20.
    Qed.

    #[using="IN_STACKSH"] Lemma gs_stack_real : forall L RNG (s : PS) CL FB FL (m : mem) lo hi, GIOA L RNG s CL FB FL m ->
      ATOP + 4096 <= lo -> lo <= hi -> hi <= al_top L -> hi + 8 <= 2^47 -> sobj RNG m lo hi.
    Proof.
      intros L RNG s CL FB FL m lo hi G H1 H2 H3 H4. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (_ & GC); nd_post).
      pose proof (gconj_In _ _ _ _ _ _ _ GC (in_cs _ IN_STACKSH)) as SP. cbn [gc_P stacksh_comp] in SP.
      destruct (stacksh_use L RNG s FB m lo (hi - lo) SP H1 ltac:(lia) ltac:(lia)) as [U (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & WR & RG)].
      replace (lo + (hi - lo)) with hi in * by lia.
      (nd_pre (AI_layout AI _ _ _ _ _ AH) 5%nat; intros T1 _ _ T4 _; nd_post). pose proof atop_range as AR.
      split. { split; [exact H2|]. right. unfold KHIGH, KEND. change (2^47) with 140737488355328 in H4. lia. }
      split; [exact U|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption.
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 AI_block_ahm CSOK INDEP IN_ENV IN_GLOBALS IN_STACKSH AI_ssc"] Theorem gia_stdio_laws_real : gia_stdio_laws GIOA.
    Proof.
      constructor.
      - exact gs_stdio_real.
      - exact gs_ssp_real.
      - exact gs_errno_real.
      - exact gs_env_real.
      - exact gs_ckpf_real.
      - intros L RNG s CL FB FL m G. exact (stdio_env_libc _ _ _ (g_env _ _ _ _ _ _ _ G)).   (* [comment removed for export] *)
      - intros L RNG s CL FB FL m G. exact (stdio_env_rng0 _ _ _ (g_env _ _ _ _ _ _ _ G)).
      - exact gs_stack_real.
      - intros L RNG s CL FB FL m lo hi G RI RS HR LE. exact (stdio_env_rodata _ _ _ lo hi (g_env _ _ _ _ _ _ _ G) (g_win _ _ _ _ _ _ _ G) RI RS HR LE).
      - intros L RNG s CL FB FL m G RI RS. exact (stdio_env_statics _ _ _ (g_env _ _ _ _ _ _ _ G) (g_win _ _ _ _ _ _ _ G) RI RS).
      - (* [comment removed for export] *)
        intros L RNG s CL FB FL m G. pose proof G as (AH & _).
        (nd_pre (g_env _ _ _ _ _ _ _ G) 4%nat; intros _ _ (AH1 & AH2 & AH3 & AH4 & AH5 & AH6) _; nd_post).
        exists AAHMv. split; [exact AH1|]. split; [exact AH3|]. split; [exact AH4|]. split; [exact AH5|]. split; [exact AH6|]. split; [exact AH2|].
        intros b Hb. pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_hb CL FB FL b Hb)) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D.
        unfold AHM_BYTES. unfold AAHM_SZ in D. exact D.
      - exact gs_step_real.
      - exact gs_keeps_real.
      - exact gs_adopt_real.
      - exact gs_release_real.
    Qed.
  End Laws.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma indep_const : forall (P : alayout -> footprint -> mem -> Prop) (D : alayout -> Z -> Prop),
    (forall L a, D L a -> ~ stdio_static a) ->
    (forall L a, D L a -> ~ ((0x603000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP))) ->
    stdio_indep (mkGC (fun L RNG _ _ m => P L RNG m) (fun L _ _ a => D L a)).
  Proof.
    intros P D HS HB. constructor; cbn [gc_P gc_dom].
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da. exact (HS L a Da).
    - intros L RNG s CL FB FL m a AH _ _ Da K. exact (HB L a Da (fb_block_band _ _ _ _ _ _ _ _ AH K)).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma indep_of_band : forall (c : gcomp),
    (forall L RNG (s s' : PS) FB FB' (m : mem), gc_P c L RNG s FB m -> gc_P c L RNG s' FB' m) ->
    (forall L (s s' : PS) FB FB' a, gc_dom c L s' FB' a -> gc_dom c L s FB a) ->
    (forall L (s : PS) FB a, gc_dom c L s FB a -> 2147450880 <= a < 0x10007fff8000) -> stdio_indep c.
  Proof.
    intros c HP HD BAND. constructor.
    - intros L RNG s s' FB FB' m PC _ _ _. exact (HP _ _ _ _ _ _ _ PC).
    - intros L s s' FB FB' a Da _ _. exact (HD _ _ _ _ _ _ Da).
    - intros L RNG s FB m a _ Da [X|X]; pose proof (BAND L s FB a Da) as B; clear - B X; lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. pose proof (BAND L s FB a Da) as B. pose proof atop_range as AR.
      destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; clear - B X AR; lia.
  Qed.

  #[using="Type"] Lemma args_indep : forall USP n, ATOP + 64 <= USP -> 0 <= n -> USP + n + 8 <= 2^47 -> stdio_indep (args_comp USP n).
  Proof.
    intros USP n G1 G2 G3. apply indep_of_band; cbn [gc_P gc_dom args_comp].
    - intros L RNG s s' FB FB' m HP. exact HP.
    - intros L s s' FB FB' a Da. exact Da.
    - intros L s FB a Da. destruct (args_dom_band USP n G1 G3 a Da) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma unp_indep : stdio_indep unp_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom unp_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. unfold unp_dom, AIMSH_LO, AIMSH_LEN in Da. lia.
  Qed.
  #[using="Type"] Lemma globals_indep : stdio_indep globals_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom globals_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia.
  Qed.
  #[using="Type"] Lemma stdinp_indep : stdio_indep stdinp_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom stdinp_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia.
  Qed.
  #[using="Type"] Lemma stacksh_indep : stdio_indep stacksh_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom stacksh_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a [Da D47]. destruct (stacksh_band L a Da D47) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma tlsobj_indep : stdio_indep tlsobj_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom tlsobj_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. destruct (tlsobj_band a Da) as (B & _). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI_block_tls"] Lemma exitci_indep : stdio_indep exitci_comp.
  Proof.
    constructor; cbn [gc_P gc_dom exitci_comp].
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da [X|X]; unfold exitci_dom, exit_dom in Da; destruct Da as [D|[(k & Hk & Rk)|D]].
      all: try (pose proof ATPv_img as TI; lia).
      all: try (unfold AIMSH_LO, AIMSH_LEN in D; lia).
      all: unfold EXIT_CI_KEEP in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]); destruct Hk.
    - intros L RNG s CL FB FL m a AH _ _ Da K. unfold exitci_dom, exit_dom in Da. destruct Da as [D|[(k & Hk & Rk)|D]].
      + apply in_block_In in K as (b & Hb & Rb).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as T. unfold hb_of in T. cbn [ab_addr ab_size] in T.
        unfold ATP in T. lia.
      + destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR;
          unfold EXIT_CI_KEEP in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]); destruct Hk.
      + destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; unfold AIMSH_LO, AIMSH_LEN in D; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma harn_stdio_indep : stdio_indep harn_comp.
  Proof.
    constructor; cbn [gc_P gc_dom harn_comp]; unfold harn_P, harn_dom.
    - intros L RNG s s' FB FB' m HP EO _ HFB. rewrite EO. destruct (ps_outfile s) as [q|] eqn:E; [| exact HP].
      (nd_pre HP 3%nat; intros A HA HC; nd_post). exists A. split; [exact (HFB q A _ eq_refl HA)| exact HC].
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da [X|X]; unfold OUTFILE_ADDR in Da; lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; unfold OUTFILE_ADDR in Da; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI_block_ahm"] Lemma env_indep : stdio_indep env_comp.
  Proof.
    constructor; cbn [gc_P gc_dom env_comp]; unfold env_P, env_dom.
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a [EP _] [K|[K|[K _]]] X.
      + exact (proj2 (proj2 (env_cell_img a K)) X).
      + unfold AIMSH_LO, AIMSH_LEN in K. destruct X; lia.
      + (nd_pre EP 4%nat; intros _ _ (_ & _ & _ & A4 & _) _; nd_post). destruct X; lia.
    - intros L RNG s CL FB FL m a AH _ _ [K|[K|[K _]]] B.
      + destruct (env_cell_img a K) as (I1 & _). destruct (fb_block_band _ _ _ _ _ _ _ _ AH B); lia.
      + unfold AIMSH_LO, AIMSH_LEN in K. pose proof atop_range as AR. destruct (fb_block_band _ _ _ _ _ _ _ _ AH B); lia.
      + apply in_block_In in B as (b & Hb & Rb).
        pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma files_harn_indep : harn_indep files_comp.
  Proof.
    split; cbn [gc_P gc_dom files_comp]; unfold files_P, files_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a [K|[_ [K _]]] R; unfold OUTFILE_ADDR in R; [destruct K; lia| lia].
  Qed.
  #[using="Type"] Lemma env_harn_indep : harn_indep env_comp.
  Proof.
    split; cbn [gc_P gc_dom env_comp]; unfold env_P, env_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a [K|[K|[_ [K _]]]] R; unfold OUTFILE_ADDR in R.
      + (nd_pre K 3%nat; intros k Hk Rk; nd_post). unfold STDIO_ENV_CELLS in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
      + unfold AIMSH_LO, AIMSH_LEN in K. lia.
      + lia.
  Qed.
End StdioInst.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section StdioInst.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  (* [comment removed for export] *)
  Hypothesis CI_ST1 : exists iv, In iv (aci AI) /\ fst iv <= 0xa9e90 /\ 0xaa160 <= snd iv.
  Hypothesis CI_ST2 : exists iv, In iv (aci AI) /\ fst iv <= 0x6020a8 /\ 0x6028d0 <= snd iv.

  (* [comment removed for export] *)
  Definition fb_geo (b : cblk) : Prop :=
    0x604000 <= cb_addr b /\ 0 <= cb_size b /\ cb_addr b + cb_size b <= ATOP
    /\ (cb_addr b + cb_size b <= ATP + -200 \/ ATP + -200 + 504 <= cb_addr b).
  Definition files_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := STDIOR (ps_libc s) FB m /\ Forall fb_geo FB.
  (* [comment removed for export] *)
  Definition nonimg (a : Z) : Prop := 0x604000 <= a /\ ~ (ATP + -200 <= a < ATP + -200 + 504).
  #[using="Type"] Lemma nonimg_not_drv : forall a, nonimg a -> ~ drv_static a.
  Proof. intros a [N1 N2] [D|D]; unfold READ_STAGE in *; lia. Qed.
  Definition files_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := stdio_static a \/ (in_block FB a /\ nonimg a).
  Definition files_comp : gcomp := mkGC files_P files_dom.

  #[using="AI_block_tls"] Lemma fb_geo_of_heap : forall L RNG st CL FB FL (m : mem) b, AHEAP AI L RNG st (LBof CL FB FL) m -> In b (CL ++ FB) -> fb_geo b.
  Proof.
    intros L RNG st CL FB FL m b AH Hb. pose proof (In_hb CL FB FL b Hb) as HI.
    (nd_pre (AI_block_bounds AI _ _ _ _ _ _ AH HI) 3%nat; intros B1 B2 B3; nd_post). pose proof (AI_block_tls _ _ _ _ _ _ AH HI) as T.
    unfold hb_of, AIMG_HI in *. cbn [ab_addr ab_size] in *. unfold fb_geo. split; [exact B1|]. split; [exact B2|]. split; [exact B3| exact T].
  Qed.
  #[using="Type"] Lemma fb_geo_nonimg : forall (FB : list cblk) a, Forall fb_geo FB -> in_block FB a -> nonimg a.
  Proof.
    intros FB a GEO K. apply in_block_In in K as (b & Hb & Rb). (nd_pre (proj1 (Forall_forall _ _) GEO b Hb) 4%nat; intros G1 G2 G3 G4; nd_post).
    split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fb_block_band : forall L RNG st CL FB FL (m : mem) a, AHEAP AI L RNG st (LBof CL FB FL) m -> in_block FB a ->
    (0x604000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP).
  Proof.
    intros L RNG st CL FB FL m a AH K. apply in_block_In in K as (b & Hb & Rb).
    (nd_pre (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) 3%nat; intros _ BR _; nd_post).
    destruct BR as (BAND & _). unfold ablk, AIMG_HI, KLS in BAND. destruct BAND as [[B1 B2]|[B1 B2]]; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma STDIOR_agree : forall l (FB : list cblk) (m m' : mem), STDIOR l FB m -> agrees_on (fun a => stdio_static a \/ in_block FB a) m m' -> STDIOR l FB m'.
  Proof. intros l FB m m' ST AG. eapply STDIOR_agree_dom; [exact ST|]. exact AG. Qed.

  #[using="AF CI_ST1 CI_ST2"] Lemma files_ok : gcomp_ok AI files_comp.
  Proof.
    constructor; cbn [gc_P gc_dom files_comp]; unfold files_P, files_dom.
    - intros L RNG RNG' s s' FB m m' [ST GEO] _ AG EL _ _. rewrite EL. split; [| exact GEO].
      eapply STDIOR_agree; [exact ST|]. intros a Ha [K|K]; apply AG; [exact Ha| left; exact K| exact Ha| right; split; [exact K| exact (fb_geo_nonimg FB a GEO K)]].
    - intros L RNG s FB m LB SP a _ HFB _ _ [K|[K _]].
      + left. right. left. destruct K as [K|K]; [destruct CI_ST1 as (iv & Hiv & I1 & I2)| destruct CI_ST2 as (iv & Hiv & I1 & I2)]; exists iv; (split; [exact Hiv| lia]).
      + left. right. right. left. apply in_block_In in K as (b & Hb & Rb). exists (hb_of b). split; [exact (HFB b Hb)|]. unfold hb_of. cbn [ab_addr ab_size]. exact Rb.
    - intros L RNG s CL FB FL m a AH [_ GEO] Ha [K|[K _]] REG.
      + eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. destruct K; lia.
      + pose proof K as K0. apply in_block_In in K as (b & Hb & Rb). (nd_pre (proj1 (Forall_forall _ _) GEO b Hb) 4%nat; intros G1 G2 G3 G4; nd_post).
        unfold client_reg, client_keeps in REG. destruct REG as [R|[R|[R|R]]].
        * lia.
        * apply in_block_In in R as (b' & Hb' & Rb').
          pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. unfold LBof in ND. apply NoDup_app_remove_r in ND.
          assert (NE : hb_of b' <> hb_of b).
          { intros E. apply hb_of_inj in E. subst b'. rewrite map_app in ND. eapply (NoDup_app_disj _ _ (hb_of b) ND); apply in_map; assumption. }
          destruct (AI_blocks_disjoint AI _ _ _ _ _ (hb_of b') (hb_of b) AH (In_hb CL FB FL b' ltac:(apply in_or_app; left; exact Hb'))
                      (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb)) NE) as [D|D]; unfold hb_of in D; cbn [ab_addr ab_size] in D; lia.
        * apply in_frames_In in R as (fr & Hf & Rf).
          destruct (AI_blocks_disjoint AI _ _ _ _ _ (fkb_of fr) (hb_of b) AH (In_fkb CL FB FL fr Hf) (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))
                      ltac:(unfold fkb_of, hb_of; discriminate)) as [D|D]; unfold fkb_of, hb_of in D; cbn [ab_addr ab_size] in D; lia.
        * destruct (fb_block_band _ _ _ _ _ _ _ _ AH K0) as [X|X]; pose proof atop_range as AR;
          apply in_frame_sh_In in R as (fr & Hf & Rf);
          (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post);
          (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post); unfold AIMG_HI in IMG;
          rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia; rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia; change (2^3) with 8 in Rf;
          clear - Rf IMG TOP X AR F64; Z.div_mod_to_equations; lia.
    - intros L s FB a [K|[_ K]] D; [| exact (nonimg_not_drv a K D)]. destruct D as [D|D]; unfold READ_STAGE in D; [destruct K; lia|].
      pose proof ATPv_img as TI. unfold ATP in D. destruct K; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CI_ENV : Forall (fun k => exists iv, In iv (aci AI) /\ fst iv <= fst k /\ snd k <= snd iv) STDIO_ENV_CELLS.
  Hypothesis AI_block_ahm : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB -> ab_addr b + ab_size b <= AAHMv \/ AAHMv + AAHM_SZ <= ab_addr b.

  Definition ahm_geo : Prop := sclr AAHMv AAHM_SZ /\ (AAHMv + AAHM_SZ <= ATP + -200 \/ ATP + -200 + 504 <= AAHMv).
  (* [comment removed for export] *)
  Definition env_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := stdio_env_P (Z_to_bv 64 (al_V L 45%nat)) RNG m /\ ahm_geo.
  Definition env_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop :=
    in_ranges STDIO_ENV_CELLS a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN) \/ ((AAHMv <= a < AAHMv + AAHM_SZ) /\ nonimg a).
  Definition env_comp : gcomp := mkGC env_P env_dom.

  #[using="Type"] Lemma env_cell_img : forall a, in_ranges STDIO_ENV_CELLS a -> 0xa75c8 <= a < 0x601c4c /\ ~ (0x5d1050 <= a < 0x6019f8) /\ ~ stdio_static a.
  Proof.
    intros a (k & Hk & Rk). unfold STDIO_ENV_CELLS in Hk. unfold stdio_static.
    repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
  Qed.

  #[using="AF CI_ENV AI_block_ahm"] Lemma env_ok : gcomp_ok AI env_comp.
  Proof.
    constructor; cbn [gc_P gc_dom env_comp]; unfold env_P, env_dom.
    - intros L RNG RNG' s s' FB m m' [EP GEO] FP AG _ _ _. split; [| exact GEO].
      eapply stdio_env_agree; [exact EP| exact FP|]. intros a Ha Da. apply AG; [exact Ha|]. unfold stdio_env_dom in Da.
      destruct Da as [D|[D|D]]; [left; exact D| right; left; exact D|]. right. right. split; [exact D|].
      (nd_pre EP 4%nat; intros _ _ (_ & _ & _ & A4 & _) _; nd_post). destruct GEO as [_ G2]. unfold AAHM_SZ in *. split; [lia|]. lia.
    - intros L RNG s FB m LB SP a _ _ _ _ [K|[K|[K _]]].
      + left. right. left. (nd_pre K 3%nat; intros k Hk Rk; nd_post). (nd_pre (proj1 (Forall_forall _ _) CI_ENV k Hk) 4%nat; intros iv Hiv I1 I2; nd_post). exists iv. split; [exact Hiv| lia].
      + right. right. left. exact K.
      + right. right. right. exact K.
    - intros L RNG s CL FB FL m a AH [EP [G1 G2]] Ha [K|[K|[K _]]] REG.
      + destruct (env_cell_img a K) as (B & _). eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      + eapply (imsh_not_client AI AF); [exact AH| exact K| exact REG].
      + (nd_pre EP 4%nat; intros _ _ (_ & _ & _ & A4 & A5 & _) _; nd_post). unfold AHM_BYTES, AAHM_SZ in *.
        unfold client_reg, client_keeps in REG. destruct REG as [R|[R|[R|R]]].
        * lia.
        * apply in_block_In in R as (b & Hb & Rb).
          pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) as D. unfold hb_of, AAHM_SZ in D. cbn [ab_addr ab_size] in D. lia.
        * apply in_frames_In in R as (fr & Hf & Rf).
          pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) as D. unfold fkb_of, AAHM_SZ in D. cbn [ab_addr ab_size] in D. lia.
        * apply in_frame_sh_In in R as (fr & Hf & Rf).
          (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post).
          (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post). unfold AIMG_HI in IMG. pose proof atop_range as AR.
          rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
          unfold sclr, KLS in G1. clear - Rf IMG TOP G1 K AR F64. Z.div_mod_to_equations. lia.
    - intros L s FB a [K|[K|[_ K]]] D.
      + (nd_pre (env_cell_img a K) 3%nat; intros B1 B2 _; nd_post). destruct D as [D|D]; unfold READ_STAGE in D; [lia|]. pose proof ATPv_img as TI. unfold ATP in D. lia.
      + exact (imsh_not_drv a K D).
      + exact (nonimg_not_drv a K D).
  Qed.

  (* [comment removed for export] *)
  Record stdio_indep (c : gcomp) : Prop := mkSI {
    si_P : forall L RNG (s s' : PS) FB FB' (m : mem), gc_P c L RNG s FB m -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s ->
             (forall q A n, ps_outfile s = Some q -> In (q, A, n) FB -> In (q, A, n) FB') -> gc_P c L RNG s' FB' m;
    si_dom : forall L (s s' : PS) FB FB' a, gc_dom c L s' FB' a -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> gc_dom c L s FB a;
    si_static : forall L RNG (s : PS) FB (m : mem) a, gc_P c L RNG s FB m -> gc_dom c L s FB a -> ~ stdio_static a;
    si_blocks : forall L RNG (s : PS) CL FB FL (m : mem) a,
        AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gc_P c L RNG s FB m -> 0 <= a < 2^64 -> gc_dom c L s FB a -> ~ in_block FB a }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CI_ST1 CI_ST2"] Lemma stdio_iv_arange : forall L RNG st CL FB FL (m : mem) (BL : list cblk) SP iv, AHEAP AI L RNG st (LBof CL FB FL) m ->
    (forall b, In b BL -> In b (CL ++ FB)) -> stdio_ivA BL SP iv ->
    aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
    \/ aahm_client (fst iv) (snd iv - fst iv).
  Proof.
    intros L RNG st CL FB FL m BL SP [lo hi] AH HBL K. cbn [fst snd] in *. unfold stdio_ivA in K. cbn [fst snd] in K.
    destruct K as [[K1 K2]|[K|[[K1 K2]|[[K1 K2]|[K1 K2]]]]].
    - left. left. left. exact K1.
    - left. right. left. unfold iv_in_block in K. apply Exists_exists in K as (b & Hb & H1 & H2). cbn [fst snd] in H1, H2.
      exists (hb_of b). split; [apply In_hb; apply HBL; exact Hb|]. unfold hb_of. cbn [ab_addr ab_size]. lia.
    - left. left. right. left. destruct CI_ST1 as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - left. left. right. left. destruct CI_ST2 as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - right. left. unfold atls_client, ATP in *. left. lia.
  Qed.

  #[using="Type"] Lemma cloc_iv_client : forall FL (CL : list cblk) iv, clocA FL CL (fst iv) (snd iv - fst iv) -> client_ivA FL CL iv.
  Proof.
    intros FL CL [lo hi] K. cbn [fst snd] in *. destruct K as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - right. left. unfold iv_in_block. apply Exists_exists. exists b. split; [exact Hb|]. cbn [fst snd]. lia.
    - right. right. left. unfold iv_in_frames. apply Exists_exists. exists fr. split; [exact Hf|]. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma indep_outside : forall c, gcomp_ok AI c -> stdio_indep c -> forall L RNG (s : PS) CL FB FL (m : mem) (X : list cblk) SP W WX a,
    AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gc_P c L RNG s FB m -> 0 <= a < 2^64 -> gc_dom c L s FB a ->
    incl X CL -> Forall (stdio_ivA (X ++ FB) SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX -> outside (W ++ WX) a.
  Proof.
    intros c OK SI L RNG s CL FB FL m X SP W WX a AH PC Ha Da HX FW FX.
    pose proof (gk_client AI c OK _ _ _ _ _ _ _ _ AH PC Ha Da) as NC.
    apply outside_app2; apply outside_of; intros iv Hi Ra.
    - pose proof (proj1 (Forall_forall _ _) FW iv Hi) as K. unfold stdio_ivA in K.
      destruct K as [[K1 K2]|[K|[[K1 K2]|[[K1 K2]|[K1 K2]]]]].
      + apply NC. left. lia.
      + unfold iv_in_block in K. apply Exists_app in K as [K|K]; apply Exists_exists in K as (b & Hb & H1 & H2).
        * apply NC. right. left. apply in_block_In. exists b. split; [apply HX; exact Hb| lia].
        * apply (si_blocks c SI _ _ _ _ _ _ _ _ AH PC Ha Da). apply in_block_In. exists b. split; [exact Hb| lia].
      + apply (si_static c SI _ _ _ _ _ _ PC Da). left. lia.
      + apply (si_static c SI _ _ _ _ _ _ PC Da). right. lia.
      + apply (gk_drv AI c OK _ _ _ _ Da). right. lia.
    - apply NC. eapply client_iv_reg; [apply cloc_iv_client; exact (proj1 (Forall_forall _ _) FX iv Hi)| exact Ra].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma comps_step : forall cs, Forall (gcomp_ok AI) cs -> Forall stdio_indep cs -> forall L RNG (s s' : PS) CL FB FB' FL (m m' : mem) (X : list cblk) SP W WX,
    AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gconj cs L RNG s FB m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
    incl X CL -> Forall (stdio_ivA (X ++ FB) SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX ->
    ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> (forall q A n, ps_outfile s = Some q -> In (q, A, n) FB -> In (q, A, n) FB') ->
    gconj cs L RNG s' FB' m'.
  Proof.
    intros cs OKs SIs L RNG s s' CL FB FB' FL m m' X SP W WX AH GC MU WM HX FW FX E1 E2 HFB.
    eapply gconj_map; [exact GC|]. intros c Hc PC.
    pose proof (proj1 (Forall_forall _ _) OKs c Hc) as OK. pose proof (proj1 (Forall_forall _ _) SIs c Hc) as SI.
    apply (si_P c SI L RNG s s' FB FB' m'); [| exact E1| exact E2| exact HFB].
    eapply (gk_agree AI c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
    apply (agrees_on_of_munch _ (W ++ WX)); [exact MU| exact WM|]. intros a Ha Da.
    eapply (indep_outside c OK SI); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Laws.
    Variables cs1 cs2 : list gcomp.
    Hypothesis CSOK : Forall (gcomp_ok AI) (cs1 ++ cs2).
    Hypothesis INDEP : Forall stdio_indep (cs1 ++ cs2).
    #[local] Notation GSTAT := (GSTAT_of (cs1 ++ files_comp :: cs2)).
    #[local] Notation GIOA := (GIOA_real AI GSTAT).

    #[using="Type"] Lemma gs_stdio_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> STDIOR (ps_libc s) FB m.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). apply gconj_app in GC as [_ GC]. cbn [gconj] in GC. exact (proj1 (proj1 GC)). Qed.

    #[using="Type"] Lemma gs_errno_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> exists e : word, rw_cells asegs m (ATP + -164) [C4 e].
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (ERR & _)). exact ERR. Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Lemma stdio_core : forall L RNG (s : PS) CL FB FB' FL (m m' : mem) (X : list cblk) W WX SP l',
      GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
      incl X CL -> Forall (stdio_ivA (X ++ FB) SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX ->
      (forall q A n, ps_outfile s = Some q -> In (q, A, n) FB -> In (q, A, n) FB') ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) -> STDIOR l' FB' m' -> (forall b, In b FB' -> In b (CL ++ FB)) ->
      AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m' /\ GSTAT L RNG (set_libc l' s) FB' m'.
    Proof.
      intros L RNG s CL FB FB' FL m m' X W WX SP l' G MU WM HX FW FX HFB ERR' ST' HIN.
      (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      apply gconj_app in GC as [GC1 GC2]. cbn [gconj] in GC2. destruct GC2 as [_ GC2].
      apply Forall_app in CSOK as [OK1 OK2]. apply Forall_app in INDEP as [IN1 IN2].
      split.
      - eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. apply Forall_app. split.
        + eapply Forall_impl; [| exact FW]. intros iv K. eapply (stdio_iv_arange _ _ _ CL FB FL m (X ++ FB)); [exact AH| | exact K].
          intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; apply HX; exact Hb| right; exact Hb].
        + eapply Forall_impl; [| exact FX]. intros iv K. left. eapply (client_iv_arange AI AF); [exact G| apply cloc_iv_client; exact K].
      - split; [exact ERR'|]. apply gconj_app. split.
        + eapply (comps_step cs1 OK1 IN1 L RNG s (set_libc l' s) CL FB FB' FL m m' X SP W WX); try eassumption; reflexivity.
        + cbn [gconj]. split; [cbn [gc_P files_comp]; unfold files_P; cbn [ps_libc set_libc]; split; [exact ST'|];
                                apply Forall_forall; intros b Hb; exact (fb_geo_of_heap _ _ _ _ _ _ _ b AH (HIN b Hb))|].
          eapply (comps_step cs2 OK2 IN2 L RNG s (set_libc l' s) CL FB FB' FL m m' X SP W WX); try eassumption; reflexivity.
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Theorem gs_step_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W WX SP l',
      GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
      Forall (stdio_ivA FB SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX -> ATOP + 4096 <= SP ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
      STDIOR l' FB m' -> GIOA L RNG (set_libc l' s) CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W WX SP l' G MU WM FW FX HSP ERR' ST'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND _; nd_post).
      destruct (stdio_core L RNG s CL FB FB FL m m' [] W WX SP l' G MU WM ltac:(intros b []) FW FX ltac:(intros q A n _ H; exact H) ERR' ST' ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [AH' GS'].
      split; [exact AH'|]. split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS'].
    Qed.

    #[using="Type"] Lemma perm_adopt : forall (b0 : cblk) CL FB FL, Permutation (LBof (b0 :: CL) FB FL) (LBof CL (b0 :: FB) FL).
    Proof.
      intros b0 CL FB FL. unfold LBof. apply Permutation_app_tail. apply Permutation_map. cbn [app]. apply Permutation_middle.
    Qed.
    #[using="Type"] Lemma perm_release : forall (b0 : cblk) CL F1 F2 FL, Permutation (LBof CL (F1 ++ b0 :: F2) FL) (LBof (b0 :: CL) (F1 ++ F2) FL).
    Proof.
      intros b0 CL F1 F2 FL. unfold LBof. apply Permutation_app_tail. apply Permutation_map. cbn [app].
      rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Theorem gs_adopt_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W SP l' (q : aptr) A,
      GIOA L RNG s ((q, A, FILE_ALLOC) :: CL) FB FL m -> munch W m m' -> wmono asegs m m' ->
      Forall (stdio_ivA ((q, A, FILE_ALLOC) :: FB) SP) W -> ATOP + 4096 <= SP ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
      STDIOR l' ((q, A, FILE_ALLOC) :: FB) m' ->
      GIOA L RNG (set_libc l' s) CL ((q, A, FILE_ALLOC) :: FB) FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W SP l' q A G MU WM FW HSP ERR' ST'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND _; nd_post).
      destruct (stdio_core L RNG s ((q, A, FILE_ALLOC) :: CL) FB ((q, A, FILE_ALLOC) :: FB) FL m m' [(q, A, FILE_ALLOC)] W [] SP l' G
                  ltac:(rewrite app_nil_r; exact MU) WM ltac:(intros b [<-|[]]; left; reflexivity) FW ltac:(constructor)
                  ltac:(intros q0 A0 n0 _ H; right; exact H) ERR' ST'
                  ltac:(intros b [<-|Hb]; [left; reflexivity| right; apply in_or_app; right; exact Hb])) as [AH' GS'].
      split. { cbn [ps_heap set_libc]. eapply (AI_perm AI); [apply perm_adopt| exact AH']. }
      split; [exact RV|]. split.
      { intros b Hb. apply AD. apply in_app_or in Hb as [Hb|[<-|Hb]]; [right; apply in_or_app; left; exact Hb| left; reflexivity| right; apply in_or_app; right; exact Hb]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS'].
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 CSOK INDEP"] Theorem gs_release_real : forall L RNG (s : PS) CL F1 F2 FL (m m' : mem) W SP l' (q : aptr) A,
      GIOA L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) FL m -> munch W m m' -> wmono asegs m m' ->
      Forall (stdio_ivA (F1 ++ (q, A, FILE_ALLOC) :: F2) SP) W -> ATOP + 4096 <= SP ->
      ps_outfile s <> Some q ->
      (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
      STDIOR l' (F1 ++ F2) m' ->
      GIOA L RNG (set_libc l' s) ((q, A, FILE_ALLOC) :: CL) (F1 ++ F2) FL m'.
    Proof.
      intros L RNG s CL F1 F2 FL m m' W SP l' q A G MU WM FW HSP NQ ERR' ST'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND _; nd_post).
      destruct (stdio_core L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) (F1 ++ F2) FL m m' [] W [] SP l' G
                  ltac:(rewrite app_nil_r; exact MU) WM ltac:(intros b []) FW ltac:(constructor)
                  ltac:(intros q0 A0 n0 EQ H; apply in_app_or in H as [H|[H|H]]; [apply in_or_app; left; exact H| exfalso; apply NQ; rewrite EQ; congruence| apply in_or_app; right; exact H])
                  ERR' ST' ltac:(intros b Hb; apply in_or_app; right; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb])) as [AH' GS'].
      split. { cbn [ps_heap set_libc]. eapply (AI_perm AI); [apply perm_release| exact AH']. }
      split; [exact RV|]. split.
      { intros b Hb. apply AD. destruct Hb as [<-|Hb]; [apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
        apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
        apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS'].
    Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls"] Theorem gs_keeps_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W WX SP,
      GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
      Forall (stdio_ivA FB SP) W -> ATOP + 4096 <= SP ->
      agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m m'.
    Proof.
      intros L RNG s CL FB FL m m' W WX SP G MU WM FW HSP.
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [K OX]. apply outside_app2; [| exact OX]. clear MU OX WX.
      pose proof G as (AH & _).
      pose proof (gr_apart AI GSTAT _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (_ & _ & BX).
      assert (GB : forall b, In b (CL ++ FB) -> ablk (cb_addr b) (cb_addr b + cb_size b))
        by (intros b Hb; exact (proj1 (geo_block AI GSTAT _ _ _ _ _ _ _ _ G Hb))).
      assert (GF : forall fr, In fr FL -> ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr mod 64 = 0 /\ fb_size fr mod 64 = 0 /\ 64 <= fb_size fr)
        by (intros fr Hf; exact (geo_frame AI AF GSTAT _ _ _ _ _ _ _ _ G Hf)).
      assert (REG : client_reg FL CL a).
      { unfold client_reg, client_keeps in *. destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
      atop_facts.
      apply outside_of. intros [lo hi] Hi Hin. cbn [fst snd] in Hin.
      pose proof (proj1 (Forall_forall _ _) FW _ Hi) as Hiv. unfold stdio_ivA in Hiv. cbn [fst snd] in Hiv.
      assert (KA : SP <= a
                   \/ (exists b, In b CL /\ cb_addr b <= a < cb_addr b + cb_size b)
                   \/ (exists fr, In fr FL /\ fb_addr fr <= a < fb_addr fr + fb_size fr)
                   \/ (exists fr, In fr FL /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3)).
      { destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; apply in_block_In; exact K| right; right; left; apply in_frames_In; exact K
                                     | right; right; right; apply in_frame_sh_In; exact K]. }
      assert (BANDa : forall F n, ablk F (F + n) -> F <= a < F + n -> ~ (KLS <= a < 0x10007fff8000)) by (intros F n B R X; exact (ablk_clear_band _ _ a B X R)).
      destruct Hiv as [[I1 I2]|[Hiv|[[I1 I2]|[[I1 I2]|[I1 I2]]]]].
      - (* [comment removed for export] *)
        destruct KA as [KK|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
        + (pose proof (ablk_lin _ _ (GB b ltac:(apply in_or_app; left; exact Hb))) as ndP__; nd_pre ndP__ 4%nat; intros _ _ T _; nd_post). lia.
        + destruct (GF fr Hf) as (B & _). (pose proof (ablk_lin _ _ B) as ndP__; nd_pre ndP__ 4%nat; intros _ _ T _; nd_post). lia.
        + (nd_pre (GF fr Hf) 4%nat; intros B A64 N64 N0; nd_post).
          pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R). lia.
      - (* [comment removed for export] *)
        unfold iv_in_block in Hiv. apply Exists_exists in Hiv as (b' & Hb' & H1 & H2). cbn [fst snd] in H1, H2.
        pose proof (GB b' ltac:(apply in_or_app; right; exact Hb')) as B'. (pose proof (ablk_lin _ _ B') as ndP__; nd_pre ndP__ 4%nat; intros _ _ T' _; nd_post).
        destruct KA as [KK|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
        + pose proof (BX b b' Hb Hb') as AP. unfold apart in AP. lia.
        + apply (gr_fr_apart AI GSTAT _ _ _ _ _ _ _ a G); [apply in_frames_In; exists fr; split; [exact Hf| exact R]|].
          apply in_block_In. exists b'. split; [apply in_or_app; right; exact Hb'| lia].
        + (nd_pre (GF fr Hf) 4%nat; intros B A64 N64 N0; nd_post).
          pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R) as SB.
          apply (BANDa _ _ B' ltac:(lia)). exact SB.
      - (* [comment removed for export] *)
        eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      - (* [comment removed for export] *)
        eapply (img_not_client AI AF); [exact AH| | exact REG]. unfold AIMG_HI. lia.
      - (* [comment removed for export] *)
        eapply (tls_not_client AI AF AI_block_tls); [exact AH| | exact REG]. lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis IN_ENV : In env_comp (cs1 ++ cs2).
    Hypothesis IN_GLOBALS : In globals_comp (cs1 ++ cs2).
    Hypothesis IN_STACKSH : In stacksh_comp (cs1 ++ cs2).
    (* [comment removed for export] *)
    Hypothesis AI_ssc : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rt_ssc m.

    #[using="Type"] Lemma in_cs : forall c, In c (cs1 ++ cs2) -> In c (cs1 ++ files_comp :: cs2).
    Proof. intros c Hc. apply in_app_or in Hc as [Hc|Hc]; apply in_or_app; [left; exact Hc| right; right; exact Hc]. Qed.
    #[using="IN_ENV"] Lemma g_env : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> stdio_env_P (Z_to_bv 64 (al_V L 45%nat)) RNG m.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). exact (proj1 (gconj_In _ _ _ _ _ _ _ GC (in_cs _ IN_ENV))). Qed.
    #[using="IN_GLOBALS"] Lemma g_win : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> wr_at asegs m 0x7fffa000 780288.
    Proof. intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & (_ & GC)). exact (proj1 (gconj_In _ _ _ _ _ _ _ GC (in_cs _ IN_GLOBALS))). Qed.

    #[using="IN_ENV"] Lemma gs_ssp_real : forall L, exists canary : word, forall RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> ssp_cells m canary.
    Proof.
      intros L. exists (Z_to_bv 64 (al_V L 45%nat)). intros RNG s CL FB FL m G. pose proof G as (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RO.
      eapply stdio_env_ssp; [exact (g_env _ _ _ _ _ _ _ G)|].
      apply (relro_word m _ _ RO); [unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.got_ssp, ARELRO_LO; lia| unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.got_ssp, ARELRO_HI; lia| vm_compute; reflexivity].
    Qed.

    #[using="IN_ENV AI_ssc"] Lemma gs_env_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> icptenv m.
    Proof.
      intros L RNG s CL FB FL m G. pose proof G as (AH & _). pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. pose proof (AI_ssc _ _ _ _ _ AH) as SSC.
      (nd_pre RT 22%nat; intros _ R2 R3 R4 R5 _ R7 R8 _ _ _ _ _ R14 R15 R16 R17 R18 R19 R20 R21 _; nd_post).
      eapply stdio_env_icptenv; [exact (g_env _ _ _ _ _ _ _ G)| exact R2| exact R3| exact R5| exact R7| exact R8| exact R4| exact R16| exact R14
                               | exact R15| exact R19| exact R17| exact R18| exact R21| exact SSC].
    Qed.

    #[using="Type"] Lemma gs_ckpf_real : forall L RNG (s : PS) CL FB FL (m : mem), GIOA L RNG s CL FB FL m -> rw_cells asegs m 0x140578 [C8 (Z_to_bv 64 4294967296)].
    Proof.
      intros L RNG s CL FB FL m (AH & _). pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
      (nd_pre RT 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R20 _; nd_post). exact R20.
    Qed.

    #[using="IN_STACKSH"] Lemma gs_stack_real : forall L RNG (s : PS) CL FB FL (m : mem) lo hi, GIOA L RNG s CL FB FL m ->
      ATOP + 4096 <= lo -> lo <= hi -> hi <= al_top L -> hi + 8 <= 2^47 -> sobj RNG m lo hi.
    Proof.
      intros L RNG s CL FB FL m lo hi G H1 H2 H3 H4. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (_ & GC); nd_post).
      pose proof (gconj_In _ _ _ _ _ _ _ GC (in_cs _ IN_STACKSH)) as SP. cbn [gc_P stacksh_comp] in SP.
      destruct (stacksh_use L RNG s FB m lo (hi - lo) SP H1 ltac:(lia) ltac:(lia)) as [U (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & WR & RG)].
      replace (lo + (hi - lo)) with hi in * by lia.
      (nd_pre (AI_layout AI _ _ _ _ _ AH) 5%nat; intros T1 _ _ T4 _; nd_post). pose proof atop_range as AR.
      split. { split; [exact H2|]. right. unfold KHIGH, KEND. change (2^47) with 140737488355328 in H4. lia. }
      split; [exact U|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption.
    Qed.

    #[using="AF AI_block_tls CI_ST1 CI_ST2 AI_block_ahm CSOK INDEP IN_ENV IN_GLOBALS IN_STACKSH AI_ssc"] Theorem gia_stdio_laws_real : gia_stdio_laws GIOA.
    Proof.
      constructor.
      - exact gs_stdio_real.
      - exact gs_ssp_real.
      - exact gs_errno_real.
      - exact gs_env_real.
      - exact gs_ckpf_real.
      - intros L RNG s CL FB FL m G. exact (stdio_env_libc _ _ _ (g_env _ _ _ _ _ _ _ G)).   (* [comment removed for export] *)
      - intros L RNG s CL FB FL m G. exact (stdio_env_rng0 _ _ _ (g_env _ _ _ _ _ _ _ G)).
      - exact gs_stack_real.
      - intros L RNG s CL FB FL m lo hi G RI RS HR LE. exact (stdio_env_rodata _ _ _ lo hi (g_env _ _ _ _ _ _ _ G) (g_win _ _ _ _ _ _ _ G) RI RS HR LE).
      - intros L RNG s CL FB FL m G RI RS. exact (stdio_env_statics _ _ _ (g_env _ _ _ _ _ _ _ G) (g_win _ _ _ _ _ _ _ G) RI RS).
      - (* [comment removed for export] *)
        intros L RNG s CL FB FL m G. pose proof G as (AH & _).
        (nd_pre (g_env _ _ _ _ _ _ _ G) 4%nat; intros _ _ (AH1 & AH2 & AH3 & AH4 & AH5 & AH6) _; nd_post).
        exists AAHMv. split; [exact AH1|]. split; [exact AH3|]. split; [exact AH4|]. split; [exact AH5|]. split; [exact AH6|]. split; [exact AH2|].
        intros b Hb. pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_hb CL FB FL b Hb)) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D.
        unfold AHM_BYTES. unfold AAHM_SZ in D. exact D.
      - exact gs_step_real.
      - exact gs_keeps_real.
      - exact gs_adopt_real.
      - exact gs_release_real.
    Qed.
  End Laws.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma indep_const : forall (P : alayout -> footprint -> mem -> Prop) (D : alayout -> Z -> Prop),
    (forall L a, D L a -> ~ stdio_static a) ->
    (forall L a, D L a -> ~ ((0x604000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP))) ->
    stdio_indep (mkGC (fun L RNG _ _ m => P L RNG m) (fun L _ _ a => D L a)).
  Proof.
    intros P D HS HB. constructor; cbn [gc_P gc_dom].
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da. exact (HS L a Da).
    - intros L RNG s CL FB FL m a AH _ _ Da K. exact (HB L a Da (fb_block_band _ _ _ _ _ _ _ _ AH K)).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma indep_of_band : forall (c : gcomp),
    (forall L RNG (s s' : PS) FB FB' (m : mem), gc_P c L RNG s FB m -> gc_P c L RNG s' FB' m) ->
    (forall L (s s' : PS) FB FB' a, gc_dom c L s' FB' a -> gc_dom c L s FB a) ->
    (forall L (s : PS) FB a, gc_dom c L s FB a -> 2147450880 <= a < 0x10007fff8000) -> stdio_indep c.
  Proof.
    intros c HP HD BAND. constructor.
    - intros L RNG s s' FB FB' m PC _ _ _. exact (HP _ _ _ _ _ _ _ PC).
    - intros L s s' FB FB' a Da _ _. exact (HD _ _ _ _ _ _ Da).
    - intros L RNG s FB m a _ Da [X|X]; pose proof (BAND L s FB a Da) as B; clear - B X; lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. pose proof (BAND L s FB a Da) as B. pose proof atop_range as AR.
      destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; clear - B X AR; lia.
  Qed.

  #[using="Type"] Lemma args_indep : forall USP n, ATOP + 64 <= USP -> 0 <= n -> USP + n + 8 <= 2^47 -> stdio_indep (args_comp USP n).
  Proof.
    intros USP n G1 G2 G3. apply indep_of_band; cbn [gc_P gc_dom args_comp].
    - intros L RNG s s' FB FB' m HP. exact HP.
    - intros L s s' FB FB' a Da. exact Da.
    - intros L s FB a Da. destruct (args_dom_band USP n G1 G3 a Da) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma unp_indep : stdio_indep unp_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom unp_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. unfold unp_dom, AIMSH_LO, AIMSH_LEN in Da. lia.
  Qed.
  #[using="Type"] Lemma globals_indep : stdio_indep globals_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom globals_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia.
  Qed.
  #[using="Type"] Lemma stdinp_indep : stdio_indep stdinp_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom stdinp_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. unfold win_dom, AIMSH_LO, AIMSH_LEN in Da. lia.
  Qed.
  #[using="Type"] Lemma stacksh_indep : stdio_indep stacksh_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom stacksh_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a [Da D47]. destruct (stacksh_band L a Da D47) as [B _]. pose proof atop_range as AR. clear - B AR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma tlsobj_indep : stdio_indep tlsobj_comp.
  Proof.
    apply indep_of_band; cbn [gc_P gc_dom tlsobj_comp]; [intros L RNG s s' FB FB' m HP; exact HP| intros L s s' FB FB' a Da; exact Da|].
    intros L s FB a Da. destruct (tlsobj_band a Da) as (B & _). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI_block_tls"] Lemma exitci_indep : stdio_indep exitci_comp.
  Proof.
    constructor; cbn [gc_P gc_dom exitci_comp].
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da [X|X]; unfold exitci_dom, exit_dom in Da; destruct Da as [D|[(k & Hk & Rk)|D]].
      all: try (pose proof ATPv_img as TI; lia).
      all: try (unfold AIMSH_LO, AIMSH_LEN in D; lia).
      all: unfold EXIT_CI_KEEP in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]); destruct Hk.
    - intros L RNG s CL FB FL m a AH _ _ Da K. unfold exitci_dom, exit_dom in Da. destruct Da as [D|[(k & Hk & Rk)|D]].
      + apply in_block_In in K as (b & Hb & Rb).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as T. unfold hb_of in T. cbn [ab_addr ab_size] in T.
        unfold ATP in T. lia.
      + destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR;
          unfold EXIT_CI_KEEP in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]); destruct Hk.
      + destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; unfold AIMSH_LO, AIMSH_LEN in D; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma harn_stdio_indep : stdio_indep harn_comp.
  Proof.
    constructor; cbn [gc_P gc_dom harn_comp]; unfold harn_P, harn_dom.
    - intros L RNG s s' FB FB' m HP EO _ HFB. rewrite EO. destruct (ps_outfile s) as [q|] eqn:E; [| exact HP].
      (nd_pre HP 3%nat; intros A HA HC; nd_post). exists A. split; [exact (HFB q A _ eq_refl HA)| exact HC].
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a _ Da [X|X]; unfold OUTFILE_ADDR in Da; lia.
    - intros L RNG s CL FB FL m a AH _ _ Da K. destruct (fb_block_band _ _ _ _ _ _ _ _ AH K) as [X|X]; pose proof atop_range as AR; unfold OUTFILE_ADDR in Da; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI_block_ahm"] Lemma env_indep : stdio_indep env_comp.
  Proof.
    constructor; cbn [gc_P gc_dom env_comp]; unfold env_P, env_dom.
    - intros L RNG s s' FB FB' m HP _ _ _. exact HP.
    - intros L s s' FB FB' a Da _ _. exact Da.
    - intros L RNG s FB m a [EP _] [K|[K|[K _]]] X.
      + exact (proj2 (proj2 (env_cell_img a K)) X).
      + unfold AIMSH_LO, AIMSH_LEN in K. destruct X; lia.
      + (nd_pre EP 4%nat; intros _ _ (_ & _ & _ & A4 & _) _; nd_post). destruct X; lia.
    - intros L RNG s CL FB FL m a AH _ _ [K|[K|[K _]]] B.
      + destruct (env_cell_img a K) as (I1 & _). destruct (fb_block_band _ _ _ _ _ _ _ _ AH B); lia.
      + unfold AIMSH_LO, AIMSH_LEN in K. pose proof atop_range as AR. destruct (fb_block_band _ _ _ _ _ _ _ _ AH B); lia.
      + apply in_block_In in B as (b & Hb & Rb).
        pose proof (AI_block_ahm _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; right; exact Hb))) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma files_harn_indep : harn_indep files_comp.
  Proof.
    split; cbn [gc_P gc_dom files_comp]; unfold files_P, files_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a [K|[_ [K _]]] R; unfold OUTFILE_ADDR in R; [destruct K; lia| lia].
  Qed.
  #[using="Type"] Lemma env_harn_indep : harn_indep env_comp.
  Proof.
    split; cbn [gc_P gc_dom env_comp]; unfold env_P, env_dom.
    - intros L RNG s FB m o HP. exact HP.
    - intros L s FB a [K|[K|[_ [K _]]]] R; unfold OUTFILE_ADDR in R.
      + (nd_pre K 3%nat; intros k Hk Rk; nd_post). unfold STDIO_ENV_CELLS in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
      + unfold AIMSH_LO, AIMSH_LEN in K. lia.
      + lia.
  Qed.
End StdioInst.
End CANSEC1.
End TwB.
