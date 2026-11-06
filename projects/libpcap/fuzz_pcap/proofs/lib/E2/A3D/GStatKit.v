(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section GStatKit.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  (* [comment removed for export] *)
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition client_reg (FL : list fblock) (CL : list cblk) (a : Z) : Prop := client_keeps FL CL (ATOP + 4096) a.
  (* [comment removed for export] *)
  Definition drv_static (a : Z) : Prop := (READ_STAGE <= a < READ_STAGE + 65536) \/ (ATP + -164 <= a < ATP + -160).

  Record gcomp : Type := mkGC {
    gc_P : alayout -> footprint -> PS -> list cblk -> mem -> Prop;
    gc_dom : alayout -> PS -> list cblk -> Z -> Prop }.

  Record gcomp_ok (c : gcomp) : Prop := mkGK {
    gk_agree : forall L RNG RNG' (s s' : PS) FB (m m' : mem),
        gc_P c L RNG s FB m -> fp_le RNG RNG' -> agrees_on (gc_dom c L s FB) m m' ->
        ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> gc_P c L RNG' s' FB m';
    gk_pres : forall L RNG (s : PS) FB (m : mem) (LB : list ablock) SP a,
        gc_P c L RNG s FB m -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP -> 0 <= a < 2^64 -> gc_dom c L s FB a ->
        aclient_addr (aci AI) LB SP a \/ aextra_addr a;
    gk_client : forall L RNG (s : PS) CL FB FL (m : mem) a,
        AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gc_P c L RNG s FB m -> 0 <= a < 2^64 -> gc_dom c L s FB a -> ~ client_reg FL CL a;
    gk_drv : forall L (s : PS) FB a, gc_dom c L s FB a -> ~ drv_static a }.

  Fixpoint gconj (cs : list gcomp) (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    match cs with
    | [] => True
    | c :: cs' => gc_P c L RNG s FB m /\ gconj cs' L RNG s FB m
    end.

  #[using="Type"] Lemma gconj_In : forall cs c L RNG s FB m, gconj cs L RNG s FB m -> In c cs -> gc_P c L RNG s FB m.
  Proof. induction cs as [|c0 cs IH]; intros c L RNG s FB m G HI; [destruct HI|]. destruct G as [G0 G]. destruct HI as [<-|HI]; [exact G0| eapply IH; eassumption]. Qed.

  #[using="Type"] Lemma gconj_map : forall cs L RNG s FB m L' RNG' s' FB' m',
    gconj cs L RNG s FB m -> (forall c, In c cs -> gc_P c L RNG s FB m -> gc_P c L' RNG' s' FB' m') -> gconj cs L' RNG' s' FB' m'.
  Proof.
    induction cs as [|c0 cs IH]; intros L RNG s FB m L' RNG' s' FB' m' G HM; [exact I|]. destruct G as [G0 G]. split.
    - apply HM; [left; reflexivity| exact G0].
    - eapply IH; [exact G|]. intros c Hc. apply HM. right. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Definition GSTAT_of (cs : list gcomp) (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    (exists e : word, rw_cells asegs m (ATP + -164) [C4 e]) /\ gconj cs L RNG s FB m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma outside_of : forall (W : list (Z * Z)) a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a HW; [exact I|]. cbn [outside]. split.
    - exact (HW (lo, hi) (or_introl eq_refl)).
    - apply IH. intros iv Hi. apply HW. right. exact Hi.
  Qed.
  #[using="Type"] Lemma outside_app2 : forall (W1 W2 : list (Z * Z)) a, outside W1 a -> outside W2 a -> outside (W1 ++ W2) a.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a O1 O2; [exact O2|]. cbn [app outside] in *. destruct O1 as [O O1]. split; [exact O| apply IH; assumption]. Qed.
  #[using="Type"] Lemma client_ivA_nil : forall FL (CL : list cblk) iv, client_ivA [] CL iv -> client_ivA FL CL iv.
  Proof.
    intros FL CL iv [K|[K|[K|K]]]; [left; exact K| right; left; exact K| |].
    - unfold iv_in_frames in K. apply Exists_nil in K. destruct K.
    - unfold iv_in_frame_shadow in K. apply Exists_nil in K. destruct K.
  Qed.
  #[using="Type"] Lemma client_iv_reg : forall FL (CL : list cblk) iv a, client_ivA FL CL iv -> fst iv <= a < snd iv -> client_reg FL CL a.
  Proof.
    intros FL CL [lo hi] a K Ha. cbn [fst snd] in *. unfold client_reg, client_keeps. destruct K as [K|[K|[K|K]]]; cbn [fst snd] in K.
    - left. lia.
    - right; left. unfold iv_in_block in K. apply Exists_exists in K as (b & Hb & H1 & H2). cbn [fst snd] in H1, H2.
      apply in_block_In. exists b. split; [exact Hb| lia].
    - right; right; left. unfold iv_in_frames in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      apply in_frames_In. exists fr. split; [exact Hf| lia].
    - right; right; right. unfold iv_in_frame_shadow in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      apply in_frame_sh_In. exists fr. split; [exact Hf| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="AF AI_block_tls"] Lemma tls_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> ATP + -200 <= a < ATP + 304 -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. unfold client_reg, client_keeps in K.
    (pose proof atp_lin as ndP__; nd_pre ndP__ 3%nat; intros (TL & _) _ TSH; nd_post). pose proof ATPv_sh as TSH'. unfold ATP in *.
    destruct K as [K|[K|[K|K]]].
    - lia.
    - apply in_block_In in K as (b & Hb & Rb).
      pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D. unfold ATP in D. lia.
    - apply in_frames_In in K as (fr & Hf & Rf).
      pose proof (AI_block_tls _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) as D. unfold fkb_of in D. cbn [ab_addr ab_size] in D. unfold ATP in D. lia.
    - apply in_frame_sh_In in K as (fr & Hf & Rf).
      (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ _ _ BAND TOP _; nd_post).
      (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post). unfold AIMG_HI in IMG. pose proof atop_range as AR.
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
      clear - Rf IMG TOP TSH' Ha AR. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AF"] Lemma client_reg_cases : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> client_reg FL CL a ->
    ATOP + 4096 <= a \/ (0x603000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP)
    \/ (exists F n, 0x603000 <= F /\ F + n <= ATOP /\ F mod 64 = 0 /\ 0 <= n /\ F / 8 + 2147450880 <= a < F / 8 + 2147450880 + n / 8).
  Proof.
    intros L RNG st CL FB FL m a AH K. unfold client_reg, client_keeps in K. destruct K as [K|[K|[K|K]]].
    - left. exact K.
    - apply in_block_In in K as (b & Hb & Rb).
      (nd_pre (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) 3%nat; intros _ BR _; nd_post).
      destruct BR as (BAND & _). unfold ablk, AIMG_HI, KLS in BAND. right. destruct BAND as [[B1 B2]|[B1 B2]]; [left| right; left]; lia.
    - apply in_frames_In in K as (fr & Hf & Rf).
      (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ _ _ BAND TOP _; nd_post).
      unfold ablk, AIMG_HI, KLS in BAND. right. destruct BAND as [[B1 B2]|[B1 B2]]; [left| right; left]; lia.
    - apply in_frame_sh_In in K as (fr & Hf & Rf).
      (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post).
      (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post). unfold AIMG_HI in IMG.
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
      right; right; right. exists (fb_addr fr), (fb_size fr). split; [exact IMG|]. split; [exact TOP|]. split; [exact F64|]. split; [clear - Rf; Z.div_mod_to_equations; lia| exact Rf].
  Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma img_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> 0 <= a < AIMG_HI -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. pose proof atop_range as AR. unfold AIMG_HI in *.
    destruct (client_reg_cases _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
    all: try (clear - Ha C1 C5; Z.div_mod_to_equations; lia).
  Qed.
  #[using="AF"] Lemma imsh_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. pose proof atop_range as AR. unfold AIMSH_LO, AIMSH_LEN in *.
    destruct (client_reg_cases _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
    all: try (clear - Ha C1 C5; Z.div_mod_to_equations; lia).
  Qed.
  #[using="AF"] Lemma stksh_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> ATOP / 8 + 2147450880 <= a < 0x10007fff8000 -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. pose proof atop_range as AR. unfold AIMG_HI in *.
    destruct (client_reg_cases _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
    all: try (clear - Ha C2 C3 C4 C5 AR; Z.div_mod_to_equations; lia).
  Qed.

  #[using="Type"] Lemma imsh_not_drv : forall a, AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN -> ~ drv_static a.
  Proof.
    intros a Ha [D|D]; unfold AIMSH_LO, AIMSH_LEN, READ_STAGE in *; [lia|]. pose proof ATPv_sh as TS. unfold ATP in D. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Laws.
    Variable cs : list gcomp.
    Hypothesis CSOK : Forall gcomp_ok cs.
    #[local] Notation GSTAT := (GSTAT_of cs).

    #[using="Type"] Lemma errno_agree : forall (P : Z -> Prop) (m m' : mem),
      (exists e : word, rw_cells asegs m (ATP + -164) [C4 e]) -> agrees_on P m m' -> (forall a, ATP + -164 <= a < ATP + -160 -> P a) ->
      exists e : word, rw_cells asegs m' (ATP + -164) [C4 e].
    Proof.
      intros P m m' [e HE] AG HP. exists e. eapply agrees_rw_cells; [exact AG| exact HE|].
      intros a Ha. apply HP. cbn [cells_size csize Nat.add] in Ha. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls CSOK"] Theorem GS_client_frame : forall L RNG (s : PS) CL FB FL (m m' : mem) W,
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' -> Forall (client_ivA FL CL) W -> GSTAT L RNG s FB m'.
    Proof.
      intros L RNG s CL FB FL m m' W G MU WM FW. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (ERR & GC); nd_post).
      assert (OUT : forall a, 0 <= a < 2^64 -> ~ client_reg FL CL a -> outside W a).
      { intros a Ha NC. apply outside_of. intros iv Hi Ra. apply NC. eapply client_iv_reg; [exact (proj1 (Forall_forall _ _) FW iv Hi)| exact Ra]. }
      split.
      - eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        apply (agrees_on_of_munch _ W); [exact MU| exact WM|]. intros a Ha Ra. apply OUT; [exact Ha|].
        eapply tls_not_client; [exact AH| lia].
      - eapply gconj_map; [exact GC|]. intros c Hc PC. pose proof (proj1 (Forall_forall _ _) CSOK c Hc) as OK.
        eapply (gk_agree c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply (agrees_on_of_munch _ W); [exact MU| exact WM|]. intros a Ha Da. apply OUT; [exact Ha|].
        eapply (gk_client c OK); eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="CSOK"] Theorem GS_pres : forall L RNG RNG' (s s' : PS) FB (LB : list ablock) SP (m m' : mem),
      GSTAT L RNG s FB m -> fp_le RNG RNG' -> aheap_pres (aci AI) LB SP m m' -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP ->
      ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> GSTAT L RNG' s' FB m'.
    Proof.
      intros L RNG RNG' s s' FB LB SP m m' (ERR & GC) FP HP HFB HSP E1 E2 E3. split.
      - eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        intros a Ha Ra. apply HP; [exact Ha|]. right. left. left. unfold ATP in Ra. lia.
      - eapply gconj_map; [exact GC|]. intros c Hc PC. pose proof (proj1 (Forall_forall _ _) CSOK c Hc) as OK.
        eapply (gk_agree c OK); [exact PC| exact FP| | exact E1| exact E2| exact E3].
        intros a Ha Da. apply HP; [exact Ha|]. eapply (gk_pres c OK); eassumption.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis CI_RS : exists iv, In iv (aci AI) /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.

    #[using="AF CI_RS"] Lemma drv_iv_arange : forall L RNG (s : PS) CL FB FL (m : mem) iv, GIOA_real AI GSTAT L RNG s CL FB FL m -> drv_ivA CL iv ->
      aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv).
    Proof.
      intros L RNG s CL FB FL m iv G [K|K]; [eapply (client_iv_arange AI AF); [exact G| apply client_ivA_nil; exact K]|].
      destruct K as [K1 K2]. destruct CI_RS as (iv0 & Hiv & H1 & H2). left. right. left. exists iv0. split; [exact Hiv|]. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma drv_outside : forall FL CL W a, Forall (drv_ivA CL) W -> ~ client_reg FL CL a -> ~ drv_static a -> outside W a.
    Proof.
      intros FL CL W a FW NC ND. apply outside_of. intros iv Hi Ra.
      destruct (proj1 (Forall_forall _ _) FW iv Hi) as [K|[K1 K2]].
      - apply NC. eapply client_iv_reg; [apply client_ivA_nil; exact K| exact Ra].
      - apply ND. left. unfold READ_STAGE in *. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls"] Lemma errno_outside : forall L RNG st CL FB FL (m : mem) W a,
      AHEAP AI L RNG st (LBof CL FB FL) m -> Forall (drv_ivA CL) W -> ATP + -164 <= a < ATP + -160 -> outside W a.
    Proof.
      intros L RNG st CL FB FL m W a AH FW Ra. apply outside_of. intros iv Hi Ri.
      destruct (proj1 (Forall_forall _ _) FW iv Hi) as [K|[K1 K2]].
      - eapply (tls_not_client _ _ _ CL FB FL m a AH); [lia|]. eapply client_iv_reg; [apply client_ivA_nil; exact K| exact Ri].
      - pose proof ATPv_img as TI. unfold ATP, READ_STAGE in *. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="AF CSOK CI_RS"] Lemma drv_frame_gen : forall L RNG (s : PS) CL FB FL (m m' : mem) W X,
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch (X ++ W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
      Forall (fun iv => aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                        \/ aahm_client (fst iv) (snd iv - fst iv)) X ->
      (forall a, 0 <= a < 2^64 -> outside X a \/ drv_static a) ->
      (exists e : word, rw_cells asegs m' (ATP + -164) [C4 e]) ->
      GIOA_real AI GSTAT L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W X G MU WM FW FX HX ERR'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      split.
      { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. apply Forall_app. split; [exact FX|].
        eapply Forall_impl; [| exact FW]. intros iv K. left. eapply drv_iv_arange; eassumption. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split; [exact ERR'|].
      eapply gconj_map; [exact GC|]. intros c Hc PC. pose proof (proj1 (Forall_forall _ _) CSOK c Hc) as OK.
      eapply (gk_agree c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
      apply (agrees_on_of_munch _ (X ++ W)); [exact MU| exact WM|]. intros a Ha Da.
      apply outside_app2.
      - destruct (HX a Ha) as [O|D]; [exact O| exfalso; exact (gk_drv c OK _ _ _ _ Da D)].
      - apply (drv_outside FL CL); [exact FW| eapply (gk_client c OK); eassumption| exact (gk_drv c OK _ _ _ _ Da)].
    Qed.

    #[using="AF AI_block_tls CSOK CI_RS"] Theorem gd_frame_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W,
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W -> GIOA_real AI GSTAT L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W G MU WM FW. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (ERR & _); nd_post).
      apply (drv_frame_gen L RNG s CL FB FL m m' W []); [exact G| exact MU| exact WM| exact FW| constructor| intros a _; left; exact I|].
      eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
      apply (agrees_on_of_munch _ W); [exact MU| exact WM|]. intros a Ha Ra. eapply errno_outside; eassumption.
    Qed.

    #[using="AF CSOK CI_RS"] Theorem gd_frame_errno_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W (e : word),
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch ((ATP + -164, ATP + -160) :: W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
      rw_cells asegs m' (ATP + -164) [C4 e] -> GIOA_real AI GSTAT L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W e G MU WM FW HE.
      apply (drv_frame_gen L RNG s CL FB FL m m' W [(ATP + -164, ATP + -160)]); [exact G| exact MU| exact WM| exact FW| | | exists e; exact HE].
      - constructor; [| constructor]. right. left. cbn [fst snd]. unfold atls_client, ATP. left. lia.
      - intros a Ha. destruct (Z_lt_ge_dec a (ATP + -164)) as [LT|GE]; [left; cbn [outside]; split; [lia| exact I]|].
        destruct (Z_lt_ge_dec a (ATP + -160)) as [LT2|GE2]; [right; right; lia| left; cbn [outside]; split; [lia| exact I]].
    Qed.

  End Laws.
End GStatKit.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section GStatKit.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  (* [comment removed for export] *)
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition client_reg (FL : list fblock) (CL : list cblk) (a : Z) : Prop := client_keeps FL CL (ATOP + 4096) a.
  (* [comment removed for export] *)
  Definition drv_static (a : Z) : Prop := (READ_STAGE <= a < READ_STAGE + 65536) \/ (ATP + -164 <= a < ATP + -160).

  Record gcomp : Type := mkGC {
    gc_P : alayout -> footprint -> PS -> list cblk -> mem -> Prop;
    gc_dom : alayout -> PS -> list cblk -> Z -> Prop }.

  Record gcomp_ok (c : gcomp) : Prop := mkGK {
    gk_agree : forall L RNG RNG' (s s' : PS) FB (m m' : mem),
        gc_P c L RNG s FB m -> fp_le RNG RNG' -> agrees_on (gc_dom c L s FB) m m' ->
        ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> gc_P c L RNG' s' FB m';
    gk_pres : forall L RNG (s : PS) FB (m : mem) (LB : list ablock) SP a,
        gc_P c L RNG s FB m -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP -> 0 <= a < 2^64 -> gc_dom c L s FB a ->
        aclient_addr (aci AI) LB SP a \/ aextra_addr a;
    gk_client : forall L RNG (s : PS) CL FB FL (m : mem) a,
        AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m -> gc_P c L RNG s FB m -> 0 <= a < 2^64 -> gc_dom c L s FB a -> ~ client_reg FL CL a;
    gk_drv : forall L (s : PS) FB a, gc_dom c L s FB a -> ~ drv_static a }.

  Fixpoint gconj (cs : list gcomp) (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    match cs with
    | [] => True
    | c :: cs' => gc_P c L RNG s FB m /\ gconj cs' L RNG s FB m
    end.

  #[using="Type"] Lemma gconj_In : forall cs c L RNG s FB m, gconj cs L RNG s FB m -> In c cs -> gc_P c L RNG s FB m.
  Proof. induction cs as [|c0 cs IH]; intros c L RNG s FB m G HI; [destruct HI|]. destruct G as [G0 G]. destruct HI as [<-|HI]; [exact G0| eapply IH; eassumption]. Qed.

  #[using="Type"] Lemma gconj_map : forall cs L RNG s FB m L' RNG' s' FB' m',
    gconj cs L RNG s FB m -> (forall c, In c cs -> gc_P c L RNG s FB m -> gc_P c L' RNG' s' FB' m') -> gconj cs L' RNG' s' FB' m'.
  Proof.
    induction cs as [|c0 cs IH]; intros L RNG s FB m L' RNG' s' FB' m' G HM; [exact I|]. destruct G as [G0 G]. split.
    - apply HM; [left; reflexivity| exact G0].
    - eapply IH; [exact G|]. intros c Hc. apply HM. right. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Definition GSTAT_of (cs : list gcomp) (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    (exists e : word, rw_cells asegs m (ATP + -164) [C4 e]) /\ gconj cs L RNG s FB m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma outside_of : forall (W : list (Z * Z)) a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a HW; [exact I|]. cbn [outside]. split.
    - exact (HW (lo, hi) (or_introl eq_refl)).
    - apply IH. intros iv Hi. apply HW. right. exact Hi.
  Qed.
  #[using="Type"] Lemma outside_app2 : forall (W1 W2 : list (Z * Z)) a, outside W1 a -> outside W2 a -> outside (W1 ++ W2) a.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a O1 O2; [exact O2|]. cbn [app outside] in *. destruct O1 as [O O1]. split; [exact O| apply IH; assumption]. Qed.
  #[using="Type"] Lemma client_ivA_nil : forall FL (CL : list cblk) iv, client_ivA [] CL iv -> client_ivA FL CL iv.
  Proof.
    intros FL CL iv [K|[K|[K|K]]]; [left; exact K| right; left; exact K| |].
    - unfold iv_in_frames in K. apply Exists_nil in K. destruct K.
    - unfold iv_in_frame_shadow in K. apply Exists_nil in K. destruct K.
  Qed.
  #[using="Type"] Lemma client_iv_reg : forall FL (CL : list cblk) iv a, client_ivA FL CL iv -> fst iv <= a < snd iv -> client_reg FL CL a.
  Proof.
    intros FL CL [lo hi] a K Ha. cbn [fst snd] in *. unfold client_reg, client_keeps. destruct K as [K|[K|[K|K]]]; cbn [fst snd] in K.
    - left. lia.
    - right; left. unfold iv_in_block in K. apply Exists_exists in K as (b & Hb & H1 & H2). cbn [fst snd] in H1, H2.
      apply in_block_In. exists b. split; [exact Hb| lia].
    - right; right; left. unfold iv_in_frames in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      apply in_frames_In. exists fr. split; [exact Hf| lia].
    - right; right; right. unfold iv_in_frame_shadow in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      apply in_frame_sh_In. exists fr. split; [exact Hf| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="AF AI_block_tls"] Lemma tls_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> ATP + -200 <= a < ATP + 304 -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. unfold client_reg, client_keeps in K.
    (pose proof atp_lin as ndP__; nd_pre ndP__ 3%nat; intros (TL & _) _ TSH; nd_post). pose proof ATPv_sh as TSH'. unfold ATP in *.
    destruct K as [K|[K|[K|K]]].
    - lia.
    - apply in_block_In in K as (b & Hb & Rb).
      pose proof (AI_block_tls _ _ _ _ _ _ AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D. unfold ATP in D. lia.
    - apply in_frames_In in K as (fr & Hf & Rf).
      pose proof (AI_block_tls _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) as D. unfold fkb_of in D. cbn [ab_addr ab_size] in D. unfold ATP in D. lia.
    - apply in_frame_sh_In in K as (fr & Hf & Rf).
      (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ _ _ BAND TOP _; nd_post).
      (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post). unfold AIMG_HI in IMG. pose proof atop_range as AR.
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
      clear - Rf IMG TOP TSH' Ha AR. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AF"] Lemma client_reg_cases : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> client_reg FL CL a ->
    ATOP + 4096 <= a \/ (0x604000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP)
    \/ (exists F n, 0x604000 <= F /\ F + n <= ATOP /\ F mod 64 = 0 /\ 0 <= n /\ F / 8 + 2147450880 <= a < F / 8 + 2147450880 + n / 8).
  Proof.
    intros L RNG st CL FB FL m a AH K. unfold client_reg, client_keeps in K. destruct K as [K|[K|[K|K]]].
    - left. exact K.
    - apply in_block_In in K as (b & Hb & Rb).
      (nd_pre (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) 3%nat; intros _ BR _; nd_post).
      destruct BR as (BAND & _). unfold ablk, AIMG_HI, KLS in BAND. right. destruct BAND as [[B1 B2]|[B1 B2]]; [left| right; left]; lia.
    - apply in_frames_In in K as (fr & Hf & Rf).
      (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ _ _ BAND TOP _; nd_post).
      unfold ablk, AIMG_HI, KLS in BAND. right. destruct BAND as [[B1 B2]|[B1 B2]]; [left| right; left]; lia.
    - apply in_frame_sh_In in K as (fr & Hf & Rf).
      (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post).
      (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post). unfold AIMG_HI in IMG.
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
      right; right; right. exists (fb_addr fr), (fb_size fr). split; [exact IMG|]. split; [exact TOP|]. split; [exact F64|]. split; [clear - Rf; Z.div_mod_to_equations; lia| exact Rf].
  Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma img_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> 0 <= a < AIMG_HI -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. pose proof atop_range as AR. unfold AIMG_HI in *.
    destruct (client_reg_cases _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
    all: try (clear - Ha C1 C5; Z.div_mod_to_equations; lia).
  Qed.
  #[using="AF"] Lemma imsh_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. pose proof atop_range as AR. unfold AIMSH_LO, AIMSH_LEN in *.
    destruct (client_reg_cases _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
    all: try (clear - Ha C1 C5; Z.div_mod_to_equations; lia).
  Qed.
  #[using="AF"] Lemma stksh_not_client : forall L RNG st CL FB FL (m : mem) a,
    AHEAP AI L RNG st (LBof CL FB FL) m -> ATOP / 8 + 2147450880 <= a < 0x10007fff8000 -> ~ client_reg FL CL a.
  Proof.
    intros L RNG st CL FB FL m a AH Ha K. pose proof atop_range as AR. unfold AIMG_HI in *.
    destruct (client_reg_cases _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
    all: try (clear - Ha C2 C3 C4 C5 AR; Z.div_mod_to_equations; lia).
  Qed.

  #[using="Type"] Lemma imsh_not_drv : forall a, AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN -> ~ drv_static a.
  Proof.
    intros a Ha [D|D]; unfold AIMSH_LO, AIMSH_LEN, READ_STAGE in *; [lia|]. pose proof ATPv_sh as TS. unfold ATP in D. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Laws.
    Variable cs : list gcomp.
    Hypothesis CSOK : Forall gcomp_ok cs.
    #[local] Notation GSTAT := (GSTAT_of cs).

    #[using="Type"] Lemma errno_agree : forall (P : Z -> Prop) (m m' : mem),
      (exists e : word, rw_cells asegs m (ATP + -164) [C4 e]) -> agrees_on P m m' -> (forall a, ATP + -164 <= a < ATP + -160 -> P a) ->
      exists e : word, rw_cells asegs m' (ATP + -164) [C4 e].
    Proof.
      intros P m m' [e HE] AG HP. exists e. eapply agrees_rw_cells; [exact AG| exact HE|].
      intros a Ha. apply HP. cbn [cells_size csize Nat.add] in Ha. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls CSOK"] Theorem GS_client_frame : forall L RNG (s : PS) CL FB FL (m m' : mem) W,
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' -> Forall (client_ivA FL CL) W -> GSTAT L RNG s FB m'.
    Proof.
      intros L RNG s CL FB FL m m' W G MU WM FW. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (ERR & GC); nd_post).
      assert (OUT : forall a, 0 <= a < 2^64 -> ~ client_reg FL CL a -> outside W a).
      { intros a Ha NC. apply outside_of. intros iv Hi Ra. apply NC. eapply client_iv_reg; [exact (proj1 (Forall_forall _ _) FW iv Hi)| exact Ra]. }
      split.
      - eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        apply (agrees_on_of_munch _ W); [exact MU| exact WM|]. intros a Ha Ra. apply OUT; [exact Ha|].
        eapply tls_not_client; [exact AH| lia].
      - eapply gconj_map; [exact GC|]. intros c Hc PC. pose proof (proj1 (Forall_forall _ _) CSOK c Hc) as OK.
        eapply (gk_agree c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
        apply (agrees_on_of_munch _ W); [exact MU| exact WM|]. intros a Ha Da. apply OUT; [exact Ha|].
        eapply (gk_client c OK); eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="CSOK"] Theorem GS_pres : forall L RNG RNG' (s s' : PS) FB (LB : list ablock) SP (m m' : mem),
      GSTAT L RNG s FB m -> fp_le RNG RNG' -> aheap_pres (aci AI) LB SP m m' -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP ->
      ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> GSTAT L RNG' s' FB m'.
    Proof.
      intros L RNG RNG' s s' FB LB SP m m' (ERR & GC) FP HP HFB HSP E1 E2 E3. split.
      - eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
        intros a Ha Ra. apply HP; [exact Ha|]. right. left. left. unfold ATP in Ra. lia.
      - eapply gconj_map; [exact GC|]. intros c Hc PC. pose proof (proj1 (Forall_forall _ _) CSOK c Hc) as OK.
        eapply (gk_agree c OK); [exact PC| exact FP| | exact E1| exact E2| exact E3].
        intros a Ha Da. apply HP; [exact Ha|]. eapply (gk_pres c OK); eassumption.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis CI_RS : exists iv, In iv (aci AI) /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.

    #[using="AF CI_RS"] Lemma drv_iv_arange : forall L RNG (s : PS) CL FB FL (m : mem) iv, GIOA_real AI GSTAT L RNG s CL FB FL m -> drv_ivA CL iv ->
      aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv).
    Proof.
      intros L RNG s CL FB FL m iv G [K|K]; [eapply (client_iv_arange AI AF); [exact G| apply client_ivA_nil; exact K]|].
      destruct K as [K1 K2]. destruct CI_RS as (iv0 & Hiv & H1 & H2). left. right. left. exists iv0. split; [exact Hiv|]. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma drv_outside : forall FL CL W a, Forall (drv_ivA CL) W -> ~ client_reg FL CL a -> ~ drv_static a -> outside W a.
    Proof.
      intros FL CL W a FW NC ND. apply outside_of. intros iv Hi Ra.
      destruct (proj1 (Forall_forall _ _) FW iv Hi) as [K|[K1 K2]].
      - apply NC. eapply client_iv_reg; [apply client_ivA_nil; exact K| exact Ra].
      - apply ND. left. unfold READ_STAGE in *. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="AF AI_block_tls"] Lemma errno_outside : forall L RNG st CL FB FL (m : mem) W a,
      AHEAP AI L RNG st (LBof CL FB FL) m -> Forall (drv_ivA CL) W -> ATP + -164 <= a < ATP + -160 -> outside W a.
    Proof.
      intros L RNG st CL FB FL m W a AH FW Ra. apply outside_of. intros iv Hi Ri.
      destruct (proj1 (Forall_forall _ _) FW iv Hi) as [K|[K1 K2]].
      - eapply (tls_not_client _ _ _ CL FB FL m a AH); [lia|]. eapply client_iv_reg; [apply client_ivA_nil; exact K| exact Ri].
      - pose proof ATPv_img as TI. unfold ATP, READ_STAGE in *. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="AF CSOK CI_RS"] Lemma drv_frame_gen : forall L RNG (s : PS) CL FB FL (m m' : mem) W X,
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch (X ++ W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
      Forall (fun iv => aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                        \/ aahm_client (fst iv) (snd iv - fst iv)) X ->
      (forall a, 0 <= a < 2^64 -> outside X a \/ drv_static a) ->
      (exists e : word, rw_cells asegs m' (ATP + -164) [C4 e]) ->
      GIOA_real AI GSTAT L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W X G MU WM FW FX HX ERR'. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH RV AD EF SZ ND (ERR & GC); nd_post).
      split.
      { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. apply Forall_app. split; [exact FX|].
        eapply Forall_impl; [| exact FW]. intros iv K. left. eapply drv_iv_arange; eassumption. }
      split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      split; [exact ERR'|].
      eapply gconj_map; [exact GC|]. intros c Hc PC. pose proof (proj1 (Forall_forall _ _) CSOK c Hc) as OK.
      eapply (gk_agree c OK); [exact PC| apply fp_le_refl| | reflexivity| reflexivity| reflexivity].
      apply (agrees_on_of_munch _ (X ++ W)); [exact MU| exact WM|]. intros a Ha Da.
      apply outside_app2.
      - destruct (HX a Ha) as [O|D]; [exact O| exfalso; exact (gk_drv c OK _ _ _ _ Da D)].
      - apply (drv_outside FL CL); [exact FW| eapply (gk_client c OK); eassumption| exact (gk_drv c OK _ _ _ _ Da)].
    Qed.

    #[using="AF AI_block_tls CSOK CI_RS"] Theorem gd_frame_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W,
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W -> GIOA_real AI GSTAT L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W G MU WM FW. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (ERR & _); nd_post).
      apply (drv_frame_gen L RNG s CL FB FL m m' W []); [exact G| exact MU| exact WM| exact FW| constructor| intros a _; left; exact I|].
      eapply (errno_agree (fun a => ATP + -164 <= a < ATP + -160)); [exact ERR| | intros a Ha; exact Ha].
      apply (agrees_on_of_munch _ W); [exact MU| exact WM|]. intros a Ha Ra. eapply errno_outside; eassumption.
    Qed.

    #[using="AF CSOK CI_RS"] Theorem gd_frame_errno_real : forall L RNG (s : PS) CL FB FL (m m' : mem) W (e : word),
      GIOA_real AI GSTAT L RNG s CL FB FL m -> munch ((ATP + -164, ATP + -160) :: W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
      rw_cells asegs m' (ATP + -164) [C4 e] -> GIOA_real AI GSTAT L RNG s CL FB FL m'.
    Proof.
      intros L RNG s CL FB FL m m' W e G MU WM FW HE.
      apply (drv_frame_gen L RNG s CL FB FL m m' W [(ATP + -164, ATP + -160)]); [exact G| exact MU| exact WM| exact FW| | | exists e; exact HE].
      - constructor; [| constructor]. right. left. cbn [fst snd]. unfold atls_client, ATP. left. lia.
      - intros a Ha. destruct (Z_lt_ge_dec a (ATP + -164)) as [LT|GE]; [left; cbn [outside]; split; [lia| exact I]|].
        destruct (Z_lt_ge_dec a (ATP + -160)) as [LT2|GE2]; [right; right; lia| left; cbn [outside]; split; [lia| exact I]].
    Qed.

  End Laws.
End GStatKit.
End CANSEC1.
End TwB.
