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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto AMalloc_iface AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.AFake_free7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ablock_shadow_unpoisoned : forall (m : mem) A n, ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> unpoisoned m A (A + n).
Proof.
  intros m A n SH A8 A0 N0 AN. split; [lia|]. split; [lia|].
  intros G H0 H1 H2.
  assert (E : ASHOFF + G = shad A + (G - A / 8)) by (rewrite shad_div; lia).
  exists (Z_to_bv 8 (if 8 * (G - A / 8) + 8 <=? n then 0 else n - 8 * (G - A / 8))). split.
  - rewrite E. apply SH; Z.div_mod_to_equations; lia.
  - destruct (Z.leb_spec0 (8 * (G - A / 8) + 8) n).
    + left. apply sval_zero.
    + right. rewrite sval_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section GioaReal.
  Variable AI : AMallocIface.
  #[local] Abbreviation cblk := (@cblock aptr).
  #[local] Abbreviation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  Definition hb_of (b : cblk) : ablock := HB (cb_tok b) (cb_addr b) (cb_size b).
  Definition fkb_of (fr : fblock) : ablock := FKB (ff_class (fb_fn fr)) (fb_addr fr) (fb_size fr).
  Definition LBof (CL FB : list cblk) (FL : list fblock) : list ablock := map hb_of (CL ++ FB) ++ map fkb_of FL.
  Definition fflagA_real (L : alayout) (f : fframe) (Fb : Z) : Z := fflag L (ff_class f) Fb.

  #[using="Type"] Lemma hb_of_inj : forall b b', hb_of b = hb_of b' -> b = b'.
  Proof. intros [[q A] n] [[q' A'] n'] E. unfold hb_of, cb_tok, cb_addr, cb_size in E. cbn in E. injection E as -> -> ->. reflexivity. Qed.
  #[using="Type"] Lemma In_hb : forall CL FB FL b, In b (CL ++ FB) -> In (hb_of b) (LBof CL FB FL).
  Proof. intros CL FB FL b H. unfold LBof. apply in_or_app. left. apply in_map. exact H. Qed.
  #[using="Type"] Lemma In_fkb : forall CL FB FL fr, In fr FL -> In (fkb_of fr) (LBof CL FB FL).
  Proof. intros CL FB FL fr H. unfold LBof. apply in_or_app. right. apply in_map. exact H. Qed.

  (* [comment removed for export] *)
  Record AFakeIface : Prop := mkAFI {
    AF_frame : forall L RNG st LB m c F n, AHEAP AI L RNG st LB m -> In (FKB c F n) LB ->
        0 <= c < FK_NCLS /\ n = fk_fsize c /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
        /\ rng RNG F n /\ rng RNG (shad F) (n / 8) /\ wr_at asegs m (shad F) (n / 8);
    AF_flag : forall L RNG st LB m c F n, AHEAP AI L RNG st LB m -> In (FKB c F n) LB ->
        rw_cells asegs m (fflag L c F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L c F) 1
        /\ ablk (fflag L c F) (fflag L c F + 1) /\ fflag L c F + 1 <= ATOP
        /\ (forall b, In b LB -> fflag L c F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L c F);
    (* [comment removed for export] *)
    AF_rng : forall L RNG st LB m, AHEAP AI L RNG st LB m -> afake_rng L RNG;
    (* [comment removed for export] *)
    AF_release : forall L RNG st LB m m' c F n spz,
        AHEAP AI L RNG st (FKB c F n :: LB) m -> ATOP <= spz ->
        munch [(fflag L c F, fflag L c F + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' (fflag L c F) [C1 (Z_to_bv 8 0)] ->
        AHEAP AI L RNG st LB m' /\ aheap_pres (aci AI) LB spz m m';
    (* [comment removed for export] *)
    AF_sm : forall c SYM, (c = 0 /\ SYM = ASTKMALLOC0) \/ (c = 1 /\ SYM = ASTKMALLOC1) ->
      forall (L : alayout) (RNG : footprint)
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (FR : bvmap 5 word) (fc : bv 32) (m : mem) (st : astate) (LB : list ablock) (lo : Z),
      AHEAP AI L RNG st LB m -> fk_count c LB < fk_nframes c -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK -> bv_unsigned sp <= al_top L ->
      tp = Z_to_bv 64 ATP -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
      evtF asegs RNG (fun ms' => exists (F : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (j0 j1 j2 : word) (junk : list byte),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 F) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   FR (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
          /\ AHEAP AI L RNG st (FKB c F (fk_fsize c) :: LB) m'
          /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + fk_fsize c) /\ F + fk_fsize c <= ATOP
          /\ length junk = Z.to_nat (fk_fsize c - 32)
          /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (fk_fsize c - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
          /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (fk_fsize c / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (fk_fsize c / 8)))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 SYM) fc None m (seg_rom asegs));
    (* [comment removed for export] *)
    AF_sm7 : forall (L : alayout) (RNG : footprint) (req : Z)
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (FR : bvmap 5 word) (fc : bv 32) (m : mem) (st : astate) (LB : list ablock) (lo : Z),
      AHEAP AI L RNG st LB m -> fk_count 7 LB < fk_nframes 7 -> a0 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK -> bv_unsigned sp <= al_top L ->
      tp = Z_to_bv 64 ATP -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
      evtF asegs RNG (fun ms' => exists (F : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (j0 j1 j2 : word) (junk sjunk : list byte),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 F) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   FR (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
          /\ AHEAP AI L RNG st (FKB 7 F 8192 :: LB) m'
          /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + 8192) /\ F + 8192 <= ATOP
          /\ length junk = Z.to_nat (8192 - 32)
          /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (8192 - 32)) junk; C8 (Z_to_bv 64 (fflag L 7 F))]
          /\ length sjunk = Z.to_nat ((8192 - req) / 8)
          /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8))); CB (Z.to_nat ((8192 - req) / 8)) sjunk])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 ASTKMALLOC7) fc None m (seg_rom asegs));
    (* [comment removed for export] *)
    AF_sf7 : forall (L : alayout) (RNG : footprint) (req : Z)
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (FR : bvmap 5 word) (fc : bv 32) (m : mem) (st : astate) (LB : list ablock) (lo F : Z),
      AHEAP AI L RNG st (FKB 7 F 8192 :: LB) m -> a0 = Z_to_bv 64 F -> a1 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 ->
      rw_cells asegs m (F + 8184) [C8 (Z_to_bv 64 (fflag L 7 F))] -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK -> bv_unsigned sp <= al_top L ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
      evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   FR (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
          /\ AHEAP AI L RNG st LB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 ASTKFREE7) fc None m (seg_rom asegs))
  }.
  Hypothesis AF : AFakeIface.

  (* [comment removed for export] *)
  Variable GSTAT : alayout -> footprint -> PS -> list cblk -> mem -> Prop.

  Definition GIOA_real (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (m : mem) : Prop :=
       AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m
    /\ aresv_ok L (ah_resv (ps_heap s))
    /\ (forall b, In b (CL ++ FB) -> ah_addr (ps_heap s) !! cb_tok b = Some (cb_addr b))
    /\ ah_frames (ps_heap s) = map (fun fr => (fb_fn fr, fb_addr fr)) FL
    /\ Forall (fun fr => fb_size fr = ff_size (fb_fn fr)) FL
    /\ List.NoDup (map fb_fn FL)
    /\ GSTAT L RNG s FB m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_block : forall L RNG s CL FB FL m b, GIOA_real L RNG s CL FB FL m -> In b (CL ++ FB) -> blockA RNG m b.
  Proof.
    intros L RNG s CL FB FL m b (AH & _) Hin.
    destruct (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb _ _ FL _ Hin))
      as (N1 & BR & R1 & R2 & SH & WR & _ & (RLO & RHI & P1 & P2 & P3 & P4 & P5 & P6)).
    pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (IMG & A0 & _ & T47). unfold AIMG_HI in IMG. atop_facts.
    split; [exact BR|]. split; [lia|].
    split; [apply ablock_shadow_unpoisoned; [exact SH| Z.div_mod_to_equations; lia| lia| lia| lia]|].
    split; [exact R1|].
    split. { eapply rng_sub'; [exact R2|]. unfold shlen. rewrite nshad_div, Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    exists (Z.max RLO 0), (Z.min RHI KEND). unfold KEND.
    assert (E0 : (Z.max RLO 0 = RLO /\ 0 <= RLO) \/ (Z.max RLO 0 = 0 /\ RLO <= 0)) by lia.
    assert (E1 : (Z.min RHI 140737488355328 = RHI /\ RHI <= 140737488355328) \/ (Z.min RHI 140737488355328 = 140737488355328 /\ 140737488355328 <= RHI)) by lia.
    split; [lia|]. split; [lia|].
    split; [destruct E0 as [[-> _]|[-> _]]; [Z.div_mod_to_equations; lia| reflexivity]|].
    split; [destruct E1 as [[-> _]|[-> _]]; [Z.div_mod_to_equations; lia| reflexivity]|].
    split; [lia|]. split; [lia|].
    assert (SUB : shad RLO <= shad (Z.max RLO 0) /\ shad (Z.max RLO 0) + (shad (Z.min RHI 140737488355328) - shad (Z.max RLO 0)) <= shad RLO + shlen (RHI - RLO))
      by (unfold shlen; rewrite !shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    split; [eapply wr_at_sub; [exact P6| lia| lia]| eapply rng_sub'; [exact P5| exact SUB]].
  Qed.

  #[using="Type"] Lemma NoDup_map_In_inj : forall {A B} (f : A -> B) (l : list A) x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
    cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | |apply IH; assumption].
    - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
    - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  Qed.

  #[using="Type"] Lemma blocks_apart_of : forall (l : list cblk),
    List.NoDup (map hb_of l) ->
    (forall b1 b2, In b1 l -> In b2 l -> hb_of b1 <> hb_of b2 -> cb_addr b1 + cb_size b1 <= cb_addr b2 \/ cb_addr b2 + cb_size b2 <= cb_addr b1) ->
    blocks_apart l.
  Proof.
    induction l as [|b l IH]; intros ND D; [exact I|]. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND]. split.
    - apply Forall_forall. intros b' Hb'. apply D; [left; reflexivity| right; exact Hb'|].
      intros E. apply NI. rewrite E. apply in_map. exact Hb'.
    - apply IH; [exact ND|]. intros b1 b2 H1 H2. apply D; right; assumption.
  Qed.

  #[using="Type"] Lemma gr_apart : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m -> blocks_apart (CL ++ FB).
  Proof.
    intros L RNG s CL FB FL m (AH & _). pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. unfold LBof in ND.
    apply NoDup_app_remove_r in ND. apply blocks_apart_of; [exact ND|].
    intros b1 b2 H1 H2 NE.
    exact (AI_blocks_disjoint AI _ _ _ _ _ (hb_of b1) (hb_of b2) AH (In_hb _ _ FL _ H1) (In_hb _ _ FL _ H2) NE).
  Qed.

  #[using="Type"] Lemma ff_size_cases : forall f, (ff_size f = 64 \/ ff_size f = 128 \/ ff_size f = 8192).
  Proof. intros f. unfold ff_size, ff_class. destruct f; cbn; lia. Qed.

  #[using="AF"] Lemma gr_frames : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m -> Forall (frameA RNG m) FL /\ List.NoDup (map fb_fn FL).
  Proof.
    intros L RNG s CL FB FL m (AH & _ & _ & _ & SZ & ND & _). split; [| exact ND].
    apply Forall_forall. intros fr Hfr. pose proof (proj1 (Forall_forall _ _) SZ fr Hfr) as E. cbv beta in E.
    destruct (AF_frame AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB _ _ Hfr)) as (Hc & Hn & F64 & BAND & TOP & R1 & R2 & WR).
    pose proof (ff_size_cases (fb_fn fr)) as SC. pose proof (ablk_lin _ _ BAND) as (_ & F0 & _).
    assert (SHE : Z.shiftr (fb_addr fr) 3 + 2147450880 = shad (fb_addr fr)) by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    assert (SZE : Z.shiftr (fb_size fr) 3 = fb_size fr / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    unfold frameA. rewrite SHE, SZE.
    split; [exact BAND|]. split; [exact TOP|]. split; [exact F64|]. split; [lia|]. split; [exact R1|]. split; [exact R2|].
    split; [rewrite E; destruct SC as [-> |[-> | ->]]; reflexivity| exact WR].
  Qed.

  #[using="Type"] Lemma gr_fr_apart : forall L RNG s CL FB FL m a, GIOA_real L RNG s CL FB FL m -> in_frames FL a -> ~ in_block (CL ++ FB) a.
  Proof.
    intros L RNG s CL FB FL m a (AH & _) Hf Hb.
    apply in_frames_In in Hf as (fr & Hfr & Ra). apply in_block_In in Hb as (b & Hbb & Rb).
    destruct (AI_blocks_disjoint AI _ _ _ _ _ (fkb_of fr) (hb_of b) AH (In_fkb CL FB _ _ Hfr) (In_hb _ _ FL _ Hbb) ltac:(unfold fkb_of, hb_of; discriminate)) as [D|D];
      unfold fkb_of, hb_of in D; cbn [ab_addr ab_size] in D; lia.
  Qed.

  #[using="Type"] Lemma gr_fr_disj : forall L RNG s CL FB FL m fr1 fr2, GIOA_real L RNG s CL FB FL m -> In fr1 FL -> In fr2 FL -> fb_fn fr1 <> fb_fn fr2 ->
    fb_addr fr1 + fb_size fr1 <= fb_addr fr2 \/ fb_addr fr2 + fb_size fr2 <= fb_addr fr1.
  Proof.
    intros L RNG s CL FB FL m fr1 fr2 (AH & _) H1 H2 NE.
    pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. unfold LBof in ND. apply NoDup_app_remove_l in ND.
    assert (NEB : fkb_of fr1 <> fkb_of fr2).
    { intros E. apply NE. f_equal. exact (NoDup_map_In_inj fkb_of FL fr1 fr2 ND H1 H2 E). }
    destruct (AI_blocks_disjoint AI _ _ _ _ _ (fkb_of fr1) (fkb_of fr2) AH (In_fkb CL FB _ _ H1) (In_fkb CL FB _ _ H2) NEB) as [D|D];
      unfold fkb_of in D; cbn [ab_addr ab_size] in D; lia.
  Qed.

  #[using="Type"] Lemma frame_base_find : forall (FL : list fblock) f Fb n, List.NoDup (map fb_fn FL) -> In (f, Fb, n) FL ->
    List.find (fun e : fframe * Z => fframe_eqb (fst e) f) (map (fun fr => (fb_fn fr, fb_addr fr)) FL) = Some (f, Fb).
  Proof.
    induction FL as [|fr FL IH]; intros f Fb n ND Hin; [destruct Hin|].
    cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND]. cbn [map List.find fst].
    destruct Hin as [->|Hin].
    - cbn [fb_fn fb_addr fst snd]. rewrite (proj2 (fframe_eqb_eq f f) eq_refl). reflexivity.
    - destruct (fframe_eqb (fb_fn fr) f) eqn:E.
      + exfalso. apply fframe_eqb_eq in E. apply NI. rewrite E. change f with (fb_fn (f, Fb, n)). apply in_map. exact Hin.
      + eapply IH; eassumption.
  Qed.

  #[using="Type"] Lemma gr_site : forall L RNG s CL FB FL m f Fb n site off, GIOA_real L RNG s CL FB FL m -> In (f, Fb, n) FL ->
    site_frameA site = Some (f, off) -> fo_site (asan_fo site_frameA) s site = Some (Fb + off).
  Proof.
    intros L RNG s CL FB FL m f Fb n site off (_ & _ & _ & EF & _ & ND & _) Hin SF.
    cbn [fo_site asan_fo]. rewrite SF. unfold ah_frame_base. rewrite EF, (frame_base_find FL f Fb n ND Hin). reflexivity.
  Qed.

  #[using="AF"] Lemma gr_flag : forall L RNG s CL FB FL m f Fb n, GIOA_real L RNG s CL FB FL m -> In (f, Fb, n) FL ->
    rw_cells asegs m (fflagA_real L f Fb) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflagA_real L f Fb) 1
    /\ ablk (fflagA_real L f Fb) (fflagA_real L f Fb + 1) /\ fflagA_real L f Fb + 1 <= ATOP
    /\ ~ in_block (CL ++ FB) (fflagA_real L f Fb) /\ ~ in_frames FL (fflagA_real L f Fb).
  Proof.
    intros L RNG s CL FB FL m f Fb n (AH & _) Hin.
    destruct (AF_flag AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB _ _ Hin)) as (C1 & R1 & B1 & T1 & AP). cbn [fb_fn fb_addr fb_size fst snd] in *.
    unfold fflagA_real. split; [exact C1|]. split; [exact R1|]. split; [exact B1|]. split; [exact T1|]. split.
    - intros Hb. apply in_block_In in Hb as (b & Hbb & Rb). pose proof (AP _ (In_hb _ _ FL _ Hbb)) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D. lia.
    - intros Hf. apply in_frames_In in Hf as (fr & Hfr & Rf). pose proof (AP _ (In_fkb CL FB _ _ Hfr)) as D. unfold fkb_of in D. cbn [ab_addr ab_size] in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_addr : gia_addr_law asan_ops GIOA_real.
  Proof.
    intros L RNG s CL FB FL m b (_ & _ & AD & _) Hin. unfold blk_addr. cbn [ho_addr asan_ops]. unfold ah_addr_of. rewrite (AD b Hin). reflexivity.
  Qed.

  #[using="Type"] Lemma gr_perm : gia_perm_law GIOA_real.
  Proof.
    intros L RNG s CL CL' FB FL m (AH & RV & AD & EF & SZ & ND & GS) PM.
    split. { eapply (AI_perm AI); [| exact AH]. unfold LBof. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_map.
             apply Permutation.Permutation_app_tail. exact PM. }
    split; [exact RV|]. split.
    { intros b Hb. apply AD. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PM| exact Hb]| right; exact Hb]. }
    split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma geo_block : forall L RNG s CL FB FL m b, GIOA_real L RNG s CL FB FL m -> In b (CL ++ FB) -> ablk (cb_addr b) (cb_addr b + cb_size b) /\ 0 <= cb_size b.
  Proof. intros L RNG s CL FB FL m b G Hb. destruct (gr_block _ _ _ _ _ _ _ _ G Hb) as ((BAND & N0 & _) & _). split; assumption. Qed.
  #[using="AF"] Lemma geo_frame : forall L RNG s CL FB FL m fr, GIOA_real L RNG s CL FB FL m -> In fr FL ->
    ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr mod 64 = 0 /\ fb_size fr mod 64 = 0 /\ 64 <= fb_size fr.
  Proof.
    intros L RNG s CL FB FL m fr G Hf. destruct (gr_frames _ _ _ _ _ _ _ G) as [FA _].
    destruct (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _ & A64 & N64 & _ & _ & S64 & _). repeat split; assumption.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma sh_band : forall F n a, ablk F (F + n) -> F mod 8 = 0 -> n mod 8 = 0 -> 0 <= n ->
    Z.shiftr F 3 + 2147450880 <= a < Z.shiftr F 3 + 2147450880 + Z.shiftr n 3 -> KLS <= a < 0x10007fff8000.
  Proof.
    intros F n a BAND F8 N8 N0 Ha. pose proof (ablk_lin _ _ BAND) as (_ & F0 & _ & T47). rewrite !Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    unfold KLS. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma client_iv_arange : forall L RNG s CL FB FL m iv, GIOA_real L RNG s CL FB FL m -> client_ivA FL CL iv ->
    aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv).
  Proof.
    intros L RNG s CL FB FL m [lo hi] G [K|[K|[K|K]]]; cbn [fst snd] in *; [left; left; exact K| | |].
    - unfold iv_in_block in K. apply Exists_exists in K as (b & Hb & H1 & H2). cbn [fst snd] in H1, H2.
      right; left. exists (hb_of b). split; [apply In_hb; apply in_or_app; left; exact Hb|]. unfold hb_of; cbn [ab_addr ab_size]. lia.
    - unfold iv_in_frames in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      right; left. exists (fkb_of fr). split; [apply In_fkb; exact Hf|]. unfold fkb_of; cbn [ab_addr ab_size]. lia.
    - unfold iv_in_frame_shadow in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      destruct (geo_frame _ _ _ _ _ _ _ _ G Hf) as (BAND & A64 & N64 & N0). pose proof (ablk_lin _ _ BAND) as (_ & F0 & _).
      right; right. right; right. exists (ff_class (fb_fn fr)), (fb_addr fr), (fb_size fr). split; [exact (In_fkb CL FB _ _ Hf)|].
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in H1, H2 by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in H2 by lia. change (2^3) with 8 in H1, H2.
      assert (E1 : fb_addr fr = 8 * (fb_addr fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64; Z.div_mod_to_equations; lia]).
      assert (E2 : fb_size fr = 8 * (fb_size fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64; Z.div_mod_to_equations; lia]).
      unfold ASHOFF. clear - H1 H2 E1 E2. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis GS_client_frame : forall L RNG s CL FB FL m m' W, GIOA_real L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
      Forall (client_ivA FL CL) W -> GSTAT L RNG s FB m'.

  #[using="AF GS_client_frame"] Lemma gr_client_frame : forall L RNG s CL FB FL m m' W, GIOA_real L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (client_ivA FL CL) W -> GIOA_real L RNG s CL FB FL m'.
  Proof.
    intros L RNG s CL FB FL m m' W G MU WM FW. pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    split. { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. eapply Forall_impl; [|exact FW]. intros iv K. left. eapply client_iv_arange; eassumption. }
    split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
    eapply GS_client_frame; eassumption.
  Qed.
  #[using="AF GS_client_frame"] Lemma gr_frame : forall L RNG s CLc PB FB FL m m' W, GIOA_real L RNG s (CLc ++ PB) FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (pcap_iv FL PB) W -> GIOA_real L RNG s (CLc ++ PB) FB FL m'.
  Proof.
    intros L RNG s CLc PB FB FL m m' W G MU WM FW. eapply gr_client_frame; [exact G| exact MU| exact WM|].
    eapply Forall_impl; [|exact FW]. intros iv [K|[K|[K|K]]]; [left; exact K| right; left| right; right; left; exact K| right; right; right; exact K].
    unfold iv_in_block in *. apply Exists_app. right. exact K.
  Qed.

  #[using="Type"] Lemma NoDup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    intros A l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
    cbn [app] in ND. apply List.NoDup_cons_iff in ND as [NI ND]. destruct H1 as [<-|H1]; [apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND H1 H2)].
  Qed.

  #[using="Type"] Lemma outside_app_intro : forall (W1 W2 : list ivl) a, outside W1 a -> outside W2 a -> outside (W1 ++ W2) a.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a O1 O2; [exact O2|]. destruct O1 as [N O1]. split; [exact N| apply IH; assumption]. Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma gr_keepsx : forall L RNG s CLc PB FB FLc FLo m m' W WX SP, GIOA_real L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
    Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
    ATOP + 4096 <= SP -> agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W WX SP G MU WM FW HSP.
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [K OX]. apply outside_app_intro; [| exact OX]. clear MU OX WX.
    pose proof (gr_apart _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & _ & BX).
    destruct (gr_frames _ _ _ _ _ _ _ G) as [_ FND].
    assert (GB : forall b, In b (CLc ++ PB) -> ablk (cb_addr b) (cb_addr b + cb_size b))
      by (intros b Hb; exact (proj1 (geo_block _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; exact Hb)))).
    assert (GF : forall fr, In fr (FLo ++ FLc) -> ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr mod 64 = 0 /\ fb_size fr mod 64 = 0 /\ 64 <= fb_size fr)
      by (intros fr Hf; exact (geo_frame _ _ _ _ _ _ _ _ G Hf)).
    assert (FD : forall fr fr', In fr FLc -> In fr' FLo -> fb_addr fr + fb_size fr <= fb_addr fr' \/ fb_addr fr' + fb_size fr' <= fb_addr fr).
    { intros fr fr' H1 H2. apply (gr_fr_disj _ _ _ _ _ _ _ fr fr' G); [apply in_or_app; right; exact H1| apply in_or_app; left; exact H2|].
      rewrite map_app in FND. intros E. eapply (NoDup_app_disj _ _ (fb_fn fr') FND); [apply in_map; exact H2| rewrite <- E; apply in_map; exact H1]. }
    atop_facts.
    induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [Hiv FW]. split; [| apply IH; exact FW]. clear IH FW.
    cbn [fst snd] in Hiv. intros Hin.
    (* [comment removed for export] *)
    assert (KA : SP <= a
                 \/ (exists b, In b CLc /\ cb_addr b <= a < cb_addr b + cb_size b)
                 \/ (exists fr, In fr FLc /\ fb_addr fr <= a < fb_addr fr + fb_size fr)
                 \/ (exists fr, In fr FLc /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3)).
    { destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; apply in_block_In; exact K| right; right; left; apply in_frames_In; exact K
                                   | right; right; right; apply in_frame_sh_In; exact K]. }
    clear K.
    (* [comment removed for export] *)
    assert (BANDa : forall F n, ablk F (F + n) -> F <= a < F + n -> ~ (KLS <= a < 0x10007fff8000)) by (intros F n B R X; exact (ablk_clear_band _ _ a B X R)).
    destruct Hiv as [[I1 I2]|[Hiv|[Hiv|Hiv]]].
    - (* [comment removed for export] *)
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
      + pose proof (ablk_lin _ _ (GB b ltac:(apply in_or_app; left; exact Hb))) as (_ & _ & T & _). lia.
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & _). pose proof (ablk_lin _ _ B) as (_ & _ & T & _). lia.
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R). lia.
    - (* [comment removed for export] *)
      unfold iv_in_block in Hiv. apply Exists_exists in Hiv as (b' & Hb' & H1 & H2). cbn [fst snd] in H1, H2.
      pose proof (GB b' ltac:(apply in_or_app; right; exact Hb')) as B'. pose proof (ablk_lin _ _ B') as (_ & _ & T' & _).
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
      + pose proof (BX b b' Hb Hb') as AP. unfold apart in AP. lia.
      + apply (gr_fr_apart _ _ _ _ _ _ _ a G); [apply in_frames_In; exists fr; split; [apply in_or_app; right; exact Hf| exact R]|].
        apply in_block_In. exists b'. split; [apply in_or_app; left; apply in_or_app; right; exact Hb'| lia].
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R) as SB.
        apply (BANDa _ _ B' ltac:(lia)). exact SB.
    - (* [comment removed for export] *)
      unfold iv_in_frames in Hiv. apply Exists_exists in Hiv as (fr' & Hf' & H1 & H2). cbn [fst snd] in H1, H2.
      destruct (GF fr' ltac:(apply in_or_app; left; exact Hf')) as (B' & _). pose proof (ablk_lin _ _ B') as (_ & _ & T' & _).
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
      + apply (gr_fr_apart _ _ _ _ _ _ _ a G); [apply in_frames_In; exists fr'; split; [apply in_or_app; left; exact Hf'| lia]|].
        apply in_block_In. exists b. split; [apply in_or_app; left; apply in_or_app; left; exact Hb| exact R].
      + pose proof (FD fr fr' Hf Hf'). lia.
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R) as SB.
        apply (BANDa _ _ B' ltac:(lia)). exact SB.
    - (* [comment removed for export] *)
      unfold iv_in_frame_shadow in Hiv. apply Exists_exists in Hiv as (fr' & Hf' & H1 & H2). cbn [fst snd] in H1, H2.
      destruct (GF fr' ltac:(apply in_or_app; left; exact Hf')) as (B' & A64' & N64' & N0').
      assert (SB' : KLS <= a < 0x10007fff8000)
        by (apply (sh_band _ _ a B' ltac:(clear - A64'; Z.div_mod_to_equations; lia) ltac:(clear - N64'; Z.div_mod_to_equations; lia) ltac:(lia)); lia).
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [unfold KLS in SB'; lia| | |].
      + exact (BANDa _ _ (GB b ltac:(apply in_or_app; left; exact Hb)) R SB').
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & _). exact (BANDa _ _ B R SB').
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (ablk_lin _ _ B) as (_ & F0 & _). pose proof (ablk_lin _ _ B') as (_ & F0' & _).
        pose proof (FD fr fr' Hf Hf') as D.
        rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3), (Z.shiftr_div_pow2 (fb_size fr) 3) in R by lia.
        rewrite (Z.shiftr_div_pow2 (fb_addr fr') 3) in H1, H2 by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr') 3) in H2 by lia. change (2^3) with 8 in *.
        assert (E1 : fb_addr fr = 8 * (fb_addr fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64; Z.div_mod_to_equations; lia]).
        assert (E2 : fb_size fr = 8 * (fb_size fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64; Z.div_mod_to_equations; lia]).
        assert (E3 : fb_addr fr' = 8 * (fb_addr fr' / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64'; Z.div_mod_to_equations; lia]).
        assert (E4 : fb_size fr' = 8 * (fb_size fr' / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64'; Z.div_mod_to_equations; lia]).
        clear - R H1 H2 Hin D E1 E2 E3 E4. lia.
  Qed.
  #[using="AF"] Lemma gr_keeps : forall L RNG s CLc PB FB FLc FLo m m' W SP, GIOA_real L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
    ATOP + 4096 <= SP -> agrees_on (client_keeps FLc CLc SP) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W SP G MU WM FW HSP.
    eapply agrees_on_weaken; [eapply (gr_keepsx _ _ _ _ _ _ _ _ _ _ W [] SP G); [rewrite app_nil_r; exact MU| exact WM| exact FW| exact HSP]|].
    intros a K. split; [exact K| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma pres_keeps : forall L RNG s CL0 FB0 FL0 FL m0 (LB : list ablock) SP (m m' : mem) (CL FB : list cblk),
    GIOA_real L RNG s CL0 FB0 FL0 m0 -> incl FL FL0 ->
    aheap_pres (aci AI) LB SP m m' -> (forall b, In b (LBof CL FB FL) -> In b LB) -> agrees_on (client_keeps FL CL SP) m m'.
  Proof.
    intros L RNG s CL0 FB0 FL0 FL m0 LB SP m m' CL FB G IFL HP INC a Ha K. apply HP; [exact Ha|]. left.
    destruct K as [K|[K|[K|K]]].
    - left. exact K.
    - right; right; left. apply in_block_In in K as (b & Hb & R). exists (hb_of b). split; [apply INC; apply In_hb; apply in_or_app; left; exact Hb| unfold hb_of; cbn [ab_addr ab_size]; exact R].
    - right; right; left. apply in_frames_In in K as (fr & Hf & R). exists (fkb_of fr). split; [apply INC; apply In_fkb; exact Hf| unfold fkb_of; cbn [ab_addr ab_size]; exact R].
    - right; right; right. apply in_frame_sh_In in K as (fr & Hf & R).
      destruct (geo_frame _ _ _ _ _ _ _ _ G (IFL _ Hf)) as (BAND & A64 & N64 & N0). pose proof (ablk_lin _ _ BAND) as (_ & F0 & _).
      exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; right. exists (ff_class (fb_fn fr)), (fb_addr fr), (fb_size fr). split; [apply INC; exact (In_fkb CL FB _ _ Hf)|].
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3), (Z.shiftr_div_pow2 (fb_size fr) 3) in R by lia. change (2^3) with 8 in R.
      assert (E1 : fb_addr fr = 8 * (fb_addr fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64; Z.div_mod_to_equations; lia]).
      assert (E2 : fb_size fr = 8 * (fb_size fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64; Z.div_mod_to_equations; lia]).
      unfold ASHOFF. clear - R E1 E2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_rt : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m -> artcells m /\ rw_cells asegs m GOT_UAR [C8 (Z_to_bv 64 0xae600)].
  Proof.
    intros L RNG s CL FB FL m (AH & _). split; [exact (AI_rtcells AI _ _ _ _ _ AH)|].
    apply (relro_word m GOT_UAR 0xae600 (AI_relro AI _ _ _ _ _ AH)); [unfold GOT_UAR, ARELRO_LO; lia| unfold GOT_UAR, ARELRO_HI; lia| vm_compute; reflexivity].
  Qed.

  Hypothesis GS_globals : forall L RNG s FB m, GSTAT L RNG s FB m ->
      wr_at asegs m 0x7fffa000 779776 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
  Hypothesis GS_tls : forall L RNG s FB m, GSTAT L RNG s FB m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504.
  Hypothesis GS_stdin_unp : forall L RNG s FB m, GSTAT L RNG s FB m -> unpoisoned m STDIN_P (STDIN_P + 8).
  Hypothesis GS_stack : forall L RNG s FB m A n, GSTAT L RNG s FB m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
      unpoisoned m A (A + n) /\ arenaA RNG m A n.
  (* [comment removed for export] *)
  Hypothesis OBL_AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.

  #[using="OBL_AI_block_tls"] Lemma gr_tls_apart : forall L RNG s CL FB FL m a, GIOA_real L RNG s CL FB FL m -> in_block (CL ++ FB) a \/ in_frames FL a ->
    ~ (ATP + -200 <= a < ATP + -200 + 504).
  Proof.
    intros L RNG s CL FB FL m a (AH & _) [K|K] R.
    - apply in_block_In in K as (b & Hb & Rb). pose proof (OBL_AI_block_tls _ _ _ _ _ _ AH (In_hb _ _ FL _ Hb)) as D. unfold hb_of in D; cbn [ab_addr ab_size] in D. lia.
    - apply in_frames_In in K as (fr & Hf & Rf). pose proof (OBL_AI_block_tls _ _ _ _ _ _ AH (In_fkb CL FB _ _ Hf)) as D. unfold fkb_of in D; cbn [ab_addr ab_size] in D. lia.
  Qed.

  #[using="GS_stdin_unp"] Lemma gr_stdin : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m ->
    rw_cells asegs m GOT_STDIN [C8 (Z_to_bv 64 STDIN_P)] /\ rw_cells asegs m STDIN_P [C8 (Z_to_bv 64 STDIN_FILE)] /\ unpoisoned m STDIN_P (STDIN_P + 8).
  Proof.
    intros L RNG s CL FB FL m (AH & _ & _ & _ & _ & _ & GS). pose proof (AI_relro AI _ _ _ _ _ AH) as RR.
    split; [apply (relro_word m GOT_STDIN STDIN_P RR); [unfold GOT_STDIN, ARELRO_LO; lia| unfold GOT_STDIN, ARELRO_HI; lia| vm_compute; reflexivity]|].
    split; [apply (relro_word m STDIN_P STDIN_FILE RR); [unfold STDIN_P, ARELRO_LO; lia| unfold STDIN_P, ARELRO_HI; lia| vm_compute; reflexivity]|].
    exact (GS_stdin_unp _ _ _ _ _ GS).
  Qed.

  (* [comment removed for export] *)
  #[using="AF GS_client_frame GS_globals GS_tls GS_stdin_unp GS_stack OBL_AI_block_tls"] Theorem gioa_real_laws : gia_laws (asan_fo site_frameA) GIOA_real fflagA_real.
  Proof.
    constructor.
    - exact gr_block.
    - exact gr_apart.
    - exact gr_frames.
    - exact gr_fr_apart.
    - exact gr_fr_disj.
    - exact gr_site.
    - exact gr_flag.
    - exact gr_client_frame.
    - exact gr_frame.
    - exact gr_keeps.
    - exact gr_keepsx.
    - exact gr_rt.
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & GS). exact (GS_globals _ _ _ _ _ GS).
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & GS). exact (GS_tls _ _ _ _ _ GS).
    - exact gr_tls_apart.
    - exact gr_stdin.
    - intros L RNG s CL FB FL m A n (_ & _ & _ & _ & _ & _ & GS). exact (GS_stack _ _ _ _ _ A n GS).
    - intros L RNG s CL FB FL m (AH & _).
      apply (relro_word m GOT_MEMSET 0xa7360 (AI_relro AI _ _ _ _ _ AH)); [unfold GOT_MEMSET, ARELRO_LO; lia| unfold GOT_MEMSET, ARELRO_HI; lia| vm_compute; reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_got : @Pcap_iface_gotA.gia_got_law aheap aptr GIOA_real.
  Proof.
    intros L RNG s CL FB FL m (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RR.
    unfold Pcap_iface_gotA.GOT_PCAP_ADDR, Pcap_iface_gotA.GOT_INSTALL_BPF, Pcap_iface_gotA.GOT_BREAKLOOP, PK. cbn [pk_oneshot pk_cleanup_sf].
    assert (W : forall A v, ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true -> rw_cells asegs m A [C8 (Z_to_bv 64 v)])
      by (intros A v H1 H2 H3; exact (relro_word m A v RR H1 H2 H3)).
    pose proof (W 0xa6128 0x86208 ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C1.
    pose proof (W 0xa6130 0x858e4 ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C2.
    pose proof (W 0xa6138 0x85f34 ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C3.
    pose proof (W 0xa6140 0x84c40 ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C4.
    pose proof (rw_cells_uncut _ _ _ _ _ C3 C4 ltac:(reflexivity)) as C34. pose proof (rw_cells_uncut _ _ _ _ _ C2 C34 ltac:(reflexivity)) as C234.
    exact (rw_cells_uncut _ _ _ _ _ C1 C234 ltac:(reflexivity)).
  Qed.
End GioaReal.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm7.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.AFake_free7.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ablock_shadow_unpoisoned : forall (m : mem) A n, ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> unpoisoned m A (A + n).
Proof.
  intros m A n SH A8 A0 N0 AN. split; [lia|]. split; [lia|].
  intros G H0 H1 H2.
  assert (E : ASHOFF + G = shad A + (G - A / 8)) by (rewrite shad_div; lia).
  exists (Z_to_bv 8 (if 8 * (G - A / 8) + 8 <=? n then 0 else n - 8 * (G - A / 8))). split.
  - rewrite E. apply SH; Z.div_mod_to_equations; lia.
  - destruct (Z.leb_spec0 (8 * (G - A / 8) + 8) n).
    + left. apply sval_zero.
    + right. rewrite sval_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section GioaReal.
  Variable AI : AMallocIface.
  #[local] Abbreviation cblk := (@cblock aptr).
  #[local] Abbreviation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  Definition hb_of (b : cblk) : ablock := HB (cb_tok b) (cb_addr b) (cb_size b).
  Definition fkb_of (fr : fblock) : ablock := FKB (ff_class (fb_fn fr)) (fb_addr fr) (fb_size fr).
  Definition LBof (CL FB : list cblk) (FL : list fblock) : list ablock := map hb_of (CL ++ FB) ++ map fkb_of FL.
  Definition fflagA_real (L : alayout) (f : fframe) (Fb : Z) : Z := fflag L (ff_class f) Fb.

  #[using="Type"] Lemma hb_of_inj : forall b b', hb_of b = hb_of b' -> b = b'.
  Proof. intros [[q A] n] [[q' A'] n'] E. unfold hb_of, cb_tok, cb_addr, cb_size in E. cbn in E. injection E as -> -> ->. reflexivity. Qed.
  #[using="Type"] Lemma In_hb : forall CL FB FL b, In b (CL ++ FB) -> In (hb_of b) (LBof CL FB FL).
  Proof. intros CL FB FL b H. unfold LBof. apply in_or_app. left. apply in_map. exact H. Qed.
  #[using="Type"] Lemma In_fkb : forall CL FB FL fr, In fr FL -> In (fkb_of fr) (LBof CL FB FL).
  Proof. intros CL FB FL fr H. unfold LBof. apply in_or_app. right. apply in_map. exact H. Qed.

  (* [comment removed for export] *)
  Record AFakeIface : Prop := mkAFI {
    AF_frame : forall L RNG st LB m c F n, AHEAP AI L RNG st LB m -> In (FKB c F n) LB ->
        0 <= c < FK_NCLS /\ n = fk_fsize c /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
        /\ rng RNG F n /\ rng RNG (shad F) (n / 8) /\ wr_at asegs m (shad F) (n / 8);
    AF_flag : forall L RNG st LB m c F n, AHEAP AI L RNG st LB m -> In (FKB c F n) LB ->
        rw_cells asegs m (fflag L c F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L c F) 1
        /\ ablk (fflag L c F) (fflag L c F + 1) /\ fflag L c F + 1 <= ATOP
        /\ (forall b, In b LB -> fflag L c F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L c F);
    (* [comment removed for export] *)
    AF_rng : forall L RNG st LB m, AHEAP AI L RNG st LB m -> afake_rng L RNG;
    (* [comment removed for export] *)
    AF_release : forall L RNG st LB m m' c F n spz,
        AHEAP AI L RNG st (FKB c F n :: LB) m -> ATOP <= spz ->
        munch [(fflag L c F, fflag L c F + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' (fflag L c F) [C1 (Z_to_bv 8 0)] ->
        AHEAP AI L RNG st LB m' /\ aheap_pres (aci AI) LB spz m m';
    (* [comment removed for export] *)
    AF_sm : forall c SYM, (c = 0 /\ SYM = ASTKMALLOC0) \/ (c = 1 /\ SYM = ASTKMALLOC1) ->
      forall (L : alayout) (RNG : footprint)
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (FR : bvmap 5 word) (fc : bv 32) (m : mem) (st : astate) (LB : list ablock) (lo : Z),
      AHEAP AI L RNG st LB m -> fk_count c LB < fk_nframes c -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK -> bv_unsigned sp <= al_top L ->
      tp = Z_to_bv 64 ATP -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
      evtF asegs RNG (fun ms' => exists (F : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (j0 j1 j2 : word) (junk : list byte),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 F) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   FR (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
          /\ AHEAP AI L RNG st (FKB c F (fk_fsize c) :: LB) m'
          /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + fk_fsize c) /\ F + fk_fsize c <= ATOP
          /\ length junk = Z.to_nat (fk_fsize c - 32)
          /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (fk_fsize c - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
          /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (fk_fsize c / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (fk_fsize c / 8)))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 SYM) fc None m (seg_rom asegs));
    (* [comment removed for export] *)
    AF_sm7 : forall (L : alayout) (RNG : footprint) (req : Z)
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (FR : bvmap 5 word) (fc : bv 32) (m : mem) (st : astate) (LB : list ablock) (lo : Z),
      AHEAP AI L RNG st LB m -> fk_count 7 LB < fk_nframes 7 -> a0 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK -> bv_unsigned sp <= al_top L ->
      tp = Z_to_bv 64 ATP -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
      evtF asegs RNG (fun ms' => exists (F : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (j0 j1 j2 : word) (junk sjunk : list byte),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 F) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   FR (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
          /\ AHEAP AI L RNG st (FKB 7 F 8192 :: LB) m'
          /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + 8192) /\ F + 8192 <= ATOP
          /\ length junk = Z.to_nat (8192 - 32)
          /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (8192 - 32)) junk; C8 (Z_to_bv 64 (fflag L 7 F))]
          /\ length sjunk = Z.to_nat ((8192 - req) / 8)
          /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8))); CB (Z.to_nat ((8192 - req) / 8)) sjunk])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 ASTKMALLOC7) fc None m (seg_rom asegs));
    (* [comment removed for export] *)
    AF_sf7 : forall (L : alayout) (RNG : footprint) (req : Z)
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (FR : bvmap 5 word) (fc : bv 32) (m : mem) (st : astate) (LB : list ablock) (lo F : Z),
      AHEAP AI L RNG st (FKB 7 F 8192 :: LB) m -> a0 = Z_to_bv 64 F -> a1 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 ->
      rw_cells asegs m (F + 8184) [C8 (Z_to_bv 64 (fflag L 7 F))] -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK -> bv_unsigned sp <= al_top L ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
      evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   FR (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
          /\ AHEAP AI L RNG st LB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 ASTKFREE7) fc None m (seg_rom asegs))
  }.
  Hypothesis AF : AFakeIface.

  (* [comment removed for export] *)
  Variable GSTAT : alayout -> footprint -> PS -> list cblk -> mem -> Prop.

  Definition GIOA_real (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (m : mem) : Prop :=
       AHEAP AI L RNG (ah_st (ps_heap s)) (LBof CL FB FL) m
    /\ aresv_ok L (ah_resv (ps_heap s))
    /\ (forall b, In b (CL ++ FB) -> ah_addr (ps_heap s) !! cb_tok b = Some (cb_addr b))
    /\ ah_frames (ps_heap s) = map (fun fr => (fb_fn fr, fb_addr fr)) FL
    /\ Forall (fun fr => fb_size fr = ff_size (fb_fn fr)) FL
    /\ List.NoDup (map fb_fn FL)
    /\ GSTAT L RNG s FB m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_block : forall L RNG s CL FB FL m b, GIOA_real L RNG s CL FB FL m -> In b (CL ++ FB) -> blockA RNG m b.
  Proof.
    intros L RNG s CL FB FL m b (AH & _) Hin.
    destruct (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb _ _ FL _ Hin))
      as (N1 & BR & R1 & R2 & SH & WR & _ & (RLO & RHI & P1 & P2 & P3 & P4 & P5 & P6)).
    pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (IMG & A0 & _ & T47). unfold AIMG_HI in IMG. atop_facts.
    split; [exact BR|]. split; [lia|].
    split; [apply ablock_shadow_unpoisoned; [exact SH| Z.div_mod_to_equations; lia| lia| lia| lia]|].
    split; [exact R1|].
    split. { eapply rng_sub'; [exact R2|]. unfold shlen. rewrite nshad_div, Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    exists (Z.max RLO 0), (Z.min RHI KEND). unfold KEND.
    assert (E0 : (Z.max RLO 0 = RLO /\ 0 <= RLO) \/ (Z.max RLO 0 = 0 /\ RLO <= 0)) by lia.
    assert (E1 : (Z.min RHI 140737488355328 = RHI /\ RHI <= 140737488355328) \/ (Z.min RHI 140737488355328 = 140737488355328 /\ 140737488355328 <= RHI)) by lia.
    split; [lia|]. split; [lia|].
    split; [destruct E0 as [[-> _]|[-> _]]; [Z.div_mod_to_equations; lia| reflexivity]|].
    split; [destruct E1 as [[-> _]|[-> _]]; [Z.div_mod_to_equations; lia| reflexivity]|].
    split; [lia|]. split; [lia|].
    assert (SUB : shad RLO <= shad (Z.max RLO 0) /\ shad (Z.max RLO 0) + (shad (Z.min RHI 140737488355328) - shad (Z.max RLO 0)) <= shad RLO + shlen (RHI - RLO))
      by (unfold shlen; rewrite !shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    split; [eapply wr_at_sub; [exact P6| lia| lia]| eapply rng_sub'; [exact P5| exact SUB]].
  Qed.

  #[using="Type"] Lemma NoDup_map_In_inj : forall {A B} (f : A -> B) (l : list A) x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
    cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | |apply IH; assumption].
    - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
    - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  Qed.

  #[using="Type"] Lemma blocks_apart_of : forall (l : list cblk),
    List.NoDup (map hb_of l) ->
    (forall b1 b2, In b1 l -> In b2 l -> hb_of b1 <> hb_of b2 -> cb_addr b1 + cb_size b1 <= cb_addr b2 \/ cb_addr b2 + cb_size b2 <= cb_addr b1) ->
    blocks_apart l.
  Proof.
    induction l as [|b l IH]; intros ND D; [exact I|]. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND]. split.
    - apply Forall_forall. intros b' Hb'. apply D; [left; reflexivity| right; exact Hb'|].
      intros E. apply NI. rewrite E. apply in_map. exact Hb'.
    - apply IH; [exact ND|]. intros b1 b2 H1 H2. apply D; right; assumption.
  Qed.

  #[using="Type"] Lemma gr_apart : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m -> blocks_apart (CL ++ FB).
  Proof.
    intros L RNG s CL FB FL m (AH & _). pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. unfold LBof in ND.
    apply NoDup_app_remove_r in ND. apply blocks_apart_of; [exact ND|].
    intros b1 b2 H1 H2 NE.
    exact (AI_blocks_disjoint AI _ _ _ _ _ (hb_of b1) (hb_of b2) AH (In_hb _ _ FL _ H1) (In_hb _ _ FL _ H2) NE).
  Qed.

  #[using="Type"] Lemma ff_size_cases : forall f, (ff_size f = 64 \/ ff_size f = 128 \/ ff_size f = 8192).
  Proof. intros f. unfold ff_size, ff_class. destruct f; cbn; lia. Qed.

  #[using="AF"] Lemma gr_frames : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m -> Forall (frameA RNG m) FL /\ List.NoDup (map fb_fn FL).
  Proof.
    intros L RNG s CL FB FL m (AH & _ & _ & _ & SZ & ND & _). split; [| exact ND].
    apply Forall_forall. intros fr Hfr. pose proof (proj1 (Forall_forall _ _) SZ fr Hfr) as E. cbv beta in E.
    destruct (AF_frame AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB _ _ Hfr)) as (Hc & Hn & F64 & BAND & TOP & R1 & R2 & WR).
    pose proof (ff_size_cases (fb_fn fr)) as SC. pose proof (ablk_lin _ _ BAND) as (_ & F0 & _).
    assert (SHE : Z.shiftr (fb_addr fr) 3 + 2147450880 = shad (fb_addr fr)) by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    assert (SZE : Z.shiftr (fb_size fr) 3 = fb_size fr / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    unfold frameA. rewrite SHE, SZE.
    split; [exact BAND|]. split; [exact TOP|]. split; [exact F64|]. split; [lia|]. split; [exact R1|]. split; [exact R2|].
    split; [rewrite E; destruct SC as [-> |[-> | ->]]; reflexivity| exact WR].
  Qed.

  #[using="Type"] Lemma gr_fr_apart : forall L RNG s CL FB FL m a, GIOA_real L RNG s CL FB FL m -> in_frames FL a -> ~ in_block (CL ++ FB) a.
  Proof.
    intros L RNG s CL FB FL m a (AH & _) Hf Hb.
    apply in_frames_In in Hf as (fr & Hfr & Ra). apply in_block_In in Hb as (b & Hbb & Rb).
    destruct (AI_blocks_disjoint AI _ _ _ _ _ (fkb_of fr) (hb_of b) AH (In_fkb CL FB _ _ Hfr) (In_hb _ _ FL _ Hbb) ltac:(unfold fkb_of, hb_of; discriminate)) as [D|D];
      unfold fkb_of, hb_of in D; cbn [ab_addr ab_size] in D; lia.
  Qed.

  #[using="Type"] Lemma gr_fr_disj : forall L RNG s CL FB FL m fr1 fr2, GIOA_real L RNG s CL FB FL m -> In fr1 FL -> In fr2 FL -> fb_fn fr1 <> fb_fn fr2 ->
    fb_addr fr1 + fb_size fr1 <= fb_addr fr2 \/ fb_addr fr2 + fb_size fr2 <= fb_addr fr1.
  Proof.
    intros L RNG s CL FB FL m fr1 fr2 (AH & _) H1 H2 NE.
    pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. unfold LBof in ND. apply NoDup_app_remove_l in ND.
    assert (NEB : fkb_of fr1 <> fkb_of fr2).
    { intros E. apply NE. f_equal. exact (NoDup_map_In_inj fkb_of FL fr1 fr2 ND H1 H2 E). }
    destruct (AI_blocks_disjoint AI _ _ _ _ _ (fkb_of fr1) (fkb_of fr2) AH (In_fkb CL FB _ _ H1) (In_fkb CL FB _ _ H2) NEB) as [D|D];
      unfold fkb_of in D; cbn [ab_addr ab_size] in D; lia.
  Qed.

  #[using="Type"] Lemma frame_base_find : forall (FL : list fblock) f Fb n, List.NoDup (map fb_fn FL) -> In (f, Fb, n) FL ->
    List.find (fun e : fframe * Z => fframe_eqb (fst e) f) (map (fun fr => (fb_fn fr, fb_addr fr)) FL) = Some (f, Fb).
  Proof.
    induction FL as [|fr FL IH]; intros f Fb n ND Hin; [destruct Hin|].
    cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND]. cbn [map List.find fst].
    destruct Hin as [->|Hin].
    - cbn [fb_fn fb_addr fst snd]. rewrite (proj2 (fframe_eqb_eq f f) eq_refl). reflexivity.
    - destruct (fframe_eqb (fb_fn fr) f) eqn:E.
      + exfalso. apply fframe_eqb_eq in E. apply NI. rewrite E. change f with (fb_fn (f, Fb, n)). apply in_map. exact Hin.
      + eapply IH; eassumption.
  Qed.

  #[using="Type"] Lemma gr_site : forall L RNG s CL FB FL m f Fb n site off, GIOA_real L RNG s CL FB FL m -> In (f, Fb, n) FL ->
    site_frameA site = Some (f, off) -> fo_site (asan_fo site_frameA) s site = Some (Fb + off).
  Proof.
    intros L RNG s CL FB FL m f Fb n site off (_ & _ & _ & EF & _ & ND & _) Hin SF.
    cbn [fo_site asan_fo]. rewrite SF. unfold ah_frame_base. rewrite EF, (frame_base_find FL f Fb n ND Hin). reflexivity.
  Qed.

  #[using="AF"] Lemma gr_flag : forall L RNG s CL FB FL m f Fb n, GIOA_real L RNG s CL FB FL m -> In (f, Fb, n) FL ->
    rw_cells asegs m (fflagA_real L f Fb) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflagA_real L f Fb) 1
    /\ ablk (fflagA_real L f Fb) (fflagA_real L f Fb + 1) /\ fflagA_real L f Fb + 1 <= ATOP
    /\ ~ in_block (CL ++ FB) (fflagA_real L f Fb) /\ ~ in_frames FL (fflagA_real L f Fb).
  Proof.
    intros L RNG s CL FB FL m f Fb n (AH & _) Hin.
    destruct (AF_flag AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB _ _ Hin)) as (C1 & R1 & B1 & T1 & AP). cbn [fb_fn fb_addr fb_size fst snd] in *.
    unfold fflagA_real. split; [exact C1|]. split; [exact R1|]. split; [exact B1|]. split; [exact T1|]. split.
    - intros Hb. apply in_block_In in Hb as (b & Hbb & Rb). pose proof (AP _ (In_hb _ _ FL _ Hbb)) as D. unfold hb_of in D. cbn [ab_addr ab_size] in D. lia.
    - intros Hf. apply in_frames_In in Hf as (fr & Hfr & Rf). pose proof (AP _ (In_fkb CL FB _ _ Hfr)) as D. unfold fkb_of in D. cbn [ab_addr ab_size] in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_addr : gia_addr_law asan_ops GIOA_real.
  Proof.
    intros L RNG s CL FB FL m b (_ & _ & AD & _) Hin. unfold blk_addr. cbn [ho_addr asan_ops]. unfold ah_addr_of. rewrite (AD b Hin). reflexivity.
  Qed.

  #[using="Type"] Lemma gr_perm : gia_perm_law GIOA_real.
  Proof.
    intros L RNG s CL CL' FB FL m (AH & RV & AD & EF & SZ & ND & GS) PM.
    split. { eapply (AI_perm AI); [| exact AH]. unfold LBof. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_map.
             apply Permutation.Permutation_app_tail. exact PM. }
    split; [exact RV|]. split.
    { intros b Hb. apply AD. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PM| exact Hb]| right; exact Hb]. }
    split; [exact EF|]. split; [exact SZ|]. split; [exact ND| exact GS].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma geo_block : forall L RNG s CL FB FL m b, GIOA_real L RNG s CL FB FL m -> In b (CL ++ FB) -> ablk (cb_addr b) (cb_addr b + cb_size b) /\ 0 <= cb_size b.
  Proof. intros L RNG s CL FB FL m b G Hb. destruct (gr_block _ _ _ _ _ _ _ _ G Hb) as ((BAND & N0 & _) & _). split; assumption. Qed.
  #[using="AF"] Lemma geo_frame : forall L RNG s CL FB FL m fr, GIOA_real L RNG s CL FB FL m -> In fr FL ->
    ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr mod 64 = 0 /\ fb_size fr mod 64 = 0 /\ 64 <= fb_size fr.
  Proof.
    intros L RNG s CL FB FL m fr G Hf. destruct (gr_frames _ _ _ _ _ _ _ G) as [FA _].
    destruct (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _ & A64 & N64 & _ & _ & S64 & _). repeat split; assumption.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma sh_band : forall F n a, ablk F (F + n) -> F mod 8 = 0 -> n mod 8 = 0 -> 0 <= n ->
    Z.shiftr F 3 + 2147450880 <= a < Z.shiftr F 3 + 2147450880 + Z.shiftr n 3 -> KLS <= a < 0x10007fff8000.
  Proof.
    intros F n a BAND F8 N8 N0 Ha. pose proof (ablk_lin _ _ BAND) as (_ & F0 & _ & T47). rewrite !Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    unfold KLS. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma client_iv_arange : forall L RNG s CL FB FL m iv, GIOA_real L RNG s CL FB FL m -> client_ivA FL CL iv ->
    aclient_range (aci AI) (LBof CL FB FL) (ATOP + 4096) (fst iv) (snd iv - fst iv).
  Proof.
    intros L RNG s CL FB FL m [lo hi] G [K|[K|[K|K]]]; cbn [fst snd] in *; [left; left; exact K| | |].
    - unfold iv_in_block in K. apply Exists_exists in K as (b & Hb & H1 & H2). cbn [fst snd] in H1, H2.
      right; left. exists (hb_of b). split; [apply In_hb; apply in_or_app; left; exact Hb|]. unfold hb_of; cbn [ab_addr ab_size]. lia.
    - unfold iv_in_frames in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      right; left. exists (fkb_of fr). split; [apply In_fkb; exact Hf|]. unfold fkb_of; cbn [ab_addr ab_size]. lia.
    - unfold iv_in_frame_shadow in K. apply Exists_exists in K as (fr & Hf & H1 & H2). cbn [fst snd] in H1, H2.
      destruct (geo_frame _ _ _ _ _ _ _ _ G Hf) as (BAND & A64 & N64 & N0). pose proof (ablk_lin _ _ BAND) as (_ & F0 & _).
      right; right. right; right. exists (ff_class (fb_fn fr)), (fb_addr fr), (fb_size fr). split; [exact (In_fkb CL FB _ _ Hf)|].
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in H1, H2 by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in H2 by lia. change (2^3) with 8 in H1, H2.
      assert (E1 : fb_addr fr = 8 * (fb_addr fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64; Z.div_mod_to_equations; lia]).
      assert (E2 : fb_size fr = 8 * (fb_size fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64; Z.div_mod_to_equations; lia]).
      unfold ASHOFF. clear - H1 H2 E1 E2. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis GS_client_frame : forall L RNG s CL FB FL m m' W, GIOA_real L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
      Forall (client_ivA FL CL) W -> GSTAT L RNG s FB m'.

  #[using="AF GS_client_frame"] Lemma gr_client_frame : forall L RNG s CL FB FL m m' W, GIOA_real L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (client_ivA FL CL) W -> GIOA_real L RNG s CL FB FL m'.
  Proof.
    intros L RNG s CL FB FL m m' W G MU WM FW. pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    split. { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. eapply Forall_impl; [|exact FW]. intros iv K. left. eapply client_iv_arange; eassumption. }
    split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
    eapply GS_client_frame; eassumption.
  Qed.
  #[using="AF GS_client_frame"] Lemma gr_frame : forall L RNG s CLc PB FB FL m m' W, GIOA_real L RNG s (CLc ++ PB) FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (pcap_iv FL PB) W -> GIOA_real L RNG s (CLc ++ PB) FB FL m'.
  Proof.
    intros L RNG s CLc PB FB FL m m' W G MU WM FW. eapply gr_client_frame; [exact G| exact MU| exact WM|].
    eapply Forall_impl; [|exact FW]. intros iv [K|[K|[K|K]]]; [left; exact K| right; left| right; right; left; exact K| right; right; right; exact K].
    unfold iv_in_block in *. apply Exists_app. right. exact K.
  Qed.

  #[using="Type"] Lemma NoDup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    intros A l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
    cbn [app] in ND. apply List.NoDup_cons_iff in ND as [NI ND]. destruct H1 as [<-|H1]; [apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND H1 H2)].
  Qed.

  #[using="Type"] Lemma outside_app_intro : forall (W1 W2 : list ivl) a, outside W1 a -> outside W2 a -> outside (W1 ++ W2) a.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a O1 O2; [exact O2|]. destruct O1 as [N O1]. split; [exact N| apply IH; assumption]. Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma gr_keepsx : forall L RNG s CLc PB FB FLc FLo m m' W WX SP, GIOA_real L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
    Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
    ATOP + 4096 <= SP -> agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W WX SP G MU WM FW HSP.
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [K OX]. apply outside_app_intro; [| exact OX]. clear MU OX WX.
    pose proof (gr_apart _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & _ & BX).
    destruct (gr_frames _ _ _ _ _ _ _ G) as [_ FND].
    assert (GB : forall b, In b (CLc ++ PB) -> ablk (cb_addr b) (cb_addr b + cb_size b))
      by (intros b Hb; exact (proj1 (geo_block _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; exact Hb)))).
    assert (GF : forall fr, In fr (FLo ++ FLc) -> ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr mod 64 = 0 /\ fb_size fr mod 64 = 0 /\ 64 <= fb_size fr)
      by (intros fr Hf; exact (geo_frame _ _ _ _ _ _ _ _ G Hf)).
    assert (FD : forall fr fr', In fr FLc -> In fr' FLo -> fb_addr fr + fb_size fr <= fb_addr fr' \/ fb_addr fr' + fb_size fr' <= fb_addr fr).
    { intros fr fr' H1 H2. apply (gr_fr_disj _ _ _ _ _ _ _ fr fr' G); [apply in_or_app; right; exact H1| apply in_or_app; left; exact H2|].
      rewrite map_app in FND. intros E. eapply (NoDup_app_disj _ _ (fb_fn fr') FND); [apply in_map; exact H2| rewrite <- E; apply in_map; exact H1]. }
    atop_facts.
    induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [Hiv FW]. split; [| apply IH; exact FW]. clear IH FW.
    cbn [fst snd] in Hiv. intros Hin.
    (* [comment removed for export] *)
    assert (KA : SP <= a
                 \/ (exists b, In b CLc /\ cb_addr b <= a < cb_addr b + cb_size b)
                 \/ (exists fr, In fr FLc /\ fb_addr fr <= a < fb_addr fr + fb_size fr)
                 \/ (exists fr, In fr FLc /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3)).
    { destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; apply in_block_In; exact K| right; right; left; apply in_frames_In; exact K
                                   | right; right; right; apply in_frame_sh_In; exact K]. }
    clear K.
    (* [comment removed for export] *)
    assert (BANDa : forall F n, ablk F (F + n) -> F <= a < F + n -> ~ (KLS <= a < 0x10007fff8000)) by (intros F n B R X; exact (ablk_clear_band _ _ a B X R)).
    destruct Hiv as [[I1 I2]|[Hiv|[Hiv|Hiv]]].
    - (* [comment removed for export] *)
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
      + pose proof (ablk_lin _ _ (GB b ltac:(apply in_or_app; left; exact Hb))) as (_ & _ & T & _). lia.
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & _). pose proof (ablk_lin _ _ B) as (_ & _ & T & _). lia.
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R). lia.
    - (* [comment removed for export] *)
      unfold iv_in_block in Hiv. apply Exists_exists in Hiv as (b' & Hb' & H1 & H2). cbn [fst snd] in H1, H2.
      pose proof (GB b' ltac:(apply in_or_app; right; exact Hb')) as B'. pose proof (ablk_lin _ _ B') as (_ & _ & T' & _).
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
      + pose proof (BX b b' Hb Hb') as AP. unfold apart in AP. lia.
      + apply (gr_fr_apart _ _ _ _ _ _ _ a G); [apply in_frames_In; exists fr; split; [apply in_or_app; right; exact Hf| exact R]|].
        apply in_block_In. exists b'. split; [apply in_or_app; left; apply in_or_app; right; exact Hb'| lia].
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R) as SB.
        apply (BANDa _ _ B' ltac:(lia)). exact SB.
    - (* [comment removed for export] *)
      unfold iv_in_frames in Hiv. apply Exists_exists in Hiv as (fr' & Hf' & H1 & H2). cbn [fst snd] in H1, H2.
      destruct (GF fr' ltac:(apply in_or_app; left; exact Hf')) as (B' & _). pose proof (ablk_lin _ _ B') as (_ & _ & T' & _).
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [lia| | |].
      + apply (gr_fr_apart _ _ _ _ _ _ _ a G); [apply in_frames_In; exists fr'; split; [apply in_or_app; left; exact Hf'| lia]|].
        apply in_block_In. exists b. split; [apply in_or_app; left; apply in_or_app; left; exact Hb| exact R].
      + pose proof (FD fr fr' Hf Hf'). lia.
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (sh_band _ _ a B ltac:(clear - A64; Z.div_mod_to_equations; lia) ltac:(clear - N64; Z.div_mod_to_equations; lia) ltac:(lia) R) as SB.
        apply (BANDa _ _ B' ltac:(lia)). exact SB.
    - (* [comment removed for export] *)
      unfold iv_in_frame_shadow in Hiv. apply Exists_exists in Hiv as (fr' & Hf' & H1 & H2). cbn [fst snd] in H1, H2.
      destruct (GF fr' ltac:(apply in_or_app; left; exact Hf')) as (B' & A64' & N64' & N0').
      assert (SB' : KLS <= a < 0x10007fff8000)
        by (apply (sh_band _ _ a B' ltac:(clear - A64'; Z.div_mod_to_equations; lia) ltac:(clear - N64'; Z.div_mod_to_equations; lia) ltac:(lia)); lia).
      destruct KA as [K|[(b & Hb & R)|[(fr & Hf & R)|(fr & Hf & R)]]]; [unfold KLS in SB'; lia| | |].
      + exact (BANDa _ _ (GB b ltac:(apply in_or_app; left; exact Hb)) R SB').
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & _). exact (BANDa _ _ B R SB').
      + destruct (GF fr ltac:(apply in_or_app; right; exact Hf)) as (B & A64 & N64 & N0).
        pose proof (ablk_lin _ _ B) as (_ & F0 & _). pose proof (ablk_lin _ _ B') as (_ & F0' & _).
        pose proof (FD fr fr' Hf Hf') as D.
        rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3), (Z.shiftr_div_pow2 (fb_size fr) 3) in R by lia.
        rewrite (Z.shiftr_div_pow2 (fb_addr fr') 3) in H1, H2 by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr') 3) in H2 by lia. change (2^3) with 8 in *.
        assert (E1 : fb_addr fr = 8 * (fb_addr fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64; Z.div_mod_to_equations; lia]).
        assert (E2 : fb_size fr = 8 * (fb_size fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64; Z.div_mod_to_equations; lia]).
        assert (E3 : fb_addr fr' = 8 * (fb_addr fr' / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64'; Z.div_mod_to_equations; lia]).
        assert (E4 : fb_size fr' = 8 * (fb_size fr' / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64'; Z.div_mod_to_equations; lia]).
        clear - R H1 H2 Hin D E1 E2 E3 E4. lia.
  Qed.
  #[using="AF"] Lemma gr_keeps : forall L RNG s CLc PB FB FLc FLo m m' W SP, GIOA_real L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
    ATOP + 4096 <= SP -> agrees_on (client_keeps FLc CLc SP) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W SP G MU WM FW HSP.
    eapply agrees_on_weaken; [eapply (gr_keepsx _ _ _ _ _ _ _ _ _ _ W [] SP G); [rewrite app_nil_r; exact MU| exact WM| exact FW| exact HSP]|].
    intros a K. split; [exact K| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="AF"] Lemma pres_keeps : forall L RNG s CL0 FB0 FL0 FL m0 (LB : list ablock) SP (m m' : mem) (CL FB : list cblk),
    GIOA_real L RNG s CL0 FB0 FL0 m0 -> incl FL FL0 ->
    aheap_pres (aci AI) LB SP m m' -> (forall b, In b (LBof CL FB FL) -> In b LB) -> agrees_on (client_keeps FL CL SP) m m'.
  Proof.
    intros L RNG s CL0 FB0 FL0 FL m0 LB SP m m' CL FB G IFL HP INC a Ha K. apply HP; [exact Ha|]. left.
    destruct K as [K|[K|[K|K]]].
    - left. exact K.
    - right; right; left. apply in_block_In in K as (b & Hb & R). exists (hb_of b). split; [apply INC; apply In_hb; apply in_or_app; left; exact Hb| unfold hb_of; cbn [ab_addr ab_size]; exact R].
    - right; right; left. apply in_frames_In in K as (fr & Hf & R). exists (fkb_of fr). split; [apply INC; apply In_fkb; exact Hf| unfold fkb_of; cbn [ab_addr ab_size]; exact R].
    - right; right; right. apply in_frame_sh_In in K as (fr & Hf & R).
      destruct (geo_frame _ _ _ _ _ _ _ _ G (IFL _ Hf)) as (BAND & A64 & N64 & N0). pose proof (ablk_lin _ _ BAND) as (_ & F0 & _).
      exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; right. exists (ff_class (fb_fn fr)), (fb_addr fr), (fb_size fr). split; [apply INC; exact (In_fkb CL FB _ _ Hf)|].
      rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3), (Z.shiftr_div_pow2 (fb_size fr) 3) in R by lia. change (2^3) with 8 in R.
      assert (E1 : fb_addr fr = 8 * (fb_addr fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - A64; Z.div_mod_to_equations; lia]).
      assert (E2 : fb_size fr = 8 * (fb_size fr / 8)) by (apply Z_div_exact_full_2; [lia| clear - N64; Z.div_mod_to_equations; lia]).
      unfold ASHOFF. clear - R E1 E2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_rt : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m -> artcells m /\ rw_cells asegs m GOT_UAR [C8 (Z_to_bv 64 0xaea00)].
  Proof.
    intros L RNG s CL FB FL m (AH & _). split; [exact (AI_rtcells AI _ _ _ _ _ AH)|].
    apply (relro_word m GOT_UAR 0xaea00 (AI_relro AI _ _ _ _ _ AH)); [unfold GOT_UAR, ARELRO_LO; lia| unfold GOT_UAR, ARELRO_HI; lia| vm_compute; reflexivity].
  Qed.

  Hypothesis GS_globals : forall L RNG s FB m, GSTAT L RNG s FB m ->
      wr_at asegs m 0x7fffa000 780288 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
  Hypothesis GS_tls : forall L RNG s FB m, GSTAT L RNG s FB m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504.
  Hypothesis GS_stdin_unp : forall L RNG s FB m, GSTAT L RNG s FB m -> unpoisoned m STDIN_P (STDIN_P + 8).
  Hypothesis GS_stack : forall L RNG s FB m A n, GSTAT L RNG s FB m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
      unpoisoned m A (A + n) /\ arenaA RNG m A n.
  (* [comment removed for export] *)
  Hypothesis OBL_AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.

  #[using="OBL_AI_block_tls"] Lemma gr_tls_apart : forall L RNG s CL FB FL m a, GIOA_real L RNG s CL FB FL m -> in_block (CL ++ FB) a \/ in_frames FL a ->
    ~ (ATP + -200 <= a < ATP + -200 + 504).
  Proof.
    intros L RNG s CL FB FL m a (AH & _) [K|K] R.
    - apply in_block_In in K as (b & Hb & Rb). pose proof (OBL_AI_block_tls _ _ _ _ _ _ AH (In_hb _ _ FL _ Hb)) as D. unfold hb_of in D; cbn [ab_addr ab_size] in D. lia.
    - apply in_frames_In in K as (fr & Hf & Rf). pose proof (OBL_AI_block_tls _ _ _ _ _ _ AH (In_fkb CL FB _ _ Hf)) as D. unfold fkb_of in D; cbn [ab_addr ab_size] in D. lia.
  Qed.

  #[using="GS_stdin_unp"] Lemma gr_stdin : forall L RNG s CL FB FL m, GIOA_real L RNG s CL FB FL m ->
    rw_cells asegs m GOT_STDIN [C8 (Z_to_bv 64 STDIN_P)] /\ rw_cells asegs m STDIN_P [C8 (Z_to_bv 64 STDIN_FILE)] /\ unpoisoned m STDIN_P (STDIN_P + 8).
  Proof.
    intros L RNG s CL FB FL m (AH & _ & _ & _ & _ & _ & GS). pose proof (AI_relro AI _ _ _ _ _ AH) as RR.
    split; [apply (relro_word m GOT_STDIN STDIN_P RR); [unfold GOT_STDIN, ARELRO_LO; lia| unfold GOT_STDIN, ARELRO_HI; lia| vm_compute; reflexivity]|].
    split; [apply (relro_word m STDIN_P STDIN_FILE RR); [unfold STDIN_P, ARELRO_LO; lia| unfold STDIN_P, ARELRO_HI; lia| vm_compute; reflexivity]|].
    exact (GS_stdin_unp _ _ _ _ _ GS).
  Qed.

  (* [comment removed for export] *)
  #[using="AF GS_client_frame GS_globals GS_tls GS_stdin_unp GS_stack OBL_AI_block_tls"] Theorem gioa_real_laws : gia_laws (asan_fo site_frameA) GIOA_real fflagA_real.
  Proof.
    constructor.
    - exact gr_block.
    - exact gr_apart.
    - exact gr_frames.
    - exact gr_fr_apart.
    - exact gr_fr_disj.
    - exact gr_site.
    - exact gr_flag.
    - exact gr_client_frame.
    - exact gr_frame.
    - exact gr_keeps.
    - exact gr_keepsx.
    - exact gr_rt.
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & GS). exact (GS_globals _ _ _ _ _ GS).
    - intros L RNG s CL FB FL m (_ & _ & _ & _ & _ & _ & GS). exact (GS_tls _ _ _ _ _ GS).
    - exact gr_tls_apart.
    - exact gr_stdin.
    - intros L RNG s CL FB FL m A n (_ & _ & _ & _ & _ & _ & GS). exact (GS_stack _ _ _ _ _ A n GS).
    - intros L RNG s CL FB FL m (AH & _).
      apply (relro_word m GOT_MEMSET 0xa7740 (AI_relro AI _ _ _ _ _ AH)); [unfold GOT_MEMSET, ARELRO_LO; lia| unfold GOT_MEMSET, ARELRO_HI; lia| vm_compute; reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gr_got : @A3P.Pcap_iface_gotA.TwB.gia_got_law aheap aptr GIOA_real.
  Proof.
    intros L RNG s CL FB FL m (AH & _). pose proof (AI_relro AI _ _ _ _ _ AH) as RR.
    unfold A3P.Pcap_iface_gotA.TwB.GOT_PCAP_ADDR, A3P.Pcap_iface_gotA.TwB.GOT_INSTALL_BPF, A3P.Pcap_iface_gotA.TwB.GOT_BREAKLOOP, PK. cbn [pk_oneshot pk_cleanup_sf].
    assert (W : forall A v, ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true -> rw_cells asegs m A [C8 (Z_to_bv 64 v)])
      by (intros A v H1 H2 H3; exact (relro_word m A v RR H1 H2 H3)).
    pose proof (W 0xa6508 0x863b4 ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C1.
    pose proof (W 0xa6510 0x85a0c ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C2.
    pose proof (W 0xa6518 0x860a4 ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C3.
    pose proof (W 0xa6520 0x84ccc ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C4.
    pose proof (rw_cells_uncut _ _ _ _ _ C3 C4 ltac:(reflexivity)) as C34. pose proof (rw_cells_uncut _ _ _ _ _ C2 C34 ltac:(reflexivity)) as C234.
    exact (rw_cells_uncut _ _ _ _ _ C1 C234 ltac:(reflexivity)).
  Qed.
End GioaReal.
End CANSEC1.
End TwB.
