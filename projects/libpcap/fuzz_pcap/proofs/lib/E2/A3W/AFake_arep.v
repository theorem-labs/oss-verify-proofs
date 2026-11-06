(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFakeProbe. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.AFake_free7.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFAKE.
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

#[using="Type"] Lemma HB_FAKE : forall L RNG st LB m p A n,
  AHEAP_P AH L RNG st LB m -> In (HB p A n) LB ->
  ablock_range A n /\ (A + n <= al_fake L \/ al_fake L + 11571200 <= A).
Proof. intros. split; [eapply AHEAP_P_hb_range; eauto| eapply AHEAP_P_hb_fake; eauto]. Qed.

#[using="HL"] Lemma AREP_frame_ext' : forall L st X m m' W,
  alayout_ok L -> AREP AH L st X m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
            (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
         \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
         \/ ATOP <= fst iv) W ->
  AREP AH L st X m'.
Proof.
  (* [comment removed for export] *)
  intros L st X m m' W AL AR MU WM HW. eapply (AREP_frame_ext AH HL); [exact AL| exact AR| exact MU| exact WM|].
  eapply List.Forall_impl; [| exact HW]. cbv beta. intros iv H Hlt.
  destruct (H Hlt) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; left; exact A].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma AREP_cells : forall L st X m, AREP AH L st X m ->
  rt_got m /\ rt_shbase m
  /\ rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)]
  /\ rt_inited m /\ rt_layout m
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None).
Proof.
  intros L st X m H. pose proof (AREP_relro AH L st X m H) as RR. unfold AREP, arep_rt in H. decompose [and] H.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_OK"] Theorem fake_flag_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP          (* [comment removed for export] *)
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHP Hin. (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof (afake_lb L LB m cls F N HFK Hin) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR; nd_post).
  pose proof (afake_flag L LB m cls F N HFK Hin) as FL.
  destruct HFK as (G & _). (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold FAKESZ, KHIGH, AIMG_HI in *.   (* [comment removed for export] *)
  (nd_pre ARNG 8%nat; intros _ _ _ _ _ _ RF _; nd_post).
  split; [exact FL|]. split; [eapply rng_sub'; [exact RF| lia]|]. split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split.
  - intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    + pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [_ D]. lia.
    + (pose proof (afake_lb L LB m c' A' n' (proj2 (proj2 (proj2 AHP))) Hb) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ X1 X2 _; nd_post). lia.
  - intros (iv & Hiv & R). pose proof (CI_OK iv Hiv). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_tail : forall L st X b LB, ablocks L st X (b :: LB) -> ablocks L st X LB.
Proof.
  intros L st X b LB (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). right; exact Hin.
  - intros c A n Hin. apply (H2 c A n). right; exact Hin.
  - destruct b as [[p|c] A n]; cbn in H3; [inversion H3; assumption| exact H3].
  - inversion H4; assumption.
Qed.

#[using="HL"] Theorem fake_release_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_P AH L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP. (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof (afake_lb L _ m cls F N HFK ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR; nd_post).
  assert (NI : ~ In (mkABlock (ABFake cls) F N) LB) by ((nd_pre BL 4%nat; intros _ _ _ ND; nd_post); inversion ND; assumption).
  destruct HFK as (G & HFK'). (pose proof G as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold FAKESZ, AIMG_HI in *.   (* [comment removed for export] *)
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| eapply ablocks_tail; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AH ah_fake]. apply (afake_release L LB m cls F N); [exact (conj G HFK')| exact NI].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.


#[using="Type"] Lemma AREP_poison_cells : forall L st X m, AREP AH L st X m -> poison_cells m.
Proof.
  intros L st X m H. unfold AREP, arep_rt in H. decompose [and] H. unfold poison_cells.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_fake_cls (c : Z) (b : ablock) : bool := match ab_kind b with ABFake c' => Z.eqb c' c | ABHeap _ => false end.
Definition fk_count (c : Z) (LB : list ablock) : Z := Z.of_nat (length (List.filter (is_fake_cls c) LB)).

#[using="Type"] Lemma fk_count_le_length : forall c LB, fk_count c LB <= Z.of_nat (length LB).
Proof. intros c LB. unfold fk_count. pose proof (filter_length_le (is_fake_cls c) LB). lia. Qed.

#[using="Type"] Lemma fk_frame_inj : forall L c p1 p2, 0 <= c -> fk_frame L c p1 = fk_frame L c p2 -> p1 = p2.
Proof. intros L c p1 p2 Hc E. unfold fk_frame in E. pose proof (fk_fsize_pos c Hc). nia. Qed.

#[using="Type"] Lemma probe_find : forall L LB m c h,
  AFAKE L LB m -> 0 <= c < FK_NCLS -> fk_count c LB < fk_nframes c ->
  exists j, 0 <= j < fk_nframes c
    /\ (forall k, 0 <= k < j -> rw_cells asegs m (fk_flag L c ((h + k) mod fk_nframes c)) [C1 (Z_to_bv 8 1)])
    /\ rw_cells asegs m (fk_flag L c ((h + j) mod fk_nframes c)) [C1 (Z_to_bv 8 0)].
Proof.
  intros L LB m c h AF Hc CNT.
  (pose proof AF as ndP__; nd_pre ndP__ 9%nat; intros G _ _ _ _ DC1 _ FL LV; nd_post).
  (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). pose proof (ablk_lin _ _ G2) as (GL1 & _). unfold AIMG_HI, FAKESZ in *.
  assert (NP : 0 < fk_nframes c) by (apply fk_nframes_pos; unfold FK_NCLS in Hc; lia).
  set (N := fk_nframes c) in *.
  assert (POS : forall k, 0 <= (h + k) mod N < N) by (intros k; apply Z.mod_pos_bound; exact NP).
  (* [comment removed for export] *)
  assert (CELL : forall pos, 0 <= pos < N -> exists b : byte, rw_cells asegs m (fk_flag L c pos) [C1 b] /\ m (wa (fk_flag L c pos)) = Some b).
  { intros pos Hp. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    pose proof (dc_sub m (al_fake L + 4096) (11571200 - 4096) (fk_flag L c pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D.
    destruct (c1_of_dc m _ D) as [b Hb]. exists b. split; [exact Hb|]. apply (rw_C1_high m _ b Hb). lia. }
  (* [comment removed for export] *)
  assert (ONE : forall pos b, 0 <= pos < N -> m (wa (fk_flag L c pos)) = Some b -> b <> Z_to_bv 8 0 ->
                 b = Z_to_bv 8 1 /\ In (FKB c (fk_frame L c pos) (fk_fsize c)) LB).
  { intros pos b Hp Hb NZ. pose proof (FL c pos b Hc Hp Hb NZ) as IN. split; [|exact IN].
    (nd_pre (LV _ _ _ IN) 6%nat; intros _ _ pos' Hp' HF' B1; nd_post).
    apply fk_frame_inj in HF'; [|lia]. subst pos'. congruence. }
  destruct (first_free (fun i => m (wa (fk_flag L c ((h + i) mod N))) = Some (Z_to_bv 8 0))
              ltac:(intros i; apply (decide _)) (fk_count c LB + 1) ltac:(unfold fk_count; lia)) as [(j & Hj & Pj & Lj)|NONE].
  - exists j. split; [lia|]. split.
    + intros k Hk. (nd_pre (CELL _ (POS k)) 3%nat; intros b Cb Mb; nd_post).
      destruct (ONE _ b (POS k) Mb) as [-> _]; [| exact Cb]. intros ->. exact (Lj k Hk Mb).
    + (nd_pre (CELL _ (POS j)) 3%nat; intros b Cb Mb; nd_post). rewrite Mb in Pj. injection Pj as ->. exact Cb.
  - exfalso.
    pose proof (pigeon_Z ablock (fun k => FKB c (fk_frame L c ((h + k) mod N)) (fk_fsize c)) (fk_count c LB + 1)
                  (List.filter (is_fake_cls c) LB) ltac:(unfold fk_count; lia)) as PG.
    cbv beta in PG. unfold fk_count in *. 
    assert (LE : Z.of_nat (length (List.filter (is_fake_cls c) LB)) + 1 <= Z.of_nat (length (List.filter (is_fake_cls c) LB))); [|lia].
    apply PG.
    + intros k Hk. apply filter_In. split; [| cbn; apply Z.eqb_refl].
      (nd_pre (CELL _ (POS k)) 3%nat; intros b Cb Mb; nd_post).
      destruct (ONE _ b (POS k) Mb) as [_ IN]; [| exact IN]. intros ->. exact (NONE k Hk Mb).
    + intros k1 k2 H1 H2 E. injection E as E. apply fk_frame_inj in E; [|lia].
      eapply (probe_pos_inj N h); [exact NP | lia | lia | exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma byte01_ne : Z_to_bv 8 0 <> Z_to_bv 8 1 :> byte.
Proof. intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate. Qed.

#[using="Type"] Lemma fk_fsize_cases : forall c, 0 <= c <= 7 -> 64 <= fk_fsize c <= 8192 /\ fk_fsize c mod 64 = 0.
Proof.
  intros c Hc. assert (E : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; repeat split; congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_of_dc : forall m A, dc_at m A 88 -> exists (h0 h1 h2 : word) (hs : list byte), rw_cells asegs m A [C8 h0; C8 h1; C8 h2; CB 64 hs].
Proof.
  intros m A D. destruct (dc_take m A 88 8 D ltac:(lia)) as [D0 D1]. replace (88 - 8) with 80 in D1 by reflexivity.
  destruct (dc_take m (A + 8) 80 16 D1 ltac:(lia)) as [D12 D3]. replace (80 - 16) with 64 in D3 by reflexivity.
  destruct (c8_of_dc m A D0) as [h0 H0]. (nd_pre (c8c8_of_dc m (A + 8) D12) 3%nat; intros h1 h2 H12; nd_post). destruct D3 as [hs H3].
  change (Z.to_nat 64) with 64%nat in H3. exists h0, h1, h2, hs.
  apply (proj2 (rw_cells_app asegs m A [C8 h0] _)). split; [exact H0|]. cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs m (A + Z.of_nat 8) [C8 h1; C8 h2] _)). split; [replace (A + Z.of_nat 8) with (A + 8) by lia; exact H12|].
  cbn [cells_size csize Nat.add]. replace (A + Z.of_nat 8 + Z.of_nat 16) with (A + 8 + 16) by lia. exact H3.
Qed.

Definition sm_core__stmt : Prop := forall L RNG st LB m m' lo spz c pos size K shn flag F,
  AHEAP_P AH L RNG st LB m ->
  0 <= c <= 7 -> 0 <= pos < fk_nframes c -> size = fk_fsize c ->
  flag = fk_flag L c pos -> F = fk_frame L c pos ->
  m (wa flag) = Some (Z_to_bv 8 0) ->
  ATOP + 4096 <= lo -> 0 <= K -> lo <= spz - K -> spz <= al_top L ->
  0 <= shn <= size / 8 ->
  munch [(spz - K, spz); (al_fake L + 8 * c, al_fake L + 8 * c + 8); (flag, flag + 1); (F + 24, F + 32); (F + size - 8, F + size);
         (shad F, shad F + shn)] m m' ->
  wmono asegs m m' ->
  rw_cells asegs m' flag [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m' (F + size - 8) [C8 (Z_to_bv 64 flag)] ->
  aheap_pres CI LB spz m m'
  /\ AHEAP_P AH L RNG st (FKB c F size :: LB) m'
  /\ F mod 64 = 0 /\ ablk F (F + size) /\ F + size <= ATOP /\ 0 < F
  /\ (exists (j0 j1 j2 : word) (junk : list byte), length junk = Z.to_nat (size - 32)
        /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (size - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))])
  /\ rng RNG F size /\ rng RNG (shad F) (size / 8).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 5).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 6).
Variable spz : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 7).
Variable c : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 8).
Variable pos : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 9).
Variable size : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 10).
Variable K : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 11).
Variable shn : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 12).
Variable flag : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 13).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 14).
#[using="HL CI_OK"] Lemma sm_core__body : ltac:(let T := type of (fun (h : sm_core__stmt) => h L RNG st LB m m' lo spz c pos size K shn flag F) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (st, (LB, (m, (m', (lo, (spz, (c, (pos, (size, (K, (shn, (flag, F))))))))))))))) as _.
  intros AHP Hc Hp Hsz EFL EFR FL0 BOT K0 LO SPT SHN MU WM FL1 FPTR.
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE HDR LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  (nd_pre CE 8%nat; intros REAL DTVP DV DTV1 BD CF VERB T48; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros SK1 SK2 SK3; nd_post).
  assert (Hc' : 0 <= c < FK_NCLS) by (unfold FK_NCLS; lia).
  pose proof (fk_flag_range L c pos Hc' Hp) as FRG. rewrite <- EFL in FRG.
  (pose proof (fk_frame_range L c pos Hc' Hp) as ndP__; nd_pre ndP__ 4%nat; intros _ _ FR3 FR4; nd_post). rewrite <- EFR in FR3. rewrite <- EFR, <- Hsz in FR4.
  pose proof (fk_frame_al64 L c pos G1 ltac:(lia)) as F64. rewrite <- EFR in F64.
  pose proof (fk_fsize_cases c Hc) as (SZ1 & SZ2). rewrite <- Hsz in SZ1, SZ2.
  assert (EFF : fflag L c F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  unfold FAKESZ, KHIGH, AIMG_HI in *.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + size / 8 <= shad (al_fake L) + 1446400 /\ shad F + size / 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. clear - G1 GL1 G3 FR3 FR4 F64 SZ1 SZ2 ATR. Z.div_mod_to_equations. lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (SHD : shad F + size / 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. clear - G2c G3 FR3 FR4 SZ1 ATR. Z.div_mod_to_equations. lia. }
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (spz - K <= a < spz) -> ~ (al_fake L + 8 * c <= a < al_fake L + 8 * c + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + size - 8 <= a < F + size) -> ~ (shad F <= a < shad F + shn) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside fst snd]. repeat split; lia. }
  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length fst snd]; K; lia].
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite SHL.
    repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor]. }
  assert (NOTIN : ~ In (FKB c F size) LB).
  { intros IN. (nd_pre (LV _ _ _ IN) 6%nat; intros _ _ pos' Hp' HF' B1; nd_post). rewrite EFR in HF'. apply fk_frame_inj in HF'; [|lia]. subst pos'.
    rewrite <- EFL, FL0 in B1. apply byte01_ne. congruence. }
  (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF TCD TCT; nd_post).
  assert (HFK' : AFAKE L (FKB c F size :: LB) m').
  { split; [exact G|]. split.
    { tclr_int TCF. unfold afake_cells.
      split; [xportk REAL MU WM ltac:(clear -GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR)|].
      split; [xportk DTVP MU WM ltac:(clear -KT GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk DV MU WM ltac:(clear -KT GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk DTV1 MU WM ltac:(clear -KT GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk CF MU WM ltac:(clear -GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR)|].
      split; [xportk VERB MU WM ltac:(clear -GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR)|].
      eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split.
    { (nd_pre HDR 5%nat; intros h0 h1 h2 hs HS; nd_post). apply hdr_of_dc.
      eapply dc_at_any; [exact (dc_of_cells m _ _ HS)| exact WM| lia]. }
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO K0 FRG FR3 FR4 SHD SZ1 SHN Hc ATR)|].
    split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO K0 FRG FR3 FR4 SHD SZ1 SHN Hc ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c2 pos' b Hc2 Hp2 Hb NZ.
      destruct (Z.eq_dec (fk_flag L c2 pos') flag) as [EQ|NE].
      + left. assert (E2 : (c2, pos') = (c, pos)).
        { destruct (decide ((c2, pos') = (c, pos))) as [E|NE2]; [exact E| exfalso].
          apply (fk_flags_disjoint L c2 pos' c pos Hc2 Hp2 Hc' Hp NE2). rewrite EQ, EFL. reflexivity. }
        injection E2 as -> ->. rewrite <- EFR, <- Hsz. reflexivity.
      + right. pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2.
        rewrite OUT in Hb by (clear -FRG2 NE G3 GL1 BOT LO K0 FR3 FR4 SHD SZ1 SHN Hc ATR; lia). eapply FL; eauto.
    - intros c2 F' n' [E|Hin].
      + injection E as <- <- <-. split; [exact Hc'|]. split; [exact Hsz|].
        exists pos. split; [exact Hp|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + (nd_pre (LV c2 F' n' Hin) 6%nat; intros Hc2 Hn pos' Hp2 HF' B1; nd_post).
        split; [exact Hc2|]. split; [exact Hn|]. exists pos'. split; [exact Hp2|]. split; [exact HF'|].
        assert (NE : fk_flag L c2 pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c2 pos' c pos Hc2 Hp2 Hc' Hp).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, Hsz, <- HF', <- Hn. exact Hin. }
        pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2.
        rewrite OUT by (clear -FRG2 NE G3 GL1 BOT LO K0 FR3 FR4 SHD SZ1 SHN Hc ATR; lia). exact B1. }
  assert (BL' : ablocks L st X (FKB c F size :: LB)).
  { (nd_pre BL 4%nat; intros B1 B2 B3 B4; nd_post). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c2 A n [E|Hin]; [| exact (B2 c2 A n Hin)]. injection E as <- <- <-. clear -FR3 FR4 SZ1. lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FKB c F size :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + size <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c2] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. clear -Q2 Q3 Q4 D FR3 FR4 SZ1 G3 GL1 ATR. lia.
    - (pose proof (afake_lb L LB m c2 A' n' HFK Hb) as ndP__; nd_pre ndP__ 12%nat; intros Hc2 Hn' Np' _ X1 X2 X3 X4 pos' Hp2 HF' _; nd_post).
      assert (NEQ : (c2, pos') <> (c, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, Hsz, <- HF', <- Hn'. exact Hb. }
      pose proof (fk_frames_disjoint L c2 pos' c pos Hc2 Hp2 Hc' Hp NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn', <- Hsz in DJ.
      split; [exact X3|]. unfold FAKESZ in *. clear -X1 X2 X4 DJ. lia. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + size)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c2 & FA & fn & Hb & Hr)]];
      [ clear - X1 G3 FR4 SZ1 ATR; lia | pose proof (CI_OK iv Hiv) as CK; clear - Hr CK GL1 FR3; lia |].
    (nd_pre (BLK _ Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. unfold AIMG_HI in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  assert (HPR : aheap_pres CI LB spz m m').
  { intros a Ha Hcl. split; [| intros W0; apply WM; exact W0].
    destruct Hcl as [Hcl|TL].
    2:{ (* [comment removed for export] *)
        (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF0 _ _; nd_post). unfold tclr in TCF0. pose proof atp_lin as TLN. pose proof atp_below_atop as TBA.
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
            rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_fake L ALO) as DAF. unfold adisj in DAF.
            apply OUT; clear - Ha IM OAH OAHI DAF BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
            apply OUT; clear - Ha IM G2t BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR; Z.div_mod_to_equations; lia. }
        - apply OUT; clear - Ha T TCF0 TLN TBA BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR; lia.
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SATOP : shad ATOP <= 17594332446720) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -ATR; Z.div_mod_to_equations; lia).
          assert (TSA : shad ta + 1 <= shad F \/ shad F + size / 8 <= shad ta).
          { destruct (tls_shadow_apart ta F size Hta ltac:(clear -SZ1; lia)) as [D|D].
            - destruct TCF0 as [D|D]; [right; split; [clear -D FR4; lia| clear -F64; Z.div_mod_to_equations; lia] | left; clear -D FR3; lia].
            - left; exact D.
            - right. unfold shlen in D. rewrite Z.shiftr_div_pow2 in D by lia. exact D. }
          pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
          apply OUT; clear - Ha TS1 TS2 SATOP TSA G2t BOT LO K0 GL1 G3 FRG FR3 FR4 SZ1 SHN Hc ATR; lia. }
    destruct Hcl as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO K0 SPT GL1 G3 FRG FR3 FR4 SB2 SB3 SHS SHN SZ1 Hc ATR; lia.
    - pose proof (CI_OK iv Hiv) as CK. apply OUT; clear - Ha CK Hr BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SHS SHN SZ1 Hc ATR; lia.
    - (nd_pre (BLK b Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SB2 SB3 SHS SHN SZ1 Hc ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *. rewrite SHF in OUT.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 FRG FR3 FR4 SZ1 SZ2 SHN LO BOT K0 Hc ATR; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F (size - 8) DC1 ltac:(clear -FR3; lia) ltac:(clear -SZ1; lia) ltac:(clear -FR4; lia)) as DF0.
  pose proof (dc_at_any m m' F (size - 8) DF0 WM ltac:(clear -GL1 FR3; lia)) as DF1.
  destruct (dc_take m' F (size - 8) 24 DF1 ltac:(clear -SZ1; lia)) as [DW DJ]. replace (size - 8 - 24) with (size - 32) in DJ by (clear; lia).
  destruct (dc_take m' F 24 8 DW ltac:(clear; lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. (nd_pre (c8c8_of_dc m' (F + 8) DW12) 3%nat; intros j1 j2 J12; nd_post).
  destruct DJ as [junk J1].
  assert (LJ : length junk = Z.to_nat (size - 32)) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (size - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB (Z.to_nat (size - 32)) junk] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia. exact J1.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SZ1; lia).
      replace (F + Z.of_nat 8 + Z.of_nat 16 + (size - 32)) with (F + size - 8) by lia. exact FPTR. }
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  split; [exact HPR|]. split; [exact AHP'|]. split; [exact F64|].
  split; [eapply ablk_sub; [exact G2| clear - FR3; lia| clear - FR4; lia]|]. split; [clear - G3 FR4; lia|]. split; [clear -GL1 FR3; lia|].
  split; [exists j0, j1, j2, junk; split; [exact LJ| exact FRM]|].
  split; [eapply rng_sub'; [exact A7| clear - FR3 FR4 SZ1; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 SZ1; Z.div_mod_to_equations; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Lemma sm_core : ltac:(let t := eval cbv delta [sm_core__stmt] in sm_core__stmt in exact t).
Proof. exact sm_core__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SM_STACK : Z := 4096.

(* [comment removed for export] *)
Definition sm_postP (c size : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FKB c F size :: LB) m'
    /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + size) /\ F + size <= ATOP
    /\ length junk = Z.to_nat (size - 32)
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (size - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
    /\ rng RNG F size /\ rng RNG (shad F) (size / 8).

(* [comment removed for export] *)
#[using="Type"] Lemma tlsga_of_inv : forall L st X LB m, AREP AH L st X m -> AFAKE L LB m ->
  tlsga_cells m (al_t L) (al_dtls L) ATPv (Z_to_bv 64 (al_fake L)).
Proof.
  intros L st X LB m AR HFK. (nd_pre HFK 3%nat; intros G CE _; nd_post). (nd_pre CE 8%nat; intros REAL DTVP DV DTV1 BD CF VERB T48; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  pose proof (relro_word m 0xa5500 0x13e098 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xa61c8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xa61b8 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  (nd_pre (c8c8_of_dc m _ T48) 3%nat; intros tb te T48'; nd_post).
  unfold tlsga_cells. split; [exact REAL|]. split; [exact DESC|]. split; [exact DTVP|].
  split; [unfold ADTV, ATP; replace (ATPv + 288 + 8) with (ATPv + 296) by (clear; lia); exact DTV1|].
  split; [exact R2|]. split; [exact CF|]. split; [exact GB0|]. split; [exact VERB|]. split; [exact G08|].
  split; [exact DV|]. split; [exact BD|]. exists tb, te; exact T48'.
Qed.

Definition stack_malloc_0_P__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fk_count 0 LB < fk_nframes 0 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm_postP 0 64 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 32).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 38).
#[using="HL CI_OK"] Lemma stack_malloc_0_P__body : ltac:(let T := type of (fun (h : stack_malloc_0_P__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP CNT MI ST BOT LO SPT TP RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (tlsga_of_inv L st X LB m AR HFK) as TC.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HNT) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  pose proof atop_range as ATR.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  (* [comment removed for export] *)
  pose proof (dc_sub m (al_fake L) 88 (al_fake L) 8 (dc_of_cells m _ _ HNT) ltac:(lia) ltac:(lia) ltac:(lia)) as DH.
  destruct (c8_of_dc m _ DH) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  (nd_pre (probe_find L LB m 0 h HFK ltac:(unfold FK_NCLS; lia) CNT) 4%nat; intros j Hj LIVE FREE; nd_post).
  replace (fk_nframes 0) with 16384 in * by reflexivity.
  set (pos := Z.land (h + j) 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (LM : forall x, Z.land x 16383 = x mod 16384) by (intros x; change 16383 with (2^14 - 1); rewrite land_ones_mod by lia; reflexivity).
  assert (PB : 0 <= pos < 16384) by (subst pos; rewrite LM; apply Z.mod_pos_bound; lia).
  assert (FKF : forall p, fk_flag L 0 p = al_fake L + 4096 + p) by (intros p; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFL : flag = fk_flag L 0 pos) by (rewrite FKF; reflexivity).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (LIVE' : forall k, 0 <= k < j -> rw_cells asegs m (al_fake L + 4096 + Z.land (h + k) 16383) [C1 (Z_to_bv 8 1)]).
  { intros k Hk. rewrite LM, <- FKF. exact (LIVE k Hk). }
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]) by (subst flag pos; rewrite LM, <- FKF; exact FREE).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 8 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].
  assert (HW' : rw_cells asegs m (al_fake L) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
  (* [comment removed for export] *)
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  assert (HPOS : pos = Z.land (h + j) 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc0_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) ATPv (al_fake L) h j pos flag F j24 j56 sh0);
      try exact MI; try exact ST; try exact TP; try exact TC; try exact LIVE'; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 14%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MU WM MI' ST' HNT2 FL1 F24' F56' SH'; nd_post).
  unfold sm0_W in MU.
  (nd_pre (sm_core L RNG st LB m m' lo (bv_unsigned sp) 0 pos 64 208 8 flag F AHP ltac:(lia) ltac:(replace (fk_nframes 0) with 16384 by reflexivity; exact PB)
              eq_refl EFL EFR FLM BOT ltac:(lia) ltac:(lia) SPT ltac:(cbn; lia)
              ltac:(eapply munch_weaken; [| exact MU]; intros xq Hq; cbn [outside fst snd] in Hq |- *; clear -Hq; lia) WM FL1
              ltac:(replace (F + 64 - 8) with (F + 56) by lia; exact F56')) 9%nat; intros HPR AHP' F64 FBLK FTOP F0 (j0 & j1 & j2 & junk & LJ & FRM) RF1 RF2; nd_post).
  unfold sm_postP. exists F. do 14 eexists. exists m', j0, j1, j2, junk.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [exact F0|]. split; [exact FBLK|]. split; [exact FTOP|]. split; [exact LJ|]. split; [exact FRM|].
  split; [| split; [exact RF1| exact RF2]].
  eapply rw_cells_recast; [exact SH' | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity].
Qed.
End Zd2.
#[using="HL CI_OK"] Theorem stack_malloc_0_P : ltac:(let t := eval cbv delta [stack_malloc_0_P__stmt] in stack_malloc_0_P__stmt in exact t).
Proof. exact stack_malloc_0_P__body. Qed.

Definition stack_malloc_1_P__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fk_count 1 LB < fk_nframes 1 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm_postP 1 128 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 32).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 38).
#[using="HL CI_OK"] Lemma stack_malloc_1_P__body : ltac:(let T := type of (fun (h : stack_malloc_1_P__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP CNT MI ST BOT LO SPT TP RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (tlsga_of_inv L st X LB m AR HFK) as TC.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HNT) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  pose proof atop_range as ATR.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  (* [comment removed for export] *)
  pose proof (dc_sub m (al_fake L) 88 (al_fake L + 8) 8 (dc_of_cells m _ _ HNT) ltac:(lia) ltac:(lia) ltac:(lia)) as DH.
  destruct (c8_of_dc m _ DH) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  (nd_pre (probe_find L LB m 1 h HFK ltac:(unfold FK_NCLS; lia) CNT) 4%nat; intros j Hj LIVE FREE; nd_post).
  replace (fk_nframes 1) with 8192 in * by reflexivity.
  set (pos := Z.land (h + j) 8191). set (flag := (al_fake L) + 20480 + pos). set (F := (al_fake L) + 1085440 + pos * 128).
  assert (LM : forall x, Z.land x 8191 = x mod 8192) by (intros x; change 8191 with (2^13 - 1); rewrite land_ones_mod by lia; reflexivity).
  assert (PB : 0 <= pos < 8192) by (subst pos; rewrite LM; apply Z.mod_pos_bound; lia).
  assert (FKF : forall p, fk_flag L 1 p = al_fake L + 20480 + p) by (intros p; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFL : flag = fk_flag L 1 pos) by (rewrite FKF; reflexivity).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (LIVE' : forall k, 0 <= k < j -> rw_cells asegs m (al_fake L + 20480 + Z.land (h + k) 8191) [C1 (Z_to_bv 8 1)]).
  { intros k Hk. rewrite LM, <- FKF. exact (LIVE k Hk). }
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]) by (subst flag pos; rewrite LM, <- FKF; exact FREE).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 16 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D120.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D120) as [j120 F120].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  (nd_pre (c8c8_of_dc m _ DS2) 3%nat; intros sh0 sh1 SH0; nd_post).
  assert (HW' : rw_cells asegs m (al_fake L + 8) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
  (* [comment removed for export] *)
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  assert (HPOS : pos = Z.land (h + j) 8191) by reflexivity. assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc1_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) ATPv (al_fake L) h j pos flag F j24 j120 sh0 sh1);
      try exact MI; try exact ST; try exact TP; try exact TC; try exact LIVE'; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 14%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MU WM MI' ST' HNT2 FL1 F24' F120' SH'; nd_post).
  unfold sm1_W in MU.
  (nd_pre (sm_core L RNG st LB m m' lo (bv_unsigned sp) 1 pos 128 208 16 flag F AHP ltac:(lia) ltac:(replace (fk_nframes 1) with 8192 by reflexivity; exact PB)
              eq_refl EFL EFR FLM BOT ltac:(lia) ltac:(lia) SPT ltac:(cbn; lia)
              ltac:(eapply munch_weaken; [| exact MU]; intros xq Hq; cbn [outside fst snd] in Hq |- *; clear -Hq; lia) WM FL1
              ltac:(replace (F + 128 - 8) with (F + 120) by lia; exact F120')) 9%nat; intros HPR AHP' F64 FBLK FTOP F0 (j0 & j1 & j2 & junk & LJ & FRM) RF1 RF2; nd_post).
  unfold sm_postP. exists F. do 14 eexists. exists m', j0, j1, j2, junk.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [exact F0|]. split; [exact FBLK|]. split; [exact FTOP|]. split; [exact LJ|]. split; [exact FRM|].
  split; [| split; [exact RF1| exact RF2]].
  eapply rw_cells_recast; [exact SH' | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity].
Qed.
End Zd3.
#[using="HL CI_OK"] Theorem stack_malloc_1_P : ltac:(let t := eval cbv delta [stack_malloc_1_P__stmt] in stack_malloc_1_P__stmt in exact t).
Proof. exact stack_malloc_1_P__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sm7_postP (req : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk sjunk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FKB 7 F 8192 :: LB) m'
    /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + 8192) /\ F + 8192 <= ATOP
    /\ length junk = Z.to_nat (8192 - 32)
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (8192 - 32)) junk; C8 (Z_to_bv 64 (fflag L 7 F))]
    /\ length sjunk = Z.to_nat ((8192 - req) / 8)
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8))); CB (Z.to_nat ((8192 - req) / 8)) sjunk]
    /\ rng RNG F 8192 /\ rng RNG (shad F) (8192 / 8).

Definition stack_malloc_7_P__stmt : Prop := forall (L : alayout) (RNG : footprint) (req : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fk_count 7 LB < fk_nframes 7 ->
  a0 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm7_postP req L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC7) fc None m (seg_rom asegs)).
Section Zd4.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 1).
Variable req : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 33).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 36).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 37).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 39).
#[using="HL CI_OK"] Lemma stack_malloc_7_P__body : ltac:(let T := type of (fun (h : stack_malloc_7_P__stmt) => h L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (req, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP CNT A0 REQ REQ8 MI ST BOT LO SPT TP RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (tlsga_of_inv L st X LB m AR HFK) as TC. pose proof (AREP_poison_cells L st X m AR) as PC.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HNT) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  pose proof atop_range as ATR.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  (* [comment removed for export] *)
  pose proof (dc_sub m (al_fake L) 88 (al_fake L + 56) 8 (dc_of_cells m _ _ HNT) ltac:(lia) ltac:(lia) ltac:(lia)) as DH.
  destruct (c8_of_dc m _ DH) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  (nd_pre (probe_find L LB m 7 h HFK ltac:(unfold FK_NCLS; lia) CNT) 4%nat; intros j Hj LIVE FREE; nd_post).
  replace (fk_nframes 7) with 128 in * by reflexivity.
  set (pos := Z.land (h + j) 127). set (flag := (al_fake L) + 36608 + pos). set (F := (al_fake L) + 7376896 + pos * 8192).
  assert (LM : forall x, Z.land x 127 = x mod 128) by (intros x; change 127 with (2^7 - 1); rewrite land_ones_mod by lia; reflexivity).
  assert (PB : 0 <= pos < 128) by (subst pos; rewrite LM; apply Z.mod_pos_bound; lia).
  assert (FKF : forall p, fk_flag L 7 p = al_fake L + 36608 + p) by (intros p; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFL : flag = fk_flag L 7 pos) by (rewrite FKF; reflexivity).
  assert (EFR : F = fk_frame L 7 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (LIVE' : forall k, 0 <= k < j -> rw_cells asegs m (al_fake L + 36608 + Z.land (h + k) 127) [C1 (Z_to_bv 8 1)]).
  { intros k Hk. rewrite LM, <- FKF. exact (LIVE k Hk). }
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]) by (subst flag pos; rewrite LM, <- FKF; exact FREE).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHQ : shlen req = req / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 1024 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 8184) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D8184.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D8184) as [j8184 F8184].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) (shlen req) DC2 ltac:(lia) ltac:(rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia) ltac:(rewrite SHQ; clear -REQ SB2; Z.div_mod_to_equations; lia)) as DS2.
  destruct DS2 as [shj SHJ].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + req / 8) ((8192 - req) / 8) DC2 ltac:(clear -REQ SB1; Z.div_mod_to_equations; lia) ltac:(clear -REQ; Z.div_mod_to_equations; lia) ltac:(clear -REQ REQ8 SB2; Z.div_mod_to_equations; lia)) as DS3.
  assert (HW' : rw_cells asegs m (al_fake L + 56) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
  (* [comment removed for export] *)
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  assert (HPOS : pos = Z.land (h + j) 127) by reflexivity. assert (HFLAG : flag = (al_fake L) + 36608 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 7376896 + pos * 8192) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc7_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) ATPv (al_fake L) h j pos flag F req j24 j8184 shj);
      try exact MI; try exact ST; try exact TP; try exact TC; try exact PC; try exact LIVE'; try exact A0; try exact SHJ; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 16%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MU WM MI' ST' HNT2 FL1 F24' F8184' SH'; nd_post).
  unfold sm7_W in MU.
  (nd_pre (sm_core L RNG st LB m m' lo (bv_unsigned sp) 7 pos 8192 224 (shlen req) flag F AHP ltac:(lia) ltac:(replace (fk_nframes 7) with 128 by reflexivity; exact PB)
              eq_refl EFL EFR FLM BOT ltac:(lia) ltac:(lia) SPT ltac:(rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia)
              ltac:(eapply munch_weaken; [| exact MU]; intros xq Hq; cbn [outside fst snd] in Hq |- *; clear -Hq; lia) WM FL1
              ltac:(replace (F + 8192 - 8) with (F + 8184) by lia; exact F8184')) 9%nat; intros HPR AHP' F64 FBLK FTOP F0 (j0 & j1 & j2 & junk & LJ & FRM) RF1 RF2; nd_post).
  pose proof (dc_at_any m m' _ _ DS3 WM ltac:(clear -SB1 SHS GL1 REQ; Z.div_mod_to_equations; lia)) as DS3'. destruct DS3' as [sjunk SJ].
  assert (LSJ : length sjunk = Z.to_nat ((8192 - req) / 8)) by (destruct SJ as [[[WF _] _] _]; cbn in WF; lia).
  unfold sm7_postP. exists F. do 14 eexists. exists m', j0, j1, j2, junk, sjunk.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [exact F0|]. split; [exact FBLK|]. split; [exact FTOP|]. split; [exact LJ|]. split; [exact FRM|].
  split; [exact LSJ|]. split; [| split; [exact RF1| exact RF2]].
  rewrite SHQ in SH'.
  apply (proj2 (rw_cells_app asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8)))] _)). split; [exact SH'|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -REQ; Z.div_mod_to_equations; lia). exact SJ.
Qed.
End Zd4.
#[using="HL CI_OK"] Theorem stack_malloc_7_P : ltac:(let t := eval cbv delta [stack_malloc_7_P__stmt] in stack_malloc_7_P__stmt in exact t).
Proof. exact stack_malloc_7_P__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma outside_of_Forall : forall (W : list (Z * Z)) (Q : Z * Z -> Prop) a,
  Forall Q W -> (forall iv, Q iv -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof. induction W as [|[lo hi] W IH]; intros Q a HF HQ; cbn; [exact I|]. inversion HF; subst. split; [exact (HQ (lo, hi) H1)| eapply IH; eauto]. Qed.

#[using="Type"] Lemma fk_fsize_mod64 : forall c, 0 <= c -> fk_fsize c mod 64 = 0.
Proof. intros c Hc. unfold fk_fsize. rewrite Z.pow_add_r by lia. change (2^6) with 64. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

Definition sf_core__stmt : Prop := forall L RNG st LB m m' c F size flag W spz,
  AHEAP_P AH L RNG st (FKB c F size :: LB) m ->
  flag = fflag L c F -> ATOP <= spz ->
  munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (ATOP <= fst iv /\ snd iv <= spz) \/ (fst iv = flag /\ snd iv = flag + 1)
                    \/ (shad F <= fst iv /\ snd iv <= shad F + size / 8)) W ->
  rw_cells asegs m' flag [C1 (Z_to_bv 8 0)] ->
  AHEAP_P AH L RNG st LB m' /\ aheap_pres CI LB spz m m'.
Section Zd5.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 5).
Variable c : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 6).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 7).
Variable size : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 8).
Variable flag : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 9).
Variable W : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 10).
Variable spz : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 11).
#[using="HL CI_OK"] Lemma sf_core__body : ltac:(let T := type of (fun (h : sf_core__stmt) => h L RNG st LB m m' c F size flag W spz) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (st, (LB, (m, (m', (c, (F, (size, (flag, (W, spz)))))))))))) as _.
  intros AHP EFLG SPZ MU WM HW FL1.
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof (afake_lb L _ m c F size HFK ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR; nd_post).
  assert (NI : ~ In (FKB c F size) LB) by ((nd_pre BL 4%nat; intros _ _ _ ND; nd_post); inversion ND; assumption).
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE HDR LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  (nd_pre CE 8%nat; intros REAL DTVP DV DTV1 BD CF VERB T48; nd_post).
  rewrite <- EFLG in EF, FR. pose proof (fk_fsize_mod64 c ltac:(lia)) as SZ2. rewrite <- Hn in SZ2.
  unfold FAKESZ, KHIGH, AIMG_HI in *.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + size / 8 <= shad (al_fake L) + 1446400 /\ shad F + size / 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. clear - G1 GL1 G3 FLO FHI F64 Npos SZ2 ATR. Z.div_mod_to_equations. lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (SHD : shad F + size / 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. clear - G2c G3 FLO FHI Npos ATR. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (DJ : forall A n, A + n <= ATOP -> (A + n <= flag \/ flag + 1 <= A) -> (A + n <= shad F \/ shad F + size / 8 <= A) -> disjoint_from W A n).
  { intros A n H1 H2 H3. apply disjoint_from_Forall. eapply Forall_impl; [| exact HW]. cbv beta. intros iv HQ. clear -HQ H1 H2 H3. lia. }
  assert (OUT : forall a, 0 <= a < 2^64 -> (a < ATOP \/ spz <= a) -> a <> flag -> ~ (shad F <= a < shad F + size / 8) -> m' (wa a) = m (wa a)).
  { intros a Ha H1 H2 H3. apply MU. rewrite wa_unsigned by lia. eapply outside_of_Forall; [exact HW|]. cbv beta. intros iv HQ. clear -HQ H1 H2 H3. lia. }
  assert (AT : m' (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m' flag _ FL1); clear -FR GL1; lia).
  (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF TCD TCT; nd_post).
  Local Ltac xdj H MU WM DJ K := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add]; K; lia].
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite SHL. eapply Forall_impl; [| exact HW]. cbv beta. intros iv HQ _.
    clear -HQ FR SB1 SB2. lia. }
  assert (HFK' : AFAKE L LB m').
  { split; [exact G|]. split.
    { tclr_int TCF. unfold afake_cells.
      split; [xdj REAL MU WM DJ ltac:(clear -GL1 FR SB1 SHS ATR)|].
      split; [xdj DTVP MU WM DJ ltac:(clear -KT GL1 G3 FR SB1 SB3 SHS ATR)|].
      split; [xdj DV MU WM DJ ltac:(clear -KT GL1 G3 FR SB1 SB3 SHS ATR)|].
      split; [xdj DTV1 MU WM DJ ltac:(clear -KT GL1 G3 FR SB1 SB3 SHS ATR)|].
      split; [xdj BD MU WM DJ ltac:(clear -G5s G6 G9 G3 GL1 FR SB1 SB3 SHS ATR)|].
      split; [xdj CF MU WM DJ ltac:(clear -GL1 FR SB1 SHS ATR)|].
      split; [xdj VERB MU WM DJ ltac:(clear -GL1 FR SB1 SHS ATR)|].
      eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split.
    { (nd_pre HDR 5%nat; intros h0 h1 h2 hs HS; nd_post). apply hdr_of_dc. eapply dc_at_any; [exact (dc_of_cells m _ _ HS)| exact WM| lia]. }
    split; [xdj LOG MU WM DJ ltac:(clear -G3 GL1 FR SHD ATR)|].
    split; [xdj NGC MU WM DJ ltac:(clear -G3 GL1 FR SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c2 pos' b Hc2 Hp2 Hb NZ.
      destruct (Z.eq_dec (fk_flag L c2 pos') flag) as [EQ|NE]; [exfalso; rewrite EQ, AT in Hb; congruence|].
      pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2.
      rewrite OUT in Hb by (clear -FRG2 NE G3 GL1 SHD ATR; lia).
      destruct (FL c2 pos' b Hc2 Hp2 Hb NZ) as [E|IN]; [|exact IN].
      exfalso. injection E as <- EF' _. apply NE. rewrite HF in EF'. apply fk_frame_inj in EF'; [|lia]. subst pos'. symmetry. exact EF.
    - intros c2 F' n' Hin. (nd_pre (LV c2 F' n' ltac:(right; exact Hin)) 6%nat; intros Hc2 Hn' pos' Hp2 HF' B1; nd_post).
      split; [exact Hc2|]. split; [exact Hn'|]. exists pos'. split; [exact Hp2|]. split; [exact HF'|].
      assert (NE : fk_flag L c2 pos' <> flag).
      { rewrite EF. apply (fk_flags_disjoint L c2 pos' c pos Hc2 Hp2 Hc Hp).
        intros E. injection E as -> ->. apply NI. rewrite HF, Hn, <- HF', <- Hn'. exact Hin. }
      pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2. rewrite OUT by (clear -FRG2 NE G3 GL1 SHD ATR; lia). exact B1. }
  split.
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| eapply ablocks_tail; exact BL]|]. cbn [AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + size <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c2] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st _ m p A' n' AHP ltac:(right; exact Hb)) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. clear -Q2 Q3 Q4 D FLO FHI Npos G3 GL1 ATR. lia.
    - (pose proof (afake_lb L _ m c2 A' n' HFK ltac:(right; exact Hb)) as ndP__; nd_pre ndP__ 9%nat; intros Hc2 Hn' Np' _ X1 X2 X3 X4 _; nd_post).
      pose proof (afake_lb_disjoint L _ m c2 A' n' c F size HFK ltac:(right; exact Hb) ltac:(left; reflexivity) ltac:(intros E; apply NI; rewrite <- E; exact Hb)) as DJF.
      split; [exact X3|]. clear -X1 X2 X4 DJF. lia. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') -> 0 <= a' < 2^47 /\ ~ (F <= a' < F + size)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c2 & FA & fn & Hb & Hr)]];
      [ clear - X1 FC ATR; lia | pose proof (CI_OK iv Hiv) as CK; clear - Hr CK GL1 FLO; lia |].
    (nd_pre (BLK _ Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. unfold AIMG_HI in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  intros a Ha Hcl. split; [| intros W0; apply WM; exact W0].
  destruct Hcl as [Hcl|TL].
  2:{ (* [comment removed for export] *)
      (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF0 _ _; nd_post). unfold tclr in TCF0. pose proof atp_lin as TLN. pose proof atp_below_atop as TBA.
      destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
      4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
            rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_fake L ALO) as DAF. unfold adisj in DAF.
          apply OUT; clear - Ha IM OAH OAHI DAF GL1 G3 FR SB1 SB3 SHS ATR; lia. }
      3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
          apply OUT; clear - Ha IM G2t GL1 G3 FR SB1 SHS ATR; Z.div_mod_to_equations; lia. }
      - apply OUT; clear - Ha T TCF0 TLN TBA GL1 G3 FR SB1 SB3 SHS ATR; lia.
      - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
        assert (SATOP : shad ATOP <= 17594332446720) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -ATR; Z.div_mod_to_equations; lia).
        assert (TSA : shad ta + 1 <= shad F \/ shad F + size / 8 <= shad ta).
        { destruct (tls_shadow_apart ta F size Hta ltac:(clear -Npos; lia)) as [D|D].
          - destruct TCF0 as [D|D]; [right; split; [clear -D FHI; lia| clear -F64; Z.div_mod_to_equations; lia] | left; clear -D FLO; lia].
          - left; exact D.
          - right. unfold shlen in D. rewrite Z.shiftr_div_pow2 in D by lia. exact D. }
        pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
        apply OUT; clear - Ha TS1 TS2 SATOP TSA G2t GL1 G3 FR ATR; lia. }
  destruct Hcl as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - apply OUT; clear - Ha Hs SPZ G3 FR SB3 ATR; lia.
  - pose proof (CI_OK iv Hiv) as CK. apply OUT; clear - Ha CK Hr GL1 FR SB1 SHS ATR; lia.
  - (nd_pre (BLK b Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). unfold ablk, AIMG_HI, KLS in Y1.
    apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr GL1 G3 FR SB1 SB3 SHS ATR; lia.
  - destruct (CLA a' Ha') as [A'R NA].
    assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SHA in Ha |- *. rewrite SHF in OUT.
    pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
    apply OUT; clear - Ha A'R NA F64 G2b G3 FR FLO FHI Npos SZ2 ATR; Z.div_mod_to_equations; lia.
Qed.
End Zd5.
#[using="HL CI_OK"] Lemma sf_core : ltac:(let t := eval cbv delta [sf_core__stmt] in sf_core__stmt in exact t).
Proof. exact sf_core__body. Qed.

(* [comment removed for export] *)
#[using="HL CI_OK"] Theorem fake_release_gen_P : forall L RNG st LB m m' cls F N spz,
  AHEAP_P AH L RNG st (FKB cls F N :: LB) m -> ATOP <= spz ->
  munch [(fflag L cls F, fflag L cls F + 1)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (fflag L cls F) [C1 (Z_to_bv 8 0)] ->
  AHEAP_P AH L RNG st LB m' /\ aheap_pres CI LB spz m m'.
Proof.
  intros L RNG st LB m m' cls F N spz AHP SPZ MU WM FL1.
  eapply (sf_core L RNG st LB m m' cls F N (fflag L cls F) _ spz AHP eq_refl SPZ MU WM); [| exact FL1].
  constructor; [right; left; cbn [fst snd]; split; reflexivity | constructor].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sf7_postP (req : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo F : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st LB m'
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 245) (Z.to_nat (req / 8)))].

Definition stack_free_7_P__stmt : Prop := forall (L : alayout) (RNG : footprint) (req : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo F : Z),
  AHEAP_P AH L RNG st (FKB 7 F 8192 :: LB) m ->
  a0 = Z_to_bv 64 F -> a1 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 ->
  rw_cells asegs m (F + 8184) [C8 (Z_to_bv 64 (fflag L 7 F))] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sf7_postP req L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo F m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKFREE7) fc None m (seg_rom asegs)).
Section Zd6.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 1).
Variable req : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 33).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 36).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 37).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 40).
Let flag := fflag L 7 F.
#[using="HL CI_OK flag"] Lemma stack_free_7_P__body : ltac:(let T := type of (fun (h : stack_free_7_P__stmt) => h L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo F) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (req, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, (lo, F))))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP A0 A1 REQ REQ8 SFP MI ST BOT LO SPT RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (AREP_poison_cells L st X m AR) as PC.
  (nd_pre (fake_flag_P L RNG st _ m 7 F 8192 AHP ltac:(left; reflexivity)) 5%nat; intros FLG RFLG FLB FLT _; nd_post).
  (pose proof (afake_lb L _ m 7 F 8192 HFK ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR0; nd_post).
  (pose proof HFK as ndP__; nd_pre ndP__ 8%nat; intros G _ _ _ _ _ DC2 _; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 _; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). pose proof atop_range as ATR.
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  chg (fflag L 7 F) flag.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHQ : shlen req = req / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 1024 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. clear - G1 GL1 G3 FLO FHI F64 ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  assert (SHD : shad F + 1024 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. clear - G2c G3 FLO FHI ATR. Z.div_mod_to_equations. lia. }
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) (shlen req) DC2 ltac:(lia) ltac:(rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia)
                ltac:(rewrite SHQ; clear -REQ SB2; Z.div_mod_to_equations; lia)) as DS2.
  destruct DS2 as [shj SHJ].
  assert (EFLAG : flag = fflag L 7 F) by reflexivity.
  clearbody flag.
  eapply evtF_mono.
  { eapply (stack_free7_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo flag F req (Z_to_bv 8 1) shj);
      try exact MI; try exact ST; try exact PC; try exact SFP; try exact FLG; try exact SHJ; try exact A0; try exact A1; try exact RIMG; try exact RTLS;
      try exact FK; try exact FLB; try exact RFLG; try exact REQ8;
      try (unfold SF7_STACK; clear -BOT LO FC FLT REQ ATR; lia).
    all: try (clear -F64; Z.div_mod_to_equations; lia).
    all: try (clear -FR0 FLO FHI; lia).
    all: try (rewrite SHQ; clear -FR0 SHD REQ; Z.div_mod_to_equations; lia).
    all: try (eapply rng_sub'; [exact RSTK| clear -BOT LO SPT; lia]).
    all: try (eapply rng_sub'; [exact RF| clear -FLO FHI; lia]).
    all: try (eapply rng_sub'; [exact RSH| rewrite SHQ; clear -SB1 SB2 REQ; Z.div_mod_to_equations; lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 17%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU WM MI' ST' FLG0 SH'; nd_post).
  unfold sf7_W, SF7_STACK in MU.
  destruct (sf_core L RNG st LB m m' 7 F 8192 flag _ (bv_unsigned sp) AHP EFLAG ltac:(clear -BOT LO; lia) MU WM) as (AHP' & HPR); [| exact FLG0 |].
  { repeat (constructor; [cbn [fst snd] |]); [left; clear -BOT LO; lia | right; left; split; reflexivity | right; right; rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia | constructor]. }
  unfold sf7_postP. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  rewrite SHQ in SH'. exact SH'.
Qed.
End Zd6.
#[using="HL CI_OK"] Theorem stack_free_7_P : ltac:(let t := eval cbv delta [stack_free_7_P__stmt] in stack_free_7_P__stmt in exact t).
Proof. exact stack_free_7_P__body. Qed.

End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm7.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.AFake_free7.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFAKE.
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

#[using="Type"] Lemma HB_FAKE : forall L RNG st LB m p A n,
  AHEAP_P AH L RNG st LB m -> In (HB p A n) LB ->
  ablock_range A n /\ (A + n <= al_fake L \/ al_fake L + 11571200 <= A).
Proof. intros. split; [eapply AHEAP_P_hb_range; eauto| eapply AHEAP_P_hb_fake; eauto]. Qed.

#[using="HL"] Lemma AREP_frame_ext' : forall L st X m m' W,
  alayout_ok L -> AREP AH L st X m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
            (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
         \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
         \/ ATOP <= fst iv) W ->
  AREP AH L st X m'.
Proof.
  (* [comment removed for export] *)
  intros L st X m m' W AL AR MU WM HW. eapply (AREP_frame_ext AH HL); [exact AL| exact AR| exact MU| exact WM|].
  eapply List.Forall_impl; [| exact HW]. cbv beta. intros iv H Hlt.
  destruct (H Hlt) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; left; exact A].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma AREP_cells : forall L st X m, AREP AH L st X m ->
  rt_got m /\ rt_shbase m
  /\ rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)]
  /\ rt_inited m /\ rt_layout m
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None).
Proof.
  intros L st X m H. pose proof (AREP_relro AH L st X m H) as RR. unfold AREP, arep_rt in H. decompose [and] H.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_OK"] Theorem fake_flag_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP          (* [comment removed for export] *)
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHP Hin. (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof (afake_lb L LB m cls F N HFK Hin) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR; nd_post).
  pose proof (afake_flag L LB m cls F N HFK Hin) as FL.
  destruct HFK as (G & _). (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold FAKESZ, KHIGH, AIMG_HI in *.   (* [comment removed for export] *)
  (nd_pre ARNG 8%nat; intros _ _ _ _ _ _ RF _; nd_post).
  split; [exact FL|]. split; [eapply rng_sub'; [exact RF| lia]|]. split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split.
  - intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    + pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [_ D]. lia.
    + (pose proof (afake_lb L LB m c' A' n' (proj2 (proj2 (proj2 AHP))) Hb) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ X1 X2 _; nd_post). lia.
  - intros (iv & Hiv & R). pose proof (CI_OK iv Hiv). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_tail : forall L st X b LB, ablocks L st X (b :: LB) -> ablocks L st X LB.
Proof.
  intros L st X b LB (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). right; exact Hin.
  - intros c A n Hin. apply (H2 c A n). right; exact Hin.
  - destruct b as [[p|c] A n]; cbn in H3; [inversion H3; assumption| exact H3].
  - inversion H4; assumption.
Qed.

#[using="HL"] Theorem fake_release_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_P AH L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP. (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof (afake_lb L _ m cls F N HFK ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR; nd_post).
  assert (NI : ~ In (mkABlock (ABFake cls) F N) LB) by ((nd_pre BL 4%nat; intros _ _ _ ND; nd_post); inversion ND; assumption).
  destruct HFK as (G & HFK'). (pose proof G as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold FAKESZ, AIMG_HI in *.   (* [comment removed for export] *)
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| eapply ablocks_tail; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AH ah_fake]. apply (afake_release L LB m cls F N); [exact (conj G HFK')| exact NI].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.


#[using="Type"] Lemma AREP_poison_cells : forall L st X m, AREP AH L st X m -> poison_cells m.
Proof.
  intros L st X m H. unfold AREP, arep_rt in H. decompose [and] H. unfold poison_cells.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_fake_cls (c : Z) (b : ablock) : bool := match ab_kind b with ABFake c' => Z.eqb c' c | ABHeap _ => false end.
Definition fk_count (c : Z) (LB : list ablock) : Z := Z.of_nat (length (List.filter (is_fake_cls c) LB)).

#[using="Type"] Lemma fk_count_le_length : forall c LB, fk_count c LB <= Z.of_nat (length LB).
Proof. intros c LB. unfold fk_count. pose proof (filter_length_le (is_fake_cls c) LB). lia. Qed.

#[using="Type"] Lemma fk_frame_inj : forall L c p1 p2, 0 <= c -> fk_frame L c p1 = fk_frame L c p2 -> p1 = p2.
Proof. intros L c p1 p2 Hc E. unfold fk_frame in E. pose proof (fk_fsize_pos c Hc). nia. Qed.

#[using="Type"] Lemma probe_find : forall L LB m c h,
  AFAKE L LB m -> 0 <= c < FK_NCLS -> fk_count c LB < fk_nframes c ->
  exists j, 0 <= j < fk_nframes c
    /\ (forall k, 0 <= k < j -> rw_cells asegs m (fk_flag L c ((h + k) mod fk_nframes c)) [C1 (Z_to_bv 8 1)])
    /\ rw_cells asegs m (fk_flag L c ((h + j) mod fk_nframes c)) [C1 (Z_to_bv 8 0)].
Proof.
  intros L LB m c h AF Hc CNT.
  (pose proof AF as ndP__; nd_pre ndP__ 9%nat; intros G _ _ _ _ DC1 _ FL LV; nd_post).
  (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). pose proof (ablk_lin _ _ G2) as (GL1 & _). unfold AIMG_HI, FAKESZ in *.
  assert (NP : 0 < fk_nframes c) by (apply fk_nframes_pos; unfold FK_NCLS in Hc; lia).
  set (N := fk_nframes c) in *.
  assert (POS : forall k, 0 <= (h + k) mod N < N) by (intros k; apply Z.mod_pos_bound; exact NP).
  (* [comment removed for export] *)
  assert (CELL : forall pos, 0 <= pos < N -> exists b : byte, rw_cells asegs m (fk_flag L c pos) [C1 b] /\ m (wa (fk_flag L c pos)) = Some b).
  { intros pos Hp. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    pose proof (dc_sub m (al_fake L + 4096) (11571200 - 4096) (fk_flag L c pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D.
    destruct (c1_of_dc m _ D) as [b Hb]. exists b. split; [exact Hb|]. apply (rw_C1_high m _ b Hb). lia. }
  (* [comment removed for export] *)
  assert (ONE : forall pos b, 0 <= pos < N -> m (wa (fk_flag L c pos)) = Some b -> b <> Z_to_bv 8 0 ->
                 b = Z_to_bv 8 1 /\ In (FKB c (fk_frame L c pos) (fk_fsize c)) LB).
  { intros pos b Hp Hb NZ. pose proof (FL c pos b Hc Hp Hb NZ) as IN. split; [|exact IN].
    (nd_pre (LV _ _ _ IN) 6%nat; intros _ _ pos' Hp' HF' B1; nd_post).
    apply fk_frame_inj in HF'; [|lia]. subst pos'. congruence. }
  destruct (first_free (fun i => m (wa (fk_flag L c ((h + i) mod N))) = Some (Z_to_bv 8 0))
              ltac:(intros i; apply (decide _)) (fk_count c LB + 1) ltac:(unfold fk_count; lia)) as [(j & Hj & Pj & Lj)|NONE].
  - exists j. split; [lia|]. split.
    + intros k Hk. (nd_pre (CELL _ (POS k)) 3%nat; intros b Cb Mb; nd_post).
      destruct (ONE _ b (POS k) Mb) as [-> _]; [| exact Cb]. intros ->. exact (Lj k Hk Mb).
    + (nd_pre (CELL _ (POS j)) 3%nat; intros b Cb Mb; nd_post). rewrite Mb in Pj. injection Pj as ->. exact Cb.
  - exfalso.
    pose proof (pigeon_Z ablock (fun k => FKB c (fk_frame L c ((h + k) mod N)) (fk_fsize c)) (fk_count c LB + 1)
                  (List.filter (is_fake_cls c) LB) ltac:(unfold fk_count; lia)) as PG.
    cbv beta in PG. unfold fk_count in *. 
    assert (LE : Z.of_nat (length (List.filter (is_fake_cls c) LB)) + 1 <= Z.of_nat (length (List.filter (is_fake_cls c) LB))); [|lia].
    apply PG.
    + intros k Hk. apply filter_In. split; [| cbn; apply Z.eqb_refl].
      (nd_pre (CELL _ (POS k)) 3%nat; intros b Cb Mb; nd_post).
      destruct (ONE _ b (POS k) Mb) as [_ IN]; [| exact IN]. intros ->. exact (NONE k Hk Mb).
    + intros k1 k2 H1 H2 E. injection E as E. apply fk_frame_inj in E; [|lia].
      eapply (probe_pos_inj N h); [exact NP | lia | lia | exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma byte01_ne : Z_to_bv 8 0 <> Z_to_bv 8 1 :> byte.
Proof. intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate. Qed.

#[using="Type"] Lemma fk_fsize_cases : forall c, 0 <= c <= 7 -> 64 <= fk_fsize c <= 8192 /\ fk_fsize c mod 64 = 0.
Proof.
  intros c Hc. assert (E : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; repeat split; congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_of_dc : forall m A, dc_at m A 88 -> exists (h0 h1 h2 : word) (hs : list byte), rw_cells asegs m A [C8 h0; C8 h1; C8 h2; CB 64 hs].
Proof.
  intros m A D. destruct (dc_take m A 88 8 D ltac:(lia)) as [D0 D1]. replace (88 - 8) with 80 in D1 by reflexivity.
  destruct (dc_take m (A + 8) 80 16 D1 ltac:(lia)) as [D12 D3]. replace (80 - 16) with 64 in D3 by reflexivity.
  destruct (c8_of_dc m A D0) as [h0 H0]. (nd_pre (c8c8_of_dc m (A + 8) D12) 3%nat; intros h1 h2 H12; nd_post). destruct D3 as [hs H3].
  change (Z.to_nat 64) with 64%nat in H3. exists h0, h1, h2, hs.
  apply (proj2 (rw_cells_app asegs m A [C8 h0] _)). split; [exact H0|]. cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs m (A + Z.of_nat 8) [C8 h1; C8 h2] _)). split; [replace (A + Z.of_nat 8) with (A + 8) by lia; exact H12|].
  cbn [cells_size csize Nat.add]. replace (A + Z.of_nat 8 + Z.of_nat 16) with (A + 8 + 16) by lia. exact H3.
Qed.

Definition sm_core__stmt : Prop := forall L RNG st LB m m' lo spz c pos size K shn flag F,
  AHEAP_P AH L RNG st LB m ->
  0 <= c <= 7 -> 0 <= pos < fk_nframes c -> size = fk_fsize c ->
  flag = fk_flag L c pos -> F = fk_frame L c pos ->
  m (wa flag) = Some (Z_to_bv 8 0) ->
  ATOP + 4096 <= lo -> 0 <= K -> lo <= spz - K -> spz <= al_top L ->
  0 <= shn <= size / 8 ->
  munch [(spz - K, spz); (al_fake L + 8 * c, al_fake L + 8 * c + 8); (flag, flag + 1); (F + 24, F + 32); (F + size - 8, F + size);
         (shad F, shad F + shn)] m m' ->
  wmono asegs m m' ->
  rw_cells asegs m' flag [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m' (F + size - 8) [C8 (Z_to_bv 64 flag)] ->
  aheap_pres CI LB spz m m'
  /\ AHEAP_P AH L RNG st (FKB c F size :: LB) m'
  /\ F mod 64 = 0 /\ ablk F (F + size) /\ F + size <= ATOP /\ 0 < F
  /\ (exists (j0 j1 j2 : word) (junk : list byte), length junk = Z.to_nat (size - 32)
        /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (size - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))])
  /\ rng RNG F size /\ rng RNG (shad F) (size / 8).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 5).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 6).
Variable spz : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 7).
Variable c : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 8).
Variable pos : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 9).
Variable size : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 10).
Variable K : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 11).
Variable shn : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 12).
Variable flag : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 13).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sm_core__stmt 14).
#[using="HL CI_OK"] Lemma sm_core__body : ltac:(let T := type of (fun (h : sm_core__stmt) => h L RNG st LB m m' lo spz c pos size K shn flag F) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (st, (LB, (m, (m', (lo, (spz, (c, (pos, (size, (K, (shn, (flag, F))))))))))))))) as _.
  intros AHP Hc Hp Hsz EFL EFR FL0 BOT K0 LO SPT SHN MU WM FL1 FPTR.
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE HDR LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  (nd_pre CE 8%nat; intros REAL DTVP DV DTV1 BD CF VERB T48; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros SK1 SK2 SK3; nd_post).
  assert (Hc' : 0 <= c < FK_NCLS) by (unfold FK_NCLS; lia).
  pose proof (fk_flag_range L c pos Hc' Hp) as FRG. rewrite <- EFL in FRG.
  (pose proof (fk_frame_range L c pos Hc' Hp) as ndP__; nd_pre ndP__ 4%nat; intros _ _ FR3 FR4; nd_post). rewrite <- EFR in FR3. rewrite <- EFR, <- Hsz in FR4.
  pose proof (fk_frame_al64 L c pos G1 ltac:(lia)) as F64. rewrite <- EFR in F64.
  pose proof (fk_fsize_cases c Hc) as (SZ1 & SZ2). rewrite <- Hsz in SZ1, SZ2.
  assert (EFF : fflag L c F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  unfold FAKESZ, KHIGH, AIMG_HI in *.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + size / 8 <= shad (al_fake L) + 1446400 /\ shad F + size / 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. clear - G1 GL1 G3 FR3 FR4 F64 SZ1 SZ2 ATR. Z.div_mod_to_equations. lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (SHD : shad F + size / 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. clear - G2c G3 FR3 FR4 SZ1 ATR. Z.div_mod_to_equations. lia. }
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (spz - K <= a < spz) -> ~ (al_fake L + 8 * c <= a < al_fake L + 8 * c + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + size - 8 <= a < F + size) -> ~ (shad F <= a < shad F + shn) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside fst snd]. repeat split; lia. }
  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length fst snd]; K; lia].
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite SHL.
    repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor]. }
  assert (NOTIN : ~ In (FKB c F size) LB).
  { intros IN. (nd_pre (LV _ _ _ IN) 6%nat; intros _ _ pos' Hp' HF' B1; nd_post). rewrite EFR in HF'. apply fk_frame_inj in HF'; [|lia]. subst pos'.
    rewrite <- EFL, FL0 in B1. apply byte01_ne. congruence. }
  (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF TCD TCT; nd_post).
  assert (HFK' : AFAKE L (FKB c F size :: LB) m').
  { split; [exact G|]. split.
    { tclr_int TCF. unfold afake_cells.
      split; [xportk REAL MU WM ltac:(clear -GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR)|].
      split; [xportk DTVP MU WM ltac:(clear -KT GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk DV MU WM ltac:(clear -KT GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk DTV1 MU WM ltac:(clear -KT GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO K0 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR)|].
      split; [xportk CF MU WM ltac:(clear -GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR)|].
      split; [xportk VERB MU WM ltac:(clear -GL1 G3 BOT LO K0 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR)|].
      eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split.
    { (nd_pre HDR 5%nat; intros h0 h1 h2 hs HS; nd_post). apply hdr_of_dc.
      eapply dc_at_any; [exact (dc_of_cells m _ _ HS)| exact WM| lia]. }
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO K0 FRG FR3 FR4 SHD SZ1 SHN Hc ATR)|].
    split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO K0 FRG FR3 FR4 SHD SZ1 SHN Hc ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c2 pos' b Hc2 Hp2 Hb NZ.
      destruct (Z.eq_dec (fk_flag L c2 pos') flag) as [EQ|NE].
      + left. assert (E2 : (c2, pos') = (c, pos)).
        { destruct (decide ((c2, pos') = (c, pos))) as [E|NE2]; [exact E| exfalso].
          apply (fk_flags_disjoint L c2 pos' c pos Hc2 Hp2 Hc' Hp NE2). rewrite EQ, EFL. reflexivity. }
        injection E2 as -> ->. rewrite <- EFR, <- Hsz. reflexivity.
      + right. pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2.
        rewrite OUT in Hb by (clear -FRG2 NE G3 GL1 BOT LO K0 FR3 FR4 SHD SZ1 SHN Hc ATR; lia). eapply FL; eauto.
    - intros c2 F' n' [E|Hin].
      + injection E as <- <- <-. split; [exact Hc'|]. split; [exact Hsz|].
        exists pos. split; [exact Hp|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + (nd_pre (LV c2 F' n' Hin) 6%nat; intros Hc2 Hn pos' Hp2 HF' B1; nd_post).
        split; [exact Hc2|]. split; [exact Hn|]. exists pos'. split; [exact Hp2|]. split; [exact HF'|].
        assert (NE : fk_flag L c2 pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c2 pos' c pos Hc2 Hp2 Hc' Hp).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, Hsz, <- HF', <- Hn. exact Hin. }
        pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2.
        rewrite OUT by (clear -FRG2 NE G3 GL1 BOT LO K0 FR3 FR4 SHD SZ1 SHN Hc ATR; lia). exact B1. }
  assert (BL' : ablocks L st X (FKB c F size :: LB)).
  { (nd_pre BL 4%nat; intros B1 B2 B3 B4; nd_post). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c2 A n [E|Hin]; [| exact (B2 c2 A n Hin)]. injection E as <- <- <-. clear -FR3 FR4 SZ1. lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FKB c F size :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + size <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c2] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. clear -Q2 Q3 Q4 D FR3 FR4 SZ1 G3 GL1 ATR. lia.
    - (pose proof (afake_lb L LB m c2 A' n' HFK Hb) as ndP__; nd_pre ndP__ 12%nat; intros Hc2 Hn' Np' _ X1 X2 X3 X4 pos' Hp2 HF' _; nd_post).
      assert (NEQ : (c2, pos') <> (c, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, Hsz, <- HF', <- Hn'. exact Hb. }
      pose proof (fk_frames_disjoint L c2 pos' c pos Hc2 Hp2 Hc' Hp NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn', <- Hsz in DJ.
      split; [exact X3|]. unfold FAKESZ in *. clear -X1 X2 X4 DJ. lia. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + size)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c2 & FA & fn & Hb & Hr)]];
      [ clear - X1 G3 FR4 SZ1 ATR; lia | pose proof (CI_OK iv Hiv) as CK; clear - Hr CK GL1 FR3; lia |].
    (nd_pre (BLK _ Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. unfold AIMG_HI in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  assert (HPR : aheap_pres CI LB spz m m').
  { intros a Ha Hcl. split; [| intros W0; apply WM; exact W0].
    destruct Hcl as [Hcl|TL].
    2:{ (* [comment removed for export] *)
        (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF0 _ _; nd_post). unfold tclr in TCF0. pose proof atp_lin as TLN. pose proof atp_below_atop as TBA.
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
            rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_fake L ALO) as DAF. unfold adisj in DAF.
            apply OUT; clear - Ha IM OAH OAHI DAF BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
            apply OUT; clear - Ha IM G2t BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SHS SZ1 SHN Hc ATR; Z.div_mod_to_equations; lia. }
        - apply OUT; clear - Ha T TCF0 TLN TBA BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SB3 SHS SZ1 SHN Hc ATR; lia.
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SATOP : shad ATOP <= 17594332446720) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -ATR; Z.div_mod_to_equations; lia).
          assert (TSA : shad ta + 1 <= shad F \/ shad F + size / 8 <= shad ta).
          { destruct (tls_shadow_apart ta F size Hta ltac:(clear -SZ1; lia)) as [D|D].
            - destruct TCF0 as [D|D]; [right; split; [clear -D FR4; lia| clear -F64; Z.div_mod_to_equations; lia] | left; clear -D FR3; lia].
            - left; exact D.
            - right. unfold shlen in D. rewrite Z.shiftr_div_pow2 in D by lia. exact D. }
          pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
          apply OUT; clear - Ha TS1 TS2 SATOP TSA G2t BOT LO K0 GL1 G3 FRG FR3 FR4 SZ1 SHN Hc ATR; lia. }
    destruct Hcl as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO K0 SPT GL1 G3 FRG FR3 FR4 SB2 SB3 SHS SHN SZ1 Hc ATR; lia.
    - pose proof (CI_OK iv Hiv) as CK. apply OUT; clear - Ha CK Hr BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SHS SHN SZ1 Hc ATR; lia.
    - (nd_pre (BLK b Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr BOT LO K0 GL1 G3 FRG FR3 FR4 SB1 SB2 SB3 SHS SHN SZ1 Hc ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *. rewrite SHF in OUT.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 FRG FR3 FR4 SZ1 SZ2 SHN LO BOT K0 Hc ATR; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F (size - 8) DC1 ltac:(clear -FR3; lia) ltac:(clear -SZ1; lia) ltac:(clear -FR4; lia)) as DF0.
  pose proof (dc_at_any m m' F (size - 8) DF0 WM ltac:(clear -GL1 FR3; lia)) as DF1.
  destruct (dc_take m' F (size - 8) 24 DF1 ltac:(clear -SZ1; lia)) as [DW DJ]. replace (size - 8 - 24) with (size - 32) in DJ by (clear; lia).
  destruct (dc_take m' F 24 8 DW ltac:(clear; lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. (nd_pre (c8c8_of_dc m' (F + 8) DW12) 3%nat; intros j1 j2 J12; nd_post).
  destruct DJ as [junk J1].
  assert (LJ : length junk = Z.to_nat (size - 32)) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (size - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB (Z.to_nat (size - 32)) junk] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia. exact J1.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SZ1; lia).
      replace (F + Z.of_nat 8 + Z.of_nat 16 + (size - 32)) with (F + size - 8) by lia. exact FPTR. }
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  split; [exact HPR|]. split; [exact AHP'|]. split; [exact F64|].
  split; [eapply ablk_sub; [exact G2| clear - FR3; lia| clear - FR4; lia]|]. split; [clear - G3 FR4; lia|]. split; [clear -GL1 FR3; lia|].
  split; [exists j0, j1, j2, junk; split; [exact LJ| exact FRM]|].
  split; [eapply rng_sub'; [exact A7| clear - FR3 FR4 SZ1; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 SZ1; Z.div_mod_to_equations; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Lemma sm_core : ltac:(let t := eval cbv delta [sm_core__stmt] in sm_core__stmt in exact t).
Proof. exact sm_core__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SM_STACK : Z := 4096.

(* [comment removed for export] *)
Definition sm_postP (c size : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FKB c F size :: LB) m'
    /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + size) /\ F + size <= ATOP
    /\ length junk = Z.to_nat (size - 32)
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (size - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
    /\ rng RNG F size /\ rng RNG (shad F) (size / 8).

(* [comment removed for export] *)
#[using="Type"] Lemma tlsga_of_inv : forall L st X LB m, AREP AH L st X m -> AFAKE L LB m ->
  tlsga_cells m (al_t L) (al_dtls L) ATPv (Z_to_bv 64 (al_fake L)).
Proof.
  intros L st X LB m AR HFK. (nd_pre HFK 3%nat; intros G CE _; nd_post). (nd_pre CE 8%nat; intros REAL DTVP DV DTV1 BD CF VERB T48; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  pose proof (relro_word m 0xa58e0 0x13e498 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xa65a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xa6598 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  (nd_pre (c8c8_of_dc m _ T48) 3%nat; intros tb te T48'; nd_post).
  unfold tlsga_cells. split; [exact REAL|]. split; [exact DESC|]. split; [exact DTVP|].
  split; [unfold ADTV, ATP; replace (ATPv + 288 + 8) with (ATPv + 296) by (clear; lia); exact DTV1|].
  split; [exact R2|]. split; [exact CF|]. split; [exact GB0|]. split; [exact VERB|]. split; [exact G08|].
  split; [exact DV|]. split; [exact BD|]. exists tb, te; exact T48'.
Qed.

Definition stack_malloc_0_P__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fk_count 0 LB < fk_nframes 0 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm_postP 0 64 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 32).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_0_P__stmt 38).
#[using="HL CI_OK"] Lemma stack_malloc_0_P__body : ltac:(let T := type of (fun (h : stack_malloc_0_P__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP CNT MI ST BOT LO SPT TP RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (tlsga_of_inv L st X LB m AR HFK) as TC.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HNT) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  pose proof atop_range as ATR.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  (* [comment removed for export] *)
  pose proof (dc_sub m (al_fake L) 88 (al_fake L) 8 (dc_of_cells m _ _ HNT) ltac:(lia) ltac:(lia) ltac:(lia)) as DH.
  destruct (c8_of_dc m _ DH) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  (nd_pre (probe_find L LB m 0 h HFK ltac:(unfold FK_NCLS; lia) CNT) 4%nat; intros j Hj LIVE FREE; nd_post).
  replace (fk_nframes 0) with 16384 in * by reflexivity.
  set (pos := Z.land (h + j) 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (LM : forall x, Z.land x 16383 = x mod 16384) by (intros x; change 16383 with (2^14 - 1); rewrite land_ones_mod by lia; reflexivity).
  assert (PB : 0 <= pos < 16384) by (subst pos; rewrite LM; apply Z.mod_pos_bound; lia).
  assert (FKF : forall p, fk_flag L 0 p = al_fake L + 4096 + p) by (intros p; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFL : flag = fk_flag L 0 pos) by (rewrite FKF; reflexivity).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (LIVE' : forall k, 0 <= k < j -> rw_cells asegs m (al_fake L + 4096 + Z.land (h + k) 16383) [C1 (Z_to_bv 8 1)]).
  { intros k Hk. rewrite LM, <- FKF. exact (LIVE k Hk). }
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]) by (subst flag pos; rewrite LM, <- FKF; exact FREE).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 8 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].
  assert (HW' : rw_cells asegs m (al_fake L) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
  (* [comment removed for export] *)
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  assert (HPOS : pos = Z.land (h + j) 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc0_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) ATPv (al_fake L) h j pos flag F j24 j56 sh0);
      try exact MI; try exact ST; try exact TP; try exact TC; try exact LIVE'; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 14%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MU WM MI' ST' HNT2 FL1 F24' F56' SH'; nd_post).
  unfold sm0_W in MU.
  (nd_pre (sm_core L RNG st LB m m' lo (bv_unsigned sp) 0 pos 64 208 8 flag F AHP ltac:(lia) ltac:(replace (fk_nframes 0) with 16384 by reflexivity; exact PB)
              eq_refl EFL EFR FLM BOT ltac:(lia) ltac:(lia) SPT ltac:(cbn; lia)
              ltac:(eapply munch_weaken; [| exact MU]; intros xq Hq; cbn [outside fst snd] in Hq |- *; clear -Hq; lia) WM FL1
              ltac:(replace (F + 64 - 8) with (F + 56) by lia; exact F56')) 9%nat; intros HPR AHP' F64 FBLK FTOP F0 (j0 & j1 & j2 & junk & LJ & FRM) RF1 RF2; nd_post).
  unfold sm_postP. exists F. do 14 eexists. exists m', j0, j1, j2, junk.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [exact F0|]. split; [exact FBLK|]. split; [exact FTOP|]. split; [exact LJ|]. split; [exact FRM|].
  split; [| split; [exact RF1| exact RF2]].
  eapply rw_cells_recast; [exact SH' | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity].
Qed.
End Zd2.
#[using="HL CI_OK"] Theorem stack_malloc_0_P : ltac:(let t := eval cbv delta [stack_malloc_0_P__stmt] in stack_malloc_0_P__stmt in exact t).
Proof. exact stack_malloc_0_P__body. Qed.

Definition stack_malloc_1_P__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fk_count 1 LB < fk_nframes 1 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm_postP 1 128 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 32).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_1_P__stmt 38).
#[using="HL CI_OK"] Lemma stack_malloc_1_P__body : ltac:(let T := type of (fun (h : stack_malloc_1_P__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP CNT MI ST BOT LO SPT TP RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (tlsga_of_inv L st X LB m AR HFK) as TC.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HNT) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  pose proof atop_range as ATR.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  (* [comment removed for export] *)
  pose proof (dc_sub m (al_fake L) 88 (al_fake L + 8) 8 (dc_of_cells m _ _ HNT) ltac:(lia) ltac:(lia) ltac:(lia)) as DH.
  destruct (c8_of_dc m _ DH) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  (nd_pre (probe_find L LB m 1 h HFK ltac:(unfold FK_NCLS; lia) CNT) 4%nat; intros j Hj LIVE FREE; nd_post).
  replace (fk_nframes 1) with 8192 in * by reflexivity.
  set (pos := Z.land (h + j) 8191). set (flag := (al_fake L) + 20480 + pos). set (F := (al_fake L) + 1085440 + pos * 128).
  assert (LM : forall x, Z.land x 8191 = x mod 8192) by (intros x; change 8191 with (2^13 - 1); rewrite land_ones_mod by lia; reflexivity).
  assert (PB : 0 <= pos < 8192) by (subst pos; rewrite LM; apply Z.mod_pos_bound; lia).
  assert (FKF : forall p, fk_flag L 1 p = al_fake L + 20480 + p) by (intros p; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFL : flag = fk_flag L 1 pos) by (rewrite FKF; reflexivity).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (LIVE' : forall k, 0 <= k < j -> rw_cells asegs m (al_fake L + 20480 + Z.land (h + k) 8191) [C1 (Z_to_bv 8 1)]).
  { intros k Hk. rewrite LM, <- FKF. exact (LIVE k Hk). }
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]) by (subst flag pos; rewrite LM, <- FKF; exact FREE).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 16 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D120.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D120) as [j120 F120].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  (nd_pre (c8c8_of_dc m _ DS2) 3%nat; intros sh0 sh1 SH0; nd_post).
  assert (HW' : rw_cells asegs m (al_fake L + 8) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
  (* [comment removed for export] *)
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  assert (HPOS : pos = Z.land (h + j) 8191) by reflexivity. assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc1_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) ATPv (al_fake L) h j pos flag F j24 j120 sh0 sh1);
      try exact MI; try exact ST; try exact TP; try exact TC; try exact LIVE'; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 14%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MU WM MI' ST' HNT2 FL1 F24' F120' SH'; nd_post).
  unfold sm1_W in MU.
  (nd_pre (sm_core L RNG st LB m m' lo (bv_unsigned sp) 1 pos 128 208 16 flag F AHP ltac:(lia) ltac:(replace (fk_nframes 1) with 8192 by reflexivity; exact PB)
              eq_refl EFL EFR FLM BOT ltac:(lia) ltac:(lia) SPT ltac:(cbn; lia)
              ltac:(eapply munch_weaken; [| exact MU]; intros xq Hq; cbn [outside fst snd] in Hq |- *; clear -Hq; lia) WM FL1
              ltac:(replace (F + 128 - 8) with (F + 120) by lia; exact F120')) 9%nat; intros HPR AHP' F64 FBLK FTOP F0 (j0 & j1 & j2 & junk & LJ & FRM) RF1 RF2; nd_post).
  unfold sm_postP. exists F. do 14 eexists. exists m', j0, j1, j2, junk.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [exact F0|]. split; [exact FBLK|]. split; [exact FTOP|]. split; [exact LJ|]. split; [exact FRM|].
  split; [| split; [exact RF1| exact RF2]].
  eapply rw_cells_recast; [exact SH' | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity].
Qed.
End Zd3.
#[using="HL CI_OK"] Theorem stack_malloc_1_P : ltac:(let t := eval cbv delta [stack_malloc_1_P__stmt] in stack_malloc_1_P__stmt in exact t).
Proof. exact stack_malloc_1_P__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sm7_postP (req : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk sjunk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FKB 7 F 8192 :: LB) m'
    /\ F mod 64 = 0 /\ 0 < F /\ ablk F (F + 8192) /\ F + 8192 <= ATOP
    /\ length junk = Z.to_nat (8192 - 32)
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (8192 - 32)) junk; C8 (Z_to_bv 64 (fflag L 7 F))]
    /\ length sjunk = Z.to_nat ((8192 - req) / 8)
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8))); CB (Z.to_nat ((8192 - req) / 8)) sjunk]
    /\ rng RNG F 8192 /\ rng RNG (shad F) (8192 / 8).

Definition stack_malloc_7_P__stmt : Prop := forall (L : alayout) (RNG : footprint) (req : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fk_count 7 LB < fk_nframes 7 ->
  a0 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm7_postP req L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC7) fc None m (seg_rom asegs)).
Section Zd4.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 1).
Variable req : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 33).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 36).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 37).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_malloc_7_P__stmt 39).
#[using="HL CI_OK"] Lemma stack_malloc_7_P__body : ltac:(let T := type of (fun (h : stack_malloc_7_P__stmt) => h L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (req, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP CNT A0 REQ REQ8 MI ST BOT LO SPT TP RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (tlsga_of_inv L st X LB m AR HFK) as TC. pose proof (AREP_poison_cells L st X m AR) as PC.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HNT) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  pose proof atop_range as ATR.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (nd_pre (AREP_cells L st X m AR) 10%nat; intros R2 R11 R13 R14 R15 R16 R24 R25 R28 RR; nd_post).
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  (* [comment removed for export] *)
  pose proof (dc_sub m (al_fake L) 88 (al_fake L + 56) 8 (dc_of_cells m _ _ HNT) ltac:(lia) ltac:(lia) ltac:(lia)) as DH.
  destruct (c8_of_dc m _ DH) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  (nd_pre (probe_find L LB m 7 h HFK ltac:(unfold FK_NCLS; lia) CNT) 4%nat; intros j Hj LIVE FREE; nd_post).
  replace (fk_nframes 7) with 128 in * by reflexivity.
  set (pos := Z.land (h + j) 127). set (flag := (al_fake L) + 36608 + pos). set (F := (al_fake L) + 7376896 + pos * 8192).
  assert (LM : forall x, Z.land x 127 = x mod 128) by (intros x; change 127 with (2^7 - 1); rewrite land_ones_mod by lia; reflexivity).
  assert (PB : 0 <= pos < 128) by (subst pos; rewrite LM; apply Z.mod_pos_bound; lia).
  assert (FKF : forall p, fk_flag L 7 p = al_fake L + 36608 + p) by (intros p; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFL : flag = fk_flag L 7 pos) by (rewrite FKF; reflexivity).
  assert (EFR : F = fk_frame L 7 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (LIVE' : forall k, 0 <= k < j -> rw_cells asegs m (al_fake L + 36608 + Z.land (h + k) 127) [C1 (Z_to_bv 8 1)]).
  { intros k Hk. rewrite LM, <- FKF. exact (LIVE k Hk). }
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]) by (subst flag pos; rewrite LM, <- FKF; exact FREE).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHQ : shlen req = req / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 1024 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 8184) 8 DC1 ltac:(subst F; lia) ltac:(lia) ltac:(subst F; lia)) as D8184.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D8184) as [j8184 F8184].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) (shlen req) DC2 ltac:(lia) ltac:(rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia) ltac:(rewrite SHQ; clear -REQ SB2; Z.div_mod_to_equations; lia)) as DS2.
  destruct DS2 as [shj SHJ].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + req / 8) ((8192 - req) / 8) DC2 ltac:(clear -REQ SB1; Z.div_mod_to_equations; lia) ltac:(clear -REQ; Z.div_mod_to_equations; lia) ltac:(clear -REQ REQ8 SB2; Z.div_mod_to_equations; lia)) as DS3.
  assert (HW' : rw_cells asegs m (al_fake L + 56) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
  (* [comment removed for export] *)
  (pose proof ARNG as ndP__; nd_pre ndP__ 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10; nd_post).
  assert (HPOS : pos = Z.land (h + j) 127) by reflexivity. assert (HFLAG : flag = (al_fake L) + 36608 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 7376896 + pos * 8192) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc7_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) ATPv (al_fake L) h j pos flag F req j24 j8184 shj);
      try exact MI; try exact ST; try exact TP; try exact TC; try exact PC; try exact LIVE'; try exact A0; try exact SHJ; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 16%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MU WM MI' ST' HNT2 FL1 F24' F8184' SH'; nd_post).
  unfold sm7_W in MU.
  (nd_pre (sm_core L RNG st LB m m' lo (bv_unsigned sp) 7 pos 8192 224 (shlen req) flag F AHP ltac:(lia) ltac:(replace (fk_nframes 7) with 128 by reflexivity; exact PB)
              eq_refl EFL EFR FLM BOT ltac:(lia) ltac:(lia) SPT ltac:(rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia)
              ltac:(eapply munch_weaken; [| exact MU]; intros xq Hq; cbn [outside fst snd] in Hq |- *; clear -Hq; lia) WM FL1
              ltac:(replace (F + 8192 - 8) with (F + 8184) by lia; exact F8184')) 9%nat; intros HPR AHP' F64 FBLK FTOP F0 (j0 & j1 & j2 & junk & LJ & FRM) RF1 RF2; nd_post).
  pose proof (dc_at_any m m' _ _ DS3 WM ltac:(clear -SB1 SHS GL1 REQ; Z.div_mod_to_equations; lia)) as DS3'. destruct DS3' as [sjunk SJ].
  assert (LSJ : length sjunk = Z.to_nat ((8192 - req) / 8)) by (destruct SJ as [[[WF _] _] _]; cbn in WF; lia).
  unfold sm7_postP. exists F. do 14 eexists. exists m', j0, j1, j2, junk, sjunk.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [exact F0|]. split; [exact FBLK|]. split; [exact FTOP|]. split; [exact LJ|]. split; [exact FRM|].
  split; [exact LSJ|]. split; [| split; [exact RF1| exact RF2]].
  rewrite SHQ in SH'.
  apply (proj2 (rw_cells_app asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8)))] _)). split; [exact SH'|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -REQ; Z.div_mod_to_equations; lia). exact SJ.
Qed.
End Zd4.
#[using="HL CI_OK"] Theorem stack_malloc_7_P : ltac:(let t := eval cbv delta [stack_malloc_7_P__stmt] in stack_malloc_7_P__stmt in exact t).
Proof. exact stack_malloc_7_P__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma outside_of_Forall : forall (W : list (Z * Z)) (Q : Z * Z -> Prop) a,
  Forall Q W -> (forall iv, Q iv -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof. induction W as [|[lo hi] W IH]; intros Q a HF HQ; cbn; [exact I|]. inversion HF; subst. split; [exact (HQ (lo, hi) H1)| eapply IH; eauto]. Qed.

#[using="Type"] Lemma fk_fsize_mod64 : forall c, 0 <= c -> fk_fsize c mod 64 = 0.
Proof. intros c Hc. unfold fk_fsize. rewrite Z.pow_add_r by lia. change (2^6) with 64. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

Definition sf_core__stmt : Prop := forall L RNG st LB m m' c F size flag W spz,
  AHEAP_P AH L RNG st (FKB c F size :: LB) m ->
  flag = fflag L c F -> ATOP <= spz ->
  munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (ATOP <= fst iv /\ snd iv <= spz) \/ (fst iv = flag /\ snd iv = flag + 1)
                    \/ (shad F <= fst iv /\ snd iv <= shad F + size / 8)) W ->
  rw_cells asegs m' flag [C1 (Z_to_bv 8 0)] ->
  AHEAP_P AH L RNG st LB m' /\ aheap_pres CI LB spz m m'.
Section Zd5.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 5).
Variable c : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 6).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 7).
Variable size : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 8).
Variable flag : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 9).
Variable W : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 10).
Variable spz : ltac2:(SecDietF.SzSecF.ty 'sf_core__stmt 11).
#[using="HL CI_OK"] Lemma sf_core__body : ltac:(let T := type of (fun (h : sf_core__stmt) => h L RNG st LB m m' c F size flag W spz) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (st, (LB, (m, (m', (c, (F, (size, (flag, (W, spz)))))))))))) as _.
  intros AHP EFLG SPZ MU WM HW FL1.
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  (pose proof (afake_lb L _ m c F size HFK ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR; nd_post).
  assert (NI : ~ In (FKB c F size) LB) by ((nd_pre BL 4%nat; intros _ _ _ ND; nd_post); inversion ND; assumption).
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE HDR LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 12%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). (pose proof G5 as ndP__; nd_pre ndP__ 3%nat; intros G5s G5i G5l; nd_post). (pose proof G7 as ndP__; nd_pre ndP__ 3%nat; intros G7s G7i G7l; nd_post).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  (nd_pre CE 8%nat; intros REAL DTVP DV DTV1 BD CF VERB T48; nd_post).
  rewrite <- EFLG in EF, FR. pose proof (fk_fsize_mod64 c ltac:(lia)) as SZ2. rewrite <- Hn in SZ2.
  unfold FAKESZ, KHIGH, AIMG_HI in *.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SB : shad (al_fake L) <= shad F /\ shad F + size / 8 <= shad (al_fake L) + 1446400 /\ shad F + size / 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. clear - G1 GL1 G3 FLO FHI F64 Npos SZ2 ATR. Z.div_mod_to_equations. lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (SHD : shad F + size / 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. clear - G2c G3 FLO FHI Npos ATR. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (DJ : forall A n, A + n <= ATOP -> (A + n <= flag \/ flag + 1 <= A) -> (A + n <= shad F \/ shad F + size / 8 <= A) -> disjoint_from W A n).
  { intros A n H1 H2 H3. apply disjoint_from_Forall. eapply Forall_impl; [| exact HW]. cbv beta. intros iv HQ. clear -HQ H1 H2 H3. lia. }
  assert (OUT : forall a, 0 <= a < 2^64 -> (a < ATOP \/ spz <= a) -> a <> flag -> ~ (shad F <= a < shad F + size / 8) -> m' (wa a) = m (wa a)).
  { intros a Ha H1 H2 H3. apply MU. rewrite wa_unsigned by lia. eapply outside_of_Forall; [exact HW|]. cbv beta. intros iv HQ. clear -HQ H1 H2 H3. lia. }
  assert (AT : m' (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m' flag _ FL1); clear -FR GL1; lia).
  (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF TCD TCT; nd_post).
  Local Ltac xdj H MU WM DJ K := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add]; K; lia].
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite SHL. eapply Forall_impl; [| exact HW]. cbv beta. intros iv HQ _.
    clear -HQ FR SB1 SB2. lia. }
  assert (HFK' : AFAKE L LB m').
  { split; [exact G|]. split.
    { tclr_int TCF. unfold afake_cells.
      split; [xdj REAL MU WM DJ ltac:(clear -GL1 FR SB1 SHS ATR)|].
      split; [xdj DTVP MU WM DJ ltac:(clear -KT GL1 G3 FR SB1 SB3 SHS ATR)|].
      split; [xdj DV MU WM DJ ltac:(clear -KT GL1 G3 FR SB1 SB3 SHS ATR)|].
      split; [xdj DTV1 MU WM DJ ltac:(clear -KT GL1 G3 FR SB1 SB3 SHS ATR)|].
      split; [xdj BD MU WM DJ ltac:(clear -G5s G6 G9 G3 GL1 FR SB1 SB3 SHS ATR)|].
      split; [xdj CF MU WM DJ ltac:(clear -GL1 FR SB1 SHS ATR)|].
      split; [xdj VERB MU WM DJ ltac:(clear -GL1 FR SB1 SHS ATR)|].
      eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split.
    { (nd_pre HDR 5%nat; intros h0 h1 h2 hs HS; nd_post). apply hdr_of_dc. eapply dc_at_any; [exact (dc_of_cells m _ _ HS)| exact WM| lia]. }
    split; [xdj LOG MU WM DJ ltac:(clear -G3 GL1 FR SHD ATR)|].
    split; [xdj NGC MU WM DJ ltac:(clear -G3 GL1 FR SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c2 pos' b Hc2 Hp2 Hb NZ.
      destruct (Z.eq_dec (fk_flag L c2 pos') flag) as [EQ|NE]; [exfalso; rewrite EQ, AT in Hb; congruence|].
      pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2.
      rewrite OUT in Hb by (clear -FRG2 NE G3 GL1 SHD ATR; lia).
      destruct (FL c2 pos' b Hc2 Hp2 Hb NZ) as [E|IN]; [|exact IN].
      exfalso. injection E as <- EF' _. apply NE. rewrite HF in EF'. apply fk_frame_inj in EF'; [|lia]. subst pos'. symmetry. exact EF.
    - intros c2 F' n' Hin. (nd_pre (LV c2 F' n' ltac:(right; exact Hin)) 6%nat; intros Hc2 Hn' pos' Hp2 HF' B1; nd_post).
      split; [exact Hc2|]. split; [exact Hn'|]. exists pos'. split; [exact Hp2|]. split; [exact HF'|].
      assert (NE : fk_flag L c2 pos' <> flag).
      { rewrite EF. apply (fk_flags_disjoint L c2 pos' c pos Hc2 Hp2 Hc Hp).
        intros E. injection E as -> ->. apply NI. rewrite HF, Hn, <- HF', <- Hn'. exact Hin. }
      pose proof (fk_flag_range L c2 pos' Hc2 Hp2) as FRG2. rewrite OUT by (clear -FRG2 NE G3 GL1 SHD ATR; lia). exact B1. }
  split.
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| eapply ablocks_tail; exact BL]|]. cbn [AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + size <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c2] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st _ m p A' n' AHP ltac:(right; exact Hb)) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. clear -Q2 Q3 Q4 D FLO FHI Npos G3 GL1 ATR. lia.
    - (pose proof (afake_lb L _ m c2 A' n' HFK ltac:(right; exact Hb)) as ndP__; nd_pre ndP__ 9%nat; intros Hc2 Hn' Np' _ X1 X2 X3 X4 _; nd_post).
      pose proof (afake_lb_disjoint L _ m c2 A' n' c F size HFK ltac:(right; exact Hb) ltac:(left; reflexivity) ltac:(intros E; apply NI; rewrite <- E; exact Hb)) as DJF.
      split; [exact X3|]. clear -X1 X2 X4 DJF. lia. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') -> 0 <= a' < 2^47 /\ ~ (F <= a' < F + size)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c2 & FA & fn & Hb & Hr)]];
      [ clear - X1 FC ATR; lia | pose proof (CI_OK iv Hiv) as CK; clear - Hr CK GL1 FLO; lia |].
    (nd_pre (BLK _ Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. unfold AIMG_HI in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  intros a Ha Hcl. split; [| intros W0; apply WM; exact W0].
  destruct Hcl as [Hcl|TL].
  2:{ (* [comment removed for export] *)
      (pose proof G12 as ndP__; nd_pre ndP__ 3%nat; intros TCF0 _ _; nd_post). unfold tclr in TCF0. pose proof atp_lin as TLN. pose proof atp_below_atop as TBA.
      destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
      4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
            rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_fake L ALO) as DAF. unfold adisj in DAF.
          apply OUT; clear - Ha IM OAH OAHI DAF GL1 G3 FR SB1 SB3 SHS ATR; lia. }
      3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
          apply OUT; clear - Ha IM G2t GL1 G3 FR SB1 SHS ATR; Z.div_mod_to_equations; lia. }
      - apply OUT; clear - Ha T TCF0 TLN TBA GL1 G3 FR SB1 SB3 SHS ATR; lia.
      - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
        assert (SATOP : shad ATOP <= 17594332446720) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -ATR; Z.div_mod_to_equations; lia).
        assert (TSA : shad ta + 1 <= shad F \/ shad F + size / 8 <= shad ta).
        { destruct (tls_shadow_apart ta F size Hta ltac:(clear -Npos; lia)) as [D|D].
          - destruct TCF0 as [D|D]; [right; split; [clear -D FHI; lia| clear -F64; Z.div_mod_to_equations; lia] | left; clear -D FLO; lia].
          - left; exact D.
          - right. unfold shlen in D. rewrite Z.shiftr_div_pow2 in D by lia. exact D. }
        pose proof G2 as G2t. unfold ablk, AIMG_HI, KLS in G2t.
        apply OUT; clear - Ha TS1 TS2 SATOP TSA G2t GL1 G3 FR ATR; lia. }
  destruct Hcl as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - apply OUT; clear - Ha Hs SPZ G3 FR SB3 ATR; lia.
  - pose proof (CI_OK iv Hiv) as CK. apply OUT; clear - Ha CK Hr GL1 FR SB1 SHS ATR; lia.
  - (nd_pre (BLK b Hb) 4%nat; intros Y1 Y2 Y3 Y4; nd_post). unfold ablk, AIMG_HI, KLS in Y1.
    apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr GL1 G3 FR SB1 SB3 SHS ATR; lia.
  - destruct (CLA a' Ha') as [A'R NA].
    assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SHA in Ha |- *. rewrite SHF in OUT.
    pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
    apply OUT; clear - Ha A'R NA F64 G2b G3 FR FLO FHI Npos SZ2 ATR; Z.div_mod_to_equations; lia.
Qed.
End Zd5.
#[using="HL CI_OK"] Lemma sf_core : ltac:(let t := eval cbv delta [sf_core__stmt] in sf_core__stmt in exact t).
Proof. exact sf_core__body. Qed.

(* [comment removed for export] *)
#[using="HL CI_OK"] Theorem fake_release_gen_P : forall L RNG st LB m m' cls F N spz,
  AHEAP_P AH L RNG st (FKB cls F N :: LB) m -> ATOP <= spz ->
  munch [(fflag L cls F, fflag L cls F + 1)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (fflag L cls F) [C1 (Z_to_bv 8 0)] ->
  AHEAP_P AH L RNG st LB m' /\ aheap_pres CI LB spz m m'.
Proof.
  intros L RNG st LB m m' cls F N spz AHP SPZ MU WM FL1.
  eapply (sf_core L RNG st LB m m' cls F N (fflag L cls F) _ spz AHP eq_refl SPZ MU WM); [| exact FL1].
  constructor; [right; left; cbn [fst snd]; split; reflexivity | constructor].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sf7_postP (req : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo F : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st LB m'
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 245) (Z.to_nat (req / 8)))].

Definition stack_free_7_P__stmt : Prop := forall (L : alayout) (RNG : footprint) (req : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo F : Z),
  AHEAP_P AH L RNG st (FKB 7 F 8192 :: LB) m ->
  a0 = Z_to_bv 64 F -> a1 = Z_to_bv 64 req -> 0 < req <= 8192 -> req mod 8 = 0 ->
  rw_cells asegs m (F + 8184) [C8 (Z_to_bv 64 (fflag L 7 F))] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_atls RNG -> afake_rng L RNG ->
  evtF asegs RNG (sf7_postP req L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo F m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKFREE7) fc None m (seg_rom asegs)).
Section Zd6.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 1).
Variable req : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 33).
Variable FR : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 36).
Variable st : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 37).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'stack_free_7_P__stmt 40).
Let flag := fflag L 7 F.
#[using="HL CI_OK flag"] Lemma stack_free_7_P__body : ltac:(let T := type of (fun (h : stack_free_7_P__stmt) => h L RNG req ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo F) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (req, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (FR, (fc, (m, (st, (LB, (lo, F))))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP A0 A1 REQ REQ8 SFP MI ST BOT LO SPT RSTK RIMG RTLS (RF & RSH & RD).
  (pose proof AHP as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post). cbn [AH ah_fake] in HFK.
  pose proof (AREP_poison_cells L st X m AR) as PC.
  (nd_pre (fake_flag_P L RNG st _ m 7 F 8192 AHP ltac:(left; reflexivity)) 5%nat; intros FLG RFLG FLB FLT _; nd_post).
  (pose proof (afake_lb L _ m 7 F 8192 HFK ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos F64 FLO FHI FK FC pos Hp HF EF FR0; nd_post).
  (pose proof HFK as ndP__; nd_pre ndP__ 8%nat; intros G _ _ _ _ _ DC2 _; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 _; nd_post).
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). pose proof atop_range as ATR.
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  chg (fflag L 7 F) flag.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHQ : shlen req = req / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SB : shad (al_fake L) <= shad F /\ shad F + 1024 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. clear - G1 GL1 G3 FLO FHI F64 ATR. Z.div_mod_to_equations. lia. }
  destruct SB as (SB1 & SB2).
  assert (SHD : shad F + 1024 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. clear - G2c G3 FLO FHI ATR. Z.div_mod_to_equations. lia. }
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) (shlen req) DC2 ltac:(lia) ltac:(rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia)
                ltac:(rewrite SHQ; clear -REQ SB2; Z.div_mod_to_equations; lia)) as DS2.
  destruct DS2 as [shj SHJ].
  assert (EFLAG : flag = fflag L 7 F) by reflexivity.
  clearbody flag.
  eapply evtF_mono.
  { eapply (stack_free7_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo flag F req (Z_to_bv 8 1) shj);
      try exact MI; try exact ST; try exact PC; try exact SFP; try exact FLG; try exact SHJ; try exact A0; try exact A1; try exact RIMG; try exact RTLS;
      try exact FK; try exact FLB; try exact RFLG; try exact REQ8;
      try (unfold SF7_STACK; clear -BOT LO FC FLT REQ ATR; lia).
    all: try (clear -F64; Z.div_mod_to_equations; lia).
    all: try (clear -FR0 FLO FHI; lia).
    all: try (rewrite SHQ; clear -FR0 SHD REQ; Z.div_mod_to_equations; lia).
    all: try (eapply rng_sub'; [exact RSTK| clear -BOT LO SPT; lia]).
    all: try (eapply rng_sub'; [exact RF| clear -FLO FHI; lia]).
    all: try (eapply rng_sub'; [exact RSH| rewrite SHQ; clear -SB1 SB2 REQ; Z.div_mod_to_equations; lia]). }
  cbv beta. intros ms' PO.
  (nd_pre PO 17%nat; intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU WM MI' ST' FLG0 SH'; nd_post).
  unfold sf7_W, SF7_STACK in MU.
  destruct (sf_core L RNG st LB m m' 7 F 8192 flag _ (bv_unsigned sp) AHP EFLAG ltac:(clear -BOT LO; lia) MU WM) as (AHP' & HPR); [| exact FLG0 |].
  { repeat (constructor; [cbn [fst snd] |]); [left; clear -BOT LO; lia | right; left; split; reflexivity | right; right; rewrite SHQ; clear -REQ; Z.div_mod_to_equations; lia | constructor]. }
  unfold sf7_postP. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  rewrite SHQ in SH'. exact SH'.
Qed.
End Zd6.
#[using="HL CI_OK"] Theorem stack_free_7_P : ltac:(let t := eval cbv delta [stack_free_7_P__stmt] in stack_free_7_P__stmt in exact t).
Proof. exact stack_free_7_P__body. Qed.

End S.
End CANSEC1.
End TwB.
