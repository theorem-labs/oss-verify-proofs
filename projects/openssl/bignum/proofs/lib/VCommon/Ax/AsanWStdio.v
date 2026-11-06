(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import
  PropExec CatSim CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg LibWritev LibWritevCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWWritev AsanWSw AsanWSwRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Lemma iov_bufs_len : forall segs mem ents bss,
  iov_bufs segs mem ents bss -> Z.of_nat (length (concat bss)) = iovs_total ents.
Proof.
  intros segs mem ents. induction ents as [|[bb n] r IH]; intros [|bs bss] H; cbn [iov_bufs] in H;
    try solve [reflexivity | destruct H].
  destruct H as [H1 H2]. cbn [concat iovs_total]. rewrite length_app, Nat2Z.inj_add, (IH bss H2).
  rewrite (rdn_length _ _ _ _ _ H1). unfold word_to_nat. rewrite Z2Nat.id by (pose proof (u64_range n); lia). reflexivity.
Qed.

Fixpoint bufs_disj (lo hi : Z) (ents : list (word * word)) : Prop :=
  match ents with
  | [] => True
  | (bb, n) :: r => (bv_unsigned bb + bv_unsigned n <= lo \/ hi <= bv_unsigned bb)%Z /\ bufs_disj lo hi r
  end.

Section L.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variables b sr : Z.
Variables (wj1 wj2 : Z) (ij1 ij2 : bv 21).
Hypothesis HC : SWCode segs b sr wj1 wj2 ij1 ij2.

Variable model : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (fd f iovp0 cnt0 tot0 : Z).
Hypothesis Hh : m_halted model = None.
Hypothesis Hrom0 : ms_rom ms0 = seg_rom segs.
Hypothesis Hsvc0 : ms_svc_pending ms0 = None.
Hypothesis Hfdm : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Hypothesis Hfdr : (0 < fd < 2 ^ 31)%Z.
Hypothesis Hs1 : rg ms0 9 = Z_to_bv 64 f.
Hypothesis Hfb : (0 <= f /\ f + 124 <= 2 ^ 47)%Z.
Hypothesis Hmfd : rdn segs (ms_mem ms0) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
Hypothesis Hnlfd : no_lazy model (f + 120) (f + 124).
Hypothesis Hcnt0 : (cnt0 = 1 \/ cnt0 = 2)%Z.
Hypothesis Hiov0 : (0 <= iovp0 /\ iovp0 + 16 * cnt0 <= TASK_SIZE)%Z.
Hypothesis Hsok0 : store_ok segs (ms_mem ms0) (Z_to_bv 64 iovp0) (Z.to_nat (16 * cnt0)) = true.
Hypothesis Hnliov : no_lazy model iovp0 (iovp0 + 16 * cnt0).
Hypothesis Hdfd : (f + 124 <= iovp0 \/ iovp0 + 16 * cnt0 <= f + 120)%Z.
Hypothesis Htot0 : (1 <= tot0 <= 2 ^ 30)%Z.
Hypothesis Hs6_0 : rg ms0 22 = Z_to_bv 64 tot0.
Hypothesis HK : forall ms', SWF ms0 ms' iovp0 (iovp0 + 16 * cnt0) -> ms_pc_val ms' = pcw b 0x94 ->
  rg ms' 10 = rg ms' 22 -> (1 <= bv_unsigned (rg ms' 10) <= tot0)%Z -> realizes_cfg segs cfg (mkCfg ms' model) K.

Let F_88 := F_88 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_90 := F_90 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_110 := F_110 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_118 := F_118 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_11c := F_11c segs b sr wj1 wj2 ij1 ij2 HC.
Let pcw_jal1 := pcw_jal1 segs b sr wj1 wj2 ij1 ij2 HC.
Let pcw_jal2 := pcw_jal2 segs b sr wj1 wj2 ij1 ij2 HC.
Let walk_sr := walk_sr segs cfg b sr wj1 wj2 ij1 ij2 HC model Hh.
Let rb_c0 := rb_c0 segs cfg b sr wj1 wj2 ij1 ij2 HC model.
Let rb_c1 := rb_c1 segs cfg b sr wj1 wj2 ij1 ij2 HC model.
Let Hbnd := Hbnd segs b sr wj1 wj2 ij1 ij2 HC.

Let LO := iovp0.
Let HI := (iovp0 + 16 * cnt0)%Z.

Record MI (S : machine_state) (iovp : Z) (ents : list (word * word)) (bss : list (list byte)) : Prop := {
  mi_swf : SWF ms0 S iovp0 (iovp0 + 16 * cnt0);
  mi_len : (1 <= length ents)%nat /\ (Z.of_nat (length ents) <= cnt0)%Z;
  mi_iovp : iovp = (iovp0 + 16 * (cnt0 - Z.of_nat (length ents)))%Z;
  mi_arr : iov_array segs (ms_mem S) (Z_to_bv 64 iovp) ents;
  mi_bufs : iov_bufs segs (ms_mem S) ents bss;
  mi_bok : iov_bufs_ok ents;
  mi_disj : bufs_disj iovp0 (iovp0 + 16 * cnt0) ents;
  mi_nl : iov_nl model ents;
  mi_tot : (1 <= iovs_total ents <= tot0)%Z
}.

Record LI (S : machine_state) (iovp : Z) (ents : list (word * word)) (bss : list (list byte)) : Prop := {
  li_mi : MI S iovp ents bss;
  li_pc : ms_pc_val S = pcw b 0x110;
  li_a7 : rg S 17 = Z_to_bv 64 66;
  li_a0 : rg S 10 = Z_to_bv 64 fd;
  li_a1 : rg S 11 = Z_to_bv 64 iovp;
  li_s4 : rg S 20 = Z_to_bv 64 iovp;
  li_a2 : rg S 12 = Z_to_bv 64 (Z.of_nat (length ents));
  li_s2 : rg S 18 = Z_to_bv 64 (Z.of_nat (length ents));
  li_s6 : rg S 22 = Z_to_bv 64 (iovs_total ents)
}.

Lemma SWF_fd : forall S, SWF ms0 S iovp0 (iovp0 + 16 * cnt0) ->
  rdn segs (ms_mem S) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
Proof.
  intros S Hs. rewrite <- Hmfd. pose proof Hiov0 as H0. unfold TASK_SIZE in H0.
  apply rdn_ext; [rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  intros x Hx. rewrite bvu_z in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  apply (swf_mem _ _ _ _ Hs). lia.
Qed.

Lemma SWF_s1 : forall S, SWF ms0 S iovp0 (iovp0 + 16 * cnt0) -> rg S 9 = Z_to_bv 64 f.
Proof. intros S Hs. rewrite (swf_regs _ _ _ _ Hs); [exact Hs1|]. cbn [In CLOB]. intuition discriminate. Qed.

Lemma SWF_sok : forall S (a : Z) n, SWF ms0 S iovp0 (iovp0 + 16 * cnt0) ->
  (iovp0 <= a)%Z -> (a + Z.of_nat n <= iovp0 + 16 * cnt0)%Z ->
  store_ok segs (ms_mem S) (Z_to_bv 64 a) n = true.
Proof.
  intros S a n Hs Ha Hn. pose proof Hiov0 as H0. unfold TASK_SIZE in H0.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (swf_grows _ _ _ _ Hs) | exact Hsok0] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Ltac zofn := rewrite ?length_N_to_le_bytes in *; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in *.
Ltac zofg := rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].

Lemma rb : forall S iovp ents bss (k : nat),
  MI S iovp ents bss -> ms_pc_val S = pcw b 0x120 ->
  rg S 10 = Z_to_bv 64 (Z.of_nat k) -> rg S 19 = Z_to_bv 64 iovp ->
  rg S 18 = Z_to_bv 64 (Z.of_nat (length ents)) -> rg S 22 = Z_to_bv 64 (iovs_total ents) ->
  (1 <= Z.of_nat k < iovs_total ents)%Z ->
  (forall S' iovp' ents' bss', LI S' iovp' ents' bss' ->
     iovs_total ents' = (iovs_total ents - Z.of_nat k)%Z ->
     concat bss' = skipn k (concat bss) ->
     realizes_cfg segs cfg (mkCfg S' model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss')) K)) ->
  realizes_cfg segs cfg (mkCfg S model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat bss))) K).
Proof.
  intros S iovp ents bss k [Hswf Hlen Hiovp Harr Hbufs Hbok Hdisj Hnl Htot] Hpc Ha0 Hs3 Hs2 Hs6 Hk HIH.
  pose proof Hiov0 as Hiov0'. unfold TASK_SIZE in Hiov0'.
  pose proof (swf_svc _ _ _ _ Hswf) as Hsvc.
  pose proof (SWF_fd S Hswf) as Rfd. pose proof (SWF_s1 S Hswf) as Hs1'.
  destruct ents as [|[b0 l0] [|[b1 l1] [|e2 r2]]]; cbn [length] in Hlen; try lia; zofn.
  -
    destruct bss as [|bs0 [|bs1 bss2]]; cbn [iov_bufs] in Hbufs; try tauto. destruct Hbufs as [B0 _].
    cbn [iov_array] in Harr. destruct Harr as (R0 & R8 & Hl63 & _). rewrite bvu_z in R8 by lia.
    cbn [iovs_total] in *. cbn [iov_bufs_ok] in Hbok. destruct Hbok as [Hb0 _].
    cbn [bufs_disj] in Hdisj. destruct Hdisj as [Hd0 _]. cbn [iov_nl] in Hnl. destruct Hnl as [Hn0 _].
    pose proof (u64_range b0). pose proof (u64_range l0). unfold TASK_SIZE in Hb0.
    pose proof (rdn_length _ _ _ _ _ B0) as Lb0. unfold word_to_nat in Lb0.
    cbn [concat]. rewrite app_nil_r.
    apply (rb_c0 S _ fd f iovp (Z.of_nat k) (bv_unsigned l0 + 0) 1 b0 l0).
    all: first [ assumption | lia | (eapply no_lazy_sub; [exact Hnliov | lia | lia])
               | (apply SWF_sok; [exact Hswf | lia | cbn; lia]) | (rewrite Hs6; f_equal; lia) | idtac ].
    + intros S' Hs' Hpc' H17 H10 H11 H20 H12 H18 H22 Hm'.
      assert (Hs'0 : SWF ms0 S' iovp0 (iovp0 + 16 * cnt0)) by (eapply SWF_trans; [exact Hswf | exact Hs' | lia | lia]).
      set (ents' := [(Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k), Z_to_bv 64 (bv_unsigned l0 - Z.of_nat k))]).
      set (bss' := [skipn k bs0]).
      assert (Hcc : concat bss' = skipn k bs0) by (cbn; apply app_nil_r).
      rewrite <- Hcc. apply (HIH S' iovp ents' bss').
      * constructor; [constructor | | | | | | | | ].
        -- exact Hs'0.
        -- unfold ents'. cbn [length]. lia.
        -- unfold ents'. cbn [length]. exact Hiovp.
        -- unfold ents'. cbn [iov_array]. rewrite Hm'. rewrite !bvu_z by lia.
           split; [rewrite rdn_w2m_outZ by (zofg; lia); apply rdn_w2m_hit8; lia|].
           split; [apply rdn_w2m_hit8; lia|]. split; [rewrite ?bvu_z by lia; lia | exact I].
        -- unfold ents', bss'. cbn [iov_bufs]. split; [|exact I].
           rewrite Hm'. rewrite !rdn_w2m_outW by (rewrite ?bvu_z, ?word_to_nat_Z, ?Z2Nat.id by lia; zofg; lia).
           rewrite word_to_nat_Z by lia.
           replace (Z.to_nat (bv_unsigned l0 - Z.of_nat k)) with (word_to_nat l0 - k)%nat by (unfold word_to_nat; lia).
           rewrite <- (rdn_skipn segs (ms_mem S) (word_to_nat l0) b0 bs0 k B0) by (unfold word_to_nat; lia).
           f_equal. unfold nat_to_word. rewrite w_add_z. reflexivity.
        -- unfold ents'. cbn [iov_bufs_ok]. split; [|exact I]. rewrite !bvu_z by lia. unfold TASK_SIZE. lia.
        -- unfold ents'. cbn [bufs_disj]. split; [|exact I]. rewrite !bvu_z by lia. lia.
        -- unfold ents'. cbn [iov_nl]. split; [|exact I]. rewrite !bvu_z by lia.
           eapply no_lazy_sub; [exact Hn0 | lia | lia].
        -- unfold ents'. cbn [iovs_total]. rewrite bvu_z by lia. lia.
        -- exact Hpc'.
        -- exact H17.
        -- exact H10.
        -- exact H11.
        -- exact H20.
        -- unfold ents'. exact H12.
        -- unfold ents'. exact H18.
        -- unfold ents'. cbn [iovs_total]. rewrite bvu_z by lia. rewrite H22. f_equal. lia.
      * unfold ents'. cbn [iovs_total]. rewrite bvu_z by lia. lia.
      * rewrite Hcc. cbn [concat]. rewrite app_nil_r. reflexivity.
  -
    destruct bss as [|bs0 [|bs1 [|bs2 bss3]]]; cbn [iov_bufs] in Hbufs; try tauto. destruct Hbufs as (B0 & B1 & _).
    cbn [iov_array] in Harr. destruct Harr as (R0 & R8 & Hl63 & R16 & R24 & Hl63' & _).
    rewrite (bvu_z iovp) in R8, R16, R24 by lia. rewrite (bvu_z (iovp + 16)) in R24 by lia.
    replace (iovp + 16 + 8)%Z with (iovp + 24)%Z in R24 by lia.
    cbn [iovs_total] in *. cbn [iov_bufs_ok] in Hbok. destruct Hbok as (Hb0 & Hb1 & _).
    cbn [bufs_disj] in Hdisj. destruct Hdisj as (Hd0 & Hd1 & _). cbn [iov_nl] in Hnl. destruct Hnl as (Hn0 & Hn1 & _).
    pose proof (u64_range b0). pose proof (u64_range l0). pose proof (u64_range b1). pose proof (u64_range l1).
    unfold TASK_SIZE in Hb0, Hb1.
    pose proof (rdn_length _ _ _ _ _ B0) as Lb0. unfold word_to_nat in Lb0.
    pose proof (rdn_length _ _ _ _ _ B1) as Lb1. unfold word_to_nat in Lb1.
    assert (Hc2 : cnt0 = 2%Z) by lia.
    cbn [concat]. rewrite app_nil_r.
    destruct (Z_le_gt_dec (Z.of_nat k) (bv_unsigned l0)) as [Hkl|Hkl].
    +
      rewrite skipn_app_l by lia.
      apply (rb_c0 S _ fd f iovp (Z.of_nat k) (bv_unsigned l0 + (bv_unsigned l1 + 0)) 2 b0 l0).
      all: first [ assumption | lia | (eapply no_lazy_sub; [exact Hnliov | lia | lia])
                 | (apply SWF_sok; [exact Hswf | lia | cbn; lia]) | (rewrite Hs6; f_equal; lia) | idtac ].
      intros S' Hs' Hpc' H17 H10 H11 H20 H12 H18 H22 Hm'.
      assert (Hs'0 : SWF ms0 S' iovp0 (iovp0 + 16 * cnt0)) by (eapply SWF_trans; [exact Hswf | exact Hs' | lia | lia]).
      set (ents' := [(Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k), Z_to_bv 64 (bv_unsigned l0 - Z.of_nat k)); (b1, l1)]).
      set (bss' := [skipn k bs0; bs1]).
      assert (Hcc : concat bss' = skipn k bs0 ++ bs1) by (cbn; rewrite app_nil_r; reflexivity).
      rewrite <- Hcc. apply (HIH S' iovp ents' bss').
      * constructor; [constructor | | | | | | | | ].
        -- exact Hs'0.
        -- unfold ents'. cbn [length]. lia.
        -- unfold ents'. cbn [length]. exact Hiovp.
        -- unfold ents'. cbn [iov_array]. rewrite Hm'. rewrite !bvu_z by lia.
           split; [rewrite rdn_w2m_outZ by (zofg; lia); apply rdn_w2m_hit8; lia|].
           split; [apply rdn_w2m_hit8; lia|]. split; [rewrite ?bvu_z by lia; lia|].
           rewrite ?bvu_z by lia.
           split; [rewrite !rdn_w2m_outZ by (zofg; lia); exact R16|].
           split; [rewrite !rdn_w2m_outZ by (zofg; lia); replace (iovp + 16 + 8)%Z with (iovp + 24)%Z by lia; exact R24|].
           split; [exact Hl63' | exact I].
        -- unfold ents', bss'. cbn [iov_bufs]. split; [|split; [|exact I]].
           ++ rewrite Hm'. rewrite !rdn_w2m_outW by (rewrite ?bvu_z, ?word_to_nat_Z, ?Z2Nat.id by lia; zofg; lia).
              rewrite word_to_nat_Z by lia.
              replace (Z.to_nat (bv_unsigned l0 - Z.of_nat k)) with (word_to_nat l0 - k)%nat by (unfold word_to_nat; lia).
              rewrite <- (rdn_skipn segs (ms_mem S) (word_to_nat l0) b0 bs0 k B0) by (unfold word_to_nat; lia).
              f_equal. unfold nat_to_word. rewrite w_add_z. reflexivity.
           ++ rewrite Hm'. rewrite !rdn_w2m_outW by (unfold word_to_nat; rewrite ?Z2Nat.id by lia; zofg; lia). exact B1.
        -- unfold ents'. cbn [iov_bufs_ok]. split; [|split; [|exact I]]; rewrite ?bvu_z by lia; unfold TASK_SIZE; lia.
        -- unfold ents'. cbn [bufs_disj]. split; [|split; [|exact I]]; rewrite ?bvu_z by lia; lia.
        -- unfold ents'. cbn [iov_nl]. split; [|split; [|exact I]]; [rewrite !bvu_z by lia | exact Hn1].
           eapply no_lazy_sub; [exact Hn0 | lia | lia].
        -- unfold ents'. cbn [iovs_total]. rewrite !bvu_z by lia. lia.
        -- exact Hpc'.
        -- exact H17.
        -- exact H10.
        -- exact H11.
        -- exact H20.
        -- unfold ents'. exact H12.
        -- unfold ents'. exact H18.
        -- unfold ents'. cbn [iovs_total]. rewrite !bvu_z by lia. rewrite H22. f_equal. lia.
      * unfold ents'. cbn [iovs_total]. rewrite !bvu_z by lia. lia.
      * rewrite Hcc. cbn [concat]. rewrite app_nil_r. rewrite skipn_app_l by lia. reflexivity.
    +
      rewrite skipn_app_r by lia.
      apply (rb_c1 S _ fd f iovp (Z.of_nat k) (bv_unsigned l0 + (bv_unsigned l1 + 0)) b0 l0 b1 l1).
      all: first [ assumption | lia | (eapply no_lazy_sub; [exact Hnliov | lia | lia])
                 | (apply SWF_sok; [exact Hswf | lia | cbn; lia]) | (rewrite Hs6; f_equal; lia) | idtac ].
      intros S' Hs' Hpc' H17 H10 H11 H20 H12 H18 H22 Hm'.
      assert (Hs'0 : SWF ms0 S' iovp0 (iovp0 + 16 * cnt0)) by (eapply SWF_trans; [exact Hswf | exact Hs' | lia | lia]).
      set (d := (Z.of_nat k - bv_unsigned l0)%Z).
      set (ents' := [(Z_to_bv 64 (bv_unsigned b1 + d), Z_to_bv 64 (bv_unsigned l1 - d))]).
      set (bss' := [skipn (k - length bs0) bs1]).
      assert (Hcc : concat bss' = skipn (k - length bs0) bs1) by (cbn; rewrite app_nil_r; reflexivity).
      rewrite <- Hcc. apply (HIH S' (iovp + 16)%Z ents' bss').
      * constructor; [constructor | | | | | | | | ].
        -- exact Hs'0.
        -- unfold ents'. cbn [length]. lia.
        -- unfold ents'. cbn [length]. lia.
        -- unfold ents'. cbn [iov_array]. rewrite Hm'. rewrite !bvu_z by lia.
           split; [rewrite rdn_w2m_outZ by (zofg; lia); apply rdn_w2m_hit8; lia|].
           split; [replace (iovp + 16 + 8)%Z with (iovp + 24)%Z by lia; apply rdn_w2m_hit8; lia|].
           split; [rewrite ?bvu_z by lia; lia | exact I].
        -- unfold ents', bss'. cbn [iov_bufs]. split; [|exact I].
           rewrite Hm'. rewrite !rdn_w2m_outW by (rewrite ?bvu_z, ?word_to_nat_Z, ?Z2Nat.id by lia; zofg; lia).
           rewrite word_to_nat_Z by lia.
           replace (Z.to_nat (bv_unsigned l1 - d)) with (word_to_nat l1 - (k - length bs0))%nat by (unfold d, word_to_nat; lia).
           rewrite <- (rdn_skipn segs (ms_mem S) (word_to_nat l1) b1 bs1 (k - length bs0) B1) by (unfold word_to_nat; lia).
           f_equal. unfold nat_to_word. rewrite w_add_z. f_equal. unfold d. lia.
        -- unfold ents'. cbn [iov_bufs_ok]. split; [|exact I]. rewrite !bvu_z by lia. unfold TASK_SIZE. lia.
        -- unfold ents'. cbn [bufs_disj]. split; [|exact I]. rewrite !bvu_z by lia. lia.
        -- unfold ents'. cbn [iov_nl]. split; [|exact I]. rewrite !bvu_z by lia.
           eapply no_lazy_sub; [exact Hn1 | lia | lia].
        -- unfold ents'. cbn [iovs_total]. rewrite bvu_z by lia. lia.
        -- exact Hpc'.
        -- exact H17.
        -- exact H10.
        -- exact H11.
        -- exact H20.
        -- unfold ents'. exact H12.
        -- unfold ents'. exact H18.
        -- unfold ents'. cbn [iovs_total]. rewrite bvu_z by lia. rewrite H22. f_equal. lia.
      * unfold ents'. cbn [iovs_total]. rewrite bvu_z by lia. lia.
      * rewrite Hcc. cbn [concat]. rewrite app_nil_r. rewrite skipn_app_r by lia. reflexivity.
Qed.

Lemma K_nil : K [].
Proof.
  pose proof Htot0.
  eapply realizes_cfg_nonempty.
  apply (HK (setx ms0 10 (rg ms0 22) (pcw b 0x94) (ms_resv ms0) (ms_mem ms0))).
  - eapply SWF_setx; [apply SWF_refl; exact Hsvc0 | inclob | reflexivity | reflexivity].
  - reflexivity.
  - rewrite rg_setx_same by reflexivity. rewrite rg_setx_other by discriminate. reflexivity.
  - rewrite rg_setx_same by reflexivity. rewrite Hs6_0. rewrite bvu_z by lia. lia.
Qed.

Lemma rzc_emit_nil : forall c, realizes_cfg segs cfg c K -> realizes_cfg segs cfg c (t_emit [] K).
Proof.
  intros c H. eapply rzc_conseq; [exact H|]. apply t_eq_sym. apply t_emit_nil_eq. exact K_nil.
Qed.

Lemma MI_regs : forall S S' iovp ents bss,
  MI S iovp ents bss -> SWF ms0 S' iovp0 (iovp0 + 16 * cnt0) -> ms_mem S' = ms_mem S -> MI S' iovp ents bss.
Proof.
  intros S S' iovp ents bss [H1 H2 H3 H4 H5 H6 H7 H8 H9] Hs Hm.
  constructor; try assumption; rewrite Hm; assumption.
Qed.

Lemma SWF_FR1 : forall S S' rs, SWF ms0 S iovp0 (iovp0 + 16 * cnt0) -> FR rs S S' -> (forall r, In r rs -> In r CLOB) ->
  SWF ms0 S' iovp0 (iovp0 + 16 * cnt0).
Proof. intros S S' rs H1 H2 H3. exact (FR_SWF ms0 S S' _ _ rs H1 H2 H3). Qed.

Lemma after_writev : forall (first : bool) S iovp ents bss (k : nat),
  MI S iovp ents bss ->
  ms_pc_val S = pcw b (if first then 0x88 else 0x110) ->
  rg S 17 = Z_to_bv 64 66 ->
  rg S 10 = Z_to_bv 64 fd ->
  rg S (if first then 19 else 20) = Z_to_bv 64 iovp ->
  rg S 18 = Z_to_bv 64 (Z.of_nat (length ents)) ->
  rg S 22 = Z_to_bv 64 (iovs_total ents) ->
  (1 <= k)%nat -> (Z.of_nat k <= iovs_total ents)%Z ->
  (forall S' iovp' ents' bss', LI S' iovp' ents' bss' ->
     iovs_total ents' = (iovs_total ents - Z.of_nat k)%Z ->
     concat bss' = skipn k (concat bss) ->
     realizes_cfg segs cfg (mkCfg S' model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss')) K)) ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 (latch S) (Z_to_bv 64 (Z.of_nat k)))) model)
    (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat bss))) K).
Proof.
  intros first S iovp ents bss k HMI Hpc H17 H10 Hs3 Hs2 Hs6 Hk1 Hk2 HIH.
  pose proof (mi_swf _ _ _ _ HMI) as Hswf. pose proof (swf_svc _ _ _ _ Hswf) as Hsvc.
  pose proof (mi_tot _ _ _ _ HMI) as Htot. pose proof Hbnd as HB.
  destruct first.
  all: rewrite adv_latch; rewrite Hpc; pcn.

  all: eapply rzc_acc; [ assumption | reflexivity | | apply acc_ok_nil | ].
  1: eapply wacc_Jal; [exact (swc_j1f _ _ _ _ _ _ _ HC) | exact (swc_j1e _ _ _ _ _ _ _ HC) | exact (swc_j1d _ _ _ _ _ _ _ HC)].
  2: eapply wacc_Jal; [exact (swc_j2f _ _ _ _ _ _ _ HC) | exact (swc_j2e _ _ _ _ _ _ _ HC) | exact (swc_j2d _ _ _ _ _ _ _ HC)].
  all: rewrite ?pc_setx, ?mem_setx, ?resv_setx.
  1: rewrite pcw_jal1, pcw_add; lits.
  2: rewrite pcw_jal2, pcw_add; lits.
  2: apply (walk_sr _ _ 0x118%Z (Z.of_nat k)).
  1: apply (walk_sr _ _ 0x90%Z (Z.of_nat k)).
  all: try reflexivity; try lia.
  all: try (rewrite rg_setx_other by discriminate; rewrite rg_setx_same by reflexivity; reflexivity).
  all: try (rewrite rg_setx_same by reflexivity; reflexivity).
  all: intros S2 HF2 Hpc2.
  all: destruct HF2 as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  all: assert (R10 : rg S2 10 = Z_to_bv 64 (Z.of_nat k))
        by (rewrite F7 by (cbn [In]; intuition discriminate); rgn; reflexivity).
  all: assert (R22 : rg S2 22 = Z_to_bv 64 (iovs_total ents))
        by (rewrite F7 by (cbn [In]; intuition discriminate); rgn; exact Hs6).
  all: assert (R18 : rg S2 18 = Z_to_bv 64 (Z.of_nat (length ents)))
        by (rewrite F7 by (cbn [In]; intuition discriminate); rgn; exact Hs2).
  all: assert (HS2 : SWF ms0 S2 iovp0 (iovp0 + 16 * cnt0))
        by (eapply SWF_FR1; [| exact (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 F7)))))) | cbn [In CLOB]; intros r [->|[]]; inclob];
            eapply SWF_setx; [eapply SWF_setx; [exact Hswf | inclob | reflexivity | reflexivity] | inclob | reflexivity | reflexivity]).
    +
      assert (R19 : rg S2 19 = Z_to_bv 64 iovp).
      { rewrite F7 by (cbn [In]; intuition discriminate). rgn. exact Hs3. }
      eapply rzc_acc; [ assumption | assumption | eapply wacc_Branch; [ fetch_tac F_90 | reflexivity | exact D_90 ] | apply acc_ok_nil | ].
      rewrite R10, R22, branch_ne_z by lia. rewrite Hpc2. pcn.
      destruct (Z.eqb_spec (Z.of_nat k) (iovs_total ents)) as [Eq|Ne]; cbn [negb]; pcn.
      *
        rewrite (proj1 (skipn_all_iff k (concat bss))).
        2:{ pose proof (iov_bufs_len _ _ _ _ (mi_bufs _ _ _ _ HMI)). lia. }
        cbn [map]. apply rzc_emit_nil. apply HK.
        -- eapply SWF_setx; [exact HS2 | inclob | reflexivity | reflexivity].
        -- reflexivity.
        -- rgn. rewrite R10, R22. f_equal. exact Eq.
        -- rgn. rewrite R10. rewrite bvu_z by lia. lia.
      *
        apply (rb _ iovp ents bss k).
        -- eapply MI_regs; [exact HMI | | rewrite !mem_setx, F6; reflexivity].
           eapply SWF_setx; [exact HS2 | inclob | reflexivity | reflexivity].
        -- reflexivity.
        -- rgn. exact R10.
        -- rgn. exact R19.
        -- rgn. exact R18.
        -- rgn. exact R22.
        -- lia.
        -- exact HIH.
    +
      assert (R20 : rg S2 20 = Z_to_bv 64 iovp).
      { rewrite F7 by (cbn [In]; intuition discriminate). rgn. exact Hs3. }
      wst wacc_OpImm F_118 D_118. rgn. rewrite R20. vnorm.
      eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Branch; [ fetch_tac F_11c | reflexivity | exact D_11c ] | apply acc_ok_nil | ].
      rgn. rewrite R10, R22, branch_eq_z by lia. pcn.
      destruct (Z.eqb_spec (Z.of_nat k) (iovs_total ents)) as [Eq|Ne]; pcn.
      *
        rewrite (proj1 (skipn_all_iff k (concat bss))).
        2:{ pose proof (iov_bufs_len _ _ _ _ (mi_bufs _ _ _ _ HMI)). lia. }
        cbn [map]. apply rzc_emit_nil. apply HK.
        -- eapply SWF_setx; [eapply SWF_setx; [exact HS2 | inclob | reflexivity | reflexivity] | inclob | reflexivity | reflexivity].
        -- reflexivity.
        -- rgn. rewrite R10, R22. f_equal. exact Eq.
        -- rgn. rewrite R10. rewrite bvu_z by lia. lia.
      *
        apply (rb _ iovp ents bss k).
        -- eapply MI_regs; [exact HMI | | rewrite !mem_setx, F6; reflexivity].
           eapply SWF_setx; [eapply SWF_setx; [exact HS2 | inclob | reflexivity | reflexivity] | inclob | reflexivity | reflexivity].
        -- reflexivity.
        -- rgn. exact R10.
        -- rgn. reflexivity.
        -- rgn. exact R18.
        -- rgn. exact R22.
        -- lia.
        -- exact HIH.
Qed.

Lemma loop : forall n S iovp ents bss, LI S iovp ents bss -> (iovs_total ents <= Z.of_nat n)%Z ->
  realizes_cfg segs cfg (mkCfg S model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss)) K).
Proof.
  induction n as [|n IH]; intros S iovp ents bss HLI Hn.
  { pose proof (mi_tot _ _ _ _ (li_mi _ _ _ _ HLI)). lia. }
  destruct HLI as [HMI Hpc H17 H10 H11 H20 H12 H18 H22].
  pose proof (mi_swf _ _ _ _ HMI) as Hswf. pose proof (mi_tot _ _ _ _ HMI) as Htot.
  pose proof (mi_len _ _ _ _ HMI) as Hlen. pose proof (mi_iovp _ _ _ _ HMI) as Hiovp.
  pose proof Hiov0 as Hiov0'. unfold TASK_SIZE in Hiov0'.
  eapply rzc_acc; [exact Hh | exact (swf_svc _ _ _ _ Hswf) | eapply wacc_Ecall; [rewrite Hpc; exact F_110 | exact E_88]
                  | apply acc_ok_nil | ].
  eapply (rzc_writev_wall_nl segs cfg (latch S) (rg S 17) model fd (Z_to_bv 64 iovp) ents bss K).
  - cbn [latch ms_rom]. rewrite (swf_rom _ _ _ _ Hswf). exact Hrom0.
  - exact Hh.
  - reflexivity.
  - exact Hfdm.
  - exact Hfdr.
  - rewrite H17. apply bvu_z. lia.
  - rewrite gpr_latch0. exact H10.
  - rewrite gpr_latch1. exact H11.
  - rewrite gpr_latch2. exact H12.
  - lia.
  - rewrite bvu_z by lia. unfold TASK_SIZE. lia.
  - exact (mi_arr _ _ _ _ HMI).
  - exact (mi_bok _ _ _ _ HMI).
  - exact (mi_bufs _ _ _ _ HMI).
  - lia.
  - lia.
  - rewrite bvu_z by lia. eapply no_lazy_sub; [exact Hnliov | lia | lia].
  - exact (mi_nl _ _ _ _ HMI).
  - exact K_nil.
  - intros k Hk1 Hk2.
    pose proof (iov_bufs_len _ _ _ _ (mi_bufs _ _ _ _ HMI)) as Hbl.
    apply (after_writev false S iovp ents bss k HMI Hpc H17 H10 H20 H18 H22 Hk1 ltac:(lia)).
    intros S' iovp' ents' bss' HLI' Htot' Hcc.
    apply (IH S' iovp' ents' bss' HLI'). lia.
Qed.

Theorem from_first_ecall : forall ents0 bss0,
  MI ms0 iovp0 ents0 bss0 ->
  ms_pc_val ms0 = pcw b 0x88 ->
  rg ms0 17 = Z_to_bv 64 66 -> rg ms0 10 = Z_to_bv 64 fd -> rg ms0 11 = Z_to_bv 64 iovp0 ->
  rg ms0 19 = Z_to_bv 64 iovp0 ->
  rg ms0 12 = Z_to_bv 64 (Z.of_nat (length ents0)) -> rg ms0 18 = Z_to_bv 64 (Z.of_nat (length ents0)) ->
  iovs_total ents0 = tot0 ->
  realizes_cfg segs cfg (mkCfg ms0 model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss0)) K).
Proof.
  intros ents0 bss0 HMI Hpc H17 H10 H11 H19 H12 H18 Htot.
  pose proof (mi_swf _ _ _ _ HMI) as Hswf. pose proof (mi_tot _ _ _ _ HMI) as Htot'.
  pose proof (mi_len _ _ _ _ HMI) as Hlen. pose proof (mi_iovp _ _ _ _ HMI) as Hiovp.
  pose proof Hiov0 as Hiov0'. unfold TASK_SIZE in Hiov0'.
  eapply rzc_acc; [exact Hh | exact Hsvc0 | eapply wacc_Ecall; [rewrite Hpc; exact F_88 | exact E_88]
                  | apply acc_ok_nil | ].
  eapply (rzc_writev_wall_nl segs cfg (latch ms0) (rg ms0 17) model fd (Z_to_bv 64 iovp0) ents0 bss0 K).
  - exact Hrom0.
  - exact Hh.
  - reflexivity.
  - exact Hfdm.
  - exact Hfdr.
  - rewrite H17. apply bvu_z. lia.
  - rewrite gpr_latch0. exact H10.
  - rewrite gpr_latch1. exact H11.
  - rewrite gpr_latch2. exact H12.
  - lia.
  - rewrite bvu_z by lia. unfold TASK_SIZE. lia.
  - exact (mi_arr _ _ _ _ HMI).
  - exact (mi_bok _ _ _ _ HMI).
  - exact (mi_bufs _ _ _ _ HMI).
  - lia.
  - lia.
  - rewrite bvu_z by lia. eapply no_lazy_sub; [exact Hnliov | lia | lia].
  - exact (mi_nl _ _ _ _ HMI).
  - exact K_nil.
  - intros k Hk1 Hk2.
    pose proof (iov_bufs_len _ _ _ _ (mi_bufs _ _ _ _ HMI)) as Hbl.
    apply (after_writev true ms0 iovp0 ents0 bss0 k HMI Hpc H17 H10 H19 H18 ltac:(rewrite Hs6_0, Htot; reflexivity)
             Hk1 ltac:(lia)).
    intros S' iovp' ents' bss' HLI' Htot'' Hcc.
    apply (loop (Z.to_nat (iovs_total ents')) S' iovp' ents' bss' HLI'). lia.
Qed.

End L.

Theorem stdio_write_loop :
  forall (segs : list Segment) (cfg : SpuriousCfg) (b sr wj1 wj2 : Z) (ij1 ij2 : bv 21),
  SWCode segs b sr wj1 wj2 ij1 ij2 ->
  forall (ms : machine_state) (model : Model) (K : TSet) (fd f iovp : Z)
         (ents : list (word * word)) (bss : list (list byte)),
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs -> ms_pc_val ms = pcw b 0x88 ->
  m_halted model = None ->
  rg ms 17 = Z_to_bv 64 66 -> rg ms 10 = Z_to_bv 64 fd ->
  rg ms 11 = Z_to_bv 64 iovp -> rg ms 19 = Z_to_bv 64 iovp ->
  rg ms 12 = Z_to_bv 64 (Z.of_nat (length ents)) -> rg ms 18 = Z_to_bv 64 (Z.of_nat (length ents)) ->
  rg ms 22 = Z_to_bv 64 (iovs_total ents) -> rg ms 9 = Z_to_bv 64 f ->
  (length ents = 1 \/ length ents = 2)%nat -> (1 <= iovs_total ents <= 2 ^ 30)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) -> (0 < fd < 2 ^ 31)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 <= f)%Z -> (f + 124 <= 2 ^ 47)%Z ->
  (0 <= iovp)%Z -> (iovp + 16 * Z.of_nat (length ents) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) (Z_to_bv 64 iovp) ents ->
  iov_bufs segs (ms_mem ms) ents bss ->
  iov_bufs_ok ents ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 iovp) (16 * length ents) = true ->
  (f + 124 <= iovp \/ iovp + 16 * Z.of_nat (length ents) <= f + 120)%Z ->
  bufs_disj iovp (iovp + 16 * Z.of_nat (length ents)) ents ->
  no_lazy model iovp (iovp + 16 * Z.of_nat (length ents)) ->
  no_lazy model (f + 120) (f + 124) ->
  iov_nl model ents ->
  (forall ms', SWF ms ms' iovp (iovp + 16 * Z.of_nat (length ents)) -> ms_pc_val ms' = pcw b 0x94 ->
     rg ms' 10 = rg ms' 22 -> (1 <= bv_unsigned (rg ms' 10) <= iovs_total ents)%Z ->
     realizes_cfg segs cfg (mkCfg ms' model) K) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss)) K).
Proof.
  intros segs cfg b sr wj1 wj2 ij1 ij2 HC ms model K fd f iovp ents bss
         Hsvc Hrom Hpc Hh H17 H10 H11 H19 H12 H18 H22 H9 Hlen Htot Hfdm Hfdr Hmfd Hf0 Hf1 Hi0 Hi1
         Harr Hbufs Hbok Hsok Hdfd Hdisj Hnla Hnlf Hnlb HK.
  pose proof (u64_range (Z_to_bv 64 0)).
  apply (from_first_ecall segs cfg b sr wj1 wj2 ij1 ij2 HC model K ms fd f iovp (Z.of_nat (length ents))
           (iovs_total ents)) with (ents0 := ents) (bss0 := bss); try assumption.
  - split; assumption.
  - lia.
  - split; assumption.
  - rewrite Z2Nat.inj_mul, Nat2Z.id by lia. exact Hsok.
  - constructor.
    + apply SWF_refl. exact Hsvc.
    + lia.
    + lia.
    + exact Harr.
    + exact Hbufs.
    + exact Hbok.
    + exact Hdisj.
    + exact Hnlb.
    + lia.
  - reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
