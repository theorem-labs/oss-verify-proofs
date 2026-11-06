(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA HeapIfaceANull.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CRC.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Lemma outside_dec : forall (W : list L5.range) a, L5.outside W a \/ exists w, In w W /\ L5.in_rng w a.
Proof.
  induction W as [|w W IH]; intros a; [left; intros r []|].
  destruct (IH a) as [O|(w' & Hin & Hr)]; [|right; exists w'; split; [right; exact Hin | exact Hr]].
  destruct (Z_le_dec (fst w) a) as [H1|H1]; [destruct (Z_lt_dec a (fst w + snd w)) as [H2|H2]|].
  - right. exists w. split; [left; reflexivity | split; assumption].
  - left. intros r [<-|Hr]; [intros [_ X]; exact (H2 X) | exact (O r Hr)].
  - left. intros r [<-|Hr]; [intros [X _]; exact (H1 X) | exact (O r Hr)].
Qed.

Section Rt.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Variable FPI : FPState -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_ok_of_ra : forall (R : bvmap 5 word) r, getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> Hoare.ret_ok (getr R 1%bv).
Proof. intros R r Hra [R1 R2]. rewrite Hra. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact R2. Qed.

Lemma astk_sp : forall (M : mem) sp scr, 0 <= scr -> CHA.astk ar M sp scr -> 0x7fff7f800000 + 4096 <= sp <= 2 ^ 47.
Proof. intros M sp scr Hs (K1 & K2 & K3 & K4 & _). lia. Qed.

Lemma astack_ok_of_astk : forall (M : mem) sp scr scr0, 0 <= scr0 <= scr -> CHA.astk ar M sp scr -> astack_ok L ar M scr0 sp.
Proof.
  intros M sp scr scr0 Hs (K1 & K2 & K3 & K4 & K5 & K6). split; [exact K1|]. split; [lia|]. split; [lia|]. split; [exact K4|]. split; [|exact K6].
  intros dd m Hdd Hm.
  assert (D0 : L5.defined M (sp - scr0) scr0) by (intros i Hi; replace (sp - scr0 + i) with (sp - scr + (scr - scr0 + i)) by lia; apply K5; lia).
  exact (L5C.writable_of_defined (hl_segs L) M _ _ D0 ltac:(lia) ltac:(lia) dd m Hdd Hm).
Qed.

(* [comment removed for export] *)
Lemma ahpres_scr : forall LB FF sp scr0 scr (Wc : list L5.range) (M M' : mem),
  0 <= scr0 <= scr -> CHA.astk ar M sp scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr0 a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, sp - scr0 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
  (forall w a, In w Wc -> L5.in_rng w a -> M' (Z_to_bv 64 a) <> None) ->
  CHA.ahpres L ar LB FF sp scr Wc M M'.
Proof.
  intros LB FF sp scr0 scr Wc M M' Hs Hstk Hk Hd Hw. pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (SUB : forall a, aclient L ar LB FF sp scr a -> aclient L ar LB FF sp scr0 a).
  { intros a Hc. eapply CHA.aclient_scr; [exact Hc|]. intros x Hx. lia. }
  split; [|split].
  - intros a (Ha & Hc & Ho). exact (Hk a Ha (SUB a Hc) Ho).
  - intros i Hi. destruct (Z_le_dec (sp - scr0) (sp - scr + i)) as [G|G]; [apply Hd; lia|].
    destruct (outside_dec Wc (sp - scr + i)) as [O|(w & Hin & Hr)]; [|exact (Hw w _ Hin Hr)].
    rewrite (Hk (sp - scr + i) ltac:(lia)); [apply K5; exact Hi | | exact O].
    right; left. split; lia.
  - intros a Ha Hc Hdf. destruct (outside_dec Wc a) as [O|(w & Hin & Hr)]; [|exact (Hw w _ Hin Hr)].
    rewrite (Hk a Ha (SUB a Hc) O). exact Hdf.
Qed.

(* [comment removed for export] *)
Lemma ahpres_mono : forall LB FF sp scr0 scr (Wc : list L5.range) (M M' : mem),
  0 <= scr0 <= scr -> CHA.astk ar M sp scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr0 a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, sp - scr0 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
  (forall a : word, M a <> None -> M' a <> None) ->
  CHA.ahpres L ar LB FF sp scr Wc M M'.
Proof.
  intros LB FF sp scr0 scr Wc M M' Hs Hstk Hk Hd Hmono. pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (SUB : forall a, aclient L ar LB FF sp scr a -> aclient L ar LB FF sp scr0 a).
  { intros a Hc. eapply CHA.aclient_scr; [exact Hc|]. intros x Hx. lia. }
  split; [|split].
  - intros a (Ha & Hc & Ho). exact (Hk a Ha (SUB a Hc) Ho).
  - intros i Hi. destruct (Z_le_dec (sp - scr0) (sp - scr + i)) as [G|G]; [apply Hd; lia|]. apply Hmono. apply K5. exact Hi.
  - intros a Ha Hc Hdf. apply Hmono. exact Hdf.
Qed.

Lemma amodel_rt : forall A A' model model', CHA.amodel_ok A model -> model_rt model model' -> MInv A' model' -> CHA.amodel_ok A' model'.
Proof. intros A A' model model' [H1 _] Hrt HMI. split; [rewrite (L5LZ.model_rt_halted _ _ Hrt); exact H1 | exact HMI]. Qed.

Lemma usp : forall (R : bvmap 5 word) (M : mem) sp scr, 0 <= scr -> getr R 2%bv = Z_to_bv 64 sp -> CHA.astk ar M sp scr -> bv_unsigned (getr R 2%bv) = sp.
Proof. intros R M sp scr Hs Hsp Hstk. pose proof (astk_sp M sp scr Hs Hstk). rewrite Hsp. apply u64_of_Z. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma malloc_cps : forall scr LB FF LK cr A n sp r, 0 <= hl_scr_malloc L <= scr ->
  CBA.cps_asanG L ar HI FPI (hl_malloc L) r sp scr LB FF LK cr A 0
    (fun R M => getr R 10%bv = Z_to_bv 64 n /\ 0 < n <= 2 ^ 27 /\ acredit_ok L cr n)
    (fun R M R' M' LB' cr' LBk W => exists u, getr R' 10%bv = Z_to_bv 64 u /\ ablock_range L ar u n /\ blocks_apart u n LB /\ fframes_apart u n (FF ++ LK)
        /\ L5.defined M' u n /\ shadow_blk M' u n /\ LB' = (u, n) :: LB /\ cr' = adebit L cr n /\ LBk = LB /\ W = []).
Proof.
  intros scr LB FF LK cr A n sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Ha0 & Hn & Hcr) CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (PmHeapIfaceA.aio_malloc _ _ _ _ _ HIok fx R M model LB FF LK cr A n K HH (proj1 Hmo) (proj2 Hmo) Ha0 Hn Hcr Htp (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk M sp scr _ Hscr Hstk).
  - exact HK.
  - intros R' M' model' A' u Ha0' HRP Hrng Hbap Hfap Hdef Hsh Hpres Hrt HA' HMI' HH'. rewrite Hra. rewrite USP in Hpres. destruct Hpres as [P1 P2].
    apply (CONT fx R' M' model' ((u, n) :: LB) (adebit L cr n) LB [] LK A' HFP); [| exact HRP | | exact Hrt | exact HA' | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + exists u. split; [exact Ha0'|]. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split; [exact Hdef|]. split; [exact Hsh|]. repeat split; reflexivity.
    + apply (ahpres_scr LB FF sp (hl_scr_malloc L) scr [] M M' Hscr Hstk); [intros a Ha Hc _; exact (P1 a Ha Hc) | exact P2 | intros w a []].
Qed.

Lemma free_cps : forall scr LB FF LK cr A u n sp r, 0 <= hl_scr_free L <= scr ->
  CBA.cps_asanG L ar HI FPI (hl_free L) r sp scr LB FF LK cr A 0
    (fun R M => getr R 10%bv = Z_to_bv 64 u /\ In (u, n) LB)
    (fun R M R' M' LB' cr' LBk W => LB' = lb_remove u LB /\ cr' = cr /\ LBk = lb_remove u LB /\ W = []).
Proof.
  intros scr LB FF LK cr A u n sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Ha0 & Hin) CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (PmHeapIfaceA.aio_free _ _ _ _ _ HIok fx R M model LB FF LK cr A u n K HH (proj1 Hmo) (proj2 Hmo) Hin Ha0 Htp (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk M sp scr _ Hscr Hstk).
  - exact HK.
  - intros R' M' model' A' HRP Hpres Hrt HA' HMI' HH'. rewrite Hra. rewrite USP in Hpres. destruct Hpres as [P1 P2].
    apply (CONT fx R' M' model' (lb_remove u LB) cr (lb_remove u LB) [] LK A' HFP); [| exact HRP | | exact Hrt | exact HA' | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + repeat split; reflexivity.
    + apply (ahpres_scr (lb_remove u LB) FF sp (hl_scr_free L) scr [] M M' Hscr Hstk); [intros a Ha Hc _; exact (P1 a Ha Hc) | exact P2 | intros w a []].
Qed.

(* [comment removed for export] *)
Lemma free_null_cps : HeapIfaceANull.afree_null_spec L ar SCFG HI -> forall scr LB FF LK cr A sp r, 0 <= hl_scr_free L <= scr ->
  CBA.cps_asanG L ar HI FPI (hl_free L) r sp scr LB FF LK cr A 0
    (fun R M => getr R 10%bv = Z_to_bv 64 0)
    (fun R M R' M' LB' cr' LBk W => LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).
Proof.
  intros FN scr LB FF LK cr A sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ Ha0 CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (FN fx R M model LB FF LK cr A K HH (proj1 Hmo) (proj2 Hmo) Ha0 Htp (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk M sp scr _ Hscr Hstk).
  - exact HK.
  - intros R' M' model' A' HRP Hpres Hrt HA' HMI' HH'. rewrite Hra. rewrite USP in Hpres. destruct Hpres as [P1 P2].
    apply (CONT fx R' M' model' LB cr LB [] LK A' HFP); [| exact HRP | | exact Hrt | exact HA' | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + repeat split; reflexivity.
    + apply (ahpres_scr LB FF sp (hl_scr_free L) scr [] M M' Hscr Hstk); [intros a Ha Hc _; exact (P1 a Ha Hc) | exact P2 | intros w a []].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mem_dst (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (M : mem) (dst n : Z) : Prop :=
  0 <= n <= 2 ^ 27 /\ aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF sp scr (dst + i)) /\ L5.writable (hl_segs L) M dst n /\ app_rng ar dst n.
Definition mem_src (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (M : mem) (src n : Z) (bs : list byte) : Prop :=
  aacc M src n /\ (0 <= src /\ src + n <= 2 ^ 47) /\ app_rng ar src n /\
  (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF sp scr (src + i)) /\
  rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs.

Lemma aclientw_scr0 : forall LB FF sp scr0 scr a, 0 <= scr0 <= scr -> aclientw L ar LB FF sp scr a -> aclientw L ar LB FF sp scr0 a.
Proof. intros LB FF sp scr0 scr a Hs Hc. eapply CHA.aclient_scr; [exact Hc|]. intros x Hx. lia. Qed.
Lemma aclient_scr0 : forall LB FF sp scr0 scr a, 0 <= scr0 <= scr -> aclient L ar LB FF sp scr a -> aclient L ar LB FF sp scr0 a.
Proof. intros LB FF sp scr0 scr a Hs Hc. eapply CHA.aclient_scr; [exact Hc|]. intros x Hx. lia. Qed.

Lemma amem_pre_of : forall scr fx (R : bvmap 5 word) (M : mem) model LB FF LK cr A dst n sp r K,
  0 <= hl_scr_mem L <= scr ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> CHA.astk ar M sp scr ->
  getr R 10%bv = Z_to_bv 64 dst -> getr R 12%bv = Z_to_bv 64 n -> mem_dst LB FF sp scr M dst n ->
  amem_pre L ar HI fx R M model LB FF LK cr A dst n K.
Proof.
  intros scr fx R M model LB FF LK cr A dst n sp r K Hscr HH Hmo HK Hra Hraok Hsp Htp Hstk Ha0 Ha2 (D1 & D2 & D3 & D4 & D5).
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP. unfold amem_pre. rewrite USP.
  split; [exact HH|]. split; [exact (proj1 Hmo)|]. split; [exact (proj2 Hmo)|]. split; [exact Ha0|]. split; [exact Ha2|]. split; [exact D1|]. split; [exact Htp|].
  split; [exact (ret_ok_of_ra R r Hra Hraok)|]. split; [exact (astack_ok_of_astk M sp scr _ Hscr Hstk)|]. split; [exact D2|].
  split; [intros i Hi; exact (aclientw_scr0 _ _ _ _ _ _ Hscr (D3 i Hi))|]. split; [exact D4|]. split; [exact HK | exact D5].
Qed.

(* [comment removed for export] *)
Lemma amem_post_of : forall scr fx (R : bvmap 5 word) (M : mem) model LB FF LK cr A dst n sp r K (NEWB : Z -> Z -> Prop),
  0 <= hl_scr_mem L <= scr -> CHA.amodel_ok A model -> FPI fx ->
  getr R 1%bv = Z_to_bv 64 r -> getr R 2%bv = Z_to_bv 64 sp -> CHA.astk ar M sp scr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) (LK' : list fframe) (A' : list (Z * Z)),
        FPI fx' -> (getr R' 10%bv = Z_to_bv 64 dst /\ (forall i, 0 <= i < n -> exists v, NEWB i v /\ byte_at M' (dst + i) v) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(dst, n)]) ->
        regs_preserved R R' -> CHA.ahpres L ar LBk FF sp scr W M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom (hl_segs L))) model') K) ->
  amem_post L ar SCFG HI fx R M model LB FF LK cr A dst n NEWB K.
Proof.
  intros scr fx R M model LB FF LK cr A dst n sp r K NEWB Hscr Hmo HFP Hra Hsp Hstk CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP. unfold amem_post. rewrite USP.
  intros R' M' model' Ha0' HRP Hnew Hkeep Hdef Hrt HMI' HH'. rewrite Hra.
  apply (CONT fx R' M' model' LB cr LB [(dst, n)] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
  - repeat split; try reflexivity; assumption.
  - apply (ahpres_scr LB FF sp (hl_scr_mem L) scr [(dst, n)] M M' Hscr Hstk).
    + intros a Ha Hc Ho. apply (Hkeep a Ha Hc). intros Hin. apply (Ho (dst, n)); [left; reflexivity | exact Hin].
    + exact Hdef.
    + intros w a [<-|[]] [X1 X2]. cbn [fst snd] in X1, X2. destruct (Hnew (a - dst) ltac:(lia)) as (v & _ & Hv). unfold byte_at in Hv.
      replace (dst + (a - dst)) with a in Hv by lia. rewrite Hv. discriminate.
Qed.

(* [comment removed for export] *)
Definition memcpy_pre (LB : list (Z * Z)) (FF : list fframe) (sp scr dst src n : Z) (bs : list byte) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 11%bv = Z_to_bv 64 src /\ getr R 12%bv = Z_to_bv 64 n /\
  mem_dst LB FF sp scr M dst n /\ mem_src LB FF sp scr M src n bs /\ (dst + n <= src \/ src + n <= dst).
Definition memcpy_post (LB : list (Z * Z)) (cr : credit) (dst n : Z) (bs : list byte)
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  getr R' 10%bv = Z_to_bv 64 dst /\ (forall i, 0 <= i < n -> exists v, (nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M' (dst + i) v)
  /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(dst, n)].

Lemma memcpy_cps : forall pc, amemcpy_spec_at L ar SCFG HI pc false ->
  forall scr LB FF LK cr A dst src n bs sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A 0 (memcpy_pre LB FF sp scr dst src n bs) (memcpy_post LB cr dst n bs).
Proof.
  intros pc SPEC scr LB FF LK cr A dst src n bs sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Ha0 & Ha1 & Ha2 & HD & (S1 & S2 & S3 & S4 & S5) & Hov) CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (SPEC fx R M model LB FF LK cr A dst src n bs K (amem_pre_of scr fx R M model LB FF LK cr A dst n sp r K Hscr HH Hmo HK Hra Hraok Hsp Htp Hstk Ha0 Ha2 HD) Ha1 S1 S2 S3).
  - rewrite USP. intros i Hi. destruct (S4 i Hi) as [X|X]; [left; exact X | right; exact (aclient_scr0 _ _ _ _ _ _ Hscr X)].
  - exact S5.
  - intros _. exact Hov.
  - apply (amem_post_of scr fx R M model LB FF LK cr A dst n sp r K _ Hscr Hmo HFP Hra Hsp Hstk). exact CONT.
Qed.
Lemma asan_memcpy_cps : forall scr LB FF LK cr A dst src n bs sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI (hl_asan_memcpy L) r sp scr LB FF LK cr A 0 (memcpy_pre LB FF sp scr dst src n bs) (memcpy_post LB cr dst n bs).
Proof. exact (memcpy_cps _ (PmHeapIfaceA.aio_memcpy _ _ _ _ _ HIok)). Qed.
Lemma asan_memmove_cps : forall scr LB FF LK cr A dst src n bs sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI (hl_asan_memmove L) r sp scr LB FF LK cr A 0 (memcpy_pre LB FF sp scr dst src n bs) (memcpy_post LB cr dst n bs).
Proof. exact (memcpy_cps _ (PmHeapIfaceA.aio_memmove _ _ _ _ _ HIok)). Qed.

Definition memset_pre (LB : list (Z * Z)) (FF : list fframe) (sp scr dst c n : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 11%bv = Z_to_bv 64 c /\ getr R 12%bv = Z_to_bv 64 n /\ mem_dst LB FF sp scr M dst n.
Definition memset_post (LB : list (Z * Z)) (cr : credit) (dst c n : Z)
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  getr R' 10%bv = Z_to_bv 64 dst /\ (forall i, 0 <= i < n -> exists v, v = c mod 256 /\ byte_at M' (dst + i) v) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(dst, n)].
(* [comment removed for export] *)
Definition amemset_spec_at (pc : Z) : Prop :=
  forall fx R M model LB FF LK cr A dst c n K,
    amem_pre L ar HI fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post L ar SCFG HI fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) model) K.
Lemma amemset_at_iface : amemset_spec_at (hl_asan_memset L).
Proof. exact (PmHeapIfaceA.aio_memset _ _ _ _ _ HIok). Qed.
Lemma memset_cps : forall pc, amemset_spec_at pc ->
  forall scr LB FF LK cr A dst c n sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A 0 (memset_pre LB FF sp scr dst c n) (memset_post LB cr dst c n).
Proof.
  intros pc SPEC scr LB FF LK cr A dst c n sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Ha0 & Ha1 & Ha2 & HD) CONT.
  apply (SPEC fx R M model LB FF LK cr A dst c n K (amem_pre_of scr fx R M model LB FF LK cr A dst n sp r K Hscr HH Hmo HK Hra Hraok Hsp Htp Hstk Ha0 Ha2 HD) Ha1).
  apply (amem_post_of scr fx R M model LB FF LK cr A dst n sp r K _ Hscr Hmo HFP Hra Hsp Hstk). exact CONT.
Qed.
Lemma asan_memset_cps : forall scr LB FF LK cr A dst c n sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI (hl_asan_memset L) r sp scr LB FF LK cr A 0 (memset_pre LB FF sp scr dst c n) (memset_post LB cr dst c n).
Proof. exact (memset_cps _ amemset_at_iface). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aacc_blk : forall (M : mem) u n p m, shadow_blk M u n -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + m <= u + n -> aacc M p m.
Proof.
  intros M u n p m [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
  assert (Q : a / 8 - u / 8 = (a - u) / 8).
  { apply Z.mod_divide in U8; [|lia]. destruct U8 as [q ->]. replace (a - q * 8) with ((a - q * 8) + 0) by lia. rewrite Z.div_mul by lia.
    replace (a - q * 8 + 0) with (a + (- q) * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (LE : (a - u) / 8 <= n / 8) by (apply Z.div_le_mono; lia).
  destruct (Z_lt_le_dec ((a - u) / 8) (n / 8)) as [LT|GE].
  - left. rewrite E, Q. apply SZ. split; [apply Z.div_pos; lia | exact LT].
  - right. assert (G : (a - u) / 8 = n / 8) by lia. exists (n mod 8).
    pose proof (Z.div_mod (a - u) 8 ltac:(lia)) as D1. pose proof (Z.div_mod n 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (a - u) 8 ltac:(lia)) as B1. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B2.
    assert (NZ : n mod 8 <> 0) by lia.
    assert (AM : a mod 8 = (a - u) mod 8).
    { apply Z.mod_divide in U8; [|lia]. destruct U8 as [q ->]. replace (a - q * 8) with (a + (- q) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    split; [rewrite E, Q, G; apply SP; exact NZ | lia].
Qed.

(* [comment removed for export] *)
Lemma dst_in_block : forall LB FF LK cr A (M : mem) V sp scr u m dst n,
  ri_inv HI LB FF LK cr A M V -> In (u, m) LB -> shadow_blk M u m -> u <= dst -> dst + n <= u + m -> 0 <= n <= 2 ^ 27 ->
  mem_dst LB FF sp scr M dst n.
Proof.
  intros LB FF LK cr A M V sp scr u m dst n HH Hin Hsh H1 H2 Hn.
  destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
  destruct (WF (u, m) Hin) as (HBR & HDF & _). cbn [fst snd] in HBR, HDF. destruct HBR as (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)).
  assert (U8 : u mod 8 = 0) by (apply CHA.mod8_of_16; exact B3).
  split; [exact Hn|]. split; [exact (aacc_blk M u m dst n Hsh U8 ltac:(lia) H1 H2)|]. split; [|split].
  - intros i Hi. left. exists (u, m). split; [exact Hin | cbn [fst snd]; lia].
  - assert (D : L5.defined M dst n) by (intros i Hi; replace (dst + i) with (u + (dst - u + i)) by lia; apply HDF; lia).
    exact (L5C.writable_of_defined (hl_segs L) M _ _ D ltac:(lia) ltac:(lia)).
  - unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; [lia|]. split; [lia|]. left.
    destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _). lia.
Qed.
(* [comment removed for export] *)
Lemma src_in_block : forall LB FF LK cr A (M : mem) V sp scr u m src n bs,
  ri_inv HI LB FF LK cr A M V -> In (u, m) LB -> aacc M src n -> u <= src -> src + n <= u + m -> 0 <= n ->
  rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  mem_src LB FF sp scr M src n bs.
Proof.
  intros LB FF LK cr A M V sp scr u m src n bs HH Hin Hacc H1 H2 Hn Hrd.
  destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
  destruct (WF (u, m) Hin) as (HBR & _). cbn [fst snd] in HBR. destruct HBR as (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)).
  split; [exact Hacc|]. split; [lia|]. split; [|split; [|exact Hrd]].
  - unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; [lia|]. split; [lia|]. left. lia.
  - intros i Hi. right. left. exists (u, m). split; [exact Hin | cbn [fst snd]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shadow_of_blk : forall u n x, u mod 8 = 0 -> 0 < n -> (in_shadow_of u n x <-> L5.in_rng (S u, (n + 7) / 8) x).
Proof.
  intros u n x U8 Hn. unfold in_shadow_of, L5.in_rng, S. cbn [fst snd].
  apply Z.mod_divide in U8; [|lia]. destruct U8 as [q ->].
  assert (E1 : (q * 8 + n - 1) / 8 = q + (n - 1) / 8) by (replace (q * 8 + n - 1) with ((n - 1) + q * 8) by lia; rewrite Z.div_add by lia; lia).
  assert (E2 : (n + 7) / 8 = (n - 1) / 8 + 1) by (replace (n + 7) with ((n - 1) + 1 * 8) by lia; rewrite Z.div_add by lia; lia).
  assert (E0 : q * 8 / 8 = q) by (apply Z.div_mul; lia).
  rewrite E0, E1, E2. lia.
Qed.
Lemma shadow_cont_def : forall (M : mem) u n mid j, 0 <= mid <= n -> 0 <= j < (n + 7) / 8 -> shadow_cont M u n mid -> M (Z_to_bv 64 (S u + j)) <> None.
Proof.
  intros M u n mid j Hm Hj (Z0 & PT & OOB). unfold shadow_zero, byte_at in *.
  destruct (Z_lt_le_dec j (mid / 8)) as [G|G]; [rewrite (Z0 j ltac:(lia)); discriminate|].
  destruct (Z_le_dec ((mid + 7) / 8) j) as [G2|G2]; [rewrite (OOB j ltac:(lia)); discriminate|].
  pose proof (Z.div_mod mid 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound mid 8 ltac:(lia)) as B1.
  assert (E2 : (mid + 7) / 8 < mid / 8 + 2) by (apply Z.div_lt_upper_bound; lia).
  assert (Ej : j = mid / 8) by lia. subst j.
  destruct (Z.eq_dec (mid mod 8) 0) as [e|ne]; [|rewrite (PT ne); discriminate].
  exfalso. apply G2. replace (mid + 7) with (7 + (mid / 8) * 8) by lia. rewrite Z.div_add by lia. replace (7 / 8) with 0 by reflexivity. lia.
Qed.

Definition annotate_pre (LB : list (Z * Z)) (u n om nm : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  In (u, n) LB /\ getr R 10%bv = Z_to_bv 64 u /\ getr R 11%bv = Z_to_bv 64 (u + n) /\ getr R 12%bv = Z_to_bv 64 (u + om) /\ getr R 13%bv = Z_to_bv 64 (u + nm) /\
  0 <= om <= n /\ 0 <= nm <= n /\ n <= 2 ^ 18 /\ shadow_cont M u n om.
Definition annotate_post (LB : list (Z * Z)) (cr : credit) (u n nm : Z)
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  shadow_cont M' u n nm /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S u, (n + 7) / 8)].
Lemma annotate_cps : forall pc scr0, aannotate_spec L ar SCFG HI pc scr0 ->
  forall scr LB FF LK cr A u n om nm sp r, 0 <= scr0 <= scr ->
  CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A 0 (annotate_pre LB u n om nm) (annotate_post LB cr u n nm).
Proof.
  intros pc scr0 SPEC scr LB FF LK cr A u n om nm sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Hin & Ha0 & Ha1 & Ha2 & Ha3 & Hom & Hnm & Hn & Hsh) CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
  destruct (WF (u, n) Hin) as (HBR & _). cbn [fst snd] in HBR. destruct HBR as (B1 & B2 & B3 & B4 & _).
  assert (U8 : u mod 8 = 0) by (apply CHA.mod8_of_16; exact B3).
  apply (SPEC fx R M model LB FF LK cr A u n om nm K HH (proj1 Hmo) (proj2 Hmo) Hin Ha0 Ha1 Ha2 Ha3 Hom Hnm Hn Hsh (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk M sp scr _ Hscr Hstk).
  - exact HK.
  - rewrite USP. intros R' M' model' HRP Hsh' Hkeep Hdef _ Hrt HMI' HH'. rewrite Hra.
    apply (CONT fx R' M' model' LB cr LB [(S u, (n + 7) / 8)] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + split; [exact Hsh'|]. repeat split; reflexivity.
    + apply (ahpres_scr LB FF sp scr0 scr [(S u, (n + 7) / 8)] M M' Hscr Hstk).
      * intros a Ha Hc Ho. apply (Hkeep a Ha Hc). intros Hin'. apply (Ho (S u, (n + 7) / 8)); [left; reflexivity | apply (shadow_of_blk u n a U8 B4); exact Hin'].
      * exact Hdef.
      * intros w a [<-|[]] [X1 X2]. cbn [fst snd] in X1, X2. replace a with (S u + (a - S u)) by lia. apply (shadow_cont_def M' u n nm (a - S u) Hnm ltac:(lia) Hsh').
Qed.
(* [comment removed for export] *)
Definition amemcmp_spec_at (pc scr0 : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (p q n : Z) (b1 b2 : list byte) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 q -> getr R 12%bv = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr0 sp ->
    0 <= p -> p + n <= 2 ^ 47 -> 0 <= q -> q + n <= 2 ^ 47 ->
    rdn (hl_segs L) M (Z_to_bv 64 p) (Z.to_nat n) = Some b1 -> rdn (hl_segs L) M (Z_to_bv 64 q) (Z.to_nat n) = Some b2 ->
    (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L ar LB FF sp scr0 (p + i)) ->
    (forall i, 0 <= i < n -> hl_img_lo L <= q + i < hl_img_hi L \/ aclient L ar LB FF sp scr0 (q + i)) ->
    aacc M p n -> aacc M q n -> app_rng ar p n -> app_rng ar q n ->
    Kt [] ->
    (forall (R' : bvmap 5 word) (M' : mem) (model' : Model),
        getr R' 10%bv = Z_to_bv 64 (memcmp_val b1 b2) -> regs_preserved R R' ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr0 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - scr0 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') Kt) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) model) Kt.
Definition memcmp_pre (LB : list (Z * Z)) (FF : list fframe) (sp scr p q n : Z) (b1 b2 : list byte) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 p /\ getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= 2 ^ 27 /\
  mem_src LB FF sp scr M p n b1 /\ mem_src LB FF sp scr M q n b2.
Definition memcmp_post (LB : list (Z * Z)) (cr : credit) (b1 b2 : list byte)
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  getr R' 10%bv = Z_to_bv 64 (memcmp_val b1 b2) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [].
Lemma memcmp_cps : forall pc scr0, amemcmp_spec_at pc scr0 -> forall scr LB FF LK cr A p q n b1 b2 sp r, 0 <= scr0 <= scr ->
  CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A 0 (memcmp_pre LB FF sp scr p q n b1 b2) (memcmp_post LB cr b1 b2).
Proof.
  intros pc scr0 SPEC scr LB FF LK cr A p q n b1 b2 sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _
         (Ha0 & Ha1 & Ha2 & Hn & (P1 & P2 & P3 & P4 & P5) & (Q1 & Q2 & Q3 & Q4 & Q5)) CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (SPEC fx R M model LB FF LK cr A p q n b1 b2 K HH (proj1 Hmo) (proj2 Hmo) Ha0 Ha1 Ha2 Hn Htp (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk M sp scr _ Hscr Hstk).
  - exact (proj1 P2).
  - exact (proj2 P2).
  - exact (proj1 Q2).
  - exact (proj2 Q2).
  - exact P5.
  - exact Q5.
  - rewrite USP. intros i Hi. destruct (P4 i Hi) as [X|X]; [left; exact X | right; exact (aclient_scr0 _ _ _ _ _ _ Hscr X)].
  - rewrite USP. intros i Hi. destruct (Q4 i Hi) as [X|X]; [left; exact X | right; exact (aclient_scr0 _ _ _ _ _ _ Hscr X)].
  - exact P1.
  - exact Q1.
  - exact P3.
  - exact Q3.
  - exact HK.
  - rewrite USP. intros R' M' model' Ha0' HRP Hkeep Hdef _ Hrt HMI' HH'. rewrite Hra.
    apply (CONT fx R' M' model' LB cr LB [] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + split; [exact Ha0'|]. repeat split; reflexivity.
    + apply (ahpres_scr LB FF sp scr0 scr [] M M' Hscr Hstk); [intros a Ha Hc _; exact (Hkeep a Ha Hc) | exact Hdef | intros w a []].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition setsh_pre (FF : list fframe) (f : fframe) (sa n : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 sa /\ getr R 11%bv = Z_to_bv 64 n /\ In f FF /\ 0 <= n /\ S (ff_addr f) <= sa /\ sa + n <= S (ff_addr f) + ff_bytes (ff_class f) / 8.
Definition setsh_post (LB : list (Z * Z)) (cr : credit) (sa n v : Z)
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  (forall j, 0 <= j < n -> byte_at M' (sa + j) v) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(sa, n)].
Lemma setsh_cps : forall pc v scr0, aset_shadow_spec L ar SCFG HI pc v scr0 ->
  forall scr LB FF LK cr A f sa n sp r, 0 <= scr0 <= scr ->
  CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A 0 (setsh_pre FF f sa n) (setsh_post LB cr sa n v).
Proof.
  intros pc v scr0 SPEC scr LB FF LK cr A f sa n sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _ (Ha0 & Ha1 & Hf & Hn & Hlo & Hhi) CONT.
  pose proof (usp R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (SPEC fx R M model LB FF LK cr A f sa n K HH (proj1 Hmo) (proj2 Hmo) Ha0 Ha1 Hf Hn Hlo Hhi (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk M sp scr _ Hscr Hstk).
  - exact HK.
  - rewrite USP. intros R' M' model' HRP Hby Hkeep Hdef Hmono Hrt HMI' HH'. rewrite Hra.
    apply (CONT fx R' M' model' LB cr LB [(sa, n)] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + split; [exact Hby|]. repeat split; reflexivity.
    + apply (ahpres_scr LB FF sp scr0 scr [(sa, n)] M M' Hscr Hstk).
      * intros a Ha Hc Ho. apply (Hkeep a Ha Hc). intros Hin'. apply (Ho (sa, n)); [left; reflexivity | exact Hin'].
      * exact Hdef.
      * intros w a [<-|[]] [X1 X2]. cbn [fst snd] in X1, X2. pose proof (Hby (a - sa) ltac:(lia)) as Bv. unfold byte_at in Bv. replace (sa + (a - sa)) with a in Bv by lia. rewrite Bv. discriminate.
Qed.
End Rt.

(* [comment removed for export] *)
Section Icpt.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.
Variable ANNOTATE : Prop.
Hypothesis ICok : pm_aicpt_ok L ar IL ILX SCFG HI ANNOTATE.
Variable FPI : FPState -> Prop.

Lemma libc_memcpy_cps : forall scr LB FF LK cr A dst src n bs sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI (icl_memcpy IL) r sp scr LB FF LK cr A 0 (memcpy_pre L ar LB FF sp scr dst src n bs) (memcpy_post LB cr dst n bs).
Proof. exact (memcpy_cps L ar HI FPI _ (pic_memcpy_libc _ _ _ _ _ _ _ ICok)). Qed.
Lemma libc_memmove_cps : forall scr LB FF LK cr A dst src n bs sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI (icl_memmove IL) r sp scr LB FF LK cr A 0 (memcpy_pre L ar LB FF sp scr dst src n bs) (memcpy_post LB cr dst n bs).
Proof. exact (memcpy_cps L ar HI FPI _ (pic_memmove_libc _ _ _ _ _ _ _ ICok)). Qed.

Lemma memcmp_iface_cps : forall scr LB FF LK cr A p q n b1 b2 sp r, 0 <= iclx_scr_memcmp ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_memcmp ILX) r sp scr LB FF LK cr A 0 (memcmp_pre L ar LB FF sp scr p q n b1 b2) (memcmp_post LB cr b1 b2).
Proof.
  apply (memcmp_cps L ar HI FPI). intros fx R M model LB FF LK cr A p q n b1 b2 Kt.
  exact (pic_memcmp _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A p q n b1 b2 Kt).
Qed.

(* [comment removed for export] *)
Definition cxa_pre (f arg dso : Z) (hs : list (Z * Z)) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 f /\ getr R 11%bv = Z_to_bv 64 arg /\ getr R 12%bv = Z_to_bv 64 dso /\ 0 <= f < 2 ^ 64 /\ 0 <= arg < 2 ^ 64 /\
  atexit_state_at (hl_segs L) (iclx_atexit_tab ILX) M hs /\ Z.of_nat (length hs) + 2 <= 32 /\ hs <> [] /\
  cell_is (hl_segs L) M (iclx_need_locks ILX) 1 0 /\ L5.writable (hl_segs L) M (iclx_atexit_tab ILX) ATEXIT_TAB_BYTES /\ L5.defined M (iclx_atexit_tab ILX) ATEXIT_TAB_BYTES.
Definition cxa_post (LB : list (Z * Z)) (cr : credit) (f arg : Z) (hs : list (Z * Z))
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  getr R' 10%bv = Z_to_bv 64 0 /\ atexit_state_at (hl_segs L) (iclx_atexit_tab ILX) M' (hs ++ [(f, arg); (iclx_atcxa ILX, 0)]) /\
  LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)].
Lemma cxa_atexit_cps : forall scr LB FF LK cr A f arg dso hs sp r, 0 <= iclx_scr_cxa ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_cxa_atexit ILX) r sp scr LB FF LK cr A 0 (cxa_pre f arg dso hs) (cxa_post LB cr f arg hs).
Proof.
  intros scr LB FF LK cr A f arg dso hs sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _
         (Ha0 & Ha1 & Ha2 & Hf & Harg & Hst & Hlen & Hne & Hnl & Hwr & Hdf) CONT.
  pose proof (usp ar R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (pic_cxa_atexit _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A f arg dso hs K HH (proj1 Hmo) (proj2 Hmo) Ha0 Ha1 Ha2 Hf Harg Htp (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk L ar M sp scr _ Hscr Hstk).
  - exact Hst.
  - exact Hlen.
  - exact Hne.
  - exact Hnl.
  - exact Hwr.
  - exact HK.
  - rewrite USP. intros R' M' model' Ha0' HRP Hst' Hkeep Hdef Hmono Hrt HMI' HH'. rewrite Hra.
    apply (CONT fx R' M' model' LB cr LB [(iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + split; [exact Ha0'|]. split; [exact Hst'|]. repeat split; reflexivity.
    + apply (ahpres_scr L ar LB FF sp (iclx_scr_cxa ILX) scr [(iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)] M M' Hscr Hstk).
      * intros a Ha Hc Ho. apply (Hkeep a Ha Hc). intros Hin'. apply (Ho (iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)); [left; reflexivity | exact Hin'].
      * exact Hdef.
      * intros w a [<-|[]] [X1 X2]. cbn [fst snd] in X1, X2. apply Hmono. replace a with (iclx_atexit_tab ILX + (a - iclx_atexit_tab ILX)) by lia. apply Hdf. lia.
Qed.
(* [comment removed for export] *)
Definition cxa_pre' (f arg dso : Z) (hs : list (Z * Z)) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 f /\ getr R 11%bv = Z_to_bv 64 arg /\ getr R 12%bv = Z_to_bv 64 dso /\ 0 <= f < 2 ^ 64 /\ 0 <= arg < 2 ^ 64 /\
  atexit_state_at (hl_segs L) (iclx_atexit_tab ILX) M hs /\ Z.of_nat (length hs) + 2 <= 32 /\ hs <> [] /\
  cell_is (hl_segs L) M (iclx_need_locks ILX) 1 0 /\ L5.writable (hl_segs L) M (iclx_atexit_tab ILX) ATEXIT_TAB_BYTES.
Lemma cxa_atexit_cps' : forall scr LB FF LK cr A f arg dso hs sp r, 0 <= iclx_scr_cxa ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_cxa_atexit ILX) r sp scr LB FF LK cr A 0 (cxa_pre' f arg dso hs) (cxa_post LB cr f arg hs).
Proof.
  intros scr LB FF LK cr A f arg dso hs sp r Hscr fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _
         (Ha0 & Ha1 & Ha2 & Hf & Harg & Hst & Hlen & Hne & Hnl & Hwr) CONT.
  pose proof (usp ar R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (pic_cxa_atexit _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A f arg dso hs K HH (proj1 Hmo) (proj2 Hmo) Ha0 Ha1 Ha2 Hf Harg Htp (ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (astack_ok_of_astk L ar M sp scr _ Hscr Hstk).
  - exact Hst.
  - exact Hlen.
  - exact Hne.
  - exact Hnl.
  - exact Hwr.
  - exact HK.
  - rewrite USP. intros R' M' model' Ha0' HRP Hst' Hkeep Hdef Hmono Hrt HMI' HH'. rewrite Hra.
    apply (CONT fx R' M' model' LB cr LB [(iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + split; [exact Ha0'|]. split; [exact Hst'|]. repeat split; reflexivity.
    + apply (ahpres_mono L ar LB FF sp (iclx_scr_cxa ILX) scr [(iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)] M M' Hscr Hstk).
      * intros a Ha Hc Ho. apply (Hkeep a Ha Hc). intros Hin'. apply (Ho (iclx_atexit_tab ILX, ATEXIT_TAB_BYTES)); [left; reflexivity | exact Hin'].
      * exact Hdef.
      * exact Hmono.
Qed.

(* [comment removed for export] *)
Lemma libc_memset_cps : forall scr LB FF LK cr A dst c n sp r, 0 <= hl_scr_mem L <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_memset ILX) r sp scr LB FF LK cr A 0 (memset_pre L ar LB FF sp scr dst c n) (memset_post LB cr dst c n).
Proof. apply (memset_cps L ar HI FPI). intros fx R M model LB FF LK cr A dst c n Kt. exact (pic_memset_libc _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A dst c n Kt). Qed.
Lemma memcmp2_cps : forall scr LB FF LK cr A p q n b1 b2 sp r, 0 <= iclx_scr_memcmp ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_memcmp2 ILX) r sp scr LB FF LK cr A 0 (memcmp_pre L ar LB FF sp scr p q n b1 b2) (memcmp_post LB cr b1 b2).
Proof.
  apply (memcmp_cps L ar HI FPI). intros fx R M model LB FF LK cr A p q n b1 b2 Kt.
  exact (pic_memcmp2 _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A p q n b1 b2 Kt).
Qed.
Lemma setsh00_cps : forall scr LB FF LK cr A f sa n sp r, 0 <= iclx_scr_setsh ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_setsh00 ILX) r sp scr LB FF LK cr A 0 (setsh_pre FF f sa n) (setsh_post LB cr sa n 0).
Proof. exact (setsh_cps L ar HI FPI _ _ _ (pic_setsh00 _ _ _ _ _ _ _ ICok)). Qed.
Lemma setshf5_cps : forall scr LB FF LK cr A f sa n sp r, 0 <= iclx_scr_setsh ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_setshf5 ILX) r sp scr LB FF LK cr A 0 (setsh_pre FF f sa n) (setsh_post LB cr sa n 245).
Proof. exact (setsh_cps L ar HI FPI _ _ _ (pic_setshf5 _ _ _ _ _ _ _ ICok)). Qed.
Lemma setshf8_cps : forall scr LB FF LK cr A f sa n sp r, 0 <= iclx_scr_setsh ILX <= scr ->
  CBA.cps_asanG L ar HI FPI (iclx_setshf8 ILX) r sp scr LB FF LK cr A 0 (setsh_pre FF f sa n) (setsh_post LB cr sa n 248).
Proof. exact (setsh_cps L ar HI FPI _ _ _ (pic_setshf8 _ _ _ _ _ _ _ ICok)). Qed.
End Icpt.
End CRC.
