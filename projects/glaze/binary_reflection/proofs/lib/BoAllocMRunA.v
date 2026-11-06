(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoAllocMTag.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).

(* [comment removed for export] *)
Lemma rdn1_off : forall (m : mem) (a : word) b,
  (bv_unsigned a + 1 <= 0x10000 \/ 0x663000 <= bv_unsigned a)%Z -> rdn BSEGS m a 1 = Some [b] -> m a = Some b.
Proof using.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1%Z in R.
    rewrite (find_segment1_none_outside BSEGS 0x10000 0x663000 (bv_unsigned a) asanF_segs_in_hull) in R; [discriminate R|].
    destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNA.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S ra0 tp tsdp P top bot csz stw : word) (T tctx n SPB cnt k : Z) (D : nat) (b1 : byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation c := (class_of (needed n)).
  (* [comment removed for export] *)
  Definition ma_ab : Z := (SPB + c * 2 ^ 32 + 16 * k)%Z.
  #[local] Abbreviation m := (Z_to_bv 64 ma_ab).
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = Z_to_bv 64 n.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T)) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis GSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 16)%Z.
  Hypothesis Hk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Gab : (ma_ab mod 16 = 0 /\ 0x10007fff8000 <= ma_ab /\ ma_ab + needed n <= U S - 3584 /\ ma_ab + 2 ^ 17 <= 2 ^ 47)%Z.   (* [comment removed for export] *)
  Hypothesis GabT : (ma_ab + needed n <= T \/ T + 4096 <= ma_ab)%Z.
  Hypothesis Gabctx : (ma_ab + needed n <= tctx \/ tctx + 4096 <= ma_ab)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_rss : rdn BSEGS mem (Z_to_bv 64 0x190422) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_lmag : rdn BSEGS mem (Z_to_bv 64 0x10488) 8 = Some (LE8 MAGICw).
  Hypothesis C_tbl2 : rdn BSEGS mem (at_ (Z_to_bv 64 0x104f8) 4) 1 = Some [Z_to_bv 8 3].
  Hypothesis C_t16 : rdn BSEGS mem (at_ (Z_to_bv 64 0x105f8) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis C_t2048 : rdn BSEGS mem (at_ (Z_to_bv 64 0x105f8) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis C_minrz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3624) 2 = Some (LE2 16).
  Hypothesis C_maxrz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3626) 2 = Some (LE2 2048).
  Hypothesis C_maxsz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis C_sbeg : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok BSEGS mem thr 4096 = true.
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_T0 : rdn BSEGS mem thr 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (at_ ctxw 8) 4 = Some (LE4 0).
  Hypothesis C_cnt : rdn BSEGS mem (at_ thr (208 + 80 * c)) 4 = Some (LE4 cnt).
  Hypothesis C_csz : rdn BSEGS mem (at_ thr (208 + 80 * c + 8)) 8 = Some (LE8 csz).
  Hypothesis C_k : rdn BSEGS mem (at_ thr (208 + 80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k).
  Hypothesis C_stw : rdn BSEGS mem (at_ thr 2784) 8 = Some (LE8 stw).
  (* [comment removed for export] *)
  Hypothesis C_b1 : rdn BSEGS mem (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis C_chunk : store_ok BSEGS mem m (Z.to_nat (needed n)) = true.
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.


  Lemma nf : (24 <= needed n <= 65536)%Z /\ (needed n mod 8 = 0)%Z /\ (16 <= rz n <= 1024)%Z /\ (needed n = rounded n + rz n)%Z
             /\ (Z.max n 8 <= rounded n <= Z.max n 8 + 7)%Z /\ (1 <= c <= 30)%Z.
  Proof using Gab Gn GS k SPB S.
    pose proof (needed_facts n Gn) as [N1 N2]. pose proof (rz_log_range n) as RL.
    assert (Hrz : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    split; [lia|]. split; [exact N2|]. split; [exact Hrz|]. split; [reflexivity|]. split.
    - (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
    - apply AsArith3.class_of_range. lia.
  Qed.

  Theorem run_mA :
    exists (r : bvmap 5 word) (MP : word -> option byte) (s : Z) (bsz : list byte) (x18 x19 : word),
      msteps BSEGS (mkst R (Z_to_bv 64 0x6ef3c) mem rom)
                   (mkst r (Z_to_bv 64 0x8f4f0) (ma_P2 MP S T n cnt stw csz m b1 x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) rom)
      /\ getr r 1 = Z_to_bv 64 0x4c940 /\ getr r 2 = at_ S (-2272) /\ getr r 4 = tp /\ getr r 3 = getr R 3
      /\ getr r 10 = at_ S (-2112) /\ getr r 11 = Z_to_bv 64 (bytes_le_to_Z bsz)
      /\ getr r 8 = Z_to_bv 64 1 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = m /\ getr r 19 = Z_to_bv 64 (needed n)
      /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 22 = Z_to_bv 64 0x10ab58 /\ getr r 23 = at_ S (-2128)
      /\ getr r 24 = Z_to_bv 64 0 /\ getr r 25 = at_ m (rz n + n) /\ getr r 26 = thr /\ getr r 27 = Z_to_bv 64 1
      /\ (1 <= s <= 30 /\ bytes_le_to_Z bsz = s)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z)
      /\ mem_grows mem MP
      /\ rdn BSEGS MP (at_ S (-2120)) 4 = Some (LE4 s) /\ rdn BSEGS MP (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn BSEGS MP (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (kk : Z) (v : word),
            In (kk, v) [(-8, ra0); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
            rdn BSEGS MP (at_ S kk) 8 = Some (LE8 v)).
  Proof using Hfpc C_chunk C_b1 C_stw C_k C_csz C_cnt C_tid C_T0 C_bot C_top C_sw C_unw C_Tw C_sbeg C_maxsz C_maxrz C_minrz C_t2048 C_t16 C_tbl2 C_lmag C_rss C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_inited C_fum C_gcf C_mcs Hstk Gabctx GabT Gab Hk Hcnt GSPB Gbot Gtop GP Gtsdp Gtp Gctx GT Gn GS HR10 HR4 HR2 HR1 tctx bot top P tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr. pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2 & GT3). destruct Gctx as (Gc1 & Gc2 & Gc3). destruct Gtp as (Gtp1 & Gtp2).
    wm_parts GT1.
    destruct Gab as (Ga1 & Ga2 & Ga3 & Ga4). pose proof nf as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).
    assert (Um : U m = ma_ab) by (unorm; reflexivity).
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (MH : mpH BSEGS both_mp_tab mem S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs both_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x19fce8) 34) with (Z_to_bv 64 0x19fd0a : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (UH : uiH BSEGS both_ui_tab mem (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi both_ui_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_unw.
      - eapply (store_ok_sub BSEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - exact C_pg.
      - exact C_P.
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (GH : gctH BSEGS (ut_gct both_ui_tab) mem (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct both_ui_tab gt_tsd both_gct_tab] in G in change_no_check G' end).
      - exact C_kif. - exact C_key. - exact C_tsdp. - exact C_tctx. - exact C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH BSEGS mem thr top bot).
    { split; [exact C_sw | exact C_top | exact C_bot | exact Gbot | wd_ulia]. }
    destruct (mp_run BSEGS both_mp_tab both_mp_tab_ok R mem rom ra0 S tp (Z_to_bv 64 n) (Z_to_bv 64 0x19fce8) thr top bot tsdp ctxw P (Z_to_bv 8 1)
                HR1 HR2 HR4 HR10 MH UH GH SH Gtop D Hfpc)
      as (r1 & MP & s & RUN1 & A1 & A2 & A4 & A10 & A11 & A8 & A9 & A20 & A21 & AG1 & Hs1 & Hs2 & Psz & Ptag & Ptr & Ppc0 & Pslots & Punw & Pfoot & Pgrows).
    cbn [mt_rb both_mp_tab] in RUN1, A1.
    rewrite (ARB_lit 454460) in RUN1 by lia. rewrite (ARB_lit 312632) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (QP : forall x : word, (U x < U S - 2272 \/ U S <= U x)%Z -> MP x = mem x).
    { intros x Hx. destruct (decide (MP x = mem x)) as [E|NE]; [exact E|]. exfalso.
      destruct (Pfoot x NE) as [F|F]; [lia|].
      apply NE. replace x with (at_ thr 3168) by (apply bv_eq; rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; lia).
      rewrite (rdn1_off MP (at_ thr 3168) (Z_to_bv 8 0)); [| rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact Punw].
      rewrite (rdn1_off mem (at_ thr 3168) (Z_to_bv 8 0)); [reflexivity | rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact C_unw]. }
    (* [comment removed for export] *)
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    destruct (amA_run BSEGS both_am_tab both_am_tab_ok r1 MP rom (at_ ARB 0x6f070) (at_ S (-2128)) (at_ S (-2128)) n A1 A2 A10 A11 Gn)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    all: (lazymatch goal with |- ?G => let G' := eval cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss both_am_tab] in G in change_no_check G' end).
    { xq QP C_inited. } { xq QP C_rss. } { xq QP C_lmag. } { xq QP C_tbl2. } { xq QP C_t16. } { xq QP C_t2048. }
    { xq QP C_minrz. } { xq QP C_maxrz. } { xq QP C_maxsz. }
    { rewrite at_at. eapply store_ok_mono; [exact Pgrows|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { unorm. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    { rewrite at_u by lia. lia. }
    cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss both_am_tab] in RUN2, B22, B26.
    rewrite (ARB_lit 312632) in RUN2 by lia. rewrite (ARB_lit 313364) in RUN2 by lia.
    rewrite (ma_A_eq MP S n r1 A8 A9 A20 A21) in RUN2.
    (* [comment removed for export] *)
    Ltac r1R AG1 k := rewrite (AG1 k) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 22%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 23%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 24%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 25%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 26%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 27%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    set (MA := ma_A MP S n (getr r1 18) (getr r1 19) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in RUN2.
    assert (QA : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> MA x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite ma_A_outside; [apply QP; lia | lia | lia]. }
    assert (GRA : mem_grows mem MA) by (eapply mem_grows_trans; [exact Pgrows | (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply ma_A_grows]).
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add] in B2.
    (* [comment removed for export] *)
    assert (B4 : getr r2 4 = tp) by (rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); exact HR4).
    assert (GH2 : gctH BSEGS both_gct_tab MA (at_ S (-2272)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq QA C_kif. - xq QA C_key. - xq QA C_tsdp. - xq QA C_tctx. - xq QA C_thr.
      - unorm. lia.
      - rewrite at_at. eapply store_ok_mono; [exact GRA|].
        eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (amB_run BSEGS ARB both_HAL both_HCB ARB_ok both_gct_tab both_gct_tab_ok both_GTRB r2 MA rom (at_ S (-2272)) tp tsdp ctxw thr (Z_to_bv 64 0x10ab58) n
                B2 B4 B19 B22 Gn GH2
                ltac:(rewrite at_at; eapply store_ok_mono; [exact GRA|];
                      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(rewrite Uthr, at_u by lia; lia) ltac:(wd_ulia)
                cnt k csz stw (Z_to_bv 64 SPB) Hcnt Hk)
      as (r3 & RUN3 & C10 & C26 & AG3).
    { xq QA C_cnt. } { xq QA C_csz. } { xq QA C_k. } { xq QA C_stw. }
    { eapply store_ok_mono; [exact GRA|]. eapply (store_ok_sub BSEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [exact GRA|]. eapply (store_ok_sub BSEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { xq QA C_sbeg. }
    { unorm. lia. }
    rewrite (ARB_lit 313364) in RUN3 by lia. rewrite (ARB_lit 313396) in RUN3 by lia.
    rewrite (ma_B_eq MA S T n cnt stw csz r2 B8 B9 B18 B19 B20) in RUN3.
    set (MB := ma_B MA S T n cnt stw csz) in RUN3.
    assert (QB : forall x : word, ((U x < U S - 2320)%Z /\ (U x < T + 208 + 80 * c \/ T + 208 + 80 * c + 4 <= U x)%Z /\ (U x < T + 2784 \/ T + 2792 <= U x)%Z) \/ (U S <= U x)%Z -> MB x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB, MA in G in change_no_check G' end). rewrite ma_B_outside; first [apply QA; lia | lia]. }
    assert (GRB : mem_grows mem MB) by (eapply mem_grows_trans; [exact GRA | (lazymatch goal with |- ?G => let G' := eval unfold MB, MA in G in change_no_check G' end); apply ma_B_grows; lia]).
    replace (Z_to_bv 64 (U (Z_to_bv 64 SPB) + c * 2 ^ 32 + 16 * k)) with m in C10 by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold ma_ab in G in change_no_check G' end); unorm; reflexivity).
    (* [comment removed for export] *)
    Ltac r3r AG3 H := rewrite (AG3 _) by notin; exact H.
    (* [comment removed for export] *)
    destruct (rdn_defined_ex BSEGS MP (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply Pgrows. apply (store_ok1_heap mem); [wd_ulia|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584 1); [rewrite at_u; lia | exact Hstk | rewrite at_u by lia; wd_ulia | rewrite at_u by lia; wd_ulia_c]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (HBSZ : bytes_le_to_Z bsz = s) by (apply (bsz_val BSEGS MP (at_ S (-2120)) bsz s Rsz Psz); [rewrite at_at; exact Ptag | lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]).
    pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite Lsz in Bb. pose proof (bytes_le_to_Z_nonneg bsz) as Bb0.
    destruct (amC_run BSEGS ARB both_HAL2 r3 MB rom (at_ S (-2272)) m (at_ S (-2128)) thr ctxw (at_ S (-2112)) (Z_to_bv 64 (bytes_le_to_Z bsz)) bsz b1 n 0)
      as (r4 & RUN4 & E1 & E10 & E11 & E18 & E20 & E21 & E24 & E25 & AG4).
    { r3r AG3 B2. } { r3r AG3 B9. } { exact C10. } { r3r AG3 B19. } { r3r AG3 B20. } { r3r AG3 B21. } { r3r AG3 B23. } { r3r AG3 B25. }
    { exact C26. } { r3r AG3 B27. } { exact Gn. } { lia. }
    { rewrite Um. lia. } { rewrite at_u by lia. lia. } { rewrite Uthr. hlia. } { rewrite Uctx. lia. } { rewrite at_u by lia. lia. }
    { xq QB C_b1. }
    { eapply store_ok_mono; [exact GRB|]. eapply (store_ok_sub BSEGS mem m _ (Z.to_nat (needed n))); [rewrite Um; lia | exact C_chunk | rewrite at_u, Um; lia | rewrite at_u, Um by (rewrite Um; lia); rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold MB, ma_B in G in change_no_check G' end). rewrite !at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end).
      repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]).
      (lazymatch goal with |- ?G => let G' := eval unfold MA, ma_A in G in change_no_check G' end). rewrite !at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). rd8_chain. }
    { xq QB C_T0. }
    { xq QB C_tid. }
    { (* [comment removed for export] *)
      eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Ptr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB, MA in G in change_no_check G' end). rewrite ma_B_outside by lia. apply ma_A_outside; lia. }
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end).
      eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rsz].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB, MA in G in change_no_check G' end). rewrite ma_B_outside by lia. apply ma_A_outside; lia. }
    { split; [unorm; reflexivity | exact Lsz]. }
    { rewrite at_u, Um by lia. lia. }
    { rewrite Uthr, Um. lia. }
    { rewrite Uctx, Um. lia. }
    { rewrite at_u, Um by lia. lia. }
    rewrite (ARB_lit 313396) in RUN4 by lia. rewrite (ARB_lit 586992) in RUN4 by lia.
    (* [comment removed for export] *)
    exists r4, MP, s, bsz, (getr r1 18), (getr r1 19).
    split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4. }
    split; [rewrite E1; apply ARB_lit; lia|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try rch; try lia.
    intros x NE. destruct (Pfoot x NE) as [F|F]; [exact F|]. exfalso. apply NE. apply QP. rewrite Uthr in F. lia.
  Qed.
End RUNA.
End FPGen.
