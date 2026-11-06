(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ARep AHeapP AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AInstance AInstanceM AInstanceF AFreeAll ADeallocate AEmbRep AMalloc_x ARealloc_x AInstanceX AInstanceU ARepTwin AFreeRep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition ov_sup (ov : annOV) (LB : list ablock) : Prop :=
  forall q, @ann_ov ov q <> None -> exists A n, In (HB q A n) LB.

Definition AHEAPu2 (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m : amem) : Prop :=
  exists ov : annOV, @AHEAPu rc ov L RNG st LB m /\ ov_sup ov LB.

Lemma ov_sup_incl : forall ov LB LB', ov_sup ov LB -> (forall p A n, In (HB p A n) LB -> In (HB p A n) LB') -> ov_sup ov LB'.
Proof. intros ov LB LB' S INC q Hq. destruct (S q Hq) as (A & n & Hin). exists A, n. exact (INC _ _ _ Hin). Qed.

Lemma live_cell_u : forall (ov : annOV) L RNG st LB m p A n,
  @AHEAPu rc ov L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (@live_bytes ov p n)]
  /\ 0x2008fff7000 <= shad A /\ shad A + granules n <= 0x10007fff8000.
Proof. intros ov L RNG st LB m p A n [g AH]. exact (AHEAP_P_live_cell ov _ L RNG st LB m p A n AH). Qed.

Lemma mark_all_u : forall L RNG st LB m (l : list ablock) (ov : annOV),
  @AHEAPu rc ov L RNG st LB m -> (forall b, In b l -> In b LB) ->
  exists ov' : annOV, @AHEAPu rc ov' L RNG st LB m
    /\ (forall p A n, In (HB p A n) l -> is_primary n = true -> exists bs, @ann_ov ov' p = Some bs /\ length bs = Z.to_nat (granules n))
    /\ (forall q, @ann_ov ov' q <> None -> @ann_ov ov q <> None \/ exists A n, In (HB q A n) l).
Proof.
  intros L RNG st LB m l ov [g AH] SUB.
  destruct (AHEAP_P_mark_all (AHI (gb:=g)) (AHI_laws (gb:=g)) L RNG st LB m l ov AH SUB) as (ov' & AH' & MK & SP).
  exists ov'. split; [exists g; exact AH'|]. split; [exact MK| exact SP].
Qed.

Lemma twin_bytes_eq_u : forall (ov : annOV) L RNG RNG' st st' LB LB' m m' p A n bs,
  @AHEAPu rc ov L RNG st LB m -> @AHEAPu rc ov L RNG' st' LB' m' -> In (HB p A n) LB -> In (HB p A n) LB' -> is_primary n = true ->
  @ann_ov ov p = Some bs -> length bs = Z.to_nat (granules n) ->
  forall i, 0 <= i < granules n -> m' (wa (shad A + i)) = m (wa (shad A + i)).
Proof.
  intros ov L RNG RNG' st st' LB LB' m m' p A n bs [g AH] [g' AH'].
  exact (twin_bytes_eq ov _ _ L RNG RNG' st st' LB LB' m m' p A n bs AH AH').
Qed.

Lemma hb_lt_u : forall (ov : annOV) L RNG st LB m p A n, @AHEAPu rc ov L RNG st LB m -> In (HB p A n) LB -> (p < a_next st)%N.
Proof. intros ov L RNG st LB m p A n [g AH]. exact (AHEAP_P_hb_lt ov _ L RNG st LB m p A n AH). Qed.

Lemma twins_pres_u : forall (ov : annOV) L RNG RNG' st st' LB LB' LB0 m m',
  @AHEAPu rc ov L RNG st LB m -> @AHEAPu rc ov L RNG' st' LB' m' ->
  (forall p A n, In (HB p A n) LB0 -> In (HB p A n) LB /\ In (HB p A n) LB') ->
  (forall p A n, In (HB p A n) LB0 -> is_primary n = true -> exists bs, @ann_ov ov p = Some bs /\ length bs = Z.to_nat (granules n)) ->
  twins_pres LB0 m m'.
Proof.
  intros ov L RNG RNG' st st' LB LB' LB0 m m' AH AH' SUB MK p A n Hin PRIM i Hi.
  destruct (MK p A n Hin PRIM) as (bs & E & LBS). destruct (SUB p A n Hin) as [H1 H2].
  exact (twin_bytes_eq_u ov L RNG RNG' st st' LB LB' m m' p A n bs AH AH' H1 H2 PRIM E LBS i Hi).
Qed.

Lemma twins_pres_ov : forall (ov : annOV) L RNG RNG' st st' LB LB' LB0 m m',
  @AHEAPu rc ov L RNG st LB m -> @AHEAPu rc ov L RNG' st' LB' m' ->
  (forall p A n, In (HB p A n) LB0 -> In (HB p A n) LB /\ In (HB p A n) LB') ->
  twins_pres LB0 m m'.
Proof.
  intros ov L RNG RNG' st st' LB LB' LB0 m m' AH AH' SUB p A n Hin PRIM i Hi. destruct (SUB p A n Hin) as [H1 H2].
  destruct (live_cell_u ov L RNG st LB m p A n AH H1 PRIM) as (C1 & LO1 & _).
  destruct (live_cell_u ov L RNG' st' LB' m' p A n AH' H2 PRIM) as (C2 & _ & _).
  assert (LBS : length (@live_bytes ov p n) = Z.to_nat (granules n)) by (destruct C1 as [[WFc _] _]; cbn in WFc; tauto).
  change (shlen (n + 7)) with (granules n) in Hi.
  rewrite (cb_overlay m (shad A) _ _ i C1 ltac:(lia) ltac:(rewrite LBS; lia)).
  rewrite (cb_overlay m' (shad A) _ _ i C2 ltac:(lia) ltac:(rewrite LBS; lia)). reflexivity.
Qed.

Lemma ov_sup_fresh : forall (ov : annOV) L RNG st LB m, @AHEAPu rc ov L RNG st LB m -> ov_sup ov LB -> @ann_ov ov (a_next st) = None.
Proof.
  intros ov L RNG st LB m AH SUP. destruct (@ann_ov ov (a_next st)) as [bs|] eqn:E; [| reflexivity]. exfalso.
  destruct (SUP (a_next st) ltac:(rewrite E; discriminate)) as (A & n & Hin).
  pose proof (hb_lt_u ov L RNG st LB m _ A n AH Hin) as LT. lia.
Qed.

Lemma AIu2_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAPu2 L RNG st LB m -> AHEAPu2 L RNG' st LB m.
Proof. intros L RNG RNG' st LB m LE (ov & [g AH] & SUP). exists ov. split; [exists g; exact (AHI_rng_mono (gb:=g) L RNG RNG' st LB m LE AH)| exact SUP]. Qed.

Lemma AIu2_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAPu2 L RNG st LB m -> AHEAPu2 L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (ov & [g AH] & SUP). exists ov. split; [exists g; exact (AHI_perm (gb:=g) L RNG st LB LB' m P AH)|].
  eapply ov_sup_incl; [exact SUP|]. intros p A n Hin. exact (Permutation_in _ P Hin).
Qed.

Lemma AIu2_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAPu2 L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
  AHEAPu2 L RNG st LB m'.
Proof. intros L RNG st LB m m' W (ov & [g AH] & SUP) MU WM CW. exists ov. split; [exists g; exact (AHI_frame (gb:=g) L RNG st LB m m' W AH MU WM CW)| exact SUP]. Qed.

Lemma AIu2_frame_top : forall L RNG st LB m m',
  AHEAPu2 L RNG st LB m -> (forall a, 0 <= a < 2 ^ 47 -> m' (wa a) = m (wa a)) -> wmono asegs m m' -> AHEAPu2 L RNG st LB m'.
Proof. intros L RNG st LB m m' (ov & [g AH] & SUP) EQ WM. exists ov. split; [exists g; exact (AHI_frame_top (gb:=g) L RNG st LB m m' AH EQ WM)| exact SUP]. Qed.

Lemma AIu2_frame_twin : forall L RNG st LB m m' p A n,
  AHEAPu2 L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  munch [(shad A, shad A + shlen (n + 7))] m m' -> wmono asegs m m' ->
  (forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) <> None) ->
  AHEAPu2 L RNG st LB m'.
Proof.
  intros L RNG st LB m m' p A n (ov & [g AH] & SUP) Hin PRIM MU WM RDM.
  destruct (AHEAP_P_remark1 ov (AHI (gb:=g)) (AHI_laws (gb:=g)) L RNG st LB m m' p A n AH Hin PRIM MU WM RDM) as (bs & _ & _ & AH').
  exists (ov_set ov p bs). split; [exists g; exact AH'|].
  intros q Hq. unfold ov_set in Hq. cbn [ann_ov] in Hq. destruct (N.eq_dec q p) as [EQ|NE].
  - exists A, n. rewrite EQ. exact Hin.
  - apply N.eqb_neq in NE. rewrite NE in Hq. exact (SUP q Hq).
Qed.

Lemma AIu2_block : forall L RNG st LB m p A n,
  AHEAPu2 L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX /\
  ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
  /\ (exists bs, rw_cells asegs m (shad A) [CB (Z.to_nat (shlen (n + 7))) bs] /\ (is_primary n = false -> ablock_shadow m A n))
  /\ wr_at asegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
  /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO)).
Proof.
  intros L RNG st LB m p A n (ov & [g AH] & SUP) Hin.
  destruct (AHI_block (ov:=ov) (gb:=g) L RNG st LB m p A n AH Hin) as (N & BR & R1 & R2 & CELL & WR & CH & AR).
  split; [exact N|]. split; [exact BR|]. split; [exact R1|]. split; [exact R2|]. split; [| split; [exact WR| split; [exact CH| exact AR]]].
  eexists. split; [exact CELL|]. intros NP. rewrite NP in CELL.
  destruct BR as (B1 & B2 & B3 & B4). apply ablk_lin in B1. pose proof atop_range as ATR.
  eapply block_shadow_of_cb; [lia | clear -B4; Z.div_mod_to_equations; lia | clear -B1; lia | clear -B3 ATR; lia | exact CELL].
Qed.

Lemma amalloc_post_lift : forall (ov1 : annOV) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms',
  @AHEAPu rc ov1 L RNG st LB m -> ov_sup ov1 LB ->
  (forall p A n, In (HB p A n) LB -> is_primary n = true -> exists bs, @ann_ov ov1 p = Some bs /\ length bs = Z.to_nat (granules n)) ->
  amalloc_post aci_I (@AHEAPu rc ov1) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms' ->
  amalloc_post2 aci_I AHEAPu2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'.
Proof.
  intros until ms'. intros AH1 SUP1 MK (LE & P). split; [exact LE|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  destruct (snd r) as [p|]; [| destruct M].
  destruct M as (A & junk & M1 & M2 & M3 & M4 & M5 & M6 & M7).
  split.
  { eapply (twins_pres_u ov1 L RNG RNG' st (fst r) LB (HB p A n :: LB) LB m m' AH1 M3); [| exact MK].
    intros p' A' n' Hin. split; [exact Hin| right; exact Hin]. }
  exists A, junk. split; [exact M1|]. split; [exact M2|].
  split. { exists ov1. split; [exact M3|]. eapply ov_sup_incl; [exact SUP1|]. intros p' A' n' Hin. right. exact Hin. }
  split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].

  destruct M3 as [g' AH3].
  assert (UNM : @ann_ov ov1 p = None).
  { destruct (@ann_ov ov1 p) as [bs|] eqn:EP; [| reflexivity]. exfalso.
    destruct (SUP1 p ltac:(rewrite EP; discriminate)) as (A' & n' & Hin).
    pose proof (AHI_hb_ids (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' AH3) as ND. cbn [hb_ids flat_map ab_kind app] in ND.
    apply NoDup_cons_iff in ND as [NI _]. apply NI. unfold hb_ids. apply in_flat_map. exists (HB p A' n'). split; [exact Hin| left; reflexivity]. }
  destruct (AHI_block (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' p A n AH3 ltac:(left; reflexivity)) as (N & BR & _ & _ & CELL & _).
  rewrite (live_bytes_none p n UNM) in CELL. replace (if is_primary n then block_shadow_bytes n else block_shadow_bytes n) with (block_shadow_bytes n) in CELL by (destruct (is_primary n); reflexivity).
  destruct BR as (B1 & B2 & B3 & B4). apply ablk_lin in B1. pose proof atop_range as ATR.
  eapply block_shadow_of_cb; [lia | clear -B4; Z.div_mod_to_equations; lia | clear -B1; lia | clear -B3 ATR; lia | exact CELL].
Qed.

Lemma mark_sup_u : forall L RNG st LB m (ov0 : annOV), @AHEAPu rc ov0 L RNG st LB m -> ov_sup ov0 LB ->
  exists ov1 : annOV, @AHEAPu rc ov1 L RNG st LB m /\ ov_sup ov1 LB
    /\ (forall p A n, In (HB p A n) LB -> is_primary n = true -> exists bs, @ann_ov ov1 p = Some bs /\ length bs = Z.to_nat (granules n)).
Proof.
  intros L RNG st LB m ov0 AH0 SUP0.
  destruct (mark_all_u L RNG st LB m LB ov0 AH0 (fun b H => H)) as (ov1 & AH1 & MK & SP).
  exists ov1. split; [exact AH1|]. split; [| exact MK].
  intros q Hq. destruct (SP q Hq) as [S|E]; [exact (SUP0 q S)| exact E].
Qed.

Lemma amalloc_null_lift : forall (ov1 : annOV) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m st' RNG' ms',
  @AHEAPu rc ov1 L RNG st LB m -> ov_sup ov1 LB ->
  (fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aheap_pres_e aci_I LB (bv_unsigned sp) m m'
      /\ @AHEAPu rc ov1 L RNG' st' LB m'
      /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)]) ->
  amalloc_null_post2 aci_I AHEAPu2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo m st' RNG' ms'.
Proof.
  intros until ms'. intros AH1 SUP1 (LE & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M & ER).
  split; [exact LE|].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  split; [exact (twins_pres_ov ov1 L RNG RNG' st st' LB LB LB m m' AH1 M (fun p A n H => conj H H))|].
  split; [exists ov1; split; [exact M| exact SUP1]| exact ER].
Qed.

Section X.
Hypothesis EXHW : exh_first_stmt.
Theorem AHU2_malloc : amalloc_stmt2x aci_I AHEAPu2.
Proof.
  unfold amalloc_stmt2x. intros until RESV. intros (ov0 & AH0 & SUP0) MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK FCB C6M CAPB ERRC.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  pose proof (ov_sup_fresh ov1 L RNG st LB m AH1 SUP1) as OVF.
  eapply implF_epost_mono; [eapply (AHU_malloc_h (ov:=ov1) EXHW); eassumption|].
  intros [st' [p|]] RNG' ms'; unfold amalloc_post_h, amalloc_post2x; cbn [snd fst]; intros P.
  - eapply (amalloc_post_lift ov1); [exact AH1| exact SUP1| exact MK| exact P].
  - eapply (amalloc_null_lift ov1); [exact AH1| exact SUP1| exact P].
Qed.
End X.

Lemma unmark_u : forall (ov : annOV) L RNG st LB m p A n,
  @AHEAPu rc ov L RNG st LB m -> ov_sup ov LB -> In (HB p A n) LB -> ablock_shadow m A n ->
  exists ov' : annOV, @AHEAPu rc ov' L RNG st LB m /\ ov_sup ov' LB /\ @ann_ov ov' p = None.
Proof.
  intros ov L RNG st LB m p A n [g AH] SUP Hin CAN.
  destruct (is_primary n) eqn:PRIM.
  - exists (ov_unset ov p). split; [exists g; exact (AHEAP_P_unmark ov _ L RNG st LB m p A n AH Hin PRIM CAN)|].
    split; [| unfold ov_unset; cbn [ann_ov]; rewrite N.eqb_refl; reflexivity].
    intros q Hq. unfold ov_unset in Hq. cbn [ann_ov] in Hq. destruct (N.eqb q p); [congruence| exact (SUP q Hq)].
  -
    destruct (AHI_chunk (ov:=ov) (gb:=g) L RNG st LB m p A n AH Hin) as (ch & LV & _ & _ & KO).
    exists (ov_unset ov p). split.
    + exists g. apply AHEAP_P_unset_nonprim; [exact AH|]. intros c' n' E. rewrite E in LV. injection LV as <-. cbn in KO. congruence.
    + split; [| unfold ov_unset; cbn [ann_ov]; rewrite N.eqb_refl; reflexivity].
      intros q Hq. unfold ov_unset in Hq. cbn [ann_ov] in Hq. destruct (N.eqb q p); [congruence| exact (SUP q Hq)].
Qed.

Lemma hb_lb_remove : forall p q A n LB, In (HB q A n) (lb_remove p LB) <-> In (HB q A n) LB /\ q <> p.
Proof.
  intros p q A n LB. rewrite AFreeRep.In_lb_remove. cbn [ab_kind]. split; intros [H1 H2]; (split; [exact H1|]); intros E; apply H2; congruence.
Qed.

Theorem AHU2_free : afree_stmt2 aci_I AHEAPu2.
Proof.
  unfold afree_stmt2. intros until tr. intros (ov0 & AH0 & SUP0) HIN CAN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.

  destruct (unmark_u ov0 L RNG st LB m p A n AH0 SUP0 HIN CAN) as (ova & AHa & SUPa & UNa).
  destruct (mark_all_u L RNG st LB m (lb_remove p LB) ova AHa ltac:(intros b Hb; apply AFreeRep.In_lb_remove in Hb; tauto)) as (ov1 & AH1 & MK & SP).
  assert (SUP1 : ov_sup ov1 (lb_remove p LB)).
  { intros q Hq. destruct (SP q Hq) as [S|E]; [| exact E].
    destruct (SUPa q S) as (A' & n' & Hin). exists A', n'. apply hb_lb_remove. split; [exact Hin|]. intros ->. exact (S UNa). }
  eapply implF_epost_mono; [eapply (AHU_free (ov:=ov1)); eassumption|].
  intros r RNG' ms' (LE & P). split; [exact LE|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  split.
  { eapply (twins_pres_u ov1 L RNG RNG' st r LB (lb_remove p LB) (lb_remove p LB) m m' AH1 M); [| exact MK].
    intros p' A' n' Hin. split; [apply hb_lb_remove in Hin; tauto| exact Hin]. }
  exists ov1. split; [exact M| exact SUP1].
Qed.

Theorem AHU2_free_null : afree_null_stmt2 aci_I AHEAPu2.
Proof.
  unfold afree_null_stmt2. intros until tr. intros (ov0 & AH0 & SUP0) MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  destruct (mark_all_u L RNG st LB m LB ov0 AH0 (fun b H => H)) as (ov1 & AH1 & MK & SP).
  assert (SUP1 : ov_sup ov1 LB) by (intros q Hq; destruct (SP q Hq) as [S|E]; [exact (SUP0 q S)| exact E]).
  eapply evtF_mono; [eapply (AHU_free_null (ov:=ov1)); eassumption|].
  intros ms' P.
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  split.
  { eapply (twins_pres_u ov1 L RNG RNG st st LB LB LB m m' AH1 M); [| exact MK]. intros p' A' n' Hin. split; exact Hin. }
  exists ov1. split; [exact M| exact SUP1].
Qed.

Definition AIu2 (EXHW : exh_first_stmt) : AMallocIface2 :=
  {| aci := aci_I;
     AHEAP := AHEAPu2;
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AIu2_rng_mono;
     AI_perm := AIu2_perm;
     AI_frame := AIu2_frame;
     AI_frame_twin := AIu2_frame_twin;
     AI_block := AIu2_block;
     AI_block_bounds := fun L RNG st LB m b H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_block_bounds (ov:=ov) (gb:=g) L RNG st LB m b AH;
     AI_blocks_disjoint := fun L RNG st LB m b1 b2 H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_blocks_disjoint (ov:=ov) (gb:=g) L RNG st LB m b1 b2 AH;
     AI_blocks_nodup := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_blocks_nodup (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_hb_ids := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_hb_ids (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_layout := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_layout (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_relro := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_relro (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_rtcells := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_rtcells (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_malloc := AHU2_malloc EXHW;
     AI_free := AHU2_free;
     AI_free_null := AHU2_free_null |}.

End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB ARep.TwinB AHeapP.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB AFreeAll.TwinB ADeallocate.TwinB AEmbRep.TwinB AMalloc_x.TwinB ARealloc_x.TwinB AInstanceX.TwinB AInstanceU.TwinB ARepTwin.TwinB AFreeRep.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition ov_sup (ov : annOV) (LB : list ablock) : Prop :=
  forall q, @ann_ov ov q <> None -> exists A n, In (HB q A n) LB.

Definition AHEAPu2 (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m : amem) : Prop :=
  exists ov : annOV, @AHEAPu rc ov L RNG st LB m /\ ov_sup ov LB.

Lemma ov_sup_incl : forall ov LB LB', ov_sup ov LB -> (forall p A n, In (HB p A n) LB -> In (HB p A n) LB') -> ov_sup ov LB'.
Proof. intros ov LB LB' S INC q Hq. destruct (S q Hq) as (A & n & Hin). exists A, n. exact (INC _ _ _ Hin). Qed.

Lemma live_cell_u : forall (ov : annOV) L RNG st LB m p A n,
  @AHEAPu rc ov L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) (@live_bytes ov p n)]
  /\ 0x2008fff7000 <= shad A /\ shad A + granules n <= 0x10007fff8000.
Proof. intros ov L RNG st LB m p A n [g AH]. exact (AHEAP_P_live_cell ov _ L RNG st LB m p A n AH). Qed.

Lemma mark_all_u : forall L RNG st LB m (l : list ablock) (ov : annOV),
  @AHEAPu rc ov L RNG st LB m -> (forall b, In b l -> In b LB) ->
  exists ov' : annOV, @AHEAPu rc ov' L RNG st LB m
    /\ (forall p A n, In (HB p A n) l -> is_primary n = true -> exists bs, @ann_ov ov' p = Some bs /\ length bs = Z.to_nat (granules n))
    /\ (forall q, @ann_ov ov' q <> None -> @ann_ov ov q <> None \/ exists A n, In (HB q A n) l).
Proof.
  intros L RNG st LB m l ov [g AH] SUB.
  destruct (AHEAP_P_mark_all (AHI (gb:=g)) (AHI_laws (gb:=g)) L RNG st LB m l ov AH SUB) as (ov' & AH' & MK & SP).
  exists ov'. split; [exists g; exact AH'|]. split; [exact MK| exact SP].
Qed.

Lemma twin_bytes_eq_u : forall (ov : annOV) L RNG RNG' st st' LB LB' m m' p A n bs,
  @AHEAPu rc ov L RNG st LB m -> @AHEAPu rc ov L RNG' st' LB' m' -> In (HB p A n) LB -> In (HB p A n) LB' -> is_primary n = true ->
  @ann_ov ov p = Some bs -> length bs = Z.to_nat (granules n) ->
  forall i, 0 <= i < granules n -> m' (wa (shad A + i)) = m (wa (shad A + i)).
Proof.
  intros ov L RNG RNG' st st' LB LB' m m' p A n bs [g AH] [g' AH'].
  exact (twin_bytes_eq ov _ _ L RNG RNG' st st' LB LB' m m' p A n bs AH AH').
Qed.

Lemma hb_lt_u : forall (ov : annOV) L RNG st LB m p A n, @AHEAPu rc ov L RNG st LB m -> In (HB p A n) LB -> (p < a_next st)%N.
Proof. intros ov L RNG st LB m p A n [g AH]. exact (AHEAP_P_hb_lt ov _ L RNG st LB m p A n AH). Qed.

Lemma twins_pres_u : forall (ov : annOV) L RNG RNG' st st' LB LB' LB0 m m',
  @AHEAPu rc ov L RNG st LB m -> @AHEAPu rc ov L RNG' st' LB' m' ->
  (forall p A n, In (HB p A n) LB0 -> In (HB p A n) LB /\ In (HB p A n) LB') ->
  (forall p A n, In (HB p A n) LB0 -> is_primary n = true -> exists bs, @ann_ov ov p = Some bs /\ length bs = Z.to_nat (granules n)) ->
  twins_pres LB0 m m'.
Proof.
  intros ov L RNG RNG' st st' LB LB' LB0 m m' AH AH' SUB MK p A n Hin PRIM i Hi.
  destruct (MK p A n Hin PRIM) as (bs & E & LBS). destruct (SUB p A n Hin) as [H1 H2].
  exact (twin_bytes_eq_u ov L RNG RNG' st st' LB LB' m m' p A n bs AH AH' H1 H2 PRIM E LBS i Hi).
Qed.

Lemma twins_pres_ov : forall (ov : annOV) L RNG RNG' st st' LB LB' LB0 m m',
  @AHEAPu rc ov L RNG st LB m -> @AHEAPu rc ov L RNG' st' LB' m' ->
  (forall p A n, In (HB p A n) LB0 -> In (HB p A n) LB /\ In (HB p A n) LB') ->
  twins_pres LB0 m m'.
Proof.
  intros ov L RNG RNG' st st' LB LB' LB0 m m' AH AH' SUB p A n Hin PRIM i Hi. destruct (SUB p A n Hin) as [H1 H2].
  destruct (live_cell_u ov L RNG st LB m p A n AH H1 PRIM) as (C1 & LO1 & _).
  destruct (live_cell_u ov L RNG' st' LB' m' p A n AH' H2 PRIM) as (C2 & _ & _).
  assert (LBS : length (@live_bytes ov p n) = Z.to_nat (granules n)) by (destruct C1 as [[WFc _] _]; cbn in WFc; tauto).
  change (shlen (n + 7)) with (granules n) in Hi.
  rewrite (cb_overlay m (shad A) _ _ i C1 ltac:(lia) ltac:(rewrite LBS; lia)).
  rewrite (cb_overlay m' (shad A) _ _ i C2 ltac:(lia) ltac:(rewrite LBS; lia)). reflexivity.
Qed.

Lemma ov_sup_fresh : forall (ov : annOV) L RNG st LB m, @AHEAPu rc ov L RNG st LB m -> ov_sup ov LB -> @ann_ov ov (a_next st) = None.
Proof.
  intros ov L RNG st LB m AH SUP. destruct (@ann_ov ov (a_next st)) as [bs|] eqn:E; [| reflexivity]. exfalso.
  destruct (SUP (a_next st) ltac:(rewrite E; discriminate)) as (A & n & Hin).
  pose proof (hb_lt_u ov L RNG st LB m _ A n AH Hin) as LT. lia.
Qed.

Lemma AIu2_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAPu2 L RNG st LB m -> AHEAPu2 L RNG' st LB m.
Proof. intros L RNG RNG' st LB m LE (ov & [g AH] & SUP). exists ov. split; [exists g; exact (AHI_rng_mono (gb:=g) L RNG RNG' st LB m LE AH)| exact SUP]. Qed.

Lemma AIu2_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAPu2 L RNG st LB m -> AHEAPu2 L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (ov & [g AH] & SUP). exists ov. split; [exists g; exact (AHI_perm (gb:=g) L RNG st LB LB' m P AH)|].
  eapply ov_sup_incl; [exact SUP|]. intros p A n Hin. exact (Permutation_in _ P Hin).
Qed.

Lemma AIu2_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAPu2 L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
  AHEAPu2 L RNG st LB m'.
Proof. intros L RNG st LB m m' W (ov & [g AH] & SUP) MU WM CW. exists ov. split; [exists g; exact (AHI_frame (gb:=g) L RNG st LB m m' W AH MU WM CW)| exact SUP]. Qed.

Lemma AIu2_frame_top : forall L RNG st LB m m',
  AHEAPu2 L RNG st LB m -> (forall a, 0 <= a < 2 ^ 47 -> m' (wa a) = m (wa a)) -> wmono bsegs m m' -> AHEAPu2 L RNG st LB m'.
Proof. intros L RNG st LB m m' (ov & [g AH] & SUP) EQ WM. exists ov. split; [exists g; exact (AHI_frame_top (gb:=g) L RNG st LB m m' AH EQ WM)| exact SUP]. Qed.

Lemma AIu2_frame_twin : forall L RNG st LB m m' p A n,
  AHEAPu2 L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  munch [(shad A, shad A + shlen (n + 7))] m m' -> wmono bsegs m m' ->
  (forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) <> None) ->
  AHEAPu2 L RNG st LB m'.
Proof.
  intros L RNG st LB m m' p A n (ov & [g AH] & SUP) Hin PRIM MU WM RDM.
  destruct (AHEAP_P_remark1 ov (AHI (gb:=g)) (AHI_laws (gb:=g)) L RNG st LB m m' p A n AH Hin PRIM MU WM RDM) as (bs & _ & _ & AH').
  exists (ov_set ov p bs). split; [exists g; exact AH'|].
  intros q Hq. unfold ov_set in Hq. cbn [ann_ov] in Hq. destruct (N.eq_dec q p) as [EQ|NE].
  - exists A, n. rewrite EQ. exact Hin.
  - apply N.eqb_neq in NE. rewrite NE in Hq. exact (SUP q Hq).
Qed.

Lemma AIu2_block : forall L RNG st LB m p A n,
  AHEAPu2 L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX /\
  ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
  /\ (exists bs, rw_cells bsegs m (shad A) [CB (Z.to_nat (shlen (n + 7))) bs] /\ (is_primary n = false -> ablock_shadow m A n))
  /\ wr_at bsegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
  /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO)).
Proof.
  intros L RNG st LB m p A n (ov & [g AH] & SUP) Hin.
  destruct (AHI_block (ov:=ov) (gb:=g) L RNG st LB m p A n AH Hin) as (N & BR & R1 & R2 & CELL & WR & CH & AR).
  split; [exact N|]. split; [exact BR|]. split; [exact R1|]. split; [exact R2|]. split; [| split; [exact WR| split; [exact CH| exact AR]]].
  eexists. split; [exact CELL|]. intros NP. rewrite NP in CELL.
  destruct BR as (B1 & B2 & B3 & B4). apply ablk_lin in B1. pose proof atop_range as ATR.
  eapply block_shadow_of_cb; [lia | clear -B4; Z.div_mod_to_equations; lia | clear -B1; lia | clear -B3 ATR; lia | exact CELL].
Qed.

Lemma amalloc_post_lift : forall (ov1 : annOV) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms',
  @AHEAPu rc ov1 L RNG st LB m -> ov_sup ov1 LB ->
  (forall p A n, In (HB p A n) LB -> is_primary n = true -> exists bs, @ann_ov ov1 p = Some bs /\ length bs = Z.to_nat (granules n)) ->
  amalloc_post aci_I (@AHEAPu rc ov1) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms' ->
  amalloc_post2 aci_I AHEAPu2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'.
Proof.
  intros until ms'. intros AH1 SUP1 MK (LE & P). split; [exact LE|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  destruct (snd r) as [p|]; [| destruct M].
  destruct M as (A & junk & M1 & M2 & M3 & M4 & M5 & M6 & M7).
  split.
  { eapply (twins_pres_u ov1 L RNG RNG' st (fst r) LB (HB p A n :: LB) LB m m' AH1 M3); [| exact MK].
    intros p' A' n' Hin. split; [exact Hin| right; exact Hin]. }
  exists A, junk. split; [exact M1|]. split; [exact M2|].
  split. { exists ov1. split; [exact M3|]. eapply ov_sup_incl; [exact SUP1|]. intros p' A' n' Hin. right. exact Hin. }
  split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].

  destruct M3 as [g' AH3].
  assert (UNM : @ann_ov ov1 p = None).
  { destruct (@ann_ov ov1 p) as [bs|] eqn:EP; [| reflexivity]. exfalso.
    destruct (SUP1 p ltac:(rewrite EP; discriminate)) as (A' & n' & Hin).
    pose proof (AHI_hb_ids (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' AH3) as ND. cbn [hb_ids flat_map ab_kind app] in ND.
    apply NoDup_cons_iff in ND as [NI _]. apply NI. unfold hb_ids. apply in_flat_map. exists (HB p A' n'). split; [exact Hin| left; reflexivity]. }
  destruct (AHI_block (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' p A n AH3 ltac:(left; reflexivity)) as (N & BR & _ & _ & CELL & _).
  rewrite (live_bytes_none p n UNM) in CELL. replace (if is_primary n then block_shadow_bytes n else block_shadow_bytes n) with (block_shadow_bytes n) in CELL by (destruct (is_primary n); reflexivity).
  destruct BR as (B1 & B2 & B3 & B4). apply ablk_lin in B1. pose proof atop_range as ATR.
  eapply block_shadow_of_cb; [lia | clear -B4; Z.div_mod_to_equations; lia | clear -B1; lia | clear -B3 ATR; lia | exact CELL].
Qed.

Lemma mark_sup_u : forall L RNG st LB m (ov0 : annOV), @AHEAPu rc ov0 L RNG st LB m -> ov_sup ov0 LB ->
  exists ov1 : annOV, @AHEAPu rc ov1 L RNG st LB m /\ ov_sup ov1 LB
    /\ (forall p A n, In (HB p A n) LB -> is_primary n = true -> exists bs, @ann_ov ov1 p = Some bs /\ length bs = Z.to_nat (granules n)).
Proof.
  intros L RNG st LB m ov0 AH0 SUP0.
  destruct (mark_all_u L RNG st LB m LB ov0 AH0 (fun b H => H)) as (ov1 & AH1 & MK & SP).
  exists ov1. split; [exact AH1|]. split; [| exact MK].
  intros q Hq. destruct (SP q Hq) as [S|E]; [exact (SUP0 q S)| exact E].
Qed.

Lemma amalloc_null_lift : forall (ov1 : annOV) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m st' RNG' ms',
  @AHEAPu rc ov1 L RNG st LB m -> ov_sup ov1 LB ->
  (fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres_e aci_I LB (bv_unsigned sp) m m'
      /\ @AHEAPu rc ov1 L RNG' st' LB m'
      /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)]) ->
  amalloc_null_post2 aci_I AHEAPu2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo m st' RNG' ms'.
Proof.
  intros until ms'. intros AH1 SUP1 (LE & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M & ER).
  split; [exact LE|].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  split; [exact (twins_pres_ov ov1 L RNG RNG' st st' LB LB LB m m' AH1 M (fun p A n H => conj H H))|].
  split; [exists ov1; split; [exact M| exact SUP1]| exact ER].
Qed.

Section X.
Hypothesis EXHW : exh_first_stmt.
Theorem AHU2_malloc : amalloc_stmt2x aci_I AHEAPu2.
Proof.
  unfold amalloc_stmt2x. intros until RESV. intros (ov0 & AH0 & SUP0) MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK FCB C6M CAPB ERRC.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  pose proof (ov_sup_fresh ov1 L RNG st LB m AH1 SUP1) as OVF.
  eapply implF_epost_mono; [eapply (AHU_malloc_h (ov:=ov1) EXHW); eassumption|].
  intros [st' [p|]] RNG' ms'; unfold amalloc_post_h, amalloc_post2x; cbn [snd fst]; intros P.
  - eapply (amalloc_post_lift ov1); [exact AH1| exact SUP1| exact MK| exact P].
  - eapply (amalloc_null_lift ov1); [exact AH1| exact SUP1| exact P].
Qed.
End X.

Lemma unmark_u : forall (ov : annOV) L RNG st LB m p A n,
  @AHEAPu rc ov L RNG st LB m -> ov_sup ov LB -> In (HB p A n) LB -> ablock_shadow m A n ->
  exists ov' : annOV, @AHEAPu rc ov' L RNG st LB m /\ ov_sup ov' LB /\ @ann_ov ov' p = None.
Proof.
  intros ov L RNG st LB m p A n [g AH] SUP Hin CAN.
  destruct (is_primary n) eqn:PRIM.
  - exists (ov_unset ov p). split; [exists g; exact (AHEAP_P_unmark ov _ L RNG st LB m p A n AH Hin PRIM CAN)|].
    split; [| unfold ov_unset; cbn [ann_ov]; rewrite N.eqb_refl; reflexivity].
    intros q Hq. unfold ov_unset in Hq. cbn [ann_ov] in Hq. destruct (N.eqb q p); [congruence| exact (SUP q Hq)].
  -
    destruct (AHI_chunk (ov:=ov) (gb:=g) L RNG st LB m p A n AH Hin) as (ch & LV & _ & _ & KO).
    exists (ov_unset ov p). split.
    + exists g. apply AHEAP_P_unset_nonprim; [exact AH|]. intros c' n' E. rewrite E in LV. injection LV as <-. cbn in KO. congruence.
    + split; [| unfold ov_unset; cbn [ann_ov]; rewrite N.eqb_refl; reflexivity].
      intros q Hq. unfold ov_unset in Hq. cbn [ann_ov] in Hq. destruct (N.eqb q p); [congruence| exact (SUP q Hq)].
Qed.

Lemma hb_lb_remove : forall p q A n LB, In (HB q A n) (lb_remove p LB) <-> In (HB q A n) LB /\ q <> p.
Proof.
  intros p q A n LB. rewrite AFreeRep.TwinB.In_lb_remove. cbn [ab_kind]. split; intros [H1 H2]; (split; [exact H1|]); intros E; apply H2; congruence.
Qed.

Theorem AHU2_free : afree_stmt2 aci_I AHEAPu2.
Proof.
  unfold afree_stmt2. intros until tr. intros (ov0 & AH0 & SUP0) HIN CAN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.

  destruct (unmark_u ov0 L RNG st LB m p A n AH0 SUP0 HIN CAN) as (ova & AHa & SUPa & UNa).
  destruct (mark_all_u L RNG st LB m (lb_remove p LB) ova AHa ltac:(intros b Hb; apply AFreeRep.TwinB.In_lb_remove in Hb; tauto)) as (ov1 & AH1 & MK & SP).
  assert (SUP1 : ov_sup ov1 (lb_remove p LB)).
  { intros q Hq. destruct (SP q Hq) as [S|E]; [| exact E].
    destruct (SUPa q S) as (A' & n' & Hin). exists A', n'. apply hb_lb_remove. split; [exact Hin|]. intros ->. exact (S UNa). }
  eapply implF_epost_mono; [eapply (AHU_free (ov:=ov1)); eassumption|].
  intros r RNG' ms' (LE & P). split; [exact LE|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  split.
  { eapply (twins_pres_u ov1 L RNG RNG' st r LB (lb_remove p LB) (lb_remove p LB) m m' AH1 M); [| exact MK].
    intros p' A' n' Hin. split; [apply hb_lb_remove in Hin; tauto| exact Hin]. }
  exists ov1. split; [exact M| exact SUP1].
Qed.

Theorem AHU2_free_null : afree_null_stmt2 aci_I AHEAPu2.
Proof.
  unfold afree_null_stmt2. intros until tr. intros (ov0 & AH0 & SUP0) MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  destruct (mark_all_u L RNG st LB m LB ov0 AH0 (fun b H => H)) as (ov1 & AH1 & MK & SP).
  assert (SUP1 : ov_sup ov1 LB) by (intros q Hq; destruct (SP q Hq) as [S|E]; [exact (SUP0 q S)| exact E]).
  eapply evtF_mono; [eapply (AHU_free_null (ov:=ov1)); eassumption|].
  intros ms' P.
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  split.
  { eapply (twins_pres_u ov1 L RNG RNG st st LB LB LB m m' AH1 M); [| exact MK]. intros p' A' n' Hin. split; exact Hin. }
  exists ov1. split; [exact M| exact SUP1].
Qed.

Definition AIu2 (EXHW : exh_first_stmt) : AMallocIface2 :=
  {| aci := aci_I;
     AHEAP := AHEAPu2;
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AIu2_rng_mono;
     AI_perm := AIu2_perm;
     AI_frame := AIu2_frame;
     AI_frame_twin := AIu2_frame_twin;
     AI_block := AIu2_block;
     AI_block_bounds := fun L RNG st LB m b H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_block_bounds (ov:=ov) (gb:=g) L RNG st LB m b AH;
     AI_blocks_disjoint := fun L RNG st LB m b1 b2 H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_blocks_disjoint (ov:=ov) (gb:=g) L RNG st LB m b1 b2 AH;
     AI_blocks_nodup := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_blocks_nodup (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_hb_ids := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_hb_ids (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_layout := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_layout (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_relro := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_relro (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_rtcells := fun L RNG st LB m H => let '(ex_intro _ ov (conj (ex_intro _ g AH) _)) := H in AHI_rtcells (ov:=ov) (gb:=g) L RNG st LB m AH;
     AI_malloc := AHU2_malloc EXHW;
     AI_free := AHU2_free;
     AI_free_null := AHU2_free_null |}.

End CANSEC1.
End TwinB.
