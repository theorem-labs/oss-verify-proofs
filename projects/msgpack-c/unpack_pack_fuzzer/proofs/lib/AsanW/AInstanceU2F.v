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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ARep AHeapP AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AInstance AInstanceM AInstanceF AFreeAll ADeallocate AEmbRep AMalloc_x ARealloc_x AInstanceX AInstanceU ARepTwin AFreeRep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AAlignedPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.AAlignedPG. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AInstanceA16 AInstanceUF AInstanceUT F_ahnr AFake_hnrP AFake_relP AFake_tlsP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsgaG. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm1g. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1_16. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aaligned_iseg F_arealloc_iseg AFake_cnt. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import FsKit ARepExt RtCells AFake_gcP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Section Shapes.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition aaligned16_stmt2x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary16 n = true -> n mod 16 = 0 ->
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AALIGNED_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AALIGNED_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (aaligned16x ATOP RESV st n))
        (epostF (amalloc_post2x CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom asegs)).

Definition arealloc_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ twins_pres (lb_remove p LB) m m'
    /\ match snd r with
       | None => False
       | Some q => exists UB (src junk : list byte),
           a0 = Z_to_bv 64 UB /\ ablock_range UB n
           /\ AHEAP L RNG' (fst r) (HB q UB n :: lb_remove p LB) m'

           /\ bytes_at asegs m A src /\ length src = Z.to_nat (Z.min n nold)
           /\ rw_cells asegs m' UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) junk]
           /\ rng RNG' UB n /\ rng RNG' (shad UB) (shlen (n + 7))
           /\ ablock_shadow m' UB n
       end.

Definition arealloc_post2x (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => arealloc_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m r RNG' ms'
    | None => amalloc_null_post2 CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo m (fst r) RNG' ms'
    end.

Definition arealloc_stmt2x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m -> In (HB p A nold) LB ->
  ablock_shadow m A nold ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AREALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AREALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (arealloc RESV st p n))
        (epostF (arealloc_post2x L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom asegs)).

End Shapes.

Section X.
Hypothesis EXHW : exh_first_stmt.
Theorem AHU2_aligned16 : aaligned16_stmt2x aci_I AHEAPu2.
Proof.
  unfold aaligned16_stmt2x. intros until RESV. intros PRIM N16 (ov0 & AH0 & SUP0). intros.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  pose proof (ov_sup_fresh ov1 L RNG st LB m AH1 SUP1) as OVF.
  eapply implF_epost_mono; [eapply (AHU_aligned16_h (ov:=ov1) EXHW); eassumption|].
  intros [st' [q|]] RNG' ms'; unfold amalloc_post_h, amalloc_post2x; cbn [snd fst]; intros P.
  - eapply (amalloc_post_lift ov1); [exact AH1| exact SUP1| exact MK| exact P].
  - eapply (amalloc_null_lift ov1); [exact AH1| exact SUP1| exact P].
Qed.

Theorem AHU2_realloc : arealloc_stmt2x aci_I AHEAPu2.
Proof.
  unfold arealloc_stmt2x. intros until RESV. intros (ov0 & AH0 & SUP0) HIN CAN. intros.
  destruct (unmark_u ov0 L RNG st LB m p A nold AH0 SUP0 HIN CAN) as (ova & AHa & SUPa & UNa).
  destruct (mark_all_u L RNG st LB m (lb_remove p LB) ova AHa ltac:(intros b Hb; apply AFreeRep.In_lb_remove in Hb; tauto)) as (ov1 & AH1 & MK & SP).
  assert (SUPr : ov_sup ov1 (lb_remove p LB)).
  { intros q Hq. destruct (SP q Hq) as [S|E]; [| exact E].
    destruct (SUPa q S) as (A' & n' & Hin). exists A', n'. apply hb_lb_remove. split; [exact Hin|]. intros ->. exact (S UNa). }
  assert (SUP1 : ov_sup ov1 LB).
  { intros q Hq. destruct (SUPr q Hq) as (A' & n' & Hin). exists A', n'. apply hb_lb_remove in Hin. tauto. }
  pose proof (ov_sup_fresh ov1 L RNG st LB m AH1 SUP1) as OVF.
  eapply implF_epost_mono; [eapply (AHU_realloc_h (ov:=ov1) EXHW); eassumption|].
  intros [st' [q0|]] RNG' ms'; unfold arealloc_post_h, arealloc_post2x; cbn [snd fst].
  2: { intros P. eapply (amalloc_null_lift ov1); [exact AH1| exact SUP1| exact P]. }
  set (r := (st', Some q0)). intros (LE & P). split; [exact LE|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  destruct (snd r) as [q|]; [| destruct M].
  destruct M as (UB & src & junk & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split.
  { eapply (twins_pres_u ov1 L RNG RNG' st (fst r) LB (HB q UB n :: lb_remove p LB) (lb_remove p LB) m m' AH1 M3); [| exact MK].
    intros p' A' n' Hin. split; [apply hb_lb_remove in Hin; tauto| right; exact Hin]. }
  exists UB, src, junk. split; [exact M1|]. split; [exact M2|].
  split. { exists ov1. split; [exact M3|]. eapply ov_sup_incl; [exact SUPr|]. intros p' A' n' Hin. right. exact Hin. }
  split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|]. split; [exact M8|].
  destruct M3 as [g' AH3].
  assert (UNM : @ann_ov ov1 q = None).
  { destruct (@ann_ov ov1 q) as [bs|] eqn:EP; [| reflexivity]. exfalso.
    destruct (SUPr q ltac:(rewrite EP; discriminate)) as (A' & n' & Hin).
    pose proof (AHI_hb_ids (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' AH3) as ND. cbn [hb_ids flat_map ab_kind app] in ND.
    apply NoDup_cons_iff in ND as [NI _]. apply NI. unfold hb_ids. apply in_flat_map. exists (HB q A' n'). split; [exact Hin| left; reflexivity]. }
  destruct (AHI_block (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' q UB n AH3 ltac:(left; reflexivity)) as (N & BR & _ & _ & CELL & _).
  rewrite (live_bytes_none q n UNM) in CELL. replace (if is_primary n then block_shadow_bytes n else block_shadow_bytes n) with (block_shadow_bytes n) in CELL by (destruct (is_primary n); reflexivity).
  destruct BR as (B1 & B2 & B3 & B4). apply ablk_lin in B1. pose proof atop_range as ATR.
  eapply block_shadow_of_cb; [lia | clear -B4; Z.div_mod_to_equations; lia | clear -B1; lia | clear -B3 ATR; lia | exact CELL].
Qed.
End X.

Definition smU_post2 (c n : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (LBk : list ablock) (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres aci_I LBk (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAPu2 L RNG st (mkABlock (ABFake c) F n :: LBk) m'
    /\ (forall b, In b LBk -> In b LB) /\ (forall b, In b LB -> fk_live L m sp b -> In b LBk)
    /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) (Z.to_nat (n / 64)))
    /\ rng RNG F n /\ rng RNG (shad F) (n / 8)
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Definition smU_stmt2 (c n nfr entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAPu2 L RNG st LB m ->
  Z.of_nat (fk_count c LB) < nfr ->
  (forall c' F n', In (mkABlock (ABFake c') F n') LB -> c' <= 2) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (smU_post2 c n L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma smU_lift : forall c n nfr entry, (forall ov : annOV, @smU_stmt rc ov c n nfr entry) -> smU_stmt2 c n nfr entry.
Proof.
  intros c n nfr entry TH. unfold smU_stmt2. intros until lo. intros (ov0 & AH0 & SUP0). intros.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  eapply evtF_mono; [eapply (TH ov1); eassumption|].
  intros ms' (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & LBk & j0 & j1 & j2 & junk
              & E & MI' & ST' & PR & AH' & KS & KL & REST).
  exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', LBk, j0, j1, j2, junk.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  assert (HK : forall p A n0, In (HB p A n0) LB -> In (HB p A n0) LBk) by (intros p A n0 Hin; apply KL; [exact Hin| apply fk_live_heap]).
  split.
  { eapply (twins_pres_u ov1 L RNG RNG st st LB _ LB m m' AH1 AH'); [| exact MK].
    intros p A n0 Hin. split; [exact Hin| right; exact (HK p A n0 Hin)]. }
  split. { exists ov1. split; [exact AH'|]. eapply ov_sup_incl; [exact SUP1|]. intros p A n0 Hin. right. exact (HK p A n0 Hin). }
  split; [exact KS|]. split; [exact KL| exact REST].
Qed.

Theorem AHU2_stack_malloc_0 : smU_stmt2 0 64 16384 AFake_sm0.AFake_sm0.ASTKMALLOC0.
Proof. apply smU_lift. intros ov. exact (@AHU_stack_malloc_0 rc ov). Qed.
Theorem AHU2_stack_malloc_1 : smU_stmt2 1 128 8192 AFake_sm0.AFake_sm1g.ASTKMALLOC1.
Proof. apply smU_lift. intros ov. exact (@AHU_stack_malloc_1 rc ov). Qed.
Theorem AHU2_stack_malloc_2 : smU_stmt2 2 256 4096 AFake_sm0.AFake_sm2.ASTKMALLOC2.
Proof. apply smU_lift. intros ov. exact (@AHU_stack_malloc_2 rc ov). Qed.

Definition hnrU_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ AHEAPu2 L RNG st LB m'
    /\ twins_pres LB m m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr aci_I LB (bv_unsigned sp) a ->
          ~ (shad (hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None))
    /\ rw_cells asegs m' (shad (hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - hnr_bottom sp))))].

Theorem AHU2_hnr : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAPu2 L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HNR_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (shad (hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  rng RNG (shad (hnr_bottom sp)) (shlen (al_top L - hnr_bottom sp)) ->
  evtF asegs RNG (hnrU_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHNR) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros (ov0 & AH0 & SUP0). intros.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  eapply evtF_mono; [eapply (AHU_hnr (ov:=ov1)); eassumption|].
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & AH' & REST).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists ov1; split; [exact AH'| exact SUP1]|].
  split; [| exact REST].
  eapply (twins_pres_u ov1 L RNG RNG st st LB LB LB m m' AH1 AH'); [| exact MK]. intros p A n0 Hin. split; exact Hin.
Qed.

Theorem AHU2_fake_release : forall L RNG st LB m c F n,
  AHEAPu2 L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  AHEAPu2 L RNG st (fk_rel c F LB) (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m c F n (ov & AH & SUP) Hb. exists ov. split; [exact (AHU_fake_release (ov:=ov) L RNG st LB m c F n AH Hb)|].
  eapply ov_sup_incl; [exact SUP|]. intros p A n0 Hin. apply AFake_relP.fk_rel_In. split; [exact Hin| reflexivity].
Qed.

Definition tlsgaU_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m'
    /\ aheap_pres aci_I LB (bv_unsigned sp) m m'
    /\ AHEAPu2 L RNG st LB m'.

Definition tlsgaU_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAPu2 L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF asegs RNG (tlsgaU_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).

Theorem AHU2_tlsga : tlsgaU_stmt2.
Proof.
  unfold tlsgaU_stmt2. intros until A. intros (ov0 & AH0 & SUP0). intros.
  eapply evtF_mono; [eapply (AHU_tlsga (ov:=ov0)); eassumption|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & MU & WM & PR & AH').
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MU|]. split; [exact WM|]. split; [exact PR|]. exists ov0. split; [exact AH'| exact SUP0].
Qed.
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

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB AFreeAll.TwinB ADeallocate.TwinB AEmbRep.TwinB AMalloc_x.TwinB ARealloc_x.TwinB AInstanceX.TwinB AInstanceU.TwinB ARepTwin.TwinB AFreeRep.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.TwinB.AAlignedPG. Import AInstanceA16.TwinB AInstanceUF.TwinB AInstanceUT.TwinB F_ahnr.TwinB AFake_hnrP.TwinB AFake_relP.TwinB AFake_tlsP.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsgaG.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm1g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1_16. Import F_aaligned_iseg.TwinB F_arealloc_iseg.TwinB AFake_cnt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import FsKit.TwinB ARepExt.TwinB RtCells.TwinB AFake_gcP.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Section Shapes.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition aaligned16_stmt2x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary16 n = true -> n mod 16 = 0 ->
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AALIGNED_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AALIGNED_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (aaligned16x ATOP RESV st n))
        (epostF (amalloc_post2x CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom bsegs)).

Definition arealloc_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ twins_pres (lb_remove p LB) m m'
    /\ match snd r with
       | None => False
       | Some q => exists UB (src junk : list byte),
           a0 = Z_to_bv 64 UB /\ ablock_range UB n
           /\ AHEAP L RNG' (fst r) (HB q UB n :: lb_remove p LB) m'

           /\ bytes_at bsegs m A src /\ length src = Z.to_nat (Z.min n nold)
           /\ rw_cells bsegs m' UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) junk]
           /\ rng RNG' UB n /\ rng RNG' (shad UB) (shlen (n + 7))
           /\ ablock_shadow m' UB n
       end.

Definition arealloc_post2x (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => arealloc_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m r RNG' ms'
    | None => amalloc_null_post2 CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo m (fst r) RNG' ms'
    end.

Definition arealloc_stmt2x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m -> In (HB p A nold) LB ->
  ablock_shadow m A nold ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AREALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AREALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (arealloc RESV st p n))
        (epostF (arealloc_post2x L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom bsegs)).

End Shapes.

Section X.
Hypothesis EXHW : exh_first_stmt.
Theorem AHU2_aligned16 : aaligned16_stmt2x aci_I AHEAPu2.
Proof.
  unfold aaligned16_stmt2x. intros until RESV. intros PRIM N16 (ov0 & AH0 & SUP0). intros.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  pose proof (ov_sup_fresh ov1 L RNG st LB m AH1 SUP1) as OVF.
  eapply implF_epost_mono; [eapply (AHU_aligned16_h (ov:=ov1) EXHW); eassumption|].
  intros [st' [q|]] RNG' ms'; unfold amalloc_post_h, amalloc_post2x; cbn [snd fst]; intros P.
  - eapply (amalloc_post_lift ov1); [exact AH1| exact SUP1| exact MK| exact P].
  - eapply (amalloc_null_lift ov1); [exact AH1| exact SUP1| exact P].
Qed.

Theorem AHU2_realloc : arealloc_stmt2x aci_I AHEAPu2.
Proof.
  unfold arealloc_stmt2x. intros until RESV. intros (ov0 & AH0 & SUP0) HIN CAN. intros.
  destruct (unmark_u ov0 L RNG st LB m p A nold AH0 SUP0 HIN CAN) as (ova & AHa & SUPa & UNa).
  destruct (mark_all_u L RNG st LB m (lb_remove p LB) ova AHa ltac:(intros b Hb; apply AFreeRep.TwinB.In_lb_remove in Hb; tauto)) as (ov1 & AH1 & MK & SP).
  assert (SUPr : ov_sup ov1 (lb_remove p LB)).
  { intros q Hq. destruct (SP q Hq) as [S|E]; [| exact E].
    destruct (SUPa q S) as (A' & n' & Hin). exists A', n'. apply hb_lb_remove. split; [exact Hin|]. intros ->. exact (S UNa). }
  assert (SUP1 : ov_sup ov1 LB).
  { intros q Hq. destruct (SUPr q Hq) as (A' & n' & Hin). exists A', n'. apply hb_lb_remove in Hin. tauto. }
  pose proof (ov_sup_fresh ov1 L RNG st LB m AH1 SUP1) as OVF.
  eapply implF_epost_mono; [eapply (AHU_realloc_h (ov:=ov1) EXHW); eassumption|].
  intros [st' [q0|]] RNG' ms'; unfold arealloc_post_h, arealloc_post2x; cbn [snd fst].
  2: { intros P. eapply (amalloc_null_lift ov1); [exact AH1| exact SUP1| exact P]. }
  set (r := (st', Some q0)). intros (LE & P). split; [exact LE|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & PR & M).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  destruct (snd r) as [q|]; [| destruct M].
  destruct M as (UB & src & junk & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split.
  { eapply (twins_pres_u ov1 L RNG RNG' st (fst r) LB (HB q UB n :: lb_remove p LB) (lb_remove p LB) m m' AH1 M3); [| exact MK].
    intros p' A' n' Hin. split; [apply hb_lb_remove in Hin; tauto| right; exact Hin]. }
  exists UB, src, junk. split; [exact M1|]. split; [exact M2|].
  split. { exists ov1. split; [exact M3|]. eapply ov_sup_incl; [exact SUPr|]. intros p' A' n' Hin. right. exact Hin. }
  split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|]. split; [exact M8|].
  destruct M3 as [g' AH3].
  assert (UNM : @ann_ov ov1 q = None).
  { destruct (@ann_ov ov1 q) as [bs|] eqn:EP; [| reflexivity]. exfalso.
    destruct (SUPr q ltac:(rewrite EP; discriminate)) as (A' & n' & Hin).
    pose proof (AHI_hb_ids (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' AH3) as ND. cbn [hb_ids flat_map ab_kind app] in ND.
    apply NoDup_cons_iff in ND as [NI _]. apply NI. unfold hb_ids. apply in_flat_map. exists (HB q A' n'). split; [exact Hin| left; reflexivity]. }
  destruct (AHI_block (ov:=ov1) (gb:=g') L RNG' (fst r) _ m' q UB n AH3 ltac:(left; reflexivity)) as (N & BR & _ & _ & CELL & _).
  rewrite (live_bytes_none q n UNM) in CELL. replace (if is_primary n then block_shadow_bytes n else block_shadow_bytes n) with (block_shadow_bytes n) in CELL by (destruct (is_primary n); reflexivity).
  destruct BR as (B1 & B2 & B3 & B4). apply ablk_lin in B1. pose proof atop_range as ATR.
  eapply block_shadow_of_cb; [lia | clear -B4; Z.div_mod_to_equations; lia | clear -B1; lia | clear -B3 ATR; lia | exact CELL].
Qed.
End X.

Definition smU_post2 (c n : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (LBk : list ablock) (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres aci_I LBk (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAPu2 L RNG st (mkABlock (ABFake c) F n :: LBk) m'
    /\ (forall b, In b LBk -> In b LB) /\ (forall b, In b LB -> fk_live L m sp b -> In b LBk)
    /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) (Z.to_nat (n / 64)))
    /\ rng RNG F n /\ rng RNG (shad F) (n / 8)
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Definition smU_stmt2 (c n nfr entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAPu2 L RNG st LB m ->
  Z.of_nat (fk_count c LB) < nfr ->
  (forall c' F n', In (mkABlock (ABFake c') F n') LB -> c' <= 2) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (smU_post2 c n L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma smU_lift : forall c n nfr entry, (forall ov : annOV, @smU_stmt rc ov c n nfr entry) -> smU_stmt2 c n nfr entry.
Proof.
  intros c n nfr entry TH. unfold smU_stmt2. intros until lo. intros (ov0 & AH0 & SUP0). intros.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  eapply evtF_mono; [eapply (TH ov1); eassumption|].
  intros ms' (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & LBk & j0 & j1 & j2 & junk
              & E & MI' & ST' & PR & AH' & KS & KL & REST).
  exists F, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', LBk, j0, j1, j2, junk.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR|].
  assert (HK : forall p A n0, In (HB p A n0) LB -> In (HB p A n0) LBk) by (intros p A n0 Hin; apply KL; [exact Hin| apply fk_live_heap]).
  split.
  { eapply (twins_pres_u ov1 L RNG RNG st st LB _ LB m m' AH1 AH'); [| exact MK].
    intros p A n0 Hin. split; [exact Hin| right; exact (HK p A n0 Hin)]. }
  split. { exists ov1. split; [exact AH'|]. eapply ov_sup_incl; [exact SUP1|]. intros p A n0 Hin. right. exact (HK p A n0 Hin). }
  split; [exact KS|]. split; [exact KL| exact REST].
Qed.

Theorem AHU2_stack_malloc_0 : smU_stmt2 0 64 16384 AFake_sm0.TwinB.AFake_sm0.ASTKMALLOC0.
Proof. apply smU_lift. intros ov. exact (@AHU_stack_malloc_0 rc ov). Qed.
Theorem AHU2_stack_malloc_1 : smU_stmt2 1 128 8192 AFake_sm0.TwinB.AFake_sm1g.ASTKMALLOC1.
Proof. apply smU_lift. intros ov. exact (@AHU_stack_malloc_1 rc ov). Qed.
Theorem AHU2_stack_malloc_2 : smU_stmt2 2 256 4096 AFake_sm0.TwinB.AFake_sm2.ASTKMALLOC2.
Proof. apply smU_lift. intros ov. exact (@AHU_stack_malloc_2 rc ov). Qed.

Definition hnrU_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AHEAPu2 L RNG st LB m'
    /\ twins_pres LB m m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr aci_I LB (bv_unsigned sp) a ->
          ~ (shad (hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None))
    /\ rw_cells bsegs m' (shad (hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - hnr_bottom sp))))].

Theorem AHU2_hnr : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAPu2 L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HNR_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m (shad (hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  rng RNG (shad (hnr_bottom sp)) (shlen (al_top L - hnr_bottom sp)) ->
  evtF bsegs RNG (hnrU_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHNR) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros (ov0 & AH0 & SUP0). intros.
  destruct (mark_sup_u L RNG st LB m ov0 AH0 SUP0) as (ov1 & AH1 & SUP1 & MK).
  eapply evtF_mono; [eapply (AHU_hnr (ov:=ov1)); eassumption|].
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & AH' & REST).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists ov1; split; [exact AH'| exact SUP1]|].
  split; [| exact REST].
  eapply (twins_pres_u ov1 L RNG RNG st st LB LB LB m m' AH1 AH'); [| exact MK]. intros p A n0 Hin. split; exact Hin.
Qed.

Theorem AHU2_fake_release : forall L RNG st LB m c F n,
  AHEAPu2 L RNG st LB m -> In (mkABlock (ABFake c) F n) LB ->
  AHEAPu2 L RNG st (fk_rel c F LB) (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m c F n (ov & AH & SUP) Hb. exists ov. split; [exact (AHU_fake_release (ov:=ov) L RNG st LB m c F n AH Hb)|].
  eapply ov_sup_incl; [exact SUP|]. intros p A n0 Hin. apply AFake_relP.TwinB.fk_rel_In. split; [exact Hin| reflexivity].
Qed.

Definition tlsgaU_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m'
    /\ aheap_pres aci_I LB (bv_unsigned sp) m m'
    /\ AHEAPu2 L RNG st LB m'.

Definition tlsgaU_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAPu2 L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF bsegs RNG (tlsgaU_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom bsegs)).

Theorem AHU2_tlsga : tlsgaU_stmt2.
Proof.
  unfold tlsgaU_stmt2. intros until A. intros (ov0 & AH0 & SUP0). intros.
  eapply evtF_mono; [eapply (AHU_tlsga (ov:=ov0)); eassumption|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MI' & ST' & MU & WM & PR & AH').
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MU|]. split; [exact WM|]. split; [exact PR|]. exists ov0. split; [exact AH'| exact SUP0].
Qed.
End CANSEC1.
End TwinB.
