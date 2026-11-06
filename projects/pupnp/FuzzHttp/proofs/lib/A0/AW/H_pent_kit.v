(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr Agree SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_presp_B.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjA HCount HObjK HObjF H_freelist H_ListAddTail H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X H_vfm_GX
     H_match_A H_match_X H_UpnpPrintf H_membuffer_delete H2KitA HPrepA H_hlist_view H_phdr_seg H_phdr H_pent_seg H_pent_seg2.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation hdr := (hdr FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition gstA (L : list (Z * Z)) (m : mem) : Prop := Forall (fun xn : Z * Z => shw m (fst xn) (snd xn)) L.
Definition germ_WA (P : Z) (hs : list hdr) : list ivl :=
  ((P + 384, P + 400) :: (P + 440, P + 480) :: (ERRNO_A, ERRNO_A + 4) :: map (fun h => (vA FI AI h, vA FI AI h + (vcap FI AI h + 1))) hs)%Z.
Definition germ_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (lo P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X A cur err hack pos entp csz : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI) (r err' hack' pos' entp' clen' : Z) (ev' : word),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV (germ_WA P hs)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fkeep FI (germ_WA P hs) st m m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ p_ent m' P (wz (A + cur)) (wz 0) /\ p_ctl m' P err' hack' pos' entp' clen' csz cur /\ p_hlist FI AI m' P ns hs X
    /\ clow canary ev' m' /\ rw_cells asegs m' INITWASCALLED_A [C1 (Z_to_bv 8 0)]
    /\ ( (r = 0 /\ pos' = 4 /\ entp' = entp /\ err' = err /\ hack' = hack)
       \/ (r = 6 /\ pos' = pos /\ 2 <= entp' <= 4 /\ err' = err /\ hack' = hack)
       \/ (r = 3 /\ pos' = pos /\ entp' = entp /\ err' = 411) ).
Definition germ_stmt_A (GST : mem -> Prop) : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI)
         (P lo cur A len cap : Z) (okm : option K) (bs : list byte) (ns : list (BLK * Z)) (hs : list hdr) (X : Z)
         (meth isreq maj min rm sc err hack pos entp clen csz esp : Z) (eb el ev canary : word),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st (wz A0_TP) 2 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16384 -> q mod 16 = 0 -> q + 64 <= 2^47 -> mem_inv asegs m ->
  lb (fs_live FI st) P 504 -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  bsub FI AI (hl_blocks FI AI ns hs) LB -> NoDup (map blk_id (hl_blocks FI AI ns hs)) ->
  p_meth m P meth -> p_rs m P rm sc -> p_ver m P isreq maj min -> p_hlist FI AI m P ns hs X -> X <= 2^27 + 64 ->
  p_ent m P eb el -> p_msg FI AI m LB P A len cap okm bs -> p_ctl m P err hack pos entp clen csz esp -> p_scan m P cur -> 0 <= cur <= len ->
  clow canary ev m -> shw m ERRNO_A 4 -> rw_cells asegs m INITWASCALLED_A [C1 (Z_to_bv 8 0)] -> GST m ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  a0 = wz P ->
  evt asegs (germ_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo P ns hs X A cur err hack pos entp csz canary m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz 0x89068) fc None m (seg_rom asegs)).

Definition pe_meas0 (gmax entp : Z) (el : word) : Z :=
  if (entp =? 1) then 2 * gmax + 4
  else if (entp =? 3) then 2 * (gmax - bv_unsigned el) + 3
  else if (entp =? 5) then 2 * (gmax - bv_unsigned el) + 2
  else 0.
Inductive edel1 : Z -> BL -> Z -> BL -> Prop :=
| ed_del : forall N (LB : BL) (k k' : K) A A' c c', In (k, A, c + 1) LB -> 0 <= c' <= c ->
    edel1 N LB (N + nsec1 (c' + 1)) ((k', A', c' + 1) :: lb_remove (am_K_eqb FI AI) k LB).
Inductive edels : Z -> Z -> BL -> Z -> BL -> Prop :=
| eds_nil : forall N LB, edels 0 N LB N LB
| eds_cons : forall k N LB N1 LB1 N2 LB2, edel1 N LB N1 LB1 -> edels k N1 LB1 N2 LB2 -> edels (k + 1) N LB N2 LB2.

Inductive esteps : Z -> Z -> Z -> BL -> Z -> BL -> Prop :=
| ess_nil : forall N LB, esteps 0 0 N LB N LB
| ess_del : forall k d N LB N1 LB1 N2 LB2, edel1 N LB N1 LB1 -> esteps k d N1 LB1 N2 LB2 -> esteps (k + 1) d N LB N2 LB2
| ess_hdr : forall k d d1 N LB N1 LB1 N2 LB2, H_phdr.hlines FI AI d1 N LB N1 LB1 -> esteps k d N1 LB1 N2 LB2 -> esteps k (d1 + d) N LB N2 LB2.

Definition ebud (M c G : Z) (s : PS) (LB : BL) : Prop :=
  forall k N1 LB1 (s1 : PS), edels k (am_nsec FI AI s) LB N1 LB1 -> 0 <= k <= M -> am_nsec FI AI s1 = N1 -> H_phdr.hbud FI AI c G s1 LB1.

Definition ent_okA (gmax entp cur esp csz : Z) (elw : word) : Prop :=
  (2 <= entp -> esp <= cur)
  /\ (entp = 3 \/ entp = 5 -> exists elen, elw = wz elen /\ 0 <= elen <= gmax)
  /\ (entp = 5 -> 1 <= csz <= gmax /\ csz < 2^31).

Definition pent_WA (P : Z) : list ivl := [(P + 4, P + 8); (P + 288, P + 344); (P + 384, P + 432); (P + 440, P + 480); (P + 488, P + 496); (ERRNO_A, ERRNO_A + 4)]%Z.

Definition pent_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LB LBK : BL) (P lo isreq maj min rm sc gmax Mx cx HSx PHx NBx : Z) (canary : word) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI)
                           (r cur' A' len' cap' : Z) (okm' : option K) (bs' : list byte) (eb' el' : word)
                           (err' hack' pos' entp' clen' csz' esp' X' meth' : Z) (ns' : list (BLK * Z)) (hs' : list hdr),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st' m' /\ fs_live FI st' = fs_live FI st
    /\ apxF FI AI (pent_WA P) LBK q st m m'
    /\ RHEAP_A FI AI s' LB' m'
    /\ bsub FI AI (hl_blocks FI AI ns' hs' ++ okbA FI AI okm' A' cap' ++ LBK) LB'
    /\ NoDup (map blk_id (hl_blocks FI AI ns' hs' ++ okbA FI AI okm' A' cap' ++ LBK))
    /\ (exists k d, esteps k d (am_nsec FI AI s) LB (am_nsec FI AI s') LB' /\ 0 <= k <= Mx + 1 /\ 0 <= d <= cx
                    /\ 5 * (am_nsec FI AI s' - k) <= PHx + HCount.phiH FI AI hs'
                    /\ Z.of_nat (length LB') <= NBx + 4 * Z.of_nat (length hs'))

    /\ H_phdr.hsumA FI AI hs' <= HSx + cx
    /\ p_scan m' P cur' /\ p_msg FI AI m' LB' P A' len' cap' okm' bs' /\ 0 <= cur' <= len'
    /\ p_ent m' P eb' el' /\ p_ctl m' P err' hack' pos' entp' clen' csz' esp' /\ p_hlist FI AI m' P ns' hs' X'
    /\ p_meth m' P meth' /\ p_ver m' P isreq maj min /\ p_rs m' P rm sc
    /\ shw m' P 504 /\ shz m' (sh lo) (sh q) /\ shr m' (sh lo - sh lo mod 8) (sh q + 8)
    /\ H_pent_seg.pstatE gmax m' /\ (exists ev', clow canary ev' m')
    /\ (r <> 3 -> ent_okA gmax entp' cur' esp' csz' el')
    /\ 0 <= r <= 5 /\ r <> 4
    /\ okm' <> None.

Definition pent_stmt_A (GL : list (Z * Z)) : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB LBK : BL) (st : fsstate FI)
         (P lo cur A len cap : Z) (kA : K) (bs : list byte) (ns : list (BLK * Z)) (hs : list hdr) (X : Z)
         (meth isreq maj min rm sc err hack pos entp clen csz esp gmax : Z) (eb el ev canary : word)
         (ws : list word) (cslack : list byte) (ras : list Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st (wz A0_TP) 4 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 49152 -> q mod 16 = 0 -> q + 64 <= am_stack_top FI AI -> mem_inv asegs m ->
  lb (fs_live FI st) P 504 -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  p_scan m P cur -> p_msg FI AI m LB P A len cap (Some kA) bs -> 0 <= cur <= len ->
  p_ent m P eb el -> p_ctl m P err hack pos entp clen csz esp -> p_hlist FI AI m P ns hs X ->
  p_meth m P meth -> p_ver m P isreq maj min -> p_rs m P rm sc ->
  bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap ++ LBK) LB -> NoDup (map blk_id (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap ++ LBK)) ->
  X + 2 * (len - cur) <= 2^27 + 64 ->
  ebud (pe_meas0 gmax entp el + 1) (len - cur) (HCount.cgG FI AI hs) s LB ->
  ent_okA gmax entp cur esp csz el -> 0 < gmax < 2^32 ->
  H_pent_seg.pstatE gmax m -> clow canary ev m -> shw m ERRNO_A 4 -> gstA GL m ->
  shw m SEPTAB_A 20 -> shw m FMT_CHUNK_A 7 -> shw m FMT_CRLF_A 3 ->
  length ws = 66%nat -> (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64) ->
  H_phdr.phdr_statics ws m cslack -> am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32) ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: 0x8847c :: 0x8a000 :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz P ->
  AJ FI AI J (pent_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB LBK P lo isreq maj min rm sc gmax (pe_meas0 gmax entp el) (len - cur) (H_phdr.hsumA FI AI hs) (5 * am_nsec FI AI s - HCount.phiH FI AI hs) (Z.of_nat (length LB) - 4 * Z.of_nat (length hs)) canary m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz H_pent_seg.parse_entity_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="Type"] Lemma esteps_trans : forall k d N LB N1 LB1, esteps k d N LB N1 LB1 -> forall k2 d2 N2 LB2, esteps k2 d2 N1 LB1 N2 LB2 -> esteps (k + k2) (d + d2) N LB N2 LB2.
Proof.
  intros k d N LB N1 LB1 H. induction H; intros k2' d2' N3 LB3 H2.
  - exact H2.
  - replace (k + 1 + k2') with (k + k2' + 1) by lia. eapply ess_del; [exact H| apply IHesteps; exact H2].
  - replace (d1 + d + d2') with (d1 + (d + d2')) by lia. eapply ess_hdr; [exact H| apply IHesteps; exact H2].
Qed.
#[using="Type"] Lemma esteps_del1 : forall N LB N1 LB1, edel1 N LB N1 LB1 -> esteps 1 0 N LB N1 LB1.
Proof. intros N LB N1 LB1 H. change 1 with (0 + 1). eapply ess_del; [exact H| apply ess_nil]. Qed.
#[using="Type"] Lemma esteps_hdr1 : forall d N LB N1 LB1, H_phdr.hlines FI AI d N LB N1 LB1 -> esteps 0 d N LB N1 LB1.
Proof. intros d N LB N1 LB1 H. replace d with (d + 0) by lia. eapply ess_hdr; [exact H| apply ess_nil]. Qed.
#[using="Type"] Lemma hbud_mono : forall c c' G (s : PS) (LB : BL), c' <= c -> H_phdr.hbud FI AI c G s LB -> H_phdr.hbud FI AI c' G s LB.
Proof.
  intros c c' G s LB Hc HB N' LB' s' n (d1 & d2 & N1 & LB1 & H1 & H2 & H3 & H4) E Hn. apply (HB N' LB' s' n); [| exact E| exact Hn].
  exists d1, d2, N1, LB1. split; [exact H1|]. split; [exact H2|]. split; [lia| exact H4].
Qed.

#[using="Type"] Lemma ebud_hbud : forall M c G (s : PS) (LB : BL), ebud M c G s LB -> 0 <= M -> H_phdr.hbud FI AI c G s LB.
Proof. intros M c G s LB HB HM. apply (HB 0 (am_nsec FI AI s) LB s); [apply eds_nil| lia| reflexivity]. Qed.
#[using="Type"] Lemma ebud_le_now : forall M c G (s : PS) (LB : BL) n, ebud M c G s LB -> 0 <= G -> 0 <= M -> 0 <= c -> n <= A0_MAXREQ -> am_budget_le FI AI s LB n.
Proof. intros M c G s LB n HB HG HM Hc Hn. exact (H_phdr.hbud_le_now FI AI c G s LB n (ebud_hbud M c G s LB HB HM) HG Hc Hn). Qed.

#[using="Type"] Lemma hbud_after_lines : forall c G d (s s' : PS) (LB LB' : BL) n, H_phdr.hbud FI AI c G s LB ->
  H_phdr.hlines FI AI d (am_nsec FI AI s) LB (am_nsec FI AI s') LB' -> d <= c ->
  CG_A * (am_nsec FI AI s' - am_nsec FI AI s) <= G + CG_B * d + CG_SL -> n <= A0_MAXREQ -> am_budget_le FI AI s' LB' n.
Proof.
  intros c G d s s' LB LB' n HB HL Hd GD Hn n' Hn'. apply (H_phdr.hbud_lines_now FI AI c G d s LB s' LB' n' HB HL Hd GD). lia.
Qed.

#[using="Type"] Lemma ebud_step : forall M c c' G (s s' : PS) (LB LB' : BL), ebud M c G s LB -> edel1 (am_nsec FI AI s) LB (am_nsec FI AI s') LB' -> c' <= c -> ebud (M - 1) c' G s' LB'.
Proof.
  intros M c c' G s s' LB LB' HB ST Hc k N1 LB1 s1 ES Hk E. apply (hbud_mono c c' G s1 LB1 Hc). apply (HB (k + 1) N1 LB1 s1); [| lia| exact E].
  eapply eds_cons; [exact ST| exact ES].
Qed.
#[using="Type"] Lemma ebud_mono : forall M M' c c' G (s : PS) (LB : BL), M' <= M -> c' <= c -> ebud M c G s LB -> ebud M' c' G s LB.
Proof. intros M M' c c' G s LB HM Hc HB k N1 LB1 s1 ES Hk E. exact (hbud_mono c c' G s1 LB1 Hc (HB k N1 LB1 s1 ES ltac:(lia) E)). Qed.

#[using="Type"] Lemma ebud_same : forall M c G (s s' : PS) (LB : BL), ebud M c G s LB -> am_nsec FI AI s' = am_nsec FI AI s -> ebud M c G s' LB.
Proof. intros M c G s s' LB HB E k N1 LB1 s1 ES Hk E1. apply (HB k N1 LB1 s1); [rewrite <- E; exact ES| exact Hk| exact E1]. Qed.

Section PJ.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem) (canary : word).
  Hypothesis POK : H_pent_seg.pe_okA FI q lo P st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st (wz A0_TP) 4.
  Hypothesis FE0 : FSENV FI m0.
  Notation F := (H_pent_seg.eF FI st). Notation FL := (H_pent_seg.eFL FI st). Notation SF := (H_pent_seg.eSF FI st).

Local Notation pe_okA := (H_pent_seg.pe_okA FI q lo P st).
Local Notation eF := (H_pent_seg.eF FI st).

Local Notation pscr := (H_pent_seg.pscr FI P st).
Local Notation prestS := (H_pent_seg.prestS FI q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pinvS := (H_pent_seg.pinvS FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pregs := (H_pent_seg.pregs FI q P st gp (wz A0_TP)).
Local Notation dispstA := (H_pent_seg.dispstA FI q P st gp (wz A0_TP) F_ fc).
Local Notation loopstA := (H_pent_seg.loopstA FI q P st gp (wz A0_TP) F_ fc).
Local Notation prologueE := (H_pent_seg.prologueE FI STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO FE0).
Local Notation epostA := (H_pent_seg.epostA FI q lo st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation pWE := (H_pent_seg.pWE FI q lo st).
Local Notation rframeE := (H_pent_seg.rframeE FI q lo st).
Local Notation exitF := (H_pent_seg.exitF FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).

Local Notation blkstA := (H_pent_seg.blkstA FI q P st gp (wz A0_TP) F_ fc).
Local Notation dispE := (H_pent_seg.dispE FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation exitstA := (H_pent_seg.exitstA FI q st gp (wz A0_TP) F_ fc).
Local Notation loopE := (H_pent_seg.loopE FI q P st gp (wz A0_TP) F_ fc).
Local Notation retireE := (H_pent_seg.retireE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation inP := (H_pent_seg.inP P).
Local Notation dj_inP := (H_pent_seg.dj_inP P).
Local Notation pinv_stepP := (H_pent_seg.pinv_stepP FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation pobj_rframe := (H_pent_seg.pobj_rframe FI q lo P st m0 POK RF0).
Local Notation blk4W := (H_pent_seg.blk4W P).
Local Notation blk4E := (H_pent_seg.blk4E FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation pinv_stepSh := (H_pent_seg.pinv_stepSh FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation repoisonE := (H_pent_seg.repoisonE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation unpoisonE := (H_pent_seg.unpoisonE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation outX := (H_pent_seg.outX FI).
Local Notation clsX := (H_pent_seg.clsX FI).
Local Notation dj_inPX := (H_pent_seg.dj_inPX FI P).
Local Notation pinv_stepX := (H_pent_seg.pinv_stepX FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation cb_split1E := (H_pent_seg.cb_split1E ra).
Local Notation epostA_mono := (H_pent_seg.epostA_mono FI q lo st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation xobj_rframe := (H_pent_seg.xobj_rframe FI q lo P st m0 POK RF0).
Local Notation blk2W := (H_pent_seg.blk2W P).
Local Notation blk2post := (H_pent_seg.blk2post FI q lo P st).
Local Notation blk2E := (H_pent_seg.blk2E FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation eframe_facts := (H_pent_seg.eframe_facts FI q lo P st m0 POK RF0).
Local Notation elive := (H_pent_seg.elive FI P st).
Local Notation elive_of := (H_pent_seg.elive_of FI q lo P st m0 POK RF0).
Local Notation pinv_rf := (H_pent_seg.pinv_rf FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation inFJ := (H_pent_seg.inFJ FI st).
Local Notation inW3 := (H_pent_seg.inW3 FI P st).
Local Notation dj_W3 := (H_pent_seg.dj_W3 FI P st).
Local Notation app_W3 := (H_pent_seg.app_W3 FI q lo P st m0 POK RF0).
Local Notation fsw_W3 := (H_pent_seg.fsw_W3 FI q lo P st m0 POK RF0).
Local Notation out_W3 := (H_pent_seg.out_W3 FI q lo P st m0 POK RF0).
Local Notation pinv_stepF := (H_pent_seg.pinv_stepF FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation fj_split := (H_pent_seg.fj_split FI st).
Local Notation fj_join := (H_pent_seg.fj_join FI st).
Local Notation eouts_shw := (H_pent_seg.eouts_shw FI q lo P st m0 POK RF0).
Local Notation txt_okA := (H_pent_seg.txt_okA FI).
Local Notation pctx := (H_pent_seg.pctx q lo P canary).
Local Notation clow_stepW := (H_pent_seg.clow_stepW canary).
Local Notation low_fsW := (H_pent_seg.low_fsW FI q lo P st POK).
Local Notation pctx_stepF := (H_pent_seg.pctx_stepF FI q lo P st m0 POK RF0 canary).
Local Notation pctx_stepP := (H_pent_seg.pctx_stepP FI q lo P st m0 POK RF0 canary).
Local Notation dj_FJER := (H_pent_seg.dj_FJER FI st).
Local Notation evf_ok := (H_pent_seg.evf_ok FI q lo P st m0 POK RF0).
Local Notation pregsG := (H_pent_seg.pregsG FI q P st gp (wz A0_TP)).
Local Notation ajcallstE := (H_pent_seg.ajcallstE FI q P st gp (wz A0_TP) F_ fc).
Local Notation ajretstE := (H_pent_seg.ajretstE FI q P st gp (wz A0_TP) F_ fc).
Local Notation hiER_fsW3 := (H_pent_seg.hiER_fsW3 FI q lo P st m0 POK RF0).
Local Notation blk1aE := (H_pent_seg.blk1aE FI q P st gp (wz A0_TP) F_ fc).
Local Notation blk1bE := (H_pent_seg.blk1bE FI q P st gp (wz A0_TP) F_ fc).
Local Notation blk6aE := (H_pent_seg.blk6aE FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation blk6bE := (H_pent_seg.blk6bE FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation blk6cW := (H_pent_seg.blk6cW P).
Local Notation blk6cE := (H_pent_seg.blk6cE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation blk3cW := (H_pent_seg.blk3cW P).
Local Notation blk3cE := (H_pent_seg.blk3cE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary).
Local Notation blk3W := (H_pent_seg.blk3W FI P st).
Local Notation blk3W_ok := (H_pent_seg.blk3W_ok FI P st).
Local Notation blk3W_fcls := (H_pent_seg.blk3W_fcls FI q lo P st m0 POK RF0).
Local Notation blk3bE := (H_pent_seg.blk3bE FI IC STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary).
Local Notation retstA := (H_pent_seg.retstA FI q st gp (wz A0_TP) F_ fc).
Local Notation blk5W := (H_pent_seg.blk5W P).
Local Notation blk5W_ok := (H_pent_seg.blk5W_ok FI P st).
Local Notation blk5aE := (H_pent_seg.blk5aE FI IC STACK_MALLOC_0 STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary).
Local Notation blk5cW := (H_pent_seg.blk5cW P).
Local Notation blk5cE := (H_pent_seg.blk5cE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary).

  #[using="m0 POK RF0"] Lemma pinv_stepA : forall shd, Z.of_nat (cells_size shd) = 16 -> forall (W : list ivl) (LBK : BL) q' m m2 stc,
    pinvS shd q' m -> apx FI AI W LBK q' m m2 -> Forall inP W ->
    fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> RFAKE FI stc m2 ->
    stk asegs m2 lo q' -> mem_inv asegs m2 -> asan_env asegs m2 ->
    pinvS shd q' m2.
  Proof.
    intros shd HSZ W LBK q' m m2 stc (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR) AP HW LIVE1 RF2 ST2 MI2 AE2.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & _).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    assert (QLO : lo <= q' /\ alloc_ceiling <= q') by (clear - QB LO CLO; lia).
    assert (TRS : forall X cs, q' <= X -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs HX C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_above; exact HX| apply (dj_inP W _ _ HW); right; clear - HX QLO PHI; lia]. }
    assert (TRF : forall X cs, F <= X -> X + Z.of_nat (cells_size cs) <= F + 128 -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs H1 H2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; clear - H1 H2 FLO FHI; lia| apply (dj_inP W _ _ HW); clear - H1 H2 PAF; lia]. }
    unfold H_pent_seg.pinvS, H_pent_seg.prestS.
    split; [exact ST2|].
    split; [exists j0, j160; apply TRS; [clear; lia| exact QC]|].
    split; [exact MI2|]. split; [exact AE2|]. split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split. { eapply (stk_gagree (fun a => aclient FI AI LBK q' a /\ outside W a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact GAP|].
             intros a Ha. split; [left; clear - Ha; lia|]. eapply disjoint_outside; [apply (dj_inP W a 1 HW); right; clear - Ha QLO PHI; lia| lia]. }
    split; [apply TRS; [clear - QB; lia| exact FRhi]|].
    split; [exists w0; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FH]|].
    split; [exists jf; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT1]|].
    split; [apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT2]|].
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact SHF| apply aclient_range_fs_shadow; rewrite ?HSZ; clear - SHF1 SHF2; lia| apply (dj_inP W _ _ HW); rewrite HSZ; clear - PSH; lia]. }
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact FLG| apply aclient_range_fs; simpl_sizes; clear - FLLO FLHI; lia| apply (dj_inP W _ _ HW); simpl_sizes; clear - PAFL; lia]. }
    exists stc. split; [exact RF2| exact LIVE1].
  Qed.

  #[using="AMS"] Lemma stack_shadow_clientE : forall (LB : BL) q0 lo' a,
    sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> aclient FI AI LB q0 a.
  Proof.
    intros LB q0 lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
    apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
  Qed.
  #[using="HC FI P st POK"] Lemma sh_window_okE : SH_LO <= sh lo - sh lo mod 8 /\ sh lo - sh lo mod 8 <= sh lo /\ sh q <= SH_HI /\ sh q + 8 <= SH_HI.
  Proof.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & _). destruct (stack_window_lo FI lo CLO) as [S1 _]. pose proof (stack_lo_ok lo).
    pose proof (sh_hi_ok q ltac:(lia)). pose proof (sh_hi_ok8 q ltac:(lia)). repeat split; assumption.
  Qed.

  #[using="AMS q lo st m0 POK RF0"] Lemma imgsh_apxE : forall (W : list ivl) (LBK : BL) q' m m2 X n, apx FI AI W LBK q' m m2 -> Forall inP W ->
    shw m X n -> 0x10000 <= X -> X + n <= 0x609000 -> shw m2 X n.
  Proof.
    intros W LBK q' m m2 X n AP HW SW X1 X2. pose proof (shw_win_ok _ _ _ SW) as [Hn _].
    pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    eapply (shw_band_eq m m2 X n 0x7fffa000 0x800b9200 SW).
    - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) _ _)) Hv).
      + right; left. exists 0x7fffa000, 0x800b9200. split; [| lia]. apply AMS. unfold a0_static. split; [lia|]. do 11 right. left. lia.
      + apply outside_of_forall. eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. clear - H1 H2 H3 Ha PF1 PF2 B1 B2 B5. lia.
    - lia.
    - lia.
    - reflexivity.
    - reflexivity.
    - unfold sh, SHADOW_OFF. clear - X1. Z.div_mod_to_equations. lia.
    - intros _. unfold sh, SHADOW_OFF. clear - X2 Hn. Z.div_mod_to_equations. lia.
  Qed.
  #[using="AMS q lo st POK"] Lemma imgcell_apxE : forall (W : list ivl) (LBK : BL) q' m m2 X cs, apx FI AI W LBK q' m m2 -> Forall inP W ->
    rw_cells asegs m X cs -> a0_static X (X + Z.of_nat (cells_size cs)) -> X + Z.of_nat (cells_size cs) <= 0x609000 -> rw_cells asegs m2 X cs.
  Proof.
    intros W LBK q' m m2 X cs AP HW C HS HX. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    eapply (apx_rw_cells FI AI); [exact AP| exact C| eapply aclient_range_static; [apply AMS; exact HS| lia| lia]| apply (dj_inP W _ _ HW); left; clear - HX PLO; lia].
  Qed.

  Ltac stat_band := unfold a0_static; split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; env_band.

  #[using="AMS m0 POK RF0"] Lemma pctx_stepA : forall (LBK LB2 : BL) (sx : PS) q' A len cap cur bs A' len' cap' bs' (k' : K) m m2 stc,
    pctx A len cap cur bs m -> apx FI AI [(P + 400, P + 400 + 32)]%Z LBK q' m m2 ->
    q + -304 <= q' <= q + -288 ->
    fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> RFAKE FI stc m ->
    RHEAP_A FI AI sx LB2 m2 -> In (k', A', cap' + 1) LB2 ->
    rw_cells asegs m2 (P + 400) (mbuf_cells A' len' cap') -> rw_cells asegs m2 A' [CB (Z.to_nat (cap' + 1)) bs'] -> 0 <= cap' ->
    pctx A' len' cap' cur bs' m2.
  Proof.
    intros LBK LB2 sx q' A len cap cur bs A' len' cap' bs' k' m m2 stc
      (SC & _ & _ & SHP & _ & SHSEP & SHF1 & SHF2 & SHZ & SHR & (ev & CL1 & CL2 & CL3) & SHE) AP QB LIVE1 RF HR2 KIN2 MBC2 TXT2 CAP0.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    destruct (elive_of stc LIVE1) as (_ & _ & _ & LVP & _).
    destruct sh_window_okE as (W1 & W2 & W3 & W4).
    assert (HW : Forall inP [(P + 400, P + 400 + 32)]%Z) by (unfold inP; repeat constructor; cbn [fst snd]; lia).
    assert (AW : app_ivs [(P + 400, P + 400 + 32)]%Z).
    { constructor; [| constructor]. unfold app_iv, SH_HI. cbn [fst snd]. clear - PF1 PF2 B1 B2 B5. lia. }
    unfold H_pent_seg.pctx.
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact SC| apply aclient_range_fs; simpl_sizes; clear - PF1 PF2; lia| cbn [disjoint_from]; simpl_sizes; split; [clear; lia| exact I]]. }
    split; [exact MBC2|]. split; [exact TXT2|].
    split. { eapply (mlocNB_shw_apx FI AI AMS _ LBK q' stc m m2 P 504); [right; exact LVP| exact SHP| exact AP| exact AW| exact RF| clear - QB LO CLO; lia]. }
    split; [eapply (block_shw FI AI sx LB2 m2 (k', A', cap' + 1) A' (cap' + 1) HR2 KIN2); cbn; lia|].
    split; [apply (imgsh_apxE _ LBK q' m m2 _ _ AP HW SHSEP); unfold SEPTAB_A; lia|].
    split; [apply (imgsh_apxE _ LBK q' m m2 _ _ AP HW SHF1); lia|].
    split; [apply (imgsh_apxE _ LBK q' m m2 _ _ AP HW SHF2); lia|].
    assert (STKSH : forall a, sh lo - sh lo mod 8 <= a < sh q + 8 -> aclient FI AI LBK q' a /\ outside [(P + 400, P + 400 + 32)]%Z a).
    { intros a Ha. assert (SLO : sh alloc_ceiling - sh alloc_ceiling mod 8 <= sh lo - sh lo mod 8).
      { pose proof (sh_mono alloc_ceiling lo CLO) as HM. clear - HM. Z.div_mod_to_equations. lia. }
      split; [apply (stack_shadow_clientE LBK q' (sh lo - sh lo mod 8) a SLO); unfold SH_HI in W4; lia|].
      cbn [outside]. split; [| exact I]. unfold SH_LO, SH_HI in *. clear - Ha W1 W4 PF1 PF2 B1 B2 B5. lia. }
    split. { intros a Ha. destruct (STKSH a ltac:(lia)) as [C O]. exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) (SHZ a Ha)). }
    split. { intros a Ha. destruct (SHR a Ha) as [v Hv]. exists v. destruct (STKSH a Ha) as [C O]. exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) Hv). }
    split.
    { exists ev. unfold clow, A0_got_ssp, A0_ssp_guard in *. split; [| split].
      - apply (imgcell_apxE _ LBK q' m m2 _ _ AP HW CL1); [stat_band| simpl_sizes; lia].
      - apply (imgcell_apxE _ LBK q' m m2 _ _ AP HW CL2); [stat_band| simpl_sizes; lia].
      - apply (imgcell_apxE _ LBK q' m m2 _ _ AP HW CL3); [stat_band| simpl_sizes; lia]. }
    apply (imgsh_apxE _ LBK q' m m2 _ _ AP HW SHE); lia.
  Qed.
  #[using="AMS q lo st m0 POK RF0"] Lemma pstat_stepA : forall (W : list ivl) (LBK : BL) q' gmax m m2, pstatE gmax m -> apx FI AI W LBK q' m m2 -> Forall inP W -> pstatE gmax m2.
  Proof.
    intros W LBK q' gmax m m2 (G1 & G2 & G3 & G4) AP HW. unfold H_pent_seg.pstatE.
    split; [apply (imgcell_apxE _ LBK q' m m2 _ _ AP HW G1); [stat_band| simpl_sizes; lia]|].
    split; [apply (imgcell_apxE _ LBK q' m m2 _ _ AP HW G2); [stat_band| simpl_sizes; lia]|].
    split; [apply (imgsh_apxE _ LBK q' m m2 _ _ AP HW G3); lia|].
    apply (imgcell_apxE _ LBK q' m m2 _ _ AP HW G4); [stat_band| simpl_sizes; lia].
  Qed.

  #[using="IC AC ASL AMS m0 POK RF0"] Lemma delJ : forall shd, Z.of_nat (cells_size shd) = 16 ->
    forall (ra' q' idx num A len cap cur gmax : Z) (bs : list byte) (kA : K) (s : PS) (LB : BL) m
      x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31 (Q : PS -> BL -> machine_state -> Prop),
    pinvS shd q' m -> pctx A len cap cur bs m -> pstatE gmax m ->
    RHEAP_A FI AI s LB m -> In (kA, A, cap + 1) LB -> q + 64 <= am_stack_top FI AI ->
    cap + 8 <= 2^28 -> am_budget_le FI AI s LB (cap + 6) -> 0 <= len <= cap ->
    0 <= idx -> 0 <= num -> idx + num <= len -> ret_pc (wz ra') = wz ra' ->
    (forall (s' : PS) (LB' : BL) m' A' len' cap' (k' : K) bs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvS shd q' m' -> pctx A' len' cap' cur bs' m' -> pstatE gmax m' -> RHEAP_A FI AI s' LB' m' -> In (k', A', cap' + 1) LB' ->
       apx FI AI [(P + 400, P + 400 + 32)]%Z (lb_keepA FI AI (Some kA) LB) q' m m' ->
       ((k' = kA /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
        \/ (LB' = (k', A', cap' + 1) :: lb_keepA FI AI (Some kA) LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1))) ->
       0 <= len' <= cap' -> cap' <= cap ->
       ((len = 0 /\ len' = 0 /\ bs' = bs)
        \/ (1 <= len /\ len' = len - num /\ firstn (Z.to_nat (len' + 1)) bs' = firstn (Z.to_nat len') (del_bytesA bs idx num len) ++ [Z_to_bv 8 0])) ->
       AJ FI AI J Q (ajretstE ra' q' y10 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x26 y28 y29 y30 y31 m') s' LB') ->
    AJ FI AI J Q (ajcallstE 0x8c704 ra' q' (wz (P + 400)) (wz idx) (wz num) x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31 m) s LB.
  Proof.
    intros shd HSZ ra' q' idx num A len cap cur gmax bs kA s LB m x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31 Q
      INV CTX PST HR KIN QTOP CAPB BUD LENC I0 N0 INL RPC K.
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & VR). destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF & LIVE1)).
    pose proof CTX as (_ & MBC & TXT & SHP & _).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    destruct (elive_of stc LIVE1) as (_ & _ & _ & LVP & _).
    unfold H_pent_seg.ajcallstE, H_pent_seg.pregsG.
    eapply (aj_bind FI AI J).
    { eapply (membuffer_delete_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (st := stc) (ok := Some kA) (MB := P + 400) (idx := idx) (num := num)
                                                                (A := A) (len := len) (cap := cap) (bs := bs).
      - exact HR.
      - exact RF.
      - exact AE.
      - exact ST.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO QB. lia.
      - exact QAL.
      - clear - QB QTOP. lia.
      - exact MI.
      - exact MBC.
      - exact LENC.
      - exact CAPB.
      - exact BUD.
      - cbn [mownA]. split; [exact KIN| exact TXT].
      - right; right. apply (Contracts.lb_sub _ _ _ _ _ LVP); clear; lia.
      - clear - PHI. lia.
      - clear - PAL. Z.div_mod_to_equations. lia.
      - apply (shw_sub _ P 504); [exact SHP| clear; lia| clear; lia| clear; lia].
      - exact I0.
      - exact N0.
      - exact INL.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    intros s' LB' ms' PO. unfold membuffer_delete_post_A in PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & A' & len' & cap' & ok' & bs'
                    & -> & MI' & ST' & AE' & RF' & APX & HR' & LBC & MBC' & LC' & CC' & OWN' & LENC').
    rewrite RPC.
    assert (OK' : exists k', ok' = Some k' /\ ((k' = kA /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
                  \/ (LB' = (k', A', cap' + 1) :: lb_keepA FI AI (Some kA) LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1)))).
    { destruct LBC as [(E1 & E2 & E3 & E4 & E5)|(k' & E1 & E2 & E3)]; [exists kA; split; [exact E1| left; auto]| exists k'; split; [exact E1| right; auto]]. }
    destruct OK' as (k' & -> & LBC'). cbn [mownA] in OWN'. destruct OWN' as [KIN' TXT'].
    assert (HWd : Forall inP [(P + 400, P + 400 + 32)]%Z) by (unfold H_pent_seg.inP; repeat constructor; cbn [fst snd]; lia).
    unfold H_pent_seg.ajretstE, H_pent_seg.pregsG in K.
    eapply (K s' LB' m' A' len' cap' k' bs'); try eassumption.
    - exact (pinv_stepA shd HSZ _ _ q' m m' stc INV APX HWd LIVE1 RF' ST' MI' AE').
    - exact (pctx_stepA _ LB' s' q' A len cap cur bs A' len' cap' bs' k' m m' stc CTX APX QB LIVE1 RF HR' KIN' MBC' TXT' ltac:(lia)).
    - exact (pstat_stepA _ _ q' gmax m m' PST APX HWd).
  Qed.

  #[using="Type"] Lemma pctl_split : forall m err hack pos entp clen csz esp,
    rw_cells asegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp) ->
    rw_cells asegs m (P + 440) [C4 (wz err)] /\ rw_cells asegs m (P + 444) [C4 (wz hack)] /\ rw_cells asegs m (P + 448) [C4 (wz pos)]
    /\ rw_cells asegs m (P + 452) [C4 (wz entp)] /\ rw_cells asegs m (P + 456) [C4 (wz clen)] /\ rw_cells asegs m (P + 460) [C4 (wz 0)]
    /\ rw_cells asegs m (P + 464) [C8 (wz csz)] /\ rw_cells asegs m (P + 472) [C8 (wz esp)].
  Proof.
    intros m err hack pos entp clen csz esp H. unfold p_ctl_cells in H.
    split_chunk H 1%nat H1 R1. split_chunk R1 1%nat H2 R2. split_chunk R2 1%nat H3 R3. split_chunk R3 1%nat H4 R4.
    split_chunk R4 1%nat H5 R5. split_chunk R5 1%nat H6 R6. split_chunk R6 1%nat H7 H8.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7| exact H8].
  Qed.
  #[using="Type"] Lemma pctl_join : forall m err hack pos entp clen csz esp,
    rw_cells asegs m (P + 440) [C4 (wz err)] -> rw_cells asegs m (P + 444) [C4 (wz hack)] -> rw_cells asegs m (P + 448) [C4 (wz pos)] ->
    rw_cells asegs m (P + 452) [C4 (wz entp)] -> rw_cells asegs m (P + 456) [C4 (wz clen)] -> rw_cells asegs m (P + 460) [C4 (wz 0)] ->
    rw_cells asegs m (P + 464) [C8 (wz csz)] -> rw_cells asegs m (P + 472) [C8 (wz esp)] ->
    rw_cells asegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp).
  Proof.
    intros m err hack pos entp clen csz esp H1 H2 H3 H4 H5 H6 H7 H8. unfold p_ctl_cells.
    join_chunks H7 H8 J7. join_chunks H6 J7 J6. join_chunks H5 J6 J5. join_chunks H4 J5 J4. join_chunks H3 J4 J3. join_chunks H2 J3 J2. join_chunks H1 J2 J1.
    exact J1.
  Qed.

  #[using="Type"] Lemma ent4_join : forall m (eb el : word) A len cap,
    rw_cells asegs m (P + 384) [C8 eb; C8 el] -> rw_cells asegs m (P + 400) (mbuf_cells A len cap) ->
    rw_cells asegs m (P + 384) [C8 eb; C8 el; C8 (wz A); C8 (wz len)] /\ rw_cells asegs m (P + 416) [C8 (wz cap); C8 (wz MEMBUF_DEF_SIZE_INC)].
  Proof.
    intros m eb el A len cap HE HM. unfold mbuf_cells in HM. split_chunk HM 2%nat M1 M2. join_chunks HE M1 JE. split; [exact JE| exact M2].
  Qed.
  #[using="Type"] Lemma ent4_split : forall m (eb el : word) A len cap,
    rw_cells asegs m (P + 384) [C8 eb; C8 el; C8 (wz A); C8 (wz len)] -> rw_cells asegs m (P + 416) [C8 (wz cap); C8 (wz MEMBUF_DEF_SIZE_INC)] ->
    rw_cells asegs m (P + 384) [C8 eb; C8 el] /\ rw_cells asegs m (P + 400) (mbuf_cells A len cap).
  Proof.
    intros m eb el A len cap H4 M2. split_chunk H4 2%nat HE M1. join_chunks M1 M2 JE. split; [exact HE| unfold mbuf_cells; exact JE].
  Qed.

  #[using="Type"] Lemma pctx_of : forall (s : PS) (LB : BL) m A len cap (kA : K) bs cur ev,
    RHEAP_A FI AI s LB m -> p_scan m P cur -> p_msg FI AI m LB P A len cap (Some kA) bs ->
    shw m P 504 -> shw m SEPTAB_A 20 -> shw m FMT_CHUNK_A 7 -> shw m FMT_CRLF_A 3 ->
    shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) -> clow canary ev m -> shw m ERRNO_A 4 ->
    pctx A len cap cur bs m /\ txt_okA A len cap /\ In (kA, A, cap + 1) LB /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof.
    intros s LB m A len cap kA bs cur ev HR PSC PMSG SHP SHSEP SHF1 SHF2 SHZ SHR CLOW SHE.
    destruct (p_msg_facts FI AI m LB P A len cap (Some kA) bs s HR PMSG) as (HL & HCp & LBS0 & _ & SOME).
    destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct PMSG as (MBC & [HIN TXC] & _ & _ & MNUL).
    split.
    { unfold H_pent_seg.pctx. split; [exact PSC|]. split; [exact MBC|]. split; [exact TXC|]. split; [exact SHP|].
      split; [eapply (block_shw FI AI s LB m (kA, A, cap + 1) A (cap + 1) HR HIN); cbn; lia|].
      split; [exact SHSEP|]. split; [exact SHF1|]. split; [exact SHF2|]. split; [exact SHZ|]. split; [exact SHR|]. split; [exists ev; exact CLOW| exact SHE]. }
    split; [| split; [exact HIN| exact MNUL]].
    unfold H_pent_seg.txt_okA. split; [exact S1|]. split; [exact S2|]. split; [exact HL|]. split; [exact S3|]. split; [exact S5|]. split; [exact S6|].
    unfold LMAX_A in HCp. clear - HCp. lia.
  Qed.

  Variables (LBK : BL) (isreq maj min rm sc gmax : Z) (ws : list word) (cslack : list byte) (ras : list Z) (GL : list (Z * Z)).
  Variables (s_0 : PS) (LB_0 : BL) (M0 c0 HS0 PH0 NB0 : Z).
  Hypothesis HR0 : RHEAP_A FI AI s_0 LB_0 m0.
  Hypothesis KSUB0 : bsub FI AI LBK LB_0.
  Hypothesis QTOP : q + 64 <= am_stack_top FI AI.
  Hypothesis GMX : 0 < gmax < 2^32.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64.
  Hypothesis ZSTAT : am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32).
  Hypothesis TRACE : In (PC0_MALLOC :: 0x8847c :: 0x8a000 :: bv_unsigned ra :: ras) A0_TRACES.
  Hypothesis GLR : Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL.
  Hypothesis GERM : germ_stmt_A (gstA GL).

  Local Notation pinv := (pinvS eshadow).
  Local Notation POST := (pent_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s_0 LB_0 LBK P lo isreq maj min rm sc gmax M0 c0 HS0 PH0 NB0 canary m0).
  Local Notation pe_measA := (pe_meas0 gmax).

  #[using="Type"] Lemma aj_cps : forall (Q : PS -> BL -> machine_state -> Prop) ms (s : PS) (LB : BL),
    evt asegs (fun ms' => AJ FI AI J Q ms' s LB) ms -> AJ FI AI J Q ms s LB.
  Proof. intros Q ms s LB H. eapply (aj_evt FI AI J); [exact H| intros ms' H'; exact H']. Qed.

  Definition estat (m : mem) : Prop :=
    shw m P 504 /\ shw m SEPTAB_A 20 /\ shw m FMT_CHUNK_A 7 /\ shw m FMT_CRLF_A 3
    /\ shz m (sh lo) (sh q) /\ shr m (sh lo - sh lo mod 8) (sh q + 8)
    /\ (exists ev, clow canary ev m) /\ shw m ERRNO_A 4 /\ pstatE gmax m.
  Definition estat2 (m : mem) : Prop := H_phdr.phdr_statics ws m cslack /\ gstA GL m.

  Definition EX (s : PS) (LB : BL) (m : mem) (cur A len cap : Z) (okm : option K) (bs : list byte) (eb el : word)
      (err hack pos entp clen csz esp : Z) (ns : list (BLK * Z)) (hs : list hdr) (X meth : Z) : Prop :=
    RHEAP_A FI AI s LB m
    /\ p_scan m P cur /\ p_msg FI AI m LB P A len cap okm bs /\ 0 <= cur <= len
    /\ p_ent m P eb el /\ p_ctl m P err hack pos entp clen csz esp /\ p_hlist FI AI m P ns hs X
    /\ p_meth m P meth /\ p_ver m P isreq maj min /\ p_rs m P rm sc
    /\ bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap ++ LBK) LB
    /\ NoDup (map blk_id (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap ++ LBK))
    /\ estat m
    /\ apxF FI AI (pent_WA P) LBK q st m0 m
    /\ (exists k d, esteps k d (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s) LB /\ 0 <= k <= M0 + 1 /\ 0 <= d <= c0
                    /\ 5 * (am_nsec FI AI s - k) <= PH0 + HCount.phiH FI AI hs /\ Z.of_nat (length LB) <= NB0 + 4 * Z.of_nat (length hs))
    /\ H_phdr.hsumA FI AI hs <= HS0 + c0.
  Definition EI (s : PS) (LB : BL) (m : mem) (q' cur A len cap : Z) (okm : option K) (bs : list byte) (eb el : word)
      (err hack pos entp clen csz esp : Z) (ns : list (BLK * Z)) (hs : list hdr) (X meth : Z) : Prop :=
    EX s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
    /\ pinv q' m /\ X + 2 * (len - cur) <= 2^27 + 64
    /\ estat2 m /\ (ebud (pe_measA entp el + 1) (len - cur) (HCount.cgG FI AI hs) s LB /\ len - cur <= c0 /\ H_phdr.hsumA FI AI hs <= HS0
                  /\ exists k0, esteps k0 0 (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s) LB /\ 0 <= k0 /\ k0 + pe_measA entp el <= M0
                                /\ 5 * (am_nsec FI AI s - k0) <= PH0 + HCount.phiH FI AI hs /\ Z.of_nat (length LB) <= NB0 + 4 * Z.of_nat (length hs))
    /\ fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras
    /\ ent_okA gmax entp cur esp csz el.

  #[using="Type"] Lemma EX_done : forall (s : PS) (LB : BL) m' (st' : fsstate FI) cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth r
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    okm <> None ->
    EX s LB m' cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth ->
    mem_inv asegs m' -> stk asegs m' lo q -> asan_env asegs m' -> RFAKE FI st' m' -> fs_live FI st' = fs_live FI st ->
    (r <> 3 -> ent_okA gmax entp cur esp csz el) -> 0 <= r <= 5 -> r <> 4 ->
    POST s LB (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F_ (ret_pc ra) fc None m' (seg_rom asegs)).
  Proof.
    intros s LB m' st' cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 OKN
      (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & PRS & SUB & ND & (SHP & _ & _ & _ & SHZ & SHR & CL & _ & PST) & APF & ES & HSF) MI ST AE RF LIVE EOK R1 R2.
    unfold pent_post_A.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st', r, cur, A, len, cap, okm, bs, eb, el, err, hack, pos, entp, clen, csz, esp, X, meth, ns, hs.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact AE|]. split; [exact RF|]. split; [exact LIVE|].
    split; [exact APF|]. split; [exact HR|]. split; [exact SUB|]. split; [exact ND|]. split; [exact ES|]. split; [exact HSF|].
    split; [exact PSC|]. split; [exact PMSG|]. split; [exact CUR|]. split; [exact PENT|]. split; [exact PCTL|]. split; [exact PHL|].
    split; [exact PMETH|]. split; [exact PVER|]. split; [exact PRS|]. split; [exact SHP|]. split; [exact SHZ|]. split; [exact SHR|].
    split; [exact PST|]. split; [exact CL|]. split; [exact EOK|]. split; [exact R1|]. split; [exact R2| exact OKN].
  Qed.

  Definition wpok (iv : ivl) : Prop := inP iv \/ H_pent_seg.inER iv.
  Definition ekeep (WP : list ivl) (OB : BL) (m m' : mem) : Prop :=
    (forall a cs, (P <= a /\ a + Z.of_nat (cells_size cs) <= P + 504) \/ (a0_static a (a + Z.of_nat (cells_size cs)) /\ a + Z.of_nat (cells_size cs) <= 0x609000) ->
        disjoint_from WP a (Z.of_nat (cells_size cs)) -> rw_cells asegs m a cs -> rw_cells asegs m' a cs)
    /\ (forall a bs, a0_static a (a + Z.of_nat (length bs)) -> a + Z.of_nat (length bs) <= 0x5e68c8 -> bytes_at asegs m a bs -> bytes_at asegs m' a bs)
    /\ (forall a n, a0_static a (a + n) -> a + n <= 0x5e68c8 -> wr_at asegs m a n -> wr_at asegs m' a n)
    /\ bkeep FI AI OB m m'
    /\ (forall X n, 0x10000 <= X -> X + n <= 0x609000 -> shw m X n -> shw m' X n)
    /\ apxF FI AI (pent_WA P) LBK q st m m'
    /\ (forall rs a, fpchain m (am_stack_top FI AI) q a rs -> fpchain m' (am_stack_top FI AI) q a rs)
    /\ (shw m P 504 -> shw m' P 504)
    /\ (shz m (sh lo) (sh q) -> shz m' (sh lo) (sh q)) /\ (shr m (sh lo - sh lo mod 8) (sh q + 8) -> shr m' (sh lo - sh lo mod 8) (sh q + 8)).

  #[using="ws WSL"] Lemma shw_munch_gen : forall (W : list ivl) m m' X n, shw m X n -> munch W m m' ->
    (forall a, sh X - sh X mod 8 <= a < sh (X + n - 1) - sh (X + n - 1) mod 8 + 8 -> outside W a) -> shw m' X n.
  Proof.
    intros W m m' X n (ACC & RD & WK) MU OUT. split; [| split; [| exact WK]].
    - intros a Ha. destruct (ACC a Ha) as (k & (B0 & B1 & BB) & Hk). exists k. split; [| exact Hk].
      split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi).
      cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r.
      pose proof (win_ok_sh_band X n a WK Ha) as SB.
      apply (mrd_munch W m m' (sh a) MU); [| exact (shband_range _ SB)].
      apply OUT. unfold sh, SHADOW_OFF. clear - Ha. Z.div_mod_to_equations. lia.
    - intros Hn a Ha. destruct (RD Hn a Ha) as (v & Hv). exists v. rewrite <- Hv.
      pose proof (win_ok_words_band X n a WK Hn Ha) as SB.
      apply (mrd_munch W m m' a MU); [| exact (shband_range _ SB)]. exact (OUT a Ha).
  Qed.

  #[using="HC FI q lo st POK ws WSL"] Lemma dj_wpok_low2 : forall (WP : list ivl) X n, Forall wpok WP -> X + n <= 0x5e68c8 \/ (0x5e68d0 <= X /\ X + n <= 0x609000) -> disjoint_from WP X n.
  Proof.
    intros WP X n HW HX. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    induction HW as [|[x y] W [(H1 & H2 & H3)|(H1 & H2 & H3)] _ IH]; cbn [disjoint_from fst snd] in *; [exact I| |]; (split; [lia| exact IH]).
  Qed.
  #[using="HC FI q lo st POK ws WSL"] Lemma dj_wpok_low : forall (WP : list ivl) X n, Forall wpok WP -> X + n <= 0x5e68c8 -> disjoint_from WP X n.
  Proof.
    intros WP X n HW HX. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    induction HW as [|[x y] W [(H1 & H2 & H3)|(H1 & H2 & H3)] _ IH]; cbn [disjoint_from fst snd] in *; [exact I| |]; (split; [lia| exact IH]).
  Qed.

  #[using="Type"] Lemma ek_pcell : forall WP OB m m' a cs, ekeep WP OB m m' -> P <= a -> a + Z.of_nat (cells_size cs) <= P + 504 ->
    disjoint_from WP a (Z.of_nat (cells_size cs)) -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof. intros WP OB m m' a cs (K1 & _) H1 H2 DJ C. apply (K1 a cs); [left; split; assumption| exact DJ| exact C]. Qed.
  #[using="POK ws WSL"] Lemma ek_scell : forall WP OB m m' a cs, ekeep WP OB m m' -> Forall wpok WP -> a0_static a (a + Z.of_nat (cells_size cs)) ->
    a + Z.of_nat (cells_size cs) <= 0x5e68c8 -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof. intros WP OB m m' a cs (K1 & _) HW H1 H2 C. apply (K1 a cs); [right; split; [exact H1| lia]| apply (dj_wpok_low WP _ _ HW H2)| exact C]. Qed.

  #[using="ws WSL"] Lemma ek_hlist : forall WP OB m m' ns hs X, ekeep WP OB m m' -> p_hlist FI AI m P ns hs X -> bsub FI AI (hl_blocks FI AI ns hs) OB ->
    disjoint_from WP (P + 288) 96 -> p_hlist FI AI m' P ns hs X.
  Proof.
    intros WP OB m m' ns hs X EK (LHC & FLC & FFC & DL & HM & IT & VB & ZL & X0) SUB DJ.
    pose proof EK as (_ & _ & _ & BK & _).
    assert (PK : forall a cs, P + 288 <= a -> a + Z.of_nat (cells_size cs) <= P + 384 -> rw_cells asegs m a cs -> rw_cells asegs m' a cs).
    { intros a cs H1 H2 C. apply (ek_pcell WP OB m m' a cs EK); [lia| lia| | exact C]. eapply disjoint_from_sub; [exact DJ| lia| lia]. }
    unfold p_hlist.
    split; [apply PK; [lia| unfold lhead_cells; simpl_sizes; lia| exact LHC]|].
    split; [apply PK; [lia| unfold fl_cells; simpl_sizes; lia| exact FLC]|].
    split; [apply PK; [lia| simpl_sizes; lia| exact FFC]|].
    split. { eapply (dlseg_bkeep FI AI); [exact DL| exact BK|]. intros b it Hb. apply SUB. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hb). }
    split. { eapply (hdrs_mem_bkeep FI AI); [exact HM| exact BK|]. intros b Hb. apply SUB. unfold hl_blocks. apply in_or_app. right. exact Hb. }
    repeat (split; [assumption|]). exact X0.
  Qed.

  #[using="POK ws WSL"] Lemma ek_pstat : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> pstatE gmax m -> pstatE gmax m'.
  Proof.
    intros WP OB m m' EK HW (G1 & G2 & G3 & G4). pose proof EK as (_ & _ & _ & _ & SK & _). unfold H_pent_seg.pstatE.
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact G1]|].
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact G2]|].
    split; [apply SK; [lia| lia| exact G3]|].
    apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact G4].
  Qed.

  #[using="POK ws WSL"] Lemma ek_clow : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> disjoint_from WP ERRNO_A 4 ->
    (exists ev, clow canary ev m) -> exists ev, clow canary ev m'.
  Proof.
    intros WP OB m m' EK HW DJ (ev & CL1 & CL2 & CL3). pose proof EK as (K1 & _). exists ev. unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [apply (K1 _ _); [right; split; [stat_band| simpl_sizes; lia]| simpl_sizes; exact DJ| exact CL1]|].
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact CL2]|].
    apply (K1 _ _); [right; split; [stat_band| simpl_sizes; lia]| apply (dj_wpok_low2 WP _ _ HW); simpl_sizes; lia| exact CL3].
  Qed.
  #[using="POK ws WSL"] Lemma ek_stat : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> estat m -> (exists ev, clow canary ev m') -> estat m'.
  Proof.
    intros WP OB m m' EK HW (SHP & SHSEP & SHF1 & SHF2 & SHZ & SHR & _ & SHE & PST) CL.
    pose proof EK as (_ & _ & _ & _ & SK & _ & _ & K7 & K8 & K9). unfold estat.
    split; [exact (K7 SHP)|]. split; [apply SK; [unfold SEPTAB_A; lia| unfold SEPTAB_A; lia| exact SHSEP]|].
    split; [apply SK; [lia| lia| exact SHF1]|]. split; [apply SK; [lia| lia| exact SHF2]|].
    split; [exact (K8 SHZ)|]. split; [exact (K9 SHR)|]. split; [exact CL|].
    split; [apply SK; [lia| lia| exact SHE]|]. exact (ek_pstat WP OB m m' EK HW PST).
  Qed.

  #[using="WSL GLR"] Lemma ek_stat2 : forall WP OB m m', ekeep WP OB m m' -> estat2 m -> estat2 m'.
  Proof.
    intros WP OB m m' (_ & BK & WK & _ & SK & _) ((HS & SHSEP & SHFMT & COMMAB & CSL & SHC & ZB & SHZ0) & GS).
    split.
    - unfold H_phdr.phdr_statics.
      split.
      { destruct HS as ((TB1 & TB2) & SHT & TS). split; [split|split].
        - apply BK; [unfold a0_static; rewrite u64s_length, WSL; split; [lia|]; right; left; lia| rewrite u64s_length, WSL; lia| exact TB1].
        - apply WK; [unfold a0_static; rewrite WSL; split; [lia|]; right; left; lia| rewrite WSL; lia| exact TB2].
        - apply SK; [lia| lia| exact SHT].
        - intros i Hi. destruct (TS i Hi) as (Sx & str & slack & E1 & E2 & E3 & E4 & E5 & E6 & E7).
          exists Sx, str, slack. repeat (split; [assumption|]). apply SK; [lia| lia| exact E7]. }
      split; [apply SK; [unfold SEPTAB_A; lia| unfold SEPTAB_A; lia| exact SHSEP]|].
      split; [apply SK; [lia| lia| exact SHFMT]|].
      split; [exact COMMAB|]. split; [exact CSL|].
      split; [apply SK; [lia| lia| exact SHC]|].
      split; [apply BK; [unfold a0_static; cbn [length Z.of_nat Pos.of_succ_nat]; split; [lia|]; env_band| cbn [length Z.of_nat Pos.of_succ_nat]; lia| exact ZB]|].
      apply SK; [lia| lia| exact SHZ0].
    - unfold gstA in *. rewrite Forall_forall in *. intros xn Hx. pose proof (GLR xn Hx) as [G1 G2]. apply SK; [exact G1| exact G2| exact (GS xn Hx)].
  Qed.

  Definition ecls (WP : list ivl) (TB : BL) (iv : ivl) : Prop :=
    fst iv < snd iv /\
    ( (alloc_ceiling <= fst iv /\ snd iv <= q)
      \/ (F <= fst iv /\ snd iv <= F + 128) \/ (SF <= fst iv /\ snd iv <= SF + 16) \/ (FL <= fst iv /\ snd iv <= FL + 1)
      \/ inside WP (fst iv) (snd iv - fst iv)
      \/ (exists b, In b TB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ).

  #[using="ws WSL"] Lemma inside_wpok : forall (WP : list ivl) x n, Forall wpok WP -> inside WP x n -> 0 <= n ->
    (P <= x /\ x + n <= P + 504) \/ (0x5e68c8 <= x /\ x + n <= 0x5e68d0).
  Proof.
    intros WP x n HW. induction HW as [|[a b] W [(H1 & H2 & H3)|(H1 & H2 & H3)] _ IH]; cbn [inside fst snd] in *; intros HI Hn; [destruct HI| |];
      (destruct HI as [HI|HI]; [| exact (IH HI Hn)]); [left| right]; lia.
  Qed.
  #[using="ws WSL"] Lemma inside_dj : forall (WP : list ivl) x n a k, inside WP x n -> disjoint_from WP a k -> 0 <= n -> a + k <= x \/ x + n <= a \/ n = 0.
  Proof.
    induction WP as [|[lo' hi'] W IH]; intros x n a k HI HD Hn; cbn [inside disjoint_from] in *; [destruct HI|].
    destruct HD as [D1 D2]. destruct HI as [HI|HI]; [lia| exact (IH x n a k HI D2 Hn)].
  Qed.
  #[using="Type"] Lemma inside_sub : forall (WP W' : list ivl) x n, inside WP x n -> Forall (fun iv : ivl => inside W' (fst iv) (snd iv - fst iv)) WP -> inside W' x n.
  Proof.
    induction WP as [|[lo' hi'] W IH]; intros W' x n HI HF; cbn [inside] in HI; [destruct HI|].
    inversion HF as [|? ? H1 H2]; subst. cbn [fst snd] in H1. destruct HI as [HI|HI]; [| exact (IH W' x n HI H2)].
    clear - H1 HI. induction W' as [|[a b] W' IH']; cbn [inside] in *; [destruct H1|]. destruct H1 as [H1|H1]; [left; lia| right; exact (IH' H1)].
  Qed.
  #[using="Type"] Lemma dj_forall : forall (W : list ivl) a n, Forall (fun iv : ivl => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
  Proof. induction W as [|[x y] W IH]; intros a n HF; cbn [disjoint_from]; [exact I|]. inversion HF as [|? ? H1 H2]; subst. split; [exact H1| exact (IH a n H2)]. Qed.

  #[using="ASL AMS m0 POK RF0 ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma ekeep_munch : forall (W WP : list ivl) (TB OB : BL) (s : PS) (LB : BL) m m',
    munch W m m' -> wmono asegs m m' -> Forall (ecls WP TB) W -> Forall wpok WP ->
    Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI TB LB -> bsub FI AI OB LB -> bsub FI AI LBK LB -> idj TB OB -> idj TB LBK ->
    ekeep WP OB m m' /\ RHEAP_A FI AI s LB m'.
  Proof.
    intros W WP TB OB s LB m m' MU WM HCL HWP HWI HR TSUB OSUB KSUB TO TK.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000 /\ sh (FSB FI) + A0_FS_SHSIZE <= lo).
    { unfold sh, SHADOW_OFF in *. clear - B1 B2 B4 ACR CLO. repeat split; Z.div_mod_to_equations; lia. }
    destruct SHB as (SB1 & SB2 & SB3).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (BLK : forall b, In b LB -> 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling /\ 0x609000 <= blk_addr b
                    /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
                    /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b)).
    { intros b Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & R4 & R5 & R6 & R7). auto. }

    assert (DJ1 : forall a n, ((P <= a /\ a + n <= P + 504) \/ (a + n <= 0x609000 /\ 0 <= n)) -> disjoint_from WP a n -> 0 <= n -> disjoint_from W a n).
    { intros a n HA HD Hn. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJ2 : forall b, In b OB -> disjoint_from W (blk_addr b) (blk_size b)).
    { intros b Hb. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct (BLK b (OSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5).
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b' & Hb' & CL)]]]]]; try lia.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - assert (NE : b' <> b) by (apply (idj_neq TB OB b' b TO Hb' Hb)).
        destruct (am_blocks_disjoint FI AI s LB m b' b HR (TSUB b' Hb') (OSUB b Hb) NE); lia. }
    assert (FSW : Forall (fsw_iv FI) W).
    { eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *. unfold fsw_iv, app_iv, SH_HI. cbn [fst snd].
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (SK : forall X n, X + n <= 0x609000 -> shw m X n -> shw m' X n).
    { intros X n HX SW. apply (shw_frame_fs FI W m m' X n SW MU FSW). left. lia. }
    split; [unfold ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]|].
    - intros a cs HA HD C. eapply rw_cells_transport; [exact C| exact MU| exact WM|]. apply DJ1; [| exact HD| lia].
      destruct HA as [HA|[_ HA]]; [left; exact HA| right; split; [exact HA| lia]].
    - intros a bs HS HX B. eapply bytes_at_transport; [exact B| exact MU|]. apply DJ1; [right; lia| apply (dj_wpok_low WP _ _ HWP HX)| lia].
    - intros a n HS HX Wr. destruct (Z_le_gt_dec 0 n) as [Hn|Hn].
      + eapply wr_at_transport; [exact Wr| exact WM].
      + eapply wr_at_transport; [exact Wr| exact WM].
    - exact (bkeep_of_munch FI AI OB W m m' MU WM DJ2).
    - intros X n _ HX SW. exact (SK X n HX SW).
    - apply (apxF_of_munch FI AI ASL s_0 LB_0 LBK m0 m0 q st (pent_WA P) W m m' HR0 KSUB0 RF0 MU WM).
      eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]].
      + left. exact CL.
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl). left. cbn [FB_of]. lia.
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl). right; left. cbn [SB_of]. lia.
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl). right; right. lia.
      + right; right. exact (inside_sub WP (pent_WA P) x (y - x) CL HWI).
      + right; left. intros a Ha Hc. apply (fresh_block_not_aclient FI AI ASL s LB LBK b q m a HR (TSUB b Hb)); [| lia| lia|].
        * intros b0 Hb0. split; [exact (KSUB b0 Hb0)|]. intros ->. exact (idj_neq TB LBK b b TK Hb Hb0 eq_refl).
        * exact (fclient_aclient FI AI LBK q st m0 a RF0 Hc).
    - intros rs a CH. apply (fpchain_frame rs m m' _ q a W CH MU WM). eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia.
    - intros SHP. apply (shw_munch_gen W m m' P 504 SHP MU). intros a Ha.
      assert (HB : 0x7fff8000 <= a < 0x10007fff8000 /\ (a < SF \/ SF + 16 <= a)).
      { unfold sh, SHADOW_OFF in *. clear - Ha PLO PHI ACR PAF FAL SFB PAL. Z.div_mod_to_equations. lia. }
      apply disjoint_outside with (a := a) (n := 1); [| lia]. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia.
    - intros SHZ. exact (shz_stack_fs FI W m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FSW).
    - intros SHR. exact (shr_stack_fs FI W m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FSW).
    - apply (am_heap_frame FI AI s LB m m' W HR MU WM). eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]].
      + left. lia.
      + do 3 right; left. lia.
      + do 4 right. lia.
      + do 3 right; left. lia.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; [do 3 right; left; lia|].
        right; left. exists 0x5e68c8, 0x5e68d0. split; [| unfold a0_wsafe; lia]. apply AMS. unfold a0_static. split; [lia|]. env_band.
      + right; right; left. exists b. split; [exact (TSUB b Hb)| lia].
  Qed.

  Ltac plia := lazymatch goal with |- ?G => let H := fresh "PL" in assert (H : 0x609000 <= P -> G) by (clear; intros; lia); apply H; exact (proj1 (proj2 (proj2 (proj2 (proj2 POK))))) end.
  Ltac djw := unfold H_pent_seg.blk4W, H_pent_seg.blk2W, H_pent_seg.blk6cW, H_pent_seg.blk3cW, H_pent_seg.blk5cW; cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
  Ltac wpokP := repeat apply Forall_cons; try apply Forall_nil; left; unfold H_pent_seg.inP; cbn [fst snd]; plia.
  Ltac winP := repeat apply Forall_cons; try apply Forall_nil; unfold pent_WA; cbn [inside fst snd]; plia.
  Ltac clsP := repeat (apply Forall_cons; [split; [cbn [fst snd]; plia| do 4 right; left; cbn [inside fst snd]; plia]|]).
  Ltac ekc EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| djw].

  #[using="Type"] Lemma apxF_weaken2 : forall W W' (LB LB' : BL) q0 q1 (st0 st1 : fsstate FI) m m',
    apxF FI AI W LB' q1 st1 m m' -> q1 <= q0 -> (forall b, In b LB -> In b LB') -> (forall g, In g (fs_live FI st0) -> In g (fs_live FI st1)) ->
    (forall a, fclient FI AI LB q0 st0 a -> outside W' a -> outside W a) -> apxF FI AI W' LB q0 st0 m m'.
  Proof.
    intros W W' LB LB' q0 q1 st0 st1 m m' H HQ HL HF HO a Ha Hc Ho. apply H; [exact Ha| | exact (HO a Hc Ho)].
    eapply (fclient_weaken FI AI LB' LB q1 q0 st1 st0 a); eauto.
  Qed.
  #[using="ASL lo P m0 POK RF0 ws WSL"] Lemma blk_not_fclient : forall (s : PS) (LB : BL) m (b : BLK) a, RHEAP_A FI AI s LB m -> In b LB -> bsub FI AI LBK LB -> idj [b] LBK ->
    blk_addr b <= a < blk_addr b + blk_size b -> ~ fclient FI AI LBK q st a.
  Proof.
    intros s LB m b a HR Hb KSUB TK Ha Hc. pose proof POK as POK'. destruct POK' as (CLO & LO & _).
    apply (fresh_block_not_aclient FI AI ASL s LB LBK b q m a HR Hb); [| lia| exact Ha| exact (fclient_aclient FI AI LBK q st m0 a RF0 Hc)].
    intros b0 Hb0. split; [exact (KSUB b0 Hb0)|]. intros ->. exact (idj_neq [b] LBK b b TK (or_introl eq_refl) Hb0 eq_refl).
  Qed.

  Definition fcls (WP : list ivl) (VB : BL) (iv : ivl) : Prop :=
    fst iv < snd iv /\
    ( inside WP (fst iv) (snd iv - fst iv) \/ inFJ iv
      \/ (exists b, In b VB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ).

  #[using="ASL AMS m0 POK RF0 ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma ekeep_fk : forall (W WP : list ivl) (VB OB : BL) (s : PS) (LB : BL) qx (stx : fsstate FI) m m',
    munch ((lo, qx) :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W stx m m' -> lo <= qx <= q ->
    (forall g, In g (fs_live FI st) -> In g (fs_live FI stx)) -> (shw m P 504 -> shw m' P 504) ->
    Forall (fcls WP VB) W -> Forall wpok WP -> Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI VB LB -> bsub FI AI OB LB -> bsub FI AI LBK LB -> idj VB OB -> idj VB LBK ->
    ekeep WP OB m m' /\ RHEAP_A FI AI s LB m'.
  Proof.
    intros W WP VB OB s LB qx stx m m' MU WM FK QX LSUB SHPK HCL HWP HWI HR VSUB OSUB KSUB VO VK.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000 /\ sh (FSB FI) + A0_FS_SHSIZE <= lo).
    { unfold sh, SHADOW_OFF in *. clear - B1 B2 B4 ACR CLO. repeat split; Z.div_mod_to_equations; lia. }
    destruct SHB as (SB1 & SB2 & SB3).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (BLK : forall b, In b LB -> 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling /\ 0x609000 <= blk_addr b
                    /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
                    /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b)).
    { intros b Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & R4 & R5 & R6 & R7). auto. }

    assert (DJP : forall a n, P <= a -> a + n <= P + 504 -> disjoint_from WP a n -> 0 <= n -> disjoint_from W a n).
    { intros a n H1 H2 HD Hn. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - lia.
      - destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJS : forall a n, a + n <= 0x609000 -> disjoint_from WP a n -> 0 <= n -> disjoint_from ((lo, qx) :: FSIV W) a n).
    { intros a n H1 HD Hn. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
      apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - lia.
      - destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJ2 : forall b, In b OB -> disjoint_from ((lo, qx) :: FSIV W) (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (BLK b (OSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
      apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b' & Hb' & CL)]]; cbn [fst snd] in *.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - lia.
      - assert (NE : b' <> b) by (apply (idj_neq VB OB b' b VO Hb' Hb)).
        destruct (am_blocks_disjoint FI AI s LB m b' b HR (VSUB b' Hb') (OSUB b Hb) NE); lia. }
    assert (APW : app_ivs W).
    { eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd].
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - lia.
      - destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (FSW : Forall (fsw_iv FI) ((lo, qx) :: FSIV W)) by (apply fsw_cons_app; [apply app_iv_stack; exact CLO| apply fsw_FSIV; exact APW]).
    assert (SK : forall X n, X + n <= 0x609000 -> shw m X n -> shw m' X n).
    { intros X n HX SW. apply (shw_frame_fs FI _ m m' X n SW MU FSW). left. lia. }
    assert (LVP : lb (fs_live FI stx) P 504) by (exact (lb_mono _ _ _ _ PLB LSUB)).
    split; [unfold ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]|].
    - intros a cs HA HD C. destruct HA as [[H1 H2]|[_ HA]].
      + apply (rw_cells_fkeep FI W stx m m' a cs C FK WM); [left; apply (Contracts.lb_sub _ _ _ _ _ LVP); lia| apply DJP; [exact H1| exact H2| exact HD| lia]].
      + eapply rw_cells_transport; [exact C| exact MU| exact WM| apply DJS; [exact HA| exact HD| lia]].
    - intros a bs HS HX B. eapply bytes_at_transport; [exact B| exact MU|]. apply DJS; [lia| apply (dj_wpok_low WP _ _ HWP HX)| lia].
    - intros a n HS HX Wr. eapply wr_at_transport; [exact Wr| exact WM].
    - exact (bkeep_of_munch FI AI OB _ m m' MU WM DJ2).
    - intros X n _ HX SW. exact (SK X n HX SW).
    - eapply (apxF_weaken2 W (pent_WA P) LBK LBK q q st st m m'); [| lia| intros b Hb; exact Hb| intros g Hg; exact Hg|].
      + apply (apxF_of_munch_fkeep FI AI ASL s_0 LB_0 LBK m0 m0 q lo st W m m' HR0 KSUB0 RF0 CLO ltac:(lia)); [| exact WM|].
        * eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (O1 & O2). split; [lia| exact O2].
        * eapply (fkeep_weaken FI W W stx st m m' FK); [intros x Hx; exact Hx| exact LSUB].
      + intros a Hc Ho. apply outside_of_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL) Hr. cbn [fst snd] in *.
        destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
        * apply (inside_not_outside (pent_WA P) x (y - x) a (inside_sub WP (pent_WA P) x (y - x) CL HWI)); [lia| exact Ho].
        * apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl a); [left; cbn [FB_of]; lia| exact Hc].
        * apply (blk_not_fclient s LB m b a HR (VSUB b Hb) KSUB); [intros b1 b2 [E|[]] H2; subst b1; exact (VK b b2 Hb H2)| lia| exact Hc].
    - intros rs a CH. apply (fpchain_frame rs m m' _ q a _ CH MU WM). apply Forall_cons; [cbn [snd]; lia|]. apply Forall_cons; [cbn [snd]; lia|]. apply Forall_cons; [cbn [snd]; lia|].
      eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + lia.
      + destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia.
    - exact SHPK.
    - intros SHZ. exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FSW).
    - intros SHR. exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FSW).
    - apply (am_heap_frame FI AI s LB m m' _ HR MU WM). apply Forall_cons; [left; cbn [fst]; lia|].
      apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]. apply Forall_cons; [do 4 right; cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; [do 3 right; left; lia|].
        right; left. exists 0x5e68c8, 0x5e68d0. split; [| unfold a0_wsafe; lia]. apply AMS. unfold a0_static. split; [lia|]. env_band.
      + do 3 right; left. lia.
      + right; right; left. exists b. split; [exact (VSUB b Hb)| lia].
  Qed.

  #[using="ws WSL"] Lemma fpchain_keep : forall rs m m2 top bottom a,
    (forall X v, bottom <= X -> bytes_at asegs m X (le8 v) -> bytes_at asegs m2 X (le8 v)) ->
    fpchain m top bottom a rs -> fpchain m2 top bottom a rs.
  Proof.
    induction rs as [|r rest IH]; intros m m2 top bottom a TR CH; cbn [fpchain] in *; [exact CH|].
    destruct CH as (V & V16 & R1 & R2 & a' & R3 & CH'). unfold valid_frame, rd64 in *.
    split; [exact V|]. split; [exact V16|]. split; [split; [apply TR; [lia| exact (proj1 R1)]| exact (proj2 R1)]|]. split; [exact R2|].
    exists a'. split; [split; [apply TR; [lia| exact (proj1 R3)]| exact (proj2 R3)]|].
    eapply IH; [| exact CH']. intros X v HX B. apply TR; [lia| exact B].
  Qed.

  Definition acls (WP : list ivl) (TB : BL) (iv : ivl) : Prop :=
    fst iv < snd iv /\ ( inside WP (fst iv) (snd iv - fst iv) \/ (exists b, In b TB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ).

  #[using="ASL AMS m0 POK RF0 ws WSL"] Lemma ekeep_apxF : forall (W WP : list ivl) (TB OB LBc : BL) (s : PS) (LB : BL) q' (stc : fsstate FI) m m',
    apxF FI AI W LBc q' stc m m' -> alloc_ceiling <= q' -> q' <= q -> (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) ->
    Forall (acls WP TB) W -> Forall wpok WP -> Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI TB LB -> bsub FI AI OB LBc -> bsub FI AI OB LB -> bsub FI AI LBK LBc -> bsub FI AI LBK LB ->
    idj TB OB -> idj TB LBK ->
    shw m' P 504 ->
    ekeep WP OB m m'.
  Proof.
    intros W WP TB OB LBc s LB q' stc m m' AP QC QQ LSUB HCL HWP HWI HR TSUB OSUBc OSUB KSUBc KSUB TO TK SHP'.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (BLK : forall b, In b LB -> 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling /\ 0x609000 <= blk_addr b
                    /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
                    /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b)).
    { intros b Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & R4 & R5 & R6 & R7). auto. }
    assert (LVP : lb (fs_live FI stc) P 504) by (exact (lb_mono _ _ _ _ PLB LSUB)).
    assert (DJ1 : forall a n, ((P <= a /\ a + n <= P + 504) \/ a + n <= 0x609000) -> disjoint_from WP a n -> 0 <= n -> disjoint_from W a n).
    { intros a n HA HD Hn. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|(b & Hb & CL)].
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJH : forall a n, (alloc_ceiling <= a \/ (0x7fff7000 <= a /\ a + n <= 0x10007fff8000)) -> disjoint_from W a n).
    { intros a n HA. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|(b & Hb & CL)].
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    destruct sh_window_okE as (W1 & W2 & W3 & W4).
    assert (STKSH : forall a, sh lo - sh lo mod 8 <= a < sh q + 8 -> fclient FI AI LBc q' stc a /\ outside W a).
    { intros a Ha. assert (SLO : sh alloc_ceiling - sh alloc_ceiling mod 8 <= sh lo - sh lo mod 8).
      { pose proof (sh_mono alloc_ceiling lo CLO) as HM. clear - HM. Z.div_mod_to_equations. lia. }
      split.
      - right; left. exists (sh lo - sh lo mod 8), 0x10007fff8000. split; [| unfold SH_HI in W4; lia].
        apply AMS. unfold a0_static. split; [unfold SH_HI in W4; lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
      - apply disjoint_outside with (a := a) (n := 1); [| lia]. apply DJH. right. unfold SH_LO, SH_HI in *. lia. }
    unfold ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - intros a cs HA HD C. apply (apxF_rw_cells FI AI W LBc q' stc m m' a cs AP C); [| apply DJ1; [destruct HA as [HA|[_ HA]]; [left; exact HA| right; exact HA]| exact HD| lia]].
      destruct HA as [[H1 H2]|[HS HA]].
      + apply fclient_range_lb. apply (Contracts.lb_sub _ _ _ _ _ LVP); lia.
      + apply (fclient_range_static FI AI LBc q' stc a _ a (a + Z.of_nat (cells_size cs)) (AMS _ _ HS)); lia.
    - intros a bs HS HX B. apply (apxF_bytes_at FI AI W LBc q' stc m m' a bs AP B).
      + apply (fclient_range_static FI AI LBc q' stc a _ a (a + Z.of_nat (length bs)) (AMS _ _ HS)); lia.
      + apply DJ1; [right; lia| apply (dj_wpok_low WP _ _ HWP HX)| lia].
    - intros a n HS HX Wr. apply (apxF_wr_at FI AI W LBc q' stc m m' a n AP Wr).
      + apply (fclient_range_static FI AI LBc q' stc a _ a (a + n) (AMS _ _ HS)); lia.
      + destruct (Z_le_gt_dec 0 n) as [Hn|Hn]; [apply DJ1; [right; lia| apply (dj_wpok_low WP _ _ HWP HX)| lia]|].
        apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
        destruct CL as [CL|(b & Hb & CL)]; [destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia| destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5); lia].
    - intros b X cs Hb L1 L2 C. apply (apxF_rw_cells FI AI W LBc q' stc m m' X cs AP C); [apply (fclient_range_block FI AI LBc q' stc X _ b (OSUBc b Hb) L1 L2)|].
      destruct (BLK b (OSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5).
      apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|(b' & Hb' & CL)].
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + assert (NE : b' <> b) by (apply (idj_neq TB OB b' b TO Hb' Hb)).
        destruct (am_blocks_disjoint FI AI s LB m b' b HR (TSUB b' Hb') (OSUB b Hb) NE); lia.
    - intros X n X1 X2 SW. pose proof (shw_win_ok _ _ _ SW) as [Hn _].
      eapply (shw_band_eq m m' X n 0x7fffa000 0x800b9200 SW).
      + intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) _ _)) Hv).
        * right; left. exists 0x7fffa000, 0x800b9200. split; [| lia]. apply AMS. unfold a0_static. split; [lia|]. do 11 right. left. lia.
        * apply disjoint_outside with (a := a) (n := 1); [| lia]. apply DJH. right. lia.
      + lia.
      + lia.
      + reflexivity.
      + reflexivity.
      + unfold sh, SHADOW_OFF. clear - X1. Z.div_mod_to_equations. lia.
      + intros _. unfold sh, SHADOW_OFF. clear - X2 Hn. Z.div_mod_to_equations. lia.
    - eapply (apxF_weaken2 W (pent_WA P) LBK LBc q q' st stc m m' AP QQ KSUBc LSUB).
      intros a Hc Ho. apply outside_of_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL) Hr. cbn [fst snd] in *.
      destruct CL as [CL|(b & Hb & CL)].
      + apply (inside_not_outside (pent_WA P) x (y - x) a (inside_sub WP (pent_WA P) x (y - x) CL HWI)); [lia| exact Ho].
      + apply (blk_not_fclient s LB m b a HR (TSUB b Hb) KSUB); [intros b1 b2 [E|[]] H2; subst b1; exact (TK b b2 Hb H2)| lia| exact Hc].
    - intros rs a CH. apply (fpchain_keep rs m m' _ q a); [| exact CH]. intros X v HX B.
      apply (apxF_bytes_at FI AI W LBc q' stc m m' X _ AP B); [apply fclient_range_above; lia| apply DJH; left; lia].
    - intros _. exact SHP'.
    - intros SHZ a Ha. destruct (STKSH a ltac:(lia)) as [C O]. exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) (SHZ a Ha)).
    - intros SHR a Ha. destruct (SHR a Ha) as [v Hv]. exists v. destruct (STKSH a Ha) as [C O]. exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) Hv).
  Qed.

  #[using="Type"] Lemma ekeep_trans : forall WP OB m1 m2 m3, ekeep WP OB m1 m2 -> ekeep WP OB m2 m3 -> ekeep WP OB m1 m3.
  Proof.
    intros WP OB m1 m2 m3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    unfold ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - intros a cs HA HD C. exact (C1 a cs HA HD (A1 a cs HA HD C)).
    - intros a bs HS HX B. exact (C2 a bs HS HX (A2 a bs HS HX B)).
    - intros a n HS HX Wr. exact (C3 a n HS HX (A3 a n HS HX Wr)).
    - exact (bkeep_trans FI AI OB m1 m2 m3 A4 C4).
    - intros X n X1 X2 SW. exact (C5 X n X1 X2 (A5 X n X1 X2 SW)).
    - exact (apxF_trans FI AI _ _ _ _ m1 m2 m3 A6 C6).
    - intros rs a CH. exact (C7 rs a (A7 rs a CH)).
    - intros H. exact (C8 (A8 H)).
    - intros H. exact (C9 (A9 H)).
    - intros H. exact (C10 (A10 H)).
  Qed.

  #[using="Type"] Lemma ekeep_weaken : forall WP WP' OB m m', ekeep WP OB m m' -> (forall a n, disjoint_from WP' a n -> disjoint_from WP a n) -> ekeep WP' OB m m'.
  Proof.
    intros WP WP' OB m m' (A1 & A2) HS. split; [| exact A2]. intros a cs HA HD C. exact (A1 a cs HA (HS _ _ HD) C).
  Qed.

  #[using="Type"] Lemma ekeep_sub : forall WP OB OB' m m', ekeep WP OB m m' -> bsub FI AI OB' OB -> ekeep WP OB' m m'.
  Proof.
    intros WP OB OB' m m' (A1 & A2 & A3 & A4 & AR) HS. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [| exact AR].
    exact (bkeep_sub FI AI OB OB' m m' A4 HS).
  Qed.

  #[using="ws WSL"] Lemma ek_meth : forall WP OB m m' meth, ekeep WP OB m m' -> disjoint_from WP P 8 -> p_meth m P meth -> p_meth m' P meth.
  Proof. intros WP OB m m' meth EK DJ [C R]. split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="ws WSL"] Lemma ek_ent : forall WP OB m m' eb el, ekeep WP OB m m' -> disjoint_from WP (P + 384) 16 -> p_ent m P eb el -> p_ent m' P eb el.
  Proof. intros WP OB m m' eb el EK DJ C. unfold p_ent in *. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="ws WSL"] Lemma ek_ctl : forall WP OB m m' err hack pos entp clen csz esp, ekeep WP OB m m' -> disjoint_from WP (P + 440) 40 ->
    p_ctl m P err hack pos entp clen csz esp -> p_ctl m' P err hack pos entp clen csz esp.
  Proof.
    intros WP OB m m' err hack pos entp clen csz esp EK DJ [C R]. split; [| exact R].
    apply (ek_pcell WP OB m m' _ _ EK); [lia| unfold p_ctl_cells; simpl_sizes; lia| unfold p_ctl_cells; simpl_sizes; exact DJ| exact C].
  Qed.
  #[using="ws WSL"] Lemma ek_scan : forall WP OB m m' cur, ekeep WP OB m m' -> disjoint_from WP (P + 480) 20 -> p_scan m P cur -> p_scan m' P cur.
  Proof. intros WP OB m m' cur EK DJ C. unfold p_scan in *. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="ws WSL"] Lemma ek_msg : forall WP OB (LB : BL) m m' A len cap okm bs, ekeep WP OB m m' -> disjoint_from WP (P + 400) 32 -> bsub FI AI (okbA FI AI okm A cap) OB ->
    p_msg FI AI m LB P A len cap okm bs -> p_msg FI AI m' LB P A len cap okm bs.
  Proof.
    intros WP OB LB m m' A len cap okm bs EK DJ SUB (MBC & OWN & R1 & R2 & R3). pose proof EK as (_ & _ & _ & BK & _).
    split; [apply (ek_pcell WP OB m m' _ _ EK); [lia| unfold mbuf_cells; simpl_sizes; lia| unfold mbuf_cells; simpl_sizes; exact DJ| exact MBC]|].
    split; [| split; [exact R1| split; [exact R2| exact R3]]].
    destruct okm as [k|]; cbn [mownA] in *; [| exact OWN]. destruct OWN as [HIN TXC]. split; [exact HIN|].
    apply (BK (k, A, cap + 1) A _ (SUB _ (or_introl eq_refl))); [cbn [blk_addr fst snd]; lia| | exact TXC].
    cbn [blk_addr blk_size fst snd cells_size csize]. destruct TXC as [[W _] _]. cbn in W. lia.
  Qed.

  #[using="POK ws WSL"] Lemma EX_move : forall WP OB (s : PS) (LB : BL) m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
      (s' : PS) (LB' : BL) m' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth',
    EX s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth ->
    ekeep WP OB m m' -> Forall wpok WP -> disjoint_from WP (P + 224) 8 -> disjoint_from WP (P + 264) 24 ->
    RHEAP_A FI AI s' LB' m' -> p_scan m' P cur' -> p_msg FI AI m' LB' P A' len' cap' okm' bs' -> 0 <= cur' <= len' ->
    p_ent m' P eb' el' -> p_ctl m' P err' hack' pos' entp' clen' csz' esp' -> p_hlist FI AI m' P ns' hs' X' -> p_meth m' P meth' ->
    bsub FI AI (hl_blocks FI AI ns' hs' ++ okbA FI AI okm' A' cap' ++ LBK) LB' ->
    NoDup (map blk_id (hl_blocks FI AI ns' hs' ++ okbA FI AI okm' A' cap' ++ LBK)) ->
    (exists ev, clow canary ev m') ->
    (exists k d, esteps k d (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s') LB' /\ 0 <= k <= M0 + 1 /\ 0 <= d <= c0 /\ 5 * (am_nsec FI AI s' - k) <= PH0 + HCount.phiH FI AI hs' /\ Z.of_nat (length LB') <= NB0 + 4 * Z.of_nat (length hs')) ->
    H_phdr.hsumA FI AI hs' <= HS0 + c0 ->
    EX s' LB' m' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth'.
  Proof.
    intros WP OB s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
           s' LB' m' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth'
           (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & PRS & SUB & ND & STAT & APF & ES & _)
           EK HW DJ1 DJ2 HR' PSC' PMSG' CUR' PENT' PCTL' PHL' PMETH' SUB' ND' CL' ES' HSF'.
    unfold EX. split; [exact HR'|]. split; [exact PSC'|]. split; [exact PMSG'|]. split; [exact CUR'|]. split; [exact PENT'|]. split; [exact PCTL'|].
    split; [exact PHL'|]. split; [exact PMETH'|].
    split. { destruct PVER as ((pad & C) & R). split; [| exact R]. exists pad. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ2| exact C]. }
    split. { destruct PRS as (C & R). split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ1| exact C]. }
    split; [exact SUB'|]. split; [exact ND'|]. split; [exact (ek_stat WP OB m m' EK HW STAT CL')|].
    split; [eapply (apxF_trans FI AI); [exact APF| destruct EK as (_ & _ & _ & _ & _ & K5 & _); exact K5]|].
    split; [exact ES'| exact HSF'].
  Qed.

  #[using="P POK ws WSL"] Lemma pWE_cls : Forall (ecls [] []) pWE.
  Proof.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & _).
    unfold H_pent_seg.pWE, ecls. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [lia|]).
    - left. lia.
    - right; left. lia.
    - right; right; left. lia.
    - right; right; right; left. lia.
  Qed.

  #[using="ASL AMS POK RF0 ws HR0 KSUB0 WSL"] Lemma exitJ : forall pc q' r (s : PS) (LB : BL) m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    okm <> None -> retire_pc pc -> EX s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth -> pinv q' m ->
    (r <> 3 -> ent_okA gmax entp cur esp csz el) -> 0 <= r <= 5 -> r <> 4 ->
    AJ FI AI J POST (retstA pc q' r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 m) s LB.
  Proof.
    intros pc q' r s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 OKN RP EXF INV EOK R1 R2.
    apply aj_cps. unfold H_pent_seg.retstA.
    eapply evt_mono.
    { apply (retireE pc q' r (fun mm => munch pWE m mm /\ wmono asegs m mm)); [exact RP| exact INV| split; [apply munch_refl| apply wmono_refl]|].
      intros ma mb [MU1 WM1] MU2 WM2. split; [eapply munch_trans; eassumption| eapply wmono_trans; eassumption]. }
    intros ms' (r0 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MI & LIVE & RF & ST & AE & (MU & WM) & ->).
    apply (aj_ret FI AI J).
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & _ & _ & SUB & ND & (_ & _ & _ & _ & _ & _ & CL & _) & _ & SCR & HSF).
    assert (OSUB : bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap) LB).
    { intros b Hb. apply SUB. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; left; exact Hb]. }
    assert (KSUB : bsub FI AI LBK LB) by (intros b Hb; apply SUB; apply in_or_app; right; apply in_or_app; right; exact Hb).
    destruct (ekeep_munch pWE [] [] (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap) s LB m m' MU WM pWE_cls (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    eapply (EX_done s LB m' st' cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth r); [exact OKN| | exact MI| exact ST| exact AE| exact RF| exact LIVE| exact EOK| exact R1| exact R2].
    eapply (EX_move [] _ s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth s LB m'); [exact EXF| exact EK| apply Forall_nil| exact I| exact I| exact HR'
      | exact (ek_scan _ _ m m' cur EK I PSC)
      | apply (ek_msg _ _ LB m m' A len cap okm bs EK I); [intros b Hb; apply in_or_app; right; exact Hb| exact PMSG]
      | exact CUR
      | exact (ek_ent _ _ m m' eb el EK I PENT)
      | exact (ek_ctl _ _ m m' _ _ _ _ _ _ _ EK I PCTL)
      | apply (ek_hlist _ _ m m' ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| exact I]
      | exact (ek_meth _ _ m m' meth EK I PMETH)
      | exact SUB| exact ND
      | exact (ek_clow _ _ m m' EK (Forall_nil _) I CL)
      | exact SCR| exact HSF].
  Qed.

  #[using="P POK ws WSL"] Lemma pWE_clsG : forall WP TB, Forall (ecls WP TB) pWE.
  Proof.
    intros WP TB. eapply Forall_impl; [| exact pWE_cls]. intros iv (H1 & H2). split; [exact H1|].
    destruct H2 as [H2|[H2|[H2|[H2|[H2|(b & [] & _)]]]]]; [left; exact H2| right; left; exact H2| right; right; left; exact H2| right; right; right; left; exact H2| destruct H2].
  Qed.
  #[using="Type"] Lemma OB_sub : forall (LB : BL) ns hs okm A cap, bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap ++ LBK) LB ->
    bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap) LB /\ bsub FI AI LBK LB.
  Proof.
    intros LB ns hs okm A cap SUB. split; intros b Hb; apply SUB.
    - apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; left; exact Hb].
    - apply in_or_app; right; apply in_or_app; right; exact Hb.
  Qed.

  #[using="ASL AMS POK RF0 ws HR0 KSUB0 WSL"] Lemma case4 : forall q' (s : PS) (LB : BL) m cur A len cap okm bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    okm <> None -> EX s LB m cur A len cap okm bs eb el err hack pos 4 clen csz esp ns hs X meth -> pinv q' m -> ent_okA gmax 4 cur esp csz el ->
    AJ FI AI J POST (blkstA q' 0x89f24 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m cur A len cap okm bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 OKN EXF INV EOK.
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & _ & SUB & ND & (SHP & _ & _ & _ & _ & _ & CL & _) & _ & SCR & HSF).
    destruct (OB_sub LB ns hs okm A cap SUB) as [OSUB KSUB].
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    destruct PVER as ((pad & VC) & _). split_chunk VC 1%nat DISC VR. clear VR.
    pose proof PMSG as (MBC & OWN & LENC & CAPB & NUL). unfold LMAX_A in CAPB.
    destruct (ent4_join m eb el A len cap PENT MBC) as [E4 M2].
    pose proof PCTL as (CTLC & CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (_ & _ & _ & _ & _ & _ & _ & C472).
    pose proof PSC as PSC'. unfold p_scan in PSC'. split_chunk PSC' 1%nat S1 S2. split_chunk S2 1%nat CURC S3.
    apply aj_cps. eapply evt_mono.
    { exact (blk4E q' 0 A len esp eb el (wz cur) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV SHP ltac:(lia) CR7 DISC E4 C472 CURC). }
    intros ms' (r0 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MI & LIVE & RF & ST & AE & (MU & WM & _ & E4' & _ & CUR') & ->).
    apply (aj_ret FI AI J).
    destruct (ekeep_munch (blk4W ++ pWE) blk4W [] (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap) s LB m m' MU WM) as [EK HR'];
      [apply Forall_app; split; [unfold H_pent_seg.blk4W; clsP; apply Forall_nil| apply pWE_clsG]| unfold H_pent_seg.blk4W; wpokP| unfold H_pent_seg.blk4W; winP| exact HR
       | intros b []| exact OSUB| exact KSUB| intros a b []| intros a b []|].
    assert (M2' : rw_cells asegs m' (P + 416) [C8 (wz cap); C8 (wz MEMBUF_DEF_SIZE_INC)]) by (apply (ek_pcell _ _ m m' _ _ EK); [lia| simpl_sizes; lia| djw| exact M2]).
    destruct (ent4_split m' _ _ A len cap E4' M2') as [PENT' MBC'].
    assert (S1' : rw_cells asegs m' (P + 480) [C8 (wz (P + 400))]) by (apply (ek_pcell _ _ m m' _ _ EK); [lia| simpl_sizes; lia| djw| exact S1]).
    assert (S3' : rw_cells asegs m' (P + 496) [C4 (wz 0)]) by (apply (ek_pcell _ _ m m' _ _ EK); [lia| simpl_sizes; lia| djw| exact S3]).
    join_chunks CUR' S3' J2. join_chunks S1' J2 PSC2.
    eapply (EX_done s LB m' st' len A len cap okm bs _ _ err hack pos 4 clen csz esp ns hs X meth 2); [exact OKN| | exact MI| exact ST| exact AE| exact RF| exact LIVE| | lia| lia].
    eapply (EX_move blk4W _ s LB m cur A len cap okm bs eb el err hack pos 4 clen csz esp ns hs X meth s LB m'); [exact EXF| exact EK| unfold H_pent_seg.blk4W; wpokP| djw| djw| exact HR'
      | exact PSC2
      | split; [exact MBC'|]; destruct (ek_msg _ _ LB m m' A len cap okm bs EK ltac:(djw) ltac:(intros b Hb; apply in_or_app; right; exact Hb) PMSG) as (_ & OWN' & R'); split; [exact OWN'| exact R']
      | lia
      | exact PENT'
      | exact (ek_ctl _ _ m m' _ _ _ _ _ _ _ EK ltac:(djw) PCTL)
      | apply (ek_hlist _ _ m m' ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| djw]
      | exact (ek_meth _ _ m m' meth EK ltac:(djw) PMETH)
      | exact SUB| exact ND
      | exact (ek_clow _ _ m m' EK ltac:(unfold H_pent_seg.blk4W; wpokP) ltac:(djw) CL)
      | exact SCR| exact HSF].
    intros _. destruct EOK as (E1 & E2 & E3). split; [intros _; specialize (E1 ltac:(lia)); lia|]. split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx].
  Qed.

  #[using="ASL AMS POK RF0 ws HR0 KSUB0 WSL"] Lemma case2 : forall q' (s : PS) (LB : BL) m cur A len cap okm bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    okm <> None -> EX s LB m cur A len cap okm bs eb el err hack pos 2 clen csz esp ns hs X meth -> pinv q' m -> ent_okA gmax 2 cur esp csz el ->
    AJ FI AI J POST (blkstA q' 0x8a0c0 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m cur A len cap okm bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 OKN EXF INV EOK.
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & _ & SUB & ND & (SHP & _ & _ & _ & _ & _ & CL & _) & _ & SCR & HSF).
    destruct (OB_sub LB ns hs okm A cap SUB) as [OSUB KSUB].
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct PVER as ((pad & VC) & _). split_chunk VC 1%nat DISC VR. clear VR.
    destruct (p_msg_facts FI AI m LB P A len cap okm bs s HR PMSG) as (HL & HCp & LBS0 & NONE & SOME). unfold LMAX_A in HCp.
    pose proof PMSG as (MBC & OWN & _ & _ & NUL).
    destruct (ent4_join m eb el A len cap PENT MBC) as [E4 M2].
    pose proof PCTL as (CTLC & CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (C440 & C444 & C448 & C452 & C456 & C460 & C464 & C472).
    assert (ESP : esp <= cur) by (destruct EOK as (E1 & _); apply E1; lia).
    assert (AR : 0 <= A < 2^63).
    { destruct okm as [k|]; [destruct (SOME ltac:(discriminate)) as (S1 & S2 & _); lia| destruct (NONE eq_refl) as (-> & _); lia]. }
    apply aj_cps. eapply evt_mono.
    { apply (blk2E q' A len cap esp clen eb el (wz pos) bs x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV SHP ltac:(lia) ltac:(lia) ltac:(lia) CR5 AR DISC E4 C448 C456 C472).
      intros LT. destruct okm as [k|]; [| destruct (NONE eq_refl) as (_ & -> & _); exfalso; lia].
      destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6). cbn [mownA] in OWN. destruct OWN as [HIN TXC].
      split; [unfold H_pent_seg.outX; cbn [fst snd]; lia|]. split; [exact S4| exact TXC]. }
    intros ms' (r0 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MI & LIVE & RF & ST & AE & (WM & _ & _ & _ & ARMS)).
    apply (aj_ret FI AI J).
    assert (EOK' : forall el', ent_okA gmax 2 cur esp csz el').
    { intros el'. split; [intros _; exact ESP|]. split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx]. }
    destruct ARMS as [(-> & LT & MU & E4' & C448')|(-> & GE & E4' & C448' & [(EQ & MU)|(LT & MU & TXC')])].
    -
      destruct (ekeep_munch (blk2W ++ pWE) blk2W [] (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap) s LB m m' MU WM) as [EK HR'];
        [apply Forall_app; split; [unfold H_pent_seg.blk2W; clsP; apply Forall_nil| apply pWE_clsG]| unfold H_pent_seg.blk2W; wpokP| unfold H_pent_seg.blk2W; winP| exact HR
         | intros b []| exact OSUB| exact KSUB| intros a b []| intros a b []|].
      ekc EK M2. destruct (ent4_split m' _ _ A len cap E4' M2) as [PENT' MBC'].
      ekc EK C440. ekc EK C444. ekc EK C452. ekc EK C456. ekc EK C460. ekc EK C464. ekc EK C472.
      pose proof (pctl_join m' err hack pos 2 clen csz esp C440 C444 C448' C452 C456 C460 C464 C472) as CTL'.
      eapply (EX_done s LB m' st' cur A len cap okm bs _ _ err hack pos 2 clen csz esp ns hs X meth 1); [exact OKN| | exact MI| exact ST| exact AE| exact RF| exact LIVE| intros _; apply EOK'| lia| lia].
      eapply (EX_move blk2W _ s LB m cur A len cap okm bs eb el err hack pos 2 clen csz esp ns hs X meth s LB m'); [exact EXF| exact EK| unfold H_pent_seg.blk2W; wpokP| djw| djw| exact HR'
        | exact (ek_scan _ _ m m' cur EK ltac:(djw) PSC)
        | split; [exact MBC'|]; destruct (ek_msg _ _ LB m m' A len cap okm bs EK ltac:(djw) ltac:(intros b Hb; apply in_or_app; right; exact Hb) PMSG) as (_ & OWN' & R'); split; [exact OWN'| exact R']
        | exact CUR
        | exact PENT'
        | split; [exact CTL'| repeat (split; [assumption|]); assumption]
        | apply (ek_hlist _ _ m m' ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| djw]
        | exact (ek_meth _ _ m m' meth EK ltac:(djw) PMETH)
        | exact SUB| exact ND
        | exact (ek_clow _ _ m m' EK ltac:(unfold H_pent_seg.blk2W; wpokP) ltac:(djw) CL)
        | exact SCR| exact HSF].
    -
      destruct (ekeep_munch (blk2W ++ pWE) blk2W [] (hl_blocks FI AI ns hs ++ okbA FI AI okm A cap) s LB m m' MU WM) as [EK HR'];
        [apply Forall_app; split; [unfold H_pent_seg.blk2W; clsP; apply Forall_nil| apply pWE_clsG]| unfold H_pent_seg.blk2W; wpokP| unfold H_pent_seg.blk2W; winP| exact HR
         | intros b []| exact OSUB| exact KSUB| intros a b []| intros a b []|].
      ekc EK M2. destruct (ent4_split m' _ _ A len cap E4' M2) as [PENT' MBC'].
      ekc EK C440. ekc EK C444. ekc EK C452. ekc EK C456. ekc EK C460. ekc EK C464. ekc EK C472.
      pose proof (pctl_join m' err hack 4 2 clen csz esp C440 C444 C448' C452 C456 C460 C464 C472) as CTL'.
      eapply (EX_done s LB m' st' cur A len cap okm bs _ _ err hack 4 2 clen csz esp ns hs X meth 0); [exact OKN| | exact MI| exact ST| exact AE| exact RF| exact LIVE| intros _; apply EOK'| lia| lia].
      eapply (EX_move blk2W _ s LB m cur A len cap okm bs eb el err hack pos 2 clen csz esp ns hs X meth s LB m'); [exact EXF| exact EK| unfold H_pent_seg.blk2W; wpokP| djw| djw| exact HR'
        | exact (ek_scan _ _ m m' cur EK ltac:(djw) PSC)
        | split; [exact MBC'|]; destruct (ek_msg _ _ LB m m' A len cap okm bs EK ltac:(djw) ltac:(intros b Hb; apply in_or_app; right; exact Hb) PMSG) as (_ & OWN' & R'); split; [exact OWN'| exact R']
        | exact CUR
        | exact PENT'
        | split; [exact CTL'| repeat (split; [first [assumption| lia]|]); lia]
        | apply (ek_hlist _ _ m m' ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| djw]
        | exact (ek_meth _ _ m m' meth EK ltac:(djw) PMETH)
        | exact SUB| exact ND
        | exact (ek_clow _ _ m m' EK ltac:(unfold H_pent_seg.blk2W; wpokP) ltac:(djw) CL)
        | exact SCR| exact HSF].
    -
      destruct okm as [k|]; [| destruct (NONE eq_refl) as (_ & -> & _); exfalso; lia].
      destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6). cbn [mownA] in OWN. destruct OWN as [HIN TXC].
      cbn [okbA] in *.
      assert (NDX : idj [(k, A, cap + 1)] (hl_blocks FI AI ns hs) /\ idj [(k, A, cap + 1)] LBK).
      { apply nd_app in ND. destruct ND as (_ & I1 & ND2). apply (nd_app [(k, A, cap + 1)] LBK) in ND2. destruct ND2 as (_ & I2 & _).
        split; [apply idj_sym; intros a b Ha Hb; apply (I1 a b Ha); apply in_or_app; left; exact Hb| exact I2]. }
      destruct NDX as [TO TK].
      destruct (ekeep_munch ((A + (esp + clen), A + (esp + clen) + 1) :: blk2W ++ pWE) blk2W [(k, A, cap + 1)] (hl_blocks FI AI ns hs) s LB m m' MU WM) as [EK HR'];
        [apply Forall_cons; [split; [cbn [fst snd]; lia| do 5 right; exists (k, A, cap + 1); cbn [blk_addr blk_size fst snd]; split; [left; reflexivity| lia]]|];
         apply Forall_app; split; [unfold H_pent_seg.blk2W; clsP; apply Forall_nil| apply pWE_clsG]| unfold H_pent_seg.blk2W; wpokP| unfold H_pent_seg.blk2W; winP| exact HR
         | intros b [<-|[]]; exact HIN| intros b Hb; apply SUB; apply in_or_app; left; exact Hb| exact KSUB| exact TO| exact TK|].
      ekc EK M2. destruct (ent4_split m' _ _ A len cap E4' M2) as [PENT' MBC'].
      ekc EK C440. ekc EK C444. ekc EK C452. ekc EK C456. ekc EK C460. ekc EK C464. ekc EK C472.
      pose proof (pctl_join m' err hack 4 2 clen csz esp C440 C444 C448' C452 C456 C460 C464 C472) as CTL'.
      eapply (EX_done s LB m' st' cur A len cap (Some k) _ _ _ err hack 4 2 clen csz esp ns hs X meth 0); [discriminate| | exact MI| exact ST| exact AE| exact RF| exact LIVE| intros _; apply EOK'| lia| lia].
      eapply (EX_move blk2W _ s LB m cur A len cap (Some k) bs eb el err hack pos 2 clen csz esp ns hs X meth s LB m'); [exact EXF| exact EK| unfold H_pent_seg.blk2W; wpokP| djw| djw| exact HR'
        | exact (ek_scan _ _ m m' cur EK ltac:(djw) PSC)
        | split; [exact MBC'|]; split; [cbn [mownA]; split; [exact HIN| exact TXC']|]; split; [lia|]; split; [unfold LMAX_A; lia|];
          rewrite P0.H_presp_B.set_byte_other; [exact NUL| rewrite <- (Nat2Z.id (length bs)), LBS0; lia| lia]
        | exact CUR
        | exact PENT'
        | split; [exact CTL'| repeat (split; [first [assumption| lia]|]); lia]
        | apply (ek_hlist _ _ m m' ns hs X EK PHL); [intros b Hb; exact Hb| djw]
        | exact (ek_meth _ _ m m' meth EK ltac:(djw) PMETH)
        | exact SUB| exact ND
        | exact (ek_clow _ _ m m' EK ltac:(unfold H_pent_seg.blk2W; wpokP) ltac:(djw) CL)
        | exact SCR| exact HSF].
  Qed.

  #[using="ws GMX WSL"] Lemma pe_measA_nonneg : forall entp cur esp csz el, ent_okA gmax entp cur esp csz el -> 0 <= pe_measA entp el.
  Proof.
    intros entp cur esp csz el (_ & E2 & _). unfold pe_meas0. destruct (entp =? 1) eqn:Q1; [lia|].
    destruct (entp =? 3) eqn:Q3; [apply Z.eqb_eq in Q3; destruct (E2 (or_introl Q3)) as (elen & -> & R); rewrite unsigned_lit by lia; lia|].
    destruct (entp =? 5) eqn:Q5; [apply Z.eqb_eq in Q5; destruct (E2 (or_intror Q5)) as (elen & -> & R); rewrite unsigned_lit by lia; lia| lia].
  Qed.
  Definition CONT (M : Z) : Prop :=
    forall (s : PS) (LB : BL) m q' cur A len cap (kA : K) bs eb el err hack pos entp clen csz esp ns hs X meth
           x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31,
      EI s LB m q' cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth -> pe_measA entp el < M ->
      AJ FI AI J POST (dispstA q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m) s LB.

  #[using="POK GMX WSL GLR"] Lemma EI_move : forall WP OB (s : PS) (LB : BL) m q' cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
      (s' : PS) (LB' : BL) m' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth',
    EI s LB m q' cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth ->
    ekeep WP OB m m' -> Forall wpok WP -> disjoint_from WP (P + 224) 8 -> disjoint_from WP (P + 264) 24 ->
    RHEAP_A FI AI s' LB' m' -> pinv q' m' -> p_scan m' P cur' -> p_msg FI AI m' LB' P A' len' cap' okm' bs' -> 0 <= cur' <= len' ->
    p_ent m' P eb' el' -> p_ctl m' P err' hack' pos' entp' clen' csz' esp' -> p_hlist FI AI m' P ns' hs' X' -> p_meth m' P meth' ->
    bsub FI AI (hl_blocks FI AI ns' hs' ++ okbA FI AI okm' A' cap' ++ LBK) LB' ->
    NoDup (map blk_id (hl_blocks FI AI ns' hs' ++ okbA FI AI okm' A' cap' ++ LBK)) ->
    (exists ev, clow canary ev m') -> ent_okA gmax entp' cur' esp' csz' el' ->
    X' + 2 * (len' - cur') <= 2^27 + 64 ->
    ebud (pe_measA entp' el' + 1) (len' - cur') (HCount.cgG FI AI hs') s' LB' -> len' - cur' <= c0 -> H_phdr.hsumA FI AI hs' <= HS0 ->
    (exists k0, esteps k0 0 (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s') LB' /\ 0 <= k0 /\ k0 + pe_measA entp' el' <= M0
                /\ 5 * (am_nsec FI AI s' - k0) <= PH0 + HCount.phiH FI AI hs' /\ Z.of_nat (length LB') <= NB0 + 4 * Z.of_nat (length hs')) ->
    EI s' LB' m' q' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth'.
  Proof.
    intros WP OB s LB m q' cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth
           s' LB' m' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth'
           (EXF & _ & _ & ST2 & _ & CH & _) EK HW DJ1 DJ2 HR' INV' PSC' PMSG' CUR' PENT' PCTL' PHL' PMETH' SUB' ND' CL' EOK' XB' BUD' CB' HSS' DELS'.
    assert (SCR' : exists k d, esteps k d (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s') LB' /\ 0 <= k <= M0 + 1 /\ 0 <= d <= c0 /\ 5 * (am_nsec FI AI s' - k) <= PH0 + HCount.phiH FI AI hs' /\ Z.of_nat (length LB') <= NB0 + 4 * Z.of_nat (length hs')).
    { destruct DELS' as (k0 & ES0 & K0 & KM & KC & KN). pose proof (pe_measA_nonneg _ _ _ _ _ EOK') as MP. exists k0, 0. split; [exact ES0|]. clear - K0 KM KC KN MP CB' CUR'. lia. }
    unfold EI.
    split; [exact (EX_move WP OB s LB m cur A len cap okm bs eb el err hack pos entp clen csz esp ns hs X meth s' LB' m' cur' A' len' cap' okm' bs' eb' el' err' hack' pos' entp' clen' csz' esp' ns' hs' X' meth'
                     EXF EK HW DJ1 DJ2 HR' PSC' PMSG' CUR' PENT' PCTL' PHL' PMETH' SUB' ND' CL' SCR' ltac:(clear - HSS' CB' CUR'; lia))|].
    split; [exact INV'|]. split; [exact XB'|]. split; [exact (ek_stat2 WP OB m m' EK ST2)|]. split; [exact (conj BUD' (conj CB' (conj HSS' DELS')))|].
    split; [destruct EK as (_ & _ & _ & _ & _ & _ & K7 & _); exact (K7 _ _ CH)| exact EOK'].
  Qed.

  #[using="Type"] Lemma pctx_back : forall (LB : BL) m A len cap cur bs (kA : K), pctx A len cap cur bs m -> In (kA, A, cap + 1) LB ->
    0 <= len <= cap -> cap + 1 <= LMAX_A -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    p_scan m P cur /\ p_msg FI AI m LB P A len cap (Some kA) bs /\ (exists ev, clow canary ev m).
  Proof.
    intros LB m A len cap cur bs kA (SC & MBC & TXT & _ & _ & _ & _ & _ & _ & _ & CLW & _) HIN LC CB NUL.
    split; [exact SC|]. split; [| exact CLW]. split; [exact MBC|]. split; [cbn [mownA]; split; [exact HIN| exact TXT]|]. split; [exact LC|]. split; [exact CB| exact NUL].
  Qed.
  #[using="ws WSL"] Lemma txt_ok_blk : forall (s : PS) (LB : BL) m (k : K) A len cap, RHEAP_A FI AI s LB m -> In (k, A, cap + 1) LB -> 0 <= len <= cap -> cap + 1 <= LMAX_A ->
    txt_okA A len cap.
  Proof.
    intros s LB m k A len cap HR HIN LC CB. destruct (am_block_range FI AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn [blk_addr blk_size fst snd] in *.
    unfold LMAX_A in CB. unfold H_pent_seg.txt_okA. split; [exact R5|]. split; [exact R4|]. split; [exact LC|]. split; [exact R2|]. split; [exact R7|]. split; [exact R6| lia].
  Qed.

  #[using="Type"] Lemma del_books : forall (s' : PS) (LB LB' : BL) m' ns hs (kA k' : K) A cap A' cap',
    RHEAP_A FI AI s' LB' m' ->
    bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap ++ LBK) LB ->
    NoDup (map blk_id (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap ++ LBK)) ->
    ((k' = kA /\ LB' = LB /\ A' = A /\ cap' = cap) \/ LB' = (k', A', cap' + 1) :: lb_keepA FI AI (Some kA) LB) ->
    bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI (Some k') A' cap' ++ LBK) LB'
    /\ NoDup (map blk_id (hl_blocks FI AI ns hs ++ okbA FI AI (Some k') A' cap' ++ LBK))
    /\ bsub FI AI (hl_blocks FI AI ns hs) (lb_keepA FI AI (Some kA) LB) /\ bsub FI AI LBK (lb_keepA FI AI (Some kA) LB).
  Proof.
    intros s' LB LB' m' ns hs kA k' A cap A' cap' HR' SUB ND CASES. cbn [okbA] in *.
    pose proof ND as ND0. apply nd_app in ND0. destruct ND0 as (NDH & IH & ND2). apply (nd_cons (kA, A, cap + 1) LBK) in ND2. destruct ND2 as (IK & NDK).
    apply (idj_app_r (hl_blocks FI AI ns hs) [(kA, A, cap + 1)] LBK) in IH. destruct IH as [IHA IHK].
    assert (KH : bsub FI AI (hl_blocks FI AI ns hs) (lb_keepA FI AI (Some kA) LB)).
    { intros b Hb. cbn [lb_keepA]. apply (in_lb_remove FI AI); [apply SUB; apply in_or_app; left; exact Hb|]. exact (IHA b _ Hb (or_introl eq_refl)). }
    assert (KK : bsub FI AI LBK (lb_keepA FI AI (Some kA) LB)).
    { intros b Hb. cbn [lb_keepA]. apply (in_lb_remove FI AI); [apply SUB; apply in_or_app; right; right; exact Hb|]. intros E. exact (IK (kA, A, cap + 1) b (or_introl eq_refl) Hb (eq_sym E)). }
    destruct CASES as [(-> & -> & -> & ->)| ->]; [split; [exact SUB|]; split; [exact ND|]; split; [exact KH| exact KK]|].
    pose proof (am_blocks_nodup FI AI s' _ m' HR') as NDL. apply (nd_cons (k', A', cap' + 1) (lb_keepA FI AI (Some kA) LB)) in NDL. destruct NDL as [NIN _].
    assert (FR : forall b, In b (lb_keepA FI AI (Some kA) LB) -> blk_id b <> k').
    { intros b Hb E. exact (NIN (k', A', cap' + 1) b (or_introl eq_refl) Hb (eq_sym E)). }
    split; [| split; [| split; [exact KH| exact KK]]].
    - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|[Hb|Hb]]; [right; exact (KH b Hb)| left; exact Hb| right; exact (KK b Hb)].
    - apply nd_app. split; [exact NDH|]. split.
      + apply (idj_app_r (hl_blocks FI AI ns hs) [(k', A', cap' + 1)] LBK). split; [| exact IHK].
        intros a b Ha [<-|[]]. cbn [blk_id fst]. exact (FR a (KH a Ha)).
      + apply (nd_cons (k', A', cap' + 1) LBK). split; [| exact NDK]. intros a b [<-|[]] Hb. cbn [blk_id fst]. intros E. exact (FR b (KK b Hb) (eq_sym E)).
  Qed.

  #[using="ws WSL"] Lemma del_nul : forall (bs bs' : list byte) idx num len len' cap,
    Z.of_nat (length bs) = cap + 1 -> 0 <= idx -> 0 <= num -> idx + num <= len -> len <= cap -> len' = len - num ->
    firstn (Z.to_nat (len' + 1)) bs' = firstn (Z.to_nat len') (del_bytesA bs idx num len) ++ [Z_to_bv 8 0] ->
    nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0).
  Proof.
    intros bs bs' idx num len len' cap LBS I0 N0 INL LC -> FN.
    assert (LD : length (del_bytesA bs idx num len) = length bs).
    { unfold del_bytesA. apply upd_bytes_length. rewrite firstn_length. lia. }
    replace (Z.to_nat (len - num + 1)) with (Datatypes.S (Z.to_nat (len - num))) in FN by lia.
    rewrite <- (firstn_skipn (Datatypes.S (Z.to_nat (len - num))) bs'). rewrite FN.
    assert (L1 : length (firstn (Z.to_nat (len - num)) (del_bytesA bs idx num len)) = Z.to_nat (len - num)) by (rewrite firstn_length_le; [reflexivity| rewrite LD; lia]).
    rewrite nth_error_app1 by (rewrite app_length, L1; cbn; lia).
    rewrite nth_error_app2 by lia. rewrite L1, Nat.sub_diag. reflexivity.
  Qed.

  Definition WP5 : list ivl := [(P + 392, P + 400); (P + 400, P + 432); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z.
  #[using="HC FI q lo st POK"] Lemma WP5_ok : Forall wpok WP5.
  Proof. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _). unfold WP5. wpokP. Qed.
  #[using="HC FI q lo st POK"] Lemma WP5_in : Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WP5.
  Proof. unfold WP5. winP. Qed.
  Ltac dj5 := unfold WP5; cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
  Ltac ekc5 EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| unfold H_pent_seg.blk5W, H_pent_seg.blk3W; dj5].
  Ltac wk5 := intros a n; unfold WP5, H_pent_seg.blk5W, H_pent_seg.blk5cW, H_pent_seg.blk3cW; cbn [disjoint_from]; clear; intros; repeat split; try exact I; lia.

  #[using="ws WSL"] Lemma del_script : forall (s s' : PS) (LB LB' : BL) (kA k' : K) A cap A' cap' M c c' G k0,
    In (kA, A, cap + 1) LB -> 0 <= cap' <= cap -> c' <= c -> ebud M c G s LB ->
    esteps k0 0 (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s) LB ->
    ((k' = kA /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
     \/ (LB' = (k', A', cap' + 1) :: lb_keepA FI AI (Some kA) LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1))) ->
    (exists k1, esteps k1 0 (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s') LB' /\ k0 <= k1 <= k0 + 1 /\ am_nsec FI AI s' - k1 <= am_nsec FI AI s - k0 /\ Z.of_nat (length LB') <= Z.of_nat (length LB)) /\ ebud (M - 1) c' G s' LB'.
  Proof.
    intros s s' LB LB' kA k' A cap A' cap' M c c' G k0 KIN CC Hc BUD ES0 [(-> & -> & -> & -> & E)|(-> & E)].
    - split; [exists k0; split; [rewrite E; exact ES0| rewrite E; lia]|]. apply (ebud_mono M (M - 1) c c' G s' LB ltac:(lia) Hc). exact (ebud_same M c G s s' LB BUD E).
    - assert (STP : edel1 (am_nsec FI AI s) LB (am_nsec FI AI s') ((k', A', cap' + 1) :: lb_keepA FI AI (Some kA) LB)).
      { rewrite E. cbn [lb_keepA]. exact (ed_del (am_nsec FI AI s) LB kA k' A A' cap cap' KIN CC). }
      split; [exists (k0 + 1); split; [exact (esteps_trans k0 0 _ _ _ _ ES0 1 0 _ _ (esteps_del1 _ _ _ _ STP))| rewrite E; pose proof (nsec1_range (cap' + 1)) as NR; pose proof (H_phdr.lb_remove_len FI AI kA LB _ KIN eq_refl) as RL; cbn [lb_keepA length]; clear - NR RL; lia]| exact (ebud_step M c c' G s s' LB _ BUD STP Hc)].
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 POK RF0 FCO HR0 KSUB0 QTOP GMX WSL GLR"] Lemma case5 : forall q' (s : PS) (LB : BL) m cur A len cap (kA : K) bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    CONT (pe_measA 5 el) ->
    EI s LB m q' cur A len cap (Some kA) bs eb el err hack pos 5 clen csz esp ns hs X meth ->
    AJ FI AI J POST (blkstA q' 0x89d18 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HCN EIF.
    pose proof EIF as (EXF & INV & XB & ST2 & (BUD & CB & HSS & (k0 & ES0 & K0 & KM & KC & KN)) & CH & EOK).
    pose proof (pe_measA_nonneg _ _ _ _ _ EOK) as MP.
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & _ & SUB & ND & (SHP & SHSEP & SHF1 & SHF2 & SHZ & SHR & (ev & CLOW) & SHE & PST) & _ & SCR & HSF).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (OB_sub LB ns hs (Some kA) A cap SUB) as [OSUB KSUB].
    assert (HSUB : bsub FI AI (hl_blocks FI AI ns hs) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    destruct (pctx_of s LB m A len cap kA bs cur ev HR PSC PMSG SHP SHSEP SHF1 SHF2 SHZ SHR CLOW SHE) as (CTX & TOK & KIN & NUL).
    destruct (p_msg_facts FI AI m LB P A len cap (Some kA) bs s HR PMSG) as (HL & HCp & LBS0 & _ & _). unfold LMAX_A in HCp.
    destruct EOK as (E1 & E2 & E3). specialize (E1 ltac:(lia)). destruct (E2 ltac:(right; reflexivity)) as (elen & -> & ELR). specialize (E3 eq_refl).
    pose proof PCTL as (CTLC & CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (C440 & C444 & C448 & C452 & C456 & C460 & C464 & C472).
    pose proof PENT as PENT0. unfold p_ent in PENT0. split_chunk PENT0 1%nat C384 C392.
    pose proof INV as (_ & _ & _ & _ & (QB & QAL) & _).
    apply aj_cps. apply (blk5aE q' A len cap cur csz gmax bs x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ INV CTX TOK PST CUR ltac:(lia) C464 (am_fsenv FI AI _ _ _ HR)).
    -
      intros LT y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31. apply evt_done.
      apply (exitJ 0x8a14c q' 1 s LB m cur A len cap (Some kA) bs eb (wz elen) err hack pos 5 clen csz esp ns hs X meth); [discriminate| unfold retire_pc; lia| exact EXF| exact INV| intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 EIF))))))| lia| lia].
    -
      intros m1 r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 R1 R2 GE INV1 CTX1 PST1 C464' MU WM FK. apply evt_done.
      pose proof CTX1 as (_ & _ & _ & SHP1 & _).
      destruct (ekeep_fk blk5W blk5W [] (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap) s LB q st m m1 MU WM FK ltac:(lia) (fun g Hg => Hg) (fun _ => SHP1)) as [EK HR1];
        [unfold H_pent_seg.blk5W; repeat apply Forall_cons; try apply Forall_nil; split; [cbn [fst snd]; lia| left; cbn [inside fst snd]; lia]
         | unfold H_pent_seg.blk5W; wpokP| unfold H_pent_seg.blk5W; winP| exact HR| intros b []| exact OSUB| exact KSUB| intros a b []| intros a b []|].
      destruct (pctx_back LB m1 A len cap cur bs kA CTX1 KIN HL ltac:(unfold LMAX_A; lia) NUL) as (PSC1 & PMSG1 & CL1).
      apply (exitJ 0x8a1bc q' r s LB m1 cur A len cap (Some kA) bs eb (wz elen) err hack pos 5 clen csz esp ns hs X meth); [discriminate| unfold retire_pc; lia| | exact INV1| intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 EIF))))))| lia| exact R2].
      eapply (EX_move blk5W _ s LB m cur A len cap (Some kA) bs eb (wz elen) err hack pos 5 clen csz esp ns hs X meth s LB m1); [exact EXF| exact EK| unfold H_pent_seg.blk5W; wpokP
        | unfold H_pent_seg.blk5W; djw| unfold H_pent_seg.blk5W; djw| exact HR1| exact PSC1| exact PMSG1| exact CUR
        | exact (ek_ent _ _ m m1 _ _ EK ltac:(unfold H_pent_seg.blk5W; djw) PENT)
        | exact (ek_ctl _ _ m m1 _ _ _ _ _ _ _ EK ltac:(unfold H_pent_seg.blk5W; djw) PCTL)
        | apply (ek_hlist _ _ m m1 ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| unfold H_pent_seg.blk5W; djw]
        | exact (ek_meth _ _ m m1 meth EK ltac:(unfold H_pent_seg.blk5W; djw) PMETH)
        | exact SUB| exact ND| exact CL1| exact SCR| exact HSF].
    -
      intros m1 cur' y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 GE C1 C2 INV1 CTX1 PST1 C464' MU WM FK. apply evt_done.
      pose proof CTX1 as (_ & _ & _ & SHP1 & _).
      destruct (ekeep_fk blk5W blk5W [] (hl_blocks FI AI ns hs) s LB q st m m1 MU WM FK ltac:(lia) (fun g Hg => Hg) (fun _ => SHP1)) as [EK1 HR1];
        [unfold H_pent_seg.blk5W; repeat apply Forall_cons; try apply Forall_nil; split; [cbn [fst snd]; lia| left; cbn [inside fst snd]; lia]
         | unfold H_pent_seg.blk5W; wpokP| unfold H_pent_seg.blk5W; winP| exact HR| intros b []| exact HSUB| exact KSUB| intros a b []| intros a b []|].
      destruct (pinv_rf eshadow q' m1 INV1) as (stc & RF1 & LIVE1). destruct (elive_of stc LIVE1) as (_ & _ & _ & _ & LSUB).
      eapply (delJ eshadow eq_refl 0x89d98 q' (cur + csz) (cur' - (cur + csz)) A len cap cur' gmax bs kA s LB m1); [exact INV1| exact CTX1| exact PST1| exact HR1| exact KIN| exact QTOP| lia
        | apply (ebud_le_now _ (len - cur) _ s LB _ BUD); [exact (H_phdr.p_hlist_cgG FI AI _ _ _ _ _ PHL)| clear - MP; lia| clear - CUR; lia| unfold A0_MAXREQ; clear - HCp; lia]| exact HL| lia| lia| lia| apply ret_pc_even; lia|].
      intros sd LB2 m2 A2 len2 cap2 k2 bs2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 INV2 CTX2 PST2 HR2 KIN2 APX LBC LENC2 CAPLE LENCASES.
      destruct LENCASES as [(L0 & _)|(_ & LEN2 & FN)]; [exfalso; lia|].
      pose proof (del_nul bs bs2 (cur + csz) (cur' - (cur + csz)) len len2 cap LBS0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) LEN2 FN) as NUL2.
      assert (LBC' : (k2 = kA /\ LB2 = LB /\ A2 = A /\ cap2 = cap) \/ LB2 = (k2, A2, cap2 + 1) :: lb_keepA FI AI (Some kA) LB) by (destruct LBC as [(Z1 & Z2 & Z3 & Z4 & _)|(Z1 & _)]; [left; auto| right; exact Z1]).
      destruct (del_books sd LB LB2 m2 ns hs kA k2 A cap A2 cap2 HR2 SUB ND LBC') as (SUB2 & ND2 & KH & KK).
      destruct (del_script s sd LB LB2 kA k2 A cap A2 cap2 _ (len - cur) (len2 - (cur + csz)) _ k0 KIN ltac:(lia) ltac:(lia) BUD ES0 LBC) as ((k1 & ES2 & K1) & BUD2).
      assert (MEAS : pe_measA 3 (wz (elen + csz)) + 1 <= pe_measA 5 (wz elen) \/ gmax < elen + csz) by (unfold pe_meas0; cbn [Z.eqb Pos.eqb]; destruct (Z_le_gt_dec (elen + csz) gmax); [left; rewrite !unsigned_lit by lia; lia| right; lia]).
      destruct (OB_sub LB2 ns hs (Some k2) A2 cap2 SUB2) as [_ KSUB2].
      assert (HSUB2 : bsub FI AI (hl_blocks FI AI ns hs) LB2) by (intros b Hb; apply SUB2; apply in_or_app; left; exact Hb).
      pose proof CTX2 as (_ & _ & _ & SHP2 & _ & _ & _ & _ & SHZ2 & SHR2 & _).
      pose proof (ekeep_apxF [(P + 400, P + 400 + 32)]%Z [(P + 400, P + 400 + 32)]%Z [] (hl_blocks FI AI ns hs) (lb_keepA FI AI (Some kA) LB) s LB q' stc m1 m2
                    (apxF_of_apx FI AI _ _ _ q' q' stc stc m1 m1 m2 APX RF1 ltac:(lia) (fun b Hb => Hb) (fun g Hg => Hg)) ltac:(lia) ltac:(lia) LSUB
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; split; [cbn [fst snd]; lia| left; cbn [inside fst snd]; lia]) ltac:(wpokP) ltac:(winP) HR1
                    (fun b Hb => False_ind _ Hb) KH HSUB KK KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha) SHP2) as EK2.
      pose proof (txt_ok_blk sd LB2 m2 k2 A2 len2 cap2 HR2 KIN2 LENC2 ltac:(unfold LMAX_A; lia)) as TOK2.
      pose proof C392 as C392'. ekc5 EK1 C392'. ekc5 EK2 C392'.
      pose proof C440 as C440'. ekc5 EK1 C440'. ekc5 EK2 C440'.
      pose proof C452 as C452'. ekc5 EK1 C452'. ekc5 EK2 C452'.
      pose proof C464 as C464''. ekc5 EK1 C464''. ekc5 EK2 C464''.

      assert (FIN : forall m3 (err' entp' : Z) (C392n : rw_cells asegs m3 (P + 392) [C8 (wz (elen + csz))]) (C440n : rw_cells asegs m3 (P + 440) [C4 (wz err')])
                      (C452n : rw_cells asegs m3 (P + 452) [C4 (wz entp')]),
                 munch blk5cW m2 m3 -> wmono asegs m2 m3 -> pctx A2 len2 cap2 (cur + csz) bs2 m3 -> 0 <= err' < 2^31 -> 0 <= entp' <= 6 ->
                 exists eb', ekeep WP5 (hl_blocks FI AI ns hs) m m3 /\ RHEAP_A FI AI sd LB2 m3
                   /\ p_scan m3 P (cur + csz) /\ p_msg FI AI m3 LB2 P A2 len2 cap2 (Some k2) bs2 /\ p_ent m3 P eb' (wz (elen + csz))
                   /\ p_ctl m3 P err' hack pos entp' clen csz esp /\ p_hlist FI AI m3 P ns hs X /\ p_meth m3 P meth /\ (exists ev', clow canary ev' m3)).
      { intros m3 err' entp' C392n C440n C452n MU3 WM3 CTX3 ER' EN'.
        destruct (ekeep_munch blk5cW blk5cW [] (hl_blocks FI AI ns hs) sd LB2 m2 m3 MU3 WM3) as [EK3 HR3];
          [unfold H_pent_seg.blk5cW; clsP; apply Forall_nil| unfold H_pent_seg.blk5cW; wpokP| unfold H_pent_seg.blk5cW; winP| exact HR2
           | intros b []| exact HSUB2| exact KSUB2| intros a b []| intros a b []|].
        pose proof (ekeep_trans WP5 _ m m1 m3 (ekeep_weaken _ WP5 _ m m1 EK1 ltac:(wk5))
                      (ekeep_trans WP5 _ m1 m2 m3 (ekeep_weaken _ WP5 _ m1 m2 EK2 ltac:(wk5)) (ekeep_weaken _ WP5 _ m2 m3 EK3 ltac:(wk5)))) as EK.
        destruct (pctx_back LB2 m3 A2 len2 cap2 (cur + csz) bs2 k2 CTX3 KIN2 LENC2 ltac:(unfold LMAX_A; lia) NUL2) as (PSC3 & PMSG3 & CL3).
        pose proof C384 as C384'. ekc5 EK C384'. join_chunks C384' C392n PENT3.
        pose proof C444 as C444'. ekc5 EK C444'. pose proof C448 as C448'. ekc5 EK C448'. pose proof C456 as C456'. ekc5 EK C456'.
        pose proof C460 as C460'. ekc5 EK C460'. pose proof C464 as C464n. ekc5 EK C464n. pose proof C472 as C472'. ekc5 EK C472'.
        pose proof (pctl_join m3 err' hack pos entp' clen csz esp C440n C444' C448' C452n C456' C460' C464n C472') as CTL3.
        exists eb. split; [exact EK|]. split; [exact HR3|]. split; [exact PSC3|]. split; [exact PMSG3|]. split; [exact PENT3|].
        split; [split; [exact CTL3| repeat (split; [first [assumption| lia]|]); lia]|].
        split; [apply (ek_hlist _ _ m m3 ns hs X EK PHL); [intros b Hb; exact Hb| dj5]|].
        split; [exact (ek_meth _ _ m m3 meth EK ltac:(dj5) PMETH)| exact CL3]. }
      apply aj_cps.
      apply (blk5cE q' A2 len2 cap2 (cur + csz) cur' csz elen err 5 gmax bs2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m2 _ INV2 CTX2 TOK2 PST2 GMX ltac:(lia) ltac:(lia) ltac:(lia)
               C392' C440' C452' C464'').
      +
        intros OV m3 v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v28 v29 v30 v31 INV3 CTX3 PST3 C392n C440n C452n C464n MU3 WM3. apply evt_done.
        destruct (FIN m3 413 5 C392n C440n C452n MU3 WM3 CTX3 ltac:(lia) ltac:(lia)) as (eb' & EK & HR3 & PSC3 & PMSG3 & PENT3 & PCTL3 & PHL3 & PMETH3 & CL3).
        apply (exitJ 0x8a1f4 q' 3 sd LB2 m3 (cur + csz) A2 len2 cap2 (Some k2) bs2 eb' (wz (elen + csz)) 413 hack pos 5 clen csz esp ns hs X meth); [discriminate| unfold retire_pc; lia| | exact INV3| intros Hx; exfalso; apply Hx; reflexivity| lia| lia].
        eapply (EX_move WP5 _ s LB m cur A len cap (Some kA) bs eb (wz elen) err hack pos 5 clen csz esp ns hs X meth sd LB2 m3); [exact EXF| exact EK| exact WP5_ok
          | dj5| dj5| exact HR3| exact PSC3| exact PMSG3| lia| exact PENT3| exact PCTL3| exact PHL3| exact PMETH3| exact SUB2| exact ND2| exact CL3| exists k1, 0; split; [exact ES2| clear - K1 K0 KM KC KN MP CB CUR; lia]| exact HSF].
      +
        intros LE m3 v1 v5 v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 INV3 CTX3 PST3 C392n C440n C452n C464n MU3 WM3.
        destruct (FIN m3 err 3 C392n C440n C452n MU3 WM3 CTX3 ltac:(lia) ltac:(lia)) as (eb' & EK & HR3 & PSC3 & PMSG3 & PENT3 & PCTL3 & PHL3 & PMETH3 & CL3).
        apply (loopE q' 6 v1 v5 v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 m3 _ ltac:(lia)); [| intros Hx; exfalso; apply Hx; reflexivity].
        intros _ v10b. apply evt_done.
        eapply (HCN sd LB2 m3 q' (cur + csz) A2 len2 cap2 k2 bs2 eb' (wz (elen + csz)) err hack pos 3 clen csz esp ns hs X meth).
        * eapply (EI_move WP5 _ s LB m q' cur A len cap (Some kA) bs eb (wz elen) err hack pos 5 clen csz esp ns hs X meth sd LB2 m3); [exact EIF| exact EK| exact WP5_ok
            | dj5| dj5| exact HR3| exact INV3| exact PSC3| exact PMSG3| lia| exact PENT3| exact PCTL3| exact PHL3| exact PMETH3| exact SUB2| exact ND2| exact CL3| | (clear - XB LEN2 C1 C2 E3 GE CUR; lia)| | clear - CB C1 C2 LEN2 GE E3; lia| exact HSS|].
          -- split; [intros _; lia|]. split; [intros _; exists (elen + csz); split; [reflexivity| lia]| intros Hx; discriminate Hx].
          -- eapply ebud_mono; [| | exact BUD2]; [destruct MEAS as [MS|MS]; [clear - MS; lia| exfalso; clear - MS LE; lia]| clear; lia].
          -- exists k1. split; [exact ES2|]. destruct MEAS as [MS|MS]; [clear - MS K1 K0 KM KC KN; lia| exfalso; clear - MS LE; lia].
        * destruct MEAS as [MS|MS]; [clear - MS; lia| exfalso; clear - MS LE; lia].
  Qed.

  Definition SIX (s : PS) (LB : BL) (m : mem) (cur A len cap : Z) (kA : K) (bs : list byte) (eb el : word)
      (err hack pos entp clen csz esp : Z) (ns : list (BLK * Z)) (hs : list hdr) (X meth : Z) : Prop :=
    RHEAP_A FI AI s LB m /\ p_scan m P cur /\ p_msg FI AI m LB P A len cap (Some kA) bs /\ p_ent m P eb el
    /\ p_ctl m P err hack pos entp clen csz esp /\ p_hlist FI AI m P ns hs X /\ p_meth m P meth /\ (exists ev, clow canary ev m)
    /\ bsub FI AI (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap ++ LBK) LB.

  #[using="ws WSL"] Lemma sf_cls : forall WP TB, Forall (ecls WP TB) [(SF, SF + 16)]%Z.
  Proof. intros WP TB. apply Forall_cons; [| apply Forall_nil]. split; [cbn [fst snd]; lia|]. right; right; left. cbn [fst snd]. lia. Qed.

  #[using="ASL AMS m0 POK RF0 ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma six_sf : forall (s : PS) (LB : BL) m m' cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth,
    SIX s LB m cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
    SIX s LB m' cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth
    /\ ekeep [] (hl_blocks FI AI ns hs) m m'.
  Proof.
    intros s LB m m' cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth (HR & PSC & PMSG & PENT & PCTL & PHL & PMETH & CL & SUB) MU WM.
    destruct (OB_sub LB ns hs (Some kA) A cap SUB) as [OSUB KSUB].
    destruct (ekeep_munch [(SF, SF + 16)]%Z [] [] (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap) s LB m m' MU WM (sf_cls [] []) (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    split.
    - split; [exact HR'|]. split; [exact (ek_scan _ _ m m' cur EK I PSC)|].
      split; [apply (ek_msg _ _ LB m m' A len cap (Some kA) bs EK I); [intros b Hb; apply in_or_app; right; exact Hb| exact PMSG]|].
      split; [exact (ek_ent _ _ m m' eb el EK I PENT)|]. split; [exact (ek_ctl _ _ m m' _ _ _ _ _ _ _ EK I PCTL)|].
      split; [apply (ek_hlist _ _ m m' ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| exact I]|].
      split; [exact (ek_meth _ _ m m' meth EK I PMETH)|]. split; [exact (ek_clow _ _ m m' EK (Forall_nil _) I CL)| exact SUB].
    - destruct EK as (K1 & K2 & K3 & K4 & KR). split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [| exact KR].
      apply (bkeep_sub FI AI _ _ m m' K4). intros b Hb. apply in_or_app. left. exact Hb.
  Qed.

  #[using="ASL AMS POK RF0 HR0 KSUB0 WSL"] Lemma repJ : forall M q' r (s : PS) (LB : BL) m cur A len cap (kA : K) bs eb el err hack pos entp clen csz esp ns hs X meth
      x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    CONT M -> pinvS eshadowU q' m -> 0 <= r <= 6 -> r <> 4 ->
    (forall m', pinv q' m' -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
       EX s LB m' cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth
       /\ (r = 6 -> EI s LB m' q' cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth)) ->
    (r = 6 -> pe_measA entp el < M) -> (r <> 6 -> r <> 3 -> ent_okA gmax entp cur esp csz el) ->
    AJ FI AI J POST (MS (pregs q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz 0x89ecc) fc None m (seg_rom asegs)) s LB.
  Proof.
    intros M q' r s LB m cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           HCN INVU R1 R2 HM MEAS EOKX.
    apply aj_cps. apply (repoisonE q' r x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ INVU).
    intros y10 m' INV' MU WM. destruct (HM m' INV' MU WM) as [EXF EIF].
    apply (loopE q' r x1 x5 x6 y10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' _ R1).
    - intros E6 z10. apply evt_done. eapply (HCN s LB m' q'); [exact (EIF E6)| exact (MEAS E6)].
    - intros N6 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z28 z29 z30 z31. apply evt_done.
      apply (exitJ 0x8a1f4 q' r s LB m' cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth); [discriminate| unfold retire_pc; lia| exact EXF| exact INV'| exact (EOKX N6)| lia| exact R2].
  Qed.

  Definition WP1 : list ivl := [(P + 464, P + 472); (P + 488, P + 496); (ERRNO_A, ERRNO_A + 4)]%Z.
  Definition WP3 : list ivl := [(P + 464, P + 472); (P + 488, P + 496); (ERRNO_A, ERRNO_A + 4); (P + 392, P + 400); (P + 400, P + 432); (P + 440, P + 444); (P + 452, P + 456)]%Z.
  #[using="ws WSL"] Lemma WP1_ok : Forall wpok WP1.
  Proof. unfold WP1. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|]. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|].
         apply Forall_cons; [right; unfold H_pent_seg.inER; cbn [fst snd]; lia| apply Forall_nil]. Qed.
  #[using="HC FI q lo st POK"] Lemma WP1_in : Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WP1.
  Proof. unfold WP1. winP. Qed.
  #[using="HC FI q lo st POK ws WSL"] Lemma WP3_ok : Forall wpok WP3.
  Proof. unfold WP3. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|]. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|].
         apply Forall_cons; [right; unfold H_pent_seg.inER; cbn [fst snd]; lia|]. wpokP. Qed.
  #[using="ws WSL"] Lemma blk3W_cls : Forall (fcls WP1 []) blk3W.
  Proof.
    unfold H_pent_seg.blk3W, WP1, fcls.
    repeat apply Forall_cons; try apply Forall_nil; (split; [cbn [fst snd]; lia|]);
      [left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia| right; left; unfold H_pent_seg.inFJ; cbn [fst snd]; lia
       | right; left; unfold H_pent_seg.inFJ; cbn [fst snd]; lia| left; cbn [inside fst snd]; lia].
  Qed.
  Ltac dj3 := unfold WP1, WP3, H_pent_seg.blk3cW; cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
  Ltac ekc3 EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| dj3].
  Ltac wk3 := intros a n; unfold WP1, WP3, H_pent_seg.blk3cW; cbn [disjoint_from]; clear; intros; repeat split; try exact I; lia.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO HR0 KSUB0 QTOP GMX WSL GLR"] Lemma case3 : forall q' (s : PS) (LB : BL) m cur A len cap (kA : K) bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    CONT (pe_measA 3 el) ->
    EI s LB m q' cur A len cap (Some kA) bs eb el err hack pos 3 clen csz esp ns hs X meth ->
    AJ FI AI J POST (blkstA q' 0x89c38 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HCN EIF.
    pose proof EIF as (EXF & INV & XB & ST2 & (BUD & CB & HSS & (k0 & ES0 & K0 & KM & KC & KN)) & CH & EOK).
    pose proof (pe_measA_nonneg _ _ _ _ _ EOK) as MP.
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & _ & SUB & ND & STAT & _ & SCR & HSF).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (OB_sub LB ns hs (Some kA) A cap SUB) as [OSUB KSUB].
    assert (HSUB : bsub FI AI (hl_blocks FI AI ns hs) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    destruct (p_msg_facts FI AI m LB P A len cap (Some kA) bs s HR PMSG) as (HL & HCp & LBS0 & _ & _). unfold LMAX_A in HCp.
    pose proof EOK as (E1 & E2 & E3). specialize (E1 ltac:(lia)). destruct (E2 ltac:(left; reflexivity)) as (elen & -> & ELR).
    pose proof PCTL as (CTLC & CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (C440 & C444 & C448 & C452 & C456 & C460 & C464 & C472).
    pose proof PENT as PENT0. unfold p_ent in PENT0. split_chunk PENT0 1%nat C384 C392.
    destruct PVER as ((pad & VC) & _). split_chunk VC 1%nat C264 VR. clear VR.
    pose proof INV as (_ & _ & _ & _ & (QB & QAL) & _).
    apply aj_cps. apply (unpoisonE q' x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ INV).
    intros mu INVU MU0 WM0.
    assert (SIX0 : SIX s LB m cur A len cap kA bs eb (wz elen) err hack pos 3 clen csz esp ns hs X meth).
    { destruct STAT as (_ & _ & _ & _ & _ & _ & CL & _). unfold SIX. repeat (split; [assumption|]). exact SUB. }
    destruct (six_sf s LB m mu _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SIX0 MU0 WM0) as [(HRu & PSCu & PMSGu & _ & _ & _ & _ & (evu & CLu) & _) EK0].
    pose proof (ek_stat [] _ m mu EK0 (Forall_nil _) STAT (ex_intro _ evu CLu)) as (SHPu & SHSEPu & SHF1u & SHF2u & SHZu & SHRu & _ & SHEu & PSTu).
    destruct (pctx_of s LB mu A len cap kA bs cur evu HRu PSCu PMSGu SHPu SHSEPu SHF1u SHF2u SHZu SHRu CLu SHEu) as (CTXu & TOK & KIN & NUL).
    pose proof C464 as C464u. ekc3 EK0 C464u.
    apply (blk3bE q' A len cap cur gmax bs (wz csz) x1 x5 x6 (wz 4) (wz 5) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mu _ INVU CTXu TOK PSTu CUR NUL ltac:(apply unsigned_lit; lia) C464u (am_fsenv FI AI _ _ _ HRu)).
    -
      intros m1 r y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 R1 R2 INV1 CTX1 PST1 C464' MU WM FK. apply evt_done.
      pose proof CTX1 as (_ & _ & _ & SHP1 & _).
      destruct (ekeep_fk blk3W WP1 [] (hl_blocks FI AI ns hs) s LB q st mu m1 MU WM FK ltac:(lia) (fun g Hg => Hg) (fun _ => SHP1) blk3W_cls WP1_ok WP1_in HRu
                  (fun b Hb => False_ind _ Hb) HSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK1 HR1].
      pose proof (ekeep_trans WP1 _ m mu m1 (ekeep_weaken _ WP1 _ m mu EK0 ltac:(wk3)) EK1) as EK01.
      destruct (pctx_back LB m1 A len cap cur bs kA CTX1 KIN HL ltac:(unfold LMAX_A; lia) NUL) as (PSC1 & PMSG1 & CL1).
      pose proof C440 as C440'. ekc3 EK01 C440'. pose proof C444 as C444'. ekc3 EK01 C444'. pose proof C448 as C448'. ekc3 EK01 C448'. pose proof C452 as C452'. ekc3 EK01 C452'.
      pose proof C456 as C456'. ekc3 EK01 C456'. pose proof C460 as C460'. ekc3 EK01 C460'. pose proof C472 as C472'. ekc3 EK01 C472'.
      pose proof (pctl_join m1 err hack pos 3 clen csz esp C440' C444' C448' C452' C456' C460' C464' C472') as CTL1.
      assert (SIX1 : SIX s LB m1 cur A len cap kA bs eb (wz elen) err hack pos 3 clen csz esp ns hs X meth).
      { unfold SIX. split; [exact HR1|]. split; [exact PSC1|]. split; [exact PMSG1|]. split; [exact (ek_ent _ _ m m1 _ _ EK01 ltac:(dj3) PENT)|].
        split; [split; [exact CTL1| repeat (split; [assumption|]); assumption]|].
        split; [apply (ek_hlist _ _ m m1 ns hs X EK01 PHL); [intros b Hb; exact Hb| dj3]|].
        split; [exact (ek_meth _ _ m m1 meth EK01 ltac:(dj3) PMETH)|]. split; [exact CL1| exact SUB]. }
      apply (repJ (pe_measA 3 (wz elen)) q' r s LB m1 cur A len cap kA bs eb (wz elen) err hack pos 3 clen csz esp ns hs X meth); [exact HCN| exact INV1| lia| exact R2| | intros Hx; exfalso; lia| intros _ _; exact EOK].
      intros m4 INV4 MU4 WM4.
      destruct (six_sf s LB m1 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SIX1 MU4 WM4) as [(HR4 & PSC4 & PMSG4 & PENT4 & PCTL4 & PHL4 & PMETH4 & CL4 & _) EK4].
      pose proof (ekeep_trans WP1 _ m m1 m4 EK01 (ekeep_weaken _ WP1 _ m1 m4 EK4 ltac:(wk3))) as EK.
      split; [| intros Hx; exfalso; lia].
      eapply (EX_move WP1 _ s LB m cur A len cap (Some kA) bs eb (wz elen) err hack pos 3 clen csz esp ns hs X meth s LB m4); [exact EXF| exact EK| exact WP1_ok
        | dj3| dj3| exact HR4| exact PSC4| exact PMSG4| exact CUR| exact PENT4| exact PCTL4| exact PHL4| exact PMETH4| exact SUB| exact ND| exact CL4| exact SCR| exact HSF].
    -
      intros m1 v cur' y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 VR C1 C2 INV1 CTX1 PST1 C464v MU WM FK. apply evt_done.
      pose proof CTX1 as (_ & _ & _ & SHP1 & _).
      destruct (ekeep_fk blk3W WP1 [] (hl_blocks FI AI ns hs) s LB q st mu m1 MU WM FK ltac:(lia) (fun g Hg => Hg) (fun _ => SHP1) blk3W_cls WP1_ok WP1_in HRu
                  (fun b Hb => False_ind _ Hb) HSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK1 HR1].
      pose proof (ekeep_trans WP1 _ m mu m1 (ekeep_weaken _ WP1 _ m mu EK0 ltac:(wk3)) EK1) as EK01.
      destruct (pinv_rf eshadowU q' m1 INV1) as (stc & RF1 & LIVE1). destruct (elive_of stc LIVE1) as (_ & _ & _ & _ & LSUB).
      eapply (delJ eshadowU eq_refl 0x89ca4 q' cur (cur' - cur) A len cap cur' gmax bs kA s LB m1); [exact INV1| exact CTX1| exact PST1| exact HR1| exact KIN| exact QTOP| lia
        | apply (ebud_le_now _ (len - cur) _ s LB _ BUD); [exact (H_phdr.p_hlist_cgG FI AI _ _ _ _ _ PHL)| clear - MP; lia| clear - CUR; lia| unfold A0_MAXREQ; clear - HCp; lia]| exact HL| lia| lia| lia| apply ret_pc_even; lia|].
      intros sd LB2 m2 A2 len2 cap2 k2 bs2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 INV2 CTX2 PST2 HR2 KIN2 APX LBC LENC2 CAPLE LENCASES.
      destruct LENCASES as [(L0 & _)|(_ & LEN2 & FN)]; [exfalso; lia|].
      pose proof (del_nul bs bs2 cur (cur' - cur) len len2 cap LBS0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) LEN2 FN) as NUL2.
      assert (LBC' : (k2 = kA /\ LB2 = LB /\ A2 = A /\ cap2 = cap) \/ LB2 = (k2, A2, cap2 + 1) :: lb_keepA FI AI (Some kA) LB) by (destruct LBC as [(Z1 & Z2 & Z3 & Z4 & _)|(Z1 & _)]; [left; auto| right; exact Z1]).
      destruct (del_books sd LB LB2 m2 ns hs kA k2 A cap A2 cap2 HR2 SUB ND LBC') as (SUB2 & ND2 & KH & KK).
      destruct (del_script s sd LB LB2 kA k2 A cap A2 cap2 _ (len - cur) (len2 - cur) _ k0 KIN ltac:(lia) ltac:(lia) BUD ES0 LBC) as ((k1 & ES2 & K1) & BUD2).
      destruct (OB_sub LB2 ns hs (Some k2) A2 cap2 SUB2) as [_ KSUB2].
      assert (HSUB2 : bsub FI AI (hl_blocks FI AI ns hs) LB2) by (intros b Hb; apply SUB2; apply in_or_app; left; exact Hb).
      pose proof CTX2 as (_ & _ & _ & SHP2 & _ & _ & _ & _ & SHZ2 & SHR2 & _).
      pose proof (ekeep_apxF [(P + 400, P + 400 + 32)]%Z [(P + 400, P + 400 + 32)]%Z [] (hl_blocks FI AI ns hs) (lb_keepA FI AI (Some kA) LB) s LB q' stc m1 m2
                    (apxF_of_apx FI AI _ _ _ q' q' stc stc m1 m1 m2 APX RF1 ltac:(lia) (fun b Hb => Hb) (fun g Hg => Hg)) ltac:(lia) ltac:(lia) LSUB
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; split; [cbn [fst snd]; lia| left; cbn [inside fst snd]; lia]) ltac:(wpokP) ltac:(winP) HR1
                    (fun b Hb => False_ind _ Hb) KH HSUB KK KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha) SHP2) as EK2.
      pose proof (txt_ok_blk sd LB2 m2 k2 A2 len2 cap2 HR2 KIN2 LENC2 ltac:(unfold LMAX_A; lia)) as TOK2.
      pose proof C264 as C264'. ekc3 EK01 C264'. ekc EK2 C264'.
      pose proof C392 as C392'. ekc3 EK01 C392'. ekc EK2 C392'.
      pose proof C440 as C440'. ekc3 EK01 C440'. ekc EK2 C440'.
      pose proof C452 as C452'. ekc3 EK01 C452'. ekc EK2 C452'.
      pose proof C472 as C472'. ekc3 EK01 C472'. ekc EK2 C472'.
      ekc EK2 C464v.
      apply aj_cps.
      apply (blk3cE q' A2 len2 cap2 cur cur' v esp err 3 gmax (wz elen) bs2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m2 _ INV2 CTX2 TOK2 PST2 GMX VR CR7 ltac:(lia)
               C264' C392' C440' C452' C464v C472').
      intros m3 r err' entp' w392' v1 v5 v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 INV3 CTX3 PST3 C264n C392n C440n C452n C464n C472n MU3 WM3 ARMS. apply evt_done.
      destruct (ekeep_munch blk3cW blk3cW [] (hl_blocks FI AI ns hs) sd LB2 m2 m3 MU3 WM3) as [EK3 HR3];
        [unfold H_pent_seg.blk3cW; clsP; apply Forall_nil| unfold H_pent_seg.blk3cW; wpokP| unfold H_pent_seg.blk3cW; winP| exact HR2
         | intros b []| exact HSUB2| exact KSUB2| intros a b []| intros a b []|].
      pose proof (ekeep_trans WP3 _ m m1 m3 (ekeep_weaken _ WP3 _ m m1 EK01 ltac:(wk3))
                    (ekeep_trans WP3 _ m1 m2 m3 (ekeep_weaken _ WP3 _ m1 m2 EK2 ltac:(wk3)) (ekeep_weaken _ WP3 _ m2 m3 EK3 ltac:(wk3)))) as EK03.
      destruct (pctx_back LB2 m3 A2 len2 cap2 cur bs2 k2 CTX3 KIN2 LENC2 ltac:(unfold LMAX_A; lia) NUL2) as (PSC3 & PMSG3 & CL3).
      pose proof C384 as C384'. ekc3 EK03 C384'. join_chunks C384' C392n PENT3.
      pose proof C444 as C444'. ekc3 EK03 C444'. pose proof C448 as C448'. ekc3 EK03 C448'. pose proof C456 as C456'. ekc3 EK03 C456'. pose proof C460 as C460'. ekc3 EK03 C460'.
      pose proof (pctl_join m3 err' hack pos entp' clen v esp C440n C444' C448' C452n C456' C460' C464n C472n) as CTL3.
      assert (RNG : 0 <= err' < 2^31 /\ 0 <= entp' <= 6) by (destruct ARMS as [(Z1 & Z2 & Z3 & Z4 & Z5)|[(Z1 & Z2 & Z3 & Z4 & Z5 & Z6)|(Z1 & Z2 & Z3 & Z4 & Z5 & Z6)]]; lia).
      assert (SIX3 : SIX sd LB2 m3 cur A2 len2 cap2 k2 bs2 eb w392' err' hack pos entp' clen v esp ns hs X meth).
      { unfold SIX. split; [exact HR3|]. split; [exact PSC3|]. split; [exact PMSG3|]. split; [exact PENT3|].
        split; [split; [exact CTL3| repeat (split; [first [assumption| lia]|]); lia]|].
        split; [apply (ek_hlist _ _ m m3 ns hs X EK03 PHL); [intros b Hb; exact Hb| dj3]|].
        split; [exact (ek_meth _ _ m m3 meth EK03 ltac:(dj3) PMETH)|]. split; [exact CL3| exact SUB2]. }
      assert (RR : (r = 6 \/ r = 3) /\ (r = 6 -> ent_okA gmax entp' cur esp v w392' /\ pe_measA entp' w392' + 1 <= pe_measA 3 (wz elen))).
      { destruct ARMS as [(Z1 & -> & -> & -> & Z5)|[(Z1 & Z2 & -> & Z4 & Z5 & Z6)|(Z1 & Z2 & -> & -> & -> & Z6)]].
        - split; [left; reflexivity|]. intros _. split; [split; [intros _; lia| split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx]]|].
          unfold pe_meas0. cbn [Z.eqb Pos.eqb]. rewrite !unsigned_lit by lia. lia.
        - split; [right; reflexivity| intros Hx; discriminate Hx].
        - split; [left; reflexivity|]. intros _. split; [split; [intros _; lia| split; [intros _; exists elen; split; [reflexivity| lia]| intros _; lia]]|].
          unfold pe_meas0. cbn [Z.eqb Pos.eqb]. rewrite !unsigned_lit by lia. lia. }
      destruct RR as [R63 R6].
      apply (repJ (pe_measA 3 (wz elen)) q' r sd LB2 m3 cur A2 len2 cap2 k2 bs2 eb w392' err' hack pos entp' clen v esp ns hs X meth); [exact HCN| exact INV3| lia| lia| | intros Hx; pose proof (proj2 (R6 Hx)) as MS; clear - MS; lia| intros H6 H3; exfalso; lia].
      intros m4 INV4 MU4 WM4.
      destruct (six_sf sd LB2 m3 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SIX3 MU4 WM4) as [(HR4 & PSC4 & PMSG4 & PENT4 & PCTL4 & PHL4 & PMETH4 & CL4 & _) EK4].
      pose proof (ekeep_trans WP3 _ m m3 m4 EK03 (ekeep_weaken _ WP3 _ m3 m4 EK4 ltac:(wk3))) as EK.
      split.
      + eapply (EX_move WP3 _ s LB m cur A len cap (Some kA) bs eb (wz elen) err hack pos 3 clen csz esp ns hs X meth sd LB2 m4); [exact EXF| exact EK| exact WP3_ok
          | dj3| dj3| exact HR4| exact PSC4| exact PMSG4| lia| exact PENT4| exact PCTL4| exact PHL4| exact PMETH4| exact SUB2| exact ND2| exact CL4| exists k1, 0; split; [exact ES2| clear - K1 K0 KM KC KN MP CB CUR; lia]| exact HSF].
      + intros H6.
        eapply (EI_move WP3 _ s LB m q' cur A len cap (Some kA) bs eb (wz elen) err hack pos 3 clen csz esp ns hs X meth sd LB2 m4); [exact EIF| exact EK| exact WP3_ok
          | dj3| dj3| exact HR4| exact INV4| exact PSC4| exact PMSG4| lia| exact PENT4| exact PCTL4| exact PHL4| exact PMETH4| exact SUB2| exact ND2| exact CL4
          | exact (proj1 (R6 H6))| lia
          | eapply ebud_mono; [| | exact BUD2]; [pose proof (proj2 (R6 H6)) as MS; clear - MS; lia| clear; lia]
          | clear - CB LEN2 C1; lia| exact HSS
          | exists k1; split; [exact ES2|]; pose proof (proj2 (R6 H6)) as MS; clear - MS K1 K0 KM KC KN; lia].
  Qed.

  Definition WPg : list ivl := [(P + 384, P + 400); (P + 440, P + 480); (ERRNO_A, ERRNO_A + 4)]%Z.
  Definition vblocks (hs : list hdr) : BL := map (fun h => (vk FI AI h, vA FI AI h, vcap FI AI h + 1)) hs.
  #[using="ws WSL"] Lemma WPg_ok : Forall wpok WPg.
  Proof. unfold WPg. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|]. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|].
         apply Forall_cons; [right; unfold H_pent_seg.inER; cbn [fst snd]; lia| apply Forall_nil]. Qed.
  #[using="HC FI q lo st POK"] Lemma WPg_in : Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WPg.
  Proof. unfold WPg. winP. Qed.
  #[using="Type"] Lemma hs_pure : forall m hs h, hdrs_mem FI AI m hs -> In h hs -> hdro_pure FI AI h.
  Proof. intros m hs h. induction hs as [|h0 hs IH]; intros HM Hh; [destruct Hh|]. cbn [hdrs_mem] in HM. destruct HM as (_ & HP & HM'). destruct Hh as [<-|Hh]; [exact HP| exact (IH HM' Hh)]. Qed.
  #[using="Type"] Lemma vblocks_sub : forall ns hs, bsub FI AI (vblocks hs) (hl_blocks FI AI ns hs).
  Proof.
    intros ns hs b Hb. unfold vblocks in Hb. apply in_map_iff in Hb. destruct Hb as (h & <- & Hh). unfold hl_blocks. apply in_or_app. right.
    unfold hdrs_blocks. apply in_concat. exists (hblocks FI AI h). split; [apply in_map; exact Hh|]. unfold hblocks. right; left. reflexivity.
  Qed.
  #[using="ws WSL"] Lemma germW_cls : forall m hs, hdrs_mem FI AI m hs -> Forall (fcls WPg (vblocks hs)) (germ_WA P hs).
  Proof.
    intros m hs HM. unfold germ_WA, fcls.
    apply Forall_cons; [split; [cbn [fst snd]; lia| left; unfold WPg; cbn [inside fst snd]; lia]|].
    apply Forall_cons; [split; [cbn [fst snd]; lia| left; unfold WPg; cbn [inside fst snd]; lia]|].
    apply Forall_cons; [split; [cbn [fst snd]; lia| left; unfold WPg; cbn [inside fst snd]; lia]|].
    apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (h & <- & Hh). cbn [fst snd].
    destruct (hs_pure m hs h HM Hh) as (V1 & _). split; [lia|]. right; right.
    exists (vk FI AI h, vA FI AI h, vcap FI AI h + 1). split; [unfold vblocks; apply in_map_iff; exists h; split; [reflexivity| exact Hh]|]. cbn [blk_addr blk_size fst snd]. lia.
  Qed.
  #[using="q lo POK ws WSL"] Lemma germW_W3 : forall (s : PS) (LB : BL) m ns hs, RHEAP_A FI AI s LB m -> bsub FI AI (hl_blocks FI AI ns hs) LB -> hdrs_mem FI AI m hs -> Forall inW3 (germ_WA P hs).
  Proof.
    intros s LB m ns hs HR HSUB HM. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    unfold germ_WA, H_pent_seg.inW3.
    apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|]. apply Forall_cons; [left; unfold H_pent_seg.inP; cbn [fst snd]; lia|].
    apply Forall_cons; [right; right; left; unfold H_pent_seg.inER; cbn [fst snd]; lia|].
    apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (h & <- & Hh). do 3 right.
    destruct (hs_pure m hs h HM Hh) as (V1 & _).
    assert (HIN : In (vk FI AI h, vA FI AI h, vcap FI AI h + 1) LB) by (apply HSUB; apply (vblocks_sub ns hs); unfold vblocks; apply in_map_iff; exists h; split; [reflexivity| exact Hh]).
    destruct (am_block_range FI AI s LB m _ HR HIN) as (_ & _ & R3 & R4 & R5 & R6 & R7). cbn [blk_addr blk_size fst snd] in *.
    unfold H_pent_seg.outX. cbn [fst snd]. lia.
  Qed.

  #[using="q lo m0 POK RF0 ws WSL"] Lemma germW_djF : forall (s : PS) (LB : BL) m ns hs X n, RHEAP_A FI AI s LB m -> bsub FI AI (hl_blocks FI AI ns hs) LB -> F <= X -> X + n <= F + 128 -> 0 <= n ->
    disjoint_from (germ_WA P hs) X n.
  Proof.
    intros s LB m ns hs X n HR HSUB H1 H2 Hn. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _ & PF1 & PF2). pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    unfold germ_WA. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
    apply dj_forall. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (h & <- & Hh). cbn [fst snd].
    assert (HIN : In (vk FI AI h, vA FI AI h, vcap FI AI h + 1) LB) by (apply HSUB; apply (vblocks_sub ns hs); unfold vblocks; apply in_map_iff; exists h; split; [reflexivity| exact Hh]).
    destruct (am_block_range FI AI s LB m _ HR HIN) as (_ & _ & R3 & R4 & R5 & R6 & R7). cbn [blk_addr blk_size fst snd] in *. lia.
  Qed.

  #[using="ASL AMS POK RF0 FCO HR0 KSUB0 GMX WSL GLR GERM"] Lemma case1 : forall q' (s : PS) (LB : BL) m cur A len cap (kA : K) bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    CONT (pe_measA 1 el) ->
    EI s LB m q' cur A len cap (Some kA) bs eb el err hack pos 1 clen csz esp ns hs X meth ->
    AJ FI AI J POST (blkstA q' 0x89bf0 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HCN EIF.
    pose proof EIF as (EXF & INV & XB & ST2 & (BUD & CB & HSS & (k0 & ES0 & K0 & KM & KC & KN)) & CH & EOK).
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & PRS & SUB & ND & (SHP & SHSEP & SHF1 & SHF2 & SHZ & SHR & (ev & CLOW) & SHE & PST) & _ & SCR & HSF).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (OB_sub LB ns hs (Some kA) A cap SUB) as [OSUB KSUB].
    assert (HSUB : bsub FI AI (hl_blocks FI AI ns hs) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    assert (TSUB : bsub FI AI (okbA FI AI (Some kA) A cap) LB) by (intros b Hb; apply SUB; apply in_or_app; right; apply in_or_app; left; exact Hb).
    pose proof ND as ND0. apply nd_app in ND0. destruct ND0 as (NDH & IH & ND2). apply (nd_app (okbA FI AI (Some kA) A cap) LBK) in ND2. destruct ND2 as (_ & ITK & _).
    apply (idj_app_r (hl_blocks FI AI ns hs) (okbA FI AI (Some kA) A cap) LBK) in IH. destruct IH as [IHT IHK].
    pose proof PHL as (_ & _ & _ & _ & HM & _).
    pose proof INV as (ST & PSCR & MI & AE & (QB & QAL) & VR). destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & _ & _ & (stc & RF & LIVE1)).
    destruct (elive_of stc LIVE1) as (LVF & _ & _ & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1' & SHF2' & PAF & PAFL & PF1 & PF2).
    destruct PST as (G1 & G2 & G3 & IWC). destruct ST2 as (PHS & GS).
    pose proof (germW_W3 s LB m ns hs HR HSUB HM) as HW3.
    apply aj_cps. apply (blk1aE q' x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ PSCR MI).
    unfold H_pent_seg.ajcallstE, H_pent_seg.pregsG.
    eapply evt_cut.
    { eapply (GERM (wz 0x89bf8) q') with (st := stc) (lo := lo) (s := s) (LB := LB) (P := P) (cur := cur) (A := A) (len := len) (cap := cap) (okm := Some kA) (bs := bs)
                                        (ns := ns) (hs := hs) (X := X) (meth := meth) (isreq := isreq) (maj := maj) (min := min) (rm := rm) (sc := sc)
                                        (err := err) (hack := hack) (pos := pos) (entp := 1) (clen := clen) (csz := csz) (esp := esp) (eb := eb) (el := el) (ev := ev) (canary := canary);
        [exact HR| exact RF| exact (fs_call_ok_le FI _ _ _ 2%nat (fs_call_ok_push FI st stc (wz A0_TP) 3%nat _ FCO LIVE1) ltac:(lia))| exact AE| exact ST| exact CLO| lia| exact QAL| lia| exact MI| exact LVP| exact PHI| exact PAL| exact SHP| exact HSUB| exact NDH
         | exact PMETH| exact PRS| exact PVER| exact PHL| lia| exact PENT| exact PMSG| exact PCTL| exact PSC| exact CUR| exact CLOW| exact SHE| exact IWC| exact GS
         | apply (shz_sub m _ _ _ _ SHZ); [lia| apply sh_mono; lia]| apply (shr_sub m _ _ _ _ SHR); [lia| pose proof (sh_mono q' q ltac:(lia)); lia]| reflexivity]. }
    intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & r & err' & hack' & pos' & entp' & clen' & ev'
                & -> & MU & WM & MI' & FK & LIVE' & RF' & ST' & AE' & PENT' & PCTL' & PHL' & CLOW' & IWC' & RCASES).
    rewrite ret_pc_even by lia.

    assert (SHPK : shw m P 504 -> shw m' P 504).
    { intros _. apply (shw_fkeep FI (germ_WA P hs) stc m m' P 504 SHP FK RF LVP). exact (out_W3 _ HW3). }
    destruct (ekeep_fk (germ_WA P hs) WPg (vblocks hs) (okbA FI AI (Some kA) A cap) s LB q' stc m m' MU WM FK ltac:(lia) LSUB SHPK (germW_cls m hs HM) WPg_ok WPg_in HR) as [EK HR'];
      [intros b Hb; apply HSUB; exact (vblocks_sub ns hs b Hb)| exact TSUB| exact KSUB
       | intros a b Ha Hb; exact (IHT a b (vblocks_sub ns hs a Ha) Hb)| intros a b Ha Hb; exact (IHK a b (vblocks_sub ns hs a Ha) Hb)|].
    assert (INV' : pinv q' m').
    { apply (pinv_stepF eshadow eq_refl (germ_WA P hs) q' m m' stc st' INV LIVE1 MU WM FK LIVE' RF' ST' MI' AE' HW3). exists jf.
      apply (rw_cells_fkeep FI (germ_WA P hs) stc m m' _ _ FT1 FK WM); [left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia|].
      apply (germW_djF s LB m ns hs _ _ HR HSUB); simpl_sizes; lia. }
    assert (RR : 0 <= r <= 6 /\ r <> 4) by (destruct RCASES as [(Z1 & _)|[(Z1 & _)|(Z1 & _)]]; lia).
    pose proof PCTL' as (_ & CR1' & CR2' & CR3' & CR4' & CR5' & CR6' & CR7').
    Ltac djg := unfold WPg; cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
    assert (PSC' : p_scan m' P cur) by (exact (ek_scan _ _ m m' cur EK ltac:(djg) PSC)).
    assert (PMSG' : p_msg FI AI m' LB P A len cap (Some kA) bs) by (apply (ek_msg _ _ LB m m' A len cap (Some kA) bs EK ltac:(djg)); [intros b Hb; exact Hb| exact PMSG]).
    assert (PMETH' : p_meth m' P meth) by (exact (ek_meth _ _ m m' meth EK ltac:(djg) PMETH)).
    assert (EXF' : EX s LB m' cur A len cap (Some kA) bs (wz (A + cur)) (wz 0) err' hack' pos' entp' clen' csz cur ns hs X meth).
    { eapply (EX_move WPg _ s LB m cur A len cap (Some kA) bs eb el err hack pos 1 clen csz esp ns hs X meth s LB m'); [exact EXF| exact EK| exact WPg_ok
        | djg| djg| exact HR'| exact PSC'| exact PMSG'| exact CUR| exact PENT'| exact PCTL'| exact PHL'| exact PMETH'| exact SUB| exact ND| exists ev'; exact CLOW'| exact SCR| exact HSF]. }
    apply (blk1bE q' r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (wz 3) t3 t4 t5 t6 m' _ (proj1 (proj2 INV')) MI').
    apply (loopE q' r (wz 0x89bf8) t0 t1 (wz r) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' _ ltac:(lia)).
    - intros E6 z10. apply evt_done.
      destruct RCASES as [(Z1 & _)|[(_ & Z2 & Z3 & Z4 & Z5)|(Z1 & _)]]; [exfalso; lia| | exfalso; lia].
      eapply (HCN s LB m' q' cur A len cap kA bs (wz (A + cur)) (wz 0) err' hack' pos' entp' clen' csz cur ns hs X meth).
      + assert (MEAS : pe_measA entp' (wz 0) + 1 <= pe_measA 1 el).
        { unfold pe_meas0. cbn [Z.eqb Pos.eqb]. assert (E0 : bv_unsigned (wz 0) = 0) by (apply unsigned_lit; lia).
          destruct (entp' =? 1) eqn:Q1; [apply Z.eqb_eq in Q1; exfalso; lia|]. destruct (entp' =? 3); [rewrite E0; lia|]. destruct (entp' =? 5); [rewrite E0; lia| lia]. }
        eapply (EI_move WPg _ s LB m q' cur A len cap (Some kA) bs eb el err hack pos 1 clen csz esp ns hs X meth s LB m'); [exact EIF| exact EK| exact WPg_ok
          | djg| djg| exact HR'| exact INV'| exact PSC'| exact PMSG'| exact CUR| exact PENT'| exact PCTL'| exact PHL'| exact PMETH'| exact SUB| exact ND| exists ev'; exact CLOW'
          | | exact XB
          | eapply ebud_mono; [| | exact BUD]; [clear - MEAS; lia| clear; lia]
          | exact CB| exact HSS
          | exists k0; split; [exact ES0|]; clear - MEAS K0 KM KC KN; lia].
        split; [intros _; lia|]. split; [intros _; exists 0; split; [reflexivity| lia]| intros Hx; exfalso; lia].
      + assert (MEAS : pe_measA entp' (wz 0) + 1 <= pe_measA 1 el).
        { unfold pe_meas0. cbn [Z.eqb Pos.eqb]. assert (E0 : bv_unsigned (wz 0) = 0) by (apply unsigned_lit; lia).
          destruct (entp' =? 1) eqn:Q1; [apply Z.eqb_eq in Q1; exfalso; lia|]. destruct (entp' =? 3); [rewrite E0; lia|]. destruct (entp' =? 5); [rewrite E0; lia| lia]. }
        clear - MEAS. lia.
    - intros N6 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z28 z29 z30 z31. apply evt_done.
      apply (exitJ 0x8a1f4 q' r s LB m' cur A len cap (Some kA) bs (wz (A + cur)) (wz 0) err' hack' pos' entp' clen' csz cur ns hs X meth); [discriminate| unfold retire_pc; lia| exact EXF'| exact INV'| | lia| lia].
      intros N3. destruct RCASES as [(Z1 & Z2 & -> & _)|[(Z1 & _)|(Z1 & _)]]; [| exfalso; lia| exfalso; lia].
      split; [intros Hx; exfalso; lia|]. split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx].
  Qed.
End PJ.
End W.
