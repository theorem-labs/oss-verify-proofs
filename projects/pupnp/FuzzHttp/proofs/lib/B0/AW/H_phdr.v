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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HApxF HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjA HObjK HObjF FsEnvKit HCount H_list_access H_memptr_cmp H_ListFind H_freelist H_ListAddTail H_httpheader_free
     H_membuffer_assign H_membuffer_append H_init_shw H_scanner_get_token H_map_str_to_int H_vfm_A H_vfm_G H_match_A H2KitA HPrepA H_hlist_view H_list_shw H_phdr_seg.
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
Ltac hokA V := destruct V as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB & ALO & AHI & LENC & AAL & TFS & TBAND & CAPB).

Inductive hgrow (n : Z) : Z -> BL -> Z -> BL -> Prop :=
| hg_same : forall N LB, hgrow n N LB N LB
| hg_new : forall N (LB : BL) (k k' : K) A A' c c' len, In (k, A, c + 1) LB -> 0 <= len <= c -> len + n <= c' -> c' <= c + n + 5 ->
    c < len + n -> c + 5 <= c' <= c + Z.max 5 n ->
    hgrow n N LB (N + nsec1 (c' + 1)) ((k', A', c' + 1) :: lb_remove (am_K_eqb FI AI) k LB).

Inductive hline : Z -> Z -> BL -> Z -> BL -> Prop :=
| hl_new : forall N (LB : BL) d tlz l (kh kn kv kd : K) H NA nc VA vc D,
    1 <= tlz -> 1 <= l -> tlz + 1 <= d -> tlz + l + 1 <= d -> tlz <= nc <= tlz + 5 -> l <= vc <= l + 5 ->
    hline d N LB (N + nsec1 (nc + 1) + nsec1 (vc + 1)) ((kd, D, 24) :: (kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB)
| hl_ext : forall N LB d l N1 LB1 N2 LB2, 2 <= d -> 0 <= l /\ l + 3 <= d -> hgrow 2 N LB N1 LB1 -> hgrow l N1 LB1 N2 LB2 -> hline d N LB N2 LB2.

Inductive hpart : Z -> Z -> BL -> Z -> BL -> Prop :=
| hp_refl : forall N LB d, 0 <= d -> hpart d N LB N LB
| hp_new1 : forall N (LB : BL) d (kh : K) H, 2 <= d -> hpart d N LB N ((kh, H, 88) :: LB)
| hp_new2 : forall N (LB : BL) d tlz (kh kn : K) H NA nc, 1 <= tlz -> tlz + 1 <= d -> tlz <= nc <= tlz + 5 ->
    hpart d N LB (N + nsec1 (nc + 1)) ((kn, NA, nc + 1) :: (kh, H, 88) :: LB)
| hp_new3 : forall N (LB : BL) d tlz l (kh kn kv : K) H NA nc VA vc,
    1 <= tlz -> 1 <= l -> tlz + 1 <= d -> tlz + l + 1 <= d -> tlz <= nc <= tlz + 5 -> l <= vc <= l + 5 ->
    hpart d N LB (N + nsec1 (nc + 1) + nsec1 (vc + 1)) ((kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB)
| hp_ext1 : forall N LB d N1 LB1, 2 <= d -> hgrow 2 N LB N1 LB1 -> hpart d N LB N1 LB1.

Inductive hlines : Z -> Z -> BL -> Z -> BL -> Prop :=
| hls_nil : forall N LB, hlines 0 N LB N LB
| hls_cons : forall d1 d2 N LB N1 LB1 N2 LB2, hline d1 N LB N1 LB1 -> hlines d2 N1 LB1 N2 LB2 -> hlines (d1 + d2) N LB N2 LB2.

Definition hreach (c G : Z) (N : Z) (LB : BL) (N' : Z) (LB' : BL) : Prop :=
  exists d1 d2 N1 LB1, hlines d1 N LB N1 LB1 /\ hpart d2 N1 LB1 N' LB' /\ d1 + d2 <= c /\ CG_A * (N' - N) <= G + CG_B * (d1 + d2) + CG_SL.

Definition hbud (c G : Z) (s : aps FI AI) (LB : BL) : Prop :=
  forall N' LB' (s' : aps FI AI) n, hreach c G (am_nsec FI AI s) LB N' LB' -> am_nsec FI AI s' = N' -> 0 <= n <= A0_MAXREQ -> am_budget FI AI s' LB' n.

#[using="Type"] Lemma hline_nonneg : forall d N LB N' LB', hline d N LB N' LB' -> 2 <= d.
Proof. intros d N LB N' LB' H. destruct H; lia. Qed.
#[using="Type"] Lemma hlines_nonneg : forall d N LB N' LB', hlines d N LB N' LB' -> 0 <= d.
Proof. intros d N LB N' LB' H. induction H; [lia|]. pose proof (hline_nonneg _ _ _ _ _ H). lia. Qed.
#[using="Type"] Lemma hlines_snoc : forall d1 N LB N1 LB1, hlines d1 N LB N1 LB1 -> forall d2 N2 LB2, hline d2 N1 LB1 N2 LB2 -> hlines (d1 + d2) N LB N2 LB2.
Proof.
  intros d1 N LB N1 LB1 H. induction H; intros d3 N3 LB3 HL.
  - replace (0 + d3) with (d3 + 0) by lia. eapply hls_cons; [exact HL| apply hls_nil].
  - replace (d1 + d2 + d3) with (d1 + (d2 + d3)) by lia. eapply hls_cons; [exact H| apply IHhlines; exact HL].
Qed.

#[using="Type"] Lemma lb_remove_len : forall k (LB : BL) b, In b LB -> blk_id b = k -> (length (lb_remove (am_K_eqb FI AI) k LB) < length LB)%nat.
Proof.
  induction LB as [|b0 LB IH]; intros b HIN E; [destruct HIN|].
  assert (LE : (length (lb_remove (am_K_eqb FI AI) k LB) <= length LB)%nat) by (unfold lb_remove; apply list.length_filter).
  unfold lb_remove in *. rewrite list.filter_cons. destruct (decide _) as [D|D].
  - destruct HIN as [->|HIN]; [| cbn [length]; specialize (IH b HIN E); lia].
    exfalso. apply Is_true_true_1 in D. rewrite E in D.
    pose proof (proj2 (am_K_eqb_eq FI AI k k) eq_refl) as Q. rewrite Q in D. discriminate D.
  - cbn [length]. lia.
Qed.
#[using="Type"] Lemma hgrow_len : forall n N LB N' LB', hgrow n N LB N' LB' -> (length LB' <= length LB)%nat.
Proof.
  intros n N LB N' LB' H. destruct H as [N LB|N LB k k' A A' c c' len HIN]; [lia|].
  cbn [length]. pose proof (lb_remove_len k LB (k, A, c + 1) HIN eq_refl). lia.
Qed.
#[using="Type"] Lemma hl_blocks_len : forall (ns : list (BLK * Z)) (hs : list hdr), map snd ns = map (hA FI AI) hs -> length (hl_blocks FI AI ns hs) = (4 * length hs)%nat.
Proof.
  intros ns hs E. unfold hl_blocks. rewrite length_app, length_map.
  assert (L1 : length ns = length hs) by (rewrite <- (length_map snd ns), E, length_map; reflexivity).
  assert (L2 : length (hdrs_blocks FI AI hs) = (3 * length hs)%nat).
  { clear. induction hs as [|h hs IH]; [reflexivity|]. rewrite hdrs_blocks_cons, length_app, IH. cbn [hblocks length]. lia. }
  lia.
Qed.
#[using="Type"] Lemma p_hlist_len : forall m P ns hs X, p_hlist FI AI m P ns hs X -> length (hl_blocks FI AI ns hs) = (4 * length hs)%nat.
Proof. intros m P ns hs X (_ & _ & _ & _ & _ & IT & _). exact (hl_blocks_len ns hs IT). Qed.

#[using="Type"] Lemma p_hlist_pure : forall m P ns hs X, p_hlist FI AI m P ns hs X -> Forall (hdro_pure FI AI) hs.
Proof. intros m P ns hs X (_ & _ & _ & _ & HM & _). apply Forall_forall. intros h Hh. exact (proj2 (hdrs_mem_In FI AI hs m h HM Hh)). Qed.
#[using="Type"] Lemma p_hlist_cgG : forall m P ns hs X, p_hlist FI AI m P ns hs X -> 0 <= cgG FI AI hs.
Proof. intros m P ns hs X H. exact (cgG_nonneg FI AI hs (p_hlist_pure m P ns hs X H)). Qed.

#[using="Type"] Lemma hpart_d_nonneg : forall d N LB N' LB', hpart d N LB N' LB' -> 0 <= d.
Proof. intros d N LB N' LB' H. destruct H; lia. Qed.
#[using="Type"] Lemma hpart_nsec : forall d N LB N' LB', hpart d N LB N' LB' -> N <= N' <= N + 2.
Proof.
  intros d N LB N' LB' H. destruct H as [N LB d D0|N LB d kh H D2|N LB d tlz kh kn H NA nc T1 T2 T3|N LB d tlz l kh kn kv H NA nc VA vc T1 T2 T3 T4 T5 T6|N LB d N1 LB1 D2 HG]; try lia.
  - pose proof (nsec1_range (nc + 1)). lia.
  - pose proof (nsec1_range (nc + 1)). pose proof (nsec1_range (vc + 1)). lia.
  - destruct HG as [N LB|N LB k k' A A' c c' len HIN]; [lia|]. pose proof (nsec1_range (c' + 1)). lia.
Qed.

#[using="Type"] Lemma hbud_now : forall c G s LB n, hbud c G s LB -> 0 <= G -> 0 <= c -> 0 <= n <= A0_MAXREQ -> am_budget FI AI s LB n.
Proof.
  intros c G s LB n HB HG Hc Hn. apply (HB (am_nsec FI AI s) LB s n); [| reflexivity| exact Hn].
  exists 0, 0, (am_nsec FI AI s), LB. split; [apply hls_nil|]. split; [apply hp_refl; lia|]. unfold CG_A, CG_B, CG_SL. lia.
Qed.
#[using="Type"] Lemma hbud_le_now : forall c G s LB n, hbud c G s LB -> 0 <= G -> 0 <= c -> n <= A0_MAXREQ -> am_budget_le FI AI s LB n.
Proof. intros c G s LB n HB HG Hc Hn n' Hn'. apply (hbud_now c G s LB n' HB HG Hc). lia. Qed.

#[using="Type"] Lemma hbud_part : forall c G d s LB s' LB' n, hbud c G s LB -> 0 <= G -> hpart d (am_nsec FI AI s) LB (am_nsec FI AI s') LB' -> d <= c ->
  0 <= n <= A0_MAXREQ -> am_budget FI AI s' LB' n.
Proof.
  intros c G d s LB s' LB' n HB HG HP Hd Hn. apply (HB (am_nsec FI AI s') LB' s' n); [| reflexivity| exact Hn].
  exists 0, d, (am_nsec FI AI s), LB. split; [apply hls_nil|]. split; [exact HP|].
  pose proof (hpart_d_nonneg _ _ _ _ _ HP). pose proof (hpart_nsec _ _ _ _ _ HP). unfold CG_A, CG_B, CG_SL. lia.
Qed.

#[using="Type"] Lemma hbud_line : forall c G G' d s LB s' LB', hbud c G s LB -> hline d (am_nsec FI AI s) LB (am_nsec FI AI s') LB' ->
  CG_A * (am_nsec FI AI s' - am_nsec FI AI s) + G' <= G + CG_B * d -> hbud (c - d) G' s' LB'.
Proof.
  intros c G G' d s LB s' LB' HB HL CPL N2 LB2 s2 n (d1 & d2 & N1 & LB1 & HLS & HP & Hd & GD) EN Hn.
  apply (HB N2 LB2 s2 n); [| exact EN| exact Hn].
  exists (d + d1), d2, N1, LB1. split; [eapply hls_cons; [exact HL| exact HLS]|]. split; [exact HP|]. split; [lia|].
  unfold CG_A, CG_B, CG_SL in *. lia.
Qed.

#[using="Type"] Lemma hbud_lines_now : forall c G d s LB s' LB' n, hbud c G s LB -> hlines d (am_nsec FI AI s) LB (am_nsec FI AI s') LB' -> d <= c ->
  CG_A * (am_nsec FI AI s' - am_nsec FI AI s) <= G + CG_B * d + CG_SL -> 0 <= n <= A0_MAXREQ -> am_budget FI AI s' LB' n.
Proof.
  intros c G d s LB s' LB' n HB HL Hd GD Hn. apply (HB (am_nsec FI AI s') LB' s' n); [| reflexivity| exact Hn].
  exists d, 0, (am_nsec FI AI s'), LB'. split; [exact HL|]. split; [apply hp_refl; lia|]. split; [lia|]. replace (d + 0) with d by lia. exact GD.
Qed.

Definition phdr_WA (P A cap : Z) : list ivl :=
  [(P + 4, P + 8); (P + 288, P + 344); (P + 448, P + 452); (P + 488, P + 496); (A, A + (cap + 1))]%Z.

Definition phdr_statics (ws : list word) (m : mem) (cslack : list byte) : Prop :=
  H_phdr_seg.hstat ws m /\ shw m SEPTAB_A 20 /\ shw m FMT_HDR_A 8
  /\ (forall m', mem_inv asegs m' -> bytes_at asegs m' COMMA_ADDR_A ([Z_to_bv 8 44; Z_to_bv 8 32] ++ Z_to_bv 8 0 :: cslack))
  /\ 5 <= Z.of_nat (length cslack) <= 16 /\ shw m COMMA_ADDR_A 3
  /\ bytes_at asegs m ZERO_ADDR_A [Z_to_bv 8 0] /\ shw m ZERO_ADDR_A 1.

Definition hsumA (hs : list hdr) : Z := fold_right (fun h a => vlen FI AI h + nlen FI AI h + a) 0 hs.
#[using="Type"] Lemma hsumA_app : forall hs1 hs2, hsumA (hs1 ++ hs2) = hsumA hs1 + hsumA hs2.
Proof. intros hs1 hs2. unfold hsumA. induction hs1 as [|h hs1 IH]; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.
#[using="Type"] Lemma hsumA_hlenA : forall hs, hsumA hs = hlenA FI AI hs.
Proof. reflexivity. Qed.

Definition phdr_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LB LBK : BL) (P cur A len cap : Z) (kA : K) (bs : list byte) (X HB CB NB HS : Z)
    (meth isreq maj min err hack pos entp clen csz esp lo : Z) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI)
                           (r cur' meth' pos' d : Z) (ns' : list (BLK * Z)) (hs' : list hdr),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st' m' /\ fs_live FI st' = fs_live FI st
    /\ apxF FI AI (phdr_WA P A cap) LBK q st m m'
    /\ RHEAP_A FI AI s' LB' m'
    /\ In (kA, A, cap + 1) LB' /\ bsub FI AI (hl_blocks FI AI ns' hs') LB' /\ bsub FI AI LBK LB'
    /\ NoDup (map blk_id (hl_blocks FI AI ns' hs' ++ (kA, A, cap + 1) :: LBK))
    /\ hlines d (am_nsec FI AI s) LB (am_nsec FI AI s') LB' /\ 0 <= d <= cur' - cur
    /\ p_scan m' P cur' /\ p_msg FI AI m' LB' P A len cap (Some kA) bs /\ p_meth m' P meth' /\ p_ver m' P isreq maj min
    /\ p_hlist FI AI m' P ns' hs' (X + 2 * (cur' - cur)) /\ 2 * hsumA hs' <= HB + (X + 2 * (cur' - cur))
    /\ hsumA hs' <= HS + d
    /\ 5 * am_nsec FI AI s' <= CB + phiH FI AI hs' /\ Z.of_nat (length LB') <= NB + 4 * Z.of_nat (length hs')
    /\ p_ctl m' P err hack pos' entp clen csz esp
    /\ shw m' P 504 /\ shz m' (sh lo) (sh q) /\ shr m' (sh lo - sh lo mod 8) (sh q + 8)
    /\ (meth' = meth \/ meth' = 11) /\ cur <= cur' <= len /\ 0 <= r <= 5
    /\ ( (r = PARSE_OK /\ pos' = POS_ENTITY_A) \/ (r = PARSE_SUCCESS /\ pos' = POS_COMPLETE_A) \/ (r <> PARSE_OK /\ pos' = pos) ).

Definition phdr_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB LBK : BL) (st : fsstate FI)
         (P lo cur A len cap : Z) (kA : K) (bs : list byte) (ns : list (BLK * Z)) (hs : list hdr) (X : Z)
         (meth isreq maj min err hack pos entp clen csz esp : Z) (ws : list word) (cslack : list byte) (ras : list Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st (wz A0_TP) 3 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - PHDR_DEPTH_A -> q mod 16 = 0 -> q + 64 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  lb (fs_live FI st) P 504 -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  p_scan m P cur -> p_msg FI AI m LB P A len cap (Some kA) bs -> 0 <= cur <= len ->
  p_meth m P meth -> p_ver m P isreq maj min -> p_hlist FI AI m P ns hs X -> p_ctl m P err hack pos entp clen csz esp ->
  bsub FI AI (hl_blocks FI AI ns hs) LB -> bsub FI AI LBK LB -> NoDup (map blk_id (hl_blocks FI AI ns hs ++ (kA, A, cap + 1) :: LBK)) ->
  X + 2 * (len - cur) <= 2^27 + 64 ->
  hbud (len - cur) (cgG FI AI hs) s LB ->
  length ws = 66%nat -> (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64) ->
  phdr_statics ws m cslack -> am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32) ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: 0x887a0 :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz P ->
  AJ FI AI J (phdr_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB LBK P cur A len cap kA bs X (2 * hsumA hs - X) (5 * am_nsec FI AI s - phiH FI AI hs) (Z.of_nat (length LB) - 4 * Z.of_nat (length hs)) (hsumA hs)
                          meth isreq maj min err hack pos entp clen csz esp lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz parse_headers_entryA) fc None m (seg_rom asegs))
    s LB.

Section PHJ.
  Variables (q lo P A len cap : Z) (st : fsstate FI).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis HOK : H_phdr_seg.ph_okA FI q lo P A len cap st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st (wz A0_TP) 3.
  Hypothesis FE0 : FSENV FI m0.
  Variable ws : list word.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64.
  Notation F := (H_phdr_seg.hF FI st). Notation FL := (H_phdr_seg.hFL FI st). Notation SF := (H_phdr_seg.hSF FI st).
  Notation S := (P + 480)%Z. Notation MB := (P + 400)%Z. Notation L := (P + 288)%Z.

Local Notation ph_okA := (H_phdr_seg.ph_okA FI q lo P A len cap st).
Local Notation hF := (H_phdr_seg.hF FI st).
Local Notation hWHP := (H_phdr_seg.hWHP P).
Local Notation hWHS := (H_phdr_seg.hWHS P).
Local Notation hW0 := (H_phdr_seg.hW0 FI q lo P A cap).
Local Notation hpm := (H_phdr_seg.hpm P).
Local Notation hSHC := (H_phdr_seg.hSHC P).
Local Notation hrestT := (H_phdr_seg.hrestT FI q lo P A cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation hscr := (H_phdr_seg.hscr FI P st).
Local Notation hscrE := (H_phdr_seg.hscrE FI P st).
Local Notation hinvGT := (H_phdr_seg.hinvGT FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation hinv := (H_phdr_seg.hinv FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation hinvE := (H_phdr_seg.hinvE FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation headstH := (H_phdr_seg.headstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation epistH := (H_phdr_seg.epistH FI q st gp (wz A0_TP) F_ fc).
Local Notation lb_in_fsH := (H_phdr_seg.lb_in_fsH FI st m0 RF0).
Local Notation sub_app_iv_fsH := (H_phdr_seg.sub_app_iv_fsH FI).
Local Notation WHP_app := (H_phdr_seg.WHP_app FI q lo P A len cap st m0 HOK RF0).
Local Notation WHS_app := (H_phdr_seg.WHS_app FI q lo P A len cap st m0 HOK RF0).
Local Notation text_app_iv := (H_phdr_seg.text_app_iv FI q lo P A len cap st HOK).
Local Notation W0_fsw := (H_phdr_seg.W0_fsw FI q lo P A len cap st m0 HOK RF0).
Local Notation hframe_facts := (H_phdr_seg.hframe_facts FI q lo P A len cap st m0 HOK RF0).
Local Notation hWL := (H_phdr_seg.hWL FI lo P A cap st).
Local Notation fs_shadow_band := (H_phdr_seg.fs_shadow_band FI q lo P A len cap st HOK).
Local Notation text_out_fs := (H_phdr_seg.text_out_fs FI q lo P A len cap st HOK).
Local Notation WL_app := (H_phdr_seg.WL_app FI q lo P A len cap st m0 HOK RF0).
Local Notation WL_env := (H_phdr_seg.WL_env FI q lo P A len cap st m0 HOK RF0).
Local Notation WL_sub0 := (H_phdr_seg.WL_sub0 FI q lo P A len cap st m0 HOK RF0).
Local Notation WL_fk := (H_phdr_seg.WL_fk FI q lo P A len cap st m0 HOK RF0).
Local Notation hlive := (H_phdr_seg.hlive FI P st).
Local Notation hlive_of := (H_phdr_seg.hlive_of FI q lo P A len cap st m0 HOK RF0).
Local Notation WL_rf := (H_phdr_seg.WL_rf FI q lo P A len cap st HOK).
Local Notation WL_dj_stack := (H_phdr_seg.WL_dj_stack FI q lo P A len cap st m0 HOK RF0).
Local Notation WL_dj_frame := (H_phdr_seg.WL_dj_frame FI q lo P A len cap st m0 HOK RF0).
Local Notation hpm_refl := (H_phdr_seg.hpm_refl P).
Local Notation hpm_step := (H_phdr_seg.hpm_step P).
Local Notation hpm_fkeep := (H_phdr_seg.hpm_fkeep FI P).
Local Notation hpm_set := (H_phdr_seg.hpm_set P).
Local Notation WL_dj_meth := (H_phdr_seg.WL_dj_meth FI q lo P A len cap st m0 HOK RF0).
Local Notation hWok := (H_phdr_seg.hWok FI q lo P A cap st).
Local Notation WL_ok := (H_phdr_seg.WL_ok FI q lo P A len cap st m0 HOK RF0).
Local Notation hrest_stepG := (H_phdr_seg.hrest_stepG FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hrest_hpm := (H_phdr_seg.hrest_hpm FI q lo P A cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation hrest_qb := (H_phdr_seg.hrest_qb FI q lo P A cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation hrest_stepW := (H_phdr_seg.hrest_stepW FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation sh_window_ok := (H_phdr_seg.sh_window_ok FI q lo P A len cap st HOK).
Local Notation hinv_stepG := (H_phdr_seg.hinv_stepG FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hinv_stepW := (H_phdr_seg.hinv_stepW FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hWC := (H_phdr_seg.hWC FI P st).
Local Notation hWF := (H_phdr_seg.hWF FI lo P st).
Local Notation fkeep_weaken_fkH := (H_phdr_seg.fkeep_weaken_fkH FI).
Local Notation WC_fk := (H_phdr_seg.WC_fk FI P st m0 RF0).
Local Notation WC_app := (H_phdr_seg.WC_app FI q lo P A len cap st m0 HOK RF0).
Local Notation WF_fsw := (H_phdr_seg.WF_fsw FI q lo P A len cap st m0 HOK RF0).
Local Notation WF_env := (H_phdr_seg.WF_env FI q lo P A len cap st m0 HOK RF0).
Local Notation WF_sub0 := (H_phdr_seg.WF_sub0 FI q lo P A len cap st m0 HOK RF0).
Local Notation WF_dj_stack := (H_phdr_seg.WF_dj_stack FI q lo P A len cap st m0 HOK RF0).
Local Notation WC_dj_frame := (H_phdr_seg.WC_dj_frame FI q lo P A len cap st m0 HOK RF0).
Local Notation hrest_stepF := (H_phdr_seg.hrest_stepF FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hrest_rf := (H_phdr_seg.hrest_rf FI q lo P A cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation WC_fsout := (H_phdr_seg.WC_fsout FI q lo P A len cap st m0 HOK RF0).
Local Notation hinv_stepF := (H_phdr_seg.hinv_stepF FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hscr_E := (H_phdr_seg.hscr_E FI P st).
Local Notation hinv_E := (H_phdr_seg.hinv_E FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation tok_shwH := (H_phdr_seg.tok_shwH FI q lo P A len cap st HOK).
Local Notation hWS := (H_phdr_seg.hWS lo P).
Local Notation WS_sub := (H_phdr_seg.WS_sub FI lo P A cap st).
Local Notation text_bytesH := (H_phdr_seg.text_bytesH FI q lo P A len cap st HOK).
Local Notation WS_dj_obj := (H_phdr_seg.WS_dj_obj FI q lo P A len cap st m0 HOK RF0).
Local Notation hinv_stepS := (H_phdr_seg.hinv_stepS FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hscr_stepS := (H_phdr_seg.hscr_stepS FI q lo P A len cap st m0 HOK RF0).
Local Notation sgt_callH := (H_phdr_seg.sgt_callH IC FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0).
Local Notation hinv_stepX := (H_phdr_seg.hinv_stepX FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hWE := (H_phdr_seg.hWE FI q lo st).
Local Notation WE_fk := (H_phdr_seg.WE_fk FI q lo P A len cap st m0 HOK RF0).
Local Notation WE_fsw := (H_phdr_seg.WE_fsw FI q lo P A len cap st m0 HOK RF0).
Local Notation WE_env := (H_phdr_seg.WE_env FI q lo P A len cap st m0 HOK RF0).
Local Notation WE_sub0 := (H_phdr_seg.WE_sub0 FI q lo P A len cap st m0 HOK RF0).
Local Notation WE_dj_obj := (H_phdr_seg.WE_dj_obj FI q lo P A len cap st m0 HOK RF0).
Local Notation shwP_fkeep := (H_phdr_seg.shwP_fkeep FI q lo P A len cap st m0 HOK RF0).
Local Notation hpostE := (H_phdr_seg.hpostE FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation xstH := (H_phdr_seg.xstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation exitH1 := (H_phdr_seg.exitH1 FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0).
Local Notation epiH := (H_phdr_seg.epiH FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0).
Local Notation prologueH := (H_phdr_seg.prologueH IC FI STACK_MALLOC_2 q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 FCO FE0).
Local Notation hvf_ok := (H_phdr_seg.hvf_ok FI q lo P A len cap st m0 HOK RF0).
Local Notation hval_shw := (H_phdr_seg.hval_shw FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0).
Local Notation hrest_mu := (H_phdr_seg.hrest_mu FI q lo P A cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation endstH := (H_phdr_seg.endstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation namestH := (H_phdr_seg.namestH FI q P st gp (wz A0_TP) F_ fc).
Local Notation headH := (H_phdr_seg.headH IC FI STACK_MALLOC_0 STACK_MALLOC_1 q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 FCO).
Local Notation hstat := (H_phdr_seg.hstat ws).
Local Notation above_image_dj := (H_phdr_seg.above_image_dj ws WSL).
Local Notation hstat_step := (H_phdr_seg.hstat_step FI ws WSL).
Local Notation WL_above := (H_phdr_seg.WL_above FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation WF_above := (H_phdr_seg.WF_above FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation WL_fsw := (H_phdr_seg.WL_fsw FI q lo P A len cap st m0 HOK RF0).
Local Notation bytes_skipnH := (H_phdr_seg.bytes_skipnH ws WSL).
Local Notation knownstH := (H_phdr_seg.knownstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation unkstH := (H_phdr_seg.unkstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation nameH := (H_phdr_seg.nameH IC FI STACK_MALLOC_0 q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 FCO ws WSL).
Local Notation hinv_stepSh := (H_phdr_seg.hinv_stepSh FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation WM_ok := (H_phdr_seg.WM_ok FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hinv_stepM := (H_phdr_seg.hinv_stepM FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation hstat_stepM := (H_phdr_seg.hstat_stepM FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation unpoisonH := (H_phdr_seg.unpoisonH FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation repoisonH := (H_phdr_seg.repoisonH FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation u64arr_read4A := (H_phdr_seg.u64arr_read4A ws WSL).
Local Notation tempstH := (H_phdr_seg.tempstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation knownA := (H_phdr_seg.knownA FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL HID).
Local Notation own_iv := (H_phdr_seg.own_iv FI st).
Local Notation own_dj := (H_phdr_seg.own_dj FI st).
Local Notation own_sub0 := (H_phdr_seg.own_sub0 FI q lo P A len cap st m0 HOK RF0).
Local Notation hinv_stepOwn := (H_phdr_seg.hinv_stepOwn FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation hinv_stepL := (H_phdr_seg.hinv_stepL FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation hscr_stepL := (H_phdr_seg.hscr_stepL FI lo P st ws WSL).
Local Notation hstat_stepL := (H_phdr_seg.hstat_stepL FI q lo P A len cap st HOK ws WSL).
Local Notation htmp_shw := (H_phdr_seg.htmp_shw FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation hapx := (H_phdr_seg.hapx FI A cap).
Local Notation hlist := (H_phdr_seg.hlist FI P A cap).
Local Notation hapx_dj0 := (H_phdr_seg.hapx_dj0 FI q lo P A len cap st m0 HOK RF0).
Local Notation hlist_stretch := (H_phdr_seg.hlist_stretch FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hlist_stepL := (H_phdr_seg.hlist_stepL FI q lo P A len cap st HOK ws WSL).
Local Notation W0_above := (H_phdr_seg.W0_above FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hstat_stretch := (H_phdr_seg.hstat_stretch FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hnow := (H_phdr_seg.hnow FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation hinv_rest := (H_phdr_seg.hinv_rest FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation hpcells_now := (H_phdr_seg.hpcells_now FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 HOK ws WSL).
Local Notation hmeth_now := (H_phdr_seg.hmeth_now FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation newstH := (H_phdr_seg.newstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation existstH := (H_phdr_seg.existstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation hscr_stepSh := (H_phdr_seg.hscr_stepSh FI q lo P A len cap st m0 HOK RF0).
Local Notation knownB := (H_phdr_seg.knownB FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation hslk := (H_phdr_seg.hslk A cap).
Local Notation hslk_stretch := (H_phdr_seg.hslk_stretch FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hnames := (H_phdr_seg.hnames FI A cap).
Local Notation hnames_gen := (H_phdr_seg.hnames_gen FI A cap ws WSL).
Local Notation cb_split1H := (H_phdr_seg.cb_split1H ra ws WSL).
Local Notation cb_join1H := (H_phdr_seg.cb_join1H ws WSL).
Local Notation scanstH := (H_phdr_seg.scanstH FI q P A st gp (wz A0_TP) F_ fc).
Local Notation unkA := (H_phdr_seg.unkA FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation unkB := (H_phdr_seg.unkB FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation lseg_stretch := (H_phdr_seg.lseg_stretch FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hnames_stretch := (H_phdr_seg.hnames_stretch FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hcstr := (H_phdr_seg.hcstr FI q lo P A len cap st HOK ws WSL).
Local Notation unkLoop := (H_phdr_seg.unkLoop IC FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation unkH := (H_phdr_seg.unkH IC FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation nextstH := (H_phdr_seg.nextstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation nextH := (H_phdr_seg.nextH IC FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation hinv_stepPR := (H_phdr_seg.hinv_stepPR FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation endH := (H_phdr_seg.endH FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation aj_iv := (H_phdr_seg.aj_iv FI P A cap).
Local Notation aj_dj := (H_phdr_seg.aj_dj FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation aj_app := (H_phdr_seg.aj_app FI q lo P A len cap st m0 HOK RF0).
Local Notation aj_out_band := (H_phdr_seg.aj_out_band FI q lo P A len cap st m0 HOK RF0).
Local Notation aj_out_stksh := (H_phdr_seg.aj_out_stksh FI q lo P A len cap st m0 HOK RF0).
Local Notation stack_shadow_clientH := (H_phdr_seg.stack_shadow_clientH FI AI ws WSL AMS).
Local Notation hinv_stepA := (H_phdr_seg.hinv_stepA FI AI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL AMS).
Local Notation ajcallstH := (H_phdr_seg.ajcallstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation ajretstH := (H_phdr_seg.ajretstH FI q P st gp (wz A0_TP) F_ fc).
Local Notation existE1 := (H_phdr_seg.existE1 FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc ws WSL).
Local Notation existE2 := (H_phdr_seg.existE2 FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation existE3 := (H_phdr_seg.existE3 FI q P st gp (wz A0_TP) F_ fc).
Local Notation hb_iv := (H_phdr_seg.hb_iv FI lo st).
Local Notation hb_dj := (H_phdr_seg.hb_dj FI q lo P A len cap st m0 HOK RF0 ws WSL).
Local Notation hinv_stepHB := (H_phdr_seg.hinv_stepHB FI q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 HOK RF0 ws WSL).
Local Notation newN1 := (H_phdr_seg.newN1 FI q P st gp (wz A0_TP) F_ fc).
Local Notation newN3 := (H_phdr_seg.newN3 FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation newN5 := (H_phdr_seg.newN5 FI q P st gp (wz A0_TP) F_ fc ws WSL).
Local Notation hWN := (H_phdr_seg.hWN FI lo st).
Local Notation newN2 := (H_phdr_seg.newN2 FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
Local Notation newN4 := (H_phdr_seg.newN4 FI q lo P A len cap st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 HOK RF0 ws WSL).
  Local Notation W0 := hW0. Local Notation WHS := hWHS. Local Notation WHP := hWHP. Local Notation WL := hWL. Local Notation WE := hWE.
  Local Notation zb := (Z_to_bv 8 0).

#[using="ws WSL"] Lemma blk_hapx : forall s (LB : BL) m (b : BLK) (kA : K),
  RHEAP_A FI AI s LB m -> In b LB -> In (kA, A, cap + 1) LB -> b <> (kA, A, cap + 1) ->
  0x609000 <= blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling /\ blk_addr b mod 8 = 0 /\ 0 <= blk_size b
  /\ hapx (blk_addr b) (blk_size b).
Proof.
  intros s LB m b kA HR Hb HA NE.
  destruct (am_block_range FI AI s LB m b HR Hb) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof (am_blocks_disjoint FI AI s LB m b (kA, A, cap + 1) HR Hb HA NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
  split; [exact R5|]. split; [lia|]. split; [clear - R2; Z.div_mod_to_equations; lia|]. split; [exact R3|].
  unfold H_phdr_seg.hapx. split; [exact R7|]. split; [exact R6|]. lia.
Qed.

#[using="ws WSL"] Lemma hviews_of_plist : forall s (LB : BL) m (kA : K) (ns : list (BLK * Z)) (hs : list hdr) X,
  RHEAP_A FI AI s LB m -> p_hlist FI AI m P ns hs X ->
  bsub FI AI (hl_blocks FI AI ns hs) LB -> In (kA, A, cap + 1) LB -> ~ In (kA, A, cap + 1) (hl_blocks FI AI ns hs) ->
  hlist m (hd_addr FI AI ns (P + 312)) (last_addr FI AI ns (P + 288)) (zlength ns) 0 0 httpheader_free_entryA (ns3_of FI AI ns hs)
  /\ hnames m (ns3_of FI AI ns hs)
  /\ (zlength ns = 0 <-> ns3_of FI AI ns hs = []) /\ 0 <= zlength ns.
Proof.
  intros s LB m kA ns hs X HR (LHC & FLC & FFC & DL & HM & IT & VB & ZL & X0) SUB HA NIN.
  assert (LEN : length ns = length hs) by (rewrite <- (length_map snd ns), IT, length_map; reflexivity).
  unfold hl_blocks in SUB, NIN. apply (bsub_app FI AI) in SUB. destruct SUB as [NSUB HSUB].
  assert (NODE : forall b it, In (b, it) ns -> In b LB /\ b <> (kA, A, cap + 1) /\ blk_size b = 24).
  { intros b it HI. assert (Hb : In b (map fst ns)) by (apply (in_map fst _ _ HI)).
    split; [apply NSUB; exact Hb|]. split; [intros E; apply NIN; apply in_or_app; left; rewrite <- E; exact Hb|].
    exact (proj1 (dlseg_facts FI AI _ _ _ _ _ _ DL HI)). }
  assert (HBLK : forall h b, In h hs -> In b (hblocks FI AI h) -> In b LB /\ b <> (kA, A, cap + 1)).
  { intros h b Hh Hb. pose proof (hdrs_blocks_In FI AI hs h b Hh Hb) as Hbb.
    split; [apply HSUB; exact Hbb| intros E; apply NIN; apply in_or_app; right; rewrite <- E; exact Hbb]. }
  assert (HANZ : forall h, In h hs -> hA FI AI h <> 0).
  { intros h Hh. destruct (HBLK h (hk FI AI h, hA FI AI h, 88) Hh ltac:(left; reflexivity)) as [Hb _].
    destruct (am_block_range FI AI s LB m _ HR Hb) as (R1 & _). cbn in R1. lia. }
  split; [| split; [| split]].
  -
    split; [| split; [| split]].
    + pose proof (proj2 (rw_cells_app asegs m (P + 344) (fl_cells 0 0) [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)])) as Jc1.
      unfold fl_cells in Jc1 at 2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in Jc1.
      change (Z.of_nat 24) with 24 in Jc1. replace (P + 344 + 24) with (P + 368) in Jc1 by lia. specialize (Jc1 (conj FLC FFC)).
      pose proof (proj2 (rw_cells_app asegs m (P + 288) (lhead_cells (hd_addr FI AI ns (P + 312)) (last_addr FI AI ns (P + 288)) (zlength ns))
         (fl_cells 0 0 ++ [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)]))) as Jc2.
      unfold lhead_cells in Jc2 at 2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in Jc2.
      change (Z.of_nat 56) with 56 in Jc2. replace (P + 288 + 56) with (P + 344) in Jc2 by lia. specialize (Jc2 (conj LHC Jc1)).
      exact Jc2.
    + replace (P + 288 + 24) with (P + 312) by lia. apply (lsegA_of_dlseg FI AI); assumption.
    + intros N it id HI. destruct (ns3_of_In FI AI ns hs N it id IT HI) as (b & h & Hb & Hh & -> & -> & ->).
      destruct (NODE b _ Hb) as (BIN & BNE & BSZ).
      destruct (blk_hapx s LB m b kA HR BIN HA BNE) as (B1 & B2 & B3 & B4 & _). rewrite BSZ in B2.
      destruct (HBLK h (hk FI AI h, hA FI AI h, 88) Hh ltac:(left; reflexivity)) as [HIN HNE].
      destruct (blk_hapx s LB m _ kA HR HIN HA HNE) as (C1 & C2 & C3 & C4 & _). cbn [blk_addr blk_size fst snd] in C1, C2, C3.
      split; (split; [assumption|]; split; [lia|]; split; [assumption|]).
      * eapply (block_shw FI AI s LB m b); [exact HR| exact BIN| lia| lia| lia].
      * eapply (block_shw FI AI s LB m (hk FI AI h, hA FI AI h, 88)); [exact HR| exact HIN| cbn; lia| cbn; lia| lia].
    + intros N it id HI. destruct (ns3_of_In FI AI ns hs N it id IT HI) as (b & h & Hb & Hh & -> & -> & ->).
      destruct (NODE b _ Hb) as (BIN & BNE & BSZ).
      destruct (blk_hapx s LB m b kA HR BIN HA BNE) as (_ & _ & _ & _ & HX). rewrite BSZ in HX.
      destruct (HBLK h (hk FI AI h, hA FI AI h, 88) Hh ltac:(left; reflexivity)) as [HIN HNE].
      destruct (blk_hapx s LB m _ kA HR HIN HA HNE) as (_ & _ & _ & _ & HY). cbn [blk_addr blk_size fst snd] in HY.
      split; [exact HX|]. unfold H_phdr_seg.hapx in *. lia.
  -
    intros N it id HI. destruct (ns3_of_In FI AI ns hs N it id IT HI) as (b & h & Hb & Hh & -> & -> & ->).
    destruct (hdrs_mem_In FI AI hs m h HM Hh) as [((pad & HCc) & _ & _ & _ & (nb & NBC & NBZ)) HP0].
    destruct (HBLK h (nk FI AI h, nA FI AI h, ncap FI AI h + 1) Hh ltac:(right; right; left; reflexivity)) as [NIN' NNE].
    destruct (blk_hapx s LB m _ kA HR NIN' HA NNE) as (D1 & D2 & D3 & D4 & HX). cbn [blk_addr blk_size fst snd] in D1, D2, D3, D4, HX.
    pose proof (rw_cells_bytes_at asegs _ _ _ NBC) as BN. cbn [cells_bytes cbytes] in BN. rewrite app_nil_r in BN.
    assert (NBL : Z.of_nat (length nb) = ncap FI AI h + 1).
    { destruct NBC as [[W _] _]. cbn in W. destruct W as [W _]. unfold hdro_pure in HP0. lia. }
    exists (nA FI AI h), (nlen FI AI h), nb.
    split.
    { pose proof (proj1 (rw_cells_app asegs m (hA FI AI h) [C8 (wz (nA FI AI h)); C8 (wz (nlen FI AI h))] [C4 (wz (hid FI AI h)); C4 pad]) HCc) as [Jc _]. exact Jc. }
    split; [exact BN|]. unfold hdro_pure in HP0. rewrite NBL.
    split; [lia|]. split; [pose proof (VB h Hh) as [_ VBn]; unfold LMAX_A in VBn; lia|].
    split; [eapply (block_shw FI AI s LB m (nk FI AI h, nA FI AI h, ncap FI AI h + 1)); [exact HR| exact NIN'| cbn; lia| cbn; lia| lia]|].
    split; [exact D1|]. split; [exact D2| exact HX].
  - rewrite (ns3_of_nil_iff FI AI ns hs LEN). unfold zlength. destruct ns; cbn [length]; split; intros E; try reflexivity; try discriminate; lia.
  - unfold zlength. lia.
Qed.

  Variables (LBK : BL) (kA : K) (bs : list byte) (isreq maj min err hack entp clen csz esp : Z) (ras : list Z) (cslack : list byte) (HB0 CB0 NB0 HS0 : Z).
  Hypothesis VERR : 0 <= isreq <= 1 /\ - 2^31 <= maj < 2^31 /\ - 2^31 <= min < 2^31.
  Hypothesis CTLR : 0 <= err < 2^31 /\ 0 <= hack <= 1 /\ 0 <= entp <= 6 /\ 0 <= clen < 2^32 /\ 0 <= csz < 2^64 /\ 0 <= esp < 2^64.
  Hypothesis QTOP : q + 64 <= am_stack_top FI AI.
  Hypothesis TRACE : In (PC0_MALLOC :: 0x887a0 :: bv_unsigned ra :: ras) A0_TRACES.
  Hypothesis COMMAB : forall m', mem_inv asegs m' -> bytes_at asegs m' COMMA_ADDR_A ([Z_to_bv 8 44; Z_to_bv 8 32] ++ Z_to_bv 8 0 :: cslack).
  Hypothesis CSL : 5 <= Z.of_nat (length cslack) <= 16.
  Hypothesis ZSTAT : am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32).
  Hypothesis BSL : Z.of_nat (length bs) = cap + 1.

  #[using="Type"] Lemma hinv_restart : forall t scr q' cur ty tb tl va vl bs' mb m,
    hinvGT t scr q' cur ty tb tl va vl bs' mb m -> hinvGT t scr q' cur ty tb tl va vl bs' m m.
  Proof.
    intros t scr q' cur ty tb tl va vl bs' mb m
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & QBA & HR).
    destruct HR as (Hq & GAP & FRhi & FH & FT1 & FT2 & FT3 & FLP & SHF & FLG & _ & _ & _ & STC & _).
    unfold H_phdr_seg.hinvGT. repeat (split; [assumption|]). unfold H_phdr_seg.hrestT. repeat (split; [assumption|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply fkeep_refl|]. split; [exact STC| apply hpm_refl].
  Qed.

  Definition ainv (s : PS) (LB : BL) (m : mem) (ns : list (BLK * Z)) (hs : list hdr) (X meth pos : Z) : Prop :=
    RHEAP_A FI AI s LB m /\ In (kA, A, cap + 1) LB /\ bsub FI AI (hl_blocks FI AI ns hs) LB /\ bsub FI AI LBK LB
    /\ NoDup (map blk_id (hl_blocks FI AI ns hs ++ (kA, A, cap + 1) :: LBK))
    /\ p_hlist FI AI m P ns hs X
    /\ rw_cells asegs m P [C4 (wz 1)] /\ rw_cells asegs m (P + 4) [C4 (wz meth)] /\ 0 <= meth <= 11
    /\ (exists pad, rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad])
    /\ rw_cells asegs m (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos)] /\ 0 <= pos <= 4
    /\ rw_cells asegs m (P + 452) [C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)]
    /\ hstat m /\ shw m COMMA_ADDR_A 3 /\ bytes_at asegs m ZERO_ADDR_A [Z_to_bv 8 0] /\ shw m ZERO_ADDR_A 1
    /\ apxF FI AI (phdr_WA P A cap) LBK q st m0 m
    /\ fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras
    /\ 2 * hsumA hs <= HB0 + X.

  #[using="Type"] Lemma ainv_hsum : forall s LB m ns hs X meth pos, ainv s LB m ns hs X meth pos -> 2 * hsumA hs <= HB0 + X.
  Proof. intros s LB m ns hs X meth pos (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSM). exact HSM. Qed.

  #[using="q lo A len cap st m0 HOK RF0"] Lemma pgeom : FSB FI + 36864 <= P /\ P + 504 <= FSB FI + A0_FS_SIZE.
  Proof. destruct HOK as (_ & _ & _ & _ & _ & _ & _ & PLB & _). exact (lb_in_fsH _ _ PLB). Qed.

  #[using="Type"] Lemma pblk_facts : forall s (LB : BL) m ns hs (b : BLK),
    RHEAP_A FI AI s LB m -> In (kA, A, cap + 1) LB -> bsub FI AI (hl_blocks FI AI ns hs) LB ->
    NoDup (map blk_id (hl_blocks FI AI ns hs ++ (kA, A, cap + 1) :: LBK)) -> In b (hl_blocks FI AI ns hs) ->
    In b LB /\ b <> (kA, A, cap + 1).
  Proof.
    intros s LB m ns hs b HR HA SUB ND Hb. split; [apply SUB; exact Hb|].
    apply nd_app in ND. destruct ND as (_ & IDJ & _).
    apply (idj_neq _ _ b (kA, A, cap + 1) IDJ Hb). left. reflexivity.
  Qed.

  #[using="len st m0 HOK RF0 ws WSL"] Lemma pblk_keep0 : forall s (LB : BL) mb m ns hs,
    RHEAP_A FI AI s LB mb -> In (kA, A, cap + 1) LB -> bsub FI AI (hl_blocks FI AI ns hs) LB ->
    NoDup (map blk_id (hl_blocks FI AI ns hs ++ (kA, A, cap + 1) :: LBK)) ->
    munch W0 mb m -> wmono asegs mb m -> bkeep FI AI (hl_blocks FI AI ns hs) mb m.
  Proof.
    intros s LB mb m ns hs HR HA SUB ND MU WM. apply (bkeep_of_munch FI AI _ W0 mb m MU WM). intros b Hb.
    destruct (pblk_facts s LB mb ns hs b HR HA SUB ND Hb) as [BIN BNE].
    destruct (blk_hapx s LB mb b kA HR BIN HA BNE) as (B1 & B2 & B3 & B4 & HX).
    apply hapx_dj0; assumption.
  Qed.

  #[using="ws WSL bs cslack"] Lemma plist_keep : forall m m' ns hs X,
    p_hlist FI AI m P ns hs X -> bkeep FI AI (hl_blocks FI AI ns hs) m m' ->
    (forall a cs, P + 288 <= a -> a + Z.of_nat (cells_size cs) <= P + 384 -> rw_cells asegs m a cs -> rw_cells asegs m' a cs) ->
    p_hlist FI AI m' P ns hs X.
  Proof.
    intros m m' ns hs X (LHC & FLC & FFC & DL & HM & IT & VB & ZL & X0) BK PK.
    unfold p_hlist.
    split; [apply PK; [lia| unfold lhead_cells; simpl_sizes; lia| exact LHC]|].
    split; [apply PK; [lia| unfold fl_cells; simpl_sizes; lia| exact FLC]|].
    split; [apply PK; [lia| simpl_sizes; lia| exact FFC]|].
    split. { eapply (dlseg_bkeep FI AI); [exact DL| exact BK|]. intros b it Hb. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hb). }
    split. { eapply (hdrs_mem_bkeep FI AI); [exact HM| exact BK|]. intros b Hb. unfold hl_blocks. apply in_or_app. right. exact Hb. }
    repeat (split; [assumption|]). exact X0.
  Qed.

  #[using="len st m0 HOK RF0 ws WSL bs cslack"] Lemma heap_W0H : forall s (LB : BL) mb m, RHEAP_A FI AI s LB mb -> In (kA, A, cap + 1) LB -> munch W0 mb m -> wmono asegs mb m ->
    RHEAP_A FI AI s LB m.
  Proof.
    intros s LB mb m HR HA MU WM. destruct pgeom as [PF1 PF2]. hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _).
    eapply (am_heap_frame FI AI s LB mb m W0 HR MU WM). unfold H_phdr_seg.hW0, H_phdr_seg.hWHS.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [do 4 right; cbn [fst snd]; lia|].
    apply Forall_cons; [right; right; left; exists (kA, A, cap + 1); cbn [fst snd blk_addr blk_size]; split; [exact HA| lia]|].
    apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]. apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  #[using="ASL HOK RF0 WSL bs cslack"] Lemma ainv_stretch : forall t scr q' cur ty tb tl va vl bs' mb m s LB ns hs X meth pos,
    ainv s LB mb ns hs X meth pos -> hinvGT t scr q' cur ty tb tl va vl bs' mb m ->
    exists meth', ainv s LB m ns hs X meth' pos /\ (meth' = meth \/ meth' = 11).
  Proof.
    intros t scr q' cur ty tb tl va vl bs' mb m s LB ns hs X meth pos
      (HR & HA & SUB & KSUB & ND & PHL & PM0 & PM4 & MR & (pad & VER) & CT3 & PR & CT5 & HS & SHC & ZB & SHZ0 & APF & CH & HSM) INV.
    destruct (hrest_mu t q' mb m (hinv_rest _ _ _ _ _ _ _ _ _ _ _ _ INV)) as (MU & WM & FK).
    destruct (hmeth_now _ _ _ _ _ _ _ _ _ _ _ _ meth INV PM4) as (meth' & PM4' & OR).
    destruct pgeom as [PF1 PF2]. pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (PK : forall a cs, P <= a -> a + Z.of_nat (cells_size cs) <= P + 504 -> disjoint_from WHS a (Z.of_nat (cells_size cs)) ->
                 rw_cells asegs mb a cs -> rw_cells asegs m a cs).
    { intros a cs H1 H2 DJ C. exact (hpcells_now _ _ _ _ _ _ _ _ _ _ _ _ a cs INV C H1 H2 DJ). }
    assert (DJW : forall a n, P + 8 <= a -> a + n <= P + 488 -> disjoint_from WHS a n).
    { intros a n H1 H2. unfold H_phdr_seg.hWHS. cbn [disjoint_from]. split; [lia|]. split; [lia| exact I]. }
    exists meth'. split; [| exact OR]. unfold ainv.
    split; [exact (heap_W0H s LB mb m HR HA MU WM)|]. split; [exact HA|]. split; [exact SUB|]. split; [exact KSUB|]. split; [exact ND|].
    split. { apply (plist_keep mb m ns hs X PHL (pblk_keep0 s LB mb m ns hs HR HA SUB ND MU WM)).
             intros a cs H1 H2 C. apply (PK a cs); [lia| lia| apply DJW; lia| exact C]. }
    split. { apply (PK P _); [lia| simpl_sizes; lia| | exact PM0]. unfold H_phdr_seg.hWHS. cbn [disjoint_from]. simpl_sizes. split; [lia|]. split; [lia| exact I]. }
    split; [exact PM4'|]. split; [clear - OR MR; lia|].
    split; [exists pad; apply (PK (P + 264) _); [lia| simpl_sizes; lia| apply DJW; simpl_sizes; lia| exact VER]|].
    split; [apply (PK (P + 440) _); [lia| simpl_sizes; lia| apply DJW; simpl_sizes; lia| exact CT3]|].
    split; [exact PR|].
    split; [apply (PK (P + 452) _); [lia| simpl_sizes; lia| apply DJW; simpl_sizes; lia| exact CT5]|].
    split; [exact (hstat_stretch mb m HS MU WM)|].
    split; [apply (shw_frame_fs FI W0 mb m _ _ SHC MU W0_fsw); left; lia|].
    split; [eapply bytes_at_transport; [exact ZB| exact MU| apply (above_image_dj W0 _ _ W0_above); cbn [length]; lia]|].
    split; [apply (shw_frame_fs FI W0 mb m _ _ SHZ0 MU W0_fsw); left; lia|].
    split.
    { eapply (apxF_trans FI AI); [exact APF|].
      eapply (apxF_weaken FI AI ((A, A + (cap + 1)) :: WHS) (phdr_WA P A cap) LBK LBK q q st st mb m); [| | lia| intros b Hb; exact Hb| intros g Hg; exact Hg].
      - apply (apxF_of_munch_fkeep FI AI ASL s LB LBK mb m0 q lo st ((A, A + (cap + 1)) :: WHS) mb m HR KSUB RF0 CLO ltac:(lia) MU WM).
        eapply (fkeep_weaken FI WHS _ st st mb m FK); [| intros g Hg; exact Hg]. intros xo Ho. cbn [outside] in Ho. exact (proj2 Ho).
      - intros xo Ho. unfold phdr_WA in Ho. unfold H_phdr_seg.hWHS. cbn [outside] in *. destruct Ho as (O1 & O2 & O3 & O4 & O5 & _).
        split; [exact O5|]. split; [exact O1|]. split; [exact O4| exact I]. }
    split; [| exact HSM].
    eapply (fpchain_frame ras mb m _ q _ W0 CH MU WM). unfold H_phdr_seg.hW0, H_phdr_seg.hWHS.
    pose proof fs_shadow_band as (S1 & S2 & S3).
    repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil.
  Qed.

  #[using="q lo len st m0 HOK RF0"] Lemma aj_djP : forall (W : list ivl) a n, Forall aj_iv W -> P <= a -> a + n <= P + 288 -> disjoint_from W a n.
  Proof.
    intros W a n HW H1 H2. destruct pgeom as [PF1 PF2].
    induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold H_phdr_seg.aj_iv in HO. cbn [fst snd] in HO. destruct HO as (LE & XLO & YHI & [(O1 & O2 & O3)|O4]); [clear - O1 H1 H2 PF1 PF2; lia| clear - O4 H1 H2; lia].
  Qed.
  #[using="ws WSL bs cslack"] Lemma aj_dj_img : forall (W : list ivl) a n, Forall aj_iv W -> a + n <= 0x609000 -> disjoint_from W a n.
  Proof.
    intros W a n HW H1. induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold H_phdr_seg.aj_iv in HO. cbn [fst snd] in HO. destruct HO as (LE & XLO & _). lia.
  Qed.

  #[using="AMS q lo len st m0 HOK RF0 ws WSL bs cslack"] Lemma imgsh_apx : forall (W : list ivl) (LBKc : BL) q' m m2 X n,
    apx FI AI W LBKc q' m m2 -> Forall aj_iv W -> shw m X n -> 0x10000 <= X -> X + n <= 0x609000 -> shw m2 X n.
  Proof.
    intros W LBKc q' m m2 X n AP HW SW X1 X2. pose proof (shw_win_ok _ _ _ SW) as [Hn _].
    eapply (shw_band_eq m m2 X n 0x7fffa000 0x800b9200 SW).
    - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) _ _)) Hv).
      + right; left. exists 0x7fffa000, 0x800b9200. split; [| lia]. apply AMS. unfold a0_static. split; [lia|]. do 11 right. left. lia.
      + apply (aj_out_band W HW). exact Ha.
    - lia.
    - lia.
    - reflexivity.
    - reflexivity.
    - unfold sh, SHADOW_OFF. clear - X1. Z.div_mod_to_equations. lia.
    - intros _. unfold sh, SHADOW_OFF. clear - X2 Hn. Z.div_mod_to_equations. lia.
  Qed.
  #[using="AMS q lo len st m0 HOK RF0 WSL bs cslack"] Lemma hstat_apx : forall (W : list ivl) (LBKc : BL) q' m m2, apx FI AI W LBKc q' m m2 -> Forall aj_iv W -> hstat m -> hstat m2.
  Proof.
    intros W LBKc q' m m2 AP HW (TB & SHT & TS).
    assert (TST : am_static FI AI 0xaf320 0xafa20) by (apply AMS; unfold a0_static; split; [lia|]; right; left; lia).
    split; [| split].
    - destruct TB as [TB1 TB2]. split.
      + eapply (apx_bytes_at FI AI); [exact AP| exact TB1| | apply (aj_dj_img W _ _ HW)]; rewrite u64s_length, WSL.
        * apply (aclient_range_static FI AI _ q' _ _ 0xaf320 0xafa20 TST); lia.
        * lia.
      + eapply (apx_wr_at FI AI); [exact AP| exact TB2| | apply (aj_dj_img W _ _ HW)]; rewrite WSL.
        * apply (aclient_range_static FI AI _ q' _ _ 0xaf320 0xafa20 TST); lia.
        * lia.
    - apply (imgsh_apx W LBKc q' m m2 _ _ AP HW SHT); lia.
    - intros i Hi. destruct (TS i Hi) as (Sx & str & slack & E1 & E2 & E3 & E4 & E5 & E6 & E7).
      exists Sx, str, slack. repeat (split; [assumption|]). apply (imgsh_apx W LBKc q' m m2 _ _ AP HW E7); lia.
  Qed.

  #[using="q lo len st m0 HOK RF0 ws WSL bs cslack"] Lemma fpchain_apx : forall (W : list ivl) (LBKc : BL) q' rs m m2 top bottom a,
    apx FI AI W LBKc q' m m2 -> Forall aj_iv W -> q' <= bottom -> alloc_ceiling <= bottom ->
    fpchain m top bottom a rs -> fpchain m2 top bottom a rs.
  Proof.
    intros W LBKc q' rs. induction rs as [|r rest IH]; intros m m2 top bottom a AP HW HB HC0 CH; cbn [fpchain] in *; [exact CH|].
    destruct CH as (V & V16 & R1 & R2 & a' & R3 & CH'). unfold valid_frame, rd64 in *.
    assert (TR : forall X v, bottom <= X -> bytes_at asegs m X (le8 v) -> bytes_at asegs m2 X (le8 v)).
    { intros X v HX B. eapply (apx_bytes_at FI AI); [exact AP| exact B| apply aclient_range_above; lia|].
      rewrite length_le8. apply (aj_dj W X _ HW). left. lia. }
    split; [exact V|]. split; [exact V16|]. split; [split; [apply TR; [lia| exact (proj1 R1)]| exact (proj2 R1)]|]. split; [exact R2|].
    exists a'. split; [split; [apply TR; [lia| exact (proj1 R3)]| exact (proj2 R3)]|].
    eapply IH; [exact AP| exact HW| lia| lia| exact CH'].
  Qed.

  #[using="Type"] Lemma apxF_of_apx2 : forall W W' (LB LB' : BL) q0 q' (st0 st' : fsstate FI) mx m m',
    apx FI AI W LB' q' m m' -> RFAKE FI st' mx -> q' <= q0 -> (forall b, In b LB -> In b LB') ->
    (forall g, In g (fs_live FI st0) -> In g (fs_live FI st')) ->
    (forall a, fclient FI AI LB q0 st0 a -> outside W' a -> outside W a) ->
    apxF FI AI W' LB q0 st0 m m'.
  Proof.
    intros W W' LB LB' q0 q' st0 st' mx m m' H RF HS HL HF HO a Ha Hc Ho. apply H; [exact Ha| | exact (HO a Hc Ho)].
    eapply (fclient_aclient FI AI LB' q' st' mx a RF). eapply (fclient_weaken FI AI); eauto.
  Qed.

  #[using="AMS lo len HOK RF0 WSL bs cslack ZSTAT"] Lemma ainv_apx : forall (W : list ivl) (LBKc : BL) (stc : fsstate FI) q' m m2 s LB sx LBx ns hs ns2 hs2 X X2 meth pos,
    ainv s LB m ns hs X meth pos -> (2 * hsumA hs <= HB0 + X -> 2 * hsumA hs2 <= HB0 + X2) ->
    apx FI AI W LBKc q' m m2 -> Forall aj_iv W -> q + -272 <= q' <= q + -256 ->
    RFAKE FI stc m2 -> fs_live FI stc = fs_newff FI st 2 :: fs_live FI st ->
    (forall b, In b LBK -> In b LBKc) ->
    (forall a, fclient FI AI LBK q st a -> outside (phdr_WA P A cap) a -> outside W a) ->
    RHEAP_A FI AI sx LBx m2 -> In (kA, A, cap + 1) LBx -> bsub FI AI (hl_blocks FI AI ns2 hs2) LBx -> bsub FI AI LBK LBx ->
    NoDup (map blk_id (hl_blocks FI AI ns2 hs2 ++ (kA, A, cap + 1) :: LBK)) -> p_hlist FI AI m2 P ns2 hs2 X2 ->
    ainv sx LBx m2 ns2 hs2 X2 meth pos.
  Proof.
    intros W LBKc stc q' m m2 s LB sx LBx ns hs ns2 hs2 X X2 meth pos
      (HR & HA & SUB & KSUB & ND & PHL & PM0 & PM4 & MR & (pad & VER) & CT3 & PR & CT5 & HS & SHC & ZB & SHZ0 & APF & CH & HSM)
      HSUM AP HW QB RF2 LIVE1 KC OUTW HR2 HA2 SUB2 KSUB2 ND2 PHL2.
    destruct pgeom as [PF1 PF2]. pose proof HOK as HOK'. hokA HOK'.
    assert (TRP : forall X0 cs, P <= X0 -> X0 + Z.of_nat (cells_size cs) <= P + 504 ->
                  (X0 + Z.of_nat (cells_size cs) <= P + 288 \/ P + 400 <= X0) -> rw_cells asegs m X0 cs -> rw_cells asegs m2 X0 cs).
    { intros X0 cs H1 H2 H3 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; lia|].
      destruct H3 as [H3|H3]; [apply (aj_djP W _ _ HW); lia| apply (aj_dj W _ _ HW); do 4 right; left; lia]. }
    unfold ainv. repeat (split; [assumption|]).
    split; [apply TRP; [lia| simpl_sizes; lia| left; simpl_sizes; lia| exact PM0]|].
    split; [apply TRP; [lia| simpl_sizes; lia| left; simpl_sizes; lia| exact PM4]|]. split; [exact MR|].
    split; [exists pad; apply TRP; [lia| simpl_sizes; lia| left; simpl_sizes; lia| exact VER]|].
    split; [apply TRP; [lia| simpl_sizes; lia| right; lia| exact CT3]|]. split; [exact PR|].
    split; [apply TRP; [lia| simpl_sizes; lia| right; lia| exact CT5]|].
    split; [exact (hstat_apx W LBKc q' m m2 AP HW HS)|].
    split; [apply (imgsh_apx W LBKc q' m m2 _ _ AP HW SHC); lia|].
    split. { eapply (apx_bytes_at FI AI); [exact AP| exact ZB| | apply (aj_dj_img W _ _ HW); cbn [length]; lia].
             cbn [length]. apply (aclient_range_static FI AI _ q' _ _ _ _ ZSTAT); lia. }
    split; [apply (imgsh_apx W LBKc q' m m2 _ _ AP HW SHZ0); lia|].
    split.
    { eapply (apxF_trans FI AI); [exact APF|].
      apply (apxF_of_apx2 W (phdr_WA P A cap) LBK LBKc q q' st stc m2 m m2 AP RF2 ltac:(lia) KC); [| exact OUTW].
      intros g Hg. rewrite LIVE1. right. exact Hg. }
    split; [apply (fpchain_apx W LBKc q' ras m m2 _ q _ AP HW ltac:(lia) ltac:(lia) CH)| exact (HSUM HSM)].
  Qed.

  #[using="ASL RF0 WSL bs cslack"] Lemma ainv_munch : forall (W : list ivl) m m' s LB ns hs X meth pos pos',
    ainv s LB m ns hs X meth pos -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => alloc_ceiling <= fst iv
                      \/ (exists lo' hi', am_static FI AI lo' hi' /\ lo' <= fst iv /\ snd iv <= hi' /\ a0_wsafe (fst iv) (snd iv))
                      \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                      \/ (FSB FI <= fst iv /\ snd iv <= FSB FI + A0_FS_SIZE)
                      \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE)) W ->
    (forall b, In b (hl_blocks FI AI ns hs) -> disjoint_from W (blk_addr b) (blk_size b)) ->
    (forall a n, P <= a -> a + n <= P + 504 -> (a + n <= P + 448 \/ P + 452 <= a) -> disjoint_from W a n) ->
    Forall (fsw_iv FI) W -> Forall (fun iv : ivl => 0x609000 <= fst iv) W ->
    Forall (fun iv : ivl => snd iv <= q) W ->
    Forall (fun iv : ivl => (alloc_ceiling <= fst iv /\ snd iv <= q) \/ (forall a, fst iv <= a < snd iv -> ~ fclient FI AI LBK q st a)
                            \/ inside (phdr_WA P A cap) (fst iv) (snd iv - fst iv)) W ->
    rw_cells asegs m' (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos')] -> 0 <= pos' <= 4 ->
    ainv s LB m' ns hs X meth pos'.
  Proof.
    intros W m m' s LB ns hs X meth pos pos'
      (HR & HA & SUB & KSUB & ND & PHL & PM0 & PM4 & MR & (pad & VER) & CT3 & PR & CT5 & HS & SHC & ZB & SHZ0 & APF & CH & HSM)
      MU WM C1 C2 C3 C4a C4b C5 C6 CT3' PR'.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (PK : forall a cs, P <= a -> a + Z.of_nat (cells_size cs) <= P + 504 -> (a + Z.of_nat (cells_size cs) <= P + 448 \/ P + 452 <= a) ->
                 rw_cells asegs m a cs -> rw_cells asegs m' a cs).
    { intros a cs H1 H2 H3 C. eapply rw_cells_transport; [exact C| exact MU| exact WM| apply C3; assumption]. }
    unfold ainv.
    split; [exact (am_heap_frame FI AI s LB m m' W HR MU WM C1)|]. split; [exact HA|]. split; [exact SUB|]. split; [exact KSUB|]. split; [exact ND|].
    split. { apply (plist_keep m m' ns hs X PHL (bkeep_of_munch FI AI _ W m m' MU WM C2)). intros a cs H1 H2 C. apply (PK a cs); [lia| lia| left; lia| exact C]. }
    split; [apply (PK P _); [lia| simpl_sizes; lia| left; simpl_sizes; lia| exact PM0]|].
    split; [apply (PK (P + 4) _); [lia| simpl_sizes; lia| left; simpl_sizes; lia| exact PM4]|]. split; [exact MR|].
    split; [exists pad; apply (PK (P + 264) _); [lia| simpl_sizes; lia| left; simpl_sizes; lia| exact VER]|].
    split; [exact CT3'|]. split; [exact PR'|].
    split; [apply (PK (P + 452) _); [lia| simpl_sizes; lia| right; lia| exact CT5]|].
    split; [exact (hstat_step W m m' HS MU WM C4a C4b)|].
    split; [apply (shw_frame_fs FI W m m' _ _ SHC MU C4a); left; lia|].
    split; [eapply bytes_at_transport; [exact ZB| exact MU| apply (above_image_dj W _ _ C4b); cbn [length]; lia]|].
    split; [apply (shw_frame_fs FI W m m' _ _ SHZ0 MU C4a); left; lia|].
    split; [eapply (apxF_trans FI AI); [exact APF| exact (apxF_of_munch FI AI ASL s LB LBK m m0 q st (phdr_WA P A cap) W m m' HR KSUB RF0 MU WM C6)]|].
    split; [exact (fpchain_frame ras m m' _ q _ W CH MU WM C5)| exact HSM].
  Qed.

  #[using="ASL len HOK RF0 WSL bs cslack"] Lemma ainv_summary : forall mb m s LB ns hs X meth meth' pos,
    ainv s LB mb ns hs X meth pos -> munch W0 mb m -> wmono asegs mb m -> fkeep FI WHS st mb m ->
    rw_cells asegs m (P + 4) [C4 (wz meth')] -> 0 <= meth' <= 11 ->
    ainv s LB m ns hs X meth' pos.
  Proof.
    intros mb m s LB ns hs X meth meth' pos
      (HR & HA & SUB & KSUB & ND & PHL & PM0 & PM4 & MR & (pad & VER) & CT3 & PR & CT5 & HS & SHC & ZB & SHZ0 & APF & CH & HSM) MU WM FK PM4' MR'.
    destruct pgeom as [PF1 PF2]. pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (PK : forall a cs, P <= a -> a + Z.of_nat (cells_size cs) <= P + 504 -> disjoint_from WHS a (Z.of_nat (cells_size cs)) ->
                 rw_cells asegs mb a cs -> rw_cells asegs m a cs).
    { intros a cs H1 H2 DJ C. eapply (rw_cells_fkeep FI WHS st mb m); [exact C| exact FK| exact WM| left; apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact DJ]. }
    assert (DJW : forall a n, P + 8 <= a -> a + n <= P + 488 -> disjoint_from WHS a n).
    { intros a n H1 H2. unfold H_phdr_seg.hWHS. cbn [disjoint_from]. split; [lia|]. split; [lia| exact I]. }
    unfold ainv.
    split; [exact (heap_W0H s LB mb m HR HA MU WM)|]. split; [exact HA|]. split; [exact SUB|]. split; [exact KSUB|]. split; [exact ND|].
    split. { apply (plist_keep mb m ns hs X PHL (pblk_keep0 s LB mb m ns hs HR HA SUB ND MU WM)).
             intros a cs H1 H2 C. apply (PK a cs); [lia| lia| apply DJW; lia| exact C]. }
    split. { apply (PK P _); [lia| simpl_sizes; lia| | exact PM0]. unfold H_phdr_seg.hWHS. cbn [disjoint_from]. simpl_sizes. split; [lia|]. split; [lia| exact I]. }
    split; [exact PM4'|]. split; [exact MR'|].
    split; [exists pad; apply (PK (P + 264) _); [lia| simpl_sizes; lia| apply DJW; simpl_sizes; lia| exact VER]|].
    split; [apply (PK (P + 440) _); [lia| simpl_sizes; lia| apply DJW; simpl_sizes; lia| exact CT3]|].
    split; [exact PR|].
    split; [apply (PK (P + 452) _); [lia| simpl_sizes; lia| apply DJW; simpl_sizes; lia| exact CT5]|].
    split; [exact (hstat_stretch mb m HS MU WM)|].
    split; [apply (shw_frame_fs FI W0 mb m _ _ SHC MU W0_fsw); left; lia|].
    split; [eapply bytes_at_transport; [exact ZB| exact MU| apply (above_image_dj W0 _ _ W0_above); cbn [length]; lia]|].
    split; [apply (shw_frame_fs FI W0 mb m _ _ SHZ0 MU W0_fsw); left; lia|].
    split.
    { eapply (apxF_trans FI AI); [exact APF|].
      eapply (apxF_weaken FI AI ((A, A + (cap + 1)) :: WHS) (phdr_WA P A cap) LBK LBK q q st st mb m); [| | lia| intros b Hb; exact Hb| intros g Hg; exact Hg].
      - apply (apxF_of_munch_fkeep FI AI ASL s LB LBK mb m0 q lo st ((A, A + (cap + 1)) :: WHS) mb m HR KSUB RF0 CLO ltac:(lia) MU WM).
        eapply (fkeep_weaken FI WHS _ st st mb m FK); [| intros g Hg; exact Hg]. intros xo Ho. cbn [outside] in Ho. exact (proj2 Ho).
      - intros xo Ho. unfold phdr_WA in Ho. unfold H_phdr_seg.hWHS. cbn [outside] in *. destruct Ho as (O1 & O2 & O3 & O4 & O5 & _).
        split; [exact O5|]. split; [exact O1|]. split; [exact O4| exact I]. }
    split; [| exact HSM].
    eapply (fpchain_frame ras mb m _ q _ W0 CH MU WM). unfold H_phdr_seg.hW0, H_phdr_seg.hWHS.
    pose proof fs_shadow_band as (S1 & S2 & S3).
    repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil.
  Qed.

  Definition exrel (r pos pos' : Z) : Prop :=
    (r = PARSE_OK /\ pos' = POS_ENTITY_A) \/ (r = PARSE_SUCCESS /\ pos' = POS_COMPLETE_A) \/ (r <> PARSE_OK /\ pos' = pos).

  Definition fmid (m : mem) (sv tlz pos : Z) (ns3 : list (Z * Z * Z)) : machine_state -> Prop := fun ms' =>
    (exists (q' r cur' pos' : Z) (mb' me : mem) (tyw tb tl va vl : word) y1 y5 y6 y7 y11 y12 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
        ms' = epistH q' r y1 y5 y6 y7 y11 y12 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 me
        /\ hinvE q' cur' tyw tb tl va vl bs mb' me
        /\ ((mb' = m /\ pos' = pos)
            \/ (mb' = me /\ munch [(P + 448, P + 452)]%Z m me /\ wmono asegs m me /\ mem_inv asegs me
                /\ rw_cells asegs me (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos')]))
        /\ 0 <= r <= 5 /\ sv <= cur' <= len /\ exrel r pos pos' /\ 0 <= pos' <= 4)
    \/ (exists (q' id cur' o l : Z) (m' : mem) (tyw : word) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y28 y29 y30 y31,
        ms' = newstH q' id y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y28 y29 y30 y31 m'
        /\ hinv q' cur' tyw (wz (A + sv)) (wz tlz) (wz (A + o)) (wz l) bs m m'
        /\ sv + tlz + 1 <= o /\ 0 <= l /\ o + l <= len /\ sv + tlz + 1 <= cur' /\ o + l + 1 <= cur' /\ cur' <= len /\ (id = -1 \/ 0 <= id < 64))
    \/ (exists (q' it N id cur' o l : Z) (m' : mem) (tyw : word) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y27 y28 y29 y30 y31,
        ms' = existstH q' it y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y27 y28 y29 y30 y31 m'
        /\ hinv q' cur' tyw (wz (A + sv)) (wz tlz) (wz (A + o)) (wz l) bs m m'
        /\ In (N, it, id) ns3
        /\ sv + tlz + 1 <= o /\ 0 <= l /\ o + l <= len /\ sv + tlz + 1 <= cur' /\ o + l + 1 <= cur' /\ cur' <= len).

  #[using="ws WSL bs cslack"] Lemma exrel_end : forall ty meth pos, ty <> 0 -> 0 <= pos <= 4 -> exrel (end_r ty isreq meth) pos (end_pos ty isreq meth pos) /\ 0 <= end_pos ty isreq meth pos <= 4
                                                     /\ 0 <= end_r ty isreq meth <= 5.
  Proof.
    intros ty meth pos TY PR. unfold exrel, H_phdr_seg.end_r, H_phdr_seg.end_pos, PARSE_OK, PARSE_SUCCESS, POS_ENTITY_A, POS_COMPLETE_A.
    destruct (ty =? 2); [destruct (negb (isreq =? 0) && (meth =? 4))%bool|]; repeat split; try lia.
  Qed.

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 m0 HOK RF0 FCO WSL HID cslack VERR BSL"] Lemma frontH : forall (q' sv tlz cur ty meth pos first last size : Z) (va vl pad : word) (m : mem) (ns3 : list (Z * Z * Z)) (sl : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31,
    hinv q' cur (wz ty) (wz (A + sv)) (wz tlz) va vl bs m m -> FSENV FI m ->
    0 <= sv -> 1 <= tlz -> sv + tlz = cur -> cur <= len -> 0 <= ty <= 5 ->
    hstat m -> hlist m first last size 0 0 httpheader_free_entryA ns3 -> hnames m ns3 -> hslk m sl -> 0 <= size < 2^63 -> (size = 0 <-> ns3 = []) ->
    rw_cells asegs m (P + 4) [C4 (wz meth)] -> 0 <= meth <= 11 ->
    rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] ->
    rw_cells asegs m (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos)] -> 0 <= pos <= 4 ->
    evt asegs (fmid m sv tlz pos ns3) (headstH q' sv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' sv tlz cur ty meth pos first last size va vl pad m ns3 sl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
           INV FE SV0 TL1 TCL CLN TYR HS HLI HNM HSL SZR SZE PM4 MR VER CT3 PR.
    pose proof HOK as HOK'. hokA HOK'.
    eapply (headH q' sv cur ty (wz (A + sv)) (wz tlz) va vl bs m m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmid m sv tlz pos ns3) INV TYR ltac:(lia) FE).
    -
      intros TY0 y1 y11. destruct (exrel_end ty meth pos TY0 PR) as (EX & PR' & RR).
      eapply (endH q' sv ty cur isreq maj min meth err hack pos pad (wz (A + sv)) (wz tlz) va vl bs m m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmid m sv tlz pos ns3)
                INV TY0 TYR VER (proj1 VERR) PM4 MR CT3).
      intros mb' m' z1 z5 z6 z7 z11 z12 z15 z16 z17 z18 z19 z20 z21 z22 z24 z25 z26 z27 z28 z29 z30 z31 INVE LINK VER' PM4' CT3'.
      apply evt_done. left. exists q', (end_r ty isreq meth), cur, (end_pos ty isreq meth pos), mb', m', (wz ty), (wz (A + sv)), (wz tlz), va, vl.
      exists z1, z5, z6, z7, z11, z12, z15, z16, z17, z18, z19, z20, z21, z22, z24, z25, z26, z27, z28, z29, z30, z31.
      split; [reflexivity|]. split; [exact INVE|].
      split. { destruct LINK as [(-> & -> & TY2)|(-> & TY2 & MUc & WMc)].
               - left. split; [reflexivity|]. unfold H_phdr_seg.end_pos. replace (ty =? 2) with false by (symmetry; apply Z.eqb_neq; exact TY2). reflexivity.
               - right. split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. split; [| exact CT3'].
                 destruct INVE as (_ & _ & _ & _ & _ & _ & _ & MI' & _). exact MI'. }
      split; [exact RR|]. split; [lia|]. split; [exact EX| exact PR'].
    -
      intros m' r va' vl' z1 z5 z6 z7 z11 z12 z15 z16 z17 z18 z19 z20 z21 z22 z24 z25 z26 z27 z28 z29 z30 z31 INVE RR RN4.
      apply evt_done. left. exists q', r, sv, pos, m, m', (wz ty), (wz (A + sv)), (wz tlz), va', vl'.
      exists z1, z5, z6, z7, z11, z12, z15, z16, z17, z18, z19, z20, z21, z22, z24, z25, z26, z27, z28, z29, z30, z31.
      split; [reflexivity|]. split; [exact INVE|]. split; [left; split; reflexivity|]. split; [exact RR|]. split; [lia|].
      split; [right; right; split; [unfold PARSE_OK; exact RN4| reflexivity]| exact PR].
    -
      intros m1 cur' o l z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 INV1 FE1 O1 L0 OL C1 C2 C3.
      destruct (hnow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV1 HS HLI) as [HS1 _].
      eapply (nameH q' sv cur' sv tlz (wz ty) (wz (A + o)) (wz l) bs m m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmid m sv tlz pos ns3) INV1 HS1 FE1 SV0 TL1 ltac:(lia)).
      +
        intros m2 idx w1 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV2 HS2 IDX.
        destruct (hmeth_now _ _ _ _ _ _ _ _ _ _ _ _ meth INV2 PM4) as (meth2 & PM42 & _).
        eapply (knownA q' idx sv tlz cur' meth2 (wz ty) (wz (A + o)) (wz l) bs m m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmid m sv tlz pos ns3) INV2 HS2 IDX PM42).
        intros m3 id meth3 u10 u11 u12 u13 INV3 HS3 PM43 IDR _.
        eapply (knownB q' id sv tlz cur' first last size 0 0 httpheader_free_entryA ns3 (wz ty) (wz (A + o)) (wz l) bs m m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (fmid m sv tlz pos ns3) INV3 HS HLI IDR).
        * intros m4 v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 INV4.
          apply evt_done. right; left. exists q', id, cur', o, l, m4, (wz ty). do 18 eexists. split; [reflexivity|]. split; [exact INV4|].
          repeat (split; [lia|]). right. exact IDR.
        * intros m4 N it v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 INV4 HIN.
          apply evt_done. right; right. exists q', it, N, id, cur', o, l, m4, (wz ty). do 19 eexists. split; [reflexivity|]. split; [exact INV4|]. split; [exact HIN|].
          repeat (split; [lia|]). lia.
      +
        intros m2 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV2 HS2.
        assert (HbE : exists bE, nth_error bs (Z.to_nat cur) = Some bE).
        { destruct (nth_error bs (Z.to_nat cur)) as [bE|] eqn:E; [exists bE; reflexivity|]. apply nth_error_None in E. lia. }
        destruct HbE as [bE HbE].
        eapply (unkA q' cur' cur sv tlz (wz ty) (wz (A + o)) (wz l) bs bE m m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmid m sv tlz pos ns3) INV2 SV0 TL1 TCL CLN HbE).
        intros m3 u10 u11 u12 u13 INV3.
        assert (LT : (Z.to_nat cur < length bs)%nat) by lia.
        assert (Hz : nth_error (P0.H_presp_B.set_byte bs (Z.to_nat cur) zb) (Z.to_nat cur) = Some zb) by (apply P0.H_presp_B.set_byte_same; exact LT).
        eapply (unkH q' cur' cur sv tlz first last size 0 0 httpheader_free_entryA ns3 _ (wz ty) (wz (A + o)) (wz l) _ sl m m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (fmid m sv tlz pos ns3) INV3 HLI HNM HSL SZR SZE SV0 TL1 TCL CLN Hz).
        intros m4 s7v v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v26 v28 v29 v30 v31 INV4 S7 S7R.
        eapply (unkB q' cur' cur sv tlz s7v (wz ty) (wz (A + o)) (wz l) bs bE m m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmid m sv tlz pos ns3) INV4 SV0 TL1 TCL CLN HbE S7R).
        * intros S70 m5 t10 t11 t12 t13 INV5.
          apply evt_done. right; left. exists q', (-1), cur', o, l, m5, (wz ty). do 18 eexists. split; [reflexivity|]. split; [exact INV5|].
          repeat (split; [lia|]). left. reflexivity.
        * intros S7N m5 t10 t11 t12 t13 INV5. destruct S7 as [S7|(N' & id' & HIN)]; [contradiction|].
          apply evt_done. right; right. exists q', s7v, N', id', cur', o, l, m5, (wz ty). do 19 eexists. split; [reflexivity|]. split; [exact INV5|]. split; [exact HIN|].
          repeat (split; [lia|]). lia.
  Qed.

  #[using="ASL RF0 WSL bs cslack"] Lemma ainv_munchP : forall (W : list ivl) m m' s LB ns hs X meth pos,
    ainv s LB m ns hs X meth pos -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => alloc_ceiling <= fst iv
                      \/ (exists lo' hi', am_static FI AI lo' hi' /\ lo' <= fst iv /\ snd iv <= hi' /\ a0_wsafe (fst iv) (snd iv))
                      \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                      \/ (FSB FI <= fst iv /\ snd iv <= FSB FI + A0_FS_SIZE)
                      \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE)) W ->
    (forall b, In b (hl_blocks FI AI ns hs) -> disjoint_from W (blk_addr b) (blk_size b)) ->
    (forall a n, P <= a -> a + n <= P + 504 -> disjoint_from W a n) ->
    Forall (fsw_iv FI) W -> Forall (fun iv : ivl => 0x609000 <= fst iv) W ->
    Forall (fun iv : ivl => snd iv <= q) W ->
    Forall (fun iv : ivl => (alloc_ceiling <= fst iv /\ snd iv <= q) \/ (forall a, fst iv <= a < snd iv -> ~ fclient FI AI LBK q st a)
                            \/ inside (phdr_WA P A cap) (fst iv) (snd iv - fst iv)) W ->
    ainv s LB m' ns hs X meth pos.
  Proof.
    intros W m m' s LB ns hs X meth pos AINV MU WM C1 C2 C3 C4a C4b C5 C6.
    pose proof AINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT3 & PR & _).
    apply (ainv_munch W m m' s LB ns hs X meth pos pos AINV MU WM C1 C2); [| exact C4a| exact C4b| exact C5| exact C6| | exact PR].
    - intros a n H1 H2 _. exact (C3 a n H1 H2).
    - eapply rw_cells_transport; [exact CT3| exact MU| exact WM| apply C3; simpl_sizes; lia].
  Qed.

  Definition hfresh (s : PS) (LB : BL) (m : mem) (ns : list (BLK * Z)) (hs : list hdr) (kh : K) (H : Z) : Prop :=
    In (kh, H, 88) LB /\ ~ In (kh, H, 88) (hl_blocks FI AI ns hs) /\ (kh, H, 88) <> (kA, A, cap + 1) /\ ~ In (kh, H, 88) LBK.

  #[using="ASL len HOK RF0 WSL bs cslack"] Lemma ainv_hblk : forall (W : list ivl) (kh : K) H q' m m' s LB ns hs X meth pos,
    ainv s LB m ns hs X meth pos -> munch W m m' -> wmono asegs m m' -> Forall (hb_iv q' H) W ->
    q + -272 <= q' <= q + -256 -> hfresh s LB m ns hs kh H ->
    ainv s LB m' ns hs X meth pos.
  Proof.
    intros W kh H q' m m' s LB ns hs X meth pos AINV MU WM HW QB (HIN & HNP & HNT & HNK).
    pose proof AINV as (HR & HA & SUB & KSUB & ND & _).
    destruct pgeom as [PF1 PF2]. pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    destruct (blk_hapx s LB m (kh, H, 88) kA HR HIN HA HNT) as (H1 & H2 & H3 & _ & (HX1 & HX2 & HX3)). cbn [blk_addr blk_size fst snd] in H1, H2, H3, HX1, HX2, HX3.
    apply (ainv_munchP W m m' s LB ns hs X meth pos AINV MU WM).
    - eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *.
      + left. lia.
      + right; right; left. exists (kh, H, 88). cbn [blk_addr blk_size fst snd]. split; [exact HIN| lia].
      + do 3 right; left. lia.
    - intros b Hb. destruct (pblk_facts s LB m ns hs b HR HA SUB ND Hb) as [BIN BNE].
      assert (BNH : b <> (kh, H, 88)) by (intros E; apply HNP; rewrite <- E; exact Hb).
      destruct (am_block_range FI AI s LB m b HR BIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      pose proof (am_blocks_disjoint FI AI s LB m b (kh, H, 88) HR BIN HIN BNH) as DJB. cbn [blk_addr blk_size fst snd] in DJB.
      clear - HW R3 R4 R7 DJB CLO LO QB FLO FHI B1 B2.
      induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
      destruct HO as (LE & [O|[O|O]]); cbn [fst snd] in *; lia.
    - intros a n A1 A2. clear - HW A1 A2 PF1 PF2 PHI CLO HX1 PAF.
      induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
      destruct HO as (LE & [O|[O|O]]); cbn [fst snd] in *; lia.
    - eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *; left.
      + apply app_iv_stack. lia.
      + unfold app_iv, SH_HI. cbn [fst snd]. clear - O LE HX1 HX2 HX3 H1 H2 H3 ACR CLO. lia.
      + apply sub_app_iv_fsH; lia.
    - eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *; lia.
    - eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *; lia.
    - eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *.
      + left. lia.
      + right; left. intros a Ha Hc. apply (fclient_aclient FI AI LBK q st m0 a RF0) in Hc.
        apply (fresh_block_not_aclient FI AI ASL s LB LBK (kh, H, 88) q m a HR HIN); [| lia| cbn [blk_addr blk_size fst snd]; lia| exact Hc].
        intros b0 Hb0. split; [apply KSUB; exact Hb0| intros E; apply HNK; rewrite <- E; exact Hb0].
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s LB LBK m q st 2 m0 F SF FL HR KSUB ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl a).
        left. cbn [FB_of]. lia.
  Qed.

  Variables (N0 : Z) (s_0 : PS) (LB0 : BL) (cur0 X0 meth0 pos0 : Z).
  Hypothesis N0E : N0 = am_nsec FI AI s_0.
  Hypothesis MSGP : cap + 1 <= LMAX_A /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0).
  Hypothesis X0B : X0 + 2 * (len - cur0) <= 2^27 + 64.
  Hypothesis X00 : 0 <= X0.
  Hypothesis CUR0 : 0 <= cur0 <= len.
  Local Notation POST := (phdr_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s_0 LB0 LBK P cur0 A len cap kA bs X0 HB0 CB0 NB0 HS0
                                      meth0 isreq maj min err hack pos0 entp clen csz esp lo m0).

  Definition cntf (s : PS) (LB : BL) (hs : list hdr) (d : Z) : Prop :=
    5 * am_nsec FI AI s <= CB0 + phiH FI AI hs /\ Z.of_nat (length LB) <= NB0 + 4 * Z.of_nat (length hs)
    /\ hsumA hs <= HS0 + d /\ 0 <= cgG FI AI hs.
  Definition lfacts (s : PS) (LB : BL) (X sv d meth : Z) (hs : list hdr) : Prop :=
    cntf s LB hs d
    /\ hbud (len - sv) (cgG FI AI hs) s LB /\ hlines d N0 LB0 (am_nsec FI AI s) LB /\ 0 <= d <= sv - cur0 /\ cur0 <= sv <= len
    /\ X = X0 + 2 * (sv - cur0) /\ (meth = meth0 \/ meth = 11).

  #[using="ws WSL bs cslack"] Lemma p_hlist_mono : forall m ns hs X X', p_hlist FI AI m P ns hs X -> X <= X' -> p_hlist FI AI m P ns hs X'.
  Proof.
    intros m ns hs X X' (LHC & FLC & FFC & DL & HM & IT & VB & ZL & XP) LE. unfold p_hlist. repeat (split; [assumption|]).
    split; [intros h Hh; destruct (VB h Hh); split; lia|]. split; lia.
  Qed.

  #[using="ASL HOK RF0 WSL cslack VERR CTLR N0E MSGP"] Lemma exit_epi : forall s LB ns hs X meth pos' d (q' r cur' : Z) (mb' me : mem) (tyw tb tl va vl : word)
      y1 y5 y6 y7 y11 y12 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
    ainv s LB mb' ns hs X meth pos' -> hinvE q' cur' tyw tb tl va vl bs mb' me ->
    hlines d N0 LB0 (am_nsec FI AI s) LB -> 0 <= d <= cur' - cur0 -> cur0 <= cur' <= len -> X <= X0 + 2 * (cur' - cur0) ->
    (meth = meth0 \/ meth = 11) -> 0 <= r <= 5 -> exrel r pos0 pos' -> cntf s LB hs d ->
    AJ FI AI J POST (epistH q' r y1 y5 y6 y7 y11 y12 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 me) s LB.
  Proof.
    intros s LB ns hs X meth pos' d q' r cur' mb' me tyw tb tl va vl y1 y5 y6 y7 y11 y12 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31
           AINV INVE HLS DR CR XR MO RR EX CNT.
    destruct (ainv_stretch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AINV INVE) as (meth2 & AINV2 & MO2).
    pose proof (hinv_restart _ _ _ _ _ _ _ _ _ _ _ _ INVE) as INVE2.
    eapply (aj_evt FI AI J); [exact (epiH q' r cur' tyw tb tl va vl bs me me y1 y5 y6 y7 y11 y12 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 INVE2)|].
    intros ms' PO. unfold H_phdr_seg.hpostE in PO.
    destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MUE & WME & MU & WM & FK & MI' & LIVE' & RF' & ST' & AE'
                    & SC' & MBC' & TXT' & SHP' & SHA' & SHZ' & SHR').
    pose proof AINV2 as (_ & HA2 & _ & _ & _ & _ & _ & PM42 & MR2 & _).
    assert (PM4' : rw_cells asegs m' (P + 4) [C4 (wz meth2)]).
    { eapply rw_cells_transport; [exact PM42| exact MUE| exact WME| apply WE_dj_obj; left; simpl_sizes; lia]. }
    pose proof (ainv_summary me m' s LB ns hs X meth2 meth2 pos' AINV2 MU WM FK PM4' MR2)
      as (HR' & HA' & SUB' & KSUB' & ND' & PHL' & PM0' & _ & _ & (pad & VER') & CT3' & PR' & CT5' & _ & _ & _ & _ & APF' & _).
    apply (aj_ret FI AI J). unfold phdr_post_A.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st', r, cur', meth2, pos', d, ns, hs.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AE'|]. split; [exact RF'|]. split; [exact LIVE'|].
    split; [exact APF'|]. split; [exact HR'|]. split; [exact HA'|]. split; [exact SUB'|]. split; [exact KSUB'|]. split; [exact ND'|].
    split; [rewrite <- N0E; exact HLS|]. split; [exact DR|].
    split; [exact SC'|].
    split; [split; [exact MBC'|]; split; [split; [exact HA'| exact TXT']|]; destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENC & _); split; [exact LENC| exact MSGP]|].
    split. { split; [| exact MR2]. exact (proj2 (rw_cells_app asegs m' P [C4 (wz 1)] [C4 (wz meth2)]) (conj PM0' PM4')). }
    split; [split; [exists pad; exact VER'| exact VERR]|].
    split; [apply (p_hlist_mono m' ns hs X _ PHL' XR)|].
    split; [pose proof (ainv_hsum _ _ _ _ _ _ _ _ AINV2) as HSx; clear - HSx XR; lia|].
    split; [exact (proj1 (proj2 (proj2 CNT)))|].
    split; [exact (proj1 CNT)|]. split; [exact (proj1 (proj2 CNT))|].
    split. { destruct CTLR as (E1 & E2 & E3 & E4 & E5 & E6). split; [| repeat (split; [assumption|]); assumption].
             unfold p_ctl_cells.
             apply (proj2 (rw_cells_app asegs m' (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos')] [C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)])).
             split; [exact CT3'|]. replace (P + 440 + Z.of_nat (cells_size [C4 (wz err); C4 (wz hack); C4 (wz pos')])) with (P + 452) by (simpl_sizes; lia). exact CT5'. }
    split; [exact SHP'|]. split; [exact SHZ'|]. split; [exact SHR'|].
    split; [clear - MO MO2; lia|]. split; [exact CR|]. split; [exact RR| exact EX].
  Qed.

  #[using="ASL HOK RF0 WSL cslack VERR CTLR N0E MSGP CUR0"] Lemma exit_x : forall s LB ns hs X meth d (q' r sv cur : Z) (mb m : mem) (tyw tb tl va vl : word)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    ainv s LB mb ns hs X meth pos0 -> hinvE q' cur tyw tb tl va vl bs mb m ->
    hlines d N0 LB0 (am_nsec FI AI s) LB -> 0 <= d <= sv - cur0 -> cur0 <= sv <= len -> X <= X0 + 2 * (sv - cur0) ->
    (meth = meth0 \/ meth = 11) -> 0 <= r <= 5 -> r <> PARSE_OK -> cntf s LB hs d ->
    AJ FI AI J POST (xstH q' r sv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 m) s LB.
  Proof.
    intros s LB ns hs X meth d q' r sv cur mb m tyw tb tl va vl x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31
           AINV INVE HLS DR SR XR MO RR RN CNT.
    eapply (aj_evt FI AI J (fun ms' => exists m', ms' = epistH q' r x1 x5 x6 x7 x11 x12 x15 x16 x17 (wz sv) x19 x20 (wz (P + 488)) x22 x24 x25 x26 x27 x28 x29 x30 x31 m'
                                                   /\ hinvE q' sv tyw tb tl va vl bs mb m')).
    - eapply (exitH1 q' r sv cur tyw tb tl va vl bs mb m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVE ltac:(lia)).
      intros m' INVE'. apply evt_done. exists m'. split; [reflexivity| exact INVE'].
    - intros ms' (m' & -> & INVE').
      eapply (exit_epi s LB ns hs X meth pos0 d q' r sv mb m' tyw tb tl va vl); [exact AINV| exact INVE'| exact HLS| exact DR| exact SR| exact XR| exact MO| exact RR| | exact CNT].
      right; right. split; [exact RN| reflexivity].
  Qed.

  Definition khead (bound : Z) : Prop :=
    forall s LB m ns hs X meth d (q' sv tlz ty : Z) (va vl : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31,
      bound <= sv ->
      ainv s LB m ns hs X meth pos0 -> hinv q' (sv + tlz) (wz ty) (wz (A + sv)) (wz tlz) va vl bs m m ->
      1 <= tlz -> sv + tlz <= len -> 0 <= ty <= 5 -> lfacts s LB X sv d meth hs ->
      AJ FI AI J POST (headstH q' sv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m) s LB.

  #[using="IC ASL HOK RF0 WSL cslack VERR CTLR N0E MSGP CUR0"] Lemma next_tail : forall s LB ns hs X meth d (q' cur : Z) (mb m : mem) (ty tb tl va vl : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x26 x27 x28 x29 x30 x31,
    khead cur ->
    ainv s LB mb ns hs X meth pos0 -> hinv q' cur ty tb tl va vl bs mb m -> lfacts s LB X cur d meth hs ->
    AJ FI AI J POST (nextstH q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x26 x27 x28 x29 x30 x31 m) s LB.
  Proof.
    intros s LB ns hs X meth d q' cur mb m ty tb tl va vl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x26 x27 x28 x29 x30 x31
           KH AINV INV LF.
    pose proof LF as (CNT & HB & HLS & DR & SR & XE & MO).
    eapply (aj_evt FI AI J (fun ms' =>
       (exists m' tlz ty' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
           ms' = headstH q' cur y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x27 y28 y29 y30 y31 m'
           /\ hinv q' (cur + tlz) (wz ty') (wz (A + cur)) (wz tlz) va vl bs mb m' /\ 1 <= tlz /\ cur + tlz <= len /\ 0 <= ty' <= 5)
       \/ (exists m' r tb' tl' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
           ms' = xstH q' r cur y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 (wz (-8)) (wz 2147450880) (wz S) (wz (F + 160)) (wz L) (wz 4) x27 y28 y29 y30 y31 m'
           /\ hinvE q' cur ty tb' tl' va vl bs mb m' /\ (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE)))).
    - eapply (nextH q' cur ty tb tl va vl bs mb m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV).
      + intros m' tlz ty' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV' T1 T2 T3 _. apply evt_done. left.
        exists m', tlz, ty', y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31. repeat (split; [first [reflexivity| assumption]|]). exact T3.
      + intros m' r tb' tl' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INVE RR. apply evt_done. right.
        exists m', r, tb', tl', y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31. split; [reflexivity|]. split; [exact INVE| exact RR].
    - intros ms' [(m' & tlz & ty' & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & INV' & T1 & T2 & T3)
                 |(m' & r & tb' & tl' & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & INVE & RR)].
      + destruct (ainv_stretch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AINV INV') as (meth2 & AINV2 & MO2).
        eapply (KH s LB m' ns hs X meth2 d q' cur tlz ty' va vl); [lia| exact AINV2| exact (hinv_restart _ _ _ _ _ _ _ _ _ _ _ _ INV')| exact T1| exact T2| exact T3|].
        unfold lfacts. split; [exact CNT|]. repeat (split; [assumption|]). clear - MO MO2. lia.
      + eapply (exit_x s LB ns hs X meth d q' r cur cur mb m' ty tb' tl' va vl); [exact AINV| exact INVE| exact HLS| exact DR| exact SR| lia| exact MO| | | exact CNT];
          unfold PARSE_INCOMPLETE, PARSE_FAILURE, PARSE_OK in *; lia.
  Qed.

  #[using="ws WSL bs ras cslack TRACE"] Lemma ra_big : 4096 <= bv_unsigned ra.
  Proof.
    pose proof TRACE as T. unfold A0_TRACES in T. cbn [In] in T.
    repeat (destruct T as [T|T]; [try discriminate T; injection T as T1 T2; lia|]). destruct T.
  Qed.
  #[using="HOK ws WSL bs cslack QTOP TRACE"] Lemma chain_cons : forall t scr q' cur ty tb tl va vl bs' mb m,
    hinvGT t scr q' cur ty tb tl va vl bs' mb m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras ->
    fpchain m (am_stack_top FI AI) q' (bv_unsigned (wz q)) (bv_unsigned ra :: ras).
  Proof.
    intros t scr q' cur ty tb tl va vl bs' mb m INV CH.
    pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & QAL) & HR).
    destruct HR as (_ & _ & FRhi & _). pose proof HOK as HOK'. hokA HOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (proj1 (rw_cells_app asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FRhi) as [_ T2].
    replace (q + -104 + Z.of_nat (cells_size [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) with (q - 16) in T2 by (simpl_sizes; lia).
    pose proof (proj1 (rw_cells_app asegs m (q - 16) [C8 s0] [C8 ra]) T2) as [T3 T4].
    replace (q - 16 + Z.of_nat (cells_size [C8 s0])) with (q - 8) in T4 by (simpl_sizes; lia).
    pose proof (rw_cells_bytes_at asegs _ _ _ T3) as B3. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r in B3.
    pose proof (rw_cells_bytes_at asegs _ _ _ T4) as B4. cbn [cells_bytes cbytes] in B4. rewrite app_nil_r in B4.
    rewrite unsigned_lit by lia. cbn [fpchain]. unfold valid_frame, rd64.
    pose proof (bv_unsigned_in_range _ ra) as RR. pose proof (bv_unsigned_in_range _ s0) as SR. unfold bv_modulus in RR, SR.
    split; [split; [lia|]; split; [lia| clear - AL16; Z.div_mod_to_equations; lia]|]. split; [lia|].
    split; [split; [rewrite Z_to_bv_bv_unsigned; exact B4| exact RR]|]. split; [exact ra_big|].
    exists (bv_unsigned s0). split; [split; [rewrite Z_to_bv_bv_unsigned; exact B3| exact SR]| exact CH].
  Qed.

  #[using="q lo len m0 HOK RF0 ws WSL bs cslack"] Lemma hscr_apx : forall (W : list ivl) (LBKc : BL) q' m m2, apx FI AI W LBKc q' m m2 -> Forall aj_iv W -> alloc_ceiling <= q' ->
    hscr q' m -> hscr q' m2.
  Proof.
    intros W LBKc q' m m2 AP HW QC (j0 & j96 & j128 & SCR). exists j0, j96, j128.
    eapply (apx_rw_cells FI AI); [exact AP| exact SCR| apply aclient_range_above; lia| apply (aj_dj W _ _ HW); left; exact QC].
  Qed.

  #[using="q lo A len cap st m0 HOK RF0 ws WSL bs cslack"] Lemma plist_apx : forall (W : list ivl) (LBKc : BL) q' m m2 ns hs X,
    p_hlist FI AI m P ns hs X -> apx FI AI W LBKc q' m m2 -> bsub FI AI (hl_blocks FI AI ns hs) LBKc ->
    (forall b, In b (hl_blocks FI AI ns hs) -> disjoint_from W (blk_addr b) (blk_size b)) ->
    (forall a n, P + 288 <= a -> a + n <= P + 384 -> disjoint_from W a n) ->
    p_hlist FI AI m2 P ns hs X.
  Proof.
    intros W LBKc q' m m2 ns hs X PHL AP SUB DJB DJL. destruct pgeom as [PF1 PF2].
    apply (plist_keep m m2 ns hs X PHL (bkeep_of_apx FI AI _ W LBKc q' m m2 AP SUB DJB)).
    intros a cs H1 H2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; lia| apply DJL; lia].
  Qed.
  #[using="Type"] Lemma fresh_notin : forall sx (LBx : BL) mx (b : BLK), RHEAP_A FI AI sx (b :: LBx) mx -> ~ In b LBx.
  Proof.
    intros sx LBx mx b HR HI. pose proof (am_blocks_nodup FI AI sx _ mx HR) as ND. cbn [map] in ND. inversion ND as [|x l NI ND']. subst.
    apply NI. apply base.list_elem_of_In. apply in_map. exact HI.
  Qed.

  #[using="HOK ws WSL cslack"] Lemma text_src : forall t scr q' cur ty tb tl va vl mb m o n, hinvGT t scr q' cur ty tb tl va vl bs mb m -> 0 <= o -> 0 <= n -> o + n <= len ->
    bytes_at asegs m (A + o) (firstn (Z.to_nat n) (skipn (Z.to_nat o) bs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat o) bs))) = n.
  Proof.
    intros t scr q' cur ty tb tl va vl mb m o n INV O0 N0' ON. pose proof INV as (_ & _ & _ & _ & _ & _ & TXT & _).
    destruct (text_bytesH m bs TXT) as [B BL]. destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENC & _).
    pose proof (bytes_skipnH m A bs o B ltac:(lia)) as B2.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat o) bs)) in B2. apply bytes_at_app in B2. destruct B2 as [B3 _].
    split; [exact B3|]. rewrite length_firstn, length_skipn. lia.
  Qed.

  #[using="Type"] Lemma hdrs_blocks_snoc : forall (hs : list hdr) h, hdrs_blocks FI AI (hs ++ [h]) = hdrs_blocks FI AI hs ++ hblocks FI AI h.
  Proof. intros hs h. unfold hdrs_blocks. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.
  #[using="Type"] Lemma hdrs_mem_snoc : forall (hs : list hdr) m h, hdrs_mem FI AI m hs -> hdro_mem FI AI m h -> hdro_pure FI AI h -> hdrs_mem FI AI m (hs ++ [h]).
  Proof.
    induction hs as [|h0 hs IH]; intros m h HS HM HP; cbn [app HObjA.hdrs_mem] in *; [split; [exact HM| split; [exact HP| exact I]]|].
    destruct HS as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. exact (IH m h H3 HM HP).
  Qed.
  #[using="ws WSL bs cslack"] Lemma nul_of_firstn : forall (xs src : list byte) n, Z.of_nat (length src) = n -> firstn (Z.to_nat (n + 1)) xs = src ++ [Z_to_bv 8 0] ->
    nth_error xs (Z.to_nat n) = Some (Z_to_bv 8 0).
  Proof.
    intros xs src n LS E. assert (E2 : nth_error (firstn (Z.to_nat (n + 1)) xs) (Z.to_nat n) = nth_error xs (Z.to_nat n)).
    { rewrite nth_error_firstn. replace (Z.to_nat n <? Z.to_nat (n + 1))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    rewrite <- E2, E. rewrite nth_error_app2 by lia. replace (Z.to_nat n - length src)%nat with 0%nat by lia. reflexivity.
  Qed.

  #[using="len cap bs isreq maj min err hack entp clen csz esp cslack VERR CTLR CSL cur0 MSGP CUR0"] Lemma nd_insert3 : forall sx mx (LBx X Z : BL) (h n v : BLK),
    RHEAP_A FI AI sx (v :: n :: h :: LBx) mx -> bsub FI AI (X ++ Z) LBx -> NoDup (map blk_id (X ++ Z)) ->
    NoDup (map blk_id (X ++ [h; v; n] ++ Z)).
  Proof.
    intros sx mx LBx X Z h n v HR SUB ND.
    pose proof (am_blocks_nodup FI AI sx _ mx HR) as NDL. change (v :: n :: h :: LBx) with ([v; n; h] ++ LBx) in NDL.
    apply nd_app in NDL. destruct NDL as (N3 & IDJ3 & _).
    apply nd_app in ND. destruct ND as (NX & IXZ & NZ).
    assert (IY : idj [h; v; n] (X ++ Z)).
    { intros a b Ha Hb. apply (IDJ3 a b); [cbn [In] in *; tauto| apply SUB; exact Hb]. }
    apply idj_app_r in IY. destruct IY as [IYX IYZ].
    apply nd_app. split; [exact NX|]. split.
    - apply idj_app_r. split; [apply idj_sym; exact IYX| exact IXZ].
    - apply nd_app. split; [| split; [exact IYZ| exact NZ]].
      cbn [map] in N3 |- *. inversion N3 as [|x1 l1 A1 N2]; subst. inversion N2 as [|x2 l2 A2 N1]; subst.
      constructor; [| constructor; [| constructor; [| constructor]]].
      + intros Hx. apply elem_of_cons in Hx. destruct Hx as [Hx|Hx]; [apply A1; rewrite <- Hx; right; left|].
        apply elem_of_cons in Hx. destruct Hx as [Hx|Hx]; [apply A2; rewrite <- Hx; left| inversion Hx].
      + intros Hx. apply elem_of_cons in Hx. destruct Hx as [Hx|Hx]; [apply A1; rewrite Hx; left| inversion Hx].
      + intros Hx. inversion Hx.
  Qed.
  #[using="WSL cslack"] Lemma khead_mono : forall b b', khead b -> b <= b' -> khead b'.
  Proof. intros b b' KH LE. unfold khead in *. intros. eapply KH; try eassumption. lia. Qed.

  #[using="IC AC ASL AMS HOK RF0 WSL cslack VERR CTLR QTOP TRACE CSL ZSTAT BSL N0E MSGP X0B X00 CUR0"] Lemma new_tail : forall s LB ns hs X meth d (q' id sv tlz cur' o l : Z) (m m' : mem) (tyw : word)
      y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y28 y29 y30 y31,
    khead (sv + 1) ->
    ainv s LB m ns hs X meth pos0 -> hinv q' cur' tyw (wz (A + sv)) (wz tlz) (wz (A + o)) (wz l) bs m m' ->
    lfacts s LB X sv d meth hs ->
    0 <= sv -> 1 <= tlz -> sv + tlz + 1 <= o -> 0 <= l -> o + l <= len -> sv + tlz + 1 <= cur' -> o + l + 1 <= cur' -> cur' <= len ->
    (id = -1 \/ 0 <= id < 64) ->
    AJ FI AI J POST (newstH q' id y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y28 y29 y30 y31 m') s LB.
  Proof.
    intros s LB ns hs X meth d q' id sv tlz cur' o l m m' tyw y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y28 y29 y30 y31
           KH AINV INV LF SV0 TL1 O1 L0 OL C1 C2 C3 IDR.
    destruct (ainv_stretch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AINV INV) as (meth1 & AINV1 & MO1).
    pose proof (hinv_restart _ _ _ _ _ _ _ _ _ _ _ _ INV) as INV1. clear AINV INV.
    pose proof LF as (CNT & HB & HLS & DR & SR & XE & MO).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    pose proof INV1 as (ST1 & SCR1 & _ & _ & _ & _ & TXT1 & MI1 & AE1 & _ & _ & _ & _ & _ & _ & _ & (QB & QAL) & HR1).
    destruct (hrest_rf _ _ _ _ HR1) as (stc & RFc & LIVEc).
    pose proof AINV1 as (HRa & HAa & SUBa & KSUBa & NDa & PHLa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHa & _).

    eapply (aj_evt FI AI J (fun ms' => ms' = ajcallstH 0x58618 0x887a0 q' (wz 88) y11 y12 y5 y6 y7 y13 y14 y15 y16 y17 (wz 0) y21 y26 (wz id) y28 y29 y30 y31 m')).
    { eapply (newN1 q' id m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MI1). apply evt_done. reflexivity. }
    intros ms' ->. unfold H_phdr_seg.ajcallstH.
    eapply (aj_bind FI AI J).
    { eapply (ac_malloc FI AI J AC) with (st := stc) (n := 88) (lo := lo) (ras := bv_unsigned ra :: ras).
      - exact HRa.
      - exact AE1.
      - exact RFc.
      - exact ST1.
      - exact CLO.
      - unfold A0_RT_STACK. lia.
      - exact QAL.
      - lia.
      - exact MI1.
      - exact (chain_cons _ _ _ _ _ _ _ _ _ _ _ _ INV1 CHa).
      - rewrite unsigned_lit by lia. exact TRACE.
      - reflexivity.
      - unfold A0_MAXREQ. lia.
      - apply (hbud_now (len - sv) _ s LB 88 HB); [exact (proj2 (proj2 (proj2 CNT)))| lia| unfold A0_MAXREQ; lia]. }
    intros sa LBa msa PO. unfold malloc_post_A in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & kh & H & junk & -> & (MIm & STm & AEm & RFm & APm) & -> & HR1' & HCB & _ & WMm & NS1).
    assert (NS1' : am_nsec FI AI sa = am_nsec FI AI s) by (rewrite NS1; replace (a0_cls 88 =? 0) with false by reflexivity; lia).
    replace (ret_pc (Z_to_bv 64 559008)) with (Z_to_bv 64 559008) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (fresh_notin sa LB m1 (kh, H, 88) HR1') as HNI.
    assert (HINa : In (kh, H, 88) ((kh, H, 88) :: LB)) by (left; reflexivity).
    assert (HAb : In (kA, A, cap + 1) ((kh, H, 88) :: LB)) by (right; exact HAa).
    assert (HNT : (kh, H, 88) <> (kA, A, cap + 1)) by (intros E; apply HNI; rewrite E; exact HAa).
    destruct (blk_hapx sa _ m1 (kh, H, 88) kA HR1' HINa HAb HNT) as (HLO & HHI & HAL & _ & HAPH). cbn [blk_addr blk_size fst snd] in HLO, HHI, HAL, HAPH.
    pose proof (block_shw FI AI sa _ m1 (kh, H, 88) H 88 HR1' HINa ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWH.

    pose proof (apx_of_apres FI AI [] LB q' m' m1 APm) as APX1.
    assert (QC : alloc_ceiling <= q') by lia.
    pose proof (hinv_stepA 248 hscr [] LB ((kh, H, 88) :: LB) sa kA stc q' cur' tyw _ _ _ _ bs m' m' m1 INV1 APX1 (Forall_nil _) HR1' HAa HAb STm MIm AEm RFc RFm LIVEc
                  (hscr_apx [] LB q' m' m1 APX1 (Forall_nil _) QC)) as INV2.
    assert (AINV2 : ainv sa ((kh, H, 88) :: LB) m1 ns hs X meth1 pos0).
    { apply (ainv_apx [] LB stc q' m' m1 s LB sa _ ns hs ns hs X X meth1 pos0 AINV1 (fun HSx => HSx) APX1 (Forall_nil _) QB RFm LIVEc (fun b Hb => KSUBa b Hb)).
      - intros a _ _. exact I.
      - exact HR1'.
      - exact HAb.
      - intros b Hb. right. apply SUBa. exact Hb.
      - intros b Hb. right. apply KSUBa. exact Hb.
      - exact NDa.
      - apply (plist_apx [] LB q' m' m1 ns hs X PHLa APX1 SUBa); intros; exact I. }
    assert (HF : hfresh sa ((kh, H, 88) :: LB) m1 ns hs kh H).
    { split; [exact HINa|]. split; [intros E; apply HNI; apply SUBa; exact E|]. split; [exact HNT| intros E; apply HNI; apply KSUBa; exact E]. }
    clear AINV1 INV1 HRa PHLa CHa APm APX1 ST1 SCR1 TXT1 MI1 AE1 HR1 RFc.

    assert (LB63 : 0 <= l < 2^63) by (destruct MSGP as [MP _]; unfold LMAX_A in MP; lia).
    eapply (aj_evt FI AI J (fun ms' => exists m3 (va' : word) (l' : Z) (j24 : list byte) z5 z6 z7 z13 z14 z15 z16 z17 z28 z29 z30 z31,
        ms' = ajcallstH 0x8ca3c 0x887f4 q' (wz (H + 56)) (wz (A + sv)) (wz tlz) z5 z6 z7 z13 z14 z15 z16 z17 (wz (H + 56)) (wz H) (wz (H + 24)) (wz id) z28 z29 z30 z31 m3
        /\ hinv q' cur' tyw (wz (A + sv)) (wz tlz) va' (wz l') bs m3 m3 /\ munch (hWN q' H) m1 m3 /\ wmono asegs m1 m3
        /\ rw_cells asegs m3 H [CB 24 j24] /\ rw_cells asegs m3 (H + 24) (mbuf_cells 0 0 0) /\ rw_cells asegs m3 (H + 56) (mbuf_cells 0 0 0)
        /\ shw m3 H 88 /\ ((l <> 0 /\ va' = wz (A + o) /\ l' = l) \/ (l = 0 /\ va' = wz ZERO_ADDR_A /\ l' = 1)))).
    { eapply (newN2 q' H id cur' l tyw (wz (A + sv)) (wz tlz) (wz (A + o)) bs junk m1 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2 LB63 HCB SHWH HLO HHI HAL HAPH).
      intros m3 va' l' j24 z5 z6 z7 z13 z14 z15 z16 z17 z28 z29 z30 z31 I3 MU3 WM3 C24 CV CN SH3 ALT. apply evt_done.
      exists m3, va', l', j24, z5, z6, z7, z13, z14, z15, z16, z17, z28, z29, z30, z31. repeat (split; [first [reflexivity| assumption]|]). exact ALT. }
    intros ms' (m3 & va' & l' & j24 & z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & INV3 & MU3 & WM3 & C24 & CV & CN & SH3 & ALT).
    assert (AINV3 : ainv sa ((kh, H, 88) :: LB) m3 ns hs X meth1 pos0).
    { apply (ainv_hblk (hWN q' H) kh H q' m1 m3 sa _ ns hs X meth1 pos0 AINV2 MU3 WM3); [| exact QB| exact HF].
      unfold H_phdr_seg.hWN, H_phdr_seg.hb_iv.
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; left; clear; lia]|].
      apply Forall_cons; [cbn [fst snd]; split; [clear - QB LO; lia| left; clear; lia]|].
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; right; clear; lia]|]. apply Forall_nil. }
    assert (HR3 : RHEAP_A FI AI sa ((kh, H, 88) :: LB) m3) by (exact (proj1 AINV3)).
    clear AINV2 INV2 HR1' HCB SHWH junk MU3 WM3 STm MIm AEm RFm.

    assert (HFO : forall sx (LBx : BL) mx a, RHEAP_A FI AI sx LBx mx -> In (kh, H, 88) LBx -> bsub FI AI LBK LBx -> ~ In (kh, H, 88) LBK ->
                  fclient FI AI LBK q st a -> H <= a < H + 88 -> False).
    { intros sx LBx mx a HRx HINx KSx HNKx Hc Hr. apply (fclient_aclient FI AI LBK q st m0 a RF0) in Hc.
      apply (fresh_block_not_aclient FI AI ASL sx LBx LBK (kh, H, 88) q mx a HRx HINx); [| lia| cbn [blk_addr blk_size fst snd]; lia| exact Hc].
      intros b0 Hb0. split; [apply KSx; exact Hb0| intros E; apply HNKx; rewrite <- E; exact Hb0]. }
    destruct HF as (_ & HNP & _ & HNK).
    destruct HAPH as (HX1 & HX2 & HX3).
    assert (HDJ : forall sx (LBx : BL) mx b, RHEAP_A FI AI sx LBx mx -> In (kh, H, 88) LBx -> In b LBx -> b <> (kh, H, 88) ->
                  forall x n, H <= x -> x + n <= H + 88 -> disjoint_from [(x, x + n)]%Z (blk_addr b) (blk_size b)).
    { intros sx LBx mx b HRx HINx Hb NE x n X1 X2. pose proof (am_blocks_disjoint FI AI sx LBx mx b (kh, H, 88) HRx Hb HINx NE) as DJ.
      cbn [blk_addr blk_size fst snd] in DJ. cbn [disjoint_from]. split; [lia| exact I]. }

    pose proof INV3 as (ST3 & SCR3 & _ & _ & _ & _ & _ & MI3 & AE3 & _ & _ & _ & _ & _ & _ & _ & _ & HRS3).
    destruct (hrest_rf _ _ _ _ HRS3) as (st3 & RF3 & LIVE3).
    destruct (text_src _ _ _ _ _ _ _ _ _ _ _ sv tlz INV3 SV0 ltac:(lia) ltac:(lia)) as [BSRC LSRC].
    unfold H_phdr_seg.ajcallstH.
    eapply (aj_bind FI AI J).
    { eapply (membuffer_assign_spec_A IC FI AI J AC ASL AMS) with (st := st3) (ok := None) (MB := H + 56) (SRC := A + sv) (n := tlz) (A := 0) (len := 0) (cap := 0)
                                                                  (lo := lo) (src := firstn (Z.to_nat tlz) (skipn (Z.to_nat sv) bs)) (bs := []).
      - exact HR3.
      - exact RF3.
      - exact AE3.
      - exact ST3.
      - exact CLO.
      - unfold A0_RT_STACK. lia.
      - exact QAL.
      - clear - QB QTOP. lia.
      - exact MI3.
      - exact CN.
      - clear. lia.
      - destruct MSGP as [MP _]. unfold LMAX_A in MP. lia.
      - intros n' Hn'. apply (hbud_part (len - sv) _ 2 s LB sa _ n' HB (proj2 (proj2 (proj2 CNT)))); [rewrite NS1'; apply hp_new1; lia| lia|].
        destruct MSGP as [MP _]. unfold LMAX_A in MP. unfold A0_MAXREQ. lia.
      - cbn [mownA]. repeat split; reflexivity.
      - right; left. exists (kh, H, 88). cbn [lb_keepA blk_addr blk_size fst snd]. split; [exact HINa| clear; lia].
      - clear - HHI. lia.
      - clear - HAL. Z.div_mod_to_equations. lia.
      - eapply shw_sub; [exact SH3| lia| lia| lia].
      - exact BSRC.
      - exact LSRC.
      - clear - ALO SV0. lia.
      - left. right; left. exists (kA, A, cap + 1). cbn [lb_keepA blk_addr blk_size fst snd]. split; [exact HAb| clear - SV0 TL1 O1 OL L0 LENC; lia].
      - apply (block_shw FI AI sa _ m3 (kA, A, cap + 1) (A + sv) tlz HR3 HAb); cbn [blk_addr blk_size fst snd]; clear - SV0 TL1 O1 OL L0 LENC; lia.
      - pose proof alloc_ceiling_range as ACRx; unfold alloc_floor, alloc_ceiling_max in ACRx; clear - ACRx AHI SV0 TL1 O1 OL L0 LENC; lia.
      - clear - HX3 SV0 TL1 O1 OL L0 LENC. lia.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    intros sb LBb msb PO. unfold membuffer_assign_post_A in PO.
    destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m4 & NA & nc & okn & nbs
                    & -> & MI4 & ST4 & AE4 & RF4 & APX4 & HR4 & LBALT & NMC & NC1 & NC2 & NOWN & NNUL).
    cbn [lb_keepA] in APX4, LBALT.
    destruct LBALT as [(_ & _ & _ & -> & _)|(kn & -> & -> & NS4)]; [exfalso; lia|].

    assert (HW4 : forall x n, H <= x -> 0 <= n -> x + n <= H + 88 -> Forall aj_iv [(x, x + n)]%Z).
    { intros x n X1 X2 X3. constructor; [| constructor]. unfold H_phdr_seg.aj_iv. cbn [fst snd]. split; [clear - X2; lia|]. split; [clear - HLO X1; lia|]. split; [clear - HHI X3; lia|].
      left. split; [clear - HX1 X1 X3; lia|]. split; [clear - HX2 X1 X3; lia| clear - HX3 X1 X3; lia]. }
    pose proof (HW4 (H + 56) 32 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as HWn.
    pose proof (hinv_stepA 248 hscr _ _ _ sb kA st3 q' cur' tyw _ _ _ _ bs m3 m3 m4 INV3 APX4 HWn HR4 HAb (or_intror HAb) ST4 MI4 AE4 RF3 RF4 LIVE3
                  (hscr_apx _ _ q' m3 m4 APX4 HWn QC)) as INV4.
    assert (HINb : In (kh, H, 88) ((kn, NA, nc + 1) :: (kh, H, 88) :: LB)) by (right; left; reflexivity).
    assert (AINV4 : ainv sb ((kn, NA, nc + 1) :: (kh, H, 88) :: LB) m4 ns hs X meth1 pos0).
    { apply (ainv_apx _ _ st3 q' m3 m4 sa _ sb _ ns hs ns hs X X meth1 pos0 AINV3 (fun HSx => HSx) APX4 HWn QB RF4 LIVE3).
      - intros b Hb. right. apply KSUBa. exact Hb.
      - intros a Hc _. cbn [outside]. split; [| exact I]. intros Hr.
        apply (HFO sb _ m4 a HR4 HINb); [intros b Hb; right; right; apply KSUBa; exact Hb| exact HNK| exact Hc| clear - Hr; lia].
      - exact HR4.
      - right. exact HAb.
      - intros b Hb. right; right. apply SUBa. exact Hb.
      - intros b Hb. right; right. apply KSUBa. exact Hb.
      - exact NDa.
      - apply (plist_apx _ _ q' m3 m4 ns hs X (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 AINV3)))))) APX4).
        + intros b Hb. right. apply SUBa. exact Hb.
        + intros b Hb. apply (HDJ sa _ m3 b HR3 HINa); [right; apply SUBa; exact Hb| intros E; apply HNP; rewrite <- E; exact Hb| clear; lia| clear; lia].
        + intros a n A1 A2. destruct pgeom as [PF1 PF2]. cbn [disjoint_from]. split; [clear - A1 A2 PF1 PF2 HX1; lia| exact I]. }
    assert (TRH4 : forall xa cs, H <= xa -> xa + Z.of_nat (cells_size cs) <= H + 56 -> rw_cells asegs m3 xa cs -> rw_cells asegs m4 xa cs).
    { intros xa cs X1 X2 C. eapply (apx_rw_cells FI AI); [exact APX4| exact C| | cbn [disjoint_from]; split; [clear - X2; lia| exact I]].
      eapply (aclient_range_block FI AI _ q' xa _ (kh, H, 88) HINa); cbn [blk_addr blk_size fst snd]; clear - X1 X2; lia. }
    assert (C24b : rw_cells asegs m4 H [CB 24 j24]) by (apply TRH4; [clear; lia| simpl_sizes; clear; lia| exact C24]).
    assert (CVb : rw_cells asegs m4 (H + 24) (mbuf_cells 0 0 0)) by (apply TRH4; [clear; lia| unfold mbuf_cells; simpl_sizes; clear; lia| exact CV]).
    cbn [mownA] in NOWN. destruct NOWN as [NIN NBC]. specialize (NNUL ltac:(clear - TL1; lia)).
    assert (NSb : am_nsec FI AI sb = am_nsec FI AI s + nsec1 (nc + 1)) by (rewrite NS4, NS1'; reflexivity).
    clear AINV3 INV3 HR3 APX4 ST3 SCR3 MI3 AE3 HRS3 RF3 C24 CV CN SH3 TRH4 BSRC LSRC ST4 AE4 RF4 NS4.

    replace (ret_pc (Z_to_bv 64 559092)) with (Z_to_bv 64 559092) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (aj_evt FI AI J (fun ms' => ms' = ajcallstH 0x8ca3c 0x88808 q' (wz (H + 24)) va' (wz l') u0 u1 u2 e3 e4 e5 e6 e7 (wz (H + 56)) (wz H) (wz (H + 24)) (wz id) u3 u4 u5 u6 m4)).
    { eapply (newN3 q' H cur' tyw (wz (A + sv)) (wz tlz) va' (wz l') bs m4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV4). apply evt_done. reflexivity. }
    intros ms' ->.
    pose proof INV4 as (ST4 & _ & _ & _ & _ & _ & _ & _ & AE4 & _ & _ & _ & _ & _ & _ & _ & _ & HRS4).
    destruct (hrest_rf _ _ _ _ HRS4) as (st4 & RF4 & LIVE4).
    pose proof AINV4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZB4 & SHZ4 & _).
    assert (SRCV : exists SRC src, va' = wz SRC /\ bytes_at asegs m4 SRC src /\ Z.of_nat (length src) = l' /\ 0 < SRC
                   /\ msrcA FI AI ((kn, NA, nc + 1) :: (kh, H, 88) :: LB) q' st4 SRC l' /\ shw m4 SRC l' /\ SRC + l' < 2^47 /\ (SRC + l' <= H + 24 \/ H + 24 + 32 <= SRC)
                   /\ 1 <= l' /\ tlz + l' + 1 <= cur' - sv /\ l' <= len + 1).
    { destruct ALT as [(LN & -> & ->)|(-> & -> & ->)].
      - destruct (text_src _ _ _ _ _ _ _ _ _ _ _ o l INV4 ltac:(clear - O1 SV0 TL1; lia) L0 OL) as [B1 B2].
        exists (A + o), (firstn (Z.to_nat l) (skipn (Z.to_nat o) bs)). split; [reflexivity|]. split; [exact B1|]. split; [exact B2|]. split; [clear - ALO O1 SV0 TL1; lia|].
        split; [left; right; left; exists (kA, A, cap + 1); cbn [blk_addr blk_size fst snd]; split; [right; exact HAb| clear - O1 SV0 TL1 OL L0 LENC; lia]|].
        split; [apply (block_shw FI AI sb _ m4 (kA, A, cap + 1) (A + o) l HR4 (or_intror HAb)); cbn [blk_addr blk_size fst snd]; clear - O1 SV0 TL1 OL L0 LENC; lia|].
        split; [pose proof alloc_ceiling_range as ACRx; unfold alloc_floor, alloc_ceiling_max in ACRx; clear - ACRx AHI O1 SV0 TL1 OL L0 LENC; lia|].
        split; [clear - HX3 O1 SV0 TL1 OL L0 LENC; lia|]. clear - LN L0 O1 C2 OL SV0 TL1. lia.
      - exists ZERO_ADDR_A, [Z_to_bv 8 0]. split; [reflexivity|]. split; [exact ZB4|]. split; [reflexivity|]. split; [clear; lia|].
        split; [right; split; [clear; lia|]; split; [clear; lia|]; exists ZERO_ADDR_A, (ZERO_ADDR_A + 32); split; [exact ZSTAT| clear; lia]|].
        split; [exact SHZ4|]. split; [clear; lia|]. split; [clear - HLO; lia|]. clear - TL1 C1 SV0 LENC C3 O1 C2 L0. lia. }
    destruct SRCV as (SRC & src & -> & BSV & LSV & SRC0 & MSV & SHV & SRCHI & APV & LV1 & LVD & LVL).
    unfold H_phdr_seg.ajcallstH.
    eapply (aj_bind FI AI J).
    { eapply (membuffer_assign_spec_A IC FI AI J AC ASL AMS) with (st := st4) (ok := None) (MB := H + 24) (SRC := SRC) (n := l') (A := 0) (len := 0) (cap := 0)
                                                                  (lo := lo) (src := src) (bs := []).
      - exact HR4.
      - exact RF4.
      - exact AE4.
      - exact ST4.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO QB. lia.
      - exact QAL.
      - clear - QB QTOP. lia.
      - exact MI4.
      - exact CVb.
      - clear. lia.
      - destruct MSGP as [MP _]. unfold LMAX_A in MP. clear - LVL LENC MP. lia.
      - intros n' Hn'. apply (hbud_part (len - sv) _ (tlz + 1) s LB sb _ n' HB (proj2 (proj2 (proj2 CNT)))); [rewrite NSb; apply (hp_new2 _ _ _ tlz); [exact TL1| clear; lia| clear - NC1 NC2; lia]| clear - C1 C3; lia|].
        destruct MSGP as [MP _]. unfold LMAX_A in MP. unfold A0_MAXREQ. clear - Hn' LVL LENC MP. lia.
      - cbn [mownA]. repeat split; reflexivity.
      - right; left. exists (kh, H, 88). cbn [lb_keepA blk_addr blk_size fst snd]. split; [exact HINb| clear; lia].
      - clear - HHI. lia.
      - clear - HAL. Z.div_mod_to_equations. lia.
      - apply (block_shw FI AI sb _ m4 (kh, H, 88) (H + 24) 32 HR4 HINb); cbn [blk_addr blk_size fst snd]; clear; lia.
      - exact BSV.
      - exact LSV.
      - exact SRC0.
      - exact MSV.
      - exact SHV.
      - exact SRCHI.
      - exact APV.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    intros sc LBc msc PO. unfold membuffer_assign_post_A in PO.
    destruct PO as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m5 & VA & vc & okv & vbs
                    & -> & MI5 & ST5 & AE5 & RF5 & APX5 & HR5 & LBALT & VMC & VC1 & VC2 & VOWN & VNUL).
    cbn [lb_keepA] in APX5, LBALT.
    destruct LBALT as [(_ & _ & _ & -> & _)|(kv & -> & -> & NS5)]; [exfalso; clear - VC1 LV1; lia|].
    pose proof (HW4 (H + 24) 32 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as HWv.
    pose proof (hinv_stepA 248 hscr _ _ _ sc kA st4 q' cur' tyw _ _ _ _ bs m4 m4 m5 INV4 APX5 HWv HR5 (or_intror HAb) (or_intror (or_intror HAb)) ST5 MI5 AE5 RF4 RF5 LIVE4
                  (hscr_apx _ _ q' m4 m5 APX5 HWv QC)) as INV5.
    assert (HINc : In (kh, H, 88) ((kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB)) by (right; right; left; reflexivity).
    assert (AINV5 : ainv sc ((kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB) m5 ns hs X meth1 pos0).
    { apply (ainv_apx _ _ st4 q' m4 m5 sb _ sc _ ns hs ns hs X X meth1 pos0 AINV4 (fun HSx => HSx) APX5 HWv QB RF5 LIVE4).
      - intros b Hb. right; right. apply KSUBa. exact Hb.
      - intros a Hc _. cbn [outside]. split; [| exact I]. intros Hr.
        apply (HFO sc _ m5 a HR5 HINc); [intros b Hb; do 3 right; apply KSUBa; exact Hb| exact HNK| exact Hc| clear - Hr; lia].
      - exact HR5.
      - right; right. exact HAb.
      - intros b Hb. do 3 right. apply SUBa. exact Hb.
      - intros b Hb. do 3 right. apply KSUBa. exact Hb.
      - exact NDa.
      - apply (plist_apx _ _ q' m4 m5 ns hs X (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 AINV4)))))) APX5).
        + intros b Hb. right; right. apply SUBa. exact Hb.
        + intros b Hb. apply (HDJ sb _ m4 b HR4 HINb); [right; right; apply SUBa; exact Hb| intros E; apply HNP; rewrite <- E; exact Hb| clear; lia| clear; lia].
        + intros a n A1 A2. destruct pgeom as [PF1 PF2]. cbn [disjoint_from]. split; [clear - A1 A2 PF1 PF2 HX1; lia| exact I]. }
    assert (NNE : (kn, NA, nc + 1) <> (kh, H, 88)).
    { intros E. pose proof (fresh_notin sb _ m4 (kn, NA, nc + 1) HR4) as NI. apply NI. rewrite E. left. reflexivity. }
    assert (TRH5 : forall xa cs, H <= xa -> xa + Z.of_nat (cells_size cs) <= H + 88 -> (xa + Z.of_nat (cells_size cs) <= H + 24 \/ H + 56 <= xa) ->
                   rw_cells asegs m4 xa cs -> rw_cells asegs m5 xa cs).
    { intros xa cs X1 X2 X3 C. eapply (apx_rw_cells FI AI); [exact APX5| exact C| | cbn [disjoint_from]; split; [clear - X3; lia| exact I]].
      eapply (aclient_range_block FI AI _ q' xa _ (kh, H, 88) HINb); cbn [blk_addr blk_size fst snd]; clear - X1 X2; lia. }
    assert (C24c : rw_cells asegs m5 H [CB 24 j24]) by (apply TRH5; [clear; lia| simpl_sizes; clear; lia| left; simpl_sizes; clear; lia| exact C24b]).
    assert (NMCc : rw_cells asegs m5 (H + 56) (mbuf_cells NA tlz nc)) by (apply TRH5; [clear; lia| unfold mbuf_cells; simpl_sizes; clear; lia| right; clear; lia| exact NMC]).
    assert (NBCc : rw_cells asegs m5 NA [CB (Z.to_nat (nc + 1)) nbs]).
    { eapply (apx_rw_cells FI AI); [exact APX5| exact NBC| |].
      - eapply (aclient_range_block FI AI _ q' NA _ (kn, NA, nc + 1) NIN); cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; [clear; lia|]. rewrite Nat.add_0_r, Z2Nat.id by (clear - NC1 TL1; lia). clear. lia.
      - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - NC1 TL1; lia).
        apply (HDJ sb _ m4 (kn, NA, nc + 1) HR4 HINb NIN NNE); clear; lia. }
    cbn [mownA] in VOWN. destruct VOWN as [VIN VBC]. specialize (VNUL ltac:(clear - LV1; lia)).
    assert (NSc : am_nsec FI AI sc = am_nsec FI AI s + nsec1 (nc + 1) + nsec1 (vc + 1)) by (rewrite NS5, NSb; reflexivity).
    clear AINV4 INV4 HR4 APX5 ST4 AE4 HRS4 RF4 C24b CVb NMC NBC TRH5 BSV MSV SHV APV ZB4 SHZ4 ST5 AE5 RF5 NS5 MI4.

    replace (ret_pc (Z_to_bv 64 559112)) with (Z_to_bv 64 559112) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (SHW5 : shw m5 H 88) by (apply (block_shw FI AI sc _ m5 (kh, H, 88) H 88 HR5 HINc); cbn [blk_addr blk_size fst snd]; clear; lia).
    assert (IDR' : - 2^31 <= id < 2^31) by (clear - IDR; lia).
    eapply (aj_evt FI AI J (fun ms' => exists m6 (hpad yc : word),
        ms' = ajcallstH 0x8bbf4 0x88888 q' (wz L) (wz H) yc w0 w1 w2 g3 g4 g5 g6 g7 (wz (H + 56)) (wz H) (wz (H + 24)) (wz id) w3 w4 w5 w6 m6
        /\ hinv q' cur' tyw (wz (A + sv)) (wz tlz) (wz SRC) (wz l') bs m6 m6 /\ munch [(H, H + 24)]%Z m5 m6 /\ wmono asegs m5 m6
        /\ rw_cells asegs m6 H [C8 (wz NA); C8 (wz tlz); C4 (wz id); C4 hpad] /\ shw m6 H 88)).
    { eapply (newN4 q' H id NA tlz nc cur' tyw (wz (A + sv)) (wz tlz) (wz SRC) (wz l') bs j24 m5 m5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV5 C24c NMCc SHW5 HLO HHI HAL (conj HX1 (conj HX2 HX3)) IDR').
      intros m6 hpad yc I6 MU6 WM6 HC6 SH6. apply evt_done. exists m6, hpad, yc. repeat (split; [first [reflexivity| assumption]|]). exact SH6. }
    intros ms' (m6 & hpad & yc & -> & INV6 & MU6 & WM6 & HC6 & SH6).
    assert (AINV6 : ainv sc ((kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB) m6 ns hs X meth1 pos0).
    { apply (ainv_hblk [(H, H + 24)]%Z kh H q' m5 m6 sc _ ns hs X meth1 pos0 AINV5 MU6 WM6); [| exact QB|].
      - unfold H_phdr_seg.hb_iv. apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; left; clear; lia]| apply Forall_nil].
      - split; [exact HINc|]. split; [exact HNP|]. split; [exact HNT| exact HNK]. }
    assert (HR6 : RHEAP_A FI AI sc ((kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB) m6) by (exact (proj1 AINV6)).
    assert (VNE : (kv, VA, vc + 1) <> (kh, H, 88)).
    { intros E. pose proof (fresh_notin sc _ m5 (kv, VA, vc + 1) HR5) as NI. apply NI. rewrite E. right; left. reflexivity. }
    assert (TR6 : forall xa cs, disjoint_from [(H, H + 24)]%Z xa (Z.of_nat (cells_size cs)) -> rw_cells asegs m5 xa cs -> rw_cells asegs m6 xa cs).
    { intros xa cs DJ C. eapply rw_cells_transport; [exact C| exact MU6| exact WM6| exact DJ]. }
    assert (VMC6 : rw_cells asegs m6 (H + 24) (mbuf_cells VA l' vc)) by (apply TR6; [unfold mbuf_cells; cbn [disjoint_from]; simpl_sizes; split; [clear; lia| exact I]| exact VMC]).
    assert (NMC6 : rw_cells asegs m6 (H + 56) (mbuf_cells NA tlz nc)) by (apply TR6; [unfold mbuf_cells; cbn [disjoint_from]; simpl_sizes; split; [clear; lia| exact I]| exact NMCc]).
    assert (NBC6 : rw_cells asegs m6 NA [CB (Z.to_nat (nc + 1)) nbs]).
    { apply TR6; [| exact NBCc]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - NC1 TL1; lia).
      apply (HDJ sc _ m5 (kn, NA, nc + 1) HR5 HINc (or_intror NIN) NNE); clear; lia. }
    assert (VBC6 : rw_cells asegs m6 VA [CB (Z.to_nat (vc + 1)) vbs]).
    { apply TR6; [| exact VBC]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - VC1 LV1; lia).
      apply (HDJ sc _ m5 (kv, VA, vc + 1) HR5 HINc VIN VNE); clear; lia. }

    set (hnew := mkHdr FI AI H kh id NA tlz nc kn VA l' vc kv).
    assert (HPURE : hdro_pure FI AI hnew) by (unfold hdro_pure, hnew; cbn; clear - TL1 NC1 NC2 LV1 VC1 VC2 IDR'; lia).
    assert (HMEM6 : hdro_mem FI AI m6 hnew).
    { unfold hdro_mem, hnew. cbn [hA nA nlen hid vA vlen vcap ncap].
      split; [exists hpad; exact HC6|]. split; [exact VMC6|].
      split; [exists vbs; split; [exact VBC6| exact (nul_of_firstn vbs src l' LSV VNUL)]|]. split; [exact NMC6|].
      exists nbs. split; [exact NBC6|]. refine (nul_of_firstn nbs _ tlz _ NNUL). rewrite length_firstn, length_skipn. clear - BSL SV0 TL1 O1 OL L0 LENC. lia. }
    clear AINV5 INV5 HR5 C24c NMCc NBCc VMC VBC SHW5 MU6 WM6 TR6 MI5.

    pose proof INV6 as (ST6 & _ & _ & _ & _ & _ & _ & MI6 & AE6 & SHP6 & _ & _ & _ & _ & _ & _ & _ & HRS6).
    destruct (hrest_rf _ _ _ _ HRS6) as (st6 & RF6 & LIVE6).
    destruct (hlive_of st6 LIVE6) as (_ & _ & _ & LVP6 & _).
    pose proof AINV6 as (_ & _ & _ & _ & _ & PHL6 & _).
    pose proof PHL6 as (LHC6 & FLC6 & FFC6 & DL6 & HM6 & IT6 & VB6 & ZL6 & XP6).
    set (LBKc := hdrs_blocks FI AI hs ++ hblocks FI AI hnew ++ (kA, A, cap + 1) :: LBK).
    assert (SUBc : bsub FI AI LBKc ((kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB)).
    { intros b Hb. unfold LBKc in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [do 3 right; apply SUBa; unfold hl_blocks; apply in_or_app; right; exact Hb|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - unfold hnew in Hb. cbn [hblocks hk hA vk vA vcap nk nA ncap In] in Hb. destruct Hb as [<-|[<-|[<-|[]]]]; [exact HINc| left; reflexivity| right; left; reflexivity].
      - destruct Hb as [<-|Hb]; [do 3 right; exact HAa| do 3 right; apply KSUBa; exact Hb]. }
    assert (NDc : NoDup (map blk_id (map fst ns ++ LBKc))).
    { unfold LBKc. rewrite app_assoc.
      apply (nd_insert3 sc m6 LB (map fst ns ++ hdrs_blocks FI AI hs) ((kA, A, cap + 1) :: LBK) (kh, H, 88) (kn, NA, nc + 1) (kv, VA, vc + 1) HR6).
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply SUBa; exact Hb| destruct Hb as [<-|Hb]; [exact HAa| apply KSUBa; exact Hb]].
      - exact NDa. }
    unfold H_phdr_seg.ajcallstH.
    eapply (aj_bind FI AI J).
    { eapply (ListAddTail_spec_A FI AI J AC ASL AMS) with (st := st6) (LBK := LBKc) (ns := ns) (L := L) (IT := H) (fk := 0) (lo := lo).
      - exact HR6.
      - exact RF6.
      - exact AE6.
      - exact ST6.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO QB. lia.
      - exact QAL.
      - clear - QB QTOP. lia.
      - exact MI6.
      - replace (L + 24) with (P + 312) by (clear; lia). exact LHC6.
      - replace (L + 56) with (P + 344) by (clear; lia). exact FLC6.
      - replace (L + 24) with (P + 312) by (clear; lia). exact DL6.
      - right. apply (Contracts.lb_sub _ _ _ _ _ LVP6); clear; lia.
      - clear - PHI. lia.
      - clear - PAL. Z.div_mod_to_equations. lia.
      - eapply shw_sub; [exact SHP6| clear; lia| clear; lia| clear; lia].
      - clear - ZL6 XE X0B SR CUR0. lia.
      - clear - HLO HHI ACR. lia.
      - apply (hbud_part (len - sv) _ (cur' - sv) s LB sc _ 24 HB (proj2 (proj2 (proj2 CNT)))); [rewrite NSc; apply (hp_new3 _ _ _ tlz l'); [exact TL1| exact LV1| clear - C1; lia| clear - LVD; lia| clear - NC1 NC2; lia| clear - VC1 VC2; lia]| clear - C3; lia|].
        unfold A0_MAXREQ. clear. lia.
      - intros b Hb. do 3 right. apply SUBa. unfold hl_blocks. apply in_or_app. left. exact Hb.
      - exact SUBc.
      - exact NDc.
      - reflexivity.
      - reflexivity. }
    intros sd LBd msd PO. unfold ListAddTail_post_A in PO.
    destruct PO as (r0 & r1 & r2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & r3 & r4 & r5 & r6 & m7 & rr & ns' & -> & MI7 & ST7 & AE7 & RF7 & APX7 & HR7 & KS7 & NS7 & ND7
                    & LHC7 & FLC7 & DL7 & NSEC7 & (kd & RNZ & -> & ->)).

    destruct pgeom as [PF1 PF2].
    assert (HW7 : Forall aj_iv [(L, L + 56)]%Z).
    { constructor; [| constructor]. unfold H_phdr_seg.aj_iv. cbn [fst snd]. split; [clear; lia|]. split; [clear - PLO; lia|]. split; [clear - PHI; lia|]. right. clear. lia. }
    assert (TXc : In (kA, A, cap + 1) LBKc) by (unfold LBKc; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    pose proof (hinv_stepA 248 hscr _ LBKc _ sd kA st6 q' cur' tyw _ _ _ _ bs m6 m6 m7 INV6 APX7 HW7 HR7 TXc (or_intror (or_intror (or_intror (or_intror HAa)))) ST7 MI7 AE7 RF6 RF7 LIVE6
                  (hscr_apx _ _ q' m6 m7 APX7 HW7 QC)) as INV7.
    assert (BK7 : bkeep FI AI LBKc m6 m7).
    { apply (bkeep_of_apx FI AI LBKc _ LBKc q' m6 m7 APX7 (fun b Hb => Hb)). intros b Hb.
      destruct (am_block_range FI AI sc _ m6 b HR6 (SUBc b Hb)) as (_ & _ & R3 & _ & _ & _ & R7).
      cbn [disjoint_from]. split; [clear - R3 R7 PF1 PF2; lia| exact I]. }
    set (X' := X + 2 * (cur' - sv)).
    assert (AINV7 : ainv sd ((kd, rr, 24) :: (kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB) m7 (ns ++ [((kd, rr, 24), H)]) (hs ++ [hnew]) X' meth1 pos0).
    { apply (ainv_apx _ LBKc st6 q' m6 m7 sc _ sd _ ns hs (ns ++ [((kd, rr, 24), H)]) (hs ++ [hnew]) X X' meth1 pos0 AINV6
               ltac:(intros HSx; rewrite hsumA_app; unfold hnew, X'; cbn [hsumA fold_right vlen nlen] in HSx |- *; clear - HSx LVD TL1 C1; lia) APX7 HW7 QB RF7 LIVE6).
      - intros b Hb. unfold LBKc. apply in_or_app; right. apply in_or_app; right. right. exact Hb.
      - intros a _ Ho. unfold phdr_WA in Ho. cbn [outside] in *. destruct Ho as (_ & O2 & _). split; [| exact I]. clear - O2. lia.
      - exact HR7.
      - do 4 right. exact HAa.
      - unfold hl_blocks. rewrite hdrs_blocks_snoc. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (NS7 b Hb)|].
        apply KS7. unfold LBKc. rewrite app_assoc. apply in_or_app. left. exact Hb.
      - intros b Hb. do 4 right. apply KSUBa. exact Hb.
      - unfold hl_blocks. rewrite hdrs_blocks_snoc. rewrite <- !app_assoc. exact ND7.
      - unfold p_hlist.
        split; [replace (L + 24) with (P + 312) in LHC7 by (clear; lia); exact LHC7|].
        split; [replace (L + 56) with (P + 344) in FLC7 by (clear; lia); exact FLC7|].
        split. { eapply (apx_rw_cells FI AI); [exact APX7| exact FFC6| apply aclient_range_fs; simpl_sizes; clear - PF1 PF2; lia| cbn [disjoint_from]; simpl_sizes; split; [clear; lia| exact I]]. }
        split; [replace (L + 24) with (P + 312) in DL7 by (clear; lia); exact DL7|].
        split. { apply hdrs_mem_snoc; [| | exact HPURE].
                 - eapply (hdrs_mem_bkeep FI AI); [exact HM6| exact BK7|]. intros b Hb. unfold LBKc. apply in_or_app. left. exact Hb.
                 - eapply (hdro_mem_bkeep FI AI); [exact HMEM6| exact BK7| | unfold hnew; cbn; clear - VC1 LV1; lia| unfold hnew; cbn; clear - NC1 TL1; lia].
                   intros b Hb. unfold LBKc. apply in_or_app; right. apply in_or_app; left. exact Hb. }
        split; [rewrite !map_app, IT6; reflexivity|].
        split. { intros h Hh. apply in_app_or in Hh. destruct Hh as [Hh|[<-|[]]].
                 - destruct (VB6 h Hh) as [V1 V2]. split; [unfold X'; clear - V1 C1 SV0 TL1; lia| exact V2].
                 - unfold hnew. cbn [vlen nlen]. destruct MSGP as [MP _]. split; [unfold X'; clear - LVD C1 TL1 XP6; lia| clear - MP C1 C3 LENC SV0 TL1; lia]. }
        split; [unfold zlength in *; rewrite length_app; cbn [length]; unfold X'; clear - ZL6 C1 SV0 TL1; lia| unfold X'; clear - XP6 C1 SV0 TL1; lia]. }

    replace (ret_pc (Z_to_bv 64 559240)) with (Z_to_bv 64 559240) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (RRR : 0 < rr < 2^64).
    { destruct (am_block_range FI AI sd _ m7 (kd, rr, 24) HR7 (or_introl eq_refl)) as (R1 & _ & _ & R4 & _). cbn [blk_addr blk_size fst snd] in R1, R4. clear - R1 R4 ACR. lia. }
    eapply (aj_evt FI AI J (fun ms' => ms' = nextstH q' (wz 0x88888) r0 r1 r2 (wz rr) h1 h2 h3 h4 h5 h6 h7 (wz (H + 56)) (wz H) (wz (H + 24)) (wz id) r3 r4 r5 r6 m7)).
    { eapply (newN5 q' rr m7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MI7 RRR). apply evt_done. reflexivity. }
    intros ms' ->.
    assert (HLN : hline (cur' - sv) (am_nsec FI AI s) LB (am_nsec FI AI sd) ((kd, rr, 24) :: (kv, VA, vc + 1) :: (kn, NA, nc + 1) :: (kh, H, 88) :: LB)).
    { rewrite NSEC7, NSc. apply (hl_new _ _ _ tlz l'); [exact TL1| exact LV1| clear - C1; lia| clear - LVD; lia| clear - NC1 NC2; lia| clear - VC1 VC2; lia]. }
    eapply (next_tail sd _ _ _ X' meth1 (d + (cur' - sv)) q' cur' m7 m7 tyw _ _ _ _); [exact (khead_mono (sv + 1) cur' KH ltac:(clear - C1 TL1; lia))| exact AINV7| exact INV7|].
    unfold lfacts.
    pose proof (w0_new vc ltac:(clear - VC1 LV1; lia)) as W1. pose proof (w0_new nc ltac:(clear - NC1 TL1; lia)) as W2.
    split. { destruct CNT as (CNT & CNL & CN3 & CN4). split; [| split; [rewrite length_app; cbn [length]; clear - CNL; lia| split]].
             - rewrite NSEC7, NSc, (phiH_app FI AI). unfold hnew. cbn [phiH fold_right vcap ncap]. clear - CNT W1 W2. lia.
             - rewrite hsumA_app. unfold hnew. cbn [hsumA fold_right vlen nlen]. clear - CN3 LVD. lia.
             - pose proof AINV7 as (_ & _ & _ & _ & _ & PHL7 & _). exact (p_hlist_cgG _ _ _ _ _ PHL7). }
    split; [replace (len - cur') with (len - sv - (cur' - sv)) by (clear; lia); eapply hbud_line; [exact HB| exact HLN|]; apply (cgG_step FI AI);
              [rewrite NSEC7, NSc, (phiH_app FI AI); unfold hnew; cbn [phiH fold_right vcap ncap]; clear - W1 W2; lia
              | rewrite (hlenA_app FI AI); unfold hnew; cbn [hlenA fold_right vlen nlen]; clear - LVD; lia]|].
    split; [exact (hlines_snoc d N0 LB0 _ LB HLS (cur' - sv) _ _ HLN)|].
    split; [clear - DR C1 SV0 TL1; lia|]. split; [clear - SR C1 C3 TL1; lia|]. split; [unfold X'; clear - XE; lia|]. clear - MO MO1. lia.
  Qed.

  #[using="len cap bs isreq maj min err hack entp clen csz esp cslack VERR CTLR CSL cur0 MSGP CUR0"] Lemma hdrs_mem_app : forall (l1 l2 : list hdr) m, hdrs_mem FI AI m (l1 ++ l2) <-> hdrs_mem FI AI m l1 /\ hdrs_mem FI AI m l2.
  Proof.
    induction l1 as [|h0 l1 IH]; intros l2 m; cbn [app HObjA.hdrs_mem]; [tauto|]. rewrite (IH l2 m). tauto.
  Qed.
  #[using="Type"] Lemma hdrs_blocks_app : forall (l1 l2 : list hdr), hdrs_blocks FI AI (l1 ++ l2) = hdrs_blocks FI AI l1 ++ hdrs_blocks FI AI l2.
  Proof. intros l1 l2. unfold hdrs_blocks. rewrite map_app, concat_app. reflexivity. Qed.
  #[using="Type"] Lemma hl_split : forall (ns : list (BLK * Z)) (hs1 hs2 : list hdr) (h : hdr) (T : BL),
    hl_blocks FI AI ns (hs1 ++ h :: hs2) ++ T
    = (map fst ns ++ hdrs_blocks FI AI hs1 ++ [(hk FI AI h, hA FI AI h, 88)])
      ++ (vk FI AI h, vA FI AI h, vcap FI AI h + 1) :: ((nk FI AI h, nA FI AI h, ncap FI AI h + 1) :: hdrs_blocks FI AI hs2 ++ T).
  Proof.
    intros ns hs1 hs2 h T. unfold hl_blocks. rewrite hdrs_blocks_app, (hdrs_blocks_cons FI AI h hs2). unfold hblocks.
    rewrite <- !app_assoc. cbn [app]. reflexivity.
  Qed.
  #[using="Type"] Lemma nd_replace1 : forall (X Z : BL) (v v' : BLK), NoDup (map blk_id (X ++ v :: Z)) -> (forall b, In b (X ++ Z) -> blk_id b <> blk_id v') ->
    NoDup (map blk_id (X ++ v' :: Z)).
  Proof.
    intros X Z v v' ND NE. apply nd_app in ND. destruct ND as (NX & IXZ & NZ). apply nd_cons in NZ. destruct NZ as [IVZ NZ'].
    apply nd_app. split; [exact NX|]. split.
    - intros a b Ha Hb. destruct Hb as [<-|Hb]; [apply NE; apply in_or_app; left; exact Ha| apply (IXZ a b Ha); right; exact Hb].
    - apply nd_cons. split; [| exact NZ']. intros a b Ha Hb. destruct Ha as [<-|[]]. intros E. apply (NE b); [apply in_or_app; right; exact Hb| symmetry; exact E].
  Qed.
  #[using="Type"] Lemma fresh_id : forall sx (LBx : BL) mx (b : BLK), RHEAP_A FI AI sx (b :: LBx) mx -> forall b0, In b0 LBx -> blk_id b0 <> blk_id b.
  Proof.
    intros sx LBx mx b HR b0 Hb0 E. pose proof (am_blocks_nodup FI AI sx _ mx HR) as ND. cbn [map] in ND. inversion ND as [|x l NI ND']. subst.
    apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact Hb0.
  Qed.
  #[using="ASL lo P A len cap m0 HOK RF0 ws WSL bs cslack"] Lemma blk_no_fclient : forall sx (LBx : BL) mx (b : BLK) a, RHEAP_A FI AI sx LBx mx -> In b LBx -> bsub FI AI LBK LBx -> ~ In b LBK ->
    fclient FI AI LBK q st a -> blk_addr b <= a < blk_addr b + blk_size b -> False.
  Proof.
    intros sx LBx mx b a HRx HINx KSx HNKx Hc Hr. destruct HOK as (CLO & LO & _). apply (fclient_aclient FI AI LBK q st m0 a RF0) in Hc.
    apply (fresh_block_not_aclient FI AI ASL sx LBx LBK b q mx a HRx HINx); [| lia| exact Hr| exact Hc].
    intros b0 Hb0. split; [apply KSx; exact Hb0| intros E; apply HNKx; rewrite <- E; exact Hb0].
  Qed.
  #[using="Type"] Lemma nd_mid_neq : forall (X Z : BL) (v : BLK), NoDup (map blk_id (X ++ v :: Z)) -> forall b, In b (X ++ Z) -> blk_id b <> blk_id v.
  Proof.
    intros X Z v ND b Hb. apply nd_app in ND. destruct ND as (_ & IXZ & NZ). apply nd_cons in NZ. destruct NZ as [IVZ _].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply (IXZ b v Hb); left; reflexivity|].
    intros E. apply (IVZ v b); [left; reflexivity| exact Hb| symmetry; exact E].
  Qed.

  #[using="ASL AMS HOK RF0 WSL cslack VERR CTLR CSL ZSTAT cur0 MSGP CUR0"] Lemma ext_update : forall s LB sx LBx m m2 ns hs1 hs2 (h : hdr) X X' meth (stc : fsstate FI) q' cur ty tb tl va vl n A' cap' (k' : K) (vbs' : list byte),
    ainv s LB m ns (hs1 ++ h :: hs2) X meth pos0 -> hinv q' cur ty tb tl va vl bs m m ->
    RFAKE FI stc m -> RFAKE FI stc m2 -> fs_live FI stc = fs_newff FI st 2 :: fs_live FI st ->
    mem_inv asegs m2 -> stk asegs m2 lo q' -> asan_env asegs m2 ->
    apx FI AI [(hA FI AI h + 24, hA FI AI h + 24 + 32)]%Z (lb_remove (am_K_eqb FI AI) (vk FI AI h) LB) q' m m2 ->
    RHEAP_A FI AI sx LBx m2 ->
    In (k', A', cap' + 1) LBx ->
    (forall b, In b LB -> blk_id b <> vk FI AI h -> In b LBx) ->
    (forall b, In b LB -> blk_id b <> vk FI AI h -> blk_id b <> k') ->
    rw_cells asegs m2 (hA FI AI h + 24) (mbuf_cells A' (vlen FI AI h + n) cap') ->
    rw_cells asegs m2 A' [CB (Z.to_nat (cap' + 1)) vbs'] -> nth_error vbs' (Z.to_nat (vlen FI AI h + n)) = Some (Z_to_bv 8 0) ->
    1 <= n -> vlen FI AI h + n <= cap' -> cap' <= vlen FI AI h + n + 5 -> vlen FI AI h + n <= X' -> X <= X' ->
    2 * hsumA (hs1 ++ mkHdr FI AI (hA FI AI h) (hk FI AI h) (hid FI AI h) (nA FI AI h) (nlen FI AI h) (ncap FI AI h) (nk FI AI h) A' (vlen FI AI h + n) cap' k' :: hs2) <= HB0 + X' ->
    ainv sx LBx m2 ns (hs1 ++ mkHdr FI AI (hA FI AI h) (hk FI AI h) (hid FI AI h) (nA FI AI h) (nlen FI AI h) (ncap FI AI h) (nk FI AI h) A' (vlen FI AI h + n) cap' k' :: hs2) X' meth pos0
    /\ hinv q' cur ty tb tl va vl bs m2 m2.
  Proof.
    intros s LB sx LBx m m2 ns hs1 hs2 h X X' meth stc q' cur ty tb tl va vl n A' cap' k' vbs'
           AINV INV RF RF2 LIVE MI2 ST2 AE2 AP HRx U1 U2 U3 VMC' VBC' VNUL' N1 VC1 VC2 VX XX HSX.
    pose proof AINV as (HR & HA & SUB & KSUB & ND & PHL & _).
    destruct PHL as (LHC & FLC & FFC & DL & HM & IT & VB & ZL & XP).
    apply hdrs_mem_app in HM. destruct HM as [HM1 HM2']. cbn [HObjA.hdrs_mem] in HM2'. destruct HM2' as (HMh & HPh & HM2).
    destruct HMh as ((hpad & HCc) & VMC & _ & NMC & (nbs & NBC & NNUL)). pose proof HPh as (P1 & P2 & P3 & P4 & P5).
    pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & QAL) & _).
    destruct pgeom as [PF1 PF2]. pose proof HOK as HOK'. hokA HOK'.
    set (M := map fst ns ++ hdrs_blocks FI AI hs1) in *.
    set (hb := (hk FI AI h, hA FI AI h, 88)). set (vb := (vk FI AI h, vA FI AI h, vcap FI AI h + 1)). set (nb := (nk FI AI h, nA FI AI h, ncap FI AI h + 1)).
    set (Zl := nb :: hdrs_blocks FI AI hs2 ++ (kA, A, cap + 1) :: LBK).
    assert (SPL : hl_blocks FI AI ns (hs1 ++ h :: hs2) ++ (kA, A, cap + 1) :: LBK = (M ++ [hb]) ++ vb :: Zl).
    { rewrite hl_split. unfold M, hb, vb, nb, Zl. rewrite <- !app_assoc. reflexivity. }
    assert (INL : forall b, In b ((M ++ [hb]) ++ vb :: Zl) -> In b LB).
    { intros b Hb. rewrite <- SPL in Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|Hb]]; [apply SUB; exact Hb| exact HA| apply KSUB; exact Hb]. }
    rewrite SPL in ND.
    pose proof (nd_mid_neq (M ++ [hb]) Zl vb ND) as NEV. cbn [blk_id fst] in NEV.
    assert (ND2 : NoDup (map blk_id (M ++ hb :: (vb :: Zl)))) by (rewrite <- app_assoc in ND; exact ND).
    pose proof (nd_mid_neq M (vb :: Zl) hb ND2) as NEH.

    assert (HBIN : In hb LB) by (apply INL; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HBNV : blk_id hb <> vk FI AI h) by (apply NEV; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (TXIN : In (kA, A, cap + 1) ((M ++ [hb]) ++ Zl)) by (apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
    assert (HBNT : hb <> (kA, A, cap + 1)).
    { intros E. apply (NEH (kA, A, cap + 1)); [apply in_or_app; right; right; right; apply in_or_app; right; left; reflexivity| rewrite <- E; reflexivity]. }
    destruct (blk_hapx s LB m hb kA HR HBIN HA HBNT) as (HLO & HHI & HAL & _ & (HX1 & HX2 & HX3)). cbn [blk_addr blk_size fst snd hb] in HLO, HHI, HAL, HX1, HX2, HX3.
    assert (HW : Forall aj_iv [(hA FI AI h + 24, hA FI AI h + 24 + 32)]%Z).
    { constructor; [| constructor]. unfold H_phdr_seg.aj_iv. cbn [fst snd]. split; [clear; lia|]. split; [clear - HLO; lia|]. split; [clear - HHI; lia|].
      left. split; [clear - HX1; lia|]. split; [clear - HX2; lia| clear - HX3; lia]. }
    assert (KIN : In (kA, A, cap + 1) (lb_remove (am_K_eqb FI AI) (vk FI AI h) LB)) by (apply (lb_remove_In FI AI); [exact HA| exact (NEV _ TXIN)]).
    assert (TXx : In (kA, A, cap + 1) LBx) by (apply U2; [exact HA| exact (NEV _ TXIN)]).
    assert (QC : alloc_ceiling <= q') by (clear - QB LO CLO; lia).
    pose proof (hinv_stepA 248 hscr _ _ LBx sx kA stc q' cur ty tb tl va vl bs m m m2 INV AP HW HRx KIN TXx ST2 MI2 AE2 RF RF2 LIVE (hscr_apx _ _ q' m m2 AP HW QC)) as INV2.
    split; [| exact INV2].
    set (h1 := mkHdr FI AI (hA FI AI h) (hk FI AI h) (hid FI AI h) (nA FI AI h) (nlen FI AI h) (ncap FI AI h) (nk FI AI h) A' (vlen FI AI h + n) cap' k').
    set (vb' := (k', A', cap' + 1)).
    assert (SPL1 : hl_blocks FI AI ns (hs1 ++ h1 :: hs2) ++ (kA, A, cap + 1) :: LBK = (M ++ [hb]) ++ vb' :: Zl).
    { rewrite hl_split. unfold h1. cbn [hk hA vk vA vcap nk nA ncap]. unfold M, hb, vb', nb, Zl. rewrite <- !app_assoc. reflexivity. }
    assert (INL' : forall b, In b ((M ++ [hb]) ++ Zl) -> In b ((M ++ [hb]) ++ vb :: Zl)).
    { intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
    assert (OLDx : forall b, In b ((M ++ [hb]) ++ Zl) -> In b LBx /\ blk_id b <> k').
    { intros b Hb. pose proof (INL b (INL' b Hb)) as HbL. split; [apply U2; [exact HbL| exact (NEV b Hb)]| apply U3; [exact HbL| exact (NEV b Hb)]]. }

    set (OB := M ++ nb :: hdrs_blocks FI AI hs2).
    assert (OBZ : forall b, In b OB -> In b ((M ++ [hb]) ++ Zl) /\ In b (M ++ vb :: Zl)).
    { intros b Hb. unfold OB in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - split; [apply in_or_app; left; apply in_or_app; left; exact Hb| apply in_or_app; left; exact Hb].
      - assert (HZ : In b Zl) by (unfold Zl; destruct Hb as [<-|Hb]; [left; reflexivity| right; apply in_or_app; left; exact Hb]).
        split; [apply in_or_app; right; exact HZ| apply in_or_app; right; right; exact HZ]. }
    assert (OBK : bkeep FI AI OB m m2).
    { apply (bkeep_of_apx FI AI OB _ _ q' m m2 AP).
      - intros b Hb. destruct (OBZ b Hb) as [Z1 _]. apply (lb_remove_In FI AI); [exact (INL b (INL' b Z1))| exact (NEV b Z1)].
      - intros b Hb. destruct (OBZ b Hb) as [Z1 Z2].
        assert (BNE : b <> hb) by (intros E; apply (NEH b Z2); rewrite E; reflexivity).
        pose proof (am_blocks_disjoint FI AI s LB m b hb HR (INL b (INL' b Z1)) HBIN BNE) as DJ. cbn [blk_addr blk_size fst snd hb] in DJ.
        cbn [disjoint_from]. split; [clear - DJ; lia| exact I]. }
    assert (TRB : forall xa cs, hA FI AI h <= xa -> xa + Z.of_nat (cells_size cs) <= hA FI AI h + 88 ->
                  (xa + Z.of_nat (cells_size cs) <= hA FI AI h + 24 \/ hA FI AI h + 56 <= xa) -> rw_cells asegs m xa cs -> rw_cells asegs m2 xa cs).
    { intros xa cs X1 X2 X3 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| | cbn [disjoint_from]; split; [clear - X3; lia| exact I]].
      eapply (aclient_range_block FI AI _ q' xa _ hb (lb_remove_In FI AI _ _ hb HBIN HBNV)); cbn [blk_addr blk_size fst snd hb]; clear - X1 X2; lia. }
    assert (TRL : forall xa cs, P + 288 <= xa -> xa + Z.of_nat (cells_size cs) <= P + 384 -> rw_cells asegs m xa cs -> rw_cells asegs m2 xa cs).
    { intros xa cs X1 X2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; clear - X1 X2 PF1 PF2; lia|].
      cbn [disjoint_from]. split; [clear - X1 X2 PF1 PF2 HX1; lia| exact I]. }
    apply (ainv_apx _ _ stc q' m m2 s LB sx LBx ns _ ns (hs1 ++ h1 :: hs2) X X' meth pos0 AINV (fun _ => HSX) AP HW QB RF2 LIVE).
    - intros b Hb. apply (lb_remove_In FI AI); [apply KSUB; exact Hb|]. apply NEV. apply in_or_app; right. unfold Zl. right. apply in_or_app; right. right. exact Hb.
    - intros a Hc _. cbn [outside]. split; [| exact I]. intros Hr.
      apply (blk_no_fclient sx LBx m2 hb a HRx (U2 hb HBIN HBNV)); [| | exact Hc| cbn [blk_addr blk_size fst snd hb]; clear - Hr; lia].
      + intros b Hb. apply (OLDx b). apply in_or_app; right. unfold Zl. right. apply in_or_app; right. right. exact Hb.
      + intros Hk. apply (NEH hb); [| reflexivity]. apply in_or_app; right. right. unfold Zl. right. apply in_or_app; right. right. exact Hk.
    - exact HRx.
    - exact TXx.
    - intros b Hb. assert (Hb2 : In b (hl_blocks FI AI ns (hs1 ++ h1 :: hs2) ++ (kA, A, cap + 1) :: LBK)) by (apply in_or_app; left; exact Hb).
      rewrite SPL1 in Hb2. apply in_app_or in Hb2. destruct Hb2 as [Hb2|[<-|Hb2]]; [apply (OLDx b); apply in_or_app; left; exact Hb2| exact U1| apply (OLDx b); apply in_or_app; right; exact Hb2].
    - intros b Hb. apply (OLDx b). apply in_or_app; right. unfold Zl. right. apply in_or_app; right. right. exact Hb.
    - rewrite SPL1. apply (nd_replace1 (M ++ [hb]) Zl vb vb' ND). intros b Hb. cbn [blk_id fst vb']. exact (proj2 (OLDx b Hb)).
    - unfold p_hlist.
      split; [apply TRL; [clear; lia| unfold lhead_cells; simpl_sizes; clear; lia| exact LHC]|].
      split; [apply TRL; [clear; lia| unfold fl_cells; simpl_sizes; clear; lia| exact FLC]|].
      split; [apply TRL; [clear; lia| simpl_sizes; clear; lia| exact FFC]|].
      split. { eapply (dlseg_bkeep FI AI); [exact DL| exact OBK|]. intros b it Hb. unfold OB, M. apply in_or_app; left. apply in_or_app; left. exact (in_map fst _ _ Hb). }
      split. { apply hdrs_mem_app. split.
               - eapply (hdrs_mem_bkeep FI AI); [exact HM1| exact OBK|]. intros b Hb. unfold OB, M. apply in_or_app; left. apply in_or_app; right. exact Hb.
               - cbn [HObjA.hdrs_mem]. split; [| split].
                 + unfold hdro_mem, h1. cbn [hA nA nlen hid vA vlen vcap ncap].
                   split; [exists hpad; apply TRB; [clear; lia| simpl_sizes; clear; lia| left; simpl_sizes; clear; lia| exact HCc]|]. split; [exact VMC'|].
                   split; [exists vbs'; split; [exact VBC'| exact VNUL']|].
                   split; [apply TRB; [clear; lia| unfold mbuf_cells; simpl_sizes; clear; lia| right; clear; lia| exact NMC]|].
                   exists nbs. split; [| exact NNUL]. apply (OBK nb (nA FI AI h) _); [unfold OB; apply in_or_app; right; left; reflexivity| cbn [blk_addr fst snd nb]; clear; lia| | exact NBC].
                   cbn [blk_addr blk_size fst snd nb cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - P3; lia). clear. lia.
                 + unfold hdro_pure, h1. cbn [vlen vcap nlen ncap hid]. clear - P1 P2 P3 P4 P5 N1 VC1 VC2. lia.
                 + eapply (hdrs_mem_bkeep FI AI); [exact HM2| exact OBK|]. intros b Hb. unfold OB. apply in_or_app; right. right. exact Hb. }
      split; [rewrite !map_app in *; cbn [map hA h1]; exact IT|].
      split. { intros h' Hh'. apply in_app_or in Hh'. destruct Hh' as [Hh'|[<-|Hh']].
               - destruct (VB h' ltac:(apply in_or_app; left; exact Hh')) as [V1 V2]. split; [clear - V1 XX; lia| exact V2].
               - destruct (VB h ltac:(apply in_or_app; right; left; reflexivity)) as [V1 V2]. unfold h1. cbn [vlen nlen]. split; [exact VX| exact V2].
               - destruct (VB h' ltac:(apply in_or_app; right; right; exact Hh')) as [V1 V2]. split; [clear - V1 XX; lia| exact V2]. }
      split; [clear - ZL XX; lia| clear - XP XX; lia].
  Qed.

  #[using="WSL bs cslack"] Lemma ainv_mono : forall s LB m ns hs X X' meth pos, ainv s LB m ns hs X meth pos -> X <= X' -> ainv s LB m ns hs X' meth pos.
  Proof.
    intros s LB m ns hs X X' meth pos (HR & HA & SUB & KSUB & ND & PHL & PM0 & PM4 & MR & VER & CT3 & PR & CT5 & HS & SHC & ZB & SHZ0 & APF & CH & HSM) LE. unfold ainv. repeat (split; [assumption|]).
    split; [exact (p_hlist_mono m ns hs X X' PHL LE)|]. repeat (split; [assumption|]). clear - HSM LE. lia.
  Qed.

  #[using="Type"] Lemma alt_facts : forall s (LB : BL) sx (LBx : BL) mx (k : K) VA vc A' cap' (ok' : option K) vl0 n (vbs' : list byte),
    RHEAP_A FI AI sx LBx mx -> In (k, VA, vc + 1) LB ->
    ((ok' = Some k /\ LBx = LB /\ A' = VA /\ cap' = vc /\ am_nsec FI AI sx = am_nsec FI AI s)
     \/ (exists k', ok' = Some k' /\ LBx = (k', A', cap' + 1) :: lb_remove (am_K_eqb FI AI) k LB /\ am_nsec FI AI sx = am_nsec FI AI s + nsec1 (cap' + 1)
                     /\ vc < vl0 + n /\ vc + 5 <= cap' <= vc + Z.max 5 n)) ->
    mownA FI AI mx LBx A' cap' ok' vbs' -> 0 <= vl0 <= vc -> vl0 + n <= cap' -> cap' <= vc + n + 5 -> vc <= vl0 + 5 -> 0 <= n ->
    exists k', ok' = Some k' /\ In (k', A', cap' + 1) LBx /\ rw_cells asegs mx A' [CB (Z.to_nat (cap' + 1)) vbs']
      /\ (forall b, In b LB -> blk_id b <> k -> In b LBx) /\ (forall b, In b LB -> blk_id b <> k -> blk_id b <> k')
      /\ hgrow n (am_nsec FI AI s) LB (am_nsec FI AI sx) LBx
      /\ cap' <= vl0 + n + 5
      /\ 5 * (am_nsec FI AI sx - am_nsec FI AI s) <= w0 (cap' + 1) - w0 (vc + 1).
  Proof.
    intros s LB sx LBx mx k VA vc A' cap' ok' vl0 n vbs' HRx VIN [(-> & -> & -> & -> & NS)|(k' & -> & -> & NS & G1 & G2)] OWN V0 V1 V2 SL NN0; cbn [mownA] in OWN; destruct OWN as [OIN OC].
    - exists k. split; [reflexivity|]. split; [exact OIN|]. split; [exact OC|]. split; [intros b Hb _; exact Hb|]. split; [intros b _ NE; exact NE|].
      split; [rewrite NS; apply hg_same|]. split; [clear - SL NN0; lia| rewrite NS; clear; lia].
    - exists k'. split; [reflexivity|]. split; [exact OIN|]. split; [exact OC|].
      split; [intros b Hb NE; right; apply (lb_remove_In FI AI); assumption|].
      split; [intros b Hb NE; apply (fresh_id sx _ mx (k', A', cap' + 1) HRx b); apply (lb_remove_In FI AI); assumption|].
      split; [rewrite NS; apply (hg_new n _ LB k k' VA A' vc cap' vl0); assumption|]. split; [clear - SL G1 G2; lia|].
      rewrite NS. pose proof (w0_grow vc cap' ltac:(clear - V0; lia) (proj1 G2)) as WG. clear - WG. lia.
  Qed.

  #[using="IC AC ASL AMS HOK RF0 WSL cslack VERR CTLR QTOP COMMAB CSL ZSTAT N0E MSGP X0B CUR0"] Lemma ext_tail : forall s LB ns hs X meth d (q' it N id sv tlz cur' o l : Z) (m m' : mem) (tyw : word)
      y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y27 y28 y29 y30 y31,
    khead (sv + 1) ->
    ainv s LB m ns hs X meth pos0 -> hinv q' cur' tyw (wz (A + sv)) (wz tlz) (wz (A + o)) (wz l) bs m m' ->
    lfacts s LB X sv d meth hs -> In (N, it, id) (ns3_of FI AI ns hs) ->
    0 <= sv -> 1 <= tlz -> sv + tlz + 1 <= o -> 0 <= l -> o + l <= len -> sv + tlz + 1 <= cur' -> o + l + 1 <= cur' -> cur' <= len ->
    AJ FI AI J POST (existstH q' it y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y27 y28 y29 y30 y31 m') s LB.
  Proof.
    intros s LB ns hs X meth d q' it N id sv tlz cur' o l m m' tyw y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y26 y27 y28 y29 y30 y31
           KH AINV INV LF HIN SV0 TL1 O1 L0 OL C1 C2 C3.
    destruct (ainv_stretch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AINV INV) as (meth1 & AINV0 & MO1).
    pose proof (hinv_restart _ _ _ _ _ _ _ _ _ _ _ _ INV) as INV1. clear AINV INV.
    pose proof LF as (CNT & HB & HLS & DR & SR & XE & MO).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    set (dl := cur' - sv). set (X' := X + 2 * dl).
    assert (DL2 : 2 <= dl) by (unfold dl; clear - C1 TL1; lia).
    assert (LDL : l + 3 <= dl) by (unfold dl; clear - O1 C2 TL1; lia).
    rename AINV0 into AINV1.
    assert (XX' : X <= X') by (unfold X'; clear - DL2; lia).

    pose proof AINV1 as (HRa & HAa & SUBa & _ & _ & PHLa & _).
    pose proof PHLa as (_ & _ & _ & _ & HMa & ITa & VBa & _ & XPa).
    destruct (ns3_of_In FI AI ns hs N it id ITa HIN) as (b & h & Hb & Hh & -> & -> & ->).
    destruct (in_split h hs Hh) as (hs1 & hs2 & ->).
    pose proof (proj2 (proj1 (hdrs_mem_app hs1 (h :: hs2) m') HMa)) as HM2. cbn [HObjA.hdrs_mem] in HM2. destruct HM2 as (HMh & HPh & _).
    destruct HMh as (_ & VMC & (vbs & VBC & _) & _). pose proof HPh as (P1 & P2 & P3 & P4 & P5).
    destruct (VBa h ltac:(apply in_or_app; right; left; reflexivity)) as [VX _].
    assert (HBIN : In (hk FI AI h, hA FI AI h, 88) LB).
    { apply SUBa. unfold hl_blocks. apply in_or_app; right. rewrite hdrs_blocks_app, (hdrs_blocks_cons FI AI h hs2). apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
    assert (VBIN : In (vk FI AI h, vA FI AI h, vcap FI AI h + 1) LB).
    { apply SUBa. unfold hl_blocks. apply in_or_app; right. rewrite hdrs_blocks_app, (hdrs_blocks_cons FI AI h hs2). apply in_or_app; right. apply in_or_app; left. right; left. reflexivity. }
    destruct (am_block_range FI AI s LB m' _ HRa HBIN) as (HR1 & HR2 & _ & HR4 & HR5 & _). cbn [blk_addr blk_size fst snd] in HR1, HR2, HR4, HR5.
    assert (LB63 : 0 <= l < 2^63) by (destruct MSGP as [MP _]; unfold LMAX_A in MP; clear - L0 OL LENC MP O1 SV0 TL1; lia).
    pose proof INV1 as (_ & _ & _ & _ & _ & _ & _ & MI1 & _).
    eapply (aj_evt FI AI J (fun ms' =>
        (l = 0 /\ ms' = nextstH q' y1 y5 y6 y7 (wz 0) y11 y12 y13 y14 y15 y16 y17 (wz (hA FI AI h)) y21 y26 y27 y28 y29 y30 y31 m')
        \/ (l <> 0 /\ ms' = ajcallstH 0x8d078 0x888e8 q' (wz (hA FI AI h + 24)) (wz COMMA_ADDR_A) y12 y5 y6 y7 y13 y14 y15 y16 y17 (wz (hA FI AI h + 24)) y21 y26 y27 y28 y29 y30 y31 m'))).
    { eapply (existE1 q' (hA FI AI h) cur' l tyw (wz (A + sv)) (wz tlz) (wz (A + o)) bs m' m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV1 LB63 ltac:(clear - HR1; lia) ltac:(clear - HR4 ACR; lia) ltac:(clear - HR2; Z.div_mod_to_equations; lia)).
      - intros L00. apply evt_done. left. split; [exact L00| reflexivity].
      - intros LN0. apply evt_done. right. split; [exact LN0| reflexivity]. }
    intros ms' [(L00 & ->)|(LN0 & ->)].
    -
      assert (HLN : hline dl (am_nsec FI AI s) LB (am_nsec FI AI s) LB).
      { apply (hl_ext (am_nsec FI AI s) LB dl l (am_nsec FI AI s) LB (am_nsec FI AI s) LB DL2 ltac:(clear - L0 LDL; lia)); apply hg_same. }
      eapply (next_tail s LB _ _ X' meth1 (d + dl) q' cur' m' m' tyw _ _ _ _); [exact (khead_mono (sv + 1) cur' KH ltac:(clear - C1 TL1; lia))| exact (ainv_mono _ _ _ _ _ X X' _ _ AINV1 XX')| exact INV1|].
      unfold lfacts. split; [destruct CNT as (CN1 & CN2 & CN3 & CN4); unfold cntf; split; [exact CN1|]; split; [exact CN2|]; split; [clear - CN3 DL2; lia| exact CN4]|].
      split; [replace (len - cur') with (len - sv - dl) by (unfold dl; clear; lia); eapply hbud_line; [exact HB| exact HLN| unfold CG_A, CG_B; clear - DL2; lia]|].
      split; [exact (hlines_snoc d N0 LB0 _ LB HLS dl _ _ HLN)|].
      split; [unfold dl; clear - DR C1 SV0 TL1; lia|]. split; [unfold dl; clear - SR C1 C3 TL1; lia|]. split; [unfold X', dl; clear - XE; lia|]. clear - MO MO1. lia.
    -
      pose proof INV1 as (ST1 & _ & _ & _ & _ & _ & _ & _ & AE1 & _ & _ & _ & _ & _ & _ & _ & (QB & QAL) & HRS1).
      destruct (hrest_rf _ _ _ _ HRS1) as (stc & RFc & LIVEc).
      pose proof AINV1 as (_ & _ & _ & KSUBa & NDa & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHCa & _).
      assert (IDS : hk FI AI h <> vk FI AI h /\ kA <> vk FI AI h).
      { rewrite hl_split in NDa. pose proof (nd_mid_neq _ _ _ NDa) as NE. cbn [blk_id fst] in NE. split.
        - apply (NE (hk FI AI h, hA FI AI h, 88)). apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left. reflexivity.
        - apply (NE (kA, A, cap + 1)). apply in_or_app; right. right. apply in_or_app; right. left. reflexivity. }
      destruct IDS as [IDH IDT].
      assert (X'B : X' <= 2^27 + 64) by (unfold X', dl; clear - XE X0B C3 SR; lia).
      assert (VBL : Z.of_nat (length vbs) = vcap FI AI h + 1) by (destruct VBC as [[W _] _]; cbn in W; destruct W as [W _]; clear - W P1; lia).
      unfold H_phdr_seg.ajcallstH.
      eapply (aj_bind FI AI J).
      { eapply (membuffer_append_str_spec_A IC FI AI J AC ASL AMS) with (st := stc) (ok := Some (vk FI AI h)) (MB := hA FI AI h + 24) (SRC := COMMA_ADDR_A)
                 (A := vA FI AI h) (len := vlen FI AI h) (cap := vcap FI AI h) (lo := lo) (str := [Z_to_bv 8 44; Z_to_bv 8 32]) (slack := cslack) (bs := vbs).
        - exact HRa.
        - exact RFc.
        - exact AE1.
        - exact ST1.
        - exact CLO.
        - unfold A0_RT_STACK. clear - LO QB. lia.
        - exact QAL.
        - clear - QB QTOP. lia.
        - exact MI1.
        - exact VMC.
        - clear - P1. lia.
        - cbn [length]. clear - P2 VX XX' X'B. lia.
        - intros n' Hn'. apply (hbud_now (len - sv) _ s LB n' HB); [exact (proj2 (proj2 (proj2 CNT)))| clear - SR; lia|]. cbn [length] in Hn'. unfold A0_MAXREQ. clear - Hn' P2 VX XX' X'B. lia.
        - cbn [mownA]. split; [exact VBIN| exact VBC].
        - right; left. exists (hk FI AI h, hA FI AI h, 88). cbn [lb_keepA blk_addr blk_size fst snd]. split; [apply (lb_remove_In FI AI); [exact HBIN| exact IDH]| clear; lia].
        - clear - HR4. lia.
        - clear - HR2. Z.div_mod_to_equations. lia.
        - apply (block_shw FI AI s LB m' _ (hA FI AI h + 24) 32 HRa HBIN); cbn [blk_addr blk_size fst snd]; clear; lia.
        - exact (COMMAB m' MI1).
        - cbn [In]. intros [E|[E|[]]]; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
        - cbn [length]. replace ((- (COMMA_ADDR_A + Z.of_nat 2 + 1)) mod 8) with 5 by reflexivity. clear - CSL. lia.
        - clear. lia.
        - right. cbn [length]. split; [clear; lia|]. split; [clear; lia|]. exists 0x10000, 0xaca48. split; [apply AMS; unfold a0_static; split; [clear; lia| left; clear; lia]| clear; lia].
        - cbn [length]. exact SHCa.
        - left. cbn [length]. clear - CSL ACR. lia.
        - cbn [length]. clear. lia.
        - left. cbn [length]. clear - HR5. lia.
        - reflexivity.
        - reflexivity. }
      intros sx LBx msx PO. unfold membuffer_append_post_A in PO.
      destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m2 & A1 & c1 & ok1 & vbs1
                      & -> & MI2 & ST2 & AE2 & RF2 & APX2 & HR2x & LBALT & VMC2 & VC1 & VC2 & VOWN & VKEEP & VNUL).
      cbn [lb_keepA length] in APX2, LBALT, VMC2, VC1, VC2, VNUL. change (Z.of_nat 2) with 2 in *.
      destruct (alt_facts s LB sx LBx m2 (vk FI AI h) (vA FI AI h) (vcap FI AI h) A1 c1 ok1 (vlen FI AI h) 2 vbs1 HR2x VBIN LBALT VOWN ltac:(clear - P1; lia) VC1 VC2 P2 ltac:(clear; lia))
        as (k1 & -> & U1 & VBC1 & U2 & U3 & HG1 & SL1 & CG1).
      assert (NUL1 : nth_error vbs1 (Z.to_nat (vlen FI AI h + 2)) = Some (Z_to_bv 8 0)).
      { refine (nul_of_firstn vbs1 (firstn (Z.to_nat (vlen FI AI h)) vbs ++ [Z_to_bv 8 44; Z_to_bv 8 32]) _ _ _).
        - rewrite length_app, length_firstn. cbn [length]. clear - VBL P1. lia.
        - rewrite <- app_assoc. apply VNUL. clear. lia. }
      destruct (ext_update s LB sx LBx m' m2 ns hs1 hs2 h X X' meth1 stc q' cur' tyw _ _ _ _ 2 A1 c1 k1 vbs1 AINV1 INV1 RFc RF2 LIVEc MI2 ST2 AE2 APX2 HR2x U1 U2 U3 VMC2 VBC1 NUL1
                  ltac:(clear; lia) VC1 SL1 ltac:(unfold X'; clear - VX DL2; lia) XX'
                  ltac:(pose proof (ainv_hsum _ _ _ _ _ _ _ _ AINV1) as HSx; rewrite hsumA_app in HSx |- *; cbn [hsumA fold_right vlen nlen] in HSx |- *; unfold X'; clear - HSx DL2; lia)) as [AINV2 INV2].

      replace (ret_pc (Z_to_bv 64 559336)) with (Z_to_bv 64 559336) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (aj_evt FI AI J (fun ms' => ms' = ajcallstH 0x8cd1c 0x888fc q' (wz (hA FI AI h + 24)) (wz (A + o)) (wz l) u0 u1 u2 e3 e4 e5 e6 e7 (wz (hA FI AI h + 24)) (wz 0) y26 y27 u3 u4 u5 u6 m2)).
      { eapply (existE2 q' (hA FI AI h) cur' tyw (wz (A + sv)) (wz tlz) (wz (A + o)) (wz l) bs m2 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2). apply evt_done. reflexivity. }
      intros ms' ->.
      pose proof INV2 as (ST2' & _ & _ & _ & _ & _ & _ & _ & AE2' & _ & _ & _ & _ & _ & _ & _ & _ & HRS2).
      destruct (hrest_rf _ _ _ _ HRS2) as (stc2 & RFc2 & LIVEc2).
      destruct (text_src _ _ _ _ _ _ _ _ _ _ _ o l INV2 ltac:(clear - O1 SV0 TL1; lia) L0 OL) as [BSV LSV].
      assert (HBx : In (hk FI AI h, hA FI AI h, 88) LBx) by (apply U2; [exact HBIN| exact IDH]).
      assert (TXx : In (kA, A, cap + 1) LBx) by (apply U2; [exact HAa| exact IDT]).
      assert (HBNT : (hk FI AI h, hA FI AI h, 88) <> (kA, A, cap + 1)).
      { intros E.
        assert (ND2 : NoDup (map blk_id ((map fst ns ++ hdrs_blocks FI AI hs1) ++ (hk FI AI h, hA FI AI h, 88)
                         :: ((vk FI AI h, vA FI AI h, vcap FI AI h + 1) :: (nk FI AI h, nA FI AI h, ncap FI AI h + 1) :: hdrs_blocks FI AI hs2 ++ (kA, A, cap + 1) :: LBK)))).
        { pose proof NDa as ND'. rewrite hl_split in ND'. rewrite <- !app_assoc in ND'. rewrite <- !app_assoc. exact ND'. }
        pose proof (nd_mid_neq _ _ _ ND2 (kA, A, cap + 1)) as NE. cbn [blk_id fst] in NE. apply NE; [| injection E as E1 _ _; symmetry; exact E1].
        apply in_or_app; right. right. right. apply in_or_app; right. left. reflexivity. }
      destruct (blk_hapx s LB m' _ kA HRa HBIN HAa HBNT) as (_ & _ & _ & _ & (_ & _ & HX3)). cbn [blk_addr blk_size fst snd] in HX3.
      assert (VBL1 : Z.of_nat (length vbs1) = c1 + 1) by (destruct VBC1 as [[W _] _]; cbn in W; destruct W as [W _]; clear - W VC1 P1; lia).
      unfold H_phdr_seg.ajcallstH.
      eapply (aj_bind FI AI J).
      { eapply (membuffer_append_spec_A IC FI AI J AC ASL AMS) with (st := stc2) (ok := Some k1) (MB := hA FI AI h + 24) (SRC := A + o) (n := l)
                 (A := A1) (len := vlen FI AI h + 2) (cap := c1) (lo := lo) (src := firstn (Z.to_nat l) (skipn (Z.to_nat o) bs)) (bs := vbs1).
        - exact HR2x.
        - exact RFc2.
        - exact AE2'.
        - exact ST2'.
        - exact CLO.
        - unfold A0_RT_STACK. clear - LO QB. lia.
        - exact QAL.
        - clear - QB QTOP. lia.
        - exact MI2.
        - exact VMC2.
        - clear - P1 VC1. lia.
        - destruct MSGP as [MP _]. unfold LMAX_A in MP. clear - VC2 P2 VX XX' X'B OL O1 SV0 TL1 LENC MP. lia.
        - intros n' Hn'. apply (hbud_part (len - sv) _ 2 s LB sx LBx n' HB (proj2 (proj2 (proj2 CNT))) (hp_ext1 _ _ 2 _ _ ltac:(clear; lia) HG1)); [clear - C1 C3 TL1; lia|].
          unfold A0_MAXREQ. destruct MSGP as [MP _]. unfold LMAX_A in MP. clear - Hn' VC2 P2 VX XX' X'B OL O1 SV0 TL1 LENC MP. lia.
        - cbn [mownA]. split; [exact U1| exact VBC1].
        - right; left. exists (hk FI AI h, hA FI AI h, 88). cbn [lb_keepA blk_addr blk_size fst snd]. split; [apply (lb_remove_In FI AI); [exact HBx| exact (U3 _ HBIN IDH)]| clear; lia].
        - clear - HR4. lia.
        - clear - HR2. Z.div_mod_to_equations. lia.
        - apply (block_shw FI AI sx LBx m2 _ (hA FI AI h + 24) 32 HR2x HBx); cbn [blk_addr blk_size fst snd]; clear; lia.
        - exact BSV.
        - exact LSV.
        - clear - ALO O1 SV0 TL1. lia.
        - left. right; left. exists (kA, A, cap + 1). cbn [lb_keepA blk_addr blk_size fst snd]. split; [apply (lb_remove_In FI AI); [exact TXx| exact (U3 _ HAa IDT)]| clear - O1 SV0 TL1 OL L0 LENC; lia].
        - apply (block_shw FI AI sx LBx m2 (kA, A, cap + 1) (A + o) l HR2x TXx); cbn [blk_addr blk_size fst snd]; clear - O1 SV0 TL1 OL L0 LENC; lia.
        - pose proof alloc_ceiling_range as ACRx; unfold alloc_floor, alloc_ceiling_max in ACRx; clear - ACRx AHI O1 SV0 TL1 OL L0 LENC; lia.
        - clear - HX3 O1 SV0 TL1 OL L0 LENC. lia.
        - reflexivity.
        - reflexivity.
        - reflexivity. }
      intros sy LBy msy PO. unfold membuffer_append_post_A in PO.
      destruct PO as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m3 & A2 & c2 & ok2 & vbs2
                      & -> & MI3 & ST3 & AE3 & RF3 & APX3 & HR3 & LBALT3 & VMC3 & VC31 & VC32 & VOWN3 & VKEEP3 & VNUL3).
      cbn [lb_keepA] in APX3, LBALT3.
      destruct (alt_facts sx LBx sy LBy m3 k1 A1 c1 A2 c2 ok2 (vlen FI AI h + 2) l vbs2 HR3 U1 LBALT3 VOWN3 ltac:(clear - P1 VC1; lia) VC31 VC32 SL1 ltac:(clear - L0; lia))
        as (k2 & -> & U1' & VBC2 & U2' & U3' & HG2 & SL3 & CG2).
      assert (NUL2 : nth_error vbs2 (Z.to_nat (vlen FI AI h + 2 + l)) = Some (Z_to_bv 8 0)).
      { refine (nul_of_firstn vbs2 (firstn (Z.to_nat (vlen FI AI h + 2)) vbs1 ++ firstn (Z.to_nat l) (skipn (Z.to_nat o) bs)) _ _ _).
        - rewrite length_app, length_firstn. clear - VBL1 VC1 P1 LSV. lia.
        - rewrite <- app_assoc. apply VNUL3. clear - LN0 L0. lia. }
      set (h1 := mkHdr FI AI (hA FI AI h) (hk FI AI h) (hid FI AI h) (nA FI AI h) (nlen FI AI h) (ncap FI AI h) (nk FI AI h) A1 (vlen FI AI h + 2) c1 k1) in *.
      destruct (ext_update sx LBx sy LBy m2 m3 ns hs1 hs2 h1 X' X' meth1 stc2 q' cur' tyw _ _ _ _ l A2 c2 k2 vbs2 AINV2 INV2 RFc2 RF3 LIVEc2 MI3 ST3 AE3 APX3 HR3 U1' U2' U3' VMC3 VBC2 NUL2
                  ltac:(clear - LN0 L0; lia) VC31 ltac:(cbn [vlen vcap h1]; exact SL3) ltac:(unfold X'; cbn [vlen h1]; clear - VX DL2 LDL; lia) ltac:(clear; lia)
                  ltac:(pose proof (ainv_hsum _ _ _ _ _ _ _ _ AINV1) as HSx; rewrite hsumA_app in HSx |- *; unfold h1; cbn [hsumA fold_right vlen nlen] in HSx |- *; unfold X'; clear - HSx LDL; lia)) as [AINV3 INV3].

      replace (ret_pc (Z_to_bv 64 559356)) with (Z_to_bv 64 559356) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (aj_evt FI AI J (fun ms' => ms' = nextstH q' (wz 0x888fc) w0 w1 w2 (wz 0) (wz (-104)) g2 g3 g4 g5 g6 g7 (wz (hA FI AI h + 24)) (wz 0) y26 y27 w3 w4 w5 w6 m3)).
      { eapply (existE3 q' m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MI3). apply evt_done. reflexivity. }
      intros ms' ->.
      assert (HLN : hline dl (am_nsec FI AI s) LB (am_nsec FI AI sy) LBy).
      { exact (hl_ext _ _ dl l _ _ _ _ DL2 ltac:(clear - L0 LDL; lia) HG1 HG2). }
      eapply (next_tail sy LBy _ _ X' meth1 (d + dl) q' cur' m3 m3 tyw _ _ _ _); [exact (khead_mono (sv + 1) cur' KH ltac:(clear - C1 TL1; lia))| exact AINV3| exact INV3|].
      unfold lfacts.
      split. { destruct CNT as (CNT & CNL & CN3 & CN4). split; [| split; [| split]].
               - rewrite (phiH_app FI AI). rewrite (phiH_app FI AI) in CNT. cbn [phiH fold_right vcap ncap] in CNT |- *. unfold h1. cbn [vcap ncap]. clear - CNT CG1 CG2. lia.
               - pose proof (hgrow_len _ _ _ _ _ HG1) as GL1. pose proof (hgrow_len _ _ _ _ _ HG2) as GL2.
                 rewrite length_app in CNL |- *. cbn [length] in CNL |- *. clear - CNL GL1 GL2. lia.
               - rewrite hsumA_app in CN3 |- *. unfold h1. cbn [hsumA fold_right vlen nlen] in CN3 |- *. clear - CN3 LDL. lia.
               - pose proof AINV3 as (_ & _ & _ & _ & _ & PHL3 & _). exact (p_hlist_cgG _ _ _ _ _ PHL3). }
      split; [replace (len - cur') with (len - sv - dl) by (unfold dl; clear; lia); eapply hbud_line; [exact HB| exact HLN|]; apply (cgG_step FI AI);
              [rewrite !(phiH_app FI AI); cbn [phiH fold_right vcap ncap]; unfold h1; cbn [vcap ncap]; clear - CG1 CG2; lia
              | rewrite !(hlenA_app FI AI); cbn [hlenA fold_right vlen nlen]; unfold h1; cbn [vlen nlen]; clear - LDL; lia]|].
      split; [exact (hlines_snoc d N0 LB0 _ LB HLS dl _ _ HLN)|].
      split; [unfold dl; clear - DR C1 SV0 TL1; lia|]. split; [unfold dl; clear - SR C1 C3 TL1; lia|]. split; [unfold X', dl; clear - XE; lia|]. clear - MO MO1. lia.
  Qed.

  #[using="ASL lo len HOK RF0 WSL bs cslack"] Lemma ainv_pos : forall m me s LB ns hs X meth pos pos',
    ainv s LB m ns hs X meth pos -> munch [(P + 448, P + 452)]%Z m me -> wmono asegs m me ->
    rw_cells asegs me (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos')] -> 0 <= pos' <= 4 ->
    ainv s LB me ns hs X meth pos'.
  Proof.
    intros m me s LB ns hs X meth pos pos' AINV MU WM CT3' PR'.
    pose proof AINV as (HR & HA & SUB & KSUB & ND & _).
    destruct pgeom as [PF1 PF2]. pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    apply (ainv_munch [(P + 448, P + 452)]%Z m me s LB ns hs X meth pos pos' AINV MU WM); [| | | | | | | exact CT3'| exact PR'].
    - constructor; [| constructor]. do 3 right; left. cbn [fst snd]. clear - PF1 PF2. lia.
    - intros b Hb. destruct (pblk_facts s LB m ns hs b HR HA SUB ND Hb) as [BIN _].
      destruct (am_block_range FI AI s LB m b HR BIN) as (_ & _ & R3 & _ & _ & _ & R7). cbn [disjoint_from]. split; [clear - R3 R7 PF1 PF2; lia| exact I].
    - intros a n A1 A2 A3. cbn [disjoint_from]. split; [clear - A3; lia| exact I].
    - constructor; [| constructor]. left. apply sub_app_iv_fsH; clear - PF1 PF2 B1; lia.
    - constructor; [| constructor]. cbn [fst]. clear - PLO. lia.
    - constructor; [| constructor]. cbn [snd]. clear - PHI CLO LO. lia.
    - constructor; [| constructor]. right; right. unfold phdr_WA. cbn [inside fst snd]. right; right; left. clear. lia.
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 HOK RF0 FCO WSL HID cslack VERR CTLR QTOP TRACE COMMAB CSL ZSTAT BSL N0E MSGP X0B X00 CUR0"] Lemma loopH : forall (n : nat) s LB m ns hs X meth d (q' sv tlz ty : Z) (va vl : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31,
    len - sv <= Z.of_nat n ->
    ainv s LB m ns hs X meth pos0 -> hinv q' (sv + tlz) (wz ty) (wz (A + sv)) (wz tlz) va vl bs m m ->
    1 <= tlz -> sv + tlz <= len -> 0 <= ty <= 5 -> lfacts s LB X sv d meth hs ->
    AJ FI AI J POST (headstH q' sv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m) s LB.
  Proof.
    induction n as [|n IH]; intros s LB m ns hs X meth d q' sv tlz ty va vl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
                                  FUEL AINV INV TL1 TLN TYR LF; [exfalso; clear - FUEL TL1 TLN; lia|].
    pose proof LF as (CNT & HB & HLS & DR & SR & XE & MO).
    pose proof AINV as (HR & HA & SUB & KSUB & ND & PHL & _ & PM4 & MR & (pad & VER) & CT3 & PR & _ & HS & _).
    pose proof HOK as HOK'. hokA HOK'.
    assert (KH : khead (sv + 1)).
    { unfold khead. intros sx LBx mx nsx hsx Xx methx dx qx svx tlzx tyx vax vlx z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z27 z28 z29 z30 z31 BND AX IX T1 T2 T3 LFX.
      eapply (IH sx LBx mx nsx hsx Xx methx dx qx svx tlzx tyx vax vlx); [clear - FUEL BND; lia| exact AX| exact IX| exact T1| exact T2| exact T3| exact LFX]. }

    assert (NIN : ~ In (kA, A, cap + 1) (hl_blocks FI AI ns hs)).
    { intros Hi. apply nd_app in ND. destruct ND as (_ & IDJ & _). apply (IDJ _ (kA, A, cap + 1) Hi); [left; reflexivity| reflexivity]. }
    destruct (hviews_of_plist s LB m kA ns hs X HR PHL SUB HA NIN) as (HLI & HNM & SZE & SZ0).
    pose proof INV as (_ & _ & _ & _ & _ & _ & TXT & _).
    destruct (text_bytesH m bs TXT) as [TB TBL].
    destruct (block_slackA FI AI s LB m (kA, A, cap + 1) bs HR HA TB ltac:(cbn [blk_size snd]; exact TBL)) as (sl & kE & SLB & SL7 & SLAL). cbn [blk_addr blk_size fst snd] in SLB, SLAL.
    assert (HSL : hslk m sl).
    { split; [exact SLB|]. clear - SL7 SLAL. Z.div_mod_to_equations. lia. }
    assert (SZR : 0 <= zlength ns < 2^63) by (destruct PHL as (_ & _ & _ & _ & _ & _ & _ & ZL & _); clear - SZ0 ZL XE X0B SR CUR0; lia).
    eapply (aj_evt FI AI J).
    { exact (frontH q' sv tlz (sv + tlz) ty meth pos0 _ _ (zlength ns) va vl pad m _ sl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
               INV (am_fsenv FI AI _ _ _ HR) ltac:(clear - SR CUR0; lia) TL1 eq_refl TLN TYR HS
               HLI HNM HSL SZR SZE PM4 MR VER CT3 PR). }
    intros ms' [EXIT|[NEW|EXT]].
    - destruct EXIT as (qe & r & cur' & pos' & mb' & me & tyw & tb & tl & vae & vle & z1 & z5 & z6 & z7 & z11 & z12 & z15 & z16 & z17 & z18 & z19 & z20 & z21 & z22 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31
                       & -> & INVE & LINK & RR & CR & EX & PR').
      destruct LINK as [(-> & ->)|(-> & MUc & WMc & MIe & CT3')].
      + eapply (exit_epi s LB ns hs X meth pos0 d qe r cur' m me tyw tb tl vae vle); [exact AINV| exact INVE| exact HLS| clear - DR CR; lia| clear - SR CR; lia| clear - XE CR; lia| exact MO| exact RR| exact EX| exact CNT].
      + pose proof (ainv_pos m me s LB ns hs X meth pos0 pos' AINV MUc WMc CT3' PR') as AINVe.
        eapply (exit_epi s LB ns hs X meth pos' d qe r cur' me me tyw tb tl vae vle); [exact AINVe| exact INVE| exact HLS| clear - DR CR; lia| clear - SR CR; lia| clear - XE CR; lia| exact MO| exact RR| exact EX| exact CNT].
    - destruct NEW as (qe & id & cur' & o & l & m' & tyw & z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z21 & z26 & z28 & z29 & z30 & z31
                      & -> & INV' & O1 & L0 & OL & C1 & C2 & C3 & IDR).
      eapply (new_tail s LB ns hs X meth d qe id sv tlz cur' o l m m' tyw); [exact KH| exact AINV| exact INV'| exact LF| clear - SR CUR0; lia| exact TL1| exact O1| exact L0| exact OL| exact C1| exact C2| exact C3| exact IDR].
    - destruct EXT as (qe & it & N & id & cur' & o & l & m' & tyw & z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z21 & z26 & z27 & z28 & z29 & z30 & z31
                      & -> & INV' & HIN & O1 & L0 & OL & C1 & C2 & C3).
      eapply (ext_tail s LB ns hs X meth d qe it N id sv tlz cur' o l m m' tyw); [exact KH| exact AINV| exact INV'| exact LF| exact HIN| clear - SR CUR0; lia| exact TL1| exact O1| exact L0| exact OL| exact C1| exact C2| exact C3].
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 HOK RF0 FCO FE0 WSL HID cslack VERR CTLR QTOP TRACE COMMAB CSL ZSTAT BSL N0 N0E MSGP X0B X00 CUR0"] Lemma phdr_core : forall ns hs (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ainv s_0 LB0 m0 ns hs X0 meth0 pos0 -> hbud (len - cur0) (cgG FI AI hs) s_0 LB0 -> cntf s_0 LB0 hs 0 ->
    stk asegs m0 lo q ->
    rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) ->
    rw_cells asegs m0 A [CB (Z.to_nat (cap + 1)) bs] ->
    mem_inv asegs m0 -> asan_env asegs m0 ->
    shw m0 P 504 -> shw m0 A (cap + 1) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_HDR_A 8 ->
    shz m0 (sh lo) (sh q) -> shr m0 (sh lo - sh lo mod 8) (sh q + 8) ->
    AJ FI AI J POST
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz parse_headers_entryA) fc None m0 (seg_rom asegs))
      s_0 LB0.
  Proof.
    intros ns hs t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 AINV HB CNT0 ST SC MBC TXT MI AE SHP SHA SHSEP SHFMT SHZ SHR.
    assert (HLS0 : hlines 0 N0 LB0 (am_nsec FI AI s_0) LB0) by (rewrite <- N0E; apply hls_nil).
    eapply (aj_evt FI AI J (fun ms' =>
       (exists q' m tlz ty (va vl : word) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y27 y28 y29 y30 y31,
           ms' = headstH q' cur0 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y27 y28 y29 y30 y31 m
           /\ hinv q' (cur0 + tlz) (wz ty) (wz (A + cur0)) (wz tlz) va vl bs m0 m /\ 1 <= tlz /\ cur0 + tlz <= len /\ 0 <= ty <= 5)
       \/ (exists q' m r (ty tb tl va vl : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y22 y24 y25 y26 y27 y28 y29 y30 y31,
           ms' = xstH q' r cur0 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y22 y24 y25 y26 y27 y28 y29 y30 y31 m
           /\ hinvE q' cur0 ty tb tl va vl bs m0 m /\ (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE)))).
    - eapply (prologueH cur0 bs t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ ST SC MBC TXT MI AE SHP SHA SHSEP SHFMT SHZ SHR CUR0).
      + intros q' m tlz ty va vl y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y27 y28 y29 y30 y31 INV T1 T2 T3 _. apply evt_done. left.
        exists q', m, tlz, ty, va, vl, y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y27, y28, y29, y30, y31. repeat (split; [first [reflexivity| assumption]|]). exact T3.
      + intros q' m r ty tb tl va vl y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y22 y24 y25 y26 y27 y28 y29 y30 y31 INVE RR. apply evt_done. right.
        exists q', m, r, ty, tb, tl, va, vl, y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y19, y20, y22, y24, y25, y26, y27, y28, y29, y30, y31. split; [reflexivity|]. split; [exact INVE| exact RR].
    - intros ms' [(q' & m & tlz & ty & va & vl & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y27 & y28 & y29 & y30 & y31 & -> & INV & T1 & T2 & T3)
                 |(q' & m & r & ty & tb & tl & va & vl & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 & y22 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & -> & INVE & RR)].
      + destruct (ainv_stretch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AINV INV) as (meth1 & AINV1 & MO1).
        eapply (loopH (Z.to_nat (len - cur0)) s_0 LB0 m ns hs X0 meth1 0 q' cur0 tlz ty va vl);
          [clear - CUR0; lia| exact AINV1| exact (hinv_restart _ _ _ _ _ _ _ _ _ _ _ _ INV)| exact T1| exact T2| exact T3|].
        unfold lfacts. split; [exact CNT0|]. split; [exact HB|]. split; [exact HLS0|]. split; [clear; lia|]. split; [clear - CUR0; lia|]. split; [clear; lia| exact MO1].
      + eapply (exit_x s_0 LB0 ns hs X0 meth0 0 q' r cur0 cur0 m0 m ty tb tl va vl); [exact AINV| exact INVE| exact HLS0| clear; lia| clear - CUR0; lia| clear; lia| left; reflexivity| | | exact CNT0];
          unfold PARSE_INCOMPLETE, PARSE_FAILURE, PARSE_OK in *; clear - RR; lia.
  Qed.

End PHJ.

#[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2"] Theorem phdr_spec_A : phdr_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB LBK st
         P lo cur A len cap kA bs ns hs X meth isreq maj min err hack pos entp clen csz esp ws cslack ras.
  intros HR RF FCO AE ST CLO LO QAL QTOP MI PLB PHI PAL SHWP PSC PMSG HCUR PMETH PVER PHL PCTL SUB KSUB ND XB HB WSL HID STAT ZSTAT SHZ SHR CH TRACE ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  destruct (p_msg_facts FI AI m LB P A len cap (Some kA) bs s HR PMSG) as (HL & HCp & LBS0 & _ & SOME).
  destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (lb_geom FI st m P 504 RF PLB) as [PG1 PG2]. pose proof (fsb_ok FI) as (FB1 & _).
  destruct PMSG as (MBC & [HIN TXC] & _ & _ & MNUL).
  destruct PMETH as (PMC & MR). destruct PVER as ((pad & VERC) & ISR & MJR & MNR).
  destruct PCTL as (CTLC & CB1 & CB2 & CB3 & CB4 & CB5 & CB6 & CB7). unfold p_ctl_cells in CTLC.
  destruct STAT as (HS & SHSEP & SHFMT & COMMAB & CSL & SHC & ZB & SHZ0).
  assert (X00 : 0 <= X) by (destruct PHL as (_ & _ & _ & _ & _ & _ & _ & _ & XP); exact XP).
  assert (HOK : H_phdr_seg.ph_okA FI q lo P A len cap st).
  { unfold H_phdr_seg.ph_okA. split; [exact CLO|]. split; [exact LO|]. split; [exact QAL|]. split; [clear - QTOP TK3; lia|].
    split; [clear - PG1 FB1; lia|]. split; [exact PHI|]. split; [exact PAL|]. split; [exact PLB|].
    split; [exact S1|]. split; [exact S2|]. split; [exact HL|]. split; [exact S3|]. split; [exact S5|]. split; [exact S6|]. unfold LMAX_A in HCp. clear - HCp. lia. }
  destruct (proj1 (rw_cells_app asegs m P [C4 (wz 1)] [C4 (wz meth)]) PMC) as [PM0 PM4].
  destruct (proj1 (rw_cells_app asegs m (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos)] [C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)]) CTLC) as [CT3 CT5].
  replace (P + 440 + Z.of_nat (cells_size [C4 (wz err); C4 (wz hack); C4 (wz pos)])) with (P + 452) in CT5 by (simpl_sizes; lia).
  eapply (phdr_core q lo P A len cap st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m HOK RF FCO (am_fsenv FI AI _ _ _ HR) ws WSL HID LBK kA bs isreq maj min err hack entp clen csz esp ras cslack (2 * hsumA hs - X) (5 * am_nsec FI AI s - phiH FI AI hs) (Z.of_nat (length LB) - 4 * Z.of_nat (length hs)) (hsumA hs)
            (conj ISR (conj MJR MNR)) (conj CB1 (conj CB2 (conj CB4 (conj CB5 (conj CB6 CB7))))) QTOP TRACE COMMAB CSL ZSTAT LBS0 (am_nsec FI AI s) s LB cur X meth pos eq_refl
            (conj HCp MNUL) XB X00 HCUR ns hs).
  - unfold ainv. split; [exact HR|]. split; [exact HIN|]. split; [exact SUB|]. split; [exact KSUB|]. split; [exact ND|]. split; [exact PHL|].
    split; [exact PM0|]. split; [exact PM4|]. split; [exact MR|]. split; [exists pad; exact VERC|]. split; [exact CT3|]. split; [exact CB3|]. split; [exact CT5|].
    split; [exact HS|]. split; [exact SHC|]. split; [exact ZB|]. split; [exact SHZ0|]. split; [apply (apxF_refl FI AI)|]. split; [exact CH| clear; lia].
  - exact HB.
  - unfold cntf. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
    exact (p_hlist_cgG m P ns hs X PHL).
  - exact ST.
  - exact PSC.
  - exact MBC.
  - exact TXC.
  - exact MI.
  - exact AE.
  - exact SHWP.
  - exact S4.
  - exact SHSEP.
  - exact SHFMT.
  - exact SHZ.
  - exact SHR.
Qed.

End W.
