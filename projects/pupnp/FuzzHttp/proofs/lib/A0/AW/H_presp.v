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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit HObjA HObjK HObjF HPrepA H_membuffer_assign H_scanner_get_token H_vfm_G H_match_A H_presp_seg.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_snocA : forall m a bs b,
  bytes_at asegs m a bs -> mrd asegs m (wa (a + Z.of_nat (length bs))) = Some b -> a + Z.of_nat (length bs) + 1 <= 2^64 ->
  bytes_at asegs m a (bs ++ [b]).
Proof.
  intros m a bs b (H0 & H1 & HB) RD HI. split; [exact H0|]. rewrite length_app. cbn [length]. split; [lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i (length bs)).
  - rewrite nth_error_app1 by lia. apply HB. lia.
  - assert (i = length bs) by lia. subst i. rewrite nth_error_app2, Nat.sub_diag by lia. cbn. exact RD.
Qed.
Lemma bytes_at_extendA : forall k m a bs,
  bytes_at asegs m a bs ->
  (forall x, a + Z.of_nat (length bs) <= x < a + Z.of_nat (length bs) + Z.of_nat k -> exists v, mrd asegs m (wa x) = Some v) ->
  a + Z.of_nat (length bs) + Z.of_nat k <= 2^64 ->
  exists sl, bytes_at asegs m a (bs ++ sl) /\ length sl = k.
Proof.
  induction k as [|k IH]; intros m a bs B RD HI.
  - exists []. rewrite app_nil_r. split; [exact B| reflexivity].
  - destruct (RD (a + Z.of_nat (length bs)) ltac:(lia)) as [v Hv].
    pose proof (bytes_at_snocA m a bs v B Hv ltac:(lia)) as B1.
    destruct (IH m a (bs ++ [v]) B1) as (sl & B2 & L2).
    + intros x Hx. apply RD. rewrite length_app in Hx. cbn [length] in Hx. lia.
    + rewrite length_app. cbn [length]. lia.
    + exists (v :: sl). rewrite <- app_assoc in B2. cbn [app] in B2. split; [exact B2| cbn; lia].
Qed.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

#[using="Type"] Lemma block_slackA : forall s (LB : BL) m (b : BLK) bs,
  RHEAP_A FI AI s LB m -> In b LB -> bytes_at asegs m (blk_addr b) bs -> Z.of_nat (length bs) = blk_size b ->
  exists sl kE, bytes_at asegs m (blk_addr b + blk_size b) sl /\ Z.of_nat (length sl) <= 7
                /\ blk_addr b + blk_size b + Z.of_nat (length sl) = 8 * kE.
Proof.
  intros s LB m b bs HR HIN B L.
  destruct (am_block_range FI AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (RU : blk_addr b + blk_size b <= round_up8 (blk_addr b + blk_size b) <= blk_addr b + blk_size b + 7) by (unfold round_up8; Z.div_mod_to_equations; lia).
  destruct (bytes_at_extendA (Z.to_nat (round_up8 (blk_addr b + blk_size b) - (blk_addr b + blk_size b))) m (blk_addr b) bs B) as (sl & B2 & L2).
  - intros x Hx. eapply (am_block_slack FI AI); [exact HR| exact HIN| lia].
  - lia.
  - apply bytes_at_app in B2. destruct B2 as [_ B2]. rewrite L in B2.
    exists sl, ((blk_addr b + blk_size b + 7) / 8). split; [exact B2|]. split; [lia|].
    rewrite L2. unfold round_up8 in *. Z.div_mod_to_equations. lia.
Qed.

#[using="AMS"] Lemma stack_shadow_client : forall (LB : BL) q lo' a,
  sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> aclient FI AI LB q a.
Proof.
  intros LB q lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
  apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
Qed.
#[using="AMS"] Lemma shz_apx : forall W (LB : BL) q m m' lo' hi',
  shz m lo' hi' -> apx FI AI W LB q m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shz m' lo' hi'.
Proof.
  intros W LB q m m' lo' hi' Z AP H1 H2 OUT a Ha.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(lia) (stack_shadow_client LB q lo' a H1 ltac:(lia)) (OUT a Ha))) (Z a Ha)).
Qed.
#[using="AMS"] Lemma shr_apx : forall W (LB : BL) q m m' lo' hi',
  shr m lo' hi' -> apx FI AI W LB q m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shr m' lo' hi'.
Proof.
  intros W LB q m m' lo' hi' Z AP H1 H2 OUT a Ha. destruct (Z a Ha) as [v Hv]. exists v.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) (stack_shadow_client LB q lo' a H1 ltac:(lia)) (OUT a Ha))) Hv).
Qed.

#[using="Type"] Lemma apx_stk : forall W (LB : BL) q m m' lo' hi',
  apx FI AI W LB q m m' -> stk asegs m lo' hi' -> aclient_range FI AI LB q lo' (hi' - lo') -> disjoint_from W lo' (hi' - lo') ->
  stk asegs m' lo' hi'.
Proof.
  intros W LB q m m' lo' hi' AP ST HR HD.
  eapply (stk_gagree (fun a => aclient FI AI LB q a /\ outside W a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact ST|].
  intros a Ha. split; [apply HR; lia| eapply disjoint_outside; [exact HD| lia]].
Qed.

Notation ERRNO_A := 0x5e68cc%Z.

Definition presp_WA (P A bn : Z) : list ivl :=
  [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (A, A + bn); (0x5e68cc, 0x5e68d0)]%Z.

Definition p_smsgWA (m : mem) (LB : BL) (P SA slen scap : Z) (sok : option K) (sbs : list byte) : Prop :=
  rw_cells asegs m (P + 232) (mbuf_cells SA slen scap) /\ mownA FI AI m LB SA scap sok sbs /\ 0 <= slen <= scap /\ scap < 2^32.

Definition presp_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LB LBK : BL) (P cur A len cap : Z) (okm : option K) (bs : list byte)
    (SA slen scap : Z) (sok : option K) (sbs : list byte) (rm isreq err hack pos entp clen csz esp lo : Z) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI)
                           (r cur' sc' maj' min' SA' slen' scap' pos' : Z) (sok' : option K) (sbs' : list byte),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st' m' /\ fs_live FI st' = fs_live FI st
    /\ apxF FI AI (presp_WA P A (Z.of_nat (length bs))) LBK q st m m'
    /\ RHEAP_A FI AI s' LB' m'
    /\ ((sok' = sok /\ LB' = LB /\ SA' = SA /\ scap' = scap /\ am_nsec FI AI s' = am_nsec FI AI s)
        \/ (exists k', sok' = Some k' /\ LB' = (k', SA', scap' + 1) :: lb_keepA FI AI sok LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (scap' + 1)))
    /\ p_scan m' P cur' /\ p_msg FI AI m' LB' P A len cap okm bs /\ p_rs m' P rm sc' /\ p_ver m' P isreq maj' min'
    /\ p_smsgWA m' LB' P SA' slen' scap' sok' sbs' /\ p_ctl m' P err hack pos' entp clen csz esp
    /\ (exists ev', rw_cells asegs m' ERRNO_A [C4 ev'])
    /\ shw m' P 504 /\ shz m' (sh lo) (sh q) /\ shr m' (sh lo - sh lo mod 8) (sh q + 8)
    /\ 0 <= r <= 5 /\ cur <= cur' <= len /\ scap' <= scap + slen' + 5
    /\ (r = 4 -> slen' <= len)
    /\ ( (r = 4 /\ pos' = POS_HEADERS_A /\ 0 <= maj' /\ 0 <= min' /\ 0 <= sc' /\ okm <> None)
         \/ (r <> 4 /\ pos' = pos /\ sok' = sok /\ LB' = LB /\ SA' = SA /\ slen' = slen /\ scap' = scap /\ sbs' = sbs /\ am_nsec FI AI s' = am_nsec FI AI s) ).

#[using="AMS"] Lemma heap_W0 : forall s (LB : BL) m m' lo q P A bn,
  RHEAP_A FI AI s LB m -> munch ((lo, q) :: FSIV (presp_WA P A bn))%Z m m' -> wmono asegs m m' ->
  alloc_ceiling <= lo -> FSB FI <= P -> P + 504 <= FSB FI + A0_FS_SIZE ->
  ((A = 0 /\ bn = 0) \/ exists b, In b LB /\ blk_addr b = A /\ blk_size b = bn) ->
  RHEAP_A FI AI s LB m'.
Proof.
  intros s LB m m' lo q P A bn HR MU WM CLO P1 P2 TX.
  assert (ERR : am_static FI AI 0x5e68c8 0x5e68d0) by (apply AMS; unfold a0_static; split; [lia|]; do 4 right; left; lia).
  destruct TX as [[-> ->] | (b & Hb & <- & <-)].
  - eapply (am_heap_frame FI AI s LB m m' ((lo, q) :: FSIV [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (0x5e68cc, 0x5e68d0)])%Z); [exact HR| | exact WM|].
    + eapply munch_weaken; [| exact MU]. intros x Hx. unfold presp_WA. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _). repeat (split; [first [assumption | lia]|]). exact I.
    + apply Forall_cons; [left; exact CLO|]. apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]. apply Forall_cons; [do 4 right; cbn [fst snd]; lia|].
      do 3 (apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]).
      apply Forall_cons; [right; left; exists 0x5e68c8, 0x5e68d0; cbn [fst snd]; split; [exact ERR| unfold a0_wsafe; lia]|]. apply Forall_nil.
  - eapply (am_heap_frame FI AI s LB m m' _ HR MU WM). unfold presp_WA.
    destruct (am_block_range FI AI _ _ _ _ HR Hb) as (_ & _ & B2 & _).
    apply Forall_cons; [left; exact CLO|]. apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]. apply Forall_cons; [do 4 right; cbn [fst snd]; lia|].
    do 3 (apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]).
    apply Forall_cons; [right; right; left; exists b; cbn [fst snd]; split; [exact Hb| lia]|].
    apply Forall_cons; [right; left; exists 0x5e68c8, 0x5e68d0; cbn [fst snd]; split; [exact ERR| unfold a0_wsafe; lia]|]. apply Forall_nil.
Qed.

#[using="Type"] Lemma blk_dj_W0 : forall s (LB : BL) m (b : BLK) lo q P A bn X n,
  RHEAP_A FI AI s LB m -> In b LB -> blk_addr b <= X -> X + n <= blk_addr b + blk_size b ->
  alloc_ceiling <= lo -> FSB FI <= P -> P + 504 <= FSB FI + A0_FS_SIZE ->
  ((A = 0 /\ bn = 0) \/ exists b', In b' LB /\ b' <> b /\ blk_addr b' = A /\ blk_size b' = bn) ->
  disjoint_from ((lo, q) :: FSIV (presp_WA P A bn))%Z X n.
Proof.
  intros s LB m b lo q P A bn X n HR Hb X1 X2 CLO P1 P2 TX.
  destruct (am_block_range FI AI _ _ _ _ HR Hb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (fsb_ok FI) as (F1 & F2 & _ & F4 & F5).
  assert (SHE : sh (FSB FI) + A0_FS_SHSIZE = sh (FSB FI + A0_FS_SIZE)) by (unfold sh, SHADOW_OFF; clear - F4; Z.div_mod_to_equations; lia).
  unfold presp_WA. cbn [disjoint_from].
  split; [left; lia|]. split; [lia|].
  split; [rewrite SHE; unfold sh, SHADOW_OFF; clear - X1 X2 B2 B4 B5 F1 F2 F5 ACR; Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [| split; [lia| exact I]].
  destruct TX as [[-> ->] | (b' & Hb' & NE & <- & <-)]; [lia|].
  destruct (am_blocks_disjoint FI AI s LB m b' b HR Hb' Hb NE); lia.
Qed.

#[using="Type"] Lemma shw_apxF_lb : forall W (LB : BL) q st m m' X n,
  shw m X n -> apxF FI AI W LB q st m m' -> RFAKE FI st m -> lb (fs_live FI st) X n ->
  (forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside W a) -> shw m' X n.
Proof.
  intros W LB q st m m' X n SW AP RF HL OUT.
  eapply (shw_fkeep FI W st m m' X n SW); [exact (apxF_fkeep FI AI W LB q st m m' AP)| exact RF| exact HL| exact OUT].
Qed.
#[using="AMS"] Lemma stack_shadow_fclient : forall (LB : BL) q st lo' a,
  sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> fclient FI AI LB q st a.
Proof.
  intros LB q st lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
  apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
Qed.
#[using="AMS"] Lemma shz_apxF : forall W (LB : BL) q st m m' lo' hi',
  shz m lo' hi' -> apxF FI AI W LB q st m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shz m' lo' hi'.
Proof.
  intros W LB q st m m' lo' hi' Z AP H1 H2 OUT a Ha.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(lia) (stack_shadow_fclient LB q st lo' a H1 ltac:(lia)) (OUT a Ha))) (Z a Ha)).
Qed.
#[using="AMS"] Lemma shr_apxF : forall W (LB : BL) q st m m' lo' hi',
  shr m lo' hi' -> apxF FI AI W LB q st m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shr m' lo' hi'.
Proof.
  intros W LB q st m m' lo' hi' Z AP H1 H2 OUT a Ha. destruct (Z a Ha) as [v Hv]. exists v.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) (stack_shadow_fclient LB q st lo' a H1 ltac:(lia)) (OUT a Ha))) Hv).
Qed.

#[using="Type"] Lemma rw_cells_nil0 : forall m, rw_cells asegs m 0 [CB 0 []].
Proof.
  intros m. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.

Definition presp_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB LBK : BL) (st : fsstate FI)
         (P lo cur A len cap : Z) (okm : option K) (bs : list byte) (SA slen scap : Z) (sok : option K) (sbs : list byte)
         (rm sc isreq maj min err hack pos entp clen csz esp : Z) (ev canary : word),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st (wz A0_TP) 3 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - PRESP_DEPTH_A -> q mod 16 = 0 -> q + 64 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  lb (fs_live FI st) P 504 -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  p_scan m P cur -> p_msg FI AI m LB P A len cap okm bs -> 0 <= cur <= len ->
  p_rs m P rm sc -> p_ver m P isreq maj min -> p_smsg FI AI m LB P SA slen scap sok sbs -> p_ctl m P err hack pos entp clen csz esp ->
  NoDup (map blk_id (okbA FI AI okm A cap ++ okbA FI AI sok SA scap)) -> bsub FI AI LBK (lb_keepA FI AI sok LB) ->
  am_budget_le FI AI s LB (scap + len + 6) ->
  rw_cells asegs m ERRNO_A [C4 ev] ->
  rw_cells asegs m 0xaad68 [C8 (wz 0x6069b0)] -> rw_cells asegs m 0x6069b0 [C8 canary] ->
  shw m SEPTAB_A 20 -> shw m FMT_RESP_A 16 -> shw m FMT_SSCANF_A 11 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  a0 = wz P ->
  AJ FI AI J (presp_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB LBK P cur A len cap okm bs SA slen scap sok sbs
                           rm isreq err hack pos entp clen csz esp lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz presp_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1"] Theorem presp_spec_A : presp_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB LBK st
         P lo cur A len cap okm bs SA slen scap sok sbs rm sc isreq maj min err hack pos entp clen csz esp ev canary.
  intros HR RF FCO AE ST CLO LO QAL QTOP MI PLB PHI PAL SHWP PSC PMSG HCUR PRS PVER PSM PCTL ND KSUB BUD ERRC SSPG SSPC SHWSEP SHWFMT SHWFMT2 SHZ SHR ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  destruct (p_msg_facts FI AI m LB P A len cap okm bs s HR PMSG) as (HL & HCp & LBS0 & NONE & SOME). unfold LMAX_A in HCp.
  destruct (lb_geom FI st m P 504 RF PLB) as [PG1 PG2].
  pose proof (fsb_ok FI) as (FB1 & FB2 & _ & FB4 & FB5).

  assert (TXB : exists (bn kE : Z) (sl : list byte),
     Z.of_nat (length bs) = bn /\ bn >= len /\ bn <= 2^26 + 16
     /\ rw_cells asegs m A [CB (Z.to_nat bn) bs] /\ bytes_at asegs m (A + bn) sl
     /\ (0 < len -> shw m A len) /\ 0 <= A /\ (0 < len -> 0x609000 <= A) /\ A + bn <= alloc_ceiling
     /\ (A + bn <= FSB FI \/ FSB FI + A0_FS_SIZE <= A) /\ (A + bn <= 0x7fff7000 \/ 0x10007fff8000 <= A)
     /\ Z.of_nat (length sl) <= 7 /\ A + bn + Z.of_nat (length sl) <= alloc_ceiling /\ A + bn + Z.of_nat (length sl) = 8 * kE
     /\ ((okm = None /\ A = 0 /\ bn = 0 /\ cap = 0 /\ len = 0) \/ exists k, okm = Some k /\ In (k, A, bn) LB /\ bn = cap + 1)).
  { destruct okm as [k|].
    - destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
      destruct PMSG as (_ & [HIN BLKc] & _).
      pose proof (rw_cells_bytes_at asegs _ _ _ BLKc) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
      destruct (block_slackA s LB m (k, A, cap + 1) bs HR HIN BB ltac:(cbn; lia)) as (sl & kE & SLB & SL7 & SLAL). cbn [blk_addr blk_size fst snd] in SLB, SLAL.
      exists (cap + 1), kE, sl.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BLKc|]. split; [exact SLB|].
      split; [intros _; eapply shw_sub; [exact S4| lia| lia| lia]|]. split; [lia|]. split; [intros _; exact S1|]. split; [lia|].
      split; [exact S5|]. split; [lia|]. split; [exact SL7|]. split; [lia|]. split; [exact SLAL|].
      right. exists k. split; [reflexivity|]. split; [exact HIN| reflexivity].
    - destruct (NONE eq_refl) as (-> & -> & ->). destruct PMSG as (_ & (_ & _ & ->) & _).
      exists 0, 0, []. cbn [length Z.of_nat].
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact (rw_cells_nil0 m)|].
      split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia|].
      split; [intros X; lia|]. split; [lia|]. split; [intros X; lia|]. split; [lia|]. split; [left; lia|]. split; [left; lia|].
      split; [lia|]. split; [lia|]. split; [lia|]. left. repeat split; reflexivity. }
  destruct TXB as (bn & kE & sl & BN & LBS & BNMAX & TXC & SLK & SHWA & ALO & AIMG & ABHI & AFS & ABAND & SL7 & SLHI & SLAL & TXK).

  assert (AL16 : exists kq, q = 16 * kq) by (exists (q / 16); clear - QAL; Z.div_mod_to_equations; lia). destruct AL16 as [kq AL16].
  assert (PAL8 : exists kP, P = 8 * kP) by (exists (P / 8); clear - PAL; Z.div_mod_to_equations; lia). destruct PAL8 as [kP PAL8].
  assert (QHI : q < 2^64) by lia. assert (Q47 : q <= 2^47 - 64) by lia.
  assert (PLO : 6328320 <= P) by lia.
  assert (AHI : A + cap + 1 < 2^63).
  { destruct TXK as [(_ & -> & -> & -> & _)|(k & -> & HIN & ->)]; lia. }
  assert (ABANDf : ABANDd A bn) by (unfold ABANDd; exact ABAND).
  pose proof PSC as SC. unfold p_scan in SC.
  destruct PMSG as (MBC & MOWN & _ & _ & MNUL). unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC.
  destruct PRS as (RSC & RMR & SR). destruct PVER as ((pad & VERC) & ISR & MR & NR).
  destruct PSM as (SMC & SOWN & SLR & SCAPR & SNUL). unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in SMC.
  pose proof SCAPR as SCAPR'. unfold LMAX_A in SCAPR'.
  destruct PCTL as (CTLC & CB1 & CB2 & CB3 & CB4 & CB5 & CB6 & CB7). unfold p_ctl_cells in CTLC.
  assert (PINV : pinvP P A len cap bn bs sl rm isreq err hack pos entp clen csz esp SA slen scap pad m cur sc maj min).
  { unfold pinvP, rinvP. split; [exact SC|]. split; [exact MBC|]. split; [exact TXC|]. split; [exact SLK|].
    split; [exact RSC|]. split; [exact SMC|]. split; [exact VERC|]. split; [exact CTLC|]. exists ev. exact ERRC. }
  pose proof (frontP FI IC STACK_MALLOC_0 STACK_MALLOC_1 P A len cap lo q kq kP bn kE bs sl st rm isreq err hack pos entp clen csz esp SA slen scap
                pad ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m
                CLO LO AL16 QHI RF FCO (am_fsenv FI AI _ _ _ HR) BN LBS BNMAX (proj2 HL) AHI SHWP PLO PHI PAL8 PLB SHWA ALO AIMG ABHI AFS ABANDf SL7 SLHI SLAL
                SHWSEP SHWFMT SHZ SHR Q47 SHWFMT2 eq_refl canary SSPG SSPC
                cur sc maj min t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE PINV HCUR SR MR NR) as FRONT.

  assert (KSUBL : forall b, In b (lb_keepA FI AI sok LB) -> In b LB) by (intros b Hb; exact (lb_keepA_sub FI AI sok LB b Hb)).
  assert (TXK' : (A = 0 /\ bn = 0) \/ exists b : BLK, In b LB /\ blk_addr b = A /\ blk_size b = bn).
  { destruct TXK as [(_ & -> & -> & _)|(k & _ & HIN & _)]; [left; split; reflexivity| right; exists (k, A, bn); split; [exact HIN| split; reflexivity]]. }
  pose proof (H_presp_seg.WP_app FI P A len bn bs sl st m SHWP ALO ABANDf) as WAPP.
  pose proof (H_presp_seg.WP_out FI P A len bn bs sl st m SHWP ALO ABANDf) as WOUT.
  change [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (A, A + bn); (6187208, 6187216)] with (presp_WA P A bn) in WAPP, WOUT.
  assert (SOWN_T : forall m', munch ((lo, q) :: FSIV (presp_WA P A bn))%Z m m' -> wmono asegs m m' -> mownA FI AI m' LB SA scap sok sbs).
  { intros m' MU WM. destruct sok as [ks|]; cbn [mownA] in *; [| exact SOWN]. destruct SOWN as [SIN SCH]. split; [exact SIN|].
    apply (rw_cells_transport asegs _ m m' _ _ SCH MU WM).
    apply (blk_dj_W0 s LB m (ks, SA, scap + 1) lo q P A bn SA _ HR SIN); cbn [blk_addr blk_size fst snd]; [lia| | exact CLO| lia| exact PG2|].
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
    - destruct TXK as [(_ & -> & -> & _)|(k & -> & HIN & ->)]; [left; split; reflexivity| right].
      exists (k, A, cap + 1). split; [exact HIN|]. split; [| split; reflexivity].
      intros E. injection E as E1 _ _. cbn [okbA app map blk_id fst] in ND. inversion ND as [|x l NI ND']. apply NI. rewrite E1. constructor. }
  assert (MOWN_T : forall m', rw_cells asegs m' A [CB (Z.to_nat bn) bs] -> mownA FI AI m' LB A cap okm bs).
  { intros m' TX'. destruct TXK as [(-> & _)|(k & -> & HIN & ->)]; cbn [mownA] in *; [exact MOWN| split; [exact HIN| exact TX']]. }
  assert (LQ : lo <= q) by lia.
  assert (SHQ : sh q + 8 <= 0x10007fff8000) by (pose proof (sh_hi_ok8 q Q47) as X; unfold SH_HI in X; exact X).
  assert (SHL : sh alloc_ceiling - sh alloc_ceiling mod 8 <= sh lo - sh lo mod 8) by (unfold sh, SHADOW_OFF; clear - CLO; Z.div_mod_to_equations; lia).
  assert (SHB : forall a, sh lo - sh lo mod 8 <= a < sh q + 8 -> shband a).
  { intros a Ha. destruct (stack_window_lo FI lo CLO) as [X _]. unfold shband, SH_HI. lia. }
  assert (SLM : sh lo - sh lo mod 8 <= sh lo) by (pose proof (Z.mod_pos_bound (sh lo) 8 ltac:(lia)); lia).
  eapply (aj_evt FI AI J); [exact FRONT|]. clear FRONT.
  intros ms' MID. unfold midP in MID. destruct MID as [EARLY | CALL].
  -
    unfold postB, XEP in EARLY.
    destruct EARLY as (r & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & st' & -> & MU & WM & MI' & FK & LIVE' & RF' & ST' & AE'
                       & (cur' & sc' & maj' & min' & PV & RN4 & RR & CR & S1 & S2 & S3)).
    change [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (A, A + bn); (6187208, 6187216)] with (presp_WA P A bn) in MU, FK.
    destruct PV as (SC' & MBC' & TXC' & SLK' & (RSC' & SMC' & VERC' & CTLC' & (ev' & ERRC'))).
    pose proof (apxF_of_munch_fkeep FI AI ASL s LB (lb_keepA FI AI sok LB) m m q lo st (presp_WA P A bn) m m' HR KSUBL RF CLO LQ MU WM FK) as APF.
    apply (aj_ret FI AI J). unfold presp_post_A.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', st', r, cur', sc', maj', min', SA, slen, scap, pos, sok, sbs.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AE'|]. split; [exact RF'|]. split; [exact LIVE'|].
    split; [rewrite BN; eapply (apxF_weaken FI AI); [exact APF| intros x Hx; exact Hx| lia| exact KSUB| intros g Hg; exact Hg]|].
    split; [exact (heap_W0 s LB m m' lo q P A bn HR MU WM CLO ltac:(lia) PG2 TXK')|].
    split; [left; repeat split; reflexivity|].
    split; [exact SC'|].
    split; [split; [unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; exact MBC'|]; split; [exact (MOWN_T m' TXC')|]; split; [exact HL|]; split; [unfold LMAX_A; exact HCp| exact MNUL]|].
    split; [split; [exact RSC'|]; split; [exact RMR| exact S1]|].
    split; [split; [exists pad; exact VERC'|]; split; [exact ISR|]; split; [exact S2| exact S3]|].
    split; [split; [unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; exact SMC'|]; split; [exact (SOWN_T m' MU WM)|]; split; [exact SLR| unfold LMAX_A in SCAPR; lia]|].
    split; [split; [unfold p_ctl_cells; exact CTLC'| repeat (split; [assumption|]); assumption]|].
    split; [exists ev'; exact ERRC'|].
    split; [exact (shw_apxF_lb _ _ q st m m' P 504 SHWP APF RF PLB WOUT)|].
    split; [apply (shz_apxF _ _ q st m m' _ _ SHZ APF); [lia| lia| intros a Ha; apply (app_ivs_outside _ a WAPP); apply SHB; lia]|].
    split; [apply (shr_apxF _ _ q st m m' _ _ SHR APF); [lia| lia| intros a Ha; apply (app_ivs_outside _ a WAPP); apply SHB; lia]|].
    split; [exact RR|]. split; [exact CR|]. split; [clear - SLR; lia|]. split; [intros R4; exfalso; exact (RN4 R4)|]. right. repeat (split; [first [assumption | reflexivity]|]). reflexivity.

  -
    destruct CALL as (q' & t' & o & l & cur' & sc' & maj' & min' & tyw & tw1 & tw2 & bcr & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1
                      & -> & MV & PV & O0 & OT & TL & OL & CL & CC & S1 & S2 & S3).
    unfold callstP.
    pose proof MV as MV'. unfold minvP, minvB in MV'.
    destruct MV' as ((kq' & Hq32) & Hq & ST1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & MU1 & WM1 & FK1 & AE1 & (stc & RF1 & LIVE1)).
    change [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (A, A + bn); (6187208, 6187216)] with (presp_WA P A bn) in MU1, FK1.
    pose proof PV as PV'. destruct PV' as (SC1 & MBC1 & TXC1 & SLK1 & (RSC1 & SMC1 & VERC1 & CTLC1 & (ev1 & ERRC1))).
    pose proof (heap_W0 s LB m m1 lo q P A bn HR MU1 WM1 CLO ltac:(lia) PG2 TXK') as HR1.
    pose proof (apxF_of_munch_fkeep FI AI ASL s LB (lb_keepA FI AI sok LB) m m q lo st (presp_WA P A bn) m m1 HR KSUBL RF CLO LQ MU1 WM1 FK1) as APF1.
    destruct TXK as [(_ & _ & _ & _ & L0)|(k & EK & HIN & EBN)]; [exfalso; lia|].
    assert (KIN : In (k, A, bn) (lb_keepA FI AI sok LB)).
    { destruct sok as [ks|]; cbn [lb_keepA]; [| exact HIN]. apply (lb_remove_In FI AI ks LB _ HIN). cbn [blk_id fst]. intros E.
      rewrite EK in ND. cbn [okbA app map blk_id fst] in ND. inversion ND as [|x l0 NI ND']. apply NI. rewrite E. constructor. }
    destruct (H_presp_seg.liveP FI P len bs sl st m RF PLB stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
    remember (l - (t' - o)) as n eqn:En.
    assert (N0 : 0 <= n <= len) by lia.
    pose proof (text_bytes A bn bs m1 TXC1) as BUF1.
    assert (LBSn : length bs = Z.to_nat bn) by lia.
    rewrite <- (firstn_skipn (Z.to_nat t') bs) in BUF1. apply bytes_at_app in BUF1. destruct BUF1 as [_ BUF1].
    rewrite firstn_length_le in BUF1 by lia. replace (A + Z.of_nat (Z.to_nat t')) with (A + t') in BUF1 by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat t') bs)) in BUF1. apply bytes_at_app in BUF1. destruct BUF1 as [BSRC _].
    assert (LSRC : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat t') bs))) = n) by (rewrite firstn_length_le by (rewrite length_skipn; lia); lia).
    pose proof (AIMG ltac:(lia)) as AIMGu.
    eapply (aj_bind FI AI J).
    { eapply (membuffer_assign_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (st := stc) (ok := sok) (MB := P + 232) (SRC := A + t') (n := n)
                                                                 (A := SA) (len := slen) (cap := scap) (bs := sbs) (LB := LB)
                                                                 (src := firstn (Z.to_nat n) (skipn (Z.to_nat t') bs)).
      - exact HR1.
      - exact RF1.
      - exact AE1.
      - exact ST1.
      - exact CLO.
      - unfold A0_RT_STACK. lia.
      - clear - Hq32. Z.div_mod_to_equations. lia.
      - lia.
      - exact MI1.
      - unfold mbuf_cells, MEMBUF_DEF_SIZE_INC. exact SMC1.
      - exact SLR.
      - lia.
      - apply (am_budget_le_mono FI AI s LB _ _ BUD). lia.
      - exact (SOWN_T m1 MU1 WM1).
      - right; right. apply (lb_sub _ P 504 _ _ PLB1); lia.
      - lia.
      - clear - PAL. Z.div_mod_to_equations. lia.
      - eapply shw_sub; [exact (shw_apxF_lb _ _ q st m m1 P 504 SHWP APF1 RF PLB WOUT)| lia| lia| lia].
      - exact BSRC.
      - exact LSRC.
      - lia.
      - left. right; left. exists (k, A, bn). split; [exact KIN|]. cbn [blk_addr blk_size fst snd]. lia.
      - apply (block_shw FI AI s LB m1 (k, A, bn) (A + t') n HR1 HIN); cbn [blk_addr blk_size fst snd]; lia.
      -   destruct (am_block_range FI AI s LB m1 _ HR1 HIN) as (R1 & R2 & R3 & R4 & R5 & _); cbn [blk_addr blk_size fst snd] in *.
        pose proof alloc_ceiling_range as ACRx. unfold alloc_floor, alloc_ceiling_max in ACRx. lia.
      - clear - AFS PG1 PG2 N0 OT TL OL CL LBS O0 En. lia.
      - reflexivity.
      - reflexivity.
      - reflexivity. }

    intros sx LB2 ms2 PO. unfold membuffer_assign_post_A in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & A' & cap' & ok' & bs'
                    & -> & MI2 & ST2 & AE2 & RF2 & APX & HR2 & LBALT & SMC2 & NC & CC' & SOWN2 & SNUL2).
    replace (P + 232 + 32) with (P + 264) in APX by lia.

    pose proof (minvB_apx FI P A lo q bn bs sl st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m CLO LO RF PHI PLB AI (lb_keepA FI AI sok LB)
                  m q' m1 m2 tyw tw1 tw2 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l) stc MV APX ST2 MI2 AE2 RF2 LIVE1) as MV2.
    assert (ACT : aclient_range FI AI (lb_keepA FI AI sok LB) q' A bn).
    { apply (aclient_range_block FI AI _ q' A bn (k, A, bn) KIN); cbn [blk_addr blk_size fst snd]; lia. }
    assert (ACE : aclient_range FI AI (lb_keepA FI AI sok LB) q' 6187212 4).
    { apply (aclient_range_static FI AI _ q' 6187212 4 0x5e68c8 0x5e68d0); [| lia| lia]. apply AMS. unfold a0_static. split; [lia|]. do 4 right; left. lia. }
    destruct (pinv_apx FI P A len cap len bn bs sl st rm isreq err hack pos entp clen csz esp SA slen scap pad m RF BN PLB AFS AI (lb_keepA FI AI sok LB)
                q' m1 m2 cur' sc' maj' min' PV APX ACT ACE) as [LR2 CT2].

    assert (SUBW : sub_fp [(P + 232, P + 264)]%Z (presp_WA P A bn)).
    { intros x Hx. unfold presp_WA in Hx. cbn [outside] in *. split; [| exact I]. destruct Hx as (H1 & _). lia. }
    pose proof (apxF_of_apx FI AI _ (lb_keepA FI AI sok LB) (lb_keepA FI AI sok LB) q q' st stc m2 m1 m2 APX RF2 ltac:(lia) (fun b H => H) LSUB) as APF12.
    pose proof (apxF_trans FI AI _ _ q st m m1 m2 APF1
                  (apxF_weaken FI AI _ _ _ _ q q st st m1 m2 APF12 SUBW ltac:(lia) (fun b H => H) (fun g H => H))) as APF02.
    pose proof (shw_apxF_lb _ _ q st m m2 P 504 SHWP APF02 RF PLB WOUT) as SHWP2.

    assert (LB2IN : forall b, In b (lb_keepA FI AI sok LB) -> In b LB2).
    { intros b Hb. destruct LBALT as [(_ & -> & _)|(k' & _ & -> & _)]; [exact (KSUBL b Hb)| right; exact Hb]. }
    pose (R := fun mm : mem => lateR P A len cap bn bs rm isreq pad mm cur' sc' maj' min'
                               /\ rw_cells asegs mm (P + 232) (mbuf_cells A' n cap') /\ mownA FI AI mm LB2 A' cap' ok' bs').
    assert (RFR : rframeL FI P lo q st R).
    { intros ma mb (LRa & SMCa & SOWNa) MUx WMx. unfold R. split; [| split].
      - exact (lateR_rframe FI P A len cap lo q bn bs sl st rm isreq pad m CLO RF BN PHI PLB ABHI AFS ABANDf cur' sc' maj' min' ma mb LRa MUx WMx).
      - apply (rw_cells_transport asegs _ ma mb _ _ SMCa MUx WMx).
        apply (WLP_dj_P FI P lo q bs sl st m CLO RF PHI PLB); unfold mbuf_cells; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      - destruct ok' as [k''|]; cbn [mownA] in *; [| exact SOWNa]. destruct SOWNa as [SIN SCH]. split; [exact SIN|].
        apply (rw_cells_transport asegs _ ma mb _ _ SCH MUx WMx).
        destruct (am_block_range FI AI _ _ _ _ HR2 SIN) as (B0 & B1 & B2 & B3 & B4 & B5 & B6). cbn [blk_addr blk_size fst snd] in B0, B1, B2, B3, B4, B5, B6.
        cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        apply (WLP_dj_out FI P lo q bs sl st m CLO RF PLB); lia. }
    replace (ret_pc (Z_to_bv 64 556564)) with (Z_to_bv 64 556564) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (aj_evt FI AI J).
    { eapply (lateP FI P A lo q kq kP bn bs sl st err hack pos entp clen csz esp ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m
                CLO LO AL16 RF PLO PHI PAL8 PLB m2 R q' m2 tyw tw1 tw2 (Z_to_bv 64 (A + o)) (Z_to_bv 64 l));
        [exact MV2| exact CT2| exact SHWP2| | exact RFR].
      unfold R. split; [exact LR2|]. split; [exact SMC2| exact SOWN2]. }

    intros ms3 PO3. unfold postB in PO3.
    destruct PO3 as (r & w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & st3 & -> & MU3 & WM3 & MI3 & FK3 & LIVE3 & RF3 & ST3 & AE3
                     & (-> & CT3 & (LR3 & SMC3 & SOWN3))).
    change [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (A, A + bn); (6187208, 6187216)] with (presp_WA P A bn) in MU3, FK3.
    destruct LR3 as (SC3 & MBC3 & TXC3 & RSC3 & VERC3 & (ev3 & ERRC3)).
    assert (TXK2 : (A = 0 /\ bn = 0) \/ exists b : BLK, In b LB2 /\ blk_addr b = A /\ blk_size b = bn).
    { right. exists (k, A, bn). split; [apply LB2IN; exact KIN| split; reflexivity]. }
    pose proof (apxF_of_munch_fkeep FI AI ASL sx LB2 (lb_keepA FI AI sok LB) m2 m q lo st (presp_WA P A bn) m2 m3 HR2 LB2IN RF CLO LQ MU3 WM3 FK3) as APF23.
    pose proof (apxF_trans FI AI _ _ q st m m2 m3 APF02 APF23) as APF03.
    apply (aj_ret FI AI J). unfold presp_post_A.
    exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m3, st3, 4, cur', sc', maj', min', A', n, cap', 2, ok', bs'.
    split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|]. split; [exact RF3|]. split; [exact LIVE3|].
    split; [rewrite BN; eapply (apxF_weaken FI AI); [exact APF03| intros x Hx; exact Hx| lia| exact KSUB| intros g Hg; exact Hg]|].
    split; [exact (heap_W0 sx LB2 m2 m3 lo q P A bn HR2 MU3 WM3 CLO ltac:(lia) PG2 TXK2)|].
    split; [exact LBALT|].
    split; [exact SC3|].
    split; [split; [unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; exact MBC3|]; split; [rewrite EK; cbn [mownA]; split; [rewrite <- EBN; apply LB2IN; exact KIN| rewrite <- EBN; exact TXC3]|];
            split; [exact HL|]; split; [unfold LMAX_A; exact HCp| exact MNUL]|].
    split; [split; [exact RSC3|]; split; [exact RMR| lia]|].
    split; [split; [exists pad; exact VERC3|]; split; [exact ISR|]; split; lia|].
    split; [split; [exact SMC3|]; split; [exact SOWN3|]; split; [lia| unfold LMAX_A in SCAPR; lia]|].
    split; [split; [unfold p_ctl_cells; exact CT3|]; split; [exact CB1|]; split; [exact CB2|]; split; [lia|]; split; [exact CB4|]; split; [exact CB5|]; split; [exact CB6| exact CB7]|].
    split; [exists ev3; exact ERRC3|].
    split; [exact (shw_apxF_lb _ _ q st m m3 P 504 SHWP APF03 RF PLB WOUT)|].
    split; [apply (shz_apxF _ _ q st m m3 _ _ SHZ APF03); [lia| lia| intros a Ha; apply (app_ivs_outside _ a WAPP); apply SHB; lia]|].
    split; [apply (shr_apxF _ _ q st m m3 _ _ SHR APF03); [lia| lia| intros a Ha; apply (app_ivs_outside _ a WAPP); apply SHB; lia]|].
    split; [lia|]. split; [lia|]. split; [exact CC'|]. split; [intros _; clear - N0; lia|].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. rewrite EK. discriminate.
Qed.

End W.
