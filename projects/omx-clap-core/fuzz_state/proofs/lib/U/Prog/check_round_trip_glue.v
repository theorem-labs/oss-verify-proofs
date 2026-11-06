(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths and module names changed; 345 of its 429 lines of code are new or changed and 1702 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSlots AllocRoom KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger HStateRoom ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB check_reject_clean_starved past_nul.
Import ListNotations.
Local Open Scope Z_scope.


Section CS.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Definition cs (spc K : Z) (E : Z -> Prop) (G : Z -> Z -> Prop) (L : layout) (A : astate)
    (mem : word -> option byte) (md : Model) (L' : layout) (A' : astate) (mem' : word -> option byte)
    (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  (forall p n, In (p, n) (user_blocks A) -> ~ G (ptr_addr L p) n -> In (p, n) (user_blocks A')) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
     ~ (spc - K <= a < spc) -> ~ (errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) -> mbyte (ms_segs B) mem' (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) /\
  (forall a, (spc - K <= a < spc) \/ (errno_addr B <= a < errno_addr B + 4) -> writable_at (ms_segs B) mem' a).

Lemma cs_of_post : YL01.AllocExtra B MR -> ctx_owned B API ->
  forall K L A regs mem md E L' A' regs' mem' md' g,
  MR L A mem md -> call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  (length (st_regions A) <= length (st_regions A'))%nat -> (st_init_done A = true -> st_init_done A' = true) ->
  ublocks_kept L A A' g ->
  cs (spZ regs) K E (fun a n => (a, n) = g) L A mem md L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros AX CO K L A regs mem md E L' A' regs' mem' md' g HM
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HL HI HU.
  split; [|exact H6].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact HL|].
  split; [exact HI|]. split; [exact H5|]. split; [intros p n Hp Hg; exact (HU p n Hp Hg)|].
  split; [exact H7|].
  split.
  { intros a Ha Ho Hw He Hx. apply H8; [exact Ha | exact Ho | | | exact Hx].
    - exact (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md L' A' mem' md' a HM H1 Ha Ho).
    - unfold scratch_k. tauto. }
  split; [intros p n i Hp Hp' Hi _; exact (H9 p n i Hp Hp' Hi)|].
  intros a Ha. apply H10. exact Ha.
Qed.

Lemma cs_of_rpost : YL01.AllocExtra B MR -> ctx_owned B API ->
  forall K L A regs mem md E gone L' A' regs' mem' md',
  MR L A mem md -> rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  cs (spZ regs) K E gone L A mem md L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros AX CO K L A regs mem md E gone L' A' regs' mem' md' HM
    (H1 & H2 & H3 & H4 & H5 & _ & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  split; [|exact H10].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H7|].
  split; [exact H5|]. split; [exact H9|]. split; [exact H8|]. split; [exact H11|].
  split.
  { intros a [Ha|Ha] Ho Hw Hr He.
    - apply H12; [exact Ha | unfold scratch_k; tauto | exact He].
    - apply H13; [exact Ha | | unfold scratch_k; tauto | exact He].
      intros L0 A0 mem0 md0 HM0.
      exact (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md L0 A0 mem0 md0 a HM HM0
        (or_intror Ha) Ho). }
  split; [exact H14|].
  intros a Ha. apply H15. exact Ha.
Qed.

Lemma cs_seq : YL01.AllocExtra B MR -> ctx_owned B API ->
  forall K sp L A mem md L1 A1 mem1 md1 sp2 K2 E2 G L2 A2 mem2 md2,
  MR L A mem md ->
  kb_mid B API K sp L A mem md alloc_statics L1 A1 mem1 md1 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> ublocks_kept L A A1 (0, 0) ->
  cs sp2 K2 E2 G L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling + K <= sp -> sp <= 2 ^ 64 ->
  (forall p n, In (p, n) (user_blocks A) -> ~ G (ptr_addr L p) n) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ E2 (ptr_addr L p + i)) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (sp - K <= a < sp) -> E2 a -> alloc_statics a) ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> E2 a \/ ~ E2 a) ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> E2 a -> writable_at (ms_segs B) mem2 a) ->
  kb_mid B API K sp L A mem md alloc_statics L2 A2 mem2 md2 /\
  (length (st_regions A) <= length (st_regions A2))%nat /\ ublocks_kept L A A2 (0, 0).
Proof.
  intros AX CO K sp L A mem md L1 A1 mem1 md1 sp2 K2 E2 G L2 A2 mem2 md2 HM
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1) HLEN HUB
    (M2 & W2 & B2 & Y2 & LEN2 & _ & P2 & U2 & D2 & F2 & K2' & S2) H1 H2 H3 H4 HG HE HEs HDE HEw.
  pose proof alloc_ceiling_val as Hc.
  assert (UB2 : ublocks_kept L A A2 (0, 0)).
  { intros p n Hp Hne. pose proof (HUB p n Hp Hne) as Hp1. apply (U2 p n Hp1).
    rewrite (P1 p n Hp Hp1). exact (HG p n Hp). }
  assert (HU : forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1)).
  { intros p n Hp. apply (HUB p n Hp). intros Ex. injection Ex as E1 _.
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp). lia. }
  split; [|split; [lia | exact UB2]].
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split; [exact (check_reject_clean_starved.crs_layout_trans A A1 L L1 L2 Y1 Y2 HLEN)|].
  split; [intros p n Hp Hp2; pose proof (HU p n Hp) as Hp1; rewrite (P2 p n Hp1 Hp2); exact (P1 p n Hp Hp1)|].
  split; [destruct D1 as (vm1 & ->); destruct D2 as (vm2 & ->); exists vm2; reflexivity|].
  split.
  { intros a Ha Ho Ho2 Hs He.
    pose proof (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md L1 A1 mem1 md1 a HM M1 Ha Ho) as Ho1.
    destruct (F1 a Ha Ho Ho1 Hs He) as [E1a E1w].
    assert (He2 : ~ E2 a) by (intros X; apply He; apply (HEs a Ha); [intros Y; apply Hs; left; exact Y | exact X]).
    destruct (F2 a Ha Ho1 ltac:(intros X; apply Hs; left; lia) ltac:(intros X; apply Hs; right; exact X) He2)
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp2 Hi. pose proof (HU p n Hp) as Hp1.
    rewrite <- (P1 p n Hp Hp1). rewrite (K2' p n i Hp1 Hp2 Hi). 
    - rewrite (P1 p n Hp Hp1). exact (K1 p n i Hp Hp1 Hi).
    - rewrite (P1 p n Hp Hp1). exact (HE p n i Hp Hi). }
  intros a Ha.
  assert (Hd : (sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4) \/
               ~ ((sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4))) by lia.
  destruct Hd as [Hd|[Hd|Hd]]; [apply S2; left; exact Hd | apply S2; right; exact Hd |].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hd; right; exact Ha].
  destruct (HDE a Ha ltac:(tauto)) as [He|He].
  - apply HEw; [exact Ha | intros X; apply Hd; left; exact X | exact He].
  - assert (No1 : ~ owned B L1 A1 a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho); lia).
    apply (proj2 (F2 a ltac:(left; lia) No1 ltac:(tauto) ltac:(tauto) He)). apply S1. left. exact Ha.
Qed.

End CS.

Lemma crt_bytes_keep : forall (m m' : word -> option byte) a bs, Mem.bytes_at rsegs m a bs ->
  (forall i, a <= i < a + Z.of_nat (length bs) -> mbyte rsegs m' i = mbyte rsegs m i) ->
  Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) K. split; [exact H1|]. split; [exact H2|].
  intros i Hi. specialize (K (a + Z.of_nat i) ltac:(lia)).
  change (Mem.mrd rsegs m' (Mem.wa (a + Z.of_nat i))) with (mbyte rsegs m' (a + Z.of_nat i)). rewrite K. exact (H i Hi).
Qed.

Lemma crt_pw_two : forall {X : Type} (R : X -> X -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y ->
  R x y \/ R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  destruct H as [Hz H]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y H Hx Hy Hne).
Qed.

Definition crt_cells (regs : bvmap 5 word) : list cell :=
  [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22);
   C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)].

Section E.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis CO : ctx_owned B API.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : call_pre_k B MR CRT_STK L A regs mem md.

Definition GI (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
  kb_mid B API CRT_STK (spZ regs) L A mem md alloc_statics Lc Ac memc mdc /\
  (length (st_regions A) <= length (st_regions Ac))%nat /\ ublocks_kept L A Ac (0, 0) /\
  st_init_done Ac = true /\ ro_agree rsegs memc /\ guard_kept B mem memc /\
  Step.rw_cells rsegs memc (spZ regs - 104) (crt_cells regs).

Lemma crt_sp : alloc_ceiling + 14592 <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0.
Proof. pose proof PRE as (_ & _ & _ & _ & H16 & HAC & H63 & _). unfold CRT_STK, ALLOC_STACK in HAC. lia. Qed.

Lemma crt_IL : img_low B.
Proof.
  pose proof alloc_ceiling_val.
  apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia].
Qed.

Lemma crt_GS : forall x, alloc_statics x -> in_img B x /\ 0 <= x < alloc_ceiling.
Proof.
  intros x Hx.
  assert (Hg : in_globals [(G_FAIL, 8); (G_LIVE, 24)] x).
  { unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. unfold in_globals, G_LIVE, G_FAIL.
    destruct Hx as [Hx|[Hx|[Hx|Hx]]];
      [exists 0x33b40, 24 | exists 0x33b40, 24 | exists 0x33b40, 24 | exists 0x238c8, 8];
      (split; [cbn; tauto | lia]). }
  destruct (GF x Hg) as (Hi & Hr & _). split; [exact Hi | exact Hr].
Qed.

Lemma crt_blk : forall Lc Ac memc mdc p n i, MR Lc Ac memc mdc -> In (p, n) (blocks Lc Ac) -> 0 <= i < n ->
  4096 <= p + i < alloc_ceiling /\ ~ in_img B (p + i) /\ ~ owned B Lc Ac (p + i) /\ ~ alloc_statics (p + i).
Proof.
  intros Lc Ac memc mdc p n i HM Hin Hi. destruct (HsKindB.in_blocks Lc Ac p n Hin) as (q & Hq & ->).
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i HM Hq Hi) as (_ & R1 & R2 & NO).
  pose proof (YL01.ax_blocks_img AX Lc Ac memc mdc q n i HM Hq Hi) as NI.
  split; [lia|]. split; [exact NI|]. split; [exact NO|]. intros Hs. exact (NI (proj1 (crt_GS _ Hs))).
Qed.

Lemma crt_blk_disj : forall Lc Ac memc mdc p n p' n' x, MR Lc Ac memc mdc ->
  In (p, n) (blocks Lc Ac) -> In (p', n') (blocks Lc Ac) -> (p, n) <> (p', n') ->
  p <= x < p + n -> ~ (p' <= x < p' + n').
Proof.
  intros Lc Ac memc mdc p n p' n' x HM H1 H2 Hne Hx Hx'.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as DJ.
  destruct (crt_pw_two _ _ _ _ DJ H1 H2 Hne) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

Lemma gi_call : forall Lc Ac memc mdc K E G Lc' Ac' memc' mdc',
  GI Lc Ac memc mdc -> cs B API (spZ regs - 352) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  ro_agree rsegs memc' -> guard_kept B memc memc' -> 0 <= K -> K + 352 <= CRT_STK ->
  (forall p n, In (p, n) (blocks L A) -> ~ G p n) ->
  (forall p n x, In (p, n) (blocks L A) -> p <= x < p + n -> ~ E x) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (spZ regs - CRT_STK <= a < spZ regs) -> E a ->
     alloc_statics a) ->
  (forall a, spZ regs - CRT_STK <= a < spZ regs -> ~ (spZ regs - 352 - K <= a < spZ regs - 352) -> E a ->
     spZ regs - 352 <= a < spZ regs - 104 /\ mbyte rsegs memc' a <> None) ->
  (forall a, spZ regs - 352 <= a < spZ regs - 104 -> E a \/ ~ E a) ->
  GI Lc' Ac' memc' mdc'.
Proof.
  intros Lc Ac memc mdc K E G Lc' Ac' memc' mdc' (MID & LEN & UB & INI & RA & GK & FR) CS RA' GK' HK HK2 HG HE HEs HEw HDE.
  pose proof PRE as (HM & _). pose proof crt_sp as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof MID as (HMc & _).
  pose proof CS as (HM' & _ & _ & _ & _ & HINI & _ & _ & _ & HF & _).
  unfold CRT_STK, ALLOC_STACK in *.
  assert (HI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 352 - K <= a < spZ regs - 352) -> ~ E a ->
     mbyte (ms_segs B) memc' a = mbyte (ms_segs B) memc a /\
     (writable_at (ms_segs B) memc a <-> writable_at (ms_segs B) memc' a)).
  { intros a Ha Hn He. apply HF; [left; exact Ha | | exact Hn | lia | exact He].
    intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HMc Ho). lia. }
  destruct (cs_seq B API AX CO 14592 (spZ regs) L A mem md Lc Ac memc mdc (spZ regs - 352) K E G Lc' Ac' memc' mdc'
    HM MID LEN UB CS) as (MID' & LEN' & UB').
  - lia.
  - lia.
  - lia.
  - lia.
  - intros p n Hp. apply HG. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp].
  - intros p n i Hp Hi. apply (HE (ptr_addr L p) n); [|lia].
    unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp].
  - exact HEs.
  - intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs - 352)) as [Hl|Hl].
    + right. intros He. pose proof (HEw a ltac:(lia) Hn He). lia.
    + destruct (Z_lt_le_dec a (spZ regs - 104)) as [Hl2|Hl2]; [exact (HDE a ltac:(lia))|].
      right. intros He. pose proof (HEw a ltac:(lia) Hn He). lia.
  - intros a Ha Hn He. destruct (HEw a Ha Hn He) as [_ Hs]. rewrite SEG.
    apply (proj2 (check_reject_clean_starved.crs_wr_hi memc' a ltac:(lia))). exact Hs.
  - split; [exact MID'|]. split; [exact LEN'|]. split; [exact UB'|]. split; [exact (HINI INI)|]. split; [exact RA'|].
    split; [intros i Hi; rewrite (GK' i Hi); exact (GK i Hi)|].
    apply (HsKindB.rw_cells_keep memc memc' _ _ FR). intros a Ha. cbn [crt_cells cells_size csize Nat.add] in Ha.
    rewrite <- SEG. apply HI; [lia | lia |]. intros He. pose proof (HEw a ltac:(lia) ltac:(lia) He). lia.
Qed.

Lemma crt_GS2 : forall x, alloc_statics x -> in_img B x /\ 0 <= x < alloc_ceiling /\
  ~ (errno_addr B <= x < errno_addr B + 4) /\
  forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 ->
    ~ owned B L0 A0 x /\ forall p n, In (p, n) (blocks L0 A0) -> ~ (p <= x < p + n).
Proof.
  intros x Hx.
  assert (Hg : in_globals [(G_FAIL, 8); (G_LIVE, 24)] x).
  { unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. unfold in_globals, G_LIVE, G_FAIL.
    destruct Hx as [Hx|[Hx|[Hx|Hx]]];
      [exists 0x33b40, 24 | exists 0x33b40, 24 | exists 0x33b40, 24 | exists 0x238c8, 8];
      (split; [cbn; tauto | lia]). }
  destruct (GF x Hg) as (Hi & Hr & _ & He & Ho). split; [exact Hi|]. split; [exact Hr|]. split; [exact He|].
  exact Ho.
Qed.

Lemma crt_mid_W : forall K sp L0 A0 mem0 md0 (E E' : Z -> Prop) L' A' mem' md',
  kb_mid B API K sp L0 A0 mem0 md0 E L' A' mem' md' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (sp - K <= a < sp) -> E a -> E' a) ->
  kb_mid B API K sp L0 A0 mem0 md0 E' L' A' mem' md'.
Proof.
  intros K sp L0 A0 mem0 md0 E E' L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He'. apply H8; [exact Ha | exact Ho | exact Ho' | exact Hs |].
  intros He. apply He'. apply HE; [exact Ha | intros Hx; apply Hs; left; exact Hx | exact He].
Qed.

Lemma gi_entry_blk : forall Lc Ac memc mdc p n, GI Lc Ac memc mdc -> In (p, n) (blocks L A) ->
  In (p, n) (blocks Lc Ac).
Proof.
  intros Lc Ac memc mdc p n (MID & _ & UB & _) Hin.
  pose proof PRE as (HM & _). pose proof MID as (_ & _ & _ & _ & PA & _).
  destruct (HsKindB.in_blocks L A p n Hin) as (q & Hq & ->).
  assert (Hq' : In (q, n) (user_blocks Ac)).
  { apply (UB q n Hq). intros Ex. injection Ex as E1 _.
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq). lia. }
  unfold blocks. apply in_map_iff. exists (q, n). split; [cbn [fst snd]; rewrite (PA q n Hq Hq'); reflexivity | exact Hq'].
Qed.

Definition NBok (Lc : layout) (Ac : astate) (NB : list (Z * Z)) : Prop :=
  incl NB (blocks Lc Ac) /\ NoDup NB /\ (forall y, In y NB -> ~ In y (blocks L A)).

Lemma nb_entry : forall Lc Ac memc mdc NB y p n x, GI Lc Ac memc mdc -> NBok Lc Ac NB -> In y NB ->
  In (p, n) (blocks L A) -> fst y <= x < fst y + snd y -> ~ (p <= x < p + n).
Proof.
  intros Lc Ac memc mdc NB [a k] p n x GIc (INC & _ & NE) Hy Hp Hx. cbn [fst snd] in Hx.
  pose proof GIc as ((HMc & _) & _).
  apply (crt_blk_disj Lc Ac memc mdc a k p n x HMc (INC _ Hy) (gi_entry_blk Lc Ac memc mdc p n GIc Hp)); [|exact Hx].
  intros Eq. apply (NE _ Hy). rewrite Eq. exact Hp.
Qed.

Lemma cs_hi : forall spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' a,
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> MR Lc Ac memc mdc ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (spc - K <= a < spc) -> ~ E a ->
  mbyte rsegs memc' a = mbyte rsegs memc a /\ (writable_at rsegs memc a <-> writable_at rsegs memc' a).
Proof.
  intros spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' a CS HMc Ha Hw He.
  pose proof CS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  rewrite <- SEG. apply HF; [left; exact Ha | | exact Hw | lia | exact He].
  intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HMc Ho). lia.
Qed.

Lemma cs_bytes_hi : forall spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' x bs,
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> MR Lc Ac memc mdc -> Mem.bytes_at rsegs memc x bs ->
  (forall i, x <= i < x + Z.of_nat (length bs) -> alloc_ceiling <= i /\ ~ (spc - K <= i < spc) /\ ~ E i) ->
  Mem.bytes_at rsegs memc' x bs.
Proof.
  intros spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' x bs CS HMc HB H.
  apply (crt_bytes_keep memc memc' x bs HB). intros i Hi. pose proof HB as (_ & Hb & _).
  destruct (H i Hi) as (H1 & H2 & H3). exact (proj1 (cs_hi _ _ _ _ _ _ _ _ _ _ _ _ i CS HMc ltac:(lia) H2 H3)).
Qed.

Lemma cs_rw_hi : forall spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' x cl,
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> MR Lc Ac memc mdc -> Step.rw_cells rsegs memc x cl ->
  (forall i, x <= i < x + Z.of_nat (cells_size cl) -> alloc_ceiling <= i /\ ~ (spc - K <= i < spc) /\ ~ E i) ->
  Step.rw_cells rsegs memc' x cl.
Proof.
  intros spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' x cl CS HMc RW H.
  pose proof (Step.rw_cells_bound rsegs memc x cl RW) as RB.
  apply (HsKindB.rw_cells_keep memc memc' x cl RW). intros i Hi.
  destruct (H i Hi) as (H1 & H2 & H3). exact (cs_hi _ _ _ _ _ _ _ _ _ _ _ _ i CS HMc ltac:(lia) H2 H3).
Qed.

Lemma cs_blk : forall spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' p n,
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> In (p, n) (blocks Lc Ac) -> ~ G p n ->
  In (p, n) (blocks Lc' Ac') /\ (forall x, p <= x < p + n -> ~ E x -> mbyte rsegs memc' x = mbyte rsegs memc x).
Proof.
  intros spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' p n CS Hin Hg.
  pose proof CS as (_ & _ & _ & _ & _ & _ & PA & UK & _ & _ & KB & _).
  destruct (HsKindB.in_blocks Lc Ac p n Hin) as (q & Hq & ->).
  pose proof (UK q n Hq Hg) as Hq'.
  split.
  - unfold blocks. apply in_map_iff. exists (q, n). split; [cbn [fst snd]; rewrite (PA q n Hq Hq'); reflexivity | exact Hq'].
  - intros x Hx He. rewrite <- SEG. replace x with (ptr_addr Lc q + (x - ptr_addr Lc q)) by lia.
    apply (KB q n (x - ptr_addr Lc q) Hq Hq'); [lia|]. replace (ptr_addr Lc q + (x - ptr_addr Lc q)) with x by lia.
    exact He.
Qed.

Lemma cs_bytes_blk : forall spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' p n x bs,
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> In (p, n) (blocks Lc Ac) -> ~ G p n ->
  Mem.bytes_at rsegs memc x bs -> p <= x -> x + Z.of_nat (length bs) <= p + n ->
  (forall i, x <= i < x + Z.of_nat (length bs) -> ~ E i) ->
  Mem.bytes_at rsegs memc' x bs.
Proof.
  intros spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' p n x bs CS Hin Hg HB H1 H2 HE.
  destruct (cs_blk _ _ _ _ _ _ _ _ _ _ _ _ p n CS Hin Hg) as [_ KB].
  apply (crt_bytes_keep memc memc' x bs HB). intros i Hi. apply KB; [lia | exact (HE i Hi)].
Qed.

Lemma cs_ledger : forall spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' Lamc pk c f,
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> MR Lc Ac memc mdc -> alloc_ceiling <= spc - K ->
  ledger B Lc Ac memc Lamc pk c f ->
  (forall x, alloc_statics x -> ~ E x) ->
  (forall a k, In (a, k) Lamc -> ~ G (a - 16) (k + 16) /\ forall x, a - 16 <= x < a - 8 -> ~ E x) ->
  ledger B Lc' Ac' memc' Lamc pk c f.
Proof.
  intros spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' Lamc pk c f CS HMc HK LG HS HL.
  pose proof CS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  apply (ledger_frame B Lc Ac Lc' Ac' memc memc' Lamc pk c f LG).
  - intros a k Hin. pose proof (LF (a, k) Hin) as (Hk & Hb & _). cbn [fst snd] in Hb.
    exact (proj1 (cs_blk _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (k + 16) CS Hb (proj1 (HL a k Hin)))).
  - intros x [Hx | (a & k & Hin & Hx)].
    + destruct (crt_GS2 x Hx) as (Hi & Hr & Her & Ho). destruct (Ho _ _ _ _ HMc) as [Hn _].
      apply HF; [right; exact Hi | exact Hn | lia | exact Her | exact (HS x Hx)].
    + pose proof (LF (a, k) Hin) as (Hk & Hb & _). cbn [fst snd] in Hb, Hk.
      destruct (cs_blk _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (k + 16) CS Hb (proj1 (HL a k Hin))) as [_ HB].
      rewrite SEG. apply HB; [lia | exact (proj2 (HL a k Hin) x Hx)].
Qed.

Lemma gi_munch : forall Lc Ac memc mdc W m',
  GI Lc Ac memc mdc -> Frame.munch W memc m' -> Frame.wmono rsegs memc m' -> ro_agree rsegs m' ->
  (forall x, ~ Frame.outside W x -> (spZ regs - CRT_STK <= x < spZ regs - 104) \/
     exists p n, In (p, n) (blocks Lc Ac) /\ ~ In (p, n) (blocks L A) /\ p <= x < p + n) ->
  GI Lc Ac m' mdc.
Proof.
  intros Lc Ac memc mdc W m' GIc MU WM RA' HW.
  pose proof GIc as (MID & LEN & UB & INI & RA & GK & FR).
  pose proof PRE as (HM & _). pose proof crt_sp as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof MID as (HMc & _ & _ & _ & PAc & _).
  unfold CRT_STK, ALLOC_STACK in HW |- *.
  assert (EB : forall p n x, In (p, n) (blocks Lc Ac) -> p <= x < p + n ->
      x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lc Ac x).
  { intros p n x Hin Hx. destruct (crt_blk Lc Ac memc mdc p n (x - p) HMc Hin ltac:(lia)) as (R & NI & NO & _).
    replace (p + (x - p)) with x in * by lia. split; [lia|]. split; [exact NI | exact NO]. }
  assert (OUT : forall x, ~ (spZ regs - (8192 + 6400) <= x < spZ regs - 104) ->
      (forall p n, In (p, n) (blocks Lc Ac) -> ~ In (p, n) (blocks L A) -> ~ (p <= x < p + n)) ->
      Frame.outside W x).
  { intros x H1 H2. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
    destruct (HW x Ho) as [Hs | (p & n & Hin & Hne & Hx)]; [exact (H1 Hs) | exact (H2 p n Hin Hne Hx)]. }
  split.
  { apply (crt_mid_W _ _ _ _ _ _ (fun x => alloc_statics x \/
        exists p n, In (p, n) (blocks Lc Ac) /\ ~ In (p, n) (blocks L A) /\ p <= x < p + n)).
    - apply (kb_mid_tail B API crt_IL CRT_STK (spZ regs) L A mem md alloc_statics Lc Ac memc mdc m' W
        (fun x => exists p n, In (p, n) (blocks Lc Ac) /\ ~ In (p, n) (blocks L A) /\ p <= x < p + n) MID MU).
      + rewrite SEG. exact WM.
      + intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU x Ho); exact Hx|].
        pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
        apply (past_nul.pn_wview_none rsegs m' x).
        * destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
          destruct (HW _ Ho) as [Hs | (p & n & Hin & _ & Hx')].
          -- rewrite check_reject_clean_starved.crs_fs_hi in F by lia. discriminate.
          -- exact (proj1 (proj2 (EB p n _ Hin Hx')) (past_nul.pn_seg_img B SEG _ _ F)).
        * apply WM. apply past_nul.pn_wview_some. exact Hx.
      + intros x Hx Hs He. apply OUT; [unfold CRT_STK, ALLOC_STACK in Hs; lia |].
        intros p n Hin Hne Hpx. apply He. exists p, n. split; [exact Hin|]. split; [exact Hne | exact Hpx].
      + intros x Hx Ho. apply OUT; [lia |]. intros p n Hin _ Hpx. exact (proj2 (proj2 (EB p n x Hin Hpx)) Ho).
      + intros p n i Hp Hp' Hi.
        assert (Hb : In (ptr_addr L p, n) (blocks L A)).
        { unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp]. }
        pose proof (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi) as (_ & R1 & R2 & _).
        apply OUT; [lia |]. intros p' n' Hin Hne Hak.
        assert (Hc : In (ptr_addr L p, n) (blocks Lc Ac)) by exact (gi_entry_blk Lc Ac memc mdc _ _ GIc Hb).
        assert (Hneq : (p', n') <> (ptr_addr L p, n)) by (intros Eq; apply Hne; rewrite Eq; exact Hb).
        exact (crt_blk_disj Lc Ac memc mdc p' n' (ptr_addr L p) n (ptr_addr L p + i) HMc Hin Hc Hneq Hak ltac:(lia)).
    - intros a Ha Hn [Hs | (p & n & Hin & _ & Hak)]; [exact Hs|]. exfalso.
      destruct (EB p n a Hin Hak) as (H1 & H2 & _). destruct Ha as [Ha|Ha]; [lia | exact (H2 Ha)]. }
  split; [exact LEN|]. split; [exact UB|]. split; [exact INI|]. split; [exact RA'|].
  split.
  { intros i Hi. rewrite <- (GK i Hi).
    assert (Ho : owned B Lc Ac (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMc Ho) as Hlo.
    apply (mbyte_munch (ms_segs B) W memc m' _ MU); [lia|].
    apply OUT; [lia |]. intros p n Hin _ Hak. exact (proj2 (proj2 (EB p n _ Hin Hak)) Ho). }
  apply (HsKindB.rw_cells_keep memc m' _ _ FR). intros a Ha. cbn [crt_cells cells_size csize Nat.add] in Ha.
  assert (Ho : Frame.outside W a).
  { apply OUT; [lia|]. intros p n Hin _ Hak. pose proof (EB p n a Hin Hak). lia. }
  split; [exact (mbyte_munch rsegs W memc m' a MU ltac:(lia) Ho) | exact (writable_munch rsegs W memc m' a MU ltac:(lia) Ho)].
Qed.

End E.
