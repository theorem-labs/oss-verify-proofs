(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACim.v:270-271, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D3r.v, with its module names changed; 300 of its 388 lines of code are new or changed and 651 lines of the source are left out. *)
(* The packaging piece of seg_D3 (the REAC-version case of LLVMFuzzerTestOneInput's build-B walk, +0x888 ..
   +0xe24): d3tl_core (:238), the step from the case's end state to the
   boundary inv_tail (LLVMFuzzerTestOneInput_inv.v). Nothing of the listing is walked here: the case's run is
   summarised by the statement's premises (the end journal, the end frames, the live blocks, the preserved
   registers, d3_keep, and the two things the case wrote that inv_tail states, hw.have = 1 at mf+24 and the
   payload's eight bytes at SF+436).

   What the proof does: it re-states at the end state every fact of the start boundary (inv_caseV) that inv_tail
   also states. The registers come from the premise (:251) that registers 2, 3, 4, 8, 9, 22 and 27 end as they
   began, the file descriptors and the file system from the AJ_NIL_IO premise on the end journal, the meter from the start's two clauses and the premise `forall s s', mo_le MT s s' 0`, and
   every byte-level fact (val_mem, bytes_at8, sh_zero, sh_blk) from d3_keep: each address it speaks of lies in
   d3_zone and outside d3_wr. That last step is pure address arithmetic, and it needs the geometry of the four
   zones, which this file derives once (G1 .. G12 in the proof): the side-stack frame [SF, SF+1024) and its
   shadow [shadow_addr SF, +128) are below alloc_ceiling, the machine frame [mf, sp0) is above it (sp0 is at
   least alloc_ceiling + LLVMF_STK, and mf is at most 336 below sp0), and the payload copy and the input block
   are heap blocks, hence disjoint from the frame (sep_block_frame) and below the shadow band (in_app).

   The premise `STK_LLVMF <= LLVMF_STK` is the contract's own hypothesis (LLVMFuzzerTestOneInput.v:113); it is
   what puts the machine frame above alloc_ceiling. d3tl_core (:238) takes it as its first premise, and LLVMFuzzerTestOneInput_seg_D3.v:1886
   gives it that file's HSTK (:810). LLVMFuzzerTestOneInput_seg_D3_hand_stmt.v:142-144 records d3_tl_stmt as removed; no ancestor commit defines it in this unit.

   The model lemmas (d3tl_bz_zb .. d3tl_hw) are the ones of LLVMFuzzerTestOneInput_seg_D3.v, copied under the
   d3tl_ prefix so that this file does not depend on that one: only the record's answer `have = 1` and
   `hwb (S i) = firstn 8 (rec_pl i)` is used, to read the statement's two end premises as inv_tail's hw facts. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D3_hand_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the model of the case (LLVMFuzzerTestOneInput_seg_D3.v, copied) -------------------------------------- *)
Lemma d3tl_bz_zb : forall x, RcIdentModel.bz (RcIdentModel.zb x) = x mod 256.
Proof. intros x. unfold RcIdentModel.bz, RcIdentModel.zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma d3tl_le16 : forall v, 0 <= v < 65536 ->
  RcIdentModel.bz (nth 0 (RcIdentModel.le16 v) (RcIdentModel.zb 0)) +
  256 * RcIdentModel.bz (nth 1 (RcIdentModel.le16 v) (RcIdentModel.zb 0)) = v.
Proof. intros v Hv. unfold RcIdentModel.le16. cbn [nth]. rewrite !d3tl_bz_zb. Z.div_mod_to_equations. lia. Qed.

Definition d3tl_U (l r A M C : list byte) : list byte :=
  RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M)
    26 C) 36 [RcIdentModel.zb 1].

Lemma d3tl_nth_ver : forall (l r A M C : list byte) j,
  length l = 38%nat -> length r = 8%nat -> length A = 2%nat -> length M = 2%nat -> length C = 2%nat -> (j < 2)%nat ->
  RcIdentModel.nthb (d3tl_U l r A M C) (22 + j) = nth j A (RcIdentModel.zb 0) /\
  RcIdentModel.nthb (d3tl_U l r A M C) (24 + j) = nth j M (RcIdentModel.zb 0) /\
  RcIdentModel.nthb (d3tl_U l r A M C) (26 + j) = nth j C (RcIdentModel.zb 0).
Proof.
  intros l r A M C j Hl Hr HA HM HC Hj. unfold d3tl_U, RcIdentModel.nthb.
  assert (L1 : length (RcIdentModel.upd l 28 r) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  assert (L2 : length (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) = 38%nat)
    by (rewrite RcIdentModel.upd_length; lia).
  assert (L3 : length (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M) = 38%nat)
    by (rewrite RcIdentModel.upd_length; lia).
  assert (L4 : length (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M)
    26 C) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  split; [|split].
  - rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_before by lia.
    rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_in by lia. f_equal. lia.
  - rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_before by lia.
    rewrite SlotModel.nth_upd_in by lia. f_equal. lia.
  - rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_in by lia. f_equal. lia.
Qed.

Lemma d3tl_vb : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  (8 <= length (SlotModel.rec_pl inp i))%nat /\
  RcIdentModel.has_reac_version (SlotModel.rec_id inp (S i)) = 1 /\
  RcIdentModel.raw (SlotModel.rec_id inp (S i)) = firstn 8 (SlotModel.rec_pl inp i) /\
  RcIdentModel.major (SlotModel.rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2) (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3) /\
  RcIdentModel.minor (SlotModel.rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (SlotModel.rec_pl inp i) 4) (RcIdentModel.nthb (SlotModel.rec_pl inp i) 5) /\
  RcIdentModel.patch (SlotModel.rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (SlotModel.rec_pl inp i) 6) (RcIdentModel.nthb (SlotModel.rec_pl inp i) 7).
Proof.
  intros inp i Hr Ha. unfold SlotModel.rec_r in Hr. cbn [SlotModel.rec_id]. rewrite Ha in *.
  pose proof (SlotModel.rec_id_length inp i) as Hl.
  destruct (Nat.lt_ge_cases (length (SlotModel.rec_pl inp i)) 8) as [Hs|Hs].
  { rewrite (SlotModel.ING_ver_short _ _ Hs) in Hr. cbn [fst] in Hr. discriminate. }
  destruct (SlotModel.ING_ver_long _ _ Hl Hs) as (H1 & H2 & _).
  split; [exact Hs|]. split; [exact H1|]. split; [exact H2|].
  rewrite SlotModel.ING_ver_dispatch. unfold RcIdentModel.ing_version.
  destruct (Nat.leb_spec RcIdentModel.REAC_VER_LEN (length (SlotModel.rec_pl inp i))) as [E|E];
    [|unfold RcIdentModel.REAC_VER_LEN in E; lia].
  cbn [snd]. unfold RcIdentModel.OFF_RAW, RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH,
    RcIdentModel.OFF_HAS_VER, RcIdentModel.REAC_VER_LEN.
  set (pv := SlotModel.rec_pl inp i) in *.
  assert (Hr8 : length (firstn 8 pv) = 8%nat) by (rewrite length_firstn; lia).
  destruct (d3tl_nth_ver (SlotModel.rec_id inp i) (firstn 8 pv)
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 2) (RcIdentModel.nthb pv 3)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 4) (RcIdentModel.nthb pv 5)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 6) (RcIdentModel.nthb pv 7))) 0
    Hl Hr8 eq_refl eq_refl eq_refl ltac:(lia)) as (A0 & M0 & C0).
  destruct (d3tl_nth_ver (SlotModel.rec_id inp i) (firstn 8 pv)
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 2) (RcIdentModel.nthb pv 3)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 4) (RcIdentModel.nthb pv 5)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 6) (RcIdentModel.nthb pv 7))) 1
    Hl Hr8 eq_refl eq_refl eq_refl ltac:(lia)) as (A1 & M1 & C1).
  unfold d3tl_U in A0, M0, C0, A1, M1, C1. cbn [Nat.add] in A0, M0, C0, A1, M1, C1.
  unfold RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch.
  rewrite A0, A1, M0, M1, C0, C1.
  pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 2)). pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 3)).
  pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 4)). pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 5)).
  pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 6)). pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 7)).
  unfold RcIdentModel.be16. split; [|split]; apply d3tl_le16; lia.
Qed.

(* The record's payload is at least eight bytes long, so the case's record is the one that sets `hw`. *)
Lemma d3tl_ver : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  8 <= SlotModel.rec_k inp i.
Proof.
  intros inp i Hr Ha. destruct (d3tl_vb inp i Hr Ha) as (L & _).
  pose proof (SlotModel.rec_pl_length inp i) as E. pose proof (SlotModel.rec_k_range inp i). lia.
Qed.

Lemma d3tl_hw : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  SlotModel.rec_have inp (S i) = 1 /\ SlotModel.rec_hwb inp (S i) = firstn 8 (SlotModel.rec_pl inp i).
Proof.
  intros inp i Hr Ha. pose proof (d3tl_ver inp i Hr Ha) as Hk.
  unfold SlotModel.rec_have, SlotModel.rec_hwb. cbn [SlotModel.rec_hw].
  rewrite Ha, Z.eqb_refl. destruct (Z.leb_spec 8 (SlotModel.rec_k inp i)) as [_|E]; [|lia].
  split; reflexivity.
Qed.

(* ---- moving a memory fact from one state to another ------------------------------------------------------ *)
Section m.
Variable segs : list Segment.
Lemma d3tl_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
End m.
(* The two shadow facts, with the cell count given as an explicit bound (so that the side condition is a
   closed comparison and never a division with a free variable). *)
Lemma d3tl_zs_moved : forall (rd rd' : reader) Bs a n m,
  n <= 8 * m ->
  (forall i, 0 <= i < m -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n m Hm Hk Hz i Hi.
assert (Hd : n / 8 <= m) by (apply Z.div_le_upper_bound; lia).
rewrite (Hk i ltac:(lia)). exact (Hz i Hi).
Qed.
Lemma d3tl_bs_moved : forall (rd rd' : reader) Bs a n m,
  n + 7 <= 8 * m ->
  (forall i, 0 <= i < m -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n m Hm Hk Hb. apply (block_shadow_agree rd rd' Bs a n); [|exact Hb].
assert (Hd : (n + 7) / 8 <= m) by (apply Z.div_le_upper_bound; lia).
intros i Hi. apply Hk. lia.
Qed.

(* ---- the four zones, as tactics ---------------------------------------------------------------------------- *)
(* K is the zone's keep lemma (KMF / KSF / KSH / KPL / KIN of the proof below), H the fact at the start state,
   L a length equation of the list, E the shadow-address equation of the object. *)
(* the side-stack frame's offsets, as numbers, in an address goal *)
Ltac d3tl_voff := cbv [V_before N_before V_again N_again V_s N_s V_v N_v V_ev N_ev V_id N_id V_hw N_hw
  V_f N_f V_ef N_ef V_nm N_nm V_dp N_dp V_w4 N_w4 V_cnt N_cnt M_n1 M_n2].
Ltac d3tl_tv K H := eapply val_mem_moved;
  [ let kk := fresh "kk" in let Hkk := fresh "Hkk" in
    intros kk Hkk; apply K; clear - Hkk; d3tl_voff; lia | exact H ].
Ltac d3tl_tvb K H HB := eapply val_mem_moved;
  [ let kk := fresh "kk" in let Hkk := fresh "Hkk" in
    intros kk Hkk; apply K; clear - Hkk HB; d3tl_voff; lia | exact H ].
Ltac d3tl_tg K H L := unfold bytes_at8; eapply d3tl_garr8_moved;
  [ let kk := fresh "kk" in let Hkk := fresh "Hkk" in
    intros kk Hkk; rewrite length_map in Hkk; apply K; clear - Hkk L; d3tl_voff; lia | exact H ].
Ltac d3tl_tz K H E B := unfold sh_zero; eapply (d3tl_zs_moved _ _ _ _ _ B);
  [ clear; d3tl_voff; lia
  | let ii := fresh "ii" in let Hii := fresh "Hii" in
    intros ii Hii; rewrite E; apply K; clear - Hii; d3tl_voff; lia
  | exact H ].
Ltac d3tl_tb K H E B := unfold sh_blk; eapply (d3tl_bs_moved _ _ _ _ _ B);
  [ clear; d3tl_voff; lia
  | let ii := fresh "ii" in let Hii := fresh "Hii" in
    intros ii Hii; rewrite E; apply K; clear - Hii; d3tl_voff; lia
  | exact H ].
(* membership of a register number in the seven inv_tail reads *)
Ltac d3tl_inl := cbn [In]; repeat first [ left; vm_compute; reflexivity | right ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

(* The case's end state, packaged into inv_tail by d3tl_core (:238), with two premises (:238, :251) that
   LLVMFuzzerTestOneInput_seg_D3.v:1886-1897 supplies. (1) `STK_LLVMF <= LLVMF_STK` first: it is the contract's own
   hypothesis (LLVMFuzzerTestOneInput.v:113), and without it nothing puts the machine frame above
   alloc_ceiling, so the two uninstrumented machine-frame slots the case writes (mf+24, mf+208) could be
   bytes of the payload copy or of the input block, which inv_tail states unchanged. (2) the registers: the case
   does change s2 .. s5, so `aregs_preserved regs2 regsE`, the premise LLVMFuzzerTestOneInput_seg_D3_hand_stmt.v:142-144
   records for the removed d3_tl_stmt, cannot hold at the end; what inv_tail reads is the seven registers of ecommon (2, 9, 8, 3, 4) and P_body (22, 27). *)
Lemma d3tl_core : STK_LLVMF <= LLVMF_STK ->
  AR_laws SEGS B -> ameter_laws MT -> (forall s s' : astate, mo_le MT s s' 0) ->
  (forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
     ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
     m_fds md' = m_fds md /\ m_fs md' = m_fs md) ->
  forall (g : ectx) (pos mf : Z) (i : nat) (pl : Z) (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2
    (WE : world SEGS) (regsE : bvmap 5 word) memE mdE lyE SE,
  inv_caseV B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf i pl W2 (cfg_at SEGS (BASE + 0x888) regs2 mem2 md2) ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    lyE SE WE memE mdE (4 * Z.of_nat i + 3) ->
  frames SE = [(4, pos)] ->
  hblocks B g lyE SE [(pl, SlotModel.rec_k (e_pl g) i)] ->
  (forall r, In r [2; 3; 4; 8; 9; 22; 27] -> getr regsE (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  d3_keep g pos mf i pl W2 mem2 WE memE ->
  val_mem SEGS (rd WE memE) (mf + 24) 8 1 ->
  bytes_at8 WE memE (SFa g pos + V_hw + 4) (firstn 8 (SlotModel.rec_pl (e_pl g) i)) ->
  inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf i pl WE (cfg_at SEGS (BASE + 0xe24) regsE memE mdE).
Proof.
intros HSTK LAWS MTL MZERO AJ_NIL_IO g pos mf i pl W2 regs2 mem2 md2 WE regsE memE mdE lyE SE
  HV HJE HfrE HblE HPRES KEEP VE HWE.
destruct HV as (ly2 & S2 & regs2' & mem2' & md2' & Hcfg & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
unfold cfg_at in Hcfg. injection Hcfg as Hcr Hcm Hcmd. subst regs2' mem2' md2'.
destruct HC as (R2 & R9 & R8 & Hmfb & Hmf32 & R3 & R4 & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (HPB & Hhw & Hr & Ha & R10 & R24 & R25 & R21).
destruct HPB as (Hi & Hhb & Hbpl & Hid & V96 & Hfix & Hmbef & Hmag & Hmid & V112 & V120 & V128 & R22 & R27 & Hcur).
destruct Hid as (Hidb & Hidz & Hidsh).
destruct Hhw as (Hhwm & Hhw0 & Hhw24). destruct Hhwm as (Hhwb & Hhwz & Hhwsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (HIN : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
(* ---- the geometry of the four zones -------------------------------------------------------------------- *)
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 HIN) as (G1 & G2 & HSFapp).
rewrite EFa in G1, G2, HSFapp. change (fs_frame_bytes 4) with 1024 in G2, HSFapp.
assert (G3 : alloc_ceiling + 16400 <= mf)
  by (clear - Hmfb Hceil Hslo HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (G4 : mf + 216 <= e_sp0 g) by (clear - Hmfb; lia).
assert (G5 : shadow_addr (SFa g pos) + 168 <= mf)
  by (unfold shadow_addr, SHADOW_OFF; clear - G1 G2 G3 C1; Z.div_mod_to_equations; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
assert (G6 : SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos)
  by (unfold shadow_addr, SHADOW_OFF; clear - G1 G2 HSFapp C1; Z.div_mod_to_equations; lia).
assert (HPL : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2))
  by (destruct Hhb as [Hp _]; apply (Permutation_in _ (Permutation_sym Hp)); left; reflexivity).
pose proof (SlotModel.rec_k_range (e_pl g) i) as HKr.
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(clear - HKr; lia)) as (Hrq1 & Hrq2).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl _ HAR2 HPL) as (_ & G7 & Hpceil & Hpapp & _).
assert (G8 : pl + SlotModel.rec_k (e_pl g) i <= alloc_ceiling) by (clear - Hpceil Hrq2; lia).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl _ 4 pos HAR2 HPL HIN) as Hsep.
rewrite EFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (G9 : pl + SlotModel.rec_k (e_pl g) i <= SFa g pos \/ SFa g pos + 1024 <= pl)
  by (clear - Hsep Hrq2; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
assert (G10 : pl + SlotModel.rec_k (e_pl g) i <= shadow_addr (SFa g pos) \/
              shadow_addr (SFa g pos) + 128 <= pl)
  by (unfold shadow_addr, SHADOW_OFF; clear - G1 G2 G7 G8 Hpapp Hrq2 C1; Z.div_mod_to_equations; lia).
(* the input block: empty, or a heap block of the entry state, so of the current state too *)
assert (HINP : e_n g = 0 \/ In (e_p g, e_n g) (ablocks B ly2 S2) /\ 0 < e_n g).
{ pose proof HPRE as HP'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HP'.
  destruct HP' as (_ & _ & _ & _ & Hnp & _). destruct Hnp as [[Hn0 _] | [Hnn Hine]]; [left; exact Hn0|].
  right. split; [|clear - Hnn; lia].
  destruct Hhb as [Hp _]. apply (Permutation_in _ (Permutation_sym Hp)). right. exact Hine. }
assert (G11 : e_n g = 0 \/ (4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling /\
   (e_p g + e_n g <= SFa g pos \/ SFa g pos + 1024 <= e_p g) /\
   (e_p g + e_n g <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= e_p g))).
{ destruct HINP as [Hn0 | [Hine Hnn]]; [left; exact Hn0|]. right.
  pose proof (req_size_pos (e_n g) ltac:(clear - Hnn; lia)) as (_ & Hrn).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine) as (_ & Hi1 & Hi2 & Hi3 & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 4 pos HAR2 Hine HIN) as Hsep2.
  rewrite EFa in Hsep2. change (fs_frame_bytes 4) with 1024 in Hsep2.
  unfold zdisjoint in Hsep2. cbn [fst snd] in Hsep2.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hi3.
  split; [exact Hi1|]. split; [clear - Hi2 Hrn; lia|].
  split; [clear - Hsep2 Hrn; lia|].
  unfold shadow_addr, SHADOW_OFF. clear - G1 G2 Hi1 Hi2 Hi3 Hrn C1. Z.div_mod_to_equations. lia. }
(* ---- the four zones of d3_keep, as address-level facts --------------------------------------------------- *)
(* the machine frame's own slots, [mf, mf+216), minus the two the case writes *)
assert (KMF : forall a, mf <= a < mf + 216 -> ~ (mf + 24 <= a < mf + 32) -> ~ (mf + 208 <= a < mf + 216) ->
  aview SEGS (w_H WE) memE a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz Hw1 Hw2. apply KEEP;
  [unfold d3_zone; left; clear - Hz G4; lia|].
  unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
  clear - Hz Hw1 Hw2 G2 G3 G5. lia. }
(* the entry's thirteen saved words, [mf+216, sp0): above everything the case writes *)
assert (KSP : forall a, mf + 216 <= a < e_sp0 g ->
  aview SEGS (w_H WE) memE a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz. apply KEEP; [unfold d3_zone; left; clear - Hz; lia|].
  unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
  clear - Hz G2 G3 G5. lia. }
assert (KSF : forall a, SFa g pos <= a < SFa g pos + 1024 ->
  ~ (SFa g pos + 224 <= a < SFa g pos + 244) -> ~ (SFa g pos + 288 <= a < SFa g pos + 312) ->
  ~ (SFa g pos + 436 <= a < SFa g pos + 444) ->
  aview SEGS (w_H WE) memE a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz H1 H2 H3. apply KEEP; [unfold d3_zone; right; left; exact Hz|].
  unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
  clear - Hz H1 H2 H3 G2 G3 G6. lia. }
assert (KSH : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  ~ (shadow_addr (SFa g pos) + 28 <= a < shadow_addr (SFa g pos) + 31) ->
  ~ (shadow_addr (SFa g pos) + 36 <= a < shadow_addr (SFa g pos) + 39) ->
  aview SEGS (w_H WE) memE a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz H1 H2. apply KEEP; [unfold d3_zone; right; right; left; exact Hz|].
  unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
  clear - Hz H1 H2 G3 G5 G6. lia. }
assert (KPL : forall a, pl <= a < pl + SlotModel.rec_k (e_pl g) i ->
  aview SEGS (w_H WE) memE a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz. apply KEEP; [unfold d3_zone; right; right; right; left; exact Hz|].
  unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
  clear - Hz G3 G7 G8 G9 G10. lia. }
assert (KIN : forall a, e_p g <= a < e_p g + e_n g ->
  aview SEGS (w_H WE) memE a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz. apply KEEP; [unfold d3_zone; right; right; right; right; exact Hz|].
  unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
  clear - Hz G3 G11. lia. }
(* ---- the shadow cells of the two objects inv_tail speaks of ---------------------------------------------- *)
assert (ESH : forall k, shadow_of_addr SHADOW_OFF (SFa g pos + 8 * k) = shadow_addr (SFa g pos) + k)
  by (intros kk; rewrite shadow_of_addr_add8; unfold shadow_addr, shadow_of_addr; reflexivity).
assert (EID : shadow_of_addr SHADOW_OFF (SFa g pos + V_id) = shadow_addr (SFa g pos) + 44)
  by (replace (SFa g pos + V_id) with (SFa g pos + 8 * 44) by (unfold V_id; lia); apply ESH).
assert (EHW : shadow_of_addr SHADOW_OFF (SFa g pos + V_hw) = shadow_addr (SFa g pos) + 54)
  by (replace (SFa g pos + V_hw) with (SFa g pos + 8 * 54) by (unfold V_hw; lia); apply ESH).
(* ---- lengths ---------------------------------------------------------------------------------------------- *)
assert (LID : Z.of_nat (length (m_id g (S i))) = 38)
  by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (LPL : Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) = SlotModel.rec_k (e_pl g) i).
{ rewrite SlotModel.rec_pl_length. clear - HKr. lia. }
assert (LIN : Z.of_nat (length (e_pl g)) = e_n g).
{ pose proof HPRE as HP'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HP'.
  destruct HP' as (_ & _ & _ & _ & _ & Hnlen & _). clear - Hnlen. lia. }
(* ---- the model's answer for the record: hw.have = 1 and hw's eight bytes ---------------------------------- *)
destruct (d3tl_hw (e_pl g) i Hr Ha) as (HAVE & HHWB).
assert (LHWB : Z.of_nat (length (m_hwb g (S i))) = 8).
{ unfold m_hwb. rewrite HHWB. rewrite length_firstn.
  pose proof (d3tl_ver (e_pl g) i Hr Ha) as Hk8. clear - LPL Hk8. lia. }
(* ---- the registers and the journal's file state ----------------------------------------------------------- *)
assert (KR : forall r : bv 5, In (bv_unsigned r) [2; 3; 4; 8; 9; 22; 27] -> getr regsE r = getr regs2 r).
{ intros r Hreg. pose proof (HPRES (bv_unsigned r) Hreg) as Hp. rewrite Z_to_bv_bv_unsigned in Hp. exact Hp. }
assert (K2 : getr regsE 2 = w64 mf) by (rewrite (KR 2%bv ltac:(d3tl_inl)); exact R2).
assert (K9 : getr regsE 9 = w64 mf) by (rewrite (KR 9%bv ltac:(d3tl_inl)); exact R9).
assert (K8 : getr regsE 8 = w64 (e_sp0 g)) by (rewrite (KR 8%bv ltac:(d3tl_inl)); exact R8).
assert (K3 : getr regsE 3 = w64 (as_gp B)) by (rewrite (KR 3%bv ltac:(d3tl_inl)); exact R3).
assert (K4 : getr regsE 4 = w64 (as_tp B)) by (rewrite (KR 4%bv ltac:(d3tl_inl)); exact R4).
assert (K22 : getr regsE 22 = w64 (SlotModel.rec_k (e_pl g) i))
  by (rewrite (KR 22%bv ltac:(d3tl_inl)); exact R22).
assert (K27 : getr regsE 27 = w64 pl) by (rewrite (KR 27%bv ltac:(d3tl_inl)); exact R27).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJE) as [Hfdeq Hfseq].
(* ---- the meter ------------------------------------------------------------------------------------------- *)
assert (HMEV : 0 <= MEV MT).
{ unfold MEV. pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as Hm.
  pose proof (mo_free_nonneg MT MTL) as Hf. clear - Hm Hf. lia. }
assert (MLE2 : mo_le MT (e_S g) SE ((4 * Z.of_nat i + 3) * MEV MT)).
{ replace ((4 * Z.of_nat i + 3) * MEV MT) with ((4 * Z.of_nat i + 3) * MEV MT + 0) by lia.
  exact (mle_station MT _ _ _ _ _ MTL MLE (MZERO S2 SE)). }
assert (MOK2 : mo_ok MT SE ((EV_LLVMF - (4 * Z.of_nat i + 3)) * MEV MT)).
{ apply (mok_station MT S2 SE ((EV_LLVMF - (4 * Z.of_nat i + 3)) * MEV MT) 0 _ MTL MOK (MZERO S2 SE));
  [ apply Z.mul_nonneg_nonneg; [clear - Hk; lia | exact HMEV] | lia ]. }
(* ---- inv_tail -------------------------------------------------------------------------------------------- *)
unfold inv_tail, acut.
exists lyE, SE, regsE, memE, mdE.
split; [reflexivity|].
split; [exact HJE|].
split; [exact HfrE|].
split; [exact Hk|].
split; [exact MLE2|].
split; [exact MOK2|].
split.
{ unfold ecommon.
  split; [exact K2|]. split; [exact K9|]. split; [exact K8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact K3|]. split; [exact K4|].
  split; [d3tl_tv KMF V16|]. split; [d3tl_tv KMF V64|]. split; [d3tl_tv KMF V192|].
  split; [d3tl_tv KMF V168|].
  split; [d3tl_tvb KSP Vra Hmfb|]. split; [d3tl_tvb KSP Vs0 Hmfb|].
  split; [d3tl_tvb KSP W24 Hmfb|]. split; [d3tl_tvb KSP W32 Hmfb|]. split; [d3tl_tvb KSP W40 Hmfb|].
  split; [d3tl_tvb KSP W48 Hmfb|]. split; [d3tl_tvb KSP W56 Hmfb|]. split; [d3tl_tvb KSP W64 Hmfb|].
  split; [d3tl_tvb KSP W72 Hmfb|]. split; [d3tl_tvb KSP W80 Hmfb|]. split; [d3tl_tvb KSP W88 Hmfb|].
  split; [d3tl_tvb KSP W96 Hmfb|]. split; [d3tl_tvb KSP W104 Hmfb|].
  split; [d3tl_tv KSF Vflag|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Hfdeq; reflexivity|].
  split; [rewrite Hfseq; reflexivity|].
  d3tl_tg KIN Hinb LIN. }
unfold P_body, hw_live, hw_mem, id_at.
split.
{ split; [exact Hi|]. split; [exact HblE|].
  split; [d3tl_tg KPL Hbpl LPL|].
  split; [split; [d3tl_tg KSF Hidb LID | split; [d3tl_tz KSH Hidz EID 5 | d3tl_tb KSH Hidsh EID 6]]|].
  split; [d3tl_tv KMF V96|].
  split; [unfold mf_fixed;
          destruct Hfix as (A32 & A48 & A56 & A72 & A80 & A88 & A104 & A136 & A144 & A160);
          split; [d3tl_tv KMF A32|]; split; [d3tl_tv KMF A48|]; split; [d3tl_tv KMF A56|];
          split; [d3tl_tv KMF A72|]; split; [d3tl_tv KMF A80|]; split; [d3tl_tv KMF A88|];
          split; [d3tl_tv KMF A104|]; split; [d3tl_tv KMF A136|]; split; [d3tl_tv KMF A144|];
          d3tl_tv KMF A160 |].
  split; [unfold mf_before; d3tl_tv KMF Hmbef|].
  split; [unfold mf_again; d3tl_tv KMF Hmag|].
  split; [unfold mf_id; d3tl_tv KMF Hmid|].
  split; [d3tl_tv KMF V112|]. split; [d3tl_tv KMF V120|]. split; [d3tl_tv KMF V128|].
  split; [exact K22|]. split; [exact K27|]. exact Hcur. }
split.
{ split.
  { unfold bytes_at8, m_hwb. rewrite HHWB. unfold V_hw. exact HWE. }
  split; [d3tl_tz KSH Hhwz EHW 2 | d3tl_tb KSH Hhwsh EHW 3]. }
split; [d3tl_tv KSF Hhw0|].
unfold m_have. rewrite HAVE. exact VE.
Qed.

Check d3tl_core.
End c.
End b.
End a.
