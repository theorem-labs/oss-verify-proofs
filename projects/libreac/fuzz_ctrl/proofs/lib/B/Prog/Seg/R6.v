(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1577 of its 1713 lines of code are new or changed and 875 lines of the source are left out. *)
(* Segment R6 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x816ec, 0x8170c],
   9 instructions, cut Inv_B816ec_at (v1.9 pc 0x816ec) -> cut Inv_B81710_at (v1.9 pc 0x81710); the
   round-trip loop head's argument block and the returning call BAS@0x8170c = reac_ctrl_build_as (plan-asan-ubsan.md
   section 2, row R6; section 4, BAS = reac_ctrl_build_as 0x8528c).  rule 24: no function proved (a slot segment).
   Re-fit of the v1.8 proof (a working branch c439fa41c5b) onto the v1.9.0 bytes and a Theorem Labs lane's v1.9 cut bundle: the
   argument spills move [A+288] -> [A+272], [A+272] -> [A+256], [A+256] -> [A+248] and the constant 32 the exit
   carries is s11 (register 27); the cut names are still the v1.8 names.

   The code reloads the five argument spills written before the loop ([A + 312] = fr + 544, the frame's out[]
   buffer; [A + 272] = the catalogue row; [A + 264] = fr + 2624, our[]; [A + 256] = round_trip.box 0x21140;
   [A + 248] = 0x1234), passes the turn index b in a2 (mv a2,s6), zeroes a6 / a7 and calls reac_ctrl_build_as,
   which returns to 0x81710.  The range has no instrumented shadow check and no UBSan trap.  The call is taken on
   its lib/B contract (lib/B/Prog/reac_ctrl_build_as_c.v), a Section Hypothesis, never on its code.

   Cuts: SlotInv.v's official Inv_B816ec_at b (entry; its RBE and R6X bundles carry the argument spills, the
   catalogue row, the image bytes and the out[] / our[] addressability the call needs) and Inv_B81710_at b (exit,
   R7's entry).  The call's side-stack package (fp [0; 1] over r6_W / r6_D, reac_ctrl_build_as_tls, the frame and
   its shadow apart from the class-0 / class-1 areas) is built at the call from FRA by Tac_fsfree's fra_fp (
   bc14aa7165: no cut carries it).  The call's result a0 is rnb g b: build_as returns the model's n_b when the
   row's E(b) holds and 0 otherwise (then 0x81710 branches to the latch, whose R6X g (S b) is r6x_of_rbe of the
   exit's RBE).  Adopt 9 / 10 of a working branch (de0ff9e12a): the exit's RBE also carries PRA, [A + 160], [A + 112] and the
   fragment record's 72 addressable bytes (all at or above A, or with shadow bytes off the call's writes); the exit
   carries the turn-b identity / fragment records on both arms, s11 = 32 (a callee-saved register), and on
   n_b <> 0 out[]'s frame bytes rt_F, which are build_as's post under go && E (em_fr with a5 = [A + 248] =
   0x1234 = CNT16; E is n_b <> 0, go holds at the loop head).  The contract needs mem_inv, which FRA does not
   carry, so the run is stepped on the normalized
   memory (MemNorm) and carried back to the real memory by evt_normalize + AsanLift.evt_SR_canon_lazy (r6_run), as
   in R3 / R4.  Both cuts carry ENT, moved across the call by ent_munch (the call writes its own window, the out[]
   buffer, the class-0 / class-1 side-stack areas and the shadow of its window; none of them is an address ENT
   speaks of) and across the model step by ent_mat; FRA's input facts move by fra_in_keep_sh (the input block is
   a live entry block: app memory below stklo, outside the frame and the side stack).

   The helper lemmas below are the ones of lib/B/Prog/Seg/R3.v, R4.v (byte / cell / normalized-memory transport) and
   of the F3 toolkit of a working branch (shadow arithmetic, interval lists, the side-stack state fp, FRA across
   a run that writes the callee window, the frame body and the side stack), renamed r6_*. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcLay RcEmit RcPorts RcFin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFinLib RcSynthLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
(* The plain models the contract speaks (ba_go, ba_E, ba_X, ba_tbl) and the image-B contract itself. *)
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module BMB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_model_block_c.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.

(* ---- byte and cell helpers (R4) ---- *)

Lemma r6_ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

(* A spilled word read by `ld`: its 8 bytes as one read-only cell. *)
Lemma r6_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma r6_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r6_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r6_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- shadow arithmetic and interval lists (F3) ---- *)

Lemma r6_sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma r6_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

Lemma r6_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma r6_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma r6_sh_hi : forall x, 0 <= x <= APPMEM_END -> shadow_addr x <= HIGHMEM_BEG.
Proof.
  intros x Hx. unfold shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *.
  assert (Hb : 140737488355328 / 8 = 17592186044416) by (vm_compute; reflexivity).
  pose proof (Z.div_le_mono x 140737488355328 8 ltac:(lia) ltac:(lia)) as H. lia.
Qed.

(* The byte of a shadow address inside [shadow_addr lo, shadow_addr hi) with lo a multiple of 8. *)
Lemma r6_sh_inv : forall q lo hi, lo mod 8 = 0 -> 0 <= lo -> shadow_addr lo <= q < shadow_addr hi ->
  lo <= lo + 8 * (q - shadow_addr lo) < hi /\ shadow_addr (lo + 8 * (q - shadow_addr lo)) = q.
Proof.
  intros q lo hi Hm Hlo Hq.
  assert (Hk : 0 <= q - shadow_addr lo) by lia.
  pose proof (r6_sh_frame_of lo (q - shadow_addr lo) Hlo Hm Hk) as E.
  split; [split; [lia|] | rewrite E; lia].
  destruct (Z_lt_le_dec (lo + 8 * (q - shadow_addr lo)) hi) as [H|H]; [exact H|].
  exfalso. pose proof (r6_sh_ge (lo + 8 * (q - shadow_addr lo)) hi H) as Hge. rewrite E in Hge. lia.
Qed.

Lemma r6_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

Lemma r6_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma r6_addr_of1 : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn He H. split; [exact Hp|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & HA). pose proof (HA 0 ltac:(lia)) as Hb.
  rewrite Z.add_0_r in Hb. exact Hb.
Qed.

Lemma r6_out_app : forall A C x, outside A x -> outside C x -> outside (A ++ C) x.
Proof.
  induction A as [|[lo hi] A IH]; intros C x HA HB; cbn [app outside] in *; [exact HB|].
  destruct HA as [H1 H2]. split; [exact H1 | exact (IH C x H2 HB)].
Qed.

Lemma r6_dj_out_r : forall L X a b x, fp_dj L X -> In (a, b) L -> a <= x < b -> outside X x.
Proof.
  intros L X a b x H Hin Hx. unfold fp_dj in H. rewrite Forall_forall in H. pose proof (H _ Hin) as H1.
  cbn [fst snd] in H1. clear H Hin. induction X as [|[lo hi] X IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in H1 as [D H1]. unfold ly_dj in D. cbn [fst snd] in D. split; [lia | exact (IH H1)].
Qed.

Lemma r6_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof.
  intros m a. unfold mbyte, mrd, wa. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  unfold YK11.seg_rom, PropExec.seg_rom. reflexivity.
Qed.

Lemma r6_dj_lo : forall W a n, Forall (fun r => a + n <= fst r) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [fst] in H1.
  split; [left; exact H1 | exact (IH a n H2)].
Qed.

Lemma r6_rt_disjoint : forall W, Forall (fun r => AC.GT <= fst r) W -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
    RT_AGLOB_LEN.
  repeat split; apply r6_dj_lo; (eapply Forall_impl; [|exact H]);
    intros [lo hi] Hl; cbn [fst] in *; unfold AC.GT in Hl; lia.
Qed.

Lemma r6_stk : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) Hm Hw HX. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  destruct (HX a Ha) as [Ho | Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* The side stack's runtime state after a run that writes, inside the metadata region [FS, FS + 36864), only the
   class-0 and class-1 hint words [FS, FS + 16) and their flag bytes [FS + 4096, FS + 28672): the other classes'
   cells are unchanged and the class-0 / class-1 cells are the ones the run's own post states (fp_cls). *)
Lemma r6_fs_ok : forall mem mem' FS W,
  AC.a_fs_ok mem FS -> munch W mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q) ->
  (forall q, FS <= q < FS + AC.FS_SIZE -> exists b, mbyte rsegs mem' q = Some b) ->
  (forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 16) -> ~ (FS + 4096 <= q < FS + 28672) -> outside W q) ->
  fp_cls mem' FS 0%nat -> fp_cls mem' FS 1%nat -> 0 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 -> AC.a_fs_ok mem' FS.
Proof.
  intros mem mem' FS W (P1 & P2 & P3 & P4 & P5) MU Hwm Hpr Hkeep HC0 HC1 HFS0 Hsz.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (KEEP : forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 16) ->
                   ~ (FS + 4096 <= q < FS + 28672) -> mbyte rsegs mem' q = mbyte rsegs mem q).
  { intros q Hq H1 H2. apply (KindBGlue.mbyte_munch rsegs W mem mem' q MU ltac:(lia) (Hkeep q Hq H1 H2)). }
  split.
  { intros q Hq. destruct (P1 q Hq) as (Hw & Hpa). split.
    - apply (Hwm q); [lia | exact Hw].
    - exact (Hpr q Hq). }
  split.
  { unfold word_mem. intros k Hk. rewrite KEEP by lia. exact (P2 k Hk). }
  split.
  { rewrite KEEP by lia. exact P3. }
  split.
  { intros c Hc.
    destruct (Nat.eq_dec c 0) as [->|Hn0].
    - destruct HC0 as (_ & h & flags & HH & _). exists (bv_unsigned h).
      change (AC.a_fs_hint FS 0) with (fs_hint FS 0).
      exact (KindBGlue.bytes_at_le8_word rsegs mem' (fs_hint FS 0) h HH).
    - destruct (Nat.eq_dec c 1) as [->|Hn1].
      + destruct HC1 as (_ & h & flags & HH & _). exists (bv_unsigned h).
        change (AC.a_fs_hint FS 1) with (fs_hint FS 1).
        exact (KindBGlue.bytes_at_le8_word rsegs mem' (fs_hint FS 1) h HH).
      + destruct (P4 c Hc) as (h' & Hh'). exists h'. unfold word_mem. intros k Hk.
        assert (Hz : 2 <= Z.of_nat c <= 10) by lia.
        rewrite (KEEP (AC.a_fs_hint FS c + Z.of_nat k) ltac:(unfold AC.a_fs_hint; lia)
                   ltac:(unfold AC.a_fs_hint; lia) ltac:(unfold AC.a_fs_hint; lia)).
        exact (Hh' k Hk). }
  { intros c j Hc Hj.
    assert (FLG : forall (cc : nat) (flags : list byte),
              bytes_at rsegs mem' (fs_flag FS cc 0) flags -> Z.of_nat (length flags) = fs_M cc ->
              Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
              0 <= j < AC.a_fs_M cc ->
              mbyte rsegs mem' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 0) \/
              mbyte rsegs mem' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 1)).
    { intros cc flags HFl HFlen HFb Hjr.
      change (AC.a_fs_M cc) with (fs_M cc) in Hjr.
      destruct HFl as (Hb0 & Hb1 & Hb2).
      assert (Hji : (Z.to_nat j < length flags)%nat) by lia.
      pose proof (Hb2 (Z.to_nat j) Hji) as Hnb. rewrite Z2Nat.id in Hnb by lia.
      destruct (nth_error flags (Z.to_nat j)) as [bb|] eqn:Eb; [|apply nth_error_None in Eb; lia].
      rewrite Forall_forall in HFb. pose proof (HFb bb (nth_error_In flags (Z.to_nat j) Eb)) as Hv.
      change (AC.a_fs_flag FS cc j) with (fs_flag FS cc j).
      assert (Em : mbyte rsegs mem' (fs_flag FS cc j) = Some bb).
      { rewrite r6_mbyte_mrd.
        replace (wa (fs_flag FS cc j)) with (wa (fs_flag FS cc 0 + j))
          by (unfold wa, fs_flag; f_equal; lia).
        rewrite Hnb. reflexivity. }
      rewrite Em. destruct Hv as [-> | ->]; [left; reflexivity | right; reflexivity]. }
    destruct (Nat.eq_dec c 0) as [->|Hn0].
    - destruct HC0 as (_ & h & flags & _ & HFl & HFlen & HFb). exact (FLG 0%nat flags HFl HFlen HFb Hj).
    - destruct (Nat.eq_dec c 1) as [->|Hn1].
      + destruct HC1 as (_ & h & flags & _ & HFl & HFlen & HFb). exact (FLG 1%nat flags HFl HFlen HFb Hj).
      + pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
        assert (Hz : 2 <= Z.of_nat c <= 10) by lia.
        assert (Hple : 2 ^ (15 - Z.of_nat c) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia).
        assert (Hpge : 0 < 2 ^ (15 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
        assert (Hout : ~ (FS + 4096 <= AC.a_fs_flag FS c j < FS + 28672)).
        { unfold AC.a_fs_flag in *. change (2 ^ 15) with 32768 in *. change (2 ^ 13) with 8192 in *. lia. }
        assert (Hout0 : ~ (FS <= AC.a_fs_flag FS c j < FS + 16)).
        { unfold AC.a_fs_flag in *. change (2 ^ 15) with 32768 in *. change (2 ^ 13) with 8192 in *. lia. }
        rewrite (KEEP (AC.a_fs_flag FS c j) ltac:(lia) Hout0 Hout).
        exact (P5 c j Hc Hj). }
Qed.

(* ---- the model facts of the turn: the row address, the request size, and `go` ---- *)

(* The catalogue row the round trip passes: one of the 11 rows of BOX_CATALOGUE, 8-byte aligned. *)
Lemma r6_mrow_rng : forall inp, CAT <= mrow inp <= CAT + 296 * 10 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. unfold mrow, istar, CAT_ROW, CAT_N, CAT.
  pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)) as Hb.
  set (k := (mode inp / 2) mod 11) in *.
  split; [lia|].
  replace (0x9f620 + 296 * k) with ((81604 + 37 * k) * 8) by lia.
  apply Z_mod_mult.
Qed.

(* The request the round trip makes is 0 or a valid frame length 52 + 36 n with 2 <= n <= 40. *)
Lemma r6_rtn_bnd : forall inp x, 0 <= rt_n inp x <= 1492.
Proof.
  intros inp x. unfold rt_n. destruct (rt_E inp x) eqn:E; [|lia].
  unfold rt_E, BAP.ba_E in E. apply andb_prop in E as [E _].
  unfold em_wok in E. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(* The width the model reads from a catalogue row is non-negative. *)
Lemma r6_bmuw_nonneg : forall mp bs, 0 <= bm_uw mp bs.
Proof.
  intros mp bs. unfold bm_uw.
  repeat match goal with |- context[if ?c then _ else _] => destruct c end;
    try lia; pose proof (Z.le_max_r (bm_in_ch bs) 2); lia.
Qed.

(* The emitted frame is len bytes long: the 18-byte header, the 32-byte control block, the zero fill and the
   two-byte trailer (RcSynthLib's rs_synth_len, RcFinLib's rcf_stamp32_len). *)
Lemma r6_lyZ_len : forall md mb nb bx, length mb = 296%nat -> length (ly_Z md mb nb bx) = 32%nat.
Proof.
  intros md mb nb bx L. unfold ly_Z. destruct (md =? 0); [reflexivity|].
  destruct (RS6.rc mb bx =? 1); [apply rs_synth_len; exact L | reflexivity].
Qed.

Lemma r6_baX_len : forall md mb nb bx, length mb = 296%nat -> length (BAP.ba_X md mb nb bx) = 32%nat.
Proof.
  intros md mb nb bx L. unfold BAP.ba_X. destruct (bx <=? 1).
  - apply rcf_stamp32_len. apply r6_lyZ_len. exact L.
  - apply r6_lyZ_len. exact L.
Qed.

Lemma r6_emfr_len : forall d6 s6 c16 t0 t1 blk len,
  length d6 = 6%nat -> length s6 = 6%nat -> length blk = 32%nat -> 52 <= len ->
  Z.of_nat (length (em_fr d6 s6 c16 t0 t1 blk len)) = len.
Proof.
  intros d6 s6 c16 t0 t1 blk len L1 L2 L3 Hl.
  unfold em_fr, em_hdr. rewrite !length_app, repeat_length. cbn [length]. lia.
Qed.

(* The call's `go`: the out[] buffer, the catalogue row and the turn index are the ones the loop head passes. *)
Lemma r6_go : forall o md b, 0 < o -> 0 < md -> b <= 6 -> BAP.ba_go o md b = true.
Proof.
  intros o md b Ho Hm Hb. unfold BAP.ba_go. rewrite !andb_true_iff.
  split; [split|].
  - apply negb_true_iff. apply Z.eqb_neq. lia.
  - apply negb_true_iff. apply Z.eqb_neq. lia.
  - apply Z.leb_le. lia.
Qed.

(* ---- the run of the segment: ld a0,312(s1); ld a1,272(s1); mv a2,s6; ld a3,264(s1); ld a4,256(s1);
   ld a5,248(s1); li a6,0; li a7,0; jal reac_ctrl_build_as, taken on its lib/B contract (never its code).
   The premises are the contract's, with the call's arguments substituted; `go` is true (the loop head passes a
   nonzero buffer and row and b <= 6), so the result R is Rv = (if E then n_b else 0).  The run is stated on the
   memory m the contract runs on; seg_R6 instantiates it with the normalized memory, where mem_inv holds. *)
Lemma r6_evt : BAC.reac_ctrl_build_as_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr FS bb mdv Rv : Z) (mbv nbv dbv sbv junk : list byte),
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 bb ->
    0 <= A -> A + 320 <= 2 ^ 64 -> 0 <= bb <= 6 -> 0 < fr -> fr + 3136 <= APPMEM_END ->
    0 < mdv -> mdv < 2 ^ 64 ->
    (* the five argument spills, read by the five `ld` *)
    ro_cells rsegs m (A + 312) [C8 (Z_to_bv 64 (fr + 544))] ->
    ro_cells rsegs m (A + 272) [C8 (Z_to_bv 64 mdv)] ->
    ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 (fr + 2624))] ->
    ro_cells rsegs m (A + 256) [C8 (Z_to_bv 64 BOXA)] ->
    ro_cells rsegs m (A + 248) [C8 (Z_to_bv 64 0x1234)] ->
    (* the call's own value facts: go holds, and the result is n_b when E holds and 0 otherwise *)
    BAP.ba_go (fr + 544) mdv bb = true ->
    Rv = (if BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb
          then 52 + 36 * bm_uw mdv (firstn 8 (skipn 16 mbv)) else 0) ->
    (* the contract's premises, in its own order *)
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) ->
    bytes_at rsegs m (BAC.BA_FR + 72) BAP.ba_tbl ->
    ly_dj (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) (BAC.BA_FR + 72) (BAC.BA_FR + 240) ->
    length dbv = 6%nat -> bytes_at rsegs m (fr + 2624) dbv ->
    ly_dj (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) (fr + 2624) (fr + 2624 + 6) ->
    length sbv = 6%nat -> bytes_at rsegs m BOXA sbv ->
    ly_dj (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) BOXA (BOXA + 6) ->
    (mdv <> 0 -> mdv mod 8 = 0 /\ mdv + 296 <= 2 ^ 64 /\ length mbv = 296%nat /\ bytes_at rsegs m mdv mbv /\
                 ly_dj (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) mdv (mdv + 296)) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ RS6.has mbv <> 0 /\ RS6.rname mbv <> 0 ->
       name_ok nbv /\ bytes_at rsegs m (RS6.rname mbv) nbv /\
       ly_dj (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) (RS6.rname mbv)
             (RS6.rname mbv + Z.of_nat (length nbv))) ->
    (fr + 544 <> 0 -> fr + 544 + 1492 <= 2 ^ 64) ->
    (BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
       rw_cells rsegs m (fr + 544) [CB (Z.to_nat Rv) junk] /\
       ly_dj (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) (fr + 544) (fr + 544 + Rv) /\
       ly_dj (fr + 544) (fr + 544 + Rv) (BAC.BA_FR + 72) (BAC.BA_FR + 240) /\
       ly_dj (fr + 544) (fr + 544 + Rv) mdv (mdv + 296) /\
       ((bb = 5 \/ bb = 6) /\ RS6.has mbv <> 0 /\ RS6.rname mbv <> 0 ->
          ly_dj (fr + 544) (fr + 544 + Rv) (RS6.rname mbv) (RS6.rname mbv + Z.of_nat (length nbv))) /\
       ly_dj (fr + 544) (fr + 544 + Rv) (fr + 2624) (fr + 2624 + 6) /\
       ly_dj (fr + 544) (fr + 544 + Rv) BOXA (BOXA + 6)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) BAC.REAC_CTRL_BUILD_AS_K ->
    addressable m BAC.BA_SW 56 -> addressable m (BAC.BA_FR + 72) 168 ->
    addressable m (fr + 2624) 6 -> addressable m BOXA 6 ->
    app_mem (fr + 2624 + 6) /\ app_mem (fr + 2624 + 7) -> app_mem (BOXA + 6) /\ app_mem (BOXA + 7) ->
    (mdv <> 0 -> addressable m mdv 296) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ RS6.has mbv <> 0 /\ RS6.rname mbv <> 0 ->
       addressable m (RS6.rname mbv) (Z.of_nat (length nbv))) ->
    (BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
       addressable m (fr + 544) Rv /\ app_mem (fr + 544 + Rv) /\
       (fr + 544 + Rv <= RT_LO \/ RT_HI <= fr + 544)) ->
    (bb = 1 -> addressable m BMB.JOIN_0014 32) -> (bb = 2 -> addressable m BMB.JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp)
       [(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)]
       [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mdv, mdv + 296); (fr + 2624, fr + 2624 + 6); (BOXA, BOXA + 6);
        (fr + 544, fr + 544 + Rv)] ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ RS6.has mbv <> 0 /\ RS6.rname mbv <> 0 ->
       fp_dj [(RS6.rname mbv, RS6.rname mbv + Z.of_nat (length nbv))] (fp_w [0%nat; 1%nat] FS)) ->
    BAC.reac_ctrl_build_as_tls m (bv_unsigned tp) FS
      (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81710) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81710 /\ getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\
         getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 10 = Z_to_bv 64 Rv /\ getr R 18 = s2 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\
         getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         munch ([(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)] ++
                fp_w [0%nat; 1%nat] FS ++
                [(shadow_addr (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K), shadow_addr (bv_unsigned sp))]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) BAC.REAC_CTRL_BUILD_AS_K /\
         fp [0%nat; 1%nat] m' (bv_unsigned tp) FS
            (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp)
            [(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)]
            [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mdv, mdv + 296); (fr + 2624, fr + 2624 + 6); (BOXA, BOXA + 6);
             (fr + 544, fr + 544 + Rv)] /\
         (exists ob, bytes_at rsegs m' (fr + 544) ob /\ Z.of_nat (length ob) = Rv) /\
         (* the emitted frame (the contract's post under go && E), with a5 = [A + 248] = 0x1234 *)
         (BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
            bytes_at rsegs m' (fr + 544)
              (em_fr dbv sbv CNT16 (Z_to_bv 8 205) (Z_to_bv 8 234) (BAP.ba_X mdv mbv nbv bb) Rv)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x816ec) fc None m (seg_rom rsegs)).
Proof.
  intros BAS ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr FS bb mdv Rv mbv nbv dbv sbv junk -> -> HA0 HA64 Hbb Hfr0 Hfre Hmd0 Hmd64
    RO312 RO272 RO264 RO256 RO248 Hgo HRv
    H8 HST HTBL HDJ1 HDL HDB HDJ2 HSL HSB HDJ3 HMD HNM HO64 HRWall
    HMI HAC HSW HHM HAPP HAW HSW56 HFR168 HD6 HS6 HDAPP HSAPP HMDA HNMA HOA HJ14 HJ13 HFP HNMD HTLS.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HP64v : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* the contract's R is Rv, and its len is Rv whenever go && E holds *)
  assert (HR : (if BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb
                then 52 + 36 * bm_uw mdv (firstn 8 (skipn 16 mbv)) else 0) = Rv)
    by (rewrite Hgo, HRv; reflexivity).
  assert (HgE : BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
                52 + 36 * bm_uw mdv (firstn 8 (skipn 16 mbv)) = Rv).
  { intros H. rewrite <- HR, H. reflexivity. }
  unfold BAC.reac_ctrl_build_as_contract in BAS. cbv zeta in BAS.
  do 9 step.
  eapply evt_cut.
  { eapply BAS with (o := fr + 544) (md := mdv) (b := bb) (d := fr + 2624) (s := BOXA) (ns := 0)
      (mb := mbv) (nb := nbv) (db := dbv) (sb := sbv) (junk := junk) (FS := FS);
      try assumption; try reflexivity; try (apply MState.unsigned_lit; lia); try lia.
    all: try rewrite HR.
    all: try assumption.
    all: intros Hge; rewrite (HgE Hge); first [exact (HRWall Hge) | exact (HOA Hge)]. }
  intros ms' PO.
  rewrite HR in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Ems & MU & WM & MI & ST & AC' & SW' & AW & FP' & Hgo0 & Hout).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81710)) with (Z_to_bv 64 0x81710)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the out[] bytes: the emitted frame when E holds, none otherwise *)
  assert (Hob : exists ob, bytes_at rsegs m' (fr + 544) ob /\ Z.of_nat (length ob) = Rv).
  { destruct (BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb) eqn:EgE.
    - destruct (Hout ltac:(first [exact EgE | reflexivity])) as (Hbs & _).
      destruct (HMD ltac:(lia)) as (_ & _ & HmbL & _).
      rewrite <- (HgE ltac:(first [exact EgE | reflexivity])).
      eexists. split; [exact Hbs|].
      pose proof (r6_bmuw_nonneg mdv (firstn 8 (skipn 16 mbv))) as Hnn.
      apply r6_emfr_len; [exact HDL | exact HSL | apply r6_baX_len; exact HmbL | lia].
    - exists []. rewrite <- HR. try rewrite EgE.
      split; [|reflexivity]. split; [lia|]. split; [cbn [length]; lia|].
      intros i Hi. cbn [length] in Hi. lia. }
  assert (Hfb : BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
            bytes_at rsegs m' (fr + 544)
              (em_fr dbv sbv CNT16 (Z_to_bv 8 205) (Z_to_bv 8 234) (BAP.ba_X mdv mbv nbv bb) Rv)).
  { intros Hge. destruct (Hout Hge) as (Hbs & _). rewrite <- (HgE Hge).
    match type of Hbs with
    | bytes_at _ _ _ (em_fr _ _ ?c _ _ _ _) =>
        replace c with CNT16 in Hbs
          by first [vm_compute; reflexivity | unfold CNT16; rewrite MState.unsigned_lit by lia; reflexivity]
    end.
    exact Hbs. }
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact AW|].
  split; [try replace (fr + 2630) with (fr + 2624 + 6) by lia; exact FP'|].
  split; [exact Hob | exact Hfb].
Qed.

(* ---- the normalized memory: every address at or above GT is read-write in the image (R4) ---- *)

Lemma r6_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r6_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r6_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r6_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r6_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r6_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r6_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r6_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r6_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r6_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r6_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r6_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r6_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r6_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r6_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r6_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r6_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

(* The runtime cells, the side stack's thread cells and its state are byte facts, so they move with the bytes. *)
Lemma r6_cells_tr : forall m m0, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_cells m -> asan_cells m0.
Proof.
  intros m m0 TB H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* addressable reads only shadow bytes through mrd, which mem_rel keeps. *)
Lemma r6_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma r6_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma r6_tls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k TB
    (T1 & T2 & T3 & T4 & T5 & Hk & T6 & T7 & T8 & T9 & (tb & te & T10) & T11 & T12 & T13 & T14 & T15 & T16 &
     HDB & T17).
  unfold asan_tls_cells.
  repeat match goal with |- _ /\ _ => split end.
  all: try (apply TB; assumption).
  all: try lia.
  all: try assumption.
  exists tb, te. apply TB. exact T10.
Qed.

Lemma r6_cls_tr : forall m m0 FS c, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  fp_cls m FS c -> fp_cls m0 FS c.
Proof.
  intros m m0 FS c TB (Hc & h & flags & HH & HF & HFl & HFb).
  split; [exact Hc|]. exists h, flags. split; [apply TB; exact HH|]. split; [apply TB; exact HF|].
  split; [exact HFl | exact HFb].
Qed.

Lemma r6_fp_tr : forall m m0 cs TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (forall l h, 0x5fe000 <= l -> stk rsegs m l h -> stk rsegs m0 l h) ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros m m0 cs TP FS lo hi W D TB TSk
    (DT & TSv & C & T & DB & k & Htls & Htp & (P1 & P2 & P3 & P4 & P5) & H88 & H96 & Hcls & Hlo & Happ &
     Hd1 & Hd2).
  exists DT, TSv, C, T, DB, k.
  split; [exact (r6_tls_tr m m0 TP DT TSv C T DB k TB Htls)|].
  split; [apply TB; exact Htp|].
  split.
  { split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    apply TSk; [unfold ASAN_GT in P3; lia | exact P5]. }
  split; [apply TB; exact H88|]. split; [apply TB; exact H96|].
  split; [eapply Forall_impl; [|exact Hcls]; intros c Hc; exact (r6_cls_tr m m0 FS c TB Hc)|].
  split; [exact Hlo|]. split; [exact Happ|]. split; [exact Hd1 | exact Hd2].
Qed.

(* ---- the segment on the cuts ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fsfree.
Module TFF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.Tac_fsfree.

(* PRA (adopt 9 of a working branch: A4's frame-loop pointer spills; v1.9: eleven conjuncts, [A+168] = fr + 2880 twice) is
   carried by any map that carries each of its spills (R5's r5_pra). *)
Lemma r6_pra : forall fr (regs regs' : bvmap 5 word) m m',
  (forall off v, In off [136; 280; 168; 192; 200; 216; 104; 288; 296; 304] ->
     spill regs m off v -> spill regs' m' off v) ->
  PRA fr regs m -> PRA fr regs' m'.
Proof.
  intros fr regs regs' m m' K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). unfold PRA.
  split; [apply K; [cbn [In]; lia | exact H1]|]. split; [apply K; [cbn [In]; lia | exact H2]|].
  split; [apply K; [cbn [In]; lia | exact H3]|]. split; [apply K; [cbn [In]; lia | exact H4]|].
  split; [apply K; [cbn [In]; lia | exact H5]|]. split; [apply K; [cbn [In]; lia | exact H6]|].
  split; [apply K; [cbn [In]; lia | exact H7]|]. split; [apply K; [cbn [In]; lia | exact H8]|].
  split; [apply K; [cbn [In]; lia | exact H9]|]. split; [apply K; [cbn [In]; lia | exact H10]|].
  apply K; [cbn [In]; lia | exact H11].
Qed.

(* The run lemma: an evt on the normalized memory, lifted to SR on the real configuration (R4's r4_run). *)
Section Run.
Context {fx : FPState}.

Lemma r6_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r6_wx Hro HE)
    as HE'.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE' | exact Hh |].
  intros ms' md' (can & (s0 & (R & pc' & m0' & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
  subst s0.
  destruct can as [cr cf cp cs cv cc cm co].
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst.
  apply (HK _ _ _ regs' _ md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

End Run.

Section R6.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The ending callee reac_ctrl_build_as (BAS@0x8170c), taken on its lib/B contract, never on its code. *)
Hypothesis BASH : BAC.reac_ctrl_build_as_contract.

(* The inner lists of the allocator laws this file reads, taken apart once each, by statement where the law allows
   (a Theorem Labs lane 15:32Z: append-only at every level; a new generation touches these lemmas, not every site). *)
Lemma r6_fsok : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md FS HAH Hw HFS.
  decompose [and ex] (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
    H mem md FS HAH Hw HFS); assumption.
Qed.

Lemma r6_fsok_rw : forall mem FS, AC.a_fs_ok mem FS ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof. intros mem FS Hok. unfold AC.a_fs_ok in Hok. destruct Hok as (Hwr & _). exact Hwr. Qed.

Lemma r6_fsp : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw HFS)
    as P.
  decompose [and] P. split; [assumption | split; assumption].
Qed.

Lemma r6_blk : forall H mem md q kk,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (q, kk) H ->
  4096 <= q /\ q + kk <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, q <= a < q + kk -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md q kk HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md q kk HAH Hin)
    as (_ & X2 & X3 & _ & X5).
  split; [exact X2|]. split; [exact X3|].
  intros a Ha. destruct (X5 a Ha) as (Y1 & _ & _ & _ & Y5). exact (conj Y1 Y5).
Qed.

(* ---- facts read off FRA (F3's f3_fr_* / f3_A_app / f3_sh_in) ---- *)

Lemma r6_fr_stk : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  stk rsegs mem fr (fr + 3136).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (_ & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hlo : 0 <= fr).
  { pose proof (Happ fr ltac:(lia)) as H. unfold app_mem, LOWMEM_END, HIGHMEM_BEG in H. lia. }
  assert (Hhi2 : fr + 3136 <= 2 ^ 64).
  { pose proof (Happ (fr + 3135) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
  - destruct Hwin as (Hw0 & Hw1 & Hwv).
    split; [exact Hlo|]. split; [exact Hhi2|]. intros a Ha. apply Hwv.
    unfold AC.aspZ in Haspz. rewrite Hspfr in Haspz. lia.
  - split; [exact Hlo|]. split; [exact Hhi2|]. intros a Ha.
    destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
    destruct (r6_fsok_rw mem FSa (r6_fsok _ mem md FSa HAH Hwa HFSar) a ltac:(lia)) as (Hw & bb & Hb).
    split; [exact Hw|]. exists bb. rewrite <- r6_mbyte_mrd. exact Hb.
Qed.

Lemma r6_A_app : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  HIGHMEM_BEG < bv_unsigned (getr regs 9) /\ bv_unsigned (getr regs 9) + 448 <= g_S g /\
  g_S g < APPMEM_END /\ HIGHMEM_BEG <= g_S g - AF.SLOT_STACK.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_small. unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  rewrite HbvA. lia.
Qed.

Lemma r6_sh_in : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA x Hx.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ). unfold AC.GT in Hgt.
  assert (Hfrm : fr mod 32 = 0).
  { destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
      Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & _). exact Hfrm. }
  assert (H8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x).
  { rewrite r6_sh_frame_of by lia. unfold Sfr. lia. }
  rewrite <- E. apply shadow_of_app. apply Happ. lia.
Qed.

(* The registered globals of the image lie below the image top GT, and a range inside one of them is addressable. *)
Lemma r6_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a (lo & len & Hin & Hr).
  assert (HB : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? AC.GT)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB. pose proof (HB _ Hin) as Hb.
  apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  cbn [fst snd] in *. lia.
Qed.

Lemma r6_ag : forall m p n lo len,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  In (lo, len) AF.frame_AG -> 0 <= lo -> lo <= p -> 0 <= n -> p + n <= lo + len -> lo + len <= AC.GT ->
  addressable m p n.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m p n lo len HAG Hin Hlo0 Hlo Hn Hhi HGT.
  apply r6_addr_of1; [lia | exact Hn | unfold AC.GT, APPMEM_END in *; lia |].
  intros i Hi. apply HAG. exists lo, len. split; [exact Hin | lia].
Qed.

Ltac r6_in := unfold AF.frame_AG; repeat first [ left; reflexivity | right ].

(* The spill base named by a spill conjunct is the A of register 9 (R4's r4_spill_A). *)
Lemma r6_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* FSREC (SlotInv.v's side-arm FakeStack frame record) across a run that writes none of its bytes: the tp word
   (in the image, below GT), the class-6 flag byte FS + 36352 + j (below FS + 36864) and the slot's last word
   fr + 4088 (fr = FS + 6328320 + 4096 j).  Tac_slot's fsrec_munch / fsrec_munch_lo do not apply to the build_as
   call: its write set holds app bytes outside the frame body (its window) and bytes below stklo (the class-0 /
   class-1 side-stack areas), so the premise here names the three byte groups themselves. *)
Lemma r6_fsrec : forall mem mem' W fr,
  FSREC fr mem -> munch W mem mem' ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall FS j x, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> 0 <= j < 256 ->
     fr = FS + 6328320 + j * 4096 ->
     (FS + 36352 <= x < FS + 36864 \/ fr + 3136 <= x < fr + 4096) -> outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HWlo HW.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : fs_B 6 = 4096) by reflexivity.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (Hfl : fs_flag FS 6 j = FS + 36352 + j) by (unfold fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold fs_frame, fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < AC.GT)
      by (rewrite HGTv; unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by (rewrite HGTv in Hx; lia). apply HWlo. exact Hx. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply (HW FS j x Htp HFSr Hj Hfrv). left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply (HW FS j x Htp HFSr Hj Hfrv). right. rewrite HB6 in Hx. lia. }
Qed.

(* FRA moves across a run whose write set W keeps: the image and the runtime cells below GT, the frame header,
   everything at or above the spill base A, the frame's 392 shadow bytes; whose written entry-window bytes are
   readable afterwards; which keeps every shadow byte readable (so RT_meta_write); and after which the registered
   globals and the slot window outside the frame are still addressable (F3's f3_fra_run, R4's r4_fra). *)
Lemma r6_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W -> shadow_rw mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) <= x -> outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + 392 -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HSW' HAH' HSTK HWlo HWhdr HWA HWsh HWwin HAG' HWA'
    HREC HIN1' HIN2' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA0 &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWA.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hx0 Hx1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWlo. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD (fun a Ha => proj2 (HSW' a Ha)))|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS0 Hw HFSr. apply (Hfsb FS0); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * exact (HREC Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. apply HWsh. lia. }
  split.
  { exact (r6_stk W mem mem' _ _ Hwin MU WM HWwin). }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWA. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. split; [exact HIN1' | exact HIN2'].
Qed.

(* The heap invariant, ownership and the stack bounds across the call: the write set touches the stack window, the
   frame's out[] buffer, the class-0 / class-1 side-stack areas and the shadow of the window, so AH moves by
   a_laws_fs_store with the side stack's state rebuilt by r6_fs_ok. *)
Lemma r6_ah : forall g fr hb regs mem mem' md W FS,
  FRA B APIf ra g fr hb regs mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall q, FS <= q < FS + AC.FS_SIZE -> exists b, mbyte rsegs mem' q = Some b) ->
  (forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 16) -> ~ (FS + 4096 <= q < FS + 28672) -> outside W q) ->
  fp_cls mem' FS 0%nat -> fp_cls mem' FS 1%nat ->
  (forall q, 0 <= q < 2 ^ 64 ->
     ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
     ~ (FS <= q < FS + AC.FS_SIZE) ->
     ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
     mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W FS HFRA Hwtp HFSr HFSsz MU WM Hpres Hkeep HC0 HC1 Hagree.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HAH : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md).
  { destruct HFRA as (A & sp & s5 & _ & HAH & _). exact HAH. }
  assert (Hwrit : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
  assert (Hok : AC.a_fs_ok mem FS) by exact (r6_fsok _ mem md FS HAH Hwtp HFSr).
  pose proof (r6_fs_ok mem mem' FS W Hok MU Hwrit Hpres Hkeep HC0 HC1 ltac:(lia) HFSsz) as Hok'.
  exact (AC.a_laws_fs_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md FS HAH Hwtp HFSr Hagree Hwrit Hok').
Qed.

(* ---- the write set of the call and the addresses outside it ---- *)

(* The class-0 and class-1 side-stack ranges all lie in [FS, FS + 2134016) or in its shadow. *)
Lemma r6_fpw_out : forall FS x,
  0 <= FS -> ~ (FS <= x < FS + 2134016) -> ~ (shadow_addr FS <= x < shadow_addr (FS + 2134016)) ->
  outside (fp_w [0%nat; 1%nat] FS) x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros FS x HFS H1 H2.
  pose proof (r6_sh_ge (FS + 36864) FS ltac:(lia)) as S1.
  pose proof (r6_sh_ge (FS + 2134016) (FS + 1085440) ltac:(lia)) as S2.
  pose proof (r6_sh_ge (FS + 1085440) FS ltac:(lia)) as S3.
  pose proof (r6_sh_ge (FS + 2134016) (FS + 36864) ltac:(lia)) as S4.
  assert (E1 : fs_hint FS 0%nat = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E2 : fs_hint FS 1%nat = FS + 8) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E3 : fs_flag FS 0%nat 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E4 : fs_flag FS 1%nat 0 = FS + 20480) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E5 : fs_M 0%nat = 16384) by reflexivity.
  assert (E6 : fs_M 1%nat = 8192) by reflexivity.
  assert (E7 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E8 : fs_frame FS 0%nat (fs_M 0%nat) = FS + 1085440) by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (E9 : fs_frame FS 1%nat 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E10 : fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  cbn [fp_w fp_w1 flat_map app].
  rewrite E1, E2, E3, E4, E7, E8, E9, E10, E5, E6.
  cbn [outside]. repeat split; try lia; exact I.
Qed.

(* A byte of the side stack's metadata region that is neither a class-0 / class-1 hint word nor one of their flag
   bytes is outside the call's class-0 / class-1 write set: the frames begin at FS + 36864, above it. *)
Lemma r6_fpw_meta : forall FS q,
  0 <= FS -> FS <= q < FS + 36864 -> ~ (FS <= q < FS + 16) -> ~ (FS + 4096 <= q < FS + 28672) ->
  ~ (shadow_addr FS <= q < shadow_addr (FS + 2134016)) ->
  outside (fp_w [0%nat; 1%nat] FS) q.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros FS q HFS Hq H1 H2 H3.
  pose proof (r6_sh_ge (FS + 36864) FS ltac:(lia)) as S1.
  pose proof (r6_sh_ge (FS + 2134016) (FS + 1085440) ltac:(lia)) as S2.
  pose proof (r6_sh_ge (FS + 1085440) FS ltac:(lia)) as S3.
  pose proof (r6_sh_ge (FS + 2134016) (FS + 36864) ltac:(lia)) as S4.
  assert (E1 : fs_hint FS 0%nat = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E2 : fs_hint FS 1%nat = FS + 8) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E3 : fs_flag FS 0%nat 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E4 : fs_flag FS 1%nat 0 = FS + 20480) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E5 : fs_M 0%nat = 16384) by reflexivity.
  assert (E6 : fs_M 1%nat = 8192) by reflexivity.
  assert (E7 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E8 : fs_frame FS 0%nat (fs_M 0%nat) = FS + 1085440) by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (E9 : fs_frame FS 1%nat 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E10 : fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  cbn [fp_w fp_w1 flat_map app].
  rewrite E1, E2, E3, E4, E7, E8, E9, E10, E5, E6.
  cbn [outside]. repeat split; try lia; exact I.
Qed.

(* Every range of the class-0 / class-1 write set starts at or above the image top GT. *)
Lemma r6_fpw_gt : forall FS r, AC.GT <= FS -> In r (fp_w [0%nat; 1%nat] FS) -> AC.GT <= fst r.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros FS r HFS Hr.
  assert (HK : forall y, 0 <= y -> AC.GT <= shadow_addr y).
  { intros y Hy. unfold shadow_addr, AC.GT, ASAN_K. pose proof (Z.div_pos y 8 Hy ltac:(lia)). lia. }
  assert (HG : 0 <= FS) by (unfold AC.GT in HFS; lia).
  cbn [fp_w fp_w1 flat_map app] in Hr.
  repeat (destruct Hr as [<-|Hr]);
    try (cbn [fst]; unfold fs_hint, fs_flag, fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia);
    try (cbn [fst]; apply HK; unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  destruct Hr.
Qed.

(* A point of application memory is apart from the shadow of any application range. *)
Lemma r6_app_not_sh : forall x lo hi, app_mem x -> 0 <= lo -> hi <= APPMEM_END ->
  ~ (shadow_addr lo <= x < shadow_addr hi).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros x lo hi Hx Hlo Hhi.
  assert (H1 : ASAN_K <= shadow_addr lo)
    by (unfold shadow_addr; pose proof (Z.div_pos lo 8 Hlo ltac:(lia)); lia).
  destruct (Z_lt_le_dec hi 0) as [Hneg|Hpos].
  - pose proof (r6_sh_ge lo hi ltac:(lia)) as Hle. lia.
  - pose proof (r6_sh_hi hi ltac:(lia)) as H2.
    unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma r6_out_all : forall Lo S o R FS x,
  ~ (Lo <= x < S) -> ~ (o <= x < o + R) -> outside (fp_w [0%nat; 1%nat] FS) x ->
  ~ (shadow_addr Lo <= x < shadow_addr S) ->
  outside ([(Lo, S); (o, o + R)] ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Lo S o R FS x H1 H2 H3 H4.
  apply r6_out_app; [cbn [outside]; split; [lia | split; [lia | exact I]]|].
  apply r6_out_app; [exact H3 | cbn [outside]; split; [lia | exact I]].
Qed.

(* ---- the turn records: the identity record RID is 38 bytes and the fragment record RFG 72 bytes at every turn
   (ID0 / z72, kept by ING and by each fragment case), so both lie inside the frame ---- *)

Lemma r6_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r6_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r6_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact Hs].
  assert (Hn : 1 <= RcFrag.fg_n g <= 22).
  { unfold RcFrag.fg_fr in Efr.
    apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr H22]. apply andb_prop in Efr as [_ H1].
    apply Z.leb_le in H22. apply Z.leb_le in H1. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first, RcFrag.fg_body, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + assert (HT : RcFrag.fg_T st g <= 64).
      { unfold RcFrag.fg_keep in Ek. apply andb_prop in Ek as [_ HT]. apply Z.leb_le in HT. exact HT. }
      destruct (RcFrag.fg_close st g); cbn [negb fg_next];
        apply RcFragLib.rf_clear_length; apply RcFragLib.rf_fg_join_length; assumption.
    + cbn [fg_next]. apply RcFragLib.rf_clear_length. exact Hs.
Qed.

Lemma r6_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r6_fgst_len; [exact IH | apply r6_rtg_len]].
Qed.

(* ---- the segment lemma ---- *)

Lemma seg_R6 : forall b : nat, Hat B APIf ra (Inv_B81710_at B APIf ra) b -> Hat B APIf ra (Inv_B816ec_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HRS & HRBE & Hs5r & HR6X & HM2 & Hr27).
  subst c. rewrite SEGS.
  destruct HRBE as (H128 & H312 & H272 & H264 & H256 & H248 & H56 & H184 & H144 & H8 & H32 & H24 & H16 &
    H96 & H120 & H240 & H232 & H224 & H176 & H208 & H64 & HOUTA & HA2176 & HNMr & HAour' & HTBL' & HBOX' & HMB' &
    HPRA & H152 & H112 & HA2256 & H160).
  destruct HR6X as (HAout & HAour & HTBL & HBOXb & HMBb & HNMf).
  destruct HRS as (Hble & HCUR & HOUR & Hr22 & HIDB & HFGB).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & spv & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillf & Hself & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlostk & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGTfr & Happ).
  pose proof (r6_fr_stk g fr [] regs mem md HFRA) as Hfstk.
  pose proof (r6_A_app g fr [] regs mem md HFRA) as (HAhi & HA448b & HSapp & HSlo).
  pose proof (r6_sh_in g fr [] regs mem md HFRA) as HshIn.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  unfold AC.aspZ in *.
  (* numbers *)
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HBK : BAC.REAC_CTRL_BUILD_AS_K = 4640) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HCATv : CAT = 652832) by reflexivity.
  assert (HBOXv : BOXA = 135488) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HFSZ' : FS_SIZE = 11571200) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (Hfr0 : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (Hrnbb : 0 <= rnb g b <= 1492) by (unfold rnb; apply r6_rtn_bnd).
  pose proof (Hplace BAC.REAC_CTRL_BUILD_AS_K ltac:(lia)) as Hsep.
  pose proof (r6_mrow_rng (g_in g)) as (Hmrow1 & Hmrow8).
  assert (HbvA2 : fr + 3136 <= A) by (rewrite HbvA in HfrA; exact HfrA).
  assert (HGOtrue : BAP.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) = true) by (apply r6_go; lia).
  (* the call's side-stack package, built from FRA (Tac_fsfree's fra_fp): classes 0 and 1, window
     REAC_CTRL_BUILD_AS_K, the writes r6_W (the window and out[]'s first rnb g b bytes) and the data r6_D (image
     ranges below GT, our[] and out[] in the frame) *)
  destruct (TFF.fra_fp B APIf ra g fr [] regs mem md [0%nat; 1%nat] BAC.REAC_CTRL_BUILD_AS_K
              (r6_W g b fr (AC.aspZ regs)) (r6_D g b fr) HFRA) as (FS & HFP & HTLS & HDJfr & _).
  { intros cc Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; lia. }
  { rewrite HBK, HFN. lia. }
  { intros w Hw. unfold r6_W in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; unfold AC.aspZ; [left | right; left]; lia. }
  { assert (HBAFR : BAC.BA_FR = 656896) by reflexivity.
    intros d Hd. unfold r6_D in Hd. cbn [In] in Hd.
    destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; first [left; lia | right; left; lia]. }
  unfold r6_W, r6_D, AC.aspZ in HFP. unfold AC.aspZ in HTLS.
  (* the spill base of each argument spill is A *)
  destruct H312 as (A1 & HA1 & Hq312).
  assert (A1 = A) by (apply (r6_spill_A regs mem 312 (fr + 544) A A1 HA1 Hq312 Hr9); lia). subst A1.
  destruct H272 as (A2 & HA2 & Hq272).
  assert (A2 = A) by (apply (r6_spill_A regs mem 272 (mrow (g_in g)) A A2 HA2 Hq272 Hr9); lia). subst A2.
  destruct H264 as (A3 & HA3 & Hq264).
  assert (A3 = A) by (apply (r6_spill_A regs mem 264 (fr + 2624) A A3 HA3 Hq264 Hr9); lia). subst A3.
  destruct H256 as (A4 & HA4 & Hq256).
  assert (A4 = A) by (apply (r6_spill_A regs mem 256 0x21140 A A4 HA4 Hq256 Hr9); lia). subst A4.
  destruct H248 as (A5 & HA5 & Hq248).
  assert (A5 = A) by (apply (r6_spill_A regs mem 248 0x1234 A A5 HA5 Hq248 Hr9); lia). subst A5.
  destruct H128 as (A6 & HA6 & Hq128).
  assert (A6 = A) by (apply (r6_spill_A regs mem 128 0xe38f0000 A A6 HA6 Hq128 Hr9); lia). subst A6.
  (* the normalized memory the run is stepped on, and the transports onto it *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TS0 : forall l h, 0x5fe000 <= l -> stk rsegs mem l h -> stk rsegs (normalize rsegs mem) l h)
    by (intros l h Hl Hs; exact (r6_stk_rel mem (normalize rsegs mem) l h HR0 Hl Hs)).
  assert (TA0 : forall p n, addressable mem p n -> addressable (normalize rsegs mem) p n)
    by (intros p n Ha; exact (r6_addr_rel mem (normalize rsegs mem) p n HR0 Ha)).
  pose proof (r6_srw_rel mem (normalize rsegs mem) HR0 HSWm) as HSW0.
  pose proof (r6_cells_tr mem (normalize rsegs mem) TB0 HACm) as HAC0.
  (* the five loads read read-only cells *)
  pose proof (r6_ro8 _ (A + 312) (Z_to_bv 64 (fr + 544)) (TB0 _ _ Hq312)) as RO312.
  pose proof (r6_ro8 _ (A + 272) (Z_to_bv 64 (mrow (g_in g))) (TB0 _ _ Hq272)) as RO272.
  pose proof (r6_ro8 _ (A + 264) (Z_to_bv 64 (fr + 2624)) (TB0 _ _ Hq264)) as RO264.
  pose proof (r6_ro8 _ (A + 256) (Z_to_bv 64 0x21140) (TB0 _ _ Hq256)) as RO256.
  pose proof (r6_ro8 _ (A + 248) (Z_to_bv 64 0x1234) (TB0 _ _ Hq248)) as RO248.
  (* the out[] buffer as one writable cell *)
  pose proof (TS0 fr (fr + 3136) ltac:(lia) Hfstk) as Hfstk0.
  destruct (stk_split rsegs _ fr (fr + 544) (fr + 3136) Hfstk0 ltac:(lia)) as (_ & Hs2).
  destruct (stk_split rsegs _ (fr + 544) (fr + 544 + rnb g b) (fr + 3136) Hs2 ltac:(lia)) as (Hostk & _).
  destruct (stk_bytes rsegs _ (fr + 544) (fr + 544 + rnb g b) Hostk ltac:(lia)) as (junk & Hjl & Hjb).
  assert (RWo : rw_cells rsegs (normalize rsegs mem) (fr + 544) [CB (Z.to_nat (rnb g b)) junk]).
  { replace (Z.to_nat (rnb g b)) with (length junk) by lia. apply r6_rw_CB; [exact Hjb|].
    replace (Z.of_nat (length junk)) with (fr + 544 + rnb g b - (fr + 544)) by lia.
    exact (r6_wr_stk _ _ _ Hostk). }
  (* the window of the call *)
  assert (HHMlo : HIGHMEM_BEG <= bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) by lia.
  assert (Hsp0K : 0 <= bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) by lia.
  assert (Hwinle : bv_unsigned (getr regs 2) - FN_STACK <=
                   bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K <= bv_unsigned (getr regs 2))
    by lia.
  assert (HSTKw : stk rsegs mem (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)
                      (bv_unsigned (getr regs 2))).
  { destruct (stk_split rsegs mem (bv_unsigned (getr regs 2) - FN_STACK)
                (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                Hstkw Hwinle) as (_ & Hw). exact Hw. }
  assert (Hlo5 : 0x5fe000 <= bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)
    by (rewrite HBK; rewrite HHMv in HHMlo; rewrite HBK in HHMlo; lia).
  pose proof (TS0 _ _ Hlo5 HSTKw) as HSTKw0.
  assert (HAWwin : addressable mem (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)
                     BAC.REAC_CTRL_BUILD_AS_K).
  { apply r6_addr_of1; [lia | lia | lia |]. intros i Hi.
    apply HWA; [lia|]. destruct Hsep as [Hs|Hs]; lia. }
  pose proof (TA0 _ _ HAWwin) as HAWwin0.
  (* the image ranges the callee reads are addressable *)
  assert (HASW : addressable mem BAC.BA_SW 56).
  { eapply (r6_ag mem BAC.BA_SW 56 0x21980 56 HAG); [r6_in | lia | unfold BAC.BA_SW; lia | lia
      | unfold BAC.BA_SW; lia | lia]. }
  assert (HAFR : addressable mem (BAC.BA_FR + 72) 168).
  { eapply (r6_ag mem (BAC.BA_FR + 72) 168 0xa0600 264 HAG); [r6_in | lia | unfold BAC.BA_FR; lia | lia
      | unfold BAC.BA_FR; lia | lia]. }
  assert (HABOX : addressable mem BOXA 6).
  { eapply (r6_ag mem BOXA 6 0x21140 6 HAG); [r6_in | lia | lia | lia | lia | lia]. }
  assert (HAMD : addressable mem (mrow (g_in g)) 296).
  { eapply (r6_ag mem (mrow (g_in g)) 296 0x9f620 3256 HAG); [r6_in | lia | lia | lia | lia | lia]. }
  assert (HAJ14 : addressable mem BMB.JOIN_0014 32).
  { eapply (r6_ag mem BMB.JOIN_0014 32 0x21a60 32 HAG); [r6_in | lia | unfold BMB.JOIN_0014; lia | lia
      | unfold BMB.JOIN_0014; lia | lia]. }
  assert (HAJ13 : addressable mem BMB.JOIN_0013 32).
  { eapply (r6_ag mem BMB.JOIN_0013 32 0x21a20 32 HAG); [r6_in | lia | unfold BMB.JOIN_0013; lia | lia
      | unfold BMB.JOIN_0013; lia | lia]. }
  pose proof (TA0 _ _ HASW) as HASW0.
  pose proof (TA0 _ _ HAFR) as HAFR0.
  pose proof (TA0 _ _ HABOX) as HABOX0.
  pose proof (TA0 _ _ HAour) as HAour0.
  pose proof (TB0 _ _ HTBL) as HTBL0.
  pose proof (TB0 _ _ HOUR) as HOUR0.
  pose proof (TB0 _ _ HBOXb) as HBOX0.
  (* the small arithmetic premises of the contract *)
  assert (HDAPP : app_mem (fr + 2624 + 6) /\ app_mem (fr + 2624 + 7)) by (split; apply Happ; lia).
  assert (HSAPP : app_mem (BOXA + 6) /\ app_mem (BOXA + 7)) by (unfold app_mem; split; left; lia).
  assert (HDJfrw : forall p n, fr <= p -> p + n <= fr + 3136 ->
            ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2)) p (p + n)).
  { intros p n Hp Hn. unfold ly_dj. destruct Hsep as [Hs|Hs]; [right; lia | left; lia]. }
  assert (HAOUT : addressable mem (fr + 544) (rnb g b))
    by (apply (r6_addr_sub mem (fr + 544) 1492); [exact HAout | lia | lia | lia]).
  assert (HOAPP : app_mem (fr + 544 + rnb g b)) by (apply Happ; lia).
  assert (HORT : fr + 544 + rnb g b <= RT_LO \/ RT_HI <= fr + 544) by (right; unfold RT_HI; lia).
  (* the side stack of the call *)
  pose proof HFP as HFP0.
  destruct HFP0 as (DT & TS & C & T & DB & k & HTLSc & HFStp & HFSpl & HFS88 & HFS96 & HCLS & HFSlo & HFSapp &
                    HWdj & HDdj).
  assert (HFSw : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP.
    pose proof (KindBGlue.bytes_at_le8_word rsegs mem RT_TP (Z_to_bv 64 FS) HFStp) as Hw.
    rewrite MState.unsigned_lit in Hw; [exact Hw|].
    destruct HFSpl as (HF1 & HF2 & HF3 & HF4 & HF5). unfold stk, FS_SIZE in HF5. lia. }
  assert (HFSrange : 0 < FS /\ FS mod 4096 = 0 /\ AC.GT <= FS /\ FS + AC.FS_SIZE <= APPMEM_END).
  { destruct HFSpl as (HF1 & HF2 & HF3 & HF4 & HF5).
    pose proof (HF4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hap.
    unfold app_mem, ASAN_GT, FS_SIZE, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, AC.GT, AC.FS_SIZE in *. lia. }
  assert (HFSapp' : forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
  { destruct HFSpl as (_ & _ & _ & HF4 & _). intros a Ha. apply HF4. lia. }
  assert (HFSfr : FS + 6328320 <= fr) by (apply (HfsS FS HFSw); lia).
  (* the side stack's base is the one word at tp *)
  assert (HFSuniq : forall FS', word_mem rsegs mem (AC.as_tp AC.ASYMS) FS' -> 0 <= FS' < 2 ^ 64 -> FS' = FS).
  { intros FS' Hwb HFS'r.
    change (AC.as_tp AC.ASYMS) with RT_TP in Hwb.
    pose proof (KindBGlue.word_mem_le8 rsegs mem RT_TP FS' Hwb ltac:(lia)
                  ltac:(unfold RT_TP; lia) ltac:(unfold RT_TP; lia)) as Hb1.
    pose proof HFSw as HFSw2. change (AC.as_tp AC.ASYMS) with RT_TP in HFSw2.
    pose proof (KindBGlue.word_mem_le8 rsegs mem RT_TP FS HFSw2 ltac:(lia)
                  ltac:(unfold RT_TP; lia) ltac:(unfold RT_TP; lia)) as Hb2.
    pose proof (fl_le8_eq [] mem mem RT_TP (Z_to_bv 64 FS') (Z_to_bv 64 FS) Hb1 Hb2
                  (munch_refl [] mem) (fun _ _ => I)) as Heq.
    apply (f_equal (bv_unsigned (n:=64))) in Heq.
    rewrite !MState.unsigned_lit in Heq by lia. exact Heq. }
  assert (HFS8 : FS mod 8 = 0) by (destruct HFSrange as (_ & Hm & _); Z.div_mod_to_equations; lia).
  assert (HFSstklo : FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct (r6_fsp _ mem md FS HAH HFSw ltac:(lia)) as (_ & He & _). exact He. }
  (* the remaining contract premises, on the normalized memory, pre-asserted so that the run applies by
     assumption *)
  assert (Hsp16 : bv_unsigned (getr regs 2) mod 16 = 0) by (rewrite Haspz; exact Hspm).
  assert (HSPapp : bv_unsigned (getr regs 2) <= APPMEM_END) by lia.
  assert (Htp : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS).
  { rewrite Hr4. apply MState.unsigned_lit. unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  assert (HFP' : fp [0%nat; 1%nat] (normalize rsegs mem) (bv_unsigned (getr regs 4)) FS
                   (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                   [(bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned (getr regs 2));
                    (fr + 544, fr + 544 + rnb g b)]
                   [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mrow (g_in g), mrow (g_in g) + 296);
                    (fr + 2624, fr + 2624 + 6); (BOXA, BOXA + 6); (fr + 544, fr + 544 + rnb g b)]).
  { rewrite Htp. exact (r6_fp_tr mem (normalize rsegs mem) _ _ _ _ _ _ _ TB0 TS0 HFP). }
  assert (HTLS' : BAC.reac_ctrl_build_as_tls (normalize rsegs mem) (bv_unsigned (getr regs 4)) FS
                    (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))).
  { rewrite Htp. intros DT' TS' C' T' DB' k' Hc. apply HTLS.
    apply (r6_tls_tr (normalize rsegs mem) mem _ _ _ _ _ _ _
             (fun a bs Hb => proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
    exact Hc. }
  assert (HdbL : length (OUR (g_in g)) = 6%nat) by (apply OUR_length).
  assert (HsbL : length box6 = 6%nat) by reflexivity.
  assert (HmbL : length (rt_mb (g_in g)) = 296%nat)
    by (unfold rt_mb, rowb, img;
        destruct (Lib.Image.image_bytes rsegs (CAT + CAT_ROW * istar (g_in g)) 296) eqn:Ei;
        [exact (Lib.Image.image_bytes_length rsegs 296 _ _ Ei) | apply repeat_length]).
  assert (HRdef : rnb g b =
                  (if BAP.ba_E (bm_uw (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g))))) (rt_mb (g_in g))
                        (Z.of_nat b)
                   then 52 + 36 * bm_uw (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g)))) else 0))
    by reflexivity.
  assert (HDJtbl : ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                     (BAC.BA_FR + 72) (BAC.BA_FR + 240)) by (unfold ly_dj, BAC.BA_FR; right; lia).
  assert (HDJd : ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                   (fr + 2624) (fr + 2624 + 6)) by (apply HDJfrw; lia).
  assert (HDJs : ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                   BOXA (BOXA + 6)) by (unfold ly_dj; right; lia).
  assert (HMDall : mrow (g_in g) <> 0 -> mrow (g_in g) mod 8 = 0 /\ mrow (g_in g) + 296 <= 2 ^ 64 /\
                     length (rt_mb (g_in g)) = 296%nat /\
                     bytes_at rsegs (normalize rsegs mem) (mrow (g_in g)) (rt_mb (g_in g)) /\
                     ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                           (mrow (g_in g)) (mrow (g_in g) + 296)).
  { intros _. split; [exact Hmrow8|]. split; [lia|]. split; [exact HmbL|]. split; [exact (TB0 _ _ HMBb)|].
    unfold ly_dj. right. lia. }
  assert (HNMall : mrow (g_in g) <> 0 ->
            (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RS6.has (rt_mb (g_in g)) <> 0 /\
            RS6.rname (rt_mb (g_in g)) <> 0 ->
            name_ok (rt_nb (g_in g)) /\
            bytes_at rsegs (normalize rsegs mem) (RS6.rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
            ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                  (RS6.rname (rt_mb (g_in g)))
                  (RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))))).
  { intros _ Hnm. destruct (HNMf Hnm) as (Hok & Hbs & Hadr & Hpos & Hhi).
    split; [exact Hok|]. split; [exact (TB0 _ _ Hbs)|]. unfold ly_dj. right. lia. }
  assert (HO64 : fr + 544 <> 0 -> fr + 544 + 1492 <= 2 ^ 64) by (intros _; lia).
  assert (HRWall : BAP.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) &&
                   BAP.ba_E (bm_uw (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g))))) (rt_mb (g_in g))
                     (Z.of_nat b) = true ->
            rw_cells rsegs (normalize rsegs mem) (fr + 544) [CB (Z.to_nat (rnb g b)) junk] /\
            ly_dj (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
                  (fr + 544) (fr + 544 + rnb g b) /\
            ly_dj (fr + 544) (fr + 544 + rnb g b) (BAC.BA_FR + 72) (BAC.BA_FR + 240) /\
            ly_dj (fr + 544) (fr + 544 + rnb g b) (mrow (g_in g)) (mrow (g_in g) + 296) /\
            ((Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RS6.has (rt_mb (g_in g)) <> 0 /\
             RS6.rname (rt_mb (g_in g)) <> 0 ->
               ly_dj (fr + 544) (fr + 544 + rnb g b) (RS6.rname (rt_mb (g_in g)))
                     (RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))))) /\
            ly_dj (fr + 544) (fr + 544 + rnb g b) (fr + 2624) (fr + 2624 + 6) /\
            ly_dj (fr + 544) (fr + 544 + rnb g b) BOXA (BOXA + 6)).
  { intros _. split; [exact RWo|]. split; [apply HDJfrw; lia|].
    split; [unfold ly_dj, BAC.BA_FR; right; lia|].
    split; [unfold ly_dj; right; lia|].
    split; [intros Hnm; destruct (HNMf Hnm) as (_ & _ & _ & Hpos & Hhi); unfold ly_dj; right; lia|].
    split; [unfold ly_dj; left; lia | unfold ly_dj; right; lia]. }
  assert (HMDA : mrow (g_in g) <> 0 -> addressable (normalize rsegs mem) (mrow (g_in g)) 296)
    by (intros _; exact (TA0 _ _ HAMD)).
  assert (HNMA : mrow (g_in g) <> 0 ->
            (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RS6.has (rt_mb (g_in g)) <> 0 /\
            RS6.rname (rt_mb (g_in g)) <> 0 ->
            addressable (normalize rsegs mem) (RS6.rname (rt_mb (g_in g))) (Z.of_nat (length (rt_nb (g_in g))))).
  { intros _ Hnm. destruct (HNMf Hnm) as (_ & _ & Hadr & _). exact (TA0 _ _ Hadr). }
  assert (HOAall : BAP.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) &&
                   BAP.ba_E (bm_uw (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g))))) (rt_mb (g_in g))
                     (Z.of_nat b) = true ->
            addressable (normalize rsegs mem) (fr + 544) (rnb g b) /\ app_mem (fr + 544 + rnb g b) /\
            (fr + 544 + rnb g b <= RT_LO \/ RT_HI <= fr + 544)).
  { intros _. split; [exact (TA0 _ _ HAOUT)|]. split; [exact HOAPP | exact HORT]. }
  assert (HJ14 : Z.of_nat b = 1 -> addressable (normalize rsegs mem) BMB.JOIN_0014 32)
    by (intros _; exact (TA0 _ _ HAJ14)).
  assert (HJ13 : Z.of_nat b = 2 -> addressable (normalize rsegs mem) BMB.JOIN_0013 32)
    by (intros _; exact (TA0 _ _ HAJ13)).
  assert (HFPWgt : forall r, In r (fp_w [0%nat; 1%nat] FS) -> AC.GT <= fst r)
    by (intros r Hr; apply (r6_fpw_gt FS r); [lia | exact Hr]).
  assert (HNMD : mrow (g_in g) <> 0 ->
            (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RS6.has (rt_mb (g_in g)) <> 0 /\
            RS6.rname (rt_mb (g_in g)) <> 0 ->
            fp_dj [(RS6.rname (rt_mb (g_in g)),
                    RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))))]
                  (fp_w [0%nat; 1%nat] FS)).
  { intros _ Hnm. destruct (HNMf Hnm) as (_ & _ & _ & Hpos & Hhi).
    unfold fp_dj. constructor; [|constructor]. apply Forall_forall. intros r Hr.
    pose proof (HFPWgt r Hr) as Hge. unfold ly_dj. cbn [fst snd]. left. lia. }
  (* rnb g b <> 0 is the call's go && E (go holds at the loop head; E is n_b's own test) *)
  assert (HgoE : rnb g b <> 0 ->
            BAP.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) &&
            BAP.ba_E (bm_uw (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g))))) (rt_mb (g_in g))
              (Z.of_nat b) = true).
  { intros Hn0. rewrite HGOtrue. cbn [andb].
    destruct (BAP.ba_E (bm_uw (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g))))) (rt_mb (g_in g))
                (Z.of_nat b)) eqn:EE; [reflexivity|].
    exfalso. apply Hn0. rewrite HRdef. rewrite ?EE. reflexivity. }
  (* the run, on the normalized memory *)
  apply (r6_run regs (Z_to_bv 64 0x816ec) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81710 /\
       getr R 1 = Z_to_bv 64 0x81710 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
       getr R 10 = Z_to_bv 64 (rnb g b) /\ getr R 27 = getr regs 27 /\
       getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\
       munch ([(bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned (getr regs 2));
               (fr + 544, fr + 544 + rnb g b)] ++ fp_w [0%nat; 1%nat] FS ++
              [(shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K),
                shadow_addr (bv_unsigned (getr regs 2)))]) (normalize rsegs mem) m0' /\
       wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2)) /\
       asan_cells m0' /\ shadow_rw m0' /\
       addressable m0' (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) BAC.REAC_CTRL_BUILD_AS_K /\
       fp [0%nat; 1%nat] m0' (bv_unsigned (getr regs 4)) FS
          (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned (getr regs 2))
          [(bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned (getr regs 2));
           (fr + 544, fr + 544 + rnb g b)]
          [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mrow (g_in g), mrow (g_in g) + 296);
           (fr + 2624, fr + 2624 + 6); (BOXA, BOXA + 6); (fr + 544, fr + 544 + rnb g b)] /\
       (exists ob, bytes_at rsegs m0' (fr + 544) ob /\ Z.of_nat (length ob) = rnb g b) /\
       (rnb g b <> 0 -> bytes_at rsegs m0' (fr + 544) (rt_F (g_in g) (Z.of_nat b))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r6_mkR_of.
    eapply evt_mono.
    + eapply (r6_evt BASH) with (A := A) (fr := fr) (FS := FS) (bb := Z.of_nat b)
        (mdv := mrow (g_in g)) (Rv := rnb g b) (mbv := rt_mb (g_in g)) (nbv := rt_nb (g_in g))
        (dbv := OUR (g_in g)) (sbv := box6) (junk := junk);
        try assumption; try lia.
    + intros ms' (R & m' & Hms & K1 & K2 & K3 & K4 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & K23 & K24 &
                  K25 & K26 & K27 & MU & WM & ST & ACm & SWm & AW & FP' & Hob & Hfb).
      exists R, (Z_to_bv 64 0x81710), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
      split; [exact K8|]. split; [exact K9|]. split; [exact K10|]. split; [exact K27|]. split; [exact K19|].
      split; [exact K21|].
      split; [exact K22|]. split; [exact K23|]. split; [exact K25|]. split; [exact K26|].
      split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
      split; [exact ACm|]. split; [exact SWm|]. split; [exact AW|]. split; [exact FP'|].
      split; [exact Hob|].
      intros Hn0. exact (Hfb (HgoE Hn0)).
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K1 & K2 & K3 & K4 & K8 & K9 & K10 & K27 & K19 & K21 & K22 & K23 & K25 & K26 &
       MU0 & WM0 & ST0 & AC0' & SW0' & AW0 & FP0' & Hob0 & HFB0) Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81710) by (rewrite Hreg; exact K1).
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (rnb g b)) by (rewrite Hreg; exact K10).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    (* back from the normalized memory to the real one *)
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HroM.
    pose proof (r6_stk_back mem' m0' _ _ HRel Hlo5 ST0) as ST.
    pose proof (r6_cells_tr m0' mem' TB' AC0') as ACm.
    pose proof (r6_srw_back mem' m0' HRel SW0') as SWm.
    pose proof (r6_addr_back mem' m0' _ _ HRel AW0) as AW.
    pose proof (r6_fp_tr m0' mem' _ _ _ _ _ _ _ TB'
                  (fun l h Hl Hs => r6_stk_back mem' m0' l h HRel Hl Hs) FP0') as FP'.
    assert (Hob : exists ob, bytes_at rsegs mem' (fr + 544) ob /\ Z.of_nat (length ob) = rnb g b)
      by (destruct Hob0 as (ob & Hb & Hl); exists ob; split; [exact (TB' _ _ Hb) | exact Hl]).
    (* out[]'s frame bytes rt_F (build_as's post, when n_b <> 0) *)
    assert (HFB : rnb g b <> 0 -> bytes_at rsegs mem' (fr + 544) (rt_F (g_in g) (Z.of_nat b)))
      by (intros Hn0; exact (TB' _ _ (HFB0 Hn0))).
    (* the side-stack state after the call, and the presence of its bytes *)
    pose proof FP' as FP1.
    destruct FP1 as (DT' & TS' & C' & T' & DB' & k2 & HTLSc' & HFStp' & HFSpl' & H88' & H96' & HCLS' & _).
    assert (HC0 : fp_cls mem' FS 0%nat) by (inversion HCLS' as [|c0 l0 Hc0 Hl0]; exact Hc0).
    assert (HC1 : fp_cls mem' FS 1%nat)
      by (inversion HCLS' as [|c0 l0 Hc0 Hl0]; inversion Hl0 as [|c1 l1 Hc1 Hl1]; exact Hc1).
    assert (HFSstk : stk rsegs mem' FS (FS + FS_SIZE)) by (destruct HFSpl' as (_ & _ & _ & _ & H); exact H).
    assert (HFSpres : forall q, FS <= q < FS + AC.FS_SIZE -> exists bb, mbyte rsegs mem' q = Some bb).
    { intros q Hq. destruct HFSstk as (_ & _ & Hs).
      destruct (proj2 (Hs q ltac:(unfold FS_SIZE, AC.FS_SIZE in *; lia))) as (bb & Hb).
      exists bb. rewrite r6_mbyte_mrd. exact Hb. }
    (* the write set and its complement *)
    set (Wall := [(bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned (getr regs 2));
                  (fr + 544, fr + 544 + rnb g b)] ++ fp_w [0%nat; 1%nat] FS ++
                 [(shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K),
                   shadow_addr (bv_unsigned (getr regs 2)))]) in *.
    assert (Hm8 : (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) mod 8 = 0)
      by (Z.div_mod_to_equations; lia).
    (* the shadow byte of an application byte off the call's window and off the class-0 / class-1 frames *)
    assert (HoutSHb : forall b0, app_mem b0 -> 0 <= b0 ->
              (b0 < bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K \/ bv_unsigned (getr regs 2) <= b0) ->
              (b0 < FS \/ FS + 2134016 <= b0) -> outside Wall (shadow_addr b0)).
    { intros b0 Happb Hb0 Hwb Hfb.
      pose proof (shadow_of_app b0 Happb) as Hsb.
      pose proof (r6_in_shadow_bnd _ Hsb) as Hbd.
      unfold Wall. apply r6_out_all.
      - lia.
      - intros Hc. exact (app_not_shadow (shadow_addr b0) (Happ (shadow_addr b0) ltac:(lia)) Hsb).
      - apply r6_fpw_out; [lia | |].
        + intros Hc. exact (app_not_shadow (shadow_addr b0) (HFSapp' (shadow_addr b0) ltac:(lia)) Hsb).
        + destruct Hfb as [Hl|Hh].
          * pose proof (r6_sh_lt b0 FS HFS8 Hl). lia.
          * pose proof (r6_sh_ge b0 (FS + 2134016) Hh). lia.
      - destruct Hwb as [Hl|Hh].
        + pose proof (r6_sh_lt b0 _ Hm8 Hl). lia.
        + pose proof (r6_sh_ge b0 _ Hh). lia. }
    assert (HoutLO : forall x, 0 <= x < AC.GT -> outside Wall x).
    { intros x Hx. unfold Wall. apply r6_out_all; [lia | lia | | ].
      - apply r6_fpw_out; [lia | lia |].
        assert (Hs0 : ASAN_K <= shadow_addr FS)
          by (unfold shadow_addr; pose proof (Z.div_pos FS 8 ltac:(lia) ltac:(lia)); lia).
        lia.
      - assert (H0 : ASAN_K <= shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)).
        { unfold shadow_addr.
          pose proof (Z.div_pos (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) 8 Hsp0K
                        ltac:(lia)). lia. }
        lia. }
    assert (HoutFR : forall x, fr <= x < fr + 3136 -> ~ (fr + 544 <= x < fr + 544 + rnb g b) ->
              outside Wall x).
    { intros x Hx Hx2. unfold Wall. apply r6_out_all.
      - destruct Hsep as [Hs|Hs]; lia.
      - lia.
      - exact (r6_dj_out_r _ _ fr (fr + 3136) x HDJfr (or_introl eq_refl) Hx).
      - apply (r6_app_not_sh x _ _ (Happ x Hx)); lia. }
    assert (HoutHI : forall x, A <= x -> outside Wall x).
    { intros x Hx. unfold Wall. apply r6_out_all; [lia | lia | |].
      - apply r6_fpw_out; [lia | lia |].
        pose proof (r6_sh_hi (FS + 2134016) ltac:(lia)) as Hs. lia.
      - assert (Hs : shadow_addr (bv_unsigned (getr regs 2)) <= HIGHMEM_BEG) by (apply r6_sh_hi; lia). lia. }
    assert (HoutSH : forall x, Sfr fr <= x < Sfr fr + 392 -> outside Wall x).
    { intros x Hx. pose proof (HshIn x Hx) as Hin. pose proof (r6_in_shadow_bnd x Hin) as Hbd.
      assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
      unfold Wall. apply r6_out_all.
      - lia.
      - intros Hc. exact (app_not_shadow x (Happ x ltac:(lia)) Hin).
      - exact (r6_dj_out_r _ _ (Sfr fr) (Sfr fr + 392) x HDJfr (or_intror (or_introl eq_refl)) Hx).
      - destruct Hsep as [Hs|Hs].
        + assert (Hle : Sfr fr + 392 <=
                        shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)).
          { unfold Sfr. rewrite <- (r6_sh_frame_of fr 392 ltac:(lia) Hfr8 ltac:(lia)).
            apply r6_sh_ge. lia. }
          lia.
        + assert (Hge : shadow_addr (bv_unsigned (getr regs 2)) <= Sfr fr)
            by (unfold Sfr; apply r6_sh_ge; lia).
          lia. }
    assert (HoutAG : forall a, in_globals AF.frame_AG a -> outside Wall (shadow_addr a)).
    { intros a Hin. destruct (r6_ag_lo a Hin) as (Ha0 & Hagt).
      apply HoutSHb; [unfold app_mem; left; lia | lia | left; lia | left; lia]. }
    (* the slot window below the call's window holds no frame byte: on the real arm the frame starts at sp, on
       the side arm it is in the side stack, below stklo <= S - SLOT_STACK *)
    assert (HfrLo : forall x, g_S g - AF.SLOT_STACK <= x < bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K ->
              ~ (fr <= x < fr + 3136)).
    { intros x Hx Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
      - lia.
      - destruct (Hfs x Hf) as (FSb & HFSbr & Hwb & Hlob & Hhib).
        pose proof (HFSuniq FSb Hwb HFSbr) as EFS. subst FSb. lia. }
    assert (HoutWIN : forall x, g_S g - AF.SLOT_STACK <= x < g_S g ->
              outside Wall x \/ exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx.
      destruct (Z_le_gt_dec (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) x) as [HL|HL];
        [destruct (Z_lt_ge_dec x (bv_unsigned (getr regs 2))) as [HU|HU]|].
      - right. destruct ST as (_ & _ & Hs).
        assert (Hxw : bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K <= x < bv_unsigned (getr regs 2))
          by lia.
        exact (proj2 (Hs x Hxw)).
      - destruct (Z_le_gt_dec fr x) as [HF|HF]; [destruct (Z_lt_ge_dec x (fr + 3136)) as [HF2|HF2]|].
        + destruct (Z_le_gt_dec (fr + 544) x) as [HO|HO];
            [destruct (Z_lt_ge_dec x (fr + 544 + rnb g b)) as [HO2|HO2]|].
          * right. destruct Hob as (ob & Hobb & HobL).
            replace x with (fr + 544 + (x - (fr + 544))) by lia.
            exact (r6_ba_some mem' (fr + 544) ob (x - (fr + 544)) Hobb ltac:(lia)).
          * left. apply HoutFR; lia.
          * left. apply HoutFR; lia.
        + left. unfold Wall. apply r6_out_all; [lia | lia | |].
          * apply r6_fpw_out; [lia | lia |].
            pose proof (r6_sh_hi (FS + 2134016) ltac:(lia)) as Hs. lia.
          * apply (r6_app_not_sh x _ _); [unfold app_mem; right; lia | lia | lia].
        + left. unfold Wall. apply r6_out_all; [lia | lia | |].
          * apply r6_fpw_out; [lia | lia |].
            pose proof (r6_sh_hi (FS + 2134016) ltac:(lia)) as Hs. lia.
          * apply (r6_app_not_sh x _ _); [unfold app_mem; right; lia | lia | lia].
      - left. unfold Wall. apply r6_out_all; [lia | intros Hc; apply (HfrLo x); lia | |].
        + apply r6_fpw_out; [lia | lia |].
          pose proof (r6_sh_hi (FS + 2134016) ltac:(lia)) as Hs. lia.
        + apply (r6_app_not_sh x _ _); [unfold app_mem; right; lia | lia | lia]. }
    (* the runtime cells and the heap invariant after the call *)
    assert (HRTD : rt_disjoint Wall).
    { apply r6_rt_disjoint. unfold Wall. apply Forall_app. split.
      - repeat constructor; cbn [fst]; lia.
      - apply Forall_app. split.
        + apply Forall_forall. exact HFPWgt.
        + repeat constructor; cbn [fst]. unfold shadow_addr.
          pose proof (Z.div_pos (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) 8 Hsp0K
                        ltac:(lia)). lia. }
    assert (Hkeepfs : forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 16) ->
              ~ (FS + 4096 <= q < FS + 28672) -> outside Wall q).
    { intros q Hq H1 H2.
      assert (Hqapp : app_mem q) by (apply HFSapp'; lia).
      assert (Hsh3 : ~ (shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) <= q <
                        shadow_addr (bv_unsigned (getr regs 2))))
        by (apply (r6_app_not_sh q); [exact Hqapp | lia | lia]).
      assert (Hshfs : ~ (shadow_addr FS <= q < shadow_addr (FS + 2134016)))
        by (apply (r6_app_not_sh q); [exact Hqapp | lia | lia]).
      unfold Wall. apply r6_out_app; [cbn [outside]; split; [lia | split; [lia | exact I]]|].
      apply r6_out_app.
      - apply r6_fpw_meta; [lia | lia | exact H1 | exact H2 | exact Hshfs].
      - cbn [outside]. split; [lia | exact I]. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + AC.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      unfold Wall. apply r6_out_app.
      - cbn [outside]. split; [|split; [|exact I]].
        + destruct (Z_le_gt_dec (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) q) as [HL|HL];
            [destruct (Z_lt_ge_dec q (bv_unsigned (getr regs 2))) as [HU|HU]; [|lia] | lia].
          exfalso. apply Hns. right; left. unfold APPMEM_END in *. lia.
        + destruct (Z_le_gt_dec (fr + 544) q) as [HL|HL];
            [destruct (Z_lt_ge_dec q (fr + 544 + rnb g b)) as [HU|HU]; [|lia] | lia].
          exfalso. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
          * apply Hns. right; left. pose proof (Hreal q ltac:(lia)) as Hr. unfold APPMEM_END in *. lia.
          * apply Hnf. destruct (Hfs q ltac:(lia)) as (FSb & HFSbr & Hwb & Hlob & Hhib).
            pose proof (HFSuniq FSb Hwb HFSbr) as EFS.
            subst FSb. unfold AC.FS_SIZE, FS_SIZE in *. lia.
      - apply r6_out_app.
        + apply r6_fpw_out; [lia| |].
          * intros Hc. apply Hnf. unfold AC.FS_SIZE. lia.
          * intros Hc. apply Hnsh.
            destruct (r6_sh_inv q FS (FS + 2134016) HFS8 ltac:(lia) Hc) as (Hsv1 & Hsv2).
            exists (FS + 8 * (q - shadow_addr FS)).
            split; [unfold AC.FS_SIZE; lia | symmetry; exact Hsv2].
        + cbn [outside]. split; [|exact I].
          destruct (Z_le_gt_dec (shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)) q)
            as [HL|HL]; [destruct (Z_lt_ge_dec q (shadow_addr (bv_unsigned (getr regs 2)))) as [HU|HU];
                         [|lia] | lia].
          exfalso. apply Hns.
          assert (Hsi : 0 <= bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) by lia.
          assert (Hqi : shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) <= q <
                        shadow_addr (bv_unsigned (getr regs 2))) by lia.
          destruct (r6_sh_inv q _ _ Hm8 Hsi Hqi) as (Hsv1 & Hsv2).
          right; right; right.
          exists (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K +
                  8 * (q - shadow_addr (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K))).
          split; [symmetry; exact Hsv2|]. right; left. unfold APPMEM_END in *. lia. }
    destruct (r6_ah g fr [] regs mem mem' md Wall FS HFRA HFSw ltac:(lia) ltac:(lia) MU WM HFSpres
                Hkeepfs HC0 HC1 Hagree) as (HAH' & HOWN' & HSTKeq & HSTKhi).
    (* the registered globals and the slot window outside the frame stay addressable *)
    assert (HAGm : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Hin. apply (r6_addr_keep Wall mem mem' a 1 (HAG a Hin) MU).
      intros i Hi. replace (a + i) with a by lia. exact (HoutAG a Hin). }
    assert (HWAm : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      destruct (Z_le_gt_dec (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K) a) as [HL|HL];
        [destruct (Z_lt_ge_dec a (bv_unsigned (getr regs 2))) as [HU|HU]|].
      - apply (r6_addr_sub mem' (bv_unsigned (getr regs 2) - BAC.REAC_CTRL_BUILD_AS_K)
                 BAC.REAC_CTRL_BUILD_AS_K); [exact AW | lia | lia | lia].
      - apply (r6_addr_keep Wall mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros i Hi. replace (a + i) with a by lia.
        apply HoutSHb; [unfold app_mem; right; lia | lia | right; lia | right; lia].
      - apply (r6_addr_keep Wall mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros i Hi. replace (a + i) with a by lia.
        apply HoutSHb; [unfold app_mem; right; lia | lia | left; lia | right; lia]. }
    (* ENT across the call: no written byte is one ENT speaks of (ent_kept's five cases; the fifth, ENT append #1,
       is the shadow byte of an entry block byte, which is app memory below stklo and off the side stack, r6_blk) *)
    assert (HENT1 : ENT APIf g [] mem' md).
    { eapply ent_munch with (W := Wall) (mem := mem);
        [exact HENT | exact HAH | exact MU | | exact HSTKeq | exact HSTKhi |].
      - intros x Hk. destruct Hk as [Hblk | [Himg | [Habv | [(b0 & Hor & ->) | Hbsh]]]].
        5: { destruct Hbsh as (q & kk & i & Hin & Hni & Hi & ->).
             destruct (r6_blk ([] ++ g_H g) mem md q kk HAH (in_or_app _ _ _ (or_intror Hin)))
               as (Hq4 & Hend & Hall).
             destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
             assert (Hxfs : q + i < FS \/ FS + 2134016 <= q + i).
             { destruct (Z_lt_le_dec (q + i) FS) as [H|H]; [left; exact H|].
               destruct (Z_lt_le_dec (q + i) (FS + 2134016)) as [H2|H2]; [|right; exact H2].
               exfalso. apply Hnfs. apply (a_fs_in AC.ASYMS mem FS (q + i) HFSw); lia. }
             apply HoutSHb; [exact Happq | lia | left; lia | exact Hxfs]. }
        + destruct Hblk as (q & kk & i & Hin & Hni & Hi & ->).
          destruct (r6_blk ([] ++ g_H g) mem md q kk HAH (in_or_app _ _ _ (or_intror Hin)))
            as (Hq4 & Hend & Hall).
          destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
          unfold Wall. apply r6_out_all.
          * lia.
          * intros Hc. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
            -- pose proof (Hreal (q + i) ltac:(lia)) as Hr. lia.
            -- exact (Hnfs (Hfs (q + i) ltac:(lia))).
          * apply r6_fpw_out; [lia | |].
            -- intros Hc. apply Hnfs. apply (a_fs_in AC.ASYMS mem FS (q + i) HFSw); [lia | lia].
            -- apply (r6_app_not_sh (q + i) _ _ Happq); lia.
          * apply (r6_app_not_sh (q + i) _ _ Happq); lia.
        + apply HoutLO. exact (img_below_GT x Himg).
        + apply HoutHI. lia.
        + assert (Hb0 : (0 <= b0 < AC.GT) \/ (g_S g <= b0 < APPMEM_END)).
          { destruct Hor as [Hi|Hr]; [left; exact (img_below_GT b0 Hi) | right; exact Hr]. }
          apply HoutSHb.
          * unfold app_mem. destruct Hb0; lia.
          * destruct Hb0; lia.
          * destruct Hb0 as [Hl|Hh]; [left; lia | right; lia].
          * destruct Hb0 as [Hl|Hh]; [left; lia | right; lia].
      - intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
    assert (HENT'' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    (* the side-arm frame record after the call *)
    assert (HFSREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec. apply (r6_fsrec mem mem' Wall fr Hrec MU HoutLO).
      intros FS' j x Hw' HFS'r Hj Hfrj Hx.
      pose proof (HFSuniq FS' Hw' HFS'r) as EFS. subst FS'.
      destruct Hx as [Hx|Hx].
      - apply Hkeepfs; lia.
      - assert (Hxa : app_mem x) by (apply HFSapp'; lia).
        unfold Wall. apply r6_out_all.
        + lia.
        + lia.
        + apply r6_fpw_out; [lia | lia |]. apply (r6_app_not_sh x _ _ Hxa); lia.
        + apply (r6_app_not_sh x _ _ Hxa); lia. }
    (* FRA's input facts: the input block is a live entry block, so app memory below stklo, outside the frame and
       the side stack (a_laws_blocks); the call writes neither its bytes nor their shadow bytes *)
    assert (HINo : forall x, g_p g <= x < g_p g + g_n g -> outside Wall x /\ outside Wall (shadow_addr x)).
    { intros x Hx.
      destruct (Hinblk ltac:(lia)) as (Hin & _).
      destruct (r6_blk ([] ++ g_H g) mem md (g_p g) (g_n g) HAH (in_or_app _ _ _ (or_intror Hin)))
        as (Hq4 & Hend & Hall).
      destruct (Hall x ltac:(lia)) as (Happq & Hnfs).
      assert (Hxfs : x < FS \/ FS + 2134016 <= x).
      { destruct (Z_lt_le_dec x FS) as [H|H]; [left; exact H|].
        destruct (Z_lt_le_dec x (FS + 2134016)) as [H2|H2]; [|right; exact H2].
        exfalso. apply Hnfs. apply (a_fs_in AC.ASYMS mem FS x HFSw); lia. }
      split.
      - unfold Wall. apply r6_out_all.
        + lia.
        + intros Hc. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
          * pose proof (Hreal x ltac:(lia)) as Hr. lia.
          * exact (Hnfs (Hfs x ltac:(lia))).
        + apply r6_fpw_out; [lia | lia |]. apply (r6_app_not_sh x _ _ Happq); lia.
        + apply (r6_app_not_sh x _ _ Happq); lia.
      - apply HoutSHb; [exact Happq | lia | left; lia | exact Hxfs]. }
    destruct (fra_in_keep_sh g mem mem' Wall Hinb Hinblk MU HINo) as (HIN1' & HIN2').
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r6_fra_run g fr [] regs regs'' mem mem' md Wall HFRA MU WM HroM HRTD SWm HAH' HSTKeq HoutLO);
        try assumption.
      - intros x Hx. apply HoutFR; lia.
      - intros x Hx. apply HoutHI. lia. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity.
      exact Hmat. }
    (* the spills of the exit cut lie at or above A, outside the write set *)
    assert (Hspl : forall off v, 0 <= off -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply HoutHI. lia. }
    assert (Hspl2 : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A' & HA' & Hq).
      assert (A' = A) by (apply (r6_spill_A regs mem off v A A' HA' Hq Hr9); lia). subst A'.
      apply Hspl; [lia | exact Hq]. }
    (* out[] and our[] stay addressable: their shadow bytes are off the call's writes *)
    assert (HOUTAm : OUTA fr mem').
    { unfold OUTA in *. apply (r6_addr_keep Wall mem mem' (fr + 544) 1492 HOUTA MU).
      intros i Hi. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
        | right; lia]. }
    assert (HAourm : addressable mem' (fr + 2624) 6).
    { apply (r6_addr_keep Wall mem mem' (fr + 2624) 6 HAour MU).
      intros i Hi. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
        | right; lia]. }
    (* the exit's RBE: the spills are at or above A, the image bytes (row table, box, catalogue row, row name) are
       below GT, and the shadow bytes of out[], the identity record, our[] and the row name are off the call's
       writes *)
    assert (HtblL : length BAP.ba_tbl = 168%nat) by reflexivity.
    assert (HRBE' : RBE g fr regs'' mem').
    { unfold RBE.
      split; [apply Hspl; [lia | exact Hq128]|].
      split; [apply Hspl; [lia | exact Hq312]|].
      split; [apply Hspl; [lia | exact Hq272]|].
      split; [apply Hspl; [lia | exact Hq264]|].
      split; [apply Hspl; [lia | exact Hq256]|].
      split; [apply Hspl; [lia | exact Hq248]|].
      split; [exact (Hspl2 56 _ ltac:(lia) H56)|].
      split; [exact (Hspl2 184 _ ltac:(lia) H184)|].
      split; [exact (Hspl2 144 _ ltac:(lia) H144)|].
      split; [exact (Hspl2 8 _ ltac:(lia) H8)|].
      split; [exact (Hspl2 32 _ ltac:(lia) H32)|].
      split; [exact (Hspl2 24 _ ltac:(lia) H24)|].
      split; [exact (Hspl2 16 _ ltac:(lia) H16)|].
      split; [exact (Hspl2 96 _ ltac:(lia) H96)|].
      split; [exact (Hspl2 120 _ ltac:(lia) H120)|].
      split; [exact (Hspl2 240 _ ltac:(lia) H240)|].
      split; [exact (Hspl2 232 _ ltac:(lia) H232)|].
      split; [exact (Hspl2 224 _ ltac:(lia) H224)|].
      split; [exact (Hspl2 176 _ ltac:(lia) H176)|].
      split; [exact (Hspl2 208 _ ltac:(lia) H208)|].
      split; [exact (Hspl2 64 _ ltac:(lia) H64)|].
      split; [exact HOUTAm|].
      split.
      { apply (r6_addr_keep Wall mem mem' (fr + 2176) 38 HA2176 MU).
        intros i Hi. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
          | right; lia]. }
      split.
      { intros Hnm. destruct (HNMr Hnm) as (Hok & Hbs & Had & Hpos & Hhi).
        split; [exact Hok|]. split.
        - eapply fl_bytes; [exact Hbs | exact MU |]. intros x Hx. apply HoutLO. lia.
        - split; [|split; [exact Hpos | exact Hhi]].
          apply (r6_addr_keep Wall mem mem' _ _ Had MU). intros i Hi.
          apply HoutSHb; [unfold app_mem; left; lia | lia | left; lia | left; lia]. }
      split; [exact HAourm|].
      split.
      { eapply fl_bytes; [exact HTBL | exact MU |]. rewrite HtblL. intros x Hx. apply HoutLO.
        unfold BAC.BA_FR in Hx. lia. }
      split.
      { eapply fl_bytes; [exact HBOXb | exact MU |]. rewrite HsbL. intros x Hx. apply HoutLO. lia. }
      split; [eapply fl_bytes; [exact HMBb | exact MU |]; rewrite HmbL; intros x Hx; apply HoutLO; lia|].
      (* adopt 9 of a working branch: PRA, [A + 160] = fr + 64 and [A + 112] = fr + 2256, spills at or above A *)
      split.
      { apply (r6_pra fr regs regs'' mem mem'); [|exact HPRA].
        intros off v Hin Hs. apply (Hspl2 off v); [clear -Hin; cbn [In] in Hin; lia | exact Hs]. }
      split; [exact (Hspl2 152 _ ltac:(lia) H152)|].
      split; [exact (Hspl2 112 _ ltac:(lia) H112)|].
      (* adopt 10 of a working branch: the fragment record's 72 bytes, addressable (their shadow bytes are off the writes) *)
      split.
      { apply (r6_addr_keep Wall mem mem' (fr + 2256) 72 HA2256 MU).
        intros i Hi. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
          | right; lia]. }
      (* [A + 160] = fr + 32 (v1.9.0's A4 store, appended last to RBE), a spill at or above A *)
      exact (Hspl2 160 _ ltac:(lia) H160). }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr, A.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hble|].
    split; [change AC.ANMAX with 1073741824; lia|].
    split; [unfold AC.a_size; lia|].
    split; [exact HA64|].
    split; [unfold rg; rewrite E9; exact Hr9|].
    split; [unfold rg; rewrite E21; exact Hs5r|].
    split; [unfold a0v, rg; exact E10|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hq128 | exact MU |].
      rewrite length_le8. intros x Hx. apply HoutHI. lia. }
    split; [exact HRBE'|].
    (* adopt 10 of a working branch: the turn-b records on both arms (they lie in the frame, past out[]; build_as writes
       neither) and, when n_b <> 0, out[]'s frame bytes rt_F (build_as's post) *)
    split.
    { unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |]. rewrite r6_rid_len.
      intros x Hx. apply HoutFR; lia. }
    split.
    { unfold FGBr in *. eapply fl_bytes; [exact HFGB | exact MU |]. rewrite r6_rfg_len.
      intros x Hx. apply HoutFR; lia. }
    split; [exact HFB|].
    split; [unfold rg; rewrite E22; exact Hr22|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. apply HoutFR; lia. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    split; [exact HOUTAm|].
    split; [intros _; exact (r6x_of_rbe _ _ _ _ _ HRBE')|].
    (* adopt 10 of a working branch: s11 = 32 (R5's 0x816cc `li s11,32`), kept by the callee *)
    unfold rg; rewrite E27; exact Hr27.
Qed.

End R6.
