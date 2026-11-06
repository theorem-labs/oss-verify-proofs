(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2170 of its 2292 lines of code are new or changed and 889 lines of the source are left out. *)
(* Segment R9 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81658, 0x8167c], the official cuts of
   A/Prog/SlotInv.v (push 10): Inv_A81658_at b -> Inv_A81680_at b (forms-asan.md S_R9).
   rule 24: no function proved (a slot segment; reac_ctrl_parse is a Section Hypothesis on its contract).

     0x81658-0x81664  sb zero,296(s3) .. sb zero,299(s3)   the first four shadow bytes of the parse record
     0x81668          li s11,4                             the fifth granule's byte value (4 of 8 in scope)
     0x8166c          sb s11,300(s3)                       the fifth shadow byte
     0x81670-0x81678  mv a0,s8 ; mv a1,s2 ; ld a2,56(s1)   Phi, n_b and the record [A + 56] = fr + 2368 (RXS)
     0x8167c          jal 834b0 <reac_ctrl_parse>          PARSE@81624 (plan-asan 2 row R9, 4 PARSE)

   With s3 = S(fr) the five stores mark the frame variable p 36B (round_trip) at fr + 2368 usable in the frame
   shadow (plan-asan FP.4, row "p 36B (round_trip) | 2368 | 36 | 296-300 | 00 00 00 00 04"), so the 36 bytes at
   fr + 2368 become addressable: that is the parse call's output-pointer premise.  The write set of the segment is
   the five frame-shadow bytes [S(fr) + 296, S(fr) + 301), the callee's stack window [sp - 8800, sp) and its
   shadow, the 36 bytes at fr + 2368, and the class-1 side-stack bytes fp_w [1] FS with their shadow (the frame
   the callee's own __asan_stack_malloc_1 may take), as plan-asan 4 row R9 says.

   The entry cut X81658 gives RF (s8 = Phi with Phi's bytes = rt_F of turn b, s2 = n_b, the turn-b records) and
   RXS (the spill [A + 56] = fr + 2368 among them); the exit cut X81680 adds a0 = rt_k of turn b (the parse
   contract's post, read through rt_g = fr50 (rt_F ...): cp_rd reads only below offset 50) and s11 = 4.

   Shape, after Seg/F4.v's 0x81e54 arm (the same callee, the same FRA): r9_st is the Lib-level run of the five
   shadow stores and the li; r9_call / r9_calln the three argument moves and the call on the contract, the second
   on the normalized memory (the contract asks for mem_inv, which no cut carries: MemNorm.evt_normalize from
   FRA's ro_agree).  FRA / ENT move by r9_fra_sh (the shadow stores) and r9_fra_call (the call); the cut body by
   r9_keep2 / r9_keep3.  The side-stack package fp [1] / reac_ctrl_parse_tls is on no cut: Seg/Tac_fsfree.v's
   fra_fp derives it from FRA at the call (W = the callee window and the record, D = the record and, for
   50 <= n_b, Phi's first 50 bytes inside the live block). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcFinLib RcLay
  RcIdentModel RcFrag RcReply reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RFG0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module REM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.
Module REML := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmitLib.
Module RSY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module RSYL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynthLib.
Module RFIL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFinLib.
Module RLY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.
Module RBA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module RRP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Module LIMG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.

(* ---------------- model lengths of the round trip ---------------- *)

(* The fragment state keeps its 72 bytes (the ubsan twin's u1_fg_st_len, Tac_u1.v of a working branch). *)
Lemma r9_fg_st_len : forall len st g,
  length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RFG0.fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (RFG0.fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= RFG0.fg_n g <= 22).
  { unfold RFG0.fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= RFG0.bat bs i).
  { intros bs i. unfold RFG0.bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (RFG0.fg_body g) = Z.to_nat (RFG0.fg_n g)).
  { unfold RFG0.fg_body, RFG0.bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (RFG0.bat g 19 =? 1).
  - cbn [fg_next]. unfold RFG0.fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold RFG0.bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (RFG0.fg_keep st g) eqn:Ek; cbn [negb];
      [|cbn [fg_next]; unfold RFG0.fg_clear;
        rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : RFG0.fg_T st g <= 64).
    { unfold RFG0.fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H.
      exact H. }
    assert (Hj : length (RFG0.fg_join st g) = 72%nat).
    { unfold RFG0.fg_join. unfold RFG0.fg_T, RFG0.fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold RFG0.fg_T, RFG0.fg_lf. lia. }
    destruct (RFG0.fg_close st g); cbn [negb fg_next]; unfold RFG0.fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

(* The turn-b records: 38 identity bytes at fr + 2176, 72 fragment bytes at fr + 2256. *)
Lemma r9_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id.
    destruct (RRP.ir _ _); [apply RIM.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RIM.ING_length; exact IH1 | exact IH1].
    + apply r9_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

Lemma r9_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (LIMG.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (LIMG.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma r9_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, RBA.ba_X, RLY.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RLY.ly_zero
                       else if RSY.rc (rt_mb inp) b =? 1 then RSY.synth (rt_mb inp) b (rt_nb inp)
                       else RLY.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RSY.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RSYL.rs_synth_len. apply r9_row_len. }
  destruct (b <=? 1); [apply RFIL.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b <> 0: 124 <= n_b <= 1492 and F_b has n_b bytes (Tac_rt2_b2.a_rtn). *)
Lemma r9_rtn : forall inp b, rt_n inp b <> 0 ->
  124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, RBA.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (REML.em_wok_range _ Ew) as [R _].
  split; [lia|].
  unfold rt_F, REM.em_fr, REM.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, r9_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The parse reads only the first 50 bytes of the frame, and only when 50 <= n (image B's B_R9.v r9_cp_rd_lt). *)
Lemma r9_cp_rd_50 : forall n bs i, In i (cp_rd n bs) -> 50 <= n.
Proof.
  intros n bs i Hi. unfold cp_rd in Hi.
  destruct (negb (50 <=? n)) eqn:E; [destruct Hi|].
  apply negb_false_iff in E. apply Z.leb_le in E. exact E.
Qed.

Lemma r9_cp_rd_lt : forall n bs i, In i (cp_rd n bs) -> (i < 50)%nat.
Proof.
  intros n bs i Hi. unfold cp_rd in Hi.
  destruct (negb (50 <=? n)); [cbn in Hi; exfalso; exact Hi|].
  destruct (negb (cp_v bs 12 =? 0x88)); [cbn in Hi; destruct Hi as [<-|[]]; lia|].
  destruct (negb (cp_v bs 13 =? 0x19)); [cbn in Hi; destruct Hi as [<-|[<-|[]]]; lia|].
  apply in_app_or in Hi. destruct Hi as [Hi|Hi].
  - apply in_seq in Hi. lia.
  - destruct (cp_rec bs); [|cbn in Hi; exfalso; exact Hi].
    apply in_app_or in Hi. destruct Hi as [Hi|Hi].
    + cbn in Hi. destruct Hi as [<-|[<-|[<-|[]]]]; lia.
    + apply in_app_or in Hi. destruct Hi as [Hi|Hi].
      * destruct (cp_v bs 32 =? 0x12); cbn in Hi; [destruct Hi as [<-|[]]; lia | exfalso; exact Hi].
      * destruct (cp_kind bs =? 6); cbn in Hi; [destruct Hi as [<-|[<-|[<-|[]]]]; lia | exfalso; exact Hi].
Qed.

(* The bytes the parse reads at Phi are the first 50 bytes of F_b, i.e. rt_g of turn b. *)
Lemma r9_rd_g : forall m inp b phi,
  bytes_at rsegs m phi (rt_F inp b) -> rt_n inp b <> 0 ->
  forall i, In i (cp_rd (rt_n inp b) (rt_g inp b)) ->
    mrd rsegs m (wa (phi + Z.of_nat i)) = nth_error (rt_g inp b) i.
Proof.
  intros m inp b phi (H0 & HL & Hb) Hnz i Hi.
  pose proof (r9_cp_rd_lt _ _ _ Hi) as Hlt.
  destruct (r9_rtn inp b Hnz) as (Hr & HFl).
  assert (Hi' : (i < length (rt_F inp b))%nat) by lia.
  rewrite (Hb i Hi').
  unfold rt_g, fr50. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec0 i 50) as [_|C]; [|lia].
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

(* ---------------- kit (Seg/F4.v's, renamed) ---------------- *)

Ltac r9_subst_slot H := let HH := fresh in pose proof H as HH; rewrite HH; clear HH.

Lemma r9_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

Lemma r9_app_ivl : forall lo hi, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi H1 H2 a Ha. unfold app_mem. right. lia. Qed.

Lemma r9_q64_keep : forall W m m' a v, q64 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *.
  eapply fl_bytes; [exact H | exact MU |]. rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

Lemma r9_word_eq : forall W m m' a, Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  forall v, word_mem rsegs m a v <-> word_mem rsegs m' a v.
Proof.
  intros W m m' a MU HW Ha Hhi v.
  assert (HE : forall k, (k < 8)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))).
  { intros k Hk. apply MU. rewrite MState.unsigned_lit by lia. apply HW; lia. }
  split; intros H k Hk; pose proof (H k Hk) as Hb; unfold mbyte in *.
  - rewrite (HE k Hk). exact Hb.
  - rewrite (HE k Hk) in Hb. exact Hb.
Qed.

Lemma r9_spill_keep : forall regs regs' A off v m m' W,
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  getr regs' 9 = getr regs 9 -> Frame.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' W HS H9 HA HAE Hoff E9 MU HW.
  destruct HS as (A' & H9' & Hq).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    assert (Hdz : (A' - A) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. apply Zmod_0_l. }
    destruct (proj1 (Zmod_divides (A' - A) (2 ^ 64) ltac:(lia)) Hdz) as (q & Hq2).
    rewrite HP in Hq2. lia. }
  subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  exact (r9_q64_keep W m m' (A + off) v Hq MU HW).
Qed.

(* The spill cell at the cut's own spill base (the existential base of `spill` is A: register 9 pins it modulo
   2 ^ 64 and both lie far below 2 ^ 64). *)
Lemma r9_spill_at : forall regs A off v m,
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  q64 m (A + off) v.
Proof.
  intros regs A off v m HS H9 HA HAE Hoff.
  destruct HS as (A' & H9' & Hq).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    assert (Hdz : (A' - A) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. apply Zmod_0_l. }
    destruct (proj1 (Zmod_divides (A' - A) (2 ^ 64) ltac:(lia)) Hdz) as (q & Hq2).
    rewrite HP in Hq2. lia. }
  subst A'. exact Hq.
Qed.

Lemma r9_addr_keep : forall W m m' p n, addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HW. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (in_shadow_range (shadow_addr (p + i)) (shadow_of_app _ Hap)) as HR.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite Mem.wa_unsigned by lia. exact (HW i Hi).
Qed.

Lemma r9_addr_sub : forall m p n k j, addressable m p n -> 0 <= k -> 0 <= j -> k + j <= n ->
  addressable m (p + k) j.
Proof.
  intros m p n k j (H0 & Hn & Hhi & H) Hk Hj Hkj.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + k + i) with (p + (k + i)) by lia. apply H. lia.
Qed.

Lemma r9_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof. intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END. assert (0 <= a / 8) by (apply Z.div_pos; lia). lia. Qed.

Lemma r9_sh_hi : forall a, 0 <= a < APPMEM_END -> shadow_addr a < HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; [lia | unfold APPMEM_END in Ha; lia]).
  lia.
Qed.

Lemma r9_sh_hi_le : forall a, 0 <= a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia | unfold APPMEM_END in Ha; lia]).
  lia.
Qed.

Lemma r9_sh_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

Lemma r9_sh_lt2 : forall x y, 0 <= x -> x < y -> y mod 8 = 0 -> shadow_addr x < shadow_addr y.
Proof.
  intros x y H0 H Hm. unfold shadow_addr.
  assert (x / 8 < y / 8).
  { apply Z.div_lt_upper_bound; [lia|]. Z.div_mod_to_equations. lia. }
  lia.
Qed.

(* The shadow byte k of the frame base is the shadow of the frame byte fr + 8k. *)
Lemma r9_fr_sh : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr.
  replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(* The shadow byte of a frame byte from fr + 2408 on is one of the frame's shadow bytes 301..379; from below
   fr + 2368 it is one of 0..295. *)
Lemma r9_sh_frame_hi : forall fr x, fr mod 8 = 0 -> fr + 2408 <= x < fr + FRAME_BYTES ->
  Sfr fr + 301 <= shadow_addr x < Sfr fr + FRAME_SHADOW.
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr x Hm Hx. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma r9_sh_frame_lo : forall fr x, fr mod 8 = 0 -> fr <= x < fr + 2368 ->
  Sfr fr <= shadow_addr x < Sfr fr + 296.
Proof. intros fr x Hm Hx. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* A shadow byte of an address outside an eight-aligned range is outside that range's shadow (image B's
   B_R9.v r9_sh_out). *)
Lemma r9_sh_out : forall lo hi x, lo mod 8 = 0 -> hi mod 8 = 0 -> (x < lo \/ hi <= x) ->
  shadow_addr x < shadow_addr lo \/ shadow_addr hi <= shadow_addr x.
Proof. intros lo hi x Hl Hh Hx. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma r9_app_out_sh : forall x lo hi, app_mem x -> 0 <= lo -> 0 <= hi <= APPMEM_END ->
  ~ (shadow_addr lo <= x < shadow_addr hi).
Proof.
  intros x lo hi Hx Hlo Hhi HC. pose proof (r9_sh_lo lo Hlo). pose proof (r9_sh_hi_le hi Hhi).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Definition r9_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma r9_ag_true : r9_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r9_ag_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r9_ag_true (lo, n) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H1, H2. lia.
Qed.

Lemma r9_addr1 : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & Hn & Hhi & Hall) Hx.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply Hall. lia.
Qed.

Lemma r9_cell_byte : forall m a n bs x, rw_cells rsegs m a [CB n bs] -> a <= x < a + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a n bs x ((Hwf & Hb) & _) Hx.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hwf as (Hlen & _). cbn [cell_wf] in Hlen.
  destruct Hb as (H0 & H1 & Hall).
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by (rewrite Hlen; lia).
  pose proof (Hall (Z.to_nat (x - a)) Hi) as Hm.
  rewrite Z2Nat.id in Hm by lia. replace (a + (x - a)) with x in Hm by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E;
    [exists b; exact Hm | apply nth_error_None in E; lia].
Qed.

(* A CB cell block survives a write it is apart from. *)
Lemma r9_rw_keep : forall W m m' a n bs, rw_cells rsegs m a [CB n bs] ->
  Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> Frame.outside W x) ->
  rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs ((Hwf & Hb) & Hw) MU WM HO.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  pose proof Hwf as Hwf'. destruct Hwf' as (Hlen & _). cbn [cell_wf] in Hlen.
  cbn [cells_size csize] in Hw |- *. rewrite ?Nat.add_0_r in Hw |- *.
  split; [split; [exact Hwf|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    eapply fl_bytes; [exact Hb | exact MU |]. rewrite Hlen. intros x Hx. apply HO. lia.
  - eapply wr_at_transport; [exact Hw | exact WM].
Qed.

Lemma r9_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma r9_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as HR. unfold bv_modulus in HR.
  change (2 ^ Z.of_N 8) with 256 in HR. lia.
Qed.

Lemma r9_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma r9_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

Lemma r9_bytes_cons : forall m a b bs, bytes_at rsegs m a [b] -> bytes_at rsegs m (a + 1) bs ->
  bytes_at rsegs m a (b :: bs).
Proof.
  intros m a b bs (Ha0 & _ & Hb) (_ & Hbl & Hbs). split; [exact Ha0|].
  split; [cbn [length] in *; lia|].
  intros i Hi. destruct i as [|i].
  - pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth_error] in H0 |- *. exact H0.
  - cbn [nth_error]. cbn [length] in Hi.
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
    exact (Hbs i ltac:(lia)).
Qed.

Lemma r9_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma r9_le1_4 : le1 (Z_to_bv 64 4) = [Z_to_bv 8 4].
Proof. vm_compute. reflexivity. Qed.

Lemma r9_pres_at : forall m a (l : list byte) q, bytes_at rsegs m a l -> a <= q < a + Z.of_nat (length l) ->
  exists b, mbyte rsegs m q = Some b.
Proof.
  intros m a l q (Ha & Hl & H) Hq.
  assert (Hi : (Z.to_nat (q - a) < length l)%nat) by lia.
  pose proof (H _ Hi) as Hq5. rewrite Z2Nat.id in Hq5 by lia.
  replace (a + (q - a)) with q in Hq5 by lia.
  destruct (nth_error l (Z.to_nat (q - a))) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  exists b. exact Hq5.
Qed.

Lemma r9_wm_eq : forall m a v v', word_mem rsegs m a v -> word_mem rsegs m a v' ->
  v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros m a v v' H H'.
  assert (P : 2 ^ 64 <> 0) by lia.
  assert (E : forall k, (k < 8)%nat -> le_byte (v mod 2 ^ 64) 8 k = le_byte (v' mod 2 ^ 64) 8 k).
  { intros k Hk. pose proof (H k Hk) as H1. pose proof (H' k Hk) as H2.
    assert (H3 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal bv_unsigned) in H3. rewrite !kb_byte_unsigned in H3. clear H1 H2. rename H3 into H2.
    unfold le_byte in H2 |- *. change (8 * Z.of_nat 8) with 64 in H2 |- *. rewrite !Z.mod_mod by exact P.
    exact H2. }
  assert (R1 : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= v' mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite (kb_le8_digits _ R1), (kb_le8_digits _ R2).
  rewrite !E by lia. reflexivity.
Qed.

Lemma r9_wm_norm : forall m a x y, word_mem rsegs m a x -> word_mem rsegs m a y ->
  0 <= y < 2 ^ 64 -> - (2 ^ 64) < x < 2 ^ 64 -> x = y \/ x = y - 2 ^ 64.
Proof.
  intros m a x y Hx Hy Hy0 Hx0.
  pose proof (r9_wm_eq m a x y Hx Hy) as E.
  rewrite (Z.mod_small y (2 ^ 64)) in E by lia.
  destruct (Z_le_gt_dec 0 x) as [Hs|Hs].
  - left. rewrite (Z.mod_small x (2 ^ 64)) in E by lia. exact E.
  - right.
    assert (EM : (x + 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64).
    { replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    rewrite (Z.mod_small (x + 2 ^ 64) (2 ^ 64)) in EM by lia. lia.
Qed.

Lemma r9_dj_hi : forall (W : list (Z * Z)) a n, (forall lo hi, In (lo, hi) W -> a + n <= lo) ->
  disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  split; [left; exact (H lo hi (or_introl eq_refl))|].
  apply IH. intros lo' hi' Hin. exact (H lo' hi' (or_intror Hin)).
Qed.

Lemma r9_rt : forall W, (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint.
  repeat split; apply r9_dj_hi; intros lo hi Hin; pose proof (H lo hi Hin) as Hl; unfold AC.GT in Hl;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

Lemma r9_fs_meta_lo : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

Lemma r9_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RLY.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RLY.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma r9_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (r9_byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. exact (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma r9_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- L at 1. apply r9_le_bytes_to_Z.
Qed.

Lemma r9_byte_at : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mbyte rsegs m a = Some b ->
  bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 Hb. split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb.
Qed.

Lemma r9_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb).
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma r9_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (r9_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

Lemma r9_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (r9_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite r9_le8_of_bytes by lia. exact Hbs.
Qed.

Ltac r9_num :=
  cbv [RLY.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY
       asan_stack_malloc_c.GOT_CF asan_stack_malloc_c.CF bcmp_wrap_c.GOT_CF bcmp_wrap_c.CF
       GOT_VERBOSITY VERBOSITY DTLS_TPOFF
       RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       REAC_CTRL_PARSE_K AF.SLOT_STACK FN_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG
       ASAN_K] in *; lia.

Ltac r9_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

(* ---- the five frame shadow bytes [S(fr) + 296, S(fr) + 301) ---- *)

Definition r9_Wsh (fr : Z) : list (Z * Z) := [(Sfr fr + 296, Sfr fr + 301)].

Lemma r9_Wsh_cases : forall fr x, Frame.outside (r9_Wsh fr) x \/ (Sfr fr + 296 <= x < Sfr fr + 301).
Proof.
  intros fr x. unfold r9_Wsh. cbn [Frame.outside].
  destruct (Z_le_gt_dec (Sfr fr + 296) x); [destruct (Z_lt_ge_dec x (Sfr fr + 301))|].
  - right; lia.
  - left. split; [lia | exact I].
  - left. split; [lia | exact I].
Qed.

Lemma r9_Wsh_app : forall fr x, 0 <= fr -> fr + 2408 <= APPMEM_END -> app_mem x ->
  Frame.outside (r9_Wsh fr) x.
Proof.
  intros fr x H0 H1 Hx. unfold r9_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HC.
  pose proof (r9_sh_lo fr H0) as L1. pose proof (r9_sh_hi_le (fr + 2408) ltac:(lia)) as L2.
  assert (E : shadow_addr (fr + 2408) = Sfr fr + 301).
  { unfold Sfr, shadow_addr. replace (fr + 2408) with (fr + 301 * 8) by lia. rewrite Z.div_add by lia. lia. }
  unfold Sfr in HC. rewrite E in L2. unfold Sfr in L2.
  unfold app_mem in Hx. lia.
Qed.

(* The 36 record cells [fr + 2368, fr + 2404) are addressable once the five frame shadow bytes mark them. *)
Lemma r9_addr_o : forall m fr, 0 <= fr -> fr mod 32 = 0 ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> fr + 2408 <= APPMEM_END ->
  bytes_at rsegs m (Sfr fr + 296) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  addressable m (fr + 2368) 36.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros m fr H0 Hm32 Happ Hend Hbs.
  assert (Hm8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof Hbs as (Hb0 & Hbl & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. unfold addr_byte. split; [apply Happ; lia|].
  assert (Hi8lo : 0 <= i / 8) by (apply Z.div_pos; lia).
  assert (Hi8hi : i / 8 <= 4) by (Z.div_mod_to_equations; lia).
  assert (Hshadow : shadow_addr (fr + 2368 + i) = Sfr fr + 296 + i / 8).
  { unfold Sfr, shadow_addr.
    assert (E : (fr + 2368 + i) / 8 = fr / 8 + 296 + i / 8) by (Z.div_mod_to_equations; lia).
    rewrite E. lia. }
  set (gi := Z.to_nat (i / 8)).
  assert (Hgeq : i / 8 = Z.of_nat gi) by (unfold gi; rewrite Z2Nat.id by lia; reflexivity).
  pose proof (Hb gi ltac:(cbn [length]; unfold gi; lia)) as HE.
  rewrite Hshadow, Hgeq.
  assert (Hmod : (fr + 2368 + i) mod 8 = i mod 8) by (Z.div_mod_to_equations; lia).
  destruct gi as [|[|[|[|[|gi]]]]]; cbn [nth_error] in HE;
    try (exfalso; rewrite Hgeq in Hi8hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi8hi; lia).
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 4). split; [exact HE|].
    right. assert (Hsgn : bv_signed (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity).
    rewrite Hsgn. split; [|lia].
    assert (Hieq : i / 8 = 4) by (rewrite Hgeq; reflexivity).
    assert (i mod 8 < 4) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* The new 392-byte frame shadow list after the five stores. *)
Lemma r9_shnew : forall W fr mem mem' sh l5,
  bytes_at rsegs mem (Sfr fr) sh -> length sh = (Z.to_nat FRAME_SHADOW) -> Frame.munch W mem mem' ->
  (forall x, Sfr fr <= x < Sfr fr + 296 -> Frame.outside W x) ->
  (forall x, Sfr fr + 301 <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  bytes_at rsegs mem' (Sfr fr + 296) l5 -> length l5 = 5%nat ->
  bytes_at rsegs mem' (Sfr fr) (firstn 296 sh ++ l5 ++ skipn 301 sh) /\
  length (firstn 296 sh ++ l5 ++ skipn 301 sh) = (Z.to_nat FRAME_SHADOW).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros W fr mem mem' sh l5 Hsh Hlen MU Hlo Hhi H5 Hl5.
  assert (L22 : length (firstn 296 sh) = 296%nat) by (rewrite firstn_length_le; lia).
  assert (L27 : length (skipn 301 sh) = 91%nat) by (rewrite length_skipn; lia).
  split; [|rewrite !length_app, L22, Hl5, L27; reflexivity].
  pose proof Hsh as Hsh1. rewrite <- (firstn_skipn 296 sh) in Hsh1.
  apply Mem.bytes_at_app in Hsh1. destruct Hsh1 as (Hf & _).
  pose proof Hsh as Hsh2. rewrite <- (firstn_skipn 301 sh) in Hsh2.
  apply Mem.bytes_at_app in Hsh2. destruct Hsh2 as (_ & Hs).
  rewrite firstn_length_le in Hs by lia. change (Z.of_nat 301) with 301 in Hs.
  apply Mem.bytes_at_app. split.
  - eapply fl_bytes; [exact Hf | exact MU |]. rewrite L22. change (Z.of_nat 296) with 296.
    intros x Hx. apply Hlo. lia.
  - rewrite L22. change (Z.of_nat 296) with 296. apply Mem.bytes_at_app. split; [exact H5|].
    rewrite Hl5. change (Z.of_nat 5) with 5. replace (Sfr fr + 296 + 5) with (Sfr fr + 301) by lia.
    eapply fl_bytes; [exact Hs | exact MU |]. rewrite L27. change (Z.of_nat 91) with 91.
    intros x Hx. apply Hhi. lia.
Qed.

Lemma r9_sok_at : forall m a n (j : nat) b,
  wr_at rsegs m a n -> 0 <= b - a -> (b - a) + Z.of_nat j <= n ->
  store_ok rsegs m (wa b) j = true.
Proof.
  intros m a n j b H H1 H2.
  replace b with (a + (b - a)) by lia.
  exact (wr_at_store_ok rsegs m a n (b - a) j H H1 H2).
Qed.

Ltac r9_sokb W b n :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa b) n = true)
        by (eapply (r9_sok_at mm _ _ n b); [repeat apply wr_at_write; exact W | lia | lia])
  end.

Ltac r9_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* ---- the parse call's write set ---- *)

Lemma r9_fsc : forall FS, fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  change (Z.of_nat 1) with 1. change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192.
  repeat split; lia.
Qed.

Lemma r9_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w, fp_w1. cbn [flat_map app].
  destruct (r9_fsc FS) as (F1 & F2 & F3 & F4 & F5).
  rewrite F5, F4, F1, F2, F3.
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma r9_fs_frame0 : forall FS, fs_frame FS 0%nat 0 = FS + 36864.
Proof.
  intros FS. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576.
  change (2 ^ 0) with 1. lia.
Qed.

Lemma r9_afs_flag1 : forall FS j, AC.a_fs_flag FS 1%nat j = FS + 20480 + j.
Proof.
  intros FS j. unfold AC.a_fs_flag.
  change (2 ^ (15 - Z.of_nat 1)) with 16384. change (2 ^ 15) with 32768. lia.
Qed.

Lemma r9_flag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j /\ (AC.a_fs_flag FS c j < FS + 20480 \/ FS + 28672 <= AC.a_fs_flag FS c j).
Proof.
  intros FS c j Hc Hc1 Hj. unfold AC.a_fs_flag, AC.a_fs_M in *.
  destruct c as [|[|c]].
  - change (2 ^ (14 - Z.of_nat 0)) with 16384 in Hj. change (2 ^ (15 - Z.of_nat 0)) with 32768. lia.
  - exfalso. apply Hc1. reflexivity.
  - assert (P : 2 ^ (15 - Z.of_nat (S (S c))) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Definition r9_PW (o S FS : Z) : list (Z * Z) :=
  reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)].

Lemma r9_PW_eq : forall o S FS, o <> 0 -> r9_PW o S FS =
  [(o, o + 36); (S - 8800, S); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (S - 8800), shadow_addr S)].
Proof.
  intros o S FS Ho. unfold r9_PW, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K.
  replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho).
  rewrite r9_fpw1. cbn [app]. reflexivity.
Qed.

Lemma r9_PW_out : forall o S FS x, o <> 0 ->
  ~ (o <= x < o + 36) -> ~ (S - 8800 <= x < S) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (S - 8800) <= x < shadow_addr S) ->
  Frame.outside (r9_PW o S FS) x.
Proof.
  intros o S FS x Ho N1 N2 N3 N4 N5 N6 N7. rewrite (r9_PW_eq o S FS Ho). cbn [Frame.outside].
  repeat split; try exact I; assumption.
Qed.

Lemma r9_PW_out_app : forall o S FS x, o <> 0 -> app_mem x -> 0 <= FS -> FS + 2134016 <= APPMEM_END ->
  0 <= S - 8800 -> S <= APPMEM_END ->
  ~ (o <= x < o + 36) -> ~ (S - 8800 <= x < S) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  Frame.outside (r9_PW o S FS) x.
Proof.
  intros o S FS x Ho Hx HF0 HF1 HS0 HS1 N1 N2 N3 N4 N5.
  apply r9_PW_out; try assumption; apply r9_app_out_sh; (assumption || lia).
Qed.

Lemma r9_PW_out_sh : forall o S FS y, o <> 0 -> 0 <= y < APPMEM_END ->
  (o + 36 <= LOWMEM_END \/ HIGHMEM_BEG <= o) -> HIGHMEM_BEG <= S - 8800 ->
  (FS + 2134016 <= LOWMEM_END \/ HIGHMEM_BEG <= FS + 8) -> 0 <= FS -> FS mod 8 = 0 -> (S - 8800) mod 8 = 0 ->
  (y < FS + 1085440 \/ FS + 2134016 <= y) -> (y < S - 8800 \/ S <= y) ->
  Frame.outside (r9_PW o S FS) (shadow_addr y).
Proof.
  intros o S FS y Ho Hy Hoa HS HFa HF0 HF8 HS8 Hy1 Hy2.
  pose proof (r9_sh_lo y ltac:(lia)) as L1. pose proof (r9_sh_hi y Hy) as L2.
  apply r9_PW_out; [exact Ho | lia | lia | lia | lia | lia | |].
  - intros [H1 H2]. destruct Hy1 as [Hy1|Hy1].
    + pose proof (r9_sh_lt2 y (FS + 1085440) ltac:(lia) Hy1 ltac:(Z.div_mod_to_equations; lia)). lia.
    + pose proof (r9_sh_mono (FS + 2134016) y Hy1). lia.
  - intros [H1 H2]. destruct Hy2 as [Hy2|Hy2].
    + pose proof (r9_sh_lt2 y (S - 8800) ltac:(lia) Hy2 HS8). lia.
    + pose proof (r9_sh_mono S y Hy2). lia.
Qed.

Lemma r9_PW_lo : forall o S FS lo hi, o <> 0 -> AC.GT <= o -> AC.GT <= FS -> AC.GT + 8800 <= S ->
  In (lo, hi) (r9_PW o S FS) -> AC.GT <= lo.
Proof.
  intros o S FS lo hi Ho H1 H2 H3 Hin. rewrite (r9_PW_eq o S FS Ho) in Hin.
  unfold AC.GT, shadow_addr, ASAN_K in *. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
    first [lia | (assert (0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia); lia)
               | (assert (0 <= (S - 8800) / 8) by (apply Z.div_pos; lia); lia)] |]); contradiction.
Qed.

(* ---- read-only / normalized-memory transports (Seg/F4.v's) ---- *)

Definition r9_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma r9_tops_gt : r9_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r9_find_below : forall segs top x n s,
  r9_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r9_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma r9_ro_gt : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (r9_find_below sg 0x5fe000 x n s r9_tops_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma r9_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r9_ro_gt a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r9_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r9_shrw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (Hlo : 0x5fe000 <= a)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia).
  split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r9_ro_gt a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r9_shrw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r9_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma r9_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Ltac r9_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

Lemma r9_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end; r9_ba_rel R.
Qed.

Lemma r9_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R. unfold asan_tls_cells.
  split; intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|].
  all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|]. all: split; [exact Hk|].
  all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|].
  all: split; [r9_ba_rel R|]. all: split; [exists tb, te; r9_ba_rel R|].
  all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|].
  all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|]. all: split; [r9_ba_rel R|].
  all: split; [exact HDB|]. all: r9_ba_rel R.
Qed.

Lemma r9_cls_rel : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c R. unfold fp_cls.
  split; intros (Hc & h & fl & Hh & Hf & Hl & Hb); (split; [exact Hc|]); exists h, fl;
    (split; [r9_ba_rel R|]); (split; [r9_ba_rel R|]); (split; [exact Hl | exact Hb]).
Qed.

Lemma r9_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D R
    (DT & TS & C & T & DB & k & Htls & Htp & Hpl & H88 & H96 & Hcls & Hlo & Happ & Hw & Hd).
  exists DT, TS, C, T, DB, k.
  split; [exact (proj1 (r9_tls_rel m m0 TP DT TS C T DB k R) Htls)|].
  split; [r9_ba_rel R|].
  split.
  { destruct Hpl as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. apply (r9_stk_rel m m0 FS (FS + FS_SIZE) R); [unfold ASAN_GT in P3; lia | exact P5]. }
  split; [r9_ba_rel R|]. split; [r9_ba_rel R|].
  split.
  { eapply Forall_impl; [|exact Hcls]. intros c Hc. exact (proj1 (r9_cls_rel m m0 FS c R) Hc). }
  split; [exact Hlo|]. split; [exact Happ|]. split; [exact Hw | exact Hd].
Qed.

(* ---------------- the segment ---------------- *)

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee, taken on its contract (lib/A/Prog/reac_ctrl_parse_c.v), never on its code. *)
Hypothesis PARSE : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.reac_ctrl_parse_contract.

(* The frame body is byte-backed and writable (the real arm from the slot window, the side arm from a_fs_ok). *)
Lemma r9_frame_stk : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> stk rsegs mem fr (fr + FRAME_BYTES).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md HFRA.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (_ & _ & _ & Hfrw).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in Hgt; lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. lia. }
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  split; [lia|]. split; [lia|]. intros a Ha.
  split; [exact (Hfrw a Ha)|].
  destruct Hloc as [(_ & Hspfr & Hreal)|(_ & _ & Hfs & _)].
  - destruct Hwin as (_ & _ & Hwv). exact (proj2 (Hwv a ltac:(lia))).
  - destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
    destruct (AC.a_laws_fs_state _ _ _ _ _ LAWS (hb ++ g_H g) mem md FSa HAH Hwa HFSar) as (Hok & _).
    destruct Hok as (Hwr & _). destruct (Hwr a ltac:(unfold AC.FS_SIZE in *; lia)) as (_ & bb & Hb).
    exists bb. exact Hb.
Qed.

(* A sub-range of the 416-byte prologue save area is byte-backed and writable (Seg/B5Cuts.v's b5_spill_stk). *)
Lemma r9_spill_stk : forall g fr hb regs mem md A lo hi,
  FRA B APIf ra g fr hb regs mem md -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A <= lo -> lo <= hi -> hi <= A + 416 -> stk rsegs mem lo hi.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md A lo hi HFRA Hr9 HA Hlo Hmid Hhi.
  pose proof HFRA as HF. destruct HF as (A' & sp & s5 & H).
  assert (Hr9' : rg regs 9 A') by tauto.
  assert (Hsp : sp <= A') by tauto.
  assert (HAS : A' <= g_S g) by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (HA416 : A' + 416 <= g_S g) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof Hstk as Hstk'. unfold stk in Hstk'. destruct Hstk' as (Hb0 & Hb1 & _).
  assert (HA' : 0 <= A' < 2 ^ 64) by lia.
  assert (EA : A = A') by (apply r9_id; [lia | lia |]; unfold rg in Hr9, Hr9'; rewrite <- Hr9; exact Hr9').
  subst A'.
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) lo (g_S g) Hstk ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs mem lo hi (g_S g) H1 ltac:(lia)) as (H2 & _). exact H2.
Qed.

(* The runtime cells the bcmp wrapper of reac_ctrl_parse reads (Seg/B5Cuts.v's b5_rt_cells). *)
Lemma r9_byte1 : forall m a bs (i : nat) b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. destruct k as [|k]; [|lia].
  cbn [nth_error]. replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia.
  rewrite H by exact Hi. exact Hn.
Qed.

Lemma r9_rt_cells : forall sp m md, AsanRTInv.RT sp m md ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_real_cells sp m md HRT) as HR.
  pose proof (AsanRTInv.RT_cf_cells sp m md HRT) as (Hg & _ & _ & _ & _ & _ & H240 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact Hg|].
  split.
  - pose proof (r9_byte1 m (RT_CF + 240) _ 14 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in HH by (unfold RT_CF, CF; lia). exact HH.
  - pose proof (r9_byte1 m (RT_CF + 240) _ 15 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in HH by (unfold RT_CF, CF; lia). exact HH.
Qed.

(* A byte range that `stk` covers is writable in the `wr_at` form the stores need. *)
Lemma r9_wr : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Hlo Hn Hhi.
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma r9_sub_stk : forall m fr lo hi, stk rsegs m fr (fr + FRAME_BYTES) ->
  fr <= lo -> lo <= hi -> hi <= fr + FRAME_BYTES -> stk rsegs m lo hi.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros m fr lo hi Hstk Hlo Hm Hhi.
  destruct (stk_split rsegs m fr lo (fr + FRAME_BYTES) Hstk ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs m lo hi (fr + FRAME_BYTES) H1 ltac:(lia)) as (H2 & _). exact H2.
Qed.

(* The live heap block of the turn: its placement and bytes (a_laws_blocks at the cut's heap). *)
Lemma r9_blk : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  4096 <= phi /\ phi + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, phi <= a < phi + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr phi n regs mem md HFRA.
  pose proof HFRA as HF. destruct HF as (A & sp & s5 & _ & HAH & _).
  destruct (AC.a_laws_blocks AC.ASYMS _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
              (hb1 phi n ++ g_H g) mem md phi n HAH
              ltac:(unfold hb1; apply in_or_app; left; apply in_eq))
    as (Hal & Hlo & Hhi & Hein & Hbytes).
  split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hbytes a Ha) as (Hap & _ & _ & _ & Hnfs). split; [exact Hap | exact Hnfs].
Qed.

(* ---- the run of the five shadow stores and the li (0x81658-0x8166c) ---- *)

Lemma r9_st :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z),
    0 <= Sfr fr -> Sfr fr + 301 <= 2 ^ 64 ->
    wr_at rsegs m (Sfr fr + 296) 5 ->
    LE.evt rsegs
      (fun ms => exists (m2 : word -> option byte),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 4) t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81670) fc None m2 (seg_rom rsegs) /\
         Frame.munch (r9_Wsh fr) m m2 /\ Frame.wmono rsegs m m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 296) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81658) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m fr HSfr0 HSfrhi Wsh.
  r9_sokb Wsh (Sfr fr + 296) 1%nat. step.
  r9_sokb Wsh (Sfr fr + 297) 1%nat. step.
  r9_sokb Wsh (Sfr fr + 298) 1%nat. step.
  r9_sokb Wsh (Sfr fr + 299) 1%nat. step.
  (* 0x81668 li s11,4 ; 0x8166c sb s11,300(s3) *)
  step.
  r9_sokb Wsh (Sfr fr + 300) 1%nat. step.
  apply evt_done. eexists.
  split; [reflexivity|].
  split.
  { unfold r9_Wsh.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  split.
  { do 5 apply wmono_write. apply wmono_refl. }
  split.
  { intros lo hi Hs. do 5 (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hs. }
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 296 + 1) with (Sfr fr + 297) by lia.
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 297 + 1) with (Sfr fr + 298) by lia.
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 298 + 1) with (Sfr fr + 299) by lia.
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 299 + 1) with (Sfr fr + 300) by lia.
  rewrite <- r9_le1_4. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
Qed.

(* ---- AH / ownership / the stack bounds across the five frame shadow bytes ---- *)

Lemma r9_fr_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch (r9_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md HFRA MU WM HPRES.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hw2 : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  unfold AC.GT in Hgt.
  destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
  - assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha.
      destruct (r9_Wsh_cases fr a) as [Ho | Hb]; [exact Ho | exfalso].
      apply Hn. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (a - Sfr fr)).
      split; [rewrite r9_fr_sh; lia | right; left; apply Hreal; lia]. }
    exact (AC.a_laws_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md HAH P1 Hw2).
  - destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hbin).
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b' & Hbr' & Hwb' & Hbin').
    assert (Ebb : b' = b).
    { pose proof (r9_wm_eq _ _ _ _ Hwb' Hwb) as E. rewrite !Z.mod_small in E by lia. exact E. }
    subst b'.
    pose proof (AC.a_laws_fs_place _ _ _ _ _ LAWS _ _ _ b HAH Hwb Hbr) as (_ & Hstkb & _ & Happfs).
    assert (Hsz : b + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE, AF.SLOT_STACK, APPMEM_END in *; lia).
    assert (Hmeta : forall q, fs_meta b q -> Frame.outside (r9_Wsh fr) q).
    { intros q Hq. pose proof (fs_meta_below b q Hq) as Hq1. pose proof (r9_fs_meta_lo b q Hq) as Hq0.
      assert (Hqa : app_mem q) by (apply Happfs; unfold AC.FS_SIZE; lia).
      destruct (r9_Wsh_cases fr q) as [Ho | Hb2]; [exact Ho | exfalso].
      apply (AsanRTFacts.app_not_shadow q Hqa).
      replace q with (shadow_addr (fr + 8 * (q - Sfr fr))) by (rewrite r9_fr_sh; lia).
      apply AsanRTFacts.shadow_of_app, Happ. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (b <= q < b + AC.FS_SIZE) ->
              ~ (exists c, b <= c < b + AC.FS_SIZE /\ q = shadow_addr c) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq _ Hnr Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      destruct (r9_Wsh_cases fr q) as [Ho | Hb2]; [exact Ho | exfalso].
      apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
      split; [unfold AC.FS_SIZE in *; lia | rewrite r9_fr_sh; lia]. }
    exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _ (r9_Wsh fr) (hb ++ g_H g) mem mem' md b LAWS HAH Hwb Hbr Hsz MU
      Hw2 HPRES Hmeta Hagree).
Qed.

(* FRA and ENT across the five frame shadow bytes. *)
Lemma r9_fra_sh : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  Frame.munch (r9_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  bytes_at rsegs mem' (Sfr fr + 296) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md HFRA HENT MU WM H5.
  assert (HPRES : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                    exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq Hb. destruct (r9_Wsh_cases fr q) as [Ho | Hin].
    - rewrite (KindBGlue.mbyte_munch rsegs (r9_Wsh fr) mem mem' q MU Hq Ho). exact Hb.
    - apply (r9_pres_at mem' (Sfr fr + 296) _ q H5). cbn [length]. lia. }
  destruct (r9_fr_ah g fr hb regs mem mem' md HFRA MU WM HPRES) as (HAH' & Hown & HSTK & HSTKhi).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSfr : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hout : forall x, (x < Sfr fr + 296 \/ Sfr fr + 301 <= x) -> Frame.outside (r9_Wsh fr) x).
  { intros x Hx. unfold r9_Wsh. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. apply r9_id; [lia | lia |]. rewrite <- HA'. exact Hr9. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep (r9_Wsh fr) mem mem' Hro MU). intros x Hx. apply Hout. left. lia. }
  split.
  - apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs mem mem' md (r9_Wsh fr) HFRA MU WM HRO).
    + apply r9_rt. intros lo hi Hin. unfold r9_Wsh in Hin. cbn [In] in Hin.
      destruct Hin as [E|[]]. injection E as <- <-. lia.
    + exact HAH'.
    + exact HSTK.
    + exact Happ.
    + exact Hgt.
    + destruct Hsh as (sh & Hbytes & Hlen).
      exists (firstn 296 sh ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4]
              ++ skipn 301 sh).
      apply (r9_shnew (r9_Wsh fr) fr mem mem' sh _ Hbytes Hlen MU).
      * intros x Hx. apply Hout. left. lia.
      * intros x Hx. apply Hout. right. lia.
      * exact H5.
      * reflexivity.
    + intros x _ _ Hns. apply Hout. lia.
    + intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply Hout. right. lia.
    + intros x Hx. apply Hout. right. lia.
    + intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply Hout. right. lia.
    + intros x Hx. left. apply Hout. right. lia.
    + intros a Ha. pose proof (r9_ag_lt a Ha) as Hab.
      apply (addr1_munch (r9_Wsh fr) mem mem' a MU); [|exact (HAG a Ha)].
      apply Hout. left. pose proof (r9_sh_mono a fr ltac:(lia)). unfold Sfr. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ent_store with (W := r9_Wsh fr); [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKhi |].
    + intros x Hx. destruct (r9_Wsh_cases fr x) as [Ho|Hin]; [left; exact Ho | right; right; right; lia].
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- the run 0x81670-0x8167c and the call ---- *)

Lemma r9_call :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f n o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* 0x81670 mv a0,s8 ; 0x81674 mv a1,s2 ; 0x81678 ld a2,56(s1) ; 0x8167c jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof PARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (f := f) (n := n) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try lia; try assumption.
    - intros _. exact Hocell.
    - intros _. split; [exact Hoaddr|]. split; [exact Hoapp | exact HoCF]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81680)) with (Z_to_bv 64 0x81680)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* The same run on the real memory, through MemNorm.evt_normalize. *)
Lemma r9_calln :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD
    Ho4 Hocell Howin Hofo HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := r9_call ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f n o S FS bs junk Hf Hn ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (r9_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL
                ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST) as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | r9_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply r9_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Hofo]])).
  specialize (HC (r9_cells_rel m m0 REL HAC) (r9_shrw_rel m m0 REL HSW) HHI HAPP
                 (r9_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros H50; exact (r9_addr_rel m m0 _ _ REL (HFA H50)))).
  specialize (HC (r9_addr_rel m m0 _ _ REL Hoaddr) Hoapp HoCF).
  specialize (HC (r9_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL)
                 ltac:(r9_ba_rel REL)).
  specialize (HC (r9_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS;
                       exact (proj2 (r9_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  pose proof (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC)
    as HN.
  eapply evt_mono; [exact HN|].
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes,
    EFc, ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (r9_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | r9_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (r9_shrw_back m' m0' HR' SW0)|].
  split; [exact (r9_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (r9_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (r9_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

(* ---- FRA and ENT across the call ---- *)

Lemma r9_fsrec_keep : forall mem mem' W fr,
  FSREC fr mem -> Frame.munch W mem mem' ->
  (forall FS j x, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> 0 <= j < 256 ->
     fr = FS + 6328320 + j * 4096 ->
     (x = FS + 36352 + j \/ fr + 4088 <= x < fr + 4096 \/ AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8) ->
     Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HW.
  assert (HB6 : asan_stack_malloc_c.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : asan_stack_malloc_c.fs_M 6 = 256) by reflexivity.
  assert (Hfl : asan_stack_malloc_c.fs_flag FS 6 j = FS + 36352 + j)
    by (unfold asan_stack_malloc_c.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096)
    by (rewrite Hfr; unfold asan_stack_malloc_c.fs_frame, asan_stack_malloc_c.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (HO : forall x, (x = FS + 36352 + j \/ fr + 4088 <= x < fr + 4096 \/
                          AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8) -> Frame.outside W x)
    by (intros x Hx; exact (HW FS j x Htp HFSr Hj Hfrv Hx)).
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx. apply HO. right; right; lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HO. left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HO. right; left. rewrite HB6 in Hx. lia. }
Qed.

Lemma r9_fr_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> forall x, A + 16 <= x < A + 312 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWhdr HWimg HWA9 HWsaved HWsh HWwin
    HrecK HAG' HWA'.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWimg. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSH)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

Lemma r9_fra_call : forall g fr hb regs regs' mem mem' md md' FS (bs : list byte),
  FRA B APIf ra g fr hb regs mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  Frame.munch (r9_PW (fr + 2368) (AC.aspZ regs) FS) mem mem' -> Frame.wmono rsegs mem mem' ->
  ro_same rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs) ->
  addressable mem' (AC.aspZ regs - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  rw_cells rsegs mem' (fr + 2368) [CB 36 bs] ->
  shadow_rw mem' ->
  stk rsegs mem' FS (FS + FS_SIZE) -> fp_cls mem' FS 1 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ (ENT APIf g hb mem md -> ENT APIf g hb mem' md').
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md md' FS bs HFRA Htp HFS MU WM HRS Hstkw HADw HRW HSRW HFSstk Hcls
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSal & HFSapp).
  pose proof (proj1 (AC.a_laws_fs_state _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS)) as Hok.
  pose proof (HFSfr FS Htp HFS) as HFSlow.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(unfold REAC_CTRL_PARSE_K, FN_STACK, AF.SLOT_STACK; lia)) as Hwd.
  rewrite Haspz in MU, Hstkw, HADw, Hwd, Hwlo.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKf : FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKf2 : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKtp : AC.as_tp AC.ASYMS = 6141968) by (vm_compute; reflexivity).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsp8 : (sp - 8800) mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFRAMEb HFRAMEs HFSal; Z.div_mod_to_equations; lia).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as P1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (Harm : (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr) \/
                 (FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal fr ltac:(lia))).
    - right. destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b & Hbr & Hb & Hb1).
      pose proof (r9_wm_eq _ _ _ _ Hb Htp) as Heq. rewrite !Z.mod_small in Heq by lia. subst b. lia. }
  assert (Ho0 : fr + 2368 <> 0) by lia.
  assert (HSHO : forall y, 0 <= y < APPMEM_END -> (y < FS + 1085440 \/ FS + 2134016 <= y) ->
            (y < sp - 8800 \/ sp <= y) -> Frame.outside (r9_PW (fr + 2368) sp FS) (shadow_addr y)).
  { intros y Hy Hy1 Hy2. apply r9_PW_out_sh; try lia. }
  assert (HAPO : forall x, app_mem x -> ~ (fr + 2368 <= x < fr + 2404) -> ~ (sp - 8800 <= x < sp) ->
            ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
            ~ (FS + 1085440 <= x < FS + 2134016) -> Frame.outside (r9_PW (fr + 2368) sp FS) x).
  { intros x Hx N1 N2 N3 N4 N5.
    apply r9_PW_out_app; [lia | exact Hx | lia | lia | lia | lia | lia | lia | lia | lia | lia]. }
  clear Hfrm Hspm HAm HFSal Hfr8 Hsp8 HFS8.
  (* the side stack's state after the call *)
  assert (Hokp : AC.a_fs_ok mem' FS).
  { destruct Hok as (O1 & O2 & O3 & O4 & O5).
    destruct HFSstk as (_ & _ & HS).
    destruct Hcls as (_ & h1 & fl & Hh1 & Hfl & Hfll & Hflb).
    destruct (r9_fsc FS) as (F1 & F2 & F3 & F4 & F5).
    split; [|split; [|split; [|split]]].
    - intros a Ha. exact (HS a ltac:(lia)).
    - apply (kb_word_munch rsegs mem mem' (r9_PW (fr + 2368) sp FS) (FS + 88) 20 O2 MU). intros k Hk.
      split; [lia|]. apply r9_PW_out_app; try lia. apply HFSapp. lia.
    - rewrite (KindBGlue.mbyte_munch rsegs (r9_PW (fr + 2368) sp FS) mem mem' (FS + 96) MU);
        [exact O3 | lia |].
      apply r9_PW_out_app; try lia. apply HFSapp. lia.
    - intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs mem' (fs_hint FS 1) h1 Hh1).
      + destruct (O4 c Hc) as [h Hh].
        exists h. apply (kb_word_munch rsegs mem mem' (r9_PW (fr + 2368) sp FS) _ h Hh MU).
        intros k Hk. unfold AC.a_fs_hint.
        assert (Hcz : Z.of_nat c <> 1) by lia.
        split; [lia|]. apply r9_PW_out_app; try lia. apply HFSapp. lia.
    - intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + destruct Hfl as (_ & _ & Hfl).
        assert (Hj' : (Z.to_nat j < length fl)%nat).
        { change (AC.a_fs_M 1) with (fs_M 1) in Hj. rewrite F3 in Hfll, Hj. lia. }
        destruct (nth_error fl (Z.to_nat j)) as [b|] eqn:En; [|apply nth_error_None in En; lia].
        pose proof (Hfl (Z.to_nat j) Hj') as Hb. rewrite En, Z2Nat.id in Hb by lia.
        assert (Hin : In b fl) by exact (nth_error_In fl _ En).
        rewrite Forall_forall in Hflb.
        replace (AC.a_fs_flag FS 1 j) with (fs_flag FS 1 0 + j)
          by (rewrite F2, r9_afs_flag1; lia).
        destruct (Hflb b Hin) as [-> | ->]; [left | right]; exact Hb.
      + pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
        pose proof (r9_flag_other FS c j Hc Hc1 Hj) as Ho.
        rewrite (KindBGlue.mbyte_munch rsegs (r9_PW (fr + 2368) sp FS) mem mem' (AC.a_fs_flag FS c j) MU);
          [exact (O5 c j Hc Hj) | lia |].
        apply r9_PW_out_app; try lia. apply HFSapp. lia. }
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Ha.
    apply (r9_PW_out (fr + 2368) sp FS a Ho0).
    - intro Hin. destruct Harm as [R1|[S1 S2]].
      + apply Hns. right. left. lia.
      + apply Hnf. lia.
    - intro Hin. apply Hns. right. left. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnsh. exists (8 * (a - ASAN_K)). unfold shadow_addr in *. split; lia.
    - intro Hin. apply Hns. right. right. right. exists (8 * (a - ASAN_K)). unfold shadow_addr in *.
      split; [lia | right; left; lia]. }
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Hw. exact (WM (Z_to_bv 64 a) Hw). }
  destruct (AC.a_laws_fs_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as (HAH' & Hown & Hstkeq & Hstkhieq).
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs regs' mem' md md');
      [| exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat].
    apply (r9_fr_run g fr hb regs mem mem' md (r9_PW (fr + 2368) sp FS) HFRA MU WM).
    + exact (ro_agree_same rsegs mem mem' Hro HRS).
    + apply r9_rt. intros lo hi Hin.
      apply (r9_PW_lo (fr + 2368) sp FS lo hi Ho0); [lia | lia | lia | exact Hin].
    + intros a Ha. destruct (HSRW a Ha) as (_ & b & Hb). exists b. exact Hb.
    + exact HAH'.
    + exact Hstkeq.
    + intros x Hx. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
    + intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros A' HA' HA'r x Hx.
      assert (EA : A' = A) by (apply r9_id; [lia | lia |]; unfold rg in HA', Hr9; rewrite <- HA'; exact Hr9).
      subst A'. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite r9_fr_sh; lia).
      apply HSHO; lia.
    + apply (fl_stk _ mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (sp - 8800)) as [Hl|Hl];
        [|destruct (Z_lt_le_dec x sp) as [Hl2|Hl2];
          [right; destruct Hstkw as (_ & _ & Hs); exact (proj2 (Hs x ltac:(lia)))|]].
      * destruct (Z_le_gt_dec (fr + 2368) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 2404)) as [C2|C2]|].
        -- right. exact (r9_cell_byte mem' (fr + 2368) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * destruct (Z_le_gt_dec (fr + 2368) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 2404)) as [C2|C2]|].
        -- right. exact (r9_cell_byte mem' (fr + 2368) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros Hrec. apply (r9_fsrec_keep mem mem' _ fr Hrec MU).
      intros FS' j x Htp' HFS' Hj Hfrv Hx.
      assert (EFS : FS' = FS).
      { pose proof (r9_wm_eq _ _ _ _ Htp' Htp) as E. rewrite !Z.mod_small in E by lia. exact E. }
      subst FS'.
      destruct Hx as [Hx|[Hx|Hx]].
      * apply HAPO; [apply HFSapp; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [apply HFSapp; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros a Ha. pose proof (r9_ag_lt a Ha) as Hab.
      apply (addr1_munch _ mem mem' a MU); [|exact (HAG a Ha)].
      apply HSHO; lia.
    + intros a Ha Hnf.
      destruct (Z_le_gt_dec (sp - 8800) a) as [Hw1|Hw1]; [destruct (Z_lt_ge_dec a sp) as [Hw2|Hw2]|].
      * exact (r9_addr1 mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K a HADw ltac:(lia)).
      * apply (addr1_munch _ mem mem' a MU); [|exact (HWA a Ha Hnf)]. apply HSHO; lia.
      * apply (addr1_munch _ mem mem' a MU); [|exact (HWA a Ha Hnf)]. apply HSHO; lia.
  - intros HENT. eapply ent_mat; [|exact Hmat].
    eapply ent_munch; [exact HENT | exact HAH | exact MU | | exact Hstkeq | exact Hstkhieq |].
    + intros x Hk. destruct Hk as [Hblk | [Himg | [Habv | [(b & Hor & ->) | Hblks]]]].
      * destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md q k HAH
                    (in_or_app _ _ _ (or_intror Hin)))
          as (_ & Hq4 & Hend & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros HC. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
        apply HAPO; [exact Happq | | lia | lia | lia | lia].
        destruct Harm as [R1|[S1 S2]]; lia.
      * pose proof (img_below_GT x Himg) as Hxg.
        apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * assert (Hb0 : 0 <= b < APPMEM_END)
          by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X|]; lia).
        apply HSHO; [exact Hb0 | |];
          (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X|]; lia).
      * (* frame batch 2 item 9: the shadow byte of an entry block byte (app memory below stklo, off the side
           stack, below the callee's window) *)
        destruct Hblks as (q & k & i & Hin & _ & Hi & ->).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md q k HAH
                    (in_or_app _ _ _ (or_intror Hin)))
          as (_ & Hq4 & Hend & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros HC. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
        apply HSHO; [unfold app_mem in Happq; lia | lia | lia].
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- the cut body across the two write sets ---- *)

(* The official body of Inv_A81658_at / Inv_A81680_at (the same text at both cuts). *)
Definition r9_body (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\
  OUTA fr m /\ CUR g 7 regs /\
  spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
  spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
  spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
  (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\
  (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
  spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
  (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\
  (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
  spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
  addressable m (fr + 2176) 38.

(* Everything the cut carries (the official body, RF and RXS), across a write W that keeps the cells they name. *)
Lemma r9_keepg : forall g b phi fr A regs regs' mem mem' md W,
  FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
  r9_body g b phi fr regs mem -> RF g fr b phi regs mem -> RXS g fr regs mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall x, phi <= x < phi + rnb g b -> Frame.outside W x) ->
  (forall i, 0 <= i < AC.a_size (rnb g b) -> Frame.outside W (shadow_addr (phi + i))) ->
  (forall x, fr <= x < fr + 2368 \/ fr + 2404 <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall i, 0 <= i < FRAME_BYTES -> (i < 2368 \/ 2408 <= i) -> Frame.outside W (shadow_addr (fr + i))) ->
  (forall x, A <= x < A + 416 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  (In (g_p g, g_n g) (g_H g) -> forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x) ->
  (In (g_p g, g_n g) (g_H g) ->
     forall i, 0 <= i < g_n g -> Frame.outside W (shadow_addr (g_p g + i))) ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 ->
  r9_body g b phi fr regs' mem' /\ RF g fr b phi regs' mem' /\ RXS g fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g b phi fr A regs regs' mem mem' md W HFRA HBODY HRF HRXS H9 HA MU WM
    Hphi Hphish Hfr Hfrsh Hsp Himg Hinp Hinpsh E9 E18 E21 E22 E23 E24 E25.
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0) by (apply r9_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst A0.
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact H9).
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as X. unfold app_mem in X. lia. }
  assert (HfrA : fr + FRAME_BYTES <= A + 416) by lia.
  (* frame-byte helpers *)
  assert (HfrL : forall x, fr <= x < fr + 2368 -> Frame.outside W x) by (intros x Hx; apply Hfr; lia).
  assert (HfrH : forall x, fr + 2404 <= x < fr + FRAME_BYTES -> Frame.outside W x) by (intros x Hx; apply Hfr; lia).
  assert (HfrShAt : forall x, fr <= x < fr + 2368 \/ fr + 2408 <= x < fr + FRAME_BYTES ->
            Frame.outside W (shadow_addr x)).
  { intros x Hx. replace x with (fr + (x - fr)) by lia. apply Hfrsh; lia. }
  (* the length of the records *)
  destruct (r9_RS_len (g_in g) b) as (HLid & HLfg).
  destruct HBODY as (Hgn & Hb6 & HHB & Hr23 & HOUR & HOUTA & HCUR & S112 & S128 & HPRO & S104 & S96 & S64 &
    S144 & S208 & (idb & Cidb) & (jk & Cjk) & S280 & S240 & (jy & Cjy) & (j32 & Cj32) & S152 & Hr21 &
    Aid).
  destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P200 & P248 & Aour & Hinb & Hinl &
    P184 & P256 & P264 & P272 & P32).
  split.
  { split; [exact Hgn|]. split; [exact Hb6|].
    split.
    { destruct HHB as (Hnz & Had). split; [exact Hnz|].
      exact (r9_addr_keep W mem mem' phi _ Had MU Hphish). }
    split; [unfold rg in *; rewrite E23; exact Hr23|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply HfrH. lia. }
    split.
    { unfold OUTA in *. apply (r9_addr_keep W mem mem' (fr + 544) 1492 HOUTA MU).
      intros i Hi. replace (fr + 544 + i) with (fr + (544 + i)) by lia. apply Hfrsh; lia. }
    split.
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
    split; [exact (r9_spill_keep regs regs' A 112 _ mem mem' W S112 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 128 _ mem mem' W S128 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split.
    { (* PRO: the eight prologue spills, our[]'s 6 bytes and the input block *)
      split; [exact (r9_spill_keep regs regs' A 40 _ mem mem' W P40 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 120 _ mem mem' W P120 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 136 _ mem mem' W P136 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 160 _ mem mem' W P160 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 168 _ mem mem' W P168 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 176 _ mem mem' W P176 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 208 _ mem mem' W P200 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 248 _ mem mem' W P248 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split.
      { apply (r9_addr_keep W mem mem' (fr + 2624) 6 Aour MU).
        intros i Hi. replace (fr + 2624 + i) with (fr + (2624 + i)) by lia. apply Hfrsh; lia. }
      split.
      { eapply fl_bytes; [exact Hinb | exact MU |].
        intros x Hx. rewrite <- g_n_len in Hx.
        destruct (Hinl ltac:(lia)) as (Hin & _). exact (Hinp Hin x Hx). }
      split.
      { intros H0. destruct (Hinl H0) as (Hin & Had). split; [exact Hin|].
        exact (r9_addr_keep W mem mem' (g_p g) (g_n g) Had MU (Hinpsh Hin)). }
      split; [exact (r9_spill_keep regs regs' A 184 _ mem mem' W P184 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 256 _ mem mem' W P256 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 264 _ mem mem' W P264 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [exact (r9_spill_keep regs regs' A 272 _ mem mem' W P272 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      exact (r9_spill_keep regs regs' A 32 _ mem mem' W P32 H9 HA ltac:(lia) ltac:(lia) E9 MU
               ltac:(intros x Hx; apply Hsp; lia)). }
    split; [exact (r9_spill_keep regs regs' A 104 _ mem mem' W S104 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 96 _ mem mem' W S96 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 64 _ mem mem' W S64 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 144 _ mem mem' W S144 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 192 _ mem mem' W S208 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split.
    { exists idb. apply (r9_rw_keep W mem mem' _ 38 idb Cidb MU WM).
      intros x Hx. apply HfrH. cbn in Hx. lia. }
    split.
    { exists jk. apply (r9_rw_keep W mem mem' _ 72 jk Cjk MU WM).
      intros x Hx. apply HfrH. cbn in Hx. lia. }
    split; [exact (r9_spill_keep regs regs' A 280 _ mem mem' W S280 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 240 _ mem mem' W S240 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split.
    { exists jy. apply (r9_rw_keep W mem mem' _ 1 jy Cjy MU WM).
      intros x Hx. apply HfrH. cbn in Hx. lia. }
    split.
    { exists j32. apply (r9_rw_keep W mem mem' _ 32 j32 Cj32 MU WM).
      intros x Hx. apply HfrH. cbn in Hx. lia. }
    split; [exact (r9_spill_keep regs regs' A 152 _ mem mem' W S152 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [unfold rg in *; rewrite E21; exact Hr21|].
    { apply (r9_addr_keep W mem mem' (fr + 2176) 38 Aid MU).
      intros i Hi. replace (fr + 2176 + i) with (fr + (2176 + i)) by lia. apply Hfrsh; lia. } }
  split.
  { destruct HRF as (((Hb6' & HCUR' & HOUR' & Hr23' & HIDBr & HFGBr) & Hnzb & Hr24 & Hphib) & Hr18).
    split; [|unfold rg in *; rewrite E18; exact Hr18].
    split.
    { split; [exact Hb6'|].
      split.
      { destruct HCUR' as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
        split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
      split.
      { unfold OURb in *. eapply fl_bytes; [exact HOUR' | exact MU |].
        rewrite OUR_length. intros x Hx. apply HfrH. lia. }
      split; [unfold rg in *; rewrite E23; exact Hr23'|].
      split.
      { unfold IDBr in *. eapply fl_bytes; [exact HIDBr | exact MU |].
        rewrite HLid. intros x Hx. apply HfrL. lia. }
      { unfold FGBr in *. eapply fl_bytes; [exact HFGBr | exact MU |].
        rewrite HLfg. intros x Hx. apply HfrL. lia. } }
    split; [exact Hnzb|].
    split; [unfold rg in *; rewrite E24; exact Hr24|].
    destruct (r9_rtn (g_in g) (Z.of_nat b) Hnzb) as (_ & HFl).
    eapply fl_bytes; [exact Hphib | exact MU |]. rewrite HFl.
    intros x Hx. apply Hphi. unfold rnb. lia. }
  { destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X192 & X216 & Xad).
    split; [exact (r9_spill_keep regs regs' A 48 _ mem mem' W X48 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 56 _ mem mem' W X56 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 88 _ mem mem' W X88 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 80 _ mem mem' W X80 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 72 _ mem mem' W X72 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 8 _ mem mem' W X16 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 0 _ mem mem' W X8 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 200 _ mem mem' W X192 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (r9_spill_keep regs regs' A 216 _ mem mem' W X216 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    apply (r9_addr_keep W mem mem' (fr + 2256) 72 Xad MU).
    intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia. apply Hfrsh; lia. }
Qed.

(* The turn's heap block is apart from the frame: on the real arm it ends below stklo and every frame byte is at
   or above stklo; on the side arm the frame lies in the FakeStack and no block byte does. *)
Lemma r9_blk_apart : forall g b phi fr regs mem md,
  FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md -> rnb g b <> 0 ->
  forall i, 0 <= i < rnb g b -> phi + i < fr \/ fr + FRAME_BYTES <= phi + i.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g b phi fr regs mem md HFRA Hnz i Hi.
  pose proof (r9_blk g fr phi (rnb g b) regs mem md HFRA) as (Hplo & Hphi & Hpall).
  destruct (Hpall (phi + i) ltac:(lia)) as (Happi & Hnfs).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  destruct (Z_lt_le_dec (phi + i) fr) as [H|H]; [left; exact H|].
  destruct (Z_lt_le_dec (phi + i) (fr + FRAME_BYTES)) as [H2|H2]; [|right; exact H2].
  exfalso.
  destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
  - pose proof (proj1 (Hreal (phi + i) ltac:(lia))) as Hge. lia.
  - apply Hnfs. exact (Hfs (phi + i) ltac:(lia)).
Qed.

(* Any live block of the cut (the turn's buffer or an entry block of g_H, the harness's input block among them):
   its placement and bytes, and its apartness from the frame (r9_blk / r9_blk_apart for any block). *)
Lemma r9_blk_in : forall g fr hb regs mem md p n,
  FRA B APIf ra g fr hb regs mem md -> In (p, n) (hb ++ g_H g) ->
  4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md p n HFRA Hin.
  pose proof HFRA as HF. destruct HF as (A & sp & s5 & _ & HAH & _).
  destruct (AC.a_laws_blocks AC.ASYMS _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
              (hb ++ g_H g) mem md p n HAH Hin)
    as (Hal & Hlo & Hhi & Hein & Hbytes).
  split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hbytes a Ha) as (Hap & _ & _ & _ & Hnfs). split; [exact Hap | exact Hnfs].
Qed.

Lemma r9_blk_apart_in : forall g fr hb regs mem md p n,
  FRA B APIf ra g fr hb regs mem md -> In (p, n) (hb ++ g_H g) ->
  forall i, 0 <= i < n -> p + i < fr \/ fr + FRAME_BYTES <= p + i.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md p n HFRA Hin i Hi.
  pose proof (r9_blk_in g fr hb regs mem md p n HFRA Hin) as (Hplo & Hpend & Hpall).
  destruct (Hpall (p + i) ltac:(lia)) as (Happi & Hnfs).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  destruct (Z_lt_le_dec (p + i) fr) as [H|H]; [left; exact H|].
  destruct (Z_lt_le_dec (p + i) (fr + FRAME_BYTES)) as [H2|H2]; [|right; exact H2].
  exfalso.
  destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
  - pose proof (proj1 (Hreal (p + i) ltac:(lia))) as Hge. lia.
  - apply Hnfs. exact (Hfs (p + i) ltac:(lia)).
Qed.

(* The cut body, RF and RXS across the five frame shadow bytes. *)
Lemma r9_keep2 : forall g b phi fr A regs mem mem' md,
  FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
  r9_body g b phi fr regs mem -> RF g fr b phi regs mem -> RXS g fr regs mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch (r9_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  r9_body g b phi fr regs mem' /\ RF g fr b phi regs mem' /\ RXS g fr regs mem'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g b phi fr A regs mem mem' md HFRA HBODY HRF HRXS H9 HA MU WM.
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  pose proof (r9_blk g fr phi (rnb g b) regs mem md HFRA) as (Hplo & Hphib & Hpall).
  assert (Hnz : rnb g b <> 0) by (destruct HRF as ((_ & H & _) & _); exact H).
  pose proof (r9_blk_apart g b phi fr regs mem md HFRA Hnz) as Hapt.
  destruct (r9_rtn (g_in g) (Z.of_nat b) Hnz) as (Hrng & _).
  assert (Hasz : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size, rnb in *; lia).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64) by lia.
  assert (HAeq : A = A0) by (apply r9_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst A0.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia). unfold app_mem in Ha. lia. }
  assert (HWapp : forall x, app_mem x -> Frame.outside (r9_Wsh fr) x)
    by (intros x Hx; exact (r9_Wsh_app fr x Hfr0 ltac:(lia) Hx)).
  assert (E1 : shadow_addr (fr + 2368) = Sfr fr + 296)
    by (replace (fr + 2368) with (fr + 8 * 296) by lia; rewrite r9_fr_sh; reflexivity).
  assert (E2 : shadow_addr (fr + 2408) = Sfr fr + 301)
    by (replace (fr + 2408) with (fr + 8 * 301) by lia; rewrite r9_fr_sh; reflexivity).
  apply (r9_keepg g b phi fr A regs regs mem mem' md (r9_Wsh fr) HFRA HBODY HRF HRXS H9 HA MU WM).
  - intros x Hx. apply HWapp. exact (proj1 (Hpall x Hx)).
  - intros i Hi. rewrite Hasz in Hi.
    unfold r9_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HC.
    pose proof (Hapt i Hi) as Hd.
    pose proof (r9_sh_out (fr + 2368) (fr + 2408) (phi + i)
                  ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)
                  ltac:(lia)) as Hs.
    rewrite E1, E2 in Hs. unfold Sfr in Hs, HC. lia.
  - intros x Hx. apply HWapp. apply Happ. lia.
  - intros i Hi Hi2. unfold r9_Wsh. cbn [Frame.outside]. split; [|exact I].
    destruct Hi2 as [Hl|Hl].
    + pose proof (r9_sh_frame_lo fr (fr + i) Hfr8 ltac:(lia)) as HH. unfold Sfr in HH |- *. lia.
    + pose proof (r9_sh_frame_hi fr (fr + i) Hfr8 ltac:(lia)) as HH. unfold Sfr in HH |- *. lia.
  - intros x Hx. apply HWapp. unfold app_mem. right. lia.
  - intros x Hx. split.
    + apply HWapp. unfold app_mem. left. lia.
    + unfold r9_Wsh. cbn [Frame.outside]. split; [|exact I].
      pose proof (r9_sh_mono x fr ltac:(lia)). unfold Sfr. lia.
  - intros Hin x Hx. apply HWapp.
    destruct (r9_blk_in g fr (hb1 phi (rnb g b)) regs mem md (g_p g) (g_n g) HFRA
                (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hiall).
    exact (proj1 (Hiall x Hx)).
  - intros Hin i Hi.
    pose proof (r9_blk_apart_in g fr (hb1 phi (rnb g b)) regs mem md (g_p g) (g_n g) HFRA
                  (in_or_app _ _ _ (or_intror Hin)) i Hi) as Hd.
    unfold r9_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HC.
    pose proof (r9_sh_out (fr + 2368) (fr + 2408) (g_p g + i)
                  ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)
                  ltac:(lia)) as Hs.
    rewrite E1, E2 in Hs. unfold Sfr in Hs, HC. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* The cut body, RF and RXS across the parse call's writes. *)
Lemma r9_keep3 : forall g b phi fr A regs regs' mem mem' md FS,
  FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
  r9_body g b phi fr regs mem -> RF g fr b phi regs mem -> RXS g fr regs mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  Frame.munch (r9_PW (fr + 2368) (AC.aspZ regs) FS) mem mem' -> Frame.wmono rsegs mem mem' ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 ->
  r9_body g b phi fr regs' mem' /\ RF g fr b phi regs' mem' /\ RXS g fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g b phi fr A regs regs' mem mem' md FS HFRA HBODY HRF HRXS H9 HA Htp HFS MU WM
    E9 E18 E21 E22 E23 E24 E25.
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSal & HFSapp).
  pose proof (HFSfr FS Htp HFS) as HFSlow.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(unfold REAC_CTRL_PARSE_K, FN_STACK, AF.SLOT_STACK; lia)) as Hwd.
  rewrite Haspz in MU, Hwd, Hwlo.
  pose proof (r9_blk g fr phi (rnb g b) regs mem md HFRA) as (Hplo & Hphib & Hpall).
  assert (Hnz : rnb g b <> 0) by (destruct HRF as ((_ & H & _) & _); exact H).
  pose proof (r9_blk_apart g b phi fr regs mem md HFRA Hnz) as Hapt.
  destruct (r9_rtn (g_in g) (Z.of_nat b) Hnz) as (Hrng & _).
  assert (Hasz : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size, rnb in *; lia).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKf2 : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64) by lia.
  assert (HAeq : A = A0) by (apply r9_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst A0.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsp8 : (sp - 8800) mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFRAMEb HFRAMEs HFSal; Z.div_mod_to_equations; lia).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as P1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (Ho0 : fr + 2368 <> 0) by lia.
  assert (HSHO : forall y, 0 <= y < APPMEM_END -> (y < FS + 1085440 \/ FS + 2134016 <= y) ->
            (y < sp - 8800 \/ sp <= y) -> Frame.outside (r9_PW (fr + 2368) sp FS) (shadow_addr y)).
  { intros y Hy Hy1 Hy2. apply r9_PW_out_sh; try lia. }
  assert (HAPO : forall x, app_mem x -> ~ (fr + 2368 <= x < fr + 2404) -> ~ (sp - 8800 <= x < sp) ->
            ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
            ~ (FS + 1085440 <= x < FS + 2134016) -> Frame.outside (r9_PW (fr + 2368) sp FS) x).
  { intros x Hx N1 N2 N3 N4 N5.
    apply r9_PW_out_app; [lia | exact Hx | lia | lia | lia | lia | lia | lia | lia | lia | lia]. }
  assert (HblkFS : forall x, phi <= x < phi + rnb g b -> ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx HC. destruct (Hpall x Hx) as (_ & Hnfs). apply Hnfs.
    exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
  apply (r9_keepg g b phi fr A regs regs' mem mem' md (r9_PW (fr + 2368) sp FS) HFRA HBODY HRF HRXS H9 HA
           MU WM).
  - intros x Hx. pose proof (Hapt (x - phi) ltac:(lia)) as Hd.
    pose proof (HblkFS x Hx) as HnFS.
    apply HAPO; [exact (proj1 (Hpall x Hx)) | lia | lia | lia | lia | lia].
  - intros i Hi. rewrite Hasz in Hi.
    pose proof (Hapt i Hi) as Hd. pose proof (HblkFS (phi + i) ltac:(lia)) as HnFS.
    pose proof (proj1 (Hpall (phi + i) ltac:(lia))) as Happi.
    apply HSHO; [unfold app_mem in Happi; lia | lia | lia].
  - intros x Hx. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
  - intros i Hi Hi2. apply HSHO; [lia | lia | lia].
  - intros x Hx. apply HAPO; [unfold app_mem; right; lia | lia | lia | lia | lia | lia].
  - intros x Hx. split.
    + apply HAPO; [unfold app_mem; left; lia | lia | lia | lia | lia | lia].
    + apply HSHO; lia.
  - intros Hin x Hx.
    destruct (r9_blk_in g fr (hb1 phi (rnb g b)) regs mem md (g_p g) (g_n g) HFRA
                (in_or_app _ _ _ (or_intror Hin))) as (_ & Hiend & Hiall).
    pose proof (r9_blk_apart_in g fr (hb1 phi (rnb g b)) regs mem md (g_p g) (g_n g) HFRA
                  (in_or_app _ _ _ (or_intror Hin)) (x - g_p g) ltac:(lia)) as Hd.
    destruct (Hiall x Hx) as (Hax & Hnfsx).
    assert (HnFS : ~ (FS <= x < FS + AC.FS_SIZE)).
    { intros HC. apply Hnfsx. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
    apply HAPO; [exact Hax | lia | lia | lia | lia | lia].
  - intros Hin i Hi.
    destruct (r9_blk_in g fr (hb1 phi (rnb g b)) regs mem md (g_p g) (g_n g) HFRA
                (in_or_app _ _ _ (or_intror Hin))) as (_ & Hiend & Hiall).
    destruct (Hiall (g_p g + i) ltac:(lia)) as (Hax & Hnfsx).
    assert (HnFS : ~ (FS <= g_p g + i < FS + AC.FS_SIZE)).
    { intros HC. apply Hnfsx. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
    apply HSHO; [unfold app_mem in Hax; lia | lia | lia].
  - exact E9.
  - exact E18.
  - exact E21.
  - exact E22.
  - exact E23.
  - exact E24.
  - exact E25.
Qed.

(* ---------------- the segment lemma ---------------- *)

Lemma seg_R9 : forall b : nat,
  Hat B APIf ra (Inv_A81680_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A81658_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & HBODY & HRF & HRXS).
  subst c. rewrite SEGS.
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA)
    as (Hapart & HfrA & HFSfr & Hfrw).
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshb & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhigh.
  pose proof (r9_blk g fr phi (rnb g b) regs mem md HFRA) as (Hplo & Hphiend & Hpall).
  pose proof HRF as HRF0.
  destruct HRF0 as (((Hb6r & HCURr & HOURr & Hr23r & HIDBr & HFGBr) & Hnz & Hr24 & Hphibytes) & Hr18).
  pose proof (r9_blk_apart g b phi fr regs mem md HFRA Hnz) as Hapt.
  destruct (r9_rtn (g_in g) (Z.of_nat b) Hnz) as (Hrng & HFl).
  assert (Hrnbr : 124 <= rnb g b <= 1492) by (unfold rnb; lia).
  assert (Hasz : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size, rnb in *; lia).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKtp : AC.as_tp AC.ASYMS = 6141968) by (vm_compute; reflexivity).
  assert (HC5 : asan_stack_malloc_c.CF = 1287080) by (vm_compute; reflexivity).
  assert (HC4 : asan_stack_malloc_c.GOT_CF = 654016) by (vm_compute; reflexivity).
  assert (HC5' : bcmp_wrap_c.CF = 1287080) by (vm_compute; reflexivity).
  assert (HC4' : bcmp_wrap_c.GOT_CF = 654016) by (vm_compute; reflexivity).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (HfrE : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha. unfold app_mem in Ha. lia. }
  assert (HSfrlo : LOWMEM_END <= Sfr fr) by (unfold Sfr; apply r9_sh_lo; lia).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hphi64 : 0 <= phi < 2 ^ 64) by lia.
  assert (Hrnb64 : 0 <= rnb g b < 2 ^ 64) by lia.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(lia)) as Hwd. rewrite Haspz in Hwd, Hwlo, Hwstk.
  (* the five frame shadow bytes are writable *)
  assert (Wsh : wr_at rsegs mem (Sfr fr + 296) 5).
  { pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW0.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Ei : Sfr fr + 296 + i = shadow_addr (fr + 2368 + 8 * i))
      by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
    rewrite Ei.
    exact (proj1 (HSW0 (shadow_addr (fr + 2368 + 8 * i))
      (shadow_of_app (fr + 2368 + 8 * i) (Happ (fr + 2368 + 8 * i) ltac:(lia))))). }
  assert (HTPu : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
    by (rewrite Hr4; apply MState.unsigned_lit; lia).
  assert (Hbs50 : length (rt_g (g_in g) (Z.of_nat b)) = 50%nat) by (unfold rt_g; apply fr50_length).
  apply (sl_run_lib regs (Z_to_bv 64 0x81658) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x81680 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 27 = Z_to_bv 64 4 /\
       getr R0 10 = Z_to_bv 64 (fst (ctrlparse (rnb g b) (rt_g (g_in g) (Z.of_nat b)))) /\
       exists m2 FS,
         FRA B APIf ra g fr (hb1 phi (rnb g b)) regs m2 md /\
         ENT APIf g (hb1 phi (rnb g b)) m2 md /\
         r9_body g b phi fr regs m2 /\ RF g fr b phi regs m2 /\ RXS g fr regs m2 /\
         word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
         Frame.munch (r9_PW (fr + 2368) sp FS) m2 mem' /\ Frame.wmono rsegs m2 mem' /\
         ro_same rsegs m2 mem' /\
         stk rsegs mem' (sp - REAC_CTRL_PARSE_K) sp /\
         rw_cells rsegs mem' (fr + 2368)
           [CB 36 (snd (ctrlparse (rnb g b) (rt_g (g_in g) (Z.of_nat b))))] /\
         shadow_rw mem' /\ addressable mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs mem' FS (FS + FS_SIZE) /\ fp_cls mem' FS 1)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the run 0x81658 -> 0x81680 *)
    rewrite r9_mkR_of_expand.
    r9_subst_slot Hr2. r9_subst_slot Hr9. r9_subst_slot Hr19. r9_subst_slot Hr18. r9_subst_slot Hr24.
    eapply LE.evt_cut.
    { eapply r9_st with (fr := fr); [lia | lia | exact Wsh]. }
    intros ms1 (m2 & E1 & MU1 & WM1 & ST1 & HSH2). subst ms1.
    (* FRA, ENT and the cut body at m2 *)
    destruct (r9_fra_sh g fr (hb1 phi (rnb g b)) regs mem m2 md HFRA HENT MU1 WM1 HSH2)
      as (HFRA2 & HENT2).
    destruct (r9_keep2 g b phi fr A regs mem m2 md HFRA HBODY HRF HRXS Hr9 HA64 MU1 WM1)
      as (HBODY2 & HRF2 & HRXS2).
    pose proof HRF2 as HRF2c.
    destruct HRF2c as (((_ & _ & _ & _ & _ & _) & _ & _ & Hphibytes2) & _).
    pose proof HRXS2 as HRXS2c.
    destruct HRXS2c as (_ & X56 & _).
    pose proof HBODY2 as HBODY2c.
    destruct HBODY2c as (_ & _ & HHB2 & _).
    pose proof (r9_spill_at regs A 56 (fr + 2368) m2 X56 Hr9 HA64 ltac:(lia) ltac:(lia)) as Hq56.
    (* the side-stack package of the call, from FRA alone (Seg/Tac_fsfree.v's fra_fp) *)
    assert (Hne : (fr + 2368 =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (Hcs : forall cc, In cc [1%nat] -> (cc <= 5)%nat).
    { intros cc Hc. cbn [In] in Hc. destruct Hc as [<- | []]. apply Nat.leb_le. reflexivity. }
    assert (HKr : 8 <= REAC_CTRL_PARSE_K <= FN_STACK) by lia.
    assert (HWr : forall w, In w (reac_ctrl_parse_W (fr + 2368) (AC.aspZ regs)) ->
       (g_S g - AF.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
       (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
    { intros w Hw. unfold reac_ctrl_parse_W in Hw. rewrite Hne in Hw. cbn [In app] in Hw.
      destruct Hw as [<- | [<- | []]]; cbn [fst snd]; rewrite ?Haspz.
      - left. lia.
      - right. left. lia. }
    assert (HDr : forall d, In d (reac_ctrl_parse_D phi (rnb g b) (fr + 2368)) ->
       snd d <= AC.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
       (fst d < snd d /\ exists p n, In (p, n) (hb1 phi (rnb g b) ++ g_H g) /\ p <= fst d /\ snd d <= p + n)).
    { intros d Hd. unfold reac_ctrl_parse_D in Hd. rewrite Hne in Hd.
      destruct (Z_lt_ge_dec (rnb g b) 50) as [Hlt|Hge].
      - rewrite (proj2 (Z.ltb_lt (rnb g b) 50) ltac:(lia)) in Hd. cbn [In app] in Hd.
        destruct Hd as [<- | []]. right. left. cbn [fst snd]. lia.
      - rewrite (proj2 (Z.ltb_ge (rnb g b) 50) ltac:(lia)) in Hd. cbn [In app] in Hd.
        destruct Hd as [<- | [<- | []]]; cbn [fst snd].
        + right. right. split; [lia|]. exists phi, (rnb g b).
          split; [apply in_or_app; left; left; reflexivity|]. lia.
        + right. left. lia. }
    destruct (fra_fp B APIf ra g fr (hb1 phi (rnb g b)) regs m2 md [1%nat] REAC_CTRL_PARSE_K
                (reac_ctrl_parse_W (fr + 2368) (AC.aspZ regs))
                (reac_ctrl_parse_D phi (rnb g b) (fr + 2368)) HFRA2 Hcs HKr HWr HDr)
      as (FS & HFP & HTLS & _ & _).
    (* the FakeStack base as a word, and its bounds *)
    pose proof HFP as HFPc.
    destruct HFPc as (DTx & TSx & Cx & Tx & DBx & kx & _ & Htpb & Hplace & _).
    destruct Hplace as (HFS0 & HFSmod & HFSgt & HFSappf & HFSstk).
    assert (HFSub : FS + FS_SIZE <= APPMEM_END).
    { pose proof (HFSappf (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hx.
      unfold app_mem, FS_SIZE in Hx |- *. lia. }
    assert (HFS : 0 <= FS < 2 ^ 64) by (unfold FS_SIZE in HFSub; lia).
    assert (Htp2 : word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS).
    { pose proof (bytes_at_le8_word rsegs m2 (AC.as_tp AC.ASYMS) (Z_to_bv 64 FS) Htpb) as HW.
      rewrite MState.unsigned_lit in HW by lia. exact HW. }
    (* the window facts of the call *)
    destruct (fra_callee_fp B APIf ra g fr (hb1 phi (rnb g b)) regs m2 md REAC_CTRL_PARSE_K [1%nat] FS
                (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs) _ _ HFRA2 ltac:(lia) HFP HTLS
                ltac:(lia) ltac:(lia)) as (HK1 & HK2 & HK3 & HSTKw & HAPPw & HADw & _ & _).
    rewrite Haspz in HK1, HK2, HK3, HSTKw, HADw, HFP, HTLS.
    pose proof HFRA2 as HFRA2c.
    destruct HFRA2c as (A3 & sp3 & s53 & HRT2 & HAH2 & HRO2 & _).
    (* the record cell at fr + 2368 *)
    pose proof (r9_frame_stk g fr (hb1 phi (rnb g b)) regs m2 md HFRA2) as Hfstk2.
    pose proof (r9_sub_stk m2 fr (fr + 2368) (fr + 2404) Hfstk2 ltac:(lia) ltac:(lia) ltac:(lia)) as HSTKo2.
    destruct (stk_carve rsegs m2 (fr + 2368) (fr + 2404) 36 HSTKo2 ltac:(cbn; lia)) as (_ & junk & HRWo).
    replace (fr + 2404 - Z.of_nat 36) with (fr + 2368) in HRWo by (cbn; lia).
    assert (HADDRo : addressable m2 (fr + 2368) 36)
      by exact (r9_addr_o m2 fr ltac:(lia) Hfrm Happ ltac:(lia) HSH2).
    (* the instrumented globals at m2 *)
    assert (HAG2 : forall a, in_globals AF.frame_AG a -> addressable m2 a 1).
    { pose proof HFRA2 as HFRA2d.
      destruct HFRA2d as (A4 & sp4 & s54 & HRT4 & HAH4 & Hro4 & Hsn4 & Hhalt4 & Hgimg4 & Hr2x & Hspm4 &
        Haspz4 & Hstklo4 & Hr44 & Hr84 & Hr94 & Hr34 & Hr194 & Hr264 & Hfrm4 & Hs54 & HAm4 & HAS4 & Hspa4 &
        Hfa4 & HA4164 & HS44 & HAPP4 & Hspill4 & Hsel4 & Hfr244 & Hloc4 & Hhdr14 & Hhdr24 & Hsh4 & Hwin4 &
        Hsaved4 & Herrno4 & HAG4 & HWA4 & HSHI14 & HSHI24 & HSHI34 & Hhb4 & Hlive4).
      exact HAG4. }
    assert (HBCA2 : addressable m2 REAC_CTRL_PARSE_BC 6).
    { unfold REAC_CTRL_PARSE_BC. split; [lia|]. split; [lia|]. split; [lia|].
      intros i Hi.
      assert (Hg : addressable m2 (0x21200 + i) 1).
      { apply HAG2. exists 0x21200, 7. split; [|lia].
        unfold AF.frame_AG. cbn [In]. repeat (first [left; reflexivity | right]). }
      destruct Hg as (_ & _ & _ & Hg). pose proof (Hg 0 ltac:(lia)) as Hg0. rewrite Z.add_0_r in Hg0.
      exact Hg0. }
    destruct (r9_rt_cells _ _ _ HRT2) as (HBY1 & HBY2 & HBY3 & HBY4 & HBY5).
    eapply LE.evt_mono.
    { eapply r9_calln with (m := m2) (A := A) (f := phi) (n := rnb g b) (o := fr + 2368) (S := sp)
                (FS := FS) (bs := rt_g (g_in g) (Z.of_nat b)) (junk := junk).
      - lia.
      - lia.
      - unfold AC.GT in HGT. lia.
      - lia.
      - lia.
      - exact Hspm.
      - lia.
      - lia.
      - lia.
      - exact HSTKw.
      - exact HRO2.
      - exact Hbs50.
      - apply r9_rd8; [exact Hq56 | apply length_le8].
      - intros H50. split; [lia|]. split; [lia|]. left. lia.
      - exact (r9_rd_g m2 (g_in g) (Z.of_nat b) phi Hphibytes2 Hnz).
      - clear - HFRAMEb HFRAMEs Hfrm. Z.div_mod_to_equations. lia.
      - exact HRWo.
      - destruct Hwd as [Hd|Hd]; [left; lia | right; lia].
      - intros H50. pose proof (Hapt 0 ltac:(lia)) as H0. pose proof (Hapt 49 ltac:(lia)) as H49. lia.
      - exact (AsanRTInv.RT_cells _ _ _ HRT2).
      - exact (AsanRTInv.RT_shadow_rw _ _ _ HRT2).
      - lia.
      - lia.
      - exact HADw.
      - intros H50. destruct HHB2 as (_ & Had). rewrite Hasz in Had.
        replace phi with (phi + 0) by lia.
        exact (r9_addr_sub m2 phi (rnb g b) 0 50 Had ltac:(lia) ltac:(lia) ltac:(lia)).
      - exact HADDRo.
      - apply Happ. lia.
      - right. unfold AC.GT in HGT. lia.
      - exact HBCA2.
      - exact HBY1.
      - exact HBY2.
      - exact HBY3.
      - exact HBY4.
      - exact HBY5.
      - rewrite HTPu. exact HFP.
      - rewrite HTPu. exact HTLS. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
        E & MU3 & WM3 & HRS3 & ST3 & RW3 & SW3 & AD3 & FSS3 & CLS3).
      eexists _, (Z_to_bv 64 0x81680), m'. split; [exact E|].
      repeat (split; [first [reflexivity | (symmetry; assumption) | assumption]|]).
      exists m2, FS.
      split; [exact HFRA2|]. split; [exact HENT2|]. split; [exact HBODY2|]. split; [exact HRF2|].
      split; [exact HRXS2|]. split; [exact Htp2|]. split; [exact HFS|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact HRS3|]. split; [exact ST3|].
      split; [exact RW3|]. split; [exact SW3|]. split; [exact AD3|].
      split; [exact FSS3 | exact CLS3]. }
  - (* the exit cut *)
    intros R0 pc' mem' regs'' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er21 & Er22 & Er23 & Er24 & Er25 & Er27 &
       Er10 & m2 & FS & HFRA2 & HENT2 & HBODY2 & HRF2 & HRXS2 & Htp2 & HFS & MU3 & WM3 & HRS3 & ST3 & RW3 &
       SW3 & AD3 & FSS3 & CLS3) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr27 : getr regs'' 27 = Z_to_bv 64 4) by (rewrite Hreg; exact Er27).
    assert (Fr10 : getr regs'' 10 = Z_to_bv 64 (fst (ctrlparse (rnb g b) (rt_g (g_in g) (Z.of_nat b)))))
      by (rewrite Hreg; exact Er10).
    rewrite <- Haspz in MU3, ST3, AD3.
    destruct (r9_fra_call g fr (hb1 phi (rnb g b)) regs regs'' m2 mem' md md' FS _ HFRA2 Htp2 HFS MU3 WM3
                HRS3 ST3 AD3 RW3 SW3 FSS3 CLS3 Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA' & HENTi).
    pose proof (HENTi HENT2) as HENT'.
    destruct (r9_keep3 g b phi fr A regs regs'' m2 mem' md FS HFRA2 HBODY2 HRF2 HRXS2 Hr9 HA64 Htp2 HFS
                MU3 WM3 Fr9 Fr18 Fr21 Fr22 Fr23 Fr24 Fr25) as (HBODY' & HRF' & HRXS').
    rewrite <- SEGS. apply Hexit.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact HBODY'|].
    split; [exact HRF'|]. split; [exact HRXS'|].
    split; [unfold a0v, rg; exact Fr10 | unfold rg; exact Fr27].
Qed.

End S.
