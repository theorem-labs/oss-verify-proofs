(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode, on libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput.v (its
   fd_entry.v / fd_exit.v flow): the plain-image walk of LLVMFuzzerTestOneInput (fuzz_decode.c:278-344), 0x12cd4,
   2568 bytes, against LLVMFuzzerTestOneInput_c.v's LLVMFuzzerTestOneInput_sr_contract. size = 0 or size >= 2^26 is
   LLVMFuzzerTestOneInput_early.v's llvm_early; else the entry (LLVMFuzzerTestOneInput_entry.v) runs to malloc, the
   SR call g_malloc gives buf (never NULL, so the abort at 0x136d8 is not reached), the evt run of
   LLVMFuzzerTestOneInput_mid.v goes from malloc's return to check_refusal's return (every abort of a check_
   function is unreachable by its contract, whose premise the agreement theorems give at each pass), and
   LLVMFuzzerTestOneInput_exit.v frees buf and returns 0. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c
  diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c check_refusal_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_glue LLVMFuzzerTestOneInput_early
  LLVMFuzzerTestOneInput_entry LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_seg2
  LLVMFuzzerTestOneInput_mid.
Import ListNotations.
Open Scope Z_scope.

Lemma dup_size_range : forall n, 0 <= n -> 1 <= dup_size n <= n + 1.
Proof. intros n Hn. unfold dup_size. destruct (Z.eqb_spec n 0); lia. Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis BND : blocks_nodup B API.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis CIN : diginet_cursor_init_contract.
Hypothesis MNX : diginet_msg_next_contract.
Hypothesis POF : diginet_personality_of_contract.
Hypothesis DIN : diginet_decoder_init_contract.
Hypothesis DNX : diginet_decoder_next_contract.
Hypothesis CCS : check_cursor_step_contract.
Hypothesis CCM : check_cursor_message_contract.
Hypothesis CES : check_events_step_contract.
Hypothesis CEF : check_events_fields_contract.
Hypothesis CRF : check_refusal_contract.
Hypothesis CST : cstep_stmt.
Hypothesis DST : dstep_stmt.
Hypothesis DSY : dsysex_stmt.
Hypothesis DCH : dchan_stmt.
Hypothesis SET : setup_stmt.
Hypothesis CLP : cloop_stmt.
Hypothesis DSE : dsetup_stmt.
Hypothesis DLP : dloop_stmt.

Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  pose proof (mid_evt MSET MCPY CIN MNX POF DIN DNX CCS CCM CES CEF CRF CST DST DSY DCH SET CLP DSE DLP) as MID.
  intros BI j Hj ra empty stk Hk Hra L0 A0 regs0 mem0 md0 p n pl b Hpre Hn Hpd Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound stk empty L0 A0 regs0 mem0 md0 ra p n Hpre) as Hnb.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  assert (E11g : YK11.getr regs0 11 = Z_to_bv 64 n) by exact Hn1.
  destruct (Z_lt_le_dec 0 n) as [Hn0 | Hn0];
    [destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall | Hbig] |].
  2:{ apply (llvm_early B API SINK j stk empty L0 A0 regs0 mem0 md0 ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite E11g. rewrite MState.unsigned_lit by lia. right. exact Hbig. }
  2:{ apply (llvm_early B API SINK j stk empty L0 A0 regs0 mem0 md0 ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite E11g. rewrite MState.unsigned_lit by lia. left. lia. }
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  pose proof Hk as Hk0. unfold LLVM_K, LLVM_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs0 = bv_unsigned (reg_get regs0 2)) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (PAY : In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { destruct Hpl as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  destruct PAY as (PIN & PLO & PHI).
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp.
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 n) by exact Hn1.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (spZ regs0 - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. eapply norm_stk; try eassumption; try lia; unfold LF_RES_TOP; lia. }
  assert (BP0 : bytes_at rsegs (normalize rsegs mem0) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_mal (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (normalize rsegs mem0)
            (bv_unsigned (reg_get regs0 2) - 448) (spZ regs0 - stk) p n pl (llvm_saved_cells regs0)).
  all: try eassumption. all: try lia.
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    eapply e_entry with (lo := spZ regs0 - stk); try eassumption; try lia.
    - apply mem_inv_normalize. }
  { intros ms (R & m' & j' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists R, (@fp_regs fx), (Z_to_bv 64 0x14e30), (@fp_csr fx), m',
      [(bv_unsigned (reg_get regs0 2) - 448, bv_unsigned (reg_get regs0 2) - 448 + 448)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc ma HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & j' & HE & R1 & R2 & R3 & R4 & R8 & R10 & R18 & R19 & R20 & MU1 & WM1 & MI1
    & ST1 & RW1).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12d38) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R1).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs0 - 448)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R2).
  assert (G13 : YK11.getr regs1 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R3).
  assert (G14 : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R4).
  assert (G18 : YK11.getr regs1 8 = Z_to_bv 64 n) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R8).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (dup_size (n - 1))) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R10).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 (n - 1)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R18).
  assert (G119 : YK11.getr regs1 19 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R19).
  assert (G120 : YK11.getr regs1 20 = sxb (nth 0 pl (Z_to_bv 8 0))) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R20).
  assert (Hsp1 : spZ regs1 = spZ regs0 - 448) by (unfold spZ at 1; rewrite G12; apply MState.unsigned_lit; lia).
  assert (Hra1' : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0) by (rewrite Hsp1; Z.div_mod_to_equations; lia).
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (rewrite G14; exact Htp).
  pose proof (dup_size_range (n - 1) ltac:(lia)) as DSR.
  assert (ROOM1 : room_slots b (dup_size (n - 1))).
  { destruct Hroom as (Hl1 & Hl2 & Hl3). apply lf_room; lia. }
  pose proof (lf_rw_cells_rel m1 ma _ _ Hrel RW1) as RWa.
  rewrite <- SEGS. change (Z_to_bv 64 0x14e30) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (n := dup_size (n - 1)) (bres := b).
  all: try eassumption. all: try (rewrite ?Hsp1; lia). all: try (rewrite ?Hsp1; unfold ALLOC_STACK; lia).
  intros L1 A1 regs2 mem2 md2 res FR2 Hrp2 G210 Hr1 Hr2 Hr16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G1, SEGS.
  set (nb := dup_size (n - 1)) in *.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & HwX2 & _ & _ & Hro2).
  assert (Hres_in : In (res, nb) (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (res, nb) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) -> a + k <= res \/ res + nb <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (disj_mid b1 (res, nb) b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  assert (Hnf : forall a k, In (a, k) (blocks L0 A0) -> a <> res).
  { intros a k Hak Ea. subst a. pose proof (BND L1 A1 mem2 md2 HM2) as ND. rewrite Eb1, map_app in ND.
    cbn [map fst] in ND. apply NoDup_ListNoDup in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app, <- Eb2.
    apply in_map_iff. exists (res, k). split; [reflexivity | exact Hak]. }
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 448)).
  { change (reg_get regs2 2) with (YK11.getr regs2 (Z_to_bv 5 2)).
    rewrite (Y2 2 ltac:(unfold callee_saved; lia)). exact G12. }
  assert (E23 : reg_get regs2 3 = reg_get regs0 3).
  { change (reg_get regs2 3) with (YK11.getr regs2 (Z_to_bv 5 3)).
    rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13. }
  assert (E24 : reg_get regs2 4 = reg_get regs0 4).
  { change (reg_get regs2 4) with (YK11.getr regs2 (Z_to_bv 5 4)).
    rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14. }
  assert (E28 : reg_get regs2 8 = Z_to_bv 64 n).
  { change (reg_get regs2 8) with (YK11.getr regs2 (Z_to_bv 5 8)).
    rewrite (Y2 8 ltac:(unfold callee_saved; lia)). exact G18. }
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 res) by exact G210.
  assert (E218 : reg_get regs2 18 = Z_to_bv 64 (n - 1)).
  { change (reg_get regs2 18) with (YK11.getr regs2 (Z_to_bv 5 18)).
    rewrite (Y2 18 ltac:(unfold callee_saved; lia)). exact G118. }
  assert (E219 : reg_get regs2 19 = Z_to_bv 64 p).
  { change (reg_get regs2 19) with (YK11.getr regs2 (Z_to_bv 5 19)).
    rewrite (Y2 19 ltac:(unfold callee_saved; lia)). exact G119. }
  assert (E220 : reg_get regs2 20 = sxb (nth 0 pl (Z_to_bv 8 0))).
  { change (reg_get regs2 20) with (YK11.getr regs2 (Z_to_bv 5 20)).
    rewrite (Y2 20 ltac:(unfold callee_saved; lia)). exact G120. }
  assert (BP2 : bytes_at rsegs (normalize rsegs mem2) p pl).
  { assert (BD : blk_data B mem2 p pl) by (eapply blk_keep; [exact FR2 | rewrite <- Hn; exact PIN | exact Hpd]).
    apply bytes_at_normalize; [exact Hro2|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 res nb HM2 Hres_in ltac:(lia) Hro2) as [junk HJ].
  assert (RWb : forall a, bv_unsigned (reg_get regs0 2) - 448 <= a < bv_unsigned (reg_get regs0 2) ->
     mbyte rsegs mem2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs mem2 a)).
  { intros a Ha. pose proof (Habove2 a ltac:(rewrite Hsp1; lia)) as E. rewrite SEGS in E. exact E. }
  assert (SZ0 : cells_size (CB 344 j' :: llvm_saved_cells regs0) = 448%nat) by reflexivity.
  pose proof (lf_rw_cells_frame m1 mem2 _ _ RWa (fun a Ha => RWb a ltac:(rewrite SZ0 in Ha; lia))) as RW2.
  assert (NI : forall a, 0x50000 <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (lf_in_img_top B a SEGS Hi) as H; unfold LF_RES_TOP in H; lia).
  pose proof (fun H => lf_rw_cells_norm B mem2 _ _ SEGS Hro2 H RW2) as RW3.
  specialize (RW3 (fun i Hi => NI (bv_unsigned (reg_get regs0 2) - 448 + i) ltac:(rewrite SZ0 in Hi; lia))).
  assert (ST2 : Frame.stk rsegs (normalize rsegs mem2) (spZ regs0 - stk) (bv_unsigned (reg_get regs0 2) - 448)).
  { eapply norm_stk; try eassumption; try (unfold LF_RES_TOP; lia).
    intros a Ha. apply HwX2. lia. }
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_x (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
            (bv_unsigned (reg_get regs0 2) - 448) (spZ regs0 - stk) res nb (llvm_saved_cells regs0)).
  all: try eassumption. all: try lia.
  { unfold Regs6ss.mkR_of. rewrite E22, E28, E210, E218, E219, E220. subst n.
    apply MID with (junk := junk) (j := j').
    all: first [eassumption | reflexivity | apply mem_inv_normalize | lia
               | (destruct (MINE p (Z.of_nat (length pl)) PIN); lia)]. }
  { intros ms (R0 & m' & jx & jy & -> & _ & _ & _ & MU & WM & _).
    exists R0, (@fp_regs fx), (Z_to_bv 64 0x13684), (@fp_csr fx), m',
      [(spZ regs0 - stk, bv_unsigned (reg_get regs0 2) - 448 + 448); (res, res + nb)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx0 NO. cbn [outside] in NO.
    destruct (Z_lt_le_dec x (bv_unsigned (reg_get regs0 2))) as [Hlt|Hge].
    - destruct (Z_le_dec (spZ regs0 - stk) x) as [Hle|Hgt]; [left; lia|].
      right. exists res, nb. split; [|lia].
      unfold lf_mine. split; [exact Hres_in|]. split; [lia|]. exact MINE.
    - destruct (Z_le_dec res x) as [Hle|Hgt].
      + right. exists res, nb. split; [|lia]. unfold lf_mine. split; [exact Hres_in|]. split; [lia|]. exact MINE.
      + exfalso. apply NO. split; [lia|]. split; [lia | exact I]. }
  intros Rb F pc' fc mb HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (R' & m'' & jx & jy & HE & Q2 & Q3 & Q4 & MU3 & WM3 & MI3 & ST3 & RW3b).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (spZ regs0 - 448)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact Q2).
  assert (G33 : YK11.getr regs3 3 = YK11.getr regs0 3)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); change (reg_get Rb 3 = reg_get regs0 3); rewrite Q3; exact E23).
  assert (G34 : YK11.getr regs3 4 = YK11.getr regs0 4)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); change (reg_get Rb 4 = reg_get regs0 4); rewrite Q4; exact E24).
  pose proof (lf_rw_cells_rel m3 mb _ _ Hrel3 RW3b) as RW4.
  pose proof (fx_exit_holds B API FREE ERRNO_LOW SINK stk empty L0 A0 regs0 mem0 md0 ra p n b j
    (mkFP (@fp_regs fx) (@fp_csr fx)) regs3 m3 md2 L1 A1 res nb jx jy BI Hk0 Hra Hpre Hsn Hfrm FR3 Hres_in Hnf
    Hres2 G32 G33 G34 RW4) as HX.
  unfold llvm_sr_post in HX. rewrite SEGS in HX. rewrite ?SEGS. exact HX.
Qed.

End M.
