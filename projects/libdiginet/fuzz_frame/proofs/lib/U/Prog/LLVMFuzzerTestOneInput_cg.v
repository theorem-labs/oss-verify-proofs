(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_cg.v, with its module paths changed; 384 of its 407 lines of code are new or changed and 22 lines of the source are left out. *)
(* the crash-free UBSan walk of fuzz_frame's LLVMFuzzerTestOneInput against its SRcf contract, with the callee contracts as Section hypotheses. *)
(* LLVMFuzzerTestOneInput in fuzz_frame.ubsan, 0x12d48, against LLVMFuzzerTestOneInput_sr_contract_cf
   (U/Prog/LLVMFuzzerTestOneInput_cfb.v), in the form of libreac/fuzz_decode's lib/U/Prog/LLVMFuzzerTestOneInput_cg.v
   (bf7779f81ed7). The walk is the one of LLVMFuzzerTestOneInput.v (the same Exec.evt segments, lt_b from there),
   with SRcf in place of SR: the calls go through the crash-free glue lt_glue_cg.v (malloc_contract_ag,
   free_contract_cf, check_round_trip_contract_cf) and the return at once through LLVMFuzzerTestOneInput_early_cg.v.
   The room of the crash-free allocator: llvm_room_cf gives room_ag for the copy of the input (lf_room_ag) and the
   room premise of check_round_trip_contract_cf. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import memcpy_c memset_c diginet_frame_parse_c
  check_parse_refusal_c check_parse_fields_c check_round_trip_c check_announce_c CheckStackU
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_early lt_glue
  lt_seg_a lt_seg_b1 lt_seg_b2 lt_seg_c LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb check_round_trip_ccf
  lt_glue_cg LLVMFuzzerTestOneInput_early_cg.
Import ListNotations.
Open Scope Z_scope.
Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis MC : memcpy_contract.
Hypothesis MSET : memset_contract.
Hypothesis PARSE : diginet_frame_parse_contract.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract_cf fx' rc B API.
Hypothesis CA : check_announce_contract.

(* free (buf), then 0x12fdc .. ret: a0 = 0, ra, s0, s1, s2 back from their cells at S - 32 (crash-free). *)
Lemma lt_exit_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n b j (fx' : YK11.FPState) regs mem md L A buf nb,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> sink_none B mem0 md0 ->
  frm_zero (@fp_csr fx') ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  In (buf, nb) (blocks L A) -> 0 < nb -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= buf \/ buf + nb <= a) ->
  res_ok_slots A (sb_malloc b nb) ->
  YK11.getr regs 1 = Z_to_bv 64 0x12fdc ->
  YK11.getr regs 2 = Z_to_bv 64 (spZ regs0 - 176) ->
  YK11.getr regs 10 = Z_to_bv 64 buf ->
  (forall x, (x = 3 \/ x = 4 \/ 19 <= x <= 27) -> YK11.getr regs (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)) ->
  rw_cells rsegs mem (spZ regs0 - 32)
    [C8 (YK11.getr regs0 18); C8 (YK11.getr regs0 9); C8 (YK11.getr regs0 8); C8 (YK11.getr regs0 1)] ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_FREE) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b j fx' regs mem md L A buf nb
    BI Hk Hra Hpre Hsn Hfrm FR Hin Hnb Hd Hres G1 G2 G10 GK HSV.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0
    & Hpl0 & Hrod0).
  rewrite llvm_K_val in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  remember (spZ regs0) as S eqn:ES.
  assert (Hsp : spZ regs = S - 176) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hra1 : YK0s.ret_ok (YK11.getr regs 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs mod 16 = 0).
  { rewrite Hsp. replace (S - 176) with (S + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact Hal0. }
  assert (Htp1 : YK11.getr regs 4 = Z_to_bv 64 (ms_tp B)) by exact (eq_trans (GK 4 ltac:(lia)) Htp0).
  eapply (g_free_cf B API) with (stk := stk) (S := S) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (x := buf)
    (n := nb) (bres := sb_malloc b nb).
  all: try eassumption.
  all: try (rewrite ?Hsp; unfold ALLOC_STACK; lia).
  intros L' A' regs' mem' md' FR' Hrp' Eb' Hres' Habove' Hkept'.
  rewrite G1, SEGS.
  pose proof FR' as (HM' & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM') as (Hh' & Hl' & _).
  assert (HSV' : rw_cells rsegs mem' (S - 32)
    [C8 (YK11.getr regs0 18); C8 (YK11.getr regs0 9); C8 (YK11.getr regs0 8); C8 (YK11.getr regs0 1)]).
  { apply (lf_rw_cells_frame mem); [exact HSV|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    rewrite <- SEGS. apply Habove'. rewrite Hsp. lia. }
  assert (P2 : reg_get regs' 2 = Z_to_bv 64 (S - 176)).
  { change (YK11.getr regs' (Z_to_bv 5 2) = Z_to_bv 64 (S - 176)).
    rewrite (Hrp' 2 ltac:(unfold callee_saved; lia)). exact G2. }
  assert (PK : forall x, (x = 3 \/ x = 4 \/ 19 <= x <= 27) ->
            reg_get regs' (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)).
  { intros x Hx. rewrite <- lt_getr_cs by (unfold callee_saved; lia).
    rewrite (Hrp' x ltac:(unfold callee_saved; lia)). exact (GK x Hx). }
  apply (llvm_run_cf B SEGS fx' regs' (Z_to_bv 64 0x12fdc) mem' md'
    (fun ms => exists a0' : word, a0' = Z_to_bv 64 0 /\
       ms = MS (mkR (YK11.getr regs0 1) (Z_to_bv 64 (bv_unsigned (reg_get regs' 2) + 176)) (reg_get regs' 3)
                    (reg_get regs' 4) (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) (YK11.getr regs0 8)
                    (YK11.getr regs0 9) a0' (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13)
                    (reg_get regs' 14) (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17) (YK11.getr regs0 18)
                    (reg_get regs' 19) (reg_get regs' 20) (reg_get regs' 21) (reg_get regs' 22) (reg_get regs' 23)
                    (reg_get regs' 24) (reg_get regs' 25) (reg_get regs' 26) (reg_get regs' 27) (reg_get regs' 28)
                    (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31))
               (@fp_regs fx') (ret_pc (YK11.getr regs0 1)) (@fp_csr fx') None mem' (seg_rom rsegs)));
    [exact Hh' | exact Hl' | | |].
  { unfold Regs6ss.mkR_of. apply lt_d.
    - rewrite P2, MState.unsigned_lit by lia. replace (S - 176 + 144) with (S - 32) by lia. exact HSV'.
    - rewrite P2, MState.unsigned_lit by lia. lia. }
  { intros ms (a0' & _ & ->). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (a0' & Ea0 & HE) regs'' Hx''.
  injection HE as ER EF EP EC EM. subst R F pc' fc m' a0'.
  apply (SRcf_ret B).
  assert (G10'' : YK11.getr regs'' 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx''); reflexivity).
  assert (RP : regs_preserved regs0 regs'').
  { intros x Hx4. rewrite (lf_getr_eqv _ _ _ Hx'').
    destruct (lt_callee_cases x Hx4) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - change (Z_to_bv 64 (bv_unsigned (reg_get regs' 2) + 176) = YK11.getr regs0 (Z_to_bv 5 2)).
      rewrite P2, MState.unsigned_lit by lia. replace (S - 176 + 176) with S by lia. subst S.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - exact (PK 3 ltac:(lia)).
    - exact (PK 4 ltac:(lia)).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact (PK 19 ltac:(lia)).
    - exact (PK 20 ltac:(lia)).
    - exact (PK 21 ltac:(lia)).
    - exact (PK 22 ltac:(lia)).
    - exact (PK 23 ltac:(lia)).
    - exact (PK 24 ltac:(lia)).
    - exact (PK 25 ltac:(lia)).
    - exact (PK 26 ltac:(lia)).
    - exact (PK 27 ltac:(lia)). }
  subst S.
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L' A' regs'' mem' md' Hpre Hsn FR' G10'' RP)
    as (Hpost & Hsn' & Hpay & MI2).
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L', A', regs'', mem', md'.
  split; [rewrite Hra0, (lf_ret_pc _ Hra), SEGS; reflexivity|].
  split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
  split; [rewrite sb_free_malloc in Hres'; exact Hres'|].
  split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

Theorem LLVMFuzzerTestOneInput_holds_of_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  change (SRcf B (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L A regs mem md ra p n b j)).
  pose proof (llvm_n_bound B API stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn11 & Hpl0 & Hrod).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hk as Hk'. rewrite llvm_K_val in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  assert (E11 : reg_get regs 11 = Z_to_bv 64 n) by exact Hn11.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 p) by exact Hp.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem) (spZ regs - stk) (bv_unsigned (reg_get regs 2))).
  { rewrite <- Esp. apply (norm_stk B SEGS); [exact Hro | unfold LF_RES_TOP; lia | lia | exact Hstw]. }
  set (n' := n + (if n =? 0 then 1 else 0)).
  assert (Hn' : 1 <= n' <= 2 ^ 26 /\ n <= n') by (unfold n'; destruct (Z.eqb_spec n 0); lia).
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG) with (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (L := L) (A := A).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY.
    eapply lt_a with (lo := spZ regs - stk) (n := n); [exact ST0 | lia | apply mem_inv_normalize | exact E11 | lia]. }
  { intros ms (a1' & m' & -> & MU & WM & _ & _).
    do 5 eexists. exists [(bv_unsigned (reg_get regs 2) - 176, bv_unsigned (reg_get regs 2))].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply lt_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (a1' & m'' & HE & MU1 & WM1 & MI1 & SV1).
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  (* at the call of malloc *)
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 0x12d78) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 n') by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (G19 : YK11.getr regs1 9 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx1); exact E10).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 n) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (GK1 : forall x, (x = 3 \/ x = 4 \/ x = 8 \/ 19 <= x <= 27) ->
            YK11.getr regs1 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
  { intros x Hx. rewrite (lf_getr_eqv _ _ _ Hx1).
    assert (C : x = 3 \/ x = 4 \/ x = 8 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/
                x = 26 \/ x = 27) by lia.
    repeat (destruct C as [-> | C]; [reflexivity|]). subst. reflexivity. }
  assert (Hsp1 : spZ regs1 = spZ regs - 176) by (unfold spZ at 1; rewrite G12; apply MState.unsigned_lit; lia).
  assert (SVr1 : rw_cells rsegs m1 (spZ regs - 32)
    [C8 (YK11.getr regs 18); C8 (YK11.getr regs 9); C8 (YK11.getr regs 8); C8 (YK11.getr regs 1)])
    by exact (lf_rw_cells_rel m1 m'' _ _ Hrel1 SV1).
  assert (Hra1' : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G11; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0).
  { rewrite Hsp1. replace (spZ regs - 176) with (spZ regs + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact Hal. }
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by exact (eq_trans (GK1 4 ltac:(lia)) Htp).
  assert (ROOM1 : room_ag b n') by (destruct Hroom as (Hl1 & Hl2 & Hl3); apply lf_room_ag; lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x14f2c) with (Z_to_bv 64 LLVM_MALLOC).
  eapply (g_malloc_cf B API) with (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (n := n') (bres := b).
  all: try eassumption.
  all: try (rewrite ?Hsp1; unfold ALLOC_STACK; lia).
  intros L1 A1 regs2 mem2 md2 res FR2 Hrp2 G210 Hr1 Hr2 Hr16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G11, SEGS.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & Hstw2 & Herr2 & _ & Hro2).
  assert (Hres_in : In (res, n') (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (res, n') :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
  assert (MINE : forall a k, In (a, k) (blocks L A) -> a + k <= res \/ res + n' <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (disj_mid b1 (res, n') b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : reg_get regs2 2 = Z_to_bv 64 (spZ regs - 176)).
  { change (YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 176)).
    rewrite (Y2 2 ltac:(unfold callee_saved; lia)). exact G12. }
  assert (E29 : reg_get regs2 9 = Z_to_bv 64 p).
  { change (YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 p). rewrite (Y2 9 ltac:(unfold callee_saved; lia)). exact G19. }
  assert (E218 : reg_get regs2 18 = Z_to_bv 64 (Z.of_nat (length pl))).
  { change (YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 (Z.of_nat (length pl))).
    rewrite (Y2 18 ltac:(unfold callee_saved; lia)), <- Hn. exact G118. }
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 res) by exact G210.
  assert (GK2 : forall x, (x = 3 \/ x = 4 \/ x = 8 \/ 19 <= x <= 27) ->
            YK11.getr regs2 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
  { intros x Hx. rewrite (Y2 x ltac:(unfold callee_saved; lia)). exact (GK1 x Hx). }
  assert (SVr2 : rw_cells rsegs mem2 (spZ regs - 32)
    [C8 (YK11.getr regs 18); C8 (YK11.getr regs 9); C8 (YK11.getr regs 8); C8 (YK11.getr regs 1)]).
  { apply (lf_rw_cells_frame m1); [exact SVr1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    rewrite <- SEGS. apply Habove2. rewrite Hsp1. lia. }
  (* the memory lt_b reads, in the normalised memory *)
  assert (STn : Frame.stk rsegs (normalize rsegs mem2) (spZ regs - stk) (spZ regs)).
  { apply (norm_stk B SEGS); [exact Hro2 | unfold LF_RES_TOP; lia | lia | exact Hstw2]. }
  destruct (stk_split rsegs _ (spZ regs - stk) (spZ regs - 176) (spZ regs) STn ltac:(lia)) as [STlo SThi].
  destruct (stk_split rsegs _ (spZ regs - 176) (spZ regs - 32) (spZ regs) SThi ltac:(lia)) as [STfr _].
  destruct (stk_carve rsegs _ (spZ regs - 176) (spZ regs - 32) 64 STfr ltac:(lia)) as [STw [jf RFn]].
  destruct (stk_carve rsegs _ (spZ regs - 176) (spZ regs - 32 - Z.of_nat 64) 80 STw ltac:(lia)) as [_ [jw RWn]].
  replace (spZ regs - 32 - Z.of_nat 64) with (spZ regs - 176 + 80) in RFn by lia.
  replace (spZ regs - 32 - Z.of_nat 64 - Z.of_nat 80) with (spZ regs - 176) in RWn by lia.
  assert (SVn : rw_cells rsegs (normalize rsegs mem2) (spZ regs - 176 + 144)
    [C8 (YK11.getr regs 18); C8 (YK11.getr regs 9); C8 (YK11.getr regs 8); C8 (YK11.getr regs 1)]).
  { replace (spZ regs - 176 + 144) with (spZ regs - 32) by lia.
    apply (lf_rw_cells_norm B); [exact SEGS | exact Hro2 | | exact SVr2].
    intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). unfold LF_RES_TOP in *. lia. }
  assert (BLn : exists jb, rw_cells rsegs (normalize rsegs mem2) res [CB (length pl) jb]).
  { destruct (Nat.eq_dec (length pl) 0) as [L0n|L0n].
    - exists []. rewrite L0n. apply lt_rw_cells_nil. lia.
    - assert (En' : n' = n) by (unfold n'; destruct (Z.eqb_spec n 0); lia).
      rewrite En' in Hres_in.
      destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 res n HM2 Hres_in ltac:(lia) Hro2) as [jb HJ].
      exists jb. rewrite Hn, Nat2Z.id in HJ. exact HJ. }
  destruct BLn as [jb BLn].
  assert (PLn : (0 < length pl)%nat -> bytes_at rsegs (normalize rsegs mem2) p pl).
  { intros H0. destruct Hpl0 as [[Hn0 _] | [_ (q & Hq & Hqp)]]; [lia|].
    assert (Hin0 : In (p, n) (blocks L A)) by (apply blocks_In; exists q; split; [exact Hqp | exact Hq]).
    pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    assert (BD : blk_data B mem2 p pl)
      by (eapply (blk_keep B API); [exact FR2 | rewrite <- Hn; exact Hin0 | exact Hpl]).
    apply bytes_at_normalize; [exact Hro2|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  assert (DJn : (0 < length pl)%nat -> p + Z.of_nat (length pl) <= res \/ res + Z.of_nat (length pl) <= p).
  { intros H0. destruct Hpl0 as [[Hn0 _] | [_ (q & Hq & Hqp)]]; [lia|].
    assert (Hin0 : In (p, n) (blocks L A)) by (apply blocks_In; exists q; split; [exact Hqp | exact Hq]).
    pose proof (MINE p n Hin0). lia. }
  eapply (g_run_cf B API SEGS AX HGG) with (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (L := L1) (A := A1).
  { exact FR2. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of.
    eapply (lt_b MC MSET PARSE CPR CPF) with (lo := spZ regs - stk) (buf := res) (p := p) (pl := pl).
    all: try (rewrite E22, MState.unsigned_lit by lia).
    all: first [ exact STlo | exact RWn | exact RFn | exact SVn | exact BLn | exact PLn | exact DJn
               | exact E210 | exact E29 | exact E218 | apply mem_inv_normalize | lia ]. }
  { intros ms [(C0 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & u15 & m'
               & -> & MU & WM & _) | (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14
               & u15 & m' & -> & MU & WM & _)];
      do 5 eexists; eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]);
      intros x Hx NO; apply lt_out2 in NO; rewrite E22, MState.unsigned_lit in NO by lia;
      (destruct NO as [NO|NO]; [left; lia | right; exists res, n'; split; [|lia]]);
      (split; [exact Hres_in|]); (split; [lia|]); exact MINE. }
  intros R F pc' fc m0' HQ regs3 m3 Hx3 Hrel3 FR3.
  pose proof FR3 as (HM3 & HW3 & HB3 & HID3 & _ & _ & _ & _ & _ & Hstw3 & Herr3 & _ & Hro3).
  destruct HQ as [(C0 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & u15 & m''3
                  & HE & MU3 & WM3 & MI3 & BA3 & PF3 & PW3 & SV3)
                 | (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & u15 & m''3
                  & HE & MU3 & WM3 & MI3 & SV3)];
    injection HE as ER EF EP EC EM; subst R F pc' fc m0'.
  2:{ (* a frame that does not read as SPEC_OK: free *)
    rewrite <- SEGS. change (Z_to_bv 64 0x14dec) with (Z_to_bv 64 LLVM_FREE).
    apply (lt_exit_cf stk empty L A regs mem md ra p n b j (mkFP (@fp_regs fx) (@fp_csr fx)) regs3 m3 md2 L1 A1 res n');
      try assumption.
    all: try lia.
    all: try (intros a k Hak; exact (MINE a k Hak)).
    - rewrite (lf_getr_eqv _ _ _ Hx3). reflexivity.
    - rewrite (lf_getr_eqv _ _ _ Hx3). exact E22.
    - rewrite (lf_getr_eqv _ _ _ Hx3). reflexivity.
    - intros x Hx. rewrite (lf_getr_eqv _ _ _ Hx3), <- (GK2 x ltac:(lia)), lt_getr_cs by (unfold callee_saved; lia).
      assert (C : x = 3 \/ x = 4 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/
                  x = 26 \/ x = 27) by lia.
      repeat (destruct C as [-> | C]; [reflexivity|]). subst. reflexivity.
    - pose proof (lf_rw_cells_rel m3 m''3 _ _ Hrel3 SV3) as H.
      rewrite E22, MState.unsigned_lit in H by lia. replace (spZ regs - 176 + 144) with (spZ regs - 32) in H by lia.
      exact H. }
  (* SPEC_OK: check_round_trip *)
  assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 0x12fc8) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact E22).
  assert (G310 : YK11.getr regs3 10 = Z_to_bv 64 (spZ regs - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact E22).
  assert (G38 : YK11.getr regs3 8 = Z_to_bv 64 res) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (GK3 : forall x, (x = 3 \/ x = 4 \/ 19 <= x <= 27) ->
            YK11.getr regs3 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
  { intros x Hx. rewrite (lf_getr_eqv _ _ _ Hx3), <- (GK2 x ltac:(lia)), lt_getr_cs by (unfold callee_saved; lia).
    assert (C : x = 3 \/ x = 4 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/
                x = 26 \/ x = 27) by lia.
    repeat (destruct C as [-> | C]; [reflexivity|]). subst. reflexivity. }
  assert (Hsp3 : spZ regs3 = spZ regs - 176) by (unfold spZ at 1; rewrite G32; apply MState.unsigned_lit; lia).
  rewrite E22, MState.unsigned_lit in PF3, PW3, SV3 by lia.
  pose proof (proj2 (bytes_at_rel rsegs m3 m''3 res pl Hrel3) BA3) as BAr.
  pose proof (lt_ro_cells_rel m3 m''3 _ _ Hrel3 PF3) as PFr.
  pose proof (lt_ro_cells_rel m3 m''3 _ _ Hrel3 PW3) as PWr.
  pose proof (lf_rw_cells_rel m3 m''3 _ _ Hrel3 SV3) as SVr.
  pose proof (bytes_at_bound _ _ _ _ BAr) as BAb.
  assert (En' : n' = n) by (unfold n'; destruct (Z.eqb_spec n 0); [|lia]; subst n;
    destruct (fr_code_ok pl C0) as (L30 & _); lia).
  assert (Hra3 : YK0s.ret_ok (YK11.getr regs3 1)) by (rewrite G31; apply ret_ok_even; reflexivity).
  assert (Hal3 : spZ regs3 mod 16 = 0).
  { rewrite Hsp3. replace (spZ regs - 176) with (spZ regs + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact Hal. }
  assert (Htp3 : YK11.getr regs3 4 = Z_to_bv 64 (ms_tp B)) by exact (eq_trans (GK3 4 ltac:(lia)) Htp).
  assert (IB3 : in_block L1 A1 res (Z.of_nat (length pl))) by (exists res, n'; split; [exact Hres_in | lia]).
  assert (BD3 : blk_data B m3 res pl) by (apply (bytes_at_blk B); [exact SEGS | exact BAr]).
  assert (W8 : (spZ regs - 176) mod 8 = 0).
  { clear - Hal. Z.div_mod_to_equations. lia. }
  assert (WD3 : blk_data B m3 (spZ regs - 176) (spec_bytes res pl)).
  { apply (bytes_at_blk B); [exact SEGS|]. unfold spec_bytes. exact (proj2 PWr). }
  assert (ROOM3 : (sb_live (sb_malloc b n') + 3 <= sb_cap (sb_malloc b n') <= CAP_AG /\
                   128 <= sb_cap (sb_malloc b n')) /\
                  0 <= sb_bytes (sb_malloc b n') /\ sb_bytes (sb_malloc b n') + 3 * crt_len pl <= 2 ^ 29).
  { destruct Hroom as (Hl1 & Hl2 & Hl3). unfold sb_malloc, crt_len, frame_len. cbn [sb_live sb_bytes sb_cap].
    rewrite (length_fr_body pl C0). destruct (fr_body_len_ok pl C0) as (Hb1 & Hb2 & Hb3).
    repeat split; lia. }
  assert (BUF3 : 0 < res < 2 ^ 64) by lia.
  assert (LEN3 : Z.of_nat (length pl) < 2 ^ 26) by lia.
  rewrite <- SEGS. change (Z_to_bv 64 0x131e4) with (Z_to_bv 64 CHECK_ROUND_TRIP).
  eapply (g_crt_cf B API) with (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (L := L1) (A := A1) (w := spZ regs - 176) (buf := res) (b := pl) (bres := sb_malloc b n').
  all: try eassumption.
  all: try (rewrite ?Hsp3; unfold U_CRT_STACK, U_CRT_FRAME, ALLOC_STACK; lia).
  intros fx4 L4 A4 regs4 mem4 md4 Hfrm4 FR4 Hrp4 Eb4 Hres4 Habove4 Hkept4.
  rewrite G31, SEGS.
  pose proof FR4 as (HM4 & HW4 & HB4 & HID4 & _ & _ & _ & _ & _ & Hstw4 & Herr4 & _ & Hro4).
  assert (E42 : reg_get regs4 2 = Z_to_bv 64 (spZ regs - 176)).
  { change (YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 176)).
    rewrite (Hrp4 2 ltac:(unfold callee_saved; lia)). exact G32. }
  assert (E48 : reg_get regs4 8 = Z_to_bv 64 res).
  { change (YK11.getr regs4 (Z_to_bv 5 8) = Z_to_bv 64 res). rewrite (Hrp4 8 ltac:(unfold callee_saved; lia)).
    exact G38. }
  assert (GK4 : forall x, (x = 3 \/ x = 4 \/ 19 <= x <= 27) ->
            YK11.getr regs4 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
  { intros x Hx. rewrite (Hrp4 x ltac:(unfold callee_saved; lia)). exact (GK3 x Hx). }
  assert (UP4 : forall a, spZ regs - 176 <= a < spZ regs -> mbyte rsegs mem4 a = mbyte rsegs m3 a).
  { intros a Ha. rewrite <- SEGS. apply Habove4. rewrite Hsp3. lia. }
  assert (BA4 : bytes_at rsegs mem4 res pl).
  { apply (bytes_at_frame m3 mem4 res pl BAr). intros a Ha. rewrite <- SEGS.
    replace a with (res + (a - res)) by lia. apply (Hkept4 res n' (a - res) Hres_in); [intros F; exact F | lia]. }
  assert (PF4 : ro_cells rsegs mem4 (spZ regs - 176 + 80) (parse_cells res pl (repeat (b8 0) 64))).
  { apply (lt_ro_cells_frame m3); [exact PFr|]. intros a Ha. cbn [cells_size csize parse_cells Nat.add] in Ha.
    apply UP4. lia. }
  assert (PW4 : ro_cells rsegs mem4 (spZ regs - 176) (spec_cells res pl)).
  { apply (lt_ro_cells_frame m3); [exact PWr|]. intros a Ha. cbn [cells_size csize spec_cells Nat.add] in Ha.
    apply UP4. lia. }
  assert (SV4 : rw_cells rsegs mem4 (spZ regs - 176 + 144)
    [C8 (YK11.getr regs 18); C8 (YK11.getr regs 9); C8 (YK11.getr regs 8); C8 (YK11.getr regs 1)]).
  { apply (lf_rw_cells_frame m3); [exact SVr|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    rewrite <- SEGS. apply Habove4. rewrite Hsp3. lia. }
  assert (ST4 : Frame.stk rsegs (normalize rsegs mem4) (spZ regs - stk) (spZ regs - 176)).
  { apply (norm_stk B SEGS); [exact Hro4 | unfold LF_RES_TOP; lia | lia |].
    intros a Ha. apply Hstw4. lia. }
  assert (NI : forall a, LF_RES_TOP <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (lf_in_img_top B a SEGS Hi) as H; lia).
  eapply (g_run_cf B API SEGS AX HGG) with (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (L := L4) (A := A4).
  { exact FR4. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of.
    eapply (lt_c CA) with (lo := spZ regs - stk) (buf := res) (b := pl).
    all: try (rewrite E42, MState.unsigned_lit by lia).
    { exact ST4. } { unfold U_CA_STACK; lia. } { lia. } { lia. } { apply mem_inv_normalize. } { exact E48. }
    { exact C0. } { lia. } { lia. }
    { apply bytes_at_normalize; [exact Hro4 | exact BA4]. }
    { apply lt_ro_cells_norm; [exact Hro4 | exact PF4]. }
    { apply lt_ro_cells_norm; [exact Hro4 | exact PW4]. }
    { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro4 | | exact SV4].
      intros i Hi. apply NI. unfold LF_RES_TOP. lia. } }
  { intros ms (u0' & u1' & u2' & u3' & u4' & u5' & u6' & u7' & u8' & u9' & u10' & u11' & u12' & u13' & m' & -> & MU & WM
      & _).
    do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply lt_out1 in NO. rewrite E42, MState.unsigned_lit in NO by lia.
    unfold U_CA_STACK in NO. lia. }
  intros R F pc' fc m0' HQ regs5 m5 Hx5 Hrel5 FR5.
  destruct HQ as (u0' & u1' & u2' & u3' & u4' & u5' & u6' & u7' & u8' & u9' & u10' & u11' & u12' & u13' & m''5
    & HE & MU5 & WM5 & MI5 & SV5).
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  rewrite <- SEGS. change (Z_to_bv 64 0x14dec) with (Z_to_bv 64 LLVM_FREE).
  apply (lt_exit_cf stk empty L A regs mem md ra p n b j (mkFP (@fp_regs fx4) (@fp_csr fx4)) regs5 m5 md4 L4 A4 res n');
    try assumption.
  all: try lia.
  all: try (rewrite Eb4; exact Hres_in).
  all: try (intros a k Hak; exact (MINE a k Hak)).
  - rewrite (lf_getr_eqv _ _ _ Hx5). reflexivity.
  - rewrite (lf_getr_eqv _ _ _ Hx5). exact E42.
  - rewrite (lf_getr_eqv _ _ _ Hx5). exact E48.
  - intros x Hx. rewrite (lf_getr_eqv _ _ _ Hx5), <- (GK4 x Hx), lt_getr_cs by (unfold callee_saved; lia).
    assert (C : x = 3 \/ x = 4 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/
                x = 26 \/ x = 27) by lia.
    repeat (destruct C as [-> | C]; [reflexivity|]). subst. reflexivity.
  - pose proof (lf_rw_cells_rel m5 m''5 _ _ Hrel5 SV5) as H.
    rewrite E42, MState.unsigned_lit in H by lia. replace (spZ regs - 176 + 144) with (spZ regs - 32) in H by lia.
    exact H.
Qed.

End M.
