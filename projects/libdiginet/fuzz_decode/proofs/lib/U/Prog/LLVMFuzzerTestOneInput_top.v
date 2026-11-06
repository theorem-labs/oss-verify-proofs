(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the last part of the UBSan harness walk of LLVMFuzzerTestOneInput
   (fuzz_decode.ubsan, entry 0x12cfc, frame 0x1f0) and the harness SR contract from the parts.
   - llvm_exit_evt: the exit segment 0x13384-0x13394, `mv a0, s2; mv a1, s1; jal check_refusal` (0x1338c, ra
     0x13390), `ld a0, 8(sp)` (0x13390), `jal free` (0x13394, ra 0x13398): from the cut at 0x13384 to the entry of
     free(buf) (mid_free).
   - llvm_sr_of_parts: LLVMFuzzerTestOneInput_sr_contract from the early path (size 0 or size >= 2^26), the front
     (0x12cfc to 0x12df8), the two loops (0x12df8 to 0x13384), llvm_exit_evt, free (0x14ee8) and the epilogue
     0x13398-0x133d4 (`mv a0, zero`, the thirteen `ld` of ra and s0..s11 from sp + 0x188 .. sp + 0x1e8,
     `addi sp, sp, 0x1f0`, `ret`). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import check_refusal_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_glue LLVMFuzzerTestOneInput_mid.
Import ListNotations.
Open Scope Z_scope.

Lemma llvm_exit_evt : check_refusal_contract ->
  forall F fc gp tp sv Sp lo buf nn body bb m0 ms,
    mid_env sv Sp lo buf nn body bb ->
    mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_DECODER_OUT ms ->
    evt rsegs (mid_free F fc gp tp sv Sp lo buf body bb m0) ms.
Proof.
  intros CR F fc gp tp sv Sp lo buf nn body bb m0 ms
    (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9)
    (x1 & x5 & x6 & x7 & x8 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x22 & x23 & x24
      & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & j0 & j1 & -> & (MI & ST & HSV & HBUF & HBB & MU & WM)
      & HJ0 & HJ1).
  unfold mid_len in *. unfold ALLOC_STACK, LLVM_FRAME in *.
  assert (U : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  unfold LLVM_PC_DECODER_OUT.
  step. step. step.                                   (* mv a0, s2; mv a1, s1; jal check_refusal *)
  eapply evt_cut.
  { eapply (CR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m body lo bb).
    all: unfold CHECK_REFUSAL_STACK; rewrite ?U; try lia; try exact ST; try exact HBB; try exact MI. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & MUc & WMc & MI' & ST').
  replace (ret_pc (Z_to_bv 64 78736)) with (Z_to_bv 64 78736) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold CHECK_REFUSAL_STACK in MUc. rewrite U in MUc, ST'.
  pose proof (rw_cells_transport rsegs _ m m' _ _ HSV MUc WMc
    ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as HSV'.
  pose proof (rw_cells_transport rsegs _ m m' _ _ HBUF MUc WMc
    ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as HBUF'.
  pose proof (rw_cells_transport rsegs _ m m' _ _ HJ0 MUc WMc
    ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as HJ0'.
  pose proof (rw_cells_transport rsegs _ m m' _ _ HJ1 MUc WMc
    ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as HJ1'.
  pose proof (bytes_at_transport rsegs _ m m' _ _ HBB MUc
    ltac:(cbn [disjoint_from]; split; [left; lia | exact I])) as HBB'.
  pose proof (munch_trans _ m0 m m' MU (munch_weaken [(Sp - 160, Sp)] [(lo, Sp + 496)] m m'
    ltac:(unfold sub_fp; cbn [outside]; intros x (Hx & _); split; [lia | exact I]) MUc)) as MU'.
  pose proof (wmono_trans rsegs m0 m m' WM WMc) as WM'.
  clear HSV HBUF HJ0 HJ1 HBB MU WM MUc WMc ST MI.
  step.                                               (* ld a0, 8(sp) *)
  step.                                               (* jal free *)
  apply evt_done. unfold mid_free.
  do 26 eexists. exists m', j0, j1.
  split; [reflexivity|].
  split; [|split; [exact HJ0' | exact HJ1']].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact HSV'|]. split; [exact HBUF'|].
  split; [exact HBB'|]. split; [exact MU' | exact WM'].
Qed.

(* the registers of the entry of free that the SR part reads *)
Lemma mid_free_shape : forall F fc gp tp sv Sp lo buf body bb m0 ms,
  mid_free F fc gp tp sv Sp lo buf body bb m0 ms ->
  exists R m, ms = MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\
    mid_inv sv Sp lo buf body bb m0 m /\
    reg_get R 1 = Z_to_bv 64 LLVM_FREE_RA /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\
    reg_get R 4 = tp /\ reg_get R 10 = Z_to_bv 64 buf.
Proof.
  intros F fc gp tp sv Sp lo buf body bb m0 ms
    (x5 & x6 & x7 & x8 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24
      & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & j0 & j1 & -> & HI & _ & _).
  eexists _, m. split; [reflexivity|]. split; [exact HI|].
  repeat split; reflexivity.
Qed.

Lemma top_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma top_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

Lemma top_getr_cs : forall R x, callee_saved x -> YK11.getr R (Z_to_bv 5 x) = reg_get R (Z_to_bv 5 x).
Proof.
  intros R x Hx.
  destruct (top_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis BND : blocks_nodup B API.

Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

(* from the entry of free (0x14ee8, ra = 0x13398, a0 = buf) to the return: free(buf), then the epilogue
   0x13398-0x133d4; the released fd_exit.v's fx_exit_holds at this image's frame *)
Lemma llvm_exit_sr : forall stk empty L0 A0 regs0 mem0 md0 ra p n b j (fx' : YK11.FPState) regs mem md L A
    buf nn,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> sink_none B mem0 md0 ->
  frm_zero (@fp_csr fx') ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  lf_mine L0 A0 L A buf nn -> res_ok_slots A (sb_malloc b nn) ->
  YK11.getr regs 1 = Z_to_bv 64 LLVM_FREE_RA ->
  YK11.getr regs 2 = Z_to_bv 64 (spZ regs0 - LLVM_FRAME) -> YK11.getr regs 3 = YK11.getr regs0 3 ->
  YK11.getr regs 4 = YK11.getr regs0 4 -> YK11.getr regs 10 = Z_to_bv 64 buf ->
  rw_cells rsegs mem (spZ regs0 - LLVM_FRAME + 0x188) (llvm_saved_cells regs0) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_FREE) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b j fx' regs mem md L A buf nn
    BI Hstk Hra Hpre Hsn Hfrm FR (Hin & Hnn & Hd) RES G1 Hsp Hgp Htp G10 HF.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0
    & Hpl0 & Hrod0).
  unfold LLVM_K, LLVM_FRAME, ALLOC_STACK in *.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  remember (spZ regs0) as S eqn:ES.
  assert (Hspv : bv_unsigned (YK11.getr regs 2) = S - 496) by (rewrite Hsp; apply unsigned_lit; lia).
  assert (Hsp' : spZ regs = S - 496) by exact Hspv.
  assert (Hra1 : YK0s.ret_ok (YK11.getr regs 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs mod 16 = 0).
  { rewrite Hsp'. replace (S - 496) with (S + (-31) * 16) by lia. rewrite Z.mod_add by lia. exact Hal0. }
  assert (Hlo1 : S - stk <= spZ regs - ALLOC_STACK) by (rewrite Hsp'; unfold ALLOC_STACK; lia).
  assert (Hhi1 : spZ regs <= S) by lia.
  assert (H631 : spZ regs < 2 ^ 63) by lia.
  assert (HS64 : S <= 2 ^ 64) by lia.
  assert (Htp1 : YK11.getr regs 4 = Z_to_bv 64 (ms_tp B)) by (rewrite Htp; exact Htp0).
  eapply g_free with (stk := stk) (S := S) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (x := buf) (n := nn)
    (bres := sb_malloc b nn).
  all: try eassumption.
  intros L2 A2 regs2 mem2 md2 FR2 Hrp (b1 & b2 & Eb1 & Eb2) Hres2 Habove Hkept.
  pose proof FR2 as (HM2 & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (H2h & H2l & _).
  assert (Hcs2 : forall x, callee_saved x -> YK11.getr regs2 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x))
    by exact Hrp.
  assert (E2 : reg_get regs2 2 = Z_to_bv 64 (S - 496)).
  { change (YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 496)).
    rewrite (Hcs2 2 ltac:(unfold callee_saved; lia)). exact Hsp. }
  assert (E3 : reg_get regs2 3 = YK11.getr regs0 3).
  { change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs0 3).
    rewrite (Hcs2 3 ltac:(unfold callee_saved; lia)). exact Hgp. }
  assert (E4 : reg_get regs2 4 = YK11.getr regs0 4).
  { change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs0 4).
    rewrite (Hcs2 4 ltac:(unfold callee_saved; lia)). exact Htp. }
  assert (HF2 : rw_cells rsegs mem2 (S - 496 + 392) (llvm_saved_cells regs0)).
  { apply (lf_rw_cells_frame mem); [exact HF|]. intros a Ha. rewrite llvm_saved_cells_size in Ha.
    pose proof (Habove a ltac:(rewrite Hsp'; lia)) as E. rewrite SEGS in E. exact E. }
  clear HF.
  rewrite G1, SEGS. unfold LLVM_FREE_RA.
  apply (llvm_run fx' regs2 (Z_to_bv 64 0x13398) mem2 md2
    (fun ms => exists R2, ms = MS R2 (@fp_regs fx') (ret_pc (YK11.getr regs0 1)) (@fp_csr fx') None mem2
                                  (YK11.seg_rom rsegs) /\
       reg_get R2 10 = Z_to_bv 64 0 /\
       forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)));
    [exact H2h | exact H2l | | |].
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4. unfold llvm_saved_cells in HF2.
    do 16 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx2.
    destruct (top_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      try reflexivity.
    cbn. replace (S - 496 + 496) with S by lia. subst S. unfold spZ. apply Z_to_bv_bv_unsigned. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R2 & HE & H10' & Hcs') regs3 Hx3.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret. subst S.
  assert (G10' : YK11.getr regs3 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact H10').
  assert (RP : regs_preserved regs0 regs3).
  { intros x Hx4. rewrite (lf_getr_eqv _ _ _ Hx3), top_getr_cs by exact Hx4. exact (Hcs' x Hx4). }
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L2 A2 regs3 mem2 md2 Hpre Hsn FR2 G10' RP)
    as (Hpost2 & Hsn' & Hpay & MI2).
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L2, A2, regs3, mem2, md2.
  split; [rewrite Hra0, (lf_ret_pc _ Hra), SEGS; reflexivity|].
  split; [exact Hfrm|]. split; [exact Hpost2|]. split; [exact Hsn'|].
  split; [rewrite sb_free_malloc in Hres2; exact Hres2|].
  split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

Theorem llvm_sr_of_parts :
  (* the early path, size 0 or size >= 2^26: return 0 with no allocation (llvm_early) *)
  (forall j stk empty L A regs mem md ra p n b,
     llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
     lib_pre B API stk empty L A regs mem md ra p n -> sink_none B mem md ->
     res_ok_slots A b -> ro_agree rsegs mem -> frm_zero (@fp_csr fx) ->
     (bv_unsigned (YK11.getr regs 11) = 0 \/ 2 ^ 26 <= bv_unsigned (YK11.getr regs 11)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
       (llvm_sr_post B API stk L A regs mem md ra p n b j)) ->
  (* the front, 0x12cfc to 0x12df8: prologue, fuzz_dup's malloc and memcpy, the frame parse (front_post) *)
  (forall stk empty L0 A0 regs0 mem0 md0 ra p n pl b,
     llvm_binds B API -> LLVM_K <= stk -> lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n ->
     n = Z.of_nat (length pl) -> blk_data B mem0 p pl -> spZ regs0 <= 2 ^ 47 -> res_ok_slots A0 b ->
     llvm_room b -> ro_agree rsegs mem0 -> G_img_c B llvm_RELRO mem0 -> frm_zero (@fp_csr fx) -> 0 < n < 2 ^ 26 ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0)
       (front_post B API stk L0 A0 regs0 mem0 md0 n b)) ->
  (* the two loops, 0x12df8 to 0x13384: the cursor loop and the decoder loop *)
  (forall F fc gp tp sv Sp lo buf nn body bb m0 ms,
     mid_env sv Sp lo buf nn body bb ->
     mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_BODY ms ->
     evt rsegs (mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_DECODER_OUT) ms) ->
  check_refusal_contract ->
  LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros EARLY FRONT LOOPS CR.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  enough (G : SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 LLVM_ENTRY) mem (YK11.seg_rom (ms_segs B))) md)
                (llvm_sr_post B API stk L A regs mem md ra p n b j)) by exact G.
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn11 & Hpl0 & Hrod).
  assert (U11 : bv_unsigned (YK11.getr regs 11) = n) by (rewrite Hn11; apply unsigned_lit; lia).
  destruct (Z_lt_le_dec 0 n) as [Hpos|Hz]; [destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig]|].
  3: { apply (EARLY j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm). left. lia. }
  2: { apply (EARLY j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm). right. lia. }
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  eapply SR_bind;
    [exact (FRONT stk empty L A regs mem md ra p n pl b BI Hk Hpre Hn Hpl Hsp Hres Hroom Hro Hrelro Hfrm
              ltac:(lia))|].
  intros c (fx1 & L1 & A1 & regs1 & mem1 & md1 & buf & body & bb & -> & Hfrm1 & FR1 & RES1 & MINE & G2 & G3 & G4
    & G9 & G18 & HSV & HBUF & (j0 & HJ0) & (j1 & HJ1) & HBB & Hb0 & Hb1 & Hb2 & Hb3).
  remember (spZ regs) as S eqn:ES.
  unfold LLVM_FRAME in *.
  pose proof FR1 as (HM1 & HW1 & HB1 & HID1 & Hmd1 & Hhigh1 & Himg1 & Hblk1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & Hro1).
  assert (NI : forall a, 0x50000 <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (lf_in_img_top B a SEGS Hi) as H; unfold LF_RES_TOP in H; lia).
  assert (ENV : mid_env (llvm_saved_cells regs) (S - 496) (S - stk) buf (llvm_nn n) body bb).
  { unfold mid_env, mid_len.
    split; [lia|]. split; [unfold ALLOC_STACK; lia|].
    split; [replace (S - 496) with (S + (-31) * 16) by lia; rewrite Z.mod_add by lia; exact Hal|].
    split; [unfold LLVM_FRAME; lia|]. split; [lia|]. split; [unfold llvm_nn; lia|].
    split; [lia|]. split; [lia|]. split; [lia | reflexivity]. }
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem1) (S - stk) (S - 496)).
  { apply lf_stk; [unfold LF_RES_TOP; lia | lia |]. intros a Ha.
    assert (Hni : ~ in_img B a) by (apply NI; lia).
    unfold writable_at. rewrite (wview_rel_rw rsegs mem1 (normalize rsegs mem1) _ (mem_rel_normalize rsegs mem1 Hro1)
      (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    pose proof (Hstw1 a ltac:(lia)) as W. rewrite SEGS in W. exact W. }
  pose proof (lf_rw_cells_norm B mem1 _ _ SEGS Hro1
    (fun i Hi => NI (S - 496 + 392 + i) ltac:(destruct Hi as [Hi0 _]; lia)) HSV) as HSVn.
  pose proof (lf_rw_cells_norm B mem1 _ _ SEGS Hro1
    (fun i Hi => NI (S - 496 + 8 + i) ltac:(destruct Hi as [Hi0 _]; lia)) HBUF) as HBUFn.
  pose proof (lf_rw_cells_norm B mem1 _ _ SEGS Hro1
    (fun i Hi => NI (S - 496 + i) ltac:(destruct Hi as [Hi0 _]; lia)) HJ0) as HJ0n.
  pose proof (lf_rw_cells_norm B mem1 _ _ SEGS Hro1
    (fun i Hi => NI (S - 496 + 16 + i) ltac:(destruct Hi as [Hi0 _]; lia)) HJ1) as HJ1n.
  pose proof (bytes_at_normalize rsegs mem1 body bb Hro1 HBB) as HBBn.
  assert (E2 : reg_get regs1 2 = Z_to_bv 64 (S - 496)) by exact G2.
  assert (E3 : reg_get regs1 3 = YK11.getr regs 3) by exact G3.
  assert (E4 : reg_get regs1 4 = YK11.getr regs 4) by exact G4.
  assert (E9 : reg_get regs1 9 = Z_to_bv 64 (Z.of_nat (length bb))) by exact G9.
  assert (E18 : reg_get regs1 18 = Z_to_bv 64 body) by exact G18.
  assert (MID0 : mid_at (@fp_regs fx1) (@fp_csr fx1) (YK11.getr regs 3) (YK11.getr regs 4) (llvm_saved_cells regs)
      (S - 496) (S - stk) buf body bb (normalize rsegs mem1) LLVM_PC_BODY
      (MS (Regs6ss.mkR_of regs1) (@fp_regs fx1) (Z_to_bv 64 LLVM_PC_BODY) (@fp_csr fx1) None
          (normalize rsegs mem1) (seg_rom rsegs))).
  { unfold mid_at. do 26 eexists. exists (normalize rsegs mem1), j0, j1.
    split; [unfold Regs6ss.mkR_of; rewrite E2, E3, E4, E9, E18; reflexivity|].
    split; [|split; [exact HJ0n | exact HJ1n]].
    split; [exact (mem_inv_normalize rsegs mem1)|]. split; [exact ST0|]. split; [exact HSVn|].
    split; [exact HBUFn|]. split; [exact HBBn|].
    split; [apply munch_refl | apply wmono_refl]. }
  clear HSVn HBUFn HJ0n HJ1n HBBn ST0.
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := S) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := mid_free (@fp_regs fx1) (@fp_csr fx1) (YK11.getr regs 3) (YK11.getr regs 4) (llvm_saved_cells regs)
            (S - 496) (S - stk) buf body bb (normalize rsegs mem1)).
  all: try eassumption. all: try lia.
  { eapply evt_cut; [exact (LOOPS _ _ _ _ _ _ _ _ _ _ _ _ _ ENV MID0)|].
    intros ms' H'. exact (llvm_exit_evt CR _ _ _ _ _ _ _ _ _ _ _ _ _ ENV H'). }
  { intros ms HQ. destruct (mid_free_shape _ _ _ _ _ _ _ _ _ _ _ _ HQ)
      as (R & m' & -> & (_ & _ & _ & _ & _ & MU & WM) & _).
    exists R, (@fp_regs fx1), (Z_to_bv 64 LLVM_FREE), (@fp_csr fx1), m', [(S - stk, S - 496 + LLVM_FRAME)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply top_out1 in NO. unfold LLVM_FRAME in NO. lia. }
  intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
  destruct (mid_free_shape _ _ _ _ _ _ _ _ _ _ _ _ HQ)
    as (R2 & m2 & HE & (_ & _ & HSV2 & _ & _ & _ & _) & R1 & R2' & R3 & R4 & R10).
  injection HE as ER EF EP EC EM. subst R2 F pc' fc m2.
  pose proof (lf_rw_cells_rel m' m0' _ _ Hrel HSV2) as HSV3.
  rewrite <- SEGS. subst S.
  apply (llvm_exit_sr stk empty L A regs mem md ra p n b j (mkFP (@fp_regs fx1) (@fp_csr fx1)) regs' m' md1 L1 A1
    buf (llvm_nn n) BI Hk Hra Hpre Hsn Hfrm1 FR' MINE RES1).
  - rewrite (lf_getr_eqv _ _ _ Hx). exact R1.
  - rewrite (lf_getr_eqv _ _ _ Hx). unfold LLVM_FRAME. exact R2'.
  - rewrite (lf_getr_eqv _ _ _ Hx). exact R3.
  - rewrite (lf_getr_eqv _ _ _ Hx). exact R4.
  - rewrite (lf_getr_eqv _ _ _ Hx). exact R10.
  - unfold LLVM_FRAME. exact HSV3.
Qed.

End T.
