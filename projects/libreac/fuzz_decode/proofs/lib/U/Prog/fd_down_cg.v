From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0 MemNorm.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_decode_c reac_decode check_braid_c check_round_trip_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  fd_segments_c fd_glue fd_seghelp fd_up_evt fd_down_q fd_down_a fd_down_b
  reac_frame_counter_c memset_c reac_decode_plain_le_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import fd_down LLVMFuzzerTestOneInput_cfb fd_segments_ccf check_round_trip_ccf fd_glue_cg.
Import ListNotations.
Open Scope Z_scope.

Section D.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract_cf fx' rc B API.
Context (IHI : reac_frame_inspect_contract) (IHC : reac_frame_counter_contract) (IMS : memset_contract)
  (IDE : reac_decode_contract) (ICB : check_braid_contract) (IPL : reac_decode_plain_le_contract)
  (BC : bcmp_contract).

Theorem fd_down_holds_cf : fd_down_contract_cf B API.
Proof.
  intros ((SEGS & HMAL & HFRE & HGG & HG & AX) & ERRL) L A regs mem md b S len frame mode nch ns fr INV Hfrm
    H9 H25 H19 MODE.
  pose proof INV as (HM & HW & HB & Hal & Hceil & H63 & Hstw & Hfw & Htp & Herr & HID & Hro & Hh & Hl & Hsp
    & Hlen & HLEN & Hin & Hblk & Hres & Hroom).
  pose proof MODE as (Hmode & Hnch & Hns & HM4 & HM8).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold FD_FRAME, FD_WIN in *.
  rewrite Hsp in Hal, Hceil, H63, Hstw.
  unfold CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hceil, Hstw.
  assert (Hro' : ro_agree rsegs mem) by (rewrite <- SEGS; exact Hro).
  pose proof Hin as Hin'. apply blocks_In in Hin' as (qf & Hqf & Hqfin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md qf len HM Hqfin) as (Hf1 & Hf2). rewrite Hqf in Hf1, Hf2.
  pose proof (olen_bounds nch ns Hnch Hns) as OLB.
  assert (MAL : mode <> 0 /\ mode mod 4 = 0).
  { assert (H16 : (S - 176) mod 16 = 0) by exact Hal.
    assert (HS0 : 176 + 116 <= S) by (clear - Hceil Hac; lia).
    destruct Hmode as [E|[E|[E|E]]]; rewrite E; unfold MODE_44K1, MODE_48K, MODE_96K, FD_KEEP;
      [split; [lia | reflexivity] | split; [lia | reflexivity] | split; [lia | reflexivity] |].
    split; [lia|]. clear - H16. Z.div_mod_to_equations. lia. }
  assert (G2 : YK11.getr regs 2 = Z_to_bv 64 (S - 176)).
  { unfold spZ in Hsp. rewrite <- Hsp. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (WIN : forall a, S - LLVM_K <= a < S - FD_KEEP -> writable_at (ms_segs B) mem a).
  { intros a Ha. kunf. destruct (Z_lt_le_dec a (S - 176)); [apply Hstw | apply Hfw]; lia. }
  assert (FR0 : lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md L A mem md).
  { apply lf_fr_refl; try assumption. intros a Ha. apply WIN. lia. }
  assert (FRB : forall LX AXX memX mdX, lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     bytes_at rsegs (normalize rsegs memX) frame fr).
  { intros LX AXX memX mdX FRX. pose proof FRX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HroX).
    apply bytes_at_normalize; [exact HroX|]. apply (blk_bytes_at B); [exact SEGS | lia | lia |].
    eapply blk_keep; [exact FRX | rewrite HLEN; exact Hin | exact Hblk]. }
  assert (STKX : forall LX AXX memX mdX, lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     Frame.stk rsegs (normalize rsegs memX) (S - 176 - 4096) (S - 176)).
  { intros LX AXX memX mdX FRX. pose proof FRX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HwX & _ & _ & HroX).
    eapply norm_stk; try eassumption; try (kunf; lia). intros a Ha. apply HwX. kunf. lia. }
  assert (MODEX : forall LX AXX memX mdX, lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     bytes_at rsegs (normalize rsegs memX) (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { intros LX AXX memX mdX FRX. eapply mode_keep; try eassumption; kunf; lia. }
  assert (STK0 : Frame.stk rsegs (normalize rsegs mem) (S - LLVM_K) (S - 176 + 56)).
  { eapply norm_stk; try eassumption; try (kunf; lia). intros a Ha. apply WIN. kunf. lia. }
  destruct (stk_carve rsegs _ _ _ 16 STK0 ltac:(kunf; lia)) as [STK1 [junk HS40]].
  change (Z.of_nat 16) with 16 in STK1, HS40. replace (S - 176 + 56 - 16) with (S - 176 + 40) in STK1, HS40 by lia.
  destruct (stk_carve rsegs _ _ _ 32 STK1 ltac:(kunf; lia)) as [STK2 [junk8 HS8]].
  change (Z.of_nat 32) with 32 in STK2, HS8. replace (S - 176 + 40 - 32) with (S - 176 + 8) in STK2, HS8 by lia.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  pose proof (MODEX L A mem md FR0) as HM0. pose proof (FRB L A mem md FR0) as HFR0.
  pose proof (STKX L A mem md FR0) as ST0.
  assert (DMS : mode + 12 <= S - 176 - 4096 \/ S - 176 + 56 <= mode + 4) by (kunf; lia).
  assert (DMS8 : mode + 12 <= S - 176 + 8 \/ S - 176 + 56 <= mode + 4) by (kunf; lia).
  assert (HCELL : forall m0 m1 m2 A0 cs, mem_rel rsegs m1 m0 -> rw_cells rsegs m0 A0 cs ->
     (forall a, A0 <= a < A0 + Z.of_nat (cells_size cs) ->
        mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)) ->
     ro_agree rsegs m2 -> LF_RES_TOP <= A0 -> rw_cells rsegs (normalize rsegs m2) A0 cs).
  { intros m0 m1 m2 A0 cs HR C E Hr2 HA. apply (lf_rw_cells_norm B); [exact SEGS | exact Hr2 | |].
    - intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). unfold LF_RES_TOP in *. lia.
    - apply (lf_rw_cells_frame m1); [exact (lf_rw_cells_rel m1 m0 _ _ HR C) | exact E]. }
  rewrite SEGS.
  eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := q_dmalloc (@fp_regs fx) (@fp_csr fx) (reg_get regs 3) (reg_get regs 4) (normalize rsegs mem) (S - 176)
            mode nch ns len frame (S - 176 - 4096) fr junk8).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of, FD_DOWN.
    eapply (ud_st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S - 176) mode nch ns len frame
      (S - 176 - 4096) fr junk junk8).
    all: gs. }
  { intros ms (R & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists R, (@fp_regs fx), (Z_to_bv 64 0x14df4), (@fp_csr fx), m', [(S - 176 + 40, S - 176 + 56)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x0 Hx0 NO. left. apply outside1d in NO. kunf. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & HE & R1 & R2 & R3 & R4 & R9 & R10 & R18 & R19 & R23 & R25 & MU1 & WM1 & MI1
    & HS1 & HS81 & HM1 & HFR1 & ST1).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12f74) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R1).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (S - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R2).
  assert (G13 : YK11.getr regs1 3 = YK11.getr regs 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R3).
  assert (G14 : YK11.getr regs1 4 = YK11.getr regs 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R4).
  assert (G19 : YK11.getr regs1 9 = Z_to_bv 64 len) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R9).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (fd_olen nch ns)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R10).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 (fd_fits nch ns)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R18).
  assert (G119 : YK11.getr regs1 19 = Z_to_bv 64 mode) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R19).
  assert (G123 : YK11.getr regs1 23 = Z_to_bv 64 (fd_olen nch ns)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R23).
  assert (G125 : YK11.getr regs1 25 = Z_to_bv 64 frame) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R25).
  assert (Hsp1 : spZ regs1 = S - 176) by (unfold spZ; rewrite G12; apply MState.unsigned_lit; lia).
  assert (Hra1 : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0) by (rewrite Hsp1; exact Hal).
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (rewrite G14; exact Htp).
  assert (ROOM1 : room_ag b (fd_olen nch ns)).
  { destruct Hres as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _). destruct Hroom as (Hl1 & Hl2 & Hl3).
    apply lf_room_ag; lia. }
  rewrite <- SEGS. change (Z_to_bv 64 0x14df4) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (n := fd_olen nch ns) (bres := b).
  all: try eassumption. all: try (rewrite ?Hsp1; kunf; lia).
  intros L2 A2 regs2 mem2 md2 out FR2 Hrp2 G210 Hout1 Hout2 Hout16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G1.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & HwX2 & _ & _ & Hro2).
  assert (Hin2 : In (frame, len) (blocks L2 A2)).
  { rewrite Eb1. rewrite Eb2 in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
  assert (Hout_in : In (out, fd_olen nch ns) (blocks L2 A2)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW2 : pairwise ranges_disjoint (b1 ++ (out, fd_olen nch ns) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2). }
  assert (DOF : out + fd_olen nch ns <= frame \/ frame + len <= out).
  { pose proof (disj_mid b1 (out, fd_olen nch ns) b2 (frame, len) PW2 ltac:(rewrite <- Eb2; exact Hin)) as H.
    cbn [fst snd] in H. exact H. }
  assert (MINE : forall a k, In (a, k) (blocks L A) -> a + k <= out \/ out + fd_olen nch ns <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (disj_mid b1 (out, fd_olen nch ns) b2 (a, k) PW2 Hak) as H.
    cbn [fst snd] in H. lia. }
  assert (DOM : out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out).
  { destruct Hmode as [E|[E|[E|E]]]; [| | | left; kunf; lia].
    all: destruct (Z_le_gt_dec (out + fd_olen nch ns) (mode + 4)) as [D1|D1]; [left; exact D1|];
      destruct (Z_le_gt_dec (mode + 12) out) as [D2|D2]; [right; exact D2|]; exfalso;
      apply (Hnimg (Z.max out (mode + 4) - out)); [lia|];
      replace (out + (Z.max out (mode + 4) - out)) with (Z.max out (mode + 4)) by lia;
      apply (mode_img B SEGS); unfold MODE_44K1, MODE_48K, MODE_96K in E; lia. }
  assert (FREEK : forall (fx' : YK11.FPState) regsX memX mdX LX AXX,
     frm_zero (@fp_csr fx') ->
     lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     blocks LX AXX = blocks L2 A2 -> res_ok_slots AXX (sb_malloc b (fd_olen nch ns)) ->
     YK11.getr regsX 1 = Z_to_bv 64 0x13298 -> YK11.getr regsX 2 = Z_to_bv 64 (S - 176) ->
     YK11.getr regsX 3 = YK11.getr regs 3 -> YK11.getr regsX 4 = YK11.getr regs 4 ->
     YK11.getr regsX 8 = Z_to_bv 64 len -> YK11.getr regsX 10 = Z_to_bv 64 out ->
     YK11.getr regsX 18 = Z_to_bv 64 (frame + 50) -> YK11.getr regsX 25 = Z_to_bv 64 frame ->
     SRcf B (mkCfg (@YK11.mkst fx' regsX (Z_to_bv 64 LLVM_FREE) memX (YK11.seg_rom (ms_segs B))) mdX)
       (fd_seg_post_cf B API S len frame fr L A regs mem md b (fd_up_regs len frame) FD_DOWN_END)).
  { intros fx' regsX memX mdX LX AXX HfrmX FRX EbX HresX X1 X2 X3 X4 X8 X10 X18 X25.
    assert (HspX : spZ regsX = S - 176) by (unfold spZ; rewrite X2; apply MState.unsigned_lit; lia).
    eapply g_free_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
      (x := out) (n := fd_olen nch ns) (bres := sb_malloc b (fd_olen nch ns)).
    all: try eassumption. all: try (rewrite ?HspX; kunf; lia).
    - rewrite X1. apply ret_ok_even; reflexivity.
    - rewrite X4. exact Htp.
    - rewrite EbX. exact Hout_in.
    - intros L' A' regs' mem' md' FR' Hrp' (c1 & c2 & Ec1 & Ec2) Hres' Habove' Hkept'.
      rewrite X1. apply (SRcf_ret B).
      pose proof FR' as (HM' & HW' & HB' & HID' & _ & Hhigh' & _ & _ & _ & Hw' & Herr' & _ & Hro3).
      destruct (mr_model B _ (aa_laws API) _ _ _ _ HM') as (Hh' & Hl' & _).
      assert (Y : forall r, callee_saved r -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regsX (Z_to_bv 5 r))
        by exact Hrp'.
      assert (BL : blocks L' A' = blocks L A).
      { rewrite EbX, Eb1 in Ec1. rewrite Ec2, Eb2.
        assert (N1 : ~ In (out, fd_olen nch ns) (b1 ++ b2)) by (apply nonempty_not_twice; [exact PW2 | lia]).
        assert (N2 : ~ In (out, fd_olen nch ns) (c1 ++ c2)).
        { apply nonempty_not_twice; [rewrite <- Ec1; exact PW2 | lia]. }
        destruct (app_mid_inv (out, fd_olen nch ns) b1 b2 c1 c2
          ltac:(intros h; apply N1; apply in_or_app; left; exact h)
          ltac:(intros h; apply N2; apply in_or_app; left; exact h) Ec1) as [-> ->].
        reflexivity. }
      unfold fd_seg_post_cf. exists fx', L', A', regs', mem', md'.
      split; [unfold FD_DOWN_END; reflexivity|].
      split; [exact HfrmX|].
      assert (S2 : YK11.getr regs' 2 = Z_to_bv 64 (S - 176)) by (change (YK11.getr regs' 2) with (YK11.getr regs' (Z_to_bv 5 2)); rewrite (Y 2 ltac:(unfold callee_saved; lia)); exact X2).
      assert (Hsp' : spZ regs' = S - 176) by (unfold spZ; rewrite S2; apply MState.unsigned_lit; lia).
      split.
      { unfold fd_inv_cf. split; [exact HM'|]. split; [exact HW'|]. split; [exact HB'|].
        rewrite Hsp'. split; [exact Hal|]. split; [kunf; lia|]. split; [lia|].
        split; [intros a Ha; apply Hw'; kunf; lia|].
        split.
        { intros a Ha. destruct (Z_lt_le_dec a (S - FD_KEEP)) as [La|La].
          - apply Hw'. kunf. lia.
          - apply (proj1 (proj2 (Hhigh' a ltac:(kunf; lia) ltac:(kunf; lia)))). apply Hfw. exact Ha. }
        split; [change (YK11.getr regs' 4) with (YK11.getr regs' (Z_to_bv 5 4)); rewrite (Y 4 ltac:(unfold callee_saved; lia)); exact (eq_trans X4 Htp)|].
        split; [exact Herr'|]. split; [exact HID'|]. split; [rewrite SEGS; exact Hro3|].
        split; [exact Hh'|]. split; [exact Hl'|]. split; [reflexivity|].
        split; [exact Hlen|]. split; [exact HLEN|]. split; [rewrite BL; exact Hin|].
        split; [eapply blk_keep; [exact FR' | rewrite HLEN; exact Hin | exact Hblk]|].
        split; [unfold fd_res; rewrite sb_free_malloc in Hres'; exact Hres'|]. exact Hroom. }
      split; [change (YK11.getr regs' 3) with (YK11.getr regs' (Z_to_bv 5 3)); rewrite (Y 3 ltac:(unfold callee_saved; lia)); exact X3|].
      split; [change (YK11.getr regs' 4) with (YK11.getr regs' (Z_to_bv 5 4)); rewrite (Y 4 ltac:(unfold callee_saved; lia)); exact X4|].
      split; [exact BL|]. split; [exact FR'|].
      unfold fd_up_regs.
      split; [change (YK11.getr regs' 8) with (YK11.getr regs' (Z_to_bv 5 8)); rewrite (Y 8 ltac:(unfold callee_saved; lia)); exact X8|].
      split; [change (YK11.getr regs' 25) with (YK11.getr regs' (Z_to_bv 5 25)); rewrite (Y 25 ltac:(unfold callee_saved; lia)); exact X25|].
      change (YK11.getr regs' 18) with (YK11.getr regs' (Z_to_bv 5 18)); rewrite (Y 18 ltac:(unfold callee_saved; lia)). exact X18. }
  assert (HS2 : rw_cells rsegs (normalize rsegs mem2) (S - 176 + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)]).
  { eapply HCELL; [exact Hrel | exact HS1 | | exact Hro2 | kunf; lia]. intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. pose proof (Habove2 a ltac:(rewrite Hsp1; kunf; lia)) as E.
    rewrite SEGS in E. exact E. }
  assert (HS82 : rw_cells rsegs (normalize rsegs mem2) (S - 176 + 8) [CB 32 junk8]).
  { eapply HCELL; [exact Hrel | exact HS81 | | exact Hro2 | kunf; lia]. intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. pose proof (Habove2 a ltac:(rewrite Hsp1; kunf; lia)) as E.
    rewrite SEGS in E. exact E. }
  destruct (norm_blk B API SEGS AX L2 A2 mem2 md2 out (fd_olen nch ns) HM2 Hout_in ltac:(lia) Hro2) as [junko HO2].
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 176))
    by (rewrite (Y2 2 ltac:(unfold callee_saved; lia)); exact G12).
  assert (E29 : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 len)
    by (rewrite (Y2 9 ltac:(unfold callee_saved; lia)); exact G19).
  assert (E218 : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 (fd_fits nch ns))
    by (rewrite (Y2 18 ltac:(unfold callee_saved; lia)); exact G118).
  assert (E219 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 mode)
    by (rewrite (Y2 19 ltac:(unfold callee_saved; lia)); exact G119).
  assert (E223 : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 (fd_olen nch ns))
    by (rewrite (Y2 23 ltac:(unfold callee_saved; lia)); exact G123).
  assert (E225 : YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 frame)
    by (rewrite (Y2 25 ltac:(unfold callee_saved; lia)); exact G125).
  pose proof (MODEX L2 A2 mem2 md2 FR2) as HMX2. pose proof (FRB L2 A2 mem2 md2 FR2) as HFX2.
  pose proof (STKX L2 A2 mem2 md2 FR2) as STX2. pose proof (mem_inv_normalize rsegs mem2) as MIX2.
  rewrite SEGS.
  eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := q_dJ (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
            (S - 176) mode nch ns len frame out (S - 176 - 4096) fr).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of.
    eapply (ud_st2a IHI IHC IMS IDE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S - 176) mode nch ns len frame
      out (S - 176 - 4096) fr junko junk8).
    all: gs. }
  { intros ms (Rj & m' & junkJ & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists Rj, (@fp_regs fx), (Z_to_bv 64 0x130ec), (@fp_csr fx), m',
      [(S - 176 - 4096, S - 176 + 56); (out, out + fd_olen nch ns)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x0 Hx0 NO. apply outside2d in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
    right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE]. }
  intros RJ FJ pcJ fcJ m0J HQJ regsJ mJ HxJ HrelJ FRJ.
  destruct HQJ as (R' & m'' & junkJ & HE & J2 & J3 & J4 & J9 & J10 & J19 & J22 & J23 & J24 & J25 & MUJ & WMJ & MIJ
    & STJ & DCJ & HMJ & HFRJ & HOJ & HWJ).
  injection HE as ER EF EP EC EM. subst R' FJ pcJ fcJ m''.
  pose proof FRJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HroJ).
  assert (DCJ' : dcells (normalize rsegs mJ) (S - 176) len frame nch ns junkJ).
  { unfold dcells in *. eapply HCELL; [exact HrelJ | exact DCJ | | exact HroJ | kunf; lia].
    intros a Ha. split; [reflexivity | tauto]. }
  assert (HOJ' : bytes_at rsegs (normalize rsegs mJ) out (dout len fr nch ns)).
  { apply bytes_at_normalize; [exact HroJ|]. exact (proj2 (bytes_at_rel rsegs mJ _ _ _ HrelJ) HOJ). }
  assert (HWJ' : wr_at rsegs (normalize rsegs mJ) out (fd_olen nch ns)).
  { destruct (norm_blk B API SEGS AX L2 A2 mJ md2 out (fd_olen nch ns) ltac:(destruct FRJ; assumption) Hout_in
      ltac:(lia) HroJ) as [junkw HOw].
    destruct HOw as [_ HWo]. cbn [cells_size csize] in HWo. rewrite Nat.add_0_r, Z2Nat.id in HWo by lia. exact HWo. }
  pose proof (MODEX L2 A2 mJ md2 FRJ) as HMXJ. pose proof (FRB L2 A2 mJ md2 FRJ) as HFXJ.
  pose proof (STKX L2 A2 mJ md2 FRJ) as STXJ. pose proof (mem_inv_normalize rsegs mJ) as MIXJ.
  assert (K2 : YK11.getr regsJ 2 = Z_to_bv 64 (S - 176)) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J2).
  assert (K3 : YK11.getr regsJ 3 = YK11.getr regs 3).
  { rewrite (lf_getr_eqv _ _ _ HxJ). change (reg_get RJ 3 = YK11.getr regs 3). rewrite J3.
    change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs 3).
    rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13. }
  assert (K4 : YK11.getr regsJ 4 = YK11.getr regs 4).
  { rewrite (lf_getr_eqv _ _ _ HxJ). change (reg_get RJ 4 = YK11.getr regs 4). rewrite J4.
    change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs 4).
    rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14. }
  assert (K9 : YK11.getr regsJ 9 = Z_to_bv 64 len) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J9).
  assert (K10 : YK11.getr regsJ 10 = Z_to_bv 64 (dres len fr nch ns)) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J10).
  assert (K19 : YK11.getr regsJ 19 = Z_to_bv 64 mode) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J19).
  assert (K22 : YK11.getr regsJ 22 = Z_to_bv 64 out) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J22).
  assert (K23 : YK11.getr regsJ 23 = Z_to_bv 64 (fd_olen nch ns)) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J23).
  assert (K24 : YK11.getr regsJ 24 = Z_to_bv 64 (pokz len fr nch ns)) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J24).
  assert (K25 : YK11.getr regsJ 25 = Z_to_bv 64 frame) by (rewrite (lf_getr_eqv _ _ _ HxJ); exact J25).
  eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := fun ms => q_dcrt (@fp_regs fx) (@fp_csr fx) (reg_get regsJ 3) (reg_get regsJ 4) (normalize rsegs mJ)
                      (S - 176) mode nch ns len frame out (S - 176 - 4096) fr ms \/
                    q_dfree (@fp_regs fx) (@fp_csr fx) (reg_get regsJ 3) (reg_get regsJ 4) (normalize rsegs mJ)
                      (S - 176) len frame out (fd_olen nch ns) (S - 176 - 4096) fr ms).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of.
    eapply (ud_st2b ICB IMS IPL BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S - 176) mode nch ns len frame
      out (S - 176 - 4096) fr junkJ).
    all: gs. }
  { intros ms [(Rq & m' & jq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)
             | (Rq & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)].
    - exists Rq, (@fp_regs fx), (Z_to_bv 64 0x134e4), (@fp_csr fx), m',
        [(S - 176 - 4096, S - 176 + 56); (out, out + fd_olen nch ns)].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x0 Hx0 NO. apply outside2d in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE].
    - exists Rq, (@fp_regs fx), (Z_to_bv 64 0x14cb4), (@fp_csr fx), m',
        [(S - 176 - 4096, S - 176 + 56); (out, out + fd_olen nch ns)].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x0 Hx0 NO. apply outside2d in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE]. }
  intros Rb Fb pcb fcb m0b HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as [(R' & m'' & jc & HE & C1 & C2 & C3 & C4 & C9 & C10 & C11 & C12 & C13 & C18 & C19 & C22 & C23 & C24
                   & C25 & OK & Hns12 & MU & WM & MI' & ST' & DC' & HM' & HFR' & HB' & HW')
                 | (R' & m'' & HE & F1 & F2 & F3 & F4 & F8 & F10 & F18 & F25 & MU & WM & MI' & HFR' & ST')].
  2:{ injection HE as ER EF EP EC EM. subst R' Fb pcb fcb m''.
      rewrite <- SEGS. change (Z_to_bv 64 0x14cb4) with (Z_to_bv 64 LLVM_FREE).
      apply (FREEK (mkFP (@fp_regs fx) (@fp_csr fx)) regs3 m3 md2 L2 A2 Hfrm FR3 eq_refl Hres2).
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact F1.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact F2.
      - rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 3 = YK11.getr regs 3). rewrite F3. exact K3.
      - rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 4 = YK11.getr regs 4). rewrite F4. exact K4.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact F8.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact F10.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact F18.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact F25. }
  injection HE as ER EF EP EC EM. subst R' Fb pcb fcb m''.
  destruct (decode_ok_factsU len fr nch ns OK) as (L1492 & P1 & P2 & P3 & P4 & PO).
  assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 0x13124) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact C1).
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (S - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact C2).
  assert (Hsp3 : spZ regs3 = S - 176) by (unfold spZ; rewrite G32; apply MState.unsigned_lit; lia).
  assert (G33 : YK11.getr regs3 3 = YK11.getr regs 3).
  { rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 3 = YK11.getr regs 3). rewrite C3. exact K3. }
  assert (G34 : YK11.getr regs3 4 = YK11.getr regs 4).
  { rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 4 = YK11.getr regs 4). rewrite C4. exact K4. }
  assert (HB3 : bytes_at rsegs m3 out (braid_out fr nch ns)) by exact (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel3) HB').
  assert (HF3 : bytes_at rsegs m3 frame fr) by exact (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel3) HFR').
  rewrite <- SEGS. change (Z_to_bv 64 0x134e4) with (Z_to_bv 64 CHECK_ROUND_TRIP).
  eapply g_crt_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (audio := frame + 50) (pcm := out) (nch := nch) (ns := ns) (bres := sb_malloc b (fd_olen nch ns)).
  all: try eassumption. all: try (rewrite ?Hsp3; kunf; lia).
  - rewrite G31. apply ret_ok_even; reflexivity.
  - rewrite G34. exact Htp.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact C10.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact C11.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact C12.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact C13.
  - rewrite even_mod2u. apply Z.eqb_eq. exact P2.
  - exists frame, len. split; [exact Hin2|]. clear - P1 P3 P4 L1492. nia.
  - exists out, (fd_olen nch ns). split; [exact Hout_in|]. rewrite PO. lia.
  - apply (braid_map_up m3 out frame fr); [exact HB3 | exact HF3 | clear - HLEN L1492 P1 P3 P4; nia | lia | exact P2 | lia].
  - destruct Hroom as (Hl1 & Hl2 & Hl3). destruct Hres as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _).
    unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. clear - Hl1 Hl2 Hl3 Hb0 PO P1 P3 P4. nia.
  - intros fx3 L3 A3 regs4 mem4 md4 Hfrm4 FR4 Hrp4 Eb4 Hres4 Habove4 Hkept4.
    rewrite G31.
    assert (Y4 : forall r, callee_saved r -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r))
      by exact Hrp4.
    pose proof FR4 as (HM4' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro4).
    assert (Hout_in4 : In (out, fd_olen nch ns) (blocks L3 A3)) by (rewrite Eb4; exact Hout_in).
    destruct (norm_blk B API SEGS AX L3 A3 mem4 md4 out (fd_olen nch ns) HM4' Hout_in4 ltac:(lia) Hro4)
      as [junk4 HO4].
    assert (HW4 : wr_at rsegs (normalize rsegs mem4) out (fd_olen nch ns)).
    { destruct HO4 as [_ HWo]. cbn [cells_size csize] in HWo. rewrite Nat.add_0_r, Z2Nat.id in HWo by lia. exact HWo. }
    assert (HB4 : bytes_at rsegs (normalize rsegs mem4) out (braid_out fr nch ns)).
    { apply bytes_at_normalize; [exact Hro4|]. apply (bytes_at_frame m3); [exact HB3|].
      intros a Ha. unfold braid_out in Ha. rewrite length_mapseq, Z2Nat.id in Ha by (clear - P1 P3; nia).
      pose proof (Hkept4 out (fd_olen nch ns) (a - out) Hout_in (fun h => h) ltac:(rewrite PO; lia)) as E.
      replace (out + (a - out)) with a in E by lia. rewrite SEGS in E. exact E. }
    assert (DC4 : dcells (normalize rsegs mem4) (S - 176) len frame nch ns jc).
    { unfold dcells in *. eapply HCELL; [exact Hrel3 | exact DC' | | exact Hro4 | kunf; lia]. intros a Ha.
      cbn [cells_size csize Nat.add] in Ha. pose proof (Habove4 a ltac:(rewrite Hsp3; kunf; lia)) as E.
      rewrite SEGS in E. exact E. }
    assert (E42 : YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 (S - 176))
      by (rewrite (Y4 2 ltac:(unfold callee_saved; lia)); exact G32).
    assert (E49 : YK11.getr regs4 (Z_to_bv 5 9) = Z_to_bv 64 len)
      by (rewrite (Y4 9 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C9).
    assert (E418 : YK11.getr regs4 (Z_to_bv 5 18) = Z_to_bv 64 (frame + 50))
      by (rewrite (Y4 18 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C18).
    assert (E419 : YK11.getr regs4 (Z_to_bv 5 19) = Z_to_bv 64 mode)
      by (rewrite (Y4 19 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C19).
    assert (E422 : YK11.getr regs4 (Z_to_bv 5 22) = Z_to_bv 64 out)
      by (rewrite (Y4 22 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C22).
    assert (E423 : YK11.getr regs4 (Z_to_bv 5 23) = Z_to_bv 64 (fd_olen nch ns))
      by (rewrite (Y4 23 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C23).
    assert (E424 : YK11.getr regs4 (Z_to_bv 5 24) = Z_to_bv 64 (pokz len fr nch ns))
      by (rewrite (Y4 24 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C24).
    assert (E425 : YK11.getr regs4 (Z_to_bv 5 25) = Z_to_bv 64 frame)
      by (rewrite (Y4 25 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact C25).
    pose proof (MODEX L3 A3 mem4 md4 FR4) as HMX4. pose proof (FRB L3 A3 mem4 md4 FR4) as HFX4.
    pose proof (STKX L3 A3 mem4 md4 FR4) as STX4. pose proof (mem_inv_normalize rsegs mem4) as MIX4.
    rewrite SEGS.
    eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
      (Q := q_dfree (@fp_regs fx3) (@fp_csr fx3) (reg_get regs4 3) (reg_get regs4 4) (normalize rsegs mem4)
              (S - 176) len frame out (fd_olen nch ns) (S - 176 - 4096) fr).
    all: try eassumption. all: try (kunf; lia).
    { unfold Regs6ss.mkR_of.
      eapply (ud_st3 ICB IMS IPL BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S - 176) mode nch ns len frame
        out (S - 176 - 4096) fr jc).
      all: gs. }
    { intros ms (R5 & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU5 & WM5 & _).
      exists R5, (@fp_regs fx3), (Z_to_bv 64 0x14cb4), (@fp_csr fx3), m',
        [(S - 176 - 4096, S - 176 + 56); (out, out + fd_olen nch ns)].
      split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|].
      intros x0 Hx0 NO. apply outside2d in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in4|]. split; [lia | exact MINE]. }
    intros R5 F5 pc5 fc5 m05 HQ5 regs5 m5 Hx5 Hrel5 FR5.
    destruct HQ5 as (R5' & m5' & HE5 & S1 & S2 & S3 & S4 & S8 & S10 & S18 & S25 & _).
    injection HE5 as ER5 EF5 EP5 EC5 EM5. subst R5' F5 pc5 fc5 m5'.
    rewrite <- SEGS. change (Z_to_bv 64 0x14cb4) with (Z_to_bv 64 LLVM_FREE).
    apply (FREEK (mkFP (@fp_regs fx3) (@fp_csr fx3)) regs5 m5 md4 L3 A3 Hfrm4 FR5 Eb4 Hres4).
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S1.
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S2.
    + rewrite (lf_getr_eqv _ _ _ Hx5). change (reg_get R5 3 = YK11.getr regs 3). rewrite S3.
      change (YK11.getr regs4 (Z_to_bv 5 3) = YK11.getr regs 3).
      rewrite (Y4 3 ltac:(unfold callee_saved; lia)). exact G33.
    + rewrite (lf_getr_eqv _ _ _ Hx5). change (reg_get R5 4 = YK11.getr regs 4). rewrite S4.
      change (YK11.getr regs4 (Z_to_bv 5 4) = YK11.getr regs 4).
      rewrite (Y4 4 ltac:(unfold callee_saved; lia)). exact G34.
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S8.
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S10.
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S18.
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S25.
Qed.

End D.
