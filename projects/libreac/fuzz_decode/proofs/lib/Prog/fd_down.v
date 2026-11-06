From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown SlotDownB
  SlotDownT reac_frame_inspect_c reac_frame_counter_c memset_c reac_decode_c reac_decode_plain_le_c bcmp_c
  check_braid_c check_round_trip_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr fd_segments_c fd_glue
  fd_seghelp fd_down_evt fd_down_st.
Import ListNotations.
Open Scope Z_scope.

Ltac kunf := unfold FD_WIN, LLVM_K, FD_KEEP, LLVM_FRAME, FD_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK,
  MODE_44K1, MODE_48K, MODE_96K, LF_RES_TOP in *.
Ltac gs := lazymatch goal with |- forall _, _ => fail | |- _ =>
  first [eassumption | (kunf; lia) | (left; kunf; lia) | (right; kunf; lia)] end.

Lemma olen_bounds : forall nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 -> 1 <= fd_olen nch ns <= 48387.
Proof.
  intros nch ns H1 H2. unfold fd_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:E; [|lia].
  rewrite andb_true_iff, !Z.ltb_lt in E. nia.
Qed.

Lemma outside1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma outside2 : forall a1 b1 a2 b2 x, ~ outside [(a1, b1); (a2, b2)] x -> a1 <= x < b1 \/ a2 <= x < b2.
Proof.
  intros a1 b1 a2 b2 x NO. destruct (Z_le_dec a1 x); destruct (Z_lt_dec x b1); try (left; lia);
    destruct (Z_le_dec a2 x); destruct (Z_lt_dec x b2); try (right; lia);
    exfalso; apply NO; cbn [outside]; repeat split; try exact I; lia.
Qed.

Section D.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract fx' rc B API.
Context (IHI : reac_frame_inspect_contract) (IHC : reac_frame_counter_contract) (IMS : memset_contract)
  (IDE : reac_decode_contract) (ICB : check_braid_contract) (IPL : reac_decode_plain_le_contract)
  (BC : bcmp_contract).

Theorem fd_down_holds : fd_down_contract B API.
Proof.
  intros ((SEGS & HMAL & HFRE & HGG & HG & AX) & ERRL) L A regs mem md b S len frame mode nch ns fr INV Hfrm H18 MODE.
  pose proof INV as (HM & HW & HB & Hal & Hceil & H63 & Hstw & Hfw & Htp & Herr & HID & Hro & Hh & Hl & Hsp & H25
    & H26 & Hlen & HLEN & Hin & Hblk & Hres & Hroom).
  pose proof MODE as (Hmode & Hnch & Hns & HM4 & HM8).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold FD_FRAME, FD_WIN in *.
  rewrite Hsp in Hal, Hceil, H63, Hstw.
  unfold CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hceil, Hstw.
  assert (Hro' : ro_agree rsegs mem) by (rewrite <- SEGS; exact Hro).
  pose proof Hin as Hin'. apply blocks_In in Hin' as (qf & Hqf & Hqfin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md qf len HM Hqfin) as (Hf1 & Hf2). rewrite Hqf in Hf1, Hf2.
  pose proof (olen_bounds nch ns Hnch Hns) as OLB.
  assert (G2 : YK11.getr regs 2 = Z_to_bv 64 (S - 160)).
  { unfold spZ in Hsp. rewrite <- Hsp. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (WIN : forall a, S - LLVM_K <= a < S - FD_KEEP -> writable_at (ms_segs B) mem a).
  { intros a Ha. kunf. destruct (Z_lt_le_dec a (S - 160)); [apply Hstw | apply Hfw]; lia. }
  assert (FR0 : lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md L A mem md).
  { apply lf_fr_refl; try assumption. intros a Ha. apply WIN. lia. }
  assert (FRB : forall LX AXX memX mdX, lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     bytes_at rsegs (normalize rsegs memX) frame fr).
  { intros LX AXX memX mdX FRX. pose proof FRX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HroX).
    apply bytes_at_normalize; [exact HroX|]. apply (blk_bytes_at B); [exact SEGS | lia | lia |].
    eapply blk_keep; [exact FRX | rewrite HLEN; exact Hin | exact Hblk]. }
  assert (STKX : forall LX AXX memX mdX, lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     Frame.stk rsegs (normalize rsegs memX) (S - 160 - 4096) (S - 160)).
  { intros LX AXX memX mdX FRX. pose proof FRX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HwX & _ & _ & HroX).
    eapply norm_stk; try eassumption; try (kunf; lia). intros a Ha. apply HwX. kunf. lia. }
  assert (MODEX : forall LX AXX memX mdX, lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     bytes_at rsegs (normalize rsegs memX) (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { intros LX AXX memX mdX FRX. eapply mode_keep; try eassumption; kunf; lia. }
  assert (STK0 : Frame.stk rsegs (normalize rsegs mem) (S - LLVM_K) (S - 160 + 40)).
  { eapply norm_stk; try eassumption; try (kunf; lia). intros a Ha. apply WIN. kunf. lia. }
  destruct (stk_carve rsegs _ _ _ 8 STK0 ltac:(kunf; lia)) as [STK1 [junk HS32]].
  change (Z.of_nat 8) with 8 in STK1, HS32. replace (S - 160 + 40 - 8) with (S - 160 + 32) in STK1, HS32 by lia.
  destruct (stk_carve rsegs _ _ _ 24 STK1 ltac:(kunf; lia)) as [STK2 [junk8 HS8]].
  change (Z.of_nat 24) with 24 in STK2, HS8. replace (S - 160 + 32 - 24) with (S - 160 + 8) in STK2, HS8 by lia.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  pose proof (MODEX L A mem md FR0) as HM0. pose proof (FRB L A mem md FR0) as HFR0.
  pose proof (STKX L A mem md FR0) as ST0.
  assert (DMS : mode + 12 <= S - 160 - 4096 \/ S - 160 + 40 <= mode + 4) by (kunf; lia).
  assert (HCELL : forall m0 m1 m2 A0 cs, mem_rel rsegs m1 m0 -> rw_cells rsegs m0 A0 cs ->
     (forall a, A0 <= a < A0 + Z.of_nat (cells_size cs) ->
        mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)) ->
     ro_agree rsegs m2 -> LF_RES_TOP <= A0 -> rw_cells rsegs (normalize rsegs m2) A0 cs).
  { intros m0 m1 m2 A0 cs HR C E Hr2 HA. apply (lf_rw_cells_norm B); [exact SEGS | exact Hr2 | |].
    - intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). unfold LF_RES_TOP in *. lia.
    - apply (lf_rw_cells_frame m1); [exact (lf_rw_cells_rel m1 m0 _ _ HR C) | exact E]. }
  rewrite SEGS.
  eapply g_run with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := q_malloc1 (@fp_regs fx) (@fp_csr fx) (reg_get regs 3) (reg_get regs 4) (normalize rsegs mem) (S - 160)
            mode nch ns len frame (S - 160 - 4096) fr junk8).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of, FD_DOWN.
    eapply st1 with (junk := junk). all: try gs. }
  { intros ms (R & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists R, (@fp_regs fx), (Z_to_bv 64 0x147c4), (@fp_csr fx), m', [(S - 160 + 32, S - 160 + 40)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x0 Hx0 NO. left. apply outside1 in NO. kunf. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & HE & R1 & R2 & R3 & R4 & R10 & R18 & R20 & R22 & R23 & R25 & R26 & MU1 & WM1 & MI1
    & HS1 & HS81 & HM1 & HFR1 & ST1).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12eb4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R1).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (S - 160)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R2).
  assert (G13 : YK11.getr regs1 3 = YK11.getr regs 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R3).
  assert (G14 : YK11.getr regs1 4 = YK11.getr regs 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R4).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (fd_olen nch ns)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R10).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 mode) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R18).
  assert (G120 : YK11.getr regs1 20 = Z_to_bv 64 ns) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R20).
  assert (G122 : YK11.getr regs1 22 = Z_to_bv 64 (fd_olen nch ns)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R22).
  assert (G123 : YK11.getr regs1 23 = Z_to_bv 64 (fd_fits nch ns)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R23).
  assert (G125 : YK11.getr regs1 25 = Z_to_bv 64 len) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R25).
  assert (G126 : YK11.getr regs1 26 = Z_to_bv 64 frame) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R26).
  assert (Hsp1 : spZ regs1 = S - 160) by (unfold spZ; rewrite G12; apply MState.unsigned_lit; lia).
  assert (Hra1 : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0) by (rewrite Hsp1; exact Hal).
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (rewrite G14; exact Htp).
  assert (ROOM1 : room_slots b (fd_olen nch ns)).
  { destruct Hres as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _). destruct Hroom as (Hl1 & Hl2 & Hl3).
    apply lf_room; lia. }
  rewrite <- SEGS. change (Z_to_bv 64 0x147c4) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
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
     YK11.getr regsX 1 = Z_to_bv 64 0x130fc -> YK11.getr regsX 2 = Z_to_bv 64 (S - 160) ->
     YK11.getr regsX 3 = YK11.getr regs 3 -> YK11.getr regsX 4 = YK11.getr regs 4 ->
     YK11.getr regsX 8 = Z_to_bv 64 (frame + 50) -> YK11.getr regsX 10 = Z_to_bv 64 out ->
     YK11.getr regsX 25 = Z_to_bv 64 len -> YK11.getr regsX 26 = Z_to_bv 64 frame ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regsX (Z_to_bv 64 LLVM_FREE) memX (YK11.seg_rom (ms_segs B))) mdX)
       (fd_seg_post B API S len frame fr L A regs mem md b FD_DOWN_END)).
  { intros fx' regsX memX mdX LX AXX HfrmX FRX EbX HresX X1 X2 X3 X4 X8 X10 X25 X26.
    assert (HspX : spZ regsX = S - 160) by (unfold spZ; rewrite X2; apply MState.unsigned_lit; lia).
    eapply g_free with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
      (x := out) (n := fd_olen nch ns) (bres := sb_malloc b (fd_olen nch ns)).
    all: try eassumption. all: try (rewrite ?HspX; kunf; lia).
    - rewrite X1. apply ret_ok_even; reflexivity.
    - rewrite X4. exact Htp.
    - rewrite EbX. exact Hout_in.
    - intros L' A' regs' mem' md' FR' Hrp' (c1 & c2 & Ec1 & Ec2) Hres' Habove' Hkept'.
      rewrite X1. apply SR_ret.
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
      unfold fd_seg_post. exists fx', L', A', regs', mem', md'.
      split; [unfold FD_DOWN_END; reflexivity|].
      split; [exact HfrmX|].
      assert (S2 : YK11.getr regs' 2 = Z_to_bv 64 (S - 160)) by (change (YK11.getr regs' 2) with (YK11.getr regs' (Z_to_bv 5 2)); rewrite (Y 2 ltac:(unfold callee_saved; lia)); exact X2).
      assert (Hsp' : spZ regs' = S - 160) by (unfold spZ; rewrite S2; apply MState.unsigned_lit; lia).
      split.
      { unfold fd_inv. split; [exact HM'|]. split; [exact HW'|]. split; [exact HB'|].
        rewrite Hsp'. split; [exact Hal|]. split; [kunf; lia|]. split; [lia|].
        split; [intros a Ha; apply Hw'; kunf; lia|].
        split.
        { intros a Ha. destruct (Z_lt_le_dec a (S - FD_KEEP)) as [La|La].
          - apply Hw'. kunf. lia.
          - apply (proj1 (proj2 (Hhigh' a ltac:(kunf; lia) ltac:(kunf; lia)))). apply Hfw. exact Ha. }
        split; [change (YK11.getr regs' 4) with (YK11.getr regs' (Z_to_bv 5 4)); rewrite (Y 4 ltac:(unfold callee_saved; lia)); exact (eq_trans X4 Htp)|].
        split; [exact Herr'|]. split; [exact HID'|]. split; [rewrite SEGS; exact Hro3|].
        split; [exact Hh'|]. split; [exact Hl'|]. split; [reflexivity|].
        split; [change (YK11.getr regs' 25) with (YK11.getr regs' (Z_to_bv 5 25)); rewrite (Y 25 ltac:(unfold callee_saved; lia)); exact X25|].
        split; [change (YK11.getr regs' 26) with (YK11.getr regs' (Z_to_bv 5 26)); rewrite (Y 26 ltac:(unfold callee_saved; lia)); exact X26|].
        split; [exact Hlen|]. split; [exact HLEN|]. split; [rewrite BL; exact Hin|].
        split; [eapply blk_keep; [exact FR' | rewrite HLEN; exact Hin | exact Hblk]|].
        split; [unfold fd_res; rewrite sb_free_malloc in Hres'; exact Hres'|]. exact Hroom. }
      split; [change (YK11.getr regs' 3) with (YK11.getr regs' (Z_to_bv 5 3)); rewrite (Y 3 ltac:(unfold callee_saved; lia)); exact X3|].
      split; [change (YK11.getr regs' 4) with (YK11.getr regs' (Z_to_bv 5 4)); rewrite (Y 4 ltac:(unfold callee_saved; lia)); exact X4|].
      split; [exact BL|]. split; [exact FR'|].
      change (YK11.getr regs' 8) with (YK11.getr regs' (Z_to_bv 5 8)); rewrite (Y 8 ltac:(unfold callee_saved; lia)). exact X8. }
  assert (HS2 : rw_cells rsegs (normalize rsegs mem2) (S - 160 + 32) [C8 (Z_to_bv 64 nch)]).
  { eapply HCELL; [exact Hrel | exact HS1 | | exact Hro2 | kunf; lia]. intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. pose proof (Habove2 a ltac:(rewrite Hsp1; kunf; lia)) as E.
    rewrite SEGS in E. exact E. }
  assert (HS82 : rw_cells rsegs (normalize rsegs mem2) (S - 160 + 8) [CB 24 junk8]).
  { eapply HCELL; [exact Hrel | exact HS81 | | exact Hro2 | kunf; lia]. intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. pose proof (Habove2 a ltac:(rewrite Hsp1; kunf; lia)) as E.
    rewrite SEGS in E. exact E. }
  destruct (norm_blk B API SEGS AX L2 A2 mem2 md2 out (fd_olen nch ns) HM2 Hout_in ltac:(lia) Hro2) as [junko HO2].
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 160))
    by (rewrite (Y2 2 ltac:(unfold callee_saved; lia)); exact G12).
  assert (E218 : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 mode)
    by (rewrite (Y2 18 ltac:(unfold callee_saved; lia)); exact G118).
  assert (E220 : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 ns)
    by (rewrite (Y2 20 ltac:(unfold callee_saved; lia)); exact G120).
  assert (E222 : YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 (fd_olen nch ns))
    by (rewrite (Y2 22 ltac:(unfold callee_saved; lia)); exact G122).
  assert (E223 : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 (fd_fits nch ns))
    by (rewrite (Y2 23 ltac:(unfold callee_saved; lia)); exact G123).
  assert (E225 : YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 len)
    by (rewrite (Y2 25 ltac:(unfold callee_saved; lia)); exact G125).
  assert (E226 : YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 frame)
    by (rewrite (Y2 26 ltac:(unfold callee_saved; lia)); exact G126).
  rewrite SEGS.
  eapply g_run with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := fun ms => q_crt (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
                      (S - 160) mode nch ns len frame out (S - 160 - 4096) fr junk8 ms \/
                    q_free (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
                      (S - 160) len frame out (fd_olen nch ns) (S - 160 - 4096) fr ms).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of.
    eapply st2 with (junk := junko) (junk8 := junk8).
    all: try gs.
    - exact (MODEX L2 A2 mem2 md2 FR2).
    - exact (FRB L2 A2 mem2 md2 FR2).
    - exact (STKX L2 A2 mem2 md2 FR2).
    - exact (mem_inv_normalize rsegs mem2). }
  { intros ms [(Rq & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)
             | (Rq & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)].
    - exists Rq, (@fp_regs fx), (Z_to_bv 64 0x132f8), (@fp_csr fx), m',
        [(S - 160 - 4096, S - 160 + 32); (out, out + fd_olen nch ns)].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x0 Hx0 NO. apply outside2 in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE].
    - exists Rq, (@fp_regs fx), (Z_to_bv 64 0x14684), (@fp_csr fx), m',
        [(S - 160 - 4096, S - 160 + 32); (out, out + fd_olen nch ns)].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x0 Hx0 NO. apply outside2 in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE]. }
  intros Rb Fb pcb fcb m0b HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as [(R' & m'' & HE & R1' & R2' & R3' & R4' & R10' & R11' & R12' & R13' & R18' & R19' & R20' & R22'
                   & R23' & R25' & R26' & OK & Hns12 & MU & WM & MI' & ST' & HFR' & HM' & HS' & HS8' & HB' & HW')
                 | (R' & m'' & HE & R1' & R2' & R3' & R4' & R8' & R10' & R25' & R26' & MU & WM & MI' & HFR' & ST')].
  2:{ injection HE as ER EF EP EC EM. subst R' Fb pcb fcb m''.
      rewrite <- SEGS. change (Z_to_bv 64 0x14684) with (Z_to_bv 64 LLVM_FREE).
      apply (FREEK (mkFP (@fp_regs fx) (@fp_csr fx)) regs3 m3 md2 L2 A2 Hfrm FR3 eq_refl Hres2).
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R1'.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R2'.
      - rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 3 = YK11.getr regs 3). rewrite R3'.
        change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs 3).
        rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13.
      - rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 4 = YK11.getr regs 4). rewrite R4'.
        change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs 4).
        rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R8'.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R10'.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R25'.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R26'. }
  injection HE as ER EF EP EC EM. subst R' Fb pcb fcb m''.
  destruct (decode_ok_facts len fr nch ns OK) as (L1492 & P1 & P2 & P3 & P4 & PO & PK).
  assert (N3 : 3 * nch * ns <= 1440) by (clear - P4; nia).
  assert (N0 : 0 <= 3 * nch * ns) by (clear - P1 P3; nia).
  assert (N7 : 7 * nch * ns <= 3360) by (clear - P4; nia).
  assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 0x12fd0) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact R1').
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (S - 160)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact R2').
  assert (Hsp3 : spZ regs3 = S - 160) by (unfold spZ; rewrite G32; apply MState.unsigned_lit; lia).
  assert (G33 : YK11.getr regs3 3 = YK11.getr regs 3).
  { rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 3 = YK11.getr regs 3). rewrite R3'.
    change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs 3).
    rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13. }
  assert (G34 : YK11.getr regs3 4 = YK11.getr regs 4).
  { rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 4 = YK11.getr regs 4). rewrite R4'.
    change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs 4).
    rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14. }
  assert (HB3 : bytes_at rsegs m3 out (braid_out fr nch ns)) by exact (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel3) HB').
  assert (HF3 : bytes_at rsegs m3 frame fr) by exact (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel3) HFR').
  rewrite <- SEGS. change (Z_to_bv 64 0x132f8) with (Z_to_bv 64 CHECK_ROUND_TRIP).
  eapply g_crt with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (audio := frame + 50) (pcm := out) (nch := nch) (ns := ns) (bres := sb_malloc b (fd_olen nch ns)).
  all: try eassumption. all: try (rewrite ?Hsp3; kunf; lia).
  - rewrite G31. apply ret_ok_even; reflexivity.
  - rewrite G34. exact Htp.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R10'.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R11'.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R12'.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R13'.
  - rewrite even_mod2. apply Z.eqb_eq. exact P2.
  - exists frame, len. split; [exact Hin2|]. lia.
  - exists out, (fd_olen nch ns). split; [exact Hout_in|]. rewrite PO. lia.
  - apply (braid_map_of m3 out frame fr nch ns HB3 HF3); lia.
  - destruct Hroom as (Hl1 & Hl2 & Hl3). destruct Hres as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _).
    unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. unfold CAPMAX in *. lia.
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
      intros a Ha. unfold braid_out in Ha. rewrite length_mapseq, Z2Nat.id in Ha by lia.
      pose proof (Hkept4 out (fd_olen nch ns) (a - out) Hout_in (fun h => h) ltac:(rewrite PO; lia)) as E.
      replace (out + (a - out)) with a in E by lia. rewrite SEGS in E. exact E. }
    assert (HS4 : rw_cells rsegs (normalize rsegs mem4) (S - 160 + 32) [C8 (Z_to_bv 64 nch)]).
    { eapply HCELL; [exact Hrel3 | exact HS' | | exact Hro4 | kunf; lia]. intros a Ha.
      cbn [cells_size csize Nat.add] in Ha. pose proof (Habove4 a ltac:(rewrite Hsp3; kunf; lia)) as E.
      rewrite SEGS in E. exact E. }
    assert (HS84 : rw_cells rsegs (normalize rsegs mem4) (S - 160 + 8) [CB 24 junk8]).
    { eapply HCELL; [exact Hrel3 | exact HS8' | | exact Hro4 | kunf; lia]. intros a Ha.
      cbn [cells_size csize Nat.add] in Ha. pose proof (Habove4 a ltac:(rewrite Hsp3; kunf; lia)) as E.
      rewrite SEGS in E. exact E. }
    assert (E42 : YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 (S - 160))
      by (rewrite (Y4 2 ltac:(unfold callee_saved; lia)); exact G32).
    assert (E418 : YK11.getr regs4 (Z_to_bv 5 18) = Z_to_bv 64 mode)
      by (rewrite (Y4 18 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R18').
    assert (E419 : YK11.getr regs4 (Z_to_bv 5 19) = Z_to_bv 64 out)
      by (rewrite (Y4 19 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R19').
    assert (E420 : YK11.getr regs4 (Z_to_bv 5 20) = Z_to_bv 64 ns)
      by (rewrite (Y4 20 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R20').
    assert (E422 : YK11.getr regs4 (Z_to_bv 5 22) = Z_to_bv 64 (fd_olen nch ns))
      by (rewrite (Y4 22 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R22').
    assert (E423 : YK11.getr regs4 (Z_to_bv 5 23) = Z_to_bv 64 (pokz len fr nch ns))
      by (rewrite (Y4 23 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R23').
    assert (E425 : YK11.getr regs4 (Z_to_bv 5 25) = Z_to_bv 64 len)
      by (rewrite (Y4 25 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R25').
    assert (E426 : YK11.getr regs4 (Z_to_bv 5 26) = Z_to_bv 64 frame)
      by (rewrite (Y4 26 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R26').
    rewrite SEGS.
    eapply g_run with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
      (Q := q_free (@fp_regs fx3) (@fp_csr fx3) (reg_get regs4 3) (reg_get regs4 4) (normalize rsegs mem4)
              (S - 160) len frame out (fd_olen nch ns) (S - 160 - 4096) fr).
    all: try eassumption. all: try (kunf; lia).
    { unfold Regs6ss.mkR_of.
      eapply st3 with (junk8 := junk8) (mode := mode) (nch := nch).
      all: try gs.
      - exact (MODEX L3 A3 mem4 md4 FR4).
      - exact (FRB L3 A3 mem4 md4 FR4).
      - exact (STKX L3 A3 mem4 md4 FR4).
      - exact (mem_inv_normalize rsegs mem4). }
    { intros ms (R5 & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU5 & WM5 & _).
      exists R5, (@fp_regs fx3), (Z_to_bv 64 0x14684), (@fp_csr fx3), m',
        [(S - 160 - 4096, S - 160 + 32); (out, out + fd_olen nch ns)].
      split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|].
      intros x0 Hx0 NO. apply outside2 in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (fd_olen nch ns). split; [|exact NO]. split; [exact Hout_in4|]. split; [lia | exact MINE]. }
    intros R5 F5 pc5 fc5 m05 HQ5 regs5 m5 Hx5 Hrel5 FR5.
    destruct HQ5 as (R5' & m5' & HE5 & S1 & S2 & S3 & S4 & S8 & S10 & S25 & S26 & _).
    injection HE5 as ER5 EF5 EP5 EC5 EM5. subst R5' F5 pc5 fc5 m5'.
    rewrite <- SEGS. change (Z_to_bv 64 0x14684) with (Z_to_bv 64 LLVM_FREE).
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
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S25.
    + rewrite (lf_getr_eqv _ _ _ Hx5). exact S26.
Qed.

End D.
