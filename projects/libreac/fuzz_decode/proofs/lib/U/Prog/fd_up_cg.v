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
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib SlotUp
  reac_frame_inspect_c memset_c reac_decode_c reac_upstream_channels_c reac_upstream_decode_c reac_upstream_decode
  check_braid_c check_round_trip_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr fd_segments_c fd_glue
  fd_seghelp fd_up_q fd_up_evt SlotUpB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import fd_up LLVMFuzzerTestOneInput_cfb fd_segments_ccf check_round_trip_ccf fd_glue_cg.
Import ListNotations.
Open Scope Z_scope.

Section U.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract_cf fx' rc B API.
Context (IUC : reac_upstream_channels_contract) (IMS : memset_contract) (IUD : reac_upstream_decode_contract)
  (ICB : check_braid_contract).

Theorem fd_up_holds_cf : fd_up_contract_cf B API.
Proof.
  intros ((SEGS & HMAL & HFRE & HGG & HG & AX) & ERRL) L A regs mem md b S len frame fr INV Hfrm (H8 & H25 & H18).
  pose proof INV as (HM & HW & HB & Hal & Hceil & H63 & Hstw & Hfw & Htp & Herr & HID & Hro & Hh & Hl & Hsp
    & Hlen & HLEN & Hin & Hblk & Hres & Hroom).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold FD_FRAME, FD_WIN in *.
  rewrite Hsp in Hal, Hceil, H63, Hstw.
  unfold CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hceil, Hstw.
  assert (Hro' : ro_agree rsegs mem) by (rewrite <- SEGS; exact Hro).
  pose proof Hin as Hin'. apply blocks_In in Hin' as (qf & Hqf & Hqfin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md qf len HM Hqfin) as (Hf1 & Hf2). rewrite Hqf in Hf1, Hf2.
  pose proof (up_olen_bounds len Hlen) as OLB.
  pose proof (upstream_result_range len Hlen) as URB.
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
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  rewrite SEGS.
  eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := q_umalloc (@fp_regs fx) (@fp_csr fx) (reg_get regs 3) (reg_get regs 4) (normalize rsegs mem) (S - 176)
            len frame).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of, FD_UP.
    eapply (stU1 IUC). all: try gs. }
  { intros ms (R & -> & _).
    exists R, (@fp_regs fx), (Z_to_bv 64 0x14df4), (@fp_csr fx), (normalize rsegs mem), (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x0 Hx0 NO. exfalso. apply NO. cbn [outside]. exact I. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & HE & R1 & R2 & R3 & R4 & R8 & R10 & R18 & R19 & R21 & R25).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m0'.
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x13328) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R1).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (S - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R2).
  assert (G13 : YK11.getr regs1 3 = YK11.getr regs 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R3).
  assert (G14 : YK11.getr regs1 4 = YK11.getr regs 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R4).
  assert (G18 : YK11.getr regs1 8 = Z_to_bv 64 len) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R8).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 (frame + 50)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R18).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (up_olen len)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R10).
  assert (G119 : YK11.getr regs1 19 = Z_to_bv 64 (upstream_result len)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R19).
  assert (G121 : YK11.getr regs1 21 = Z_to_bv 64 (up_olen len)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R21).
  assert (G125 : YK11.getr regs1 25 = Z_to_bv 64 frame) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R25).
  assert (Hsp1 : spZ regs1 = S - 176) by (unfold spZ; rewrite G12; apply MState.unsigned_lit; lia).
  assert (Hra1 : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0) by (rewrite Hsp1; exact Hal).
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (rewrite G14; exact Htp).
  assert (ROOM1 : room_ag b (up_olen len)).
  { destruct Hres as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _). destruct Hroom as (Hl1 & Hl2 & Hl3).
    apply lf_room_ag; lia. }
  rewrite <- SEGS. change (Z_to_bv 64 0x14df4) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (n := up_olen len) (bres := b).
  all: try eassumption. all: try (rewrite ?Hsp1; kunf; lia).
  intros L2 A2 regs2 mem2 md2 out FR2 Hrp2 G210 Hout1 Hout2 Hout16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G1.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & HwX2 & _ & _ & Hro2).
  assert (Hin2 : In (frame, len) (blocks L2 A2)).
  { rewrite Eb1. rewrite Eb2 in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
  assert (Hout_in : In (out, up_olen len) (blocks L2 A2)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW2 : pairwise ranges_disjoint (b1 ++ (out, up_olen len) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2). }
  assert (DOF : out + up_olen len <= frame \/ frame + len <= out).
  { pose proof (disj_mid b1 (out, up_olen len) b2 (frame, len) PW2 ltac:(rewrite <- Eb2; exact Hin)) as H.
    cbn [fst snd] in H. exact H. }
  assert (MINE : forall a k, In (a, k) (blocks L A) -> a + k <= out \/ out + up_olen len <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (disj_mid b1 (out, up_olen len) b2 (a, k) PW2 Hak) as H.
    cbn [fst snd] in H. lia. }
  assert (FREEK : forall (fx' : YK11.FPState) regsX memX mdX LX AXX,
     frm_zero (@fp_csr fx') ->
     lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
     blocks LX AXX = blocks L2 A2 -> res_ok_slots AXX (sb_malloc b (up_olen len)) ->
     YK11.getr regsX 1 = Z_to_bv 64 0x13490 -> YK11.getr regsX 2 = Z_to_bv 64 (S - 176) ->
     YK11.getr regsX 3 = YK11.getr regs 3 -> YK11.getr regsX 4 = YK11.getr regs 4 ->
     YK11.getr regsX 8 = Z_to_bv 64 len -> YK11.getr regsX 10 = Z_to_bv 64 out ->
     YK11.getr regsX 18 = Z_to_bv 64 (frame + 50) -> YK11.getr regsX 25 = Z_to_bv 64 frame ->
     SRcf B (mkCfg (@YK11.mkst fx' regsX (Z_to_bv 64 LLVM_FREE) memX (YK11.seg_rom (ms_segs B))) mdX)
       (fd_seg_post_cf B API S len frame fr L A regs mem md b (fd_exit_regs frame) FD_UP_END)).
  { intros fx' regsX memX mdX LX AXX HfrmX FRX EbX HresX X1 X2 X3 X4 X8 X10 X18 X25.
    assert (HspX : spZ regsX = S - 176) by (unfold spZ; rewrite X2; apply MState.unsigned_lit; lia).
    eapply g_free_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
      (x := out) (n := up_olen len) (bres := sb_malloc b (up_olen len)).
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
        assert (N1 : ~ In (out, up_olen len) (b1 ++ b2)) by (apply nonempty_not_twice; [exact PW2 | lia]).
        assert (N2 : ~ In (out, up_olen len) (c1 ++ c2)).
        { apply nonempty_not_twice; [rewrite <- Ec1; exact PW2 | lia]. }
        destruct (app_mid_inv (out, up_olen len) b1 b2 c1 c2
          ltac:(intros h; apply N1; apply in_or_app; left; exact h)
          ltac:(intros h; apply N2; apply in_or_app; left; exact h) Ec1) as [-> ->].
        reflexivity. }
      unfold fd_seg_post_cf. exists fx', L', A', regs', mem', md'.
      split; [unfold FD_UP_END; reflexivity|].
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
      unfold fd_exit_regs.
      change (YK11.getr regs' 25) with (YK11.getr regs' (Z_to_bv 5 25)); rewrite (Y 25 ltac:(unfold callee_saved; lia)). exact X25. }
  destruct (norm_blk B API SEGS AX L2 A2 mem2 md2 out (up_olen len) HM2 Hout_in ltac:(lia) Hro2) as [junko HO2].
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 176))
    by (rewrite (Y2 2 ltac:(unfold callee_saved; lia)); exact G12).
  assert (E28 : YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 len)
    by (rewrite (Y2 8 ltac:(unfold callee_saved; lia)); exact G18).
  assert (E218 : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 (frame + 50))
    by (rewrite (Y2 18 ltac:(unfold callee_saved; lia)); exact G118).
  assert (E219 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (upstream_result len))
    by (rewrite (Y2 19 ltac:(unfold callee_saved; lia)); exact G119).
  assert (E221 : YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 (up_olen len))
    by (rewrite (Y2 21 ltac:(unfold callee_saved; lia)); exact G121).
  assert (E225 : YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 frame)
    by (rewrite (Y2 25 ltac:(unfold callee_saved; lia)); exact G125).
  rewrite SEGS.
  eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := fun ms => q_ucrt (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
                      (S - 176) len frame out (S - 176 - 4096) fr ms \/
                    q_ufree (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
                      (S - 176) len frame out (S - 176 - 4096) ms).
  all: try eassumption. all: try (kunf; lia).
  { unfold Regs6ss.mkR_of.
    eapply (seg_UB IMS IUD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S - 176) len frame out
      (S - 176 - 4096) fr junko).
    all: try gs.
    - exact (STKX L2 A2 mem2 md2 FR2).
    - exact (FRB L2 A2 mem2 md2 FR2).
    - exact (mem_inv_normalize rsegs mem2). }
  { intros ms [(Rq & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)
             | (Rq & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM)].
    - exists Rq, (@fp_regs fx), (Z_to_bv 64 0x134e4), (@fp_csr fx), m',
        [(S - 176 - 4096, S - 176); (out, out + up_olen len)].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x0 Hx0 NO. apply outside2u in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (up_olen len). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE].
    - exists Rq, (@fp_regs fx), (Z_to_bv 64 0x14cb4), (@fp_csr fx), m',
        [(S - 176 - 4096, S - 176); (out, out + up_olen len)].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x0 Hx0 NO. apply outside2u in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (up_olen len). split; [|exact NO]. split; [exact Hout_in|]. split; [lia | exact MINE]. }
  intros Rb Fb pcb fcb m0b HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as [(R' & m'' & HE & R1' & R2' & R3' & R4' & R8' & R10' & R11' & R12' & R13' & R18' & R19' & R20'
                   & R25' & OK & MU & WM & HFR' & HB')
                 | (R' & m'' & HE & R1' & R2' & R3' & R4' & R8' & R10' & R18' & R25' & MU & WM)].
  2:{ injection HE as ER EF EP EC EM. subst R' Fb pcb fcb m''.
      rewrite <- SEGS. change (Z_to_bv 64 0x14cb4) with (Z_to_bv 64 LLVM_FREE).
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
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R18'.
      - rewrite (lf_getr_eqv _ _ _ Hx3). exact R25'. }
  injection HE as ER EF EP EC EM. subst R' Fb pcb fcb m''.
  destruct (up_ok_facts frame out len fr Hlen OK) as (N1 & N2 & N3 & N4 & N5).
  assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 0x13474) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact R1').
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (S - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact R2').
  assert (Hsp3 : spZ regs3 = S - 176) by (unfold spZ; rewrite G32; apply MState.unsigned_lit; lia).
  assert (G33 : YK11.getr regs3 3 = YK11.getr regs 3).
  { rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 3 = YK11.getr regs 3). rewrite R3'.
    change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs 3).
    rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13. }
  assert (G34 : YK11.getr regs3 4 = YK11.getr regs 4).
  { rewrite (lf_getr_eqv _ _ _ Hx3). change (reg_get Rb 4 = YK11.getr regs 4). rewrite R4'.
    change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs 4).
    rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14. }
  assert (HB3 : bytes_at rsegs m3 out (braid_out fr (upstream_result len) 12))
    by exact (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel3) HB').
  assert (HF3 : bytes_at rsegs m3 frame fr) by exact (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel3) HFR').
  rewrite <- SEGS. change (Z_to_bv 64 0x134e4) with (Z_to_bv 64 CHECK_ROUND_TRIP).
  eapply g_crt_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (audio := frame + 50) (pcm := out) (nch := upstream_result len) (ns := 12)
    (bres := sb_malloc b (up_olen len)).
  all: try eassumption. all: try (rewrite ?Hsp3; kunf; lia).
  - rewrite G31. apply ret_ok_even; reflexivity.
  - rewrite G34. exact Htp.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R10'.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R11'.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R12'.
  - rewrite (lf_getr_eqv _ _ _ Hx3). exact R13'.
  - rewrite even_mod2u. apply Z.eqb_eq. exact N2.
  - exists frame, len. split; [exact Hin2|]. lia.
  - exists out, (up_olen len). split; [exact Hout_in|]. lia.
  - apply (braid_map_up m3 out frame fr); [exact HB3 | exact HF3 | lia | lia | exact N2 | lia].
  - destruct Hroom as (Hl1 & Hl2 & Hl3). destruct Hres as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _).
    unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. nia.
  - intros fx3 L3 A3 regs4 mem4 md4 Hfrm4 FR4 Hrp4 Eb4 Hres4 Habove4 Hkept4.
    rewrite G31.
    assert (Y4 : forall r, callee_saved r -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r))
      by exact Hrp4.
    pose proof FR4 as (HM4' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro4).
    assert (Hout_in4 : In (out, up_olen len) (blocks L3 A3)) by (rewrite Eb4; exact Hout_in).
    assert (HB4 : bytes_at rsegs (normalize rsegs mem4) out (braid_out fr (upstream_result len) 12)).
    { apply bytes_at_normalize; [exact Hro4|]. apply (bytes_at_frame m3); [exact HB3|].
      intros a Ha. unfold braid_out in Ha. rewrite length_mapseq, Z2Nat.id in Ha by nia.
      pose proof (Hkept4 out (up_olen len) (a - out) Hout_in (fun h => h) ltac:(rewrite N4; lia)) as E.
      replace (out + (a - out)) with a in E by lia. rewrite SEGS in E. exact E. }
    assert (E42 : YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 (S - 176))
      by (rewrite (Y4 2 ltac:(unfold callee_saved; lia)); exact G32).
    assert (E48 : YK11.getr regs4 (Z_to_bv 5 8) = Z_to_bv 64 len)
      by (rewrite (Y4 8 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R8').
    assert (E418 : YK11.getr regs4 (Z_to_bv 5 18) = Z_to_bv 64 (frame + 50))
      by (rewrite (Y4 18 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R18').
    assert (E419 : YK11.getr regs4 (Z_to_bv 5 19) = Z_to_bv 64 (upstream_result len))
      by (rewrite (Y4 19 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R19').
    assert (E420 : YK11.getr regs4 (Z_to_bv 5 20) = Z_to_bv 64 out)
      by (rewrite (Y4 20 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R20').
    assert (E425 : YK11.getr regs4 (Z_to_bv 5 25) = Z_to_bv 64 frame)
      by (rewrite (Y4 25 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx3); exact R25').
    rewrite SEGS.
    eapply g_run_cf with (stk := LLVM_K - FD_KEEP) (S := S - FD_KEEP) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
      (Q := q_ufree (@fp_regs fx3) (@fp_csr fx3) (reg_get regs4 3) (reg_get regs4 4) (normalize rsegs mem4)
              (S - 176) len frame out (S - 176 - 4096)).
    all: try eassumption. all: try (kunf; lia).
    { unfold Regs6ss.mkR_of.
      eapply (stU3 ICB) with (fr := fr).
      all: try gs.
      - exact (FRB L3 A3 mem4 md4 FR4).
      - exact (STKX L3 A3 mem4 md4 FR4). }
    { intros ms (R5 & m' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU5 & WM5).
      exists R5, (@fp_regs fx3), (Z_to_bv 64 0x14cb4), (@fp_csr fx3), m',
        [(S - 176 - 4096, S - 176); (out, out + up_olen len)].
      split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|].
      intros x0 Hx0 NO. apply outside2u in NO. destruct NO as [NO|NO]; [left; kunf; lia|].
      right. exists out, (up_olen len). split; [|exact NO]. split; [exact Hout_in4|]. split; [lia | exact MINE]. }
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

End U.
