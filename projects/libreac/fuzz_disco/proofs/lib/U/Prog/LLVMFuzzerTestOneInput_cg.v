From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 Contract FrameAPI KindBGlue AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require MState Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_cut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_preds uslot_R0_R3 uslot_ser_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_age_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import memcpy_c find_entry_c role_of_c reac_hunt_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import check_sighting_c reac_disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_classify_on_segment_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_gate_should_push_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_step_c reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_role_c reac_hunt_heard_anything_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_steps uslot_run LLVMFuzzerTestOneInput.
Import ListNotations.
Open Scope Z_scope.

Definition LLVMFuzzerTestOneInput_cg_contract : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs ->
    ra mod 2 = 0 ->
    ms_malloc B = 0x17aec ->
    ms_free B = 0x179ac ->
    ms_realloc B = None ->
    ms_calloc B = None ->
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) ->
    ms_guard B = 0x51c90 ->
    ms_got_guard B = 0x206a0 ->
    ms_ctx B = 0x51d28 ->
    ms_lock B = 0x51d20 ->
    ms_libc B = 0x51cb0 ->
    ms_size_classes B = 0x10620 ->
    ms_small_cnt B = 0x10680 ->
    ms_med_cnt B = 0x1069b ->
    ms_debruijn B = 0x10600 ->
    ms_tp B = 0x31a20 ->
    ms_errno_off B = -164 ->
    ms_replaced B = None ->
    ms_vmlock B = None ->
    ms_debruijn_len B = 32 ->
    @sk_ofl_head SH = 0x520e0 ->
    @sk_ofl_lock SK = 0x520d8 ->
    @sk_threaded SK = 0x51cb0 + 1 ->
    empty = 0x31930 ->
    0 < empty < 2 ^ 62 ->
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) ->
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
    (forall a, in_globals frame_RELRO a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
    (forall n b, @lib_delta LS n b = b) ->
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG) ->
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) ->
    (forall (rc : RunCeil) (fx : FPState), @malloc_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) (fx : FPState), @free_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) L A mem md, aa_MR (API rc) L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_cg fx rc LS B (API rc) SH SK [] frame_RELRO disco_GI j ENTRY ra empty SLOT_STACK.

Theorem LLVMFuzzerTestOneInput_cg_holds :
  reac_disco_table_init_contract -> reac_disco_gate_init_contract -> reac_disco_peer_lock_init_contract ->
  reac_hunt_init_contract -> reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  reac_disco_table_age_contract -> check_table_contract -> uslot_ser_chain ->
  reac_hunt_step_contract -> reac_hunt_verdict_name_contract -> reac_hunt_role_contract ->
  reac_hunt_heard_anything_contract -> memcpy_contract -> find_entry_contract -> reac_hunt_observe_contract ->
  check_sighting_contract -> reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  reac_disco_gate_should_push_contract -> bcmp_contract -> reac_disco_table_observe_contract -> role_of_contract ->
  LLVMFuzzerTestOneInput_cg_contract.
Proof.
  intros TIC GIC LIC HIC PIC SIC AGE CTC [SERA SERB] HTC VNC RLC HAC MC FEC HOC CSC CC0 CC1 GSC BC OBC ROC.
  intros B API LS SH SK ra empty HSEGS HRA HMAL HFRE HREAL HCAL HERRC HGD HGG HCTX HLK HLIBC HSC HSMC HMDC
    HDB HTP HERR HREP HVML HDBL HHEAD HLOCK HTHR HEMP HEMP2 HCTXRO HG HRELRO HLIBK HDELTA HROOM HFA HMCF HFCF HLIM
    rc fx j Hj.
  intros L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm HK.
  rewrite HLIBK.
  destruct (HFA rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAX & _).
  pose proof Hpre as (HP0 & HLEN & _ & _ & Hroom & _ & _ & _ & _ & Hsp47).
  pose proof HP0 as (HM & _ & _ & _ & _ & _ & Hceil & _ & _ & _ & _ & _ & _ & Hpp & _).
  destruct (HROOM b n Hroom) as (Hl & Hby & Hcap).
  destruct (glue_start B (API rc) ra empty L A regs mem md p n pl b HSEGS HAX HEMP HTP Hpre Hro Hfrm)
    as (HXOK & HDOK & HXIN & HCUT).
  assert (HDBLK : dblk L A p pl).
  { unfold dblk. destruct Hpp as [[Hn0 Hpe] | [_ (q0 & Hq0 & Eq0)]].
    - left. split.
      + destruct pl as [|x pl']; [reflexivity | exfalso; cbn [length] in HLEN; lia].
      + rewrite Hpe, HEMP. unfold IMG_LO, IMG_HI. lia.
    - right. rewrite <- Eq0, <- HLEN. exact (blocks_in L A q0 n Hq0). }
  assert (Hp0 : 0 < p).
  { destruct Hpp as [[_ Hpe] | [_ (q0 & Hq0 & Eq0)]]; [rewrite Hpe, HEMP; lia|].
    pose proof (mr_blocks_range _ _ (aa_laws (API rc)) L A mem md q0 n HM Hq0) as [R1 _]. lia. }
  assert (HSR : SRcf B (mkCfg (mkst regs (Z_to_bv 64 ENTRY) mem (seg_rom rsegs)) md)
    (fun c' => exists q, slot_cut B (API rc) SLOT_STACK (spZ regs) L A mem md b q []
      (fun R m => q = bv_unsigned (MState.ret_pc (getr regs 1)) /\ P_RET regs R m) c')).
  { eapply (@uslot_run_cf rc B (API rc) SH SK SLOT_STACK (spZ regs) L A mem md b);
      first [ exact HCUT | exact HXOK | exact HDOK | exact Hp0 | exact HXIN | exact HDBLK | exact (HFA rc)
            | exact (HMCF rc) | exact (HFCF rc) | exact (HLIM rc)
            | exact HR | exact (conj Hl (conj Hby Hcap)) | eassumption | (unfold SLOT_STACK; lia) ]. }
  rewrite HSEGS in HK |- *.
  apply HSR. intros c' (q & Hc'). apply HK.
  exact (glue_post B (API rc) ra empty L A regs mem md p n pl b j q c' HSEGS HRA HDELTA Hpre Hc').
Qed.
