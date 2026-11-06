From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes tx_put_c TxCalls TxRet tx_string_c tx_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttGlue RttModel RttBase RttA_Lib RttA_Call.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma ra_value : (forall fx' : YK11.FPState, @tx_value_contract fx' rc B API F) ->
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    fx1 L A mem md X Lam peak cnt bnd q want len cap txt regs1 (Pc : config -> Prop),
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rt_text B L0 A0 mem Lam t (negb (pretty =? 0)) q ->
  rt_harn B L0 A0 L A mem Lam (spZ regs0 - 112) want len cap txt ->
  getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 4 = getr regs0 4 -> YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 11 = Z_to_bv 64 doc ->
  getr regs1 12 = Z_to_bv 64 pretty -> getr regs1 13 = Z_to_bv 64 0 ->
  len + Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) 0))) + 1 <= 2 ^ 28 ->
  tx_rooms F bnd len cap (tv_calls t (negb (pretty =? 0)) 0) ->
  (forall L' A' regs' mem' md' want' cap',
     regs_preserved regs1 regs' -> cap' = tx_capf len cap (tv_calls t (negb (pretty =? 0)) 0) ->
     @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem' md' X Lam peak cnt
       (tx_fold F bnd len cap (tv_calls t (negb (pretty =? 0)) 0)) ->
     rt_text B L0 A0 mem' Lam t (negb (pretty =? 0)) q ->
     rt_harn B L0 A0 L' A' mem' Lam (spZ regs0 - 112) want'
       (len + Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) 0)))) cap'
       (txt ++ map (Z_to_bv 8) (concat (wvpieces t (negb (pretty =? 0)) 0))) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' (getr regs1 1) mem' (seg_rom (ms_segs B))) md') Pc) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 TX_VALUE) mem (seg_rom (ms_segs B))) md) Pc.
Proof.
  intros TXV L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q
    want len cap txt regs1 Pc ENT INV RT HARN G2 G4 GRA G10 G11 G12 G13 HLN ROOM K.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & PR & _ & DSUB & _ & DOCS & _ & DEP & _).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & _ & INIT & RD & _ & _ & LED & _ & PERM & NODE & RES & _).
  pose proof RS as (MRc & _).
  pose proof HARN as (HW0 & HL0 & HC0 & REC & TW & TI0 & HB0 & HLam).
  pose proof alloc_ceiling_val as HCV.
  assert (HTS : 0 <= TS_STACK /\ TV_F * 33 + TS_STACK + 112 <= RTT_K) by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (HTV : 0 <= TV_K t /\ TV_K t + 112 <= RTT_K) by (unfold TV_K; unfold TV_F in HTS |- *; lia).
  assert (SP1 : spZ regs1 = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply ra_uns; lia).
  assert (HDL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  assert (PREc : call_pre_k B (aa_MR API) (TV_K t) L A regs1 mem md).
  { apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs1 (TV_K t) 112
      PRE0 RS INIT).
    - exact SP1.
    - rewrite SP1. apply ra_mod16. exact SP16.
    - exact G4.
    - exact GRA.
    - lia.
    - lia.
    - lia. }
  assert (LA : Z.of_nat (length (map (Z_to_bv 8) (concat (wvpieces t (negb (pretty =? 0)) 0)))) =
               Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) 0)))) by (rewrite length_map; reflexivity).
  pose proof (TXV fx1 L A regs1 mem md (spZ regs0 - 112) doc pretty 0 want len cap t D txt bnd Lam peak cnt (2 ^ 64 - 1))
    as HV.
  cbv zeta in HV.
  eapply SR_bind.
  { apply HV.
    - rewrite LA. split; [exact PREc|]. split; [exact INIT|]. split; [exact (proj1 RD)|]. split; [exact G10|].
      split; [lia|]. split; [lia|]. split; [apply ra_mod8; exact SP16|]. split; [exact TW|].
      split; [exact HW0|]. split; [exact HL0|]. split; [exact HC0|]. split; [exact REC|]. split; [exact TI0|].
      split; [exact HLN|]. split; [exact RES | exact ROOM].
    - exact G11.
    - exact G12.
    - exact G13.
    - lia.
    - lia.
    - lia.
    - exact LED.
    - exact NODE.
    - exact HDL.
    - left. rewrite SP1. lia.
    - exact (ra_node_top _ _ _ _ _ _ NODE).
    - right. lia.
    - exact HLam. }
  intros c' (L' & A' & regs' & mem' & md' & -> & RP & (b1 & cap1 & R) & _).
  destruct R as (FR & _ & BK & OLD & NB & REC' & TW' & TI1 & RA' & _ & IN' & _ & HCJ & RESJ).
  rewrite LA in REC', TI1.
  assert (TXR : txr B API (TV_K t) regs1 (spZ regs0 - 112) want cap L A mem md L' A' mem' md' b1
      (len + Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) 0)))) cap1
      (txt ++ map (Z_to_bv 8) (concat (wvpieces t (negb (pretty =? 0)) 0)))).
  { split; [exact FR|]. split; [exact BK|]. split; [exact OLD|]. split; [exact NB|].
    split; [exact REC'|]. split; [exact TW'|]. split; [exact TI1|]. split; [exact RA' | exact IN']. }
  destruct (@ra_after fx rc B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X
    Lam peak cnt bnd q want len cap txt (TV_K t) regs1 L' A' mem' md' b1 _ cap1 _
    (tx_fold F bnd len cap (tv_calls t (negb (pretty =? 0)) 0))
    ENT INV RT HARN SP1 ltac:(lia) ltac:(lia) TXR RESJ) as (INV' & RT' & HARN').
  exact (K L' A' regs' mem' md' b1 cap1 RP HCJ INV' RT' HARN').
Qed.

End C.
