(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: RELOCATED to the #102 pins (image A' = asan 1be0f53d96cb, twin bff8519bbe3e) from commit preset-tree-at-2026-10-29T17-46-55Z.tsv (sha256 7c0bbc66e4a5; internal record) (old-pin image A) by the relocation script, the internal file reloc_A2.py (named with its outputs in the commit that added this line): every code address moved by symbol + offset (the internal file reloc_A2.out), the walk's functions checked by bytecmp 1480ca2faea0 + a target pass (the internal file measure_A2.out); data addresses come by name from int102's A' tables; ARXs_cf / ARmcf follow preset-tree-at-2026-10-29T18-16-07Z.tsv (sha256 4c721de248fd; internal record) (xs_placed is ARmcf's field amc_xs_placed). *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A' (#102 asan, pin 1be0f53d96cb, twin bff8519bbe3e): the fields of
   the Record wrap_free_walk_cf (lib/Reusable/YGcfMallocCompose.v:338-367) at
     segs := tfibsegs, atpD := 1 (asan_free's alloc_type, FROM_MALLOC), ARX := WrapMallocARetG.ARXq_A B (round 6),
     K := K_A (WrapFreeAK.v),
   from the walk pieces: the entry facts (WrapFreeASeed.v), the call segment (WrapFreeACall.v, __wrap_free 0x53734 to
   Deallocate's entry 0x322a4), the allocator relation at finit_cf S after the internal allocator's set-up
   (WrapFreeAInit.v) and the return segment (WrapFreeARet.v, 0x538e8 to the wrapper's ret).
   call_post: the post of field wf_call from the call segment's end state. The image facts are premises:
   TfibSyms B. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0q YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0qcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG DeallocG RGtop YGcfRmodel YG03cf YAkMemnorm YGcfBlockRange.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfDIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ADIfaceImgA AFff AFg3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import WrapFreeAStmt WrapFreeAK CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require WrapFreeAEnv WrapFreeAInit WrapFreeASeed WrapFreeACall WrapFreeARet WrapAKit AB13 AFfy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase YGcfXs YGcfMallocComposeRh YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXsMapped.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The bytes a run changed are writable or above every segment: memnorm survives (YAkMemnorm.v:85-101's argument). *)
Lemma memnorm_frame_w : forall segs (m m' : word -> option byte) (X : Z -> Prop),
  (forall a, X a \/ ~ X a) ->
  YAkMemnorm.memnorm segs m ->
  (forall x : word, ~ X (bv_unsigned x) -> m' x = m x) ->
  (forall x : word, X (bv_unsigned x) -> m' x <> None ->
     wview segs m x <> None \/ (find_segment segs (bv_unsigned x) 1 = None /\ bv_unsigned x < TASK_SIZE)) ->
  YAkMemnorm.memnorm segs m'.
Proof.
intros segs m m' X XD (Hi & Ht) Hout Hin. split; intros x b E.
- destruct (XD (bv_unsigned x)) as [Hx|Hx]; [|rewrite (Hout x Hx) in E; exact (Hi x b E)].
  destruct (Hin x Hx ltac:(rewrite E; discriminate)) as [W|[N _]].
  + unfold wview in W. revert W. destruct (m x) as [b0|] eqn:E0; intros W; [exact (Hi x b0 E0)|].
    unfold YAkMemnorm.ro_addr. revert W.
    destruct (find_segment segs (bv_unsigned x) 1) as [seg|]; intros W; [|exfalso; exact (W eq_refl)].
    revert W. destruct (seg_writable seg); intros W; [reflexivity | exfalso; exact (W eq_refl)].
  + unfold YAkMemnorm.ro_addr. rewrite N. reflexivity.
- destruct (XD (bv_unsigned x)) as [Hx|Hx]; [|rewrite (Hout x Hx) in E; exact (Ht x b E)].
  destruct (Hin x Hx ltac:(rewrite E; discriminate)) as [W|[_ T]]; [|right; exact T].
  unfold wview in W. revert W. destruct (m x) as [b0|] eqn:E0; intros W; [exact (Ht x b0 E0)|].
  revert W. destruct (find_segment segs (bv_unsigned x) 1) as [seg|]; intros W; [left; discriminate | exfalso; exact (W eq_refl)].
Qed.

(* One byte of a val_mem on the view (AFg3.v:268-273, stated here without that file's Section variables). *)
Lemma val_mem_aview_A : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section k.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
(* The record's call-site relation ARX, generic (the WrapMallocARetG.v method), so a change of the record's
   ARX re-instantiates the walk: HXI builds ARX at Deallocate's entry from the caller's acall_pre_cf and ARcf at
   finit_cf S over the entry memory; HXA / HXF are WrapFreeARet.wf_ret_gen's. *)
Variable ARX : ARXh_t tfibsegs.
Hypothesis HXI : forall ly S Hp W regs mem md ch memD mat,
  acall_pre_cf tfibsegs B ly S Hp W regs mem md ch ->
  ARcf tfibsegs B ly (finit_cf S) Hp W memD (with_vm_backing (m_vm_lazy md) mat md) ->
  ARX Hp TFIB_INST ly (finit_cf S) W memD (with_vm_backing (m_vm_lazy md) mat md).
Hypothesis HXA : ARX_ARcf tfibsegs B ARX.
Hypothesis HXF : forall Hp inst ly S W mem md mem' mat,
  ARX Hp inst ly S W mem md ->
  (forall a, aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARX Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).

(* The freed pointer is below 2 ^ 47: NULL, or a live block's user pointer (YGcfBlockRange.v:31). *)
Lemma p_below_47 : forall ly S Hp W mem md p n, ARcf tfibsegs B ly S Hp W mem md ->
  (p = PNull \/ In (p, n) (blocks S)) -> 0 <= sptr_addr B ly p < 2 ^ 47.
Proof.
intros ly S Hp W mem md p n HAR [->|Hb]; [cbn; lia|].
destruct (YGcfBlockRange.block_user_range_cf tfibsegs B ly S Hp W mem md p n HAR Hb) as (Hn & R).
pose proof (req_size_bounds n Hn) as (_ & R1 & _). ceil.
unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* The internal allocator's zone and the flag cell are owned (the owned static table covers them, by value). *)
Lemma izone_owned : forall ly S Hp rd a, ARmcf B ly S Hp rd -> WrapFreeAEnv.IZONE a -> aowned B ly S a.
Proof.
intros ly S Hp rd a M X. apply (own_static_cf B ly S Hp rd a M). rewrite (ts_owned _ TB).
unfold WrapFreeAEnv.IZONE in X.
destruct X as [X|X]; refine (ADIfaceImgA.covers_b_Exists _ _ _ _ a X); clear; vm_compute; reflexivity.
Qed.

(* T + t_unwinding is owned (the thread object is a core extent). *)
Lemma unw_owned : forall ly S Hp rd a, ARmcf B ly S Hp rd -> ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1 -> aowned B ly S a.
Proof.
intros ly S Hp rd a M X. eapply (own_core_cf B ly S Hp rd (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|].
cbn [fst snd]. unfold t_unwinding, kThreadObjSize in *. lia.
Qed.

(* Field wf_call's post from the call segment's end state (WrapFreeACall.at_DEALLOC, unpacked) and the allocator
   relation at finit_cf S over the end memory. *)
Lemma call_post : forall ly S Hp W regs mem md p n ch regsD memD mat,
  fentry_cf tfibsegs B ly S Hp W regs mem md p n ch -> rpreD_free_cf B (finit_cf S) n -> ly_bot ly + 2128 < spZ regs ->
  ARcf tfibsegs B ly (finit_cf S) Hp W memD (with_vm_backing (m_vm_lazy md) mat md) ->
  getr regsD 1 = w64 0x538e8 -> getr regsD 2 = w64 (spZ regs - 2128) ->
  getr regsD 10 = w64 TFIB_INST -> getr regsD 11 = getr regs 10 -> getr regsD 12 = w64 0 -> getr regsD 13 = w64 0 ->
  getr regsD 14 = w64 (spZ regs - 2128) -> getr regsD 15 = w64 1 ->
  getr regsD 3 = getr regs 3 -> getr regsD 4 = w64 TFIB_TP ->
  (forall r : Z, 22 <= r <= 27 -> getr regsD (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  WrapFreeAEnv.MEQI W ly regs mem memD ->
  (forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) memD a) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 2128) 8 (spZ regs - 2112) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 2120) 8 (WrapFreeAEnv.LENv ly regs ch) ->
  (forall i, (i < length (WrapFreeAEnv.tr ly regs ch))%nat ->
    val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 2112 + 8 * Z.of_nat i) 8 (nth i (WrapFreeAEnv.tr ly regs ch) 0)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
  free_dpre_cf tfibsegs B 1 ARX Hp TFIB_INST (spZ regs - 2128) (spZ regs - 2112) ly (finit_cf S) W
    regsD memD (with_vm_backing (m_vm_lazy md) mat md) p n (ftr_cf B ly regs ch) /\
  same_io md (with_vm_backing (m_vm_lazy md) mat md) /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
  YGcfMallocComposeKeep.ikeep_mn_cf tfibsegs B ly S regs W mem W memD /\ errno_kept_cf B mem memD /\
  K_A ly S Hp W regs mem md p n ch W regsD memD (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S Hp W regs mem md p n ch regsD memD mat ENT RP BOT AR R1 R2 R10 R11 R12 R13 R14 R15 R3 R4 RS MQ PRES
  OBJ0 OBJ1 TRA V1 V8 V9 V18 V19 V20 V21.
destruct ENT as (PRE & Hpn & H10 & NIN & Htr).
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & QM & SL & ER & AB & BR & XM).
pose proof (proj1 HAR) as M.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (WrapAKit.img_cover_of_ledger_cf ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (WrapAKit.HIGH_cf ly LO IMG) as (_ & _ & _ & _ & ZT & _).
pose proof (WrapAKit.cf_unwinding_val B ly S Hp (w_H W) mem M) as UNW0.
unfold spZ in Hal, Hlo, Hbot, Hhi, HPRES, BOT, R2, R14, PRES, OBJ0, OBJ1, TRA, V1, V8, V9, V18, V19, V20, V21.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (SA : bv_unsigned (getr regsD 2) = sp0 - 2128)
  by (rewrite R2; unfold w64; apply unsigned_lit_small; clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
assert (TRE : ftr_cf B ly regs ch = WrapFreeAEnv.tr ly regs ch).
{ unfold ftr_cf, WrapFreeAEnv.tr. rewrite (ts_code B TB). reflexivity. }
assert (LEN : (1 <= length (WrapFreeAEnv.tr ly regs ch) <= 30)%nat).
{ unfold WrapFreeAEnv.tr, call_trace. destruct (frame0_ok ly regs); [apply unwind_of_chain_length | cbn; lia]. }
destruct MQ as [MEQ IALP].
(* the bytes the segment kept: off the stack window, T + t_unwinding and the internal allocator's zone *)
assert (KEEP : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
  ~ WrapFreeAEnv.IZONE (bv_unsigned x) -> memD x = mem x).
{ intros x X1 X2 X3. apply MEQ; [|exact X3]. unfold WrapFreeAEnv.WIN. fold sp0. intros [Y|Y]; [exact (X1 Y) | exact (X2 Y)]. }
assert (KEEPO : forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> memD x = mem x).
{ intros x NO NS. apply KEEP.
  - intros X. apply NS. left. unfold spZ. fold sp0. exact X.
  - intros X. exact (NO (unw_owned ly S Hp _ _ M X)).
  - intros X. exact (NO (izone_owned ly S Hp _ _ M X)). }
split.
{ unfold free_dpre_cf, DeallocG.dealloc_pre.
  split.
  { exact (HXI ly S Hp W regs mem md ch memD mat PRE AR). }
  split; [exact RP|].
  split. { rewrite R1. apply YK0s.ret_ok_even. reflexivity. }
  split. { unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  unfold spZ. rewrite SA. fold sp0. unfold DeallocG.DFSTACK_G.
  split. { replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
  split. { clear - Hlo. unfold ASTACK in *. lia. }
  split. { clear - BOT. lia. }
  split. { lia. }
  split. { intros a Ha. apply PRES. clear - Ha. unfold ASTACK. lia. }
  split. { rewrite R3. exact Hgp. }
  split. { rewrite R4, (ts_tp B TB). reflexivity. }
  split. { exact R10. }
  split. { rewrite R11. exact H10. }
  split. { exact R12. }
  split. { exact R13. }
  split. { exact R14. }
  split. { exact R15. }
  split. { lia. }
  split. { clear - Hhi. lia. }
  split. { clear - Hal. replace (sp0 - 2128) with (sp0 + (-266) * 8) by lia. rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [lia | exact Hal]. }
  split. { lia. }
  split. { clear - Hhi. lia. }
  split. { clear - Hal. replace (sp0 - 2112) with (sp0 + (-264) * 8) by lia. rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [lia | exact Hal]. }
  rewrite TRE.
  split. { exact LEN. }
  split. { exact OBJ0. }
  split. { eapply val_mem_addr; [exact OBJ1 | unfold WrapFreeAEnv.LENv; lia]. }
  split. { exact TRA. }
  split. { rewrite <- TRE. exact Htr. }
  split. { exact Hpn. }
  exact NIN. }
split. { apply AFg3.same_io_wvb. }
split. { unfold RGtop.rin, spZ. rewrite SA. fold sp0. unfold DeallocG.DFSTACK_G, ASTACK. lia. }
split.
{ split; [|split].
  - intros a Ha NO NS. apply aview_same. apply KEEPO; rewrite unsigned_lit_small by exact Ha; assumption.
  - exact KEEPO.
  - intros MN. apply (memnorm_frame_w tfibsegs mem memD
      (fun a => (sp0 - ASTACK <= a < sp0) \/ (ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1) \/ WrapFreeAEnv.IZONE a)).
    + intros a. unfold WrapFreeAEnv.IZONE. lia.
    + exact MN.
    + intros x X. apply KEEP; intros Y; apply X; tauto.
    + intros x X _. pose proof (u64_range x) as Ux.
      destruct X as [X|[X|X]].
      * right. split; [apply tfib_find_segment_none_high; clear - X Hlo T7; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|].
        clear - X Hhi T4. unfold kHighMemEnd in *. unfold TASK_SIZE. lia.
      * left. assert (Ex : x = Z_to_bv 64 (ly_T ly + t_unwinding)).
        { replace (ly_T ly + t_unwinding) with (bv_unsigned x) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (OFF : off_img (ly_T ly + t_unwinding)) by (apply (zone3_off_img _ _ _ ZT); unfold t_unwinding, kThreadObjSize; lia).
        pose proof (seg_rom_none_off _ OFF) as SR. rewrite <- Ex in SR.
        pose proof (UNW0 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U. rewrite <- Ex in U.
        unfold wview. destruct (w_H W x); [rewrite SR in U; discriminate|].
        destruct (mem x); [discriminate | rewrite SR in U; discriminate].
      * left. pose proof (AFff.rw_writable mem (bv_unsigned x)) as RW. unfold writable_at in RW.
        rewrite Z_to_bv_bv_unsigned in RW. apply RW. clear - X. unfold WrapFreeAEnv.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in X. lia. }
split.
{ intros i Hi. rewrite (ts_errno B TB). apply KEEP; unfold w64; rewrite unsigned_lit_small by (unfold TFIB_ERRNO; lia).
  - clear - Hi Hlo T7. unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *. lia.
  - clear - Hi ZT. destruct ZT as (Z0 & Z1 & Z2). unfold zone3cases in Z2. intros [C1 C2].
    unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END, t_unwinding, kThreadObjSize, kHighMemBeg in *.
    destruct Z2 as [Z2|[Z2|Z2]]; lia.
  - clear - Hi. unfold WrapFreeAEnv.IZONE, TFIB_ERRNO, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia. }
unfold K_A, spZ, raZ, s0Z. fold sp0.
split; [reflexivity|]. split; [exact R2|]. split; [exact R1|]. split; [exact R3|].
split; [rewrite R4, Htp, (ts_tp B TB); reflexivity|]. split; [exact RS|].
split; [exact V1|]. split; [exact V8|]. split; [exact V9|].
split; [exact V18|]. split; [exact V19|]. split; [exact V20|]. split; [exact V21|]. exact PRES.
Qed.

(* The constant cells lie off the call segment's windows and off the internal allocator's zone (AFg3.v:274-304,
   over WrapFreeAEnv's windows). *)
Lemma const_out_A : forall ly W regs mem ch p ii, WrapFreeAEnv.free_hyps W ly regs mem ch p ii ->
  ly_tsd ly = TFIB_TSD ->
  Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ WrapFreeAEnv.WIN ly regs (aeval B ly (c_at c) + i) /\ ~ WrapFreeAEnv.IZONE (aeval B ly (c_at c) + i) /\
  0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
intros ly W regs mem ch p ii FH HTSD.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (AFfy.Tfib_const_loc ly) c Hc) as K. unfold AFfy.const_loc_ok in K.
assert (LOW : forall a, AFfy.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true ->
  ~ WrapFreeAEnv.WIN ly regs (a + i) /\ ~ WrapFreeAEnv.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold AFfy.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
  assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/ (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
    (SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
  clear L. unfold WrapFreeAEnv.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *.
  change (65536 / 8) with 8192 in R. let itop := eval vm_compute in YImgTop.IMG_TOP in let itop8 := eval vm_compute in (itop / 8) in change (itop / 8) with itop8 in R.
  split; [|lia]. destruct R as [R|[R|[R|R]]].
  1-3: apply (WrapFreeAEnv.notWIN_img W ly regs mem ch p ii FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia.
  apply (WrapFreeAEnv.notWIN_shb W ly regs mem ch p ii FH); unfold kLowShadowBeg, kHighMemBeg; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (WrapFreeAEnv.LYB W ly regs mem ch p ii FH) as (LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
  split; [apply (WrapFreeAEnv.notWIN_Thead W ly regs mem ch p ii FH); lia|].
  unfold WrapFreeAEnv.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- pose proof (WrapFreeAEnv.LYB W ly regs mem ch p ii FH) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
  split; [apply (WrapFreeAEnv.notWIN_C W ly regs mem ch p ii FH); lia|].
  unfold WrapFreeAEnv.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (WrapFreeAEnv.LYBD W ly regs mem ch p ii FH) as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2.
  split; [apply (WrapFreeAEnv.notWIN_D W ly regs mem ch p ii FH); lia|].
  unfold WrapFreeAEnv.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

(* ARcf at finit_cf S over the call segment's end memory: WrapFreeAInit.init_ARcf with the facts AFg3.v:314-372's FINH
   reads off the segment's frame (MEQI), the stack window and T + t_unwinding. *)
Lemma arcf_at_D : forall ly S Hp W regs mem md ch p mat memD,
  acall_pre_cf tfibsegs B ly S Hp W regs mem md ch ->
  WrapFreeAEnv.free_hyps W ly regs mem ch p (st_internal_inited S) ->
  WrapFreeAEnv.MEQI W ly regs mem memD ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (ly_T ly + t_unwinding) 1 0 ->
  (forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) memD a) ->
  ARcf tfibsegs B ly (finit_cf S) Hp W memD (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S Hp W regs mem md ch p mat memD PRE FH MEQ' UNW PRES'.
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & _).
pose proof (proj1 HAR) as M.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (amc_tsd _ _ _ _ _ M); exact (ts_tsd B TB)).
pose proof (WrapFreeAEnv.fh_IMG _ _ _ _ _ _ _ FH) as IMG.
unfold spZ in Hlo, Hhi, PRES'. set (sp0 := bv_unsigned (getr regs 2)) in *.
set (rd := aview tfibsegs (w_H W) mem). set (rd' := aview tfibsegs (w_H W) memD).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (HSP' : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly) by lia.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ WrapFreeAInit.D B ly ASTACK sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (proj1 MEQ' (Z_to_bv 64 a)); rewrite unsigned_lit_small by exact Ha.
  - unfold WrapFreeAEnv.WIN. fold sp0. intros [X|X]; apply ND; [right; left; exact X | left; exact X].
  - intros X. apply ND. right; right. unfold WrapFreeAEnv.IZONE in X. unfold WrapFreeAInit.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). exact X. }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
  destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (memD x); discriminate|].
  destruct (memD x) as [|] eqn:E'; [discriminate|]. clear HN.
  destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
  set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (NIMG : ~ (0x10000 <= a' < 0x600000)).
  { intros X. apply (AB13.tfib_rom_all a' X). rewrite Ex. exact ROM. }
  assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
  { intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
  destruct (EM (sp0 - ASTACK) sp0 a') as [C1|C1]. { exact (PRX memD (PRES' a' C1) E'). }
  destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) a') as [C2|C2].
  { pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
    replace (ly_T ly + t_unwinding) with a' in U by lia. rewrite Ex, Hx, E', ROM in U. discriminate. }
  destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [C4|C4]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in C4; lia|].
  destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [C5|C5]; [apply NIMG; unfold TFIB_IAL_FLAG in C5; lia|].
  rewrite (proj1 MEQ' x) in E'; [congruence | |].
  - unfold WrapFreeAEnv.WIN. fold sp0. intros [X|X]; [apply C1 | apply C2]; exact X.
  - unfold WrapFreeAEnv.IZONE. tauto. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> memD (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
  unfold w64 in *. set (x := Z_to_bv 64 a) in *.
  assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
  assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
  assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate).
  assert (C1 : ~ (sp0 - ASTACK <= a < sp0)) by (intros C1; exact (PRX memD (PRES' a C1))).
  assert (C2 : ~ (ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1)).
  { intros C2. pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
    replace (ly_T ly + t_unwinding) with a in U by lia.
    rewrite (seg_rom_none_high a ltac:(clear - Ha; unfold TFIB_IMG_END, kLowShadowBeg, kHighShadowEnd in *; lia)) in U. fold x in U. rewrite Hx in U. discriminate. }
  apply (proj1 MEQ' x); rewrite Ux.
  - unfold WrapFreeAEnv.WIN. fold sp0. intros [X|X]; [apply C1 | apply C2]; exact X.
  - unfold WrapFreeAEnv.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia. }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (val_mem_aview_A _ _ _ _ _ 0 UNW ltac:(lia)). }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (finit_cf S)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ destruct MEQ' as [_ IP]. unfold WrapFreeAEnv.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
  unfold ialloc_cells, ialloc_zero. change (st_internal_inited (finit_cf S)) with true. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
  subst rd'. split.
  - apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_A _ _ _ _ _ 0 I1). lia. }
    apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_A _ _ _ _ _ 0 I2). lia. }
    apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
      intros kk Hkk. exact (val_mem_aview_A _ _ _ _ _ kk I3 Hkk). }
    apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
      replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
      intros kk Hkk. exact (val_mem_aview_A _ _ _ _ _ kk I4 Hkk). }
  - assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> aview tfibsegs (w_H W) memD a0 = Some 0).
    { intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (amc_const B ly S Hp _ M) c Hc)|].
  intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) (const_out_A ly W regs mem ch p _ FH HTSD) c Hc i Hi) as (X1 & X2 & X3). apply aview_same.
  apply (proj1 MEQ' (Z_to_bv 64 _)); rewrite unsigned_lit_small by exact X3; [exact X1 | exact X2]. }
exact (WrapFreeAInit.init_ARcf B TB ly S Hp W mem md memD mat ASTACK sp0 HAR IMG ltac:(unfold ASTACK; lia) HSP' AG VIS NEW_unw IAL CONST' HSK).
Qed.
(* Field F1 (wf_call) at image A, in its FIX form (WrapFreeAStmt.v: the named premise ly_bot ly + 2128 < spZ regs, 2128
   = ___interceptor_free's frame). *)
Theorem wf_call_FIX_A : cf_pc_deallocate = 0x322a4 ->
  wf_call_stmt_FIX tfibsegs B 1 2128 ARX K_A.
Proof.
intros Hpc ly S Hp W regs mem md p n ch ENT RP BOT.
pose proof ENT as (PRE & Hpn & H10 & NIN & Htr).
pose proof (p_below_47 ly S Hp W mem md p n (proj1 PRE) Hpn) as P47.
pose proof (WrapFreeASeed.FH_ok_cf B TB ly S Hp W regs mem md ch (sptr_addr B ly p) PRE H10 P47) as FH.
rewrite (ts_code B TB). cbn [pc_wrap_free Tfib_code].
unfold cfg_at. rewrite <- (AFg3.wvb_self md) at 1.
eapply SRr_mono; [exact (WrapFreeACall.seg_call W ly regs mem md ch (sptr_addr B ly p) (st_internal_inited S) (m_vm_materialized md) FH)|].
intros W' c' _ (-> & regsD & memD & mat & -> & R1 & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R3 & R4 & RS & MQ & UNW & PRES
  & OBJ0 & OBJ1 & TRA & V1 & V8 & V9 & V18 & V19 & V20 & V21).
pose proof (arcf_at_D ly S Hp W regs mem md ch (sptr_addr B ly p) mat memD PRE FH MQ UNW PRES) as ARD.
exists TFIB_INST, (spZ regs - 2128), (spZ regs - 2112), regsD, memD, (with_vm_backing (m_vm_lazy md) mat md).
split; [unfold cfg_at; rewrite Hpc; reflexivity|].
exact (call_post ly S Hp W regs mem md p n ch regsD memD mat ENT RP BOT ARD R1 R2 R10 R11 R12 R13 R14 R15 R3 R4 RS MQ PRES
  OBJ0 OBJ1 TRA V1 V8 V9 V18 V19 V20 V21).
Qed.
(* The record at image A, from the two fields, once the caller's stack premise gives the room below sp that
   Deallocate's ly_bot conjunct needs (BOTP, acall_pre_cf's conjunct `ly_bot ly + ACALL_PREFIX < spZ regs`
   with ACALL_PREFIX = 4096; the walk uses 2128 of it; the closed forms below take it from acall_pre_cf). The constructor checks
   both fields against YGcfMallocCompose.v:342 / :352's text. *)
Theorem wrap_free_walk_keep_A_of_bot : cf_pc_deallocate = 0x322a4 ->
  (forall ly S Hp W regs mem md ch, acall_pre_cf tfibsegs B ly S Hp W regs mem md ch -> ly_bot ly + 4096 < spZ regs) ->
  YGcfMallocComposeKeep.wrap_free_walk_keep_cf tfibsegs B 1 ARX K_A.
Proof.
intros Hpc BOTP. constructor.
- intros ly S Hp W regs mem md p n ch ENT RP.
  pose proof (BOTP ly S Hp W regs mem md ch (proj1 ENT)) as BT.
  exact (wf_call_FIX_A Hpc ly S Hp W regs mem md p n ch ENT RP ltac:(lia)).
- exact (WrapFreeARet.wf_ret_gen B TB ARX HXA HXF).
Qed.

Theorem wrap_free_walk_A_of_bot : cf_pc_deallocate = 0x322a4 ->
  (forall ly S Hp W regs mem md ch, acall_pre_cf tfibsegs B ly S Hp W regs mem md ch -> ly_bot ly + 4096 < spZ regs) ->
  wrap_free_walk_cf tfibsegs B 1 ARX K_A.
Proof.
intros Hpc BOTP. exact (YGcfMallocComposeKeep.wrap_free_walk_cf_of_keep tfibsegs B 1 ARX K_A (wrap_free_walk_keep_A_of_bot Hpc BOTP)).
Qed.

(* The PRIMED record (lib/Reusable/YGcfMallocComposeRh.v): the same call field, the return field at the primed
   Deallocate post (WrapFreeARet.wf_ret_gen_rh). *)
Theorem wrap_free_walk_keep_rh_A_of_bot : cf_pc_deallocate = 0x322a4 ->
  (forall ly S Hp W regs mem md ch, acall_pre_cf tfibsegs B ly S Hp W regs mem md ch -> ly_bot ly + 4096 < spZ regs) ->
  YGcfMallocComposeKeep.wrap_free_walk_keep_cf_rh tfibsegs B 1 ARX K_A.
Proof.
intros Hpc BOTP. destruct (wrap_free_walk_keep_A_of_bot Hpc BOTP) as [WC _].
constructor; [exact WC | exact (WrapFreeARet.wf_ret_gen_keep_rh B TB ARX HXA HXF)].
Qed.

Theorem wrap_free_walk_rh_A_of_bot : cf_pc_deallocate = 0x322a4 ->
  (forall ly S Hp W regs mem md ch, acall_pre_cf tfibsegs B ly S Hp W regs mem md ch -> ly_bot ly + 4096 < spZ regs) ->
  YGcfMallocComposeRh.wrap_free_walk_cf_rh tfibsegs B 1 ARX K_A.
Proof.
intros Hpc BOTP. destruct (wrap_free_walk_A_of_bot Hpc BOTP) as [WC _].
constructor; [exact WC | exact (WrapFreeARet.wf_ret_gen_rh B TB ARX HXA HXF)].
Qed.
End k.

(* The call-site relation of the record: YGcfInstBase.ARXq_cf at image A (AImgA.AImg_A) and
   IOK := (fun i => i = as_inst B).  It meets HXI: IOK by ts_inst, ARcf given, xs_mapped_cf from ARcf
   (YGcfXs.ARcf_xsm), qtight from qmeter_cf's first conjunct; finit_cf (set_internal_inited) changes no field the
   last two read. *)
Definition ARXq_A (B : asyms) : ARXh_t tfibsegs :=
  YGcfInstBase.ARXq_cf (IM := AImgA.AImg_A) B (fun i => i = as_inst B).

Lemma ARXq_HXI : forall B, TfibSyms B -> forall ly S Hp W regs mem md ch memD mat,
  acall_pre_cf tfibsegs B ly S Hp W regs mem md ch ->
  ARcf tfibsegs B ly (finit_cf S) Hp W memD (with_vm_backing (m_vm_lazy md) mat md) ->
  ARXq_A B Hp TFIB_INST ly (finit_cf S) W memD (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros B TB ly S Hp W regs mem md ch memD mat PRE AR.
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QM & _).
unfold ARXq_A, YGcfInstBase.ARXq_cf, YGcfInstBase.ARX_cf.
split; [split; [symmetry; exact (ts_inst B TB)|split; [exact AR|]]|].
- eapply YGcfXs.ARcf_xsm; exact AR.
- exact (proj1 QM).
Qed.

Lemma ARXq_A_HXA : forall B, YGcfMallocCompose.ARX_ARcf tfibsegs B (ARXq_A B).
Proof. intros B Hp inst ly S W mem md H. exact (proj1 (proj2 (proj1 H))). Qed.

Lemma ARXq_A_HXF : forall B Hp inst ly S W mem md mem' mat,
  ARXq_A B Hp inst ly S W mem md ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARXq_A B Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros B Hp inst ly S W mem md mem' mat ((I & _ & XM) & Q) A.
exact (conj (conj I (conj A (xs_mapped_cf_wvb ly S md (m_vm_lazy md) mat XM))) Q).
Qed.

End c.

(* At image A's generated CfImg instance (CfImgA.v:12, cf_pc_deallocate := 0x322a4 by symbol) and the call-site
   relation ARXq_A: the record with the image facts TfibSyms B and the caller's room below sp (BOTP) as its premises. *)
Section ia. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_A.
Theorem wrap_free_walk_A : forall B, TfibSyms B ->
  (forall ly S Hp W regs mem md ch, acall_pre_cf tfibsegs B ly S Hp W regs mem md ch -> ly_bot ly + 4096 < spZ regs) ->
  wrap_free_walk_cf tfibsegs B 1 (ARXq_A B) K_A.
Proof.
intros B TB BOTP.
exact (wrap_free_walk_A_of_bot B TB (ARXq_A B) (ARXq_HXI B TB) (ARXq_A_HXA B)
  (fun Hp inst ly S W mem md mem' mat X _ A => ARXq_A_HXF B Hp inst ly S W mem md mem' mat X A)
  eq_refl BOTP).
Qed.

(* The stack premise follows from acall_pre_cf's `ly_bot ly + ACALL_PREFIX < spZ regs` (ACALL_PREFIX = 4096,
   YG0d.v:21): the closed records, premises TfibSyms B only. *)
Theorem wrap_free_walk_A_c : forall B, TfibSyms B -> wrap_free_walk_cf tfibsegs B 1 (ARXq_A B) K_A.
Proof.
intros B TB. apply (wrap_free_walk_A B TB).
intros ly S Hp W regs mem md ch PRE. pose proof PRE as (_ & _ & _ & _ & BOT & _). exact BOT.
Qed.

Theorem wrap_free_walk_rh_A : forall B, TfibSyms B -> YGcfMallocComposeRh.wrap_free_walk_cf_rh tfibsegs B 1 (ARXq_A B) K_A.
Proof.
intros B TB.
exact (wrap_free_walk_rh_A_of_bot B TB (ARXq_A B) (ARXq_HXI B TB) (ARXq_A_HXA B)
  (fun Hp inst ly S W mem md mem' mat X _ A => ARXq_A_HXF B Hp inst ly S W mem md mem' mat X A)
  eq_refl (fun ly S Hp W regs mem md ch PRE => proj1 (proj2 (proj2 (proj2 (proj2 PRE)))))).
Qed.
Theorem wrap_free_walk_keep_A : forall B, TfibSyms B ->
  YGcfMallocComposeKeep.wrap_free_walk_keep_cf tfibsegs B 1 (ARXq_A B) K_A.
Proof.
intros B TB.
exact (wrap_free_walk_keep_A_of_bot B TB (ARXq_A B) (ARXq_HXI B TB) (ARXq_A_HXA B)
  (fun Hp inst ly S W mem md mem' mat X _ A => ARXq_A_HXF B Hp inst ly S W mem md mem' mat X A)
  eq_refl (fun ly S Hp W regs mem md ch PRE => proj1 (proj2 (proj2 (proj2 (proj2 PRE)))))).
Qed.
Theorem wrap_free_walk_keep_rh_A : forall B, TfibSyms B ->
  YGcfMallocComposeKeep.wrap_free_walk_keep_cf_rh tfibsegs B 1 (ARXq_A B) K_A.
Proof.
intros B TB.
exact (wrap_free_walk_keep_rh_A_of_bot B TB (ARXq_A B) (ARXq_HXI B TB) (ARXq_A_HXA B)
  (fun Hp inst ly S W mem md mem' mat X _ A => ARXq_A_HXF B Hp inst ly S W mem md mem' mat X A)
  eq_refl (fun ly S Hp W regs mem md ch PRE => proj1 (proj2 (proj2 (proj2 (proj2 PRE)))))).
Qed.
End ia.
