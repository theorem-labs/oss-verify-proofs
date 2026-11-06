From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit SlotDefs LLVMFuzzerTestOneInput_c memchr_c memcpy_c fuzz_alloc_live_c fuzz_alloc_peak_reset_c fuzz_alloc_peak_c check_bounded_alloc_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import KindBGlue SlotInv SlotStep SlotStepA SlotStepB SlotStepC SlotStepD SlotStepE SlotStepF SlotStepG check_no_overread_c preset_base64_decode_c check_as_written_c check_round_trip_c check_reject_clean_starved_c fuzz_free_c FrameFactsCG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The slot contract of entry_fn (plain, 0x1331c) in the cut-free universe: the step lemmas SlotStepA..SlotStepG
   chained, from the slot's start state built out of lib_pre_x and the frame facts frame_facts_cg (FrameFactsCG.v:
   the agreement room and the cut-free allocator contracts); the slot contract is the frame's lib_contract_cg
   (crealizes). The contracts of the functions entry_fn calls are the premise slot_callees_plain; it holds for
   every FP state, as check_4 returns in a new one. *)

Definition slot_premise_cg : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_cg B API LS SH SK empty ->
    forall (rc : RunCeil) (fx : FPState) (j : nat) (ra : Z), (j < 4)%nat -> ra mod 2 = 0 ->
      SlotAgree.lib_contract_cg (fx := fx) (rc := rc) (LS := LS) (SH := SH) (SK := SK) B (API rc)
        omx_G frame_RELRO (omx_GI B) j FUZZ_STATE_ENTRY ra empty FUZZ_STATE_STK.

Definition slot_callees {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  memchr_contract /\ memcpy_contract /\ fuzz_alloc_live_contract /\ fuzz_alloc_peak_reset_contract /\
  fuzz_alloc_peak_contract /\ check_bounded_alloc_contract /\ check_reject_clean_contract /\
  check_no_overread_contract B API /\ preset_base64_decode_contract B API sb_form /\ check_as_written_contract B API /\
  check_round_trip_contract B API /\ check_reject_clean_starved_contract B API /\ fuzz_free_contract B API sb_form.

Definition slot_callees_plain : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_cg B API LS SH SK empty -> forall (rc : RunCeil) (fx : FPState), @slot_callees fx rc B (API rc).

Section Asm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma omx_free : ms_segs B = rsegs -> AllocExtra B MR ->
  (forall L A mem md a, MR L A mem md -> in_globals frame_G a -> ~ owned B L A a) ->
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
  globals_free B API omx_G.
Proof.
  intros HSEG AX Hown Hfg a Ha.
  assert (Hr : 0x33450 <= a < 0x33468 \/ 0x231e0 <= a < 0x231e8).
  { unfold in_globals, omx_G, Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL in Ha.
    destruct Ha as (lo & len & Hin & Hb). cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia. }
  assert (Hf : in_globals frame_G a).
  { unfold in_globals, frame_G. destruct Hr as [Hr|Hr].
    - exists 0x33450, 24. split; [right; left; reflexivity | lia].
    - exists 0x231e0, 8. split; [left; reflexivity | lia]. }
  destruct (Hfg a Hf) as (Himg & _ & _ & Herr).
  assert (HIL : img_low B).
  { apply (img_low_of_check B 0x55000); [unfold img_check; rewrite HSEG; vm_compute; reflexivity|].
    pose proof alloc_ceiling_val. lia. }
  split; [exact Himg|]. split; [exact (proj1 HIL a Himg)|]. split.
  { assert (C : forallb (fun i => match find_segment rsegs (0x33450 + Z.of_nat i) 1 with
                                  | Some s => seg_writable s | None => false end) (seq 0 24) = true /\
                forallb (fun i => match find_segment rsegs (0x231e0 + Z.of_nat i) 1 with
                                  | Some s => seg_writable s | None => false end) (seq 0 8) = true)
      by (split; vm_compute; reflexivity).
    destruct C as (C1 & C2). rewrite forallb_forall in C1, C2. rewrite HSEG.
    destruct Hr as [Hr|Hr].
    - specialize (C1 (Z.to_nat (a - 0x33450)) ltac:(apply in_seq; lia)).
      replace (0x33450 + Z.of_nat (Z.to_nat (a - 0x33450))) with a in C1 by lia.
      destruct (find_segment rsegs a 1) as [s|]; [exists s; split; [reflexivity | exact C1] | discriminate].
    - specialize (C2 (Z.to_nat (a - 0x231e0)) ltac:(apply in_seq; lia)).
      replace (0x231e0 + Z.of_nat (Z.to_nat (a - 0x231e0))) with a in C2 by lia.
      destruct (find_segment rsegs a 1) as [s|]; [exists s; split; [reflexivity | exact C2] | discriminate]. }
  split; [exact Herr|].
  intros L A mem md HM. split; [exact (Hown L A mem md a HM Hf)|].
  intros p n Hp Hpa. destruct (HsKindB.in_blocks L A p n Hp) as (q & Hq & Eq).
  apply (ax_blocks_img AX L A mem md q n (a - p) HM Hq ltac:(lia)).
  rewrite <- Eq. replace (p + (a - p)) with a by lia. exact Himg.
Qed.

Lemma sink_facts : ms_segs B = rsegs -> ms_ctx B = 0x53840 -> ms_lock B = 0x53838 -> ms_libc B = 0x537c8 ->
  ms_got_guard B = 0x221a0 -> ms_guard B = 0x537a8 -> ms_debruijn B = 0x10564 -> ms_size_classes B = 0x10584 ->
  ms_small_cnt B = 0x105e4 -> ms_med_cnt B = 0x105ff -> ms_tp B = 0x33538 -> ms_errno_off B = -164 -> ms_vmlock B = None -> ms_debruijn_len B = 32 ->
  sk_ofl_head = 0x53bf8 -> sk_ofl_lock = 0x53bf0 -> sk_threaded = 0x537c8 + 1 ->
  forall a, (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4) ->
    in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ errno_at B a /\
    ~ in_globals omx_G a.
Proof.
  intros HSEG Hctx Hlck Hlibc Hgg Hg Hdb Hsz Hsm Hmd Htp Heo Hvm Hdl Hh Hl Ht a Ha.
  rewrite Hh, Hl, Ht in Ha.
  assert (Hr : 0x537c0 <= a < 0x53c00) by lia.
  split.
  { assert (C : existsb (fun s => (bv_unsigned (fst s) <=? 0x537c0) && (0x53c00 <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
                  (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
    apply existsb_exists in C as (s & Hs & Hc). apply andb_prop in Hc as [Hc1 Hc2].
    apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
    split; [rewrite HSEG; intros E; pose proof (f_equal (@length Segment) E) as Le; vm_compute in Le; discriminate|].
    exists s. rewrite HSEG. split; [exact Hs | lia]. }
  split.
  { unfold static_owned. unfold vml_lo, vml_len. rewrite Hlck, Hlibc, Hgg, Hg, Hdb, Hsz, Hsm, Hmd, Hvm, Hdl. lia. }
  split; [rewrite Hctx; unfold CTX_SIZE; lia|].
  split; [unfold errno_at, errno_addr; rewrite Htp, Heo; lia|].
  intros Hgl. unfold in_globals, omx_G, Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL in Hgl.
  destruct Hgl as (lo & len & Hin & Hb). cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma ret_ok_any : forall ra, ra mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 ra).
Proof.
  intros ra Hra.
  assert (E : Z_to_bv 64 ra = Z_to_bv 64 (ra mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Zmod_mod. reflexivity. }
  rewrite E. apply ret_lit; [apply Z.mod_pos_bound; lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma start_of : forall empty L A regs mem md ra p n pl b j,
  empty = 0x33430 -> (j < 4)%nat -> ra mod 2 = 0 ->
  lib_pre_x B API SLOT_STACK empty L A regs mem md ra p n pl b -> omx_GI B j mem -> ro_agree (ms_segs B) mem ->
  exists peak0 cnt0, slot_start B API regs L A mem md p pl peak0 cnt0 j.
Proof.
  intros empty L A regs mem md ra p n pl b j Hem Hj Hra
    ((HM & HWF & HBD & HI & R1 & H16 & Hlo & Hhi & HW & Htp & HE & R10 & R11 & HB & _) & Hn & BD & _ & _ & SN & _ &
     FS & Hsp) (peak0 & cnt0 & AW & HPK & HCN & _) RA.
  pose proof alloc_ceiling_val. pose proof alloc_ceiling_lt.
  exists peak0, cnt0.
  split; [unfold slot_sp; split; [exact H16|]; split; [lia|]; split; [lia | exact Htp]|].
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HI|].
  split; [intros a [Ha|Ha]; [apply HW; exact Ha | apply HE; exact Ha]|].
  split; [rewrite R1; apply ret_ok_any; exact Hra|].
  split; [exact R10|]. split; [rewrite <- Hn; exact R11|].
  destruct HB as [(Hn0 & ->)|(Hnp & q & Hq & Hpq)].
  - assert (Epl : pl = []) by (destruct pl; [reflexivity | cbn in Hn; lia]). subst pl.
    cbn [length Z.of_nat]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
    split; [exact BD|]. split; [exact RA|]. split; [exact FS|]. split; [exact SN|].
    split; [exact AW|]. split; [exact HPK|]. split; [exact HCN | exact Hj].
  - pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq) as [Q1 Q2]. rewrite Hpq in Q1, Q2.
    split; [lia|]. split; [lia|]. split; [right; exists q; rewrite <- Hn; split; [exact Hq | exact Hpq]|].
    split; [exact BD|]. split; [exact RA|]. split; [exact FS|]. split; [exact SN|].
    split; [exact AW|]. split; [exact HPK|]. split; [exact HCN | exact Hj].
Qed.

Lemma slot_run : slot_env B API -> (forall fx' : YK11.FPState, @slot_callees fx' rc B API) ->
  (forall fx' : YK11.FPState, @frame_allocator rc fx' B API) ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b,
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> getr regs0 1 = Z_to_bv 64 ra ->
  res_ok_slots A0 b -> slot_bnd b -> lib_delta (Z.of_nat (length pl)) b = b -> frm_zero fp_csr ->
  SR (ms_segs B) (mkCfg (mkst regs0 (Z_to_bv 64 0x1331c) mem0 (seg_rom (ms_segs B))) md0)
    (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j).
Proof.
  intros ENV CAL FA regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b HS HRA RES HB LD FZ.
  pose proof (CAL fx) as (MEMCHR & MEMCPY & FAL & FAPR & FAP & CBA & CRC & CNO & DEC & CAW & CRT & _ & _).
  pose proof (FA fx) as (MALC & _).
  apply (step_A B API ENV MEMCHR regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b HS HRA RES LD FZ).
  intros L1 A1 regs1 mem1 md1 H1.
  apply (step_c0 B API ENV CNO regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L1 A1 regs1 mem1 md1 _ HS HB H1).
  intros L2 A2 regs2 mem2 md2 H2.
  apply (step_mal B API ENV MALC MEMCPY FAL FAPR regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L2 A2 regs2 mem2 md2 _
    HS HB H2).
  intros L3 A3 regs3 mem3 md3 H3.
  apply (step_dec B API ENV DEC FAP CBA regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L3 A3 regs3 mem3 md3 _ HS HB H3).
  intros L4 A4 regs4 mem4 md4 H4.
  assert (TAIL : forall (f : YK11.FPState) K L5 A5 regs5 mem5 md5, K <= 72 ->
            @at_pd f rc B API 0x1340c K (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L5 A5 regs5 mem5 md5 ->
            SR (ms_segs B) (mkCfg (@mkst f regs5 (Z_to_bv 64 0x13d84) mem5 (seg_rom (ms_segs B))) md5)
              (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j)).
  { intros f K L5 A5 regs5 mem5 md5 HK H5.
    pose proof (CAL f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRS & FF).
    pose proof (FA f) as (_ & FRC & _).
    apply (step_c5 B API ENV CRS regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L5 A5 regs5 mem5 md5 K _ HS HB HK H5).
    intros L6 A6 regs6 mem6 md6 H6.
    apply (step_ff B API ENV FF regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L6 A6 regs6 mem6 md6 _ HS H6).
    intros L7 A7 regs7 mem7 md7 H7.
    exact (step_fr B API ENV FRC regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L7 A7 regs7 mem7 md7 HS HRA LD H7). }
  apply (step_c2 B API ENV CAW CRC regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L4 A4 regs4 mem4 md4 _ HS HB
    (at_c2_pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L4 A4 regs4 mem4 md4 H4)).
  - intros L5 A5 regs5 mem5 md5 H5. exact (TAIL fx 4 L5 A5 regs5 mem5 md5 ltac:(lia) H5).
  - intros L5 A5 regs5 mem5 md5 H5.
    apply (step_c4 B API ENV CRT regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L5 A5 regs5 mem5 md5 _ HS HB H5).
    intros fx' L6 A6 regs6 mem6 md6 _ H6. exact (TAIL fx' 72 L6 A6 regs6 mem6 md6 ltac:(lia) H6).
Qed.

End Asm.

Theorem LLVMFuzzerTestOneInput_cg_holds : slot_callees_plain -> slot_premise_cg.
Proof.
  intros CAL B API LS SH SK empty FF rc fx j ra Hj Hra.
  pose proof FF as (SEG & MAL & FRE & _ & _ & ERR & GRD & GGD & CTX & LCK & LIBC & SZC & SMC & MDC & DBJ & TP & EOFF &
    _ & VML & DBL & SKH & SKL & SKT & EMPV & _ & _ & FG & _ & LIBK & LD & LR & FA).
  pose proof (FA rc fx) as (_ & _ & _ & _ & _ & BSP & _ & _ & _ & _ & _ & _ & _ & AX & OWN & _).
  assert (ENV : slot_env B (API rc)).
  { split; [exact SEG|]. split; [exact MAL|]. split; [exact FRE|]. split; [exact (ERR rc)|].
    split; [exact AX|]. split; [exact BSP|].
    split; [exact (omx_free B (API rc) SEG AX OWN FG)|].
    exact (sink_facts B SEG CTX LCK LIBC GGD GRD DBJ SZC SMC MDC TP EOFF VML DBL SKH SKL SKT). }
  unfold SlotAgree.lib_contract_cg. intros L A regs mem md p n pl b K PRE GI _ RA _ FZ HK.
  rewrite LIBK.
  destruct (start_of B (API rc) empty L A regs mem md ra p n pl b j EMPV Hj Hra PRE GI RA) as (peak0 & cnt0 & HS).
  pose proof PRE as ((_ & _ & _ & _ & R1 & _) & Hn & _ & RES & ROOM & _).
  assert (HB : slot_bnd b) by exact (LR b n ROOM).
  assert (CALL : forall fx' : FPState, @slot_callees fx' rc B (API rc)) by (intros fx'; exact (CAL B API LS SH SK empty FF rc fx')).
  assert (FAL : forall fx' : FPState, @frame_allocator rc fx' B (API rc)) by (intros fx'; exact (FA rc fx')).
  subst n.
  apply (SR_realizes_ms B (ms_segs B) eq_refl _ _ _
    (slot_run B (API rc) ENV CALL FAL regs L A mem md p pl peak0 cnt0 j ra b HS R1 RES HB (LD _ b) FZ)).
  intros c' Hc. apply (HK (LL 0 (m_fs md) []) c'). exact Hc.
Qed.
