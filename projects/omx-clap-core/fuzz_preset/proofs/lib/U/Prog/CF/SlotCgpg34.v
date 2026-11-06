From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YH00 YH02 YI5b YI5c YL0k
  YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI SlotPack AllocPack
  AllocPackRoom AllocPackGSF SlotAgree SlotAgreeV ZAllocator AllocAgCf34.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import ZTraceSpec ZComplete SlotTopG AllocCut
  AllocPackCut BlocksNodup FrameSlotG SlotKept FrameSlotP ReallocCert.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackFit PackOwn PackVec PackBand PackBig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Statement PackSlot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import EntryDefs EntrySR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require LinkUEntry34 PackRoomsAg34.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require AgreeLim AgreePack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* Copy of CF/SlotCgpg.v at the 2^34 law (pack_ag34_form, HLIM at SRC_LIM_MIN, the 2^34 rooms of PackRoomsAg34).
   The ubsan cut-free slot for the agreement statement (AgreeFrameP.ubsan_agrees_of_slots_pg's U premise): the
   cut-free twin of U PackSlot.slot_contract_of_entry, for the frame's allocator src0_msyms / zlib_API, at
   F := pack_ag34_form, ending in lib_contract_cgpg (crealizes) instead of SR_realizes. *)

Lemma zlib_facts : frame_facts_ubsan src0_msyms (@zlib_API) checksum_shape src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact FrameProof.errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact FrameProof.ctx_not_ro|].
  split; [exact FrameProof.frame_G_facts|].
  split; [exact FrameProof.frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  exact FrameProof.zlib_frame_allocator.
Qed.

Section S.
Context {rc : RunCeil} {LS : lib_shape}.
Hypothesis HSH : forall pl fs (K : lleaf -> TSet), @LIBK LS pl fs K = K (LL 0 fs []).
Hypothesis HLIM : AgreeLim.limlaw_at YM0b.SRC_LIM_MIN src0_msyms (@zlib_API rc).

Lemma z_slot_facts :
  slot_syms src0_msyms /\ slot_globals src0_msyms /\
  @slot_sinks src0_msyms src0_sink_head src0_sink /\ RA_LIB mod 2 = 0 /\ EMPTY = 0x35230 /\ 0 < EMPTY < 2 ^ 62 /\
  SLOT_K <= SLOT_STACK.
Proof.
  destruct zlib_facts as (HS & Hra & Hm & Hf & Hr & Hc & He & Hg & Hgg & Hctx & Hlk & Hlc & Hsc & Hsm & Hmd & Hdb & Htp &
    Heo & Hrp & Hvl & Hdl & Hoh & Hol & Hth & Hemp & Hempr & Hcro & HG & HRL & HK & HD & HA).
  assert (Hne : ms_segs src0_msyms <> []).
  { assert (H0 : in_globals frame_G G_LIVE)
      by (apply (ivls_sub_sound [(G_LIVE, 1)]); [vm_compute; reflexivity | exists G_LIVE, 1; split; [left; reflexivity | lia]]).
    exact (proj1 (proj1 (HG _ H0))). }
  split; [unfold slot_syms; repeat split; assumption|].
  split; [intros a Ha; exact (HG a (Statement.slot_G_frame a Ha))|].
  split.
  { intros a Ha. unfold slot_sink_cell in Ha. rewrite Hoh, Hol, Hth in Ha.
    unfold slot_apart, errno_addr. rewrite Hctx, Htp, Heo.
    split; [split; [|split; [|split]]|].
    - apply Statement.slot_img_data; [exact HS | exact Hne | lia].
    - unfold static_owned, vml_lo, vml_len. rewrite Hlk, Hlc, Hgg, Hg, Hdb, Hsc, Hsm, Hmd, Hvl. lia.
    - unfold CTX_SIZE. lia.
    - lia.
    - intros (lo & len & Hin & Hl). vm_compute in Hin.
      destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo len; lia. }
  split; [exact Hra|]. split; [exact Hemp|]. split; [exact Hempr|].
  unfold SLOT_K, SLOT_STACK. lia.
Qed.

Theorem ubsan_slot_cgpg34 : forall (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_cgpg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    PackSlot.CS_pre slot_G frame_RELRO (omx_GI src0_msyms) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros fx j Hj.
  destruct z_slot_facts as (Hsy & Hgl & Hsk & Hra & Hemp & Hemp2 & Hstk).
  unfold lib_contract_cgpg.
  intros L A regs mem md p n pl b K Hpre Hres Hent HGI HR Hro Hsp Hfrm HK.
  rewrite HSH.
  destruct (omx_GI_ledger src0_msyms j mem L A HGI) as (peak & cnt & Hled & Hcnt).
  destruct Hent as (Hlc & Hcap & d & Hd & Elive & Ebytes).
  cbn [TDP fold_left] in Elive, Ebytes.
  destruct Hres as (Hres & HGSF).
  pose proof Hres as Hres'.
  destruct Hres' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLL & _).
  set (b0 := PB (pb_live b) (pb_bytes b) (PackSlot.CS_pre pl)).
  assert (Hres0 : res_ok_pack A b0).
  { apply res_ok_pack_raise; [exact Hres | apply CS_of_len | intros k Hk; exact (proj2 (Hcap k Hk))]. }
  assert (HL0 : length (pb_live b0) = 49%nat) by exact HLL.
  assert (HCNT : 0 <= cnt <= 3 * 2 ^ 60) by (destruct Hcnt as [H1 H2]; split; [exact H1|]; lia).
  assert (Hrooms : entry_rooms pack_ag34_form b0 cnt pl).
  { intros Hn.
    assert (Hlen : Z.of_nat (length (zb pl)) <= pf_MAX)
      by (unfold zb; rewrite length_map; unfold ent_n in Hn; unfold pf_MAX; lia).
    apply (PackRoomsAg34.rooms_ag34 b0 (beta2_x (zb pl))); try exact Hn; try exact eq_refl; try exact HCNT; try exact HL0.
    - intros k Hk. cbn [pb_live b0]. rewrite Elive. exact (PackSlot.drv_live_le2 d Hd k Hk).
    - cbn [pb_bytes b0]. rewrite Ebytes. destruct Hd as (_ & _ & _ & HB). unfold PDRV_BYTES in HB. lia.
    - intros k Hk. cbn [pb_cap b0]. unfold PackSlot.CS_pre. apply CS_of_nth, Hk.
    - cbn [pb_cap b0]. exact (pack_big_fit (zb pl) Hlen). }
  pose proof (@LinkUEntry34.lu_entry_sr rc fx src0_msyms (@zlib_API rc) Hsy Hgl (FrameProof.zlib_frame_allocator rc)
    (fun fx' => @zlib_ag34_malloc_contract fx' rc HLIM) (fun fx' => @zlib_ag34_free_contract fx' rc)
    (fun fx' => @zlib_ag34_realloc_contract fx' rc 0x19bfc eq_refl HLIM)
    (fun fx' => @zlib_ag34_realloc_null_contract fx' rc 0x19bfc eq_refl HLIM)
    src0_sink_head src0_sink RA_LIB EMPTY SLOT_STACK Hsy Hgl Hsk Hra Hemp2 Hemp Hstk j L A regs mem md p n pl peak cnt b0
    Hj Hpre HR Hro Hsp Hfrm Hled (proj2 Hcnt) (conj Hres0 HGSF) Hrooms) as HSR.
  apply (SR_SRcf src0_msyms _ _ HSR).
  intros c' (fx' & L' & A' & regs' & mem' & md' & E1 & E2 & E3 & Dp & cset & b4 & trs & Ds & Df &
             Ec & Hf & Hpost & HGI' & Hwit & Hok).
  assert (Hfold : entry_fold pack_ag34_form b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df = b0).
  { exact (PackRoomsAg34.entry_fold_ag34 b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df HL0 HCNT Hwit). }
  rewrite Hfold in Hok. destruct Hok as (Hok & HGSF').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Ec|]. split; [exact Hf|]. split; [|exact HGI'].
  destruct Hpost as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19).
  unfold lib_post_cgpg, lib_post_pg. split; [|exact HGSF'].
  exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12
          (conj Q13 (conj Q14 (conj Q15 (conj Q16 (conj Q17 (conj Q18 (conj Hok Q19))))))))))))))))))).
Qed.

End S.
