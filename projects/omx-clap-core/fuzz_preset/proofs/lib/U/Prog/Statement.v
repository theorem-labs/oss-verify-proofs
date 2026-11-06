From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger LedgerCells SlotGI LLVMFuzzerTestOneInput_c.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* #102: slot_G (LLVMFuzzerTestOneInput_c) and frame_G (FrameAPI) are both LedgerCells.GL_runs. *)
Lemma slot_G_frame : forall a, in_globals slot_G a -> in_globals frame_G a.
Proof. intros a Ha. unfold slot_G, frame_G in *. exact Ha. Qed.

(* The page top of the ubsan image's data: the program headers of the #102 ubsan twin fuzz_preset.ubsan (sha256
   27566683952ebd54...; PT_LOADs equal to the pin 45b0357d18ff66cd's) give the RW PT_LOAD at 0x24fb0 with memsz
   0x30e70 (.data, then .bss to 0x55e20), so its pages are [0x24000, 0x56000). *)
Lemma slot_img_data : forall (B : malloc_syms) a,
  ms_segs B = rsegs -> ms_segs B <> [] -> 0x24000 <= a < 0x56000 -> in_img B a.
Proof.
  intros B a HS Hne Ha. split; [exact Hne|]. rewrite HS.
  assert (Hb : existsb (fun s => (bv_unsigned (fst s) <=? 0x24000) && (0x56000 <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
                 (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb. destruct Hb as (s & Hin & Hs).
  apply andb_true_iff in Hs. destruct Hs as (H1 & H2). apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin | lia].
Qed.

Definition slot_contract : Prop :=
  exists CS : list byte -> list Z, CS_ok CS /\
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    @LLVMFuzzerTestOneInput_contract fx rc LS B API SH SK CS.

Theorem ubsan_halts_of_frame : frame_ubsan -> slot_contract -> Statements.ubsan_halts.
Proof.
  intros HF0 (CS & HCS & HC).
  destruct (frame_ubsan_split HF0) as (B & API & LS & SH & SK & ra & empty & HF & HT).
  unfold frame_facts_ubsan in HF.
  destruct HF as (HS & Hra & Hm & Hf & Hr & Hc & He & Hg & Hgg & Hctx & Hlk & Hlc & Hsc & Hsm & Hmd & Hdb & Htp & Heo &
    Hrp & Hvl & Hdl & Hoh & Hol & Hth & Hemp & Hempr & Hcro & HG & HRL & HK & HD & HA).
  apply (HT CS slot_G (omx_GI B) slot_G_frame (slot_G_local B)).
  - intros mem Hmem. exact (slot_GI_init B mem HS Hmem).
  - exact HCS.
  - intros rc fx j Hj.
    assert (Hne : ms_segs B <> []).
    { assert (H0 : in_globals frame_G GL_OWN_RAN_OUT)
        by (exists GL_OWN_RAN_OUT, 40; split; [cbn [In frame_G GL_runs]; tauto | lia]).
      exact (proj1 (proj1 (HG _ H0))). }
    refine (HC rc fx LS B (API rc) SH SK ra empty SLOT_STACK _ _ _ (HA rc) (conj HK HD) Hra Hemp Hempr _ j Hj).
    + unfold slot_syms. repeat split; assumption.
    + intros a Ha. exact (HG a (slot_G_frame a Ha)).
    + intros a Ha. unfold slot_sink_cell in Ha. rewrite Hoh, Hol, Hth in Ha.
      unfold slot_apart, errno_addr. rewrite Hctx, Htp, Heo.
      split; [split; [|split; [|split]]|].
      * apply slot_img_data; [exact HS | exact Hne | lia].
      * unfold static_owned, vml_lo, vml_len. rewrite Hlk, Hlc, Hgg, Hg, Hdb, Hsc, Hsm, Hmd, Hvl. lia.
      * unfold CTX_SIZE. lia.
      * lia.
      * intros (lo & len & Hin & Hl). cbn [In slot_G GL_runs] in Hin.
        destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo len; unfold GL_FAIL, GL_OWN_RAN_OUT in Hl; lia.
    + unfold SLOT_K, SLOT_STACK. lia.
Qed.
