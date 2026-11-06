From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit KindBGlue SlotInv SlotDefs
  SlotStep memchr_c SlotRunA.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Local Open Scope Z_scope.

(* Entry to the check_0 call: the prologue, memchr and the length test (segment sA); a length over 0x300000
   returns 0 at once. *)

Ltac slot_regs HG :=
  let r := fresh "r" in let Hr := fresh "Hr" in let HC := fresh "HC" in
  intros r Hr; rewrite HG; unfold callee_saved in Hr;
  assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct HC as [-> | HC]; [reflexivity|]); subst r; reflexivity.

Ltac slot_kept HG :=
  let k := fresh "k" in let Hk := fresh "Hk" in let HC := fresh "HC" in
  intros k Hk; rewrite HG;
  assert (HC : k = 3 \/ k = 4 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia;
  repeat (destruct HC as [-> | HC]; [reflexivity|]); subst k; reflexivity.

Section A.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Definition at_c0 (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (p0 : Z) (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists peak, slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L A regs mem md (Z_to_bv 64 (2 ^ 64 - 1)) [] peak cnt0 b /\
  L = L0 /\ A = A0 /\ md = md0 /\
  getr regs 1 = Z_to_bv 64 0x1336c /\ getr regs 8 = getr regs0 8 /\
  getr regs 9 = Z_to_bv 64 (slot_nn pl) /\ getr regs 10 = Z_to_bv 64 p0 /\
  getr regs 11 = Z_to_bv 64 (slot_nn pl) /\ getr regs 18 = Z_to_bv 64 p0 /\ getr regs 19 = getr regs0 19 /\
  slot_nn pl <= 0x300000.

Lemma step_A : slot_env B API -> memchr_contract ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b,
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> getr regs0 1 = Z_to_bv 64 ra ->
  res_ok_slots A0 b -> lib_delta (Z.of_nat (length pl)) b = b -> frm_zero fp_csr ->
  (forall L A regs mem md, at_c0 regs0 L0 A0 mem0 md0 p0 pl cnt0 b L A regs mem md ->
     SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x13440) mem (seg_rom (ms_segs B))) md)
       (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j)) ->
  SR (ms_segs B) (mkCfg (mkst regs0 (Z_to_bv 64 0x1331c) mem0 (seg_rom (ms_segs B))) md0)
    (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j).
Proof.
  intros ENV MEMCHR regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b HS HRA RES LD FZ KC0.
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof (slot_img_low B API ENV) as IL.
  pose proof HS as (SP & HM & HWF & HBD & HI & HW & HRT & R10 & R11 & Hp & Hpe & HBLK & BD & RA0 & FS & SN & AW &
    HPK & HCN & HJ).
  pose proof SP as (H16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl. unfold SLOT_STACK in *.
  destruct (kb_md B API _ _ _ _ HM) as [Hh Hl].
  assert (STK : Frame.stk rsegs mem0 (spZ regs0 - 65536) (spZ regs0)).
  { apply HsKindB.stk_of_writable; [lia | lia |]. intros a Ha. rewrite <- SEG. apply HW. left.
    unfold SLOT_STACK. exact Ha. }
  assert (RA0' : ro_agree rsegs mem0) by (rewrite <- SEG; exact RA0).
  assert (BY : Mem.bytes_at rsegs mem0 p0 pl).
  { split; [lia|]. split; [lia|]. intros i Hi.
    change (Mem.mrd rsegs mem0 (Mem.wa (p0 + Z.of_nat i))) with (mbyte rsegs mem0 (p0 + Z.of_nat i)).
    rewrite <- SEG. rewrite (BD (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
  eapply (kb_run B regs0 (Z_to_bv 64 0x1331c) mem0 md0
    (fun R pc' m' => Frame.munch [(spZ regs0 - 48, spZ regs0)] mem0 m' /\ Frame.wmono rsegs mem0 m' /\
       ro_agree rsegs m' /\
       ((0x300000 < slot_nn pl /\ pc' = MState.ret_pc (getr regs0 1) /\
         exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
           R = Frame.mkR (getr regs0 1) (getr regs0 2) (getr regs0 3) (getr regs0 4) t0' t1' t2'
                 (getr regs0 8) (getr regs0 9) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                 (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)
                 (getr regs0 24) (getr regs0 25) (getr regs0 26) (getr regs0 27) t3' t4' t5' t6') \/
        (slot_nn pl <= 0x300000 /\
         Step.rw_cells rsegs m' (spZ regs0 - 48) (slot_cells regs0 (Z_to_bv 64 (2 ^ 64 - 1))) /\
         pc' = Z_to_bv 64 0x13440 /\
         exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
           R = Frame.mkR (Z_to_bv 64 0x1336c) (Z_to_bv 64 (spZ regs0 - 48)) (getr regs0 3) (getr regs0 4) t0' t1' t2'
                 (getr regs0 8) (Z_to_bv 64 (slot_nn pl)) (Z_to_bv 64 p0) (Z_to_bv 64 (slot_nn pl))
                 a2' a3' a4' a5' a6' a7' (Z_to_bv 64 p0) (getr regs0 19) (getr regs0 20) (getr regs0 21)
                 (getr regs0 22) (getr regs0 23) (getr regs0 24) (getr regs0 25) (getr regs0 26) (getr regs0 27)
                 t3' t4' t5' t6'))));
    [exact Hh | exact Hl | |].
  { rewrite SEG. eapply Exec.evt_mono.
    - eapply sA_run; [exact MEMCHR | exact STK | unfold spZ in *; lia | lia | exact RA0' | exact R10 | exact R11 |
        exact Hp | lia | exact BY].
    - intros ms' (m' & MU & WM & RA & POST).
      destruct POST as [(Hc & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->)
                       |(Hc & FR & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->)].
      + do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact RA|].
        left. split; [exact Hc|]. split; [reflexivity|]. do 14 eexists. reflexivity.
      + do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact RA|].
        right. split; [exact Hc|]. split; [exact FR|]. split; [reflexivity|]. do 13 eexists. reflexivity. }
  intros R pc1 mem1 regs1 (MU & WM & RA1 & POST) HG.
  assert (RA1' : ro_agree (ms_segs B) mem1) by (rewrite SEG; exact RA1).
  assert (REL0 : slot_rel B API omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L0 A0 mem0 md0)
    by (apply slot_rel_init; assumption).
  assert (REL1 : slot_rel B API omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L0 A0 mem1 md0).
  { apply (slot_rel_A B API IL omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L0 A0 mem0 md0 mem1
      [(spZ regs0 - 48, spZ regs0)] REL0 MU).
    - rewrite SEG. exact WM.
    - exact (blocks_wmono B API ENV L0 A0 mem0 md0 mem1 HM WM).
    - intros x Hx Hs. apply HsKindB.outside_one. unfold SLOT_STACK in Hs. lia.
    - intros x Hx _. apply HsKindB.outside_one. pose proof (HsKindB.in_img_low B SEG x Hx). lia.
    - intros x Hx _. apply HsKindB.outside_one. lia.
    - intros q k i Hq Hi. apply HsKindB.outside_one.
      pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq). lia. }
  assert (LG1 : ledger B L0 A0 mem1 [] peak0 cnt0 (2 ^ 64 - 1)).
  { apply (HsKindB.ledger_munch B API L0 A0 mem0 md0 mem1 [(spZ regs0 - 48, spZ regs0)] [] peak0 cnt0 _ HM
      (start_ledger B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j HS) MU).
    intros x Hx. apply HsKindB.outside_one. lia. }
  destruct POST as [(Hc & -> & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->)
                   |(Hc & FR & -> & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->)].
  - rewrite (kb_ret_pc _ HRT), HRA. apply SR_ret.
    apply (fin_of B API ENV regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L0 A0 regs1 mem1 md0 peak0 cnt0 HS HRA REL1).
    + slot_regs HG.
    + rewrite HG. reflexivity.
    + exact LG1.
    + lia.
    + exact RA1'.
    + rewrite LD. exact RES.
    + exact FZ.
  - apply (KC0 L0 A0). exists peak0.
    split.
    + split; [exact SP|]. split; [exact REL1|].
      split; [rewrite HG; reflexivity|].
      split; [slot_kept HG|].
      split; [exact FR|]. split; [exact LG1|]. split; [lia|]. split; [exact RES|]. split; [exact RA1' | exact FZ].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite HG; reflexivity|]. split; [rewrite HG; reflexivity|].
      split; [rewrite HG; reflexivity|]. split; [rewrite HG; reflexivity|].
      split; [rewrite HG; reflexivity|]. split; [rewrite HG; reflexivity|].
      split; [rewrite HG; reflexivity|]. lia.
Qed.

End A.
