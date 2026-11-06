(* check_read_kit_segs: two statements (Definitions only, no proof) the image-A walk of check_read uses at the
   allocator level, over image A's segments:
   - crd_stack_malloc_at_stmt: a class-cid fake-stack call composed into the caller's journal, from the contract
     astack_malloc_realizes and the progress law alone (the frame list grows by (cid, pos), the call's window is
     the only other change, the frame comes back with a zero shadow, its flag word and its bytes present);
   - crd_flag_free_stmt: a memory change that writes only bytes the journal allows plus the flag byte of the
     journal's first owned frame, and leaves that byte 0, releases the frame (stack_free_state) in the journal.
   Both are image-free in their proofs (lib/Reusable YCbq.v ajournal_sub, acall_kept_of_journal,
   ajournal_after_write; YG0d.v astack_free_law, frame_flag_lawP), the segments' low bound being
   lib/A/Prog/WirePImg.v wire_segs_low. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI16.

Definition crd_stack_malloc_at_stmt : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (B : asyms),
  AR_laws tfibsegs B -> stack_malloc_progressP B ->
  forall cid, @astack_malloc_realizes fx rc tfibsegs B cid -> 0 <= cid <= 10 ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr tfibsegs W (mkCfg (@mkst fx regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
      c2 = mkCfg (@mkst fx regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
      @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
      aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
      ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\
      st_nev S2 = st_nev Sc /\ (exists f, S2 = set_fs f Sc) /\
      zero_shadow (aview tfibsegs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
      rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) =
        Some (flag_addr lyc cid pos) /\
      (forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid ->
         apresent (w_H W) mem2 a) /\
      @acall_kept rc tfibsegs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).

Definition crd_flag_free_stmt : Prop :=
  forall (rc : YM05.RunCeil) (SK : YI16.sink_head) (B : asyms),
  AR_laws tfibsegs B -> astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
  forall STK sp0 FP ly S W0 mem md own' lyc Sc (W : world tfibsegs) memc mdc k cid pos memc' mdc' (Wr : Z -> Prop),
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memc mdc k ->
  0 <= cid ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) memc x) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc') ->
  (forall x : word, w_H W x = true -> memc' x = memc x) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  aview tfibsegs (w_H W) memc' (flag_addr lyc cid pos) = Some 0 ->
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W memc' mdc' k.
