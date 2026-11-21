From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_knock Require Images.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
  YK11 YM05 YO0d YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import
  ZTraceSpec ZComplete ZCompleteMF ZAllocator ZAllocatorMF SlotTopG Contract FrameAPI FrameSlotG.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Section BridgeM.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape} {AM : AllocMode}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_contract_x_G_of_gm : forall G R GI j pc ra empty stk,
  @lib_contract_gm AM fx rc LS B API SH SK G R GI j pc ra empty stk ->
  @lib_contract_x_G fx rc LS AM B API SH SK G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hpre)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_G_of_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | exact HGI'].
Qed.
End BridgeM.
(* [FrameSlotG.zlib_tables] for the may-fail API: the same static bytes, read from [MRx] at [MayFail]. *)
Lemma zlib_tables_mf : forall (rc : RunCeil) L A mem md, aa_MR (@zlib_API_mf rc) L A mem md ->
  forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs src0_msyms) (Z_to_bv 64 a) = true ->
  mbyte (ms_segs src0_msyms) mem a = seg_rom (ms_segs src0_msyms) (Z_to_bv 64 a).
Proof.
  intros rc L A mem md HMR a Hs Ha Hro.
  change (MRx (AM:=MayFail) src0_msyms L A mem md) in HMR.
  pose proof (mc_statics _ _ _ _ _ (proj1 HMR)) as ST.
  unfold static_owned in Hs.
  destruct Hs as [H|[H|[H|[H|[H|[H|Ht]]]]]].
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_lock src0_msyms) 4 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_libc src0_msyms + 3) 1 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_libc src0_msyms + 8) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_libc src0_msyms + 48) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_got_guard src0_msyms) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_guard src0_msyms) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - assert (Hv : table_addr src0_msyms a \/ vml_lo src0_msyms <= a < vml_lo src0_msyms + vml_len src0_msyms)
      by (unfold table_addr; tauto).
    destruct Hv as [Hv|Hv]; [apply (st_tables _ _ ST); exact Hv|].
    exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (vml_lo src0_msyms) (vml_len src0_msyms) a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
Qed.
Theorem plain_halts_mf_of_frame_slot : forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gm MayFail fx rc checksum_shape src0_msyms (@zlib_API_mf rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  halts_may_fail Exits.any Images.plain.
Proof.
  intros G GI HG GIL GI0 H.
  apply (plain_halts_mf_from_runtime_contracts_G checksum_shape G frame_RELRO GI (fun _ => []) checksum_permitted
    (fun data => checksum_room_calls _ _) (fun a h => frame_G_src0 a (HG a h))).
  - exact frame_RELRO_src0.
  - exact GIL.
  - exact GI0.
  - intros rc. exists (@zlib_API_mf rc). split; [apply zlib_allocator_extra_mf|].
    split; [exact (zlib_mf_allocator_holds rc)|].
    intros fx j Hj.
    exact (lib_contract_x_G_of_gm (AM:=MayFail) src0_msyms (@zlib_API_mf rc) (zlib_tables_mf rc)
      G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
