From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import FrameAPI Img0.
Import ListNotations.
Local Open Scope Z_scope.

(* PlainHalts.frame_facts_plain with the room clause weakened from sb_cap b = CAPMAX to 128 <= sb_cap b <= CAPMAX,
   so that a lib_shape with a smaller allocator capacity (the agreement frame's) also meets it. *)
Definition frame_facts_plain_ag (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
        ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x15964 /\ ms_free B = 0x15824 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4f940 /\ ms_got_guard B = 0x1e358 /\
    ms_ctx B = 0x4f9d8 /\ ms_lock B = 0x4f9d0 /\ ms_libc B = 0x4f960 /\ ms_size_classes B = 0x10698 /\
    ms_small_cnt B = 0x106f8 /\ ms_med_cnt B = 0x10713 /\ ms_debruijn B = 0x1061c /\ ms_tp B = 0x2f6d0 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 124 /\
    @sk_ofl_head SH = 0x4fd90 /\ @sk_ofl_lock SK = 0x4fd88 /\ @sk_threaded SK = 0x4f960 + 1 /\
    empty = 0x2f5e0 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

From Stdlib Require Import Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Contract FrameAPI Img0 AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan PlainHalts
  SlotImg SlotIntegration SlotEntry SlotGlue SlotStGlue SlotTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RgNeeds_c.

(* The plain slot contract of LLVMFuzzerTestOneInput on frame_facts_plain_ag: the proof of SlotTop.grant_slot_sb,
   whose room facts (SlotIntegration Section Path, RB0) need only 128 <= sb_cap b <= CAPMAX. *)
Theorem grant_slot_plain_ag : RgNeeds_c.ctrl_lay_block_need ->
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (ra empty : Z),
    frame_facts_plain_ag B API LS SH SK ra empty ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_g fx rc LS B (API rc) SH SK [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros LAY B API LS SH SK ra empty HF rc fx j _.
  destruct HF as (HB & Hra & HMAL & HFRE & _ & _ & HERR & HGU & HGG & HCTX & HLOCK & HLIBC & HSZ & HSM & HMD & HDB &
                  HTP & HEO & _ & HVM & HDL & HOFLH & HOFLL & HTHR & HEMP & _ & _ & _ & _ & HLIBK & HDELTA & HROOM & HFA).
  pose proof (HFA rc fx) as FA. pose proof (HERR rc) as Herr.
  pose proof (slot_segs LAY) as (HEAD & INIT & NSET & STURN & UENT & UTURN & ADMIT & SWEEP & RAW & RAWSW & SSETUP &
                                 SCHED & EPI).
  unfold lib_contract_g.
  intros L A regs mem md p n pl b K PRE _ HGR HRO _ HFRM HK.
  rewrite HLIBK.
  pose proof (aa_laws (API rc)) as LAWS.
  pose proof FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _).
  pose proof PRE as ((HMR & _ & _ & _ & _ & _ & HSc0 & _ & _ & Htp0 & _) & _ & _ & _ & Hroom & _ & _ & _ & _ & HS47).
  assert (HA0 : forall q k, In (q, k) (user_blocks A) ->
            4096 <= ptr_addr L q /\ ptr_addr L q + k <= alloc_ceiling /\
            (forall i, 0 <= i < k -> ~ in_img B (ptr_addr L q + i))).
  { intros q k Hq. destruct (mr_blocks_range B _ LAWS L A mem md q k HMR Hq) as (H1 & H2).
    split; [exact H1|]. split; [exact H2|]. intros i Hi. exact (ax_blocks_img AX L A mem md q k i HMR Hq Hi). }
  destruct (@entry_holds fx rc LS B (API rc) SH SK HB FA L A regs mem md p n HA0 ra empty pl b PRE HGR HRO HEMP)
    as (S1 & N1).
  assert (UB : unit_binding B).
  { refine (conj HB (conj _ _)); [rewrite HMAL | rewrite HFRE]; reflexivity. }
  assert (HTPx : x_tp (xent regs p pl) = w64 (ms_tp B)).
  { unfold xent. cbn [x_tp]. change (PropExec.getr regs (Z_to_bv 5 4)) with (YK11.getr regs 4). exact Htp0. }
  set (R := fun c => exists s L' A' md', c = mkCfg s md' /\
              St B (API rc) L A regs mem md (xent regs p pl) s L' A' md' b /\ norm_at (Ep (xent regs p pl)) s).
  assert (KR : forall s L' A' md' b', St B (API rc) L A regs mem md (xent regs p pl) s L' A' md' b' ->
                 norm_at (Ep (xent regs p pl)) s -> res_end b b' -> R (mkCfg s md')).
  { intros s L' A' md' b' S' N' Hb. unfold res_end in Hb. subst b'. exists s, L', A', md'. auto. }
  pose proof (@path_all fx rc B (API rc) HB FA Herr L A regs mem md p HA0 pl b
                HEAD INIT NSET STURN UENT UTURN ADMIT SWEEP RAW RAWSW SSETUP SCHED EPI
                (@seg_mallocT_holds fx rc B (API rc)) (@seg_mallocSW1_holds fx rc B (API rc))
                (@seg_mallocSW2_holds fx rc B (API rc)) (@seg_freeSW1_holds fx rc B (API rc))
                (@seg_freeSW2_holds fx rc B (API rc)) (@seg_freeT_holds fx rc B (API rc))
                (@st_malloc_holds fx rc B (API rc) HB FA Herr L A regs mem md)
                (@st_free_holds fx rc B (API rc) HB FA Herr L A regs mem md)
                UB HTPx (row_off_holds B HGU HGG HCTX HLOCK HLIBC HSZ HSM HMD HDB HTP HEO HVM HDL) HSc0 HS47
                (HROOM b n Hroom) R KR _ S1 N1) as PATH.
  assert (SKF : img_free B (@sk_threaded SK) /\ (forall k, 0 <= k < 4 -> img_free B (@sk_ofl_lock SK + k)) /\
                (forall k, 0 <= k < 8 -> img_free B (@sk_ofl_head SH + k))).
  { pose proof (sink_img_free B HB HGU HGG HCTX HLOCK HLIBC HSZ HSM HMD HDB HTP HEO HVM HDL) as SI.
    split; [apply SI; rewrite HTHR; lia|].
    split; [intros k Hk; apply SI; rewrite HOFLL; lia | intros k Hk; apply SI; rewrite HOFLH; lia]. }
  rewrite HB.
  apply (SR_realizes rsegs _ R _ PATH).
  intros c' (s & L' & A' & md' & -> & S' & N').
  destruct (@final_holds fx rc LS B (API rc) SH SK HB L A regs mem md p n HA0 ra empty pl b s L' A' md'
              PRE Hra HDELTA SKF S' N') as (Ecfg & POST).
  rewrite Ecfg. rewrite <- HB.
  apply HK. exists fx, L', A', (ms_regs s), (ms_mem s), md'.
  split; [reflexivity|]. split; [exact HFRM|]. split; [exact POST | exact I].
Qed.
