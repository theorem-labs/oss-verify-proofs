(* The stack each call of codec's own code uses below its caller's sp at image B (the build with the
   memory-checking runtime and the UBSan checks, fuzz_codec.asan-ubsan, sha256 73109e32e77b).

   Everything else the image-B contracts are stated over is image-independent and comes from
   lib/A/Prog/CPgBase.v unchanged: the register forms, the byte-list results, the call record, the
   premise bundles (crd_ok, cdst_ok, cdstk_ok, cobj_ok, cimg_usable, cimg_range, pers_argA, cpers_disj,
   kcall_atA, cstr_rd, cimg_rd), the shared pre cdc_entry and the shared post cdc_post, and the event and
   live-byte constants EV_CDC / LIVE_CDC (image B allocates nothing either).

   B against A (measure.tsv, and the per-function excerpts of the image):
   - diginet_ring_encode, diginet_meter_encode, leds_encode and diginet_counter_encode call
     diginet_sysex_encode instead of inlining it, and each takes a side-stack frame of class 0 for the
     payload it builds; at image A they take none;
   - leds_encode and owe_sysex are functions of their own at image B; at image A they are inlined;
   - diginet_strip_leds_encode and diginet_counter_leds_encode TAIL-call leds_encode (they pop their own
     16 bytes first), so the window they need is leds_encode's, measured from their own entry sp;
   - diginet_scribble_text makes no call at image B (at image A it fills with __asan_memset);
   - the real frames are bigger where the UBSan checks need more spill room.
   Each constant below is the function's own real frame, 32 more where it realigns sp (`andi sp,sp,-32`),
   and the deepest window below that: ESTACK for a frame request or for the checked fill and copy helpers,
   2 * ESTACK for the compare and string-compare wrappers, or a callee's own T. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgBase.
Import ListNotations.
Local Open Scope Z_scope.

(* the register-only leaves: no frame, no call (image B 0x8513c, 0x85bd8, 0x85bf8, 0x85ef8, 0x85f14) *)
Definition TB_pers_of : Z := 0.
Definition TB_ring_dot : Z := 0.
Definition TB_ring_fill : Z := 0.
Definition TB_meter_mask : Z := 0.
Definition TB_meter_segs : Z := 0.
(* a frame of 16 for the return address of the error path, and no call *)
Definition TB_seg7 : Z := 16.
Definition TB_owed_seg7 : Z := 16.
Definition TB_fader : Z := 16.
Definition TB_button : Z := 16.
Definition TB_touch : Z := 16.
Definition TB_vpot : Z := 16.
Definition TB_jog : Z := 16.
Definition TB_scribble_text : Z := 16.
(* a frame and one helper or wrapper call *)
Definition TB_sysex : Z := 48 + ESTACK.
Definition TB_owe_sysex : Z := 48 + ESTACK.
Definition TB_from_name : Z := 48 + 2 * ESTACK.
Definition TB_text_arg : Z := 32 + ESTACK.
Definition TB_check_refusal : Z := 16.
Definition TB_check_range : Z := 32 + 2 * ESTACK.
Definition TB_check_bytes : Z := 32 + 2 * ESTACK.
Definition TB_check_masks : Z := 48.
Definition TB_check_seg7 : Z := 48 + TB_owed_seg7.
Definition TB_check_pers : Z := 32 + TB_from_name.
(* the four encoders that take a class-0 frame and call diginet_sysex_encode: real frame + 32 for the
   realignment, then sysex_encode's window, which is deeper than the frame request's ESTACK *)
Definition TB_ring : Z := 128 + TB_sysex.
Definition TB_leds : Z := 128 + TB_sysex.
Definition TB_meter : Z := 160 + TB_sysex.
Definition TB_counter : Z := 160 + TB_sysex.
Definition TB_scribble : Z := 160 + TB_sysex.
(* the two that tail-call leds_encode: they pop their own frame first, so the window is leds_encode's *)
Definition TB_sleds : Z := TB_leds.
Definition TB_cleds : Z := TB_leds.
(* the text functions that take a class-1 frame (224 = real frame 192 + 32 for the realignment) *)
Definition TB_counter_text : Z := 224 + ESTACK.
Definition TB_owed_counter_text : Z := 224 + ESTACK.
(* the two text checks: their own frame and realignment, then the compare wrapper's 2 * ESTACK, which is
   deeper than either text callee's T *)
Definition TB_check_text_scribble : Z := 160 + 2 * ESTACK.
Definition TB_check_text_counter : Z := 192 + 2 * ESTACK.
(* The entry function at image B: real frame 320, 32 for the realignment, then the deepest window below
   it, check_text_counter's. The core fixes LLVMF_STK at 32768, which covers it. *)
Definition TB_main_need : Z := 352 + TB_check_text_counter.
