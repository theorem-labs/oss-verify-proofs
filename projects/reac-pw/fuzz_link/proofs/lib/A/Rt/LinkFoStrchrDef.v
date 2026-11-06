(* reac-pw/fuzz_link, image A: the statement of the two strchr calls musl fmemopen makes on link's "w" call, at the
   strchr wrapper's 4-byte jump 0x43054 (`j 0x44118`, ___interceptor_strchr; REAL(strchr) is the cell 0xa36e8 =
   0x9b0a0, musl strchr, which calls __strchrnul 0x9b0dc). It is the interface between the walk of musl fmemopen
   (which takes it as a Section hypothesis) and the walk of the wrapper (which proves it).

   The two instances (fmemopen +0x28..+0x30 and +0x34..+0x44, AMemFile.v link_amf_code; listing
   (internal path) (internal record, sha256 4ac47e6b90f5)):
   - strchr("rwa" 0x20291, 'w' = 119) = 0x20292: __strchrnul's byte loop (+0x20 `lbu`, the address is 1 mod 8) reads
     'r' then 'w' and returns at +0x28; strchr reads *r = 'w' (+0x14); the wrapper checks the shadow of
     [0x20291, 0x20293) (r - s + 1 = 2 bytes; +0xd0..+0x120, the 8-byte shadow word at 0x7fffc050, 0 at start-up);
   - strchr("w" 0x21260, '+' = 43) = 0: __strchrnul reads the aligned word at 0x21260 (+0x44) and its two constants
     (+0x40 / +0x4c, [0x10360, 0x10380), AE39.v mconsts_view), then the bytes 'w', 0 (+0xc0); strchr reads *r = 0;
     the wrapper calls internal_strlen (+0xc4, 0x657f8) on "w" (1) and checks the shadow of [0x21260, 0x21262)
     (+0x110 the word at 0x7fffc248 is not 0: the global's partial granule 2 and its redzone; +0x1c8..+0x1f8 the
     last byte's test passes, 1 < 2; the AR const law holds those shadow bytes, AF0m.v Tfib_const_shadow).
   No path reaches the wrapper's report call (+0x208 range_check and after): both checks pass.
   The donor is pcap's lib/A/AE2j.v tfib_strchr_lit (origin/ossv/recipes; relocated copy staged at
   (internal path) (internal record, sha256 4c76151d28bb)), whose instances are pcap's "rb" literal and
   strchr("rwa", 'r'); the window, the kept registers and the post are the donor's.
   This file is the statement only. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE39.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* __interceptor_trampoline_strchr (the target of fmemopen's two `jal` +0x30 / +0x44): j 0x44118 *)
Definition LA_W_STRCHR : Z := 0x43054.
(* the run's stack window: the wrapper's 0x7f0 + 0x70 (+0x00 / +0x2c), strchr's 16, __strchrnul's 16 (pcap AE2j.v
   SC_WIN); TryAsanInitFromRtl, the wrapper's first runtime call and internal_strlen run at the wrapper's depth *)
Definition FSC_WIN : Z := 2176.
(* the registers the wrapper and musl's strchr leave as they were, beside ra and sp (pcap AE2j.v KEPTS) *)
Definition FSC_KEPT : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* (s, c, the result) for the two calls *)
Definition FSC_INST : list (Z * Z * Z) := [(LA_RWA, 119, LA_RWA + 1); (LA_MODE_W, 43, 0)].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the return to ra with the result in a0, AR at the same ly S W, the registers kept, every byte outside the window
   kept, the window present, presence kept (pcap AE2j.v strchr_post) *)
Definition fsc_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (res : Z) : world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at tfibsegs (raZ regs) regs1 mem1 md1 /\ same_but_materialized md md1 /\
    AR tfibsegs B ly S W mem1 md1 /\
    getr regs1 10 = w64 res /\ getr regs1 1 = getr regs 1 /\ getr regs1 2 = getr regs 2 /\
    (forall r, In r FSC_KEPT -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FSC_WIN <= a < spZ regs) ->
       aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
    (forall a, spZ regs - FSC_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a).

(* The two calls, from AR, the stack window, the arguments, and the image bytes they read that AR does not pin: the
   mode word, "rwa\0" and __strchrnul's constants (the shadow bytes and the runtime cells are AR's). *)
Definition afm_strchr_lit : Prop :=
  forall s c res, In (s, c, res) FSC_INST ->
  forall ly S (W : world tfibsegs) regs mem md,
  AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
  spZ regs mod 16 = 0 -> ly_stk_lo ly + FSC_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - FSC_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 c ->
  val_mem tfibsegs (rd W mem) LA_MODE_W 8 119 -> garr8 tfibsegs (rd W mem) LA_RWA rwa_Z ->
  mconsts_view W mem ->
  SRr tfibsegs W (cfg_at tfibsegs LA_W_STRCHR regs mem md) (fsc_post ly S W regs mem md res).

End a.
