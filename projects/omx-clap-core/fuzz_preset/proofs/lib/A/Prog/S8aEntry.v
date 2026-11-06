(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v; 1219 of its 1297 lines of code are new or changed and 850 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102; pin sha256 1be0f53d96cb9d6c, unstripped twin bff8519b): S8a PIECE 1,
   the walk of ex_value's ENTRY, A' 0x832a4-0x833d8 with the report arms 0x83f34-0x83f40 (82 instructions), against the
   piece interface lib/A/Prog/S8aIface.v (iface 67f35bb5f4b: ev_entry_spec, ev_at_ws, ev_mid, ev_regs), at
   L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A. Theorem ev_entry_holds.
   BUILT ON: the kit of record a3bdeca3920 (texts: PRH_Base / PRH_FnEx / PRH_Img, fpre with `spZ regs + 64 <=
   ly_stk_hi ly`, PrhRoomLive with RL_set_fs) plus the WHOLE engine set by path from origin/cold/c-omx-alloc-preset-s1b
   7792959a2abb (a Theorem Labs lane's list, the internal file engine-blobs-s1b.txt plus the pair): journal lib/Reusable/YCbqG.v blob
   c3b5d0111037 (18-field AR_laws_x: field 17 alx_img, field 18 alx_layout_ok), YGcallcf.v a61c80afd3d4 (not in this
   file's closure), FCiface.v ac3796181712, YC80x ec48991942e4, YC1fPx 8549c953fad9, YCbqGcall 1baa92bd3c81, YGcallx
   a4bb5c806d6d, YGcallSx 17d7d2cdbcd1. (First Qed on h-walk-ctrl's certified set 3a970962815, YCbqG 83da015952be:
   cold/h-hpreset-7-s8a-entry-p1 7337b087a53.) Old-pin program listing (history): v4 by path from
   cold/h-verbs-1-preset-proglisting 7c8ffeba5035 (PAImg_prog.v 0ece0b9f5a, Listing_prog.v cbba047f88, Img0.v
   84c90444e0), over image A (sha256 d83eb25dbf0df6d5). The record is touched through named projections only.
   #102 RELOCATION (words equal up to pc-relative fields, but the frame string loaded at +0xa8 / +0xc4 CHANGED
   between the pins): the walk moves to image A' BY SYMBOL on a Theorem Labs lane's #102 integration listing (Listing_prog.v 7ed1529926bd,
   PAImg_prog.v 505a51ff7d08, PRH_Img.v 934516a622e8): every pc below is A' ex_value (0x832a4) + the old offset from 0x82f30;
   the listing positions 6628 / 6744 / 6940 / 9352 become 7364 / 7480 / 7676 / 10088 (A_prog_base 0x8154c -> 0x815e0, A'
   ex_value - A' LLVMFuzzerTestOneInput). The descriptor pointer the frame header stores is computed from A''s own words
   (auipc / addi at ex_value + 0xa8 / + 0xc4 -> A' 0x197bd, the #102 bytes `2 32 8 11 end.i42:246 64 8 9 num.i:247`); no
   statement here names those bytes. The kit's ledger has #102's two new cells (eve_ledger_keep keeps seven).
   THE WALK, every instruction of the piece (82 = 70 run + 12 not reached):
   - run 1, 0x832a4-0x83314 (29, YC1fPx paj_run_tok_x): the save area (13 callee-saved registers at sp0 - 256 + 152 ..
     248 and a zero word at sp0 - 256), s0 = sp0, sp = s1 = S1 (`andi sp, sp, -32`), s7 = v, the two GOT words, the
     use-after-return option word and the shadow base (alx_const, AR_laws_x field 10: the word is 1), s3 = q;
     0x8330c `beqz a2, 0x83320` NOT TAKEN (a2 = the option word = 1); 0x83310 a0 = 96; 0x83314 `jal frame_alloc_1`.
   - the call __asan_stack_malloc_1 (class 1) through YGcallSx.aj_stack_malloc_at_x for FCiface's
     astack_malloc_realizes_x 1 (ASM1), discharging count_cid 1 (frames S) < fs_frames 1 at the entry state from
     ev_pre's count_cid 1 (frames S) + S n <= fs_frames 1; it returns the class-1 fake frame F = frame_addr ly 1 pos
     (the inline real-stack fallback is not reached).
   - run 2, 0x83318-0x833d8 (41 = 2 + 2 + 37, YC1fPx paj_run_to_tok_x to 0x833dc): 0x83318-0x8331c (s6 = F,
     `j 0x83324`), 0x83324-0x83328 (s2 = F; `bnez s6, 0x83348` TAKEN: F >= 4096), 0x83348-0x833d8 (the frame header
     words: magic 0x41b58ab3, the descriptor pointer, the pc; the frame's 12 shadow bytes; s4 = shadow (q + 8); the two
     shadow checks; s2 spilled at s1 + 144; s10 = shadow q).
   - NOT REACHED (12): 0x83320 `li s6, 0` (only after a taken 0x8330c), 0x8332c-0x83344 (7, the real-stack frame
     fallback, only after s6 = 0), 0x83f34-0x83f40 (4, the two report arms).
   REPORT CHECKS, each NOT TAKEN: 0x833c8 `bnez a0, 0x83f34` (a0 = the shadow byte of q + 8, read at 0x833c0) and
   0x833d8 `bnez a0, 0x83f3c` (a0 = the shadow byte of q, read at 0x833d4). Both bytes read 0: struct ex lies on the
   real stack ([sp0, sp0 + d), ev_pre), and AR_laws_x field 12 (alx_zshadow, the real stack at the head of
   zero_shadow_ranges) keeps the real stack's shadow 0 in every state (eve_zsh_byte at the state after the call).
   THE CUT (eve_at_ws_of): ev_mid's fourteen conjuncts (the 12th pairs the room keep with the hull use) and ev_regs
   as S8aIface states them, unchanged.
   MEMNORM (S8a interface on walkkit old-pin 4951e104ca2e: ev_pre's and ev_mid's last conjunct
   `YAkMemnorm.memnorm segs mem`): taken from ev_pre, kept across run 1 and run 2 by YC1fPx's `*_inv` runners
   (paj_run_x_inv / paj_run_to_x_inv at P := YAkMemnorm.memnorm SEGS, laws YSRrMemnorm.srr_inv_laws_memnorm_k) and
   across the frame_alloc_1 call by the callee's keep (YGcallMxmn.v aj_stack_malloc_at_xm), handed to the cut.
   HYPOTHESIS CHANGE: ASM1 strengthened to the xm form (adds the memnorm keep, YGcallMxmn.v:207
   astack_malloc_realizes_xm); supplier = the frame-class lane's stack_malloc1_contract_xm (lib/A/FCm01xm.v:32, Qed,
   d05d97a36005, by path here). The kit's pj_cbytesR (PRH_Reader.v:107) carries its byte range
   `Forall (fun c => 0 < c < 256) s` first: eve_cstr passes it through.
   Every conclusion is srealizes through SRr. No released plain or UBSan file is Required and no lemma of one is
   cited.
   NUMERALS (rule 7):
   - LENGTH: 256 (the prologue's `addi sp, sp, -256`), 272 (pi_frame F_ex_value = 256 + 32 - 16), 32 / -32 (the
     `andi sp, sp, -32` realignment), 144, 152 (the s1-relative slot the frame is spilled to), 120, 128
     (fs_frame_bytes 1 and its flag-word slot), 96, 56, 24, 16, 12, 8, 4, 1, 0 (frame header, tree node, shadow byte
     counts), 40 (sizeof struct ex), 248 .. 152 (the 13 save-area offsets), 4096 (ESTACK), 16384 / 16656 (the stack
     allowance), 64 (the shadow granule's span), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (shadow and stack bounds, word
     range), 3 (the shadow shift), 27 / 32 (register numbers).
   - WORD: 0x41b58ab3 (the live frame magic), 1 (the use-after-return option's value), 2147450880 (SHADOW_OFF, in
     eve_granule_64).
   - DERIVED: the slot offsets 7364 / 7480 / 7676 / 10088 (= (pc - A_prog_base), the listing's position-abstract pcs),
     the atom numbers of the symbolic engine.
   - ADDRESS: none is written. Every address is pa_sigma / pa_val of the listing instance, a PrhImg field, or a
     Section variable. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* lia here reasons about div / mod (the realignment, the shadow granules): every such step names its div / mod
   facts itself (Z.div_mod, Z.mod_pos_bound) and abstracts the term, so no Euclidean-equation flag is relied on *)
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation PL := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

(* the listing positions this walk uses (DERIVED: pc - A_prog_base) *)
Definition EVE_ENTRY : Z := 7364.   (* 0x832a4, ex_value's entry *)
Definition EVE_RET1 : Z := 7480.    (* 0x83318, the slot after `jal frame_alloc_1` *)
Definition EVE_WS : Z := 7676.      (* 0x833dc, P_WS *)
Definition EVE_EXIT : Z := 10088.    (* 0x83d48, P_EXIT *)

(* the token engine is not used: no shadow byte of this walk is read through a token (every shadow byte it reads is
   a region chunk), so the band is empty and the entry list is nil. *)
Definition EVE_Bx : sv := SLit 0.
Definition EVE_Bspan : Z * Z := (0, 0).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the kit's allocator laws at ARx, at the harness head length cf_head, as pieces 7 + 8 take them (S8aItemsTop.v) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the frame call's rule (YGcallSx.v aj_stack_malloc_at_x) reads errno's place and the low owned bytes: OWNER the image
   instance (PALib's pal_env) and h-mani-a8 (the cf instance's owned-low law) *)
Hypothesis errno_low : api_env SEGS B.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.

(* ---- NAMED HYPOTHESES (each with its exact statement and the owner who supplies it) ---- *)
(* OWNER h-hpreset-7's frame-class lane: the class-1 contract of __asan_stack_malloc_1 over ARx, in its xm form with the
   memnorm keep as the last post conjunct (YGcallMxmn.v:207 astack_malloc_realizes_xm = FCiface.v's
   astack_malloc_realizes_x plus the keep). HYPOTHESIS CHANGE: ASM1 strengthened to the xm form (adds the memnorm keep,
   YGcallMxmn.v:207). DISCHARGE at image A: `FCm01xm.stack_malloc1_contract_xm B ARx I TB` (lib/A/FCm01xm.v:32, Qed,
   origin/cold/h-hpreset-7-frameclass d05d97a36005), given I : fs_iface tfibsegs B ARx and TB : AF0m.TfibSyms B
   (tfibsegs = Img0.rsegs = pa_segs, by conversion). *)
Hypothesis ASM1 : YGcallMxmn.astack_malloc_realizes_xm SEGS B ARx 1.
(* OWNER h-mani-a8 (the cf instance): stack_malloc's model progress and post in ARx form (YGcallSx.v's SMX). *)
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* OWNER the final image instance (AD2l.v TfibB_syms, Qed): image A's symbol record, the image premise every lib/A walk
   over B takes (AF0m.v TfibSyms). It gives the class-1 frame entry (ts_code) and places alloc.c's statics off every
   owned static area (ts_owned) and off errno (ts_errno), by computation. *)
Hypothesis TS : AF0m.TfibSyms B.
(* OWNER a Theorem Labs lane / the final image instance: the listing's object slots are the runtime's cells (YC1fP.v PALib's
   pal_got_shadow / pal_cell / pal_got_uar). *)
Hypothesis GOT_SHADOW : as_got_shadow B = VAL (A_OBJ 0).
Hypothesis GOT_UAR : as_got_uar B = VAL (A_OBJ 1).
Hypothesis CELL_SHADOW : as_shadow_cell B = VAL (A_OBJ 12).
(* OWNER a Theorem Labs lane / the final image instance: the use-after-return option is a 4-byte image word (AImgCells.A_UAR_OPT; its
   value 1 is alx_const's, AR_laws_x field 10), apart from the shadow-base cell and the two GOT words the prologue
   reads. *)
Hypothesis UAR_CELL :
  4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kLowMemEnd /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell B).
(* OWNER h-mani-a8 (the kit's one spelling, PRH_Base.v prh_head_wide; at the preset instance CfParamsPreset.v
   preset_head_wide): a ledger block's head word lies inside its allocator block. *)
Hypothesis HW : prh_head_wide.

#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
Let RUN := paj_run_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS.
Let RUNTO := paj_run_to_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS.
(* the memnorm-keeping runners: YC1fPx's _inv twins at P := YAkMemnorm.memnorm SEGS *)
Let RUNI := paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS).
Let RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS).
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL) (PI := PA).

(* ======== the symbolic states ======== *)

(* ENTRY (0x832a4): the save area below the entry sp, the two GOT words and the two cells they name. *)
Definition eve_regions1 : smem :=
  [ YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 [];
    YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 12) 0))];
    YP09.mkRegion (Some (A_OBJ 12)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))] ].
Definition eve_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 4096 (2 ^ 31) 0)] [] [].
Definition ss_eve1 : sstate := mkSS EVE_ENTRY sr_atoms eve_regions1 None eve_facts1.

(* AFTER THE CALL (0x83318): the frame, its shadow, the body's spill slot, and the two shadow bytes of the
   caller's struct (zero: the real stack's shadow). *)
Definition eve_regions2 : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
    YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
    YP09.mkRegion (Some 33%nat) 0 12 0 12 [];
    YP09.mkRegion (Some 32%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0)); YP09.mkChunk 1 (CVal 1 (SLit 0))] ].
Definition eve_facts2 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46 - 272) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 5);
           (19%nat, mkAF (2 ^ 46) (2 ^ 47) 3); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (33%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)]
          []
          [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 24 0), SOff 32 0);
            (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 8) (SLit 3)) (SOff 24 0), SOff 32 1);
            (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 24 0), SOff 33 0) ].
Definition ss_eve2 : sstate := mkSS EVE_RET1 sr_atoms eve_regions2 None eve_facts2.

(* ---- arithmetic and byte lemmas the walk needs ---- *)
Lemma eve_land32 : forall x, 0 <= x -> Z.land x (-32) = x - x mod 32.
Proof. intros x Hx. change (-32) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity. Qed.
(* a 16-aligned address is 32-aligned or 16 past a 32-aligned one: the realignment's two cases *)
Lemma eve_mod32_cases : forall x, 0 <= x -> x mod 16 = 0 -> x mod 32 = 0 \/ x mod 32 = 16.
Proof.
intros x Hx H16.
pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as Hb.
assert (H : (x mod 32) mod 16 = 0)
  by (rewrite <- (Znumtheory.Zmod_div_mod 16 32 x ltac:(lia) ltac:(lia) ltac:(exists 2; reflexivity)); exact H16).
pose proof (Z.div_mod (x mod 32) 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd.
pose proof (Z.div_pos (x mod 32) 16 ltac:(lia) ltac:(lia)).
assert ((x mod 32) / 16 <= 1) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
Lemma eve_val_mem_of_rd32 : forall (W : world SEGS) mem a v,
  rd32 (aview SEGS (w_H W) mem) a v -> val_mem SEGS (mrestrict (w_H W) mem) a 4 v.
Proof.
intros W mem a v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, H.
pose proof (bv_unsigned_in_range 8 b) as Hr. rewrite H in Hr.
unfold bv_wrap. symmetry. apply Z.mod_small. exact Hr.
Qed.
Lemma eve_val_mem_of_rdword : forall (W : world SEGS) mem a v,
  rdword (aview SEGS (w_H W) mem) a = Some v -> val_mem SEGS (mrestrict (w_H W) mem) a 8 v.
Proof. intros W mem a v H. exact (val_mem_of_rdword SEGS (w_H W) mem a v H). Qed.
(* one byte of memory from its aview *)
Lemma eve_val_mem1 : forall (W : world SEGS) mem x,
  aview SEGS (w_H W) mem x = Some 0 -> val_mem SEGS (mrestrict (w_H W) mem) x 1 0.
Proof.
intros W mem x H k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) x) as [b|] eqn:Eb; cbn [option_map] in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, H. reflexivity.
Qed.
(* the shadow byte of a real-stack granule is 0: the head of zero_shadow_ranges (YG0n.v:188) at a byte.
   (This is `alx_zshadow_byte` of YCbqG at walks-new 9052c7a7d74; on this base it is derived from alx_zshadow,
   which needs the 16 bytes at x to be inside the stack range.) *)
Lemma eve_zsh_byte : forall ly S Hp (W : world SEGS) mem md x,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= x -> x + 16 <= ly_stk_hi ly ->
  aview SEGS (w_H W) mem (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros ly S Hp W mem md x HAR Hlo Hhi.
pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md
  (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as HZ.
cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
specialize (HZ (x / 8 - ly_stk_lo ly / 8)).
replace (SHADOW_OFF + ly_stk_lo ly / 8 + (x / 8 - ly_stk_lo ly / 8)) with (SHADOW_OFF + x / 8) in HZ by lia.
apply HZ. split.
- pose proof (Z.div_le_mono (ly_stk_lo ly) x 8 ltac:(lia) Hlo). lia.
- assert (H1 : x / 8 - ly_stk_lo ly / 8 + 1 <= (x + 16 - ly_stk_lo ly) / 8).
  { apply Z.div_le_lower_bound; [lia|].
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(lia)).
    lia. }
  pose proof (Z.div_le_mono (x + 16 - ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
(* the ledger across a non-allocator memory change: the seven statics and every harness head kept. COPIED SHAPE:
   lib/A/PRH_Keep.v prh_ledger_keep / prh_ledger_keep_av (WalkS8b, cold/h-hpreset-7-walk-S8b b8cc8ce5f57), restated
   here as PRH_Keep.v is not on this base; widths prh_img_A's pi_gz_* (PRH_Img.v:147-159): 8, 8, 8, 8, 1 (g_ran_out),
   8 (g_most), 1 (g_own_ran_out). #102: the kit's prh_glob carries g_most / g_own_ran_out (PRH_Base.v 3004a98fe2d9
   prh_most / prh_own), so the keep carries the two cells as it carries the five. *)
Definition eve_ledger_cell (Lam : list (Z * Z)) (a : Z) : Prop :=
  Exists (in_zr a) PST \/ (exists ak, In ak Lam /\ fst ak - cf_head <= a < fst ak - cf_head + 8).
Lemma eve_ledger_keep : forall ly S Hp (W : world SEGS) mem ly' S' Hp' (W' : world SEGS) mem' Lam peak cnt fail ran
    most own,
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  incl (ablocks B ly S) (ablocks B ly' S') -> Hp' = Hp ->
  (forall a, eve_ledger_cell Lam a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger (PI := prh_img_A) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own LG Hinc -> Hfr.
(* the ledger's facts by the named projections (PRH_Base.v Section ledger_proj, walk kit a941cee76c3f), never by
   position: prh_glob grows on the #102 pins *)
pose proof (prh_ledger_live _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G1.
pose proof (prh_ledger_peak _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G2.
pose proof (prh_ledger_count _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G3.
pose proof (prh_ledger_fail _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G4.
pose proof (prh_ledger_ran _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G5.
pose proof (prh_ledger_most _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G6.
pose proof (prh_ledger_own _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G7.
pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as GR.
pose proof (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HND.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HF.
pose proof (prh_ledger_heads _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HP.
clear LG.
assert (VK : forall x n v, (forall j, 0 <= j < Z.of_nat n -> eve_ledger_cell Lam (x + j)) ->
   val_mem SEGS (mrestrict (w_H W) mem) x n v -> val_mem SEGS (mrestrict (w_H W') mem') x n v).
{ intros x n v Hc Hv j Hj. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' (x + Z.of_nat j))
    by (apply Hfr; apply Hc; lia). exact (Hv j Hj). }
assert (VS : forall b w j, In (b, w) PST -> 0 <= j < w -> eve_ledger_cell Lam (b + j)).
{ intros b w j Hin Hj. left. apply Exists_exists. exists (b, w). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
unfold prh_ledger, prh_glob, prh_most, prh_own.
unfold prh_most in G6. unfold prh_own in G7.
split; [|split; [exact HND | split; [| exact HP]]].
- split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G1]|].
  split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G2]|].
  split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G3]|].
  split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G4]|].
  split; [apply (VK _ 1%nat); [intros j Hj; apply (VS _ 1); [unfold prh_pst; cbn [In]; tauto | lia] | exact G5]|].
  split; [split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact (proj1 G6)] | exact (proj2 G6)]|].
  split; [split; [apply (VK _ 1%nat); [intros j Hj; apply (VS _ 1); [unfold prh_pst; cbn [In]; tauto | lia] | exact (proj1 G7)] | exact (proj2 G7)]|].
  exact GR.
- apply Forall_forall. intros ak Hak. pose proof (proj1 (Forall_forall _ _) HF ak Hak) as (K0 & K1 & K2 & K3 & K4).
  split; [exact K0|]. split; [exact (Hinc _ K1)|]. split; [exact K2|]. split; [exact K3|].
  apply (VK _ 8%nat); [|exact K4]. intros j Hj. right. exists ak. split; [exact Hak | lia].
Qed.
(* a callee-saved register at its bv name *)
Lemma eve_kept : forall (regs regs' : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' z r H Hc Hz. pose proof (H z Hc) as HH.
rewrite <- Hz, Z_to_bv_bv_unsigned in HH. exact HH.
Qed.

(* ---- byte transports (COPIED from h-walk-ctrl's S8aP7a.v p7a_vm / p7a_garr8 / p7a_wr_present / p7a_wr_av,
   origin/cold/h-walk-ctrl-S8a-items-kit 0da1b512183 :153-206, restated at this file's names) ---- *)
Lemma eve_vm : forall (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> mbyte SEGS m' z = mbyte SEGS m z) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H k Hk. rewrite E by lia. exact (H k Hk). Qed.
Lemma eve_garr8 : forall (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' a l E H j Hj. destruct (H j Hj) as [Hv Hb]. split; [|exact Hb].
apply (eve_vm m m'); [|exact Hv]. intros z Hz. apply E. lia.
Qed.
Lemma eve_vm_av : forall H H' (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> aview SEGS H' m' z = aview SEGS H m z) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v E. apply eve_vm. intros z Hz. exact (mbyte_of_aview SEGS H H' m m' z (E z Hz)).
Qed.
Lemma eve_wr_present : forall H (m : word -> option byte) z, 0 <= z < 2 ^ 64 -> ~ in_img SEGS z ->
  writable_at SEGS (mrestrict H m) z -> apresent H m z.
Proof.
intros H m z Hz Hni Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent.
assert (Hseg : find_segment SEGS (bv_unsigned (Z_to_bv 64 z)) 1 = None).
{ destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 z)) 1) as [seg|] eqn:Ef; [|reflexivity].
  exfalso. apply Hni. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by lia. exists seg. split; [exact Hin|lia]. }
destruct (H (Z_to_bv 64 z)).
- rewrite Hseg in Hw. exfalso. apply Hw. reflexivity.
- split; [reflexivity|]. destruct (m (Z_to_bv 64 z)) as [b|].
  + exists b. reflexivity.
  + rewrite Hseg in Hw. exfalso. apply Hw. reflexivity.
Qed.
Lemma eve_wr_av : forall H H' (m m' : word -> option byte) z, 0 <= z < 2 ^ 64 -> ~ in_img SEGS z ->
  aview SEGS H' m' z = aview SEGS H m z -> writable_at SEGS (mrestrict H m) z -> writable_at SEGS (mrestrict H' m') z.
Proof.
intros H H' m m' z Hz Hni E Hw. apply (apresent_writable SEGS).
exact (apresent_transfer SEGS H H' m m' z Hz Hni E (eve_wr_present H m z Hz Hni Hw)).
Qed.

(* ---- the reader's tree is kept when its node bytes and its lblk blocks keep their value and their writability
   (COPIED from S8aP7a.v p7a_P2 / p7a_cstr / p7a_hdr / p7a_nodeP / p7a_items_frame / p7a_mems_frame / p7a_nodeR_frame,
   0da1b512183 :210-332) ---- *)
Definition eve_P2 (m m' : word -> option byte) (z : Z) : Prop :=
  mbyte SEGS m' z = mbyte SEGS m z /\ (writable_at SEGS m z -> writable_at SEGS m' z).
Lemma eve_cstr : forall (m m' : word -> option byte) lblk a k s,
  (forall z, a <= z < a + k -> eve_P2 m m' z) ->
  PRH_Reader.pj_cstrR SEGS m lblk a k s -> PRH_Reader.pj_cstrR SEGS m' lblk a k s.
Proof.
intros m m' lblk a k s E (Hl & Hk & Hf & Hc & Hg). split; [exact Hl|]. split; [exact Hk|]. split; [exact Hf|].
(* the kit's pj_cbytesR (PRH_Reader.v) is `Forall (fun c => 0 < c < 256) s /\ garr8 segs m a (s ++ [0])` *)
split; [exact Hc|].
apply (eve_garr8 m m'); [|exact Hg]. intros z Hz. apply E. rewrite length_app in Hz. cbn [length] in Hz. lia.
Qed.
Lemma eve_hdr : forall (m m' : word -> option byte) p ty num str kids keys n cap,
  (forall z, p <= z < p + 56 -> eve_P2 m m' z) ->
  PRH_Reader.pj_hdrR SEGS m p ty num str kids keys n cap -> PRH_Reader.pj_hdrR SEGS m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap E
  ((Hal & Hrw) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)).
assert (EV : forall b e, p <= b -> b + e <= p + 56 -> forall z, b <= z < b + e -> mbyte SEGS m' z = mbyte SEGS m z)
  by (intros b e Hb He z Hz; exact (proj1 (E z ltac:(lia)))).
split; [split; [exact Hal|intros x Hx; exact (proj2 (E x Hx) (Hrw x Hx))]|].
split; [split; [exact T0|apply (eve_vm m m'); [apply (EV p 4); lia|exact T1]]|].
split; [split; [exact N0|apply (eve_vm m m'); [apply (EV (p + 8) 8); lia|exact N1]]|].
split; [split; [exact S0|apply (eve_vm m m'); [apply (EV (p + 16) 8); lia|exact S1]]|].
split; [split; [exact K0|apply (eve_vm m m'); [apply (EV (p + 24) 8); lia|exact K1]]|].
split; [split; [exact Y0|apply (eve_vm m m'); [apply (EV (p + 32) 8); lia|exact Y1]]|].
split; [split; [exact C0|apply (eve_vm m m'); [apply (EV (p + 40) 8); lia|exact C1]]|].
split; [exact P0|apply (eve_vm m m'); [apply (EV (p + 48) 8); lia|exact P1]].
Qed.
Definition eve_nodeP (m m' : word -> option byte) (lblk : Z -> Z -> Prop) (t : PjTree.jv) : Prop :=
  forall p D, PRH_Reader.pj_nodeR SEGS m lblk p t D ->
  (forall z, (p <= z < p + 56 \/ exists b k, In (b, k) D /\ lblk b k /\ b <= z < b + k) -> eve_P2 m m' z) ->
  PRH_Reader.pj_nodeR SEGS m' lblk p t D.
Lemma eve_items_frame : forall (m m' : word -> option byte) lblk (items : list PjTree.jv),
  Forall (eve_nodeP m m' lblk) items ->
  forall a Di, PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m lblk) a items Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length items) -> eve_P2 m m' z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> eve_P2 m m' z) ->
  PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m' lblk) a items Di.
Proof.
intros m m' lblk items IH. induction IH as [|u r Hu Hr IHr]; intros a Di H E1 E2;
  cbn [PRH_Reader.pj_itemsR] in H |- *.
- exact H.
- destruct H as (D1 & D2 & ED & H1 & H2). exists D1, D2. split; [exact ED|]. split.
  + apply (Hu a D1 H1). intros z [Hz|(b & k & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E2. exists b, k. split; [rewrite ED; apply in_or_app; left; exact Hin|]. split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z (b & k & Hin & Hl & Hz). apply E2. exists b, k.
      split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.
Lemma eve_mems_frame : forall (m m' : word -> option byte) lblk (members : list (list Z * PjTree.jv)),
  Forall (fun mm => eve_nodeP m m' lblk (snd mm)) members ->
  forall a ka Di, PRH_Reader.pj_memsR SEGS m lblk (PRH_Reader.pj_nodeR SEGS m lblk) a ka members Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length members) -> eve_P2 m m' z) ->
  (forall z, ka <= z < ka + 8 * Z.of_nat (length members) -> eve_P2 m m' z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> eve_P2 m m' z) ->
  PRH_Reader.pj_memsR SEGS m' lblk (PRH_Reader.pj_nodeR SEGS m' lblk) a ka members Di.
Proof.
intros m m' lblk members IH. induction IH as [|mm r Hu Hr IHr]; intros a ka Di H E1 E2 E3.
- cbn [PRH_Reader.pj_memsR] in H |- *. exact H.
- destruct mm as [nm u]. cbn [PRH_Reader.pj_memsR snd] in H, Hu |- *.
  destruct H as (x & k & D1 & D2 & ED & (Hx0 & Hx) & Hc & H1 & H2).
  exists x, k, D1, D2. split; [exact ED|].
  split; [split; [exact Hx0|apply (eve_vm m m'); [intros z Hz; apply E2; cbn [length]; lia|exact Hx]]|].
  split.
  { apply (eve_cstr m m'); [|exact Hc]. intros z Hz. apply E3. exists x, k.
    split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz]. }
  split.
  + apply (Hu a D1 H1). intros z [Hz|(b & kk & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E3. exists b, kk. split; [rewrite ED; right; apply in_or_app; left; exact Hin|].
      split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) (ka + 8) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z Hz. apply E2. cbn [length]. lia.
    * intros z (b & kk & Hin & Hl & Hz). apply E3. exists b, kk.
      split; [rewrite ED; right; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.
Lemma eve_nodeR_frame : forall (m m' : word -> option byte) lblk t, eve_nodeP m m' lblk t.
Proof.
intros m m' lblk t.
induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; unfold eve_nodeP; intros p D H E;
  cbn [PRH_Reader.pj_nodeR] in H |- *;
  destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & R);
  (split; [exact ND|]); (split; [exact AP|]);
  exists num, str, kids, keys, n, cap;
  (split; [apply (eve_hdr m m'); [intros z Hz; apply E; left; exact Hz|exact HH]|]).
- exact R.
- exact R.
- exact R.
- destruct R as (R1 & R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 5 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (eve_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 4 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (eve_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & R5 & Di & ED & HI).
  do 5 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (eve_items_frame m m' lblk items IH kids Di HI).
  + intros z Hz. apply E. right. destruct R5 as [(Hc0 & _)|(Hc0 & Hl)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & Di & ED & HM).
  do 4 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (eve_mems_frame m m' lblk members IH kids keys Di HM).
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists keys, (8 * cap). split; [|split; [exact Hl2|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

(* ---- shadow facts at a state of the walk (COPIED from h-walk-ctrl's S8aItems.v ev_hp_apart / ev_inblk_shadow_FIX /
   ev_lam_shadow / ev_hull_sub / ev_lam_hull :1025-1116 and S8aP7a.v p7a_inblk_hull :439-452 and YGcallHull.v
   shadow_granule_64 / stack_hull_vis_x_rng :35-59, 0da1b512183; field 14 alx_hshadow at hl := cf_head) ---- *)
Lemma eve_hull_sub : forall (rd : Z -> option Z) p mm d n, shadow_hull_vis rd p mm -> p <= d -> d + n <= p + mm ->
  0 < n -> shadow_hull_vis rd d n.
Proof.
intros rd p mm d n H Hpd Hdn Hn s Hs. apply H.
assert (M : forall x y, x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8).
{ intros x y Hxy. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
pose proof (M p d Hpd). pose proof (M (d + n - 1) (p + mm - 1) ltac:(lia)). lia.
Qed.
Lemma eve_hp_apart : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR (_ & _ & HF & HP) Hin Hnb h Hh Hr.
pose proof (Permutation_in _ HP Hh) as Hh'.
apply in_map_iff in Hh' as ([a' k] & Eh & Hak). cbn [fst] in Eh.
destruct (proj1 (Forall_forall _ _) HF (a', k) Hak) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
rewrite Eh in Hblk.
assert (Hne : (b, m) <> (h, k + cf_head)).
{ intros E. injection E as E1 _. rewrite E1 in Hnb. exact (Hnb Hh). }
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m h (k + cf_head) HAR Hin Hblk Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (H1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.
Lemma eve_inblk_shadow : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a len,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_inblk B ly S Hp a len -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a len HAR HLED (b & m & Hin & Hba & Hab & Hhd) Hlen.
destruct (Z.eq_dec len 0) as [->|Hl0]; [apply range_addressable_nil; lia|].
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (in_dec Z.eq_dec b Hp) as [Hb | Hb].
- destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin Hb) as [Hbs _].
  specialize (Hhd Hb).
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (alx_shadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin
    (eve_hp_apart ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hb)) as [Hbs _].
  eapply block_shadow_range; [exact Hbs | lia | lia].
Qed.
Lemma eve_inblk_hull : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a len,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_inblk B ly S Hp a len -> 0 < len ->
  shadow_hull_vis (aview SEGS (w_H W) mem) a len.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a len HAR HLED (b & m & Hin & Hba & Hab & Hhd) Hlen.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (in_dec Z.eq_dec b Hp) as [Hb | Hb].
- specialize (Hhd Hb). destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin Hb) as [_ Hhv].
  apply (eve_hull_sub _ (b + cf_head) (req_size m - cf_head)); [apply Hhv; lia|lia|lia|lia].
- destruct (alx_shadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin
    (eve_hp_apart ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hb)) as [_ Hhv].
  apply (eve_hull_sub _ b (req_size m)); [exact Hhv|lia|lia|lia].
Qed.
Lemma eve_lam_shadow : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own b m a len,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) Lam -> b <= a -> a + len <= b + m -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m a len HAR HLED Hin Hba Hab Hlen.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & Hhp & _).
cbn [fst snd] in Hm0, Hblk, Hhp.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (Z.eq_dec len 0) as [->|Hl0]; [apply range_addressable_nil; lia|].
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk Hhp) as [Hbs _].
assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
rewrite Hrq in Hbs.
replace (b - cf_head + cf_head) with b in Hbs by lia. replace (m + cf_head - cf_head) with m in Hbs by lia.
eapply block_shadow_range; [exact Hbs | exact Hba | exact Hab].
Qed.
Lemma eve_lam_hull : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own b m a len,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) Lam -> b <= a -> a + len <= b + m -> 0 < len ->
  shadow_hull_vis (aview SEGS (w_H W) mem) a len.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m a len HAR HLED Hin Hba Hab Hlen.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & Hhp & _).
cbn [fst snd] in Hm0, Hblk, Hhp.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk Hhp) as [_ Hhull].
assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
rewrite Hrq in Hhull.
replace (b - cf_head + cf_head) with b in Hhull by lia. replace (m + cf_head - cf_head) with m in Hhull by lia.
apply (eve_hull_sub _ b m a len); [apply Hhull; lia | lia | lia | lia].
Qed.
Lemma eve_granule_64 : forall x, shadow_addr x / 8 * 8 = SHADOW_OFF + x / 64 * 8.
Proof.
intro x. unfold shadow_addr, SHADOW_OFF.
replace (2147450880 + x / 8) with (268431360 * 8 + x / 8) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.
Lemma eve_stack_hull : forall ly S Hp (W : world SEGS) mem md v n,
  ARx ly S Hp W mem md ->
  ly_stk_lo ly <= v / 64 * 64 -> (v + n - 1) / 64 * 64 + 64 <= ly_stk_hi ly ->
  shadow_hull_vis (aview SEGS (w_H W) mem) v n.
Proof.
intros ly S Hp W mem md v n HAR Hlo Hhi s Hs.
rewrite !eve_granule_64 in Hs.
assert (Hb : ly_stk_lo ly <= 8 * (s - SHADOW_OFF) < ly_stk_hi ly) by lia.
pose proof (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md _ HAR Hb) as Z0.
assert (E : SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8 = s) by (rewrite (Z.mul_comm 8), Z.div_mul by lia; lia).
rewrite E in Z0. rewrite Z0. discriminate.
Qed.
(* ---- the two hull facts pieces 7 + 8 carry as HFHULL / HSTK64 (S8aItemsTop.v :93-95), DERIVED here from AR_laws_x
   field 18 (alx_layout_ok, YCbqG.v c3b5d0111037) through named projections only: the real stack's top is
   64-aligned (YCbqG.v stk_aligned_x); a live fake frame of 56 bytes or more is 64-aligned (layout_ok's lo_F_al:
   ly_F page aligned; every term of fs_frame_off is a multiple of 64 for a class cid >= 0), so its shadow hull is
   exactly its own fs_frame_bytes cid / 8 shadow bytes, present by field 3 (alx_frames) ---- *)
Lemma eve_stk64 : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0.
Proof. intros ly S Hp W mem md HAR. exact (proj2 (stk_aligned_x SEGS B ARx LAWS ly S Hp W mem md HAR)). Qed.
Lemma eve_fs_cid : forall c, 56 <= fs_frame_bytes c -> 0 <= c.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z.le_gt_cases 0 c) as [Hc|Hc]; [exact Hc|].
exfalso. assert (En : c = - (- c)) by lia. remember (- c) as n eqn:Hn. rewrite En in H.
rewrite Z.shiftl_div_pow2 in H by lia. rewrite ?Z.opp_involutive in H.
assert (H2 : 2 <= 2 ^ n).
{ replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
assert (H3 : 64 / 2 ^ n <= 64 / 2) by (apply Z.div_le_compat_l; lia).
change (64 / 2) with 32 in H3. pose proof (Z.le_trans _ _ _ H H3) as H5. apply H5. reflexivity.
Qed.
Lemma eve_frame_hull : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 56 <= fs_frame_bytes cid ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md cid pos HAR Hin H56.
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & _ & _ & HSP).
pose proof (lo_F_al _ (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR)) as HF. unfold page_aligned in HF.
pose proof (eve_fs_cid cid H56) as Hc.
pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc) as Ht0.
assert (Hfs : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
assert (Hfa : frame_addr ly cid pos = 64 * (ly_F ly / 4096 * 64 + 576 + cid * 16384 + pos * 2 ^ cid)).
{ unfold frame_addr, fs_frame_off, kFakeFramesOff, kStackSizeLog. change (Z.shiftl 1 20) with 1048576. rewrite Hfs.
  pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
  set (fq := ly_F ly / 4096) in D |- *. rewrite D. ring. }
set (u := ly_F ly / 4096 * 64 + 576 + cid * 16384 + pos * 2 ^ cid) in Hfa.
set (t := 2 ^ cid) in *.
assert (Hsh : shadow_addr (frame_addr ly cid pos) = SHADOW_OFF + u * 8).
{ unfold shadow_addr. rewrite Hfa. replace (64 * u) with ((u * 8) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Hf8 : fs_frame_bytes cid / 8 = t * 8).
{ rewrite Hfs. replace (64 * t) with ((t * 8) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
intros s Hs. rewrite !eve_granule_64 in Hs. rewrite Hfa, Hfs in Hs.
replace (64 * u) with (u * 64) in Hs by ring. rewrite Z.div_mul in Hs by lia.
replace (u * 64 + 64 * t - 1) with ((u + t - 1) * 64 + 63) in Hs by ring.
rewrite Z.div_add_l in Hs by lia. change (63 / 64) with 0 in Hs.
destruct (HSP (s - shadow_addr (frame_addr ly cid pos)) ltac:(rewrite Hf8, Hsh; lia)) as [Hps _].
replace (shadow_addr (frame_addr ly cid pos) + (s - shadow_addr (frame_addr ly cid pos))) with s in Hps by lia.
exact (aview_some_of_apresent SEGS _ _ _ Hps).
Qed.

(* ---- alloc.c's statics (PST) and the class-1 frame entry, from TS, by computation (COPIED SHAPE: h-hpreset-7's
   PwPstUnowned.v pu_off_b / pu_off_sound / pst_off_owned_A, origin/cold/h-hpreset-7-pst-unowned 1faacee1304) ---- *)
Definition eve_off_b (P O : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun o => (fst r + snd r <=? fst o) || (fst o + snd o <=? fst r)) O) P.
Lemma eve_off_sound : forall P O a, eve_off_b P O = true -> Exists (in_zr a) P -> ~ Exists (in_zr a) O.
Proof.
intros P O a H HP HO. apply Exists_exists in HP as (r & Hr & Ha). apply Exists_exists in HO as (o & Ho & Hb).
unfold eve_off_b in H. rewrite forallb_forall in H. specialize (H r Hr). rewrite forallb_forall in H.
specialize (H o Ho). unfold in_zr in Ha, Hb.
apply Bool.orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Definition eve_in_seg_b (r : Z * Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) &&
    (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) SEGS.
Lemma eve_pst_chk : eve_off_b PST AF0m.Tfib_owned_static = true /\ forallb eve_in_seg_b PST = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma eve_pst_unowned : forall z, Exists (in_zr z) PST -> ~ Exists (in_zr z) (as_owned_static B).
Proof. intros z Hz. rewrite (AF0m.ts_owned _ TS). exact (eve_off_sound _ _ z (proj1 eve_pst_chk) Hz). Qed.
Lemma eve_pst_errno : forall z, Exists (in_zr z) PST -> ~ (as_errno B <= z < as_errno B + 4).
Proof.
intros z Hz He. apply (eve_off_sound PST [(as_errno B, 4)] z); [| exact Hz |].
- rewrite (AF0m.ts_errno _ TS). vm_compute. reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact He.
Qed.
Lemma eve_pst_img : forall z, Exists (in_zr z) PST -> in_img SEGS z.
Proof.
intros z Hz. apply Exists_exists in Hz as (r & Hr & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) (proj2 eve_pst_chk) r Hr) as Hb. unfold eve_in_seg_b in Hb.
apply existsb_exists in Hb as (sg & Hsg & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold in_img. exists sg. split; [exact Hsg | lia].
Qed.
Lemma eve_sm1_pc : SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1.
Proof. rewrite (AF0m.ts_code _ TS). vm_compute. reflexivity. Qed.

(* ---- small transports (COPIED from S8aP7a.v p7a_garr_av / p7a_rdword / p7a_cur_keep / p7a_fs8 / p7a_sh_in,
   0da1b512183 :178-183, :408-436, :1490-1500) ---- *)
Lemma eve_garr_av : forall H H' (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> aview SEGS H' m' z = aview SEGS H m z) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l E. apply eve_garr8. intros z Hz. exact (mbyte_of_aview SEGS H H' m m' z (E z Hz)).
Qed.
Lemma eve_rdword : forall (rd rd' : Z -> option Z) x,
  (forall i, 0 <= i < 8 -> rd' (x + i) = rd (x + i)) -> rdword rd' x = rdword rd x.
Proof.
intros rd rd' x E. pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. unfold rdword.
rewrite E0, (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7) by lia. reflexivity.
Qed.
Lemma eve_cur_keep : forall (W W' : world SEGS) mem mem' q p e dep scr dl,
  prhex_cur W mem q p e dep scr dl ->
  (forall z, q <= z < q + 40 -> aview SEGS (w_H W') mem' z = aview SEGS (w_H W) mem z) ->
  prhex_cur W' mem' q p e dep scr dl.
Proof.
intros W W' mem mem' q p e dep scr dl (Q1 & Q2 & Q3 & Q4 & Q5) HK.
split; [apply eve_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q1]|].
split; [apply eve_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q2]|].
split; [apply eve_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q3]|].
split; [apply eve_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q4]|].
apply eve_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q5].
Qed.
Lemma eve_fs8 : forall c, 56 <= fs_frame_bytes c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z.le_gt_cases 0 c) as [Hc|Hc].
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z.mod_mul. lia.
- exfalso. assert (En : c = - (- c)) by lia. remember (- c) as n eqn:Hn. rewrite En in H.
  rewrite Z.shiftl_div_pow2 in H by lia. rewrite ?Z.opp_involutive in H.
  assert (H2 : 2 <= 2 ^ n).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (H3 : 64 / 2 ^ n <= 64 / 2) by (apply Z.div_le_compat_l; lia).
  change (64 / 2) with 32 in H3. pose proof (Z.le_trans _ _ _ H H3) as H5. apply H5. reflexivity.
Qed.
Lemma eve_sh_in : forall fa fs x, fa mod 8 = 0 -> fs mod 8 = 0 -> fa <= x < fa + fs ->
  fa / 8 <= x / 8 < fa / 8 + fs / 8.
Proof.
intros fa fs x Ha Hs Hx. pose proof (Z.div_mod fa 8 ltac:(lia)) as Da. pose proof (Z.div_mod fs 8 ltac:(lia)) as Ds.
rewrite Ha, Z.add_0_r in Da. rewrite Hs, Z.add_0_r in Ds.
split; [apply Z.div_le_mono; lia|].
apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_add_distr_l. rewrite <- Da, <- Ds. lia.
Qed.

(* ======== the cut P_WS (0x833dc): ev_at_ws from what the walk reaches there ========
   The machine part (the three runs, the frame call) ends with the journal from entry, the five keeping facts (every
   byte at or above the entry sp, every byte of a block live at entry, every image byte that is no owned static and no
   errno byte, every byte and shadow byte of a frame live at entry), the save area, the frame's flag word and the
   registers. ev_mid's other conjuncts follow here: the ledger (its cells: alloc.c's statics by TS, the block heads
   inside their blocks by HW), the cursor and the text's / scratch's / tree's bytes by the keeping facts, and their
   shadow facts from the laws at the NEW state (the frame call keeps no shadow byte the runtime owns): field 14
   alx_hshadow / alx_shadow for a block, alx_zshadow_byte for the real stack, the kept frame shadow for a fake frame,
   eve_frame_hull / eve_stk64 (field 18) for a root's hull; the room by PrhRoomLive's RL_set_fs (the call sets st_fs
   only). *)
Lemma eve_at_ws_of : forall (a : ev_act) pos S2 regs mem md,
  ev_pre (PI := prh_img_A) (PA := PA) B ARx a ->
  AJ (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a)
    (ea_mem a) (ea_md a) [(1, pos)] (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md 0 ->
  frames S2 = (1, pos) :: frames (ea_S a) ->
  ablocks B (ea_ly a) S2 = ablocks B (ea_ly a) (ea_S a) ->
  (exists f, S2 = set_fs f (ea_S a)) ->
  (forall z, ea_sp0 a <= z < 2 ^ 64 -> aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z) ->
  (forall b m i, In (b, m) (ablocks B (ea_ly a) (ea_S a)) -> 0 <= i < req_size m ->
     aview SEGS (w_H (ea_W a)) mem (b + i) = aview SEGS (w_H (ea_W a)) (ea_mem a) (b + i)) ->
  (forall z, in_img SEGS z -> ~ Exists (in_zr z) (as_owned_static B) -> ~ (as_errno B <= z < as_errno B + 4) ->
     aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z) ->
  (forall cid pos' z, In (cid, pos') (frames (ea_S a)) ->
     (in_zr z (frame_rng (ea_ly a) (cid, pos')) \/
      in_zr z (shadow_addr (frame_addr (ea_ly a) cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z) ->
  ev_saved (ev_setpos a pos) (ea_W a) mem ->
  rdword (aview SEGS (w_H (ea_W a)) mem) (frame_addr (ea_ly a) 1 pos + 128 - 8) = Some (flag_addr (ea_ly a) 1 pos) ->
  ev_regs (ev_setpos a pos) regs ->
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) -> getr regs 22 = w64 (frame_addr (ea_ly a) 1 pos) ->
  getr regs 23 = w64 (ea_v a) ->
  YAkMemnorm.memnorm SEGS mem ->
  ev_at_ws (PI := prh_img_A) (PA := PA) B ARx SK (ev_setpos a pos) (ea_W a) regs mem md (ea_ly a) S2 (ea_Hp a) 0.
Proof.
intros a pos S2 regs mem md HPRE HJ Hfrs Eab HSfs KHI KBLK KIMG KFRM HSAV HFLAG HREGS H20 H22 H23 HMN.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & Hcur & Hq8 & _ & Hqlo & Hqhi & Hwin & Hsrc & Hinblk & _ & _ & _ & _ & _ &
  Hwd & Hscrblk & _ & _ & Hscrx & Hled & _).
destruct HFPRE as (HPRE0 & _).
pose proof HPRE0 as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HW as HW8. unfold prh_head_wide in HW8.
assert (HSTKlo : 16656 <= ea_STK (PI := prh_img_A) a).
{ assert (HSTK : ea_STK (PI := prh_img_A) a = Z.of_nat (S (ea_n a)) * 272 + 16384).
  { unfold ea_STK, STK_ex_value. cbn [pi_frame prh_img_A]. f_equal; try (vm_compute; reflexivity). }
  rewrite HSTK. pose proof (Nat2Z.is_nonneg (ea_n a)). nia. }
pose proof HJ as (HAR2 & _).
(* the ledger at the new state: its cells are kept *)
assert (HLED2 : prh_ledger (PI := prh_img_A) B (ea_ly a) S2 (ea_Hp a) (ea_W a) mem (ea_Lam a) (ea_peak a) (ea_cnt a)
  (ea_fail a) (ea_ran a) (ea_most a) (ea_own a)).
{ apply (eve_ledger_keep (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) _ _ _ _ _ _ _ _ _ _ _ _ Hled).
  - rewrite Eab. apply incl_refl.
  - reflexivity.
  - intros z Hz. unfold eve_ledger_cell in Hz. destruct Hz as [Hz|(ak & Hak & Hz)].
    + exact (KIMG z (eve_pst_img z Hz) (eve_pst_unowned z Hz) (eve_pst_errno z Hz)).
    + pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ Hled) as HHB.
      destruct (proj1 (Forall_forall _ _) HHB ak Hak) as (Hk0 & Hblk & _).
      assert (Hrq : snd ak + cf_head <= req_size (snd ak + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (snd ak + cf_head) 0); lia).
      replace z with (fst ak - cf_head + (z - (fst ak - cf_head))) by lia.
      apply (KBLK _ (snd ak + cf_head)); [exact Hblk | lia]. }
(* a range inside a block live at entry: its bytes are kept; the block is live at the new state *)
assert (INB2 : forall x n, prhex_inblk B (ea_ly a) (ea_S a) (ea_Hp a) x n -> prhex_inblk B (ea_ly a) S2 (ea_Hp a) x n).
{ unfold prhex_inblk. rewrite Eab. tauto. }
assert (INBK : forall x n z, prhex_inblk B (ea_ly a) (ea_S a) (ea_Hp a) x n -> x <= z < x + n ->
   aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros x n z (b & m & Hin & Hbx & Hxm & _) Hz.
  assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  replace z with (b + (z - b)) by lia. apply (KBLK b m); [exact Hin | lia]. }
unfold ev_at_ws, ev_mid.
try change (ea_x0 (ev_setpos a pos)) with (ea_x0 a). try change (ea_i0 (ev_setpos a pos)) with (ea_i0 a).
try change (ea_dep (ev_setpos a pos)) with (ea_dep a). try change (ea_dl (ev_setpos a pos)) with (ea_dl a).
try change (ea_STK (ev_setpos a pos)) with (ea_STK (PI := prh_img_A) a).
try change (ea_d (ev_setpos a pos)) with (ea_d a). try change (ea_sp0 (ev_setpos a pos)) with (ea_sp0 a).
try change (ea_FP (ev_setpos a pos)) with (ea_FP a). try change (ea_ly (ev_setpos a pos)) with (ea_ly a).
try change (ea_S (ev_setpos a pos)) with (ea_S a). try change (ea_Hp (ev_setpos a pos)) with (ea_Hp a).
try change (ea_W (ev_setpos a pos)) with (ea_W a). try change (ea_mem (ev_setpos a pos)) with (ea_mem a).
try change (ea_md (ev_setpos a pos)) with (ea_md a). try change (ea_pos (ev_setpos a pos)) with pos.
try change (ea_Lam (ev_setpos a pos)) with (ea_Lam a). try change (ea_peak (ev_setpos a pos)) with (ea_peak a).
try change (ea_cnt (ev_setpos a pos)) with (ea_cnt a). try change (ea_fail (ev_setpos a pos)) with (ea_fail a).
try change (ea_ran (ev_setpos a pos)) with (ea_ran a). try change (ea_q (ev_setpos a pos)) with (ea_q a).
try change (ea_len (ev_setpos a pos)) with (ea_len a). try change (ea_scr (ev_setpos a pos)) with (ea_scr a).
try change (ea_x (ev_setpos a pos)) with (ea_x a). try change (ea_regs (ev_setpos a pos)) with (ea_regs a).
try change (ea_v (ev_setpos a pos)) with (ea_v a). try change (ea_t (ev_setpos a pos)) with (ea_t a).
try change (ea_D (ev_setpos a pos)) with (ea_D a).
try change (ea_fr (ev_setpos a pos)) with (frame_addr (ea_ly a) 1 pos).
split.
2:{ split; [exact HREGS|]. split; [exact H20|]. split; [exact H22|exact H23]. }
(* the journal *)
split; [exact HJ|].
(* the caller window: at or above the entry sp *)
split; [intros z Hz _; apply KHI; lia|].
split; [reflexivity|].
split; [exact Eab|].
split; [exact HLED2|].
(* the cursor: struct ex at q, above the entry sp *)
split; [apply (eve_cur_keep (ea_W a) (ea_W a) (ea_mem a) mem); [exact Hcur|intros z Hz; apply KHI; lia]|].
(* the text *)
split.
{ destruct Hsrc as (HBY & H4 & HCE & HAM & HRA & HHU). unfold bytes_at in *.
  split.
  { apply (eve_garr_av (w_H (ea_W a)) (w_H (ea_W a)) (ea_mem a) mem); [|exact HBY].
    intros z Hz. apply (INBK (ea_x0 a) (ea_len a)); [apply Hinblk; unfold ea_len; lia | unfold ea_len; lia]. }
  split; [exact H4|]. split; [exact HCE|]. split; [exact HAM|].
  split.
  { destruct (Z_lt_le_dec 0 (Z.of_nat (length (ea_x a)))) as [Hl|Hl]; [|apply range_addressable_nil; lia].
    apply (eve_inblk_shadow (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a)
      (ea_ran a) (ea_most a) (ea_own a)); [exact HAR2 | exact HLED2 | apply INB2; apply Hinblk; unfold ea_len; exact Hl | lia]. }
  intros Hl. apply (eve_inblk_hull (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a)
    (ea_ran a) (ea_most a) (ea_own a)); [exact HAR2 | exact HLED2 | apply INB2; apply Hinblk; unfold ea_len; exact Hl | exact Hl]. }
(* the scratch *)
split.
{ destruct Hwd as (HD0 & HDC & HAM & HWW & HRA & HHU).
  pose proof Hscrblk as (bs & msz & Hbs & Hbs1 & Hbs2 & _).
  assert (Rs : msz <= req_size msz) by (unfold req_size; destruct (Z.eqb_spec msz 0); lia).
  destruct (alx_blocks SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md bs msz HAR2
    ltac:(rewrite Eab; exact Hbs)) as (_ & _ & _ & _ & Hpr2 & _).
  split; [exact HD0|]. split; [exact HDC|]. split; [exact HAM|].
  split.
  { intros z Hz. destruct (HWW z Hz) as (_ & _ & Hs). destruct (Hpr2 z ltac:(lia)) as [Hp2z Ho2].
    split; [exact (apresent_writable SEGS _ _ _ Hp2z)|]. split; [exact Ho2|exact Hs]. }
  split.
  { apply (eve_inblk_shadow (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a)
      (ea_ran a) (ea_most a) (ea_own a)); [exact HAR2 | exact HLED2 | apply INB2; exact Hscrblk | unfold ea_len; lia]. }
  intros Hl. apply (eve_inblk_hull (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a)
    (ea_ran a) (ea_most a) (ea_own a)); [exact HAR2 | exact HLED2 | apply INB2; exact Hscrblk | exact Hl]. }
(* the tree *)
split.
{ destruct Hscrx as [Hv0|((HN & HH & HRA & HHV) & _ & _)]; [left; exact Hv0|]. right.
  assert (LAMK : forall b k z, In (b, k) (ea_Lam a) -> b <= z < b + k ->
    aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
  { intros b k z Hin Hz. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ Hled) as HHB.
    destruct (proj1 (Forall_forall _ _) HHB (b, k) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
    assert (Hrq : k + cf_head <= req_size (k + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ (b - cf_head) (k + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
    split; [replace z with (b - cf_head + (z - (b - cf_head))) by lia; apply (KBLK _ (k + cf_head)); [exact Hblk|lia]|].
    split; [apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ (b - cf_head) (k + cf_head) z HAR Hblk); lia|lia]. }
  assert (ROOT : forall z, ea_v a <= z < ea_v a + 56 ->
    aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
  { intros z Hz.
    destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos' & Hin & H1 & H2)|(H1 & H2)]].
    - apply (LAMK b mm z Hin). lia.
    - destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Fa & Fc & _).
      split; [apply (KFRM cid pos' z Hin); left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
      split; [apply (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos' z HAR Hin); lia|lia].
    - assert (H1s : ea_sp0 a <= ea_v a) by exact H1. assert (H2s : ea_v a + 56 <= ly_stk_hi (ea_ly a)) by exact H2.
      split; [apply KHI; lia|].
      split; [intros Him; pose proof (Hsegs z Him) as Hlo; unfold kLowMemEnd in Hlo; lia|lia]. }
  split.
  { apply (eve_nodeR_frame (mrestrict (w_H (ea_W a)) (ea_mem a)) (mrestrict (w_H (ea_W a)) mem) (prh_lin (ea_Lam a))
      _ _ _ HN).
    intros z Hz.
    assert (FKz : aview SEGS (w_H (ea_W a)) mem z = aview SEGS (w_H (ea_W a)) (ea_mem a) z /\ ~ in_img SEGS z /\
      0 <= z < 2 ^ 64).
    { destruct Hz as [Hz|(b & kk & _ & Hl & Hz)]; [exact (ROOT z Hz)|exact (LAMK b kk z Hl Hz)]. }
    destruct FKz as (AVz & NIz & Rz). split.
    - exact (mbyte_of_aview SEGS (w_H (ea_W a)) (w_H (ea_W a)) (ea_mem a) mem z AVz).
    - exact (eve_wr_av (w_H (ea_W a)) (w_H (ea_W a)) (ea_mem a) mem z Rz NIz AVz). }
  split.
  { destruct HH as [Hl|[(cid & pos' & Hin & H1 & H2)|Hs]]; [left; exact Hl| |right; right; exact Hs].
    right. left. exists cid, pos'. split; [rewrite Hfrs; right; exact Hin|]. split; assumption. }
  destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos' & Hin & H1 & H2)|(H1 & H2)]].
  - split.
    + exact (eve_lam_shadow (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a)
        (ea_ran a) (ea_most a) (ea_own a) b mm (ea_v a) 56 HAR2 HLED2 Hin H1 H2 ltac:(lia)).
    + exact (eve_lam_hull (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a)
        (ea_ran a) (ea_most a) (ea_own a) b mm (ea_v a) 56 HAR2 HLED2 Hin H1 H2 ltac:(lia)).
  - assert (HIN2 : In (cid, pos') (frames S2)) by (rewrite Hfrs; right; exact Hin).
    destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ cid pos' HAR Hin) as (Fal & _ & _ & _).
    destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Fa & Fc & _).
    pose proof (eve_fs8 cid ltac:(lia)) as F8.
    split.
    + set (fa := frame_addr (ea_ly a) cid pos') in *. set (fs := fs_frame_bytes cid) in *.
      assert (Hfa8 : fa mod 8 = 0).
      { pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Fal, Z.add_0_r in D. rewrite D.
        replace (32 * (fa / 32)) with (fa / 32 * 4 * 8) by lia. apply Z.mod_mul. lia. }
      apply (range_addressable_agree (aview SEGS (w_H (ea_W a)) (ea_mem a)) (aview SEGS (w_H (ea_W a)) mem)
        SHADOW_OFF (ea_v a) 56); [|exact HRA].
      intros x Hx. unfold shadow_of_addr.
      pose proof (eve_sh_in fa fs x Hfa8 F8 ltac:(lia)) as Hsx.
      apply (KFRM cid pos'); [exact Hin|right; unfold in_zr; cbn [fst snd]; unfold shadow_addr, fa, fs in *; lia].
    + apply (eve_hull_sub _ (frame_addr (ea_ly a) cid pos') (fs_frame_bytes cid) (ea_v a) 56); [|lia|lia|lia].
      exact (eve_frame_hull (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md cid pos' HAR2 HIN2 ltac:(lia)).
  - assert (H1s : ea_sp0 a <= ea_v a) by exact H1. assert (H2s : ea_v a + 56 <= ly_stk_hi (ea_ly a)) by exact H2.
    split.
    + intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
      apply (alx_zshadow_byte SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md x HAR2). lia.
    + pose proof (eve_stk64 (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md HAR2) as H64.
      apply (eve_stack_hull (ea_ly a) S2 (ea_Hp a) (ea_W a) mem md (ea_v a) 56 HAR2).
      * pose proof (Z.div_mod (ea_v a) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (ea_v a) 64 ltac:(lia)). lia.
      * pose proof (Z.div_mod (ea_v a + 56 - 1) 64 ltac:(lia)).
        pose proof (Z.mod_pos_bound (ea_v a + 56 - 1) 64 ltac:(lia)).
        pose proof (Z.div_mod (ly_stk_hi (ea_ly a)) 64 ltac:(lia)). rewrite H64 in *. lia. }
(* the save area, the flag word, the room and its paired hull use, the run position (all by the frame call's
   S2 = set_fs f (ea_S a): RL_set_fs, hull_used_secs (set_fs keeps st_secs), PresetRoomPosKeep.room_pos_set_fs), memnorm
   (the walk's keep, HMN) *)
split; [exact HSAV|].
split; [exact HFLAG|].
split.
{ destruct HSfs as (f & ->). split; [intros HR; exact (RL_set_fs (ea_S a) f HR)|].
  apply PresetHullBudget.hull_used_secs. reflexivity. }
split; [|exact HMN].
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist HRP0. destruct HSfs as (f & ->).
exact (PresetRoomPosKeep.room_pos_set_fs _ _ _ _ _ _ _ f HRP0).
Qed.

(* ======== piece 1: the entry ======== *)
Theorem ev_entry_holds : ev_entry_spec (PI := prh_img_A) (PA := PA) B ARx SK.
Proof.
unfold ev_entry_spec. intros a HPRE.
pose proof HPRE as HP.
destruct HP as (HFPRE & Hfrm & Hcnt & H10 & H11 & Hcur & Hq8 & Hchap & Hqlo & Hqhi & Hwin & Hsrc & Hinblk & Hlen3 &
  Hi0 & Hdep & Hdepn & Hdl & Hwd & Hscrblk & Hscrx & Hscrq & Htree & Hled & HMN0).
assert (Hcnt1 : count_cid 1 (frames (ea_S a)) < fs_frames 1).
{ pose proof (Nat2Z.is_nonneg (ea_n a)) as Hnn. rewrite Nat2Z.inj_succ in Hcnt. lia. }
destruct HFPRE as (HPRE0 & HROD).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (@pa_B_ok _ _ PA) as HBASE.
destruct Hwin as (Hd0 & Hd16 & Hdtop & Hdpres).
(* the function's stack need (LENGTH, from prh_img_A) *)
assert (HSTK : ea_STK (PI := prh_img_A) a = Z.of_nat (S (ea_n a)) * 272 + 16384).
{ unfold ea_STK, STK_ex_value. cbn [pi_frame prh_img_A]. f_equal; try (vm_compute; reflexivity). }
assert (HSTKlo : 16656 <= ea_STK (PI := prh_img_A) a)
  by (rewrite HSTK; pose proof (Nat2Z.is_nonneg (ea_n a)); nia).
assert (Hes : ESTACK = 4096) by reflexivity.
(* the journal at the caller-window form (STK + d) (sp0 + d), built by YCbqG's ajx_intro (P'' universe: the last
   slot is `qtight S' /\ incl (wild_part ..) (wild_part .. ++ WS)`; a trace-free stretch keeps the depot) *)
assert (HJ0 : AJ (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a)
  (ea_W a) (ea_mem a) (ea_md a) [] (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) 0).
{ unfold ajournal_x, ajournal_xw. unfold ea_sp0 in *.
  apply ajx_intro.
  - exact HAR.
  - apply layout_le_refl.
  - lia.
  - apply wle_refl.
  - apply aos_step_refl.
  - reflexivity.
  - lia.
  - lia.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros p n i H1 H2; exfalso; exact (H2 H1).
  - intros z Hz. destruct (Z_le_gt_dec (spZ (ea_regs a)) z) as [Hge|Hlt]; [apply Hdpres; lia | apply Hpres; lia].
  - unfold astk_ok. split; [rewrite Z.add_mod, Hal16, Hd16 by lia; reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    unfold ly_bot in *. split; [lia|]. split; [lia | lia].
  - intros; reflexivity.
  - exact HQT.
  - exact (incl_appl [] (incl_refl _)). }
(* ---- the symbolic state at the entry ---- *)
destruct (alx_const SEGS B ARx LAWS (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) HAR)
  as (Kcell & Kuar & Kgot & Kgotuar).
rewrite CELL_SHADOW in Kcell. rewrite GOT_SHADOW, CELL_SHADOW in Kgot. rewrite GOT_UAR in Kgotuar.
pose proof UAR_CELL as (Hu4096 & Huhi & Hu0 & Hu1 & Hu12).
assert (D012 : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12)) by (vm_compute; try discriminate; try lia).
assert (D01 : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 1)) by (vm_compute; try discriminate; try lia).
assert (D112 : VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 12)) by (vm_compute; try discriminate; try lia).
assert (Dimg : forall i, (i < 39)%nat -> 65536 <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + 8 <= 6291456).
{ intros i Hi. pose proof (@pa_obj_img _ _ PA i Hi) as HH. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HH. exact HH. }
pose proof (Dimg 0%nat ltac:(lia)) as [Di0 Di0'].
pose proof (Dimg 1%nat ltac:(lia)) as [Di1 Di1'].
pose proof (Dimg 12%nat ltac:(lia)) as [Di12 Di12'].
remember (Eimg (Ereg (ea_regs a) [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr (ea_regs a) 1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ea_regs a) _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr (ea_regs a) 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ea_regs a) _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (ea_regs a) 3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ea_regs a) _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ea_regs a) 4)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ea_regs a) _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (ea_q a))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat (ea_regs a) _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (ea_v a))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat (ea_regs a) _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ea_regs a) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ea_regs a) _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = ea_sp0 a) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg (ea_regs a) [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Rsp : 2 ^ 46 <= ea_sp0 a <= 2 ^ 47) by (unfold ea_sp0; lia).
assert (Rq : 2 ^ 46 <= ea_q a <= 2 ^ 47) by (unfold ea_sp0 in *; lia).
assert (HS : st_ok_pi SEGS VAL E ss_eve1
  (restrict (w_H (ea_W a)) (mkst (ea_regs a) (Z_to_bv 64 (BASE + EVE_ENTRY)) (ea_mem a) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_eve1. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold eve_regions1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold ea_sp0 in *. lia.
    + rewrite EO0, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply eve_val_mem_of_rdword. exact Kgot.
    + rewrite EO12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. apply eve_val_mem_of_rdword. exact Kcell.
    + rewrite EO1, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply eve_val_mem_of_rdword. exact Kgotuar.
    + rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 4 (SLit 1) 1);
      [cbn [sv_denot]; vm_compute; reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply eve_val_mem_of_rd32. exact Kuar.
  - apply pairwise_disjoint_of_extents. unfold eve_regions1, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite EO0, EO1, EO12, E33, !unsigned_lit_small by lia. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ea_sp0 in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [eve_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    unfold ea_sp0 in *. unfold kLowMemEnd in *.
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    repeat match goal with |- _ /\ _ => split end;
      try exact Hal16; try exact Hq8; try (rewrite Z.mod_1_r; reflexivity); try (unfold SHADOW_OFF; lia). }
assert (SHOK : sh_ok SEGS EVE_Bx [] E (mrestrict (w_H (ea_W a)) (ea_mem a))) by apply Forall_nil.
unfold cfg_at. change (w64 (SIGMA AS_ex_value)) with (Z_to_bv 64 (BASE + EVE_ENTRY)).
(* run 1 keeps memnorm (HMN0, ev_pre's last conjunct) by the _inv runner *)
paj_run_tok_x_inv RUNI HS HJ0 SHOK HMN0 EVE_Bspan.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- ea_d a));
  [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* what the prologue's stores left alone: everything outside the save area *)
assert (KEEP1 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_sp0 a - 256 <= z < ea_sp0 a) ->
  aview SEGS (w_H (ea_W a)) (ms_mem ms) z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros z Hz Hnot. apply aview_eq_of. apply HFr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). unfold ss_eve1, eve_regions1 in Hin. cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?Usp, ?EO0, ?EO1, ?EO12, ?E33 in Hr;
     rewrite ?unsigned_lit_small in Hr by lia; lia |]).
  destruct Hin. }
(* ---- the call of frame_alloc_1 (__asan_stack_malloc_1), a0 = 96 ---- *)
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (19%bv : bv 5) R19.
prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24.
assert (US1 : U E (SAlu ALU_AND (SOff 2 (-256)) (SLit (-32))) = ea_S1 a).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Usp.
  rewrite (zcanon_id (ea_sp0 a + -256)) by (unfold M64; lia).
  change (zcanon (-32)) with (Z.land (- 2 ^ 5) (Z.ones 64)).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia.
  unfold ea_S1, ea_SA. change (2 ^ 5) with 32.
  replace (ea_sp0 a + -256) with (ea_sp0 a - 256) by lia.
  pose proof (Z.mod_pos_bound (ea_sp0 a - 256) 32 ltac:(lia)).
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (HspT : spZ (ms_regs ms) = ea_S1 a) by (unfold spZ at 1; rewrite R2; exact US1).
assert (Hm32 : (ea_sp0 a - 256) mod 32 = 0 \/ (ea_sp0 a - 256) mod 32 = 16).
{ apply eve_mod32_cases; [lia|]. unfold ea_sp0 in *.
  rewrite <- Z.add_opp_r, Z.add_mod, Hal16 by lia. reflexivity. }
assert (HS1lo : ea_sp0 a - 272 <= ea_S1 a <= ea_sp0 a - 256).
{ unfold ea_S1, ea_SA. destruct Hm32 as [H32|H32]; rewrite H32; lia. }
assert (HS1m : (ea_S1 a - (ea_sp0 a + ea_d a)) mod 16 = 0).
{ unfold ea_S1, ea_SA.
  pose proof (Z.div_mod (ea_d a) 16 ltac:(lia)) as Hdd. rewrite Hd16, Z.add_0_r in Hdd.
  destruct Hm32 as [H32|H32]; rewrite H32;
  [ replace (ea_sp0 a - 256 - 0 - (ea_sp0 a + ea_d a)) with ((-16 - ea_d a / 16) * 16) by lia
  | replace (ea_sp0 a - 256 - 16 - (ea_sp0 a + ea_d a)) with ((-17 - ea_d a / 16) * 16) by lia ];
  apply Z_mod_mult. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  rewrite eve_sm1_pc;
  eapply (YGcallMxmn.aj_stack_malloc_at_xm (SK := SK) SEGS B PST ARx LAWS Hsegs errno_low OWNLOW SMX 1 ASM1 ltac:(lia)
    (ea_W a) rT mT (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [] (ea_ly a) (ea_S a) (ea_Hp a) dT 0
    (ea_S1 a - (ea_sp0 a + ea_d a)) (Z_to_bv 64 (BASE + EVE_RET1)) HJ0) end.
  - rewrite HspT. lia.
  - exact HS1m.
  - lia.
  - rewrite Hes. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [unfold EVE_RET1; lia | unfold EVE_RET1; reflexivity].
  - exact Hcnt1. }
(* ---- back from the call: the frame is live; rebuild the state at 0x83318; memnorm by the callee's keep ---- *)
cbv beta. intros W' c' Hwle
  (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflagw
   & Hfpres & HKept & HJsm & HSfs & HMNk).
pose proof (HMNk HMN0) as HMN2. clear HMNk HMN0.
pose proof (proj1 HJ2) as HAR2. cbv beta in HAR2.
assert (HinF : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (alx_frames SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2 1 pos HAR2 HinF)
  as (HFal & HFapp & HFpres2 & HFSpres).
pose proof (frames_bounds_x SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2 1 pos HAR2 HinF)
  as (HF4096 & HFceil & _).
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFB in HFapp, HFpres2, HFceil, Hz, Hflagw, Hfpres.
assert (HS1al : ea_S1 a mod 32 = 0).
{ unfold ea_S1, ea_SA. pose proof (Z.div_mod (ea_sp0 a - 256) 32 ltac:(lia)) as Hdm.
  replace (ea_sp0 a - 256 - (ea_sp0 a - 256) mod 32) with ((ea_sp0 a - 256) / 32 * 32) by lia.
  apply Z_mod_mult. }
(* the registers the call keeps (aregs_preserved; acallee_saved = 2,3,4,8,9,18..27) *)
assert (P2 : getr regs2 2 = w64 (ea_S1 a)).
{ rewrite (eve_kept _ _ 2 (2%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R2. unfold w64; rewrite <- US1; unfold U; rewrite Z_to_bv_bv_unsigned; reflexivity. }
assert (R9' : getr (ms_regs ms) 9 = sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-256)) (SLit (-32))) (SLit 0)))
  by (rewrite R9; cbn [sv_denot]; reflexivity).
assert (US1b : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-256)) (SLit (-32))) (SLit 0)) = ea_S1 a).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, US1, (zcanon_id 0) by (unfold M64; lia).
  rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (P9 : getr regs2 9 = w64 (ea_S1 a)).
{ rewrite (eve_kept _ _ 9 (9%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R9'. unfold w64; rewrite <- US1b; unfold U; rewrite Z_to_bv_bv_unsigned; reflexivity. }
assert (P8 : getr regs2 8 = w64 (ea_sp0 a)).
{ rewrite (eve_kept _ _ 8 (8%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R8, E2. unfold w64, ea_sp0, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (P19 : getr regs2 19 = w64 (ea_q a)).
{ rewrite (eve_kept _ _ 19 (19%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R19, E10. reflexivity. }
assert (P23 : getr regs2 23 = w64 (ea_v a)).
{ rewrite (eve_kept _ _ 23 (23%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R23, E11. reflexivity. }
assert (P24 : getr regs2 24 = w64 SHADOW_OFF).
{ rewrite (eve_kept _ _ 24 (24%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R24, E32. reflexivity. }
assert (P3 : getr regs2 3 = getr (ea_regs a) 3).
{ rewrite (eve_kept _ _ 3 (3%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R3, E3. reflexivity. }
assert (P4 : getr regs2 4 = getr (ea_regs a) 4).
{ rewrite (eve_kept _ _ 4 (4%bv : bv 5) HP2 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
  rewrite R4, E4. reflexivity. }
(* ---- the symbolic state at 0x83318 and the run to P_WS ---- *)
set (F := frame_addr (ea_ly a) 1 pos) in *.
assert (HqS : ly_stk_lo (ea_ly a) <= ea_q a /\ ea_q a + 8 + 16 <= ly_stk_hi (ea_ly a))
  by (unfold ea_sp0 in *; lia).
assert (Zq : aview SEGS (w_H (ea_W a)) mem2 (SHADOW_OFF + ea_q a / 8) = Some 0)
  by (apply (eve_zsh_byte (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2); [exact HAR2 | lia | lia]).
assert (Zq8 : aview SEGS (w_H (ea_W a)) mem2 (SHADOW_OFF + ea_q a / 8 + 1) = Some 0).
{ replace (SHADOW_OFF + ea_q a / 8 + 1) with (SHADOW_OFF + (ea_q a + 1 * 8) / 8)
    by (rewrite Z.div_add by lia; lia).
  apply (eve_zsh_byte (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2); [exact HAR2 | lia | lia]. }
assert (HFq : F / 8 + 12 <= ea_q a / 8).
{ assert (HH : (F + 16 * 8) / 8 <= ea_q a / 8) by (apply Z.div_le_mono; [lia | unfold ea_sp0 in *; lia]).
  rewrite Z.div_add in HH by lia. lia. }
remember (Eimg (Ereg regs2 [Z_to_bv 64 (shadow_addr (ea_q a)); Z_to_bv 64 (shadow_addr F)])) as Ev2 eqn:HEv2.
assert (HEI2 : img_env VAL A_LIM Ev2) by (subst Ev2; apply Eimg_env).
assert (F9 : ew Ev2 9 = w64 (ea_S1 a))
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact P9).
assert (F10 : ew Ev2 10 = w64 F)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact Ha0).
assert (F19 : ew Ev2 19 = w64 (ea_q a))
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl); exact P19).
assert (F24 : ew Ev2 24 = w64 SHADOW_OFF)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 _ 24 24%bv eq_refl); exact P24).
assert (F32 : ew Ev2 32 = Z_to_bv 64 (shadow_addr (ea_q a)))
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (F33 : ew Ev2 33 = Z_to_bv 64 (shadow_addr F))
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (Rq8 : 0 <= ea_q a / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (RF8 : 0 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HS2 : st_ok_pi SEGS VAL Ev2 ss_eve2
  (restrict (w_H (ea_W a)) (mkst regs2 (Z_to_bv 64 (BASE + EVE_RET1)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_eve2. apply pa_entry_st_ok_full.
  - subst Ev2; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold eve_regions2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite F9. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS).
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _).
      apply Hpr2. unfold ea_sp0 in *. lia.
    + rewrite F10. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Hfpres. lia.
    + rewrite F33, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
      unfold shadow_addr. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS).
      replace (SHADOW_OFF + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; lia).
      exact (proj1 (HFSpres o ltac:(change (fs_frame_bytes 1 / 8) with 16; lia))).
    + rewrite F32, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
      unfold shadow_addr. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons;
        [apply (chunk_ok_val SEGS Ev2 _ _ 0 1 (SLit 0) 0);
         [cbn [sv_denot]; vm_compute; reflexivity | lia | lia |
          rewrite Z.add_0_r; apply eve_val_mem1; exact Zq]|].
      apply Forall_cons;
        [apply (chunk_ok_val SEGS Ev2 _ _ 1 1 (SLit 0) 0);
         [cbn [sv_denot]; vm_compute; reflexivity | lia | lia |
          apply eve_val_mem1; exact Zq8]|].
      apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold eve_regions2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite F9, F10, F32, F33. unfold w64. rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold shadow_addr, SHADOW_OFF.
    destruct HFapp as [HFa1 [HFa2 | [HFa3 HFa4]]];
    unfold ea_sp0, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
    pose proof (Z.div_mod (ea_q a) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (ea_q a) 8 ltac:(lia));
    repeat match goal with |- _ /\ _ => split end; try lia.
  - split; [|split; [exact I|]].
    + cbn [eve_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite F9, F10, F19, F24, F32, F33. unfold w64.
      rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
      change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold shadow_addr, SHADOW_OFF, ea_sp0 in *.
      repeat match goal with |- _ /\ _ => split end;
        try exact HS1al; try exact HFal; try exact Hq8; try lia.
    + cbn [eve_facts2 f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
      * apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit.
        rewrite F19, F24, F32. unfold w64. rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        rewrite (zcanon_id 3) by (unfold M64; lia).
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        rewrite !Z.add_0_r. unfold shadow_addr.
        rewrite (zcanon_id (ea_q a)) by (unfold M64; lia).
        rewrite (zcanon_id (ea_q a / 8)) by (unfold M64; lia).
        rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
        rewrite (zcanon_id (ea_q a / 8 + SHADOW_OFF)) by (unfold M64, SHADOW_OFF; lia).
        rewrite (zcanon_id (SHADOW_OFF + ea_q a / 8)) by (unfold M64, SHADOW_OFF; lia). lia.
      * apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit.
        rewrite F19, F24, F32. unfold w64. rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        rewrite (zcanon_id 3) by (unfold M64; lia).
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        rewrite !Z.add_0_r. unfold shadow_addr.
        rewrite (zcanon_id (ea_q a + 8)) by (unfold M64; lia).
        replace (ea_q a + 8) with (ea_q a + 1 * 8) by lia. rewrite Z.div_add by lia.
        rewrite (zcanon_id (ea_q a / 8 + 1)) by (unfold M64; lia).
        rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
        rewrite (zcanon_id (ea_q a / 8 + 1 + SHADOW_OFF)) by (unfold M64, SHADOW_OFF; lia).
        rewrite (zcanon_id (SHADOW_OFF + ea_q a / 8 + 1)) by (unfold M64, SHADOW_OFF; lia). lia.
      * apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit.
        rewrite F10, F24, F33. unfold w64. rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        rewrite (zcanon_id 3) by (unfold M64; lia).
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        rewrite !Z.add_0_r. unfold shadow_addr.
        rewrite (zcanon_id F) by (unfold M64; lia).
        rewrite (zcanon_id (F / 8)) by (unfold M64; lia).
        rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
        rewrite (zcanon_id (F / 8 + SHADOW_OFF)) by (unfold M64, SHADOW_OFF; lia).
        rewrite (zcanon_id (SHADOW_OFF + F / 8)) by (unfold M64, SHADOW_OFF; lia). lia. }
assert (SHOK2 : sh_ok SEGS EVE_Bx [] Ev2 (mrestrict (w_H (ea_W a)) mem2)) by apply Forall_nil.
(* run 2 keeps memnorm (HMN2) by the _inv runner *)
paj_run_to_tok_x_inv RUNTOI HS2 HJ2 SHOK2 HMN2 EVE_Bspan EVE_WS.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (ea_S1 a - (ea_sp0 a + ea_d a)));
  [reflexivity | cbn [YP09.r_base]; rewrite F9; unfold w64; rewrite unsigned_lit_small by lia; lia
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F);
  [reflexivity | cbn [YP09.r_base]; rewrite F10; unfold w64; apply unsigned_lit_small; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hzr. right; right; right.
    exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (shadow_addr F));
  [reflexivity | cbn [YP09.r_base]; rewrite F33; apply unsigned_lit_small;
   unfold shadow_addr, SHADOW_OFF; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hzr. right; right; right.
    exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    fold F. change (fs_frame_bytes 1 / 8) with 16. lia. }
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
(* ---- at P_WS: what the whole piece left alone ---- *)
pose proof HKept as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
pose proof (alx_blocks SEGS B ARx LAWS (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)) as HBL.
pmkst HS2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mg _) ?dg) _ =>
assert (KEEP2 : forall z, 0 <= z < 2 ^ 64 ->
  ~ (ea_S1 a + 144 <= z < ea_S1 a + 152) -> ~ (F <= z < F + 24) ->
  ~ (shadow_addr F <= z < shadow_addr F + 12) ->
  aview SEGS (w_H (ea_W a)) mg z = aview SEGS (w_H (ea_W a)) mem2 z);
[ intros z Hzb Hn1 Hn2 Hn3; apply aview_eq_of; apply HFr;
  rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.mod_small by lia;
  intros (r & Hin & Hr); unfold ss_eve2, eve_regions2 in Hin; cbn [ss_mem In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?F9, ?F10, ?F32, ?F33 in Hr; unfold w64 in Hr;
     rewrite ?unsigned_lit_small in Hr by (unfold shadow_addr, SHADOW_OFF; lia);
     unfold shadow_addr in *; lia |]);
  destruct Hin
| ] end.
(* (i) every byte at or above the entry sp (the caller's window and its locals) *)
assert (KEEPhi : forall z, ea_sp0 a <= z < 2 ^ 64 ->
  aview SEGS (w_H (ea_W a)) (ms_mem ms0) z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros z Hzk. unfold ea_sp0 in *.
  rewrite (KEEP2 z ltac:(lia) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)
                  ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)
                  ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)).
  rewrite (HK1 z ltac:(lia) ltac:(lia)). apply KEEP1; lia. }
(* (ii) every byte of a block that was live at entry *)
assert (KEEPblk : forall b m i, In (b, m) (ablocks B (ea_ly a) (ea_S a)) -> 0 <= i < req_size m ->
  aview SEGS (w_H (ea_W a)) (ms_mem ms0) (b + i) = aview SEGS (w_H (ea_W a)) (ea_mem a) (b + i)).
{ intros b m i Hin Hi.
  destruct (HBL b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2 b m 1 pos HAR2
    ltac:(rewrite Eab; exact Hin) HinF) as Hdbf.
  unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. fold F in Hdbf. rewrite HFB in Hdbf.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  rewrite (KEEP2 (b + i) ltac:(lia) ltac:(unfold ea_sp0 in *; lia) ltac:(lia)
                  ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)).
  rewrite (HK2 b m i Hin Hi ltac:(intros HH; exact HH)). apply KEEP1; unfold ea_sp0 in *; lia. }
(* (iii) image bytes that are neither runtime-owned nor errno *)
assert (KEEPimg : forall z, in_img SEGS z -> ~ Exists (in_zr z) (as_owned_static B) ->
  ~ (as_errno B <= z < as_errno B + 4) ->
  aview SEGS (w_H (ea_W a)) (ms_mem ms0) z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros z Hin Hno Her. pose proof (Hsegs z Hin) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (KEEP2 z ltac:(lia) ltac:(unfold ea_sp0 in *; lia)
                  ltac:(intros HH;
                        destruct (alx_client_img SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2 z HAR2
                          ltac:(right; left; exists 1, pos; split;
                                [exact HinF | fold F; rewrite HFB; lia])) as [_ Hnimg];
                        exact (Hnimg Hin))
                  ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)).
  rewrite (HK3 z Hin Hno Her). apply KEEP1; unfold ea_sp0 in *; lia. }
(* (iv) the bytes and the shadow bytes of every frame that was live at entry *)
assert (KEEPfrm : forall cid pos' z, In (cid, pos') (frames (ea_S a)) ->
  (in_zr z (frame_rng (ea_ly a) (cid, pos')) \/
   in_zr z (shadow_addr (frame_addr (ea_ly a) cid pos'), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H (ea_W a)) (ms_mem ms0) z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros cid pos' z Hinf Hzf.
  assert (Hne : (cid, pos') <> (1, pos)) by (intros Heq; rewrite Heq in Hinf; exact (Hnin Hinf)).
  assert (HinS2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hinf).
  destruct (in_split _ _ Hinf) as (l1 & l2 & Esp).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2
    (1, pos) (cid, pos') [] l1 l2 HAR2 ltac:(rewrite Hfrs2, Esp; reflexivity)) as Hdff.
  unfold zdisjoint, frame_rng in Hdff. cbn [fst snd] in Hdff. fold F in Hdff. rewrite HFB in Hdff.
  pose proof (alx_frames SEGS B ARx LAWS (ea_ly a) S2 (ea_Hp a) (ea_W a) mem2 md2 cid pos' HAR2 HinS2)
    as (Hfal' & Hfapp' & _ & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  pose proof (Z.div_mod (frame_addr (ea_ly a) cid pos') 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (frame_addr (ea_ly a) cid pos') 8 ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as M3.
  unfold in_zr, frame_rng, shadow_addr in Hzf. cbn [fst snd] in Hzf.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp'.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  unfold YM05.alloc_ceiling, ASAN_CEIL, ea_sp0, SHADOW_OFF in *.
  destruct Hfapp' as (Hfa0 & [Hfa1 | (Hfa1 & Hfa2)]);
  destruct HFapp as (HFa0 & [HFa1 | (HFa1 & HFa2)]);
  destruct Hdff as [Hd1 | Hd1]; destruct Hzf as [Hzf | Hzf].
  all: rewrite (KEEP2 z ltac:(unfold shadow_addr, SHADOW_OFF, ea_sp0 in *; lia)
                        ltac:(unfold shadow_addr, SHADOW_OFF, ea_sp0 in *; lia)
                        ltac:(unfold shadow_addr, SHADOW_OFF, ea_sp0 in *; lia)
                        ltac:(unfold shadow_addr, SHADOW_OFF, ea_sp0 in *; lia)).
  all: rewrite (HK4 cid pos' z Hinf
         ltac:(unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in *; cbn [fst snd];
               first [ left; lia | right; lia ])
         ltac:(intros HH; exact HH)).
  all: apply KEEP1; unfold shadow_addr, SHADOW_OFF, ea_sp0 in *; lia. }
(* ---- P_WS (0x833dc): the registers (HS2's map), the 13 saved registers (run 1's stores in HS's region 2, kept by
   the call (HK1) and by run 2 (KEEP2)), the frame's flag word (the call's, kept by run 2) ---- *)
prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19.
prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (23%bv : bv 5) Q23.
prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (25%bv : bv 5) Q25. prreg HS2 (26%bv : bv 5) Q26.
assert (G2 : ew Ev2 2 = getr regs2 2)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (G3 : ew Ev2 3 = getr regs2 3)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (G4 : ew Ev2 4 = getr regs2 4)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (G8 : ew Ev2 8 = getr regs2 8)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (G23 : ew Ev2 23 = getr regs2 23)
  by (subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 23 23%bv eq_refl)).
assert (REGS : ev_regs (ev_setpos a pos) (ms_regs ms0)).
{ unfold ev_regs.
  change (ea_S1 (ev_setpos a pos)) with (ea_S1 a). change (ea_regs (ev_setpos a pos)) with (ea_regs a).
  change (ea_sp0 (ev_setpos a pos)) with (ea_sp0 a). change (ea_fr (ev_setpos a pos)) with F.
  change (ea_q (ev_setpos a pos)) with (ea_q a).
  split; [exact (eq_trans Q2 (eq_trans G2 P2))|].
  split; [exact (eq_trans Q3 (eq_trans G3 P3))|].
  split; [exact (eq_trans Q4 (eq_trans G4 P4))|].
  split; [exact (eq_trans Q8 (eq_trans G8 P8))|].
  split; [exact (eq_trans Q9 F9)|].
  split; [exact (eq_trans Q18 F10)|].
  split; [exact (eq_trans Q19 F19)|].
  split; [exact (eq_trans Q24 F24)|].
  split; [exact (eq_trans Q25 F33)|].
  exact (eq_trans Q26 F32). }
assert (W20 : getr (ms_regs ms0) 20 = w64 (shadow_addr (ea_q a + 8))).
{ rewrite Q20, F32. rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
  unfold w64, shadow_addr. f_equal. replace (ea_q a + 8) with (ea_q a + 1 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (W22 : getr (ms_regs ms0) 22 = w64 F) by exact (eq_trans Q22 F10).
assert (W23 : getr (ms_regs ms0) 23 = w64 (ea_v a)) by exact (eq_trans Q23 (eq_trans G23 P23)).
assert (SAV : ev_saved (ev_setpos a pos) (ea_W a) (ms_mem ms0)).
{ pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & svAll & _).
  cbn [ss_mem setpc] in svAll. apply Forall_inv in svAll. destruct svAll as (_ & _ & _ & svCh).
  cbn [YP09.r_chunks YP09.r_base ms_mem restrict] in svCh.
  assert (svEW : forall n : nat, (n < 32)%nat -> ew E n = getr (ea_regs a) (Z_to_bv 5 (Z.of_nat n))).
  { intros n Hn. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
  assert (svB : forall o r, In (o, r) EV_SAVED -> 152 <= o <= 248 /\ 1 <= r <= 27).
  { intros o r Hin. cbv [EV_SAVED In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
  lazymatch type of svCh with Forall _ ?CH =>
    assert (svCH : forall o r, In (o, r) EV_SAVED -> In (YP09.mkChunk (o - 256) (CVal 8 (SOff (Z.to_nat r) 0))) CH)
  end.
  { intros o r Hin. cbv [EV_SAVED In] in Hin.
    repeat (destruct Hin as [Hin|Hin];
      [injection Hin as <- <-; cbn [In]; repeat (first [left; reflexivity | right]) |]).
    destruct Hin. }
  unfold ev_saved. change (ea_SA (ev_setpos a pos)) with (ea_SA a). change (ea_regs (ev_setpos a pos)) with (ea_regs a).
  apply Forall_forall. intros [o r] Hin. cbn [fst snd].
  destruct (svB o r Hin) as [svO svR].
  apply (eve_vm_av (w_H (ea_W a)) (w_H (ea_W a)) (ms_mem ms) (ms_mem ms0)).
  { intros zs Hzs. unfold ea_SA in Hzs. try change (Z.of_nat 8) with 8 in Hzs. unfold ea_sp0 in *.
    rewrite (KEEP2 zs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)).
    apply HK1; lia. }
  pose proof (proj1 (Forall_forall _ _) svCh _ (svCH o r Hin)) as svC.
  replace (ea_SA a + o) with (base_val E (Some 2%nat) + (o - 256)) by (cbn [base_val]; rewrite Usp; unfold ea_SA; lia).
  apply (val_of_chunk_ok SEGS E _ _ _ _ _ _ svC).
  - cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. rewrite (svEW (Z.to_nat r)) by lia.
    rewrite Z2Nat.id by lia. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr (ea_regs a) (Z_to_bv 5 r))) as svHR. unfold bv_modulus in svHR.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ Z.of_N 64). exact svHR.
  - cbn. lia. }
assert (FLAG : rdword (aview SEGS (w_H (ea_W a)) (ms_mem ms0)) (F + 128 - 8) = Some (flag_addr (ea_ly a) 1 pos)).
{ rewrite <- Hflagw. apply eve_rdword. intros ib Hib.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold ea_sp0 in *.
  destruct HFapp as (HFa0 & [HFa1 | (HFa1 & HFa2)]);
    apply KEEP2; unfold shadow_addr, SHADOW_OFF in *; lia. }
apply SRr_ret.
exists pos, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2), (ea_ly a), S2, (ea_Hp a), 0.
split.
{ assert (EPC : SIGMA AS_ex_value + EV_WS = BASE + 7676) by (vm_compute; reflexivity).
  unfold ev_cfg, ev_pc. rewrite EPC. reflexivity. }
exact (eve_at_ws_of a pos S2 (ms_regs ms0) (ms_mem ms0) _ HPRE HJ2 Hfrs2 Eab HSfs KEEPhi KEEPblk KEEPimg KEEPfrm
  SAV FLAG REGS W20 W22 W23 HMN2).
Qed.

End f.
End d.
