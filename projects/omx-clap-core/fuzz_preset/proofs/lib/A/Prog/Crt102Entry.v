(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 787 of its 842 lines of code are new or changed and 723 lines of the source are left out. *)
(* base: commit 2fdcfd7be069 (post-landing line). kb round (brief
   the internal file wild-budget-kb-reshape.md): the continuation at M takes crt_live at kb = 0
   (the entry -> M stretch makes no wild call: the frame call and __asan_memset have old posts, so the journal's budget is
   [], wbudget [] 0 []). *)
(* fuzz_preset, image A' (asan 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4): the ENTRY of check_round_trip
   (fuzz_preset.c new:772-775) against the contract text tcheck_round_trip_specX (lib/A/PRH_FnCheck.v), from the
   function's entry (A' 0x82870) to the cut M (+0x194, where a0 / a1 / a2 are loaded for the first round_trip_text).
   It ESTABLISHES Crt102Glue's crt_live: every later segment of the walk starts from what crt102_entry hands its
   continuation. Walk of check_round_trip; slice Crt102Entry.

   INPUTS OF RECORD (taken by path, as Crt102Glue.v's header):
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b).
   - base commit e6664614c075 (the contract texts and Spec at the kit tip of record
     3ac20a5c9e30: PRH_Base.v ee2f5cd7ed35 (the E sweep: g_most / g_own_ran_out are ledger
     fields; prh_cons_from), PRH_FnCheck.v 0844ed8c0608 (tcheck_round_trip_specX as at dc6ee977244a; entry prh_ledger .. SIZE_MAXZ ran most 0,
     prh_run_at .. rp_i (PresetReqAt.round_trip rp_sm t), rp_sm = ReaderRes.jr_strtod, prh_cons_from .. rp_i
     (length (round_trip rp_sm t)); the exact advance on r = 0 only), lib/Spec/PresetReqAt.v 43c958024221, PresetRun.v
     5ac818ab1fe6; the engine whole set by path, YGcallMxmn.v b47cf7942c3d; S10Env.v d8ca1dd59ead from
     commit a977ac095573; Crt102Img.v 176eec830b61 and Crt102Glue.v 69636067b31c, the lane's
     interface, both unchanged by this file).
   - listings of record: commit d42e123915ae (lib/A/Listing_prog.v 1ab147923c5d,
     lib/A/PAImg_prog.v 47eeb54e93be, lib/Reusable/YPsym.v b6f5a85d234d).
   - the listing read: the internal file crt.A.s; the cut: DESIGN.md (sha256 d05697dd088c; internal record).
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: no function proved (proof-index check_round_trip, exit 0,
     an internal record of that lookup, run by the unit owner): written new. METHOD: the index
     snapshot of 04:58Z only, no cold/* sweep with a positive control, so [UNMEASURED as a cross-branch sweep]; the walk's owner
    (15:54Z) names an old-framework donor for check_round_trip, commit 8fdc81e94c63 (old framework per
     that message; not read by this slice).
   - source: src-102/new/fuzz_preset.c (sha256 c7b4007bba7bab3e).

   THE SEGMENTS (offsets from the entry, read off the internal file crt.A.s):
   E1 +0x000 .. +0x058  `addi sp, sp, -0xe0`, the probe word `sd zero, 0(sp)`, the 13 saves at sp0 - 8 .. sp0 - 0x68
                        (ra, s0 .. s11 = Crt102Glue.CRT_SAVED), `addi s0, sp, 0xe0`, `andi sp, sp, -0x20`, `mv s1, sp`,
                        the two GOT words (A_OBJ 1: the use-after-return flag's address into a2; A_OBJ 0: the shadow
                        base variable's address into a1). Establishes crt_saved.
   E2 +0x058            `lw a2, 0(a2)`: the flag is 1 (alx_const, through PALib's pal_got_uar).
   E3 +0x05c .. +0x06c  `ld s10, 0(a1)` (the shadow base), `mv s5, a0` (doc), `beqz a2` NOT taken (a2 = 1),
                        `addi a0, zero, 0x140`, `jal __asan_stack_malloc_3`.
   the frame call       YGcallMxmn.aj_stack_malloc_at_xm (YGcallSx.aj_stack_malloc_at_x plus the memnorm keep, which
                        crt_live carries). ITS TWO HALVES: the capacity premise count_cid 3 (frames S) < fs_frames 3 is
                        Crt102Img.crt102_cap from the TEXT's own `Z.of_nat (length (frames S)) <= ck_FRAMES_CAP -
                        FR_check_round_trip`; the existential (a fresh class-3 frame pos with S' = set_fs f S) is the
                        rule's SMX, discharged by YGcallScf.stack_malloc_x_any (the model's frame malloc at any ARx,
                        the lemma Crt102Img's crt102_smx is proved by). No contract gives a0 <> 0 without the first.
   P  +0x070 .. +0x190  `mv s3, a0`, `j +0x7c`, `mv s11, s3`, `bnez s3` TAKEN: the call returned frame_addr ly 3 pos, at
                        or above 4096 (frames_bounds_x), so the alloca fallback +0x84 .. +0x9c is never run. Then H:
                        `sd s11, 0x70(s1)` (the F spill), s4 = F + 0xe0 (&copy), s2 = shadow_addr F, s7 = -8, the
                        frame header F + 0 / 8 / 0x10, the 40 shadow bytes of the 0x140-byte request (f1 0 .. 3, f8
                        4 .. 0xa and 0x10 .. 0x16 for back / v, f2 0xb .. 0xf and 0x17 .. 0x1b, 00 0x1c .. 0x22 for
                        copy, f3 0x23 .. 0x27), a0 = s4, a1 = 0, a2 = 0x38, `jal __asan_memset`. One run: no
                        inline shadow check lies in it, so no store shares a run with a check.
   the memset           YGcallMxmn.aj_intrin_at_xm at OSet: copy's 56 bytes are 0, so at M copy is the ZERO TREE
                        (crt_copy_zero; new:774-775 `struct pj copy = empty`).
   M  +0x194            the continuation.

   NUMERALS. ADDRESS: none (every code address is pa_sigma / pa_val of the listing; the entry is
   4 * A_prog_slot AS_check_round_trip). LENGTH: 224 (= CRT_FRAME, the own frame), 32 (the realignment), 104 (the
   saves), 512 / 64 (fs_frame_bytes 3 and its shadow), 320 (0x140, the request), 56 (struct pj), 8 (the spill word,
   a shadow granule), 40 (the request's shadow bytes), 4096 (= ESTACK), 2 ^ 31 / 2 ^ 32 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 /
   2 ^ 63 / 2 ^ 64 (image, shadow, stack and word bounds), 24 / 120 (the header's and the spill slot's ends). DERIVED: the
   cut offsets are Crt102Img's names (CRT_FLAG_LW / CRT_SHB_LD / CRT_P_OFF / CRT_M_OFF = +0x58 / +0x5c / +0x70 / +0x194, 4 *
   the slot inside the function), the spill offset 112 (= CRT_SP_F), the shadow offsets 28 .. 34
   (copy's granules, (F + 0xe0) / 8 - F / 8 ..), the atom indices (the engine's numbering). WORD: 0 (the copy bytes and
   their shadow), 1 (the flag), 2 ^ 64 - 8 (s7 = -8, the f8 poison byte). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YSRrMemnorm YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA Crt102Glue Crt102Img.
(* On the Step-1 contract texts (the re-hiding move): the walk's step relation is
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf and crt_live's journal is at R := YA0nH.wle' SEGS RZ_cf (Crt102Glue).
   P .. M runs the R runner paj_run_x_invR and the memset rule YGcallMxmn.aj_intrin_at_xmR at R (lifted by
   YA0nH.SRr_SRr' under YSRrG.SRr'_bind). The frame call's rule YGcallMxmn.aj_stack_malloc_at_xm has no R form, so
   E1 .. the frame call run at wle (plain SRr, the plain entry journal) inside YSRrG.SRr'_bind, and the journal at P
   is lifted to R by YCbqG.ajournal_xwR_mono at YA0nH.wle_wle'. Contract note: the internal file WLE-CONTRACT.md. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image A': the entry and the cuts are Crt102Img.v's (CRT_PC_A, CRT_FLAG_LW = +0x58, CRT_SHB_LD = +0x5c,
   CRT_P_OFF = +0x70, CRT_M_OFF = +0x194; crt_call_SM3_A / crt_call_MEMSET_A are the two jal sites, crt_got_A the GOT
   pairs, crt_regs_A the prologue's loads and moves). This file's own duplicates of them (CRT102E_* and crt102e_cap)
   were removed when Crt102Img.v landed on the lane base. ---- *)

(* ---- the segments' symbolic states (atoms: S10Env's TE, 0-31 the entry registers, 32-63 the current ones, 64- a
   segment's extras) ---- *)
(* E1: the entry. Regions: the own frame below the entry sp (writable), the shadow base's GOT word (A_OBJ 0, holding
   the variable's address A_OBJ 12), the flag's GOT word (A_OBJ 1, holding the flag cell's address, atom 64) *)
Definition E1_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) (-224) 0 (-224) 0 [];
    got_regionP;
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))] ].
Definition E1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_E1 : sstate := mkSS CRT_PC_A sr_atoms E1_regions None E1_facts.
(* E2: the flag's load; the flag cell (a2) is the only region *)
Definition ss_E2 : sstate :=
  mkSS (CRT_PC_A + CRT_FLAG_LW) cur_atoms [YP09.mkRegion (Some (xr 12)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]] None
    (mkFacts [] [] []).
(* E3: the shadow base's load (a1 = A_OBJ 12, holding SHADOW_OFF, atom 64), the flag test, to the frame call *)
Definition ss_E3 : sstate :=
  mkSS (CRT_PC_A + CRT_SHB_LD) cur_atoms [YP09.mkRegion (Some (xr 11)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))]] None
    (mkFacts [(xr 12, mkAF 1 1 0)] [] []).
(* P: after the frame call. Regions: the F spill slot s1 + 0x70 (writable), the frame header [F, F + 0x18) (a0 = F),
   the request's 40 shadow bytes at shadow_addr F (atom 64, aliased to `(a0 >> 3) + s10`) *)
Definition ss_P : sstate := mkSS (CRT_PC_A + CRT_P_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 112 120 112 120 [];
    YP09.mkRegion (Some (xr 10)) 0 24 0 24 [];
    YP09.mkRegion (Some 64%nat) 0 40 0 40 [] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 10, mkAF 4096 (2 ^ 47) 5); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] []
           [(SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 10) 0) (SLit 3)) (SOff (xr 26) 0), SOff 64 0)]).

(* a statics cell of the ledger: membership of one of its bytes in prh_pst, cell by cell (quantified over the list,
   whatever cells the E sweep appends) *)
Ltac crt_pst_in := unfold prh_pst;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
(* a register the run did not write *)
Ltac crtkeep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.
(* a callee-saved register index, by computation *)
Ltac crt_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).

(* the own frame (at most 224 + 16 below the entry sp after the realignment) and the frame call's 4096 fit *)
Lemma crt102e_stk : 4096 + 256 <= STKC.
Proof. vm_compute. discriminate. Qed.
Lemma crt102e_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
Lemma crt102e_aview_present : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* ---- the ledger's statics across a step that keeps every statics byte (quantified over prh_pst) ---- *)
Lemma crt102e_glob_keep : forall (Wc : world SEGS) memc memc' lv pk cn fl rn mo ow,
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  prh_glob (PA := PA) Wc memc lv pk cn fl rn mo ow -> prh_glob (PA := PA) Wc memc' lv pk cn fl rn mo ow.
Proof.
intros Wc memc memc' lv pk cn fl rn mo ow K HG. unfold prh_glob, prh_most, prh_own in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; try assumption;
  (eapply ts_vm_av; [| eassumption]; intros j Hj; apply K; crt_pst_in).
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the allocator laws at the cf instance's head (engine fold, YCbqG.v) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED STAND-IN (the unit's image binding of B: PALib's fields; owner: the contract texts; S10TxString.v:166 takes
   the same). At PI_prog_A, the whole-program instance, A_OBJ 1 is the UAR flag's GOT word (Crt102Img: +0x4c / +0x50
   resolve to it) and A_OBJ 0 the shadow base variable's (+0x48 / +0x54) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* MARKED STAND-IN (owner: the core's PALib; S10TxString.v:170 takes the same): the flag cell lies in the image *)
Hypothesis pal_uar_img : IMG_LO <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP.
(* MARKED STAND-IN (owner: the core's PALib; the class-3 twin of S10TxString.v:168's pal_stack_malloc0): the
   listing's __asan_stack_malloc_3 is the code record's *)
Hypothesis pal_stack_malloc3 : SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code B) 3.
(* MARKED STAND-IN (the image binding of B; owner: the contract texts; S10TxString.v:220 takes the same): alloc.c's
   statics are not the runtime's own statics and not errno, so a runtime call's image clause keeps them *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ---- frame class 3: the frozen FCiface.v contract with the memnorm keep (YGcallMxmn.v's astack_malloc_realizes_xm;
   owner the frame-class lane, which pays the _xm contracts at the instance from its image walks, FCm3s.v), and the one
   further hypothesis of YGcallSx.v's / YGcallMxmn.v's frame-call rule (OWNLOW, YGcallSx.v:64; S10TxString.v:174).
   The rule's SMX is NOT a hypothesis: YGcallScf.stack_malloc_x_any proves it at any ARx. ---- *)
Hypothesis ASM3 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx) SEGS B ARx 3.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
(* ---- __asan_memset (OSet), the runtime row with the memnorm keep (YGcallMxmn.v's aintrin_realizes_xm at the
   listing's own pc, as FuzzStrdup.v:240 takes __asan_memcpy's; owner: the libc stdio row / the image row, whose
   po_asan_memset_cf (CfApiPreset.v:115) is the instance's row) ---- *)
Hypothesis AMS : YGcallMxmn.aintrin_realizes_xm (fx := fx) SEGS B ARx OSet (SIGMA AS___asan_memset).

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders, named as Crt102Glue's Section context names them ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (Lam : list (Z * Z))
  (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
#[local] Notation sideA := (crt_side (rc := rc) (PI := prh_img_A) (RL := RL) (L := A_prog_listing) (PA := PA) (B := B)
  (doc := doc) (t := t) (D := D) (peak := peak) (most := most)).
#[local] Notation liveA := (crt_live (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation QFA := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation posA := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation savedA := (crt_saved (rc := rc) (L := A_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation spillA := (crt_spill (rc := rc) (L := A_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation dregsA := (crt_dregs (regs := regs) (doc := doc)).
#[local] Notation zeroA := (crt_copy_zero (rc := rc) (L := A_prog_listing) (PA := PA)).
#[local] Notation cfgA := (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A)).

(* ---- the text's premises this segment reads ---- *)
Hypothesis HPRE : fpre (PA := PA) B ARx STKC ly S Hp W regs mem md ch.
Hypothesis H10 : getr regs 10 = w64 doc.
Hypothesis HTREE : ck_tree_ok (PA := PA) ly S Lam W mem doc t D.
Hypothesis HLED : prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
Hypothesis HRUN : prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t).
Hypothesis HFRM : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip.
Hypothesis HROOM : room_live_cf S.
Hypothesis HIFC : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S.
Hypothesis HFRM0 : ck_frm0 (fx := fx).
Hypothesis HSM : rp_sm = ReaderRes.jr_strtod.
Hypothesis HCONS : PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)).

(* ---- the continuation at M: Crt102Glue's crt_live with the ledger of the entry and own = 0, s5 = doc, copy the zero
   tree; the float state the segment reaches (fxk) with frm_zero and fregs_kept_x (the walk's accepted shape); and
   the room position with NOTHING of round_trip done yet (crt_pos Sc (round_trip rp_sm t), the glue's reading of the
   text's entry premises HRUN / HIFC; the frame call changes st_fs only, which the position does not read) ---- *)
Definition crt102e_cont : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos rg,
    frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
    liveA 0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
    dregsA rg (frame_addr lyc CRT_CID pos) ->
    zeroA Wc memc (frame_addr lyc CRT_CID pos) ->
    posA Sc (PresetReqAt.round_trip rp_sm t) ->
    YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_M_OFF rg memc mdc) QFA.

(* ---- the realigned frame base ---- *)
Lemma crt102e_sp1_word : 224 <= sp0 ->
  alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (getr regs 2) + -224)) (Z_to_bv 64 (-32)) = w64 sp1.
Proof.
intros H224. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. unfold w64, CRT_sp1, CRT_FRAME, CRT_ALIGN, spZ in *.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (bv_unsigned (getr regs 2) + -224)) by lia.
change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32). rewrite ts_land_m32 by lia.
rewrite Z.mod_small; [lia|]. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia|].
pose proof (Z.mul_div_le (bv_unsigned (getr regs 2) - 224) 32 ltac:(lia)). lia.
Qed.
Lemma crt102e_sp1_range : sp0 mod 16 = 0 -> 256 <= sp0 -> sp0 - 240 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0.
Proof.
intros Hal16 H. unfold CRT_sp1, CRT_FRAME, CRT_ALIGN.
pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
split; [|apply Z.mod_mul; lia]. split; [|lia].
assert ((sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16) as [Hm|Hm]
  by (rewrite Z.mod_divide in Hal16 by lia; destruct Hal16 as [q Hq]; rewrite Hq; lia); lia.
Qed.

(* ---- the side facts at the entry, and across the segment ---- *)
Lemma crt102e_side0 : sideA ly S Hp W mem Lam peak cnt 0 ran.
Proof.
pose proof HPRE as (_ & HROD & _).
pose proof HTREE as (HN & HDL & _).
refine {| crt_side_ledger := HLED; crt_side_peak := _; crt_side_room := HROOM;
          crt_side_arodata := HROD; crt_side_doc := HN; crt_side_doc_blocks := HDL |}.
lia.
Qed.

(* the side facts at a later state of the same layout whose blocks are the entry's: every block byte, every image byte
   that is not the runtime's own nor errno, every statics byte and doc's node kept *)
Lemma crt102e_side_keep : forall Sc memc mdc,
  ARx ly Sc Hp W memc mdc ->
  ablocks B ly Sc = ablocks B ly S ->
  (room_live_cf S -> room_live_cf Sc) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     aview SEGS (w_H W) memc (p + i) = aview SEGS (w_H W) mem (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  (forall a, doc <= a < doc + 56 -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a /\ apresent (w_H W) memc a) ->
  sideA ly Sc Hp W memc Lam peak cnt 0 ran.
Proof.
intros Sc memc mdc HAR Eab Hroom Kbl Kimg Kpst Kdoc.
pose proof crt102e_side0 as HS0.
pose proof (crt_side_ledger HS0) as HL0. pose proof (crt_side_arodata HS0) as HRO0.
pose proof (crt_side_doc HS0) as HN0. pose proof (crt_side_doc_blocks HS0) as HD0.
assert (HBL : Forall (fun ak => prh_hblock (PA := PA) B ly S Hp W mem (fst ak) (snd ak)) Lam)
  by (eapply prh_ledger_blocks; exact HL0).
assert (HBLK : forall a k, In (a, k) Lam ->
  In (a - 16, k + 16) (ablocks B ly S) /\ forall x, a <= x < a + k -> a - 16 <= x < a - 16 + req_size (k + 16)).
{ intros a k Hin. rewrite Forall_forall in HBL. destruct (HBL _ Hin) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
  change (@cf_head CfParams_preset) with 16 in Hab. split; [exact Hab|].
  intros x Hx. unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia. }
(* the ledger *)
assert (HL1 : prh_ledger (PA := PA) B ly Sc Hp W memc Lam peak cnt SIZE_MAXZ ran most 0).
{ unfold prh_ledger. split; [|split; [|split]].
  - apply (crt102e_glob_keep W mem memc); [exact Kpst|]. eapply prh_ledger_glob; exact HL0.
  - eapply prh_ledger_nodup; exact HL0.
  - rewrite Forall_forall in HBL |- *. intros [a k] Hin. specialize (HBL _ Hin). cbn [fst snd] in *.
    unfold prh_hblock in *. destruct HBL as (Hk & Hab & Hhp & Ha16 & Hv).
    split; [exact Hk|]. split; [rewrite Eab; exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
    eapply ts_vm_av; [|exact Hv]. intros j Hj. change (@cf_head CfParams_preset) with 16 in *.
    apply (Kbl (a - 16) (k + 16) (Z.of_nat j) Hab). unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
  - eapply prh_ledger_heads; exact HL0. }
refine {| crt_side_ledger := HL1; crt_side_peak := _; crt_side_room := Hroom HROOM;
          crt_side_arodata := _; crt_side_doc := _; crt_side_doc_blocks := HD0 |}.
{ lia. }
(* the read-only view *)
{ intros a Hro Hno Her. rewrite (Kimg a (crt102e_ro_img a Hro) Hno Her (fun Hp' => pst_not_ro_A a Hp' Hro)).
  exact (HRO0 a Hro Hno Her). }
(* the document *)
apply (pj_nodeR_frame SEGS t (mrestrict (w_H W) mem) (mrestrict (w_H W) memc) (prh_lin Lam) doc D HN0).
intros x Hx.
assert (Kx : aview SEGS (w_H W) memc x = aview SEGS (w_H W) mem x /\ apresent (w_H W) memc x).
{ destruct Hx as [Hx | ((a & k) & Hb & Hx)]; [exact (Kdoc x Hx)|].
  unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  destruct (HBLK a k (HD0 _ Hb)) as (Hab & Hr). specialize (Hr x Hx).
  split.
  - replace x with ((a - 16) + (x - (a - 16))) by lia. apply (Kbl _ _ _ Hab). lia.
  - assert (Hab' : In (a - 16, k + 16) (ablocks B ly Sc)) by (rewrite Eab; exact Hab).
    destruct (alx_blocks _ _ _ LAWS ly Sc Hp W memc mdc _ _ HAR Hab') as (_ & _ & _ & _ & Hpres & _).
    exact (proj1 (Hpres x Hr)). }
destruct Kx as [Kv Kp]. split.
- exact (mbyte_of_aview SEGS (w_H W) (w_H W) mem memc x Kv).
- intros _. exact (apresent_writable SEGS _ _ _ Kp).
Qed.

(* ---- E1: the entry's symbolic state ---- *)
Lemma crt102e_E1_entry :
  st_ok_pi SEGS VAL (TE regs regs [w64 (as_uar_cell B)]) ss_E1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CRT_PC_A)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regs [w64 (as_uar_cell B)]) (mrestrict (w_H W) mem).
Proof.
pose proof HPRE as (HPX & _).
pose proof HPX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crt102e_stk as HSTK.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow (PI := PA) B PAL), (pal_cell (PI := PA) B PAL) in Kgot.
rewrite (pal_got_uar (PI := PA) B PAL) in Kgotu.
pose proof (pal_got_uar_disj (PI := PA) B PAL) as (D01 & _).
set (E := TE regs regs [w64 (as_uar_cell B)]).
assert (E2 : ew E 2 = getr regs 2) by (apply te_entry; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (E64 : ew E 64 = w64 (as_uar_cell B)) by exact (te_more_lt regs regs [w64 (as_uar_cell B)] 0 ltac:(lia)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 1)) as R1.
pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
pose proof (ts_rdword_range _ _ _ _ Kgotu) as Ruar.
pose proof (@pa_obj_img _ _ PA 0 ltac:(lia)) as I0. pose proof (@pa_obj_img _ _ PA 1 ltac:(lia)) as I1.
pose proof crt_pa_hi_A as Hhi.
split.
- apply ts_st_ok.
  all: try change (TE regs regs [w64 (as_uar_cell B)]) with E.
  + unfold E, TE. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold E1_regions, got_regionP. repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ 2 sp0); [exact Usp | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * apply (ts_rok E _ (A_OBJ 0) (VAL (A_OBJ 0))); [rewrite Eo0; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * apply (ts_rok E _ (A_OBJ 1) (VAL (A_OBJ 1))); [rewrite Eo1; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff 64 0) (as_uar_cell B));
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgotu).
  + apply pairwise_disjoint_of_extents. unfold E1_regions, got_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite Usp, Eo0, Eo1, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [E1_facts f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- E2: the flag's load ---- *)
Lemma crt102e_E2_entry : forall regsc memc (Wc : world SEGS),
  getr regsc 12 = w64 (as_uar_cell B) -> rd32 (aview SEGS (w_H Wc) memc) (as_uar_cell B) 1 ->
  st_ok_pi SEGS VAL (TE regs regsc []) ss_E2
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_FLAG_LW))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc []) (mrestrict (w_H Wc) memc).
Proof.
intros regsc memc Wc R12 Hu. pose proof pal_uar_img as Huar. unfold IMG_LO, IMG_TOP in Huar.
set (E := TE regs regsc []).
assert (X12 : bv_unsigned (ew E (xr 12)) = as_uar_cell B).
{ unfold E, xr. rewrite (te_cur regs regsc [] 12%bv 12) by reflexivity. rewrite R12. apply unsigned_lit_small. lia. }
split.
- apply ts_st_ok.
  all: try change (TE regs regsc []) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 12) (as_uar_cell B)); [exact X12 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (ts_val_mem_rd32 _ _ _ _ Hu).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- E3: the shadow base's load, `mv s5, a0`, the flag test, to the frame call ---- *)
Lemma crt102e_E3_entry : forall regsc memc (Wc : world SEGS),
  getr regsc 11 = w64 (VAL (A_OBJ 12)) -> getr regsc 12 = w64 1 ->
  rdword (aview SEGS (w_H Wc) memc) (VAL (A_OBJ 12)) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs regsc [w64 SHADOW_OFF]) ss_E3
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_SHB_LD))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc [w64 SHADOW_OFF]) (mrestrict (w_H Wc) memc).
Proof.
intros regsc memc Wc R11 R12 Hc.
pose proof (@pa_obj_img _ _ PA 12 ltac:(lia)) as I12.
pose proof crt_pa_hi_A as Hhi. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12v.
set (E := TE regs regsc [w64 SHADOW_OFF]).
assert (X11 : bv_unsigned (ew E (xr 11)) = VAL (A_OBJ 12)).
{ unfold E, xr. rewrite (te_cur regs regsc _ 11%bv 11) by reflexivity. rewrite R11. apply unsigned_lit_small. lia. }
assert (X12 : bv_unsigned (ew E (xr 12)) = 1).
{ unfold E, xr. rewrite (te_cur regs regsc _ 12%bv 12) by reflexivity. rewrite R12. reflexivity. }
assert (E64 : ew E 64 = w64 SHADOW_OFF) by exact (te_more_lt regs regsc [w64 SHADOW_OFF] 0 ltac:(lia)).
split.
- apply ts_st_ok.
  all: try change (TE regs regsc [w64 SHADOW_OFF]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 11) (VAL (A_OBJ 12))); [exact X11 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 8 (SOff 64 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hc).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X12. cbn. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- P: after the frame call (+0x70), F = a0 a live class-3 frame ---- *)
Lemma crt102e_P_entry : forall lyc Sc Hpc (Wc : world SEGS) memc mdc pos rg,
  ARx lyc Sc Hpc Wc memc mdc -> In (CRT_CID, pos) (frames Sc) ->
  (forall a, sp1 + 112 <= a < sp1 + 120 -> apresent (w_H Wc) memc a) ->
  YM05.alloc_ceiling <= sp1 -> sp1 + 120 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr lyc CRT_CID pos) -> getr rg 26 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs rg [w64 (shadow_addr (frame_addr lyc CRT_CID pos))]) ss_P
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_P_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg [w64 (shadow_addr (frame_addr lyc CRT_CID pos))]) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Hpc Wc memc mdc pos rg HAR Hin Hsp Hc Hc47 Hs32 R9 R10 R26.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47'.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HAR Hin) as (F32 & _ & Ffr & Fsh).
change (fs_frame_bytes CRT_CID) with 512 in F2, F3, Ffr, Fsh. change (512 / 8) with 64 in Fsh.
set (F := frame_addr lyc CRT_CID pos) in *.
set (E := TE regs rg [w64 (shadow_addr F)]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (Hsh2 : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
unfold SHADOW_OFF in Hsh2.
split.
- apply ts_st_ok.
  all: try change (TE regs rg [w64 (shadow_addr F)]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hsp. lia.
    * apply (ts_rok E _ (xr 10) F); [exact X10 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Ffr. lia.
    * apply (ts_rok E _ 64 (shadow_addr F)); [exact X64 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Fsh o ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X10, X64.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X10, X26, X64.
      change (2 ^ 5) with 32. change (2 ^ 0) with 1.
      unfold shadow_addr, SHADOW_OFF. repeat split; try lia.
    * cbn [f_alias alias_ok]. split; [|exact I].
      apply (ts_alias_shadow E (xr 10) (xr 26) 64 F X10 X26 X64). lia.
- unfold sh_ok. apply Forall_nil.
Qed.


Lemma crt102e_at_P : forall S2 memB mdB kj pos rg,
  AJ STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly S2 Hp W memB mdB kj ->
  (exists f, S2 = set_fs f S) ->
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) memB a = aview SEGS (w_H W) mem a) ->
  savedA W memB ->
  rdword (aview SEGS (w_H W) memB) (frame_addr ly CRT_CID pos + fs_frame_bytes CRT_CID - 8) = Some (flag_addr ly CRT_CID pos) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memB) ->
  getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = w64 sp0 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly CRT_CID pos) -> getr rg 21 = w64 doc ->
  getr rg 26 = w64 SHADOW_OFF ->
  crt102e_cont ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (mkst rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_P_OFF))) memB (seg_rom SEGS)) mdB) QFA.
Proof.
intros S2 memB mdB kj pos rg HJ (f & ES2) KPST HSV HFL HMN R2 R3 R4 R8 R9 R10 R21 R26 HK.
pose proof HPRE as (HPX & HROD & Hsp64 & Hrac).
pose proof HPX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof crt102e_stk as HSTK.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HJ as (HARB & HLYB & _ & _ & _ & HFRB & _ & _ & _ & _ & _ & _ & _ & HPRB & _).
assert (Hin : In (CRT_CID, pos) (frames S2)) by (rewrite HFRB; left; reflexivity).
destruct (crt102e_sp1_range Hal16 ltac:(lia)) as (Hs1a & Hs1b).
destruct (crt102e_P_entry ly S2 Hp W memB mdB pos rg HARB Hin ltac:(intros a Ha; apply HPRB; lia) ltac:(lia) ltac:(lia) Hs1b
  R9 R10 R26) as [HS SHOK].
destruct (frames_bounds_x _ _ _ LAWS ly S2 Hp W memB mdB CRT_CID pos HARB Hin) as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2, Fb3, HFL.
set (F := frame_addr ly CRT_CID pos) in *.
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (HEI : img_env VAL A_LIM (TE regs rg [w64 (shadow_addr F)])) by apply te_env.
set (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS P)
  by exact (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
assert (HPM : P memB) by exact HMN.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS P PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_tok_x_inv RUN HS HJ SHOK HPM (0, 0).
{ cbv [ss_P ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0)); [reflexivity | | cbn; lia | cbn; lia |].
  { unfold xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 10) F); [reflexivity | | |].
  { unfold xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. unfold w64. apply unsigned_lit_small. lia. }
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512. fold F. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 64%nat (shadow_addr F)); [reflexivity | | |].
  { rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CRT_CID / 8) with 64. fold F. lia. }
  apply awr_ok_nil. }

pmkst HS.
pose proof HJ as (HARP & _ & _ & _ & _ & HFRP & _ & _ & _ & _ & _ & _ & _ & HPRP & _).
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23.
prreg HS (27%bv : bv 5) Q27.
assert (E42 : ew (TE regs rg [w64 (shadow_addr F)]) 42 = w64 F)
  by (change 42%nat with (32 + 10)%nat; rewrite (te_cur regs rg _ 10%bv 10) by reflexivity; exact R10).
assert (U42 : bv_unsigned (ew (TE regs rg [w64 (shadow_addr F)]) 42) = F) by (rewrite E42; apply unsigned_lit_small; lia).
assert (E64 : ew (TE regs rg [w64 (shadow_addr F)]) 64 = w64 (shadow_addr F)) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew (TE regs rg [w64 (shadow_addr F)]) 64) = shadow_addr F)
  by (rewrite E64; apply unsigned_lit_small; exact Hsh).
assert (X9 : bv_unsigned (ew (TE regs rg [w64 (shadow_addr F)]) (xr 9)) = sp1).
{ unfold xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : getr (ms_regs ms) 10 = w64 (F + 224)) by (rewrite Q10, U42; reflexivity).
assert (X11 : getr (ms_regs ms) 11 = w64 0) by (rewrite Q11; reflexivity).
assert (X12 : getr (ms_regs ms) 12 = w64 56) by (rewrite Q12; reflexivity).
assert (X18 : getr (ms_regs ms) 18 = w64 (shadow_addr F)) by (rewrite Q18; exact E64).
assert (X19 : getr (ms_regs ms) 19 = w64 F) by (rewrite Q19; exact E42).
assert (X20 : getr (ms_regs ms) 20 = w64 (F + 224)) by (rewrite Q20, U42; reflexivity).
assert (X23 : getr (ms_regs ms) 23 = w64 (2 ^ 64 - 8)) by (rewrite Q23; reflexivity).
assert (X27 : getr (ms_regs ms) 27 = w64 F) by (rewrite Q27; exact E42).
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by crtkeep HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by crtkeep HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by crtkeep HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by crtkeep HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by crtkeep HS.
assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by crtkeep HS.
assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by crtkeep HS.
(* the run's memory: what it wrote, and what it left *)
pose proof (ts_region_nth_c _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (ts_region_nth_c _ _ _ 2 _ HS eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
assert (U0 : U (TE regs rg [w64 (shadow_addr F)]) (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
assert (SH0 : forall k, 28 <= k <= 34 -> aview SEGS (w_H W) (ms_mem ms) (shadow_addr F + k) = Some 0).
{ intros k Hk. apply (ts_aview_of_vm1 _ _ _ _); [|lia].
  assert (k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34) as Hc by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
  lazymatch goal with |- val_mem _ _ (_ + ?kk) _ _ =>
    pose proof (ts_field _ _ 64 (shadow_addr F) _ _ _ _ _ kk 1 (SLit 0) HR2 X64
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
    rewrite U0 in V; exact V end. }
assert (VSP : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp1 + 112) 8 F).
{ pose proof (ts_field _ _ (xr 9) sp1 _ _ _ _ _ 112 8 (SOff 42 0) HR0 X9
    ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V. change (N.to_nat 8) with 8%nat in V.
  rewrite ts_U_atom_mod, U42 in V. exact V. }
assert (Hwr : forall a, in_wrange (TE regs rg [w64 (shadow_addr F)]) (ss_mem ss_P) a ->
  (sp1 + 112 <= a < sp1 + 120) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 40)).
{ intros a (r & Hr & Ha). cbv [ss_P ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha;
  [ change 41%nat with (xr 9) in Ha; rewrite X9 in Ha; left
  | change (xr 10) with 42%nat in Ha; rewrite U42 in Ha; right; left
  | rewrite X64 in Ha; right; right]; lia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((sp1 + 112 <= a < sp1 + 120) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 40)) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hn; exact (ts_keep W _ (ss_mem ss_P) memB (ms_mem ms) _ HFr Hwr a Ha Hn)).
(* ---- the memset (+0x190): copy := 56 zero bytes ---- *)
assert (Hsp1w : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite Z2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HRAP : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
destruct (alx_frames _ _ _ LAWS ly S2 Hp W (ms_mem ms) _ CRT_CID pos HARP ltac:(rewrite HFRP; left; reflexivity))
  as (F32 & _ & FfrP & FshP).
assert (Fq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
change (fs_frame_bytes CRT_CID) with 512 in FfrP, FshP. change (512 / 8) with 64 in FshP.
assert (Hsha : forall a, F <= a < F + 512 -> shadow_addr a = shadow_addr F + (a - F) / 8).
{ intros a Ha. unfold shadow_addr. set (q := F / 32) in *.
  assert (A3 : F / 8 = 4 * q) by (rewrite Fq at 1; replace (32 * q) with ((4 * q) * 8) by lia; apply Z.div_mul; lia).
  assert (A4 : a / 8 = (a - F) / 8 + 4 * q).
  { replace a with ((a - F) + (4 * q) * 8) at 1 by lia. apply Z.div_add. lia. }
  rewrite A4, A3. lia. }
assert (SHOPEN : forall memx, (forall k, 28 <= k <= 34 -> aview SEGS (w_H W) memx (shadow_addr F + k) = Some 0) ->
  range_addressable (aview SEGS (w_H W) memx) SHADOW_OFF (F + 224) 56).
{ intros memx Hz x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). rewrite (Hsha x) by lia.
  apply Hz. pose proof (Z.div_le_mono 224 (x - F) 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_mono (x - F) 279 8 ltac:(lia) ltac:(lia)) as D2.
  change (224 / 8) with 28 in D1. change (279 / 8) with 34 in D2. set (y := (x - F) / 8) in *. lia. }
assert (HULL : forall memx, (forall i, 0 <= i < 64 -> apresent (w_H W) memx (shadow_addr F + i)) ->
  shadow_hull_vis (aview SEGS (w_H W) memx) (F + 224) 56).
{ intros memx Hpr s Hs.
  rewrite (Hsha (F + 224)), (Hsha (F + 224 + 56 - 1)) in Hs by lia.
  replace (F + 224 - F) with 224 in Hs by lia. replace (F + 224 + 56 - 1 - F) with 279 in Hs by lia.
  change (224 / 8) with 28 in Hs. change (279 / 8) with 34 in Hs.
  pose proof (Z.div_mod (shadow_addr F + 28) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr F + 28) 8 ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (shadow_addr F + 34) 8 ltac:(lia)) as D3.
  set (y1 := (shadow_addr F + 28) / 8) in *. set (y2 := (shadow_addr F + 34) / 8) in *.
  set (r1 := (shadow_addr F + 28) mod 8) in *. set (shF := shadow_addr F) in *.
  replace s with (shF + (s - shF)) by lia.
  apply crt102e_aview_present. apply Hpr. lia. }
(* ---- the memset (+0x190, Crt102Img.crt_call_MEMSET_A): copy := 56 zero bytes ---- *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply YA0nH.SRr_SRr'.
  eapply (YGcallMxmn.aj_intrin_at_xmR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW OSet (SIGMA AS___asan_memset) AMS
    W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (F + 224) 0 56 (sp1 - sp0) (getr (ms_regs ms) 1) HJ X10 X11 X12
    ltac:(lia) ltac:(lia) ltac:(lia) Hsp1w).
  - clear - Hal16 Hs1b. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hs1b; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hs1b as [q3 Hq3]. apply Z.mod_divide; [lia|]. exists (2 * q3 - q1). lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite Z3, R3. exact Hgp.
  - rewrite Z4, R4. exact Htp.
  - reflexivity.
  - exact HRAP.
  - intros a Ha. split.
    + right; right; right. exists CRT_CID, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes CRT_CID) with 512. fold F. lia.
    + unfold ESTACK. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3.
    unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - exact (SHOPEN (ms_mem ms) SH0).
  - intros _. apply HULL. intros i Hi. exact (proj1 (FshP i Hi)).
  - exact I. }
intros W3 c3 _ (-> & rgM & memM & mdM & -> & HJM & HprM & H10M & HeffM & HfrM & HpresM & HmnM).
assert (Era : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_M_OFF)))
  by (rewrite Q1; f_equal; vm_compute; reflexivity).
rewrite Era.
pose proof HJM as (HARM & _ & _ & _ & _ & HFRM' & _ & _ & KceilM & KblM & KimgM & KfrM & _ & HPRM & _ & _ & _).
assert (HinM : In (CRT_CID, pos) (frames S2)) by exact Hin.
destruct (alx_frames _ _ _ LAWS ly S2 Hp W memM mdM CRT_CID pos HARM HinM) as (_ & _ & FfrM & FshM).
change (fs_frame_bytes CRT_CID) with 512 in FfrM, FshM. change (512 / 8) with 64 in FshM.
(* the memset keeps everything but copy and its own window; the run kept everything but its three regions *)
assert (KPM : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 224 <= a < F + 224 + 56) -> ~ (sp1 - 4096 <= a < sp1) ->
  ~ ((sp1 + 112 <= a < sp1 + 120) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 40)) ->
  aview SEGS (w_H W) memM a = aview SEGS (w_H W) memB a).
{ intros a Ha H1 H2 H3. rewrite (HfrM a Ha H1 ltac:(unfold ESTACK; lia)). exact (KP a Ha H3). }
assert (Hshb : SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 64 <= kHighShadowEnd).
{ unfold shadow_addr, SHADOW_OFF, kHighShadowEnd. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3.
  set (q := F / 32) in *. assert (F / 8 = 4 * q)
    by (rewrite Fq at 1; replace (32 * q) with ((4 * q) * 8) by lia; apply Z.div_mul; lia). lia. }
unfold SHADOW_OFF, kHighShadowEnd in Hshb. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3.
(* the statics, from the entry *)
assert (KPSTM : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (pst_in_img_A a Ha) as Hi. pose proof (Hsegs a Hi) as Hlow.
  assert (NF : ~ (F <= a < F + 512)).
  { intros Hx. exact (frm_img_x _ _ _ LAWS ly S2 Hp W memB mdB CRT_CID pos a HARB Hin
      ltac:(change (fs_frame_bytes CRT_CID) with 512; fold F; lia) Hi). }
  rewrite (KPM a ltac:(lia)); [exact (KPST a Ha) | lia | lia |].
  unfold kLowMemEnd in Hlow. lia. }
(* the thirteen saved words *)
assert (HSVM : savedA W memM).
{ intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi. apply KPM; lia. }
(* the frame's flag word and the spill *)
assert (HFLM : rdword (aview SEGS (w_H W) memM) (F + 512 - 8) = Some (flag_addr ly CRT_CID pos)).
{ rewrite <- HFL. apply ts_rdword_keep. intros j Hj. apply KPM; lia. }
assert (VSPM : val_mem SEGS (mrestrict (w_H W) memM) (sp1 + 112) 8 F).
{ eapply ts_vm_av; [|exact VSP]. intros i Hi. apply HfrM; [lia | lia | unfold ESTACK; lia]. }
assert (SH0M : forall k, 28 <= k <= 34 -> aview SEGS (w_H W) memM (shadow_addr F + k) = Some 0).
{ intros k Hk. rewrite (HfrM (shadow_addr F + k) ltac:(lia)); [exact (SH0 k Hk) | lia | unfold ESTACK; lia]. }
(* the document's node: its frame is an entry frame *)
pose proof HTREE as (_ & _ & _ & (_ & (cd & pd & Hind & Hd1 & Hd2) & _)).
assert (HindM : In (cd, pd) (frames S2)) by (rewrite HFRM'; apply in_or_app; right; exact Hind).
destruct (alx_frames _ _ _ LAWS ly S2 Hp W memM mdM cd pd HARM HindM) as (_ & _ & FdM & _).
assert (EabS : ablocks B ly S2 = ablocks B ly S) by (rewrite ES2; reflexivity).
refine (HK fx ly S2 Hp W memM mdM kj pos rgM HFRM0 (fun r _ => eq_refl) _ _ _ _).
- refine {| crt_live_journal := ex_intro _ [] (conj HJM (le_n 0)); crt_live_side := _; crt_live_lam_perm := _;
            crt_live_blocks_perm := _;
            crt_live_dx_apart := _; crt_live_saved := HSVM; crt_live_frame := _; crt_live_fspill := _;
            crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := _ |}.
  { apply (crt102e_side_keep S2 memM mdM HARM EabS).
    - intros H. rewrite ES2. apply RL_set_fs. exact H.
    - intros p n i Hp0 Hi. exact (KblM p n i Hp0 ltac:(rewrite EabS; exact Hp0) Hi (inFP_nil _)).
    - intros a Hi Hno Her Hnp. apply KimgM; [exact Hi | exact Hno | exact Her | exact Hnp |].
      apply fp_spares_closed. intros (r & [] & _).
    - exact KPSTM.
    - intros a Ha. split.
      + apply (KfrM cd pd a Hind); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil].
      + exact (proj1 (FdM a ltac:(lia))). }
  { cbn [app]. apply Permutation_refl. }
  { rewrite EabS. cbn [ck_hblks map]. rewrite app_nil_r. apply Permutation_refl. }
  { intros bk []. }
  { refine {| crt_frame_listed := HinM; crt_frame_flag_word := _; crt_frame_present := _ |}.
    - change (fs_frame_bytes CRT_CID) with 512. exact HFLM.
    - intros a Ha. exact (proj1 (FfrM a Ha)). }
  { exact VSPM. }
  { exact (SHOPEN memM SH0M). }
  { apply HULL. intros i Hi. exact (proj1 (FshM i Hi)). }
  intros H0. exact (HmnM (HPM H0)).
- assert (PM : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr rgM r = getr (ms_regs ms) r)
    by (intros r Hr; exact (ts_ap _ _ r HprM Hr)).
  refine {| crt_dregs_bregs := _; crt_dregs_s5 := _ |}.
  { refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
              crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
              crt_bregs_s11 := _ |}.
    + rewrite PM by crt_cs. rewrite Z2. exact R2.
    + rewrite PM by crt_cs. rewrite Z3. exact R3.
    + rewrite PM by crt_cs. rewrite Z4. exact R4.
    + rewrite PM by crt_cs. rewrite Z8. exact R8.
    + rewrite PM by crt_cs. rewrite Z9. exact R9.
    + rewrite PM by crt_cs. exact X18.
    + rewrite PM by crt_cs. exact X20.
    + rewrite PM by crt_cs. exact X19.
    + rewrite PM by crt_cs. exact X23.
    + rewrite PM by crt_cs. rewrite Z26. exact R26.
    + rewrite PM by crt_cs. exact X27. }
  rewrite PM by crt_cs. rewrite Z21. exact R21.
- unfold crt_copy_zero, pj_zeroR, garr8, CRT_OFF_COPY. fold F. intros j Hj. rewrite repeat_length in Hj.
  rewrite nth_repeat. split; [|lia].
  apply ts_vm1_of_aview. rewrite (HeffM (Z.of_nat j) ltac:(lia)). reflexivity.
- (* the position: nothing of round_trip done; set_fs is invisible to it *)
  refine {| crt_pos_strtod := HSM; crt_pos_ex := _ |}. exists [], rp_hist.
  refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
  + reflexivity.
  + rewrite Nat.add_0_r, ES2. exact HIFC.
  + rewrite Nat.add_0_r. exact HRUN.
  + rewrite Nat.add_0_r. exact HCONS.
Qed.


(* ---- E1 .. E3 and the frame call (+0x6c, Crt102Img.crt_call_SM3_A) ---- *)
Lemma crt102e_top : crt102e_cont ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_check_round_trip) regs mem md) QFA.
Proof.
intros HK.
(* E1 .. the frame call at wle (the frame call's rule has no R form), then crt102e_at_P at R *)
apply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf W _ (fun W' c' => YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W' c' QFA) QFA);
  [apply YA0nH.SRr_SRr' | intros W' c' _ HQ; exact HQ].
pose proof HPRE as (HPX & HROD & Hsp64 & Hrac).
pose proof HPX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof crt102e_stk as HSTK.
destruct (crt102e_sp1_range Hal16 ltac:(lia)) as (Hs1a & Hs1b).
destruct crt102e_E1_entry as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STKC [] ly S Hp W regs mem md ch HPX) as HJ.
set (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS P)
  by exact (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
assert (HPM : P mem) by (intros H; exact H).
assert (EE : forall (r : bv 5) n more, Z.of_nat n = bv_unsigned r -> ew (TE regs regs more) n = getr regs r)
  by (intros r n more Hn; apply te_entry; exact Hn).
assert (Usp : bv_unsigned (ew (TE regs regs [w64 (as_uar_cell B)]) 2) = sp0) by (rewrite (EE 2%bv 2%nat) by reflexivity; reflexivity).
assert (HEI : img_env VAL A_LIM (TE regs regs [w64 (as_uar_cell B)])) by apply te_env.
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL PA B PST ARx _ LAWS P PLAW).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL PA B PST ARx _ LAWS P PLAW).
unfold cfg_at. rewrite <- crt_pc_A.
(* ---- E1: entry to the flag's load ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (0, 0) (CRT_PC_A + CRT_FLAG_LW).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
pose proof HJ as (HAR1 & _ & _ & _ & _ & HFR1 & _ & _ & _ & _ & _ & _ & _ & HPR1 & _).
prreg HS (12%bv : bv 5) R12. prreg HS (11%bv : bv 5) R11. prreg HS (10%bv : bv 5) R10.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (ts_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (EP2 : ew (TE regs regs [w64 (as_uar_cell B)]) 2 = getr regs 2) by (apply EE; reflexivity).
assert (H224 : 224 <= sp0) by lia.
assert (X2 : getr (ms_regs ms) 2 = w64 sp1) by (rewrite R2, EP2; exact (crt102e_sp1_word H224)).
assert (X9 : getr (ms_regs ms) 9 = w64 sp1) by (rewrite R9, EP2, (crt102e_sp1_word H224); apply ts_add0_word).
assert (X8 : getr (ms_regs ms) 8 = getr regs 2) by (rewrite R8; exact EP2).
assert (X10 : getr (ms_regs ms) 10 = w64 doc) by (rewrite R10, (EE 10%bv 10%nat) by reflexivity; exact H10).
assert (X3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite R3; apply EE; reflexivity).
assert (X4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite R4; apply EE; reflexivity).
assert (X11 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 12))) by (rewrite R11, te_img by (unfold A_TEXT, A_LIM; lia); reflexivity).
assert (X12 : getr (ms_regs ms) 12 = w64 (as_uar_cell B)) by (rewrite R12; exact (te_more_lt regs regs _ 0 ltac:(lia))).
(* the saves (Crt102Glue.crt_saved) *)
assert (HSV : savedA W (ms_mem ms)).
{ intros j Hj. do 13 (destruct j as [|j]; [
    lazymatch goal with |- val_mem _ _ _ _ (bv_unsigned (getr regs (nth ?jj CRT_SAVED 0%bv))) =>
      let r := eval vm_compute in (nth jj CRT_SAVED 0%bv) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      let off := eval vm_compute in (- 8 * (Z.of_nat jj + 1)) in
      pose proof (ts_field _ _ 2 sp0 _ _ _ _ _ off 8 (SOff n 0) HR0 Usp
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; change (N.to_nat 8) with 8%nat in V;
      rewrite ts_U_atom_mod, (EE r n) in V by reflexivity;
      change (nth jj CRT_SAVED 0%bv) with r;
      replace (sp0 - 8 * (Z.of_nat jj + 1)) with (sp0 + off) by (cbn; lia); exact V
    end |]). lia. }
(* E1 wrote only its own frame below the entry sp *)
assert (Hwr1 : forall a, in_wrange (TE regs regs [w64 (as_uar_cell B)]) (ss_mem ss_E1) a -> sp0 - 224 <= a < sp0).
{ intros a (r & Hr & Ha). cbv [ss_E1 ss_mem E1_regions got_regionP In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha;
  [rewrite Usp in Ha | |]; lia. }
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 224 <= a < sp0) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; exact (ts_keep W _ (ss_mem ss_E1) mem (ms_mem ms) _ HFr Hwr1 a Ha Hn)).
clear HF HG HFr HR0 R2 R3 R4 R8 R9 R10 R11 R12.
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
(* ---- E2: the flag's load (Crt102Img.crt_regs_A: lw a2, 0(a2)) ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR1) as (_ & Kuar1 & _ & _).
destruct (crt102e_E2_entry regs1 mem1 W X12 Kuar1) as [HS2 SHOK2].
clear HS SHOK.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] => change (BASE + k) with (BASE + (CRT_PC_A + CRT_FLAG_LW)) end.
assert (HEI2 : img_env VAL A_LIM (TE regs regs1 [])) by apply te_env.
paj_run_to_tok_x_inv RUNTO HS2 HJ SHOK2 HPM (0, 0) (CRT_PC_A + CRT_SHB_LD).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS2.
pose proof HJ as (HAR2 & _).
prreg HS2 (12%bv : bv 5) Q12.
assert (Y : forall (r : bv 5), In r [2; 3; 4; 8; 9; 10; 11]%bv -> getr (ms_regs ms0) r = getr regs1 r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crtkeep HS2 |]). destruct Hr. }
assert (Hnowr2 : forall a, ~ in_wrange (TE regs regs1 []) (ss_mem ss_E2) a).
{ intros a (r & Hr & Ha). cbv [ss_E2 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
clear HF HG. rename HFr into HFr2.
set (regs2 := ms_regs ms0) in *. set (mem2 := ms_mem ms0) in *.
(* ---- E3: the shadow base's load, mv s5, a0, the flag test (not taken: a2 = 1), the frame call's a0 ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kcell2 & _ & _ & _).
rewrite (pal_cell (PI := PA) B PAL) in Kcell2.
destruct (crt102e_E3_entry regs2 mem2 W ltac:(rewrite (Y 11%bv) by (cbv; tauto); exact X11) Q12 Kcell2) as [HS3 SHOK3].
clear HS2 SHOK2.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] => change (BASE + k) with (BASE + (CRT_PC_A + CRT_SHB_LD)) end.
assert (HEI3 : img_env VAL A_LIM (TE regs regs2 [w64 SHADOW_OFF])) by apply te_env.
paj_run_tok_x_inv RUN HS3 HJ SHOK3 HPM (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS3.
pose proof HJ as (HAR3 & _ & _ & _ & _ & HFR3 & _).
assert (Y3 : forall (r : bv 5), In r [2; 3; 4; 8; 9]%bv -> getr (ms_regs ms1) r = getr regs2 r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crtkeep HS3 |]). destruct Hr. }
assert (Z21 : getr (ms_regs ms1) 21 = getr regs2 10) by crtkeep HS3.
prreg HS3 (26%bv : bv 5) Z26. prreg HS3 (1%bv : bv 5) Z1.
assert (Hnowr3 : forall a, ~ in_wrange (TE regs regs2 [w64 SHADOW_OFF]) (ss_mem ss_E3) a).
{ intros a (r & Hr & Ha). cbv [ss_E3 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
rename HFr into HFr3.
(* E2 and E3 wrote nothing *)
assert (K23 : forall a, aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem1 a).
{ intros a. apply aview_eq_of. rewrite HFr3 by apply Hnowr3. rewrite HFr2 by apply Hnowr2. reflexivity. }
assert (R2' : getr (ms_regs ms1) 2 = w64 sp1)
  by (rewrite (Y3 2%bv) by (cbv; tauto); unfold regs2; rewrite (Y 2%bv) by (cbv; tauto); exact X2).
assert (Hsp1 : spZ (ms_regs ms1) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite R2'. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* ---- the frame call: YGcallMxmn.aj_stack_malloc_at_xm, class 3. Its capacity premise is Crt102Img.crt102_cap from
   the text's frames bound (HFRM); its SMX is YGcallScf.stack_malloc_x_any ---- *)
rewrite pal_stack_malloc3.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm (SK := SK) SEGS B PST ARx LAWS Hsegs (pal_env (PI := PA) B PAL) OWNLOW
    (YGcallScf.stack_malloc_x_any SEGS ARx) 3 ASM3 ltac:(lia)
    W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - sp0) (getr (ms_regs ms1) 1) HJ Hsp1).
  - clear - Hal16 Hs1b. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hs1b; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hs1b as [q3 Hq3]. apply Z.mod_divide; [lia|]. exists (2 * q3 - q1). lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (Y3 3%bv) by (cbv; tauto). unfold regs2. rewrite (Y 3%bv) by (cbv; tauto). rewrite X3. exact Hgp.
  - rewrite (Y3 4%bv) by (cbv; tauto). unfold regs2. rewrite (Y 4%bv) by (cbv; tauto). rewrite X4. exact Htp.
  - reflexivity.
  - rewrite Z1. apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite HFR3. cbn [app]. exact (crt102_cap S HFRM). }
intros W2 c2 _ (-> & S2 & rgB & memB & mdB & pos & -> & HJ2 & HprB & H10B & EabB & HfrsB & HfreshB & _ & _ & _ &
  HflB & HfpB & HkB & _ & (fB & ES2) & HmnB).
destruct HkB as (KB1 & KB2 & KB3 & _).
assert (PB : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr rgB r = getr (ms_regs ms1) r)
  by (intros r Hr; exact (ts_ap _ _ r HprB Hr)).
assert (Era : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_P_OFF)))
  by (rewrite Z1; f_equal; vm_compute; reflexivity).
rewrite Era. apply SRr_ret. cbv beta.
pose proof (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) RZW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
  STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly S2 Hp W memB mdB 0 [] HJ2) as HJ2R.
apply (crt102e_at_P S2 memB mdB _ pos rgB HJ2R (ex_intro _ fB ES2)).
- intros a Ha. pose proof (pst_in_img_A a Ha) as Hi. destruct (pal_pst_static a Ha) as [Hno Her].
  rewrite (KB3 a Hi Hno Her), K23. apply KE1; [pose proof (Hsegs a Hi); unfold kLowMemEnd in *; lia|].
  pose proof (Hsegs a Hi). unfold kLowMemEnd in *. lia.
- intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi.
  rewrite (KB1 (sp0 - 8 * (Z.of_nat j + 1) + Z.of_nat i) ltac:(lia) ltac:(unfold ESTACK; lia)). apply K23.
- exact HflB.
- intros H0. exact (HmnB (HPM H0)).
- rewrite (PB 2%bv ltac:(crt_cs)). exact R2'.
- rewrite (PB 3%bv ltac:(crt_cs)), (Y3 3%bv) by (cbv; tauto). unfold regs2. rewrite (Y 3%bv) by (cbv; tauto). exact X3.
- rewrite (PB 4%bv ltac:(crt_cs)), (Y3 4%bv) by (cbv; tauto). unfold regs2. rewrite (Y 4%bv) by (cbv; tauto). exact X4.
- rewrite (PB 8%bv ltac:(crt_cs)), (Y3 8%bv) by (cbv; tauto). unfold regs2. rewrite (Y 8%bv) by (cbv; tauto). rewrite X8.
  unfold w64, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
- rewrite (PB 9%bv ltac:(crt_cs)), (Y3 9%bv) by (cbv; tauto). unfold regs2. rewrite (Y 9%bv) by (cbv; tauto). exact X9.
- exact H10B.
- rewrite (PB 21%bv ltac:(crt_cs)), Z21. unfold regs2. rewrite (Y 10%bv) by (cbv; tauto). exact X10.
- rewrite (PB 26%bv ltac:(crt_cs)), Z26. exact (te_more_lt regs regs2 [w64 SHADOW_OFF] 0 ltac:(lia)).
- exact HK.
Qed.

End g.

(* ---- THE DELIVERABLE: tcheck_round_trip_specX's premises this segment reads (as Crt102Glue's Section context binds
   them), the continuation at M, the entry's SRr. The continuation is the walk's accepted shape: the float state
   fxk the segment reaches with frm_zero / fregs_kept_x (here the Section's fx itself: both calls are ecall rows
   whose post is cfg_at at fx), crt_live with Dx = [] and the entry's ledger with own = 0, s5 = doc, copy the zero
   tree, and the room position crt_pos Sc (round_trip rp_sm t) with nothing done (for the r = 0 path's boundaries).
   The text's run-events premise sits where the text puts it (after the ledger). ---- *)
Theorem crt102_entry :
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk)
    (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt ran most : Z),
  fpre (PA := PA) B ARx STKC ly S Hp W regs mem md ch ->
  getr regs 10 = w64 doc ->
  ck_tree_ok (PA := PA) ly S Lam W mem doc t D ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> ck_frm0 (fx := fx) ->
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  (forall fxk lyc Sc Hpc Wc memc mdc kj pos rg,
     frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
     crt_live (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B)
       (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t)
       (D := D) (Lam := Lam) (peak := peak) (most := most)
       0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
     crt_dregs (regs := regs) (doc := doc) rg (frame_addr lyc CRT_CID pos) ->
     crt_copy_zero (rc := rc) (L := A_prog_listing) (PA := PA) Wc memc (frame_addr lyc CRT_CID pos) ->
     crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t)
       Sc (PresetReqAt.round_trip rp_sm t) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A) fxk CRT_M_OFF rg memc mdc)
       (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA)
          (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
          (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t)
          (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most))) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_check_round_trip) regs mem md)
    (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA)
      (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
      (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t)
      (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D Lam peak cnt ran most
  HPRE H10 HTREE HLED HRUN HFRM HROOM HIFC HFRM0 HSM HCONS HK.
exact (crt102e_top rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D Lam peak cnt ran most
  HPRE H10 HTREE HLED HRUN HFRM HROOM HIFC HFRM0 HSM HCONS HK).
Qed.
End f.
End w.
