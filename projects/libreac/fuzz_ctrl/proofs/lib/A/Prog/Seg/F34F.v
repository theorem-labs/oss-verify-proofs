(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1114 of its 1252 lines of code are new or changed and 873 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F34.v; 405 of its 663 lines of code are new or changed and 994 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F34.v 0fc96b3fa139 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f34_evt_of_F re-derives F34.f34_evt at ExecF.RNG_all; f34_evt_of_F_verbatim checks by constr_eq that its
   type is the type of F34.f34_evt, apart from the first premise, which names declaration_of_contract_F in place of
   declaration_of_contract -- both first premises are checked by name too. Mechanical re-run, route (a) (lead
   22:15Z); input to the ported walk only.
   REFIT 2026-10-29 (two Theorem Labs lanes 03:59Z / 04:03Z): (1) f34_evt_F's premise `AsanRTInv.RT spv m md0` is replaced by
   exactly what the proof uses, `asan_cells m` and `shadow_rw m` (the cut's ctl_rt conjuncts), with asan_cells carried
   across the four shadow stores by AsanRTFacts.asan_cells_kept (the stores hit [S + 8, S + 12), apart from
   [RT_LO, RT_HI)); the unused md0 binder goes.  (2) It fits a Theorem Labs lane's declaration_of_contract_F of the GLUE
   BASE (lib/A/Prog/declaration_of_c.v blob c8fd1bdb678: RNG first, plus rng_bytes RNG, rng RNG IMG_LO
   (IMG_HI - IMG_LO) and sh_word_rng RNG (sp - K) K), passed through as three new premises; a working branch's own tree still
   carries the older text (blob 1fe931c1c79), on which this file does not build.  f34_evt_of_F still states
   F34.f34_evt's exact type: it takes RT and gives f34_evt_F its first two conjuncts, and discharges the footprint
   at RNG_all; the pin below is unchanged. *)
(* The footprint (ExecF.evtF) twin of the instruction run of segment F34 of fuzz_ctrl LLVMFuzzerTestOneInput (asan
   build of the patched image A, libreac v1.9.0): 0x8286c-0x82884, the row loop head and the call of declaration_of,
   for the cut-free twin SegCF/F34.v (not in this delivery; RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   f34_evt_F is Seg/F34.v's f34_evt with the run an evtF under a footprint RNG and one `rng RNG <addr> <len>` premise
   per region the run reads or writes; the premises stay premises (the cut-free consumer discharges them at its own
   footprint).  The accesses, on the v1.9 pcs:
   - the four shadow stores 0x8286c .. 0x82878 `sb zero,8(s3)` .. `sb zero,11(s3)`: S + 8 .. S + 11, so
     `rng RNG (S + 8) 4`;
   - the two moves 0x8287c / 0x82880 and the call 0x82884 touch no memory;
   - declaration_of's own accesses, which its footprint contract declaration_of_c.v declaration_of_contract_F names:
     the image [IMG_LO, IMG_HI), its window [sp - K, sp) (K = DECLARATION_OF_K = 2304) and that window's 8-aligned
     shadow word span, the runtime words [RT_LO, RT_HI), the 296 row bytes at r and the 32 slot bytes at o, and the
     8-aligned shadow words that cover each of the two ranges; plus the contract's rng_bytes RNG (the footprint is
     decided byte by byte).
   As in Seg/F34.v, the call runs on the normalized memory (declaration_of's contract asks for mem_inv, which no cut
   carries); the lift is lib/A/MemNormF.v evtF_normalize_ro, the evtF form of MemNorm.evt_normalize, which keeps the
   footprint RNG.  f34_evt_of_F re-derives Seg/F34.v's Exec.evt statement from f34_evt_F at RNG_all (ExecF.evtF_evt,
   every footprint premise at RNG_all).  Seg/F34.v is unchanged apart from comment text and does not use it; it shows that the footprint form loses
   nothing.

   rule 24: no function proved.  F34 calls declaration_of at 0x82884: f34_evt_F takes its footprint contract as the
   Section Hypothesis DECLF, as Seg/F34.v takes the halts contract as DECL.  declaration_ofF.v declaration_of_F_holds
   proves it (Qed) from the footprint contracts of __asan_memset and __asan_memcpy (declaration_ofF.v
   asan_memset_contract_F / asan_memcpy_contract_F), which this tree does not prove; SegCF/F34.v passes
   declaration_of_F_holds and carries those two as its Section Hypotheses.

   The proof is Seg/F34.v's f34_evt proof, with its text, over StepF's step: the match patterns name evtF in place of
   Exec.evt, evt_cut / evt_done / evt_normalize are evtF_cut / evtF_done / MemNormF.evtF_normalize_ro, and the nine
   footprint premises of declaration_of_contract_F are the nine new ones above.  Seg/F34.v's pure helpers (f34_addr_keep,
   f34_addr_app, ...) are used from Seg/F34.v itself (imported). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcFragLib
  RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require declaration_of_c declaration_of.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 F34.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* The three footprint premises a Theorem Labs lane's declaration_of_contract_F adds (declaration_of_c.v at the glue base, blob
   c8fd1bdb678): rng_bytes (lib/Lib/RngBytes.v), the image [IMG_LO, IMG_HI) (lib/A/Prog/ImgBounds.v) and the
   8-aligned shadow word span of the window (lib/A/Prog/rng_asan.v sh_word_rng).  Required qualified, named by full
   path (image B has its own ImgBounds / rng_asan). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
(* Last (as in Seg/F38F.v and Seg/F32F.v): StepF's step / if_cases and ExecF's evtF_done match evtF goals and shadow
   Step's evt ones. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Seg/F34.v's run is stated with the image-A YK11 (its alias AYK); import it again here. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top (as in Seg/F31F.v). *)
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module SRw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SRwT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.

(* ===================== the run, over the callee's footprint contract ===================== *)

Section F34F.
(* declaration_of's footprint contract (declaration_of_c.v), proved by declaration_ofF.v declaration_of_F_holds from
   the two ASan runtime footprint contracts; SegCF/F34.v passes that theorem. *)
Hypothesis DECLF : DECLc.declaration_of_contract_F.

(* 0x8286c -> 0x82888: the four shadow stores at S + 8 .. S + 11 (so that [o, o + 32) is addressable), then
   declaration_of(r, o) by its footprint contract, on normalize m1 (Seg/F34.v's f34_evt, with its text). *)
Lemma f34_evt_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S r o spv lo : Z) (row ob : list byte),
    x2 = Z_to_bv 64 spv -> x19 = Z_to_bv 64 S -> x20 = Z_to_bv 64 r -> x25 = Z_to_bv 64 o ->
    2148236288 <= S -> S + 12 <= 2 ^ 64 ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= o -> o + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (o + k)) -> app_mem (o + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (o + k) < S + 12) ->
    rw_cells rsegs m o [CB 32 ob] -> length ob = 32%nat ->
    0 <= r -> r + 296 <= 652472 -> r mod 8 = 0 -> length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m r row -> addressable m r 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2304 <= spv -> spv <= APPMEM_END ->
    (o + 32 <= spv - 2304 \/ spv <= o) -> RT_HI <= o -> 6283264 <= o ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    (* the four shadow stores 0x8286c .. 0x82878 `sb zero,8(s3)` .. `sb zero,11(s3)` *)
    rng RNG (S + 8) 4 ->
    (* declaration_of's footprint (declaration_of_contract_F, in its order): the footprint is decided byte by byte,
       the image, its window K below sp and the aligned shadow words that cover it, the runtime words, the row and
       the aligned shadow words that cover it, the slot and the aligned shadow words that cover it *)
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.rng_bytes RNG ->
    rng RNG OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_HI
       - OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO) ->
    rng RNG (spv - DECLc.DECLARATION_OF_K) DECLc.DECLARATION_OF_K ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.sh_word_rng RNG
      (spv - DECLc.DECLARATION_OF_K) DECLc.DECLARATION_OF_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG r 296 ->
    rng RNG ((r / 8 + ASAN_K) / 8 * 8) (((r + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (r / 8 + ASAN_K) / 8 * 8) ->
    rng RNG o 32 ->
    rng RNG ((o / 8 + ASAN_K) / 8 * 8) (((o + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (o / 8 + ASAN_K) / 8 * 8) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82888) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       x18 (Z_to_bv 64 S) (Z_to_bv 64 r) x21 x22 x23 x24 (Z_to_bv 64 o) x26 x27 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82888) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' o (decl row) /\ addressable m' o 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S r o spv lo row ob
    E2 E19 E20 E25 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    Hr0 Hr1 Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HoGT HRO HAC HSW
    RGsh RGby RGimg RGwin RGws RGrt RGrow RGrows RGo RGos.
  subst x2 x19 x20 x25.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ESLOT : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (ERTH : RT_HI = 693624) by reflexivity.
  assert (ERTL : RT_LO = 654032) by reflexivity.
  assert (EDK : DECLc.DECLARATION_OF_K = 2304) by reflexivity.
  assert (EK : ASAN_K = 2147450880) by reflexivity.
  (* --- the four stores --- *)
  assert (HSok : forall (m' : word -> option byte) k, wmono rsegs m m' -> 0 <= k < 4 ->
            store_ok rsegs m' (wa (S + 8 + k)) 1 = true).
  { intros m' k Hw Hk.
    assert (WR : wr_at rsegs m' (S + 8 + k) 1).
    { split; [lia|]. split; [lia|]. intros kk Hkk. assert (Ei : kk = 0) by lia. subst kk.
      rewrite Z.add_0_r. apply Hw. apply HWv. lia. }
    pose proof (wr_at_store_ok rsegs m' (S + 8 + k) 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HSS.
    rewrite Z.add_0_r in HSS. exact HSS. }
  assert (H8 : store_ok rsegs m (wa (S + 8)) 1 = true).
  { replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia]. }
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H9 : store_ok rsegs mm (wa (S + 9)) 1 = true)
        by (replace (S + 9) with (S + 8 + 1) by lia; apply (HSok mm 1);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H10 : store_ok rsegs mm (wa (S + 10)) 1 = true)
        by (replace (S + 10) with (S + 8 + 2) by lia; apply (HSok mm 2);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H11 : store_ok rsegs mm (wa (S + 11)) 1 = true)
        by (replace (S + 11) with (S + 8 + 3) by lia; apply (HSok mm 3);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step. step. step. step.
  (* --- the post-store memory --- *)
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Em1 : mm = write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                       (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0])
        by (repeat f_equal; try reflexivity; vm_compute; reflexivity);
      rewrite Em1; clear Em1
  end.
  set (m1 := write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                 (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(S + 8, S + 12)] m m1).
  { unfold m1. apply munch_write; [apply munch_write; [apply munch_write; [apply munch_write;
      [apply munch_refl | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]. }
  assert (WM1 : wmono rsegs m m1)
    by (unfold m1; apply wmono_write, wmono_write, wmono_write, wmono_write, wmono_refl).
  (* ro_agree survives the stores: they write shadow bytes, at no read-only address *)
  assert (RO1 : ro_agree rsegs m1).
  { apply (RA.ro_agree_munch [(S + 8, S + 12)] m m1 HRO MU1).
    intros x Hx. apply RA.ro_addr_false_w.
    destruct (Z_lt_le_dec (bv_unsigned x) (S + 8)) as [L|L]; [|lia].
    exfalso. apply Hx. cbn [outside]. split; [lia | exact I]. }
  assert (Hb8 : forall k, 0 <= k < 4 -> bytes_at rsegs m1 (S + 8 + k) [Z_to_bv 8 0]).
  { intros k Hk. unfold m1.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct Hk' as [ -> | [ -> | [ -> | -> ]]].
    - rewrite Z.add_0_r.
      apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 1) with (S + 9) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 2) with (S + 10) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_same | | |]; cbn [length]; lia.
    - replace (S + 8 + 3) with (S + 11) by lia. apply bytes_at_write_same; cbn [length]; lia. }
  assert (Hkeep : forall a bs, bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= S + 8 \/ S + 12 <= a) ->
                    bytes_at rsegs m1 a bs).
  { intros a bs Hb Hd. eapply fl_bytes; [exact Hb | exact MU1 |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (Hsh1 : forall a, in_shadow a -> exists b, mrd rsegs m1 (wa a) = Some b).
  { intros a Ha.
    destruct (Z_le_dec (S + 8) a) as [Hl|Hl]; destruct (Z_lt_dec a (S + 12)) as [Hh|Hh].
    - destruct (Hb8 (a - S - 8) ltac:(lia)) as (_ & _ & Hb).
      replace (S + 8 + (a - S - 8)) with a in Hb by lia.
      pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
      rewrite Z.add_0_r in Hb0. exists (Z_to_bv 8 0). exact Hb0.
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I].
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I].
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I]. }
  assert (HSW1 : shadow_rw m1)
    by (intros a Ha; split; [apply WM1; exact (proj1 (HSW a Ha)) | exact (Hsh1 a Ha)]).
  (* asan_cells across the four stores: they write shadow bytes [S + 8, S + 12), apart from the runtime's cells
     [RT_LO, RT_HI) (S >= 2148236288 > RT_HI). *)
  assert (HAC1 : asan_cells m1).
  { apply (AsanRTFacts.asan_cells_kept [(S + 8, S + 12)] m m1 HAC MU1).
    cbn [disjoint_from]. split; [left; lia | exact I]. }
  assert (Hrow1 : bytes_at rsegs m1 r row) by (apply Hkeep; [exact Hrow | rewrite Hrlen; lia]).
  assert (Hob1 : rw_cells rsegs m1 o [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf|]. eapply fl_bytes; [exact Hbb | exact MU1 |].
      intros x Hx. cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hoblen in Hx.
      cbn [outside]. split; [|exact I]. intros Hc.
      apply (app_not_shadow x).
      + replace x with (o + (x - o)) by lia. apply Hoapp. cbn [Z.of_nat] in Hx. lia.
      + replace x with (S + 8 + (x - S - 8)) by lia. apply HSin. lia.
    - unfold m1. apply wr_at_write, wr_at_write, wr_at_write, wr_at_write. exact Hw. }
  assert (Hstk1 : stk rsegs m1 lo spv).
  { unfold m1. apply stk_write; [apply stk_write; [apply stk_write; [apply stk_write;
      [exact HST | lia | cbn [length]; lia] | lia | cbn [length]; lia] | lia | cbn [length]; lia]
      | lia | cbn [length]; lia]. }
  assert (Haddr1 : addressable m1 o 32).
  { split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. split; [apply Hoapp; lia|].
    exists (Z_to_bv 8 0). split; [|unfold shadow_ok; left; reflexivity].
    destruct (Hb8 (shadow_addr (o + k) - S - 8) ltac:(pose proof (Hosh k Hk); lia)) as (_ & _ & Hb).
    replace (S + 8 + (shadow_addr (o + k) - S - 8)) with (shadow_addr (o + k)) in Hb
      by (pose proof (Hosh k Hk); lia).
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  assert (Haddrrow1 : addressable m1 r 296).
  { apply (f34_addr_keep m m1 r 296 Hraddr). intros a Ha. unfold mrd.
    rewrite (MU1 (wa (shadow_addr a))); [reflexivity|].
    assert (Happa : app_mem a) by (pose proof (f34_addr_app m r 296 (a - r) Hraddr ltac:(lia)) as Hp;
      replace (r + (a - r)) with a in Hp by lia; exact Hp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ (shadow_of_app a Happa)); lia).
    cbn [outside]. split; [|exact I]. intros Hc.
    unfold shadow_addr, ASAN_K in *. revert Ha Hc Hr0 Hr1 HSlo. Z.div_mod_to_equations. lia. }
  (* --- declaration_of, on the normalized memory (its contract asks for mem_inv) --- *)
  pose proof (mem_rel_normalize rsegs m1 RO1) as REL1.
  pose proof DECLF as HD. unfold DECLc.declaration_of_contract_F in HD. cbv zeta in HD.
  eapply evtF_cut.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fcs None m1 (seg_rom rsegs) RO1).
    eapply HD with (lo := lo) (row := row) (ob := ob).
    all: rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit r),
      ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit o),
      ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
    - apply (RA.rel_stk_norm m1 (normalize rsegs m1) lo spv REL1); [|exact Hstk1].
      intros x Hx. apply RA.ro_addr_false_hi. lia.
    - unfold DECLc.DECLARATION_OF_K. lia.
    - exact Hr8.
    - exact Hrlen.
    - exact (bytes_at_normalize rsegs m1 r row RO1 Hrow1).
    - apply (RA.rel_rw_norm m1 (normalize rsegs m1) o [CB 32 ob] REL1); [|exact Hob1].
      intros i Hi. cbn [cells_size csize] in Hi. apply RA.ro_addr_false_hi. lia.
    - right. unfold RT_HI in HoRT. lia.
    - left. unfold DECLc.DECLARATION_OF_K. lia.
    - unfold DECLc.DECLARATION_OF_K. destruct Hodj as [HDj|HDj]; [left; lia | right; lia].
    - exact (mem_inv_normalize rsegs m1).
    - exact (RA.rel_ac_norm m1 _ REL1 HAC1).
    - exact (RA.rel_sw_norm m1 _ REL1 HSW1).
    - exact Hlo1.
    - exact Hsp1.
    - exact (RA.rel_addr_norm m1 _ r 296 REL1 Haddrrow1).
    - exact (RA.rel_addr_norm m1 _ o 32 REL1 Haddr1).
    - exact Hoend.
    - right. exact HoRT.
    - exact RGby.
    - exact RGimg.
    - exact RGwin.
    - exact RGws.
    - exact RGrt.
    - exact RGrow.
    - exact RGrows.
    - exact RGo.
    - exact RGos. }
  intros ms2 (s0 & Hpost & REL2 & SAME2).
  unfold DECLc.declaration_of_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 &
                     E0 & MU0 & WM0 & MI0 & ST0 & RW0 & BA0 & AC0 & SW0).
  subst s0.
  destruct ms2 as [rg2 fg2 pc2 sv2 rv2 fc2 m2 ro2].
  destruct REL2 as (Er2 & Ef2 & Epc2 & Esv2 & Erv2 & Efc2 & Ero2 & REL2).
  unfold MS in Er2, Ef2, Epc2, Esv2, Erv2, Efc2, Ero2, REL2.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]
    in Er2, Ef2, Epc2, Esv2, Erv2, Efc2, Ero2, REL2, SAME2.
  subst rg2 fg2 pc2 sv2 rv2 fc2 ro2.
  (* the post, brought back from the normalized memory m0 to the real one m2 *)
  pose proof (munch_rel rsegs _ m1 (normalize rsegs m1) m2 m0 REL1 REL2 SAME2 MU0) as MU2.
  pose proof (wmono_rel rsegs m1 (normalize rsegs m1) m2 m0 REL1 REL2 SAME2 WM0) as WM2.
  pose proof (ro_agree_same rsegs m1 m2 RO1 SAME2) as RO2.
  pose proof (RA.rel_stk_back m2 m0 _ _ REL2 ST0) as ST2.
  pose proof (RA.rel_rw_back m2 m0 _ _ REL2 RW0) as RW2.
  pose proof (RA.rel_sw_back m2 m0 REL2 SW0) as SW2.
  clear MU0 WM0 MI0 ST0 RW0 BA0 AC0 SW0.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit o) in MU2, RW2 by lia.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in MU2, ST2 by lia.
  rewrite Hok in RW2.
  replace (ret_pc (Z_to_bv 64 0x82888)) with (Z_to_bv 64 0x82888)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  rewrite Hok.
  (* --- the combined write set --- *)
  assert (MUa : munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m2).
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x (Hx & _). cbn [outside]. split; [exact Hx | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x (_ & Hx1 & Hx2 & _). cbn [outside].
      split; [exact Hx1|]. split; [exact Hx2 | exact I]. }
  assert (WMa : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [cells_bytes cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  assert (HINa : forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m2 (wa q) = Some b).
  { intros q Hq Hno.
    assert (Hslot : o <= q < o + 32 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. destruct Hdbb as (_ & _ & Hb).
      pose proof (Hb (Z.to_nat (q - o)) ltac:(rewrite Hdlen; lia)) as Hb0.
      replace (o + Z.of_nat (Z.to_nat (q - o))) with q in Hb0 by lia.
      destruct (nth_error (decl row) (Z.to_nat (q - o))) as [b|] eqn:En;
        [exists b; exact Hb0 | apply nth_error_None in En; rewrite Hdlen in En; lia]. }
    assert (Hshq : S + 8 <= q < S + 12 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (SW2 q ltac:(replace q with (S + 8 + (q - S - 8)) by lia; apply HSin; lia))). }
    assert (Hwinq : spv - 2304 <= q < spv -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (proj2 (proj2 ST2) q ltac:(unfold AF.SLOT_STACK in *; lia))). }
    destruct (Z_le_dec (S + 8) q) as [L1|L1]; destruct (Z_lt_dec q (S + 12)) as [L2|L2];
    destruct (Z_le_dec (spv - 2304) q) as [L3|L3]; destruct (Z_lt_dec q spv) as [L4|L4];
    destruct (Z_le_dec o q) as [L5|L5]; destruct (Z_lt_dec q (o + 32)) as [L6|L6];
    first [ apply Hshq; lia | apply Hwinq; lia | apply Hslot; lia
          | exfalso; apply Hno; cbn [outside]; repeat split; try exact I; lia ]. }
  assert (Haddr2 : addressable m2 o 32).
  { apply (f34_addr_keep m1 m2 o 32 Haddr1). intros a Ha. unfold mrd.
    rewrite (MU2 (wa (shadow_addr a))); [reflexivity|].
    assert (Hin : S + 8 <= shadow_addr a < S + 12) by (pose proof (Hosh (a - o) ltac:(lia)) as Hp;
      replace (o + (a - o)) with a in Hp by lia; exact Hp).
    assert (Happa : app_mem a) by (replace a with (o + (a - o)) by lia; apply Hoapp; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|exact I]].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      replace (shadow_addr a) with (o + (shadow_addr a - o)) by lia. apply Hoapp. lia. }
  apply evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MUa|]. split; [exact WMa|]. split; [exact RO2|]. split; [exact SW2|].
  split; [exact ST2|]. split; [exact Hdbb|]. split; [exact Haddr2 | exact HINa].
Qed.

(* Seg/F34.v's f34_evt statement, at RNG_all, under the footprint contract (with declaration_ofF.v
   declaration_of_F_holds it holds from the two ASan runtime footprint contracts).  Its RT premise gives f34_evt_F's
   asan_cells and shadow_rw (RT's first two conjuncts); every footprint premise holds at RNG_all (rng_bytes by
   RNG_all's definition, sh_word_rng by rng_asan.sh_word_rng_all, the rest by rng_all). *)
Lemma f34_evt_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S r o spv lo : Z) (row ob : list byte) (md0 : Model),
    x2 = Z_to_bv 64 spv -> x19 = Z_to_bv 64 S -> x20 = Z_to_bv 64 r -> x25 = Z_to_bv 64 o ->
    2148236288 <= S -> S + 12 <= 2 ^ 64 ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= o -> o + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (o + k)) -> app_mem (o + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (o + k) < S + 12) ->
    rw_cells rsegs m o [CB 32 ob] -> length ob = 32%nat ->
    0 <= r -> r + 296 <= 652472 -> r mod 8 = 0 -> length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m r row -> addressable m r 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2304 <= spv -> spv <= APPMEM_END ->
    (o + 32 <= spv - 2304 \/ spv <= o) -> RT_HI <= o -> 6283264 <= o ->
    ro_agree rsegs m -> AsanRTInv.RT spv m md0 ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82888) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       x18 (Z_to_bv 64 S) (Z_to_bv 64 r) x21 x22 x23 x24 (Z_to_bv 64 o) x26 x27 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82888) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' o (decl row) /\ addressable m' o 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S r o spv lo row ob md0
    E2 E19 E20 E25 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    Hr0 Hr1 Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HoGT HRO HRT.
  eapply (evtF_evt rsegs RNG_all).
  apply (f34_evt_F RNG_all x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
           x26 x27 x28 x29 x30 x31 Fr fcs m S r o spv lo row ob
           E2 E19 E20 E25 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
           Hr0 Hr1 Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HoGT HRO
           (proj1 HRT) (AsanRTInv.RT_shadow_rw _ _ _ HRT));
    first [ (intros ? ? ? ? ?; exact I)
          | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.sh_word_rng_all
          | apply rng_all ];
    unfold DECLc.DECLARATION_OF_K, RT_LO, RT_HI, ASAN_K, APPMEM_END, HIGHMEM_BEG,
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO,
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_HI in *;
    clear - HSlo HShi Ho0 Ho1 Hr0 Hr1 Hlo1 Hlo2 Hsp1; Z.div_mod_to_equations; lia.
Qed.

End F34F.

(* The pin: f34_evt_of_F states F34.f34_evt's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion), apart from the first premise, which names the _F contract in place of the plain one; both first
   premises are checked by name too. *)
Lemma f34_evt_of_F_verbatim : True.
Proof.
  lazymatch type of F34.f34_evt with ?P -> ?A =>
  lazymatch type of f34_evt_of_F with ?Q -> ?B =>
    constr_eq P OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.declaration_of_contract;
    constr_eq Q OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.declaration_of_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

(* ===================== route (C): the narrowed twin (declaration_of_contract_F_on) ===================== *)

(* Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 10:34Z amendment): the shadow bytes
   f34_evt_F's run needs present through its shadow_rw premise.  Its only use of `shadow_rw m` is to give
   declaration_of its premise on normalize m1; the callee's narrowed contract (declaration_of_c.v
   declaration_of_contract_F_on, a Theorem Labs lane 018e976802f) asks for its own region declaration_of_shadow_R a0 a1 at the
   call's arguments a0 = r (the row), a1 = o (the slot).  The four stores at S + 8 .. S + 11 need no shadow_rw: their
   store_ok comes from the wview premise, and the stored bytes are present after the stores.  So R is the callee's
   region alone. *)
Definition f34_evt_F_shadow_R (r o : Z) : Z -> Prop := DECLc.declaration_of_shadow_R r o.

(* The Section F34F above stays as it is (its lemmas take DECLc.declaration_of_contract_F, Hypothesis DECLF).
   f34_evt_F gets its twin here, under declaration_of's narrowed footprint contract, with NO AsanRTInv.RT and no
   universal shadow_rw premise.  f34_evt_of_F gets none: it re-derives F34.f34_evt, whose premise is
   AsanRTInv.RT (universal shadow_rw), and a route (C) _on lemma must not take RT (a Theorem Labs lane batch 75, 13:32Z). *)
Section F34F_on.
(* declaration_of's narrowed footprint contract (declaration_of_c.v), proved by a Theorem Labs lane's declaration_ofF.v
   declaration_of_F_holds_on_closed (a working branch 63b9129e817). *)
Hypothesis DECLF_on : DECLc.declaration_of_contract_F_on.

(* Route (C): f34_evt_F under the narrowed premise shadow_rw_on (f34_evt_F_shadow_R r o) m and the callee's _F_on
   contract.  POST: every region the caller holds on m it still holds on m' (declaration_of_post_on, moved across
   both mem_rel's by ShadowRwOnT.shadow_rw_on_rel / shadow_rw_on_of_rel).  Every other premise and conjunct is
   f34_evt_F's; the proof is f34_evt_F's with those transports. *)
Lemma f34_evt_F_on :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S r o spv lo : Z) (row ob : list byte),
    x2 = Z_to_bv 64 spv -> x19 = Z_to_bv 64 S -> x20 = Z_to_bv 64 r -> x25 = Z_to_bv 64 o ->
    2148236288 <= S -> S + 12 <= 2 ^ 64 ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= o -> o + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (o + k)) -> app_mem (o + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (o + k) < S + 12) ->
    rw_cells rsegs m o [CB 32 ob] -> length ob = 32%nat ->
    0 <= r -> r + 296 <= 652472 -> r mod 8 = 0 -> length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m r row -> addressable m r 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2304 <= spv -> spv <= APPMEM_END ->
    (o + 32 <= spv - 2304 \/ spv <= o) -> RT_HI <= o -> 6283264 <= o ->
    ro_agree rsegs m -> asan_cells m -> SRw.shadow_rw_on (f34_evt_F_shadow_R r o) m ->
    (* the four shadow stores 0x8286c .. 0x82878 `sb zero,8(s3)` .. `sb zero,11(s3)` *)
    rng RNG (S + 8) 4 ->
    (* declaration_of's footprint (declaration_of_contract_F, in its order): the footprint is decided byte by byte,
       the image, its window K below sp and the aligned shadow words that cover it, the runtime words, the row and
       the aligned shadow words that cover it, the slot and the aligned shadow words that cover it *)
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.rng_bytes RNG ->
    rng RNG OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_HI
       - OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO) ->
    rng RNG (spv - DECLc.DECLARATION_OF_K) DECLc.DECLARATION_OF_K ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.sh_word_rng RNG
      (spv - DECLc.DECLARATION_OF_K) DECLc.DECLARATION_OF_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG r 296 ->
    rng RNG ((r / 8 + ASAN_K) / 8 * 8) (((r + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (r / 8 + ASAN_K) / 8 * 8) ->
    rng RNG o 32 ->
    rng RNG ((o / 8 + ASAN_K) / 8 * 8) (((o + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (o / 8 + ASAN_K) / 8 * 8) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82888) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       x18 (Z_to_bv 64 S) (Z_to_bv 64 r) x21 x22 x23 x24 (Z_to_bv 64 o) x26 x27 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82888) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ (forall P, SRw.shadow_rw_on P m -> SRw.shadow_rw_on P m') /\
         stk rsegs m' lo spv /\
         bytes_at rsegs m' o (decl row) /\ addressable m' o 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S r o spv lo row ob
    E2 E19 E20 E25 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    Hr0 Hr1 Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HoGT HRO HAC HSWR
    RGsh RGby RGimg RGwin RGws RGrt RGrow RGrows RGo RGos.
  subst x2 x19 x20 x25.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ESLOT : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (ERTH : RT_HI = 693624) by reflexivity.
  assert (ERTL : RT_LO = 654032) by reflexivity.
  assert (EDK : DECLc.DECLARATION_OF_K = 2304) by reflexivity.
  assert (EK : ASAN_K = 2147450880) by reflexivity.
  (* --- the four stores --- *)
  assert (HSok : forall (m' : word -> option byte) k, wmono rsegs m m' -> 0 <= k < 4 ->
            store_ok rsegs m' (wa (S + 8 + k)) 1 = true).
  { intros m' k Hw Hk.
    assert (WR : wr_at rsegs m' (S + 8 + k) 1).
    { split; [lia|]. split; [lia|]. intros kk Hkk. assert (Ei : kk = 0) by lia. subst kk.
      rewrite Z.add_0_r. apply Hw. apply HWv. lia. }
    pose proof (wr_at_store_ok rsegs m' (S + 8 + k) 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HSS.
    rewrite Z.add_0_r in HSS. exact HSS. }
  assert (H8 : store_ok rsegs m (wa (S + 8)) 1 = true).
  { replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia]. }
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H9 : store_ok rsegs mm (wa (S + 9)) 1 = true)
        by (replace (S + 9) with (S + 8 + 1) by lia; apply (HSok mm 1);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H10 : store_ok rsegs mm (wa (S + 10)) 1 = true)
        by (replace (S + 10) with (S + 8 + 2) by lia; apply (HSok mm 2);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H11 : store_ok rsegs mm (wa (S + 11)) 1 = true)
        by (replace (S + 11) with (S + 8 + 3) by lia; apply (HSok mm 3);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step. step. step. step.
  (* --- the post-store memory --- *)
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Em1 : mm = write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                       (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0])
        by (repeat f_equal; try reflexivity; vm_compute; reflexivity);
      rewrite Em1; clear Em1
  end.
  set (m1 := write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                 (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(S + 8, S + 12)] m m1).
  { unfold m1. apply munch_write; [apply munch_write; [apply munch_write; [apply munch_write;
      [apply munch_refl | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]. }
  assert (WM1 : wmono rsegs m m1)
    by (unfold m1; apply wmono_write, wmono_write, wmono_write, wmono_write, wmono_refl).
  (* ro_agree survives the stores: they write shadow bytes, at no read-only address *)
  assert (RO1 : ro_agree rsegs m1).
  { apply (RA.ro_agree_munch [(S + 8, S + 12)] m m1 HRO MU1).
    intros x Hx. apply RA.ro_addr_false_w.
    destruct (Z_lt_le_dec (bv_unsigned x) (S + 8)) as [L|L]; [|lia].
    exfalso. apply Hx. cbn [outside]. split; [lia | exact I]. }
  assert (Hb8 : forall k, 0 <= k < 4 -> bytes_at rsegs m1 (S + 8 + k) [Z_to_bv 8 0]).
  { intros k Hk. unfold m1.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct Hk' as [ -> | [ -> | [ -> | -> ]]].
    - rewrite Z.add_0_r.
      apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 1) with (S + 9) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 2) with (S + 10) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_same | | |]; cbn [length]; lia.
    - replace (S + 8 + 3) with (S + 11) by lia. apply bytes_at_write_same; cbn [length]; lia. }
  assert (Hkeep : forall a bs, bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= S + 8 \/ S + 12 <= a) ->
                    bytes_at rsegs m1 a bs).
  { intros a bs Hb Hd. eapply fl_bytes; [exact Hb | exact MU1 |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  (* Route (C): the four stored bytes S + 8 .. S + 11 are a region of m1 (writable by the wview premise and wmono,
     present by the stores), and every region of m is a region of m1 (the other bytes are kept, MU1). *)
  assert (HS4m1 : SRw.shadow_rw_on (fun a => S + 8 <= a < S + 12) m1).
  { intros a Hin Ha. cbv beta in Hin. split.
    - apply WM1. replace a with (S + 8 + (a - S - 8)) by lia. apply HWv. lia.
    - destruct (Hb8 (a - S - 8) ltac:(lia)) as (_ & _ & Hb).
      replace (S + 8 + (a - S - 8)) with a in Hb by lia.
      pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
      rewrite Z.add_0_r in Hb0. exists (Z_to_bv 8 0). exact Hb0. }
  assert (KEEP1 : forall P, SRw.shadow_rw_on P m -> SRw.shadow_rw_on P m1).
  { intros P HP a Hp Ha.
    destruct (Z_le_dec (S + 8) a) as [Hl|Hl]; [destruct (Z_lt_dec a (S + 12)) as [Hh|Hh]|];
      [exact (HS4m1 a (conj Hl Hh) Ha) | |];
      (destruct (HP a Hp Ha) as (Hw & b & Hb); split; [apply WM1; exact Hw|];
       exists b; unfold mrd in *; rewrite (MU1 (wa a)); [exact Hb|];
       rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia); cbn [outside]; split; [lia | exact I]). }
  (* asan_cells across the four stores: they write shadow bytes [S + 8, S + 12), apart from the runtime's cells
     [RT_LO, RT_HI) (S >= 2148236288 > RT_HI). *)
  assert (HAC1 : asan_cells m1).
  { apply (AsanRTFacts.asan_cells_kept [(S + 8, S + 12)] m m1 HAC MU1).
    cbn [disjoint_from]. split; [left; lia | exact I]. }
  assert (Hrow1 : bytes_at rsegs m1 r row) by (apply Hkeep; [exact Hrow | rewrite Hrlen; lia]).
  assert (Hob1 : rw_cells rsegs m1 o [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf|]. eapply fl_bytes; [exact Hbb | exact MU1 |].
      intros x Hx. cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hoblen in Hx.
      cbn [outside]. split; [|exact I]. intros Hc.
      apply (app_not_shadow x).
      + replace x with (o + (x - o)) by lia. apply Hoapp. cbn [Z.of_nat] in Hx. lia.
      + replace x with (S + 8 + (x - S - 8)) by lia. apply HSin. lia.
    - unfold m1. apply wr_at_write, wr_at_write, wr_at_write, wr_at_write. exact Hw. }
  assert (Hstk1 : stk rsegs m1 lo spv).
  { unfold m1. apply stk_write; [apply stk_write; [apply stk_write; [apply stk_write;
      [exact HST | lia | cbn [length]; lia] | lia | cbn [length]; lia] | lia | cbn [length]; lia]
      | lia | cbn [length]; lia]. }
  assert (Haddr1 : addressable m1 o 32).
  { split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. split; [apply Hoapp; lia|].
    exists (Z_to_bv 8 0). split; [|unfold shadow_ok; left; reflexivity].
    destruct (Hb8 (shadow_addr (o + k) - S - 8) ltac:(pose proof (Hosh k Hk); lia)) as (_ & _ & Hb).
    replace (S + 8 + (shadow_addr (o + k) - S - 8)) with (shadow_addr (o + k)) in Hb
      by (pose proof (Hosh k Hk); lia).
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  assert (Haddrrow1 : addressable m1 r 296).
  { apply (f34_addr_keep m m1 r 296 Hraddr). intros a Ha. unfold mrd.
    rewrite (MU1 (wa (shadow_addr a))); [reflexivity|].
    assert (Happa : app_mem a) by (pose proof (f34_addr_app m r 296 (a - r) Hraddr ltac:(lia)) as Hp;
      replace (r + (a - r)) with a in Hp by lia; exact Hp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ (shadow_of_app a Happa)); lia).
    cbn [outside]. split; [|exact I]. intros Hc.
    unfold shadow_addr, ASAN_K in *. revert Ha Hc Hr0 Hr1 HSlo. Z.div_mod_to_equations. lia. }
  (* --- declaration_of, on the normalized memory (its contract asks for mem_inv) --- *)
  pose proof (mem_rel_normalize rsegs m1 RO1) as REL1.
  pose proof DECLF_on as HD. unfold DECLc.declaration_of_contract_F_on in HD. cbv zeta in HD.
  eapply evtF_cut.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fcs None m1 (seg_rom rsegs) RO1).
    eapply HD with (lo := lo) (row := row) (ob := ob).
    all: rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit r),
      ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit o),
      ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
    - apply (RA.rel_stk_norm m1 (normalize rsegs m1) lo spv REL1); [|exact Hstk1].
      intros x Hx. apply RA.ro_addr_false_hi. lia.
    - unfold DECLc.DECLARATION_OF_K. lia.
    - exact Hr8.
    - exact Hrlen.
    - exact (bytes_at_normalize rsegs m1 r row RO1 Hrow1).
    - apply (RA.rel_rw_norm m1 (normalize rsegs m1) o [CB 32 ob] REL1); [|exact Hob1].
      intros i Hi. cbn [cells_size csize] in Hi. apply RA.ro_addr_false_hi. lia.
    - right. unfold RT_HI in HoRT. lia.
    - left. unfold DECLc.DECLARATION_OF_K. lia.
    - unfold DECLc.DECLARATION_OF_K. destruct Hodj as [HDj|HDj]; [left; lia | right; lia].
    - exact (mem_inv_normalize rsegs m1).
    - exact (RA.rel_ac_norm m1 _ REL1 HAC1).
    - exact (SRwT.shadow_rw_on_rel _ m1 _ REL1 (KEEP1 _ HSWR)).
    - exact Hlo1.
    - exact Hsp1.
    - exact (RA.rel_addr_norm m1 _ r 296 REL1 Haddrrow1).
    - exact (RA.rel_addr_norm m1 _ o 32 REL1 Haddr1).
    - exact Hoend.
    - right. exact HoRT.
    - exact RGby.
    - exact RGimg.
    - exact RGwin.
    - exact RGws.
    - exact RGrt.
    - exact RGrow.
    - exact RGrows.
    - exact RGo.
    - exact RGos. }
  intros ms2 (s0 & Hpost & REL2 & SAME2).
  unfold DECLc.declaration_of_post_on in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 &
                     E0 & MU0 & WM0 & MI0 & ST0 & RW0 & BA0 & AC0 & SW0).
  subst s0.
  destruct ms2 as [rg2 fg2 pc2 sv2 rv2 fc2 m2 ro2].
  destruct REL2 as (Er2 & Ef2 & Epc2 & Esv2 & Erv2 & Efc2 & Ero2 & REL2).
  unfold MS in Er2, Ef2, Epc2, Esv2, Erv2, Efc2, Ero2, REL2.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]
    in Er2, Ef2, Epc2, Esv2, Erv2, Efc2, Ero2, REL2, SAME2.
  subst rg2 fg2 pc2 sv2 rv2 fc2 ro2.
  (* the post, brought back from the normalized memory m0 to the real one m2 *)
  pose proof (munch_rel rsegs _ m1 (normalize rsegs m1) m2 m0 REL1 REL2 SAME2 MU0) as MU2.
  pose proof (wmono_rel rsegs m1 (normalize rsegs m1) m2 m0 REL1 REL2 SAME2 WM0) as WM2.
  pose proof (ro_agree_same rsegs m1 m2 RO1 SAME2) as RO2.
  pose proof (RA.rel_stk_back m2 m0 _ _ REL2 ST0) as ST2.
  pose proof (RA.rel_rw_back m2 m0 _ _ REL2 RW0) as RW2.
  (* the callee's region transport (declaration_of_post_on), moved across both mem_rel's *)
  assert (SWP : forall P, SRw.shadow_rw_on P m1 -> SRw.shadow_rw_on P m2)
    by (intros P HP; exact (SRwT.shadow_rw_on_of_rel P m2 m0 REL2 (SW0 P (SRwT.shadow_rw_on_rel P m1 _ REL1 HP)))).
  clear MU0 WM0 MI0 ST0 RW0 BA0 AC0 SW0.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit o) in MU2, RW2 by lia.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in MU2, ST2 by lia.
  rewrite Hok in RW2.
  replace (ret_pc (Z_to_bv 64 0x82888)) with (Z_to_bv 64 0x82888)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  rewrite Hok.
  (* --- the combined write set --- *)
  assert (MUa : munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m2).
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x (Hx & _). cbn [outside]. split; [exact Hx | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x (_ & Hx1 & Hx2 & _). cbn [outside].
      split; [exact Hx1|]. split; [exact Hx2 | exact I]. }
  assert (WMa : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [cells_bytes cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  assert (HINa : forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m2 (wa q) = Some b).
  { intros q Hq Hno.
    assert (Hslot : o <= q < o + 32 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. destruct Hdbb as (_ & _ & Hb).
      pose proof (Hb (Z.to_nat (q - o)) ltac:(rewrite Hdlen; lia)) as Hb0.
      replace (o + Z.of_nat (Z.to_nat (q - o))) with q in Hb0 by lia.
      destruct (nth_error (decl row) (Z.to_nat (q - o))) as [b|] eqn:En;
        [exists b; exact Hb0 | apply nth_error_None in En; rewrite Hdlen in En; lia]. }
    assert (Hshq : S + 8 <= q < S + 12 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (SWP _ HS4m1 q Hin ltac:(replace q with (S + 8 + (q - S - 8)) by lia; apply HSin; lia))). }
    assert (Hwinq : spv - 2304 <= q < spv -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (proj2 (proj2 ST2) q ltac:(unfold AF.SLOT_STACK in *; lia))). }
    destruct (Z_le_dec (S + 8) q) as [L1|L1]; destruct (Z_lt_dec q (S + 12)) as [L2|L2];
    destruct (Z_le_dec (spv - 2304) q) as [L3|L3]; destruct (Z_lt_dec q spv) as [L4|L4];
    destruct (Z_le_dec o q) as [L5|L5]; destruct (Z_lt_dec q (o + 32)) as [L6|L6];
    first [ apply Hshq; lia | apply Hwinq; lia | apply Hslot; lia
          | exfalso; apply Hno; cbn [outside]; repeat split; try exact I; lia ]. }
  assert (Haddr2 : addressable m2 o 32).
  { apply (f34_addr_keep m1 m2 o 32 Haddr1). intros a Ha. unfold mrd.
    rewrite (MU2 (wa (shadow_addr a))); [reflexivity|].
    assert (Hin : S + 8 <= shadow_addr a < S + 12) by (pose proof (Hosh (a - o) ltac:(lia)) as Hp;
      replace (o + (a - o)) with a in Hp by lia; exact Hp).
    assert (Happa : app_mem a) by (replace a with (o + (a - o)) by lia; apply Hoapp; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|exact I]].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      replace (shadow_addr a) with (o + (shadow_addr a - o)) by lia. apply Hoapp. lia. }
  apply evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MUa|]. split; [exact WMa|]. split; [exact RO2|]. split; [intros P HP; exact (SWP P (KEEP1 P HP))|].
  split; [exact ST2|]. split; [exact Hdbb|]. split; [exact Haddr2 | exact HINa].
Qed.

End F34F_on.
