(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names and addresses changed; 898 of its 975 lines of code are new or changed and 2389 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW5.v; 156 of its 192 lines of code are new or changed and 939 lines of the source are left out. *)
(* lib/A/ACtlTopFacts.v -- two walk-shell obligations of fuzz_ctrl image A's (ASan) cgif-form walk of
   LLVMFuzzerTestOneInput (libreac v1.9.0), PROVED: CTLRT_ENTRY and CHAIN_OF_CUT of lib/A/ACtl.v's Section Ctl
   (section 4).  CTLRT_ENTRY is in route (C)'s narrowed form (ctl_rt_C at the entry state).  Image B's twins are
   lib/B/ACtlTopFacts.v's ctlrt_entry (a working branch 7882aff59d2) and chain_of_cut
   (:164-261; written on a working branch c5887dd2836).  Written by a Theorem Labs lane (ctlrt_C_entry: a Theorem Labs lane;
   chain_of_cut: a Theorem Labs lane, brief chain-of-cut.md (a working note, not in this delivery)).  rule 24:
   proves no function of the image; these are bridge lemmas of the walk shell.

   WHY ROUTE (C).  a Theorem Labs lane's truth audit (11:02Z) found the full-shadow ACtlCut.ctl_rt and the hypothesis
   A.ProgWorld.AR_states_vis0_shadow FALSE at an AR state, so the walk's top was vacuous.  ctl_from now carries
   A.ACtlRtC.ctl_rt_C (a Theorem Labs lane), which the core's AR gives at every state without AR_states_vis0_shadow and
   without AR_states_owned_ro (a Theorem Labs lane 11:10Z).

   ROUTES.
   - ctlrt_C_entry: ctl_base's lib pre (A.ACfn.tfib_lib_pre_x) carries afn_pre, whose first conjunct is AR at the
     entry state (Reusable.YCbq.afn_pre), and the entry view's arodata_okS (its 11th conjunct).
     A.ProgWorld.arodata_okP_of_S turns the latter into arodata_okP at the same span, and a Theorem Labs lane's proved
     A.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms + AR_laws only) gives ctl_rt_C at the entry.
   - chain_of_cut: image B's proof (the donor's route, cgif A/ACf5.v rt_chain :170-185 and rt_trace_in :155-163,
     origin/ossv/recipes c8557374ad2e), over A's names, A's window 416 and A's four return addresses.  The entry
     chain is afn_pre's achain at the entry (`achain ly (aview ..) sp s0 []`).  The saved-register bytes give the
     caller frame record at fp = S (the entry sp): [S - 8] = RA_LLVMF and [S - 16] = the entry s0, read through the
     core's view by tf_rdword_le8 (the bytes lie in the journal's stack window, where the journal keeps every byte
     present: ajournal's apresent clause).  Above S the journal keeps the entry view (ajournal's view clause), so
     Reusable.YCbq.achain_push builds the chain one frame up and Reusable.YCbq.achain_chain_pre turns it into
     chain_pre at the call registers (s0 = S, alloc_ceiling <= sp).  The journal keeps the layout's top
     (layout_le), so chain_pre at the entry layout is chain_pre at ly3.  The call trace is one of
     A.ACej.TRACES_LLVMFuzzerTestOneInput's eight, in A.ACej.Tfib_universe ([pc_malloc_ra0 = 0x53618 or
     pc_free_ra0 = 0x534b8; the site's return; optionally RA_LLVMF = 0x80dd8]), by computation after TFIB_LIB's
     tl_code / tl_universe (A.ACeh.TfibLib).

   STATEMENTS.  Section TopFacts repeats ACtl.v's Section Ctl contexts and variables, the three Section hypotheses
   the proofs read (TFIB_SYMS, TFIB_LIB, LAWS) and the notations ctlcx / c_md / c_mem / CB, all with ACtl.v's texts.
   ctlrt_C_entry's statement is CTLRT_ENTRY's; chain_of_cut's is CHAIN_OF_CUT's (ACtl.v section 4) character for
   character after its `Hypothesis CHAIN_OF_CUT :` head.  ACtl.v cannot be Required here (it Requires this file), so
   the check that each lemma's type is its hypothesis's is made elsewhere: ACtl.v binds CTLRT_ENTRY by a Let whose
   type is the hypothesis text and whose body is ctlrt_C_entry at its Section's arguments; lib/A/ACtlChainAudit.v
   puts chain_of_cut in CHAIN_OF_CUT's argument slot of A.ACtl.ctl_lib_x (until ACtl.v binds CHAIN_OF_CUT by the
   same kind of Let, `A.ACtlTopFacts.chain_of_cut B MT XM_LIB RLO RHI TFIB_LIB`).
   NAMES TAKEN (Required qualified, never Imported): A.ACfn (LLVMF_STK, RA_LLVMF, via ctl_base tfib_lib_pre_x),
   A.AE2k (tfib_sink_head), A.ACeh (TfibLib, tl_code, tl_universe), A.ACej (memZL_In, the universe tables),
   Reusable.YCbq (afn_pre, ajournal, achain_push, achain_chain_pre, call_trace0), Reusable.YG0d (chain_pre, rdword,
   spZ, s0Z, raZ), Reusable.YG0n (aview, apresent), Reusable.YP09 (mbyte), Reusable.YK04 (mrestrict), lib/Lib/Mem
   (bytes_at, le8, bytes_at_app, length_le8, wa_unsigned).  lib/Lib is Required in the full form and never
   Imported; getr is used YK11-qualified only.
   No Axiom, no Parameter, no Admitted, no admit; no global setting. *)

From Stdlib Require Import ZArith List Lia.
(* LPS's machine vocabulary, the same Imports as ACtl.v (word, byte, bvmap, Z_to_bv, Z_to_le_bytes). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* Every unit module by its EXACT prefix (lib/A/Reusable, lib/B/Reusable and lib/U/Reusable hold twins of YK11, YM05
   and YO09, so a partial `Reusable.YK11` would match four files). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YO09 YG0f YC5d YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YG00 YG0n YCbq YK04 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AF0m ACtlCut ACtlRtC ProgWorld ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACfn AE2k ACeh ACej.
(* lib/Lib/Mem.v in the full form: lib/A/Bz/Lib, lib/B/Bz/Lib and lib/AZ/Lib hold twins of Mem (ACtl.v:122-125). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Byte-level bridge (image B's lib/B/ACtlTopFacts.v:64-130 at c5887dd2836, module paths only): an 8-byte
   little-endian word stored at present bytes reads back through the core's view; chain_pre reads the layout
   only through its top. *)

Lemma tf_u8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. reflexivity. Qed.

(* Byte k of the little-endian bytes of a 64-bit word. *)
Lemma tf_le8_byte : forall (w : word) (k : nat), (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (lib.Lib.Mem.le8 w) k) =
  Some ((bv_unsigned w / 2 ^ (8 * Z.of_nat k)) mod 256).
Proof.
  intros w k Hk.
  change (lib.Lib.Mem.le8 w) with (Z_to_le_bytes 8 (bv_unsigned w)).
  generalize (bv_unsigned w) as v. intros v.
  destruct k as [|k].
  { cbn [Z_to_le_bytes nth_error option_map]. rewrite tf_u8. change (2 ^ (8 * Z.of_nat 0)) with 1.
    rewrite Z.div_1_r. reflexivity. }
  do 7 (destruct k as [|k]; [cbn [Z_to_le_bytes nth_error option_map]; rewrite tf_u8;
         rewrite ?Z.shiftr_shiftr by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity|]).
  lia.
Qed.

Lemma tf_rdword_le8 : forall (sg1 sg2 : list Segment) (H : word -> bool) (m : word -> option byte) (a : Z)
    (w : word),
  (forall i, 0 <= i < 8 -> lib.Reusable.YG0n.apresent H m (a + i)) ->
  lib.Lib.Mem.bytes_at sg2 m a (lib.Lib.Mem.le8 w) ->
  lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview sg1 H m) a = Some (bv_unsigned w).
Proof.
  intros sg1 sg2 H m a w Hp (_ & _ & Hb).
  pose proof (bv_unsigned_in_range 64 w) as Hv. unfold bv_modulus in Hv. change (Z.of_N 64) with 64 in Hv.
  assert (Hrd : forall i : Z, 0 <= i < 8 ->
            lib.Reusable.YG0n.aview sg1 H m (a + i) = Some ((bv_unsigned w / 2 ^ (8 * i)) mod 256)).
  { intros i Hi. destruct (Hp i Hi) as [Hh [b Hm]].
    pose proof (Hb (Z.to_nat i) ltac:(rewrite lib.Lib.Mem.length_le8; lia)) as Hn.
    rewrite Z2Nat.id in Hn by lia. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in Hn. rewrite Hm in Hn.
    pose proof (tf_le8_byte w (Z.to_nat i) ltac:(lia)) as Hk. rewrite <- Hn in Hk. cbn [option_map] in Hk.
    rewrite Z2Nat.id in Hk by lia.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
    rewrite Hh, Hm. exact Hk. }
  pose proof (Hrd 0 ltac:(lia)) as R0. rewrite Z.add_0_r in R0. change (2 ^ (8 * 0)) with 1 in R0.
  rewrite Z.div_1_r in R0.
  pose proof (Hrd 1 ltac:(lia)) as R1. change (2 ^ (8 * 1)) with 256 in R1.
  pose proof (Hrd 2 ltac:(lia)) as R2. change (2 ^ (8 * 2)) with 65536 in R2.
  pose proof (Hrd 3 ltac:(lia)) as R3. change (2 ^ (8 * 3)) with 16777216 in R3.
  pose proof (Hrd 4 ltac:(lia)) as R4. change (2 ^ (8 * 4)) with 4294967296 in R4.
  pose proof (Hrd 5 ltac:(lia)) as R5. change (2 ^ (8 * 5)) with 1099511627776 in R5.
  pose proof (Hrd 6 ltac:(lia)) as R6. change (2 ^ (8 * 6)) with 281474976710656 in R6.
  pose proof (Hrd 7 ltac:(lia)) as R7. change (2 ^ (8 * 7)) with 72057594037927936 in R7.
  unfold lib.Reusable.YG0d.rdword. rewrite R0, R1, R2, R3, R4, R5, R6, R7. cbv beta iota. f_equal.
  generalize dependent (bv_unsigned w). intros v Hv.
  assert (D0 : v = v mod 256 + 256 * (v / 256)) by (pose proof (Z.div_mod v 256); lia).
  assert (Dk : forall c, 0 < c -> v / c = (v / c) mod 256 + 256 * (v / (c * 256))).
  { intros c Hc. rewrite <- Z.div_div by lia. pose proof (Z.div_mod (v / c) 256). lia. }
  pose proof (Dk 256 ltac:(lia)) as D1. pose proof (Dk 65536 ltac:(lia)) as D2.
  pose proof (Dk 16777216 ltac:(lia)) as D3. pose proof (Dk 4294967296 ltac:(lia)) as D4.
  pose proof (Dk 1099511627776 ltac:(lia)) as D5. pose proof (Dk 281474976710656 ltac:(lia)) as D6.
  pose proof (Dk 72057594037927936 ltac:(lia)) as D7.
  cbn [Z.mul] in D1, D2, D3, D4, D5, D6, D7.
  assert (D8 : v / 18446744073709551616 = 0) by (apply Z.div_small; lia).
  lia.
Qed.

(* chain_pre reads the layout only through its top. *)
Lemma tf_chain_pre_top : forall ly ly' rd regs ch,
  lib.Reusable.YG0f.ly_top ly' = lib.Reusable.YG0f.ly_top ly ->
  lib.Reusable.YG0d.chain_pre ly rd regs ch -> lib.Reusable.YG0d.chain_pre ly' rd regs ch.
Proof.
  intros ly ly' rd regs ch Et H. unfold lib.Reusable.YG0d.chain_pre, lib.Reusable.YG0d.frame0_ok in *.
  rewrite Et. exact H.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The two obligations, in ACtl.v's Section Ctl shape. *)
Section TopFacts.

(* ACtl.v Section Ctl's contexts and variables, in its order. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* ACtl.v's TFIB_SYMS and LAWS (ctlrt_C_entry reads both; this order is the argument order of ACtl.v's
   `Let CTLRT_ENTRY := A.ACtlTopFacts.ctlrt_C_entry B MT XM_LIB RLO RHI TFIB_SYMS LAWS`), and its TFIB_LIB
   (chain_of_cut reads it). *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.

(* ACtl.v section 1's notations that CHAIN_OF_CUT's text uses, verbatim. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).

(* CTLRT_ENTRY (lib/A/ACtl.v, section 4). *)
Lemma ctlrt_C_entry : forall cx : A.ACtlCut.ctlcx, A.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  A.ACtlRtC.ctl_rt_C B (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_mem cx).
Proof using TFIB_SYMS LAWS.
  intros cx ((HAF & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
  exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI _ _ _ _ _ (proj1 HAF)
           (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS (Z.le_refl _) (Z.le_refl _))).
Qed.

(* CHAIN_OF_CUT (lib/A/ACtl.v, section 4), its text after `Hypothesis CHAIN_OF_CUT :` copied verbatim. *)
Lemma chain_of_cut : forall (FP : list (Z * Z)) (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word)
    (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.
Proof using TFIB_LIB.
  intros FP cx own ly3 S3 W3 mem3 md3 k regsT pc0 ra HB HJ H8 H1 HBY Hlo Hhi HIN.
  unfold A.ACtlCut.c_sp in *.
  destruct HB as ((HAF & _) & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & _ & H47 & _ & Htop0 & Htop1).
  destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & Hview & _ & _ & _ & _ & Hpres & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Htop3 & _).
  unfold A.ACfn.LLVMF_STK in Hview, Hpres, Hslo.
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  (* the two words of the caller frame record at fp = S, in the cut memory *)
  assert (HBY2 : lib.Lib.Mem.bytes_at segs mem3 (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) - 16)
                   (lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (A.ACtlCut.c_regs cx) 8) ++
                    lib.Lib.Mem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF))).
  { pose proof HBY as HB'.
    do 11 (apply lib.Lib.Mem.bytes_at_app in HB'; destruct HB' as [_ HB']; rewrite lib.Lib.Mem.length_le8 in HB').
    match type of HB' with lib.Lib.Mem.bytes_at _ _ ?a _ =>
      replace a with (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) - 16) in HB' by lia end.
    exact HB'. }
  apply lib.Lib.Mem.bytes_at_app in HBY2. destruct HBY2 as [HS16 HS8].
  rewrite lib.Lib.Mem.length_le8 in HS8.
  assert (HR16 : lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3)
                   (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) - 16) =
                 Some (lib.Reusable.YG0d.s0Z (A.ACtlCut.c_regs cx))).
  { refine (tf_rdword_le8 segs segs _ _ _ _ _ HS16). intros i Hi. apply Hpres. lia. }
  assert (HR8 : lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3)
                  (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) - 8) = Some A.ACfn.RA_LLVMF).
  { replace (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) - 8)
      with (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) - 16 + Z.of_nat 8) by lia.
    transitivity (Some (bv_unsigned (Z_to_bv 64 A.ACfn.RA_LLVMF))); [| reflexivity].
    refine (tf_rdword_le8 segs segs _ _ _ _ _ HS8). intros i Hi. apply Hpres. lia. }
  (* above S the journal keeps the entry view *)
  assert (Hk : forall a, lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) <= a < 2 ^ 64 ->
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3 a =
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H (A.ACtlCut.c_W cx)) (A.ACtlCut.c_mem cx) a).
  { intros a Ha. apply Hview; lia. }
  (* the call registers: s0 = S, ra >= 4096, alloc_ceiling <= sp <= S - 416 *)
  assert (Hs0T : lib.Reusable.YG0d.s0Z regsT = lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx)).
  { unfold lib.Reusable.YG0d.s0Z. rewrite H8.
    apply (lib.Lib.Mem.wa_unsigned (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx))). lia. }
  assert (HraT : 4096 <= lib.Reusable.YG0d.raZ regsT).
  { unfold lib.Reusable.YG0d.raZ. rewrite H1.
    cbn [In] in HIN. destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as _ <-; vm_compute; discriminate. }
  assert (HspT : lib.Reusable.YM05.alloc_ceiling <= lib.Reusable.YG0d.spZ regsT <= lib.Reusable.YG0d.spZ regsT)
    by lia.
  (* the trace: one of TRACES_LLVMFuzzerTestOneInput's, at either chain *)
  assert (Htr : forall ch, ch = [] \/ ch = [(lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx), A.ACfn.RA_LLVMF,
                                            lib.Reusable.YG0d.s0Z (A.ACtlCut.c_regs cx))] ->
            A.ACtlCut.ctl_trace_in B pc0 regsT ch).
  { intros ch Ech. unfold A.ACtlCut.ctl_trace_in, lib.Reusable.YCbq.call_trace0, lib.Reusable.YG00.unwind_of_chain.
    rewrite (A.ACeh.tl_universe B TFIB_LIB).
    rewrite (A.ACeh.tl_code B TFIB_LIB) in HIN.
    unfold lib.Reusable.YG0d.raZ. rewrite H1.
    cbn [In] in HIN.
    destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
      destruct Ech as [-> | ->]; cbn [flat_map app];
      apply A.ACej.memZL_In; vm_compute; reflexivity. }
  destruct (Z.ltb_spec (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx) + 16)
              (lib.Reusable.YG0f.ly_top (A.ACtlCut.c_ly cx))) as [Hlt | Hge].
  - exists [(lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx), A.ACfn.RA_LLVMF,
             lib.Reusable.YG0d.s0Z (A.ACtlCut.c_regs cx))].
    split; [| apply Htr; right; reflexivity].
    unfold A.ACtlCut.ctl_chain.
    apply (tf_chain_pre_top (A.ACtlCut.c_ly cx) ly3 _ _ _ Htop3).
    apply (lib.Reusable.YCbq.achain_chain_pre _ _ (lib.Reusable.YG0d.spZ regsT)
             (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx)) _ regsT); [| exact HspT | exact Hs0T | exact HraT].
    apply (lib.Reusable.YCbq.achain_push (A.ACtlCut.c_ly cx)
             (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H (A.ACtlCut.c_W cx)) (A.ACtlCut.c_mem cx))
             (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3)
             (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx)) (lib.Reusable.YG0d.s0Z (A.ACtlCut.c_regs cx))
             A.ACfn.RA_LLVMF [] (lib.Reusable.YG0d.spZ regsT) Hch);
      [lia | exact Hk | exact HR8 | exact HR16 | unfold A.ACfn.RA_LLVMF; lia | lia | lia | lia | lia].
  - exists []. split; [| apply Htr; left; reflexivity].
    unfold A.ACtlCut.ctl_chain.
    apply (tf_chain_pre_top (A.ACtlCut.c_ly cx) ly3 _ _ _ Htop3).
    apply (lib.Reusable.YCbq.achain_chain_pre _ _ (lib.Reusable.YG0d.spZ regsT)
             (lib.Reusable.YG0d.spZ (A.ACtlCut.c_regs cx)) _ regsT); [| exact HspT | exact Hs0T | exact HraT].
    left. split; [right; left; lia | reflexivity].
Qed.

End TopFacts.

Print Assumptions ctlrt_C_entry.
Print Assumptions chain_of_cut.
