(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module names changed; 166 of its 213 lines of code are new or changed and 512 lines of the source are left out. *)
(* lib/B/ACtlTopFacts.v -- two walk-shell obligations of fuzz_ctrl image B's (asan-ubsan) cgif-form walk of
   LLVMFuzzerTestOneInput (libreac v1.9.0), PROVED: the Section hypotheses CTLRT_ENTRY (lib/B/ACtl.v:358-359) and
   CHAIN_OF_CUT (lib/B/ACtl.v:370-390) of ACtl.v's Section Ctl, in route (C)'s shell (staging a working branch 78699c46fe7).
   Written by a Theorem Labs lane.  rule 24: proves no function of the image; these are bridge lemmas of
   the walk shell.

   STATEMENTS.  Section TopFacts below repeats ACtl.v's Section Ctl Context, Variables and the Section hypotheses
   the two proofs read (TFIB_SYMS, TFIB_LIB), with ACtl.v's exact texts, and the notations segs / CB / c_mem / c_md.
   ctlrt_entry and chain_of_cut are stated with ACtl.v's hypothesis texts token for token.  Section
   CheckAgainstACtl at the end re-opens ACtl.v's Section shape and applies B.ACtl.ctl_lib_x to both lemmas in the
   argument slots of CTLRT_ENTRY and CHAIN_OF_CUT, so the elaborator checks that each lemma's type is that
   hypothesis's type after Section instantiation.

   ROUTES.
   - ctlrt_entry: ctl_base's lib pre (Reusable.YCfn.tfib_lib_pre_x) carries afn_pre, whose first conjunct is AR at
     the entry state (YCbq.afn_pre), and the entry view's arodata_okS.  B.ProgWorld.arodata_okP_of_S turns the latter
     into arodata_okP, and the proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms + AR_laws; no
     AR_states_vis0_shadow, no AR_states_owned_ro) gives ctl_rt_C at the entry.  Its AR_laws premise is the core's
     PROVED Reusable.YG0q.AR_laws_ok (the stage files take it as a LAWS hypothesis; here no hypothesis is needed).
   - chain_of_cut: the donor's route (cgif A/ACf5.v rt_chain :170-185 and rt_trace_in :155-163, origin/ossv/recipes
     c8557374ad2e), restated over the walk's journal.  The entry chain is afn_pre's achain at the entry
     (YCbq.afn_pre: `achain ly (aview ..) sp s0 []`).  The saved-register bytes give the caller frame record at
     fp = S (the entry sp): [S - 8] = RA_LLVMF and [S - 16] = the entry s0, read through the core's view by
     tf_rdword_le8 (the bytes lie in the journal's stack window, where the journal keeps every byte present:
     ajournal's apresent clause).  Above S the journal keeps the entry view (ajournal's view clause), so
     YCbq.achain_push builds the chain one frame up and YCbq.achain_chain_pre turns it into chain_pre at the call
     registers (s0 = S, alloc_ceiling <= sp).  The layout's top is kept by the journal (layout_le), so chain_pre at
     the entry layout is chain_pre at ly3.  The call trace is one of TRACES_LLVMFuzzerTestOneInput's eight
     (Reusable.YCej, the universe tables of image B), by computation after TFIB_LIB's tl_code / tl_universe.
   NO SECTION HYPOTHESIS IS ADDED: the two lemmas use only ACtl.v's TFIB_SYMS and TFIB_LIB.

   NAMES TAKEN (Required qualified, never Imported, as ACtl.v): Reusable.YCfn (tfib_lib_pre_x via ACtlCut.ctl_base,
   LLVMF_STK, RA_LLVMF), Reusable.YCbq (afn_pre, ajournal, achain, achain_push, achain_chain_pre, call_trace0),
   Reusable.YG0d (chain_pre, rdword, spZ, s0Z, raZ), Reusable.YG0n (aview, apresent), Reusable.YG0q (AR_laws_ok),
   Reusable.YCeg (TfibLib, tl_code, tl_universe), Reusable.YCej (Tfib_universe, memZL_In), Reusable.YF0l (Tfib_code),
   lib/Lib/Mem (bytes_at, le8, bytes_at_app), B.ProgWorld (arodata_okP_of_S), B.ProgWorldCtlRtC (ctl_rt_C_of_AR),
   B.ACtlRtC (ctl_rt_C), B.ACtlCut (ctl_base, ctl_chain, ctl_trace_in), B.ACtl (ctl_lib_x, for the Check only).
   SHADOWED NAMES: getr / cfg_at / seg_rom are used YK11- / YG0d-qualified only; lib/Lib is Required, never Imported.
   No Axiom, no Parameter, no Admitted, no admit; no global setting. *)

From Coq Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YO09 YI16 YK04 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YCfn Reusable.YE2k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCeg Reusable.YF0m Reusable.YCej Reusable.YF0l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlRtC B.ProgWorld B.ProgWorldCtlRtC B.ACtl.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Byte-level bridge: an 8-byte little-endian word stored at present bytes reads back through the core's view.
   (The same computation as lib/B/ACtlW5.v's w5_le8_byte / w5_rdword, here over present bytes, so neither the
   segment list of bytes_at nor that of aview is consulted.) *)

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
  (forall i, 0 <= i < 8 -> Reusable.YG0n.apresent H m (a + i)) ->
  lib.Lib.Mem.bytes_at sg2 m a (lib.Lib.Mem.le8 w) ->
  Reusable.YG0d.rdword (Reusable.YG0n.aview sg1 H m) a = Some (bv_unsigned w).
Proof.
  intros sg1 sg2 H m a w Hp (_ & _ & Hb).
  pose proof (bv_unsigned_in_range 64 w) as Hv. unfold bv_modulus in Hv. change (Z.of_N 64) with 64 in Hv.
  assert (Hrd : forall i : Z, 0 <= i < 8 ->
            Reusable.YG0n.aview sg1 H m (a + i) = Some ((bv_unsigned w / 2 ^ (8 * i)) mod 256)).
  { intros i Hi. destruct (Hp i Hi) as [Hh [b Hm]].
    pose proof (Hb (Z.to_nat i) ltac:(rewrite lib.Lib.Mem.length_le8; lia)) as Hn.
    rewrite Z2Nat.id in Hn by lia. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in Hn. rewrite Hm in Hn.
    pose proof (tf_le8_byte w (Z.to_nat i) ltac:(lia)) as Hk. rewrite <- Hn in Hk. cbn [option_map] in Hk.
    rewrite Z2Nat.id in Hk by lia.
    unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
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
  unfold Reusable.YG0d.rdword. rewrite R0, R1, R2, R3, R4, R5, R6, R7. cbv beta iota. f_equal.
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
  Reusable.YG0f.ly_top ly' = Reusable.YG0f.ly_top ly ->
  Reusable.YG0d.chain_pre ly rd regs ch -> Reusable.YG0d.chain_pre ly' rd regs ch.
Proof.
  intros ly ly' rd regs ch Et H. unfold Reusable.YG0d.chain_pre, Reusable.YG0d.frame0_ok in *.
  rewrite Et. exact H.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The two obligations, in ACtl.v's Section Ctl shape. *)
Section TopFacts.

(* ACtl.v:144-148, verbatim. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* ACtl.v:157-158, verbatim (the hypotheses the two proofs read). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : Reusable.YCeg.TfibLib B.

(* ACtl.v:171, :178-180, verbatim. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).

(* CTLRT_ENTRY (ACtl.v:358-359). *)
Lemma ctlrt_entry : forall cx : ctlcx, CB cx ->
  B.ACtlRtC.ctl_rt_C B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (c_mem cx).
Proof using TFIB_SYMS.
  intros cx ((HAF & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
  exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS (Reusable.YG0q.AR_laws_ok segs B) RLO RHI
           _ _ _ _ _ (proj1 HAF)
           (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS (Z.le_refl _) (Z.le_refl _))).
Qed.

(* CHAIN_OF_CUT (ACtl.v:370-390). *)
Lemma chain_of_cut : forall (FP : list (Z * Z)) (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word)
    (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := Reusable.YE2k.tfib_sink_head) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     lib.Lib.Mem.le8 (Z_to_bv 64 Reusable.YCfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 448 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81764);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81aa0);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81f50);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82d1c)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.
Proof using TFIB_LIB.
  intros FP cx own ly3 S3 W3 mem3 md3 k regsT pc0 ra HB HJ H8 H1 HBY Hlo Hhi HIN.
  unfold ACtlCut.c_sp in *.
  destruct HB as ((HAF & _) & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & _ & H47 & _ & Htop0 & Htop1).
  destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & Hview & _ & _ & _ & _ & Hpres & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Htop3 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hview, Hpres, Hslo.
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  (* the two words of the caller frame record at fp = S, in the cut memory *)
  assert (HBY2 : lib.Lib.Mem.bytes_at segs mem3 (Reusable.YG0d.spZ (ACtlCut.c_regs cx) - 16)
                   (lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
                    lib.Lib.Mem.le8 (Z_to_bv 64 Reusable.YCfn.RA_LLVMF))).
  { pose proof HBY as HB'.
    do 11 (apply lib.Lib.Mem.bytes_at_app in HB'; destruct HB' as [_ HB']; rewrite lib.Lib.Mem.length_le8 in HB').
    match type of HB' with lib.Lib.Mem.bytes_at _ _ ?a _ =>
      replace a with (Reusable.YG0d.spZ (ACtlCut.c_regs cx) - 16) in HB' by lia end.
    exact HB'. }
  apply lib.Lib.Mem.bytes_at_app in HBY2. destruct HBY2 as [HS16 HS8].
  rewrite lib.Lib.Mem.length_le8 in HS8.
  assert (HR16 : Reusable.YG0d.rdword (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3)
                   (Reusable.YG0d.spZ (ACtlCut.c_regs cx) - 16) =
                 Some (Reusable.YG0d.s0Z (ACtlCut.c_regs cx))).
  { refine (tf_rdword_le8 segs segs _ _ _ _ _ HS16). intros i Hi. apply Hpres. lia. }
  assert (HR8 : Reusable.YG0d.rdword (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3)
                  (Reusable.YG0d.spZ (ACtlCut.c_regs cx) - 8) = Some Reusable.YCfn.RA_LLVMF).
  { replace (Reusable.YG0d.spZ (ACtlCut.c_regs cx) - 8) with (Reusable.YG0d.spZ (ACtlCut.c_regs cx) - 16 + Z.of_nat 8)
      by lia.
    transitivity (Some (bv_unsigned (Z_to_bv 64 Reusable.YCfn.RA_LLVMF))); [| reflexivity].
    refine (tf_rdword_le8 segs segs _ _ _ _ _ HS8). intros i Hi. apply Hpres. lia. }
  (* above S the journal keeps the entry view *)
  assert (Hk : forall a, Reusable.YG0d.spZ (ACtlCut.c_regs cx) <= a < 2 ^ 64 ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a =
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx) a).
  { intros a Ha. apply Hview; lia. }
  (* the call registers: s0 = S, ra >= 4096, alloc_ceiling <= sp <= S - 448 *)
  assert (Hs0T : Reusable.YG0d.s0Z regsT = Reusable.YG0d.spZ (ACtlCut.c_regs cx)).
  { unfold Reusable.YG0d.s0Z. rewrite H8. apply (lib.Lib.Mem.wa_unsigned (Reusable.YG0d.spZ (ACtlCut.c_regs cx))).
    lia. }
  assert (HraT : 4096 <= Reusable.YG0d.raZ regsT).
  { unfold Reusable.YG0d.raZ. rewrite H1.
    cbn [In] in HIN. destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as _ <-; vm_compute; discriminate. }
  assert (HspT : lib.Reusable.YM05.alloc_ceiling <= Reusable.YG0d.spZ regsT <= Reusable.YG0d.spZ regsT) by lia.
  (* the trace: one of TRACES_LLVMFuzzerTestOneInput's, at either chain *)
  assert (Htr : forall ch, ch = [] \/ ch = [(Reusable.YG0d.spZ (ACtlCut.c_regs cx), Reusable.YCfn.RA_LLVMF,
                                            Reusable.YG0d.s0Z (ACtlCut.c_regs cx))] ->
            ACtlCut.ctl_trace_in B pc0 regsT ch).
  { intros ch Ech. unfold ACtlCut.ctl_trace_in, Reusable.YCbq.call_trace0, Reusable.YG00.unwind_of_chain.
    rewrite (Reusable.YCeg.tl_universe B TFIB_LIB).
    rewrite (Reusable.YCeg.tl_code B TFIB_LIB) in HIN.
    unfold Reusable.YG0d.raZ. rewrite H1.
    cbn [In] in HIN.
    destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
      destruct Ech as [-> | ->]; cbn [flat_map app];
      apply Reusable.YCej.memZL_In; vm_compute; reflexivity. }
  destruct (Z.ltb_spec (Reusable.YG0d.spZ (ACtlCut.c_regs cx) + 16) (Reusable.YG0f.ly_top (ACtlCut.c_ly cx)))
    as [Hlt | Hge].
  - exists [(Reusable.YG0d.spZ (ACtlCut.c_regs cx), Reusable.YCfn.RA_LLVMF, Reusable.YG0d.s0Z (ACtlCut.c_regs cx))].
    split; [| apply Htr; right; reflexivity].
    unfold ACtlCut.ctl_chain.
    apply (tf_chain_pre_top (ACtlCut.c_ly cx) ly3 _ _ _ Htop3).
    apply (Reusable.YCbq.achain_chain_pre _ _ (Reusable.YG0d.spZ regsT) (Reusable.YG0d.spZ (ACtlCut.c_regs cx))
             _ regsT); [| exact HspT | exact Hs0T | exact HraT].
    apply (Reusable.YCbq.achain_push (ACtlCut.c_ly cx)
             (Reusable.YG0n.aview segs (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx))
             (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3)
             (Reusable.YG0d.spZ (ACtlCut.c_regs cx)) (Reusable.YG0d.s0Z (ACtlCut.c_regs cx))
             Reusable.YCfn.RA_LLVMF [] (Reusable.YG0d.spZ regsT) Hch);
      [lia | exact Hk | exact HR8 | exact HR16 | unfold Reusable.YCfn.RA_LLVMF; lia | lia | lia | lia | lia].
  - exists []. split; [| apply Htr; left; reflexivity].
    unfold ACtlCut.ctl_chain.
    apply (tf_chain_pre_top (ACtlCut.c_ly cx) ly3 _ _ _ Htop3).
    apply (Reusable.YCbq.achain_chain_pre _ _ (Reusable.YG0d.spZ regsT) (Reusable.YG0d.spZ (ACtlCut.c_regs cx))
             _ regsT); [| exact HspT | exact Hs0T | exact HraT].
    left. split; [right; left; lia | reflexivity].
Qed.

End TopFacts.

(* ---------------------------------------------------------------------------------------------------------
   3. The statements are ACtl.v's hypotheses: ACtl.v's Section Ctl shape again (Context, Variables and the Section
   hypotheses declared before CTLRT_ENTRY, verbatim ACtl.v:144-158 and :352), and B.ACtl.ctl_lib_x applied to the
   two lemmas in the argument slots of CTLRT_ENTRY and CHAIN_OF_CUT. *)
Section CheckAgainstACtl.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : Reusable.YCeg.TfibLib B.
Hypothesis LS_LEAF : forall pl fs K, @lib.Reusable.YO09.LIBK LS pl fs K = K (lib.Reusable.YO09.LL 0 fs []).

Check (ctlrt_entry B MT XM_LIB RLO RHI TFIB_SYMS
       : forall cx : ACtlCut.ctlcx, ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
         B.ACtlRtC.ctl_rt_C B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_mem cx)).
Check (@B.ACtl.ctl_lib_x fx rc LS B MT XM_LIB XN_LIB RLO RHI RELRO_IMG TFIB_SYMS TFIB_LIB LS_LEAF
         (ctlrt_entry B MT XM_LIB RLO RHI TFIB_SYMS)
         (chain_of_cut B MT XM_LIB RLO RHI TFIB_LIB)).
End CheckAgainstACtl.

Print Assumptions ctlrt_entry.
Print Assumptions chain_of_cut.
