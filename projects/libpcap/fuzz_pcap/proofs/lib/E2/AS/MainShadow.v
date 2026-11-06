(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot2 BootS1 BootS2 BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS5 BootS6 BootS7 BootState. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma H_MAIN_shadow : forall (sp p8 sb p10 p12 a : word) (W : Z) (p24 x : word),
  SHB_LO <= bv_unsigned x < SHB_HI ->
  (bv_unsigned x < 0x7fffa000 \/ 0x7fffa000 + 779776 <= bv_unsigned x) ->
  (bv_unsigned x < bv_unsigned p24 \/ bv_unsigned p24 + 4096 <= bv_unsigned x) ->
  (bv_unsigned x < Wdst sp \/ Wdst sp + 8 <= bv_unsigned x) -> (bv_unsigned x < W \/ W + 8 <= bv_unsigned x) ->
  (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) ->
  (XQv sp + CSH <= bv_unsigned x < XQv sp + CSH + NSW \/ (bv_unsigned x < SHK sp \/ SHK sp + 39 <= bv_unsigned x)) ->
  (bv_unsigned x < SH12 p12 \/ SH12 p12 + 8192 <= bv_unsigned x) ->
  (bv_unsigned x < SHRI sb \/ SHRI sb + 512 <= bv_unsigned x) ->
  (bv_unsigned x < RI sb \/ RI sb + 4096 <= bv_unsigned x) ->
  H_MAIN sp p8 sb p10 p12 a W p24 x = true.
Proof.
  intros sp p8 sb p10 p12 a W p24 x HS C1 C2 C3 C4 C5 C6 C7 C8 C9.
  unfold H_MAIN. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C1].
  apply (proj2 (hcut_true _ _ _ _)). split; [| exact C2].
  apply hjoin_old. unfold H10.
  apply (proj2 (hcut_true _ _ _ _)). split; [| exact C3].
  apply (proj2 (hcut_true _ _ _ _)). split; [| exact C4].
  unfold H9. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C5].
  assert (B7 : H7 p8 sb p10 p12 x = true).
  { unfold H7. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C7].
    unfold H6. apply hjoin_old. unfold H5. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C8].
    unfold H4. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C9].
    unfold H3. apply hjoin_old. unfold H2. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  unfold H9a. destruct C6 as [C6|C6].
  - apply hhide_in. exact C6.
  - unfold hhide. unfold H8. rewrite (proj2 (hcut_true _ _ _ _) (conj B7 C6)). reflexivity.
Qed.

Section Shadow.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  #[using="brk mbase draw inp VI VE usp"] Lemma shk_in_window : XQv sp + CSH <= SHK sp /\ SHK sp + 39 <= XQv sp + CSH + NSW.
  Proof.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, SHi, S16.
    pose proof (x9_facts sp S16 SLo ltac:(fold usp; lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & _).
    unfold SHK, CSH, NSW. fold usp in X2, X3 |- *. clear - X2 X3 X6 SLo. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem at_main_shadow_zero : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall x : word,
      (SHB_LO <= bv_unsigned x < SHB_LO + 2 ^ 28 \/ 2201439137792 <= bv_unsigned x < SHB_HI) ->
      (bv_unsigned x < 0x7fffa000 \/ 0x7fffa000 + 779776 <= bv_unsigned x) ->
      (bv_unsigned x < Wdst sp \/ Wdst sp + 8 <= bv_unsigned x) -> (bv_unsigned x < W \/ W + 8 <= bv_unsigned x) ->
      (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) ->
      (bv_unsigned x < SH12 p12 \/ SH12 p12 + 8192 <= bv_unsigned x) ->
      (bv_unsigned x < SHRI sb \/ SHRI sb + 512 <= bv_unsigned x) ->
      M x = Some (Z_to_bv 8 0).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl
           (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24)
           x HX C1 C3 C4 C5 C7 C8.
    pose proof HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    destruct shk_in_window as [K1 K2].
    assert (HS : SHB_LO <= bv_unsigned x < SHB_HI) by (unfold SHB_LO, SHB_HI in *; lia).
    assert (HH : H_MAIN sp p8 sb p10 p12 a W p24 x = true).
    { apply H_MAIN_shadow; try assumption.
      - clear - AP24 HS. lia.
      - destruct (Z_lt_ge_dec (bv_unsigned x) (SHK sp)) as [L|L]; [right; left; exact L|].
        destruct (Z_lt_ge_dec (bv_unsigned x) (SHK sp + 39)) as [L2|L2]; [left; clear - L L2 K1 K2; lia | right; right; lia].
      - unfold RI, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE in *. rewrite Hsb. unfold SBV. clear - P2 HS. pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)). lia. }
    unfold hf_ok, HC_MAIN, hc6, hc3, HC5 in HZ.
    apply Forall_inv_tail in HZ. apply Forall_inv_tail in HZ. apply Forall_inv_tail in HZ.
    destruct HX as [HX|HX].
    - apply Forall_inv_tail in HZ. apply Forall_inv in HZ. cbn [fst snd] in HZ. exact (HZ x HX HH).
    - apply Forall_inv in HZ. cbn [fst snd] in HZ. exact (HZ x HX HH).
  Qed.
End Shadow.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.TwB.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma H_MAIN_shadow : forall (sp p8 sb p10 p12 a : word) (W : Z) (p24 x : word),
  SHB_LO <= bv_unsigned x < SHB_HI ->
  (bv_unsigned x < 0x7fffa000 \/ 0x7fffa000 + 780288 <= bv_unsigned x) ->
  (bv_unsigned x < bv_unsigned p24 \/ bv_unsigned p24 + 4096 <= bv_unsigned x) ->
  (bv_unsigned x < Wdst sp \/ Wdst sp + 8 <= bv_unsigned x) -> (bv_unsigned x < W \/ W + 8 <= bv_unsigned x) ->
  (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) ->
  (XQv sp + CSH <= bv_unsigned x < XQv sp + CSH + NSW \/ (bv_unsigned x < SHK sp \/ SHK sp + 39 <= bv_unsigned x)) ->
  (bv_unsigned x < SH12 p12 \/ SH12 p12 + 8192 <= bv_unsigned x) ->
  (bv_unsigned x < SHRI sb \/ SHRI sb + 512 <= bv_unsigned x) ->
  (bv_unsigned x < RI sb \/ RI sb + 4096 <= bv_unsigned x) ->
  H_MAIN sp p8 sb p10 p12 a W p24 x = true.
Proof.
  intros sp p8 sb p10 p12 a W p24 x HS C1 C2 C3 C4 C5 C6 C7 C8 C9.
  unfold H_MAIN. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C1].
  apply (proj2 (hcut_true _ _ _ _)). split; [| exact C2].
  apply hjoin_old. unfold H10.
  apply (proj2 (hcut_true _ _ _ _)). split; [| exact C3].
  apply (proj2 (hcut_true _ _ _ _)). split; [| exact C4].
  unfold H9. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C5].
  assert (B7 : H7 p8 sb p10 p12 x = true).
  { unfold H7. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C7].
    unfold H6. apply hjoin_old. unfold H5. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C8].
    unfold H4. apply (proj2 (hcut_true _ _ _ _)). split; [| exact C9].
    unfold H3. apply hjoin_old. unfold H2. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  unfold H9a. destruct C6 as [C6|C6].
  - apply hhide_in. exact C6.
  - unfold hhide. unfold H8. rewrite (proj2 (hcut_true _ _ _ _) (conj B7 C6)). reflexivity.
Qed.

Section Shadow.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  #[using="brk mbase draw inp VI VE usp"] Lemma shk_in_window : XQv sp + CSH <= SHK sp /\ SHK sp + 39 <= XQv sp + CSH + NSW.
  Proof.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, SHi, S16.
    pose proof (x9_facts sp S16 SLo ltac:(fold usp; lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & _).
    unfold SHK, CSH, NSW. fold usp in X2, X3 |- *. clear - X2 X3 X6 SLo. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem at_main_shadow_zero : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall x : word,
      (SHB_LO <= bv_unsigned x < SHB_LO + 2 ^ 28 \/ 2201439137792 <= bv_unsigned x < SHB_HI) ->
      (bv_unsigned x < 0x7fffa000 \/ 0x7fffa000 + 780288 <= bv_unsigned x) ->
      (bv_unsigned x < Wdst sp \/ Wdst sp + 8 <= bv_unsigned x) -> (bv_unsigned x < W \/ W + 8 <= bv_unsigned x) ->
      (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) ->
      (bv_unsigned x < SH12 p12 \/ SH12 p12 + 8192 <= bv_unsigned x) ->
      (bv_unsigned x < SHRI sb \/ SHRI sb + 512 <= bv_unsigned x) ->
      M x = Some (Z_to_bv 8 0).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl
           (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24)
           x HX C1 C3 C4 C5 C7 C8.
    pose proof HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    destruct shk_in_window as [K1 K2].
    assert (HS : SHB_LO <= bv_unsigned x < SHB_HI) by (unfold SHB_LO, SHB_HI in *; lia).
    assert (HH : H_MAIN sp p8 sb p10 p12 a W p24 x = true).
    { apply H_MAIN_shadow; try assumption.
      - clear - AP24 HS. lia.
      - destruct (Z_lt_ge_dec (bv_unsigned x) (SHK sp)) as [L|L]; [right; left; exact L|].
        destruct (Z_lt_ge_dec (bv_unsigned x) (SHK sp + 39)) as [L2|L2]; [left; clear - L L2 K1 K2; lia | right; right; lia].
      - unfold RI, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE in *. rewrite Hsb. unfold SBV. clear - P2 HS. pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)). lia. }
    unfold hf_ok, HC_MAIN, hc6, hc3, HC5 in HZ.
    apply Forall_inv_tail in HZ. apply Forall_inv_tail in HZ. apply Forall_inv_tail in HZ.
    destruct HX as [HX|HX].
    - apply Forall_inv_tail in HZ. apply Forall_inv in HZ. cbn [fst snd] in HZ. exact (HZ x HX HH).
    - apply Forall_inv in HZ. cbn [fst snd] in HZ. exact (HZ x HX HH).
  Qed.
End Shadow.
End TwB.
