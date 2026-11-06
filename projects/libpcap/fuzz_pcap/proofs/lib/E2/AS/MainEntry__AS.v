(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootS5 BootS6 BootS7 BootState.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Mem Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require A3Kn MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot2 BootS1 BootH2 BootNodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS8.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require MState Cells Step.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RelSpec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainAux MainShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require RegsEqv0__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MainEntry.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootS5 BootS6 BootS7 BootState. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require A3Kn MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac in_solve_e := repeat (first [left; reflexivity | right]).
Open Scope Z_scope.

Lemma seg_rom_off : forall segs (a : word), find_segment segs (bv_unsigned a) 1 = None -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.seg_rom segs a = None.
Proof. intros segs a H. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity. Qed.

Lemma in_kn_b : forall K kn, existsb (APC.kentry_eqb K) kn = true -> In K kn.
Proof. intros K kn Hb. apply existsb_exists in Hb as (k & Hk & He). apply KNA.kentry_eqb_eq in He. subst k. exact Hk. Qed.

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  Definition V_of (a tid c : word) (pl : placements) (js : list word) : nat -> Z := uev (tgt_env (EB' a tid c pl js)).

  (* [comment removed for export] *)
  #[using="Type"] Lemma page_of_map : forall E (L : ledger) i n lo hi,
    maps_ok sp E L -> In (EVar i, n) (l_maps L) -> usp <= 2 ^ 47 -> n mod 4096 = 0 ->
    lo <= 1 -> 4096 * hi = 2 ^ 47 - 8388608 - n ->
    bv_unsigned (ev E i) mod 4096 = 0 /\ 4096 * lo <= bv_unsigned (ev E i) <= 4096 * hi.
  Proof.
    intros E L i n lo hi HMO Hin Hsp Hn Hlo Hhi. pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO.
    unfold map_ok in MO. cbn [fst snd edenot] in MO. destruct MO as (M1 & M2 & M3 & M4 & _). unfold stack_max_size in M4. fold usp in M4.
    split; [exact M1|]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma at_main_usp : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl -> usp <= 140737488355136.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & _). destruct HB as [_ HKN _ _ _ _ _ _ _ _ _ _].
    assert (IN : In (KRange (EVar 0) 140735340871680 140737488355136) (if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN else A3.BootKn11w2.KN_MAIN))
      by (destruct w1; apply in_kn_b; vmeq_refl).
    pose proof (proj1 (Forall_forall _ _) HKN _ IN) as R0. cbn [kentry_ok edenot] in R0.
    rewrite (ev_EB_sp sp draw inp a tid c pl js) in R0. fold usp in R0. lia.
  Qed.

  #[using="VI VE usp"] Theorem at_main_facts : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (mfact_ok SEGS (V_of a tid c pl js) M) (asan_mem_facts_kn ++ (if w1 then asan_mem_facts_w1 else asan_mem_facts_w2))
    /\ Forall (pfact_ok (V_of a tid c pl js)) (asan_pure_facts_kn ++ (if w1 then asan_pure_facts_w1 else asan_pure_facts_w2)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs
           (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    set (KNw := if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN else A3.BootKn11w2.KN_MAIN) in *.
    pose proof HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in S16.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    (* [comment removed for export] *)
    assert (KIN : forall K, existsb (APC.kentry_eqb K) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN && existsb (APC.kentry_eqb K) A3.BootKn11w2.KN_MAIN = true ->
                            kentry_ok SEGS E (mrestrict (H_MAIN sp p8 sb p10 p12 a W p24) M) K).
    { intros K HK. apply andb_prop in HK as [K1 K2]. apply (proj1 (Forall_forall _ _) HKN). unfold KNw. destruct w1; apply in_kn_b; assumption. }
    pose proof (KIN (KRange (EVar 0) 140735340871680 140737488355136) ltac:(vmeq_refl)) as R0. cbn [kentry_ok edenot] in R0. rewrite E0 in R0. fold usp in R0.
    (* [comment removed for export] *)
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    assert (KOK : know_ok SEGS (tgt_env E) (mrestrict (H_MAIN sp p8 sb p10 p12 a W p24) M) (vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 KNw)).
    { apply (trx_A3_sound E); [| | | | | | | exact HKN].
      - (* [comment removed for export] *) rewrite E0. exact S16.
      - rewrite E0. fold usp. lia.
      - (* [comment removed for export] *)
        assert (PG : forall i n lo hi, In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 -> lo <= 1 -> 4096 * hi = 2 ^ 47 - 8388608 - n ->
                     bv_unsigned (ev E i) mod 4096 = 0 /\ 4096 * lo <= bv_unsigned (ev E i) <= 4096 * hi)
          by (intros i n lo hi Hin Hn Hlo Hhi; exact (page_of_map E (L_MAIN lb) i n lo hi HMO Hin ltac:(lia) Hn Hlo Hhi)).
        unfold PAGES4. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        + apply (PG 26%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 27%nat 3727360); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + (* [comment removed for export] *)
          destruct (PG 28%nat 137439023104 1 34326181871 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve_e) eq_refl ltac:(lia) eq_refl) as [A1 A2].
          split; [exact A1|]. rewrite E28 in *. unfold SHB_HI in P2. lia.
        + apply (PG 36%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 37%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 38%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 46%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 60%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 83%nat 11571200); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + (* [comment removed for export] *)
          pose proof (KIN (KAlign (EVar 101) 4096) ltac:(vmeq_refl)) as KA.
          pose proof (KIN (KRange (EVar 101) 6303744 1080045568) ltac:(vmeq_refl)) as KR.
          cbn [kentry_ok edenot] in KA, KR. destruct KA as [_ KA]. split; [exact KA | lia].
        + apply (PG 104%nat 1048576); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 105%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 106%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 107%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
      - (* [comment removed for export] *)
        unfold VR_REN. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [unfold RENAMES; cbn [In]; in_solve_e|]).
        + exact (KIN (KRange (EVar 1) 1 1024) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 2) 0 256) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 3) 0 131071) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 4) 0 280000) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 5) 0 4294967294) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 8) 1 4194303) ltac:(vmeq_refl)).
      - (* [comment removed for export] *) rewrite E29, E28, Hsb. unfold SBV. lia.
      - (* [comment removed for export] *) rewrite E62, E0. fold usp.
        unfold STv. fold usp. apply u_small.
        pose proof (Z.div_mod (usp + 3935) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp + 3935) 4096 ltac:(lia)). lia.
      - (* [comment removed for export] *) rewrite E63, E62.
        pose proof (x9_facts sp S16 SLo ltac:(fold usp; lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & _). unfold XLO, XHI in *.
        rewrite !u_small by lia. reflexivity. }
    assert (HID_rom : forall x : word, H_MAIN sp p8 sb p10 p12 a W p24 x = true -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.seg_rom SEGS x = None)
      by (intros x Hx; apply seg_rom_off; exact (HH x Hx)).
    assert (HULL_vis : forall x : word, 65536 <= bv_unsigned x < 6303744 -> H_MAIN sp p8 sb p10 p12 a W p24 x = false).
    { intros x Hx. destruct (H_MAIN sp p8 sb p10 p12 a W p24 x) eqn:EH; [|reflexivity]. exfalso.
      destruct (HIN x EH) as ([e n] & Hin & Hr). cbn [fst snd] in Hr.
      pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd] in MO.
      destruct MO as (_ & _ & _ & _ & MI). unfold A_img_lo, A_img_hi in MI. lia. }
    destruct w1.
    - unfold KNw in KOK. cbv iota in KOK. rewrite KNX1_eq in KOK.
      exact (export_sound SEGS (tgt_env E) _ M KNX1 65536 6303744 KOK HID_rom HULL_vis _ _ asan_mem_facts_justified_w1 asan_pure_facts_justified_w1).
    - unfold KNw in KOK. cbv iota in KOK. rewrite KNX2_eq in KOK.
      exact (export_sound SEGS (tgt_env E) _ M KNX2 65536 6303744 KOK HID_rom HULL_vis _ _ asan_mem_facts_justified_w2 asan_pure_facts_justified_w2).
  Qed.

  (* [comment removed for export] *)
  #[using="sp usp"] Lemma off_img_Z : forall a : Z, IMG_HI <= a < 2 ^ 64 -> find_segment SEGS a 1 = None.
  Proof.
    intros a Ha. pose proof (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                               ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy) (Z_to_bv 64 a)) as X.
    assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_small; unfold IMG_HI in Ha; lia).
    rewrite U in X. apply X. apply Z.leb_le. rewrite U. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem at_main_ro_stk : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    (forall i, 0x10000 <= i < 0xa4000 -> M (wa i) = None)
    /\ stk SEGS M (usp - 8388608) usp.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM.
    destruct (at_main_facts w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM) as [HMF _].
    pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in S16.
    split.
    - intros i Hi. exact (mimg_cover SEGS _ M asan_mem_facts_kn 0x10000 0xa4000 HMFc ltac:(vmeq_refl) i Hi).
    - pose proof (mwr_find SEGS _ M asan_mem_facts_kn
                    (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
                    HMFc ltac:(vmeq_refl)) as WR.
      cbn [zv] in WR.
      (* [comment removed for export] *)
      pose proof (at_main_usp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as ULT.
      assert (E0 : ev (EB' a tid c pl js) 0%nat = sp) by apply ev_EB_sp.
      assert (DG : 32768 * V_of a tid c pl js 0%nat + (16 * V_of a tid c pl js 6%nat + 4096 * V_of a tid c pl js 10%nat) = usp).
      { unfold V_of. rewrite (V'_0 (EB' a tid c pl js)), (V'_6 (EB' a tid c pl js)), (V'_10 (EB' a tid c pl js)) by (cbv beta; rewrite E0; fold usp; lia).
        pose proof (sp_digits (EB' a tid c pl js)) as SD. cbv beta in SD. rewrite E0 in SD. fold usp in SD.
        destruct (SD S16 ltac:(lia)) as [D1 _]. rewrite E0. fold usp. lia. }
      rewrite DG in WR.
      apply wr_at_stk; [replace (usp - (usp - 8388608)) with 8388608 by lia; exact WR|].
      intros x Hx. apply off_img_Z. unfold IMG_HI. lia.
  Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma seg_rom_off : forall segs (a : word), find_segment segs (bv_unsigned a) 1 = None -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.seg_rom segs a = None.
Proof. intros segs a H. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity. Qed.

Lemma in_kn_b : forall K kn, existsb (APC.kentry_eqb K) kn = true -> In K kn.
Proof. intros K kn Hb. apply existsb_exists in Hb as (k & Hk & He). apply KNA.kentry_eqb_eq in He. subst k. exact Hk. Qed.

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  Definition V_of (a tid c : word) (pl : placements) (js : list word) : nat -> Z := uev (tgt_env (EB' a tid c pl js)).

  (* [comment removed for export] *)
  #[using="Type"] Lemma page_of_map : forall E (L : ledger) i n lo hi,
    maps_ok sp E L -> In (EVar i, n) (l_maps L) -> usp <= 2 ^ 47 -> n mod 4096 = 0 ->
    lo <= 1 -> 4096 * hi = 2 ^ 47 - 8388608 - n ->
    bv_unsigned (ev E i) mod 4096 = 0 /\ 4096 * lo <= bv_unsigned (ev E i) <= 4096 * hi.
  Proof.
    intros E L i n lo hi HMO Hin Hsp Hn Hlo Hhi. pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO.
    unfold map_ok in MO. cbn [fst snd edenot] in MO. destruct MO as (M1 & M2 & M3 & M4 & _). unfold stack_max_size in M4. fold usp in M4.
    split; [exact M1|]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma at_main_usp : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl -> usp <= 140737488355136.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & _). destruct HB as [_ HKN _ _ _ _ _ _ _ _ _ _].
    assert (IN : In (KRange (EVar 0) 140735340871680 140737488355136) (if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN))
      by (destruct w1; apply in_kn_b; vmeq_refl).
    pose proof (proj1 (Forall_forall _ _) HKN _ IN) as R0. cbn [kentry_ok edenot] in R0.
    rewrite (ev_EB_sp sp draw inp a tid c pl js) in R0. fold usp in R0. lia.
  Qed.

  #[using="VI VE usp"] Theorem at_main_facts : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (mfact_ok SEGS (V_of a tid c pl js) M) (asan_mem_facts_kn ++ (if w1 then asan_mem_facts_w1 else asan_mem_facts_w2))
    /\ Forall (pfact_ok (V_of a tid c pl js)) (asan_pure_facts_kn ++ (if w1 then asan_pure_facts_w1 else asan_pure_facts_w2)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs
           (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    set (KNw := if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN) in *.
    pose proof HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in S16.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    (* [comment removed for export] *)
    assert (KIN : forall K, existsb (APC.kentry_eqb K) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN && existsb (APC.kentry_eqb K) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN = true ->
                            kentry_ok SEGS E (mrestrict (H_MAIN sp p8 sb p10 p12 a W p24) M) K).
    { intros K HK. apply andb_prop in HK as [K1 K2]. apply (proj1 (Forall_forall _ _) HKN). unfold KNw. destruct w1; apply in_kn_b; assumption. }
    pose proof (KIN (KRange (EVar 0) 140735340871680 140737488355136) ltac:(vmeq_refl)) as R0. cbn [kentry_ok edenot] in R0. rewrite E0 in R0. fold usp in R0.
    (* [comment removed for export] *)
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    assert (KOK : know_ok SEGS (tgt_env E) (mrestrict (H_MAIN sp p8 sb p10 p12 a W p24) M) (vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 KNw)).
    { apply (trx_A3_sound E); [| | | | | | | exact HKN].
      - (* [comment removed for export] *) rewrite E0. exact S16.
      - rewrite E0. fold usp. lia.
      - (* [comment removed for export] *)
        assert (PG : forall i n lo hi, In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 -> lo <= 1 -> 4096 * hi = 2 ^ 47 - 8388608 - n ->
                     bv_unsigned (ev E i) mod 4096 = 0 /\ 4096 * lo <= bv_unsigned (ev E i) <= 4096 * hi)
          by (intros i n lo hi Hin Hn Hlo Hhi; exact (page_of_map E (L_MAIN lb) i n lo hi HMO Hin ltac:(lia) Hn Hlo Hhi)).
        unfold PAGES4. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        + apply (PG 26%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 27%nat 3727360); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + (* [comment removed for export] *)
          destruct (PG 28%nat 137439023104 1 34326181871 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve_e) eq_refl ltac:(lia) eq_refl) as [A1 A2].
          split; [exact A1|]. rewrite E28 in *. unfold SHB_HI in P2. lia.
        + apply (PG 36%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 37%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 38%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 46%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 60%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 83%nat 11571200); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + (* [comment removed for export] *)
          pose proof (KIN (KAlign (EVar 101) 4096) ltac:(vmeq_refl)) as KA.
          pose proof (KIN (KRange (EVar 101) 6307840 1080049664) ltac:(vmeq_refl)) as KR.
          cbn [kentry_ok edenot] in KA, KR. destruct KA as [_ KA]. split; [exact KA | lia].
        + apply (PG 104%nat 1048576); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 105%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 106%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
        + apply (PG 107%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve_e | reflexivity | lia | reflexivity].
      - (* [comment removed for export] *)
        unfold VR_REN. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [unfold RENAMES; cbn [In]; in_solve_e|]).
        + exact (KIN (KRange (EVar 1) 1 1024) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 2) 0 256) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 3) 0 131071) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 4) 0 280000) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 5) 0 4294967294) ltac:(vmeq_refl)).
        + exact (KIN (KRange (EVar 8) 1 4194303) ltac:(vmeq_refl)).
      - (* [comment removed for export] *) rewrite E29, E28, Hsb. unfold SBV. lia.
      - (* [comment removed for export] *) rewrite E62, E0. fold usp.
        unfold STv. fold usp. apply u_small.
        pose proof (Z.div_mod (usp + 3935) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp + 3935) 4096 ltac:(lia)). lia.
      - (* [comment removed for export] *) rewrite E63, E62.
        pose proof (x9_facts sp S16 SLo ltac:(fold usp; lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & _). unfold XLO, XHI in *.
        rewrite !u_small by lia. reflexivity. }
    assert (HID_rom : forall x : word, H_MAIN sp p8 sb p10 p12 a W p24 x = true -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.seg_rom SEGS x = None)
      by (intros x Hx; apply seg_rom_off; exact (HH x Hx)).
    assert (HULL_vis : forall x : word, 65536 <= bv_unsigned x < 6307840 -> H_MAIN sp p8 sb p10 p12 a W p24 x = false).
    { intros x Hx. destruct (H_MAIN sp p8 sb p10 p12 a W p24 x) eqn:EH; [|reflexivity]. exfalso.
      destruct (HIN x EH) as ([e n] & Hin & Hr). cbn [fst snd] in Hr.
      pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd] in MO.
      destruct MO as (_ & _ & _ & _ & MI). unfold A_img_lo, A_img_hi in MI. lia. }
    destruct w1.
    - unfold KNw in KOK. cbv iota in KOK. rewrite KNX1_eq in KOK.
      exact (export_sound SEGS (tgt_env E) _ M KNX1 65536 6307840 KOK HID_rom HULL_vis _ _ asan_mem_facts_justified_w1 asan_pure_facts_justified_w1).
    - unfold KNw in KOK. cbv iota in KOK. rewrite KNX2_eq in KOK.
      exact (export_sound SEGS (tgt_env E) _ M KNX2 65536 6307840 KOK HID_rom HULL_vis _ _ asan_mem_facts_justified_w2 asan_pure_facts_justified_w2).
  Qed.

  (* [comment removed for export] *)
  #[using="sp usp"] Lemma off_img_Z : forall a : Z, IMG_HI <= a < 2 ^ 64 -> find_segment SEGS a 1 = None.
  Proof.
    intros a Ha. pose proof (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                               ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy) (Z_to_bv 64 a)) as X.
    assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_small; unfold IMG_HI in Ha; lia).
    rewrite U in X. apply X. apply Z.leb_le. rewrite U. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem at_main_ro_stk : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    (forall i, 0x10000 <= i < 0xa5000 -> M (wa i) = None)
    /\ stk SEGS M (usp - 8388608) usp.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM.
    destruct (at_main_facts w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM) as [HMF _].
    pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in S16.
    split.
    - intros i Hi. exact (mimg_cover SEGS _ M asan_mem_facts_kn 0x10000 0xa5000 HMFc ltac:(vmeq_refl) i Hi).
    - pose proof (mwr_find SEGS _ M asan_mem_facts_kn
                    (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
                    HMFc ltac:(vmeq_refl)) as WR.
      cbn [zv] in WR.
      (* [comment removed for export] *)
      pose proof (at_main_usp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as ULT.
      assert (E0 : ev (EB' a tid c pl js) 0%nat = sp) by apply ev_EB_sp.
      assert (DG : 32768 * V_of a tid c pl js 0%nat + (16 * V_of a tid c pl js 6%nat + 4096 * V_of a tid c pl js 10%nat) = usp).
      { unfold V_of. rewrite (V'_0 (EB' a tid c pl js)), (V'_6 (EB' a tid c pl js)), (V'_10 (EB' a tid c pl js)) by (cbv beta; rewrite E0; fold usp; lia).
        pose proof (sp_digits (EB' a tid c pl js)) as SD. cbv beta in SD. rewrite E0 in SD. fold usp in SD.
        destruct (SD S16 ltac:(lia)) as [D1 _]. rewrite E0. fold usp. lia. }
      rewrite DG in WR.
      apply wr_at_stk; [replace (usp - (usp - 8388608)) with 8388608 by lia; exact WR|].
      intros x Hx. apply off_img_Z. unfold IMG_HI. lia.
  Qed.
End Entry.
End TwB.
End MainEntry.

(* [comment removed for export] *)
Module MainReadyA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot2 BootS1 BootS2 BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS5 BootS6 BootS7 BootS8 BootState. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RelSpec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require A3Kn MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainAux MainShadow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require RegsEqv0__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.RegsEqv0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.SrzEqv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac in_solve := repeat (first [left; lazymatch goal with
    | |- (?x1, ?y1) = (?x2, ?y2) =>   (* [comment removed for export] *)
        tryif (let c := eval vm_compute in (Nat.eqb y1 y2) in lazymatch c with false => idtac end) then fail else reflexivity
    | |- _ => reflexivity end | right]).
(* [comment removed for export] *)
Lemma in_nat2_b : forall (x : nat * nat) (l : list (nat * nat)),
  existsb (fun y => andb (Nat.eqb (fst y) (fst x)) (Nat.eqb (snd y) (snd x))) l = true -> In x l.
Proof.
  intros [a b] l. induction l as [|[c d] l IH]; cbn [existsb fst snd In]; [discriminate|].
  intros H. apply Bool.orb_true_iff in H as [H|H].
  - left. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1, H2. subst. reflexivity.
  - right. exact (IH H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMAIN : Z := 0x84120.           (* [comment removed for export] *)
Definition ARA : Z := 0x940c4.             (* [comment removed for export] *)
Definition AGP : Z := 0x10800.             (* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.         (* [comment removed for export] *)
Definition AIMG_HI : Z := 0x603000.
Definition KHIGH : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition ASHOFF : Z := 0x7fff8000.       (* [comment removed for export] *)

Lemma AMAIN_eq : AMAIN = A_main. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Definition mkRl (l : list word) : bvmap 5 word :=
  mkR (nth 0 l w0) (nth 1 l w0) (nth 2 l w0) (nth 3 l w0) (nth 4 l w0) (nth 5 l w0) (nth 6 l w0) (nth 7 l w0) (nth 8 l w0) (nth 9 l w0)
      (nth 10 l w0) (nth 11 l w0) (nth 12 l w0) (nth 13 l w0) (nth 14 l w0) (nth 15 l w0) (nth 16 l w0) (nth 17 l w0) (nth 18 l w0) (nth 19 l w0)
      (nth 20 l w0) (nth 21 l w0) (nth 22 l w0) (nth 23 l w0) (nth 24 l w0) (nth 25 l w0) (nth 26 l w0) (nth 27 l w0) (nth 28 l w0) (nth 29 l w0)
      (nth 30 l w0).

Lemma regs_eqv0_mkRl : forall (R : bvmap 5 word) (l : list word),
  (forall n, (1 <= n <= 31)%nat -> reg_get R (Z_to_bv 5 (Z.of_nat n)) = nth (n - 1) l w0) ->
  regs_eqv0 R (mkRl l).
Proof.
  intros R l H r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [vm_compute in Hr; discriminate|].
  rewrite (H (Datatypes.S n) ltac:(lia)).
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma add_lit : forall (w : word) k, (w + Z_to_bv 64 k)%bv = Z_to_bv 64 (bv_unsigned w + k).
Proof.
  intros w k. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma add_mul_lit : forall (w : word) c k, (w + Z_to_bv 64 c * Z_to_bv 64 k)%bv = Z_to_bv 64 (bv_unsigned w + c * k).
Proof.
  intros w c k. apply bv_eq. rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. rewrite <- (Zplus_mod_idemp_r (c mod bv_modulus 64 * (k mod bv_modulus 64))), <- Zmult_mod, Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition main_regs (usp argc tpv : Z) (t3 t4 t5 : Z) : list word :=
  [Z_to_bv 64 ARA; Z_to_bv 64 (usp - 48); Z_to_bv 64 AGP; Z_to_bv 64 tpv;
   Z_to_bv 64 4611686018427387904; Z_to_bv 64 0; Z_to_bv 64 1152921504606846976;
   Z_to_bv 64 (usp + 8); Z_to_bv 64 argc; Z_to_bv 64 argc; Z_to_bv 64 (usp + 8);
   Z_to_bv 64 (usp + 8 * argc + 16); Z_to_bv 64 6917529027641081856;
   Z_to_bv 64 12682135451164737535; Z_to_bv 64 17293822569102704639; Z_to_bv 64 1152920405095219200; Z_to_bv 64 18446742974197923840;
   Z_to_bv 64 AMAIN; Z_to_bv 64 (usp + 8 * argc + 16);
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 t3; Z_to_bv 64 t4; Z_to_bv 64 t5].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition STKSH_BASE : zexp := ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304).
Definition STKSH_LEN : zexp := ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992).
Definition asan_mem_facts_d : list mfact :=
  [MWrS STKSH_BASE STKSH_LEN; MZeroS STKSH_BASE STKSH_LEN;
   (* [comment removed for export] *)
   MWr (ZMul (ZLit 4096) (ZV 470)) 8388608; MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 4096)) 8384512].

(* [comment removed for export] *)
Definition STKWIN_BASE : zexp := ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)).
Definition STKWIN_LEN : Z := 140737496743936.
Definition win_blocks : list (zexp * Z) :=
  [(ZMul (ZLit 4096) (ZV 568), 4096); (ZMul (ZLit 4096) (ZV 487), 4096); (ZMul (ZLit 4096) (ZV 470), 8388608);
   (ZMul (ZLit 4096) (ZV 469), 1048576); (ZMul (ZLit 4096) (ZV 393), 11571200); (ZMul (ZLit 4096) (ZV 310), 4096);
   (ZMul (ZLit 4096) (ZV 245), 4096); (ZMul (ZLit 4096) (ZV 228), 65536); (ZMul (ZLit 4096) (ZV 227), 4096);
   (ZMul (ZLit 4096) (ZV 226), 8388608); (ZMul (ZLit 4096) (ZV 208), 137439023104); (ZMul (ZLit 4096) (ZV 207), 3727360);
   (ZMul (ZLit 4096) (ZV 78), 65536); (ZV 1103, 4096); (ZV 1102, 8192)].
Definition asan_pure_facts_win : list pfact := List.map (fun bn => PDisj (fst bn) (snd bn) STKWIN_BASE STKWIN_LEN) win_blocks.
(* [comment removed for export] *)
Definition asan_pure_facts_x : list pfact :=
  [PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0;
   PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095].
Definition asan_pure_facts_d : list pfact :=
  asan_pure_facts_win ++ asan_pure_facts_x ++ psym (asan_pure_facts_kn ++ asan_pure_facts_win) ++ all_pairs asan_ledger.

(* [comment removed for export] *)
Definition asan_mem_facts_w (w : bool) : list mfact := if w then asan_mem_facts_w1 else asan_mem_facts_w2.
Definition asan_pure_facts_w (w : bool) : list pfact := if w then asan_pure_facts_w1 else asan_pure_facts_w2.
(* [comment removed for export] *)
Definition asan_mem_facts : list mfact := asan_mem_facts_kn ++ asan_mem_facts_d.
Definition asan_pure_facts : list pfact := asan_pure_facts_kn ++ asan_pure_facts_d.

(* [comment removed for export] *)
Definition Wblk (en : ExecEntry) (inp : ProcInput) : Z :=
  (Z.of_nat (length (build_stack_bytes PH (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) - 16
   - (8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 184)) / 8.

(* [comment removed for export] *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (usp + 8 * argc + 8 * envc + 184 <= a < usp + 8 * argc + 8 * envc + 184 + 8 * Wblk en inp).

(* [comment removed for export] *)
Definition ashadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition ashadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn asan_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
(* [comment removed for export] *)
Definition ashadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, ashadow a -> ~ ashadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition ashadow_exposed (V : nat -> Z) (a : Z) : Prop :=
  (0x7fffa000 <= a < 0x7fffa000 + 779776)
  \/ (ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 <= a < ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 + 512)
  \/ (ASHOFF + 4096 * V 228%nat / 8 <= a < ASHOFF + 4096 * V 228%nat / 8 + 8192)
  \/ (V 1084%nat <= a < V 1084%nat + 8) \/ (V 1085%nat <= a < V 1085%nat + 8).
Definition ashadow1 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, ashadow a -> ~ ashadow_exposed V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Record amodel (V : nat -> Z) (en : ExecEntry) (inp : ProcInput) (lim : Z) (mo : Model) : Prop := AMODEL {
  am_halted   : m_halted mo = None;
  am_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  am_fs       : m_fs mo = in_fs inp;
  am_reserved : vm_reserved (m_vmmaps mo) = segments_reserved SEGS;
  am_limit    : vm_limit (m_vmmaps mo) = lim;
  am_brk      : exists lb, (lb = 0 \/ lb = 8192) /\ vm_brk (m_vmmaps mo) = Z_to_bv 64 (bv_unsigned (en_brk en) + lb);
  am_start_brk : vm_start_brk (m_vmmaps mo) = en_brk en;
  am_top      : vm_init_sp (m_vmmaps mo) = en_sp en;
  am_usp      : 0x7fff80000000 <= bv_unsigned (en_sp en) /\ bv_unsigned (en_sp en) <= 0x800000000000 /\ bv_unsigned (en_sp en) mod 16 = 0;
  am_mmap_base : vm_mmap_base (m_vmmaps mo) = en_mmap_base en;
  (* [comment removed for export] *)
  am_maps     : ledger_den V asan_ledger (vm_maps (m_vmmaps mo));
  am_sep      : ivs_sep (vm_maps (m_vmmaps mo));
  am_bounds   : Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                  /\ 0 < bv_unsigned (fst iv)
                                  /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (en_sp en) - 8388608)
                       (vm_maps (m_vmmaps mo));
  am_lazy_bounds : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (en_sp en) - 8388608)
                          (m_vm_lazy mo);
  am_noaccess_wf : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 64) (vm_noaccess (m_vmmaps mo));
  am_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= asan_totsz;
  (* [comment removed for export] *)
  am_nonlazy  : eager_used mo <= asan_eager;      (* [comment removed for export] *)
  am_abytes   : ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes;
  am_budget   : eager_used mo + ivz_bytes (allow_of ASHOFF V asan_vis) <= lim;
  am_allow_wf : ivz_wf (allow_of ASHOFF V asan_vis);
  am_mat_nodup : List.NoDup (m_vm_materialized mo);
  am_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V asan_vis) p;
  (* [comment removed for export] *)
  am_noabs    : RelSpec.fs_noabs (m_fs mo);
  am_tid      : forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE;
  am_ivs_wf   : model_ivs_wf mo;
  am_sh_lo    : NodesA.sh_entry_ok (m_vmmaps mo) (0x7fff7000, 0x10000000);
  am_sh_hi    : NodesA.sh_entry_ok (m_vmmaps mo) (0x2008fff7000, 0xdfff0001000)
}.

Definition amain_open (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkRl (main_regs usp argc 6165944 (V 1098%nat) (V 1099%nat) (V 1100%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom SEGS)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok SEGS V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv SEGS m
    /\ stk SEGS m (usp - 8388608) usp
    /\ (forall a, usp <= a < 2 ^ 64 ->
          m (wa a) = wrap_mem PH (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodel V en inp lim mo
    /\ ashadow1 V m.

Definition amain_at (en : ExecEntry) (inp : ProcInput) (lim : Z) (ms : machine_state) (mo : Model) : Prop :=
  exists (w : bool) (V : nat -> Z) (m : word -> option byte), amain_open en inp lim w V m ms mo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_pages : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (fun q => bv_unsigned (ev (EB' a tid c pl js) (fst (fst (fst q)))) mod 4096 = 0
                     /\ 4096 * snd (fst q) <= bv_unsigned (ev (EB' a tid c pl js) (fst (fst (fst q)))) <= 4096 * snd q) PAGES4.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl
           (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    set (KNw := if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN else A3.BootKn11w2.KN_MAIN) in *.
    pose proof HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    assert (KIN : forall K, existsb (APC.kentry_eqb K) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN && existsb (APC.kentry_eqb K) A3.BootKn11w2.KN_MAIN = true ->
                            kentry_ok SEGS E (mrestrict (H_MAIN sp p8 sb p10 p12 a W p24) M) K).
    { intros K HK. apply andb_prop in HK as [K1 K2]. apply (proj1 (Forall_forall _ _) HKN). unfold KNw. destruct w1; apply in_kn_b; assumption. }
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    assert (PG : forall i n lo hi, In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 -> lo <= 1 -> 4096 * hi = 2 ^ 47 - 8388608 - n ->
                 bv_unsigned (ev E i) mod 4096 = 0 /\ 4096 * lo <= bv_unsigned (ev E i) <= 4096 * hi)
      by (intros i n lo hi Hin Hn Hlo Hhi; exact (page_of_map sp E (L_MAIN lb) i n lo hi HMO Hin ltac:(fold usp; lia) Hn Hlo Hhi)).
    unfold PAGES4. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + apply (PG 26%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 27%nat 3727360); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + destruct (PG 28%nat 137439023104 1 34326181871 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) eq_refl ltac:(lia) eq_refl) as [A1 A2].
      split; [exact A1|]. rewrite E28 in *. unfold SHB_HI in P2. lia.
    + apply (PG 36%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 37%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 38%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 46%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 60%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 83%nat 11571200); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + pose proof (KIN (KAlign (EVar 101) 4096) ltac:(vmeq_refl)) as KA.
      pose proof (KIN (KRange (EVar 101) 6303744 1080045568) ltac:(vmeq_refl)) as KR.
      cbn [kentry_ok edenot] in KA, KR. destruct KA as [_ KA]. split; [exact KA | lia].
    + apply (PG 104%nat 1048576); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 105%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 106%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 107%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma V_page_addr : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall i k, In (i, k) PAGES -> 4096 * V_of sp draw inp a tid c pl js k = bv_unsigned (ev (EB' a tid c pl js) i).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM i k Hin.
    pose proof (at_main_pages _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as HAL.
    unfold V_of. rewrite (V'_page (EB' a tid c pl js) i k Hin).
    destruct (page_in4 i k Hin) as (lo & hi & H4). destruct (proj1 (Forall_forall _ _) HAL _ H4) as [A _]. cbn [fst snd] in A.
    pose proof (Z.div_mod (bv_unsigned (ev (EB' a tid c pl js) i)) 4096 ltac:(lia)) as DM. rewrite A in DM. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE envc"] Lemma at_main_regs : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    regs_eqv0 R (mkRl (main_regs usp argc 6165944 (V 1098%nat) (V 1099%nat) (V 1100%nat))).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    assert (E0 : ev (EB' a tid c pl js) 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev (EB' a tid c pl js) 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K98 : ev (EB' a tid c pl js) 98%nat = Z_to_bv 64 (V 1098%nat))
      by (unfold V, V_of; change 1098%nat with (KEEP + 98)%nat; rewrite (V'_keep (EB' a tid c pl js) HSP 98); symmetry; apply Z_to_bv_bv_unsigned).
    assert (K99 : ev (EB' a tid c pl js) 99%nat = Z_to_bv 64 (V 1099%nat))
      by (unfold V, V_of; change 1099%nat with (KEEP + 99)%nat; rewrite (V'_keep (EB' a tid c pl js) HSP 99); symmetry; apply Z_to_bv_bv_unsigned).
    assert (K100 : ev (EB' a tid c pl js) 100%nat = Z_to_bv 64 (V 1100%nat))
      by (unfold V, V_of; change 1100%nat with (KEEP + 100)%nat; rewrite (V'_keep (EB' a tid c pl js) HSP 100); symmetry; apply Z_to_bv_bv_unsigned).
    assert (E1 : ev (EB' a tid c pl js) 1%nat = Z_to_bv 64 argc) by reflexivity.
    assert (E7 : ev (EB' a tid c pl js) 7%nat = a) by reflexivity.
    assert (ARGC : 1 <= argc <= 1024) by (destruct VI as ((A1 & _) & _); exact A1).
    destruct HM as (HB & _). destruct HB as [HR _ _ _ _ _ _ _ _ _ _ _].
    assert (HR' : regs_ok (EB' a tid c pl js) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.SR_MAIN R) by (destruct w1; exact HR).
    clear HR. apply regs_eqv0_mkRl. intros n Hn.
    assert (Hin : In n (seq 1 31)) by (apply in_seq; lia). cbn [seq] in Hin. clear Hn.
    repeat (destruct Hin as [<-|Hin];
      [ match goal with |- reg_get R ?r = _ =>
          pose proof (HR' r) as G; unfold getr in G; change (bv_eqb r 0) with false in G; cbv iota in G; rewrite G; clear G;
          let e := eval vm_compute in (sr_get OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.SR_MAIN r) in change (sr_get OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.SR_MAIN r) with e
        end;
        cbn [edenot nth main_regs Nat.sub]; rewrite ?E0, ?E1, ?E7, ?K98, ?K99, ?K100;
        first [ reflexivity
              | change (alu64 Instr.ALU_ADD ?x ?y) with (x + y)%bv; rewrite add_lit; f_equal; fold usp; lia
              | change (alu64 Instr.ALU_ADD (alu64 Instr.ALU_ADD ?x (mul_div Instr.M_MUL ?c ?k)) ?y) with ((x + c * k) + y)%bv;
                rewrite add_mul_lit, add_lit, Z_to_bv_unsigned, bv_wrap_small by (fold usp; unfold bv_modulus; lia); f_equal; fold usp; lia ] |]).
    destruct Hin.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Lemma at_main_pins : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned brk / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    set (E := EB' a tid c pl js).
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (H16 : bv_unsigned (ev E 0%nat) mod 16 = 0) by (rewrite E0; exact S16).
    destruct VI as (VA & VEn & _). pose proof VA as ((A1 & A2) & _). pose proof VEn as (B1 & _).
    pose proof (W_range PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) VA VEn) as (W1 & _ & W2).
    pose proof (L0_range PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) VA) as L0R.
    destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E101 & _). fold E in E101.
    split; [intros n; unfold V, V_of, uev; apply u64_range|].
    unfold V, V_of. fold E.
    rewrite (V'_0 E HSP), (V'_6 E), (V'_10 E), E0. fold usp.
    pose proof (sp_digits E H16 HSP) as [SD _]. rewrite E0 in SD. fold usp in SD.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    rewrite (V'_ren E 1 1 ltac:(unfold RENAMES; cbn [In]; in_solve)), (V'_ren E 2 2 ltac:(unfold RENAMES; cbn [In]; in_solve)),
            (V'_ren E 3 3 ltac:(unfold RENAMES; cbn [In]; in_solve)), (V'_ren E 4 4 ltac:(unfold RENAMES; cbn [In]; in_solve)),
            (V'_ren E 5 8 ltac:(unfold RENAMES; cbn [In]; in_solve)), (V'_ren E 6 9 ltac:(unfold RENAMES; cbn [In]; in_solve)),
            (V'_page E 101 5 ltac:(apply in_nat2_b; vmeq_refl)), E101.
    split; [change (ev E 1%nat) with (Z_to_bv 64 argc); apply u_small; unfold argc; lia|].
    split; [change (ev E 2%nat) with (Z_to_bv 64 envc); apply u_small; unfold envc; lia|].
    split; [apply u_small; lia|].
    split; [change (ev E 4%nat) with (Z_to_bv 64 (Wblk en inp)); apply u_small; unfold Wblk; cbn [en_sp en_draw]; lia|].
    split; [reflexivity|]. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="sp inp usp argc envc"] Lemma ro_addr_SEGS : forall x : word, ro_addr SEGS x = true -> 0x10000 <= bv_unsigned x < 0xa4000.
  Proof.
    intros x H. unfold ro_addr in H.
    assert (FS' : find_segment SEGS (bv_unsigned x) 1 =
      if (0x10000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0x32000) then Some Asan_segment_000
      else if (0x32000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0xa4000) then Some Asan_segment_001
      else if (0xa4000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0xa7000) then Some Asan_segment_002
      else if (0xa7000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0x603000) then Some Asan_segment_003
      else None) by reflexivity.
    rewrite FS' in H. clear FS'.
    destruct (Z_lt_ge_dec (bv_unsigned x) 0x10000) as [L|L]; [|destruct (Z_lt_ge_dec (bv_unsigned x) 0xa4000) as [L2|L2]; [lia|]]; exfalso.
    - rewrite (proj2 (Z.leb_gt 0x10000 _)), (proj2 (Z.leb_gt 0x32000 _)), (proj2 (Z.leb_gt 0xa4000 _)), (proj2 (Z.leb_gt 0xa7000 _)) in H by lia.
      cbn [andb] in H. discriminate.
    - rewrite (proj2 (Z.leb_gt _ 0x32000)), (proj2 (Z.leb_gt _ 0xa4000)) in H by lia. rewrite !andb_false_r in H.
      destruct ((0xa4000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0xa7000)); [vm_compute in H; discriminate|].
      destruct ((0xa7000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0x603000)); [vm_compute in H; discriminate| discriminate].
  Qed.

  #[using="VI VE usp argc envc"] Lemma at_main_mem_inv : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    mem_inv SEGS M.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM x b Hx.
    destruct (at_main_ro_stk sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [RO _].
    destruct (ro_addr SEGS x) eqn:ER; [|reflexivity]. exfalso.
    pose proof (RO _ (ro_addr_SEGS x ER)) as N. unfold wa in N. rewrite Z_to_bv_bv_unsigned in N. congruence.
  Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.RegsEqv0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.SrzEqv.TwB.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac in_solve := repeat (first [left; lazymatch goal with
    | |- (?x1, ?y1) = (?x2, ?y2) =>   (* [comment removed for export] *)
        tryif (let c := eval vm_compute in (Nat.eqb y1 y2) in lazymatch c with false => idtac end) then fail else reflexivity
    | |- _ => reflexivity end | right]).
(* [comment removed for export] *)
Lemma in_nat2_b : forall (x : nat * nat) (l : list (nat * nat)),
  existsb (fun y => andb (Nat.eqb (fst y) (fst x)) (Nat.eqb (snd y) (snd x))) l = true -> In x l.
Proof.
  intros [a b] l. induction l as [|[c d] l IH]; cbn [existsb fst snd In]; [discriminate|].
  intros H. apply Bool.orb_true_iff in H as [H|H].
  - left. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1, H2. subst. reflexivity.
  - right. exact (IH H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMAIN : Z := 0x84188.           (* [comment removed for export] *)
Definition ARA : Z := 0x944a8.             (* [comment removed for export] *)
Definition AGP : Z := 0x10800.             (* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.         (* [comment removed for export] *)
Definition AIMG_HI : Z := 0x604000.
Definition KHIGH : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition ASHOFF : Z := 0x7fff8000.       (* [comment removed for export] *)

Lemma AMAIN_eq : AMAIN = A_main. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Definition mkRl (l : list word) : bvmap 5 word :=
  mkR (nth 0 l w0) (nth 1 l w0) (nth 2 l w0) (nth 3 l w0) (nth 4 l w0) (nth 5 l w0) (nth 6 l w0) (nth 7 l w0) (nth 8 l w0) (nth 9 l w0)
      (nth 10 l w0) (nth 11 l w0) (nth 12 l w0) (nth 13 l w0) (nth 14 l w0) (nth 15 l w0) (nth 16 l w0) (nth 17 l w0) (nth 18 l w0) (nth 19 l w0)
      (nth 20 l w0) (nth 21 l w0) (nth 22 l w0) (nth 23 l w0) (nth 24 l w0) (nth 25 l w0) (nth 26 l w0) (nth 27 l w0) (nth 28 l w0) (nth 29 l w0)
      (nth 30 l w0).

Lemma regs_eqv0_mkRl : forall (R : bvmap 5 word) (l : list word),
  (forall n, (1 <= n <= 31)%nat -> reg_get R (Z_to_bv 5 (Z.of_nat n)) = nth (n - 1) l w0) ->
  regs_eqv0 R (mkRl l).
Proof.
  intros R l H r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [vm_compute in Hr; discriminate|].
  rewrite (H (Datatypes.S n) ltac:(lia)).
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma add_lit : forall (w : word) k, (w + Z_to_bv 64 k)%bv = Z_to_bv 64 (bv_unsigned w + k).
Proof.
  intros w k. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma add_mul_lit : forall (w : word) c k, (w + Z_to_bv 64 c * Z_to_bv 64 k)%bv = Z_to_bv 64 (bv_unsigned w + c * k).
Proof.
  intros w c k. apply bv_eq. rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. rewrite <- (Zplus_mod_idemp_r (c mod bv_modulus 64 * (k mod bv_modulus 64))), <- Zmult_mod, Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition main_regs (usp argc tpv : Z) (t3 t4 t5 : Z) : list word :=
  [Z_to_bv 64 ARA; Z_to_bv 64 (usp - 48); Z_to_bv 64 AGP; Z_to_bv 64 tpv;
   Z_to_bv 64 4611686018427387904; Z_to_bv 64 0; Z_to_bv 64 1152921504606846976;
   Z_to_bv 64 (usp + 8); Z_to_bv 64 argc; Z_to_bv 64 argc; Z_to_bv 64 (usp + 8);
   Z_to_bv 64 (usp + 8 * argc + 16); Z_to_bv 64 6917529027641081856;
   Z_to_bv 64 12682135451164737535; Z_to_bv 64 17293822569102704639; Z_to_bv 64 1152920405095219200; Z_to_bv 64 18446742974197923840;
   Z_to_bv 64 AMAIN; Z_to_bv 64 (usp + 8 * argc + 16);
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 t3; Z_to_bv 64 t4; Z_to_bv 64 t5].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition STKSH_BASE : zexp := ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304).
Definition STKSH_LEN : zexp := ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992).
Definition asan_mem_facts_d : list mfact :=
  [MWrS STKSH_BASE STKSH_LEN; MZeroS STKSH_BASE STKSH_LEN;
   (* [comment removed for export] *)
   MWr (ZMul (ZLit 4096) (ZV 470)) 8388608; MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 4096)) 8384512].

(* [comment removed for export] *)
Definition STKWIN_BASE : zexp := ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)).
Definition STKWIN_LEN : Z := 140737496743936.
Definition win_blocks : list (zexp * Z) :=
  [(ZMul (ZLit 4096) (ZV 568), 4096); (ZMul (ZLit 4096) (ZV 487), 4096); (ZMul (ZLit 4096) (ZV 470), 8388608);
   (ZMul (ZLit 4096) (ZV 469), 1048576); (ZMul (ZLit 4096) (ZV 393), 11571200); (ZMul (ZLit 4096) (ZV 310), 4096);
   (ZMul (ZLit 4096) (ZV 245), 4096); (ZMul (ZLit 4096) (ZV 228), 65536); (ZMul (ZLit 4096) (ZV 227), 4096);
   (ZMul (ZLit 4096) (ZV 226), 8388608); (ZMul (ZLit 4096) (ZV 208), 137439023104); (ZMul (ZLit 4096) (ZV 207), 3727360);
   (ZMul (ZLit 4096) (ZV 78), 65536); (ZV 1103, 4096); (ZV 1102, 8192)].
Definition asan_pure_facts_win : list pfact := List.map (fun bn => PDisj (fst bn) (snd bn) STKWIN_BASE STKWIN_LEN) win_blocks.
(* [comment removed for export] *)
Definition asan_pure_facts_x : list pfact :=
  [PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0;
   PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095].
Definition asan_pure_facts_d : list pfact :=
  asan_pure_facts_win ++ asan_pure_facts_x ++ psym (asan_pure_facts_kn ++ asan_pure_facts_win) ++ all_pairs asan_ledger.

(* [comment removed for export] *)
Definition asan_mem_facts_w (w : bool) : list mfact := if w then asan_mem_facts_w1 else asan_mem_facts_w2.
Definition asan_pure_facts_w (w : bool) : list pfact := if w then asan_pure_facts_w1 else asan_pure_facts_w2.
(* [comment removed for export] *)
Definition asan_mem_facts : list mfact := asan_mem_facts_kn ++ asan_mem_facts_d.
Definition asan_pure_facts : list pfact := asan_pure_facts_kn ++ asan_pure_facts_d.

(* [comment removed for export] *)
Definition Wblk (en : ExecEntry) (inp : ProcInput) : Z :=
  (Z.of_nat (length (build_stack_bytes PH (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) - 16
   - (8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 184)) / 8.

(* [comment removed for export] *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (usp + 8 * argc + 8 * envc + 184 <= a < usp + 8 * argc + 8 * envc + 184 + 8 * Wblk en inp).

(* [comment removed for export] *)
Definition ashadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition ashadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn asan_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
(* [comment removed for export] *)
Definition ashadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, ashadow a -> ~ ashadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition ashadow_exposed (V : nat -> Z) (a : Z) : Prop :=
  (0x7fffa000 <= a < 0x7fffa000 + 780288)
  \/ (ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 <= a < ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 + 512)
  \/ (ASHOFF + 4096 * V 228%nat / 8 <= a < ASHOFF + 4096 * V 228%nat / 8 + 8192)
  \/ (V 1084%nat <= a < V 1084%nat + 8) \/ (V 1085%nat <= a < V 1085%nat + 8).
Definition ashadow1 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, ashadow a -> ~ ashadow_exposed V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Record amodel (V : nat -> Z) (en : ExecEntry) (inp : ProcInput) (lim : Z) (mo : Model) : Prop := AMODEL {
  am_halted   : m_halted mo = None;
  am_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  am_fs       : m_fs mo = in_fs inp;
  am_reserved : vm_reserved (m_vmmaps mo) = segments_reserved SEGS;
  am_limit    : vm_limit (m_vmmaps mo) = lim;
  am_brk      : exists lb, (lb = 0 \/ lb = 8192) /\ vm_brk (m_vmmaps mo) = Z_to_bv 64 (bv_unsigned (en_brk en) + lb);
  am_start_brk : vm_start_brk (m_vmmaps mo) = en_brk en;
  am_top      : vm_init_sp (m_vmmaps mo) = en_sp en;
  am_usp      : 0x7fff80000000 <= bv_unsigned (en_sp en) /\ bv_unsigned (en_sp en) <= 0x800000000000 /\ bv_unsigned (en_sp en) mod 16 = 0;
  am_mmap_base : vm_mmap_base (m_vmmaps mo) = en_mmap_base en;
  (* [comment removed for export] *)
  am_maps     : ledger_den V asan_ledger (vm_maps (m_vmmaps mo));
  am_sep      : ivs_sep (vm_maps (m_vmmaps mo));
  am_bounds   : Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                  /\ 0 < bv_unsigned (fst iv)
                                  /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (en_sp en) - 8388608)
                       (vm_maps (m_vmmaps mo));
  am_lazy_bounds : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (en_sp en) - 8388608)
                          (m_vm_lazy mo);
  am_noaccess_wf : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 64) (vm_noaccess (m_vmmaps mo));
  am_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= asan_totsz;
  (* [comment removed for export] *)
  am_nonlazy  : eager_used mo <= asan_eager;      (* [comment removed for export] *)
  am_abytes   : ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes;
  am_budget   : eager_used mo + ivz_bytes (allow_of ASHOFF V asan_vis) <= lim;
  am_allow_wf : ivz_wf (allow_of ASHOFF V asan_vis);
  am_mat_nodup : List.NoDup (m_vm_materialized mo);
  am_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V asan_vis) p;
  (* [comment removed for export] *)
  am_noabs    : RelSpec.fs_noabs (m_fs mo);
  am_tid      : forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE;
  am_ivs_wf   : model_ivs_wf mo;
  am_sh_lo    : NodesA.sh_entry_ok (m_vmmaps mo) (0x7fff7000, 0x10000000);
  am_sh_hi    : NodesA.sh_entry_ok (m_vmmaps mo) (0x2008fff7000, 0xdfff0001000)
}.

Definition amain_open (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkRl (main_regs usp argc 6166968 (V 1098%nat) (V 1099%nat) (V 1100%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom SEGS)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok SEGS V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv SEGS m
    /\ stk SEGS m (usp - 8388608) usp
    /\ (forall a, usp <= a < 2 ^ 64 ->
          m (wa a) = wrap_mem PH (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodel V en inp lim mo
    /\ ashadow1 V m.

Definition amain_at (en : ExecEntry) (inp : ProcInput) (lim : Z) (ms : machine_state) (mo : Model) : Prop :=
  exists (w : bool) (V : nat -> Z) (m : word -> option byte), amain_open en inp lim w V m ms mo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_pages : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (fun q => bv_unsigned (ev (EB' a tid c pl js) (fst (fst (fst q)))) mod 4096 = 0
                     /\ 4096 * snd (fst q) <= bv_unsigned (ev (EB' a tid c pl js) (fst (fst (fst q)))) <= 4096 * snd q) PAGES4.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl
           (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    set (KNw := if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN) in *.
    pose proof HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    assert (KIN : forall K, existsb (APC.kentry_eqb K) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN && existsb (APC.kentry_eqb K) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN = true ->
                            kentry_ok SEGS E (mrestrict (H_MAIN sp p8 sb p10 p12 a W p24) M) K).
    { intros K HK. apply andb_prop in HK as [K1 K2]. apply (proj1 (Forall_forall _ _) HKN). unfold KNw. destruct w1; apply in_kn_b; assumption. }
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    assert (PG : forall i n lo hi, In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 -> lo <= 1 -> 4096 * hi = 2 ^ 47 - 8388608 - n ->
                 bv_unsigned (ev E i) mod 4096 = 0 /\ 4096 * lo <= bv_unsigned (ev E i) <= 4096 * hi)
      by (intros i n lo hi Hin Hn Hlo Hhi; exact (page_of_map sp E (L_MAIN lb) i n lo hi HMO Hin ltac:(fold usp; lia) Hn Hlo Hhi)).
    unfold PAGES4. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + apply (PG 26%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 27%nat 3727360); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + destruct (PG 28%nat 137439023104 1 34326181871 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) eq_refl ltac:(lia) eq_refl) as [A1 A2].
      split; [exact A1|]. rewrite E28 in *. unfold SHB_HI in P2. lia.
    + apply (PG 36%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 37%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 38%nat 65536); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 46%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 60%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 83%nat 11571200); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + pose proof (KIN (KAlign (EVar 101) 4096) ltac:(vmeq_refl)) as KA.
      pose proof (KIN (KRange (EVar 101) 6307840 1080049664) ltac:(vmeq_refl)) as KR.
      cbn [kentry_ok edenot] in KA, KR. destruct KA as [_ KA]. split; [exact KA | lia].
    + apply (PG 104%nat 1048576); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 105%nat 8388608); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 106%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
    + apply (PG 107%nat 4096); [rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity | lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma V_page_addr : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall i k, In (i, k) PAGES -> 4096 * V_of sp draw inp a tid c pl js k = bv_unsigned (ev (EB' a tid c pl js) i).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM i k Hin.
    pose proof (at_main_pages _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as HAL.
    unfold V_of. rewrite (V'_page (EB' a tid c pl js) i k Hin).
    destruct (page_in4 i k Hin) as (lo & hi & H4). destruct (proj1 (Forall_forall _ _) HAL _ H4) as [A _]. cbn [fst snd] in A.
    pose proof (Z.div_mod (bv_unsigned (ev (EB' a tid c pl js) i)) 4096 ltac:(lia)) as DM. rewrite A in DM. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE envc"] Lemma at_main_regs : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    regs_eqv0 R (mkRl (main_regs usp argc 6166968 (V 1098%nat) (V 1099%nat) (V 1100%nat))).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    assert (E0 : ev (EB' a tid c pl js) 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev (EB' a tid c pl js) 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K98 : ev (EB' a tid c pl js) 98%nat = Z_to_bv 64 (V 1098%nat))
      by (unfold V, V_of; change 1098%nat with (KEEP + 98)%nat; rewrite (V'_keep (EB' a tid c pl js) HSP 98); symmetry; apply Z_to_bv_bv_unsigned).
    assert (K99 : ev (EB' a tid c pl js) 99%nat = Z_to_bv 64 (V 1099%nat))
      by (unfold V, V_of; change 1099%nat with (KEEP + 99)%nat; rewrite (V'_keep (EB' a tid c pl js) HSP 99); symmetry; apply Z_to_bv_bv_unsigned).
    assert (K100 : ev (EB' a tid c pl js) 100%nat = Z_to_bv 64 (V 1100%nat))
      by (unfold V, V_of; change 1100%nat with (KEEP + 100)%nat; rewrite (V'_keep (EB' a tid c pl js) HSP 100); symmetry; apply Z_to_bv_bv_unsigned).
    assert (E1 : ev (EB' a tid c pl js) 1%nat = Z_to_bv 64 argc) by reflexivity.
    assert (E7 : ev (EB' a tid c pl js) 7%nat = a) by reflexivity.
    assert (ARGC : 1 <= argc <= 1024) by (destruct VI as ((A1 & _) & _); exact A1).
    destruct HM as (HB & _). destruct HB as [HR _ _ _ _ _ _ _ _ _ _ _].
    assert (HR' : regs_ok (EB' a tid c pl js) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.SR_MAIN R) by (destruct w1; exact HR).
    clear HR. apply regs_eqv0_mkRl. intros n Hn.
    assert (Hin : In n (seq 1 31)) by (apply in_seq; lia). cbn [seq] in Hin. clear Hn.
    repeat (destruct Hin as [<-|Hin];
      [ match goal with |- reg_get R ?r = _ =>
          pose proof (HR' r) as G; unfold getr in G; change (bv_eqb r 0) with false in G; cbv iota in G; rewrite G; clear G;
          let e := eval vm_compute in (sr_get OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.SR_MAIN r) in change (sr_get OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.SR_MAIN r) with e
        end;
        cbn [edenot nth main_regs Nat.sub]; rewrite ?E0, ?E1, ?E7, ?K98, ?K99, ?K100;
        first [ reflexivity
              | change (alu64 Instr.ALU_ADD ?x ?y) with (x + y)%bv; rewrite add_lit; f_equal; fold usp; lia
              | change (alu64 Instr.ALU_ADD (alu64 Instr.ALU_ADD ?x (mul_div Instr.M_MUL ?c ?k)) ?y) with ((x + c * k) + y)%bv;
                rewrite add_mul_lit, add_lit, Z_to_bv_unsigned, bv_wrap_small by (fold usp; unfold bv_modulus; lia); f_equal; fold usp; lia ] |]).
    destruct Hin.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Lemma at_main_pins : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned brk / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    set (E := EB' a tid c pl js).
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (H16 : bv_unsigned (ev E 0%nat) mod 16 = 0) by (rewrite E0; exact S16).
    destruct VI as (VA & VEn & _). pose proof VA as ((A1 & A2) & _). pose proof VEn as (B1 & _).
    pose proof (W_range PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) VA VEn) as (W1 & _ & W2).
    pose proof (L0_range PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) VA) as L0R.
    destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E101 & _). fold E in E101.
    split; [intros n; unfold V, V_of, uev; apply u64_range|].
    unfold V, V_of. fold E.
    rewrite (V'_0 E HSP), (V'_6 E), (V'_10 E), E0. fold usp.
    pose proof (sp_digits E H16 HSP) as [SD _]. rewrite E0 in SD. fold usp in SD.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    rewrite (V'_ren E 1 1 ltac:(unfold RENAMES; cbn [In]; in_solve)), (V'_ren E 2 2 ltac:(unfold RENAMES; cbn [In]; in_solve)),
            (V'_ren E 3 3 ltac:(unfold RENAMES; cbn [In]; in_solve)), (V'_ren E 4 4 ltac:(unfold RENAMES; cbn [In]; in_solve)),
            (V'_ren E 5 8 ltac:(unfold RENAMES; cbn [In]; in_solve)), (V'_ren E 6 9 ltac:(unfold RENAMES; cbn [In]; in_solve)),
            (V'_page E 101 5 ltac:(apply in_nat2_b; vmeq_refl)), E101.
    split; [change (ev E 1%nat) with (Z_to_bv 64 argc); apply u_small; unfold argc; lia|].
    split; [change (ev E 2%nat) with (Z_to_bv 64 envc); apply u_small; unfold envc; lia|].
    split; [apply u_small; lia|].
    split; [change (ev E 4%nat) with (Z_to_bv 64 (Wblk en inp)); apply u_small; unfold Wblk; cbn [en_sp en_draw]; lia|].
    split; [reflexivity|]. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="sp inp usp argc envc"] Lemma ro_addr_SEGS : forall x : word, ro_addr SEGS x = true -> 0x10000 <= bv_unsigned x < 0xa5000.
  Proof.
    intros x H. unfold ro_addr in H.
    assert (FS' : find_segment SEGS (bv_unsigned x) 1 =
      if (0x10000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0x32000) then Some AsanUbsan_segment_000
      else if (0x32000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0xa5000) then Some AsanUbsan_segment_001
      else if (0xa5000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0xa7000) then Some AsanUbsan_segment_002
      else if (0xa7000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0x604000) then Some AsanUbsan_segment_003
      else None) by reflexivity.
    rewrite FS' in H. clear FS'.
    destruct (Z_lt_ge_dec (bv_unsigned x) 0x10000) as [L|L]; [|destruct (Z_lt_ge_dec (bv_unsigned x) 0xa5000) as [L2|L2]; [lia|]]; exfalso.
    - rewrite (proj2 (Z.leb_gt 0x10000 _)), (proj2 (Z.leb_gt 0x32000 _)), (proj2 (Z.leb_gt 0xa5000 _)), (proj2 (Z.leb_gt 0xa7000 _)) in H by lia.
      cbn [andb] in H. discriminate.
    - rewrite (proj2 (Z.leb_gt _ 0x32000)), (proj2 (Z.leb_gt _ 0xa5000)) in H by lia. rewrite !andb_false_r in H.
      destruct ((0xa5000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0xa7000)); [vm_compute in H; discriminate|].
      destruct ((0xa7000 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? 0x604000)); [vm_compute in H; discriminate| discriminate].
  Qed.

  #[using="VI VE usp argc envc"] Lemma at_main_mem_inv : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    mem_inv SEGS M.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM x b Hx.
    destruct (at_main_ro_stk sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [RO _].
    destruct (ro_addr SEGS x) eqn:ER; [|reflexivity]. exfalso.
    pose proof (RO _ (ro_addr_SEGS x ER)) as N. unfold wa in N. rewrite Z_to_bv_bv_unsigned in N. congruence.
  Qed.
End Entry.
End TwB.
End MainReadyA.

(* [comment removed for export] *)
Module MainReadyB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot2 BootS1 BootS2 BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS5 BootS6 BootS7 BootS8 BootState. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require A3Kn MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainAux MainShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac in_solve := repeat (first [left; lazymatch goal with
    | |- (?x1, ?y1) = (?x2, ?y2) =>   (* [comment removed for export] *)
        tryif (let c := eval vm_compute in (Nat.eqb y1 y2) in lazymatch c with false => idtac end) then fail else reflexivity
    | |- _ => reflexivity end | right]).

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).

  (* [comment removed for export] *)
  #[using="sp inp usp argc envc"] Lemma cb_zero_overlay : forall (M : word -> option byte) A n,
    rw_cells SEGS M A [CB (Z.to_nat n) (zeros n)] -> 0 <= n -> IMG_HI <= A -> A + n <= 2 ^ 64 ->
    forall i, 0 <= i < n -> M (wa (A + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros M A n [[_ (B1 & B2 & B3)] _] Hn HA HB i Hi. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r in B3.
    unfold zeros in B3. rewrite repeat_length in B3.
    specialize (B3 (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B3 by lia.
    assert (LT : (Z.to_nat i < Z.to_nat n)%nat) by lia. rewrite (nth_error_repeat (Z_to_bv 8 0) LT) in B3.
    unfold mrd in B3. destruct (M (wa (A + i))) as [b|]; [exact B3|].
    exfalso. unfold E2.Lib.PropExec.seg_rom, memory_read in B3. change (Z.of_N 1) with 1 in B3.
    unfold wa in B3. rewrite Z_to_bv_unsigned, bv_wrap_small in B3 by (unfold bv_modulus, IMG_HI in *; lia).
    rewrite (off_img_Z sp (A + i) ltac:(unfold IMG_HI in *; lia)) in B3. discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_stack_shadow : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    forall i, 0 <= i < zv V STKSH_LEN -> M (wa (zv V STKSH_BASE + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM V i Hi.
    destruct (at_main_facts sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [HMF _].
    apply Forall_app in HMF as [HMF _]. fold V in HMF.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _). fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    pose proof (at_main_shadow_zero sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as SZ.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    pose proof HB as [HR HKN HA HZ HLZ HMI F HMO RG HT Hcl Ht].
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    (* [comment removed for export] *)
    assert (V84 : V 1084%nat = W).
    { unfold V, V_of. fold E. change 1084%nat with (KEEP + 84)%nat. rewrite (V'_keep E HSP 84), E84. apply u_small.
      unfold SHB_HI, CSH in *. fold usp in WL. clear - WL WH SLo. Z.div_mod_to_equations. lia. }
    assert (WD : 0 <= Wdst sp /\ Wdst sp + 8 <= SHB_HI /\ IMG_HI <= Wdst sp).
    { unfold Wdst, SHB_HI, CSH, IMG_HI. fold usp. clear - SLo ULT. Z.div_mod_to_equations. lia. }
    assert (V85 : V 1085%nat = Wdst sp).
    { unfold V, V_of. fold E. change 1085%nat with (KEEP + 85)%nat. rewrite (V'_keep E HSP 85), E85. apply u_small.
      unfold SHB_HI in WD. clear - WD. lia. }
    pose proof (mfact_find SEGS V M _ (MZeroC (ZV 1084) 8) HMF ltac:(vmeq_refl)) as ZW. cbn [mfact_ok zv] in ZW. rewrite V84 in ZW.
    pose proof (mfact_find SEGS V M _ (MZeroC (ZV 1085) 8) HMF ltac:(vmeq_refl)) as ZD. cbn [mfact_ok zv] in ZD. rewrite V85 in ZD.
    (* [comment removed for export] *)
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (proj1 (Forall_forall _ _) HMO (EVar 38, 65536) ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as MO12.
    unfold map_ok in MO12. cbn [fst snd edenot] in MO12. fold E in MO12. rewrite E38 in MO12. destruct MO12 as (Q1 & _ & _ & Q4 & _).
    destruct HT as (T1 & _ & T3 & T4). unfold stack_max_size in *. fold usp in Q4, T3, P3.
    set (x := zv V STKSH_BASE + i).
    assert (BX : zv V STKSH_BASE = 4096 * V 0%nat + 512 * V 10%nat + 2146402304) by (cbn [zv STKSH_BASE]; lia).
    assert (LX : zv V STKSH_LEN = -4096 * V 0%nat - 512 * V 10%nat + 17592187092992) by (cbn [zv STKSH_LEN]; lia).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096).
    { rewrite PV0, PV10. clear. Z.div_mod_to_equations. lia. }
    assert (XR : 2201439137792 <= x < SHB_HI /\ usp / 4096 * 4096 - 8388608 = 8 * (zv V STKSH_BASE - CSH)).
    { assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
      assert (V10R : 0 <= V 10%nat <= 7) by (rewrite PV10; clear; Z.div_mod_to_equations; lia).
      unfold x, SHB_HI, CSH. rewrite BX. rewrite LX in Hi. clear - Hi PD SLo ULT TU V10R. lia. }
    destruct XR as (XR & XB).
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply u_small; unfold SHB_HI in XR; lia).
    destruct (Z_lt_ge_dec x W) as [CW|CW]; [| destruct (Z_lt_ge_dec x (W + 8)) as [CW2|CW2]].
    2:{ replace x with (W + (x - W)) by lia. apply (cb_zero_overlay M W 8 ZW); unfold IMG_HI, SHB_HI, CSH in *; fold usp in WL; clear - CW CW2 WL WH SLo; lia. }
    all: destruct (Z_lt_ge_dec x (Wdst sp)) as [CD|CD]; [| destruct (Z_lt_ge_dec x (Wdst sp + 8)) as [CD2|CD2]].
    all: try (replace x with (Wdst sp + (x - Wdst sp)) by lia; apply (cb_zero_overlay M (Wdst sp) 8 ZD); unfold SHB_HI in *; clear - CD CD2 WD; lia).
    all: apply SZ; rewrite UX.
    all: try (right; exact XR).
    all: try (right; unfold SHB_HI in XR; clear - XR; lia).
    all: try (left; assumption).
    all: try (right; match goal with H : ?x >= ?y |- ?y <= ?x => clear - H; lia end).
    all: try (right; assert (TSHc : TSH a = 2148221854) by (unfold TSH, CSH; rewrite T4; reflexivity); rewrite TSHc; clear - XR; lia).
    all: try (right; unfold SH12, CSH in *; clear - Q1 Q4 XB XR Hi; Z.div_mod_to_equations; lia).
    all: try (right; unfold SHRI, RI, CSH, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE in *; rewrite Hsb; unfold SBV; clear - P1 P3 XB XR Hi; Z.div_mod_to_equations; lia).
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_ashadow0 : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    ashadow0 (V_of sp draw inp a tid c pl js) M.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM x HS NV.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 38%nat 228%nat ltac:(apply in_nat2_b; vmeq_refl)) as V228.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof (at_main_shadow_zero sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as SZ.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    assert (E7 : ev E 7%nat = a) by reflexivity. rewrite E38 in V228. rewrite E28 in V208.
    assert (V209 : V 209%nat = bv_unsigned p8 mod 65536 / 4096) by (unfold V, V_of; fold E; rewrite (V'_209 E), E28; reflexivity).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply u_small; unfold ashadow in HS; lia).
    assert (VIS : forall bn, In bn asan_vis_app -> ~ (ASHOFF + zv V (fst bn) / 8 <= x < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8))
      by (intros bn Hin Hr; apply NV; exists bn; split; assumption).
    apply SZ; rewrite UX.
    - unfold ashadow in HS. unfold SHB_LO, SHB_HI. clear - HS. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZLit 65536, ZLit 6238208) ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      clear - N. change (65536 / 8) with 8192 in N. change ((65536 + 6238208) / 8) with 787968 in N. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                       ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
                      ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608 + (-32768 * V 0%nat + -4096 * V 10%nat + 140737496743936)) with 140737488355328 in N by lia.
      change (140737488355328 / 8) with 17592186044416 in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608) with (usp / 4096 * 4096 - 8388608) in N by lia.
      unfold Wdst, CSH. fold usp. clear - N SLo ULT. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                       ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
                      ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608 + (-32768 * V 0%nat + -4096 * V 10%nat + 140737496743936)) with 140737488355328 in N by lia.
      change (140737488355328 / 8) with 17592186044416 in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608) with (usp / 4096 * 4096 - 8388608) in N by lia.
      unfold SHB_HI, CSH in *. fold usp in WL. clear - N SLo ULT WL WH. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZLit 65536, ZLit 6238208) ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      pose proof HB as [_ _ _ _ _ _ _ _ _ T4 _ _]; destruct T4 as (_ & _ & _ & T4).
      assert (TSHc : TSH a = 2148221854) by (unfold TSH, CSH; rewrite T4; reflexivity). rewrite TSHc.
      clear - N. change (65536 / 8) with 8192 in N. change ((65536 + 6238208) / 8) with 787968 in N. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZMul (ZLit 4096) (ZV 228), ZLit 65536) ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      rewrite V228 in N. unfold SH12. clear - N. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096)
                      ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      rewrite V208, V209 in N. unfold SHRI, RI. rewrite Hsb. unfold SBV.
      assert (P1 : bv_unsigned p8 mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia).
      clear - N P1. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma at_main_below_window : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall i n, In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 ->
      bv_unsigned (ev (EB' a tid c pl js) i) + n <= usp / 4096 * 4096 - 8388608.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & _) i n Hin Hn.
    destruct HB as [_ _ _ _ _ _ _ HMO _ _ _ _].
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd edenot] in MO.
    destruct MO as (M1 & _ & _ & M4 & _). unfold stack_max_size in M4. fold usp in M4.
    clear - M1 M4 Hn. Z.div_mod_to_equations. lia.
  Qed.

  #[using="VI VE usp argc envc"] Lemma at_main_pure_win : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (pfact_ok (V_of sp draw inp a tid c pl js)) asan_pure_facts_win.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (at_main_below_window _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as BW.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    assert (PGB : forall i k n, In (i, k) PAGES -> In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 ->
                  pfact_ok V (PDisj (ZMul (ZLit 4096) (ZV k)) n STKWIN_BASE STKWIN_LEN)).
    { intros i k n HP Hin Hn. cbn [pfact_ok zv STKWIN_BASE]. left. rewrite (VP i k HP). pose proof (BW i n Hin Hn) as B. clear - B PD. lia. }
    unfold asan_pure_facts_win, win_blocks. cbn [List.map fst snd].
    repeat (apply Forall_cons; [first
      [ (* [comment removed for export] *)
        lazymatch goal with
        | |- pfact_ok _ (PDisj (ZMul (ZLit 4096) (ZV ?k)) ?n _ _) =>
            let i := eval vm_compute in (fst (hd (0%nat, 0%nat) (List.filter (fun p => Nat.eqb (snd p) k) PAGES))) in
            apply (PGB i k n); [apply in_nat2_b; vmeq_refl | rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity]
        end
      | cbn [pfact_ok zv STKWIN_BASE]; left; rewrite K103; pose proof (BW 103%nat 4096 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) eq_refl) as B; clear - B PD; lia
      | cbn [pfact_ok zv STKWIN_BASE]; left; rewrite K102; pose proof (BW 102%nat 8192 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) eq_refl) as B; clear - B PD; lia ] |]).
    apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_pure_x : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (pfact_ok (V_of sp draw inp a tid c pl js)) asan_pure_facts_x.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (V209 : V 209%nat = bv_unsigned (ev E 28%nat) mod 65536 / 4096) by (unfold V, V_of; fold E; apply (V'_209 E)).
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (HST : bv_unsigned (ev E 62%nat) = (bv_unsigned (ev E 0%nat) + 3935) / 4096 * 4096).
    { rewrite E62, E0. fold usp. unfold STv. fold usp. apply u_small. clear - SLo ULT. Z.div_mod_to_equations. lia. }
    assert (V344 : V 344%nat = (bv_unsigned (ev E 62%nat) - bv_unsigned (ev E 0%nat) / 4096 * 4096) / 4096) by (unfold V, V_of; fold E; apply (V'_344 E); assumption).
    unfold asan_pure_facts_x. repeat apply Forall_cons; try apply Forall_nil; cbn [pfact_ok zv].
    - (* [comment removed for export] *)
      change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite V208, V209. change (2 ^ 16) with 65536.
      set (u := bv_unsigned (ev E 28%nat)) in *.
      assert (UA : u mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia).
      replace (-4096 * (u mod 65536 / 4096) + u mod 65536) with 0 by (clear - UA; Z.div_mod_to_equations; lia).
      change (0 mod MainExport.two64) with 0. lia.
    - (* [comment removed for export] *)
      rewrite PV6, V344, HST, E0. fold usp.
      replace (16 * (usp mod 4096 / 16)) with (usp mod 4096) by (clear - S16; Z.div_mod_to_equations; lia).
      assert (X : 0 <= usp mod 4096 + -4096 * (((usp + 3935) / 4096 * 4096 - usp / 4096 * 4096) / 4096) + 3935 <= 4095)
        by (clear - SLo; Z.div_mod_to_equations; lia).
      rewrite Z.mod_small by (change MainExport.two64 with 18446744073709551616; clear - X; lia). exact X.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_stackstore : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    wr_at SEGS M (4096 * V 470%nat) 8388608
    /\ (forall i, 0 <= i < 8384512 -> M (wa (4096 * V 470%nat + 4096 + i)) = Some (Z_to_bv 8 0)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM V.
    destruct (at_main_facts sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [HMF _].
    apply Forall_app in HMF as [HMF _]. fold V in HMF.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 105%nat 470%nat ltac:(apply in_nat2_b; vmeq_refl)) as V470.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    rewrite E105 in V470.
    pose proof HB as [HR HKN HA HZ HLZ HMI F HMO RG HT Hcl Ht].
    pose proof (proj1 (Forall_forall _ _) HMO (EVar 105, 8388608) ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as MO.
    unfold map_ok in MO. cbn [fst snd edenot] in MO. rewrite E105 in MO. destruct MO as (Q1 & Q2 & _ & Q4 & _).
    pose proof (SH sp brk mbase draw inp VI VE) as SHi. unfold stack_max_size in Q4. fold usp in SHi, Q4.
    pose proof (mwr_find SEGS V M _ (ZMul (ZLit 4096) (ZV 470)) 4096 HMF ltac:(vmeq_refl)) as W1. cbn [zv] in W1.
    assert (Z2 : forall i, 0 <= i < 8384512 -> M (wa (4096 * V 470%nat + 4096 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite V470. set (x := wa (bv_unsigned p24 + 4096 + i)).
      assert (UX : bv_unsigned x = bv_unsigned p24 + 4096 + i) by (unfold x, wa; apply u_small; lia).
      assert (HH : H_MAIN sp p8 sb p10 p12 a W p24 x = true).
      { unfold H_MAIN. apply (proj2 (hcut_true _ _ _ _)). split; [| rewrite UX; unfold SHB_LO, SHB_HI in AP24; lia].
        apply (proj2 (hcut_true _ _ _ _)). split; [| rewrite UX; lia].
        apply hjoin_new. rewrite UX. lia. }
      unfold hf_ok, HC_MAIN in HZ. apply Forall_inv in HZ. cbn [fst snd] in HZ. apply (HZ x); [rewrite UX; lia | exact HH]. }
    split; [| exact Z2].
    destruct (overlay_zero_rw SEGS M (4096 * V 470%nat + 4096) 8384512 ltac:(lia) ltac:(change MainExport.two64 with 18446744073709551616; lia) ltac:(lia) Z2) as [W2 _].
    destruct W1 as (A1 & A2 & A3). destruct W2 as (B1 & B2 & B3).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i 4096) as [C|C]; [apply A3; lia|].
    replace (4096 * V 470%nat + i) with (4096 * V 470%nat + 4096 + (i - 4096)) by lia. apply B3. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_ashadow1 : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    ashadow1 (V_of sp draw inp a tid c pl js) M.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM x HS NV.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 38%nat 228%nat ltac:(apply in_nat2_b; vmeq_refl)) as V228.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof (at_main_shadow_zero sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as SZ.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (E7 : ev E 7%nat = a) by reflexivity. rewrite E38 in V228. rewrite E28 in V208.
    assert (V209 : V 209%nat = bv_unsigned p8 mod 65536 / 4096) by (unfold V, V_of; fold E; rewrite (V'_209 E), E28; reflexivity).
    assert (V84 : V 1084%nat = W).
    { unfold V, V_of. fold E. change 1084%nat with (KEEP + 84)%nat. rewrite (V'_keep E HSP 84), E84. apply u_small.
      unfold SHB_HI, CSH in *. fold usp in WL. clear - WL WH SLo. Z.div_mod_to_equations. lia. }
    assert (V85 : V 1085%nat = Wdst sp).
    { unfold V, V_of. fold E. change 1085%nat with (KEEP + 85)%nat. rewrite (V'_keep E HSP 85), E85. apply u_small.
      unfold Wdst, CSH. fold usp. clear - SLo ULT. Z.div_mod_to_equations. lia. }
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply u_small; unfold ashadow in HS; lia).
    unfold ashadow_exposed, ASHOFF in NV. rewrite V84, V85, V228, V208, V209 in NV.
    apply SZ; rewrite UX.
    - unfold ashadow in HS. unfold SHB_LO, SHB_HI. clear - HS. lia.
    - clear - NV. lia.
    - clear - NV. lia.
    - clear - NV. lia.
    - pose proof HB as [_ _ _ _ _ _ _ _ _ T4 _ _]; destruct T4 as (_ & _ & _ & T4).
      assert (TSHc : TSH a = 2148221854) by (unfold TSH, CSH; rewrite T4; reflexivity). rewrite TSHc. clear - NV. lia.
    - unfold SH12. clear - NV. lia.
    - unfold SHRI, RI. rewrite Hsb. unfold SBV.
      assert (P1 : bv_unsigned p8 mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia).
      replace (bv_unsigned p8 - 4096 * (bv_unsigned p8 mod 65536 / 4096) + 137439019008) with (bv_unsigned p8 + 65536 - bv_unsigned p8 mod 65536 + 2 ^ 37) in NV
        by (clear - P1; Z.div_mod_to_equations; lia).
      clear - NV. lia.
  Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac in_solve := repeat (first [left; lazymatch goal with
    | |- (?x1, ?y1) = (?x2, ?y2) =>   (* [comment removed for export] *)
        tryif (let c := eval vm_compute in (Nat.eqb y1 y2) in lazymatch c with false => idtac end) then fail else reflexivity
    | |- _ => reflexivity end | right]).

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).

  (* [comment removed for export] *)
  #[using="sp inp usp argc envc"] Lemma cb_zero_overlay : forall (M : word -> option byte) A n,
    rw_cells SEGS M A [CB (Z.to_nat n) (zeros n)] -> 0 <= n -> IMG_HI <= A -> A + n <= 2 ^ 64 ->
    forall i, 0 <= i < n -> M (wa (A + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros M A n [[_ (B1 & B2 & B3)] _] Hn HA HB i Hi. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r in B3.
    unfold zeros in B3. rewrite repeat_length in B3.
    specialize (B3 (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B3 by lia.
    assert (LT : (Z.to_nat i < Z.to_nat n)%nat) by lia. rewrite (nth_error_repeat (Z_to_bv 8 0) LT) in B3.
    unfold mrd in B3. destruct (M (wa (A + i))) as [b|]; [exact B3|].
    exfalso. unfold E2.Lib.PropExec.seg_rom, memory_read in B3. change (Z.of_N 1) with 1 in B3.
    unfold wa in B3. rewrite Z_to_bv_unsigned, bv_wrap_small in B3 by (unfold bv_modulus, IMG_HI in *; lia).
    rewrite (off_img_Z sp (A + i) ltac:(unfold IMG_HI in *; lia)) in B3. discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_stack_shadow : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    forall i, 0 <= i < zv V STKSH_LEN -> M (wa (zv V STKSH_BASE + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM V i Hi.
    destruct (at_main_facts sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [HMF _].
    apply Forall_app in HMF as [HMF _]. fold V in HMF.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _). fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    pose proof (at_main_shadow_zero sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as SZ.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    pose proof HB as [HR HKN HA HZ HLZ HMI F HMO RG HT Hcl Ht].
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    (* [comment removed for export] *)
    assert (V84 : V 1084%nat = W).
    { unfold V, V_of. fold E. change 1084%nat with (KEEP + 84)%nat. rewrite (V'_keep E HSP 84), E84. apply u_small.
      unfold SHB_HI, CSH in *. fold usp in WL. clear - WL WH SLo. Z.div_mod_to_equations. lia. }
    assert (WD : 0 <= Wdst sp /\ Wdst sp + 8 <= SHB_HI /\ IMG_HI <= Wdst sp).
    { unfold Wdst, SHB_HI, CSH, IMG_HI. fold usp. clear - SLo ULT. Z.div_mod_to_equations. lia. }
    assert (V85 : V 1085%nat = Wdst sp).
    { unfold V, V_of. fold E. change 1085%nat with (KEEP + 85)%nat. rewrite (V'_keep E HSP 85), E85. apply u_small.
      unfold SHB_HI in WD. clear - WD. lia. }
    pose proof (mfact_find SEGS V M _ (MZeroC (ZV 1084) 8) HMF ltac:(vmeq_refl)) as ZW. cbn [mfact_ok zv] in ZW. rewrite V84 in ZW.
    pose proof (mfact_find SEGS V M _ (MZeroC (ZV 1085) 8) HMF ltac:(vmeq_refl)) as ZD. cbn [mfact_ok zv] in ZD. rewrite V85 in ZD.
    (* [comment removed for export] *)
    pose proof (p8_factsG sp brk mbase draw lim inp (L_MAIN lb)
                  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
                   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (proj1 (Forall_forall _ _) HMO (EVar 38, 65536) ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as MO12.
    unfold map_ok in MO12. cbn [fst snd edenot] in MO12. fold E in MO12. rewrite E38 in MO12. destruct MO12 as (Q1 & _ & _ & Q4 & _).
    destruct HT as (T1 & _ & T3 & T4). unfold stack_max_size in *. fold usp in Q4, T3, P3.
    set (x := zv V STKSH_BASE + i).
    assert (BX : zv V STKSH_BASE = 4096 * V 0%nat + 512 * V 10%nat + 2146402304) by (cbn [zv STKSH_BASE]; lia).
    assert (LX : zv V STKSH_LEN = -4096 * V 0%nat - 512 * V 10%nat + 17592187092992) by (cbn [zv STKSH_LEN]; lia).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096).
    { rewrite PV0, PV10. clear. Z.div_mod_to_equations. lia. }
    assert (XR : 2201439137792 <= x < SHB_HI /\ usp / 4096 * 4096 - 8388608 = 8 * (zv V STKSH_BASE - CSH)).
    { assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
      assert (V10R : 0 <= V 10%nat <= 7) by (rewrite PV10; clear; Z.div_mod_to_equations; lia).
      unfold x, SHB_HI, CSH. rewrite BX. rewrite LX in Hi. clear - Hi PD SLo ULT TU V10R. lia. }
    destruct XR as (XR & XB).
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply u_small; unfold SHB_HI in XR; lia).
    destruct (Z_lt_ge_dec x W) as [CW|CW]; [| destruct (Z_lt_ge_dec x (W + 8)) as [CW2|CW2]].
    2:{ replace x with (W + (x - W)) by lia. apply (cb_zero_overlay M W 8 ZW); unfold IMG_HI, SHB_HI, CSH in *; fold usp in WL; clear - CW CW2 WL WH SLo; lia. }
    all: destruct (Z_lt_ge_dec x (Wdst sp)) as [CD|CD]; [| destruct (Z_lt_ge_dec x (Wdst sp + 8)) as [CD2|CD2]].
    all: try (replace x with (Wdst sp + (x - Wdst sp)) by lia; apply (cb_zero_overlay M (Wdst sp) 8 ZD); unfold SHB_HI in *; clear - CD CD2 WD; lia).
    all: apply SZ; rewrite UX.
    all: try (right; exact XR).
    all: try (right; unfold SHB_HI in XR; clear - XR; lia).
    all: try (left; assumption).
    all: try (right; match goal with H : ?x >= ?y |- ?y <= ?x => clear - H; lia end).
    all: try (right; assert (TSHc : TSH a = 2148221982) by (unfold TSH, CSH; rewrite T4; reflexivity); rewrite TSHc; clear - XR; lia).
    all: try (right; unfold SH12, CSH in *; clear - Q1 Q4 XB XR Hi; Z.div_mod_to_equations; lia).
    all: try (right; unfold SHRI, RI, CSH, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE in *; rewrite Hsb; unfold SBV; clear - P1 P3 XB XR Hi; Z.div_mod_to_equations; lia).
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_ashadow0 : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    ashadow0 (V_of sp draw inp a tid c pl js) M.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM x HS NV.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 38%nat 228%nat ltac:(apply in_nat2_b; vmeq_refl)) as V228.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof (at_main_shadow_zero sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as SZ.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    assert (E7 : ev E 7%nat = a) by reflexivity. rewrite E38 in V228. rewrite E28 in V208.
    assert (V209 : V 209%nat = bv_unsigned p8 mod 65536 / 4096) by (unfold V, V_of; fold E; rewrite (V'_209 E), E28; reflexivity).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply u_small; unfold ashadow in HS; lia).
    assert (VIS : forall bn, In bn asan_vis_app -> ~ (ASHOFF + zv V (fst bn) / 8 <= x < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8))
      by (intros bn Hin Hr; apply NV; exists bn; split; assumption).
    apply SZ; rewrite UX.
    - unfold ashadow in HS. unfold SHB_LO, SHB_HI. clear - HS. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZLit 65536, ZLit 6242304) ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      clear - N. change (65536 / 8) with 8192 in N. change ((65536 + 6242304) / 8) with 788480 in N. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                       ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
                      ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608 + (-32768 * V 0%nat + -4096 * V 10%nat + 140737496743936)) with 140737488355328 in N by lia.
      change (140737488355328 / 8) with 17592186044416 in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608) with (usp / 4096 * 4096 - 8388608) in N by lia.
      unfold Wdst, CSH. fold usp. clear - N SLo ULT. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                       ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
                      ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608 + (-32768 * V 0%nat + -4096 * V 10%nat + 140737496743936)) with 140737488355328 in N by lia.
      change (140737488355328 / 8) with 17592186044416 in N.
      replace (32768 * V 0%nat + 4096 * V 10%nat + -8388608) with (usp / 4096 * 4096 - 8388608) in N by lia.
      unfold SHB_HI, CSH in *. fold usp in WL. clear - N SLo ULT WL WH. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZLit 65536, ZLit 6242304) ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      pose proof HB as [_ _ _ _ _ _ _ _ _ T4 _ _]; destruct T4 as (_ & _ & _ & T4).
      assert (TSHc : TSH a = 2148221982) by (unfold TSH, CSH; rewrite T4; reflexivity). rewrite TSHc.
      clear - N. change (65536 / 8) with 8192 in N. change ((65536 + 6242304) / 8) with 788480 in N. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZMul (ZLit 4096) (ZV 228), ZLit 65536) ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      rewrite V228 in N. unfold SH12. clear - N. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (VIS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096)
                      ltac:(unfold asan_vis_app; cbn [In]; in_solve)) as N. cbn [fst snd zv] in N. unfold ASHOFF in N.
      rewrite V208, V209 in N. unfold SHRI, RI. rewrite Hsb. unfold SBV.
      assert (P1 : bv_unsigned p8 mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia).
      clear - N P1. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma at_main_below_window : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall i n, In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 ->
      bv_unsigned (ev (EB' a tid c pl js) i) + n <= usp / 4096 * 4096 - 8388608.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & _) i n Hin Hn.
    destruct HB as [_ _ _ _ _ _ _ HMO _ _ _ _].
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd edenot] in MO.
    destruct MO as (M1 & _ & _ & M4 & _). unfold stack_max_size in M4. fold usp in M4.
    clear - M1 M4 Hn. Z.div_mod_to_equations. lia.
  Qed.

  #[using="VI VE usp argc envc"] Lemma at_main_pure_win : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (pfact_ok (V_of sp draw inp a tid c pl js)) asan_pure_facts_win.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (at_main_below_window _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as BW.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    assert (PGB : forall i k n, In (i, k) PAGES -> In (EVar i, n) (l_maps (L_MAIN lb)) -> n mod 4096 = 0 ->
                  pfact_ok V (PDisj (ZMul (ZLit 4096) (ZV k)) n STKWIN_BASE STKWIN_LEN)).
    { intros i k n HP Hin Hn. cbn [pfact_ok zv STKWIN_BASE]. left. rewrite (VP i k HP). pose proof (BW i n Hin Hn) as B. clear - B PD. lia. }
    unfold asan_pure_facts_win, win_blocks. cbn [List.map fst snd].
    repeat (apply Forall_cons; [first
      [ (* [comment removed for export] *)
        lazymatch goal with
        | |- pfact_ok _ (PDisj (ZMul (ZLit 4096) (ZV ?k)) ?n _ _) =>
            let i := eval vm_compute in (fst (hd (0%nat, 0%nat) (List.filter (fun p => Nat.eqb (snd p) k) PAGES))) in
            apply (PGB i k n); [apply in_nat2_b; vmeq_refl | rewrite L_MAIN_maps; cbn [In]; in_solve | reflexivity]
        end
      | cbn [pfact_ok zv STKWIN_BASE]; left; rewrite K103; pose proof (BW 103%nat 4096 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) eq_refl) as B; clear - B PD; lia
      | cbn [pfact_ok zv STKWIN_BASE]; left; rewrite K102; pose proof (BW 102%nat 8192 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) eq_refl) as B; clear - B PD; lia ] |]).
    apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_pure_x : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (pfact_ok (V_of sp draw inp a tid c pl js)) asan_pure_facts_x.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (V209 : V 209%nat = bv_unsigned (ev E 28%nat) mod 65536 / 4096) by (unfold V, V_of; fold E; apply (V'_209 E)).
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (HST : bv_unsigned (ev E 62%nat) = (bv_unsigned (ev E 0%nat) + 3935) / 4096 * 4096).
    { rewrite E62, E0. fold usp. unfold STv. fold usp. apply u_small. clear - SLo ULT. Z.div_mod_to_equations. lia. }
    assert (V344 : V 344%nat = (bv_unsigned (ev E 62%nat) - bv_unsigned (ev E 0%nat) / 4096 * 4096) / 4096) by (unfold V, V_of; fold E; apply (V'_344 E); assumption).
    unfold asan_pure_facts_x. repeat apply Forall_cons; try apply Forall_nil; cbn [pfact_ok zv].
    - (* [comment removed for export] *)
      change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite V208, V209. change (2 ^ 16) with 65536.
      set (u := bv_unsigned (ev E 28%nat)) in *.
      assert (UA : u mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia).
      replace (-4096 * (u mod 65536 / 4096) + u mod 65536) with 0 by (clear - UA; Z.div_mod_to_equations; lia).
      change (0 mod AS.MainExport.TwB.two64) with 0. lia.
    - (* [comment removed for export] *)
      rewrite PV6, V344, HST, E0. fold usp.
      replace (16 * (usp mod 4096 / 16)) with (usp mod 4096) by (clear - S16; Z.div_mod_to_equations; lia).
      assert (X : 0 <= usp mod 4096 + -4096 * (((usp + 3935) / 4096 * 4096 - usp / 4096 * 4096) / 4096) + 3935 <= 4095)
        by (clear - SLo; Z.div_mod_to_equations; lia).
      rewrite Z.mod_small by (change AS.MainExport.TwB.two64 with 18446744073709551616; clear - X; lia). exact X.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_stackstore : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    wr_at SEGS M (4096 * V 470%nat) 8388608
    /\ (forall i, 0 <= i < 8384512 -> M (wa (4096 * V 470%nat + 4096 + i)) = Some (Z_to_bv 8 0)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM V.
    destruct (at_main_facts sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [HMF _].
    apply Forall_app in HMF as [HMF _]. fold V in HMF.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 105%nat 470%nat ltac:(apply in_nat2_b; vmeq_refl)) as V470.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    rewrite E105 in V470.
    pose proof HB as [HR HKN HA HZ HLZ HMI F HMO RG HT Hcl Ht].
    pose proof (proj1 (Forall_forall _ _) HMO (EVar 105, 8388608) ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as MO.
    unfold map_ok in MO. cbn [fst snd edenot] in MO. rewrite E105 in MO. destruct MO as (Q1 & Q2 & _ & Q4 & _).
    pose proof (SH sp brk mbase draw inp VI VE) as SHi. unfold stack_max_size in Q4. fold usp in SHi, Q4.
    pose proof (mwr_find SEGS V M _ (ZMul (ZLit 4096) (ZV 470)) 4096 HMF ltac:(vmeq_refl)) as W1. cbn [zv] in W1.
    assert (Z2 : forall i, 0 <= i < 8384512 -> M (wa (4096 * V 470%nat + 4096 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite V470. set (x := wa (bv_unsigned p24 + 4096 + i)).
      assert (UX : bv_unsigned x = bv_unsigned p24 + 4096 + i) by (unfold x, wa; apply u_small; lia).
      assert (HH : H_MAIN sp p8 sb p10 p12 a W p24 x = true).
      { unfold H_MAIN. apply (proj2 (hcut_true _ _ _ _)). split; [| rewrite UX; unfold SHB_LO, SHB_HI in AP24; lia].
        apply (proj2 (hcut_true _ _ _ _)). split; [| rewrite UX; lia].
        apply hjoin_new. rewrite UX. lia. }
      unfold hf_ok, HC_MAIN in HZ. apply Forall_inv in HZ. cbn [fst snd] in HZ. apply (HZ x); [rewrite UX; lia | exact HH]. }
    split; [| exact Z2].
    destruct (overlay_zero_rw SEGS M (4096 * V 470%nat + 4096) 8384512 ltac:(lia) ltac:(change AS.MainExport.TwB.two64 with 18446744073709551616; lia) ltac:(lia) Z2) as [W2 _].
    destruct W1 as (A1 & A2 & A3). destruct W2 as (B1 & B2 & B3).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i 4096) as [C|C]; [apply A3; lia|].
    replace (4096 * V 470%nat + i) with (4096 * V 470%nat + 4096 + (i - 4096)) by lia. apply B3. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp argc envc"] Lemma at_main_ashadow1 : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    ashadow1 (V_of sp draw inp a tid c pl js) M.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM x HS NV.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (VP 38%nat 228%nat ltac:(apply in_nat2_b; vmeq_refl)) as V228.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof (at_main_shadow_zero sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as SZ.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (E7 : ev E 7%nat = a) by reflexivity. rewrite E38 in V228. rewrite E28 in V208.
    assert (V209 : V 209%nat = bv_unsigned p8 mod 65536 / 4096) by (unfold V, V_of; fold E; rewrite (V'_209 E), E28; reflexivity).
    assert (V84 : V 1084%nat = W).
    { unfold V, V_of. fold E. change 1084%nat with (KEEP + 84)%nat. rewrite (V'_keep E HSP 84), E84. apply u_small.
      unfold SHB_HI, CSH in *. fold usp in WL. clear - WL WH SLo. Z.div_mod_to_equations. lia. }
    assert (V85 : V 1085%nat = Wdst sp).
    { unfold V, V_of. fold E. change 1085%nat with (KEEP + 85)%nat. rewrite (V'_keep E HSP 85), E85. apply u_small.
      unfold Wdst, CSH. fold usp. clear - SLo ULT. Z.div_mod_to_equations. lia. }
    assert (UX : bv_unsigned (wa x) = x) by (unfold wa; apply u_small; unfold ashadow in HS; lia).
    unfold ashadow_exposed, ASHOFF in NV. rewrite V84, V85, V228, V208, V209 in NV.
    apply SZ; rewrite UX.
    - unfold ashadow in HS. unfold SHB_LO, SHB_HI. clear - HS. lia.
    - clear - NV. lia.
    - clear - NV. lia.
    - clear - NV. lia.
    - pose proof HB as [_ _ _ _ _ _ _ _ _ T4 _ _]; destruct T4 as (_ & _ & _ & T4).
      assert (TSHc : TSH a = 2148221982) by (unfold TSH, CSH; rewrite T4; reflexivity). rewrite TSHc. clear - NV. lia.
    - unfold SH12. clear - NV. lia.
    - unfold SHRI, RI. rewrite Hsb. unfold SBV.
      assert (P1 : bv_unsigned p8 mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia).
      replace (bv_unsigned p8 - 4096 * (bv_unsigned p8 mod 65536 / 4096) + 137439019008) with (bv_unsigned p8 + 65536 - bv_unsigned p8 mod 65536 + 2 ^ 37) in NV
        by (clear - P1; Z.div_mod_to_equations; lia).
      clear - NV. lia.
  Qed.
End Entry.
End TwB.
End MainReadyB.

(* [comment removed for export] *)
Module MainReadyC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot2 BootS1 BootS2 BootS3 BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS5 BootS6 BootS7 BootS8 BootState. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RelSpec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require A3Kn MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainAux MainShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ledger_list (V : nat -> Z) (l : list lentry) : list (word * word) :=
  flat_map (fun e => match e with LMap b n _ => [(wa (zv V b), wa n)] | LFog _ => [] end) l.
Lemma ledger_den_list : forall V l, forallb (fun e => match e with LMap _ _ _ => true | LFog _ => false end) l = true ->
  ledger_den V l (ledger_list V l).
Proof.
  intros V l. induction l as [|[b n k|n] l IH]; intros H; cbn in H |- *; [reflexivity | | discriminate].
  eexists. split; [reflexivity | exact (IH H)].
Qed.

Lemma ivs_sum_app : forall l1 l2, ivs_sum (l1 ++ l2) = ivs_sum l1 + ivs_sum l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn [ivs_sum app]; [lia|]. rewrite IH. lia. Qed.

Lemma ivs_sum_ledger_list : forall V l,
  ivs_sum (ledger_list V l) = fold_right (fun e acc => match e with LMap _ n _ => bv_unsigned (wa n) + acc | LFog _ => acc end) 0 l.
Proof. intros V l. induction l as [|[b n k|n] l IH]; cbn [ledger_list flat_map app ivs_sum fold_right snd]; [reflexivity | | exact IH]. fold (ledger_list V l). rewrite IH. reflexivity. Qed.

Lemma resv_sum : ivs_sum (segments_reserved SEGS) = 6238208.
Proof. vmeq_refl. Qed.

Lemma fold_cost_le : forall shoff V vis, shoff mod 4096 = 0 ->
  Forall (fun bn : zexp * zexp => 0 <= zv V (fst bn) /\ 0 <= zv V (snd bn) /\ zv V (fst bn) mod 4096 = 0 /\ zv V (snd bn) mod 4096 = 0) vis ->
  fold_right (fun bn acc => vis_cost shoff V bn + acc) 0 vis
  <= fold_right (fun bn acc => (zv V (snd bn) + zv V (snd bn) / 8 + 8192) + acc) 0 vis.
Proof.
  intros shoff V vis Hs HF. induction HF as [|bn vis (A1 & A2 & A3 & A4) HF IH]; cbn [fold_right]; [lia|].
  pose proof (vis_cost_aligned shoff V bn Hs A1 A2 A3 A4). lia.
Qed.

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_maps : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    vm_maps (m_vmmaps mdl) = ledger_list (V_of sp draw inp a tid c pl js) asan_ledger.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), L_MAIN_maps. fold E.
    unfold ledger_list, asan_ledger, dl. cbn [List.map flat_map app fst snd edenot zv].
    repeat (apply (f_equal2 cons); [apply (f_equal2 pair); [first
      [ reflexivity
      | match goal with |- ev E ?i = wa (4096 * V ?k) =>
          rewrite (VP i k ltac:(apply in_nat2_b; vmeq_refl)); unfold wa; symmetry; apply Z_to_bv_bv_unsigned end
      | rewrite K103; unfold wa; symmetry; apply Z_to_bv_bv_unsigned
      | rewrite K102; unfold wa; symmetry; apply Z_to_bv_bv_unsigned ] | reflexivity] |]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Lemma at_main_bounds : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (fun iv : word * word => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                     /\ 0 < bv_unsigned (fst iv)
                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= usp - 8388608)
           (vm_maps (m_vmmaps mdl)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & _).
    destruct HB as [_ _ _ _ _ _ F HMO _ _ _ _].
    rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply Forall_forall. intros iv Hin.
    apply in_map_iff in Hin as ([e n] & <- & Hin). cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd] in MO.
    destruct MO as (M1 & M2 & M3 & M4 & M5). unfold stack_max_size, A_img_lo, A_img_hi in *. fold usp in M4.
    pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SHi.
    assert (NN : n mod 4096 = 0).
    { rewrite L_MAIN_maps in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [X|Hin]; [injection X as _ <-; reflexivity|]). destruct Hin. }
    pose proof (u64_range (edenot (EB' a tid c pl js) e)) as UR.
    rewrite (u_small n) by lia. unfold AIMG_LO, AIMG_HI. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Lemma at_main_lazy_bounds : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= usp - 8388608) (m_vm_lazy mdl).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    destruct HB as [_ _ _ _ HLZ _ _ HMO _ _ _ _].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    assert (MO : forall i n (p : word), In (EVar i, n) (l_maps (L_MAIN lb)) -> ev (EB' a tid c pl js) i = p -> 0 <= n < 2 ^ 47 ->
                 (bv_unsigned p + bv_unsigned (Z_to_bv 64 n) <= AIMG_LO \/ AIMG_HI <= bv_unsigned p)
                 /\ bv_unsigned p + bv_unsigned (Z_to_bv 64 n) <= usp - 8388608).
    { intros i n p Hin <- Hn. pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd edenot] in MO.
      destruct MO as (_ & _ & _ & M4 & M5). unfold stack_max_size, A_img_lo, A_img_hi in *. fold usp in M4.
      rewrite (u_small n) by lia. unfold AIMG_LO, AIMG_HI. split; lia. }
    set (P := fun b e : Z => (e <= AIMG_LO \/ AIMG_HI <= b) /\ e <= usp - 8388608).
    assert (PM : forall b e b' e', P b e -> b <= b' -> e' <= e -> P b' e') by (unfold P; intros; lia).
    assert (WF : forall l, Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) l -> ivs_wf l).
    { intros l HF q Hq. pose proof (proj1 (Forall_forall _ _) HF q Hq) as [_ X]. unfold iv_wf, B, BackingAlgebra.S. lia. }
    assert (L16 : Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) (LZ16 p8)).
    { unfold LZ16, LZ5. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold P.
      - exact (MO 28%nat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE p8 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) E28 ltac:(unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE; lia)).
      - rewrite HI_A_val, HI_N_val. unfold AIMG_LO, AIMG_HI. lia.
      - rewrite GAP_A_val, GAP_N_val. unfold AIMG_LO, AIMG_HI. lia.
      - rewrite LO_N_val. change (bv_unsigned LO_A) with 0x7fff7000. unfold AIMG_LO, AIMG_HI. lia. }
    assert (L18 : Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) (LZ18 p8 sb p10)).
    { unfold LZ18. apply Forall_cons.
      - cbn [fst snd]. unfold P. exact (MO 36%nat N_PA p10 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) E36 ltac:(unfold N_PA; lia)).
      - unfold LZ17. apply (Forall_maps_subtract P); [apply WF; exact L16 | exact PM | exact L16]. }
    rewrite HLZ. unfold LZ_MAIN, LZ30, LZ24. apply Forall_cons.
    - cbn [fst snd]. exact (MO 105%nat 8388608 p24 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) E105 ltac:(lia)).
    - apply (Forall_maps_subtract P); [apply WF; exact L18 | exact PM | exact L18].
  Qed.

  #[using="VI VE usp"] Lemma at_main_totsz : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    ivs_sum (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) <= asan_totsz.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    rewrite (at_main_maps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    rewrite (mf_res _ _ _ _ _ _ _ _ _ F), ivs_sum_app, resv_sum, ivs_sum_ledger_list.
    vm_compute. discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_vis_ok : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    Forall (fun bn : zexp * zexp => 0 <= zv V (fst bn) /\ 0 <= zv V (snd bn) /\ zv V (fst bn) mod 4096 = 0 /\ zv V (snd bn) mod 4096 = 0) asan_vis
    /\ zv V (snd (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                  ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))) <= 2155876351.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (V209 : 0 <= V 209%nat <= 15).
    { unfold V, V_of. fold E. rewrite (V'_209 E). clear. Z.div_mod_to_equations. lia. }
    assert (V208 : 4096 <= 4096 * V 208%nat).
    { rewrite (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)).
      destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ _ HMO _ _ _ _].
      pose proof (proj1 (Forall_forall _ _) HMO (EVar 28, 137439023104) ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as MO.
      unfold map_ok in MO. cbn [fst snd edenot] in MO. fold E in MO. lia. }
    assert (AL : forall i n, In (EVar i, n) (l_maps (L_MAIN lb)) -> bv_unsigned (ev E i) mod 4096 = 0).
    { intros i n Hin. destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ _ HMO _ _ _ _].
      pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd edenot] in MO. exact (proj1 MO). }
    pose proof (AL 103%nat 4096 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as A103.
    pose proof (AL 102%nat 8192 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as A102.
    split.
    - unfold asan_vis, asan_vis_app, asan_ghost. cbn [app].
      repeat (apply Forall_cons; [cbn [fst snd zv];
        (* [comment removed for export] *)
        first [ match goal with |- 0 <= 4096 * V ?k /\ _ => pose proof (HVR k); split; [lia|]; split; [lia|]; split; [rewrite Z.mul_comm; apply Z_mod_mult | reflexivity] end
              | split; [lia|]; split; [lia|]; split; reflexivity
              | rewrite ?K103, ?K102; pose proof (u64_range (ev E 103%nat)); pose proof (u64_range (ev E 102%nat)); split; [lia|]; split; [lia|]; split; [assumption | reflexivity]
              | idtac ] |]); try apply Forall_nil.
      + (* [comment removed for export] *) split; [lia|]. split; [lia|]. split; [|reflexivity]. clear. Z.div_mod_to_equations. lia.
      + (* [comment removed for export] *)
        assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
        split; [clear - PD TU SLo; lia|]. split; [clear - PD TU ULT; lia|]. split; clear; Z.div_mod_to_equations; lia.
    - assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
      cbn [snd zv]. clear - PD SLo ULT TU. lia.
  Qed.

  #[using="VI VE usp"] Lemma at_main_abytes : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes /\ ivz_wf (allow_of ASHOFF V asan_vis).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    destruct (at_main_vis_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as [VOK NS]. fold V in VOK, NS.
    split.
    - rewrite ivz_bytes_allow_of.
      pose proof (fold_cost_le ASHOFF V asan_vis eq_refl VOK) as LE.
      cbn [fold_right asan_vis asan_vis_app asan_ghost app fst snd] in LE |- *. cbn [snd] in NS.
      cbn [zv] in LE, NS.
      set (ns := -32768 * V 0%nat + -4096 * V 10%nat + 140737496743936) in *.
      assert (NS8 : ns / 8 <= 269484543) by (clear - NS; Z.div_mod_to_equations; lia).
      unfold asan_abytes.
      repeat match type of LE with context [?n / 8] => lazymatch n with ns => fail | _ => let v := eval vm_compute in (n / 8) in change (n / 8) with v in LE end end.
      clear - LE NS NS8. lia.
    - apply allow_of_wf; [reflexivity|]. eapply Forall_impl; [|exact VOK]. cbv beta. intros bn (_ & H & _). exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_allowed : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall p : word, bv_unsigned p mod 4096 = 0 -> page_allowedb (A_MAIN sp sb p12 a W p24) p = true ->
    aallowed (allow_of ASHOFF (V_of sp draw inp a tid c pl js) asan_vis) p.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM p PA HP.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    pose proof (VP 38%nat 228%nat ltac:(apply in_nat2_b; vmeq_refl)) as V228.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof (VP 105%nat 470%nat ltac:(apply in_nat2_b; vmeq_refl)) as V470.
    assert (E7 : ev E 7%nat = a) by reflexivity. rewrite E38 in V228. rewrite E28 in V208. rewrite E105 in V470.
    assert (V209 : V 209%nat = bv_unsigned p8 mod 65536 / 4096) by (unfold V, V_of; fold E; rewrite (V'_209 E), E28; reflexivity).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
    pose proof (x9_facts sp S16 SLo ltac:(fold usp; lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & _). fold usp in X2, X3.
    pose proof (shk_facts sp S16 SLo ltac:(fold usp; lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11). fold usp in Y9, Y10, Y11.
    (* [comment removed for export] *)
    set (STK := (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                 ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))).
    assert (INS : In STK asan_vis) by (unfold STK, asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve).
    assert (STKSH : forall lo hi, (CSH + (usp / 4096 * 4096 - 8388608) / 8) / 4096 * 4096 <= lo -> hi <= SHB_HI -> lo <= bv_unsigned p -> bv_unsigned p + 4096 <= hi ->
                    aallowed (allow_of ASHOFF V asan_vis) p).
    { intros lo hi L1 L2 L3 L4.
      assert (Q1 : zv V (fst STK) = usp / 4096 * 4096 - 8388608) by (unfold STK; cbn [fst zv]; clear - PD; lia).
      assert (Q2 : zv V (fst STK) + zv V (snd STK) = 140737488355328) by (unfold STK; cbn [fst snd zv]; clear; lia).
      apply (aallowed_shadow ASHOFF V asan_vis STK p INS); rewrite ?Q2, ?Q1; unfold pagedown, pageup, ASHOFF.
      - unfold CSH in L1. clear - L1 L3. lia.
      - unfold SHB_HI in L2. change (140737488355328 / 8) with 17592186044416. clear - L2 L4. change ((2147450880 + 17592186044416 + 4095) / 4096 * 4096) with 17594333495296. lia. }
    unfold page_allowedb, A_MAIN, A10, A9, A9a, A8, A7, A5 in HP. cbn [existsb fst snd] in HP. unfold page_size in HP.
    repeat (apply orb_prop in HP as [HP|HP]); try discriminate HP;
      apply andb_prop in HP as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZLit 65536, ZLit 6238208) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv];
        [change (pagedown (ASHOFF + 65536 / 8)) with 2147459072 | change (pageup (ASHOFF + (65536 + 6238208) / 8)) with 2148241408]; clear - H1 H2; lia.
    - (* [comment removed for export] *)
      apply (aallowed_range ASHOFF V asan_vis (ZMul (ZLit 4096) (ZV 470), ZLit 8388608) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv]; unfold pagedown, pageup; rewrite <- V470 in H1, H2; clear - H1 H2; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      eapply STKSH; [ | | exact H1 | exact H2]; unfold Wdst, CSH, SHB_HI; fold usp; clear - SLo ULT; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      eapply STKSH; [ | | exact H1 | exact H2]; unfold CSH, SHB_HI in *; fold usp in WL; clear - SLo ULT WL WH; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZLit 65536, ZLit 6238208) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv];
        [change (pagedown (ASHOFF + 65536 / 8)) with 2147459072 | change (pageup (ASHOFF + (65536 + 6238208) / 8)) with 2148241408];
        pose proof HB as [_ _ _ _ _ _ _ _ _ T4 _ _]; destruct T4 as (_ & _ & _ & T4);
        assert (TPGc : TPG a = 2148220928) by (unfold TPG, TSH, CSH; rewrite T4; reflexivity);
        rewrite TPGc in H1, H2; clear - H1 H2; lia.
    - (* [comment removed for export] *)
      unfold HWLO, NSW, CSH in H1, H2.
      destruct (Z_le_gt_dec (bv_unsigned p + 4096) SHB_HI) as [C|C].
      + apply (STKSH ((XQv sp + 2147450880) / 4096 * 4096) SHB_HI); [| lia | exact H1 | exact C].
        unfold CSH. clear - X1 X2 X6 TU. Z.div_mod_to_equations. lia.
      + apply (aallowed_shadow ASHOFF V asan_vis (ZLit 140737488355328, ZLit 32768) p ltac:(unfold asan_vis, asan_ghost; apply in_or_app; right; cbn [In]; in_solve));
          cbn [fst snd zv]; unfold pagedown, pageup, ASHOFF; unfold SHB_HI in C; clear - C H2 PA X5 X6; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      eapply STKSH; [ | exact Y4 | exact H1 | exact H2].
      unfold PLOK, CSH. unfold stack_max_size in Y11. clear - Y11 TU. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZMul (ZLit 4096) (ZV 228), ZLit 65536) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv]; unfold pagedown, pageup, ASHOFF; unfold PLO12, PHI12, SH12 in H1, H2; rewrite <- V228 in H1, H2;
        set (k := V 228%nat) in *;
        assert (T0 : 4096 * k / 8 = 512 * k) by (clear; Z.div_mod_to_equations; lia);
        assert (T2 : (4096 * k + 65536) / 8 = 512 * k + 8192) by (clear; Z.div_mod_to_equations; lia);
        rewrite ?T0, ?T2; rewrite T0 in H1, H2; clear - H1 H2; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096) p
               ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv]; unfold pagedown, pageup, ASHOFF; rewrite V208, V209; unfold SHRI, RI in H1, H2; rewrite Hsb in H1, H2; unfold SBV in H1, H2;
        assert (P1 : bv_unsigned p8 mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia);
        clear - H1 H2 P1; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_pure_led : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (pfact_ok (V_of sp draw inp a tid c pl js)) (all_pairs asan_ledger).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (at_main_maps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as MAPS. fold V in MAPS.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    apply (all_pairs_ok V asan_ledger (vm_maps (m_vmmaps mdl))).
    - rewrite MAPS. reflexivity.
    - unfold asan_ledger. repeat (apply Forall_cons; [cbn [led_ok zv]; first
        [ (* [comment removed for export] *)
          match goal with |- 0 <= 4096 * V ?k < _ /\ _ =>
            let i := match k with 487%nat => constr:(107%nat) | 568%nat => constr:(106%nat) | 470%nat => constr:(105%nat) | 469%nat => constr:(104%nat)
                                | 393%nat => constr:(83%nat) | 310%nat => constr:(60%nat) | 245%nat => constr:(46%nat) | 228%nat => constr:(38%nat)
                                | 227%nat => constr:(37%nat) | 226%nat => constr:(36%nat) | 208%nat => constr:(28%nat) | 207%nat => constr:(27%nat)
                                | 78%nat => constr:(26%nat) | 700%nat => constr:(7%nat) end in
            rewrite (VP i k ltac:(apply in_nat2_b; vmeq_refl)); split; [apply u64_range | lia] end
        | split; lia
        | rewrite ?K103, ?K102; split; [apply u64_range | lia] ] |]). apply Forall_nil.
    - destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
      apply ivs_apart_sep. rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). exact (mf_apart _ _ _ _ _ _ _ _ _ F).
  Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ledger_list (V : nat -> Z) (l : list lentry) : list (word * word) :=
  flat_map (fun e => match e with LMap b n _ => [(wa (zv V b), wa n)] | LFog _ => [] end) l.
Lemma ledger_den_list : forall V l, forallb (fun e => match e with LMap _ _ _ => true | LFog _ => false end) l = true ->
  ledger_den V l (ledger_list V l).
Proof.
  intros V l. induction l as [|[b n k|n] l IH]; intros H; cbn in H |- *; [reflexivity | | discriminate].
  eexists. split; [reflexivity | exact (IH H)].
Qed.

Lemma ivs_sum_app : forall l1 l2, ivs_sum (l1 ++ l2) = ivs_sum l1 + ivs_sum l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn [ivs_sum app]; [lia|]. rewrite IH. lia. Qed.

Lemma ivs_sum_ledger_list : forall V l,
  ivs_sum (ledger_list V l) = fold_right (fun e acc => match e with LMap _ n _ => bv_unsigned (wa n) + acc | LFog _ => acc end) 0 l.
Proof. intros V l. induction l as [|[b n k|n] l IH]; cbn [ledger_list flat_map app ivs_sum fold_right snd]; [reflexivity | | exact IH]. fold (ledger_list V l). rewrite IH. reflexivity. Qed.

Lemma resv_sum : ivs_sum (segments_reserved SEGS) = 6242304.
Proof. vmeq_refl. Qed.

Lemma fold_cost_le : forall shoff V vis, shoff mod 4096 = 0 ->
  Forall (fun bn : zexp * zexp => 0 <= zv V (fst bn) /\ 0 <= zv V (snd bn) /\ zv V (fst bn) mod 4096 = 0 /\ zv V (snd bn) mod 4096 = 0) vis ->
  fold_right (fun bn acc => vis_cost shoff V bn + acc) 0 vis
  <= fold_right (fun bn acc => (zv V (snd bn) + zv V (snd bn) / 8 + 8192) + acc) 0 vis.
Proof.
  intros shoff V vis Hs HF. induction HF as [|bn vis (A1 & A2 & A3 & A4) HF IH]; cbn [fold_right]; [lia|].
  pose proof (vis_cost_aligned shoff V bn Hs A1 A2 A3 A4). lia.
Qed.

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_maps : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    vm_maps (m_vmmaps mdl) = ledger_list (V_of sp draw inp a tid c pl js) asan_ledger.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), L_MAIN_maps. fold E.
    unfold ledger_list, asan_ledger, dl. cbn [List.map flat_map app fst snd edenot zv].
    repeat (apply (f_equal2 cons); [apply (f_equal2 pair); [first
      [ reflexivity
      | match goal with |- ev E ?i = wa (4096 * V ?k) =>
          rewrite (VP i k ltac:(apply in_nat2_b; vmeq_refl)); unfold wa; symmetry; apply Z_to_bv_bv_unsigned end
      | rewrite K103; unfold wa; symmetry; apply Z_to_bv_bv_unsigned
      | rewrite K102; unfold wa; symmetry; apply Z_to_bv_bv_unsigned ] | reflexivity] |]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Lemma at_main_bounds : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (fun iv : word * word => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                     /\ 0 < bv_unsigned (fst iv)
                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= usp - 8388608)
           (vm_maps (m_vmmaps mdl)).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & _).
    destruct HB as [_ _ _ _ _ _ F HMO _ _ _ _].
    rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply Forall_forall. intros iv Hin.
    apply in_map_iff in Hin as ([e n] & <- & Hin). cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd] in MO.
    destruct MO as (M1 & M2 & M3 & M4 & M5). unfold stack_max_size, A_img_lo, A_img_hi in *. fold usp in M4.
    pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SHi.
    assert (NN : n mod 4096 = 0).
    { rewrite L_MAIN_maps in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [X|Hin]; [injection X as _ <-; reflexivity|]). destruct Hin. }
    pose proof (u64_range (edenot (EB' a tid c pl js) e)) as UR.
    rewrite (u_small n) by lia. unfold AIMG_LO, AIMG_HI. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Lemma at_main_lazy_bounds : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= usp - 8388608) (m_vm_lazy mdl).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    destruct HB as [_ _ _ _ HLZ _ _ HMO _ _ _ _].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi.
    assert (MO : forall i n (p : word), In (EVar i, n) (l_maps (L_MAIN lb)) -> ev (EB' a tid c pl js) i = p -> 0 <= n < 2 ^ 47 ->
                 (bv_unsigned p + bv_unsigned (Z_to_bv 64 n) <= AIMG_LO \/ AIMG_HI <= bv_unsigned p)
                 /\ bv_unsigned p + bv_unsigned (Z_to_bv 64 n) <= usp - 8388608).
    { intros i n p Hin <- Hn. pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd edenot] in MO.
      destruct MO as (_ & _ & _ & M4 & M5). unfold stack_max_size, A_img_lo, A_img_hi in *. fold usp in M4.
      rewrite (u_small n) by lia. unfold AIMG_LO, AIMG_HI. split; lia. }
    set (P := fun b e : Z => (e <= AIMG_LO \/ AIMG_HI <= b) /\ e <= usp - 8388608).
    assert (PM : forall b e b' e', P b e -> b <= b' -> e' <= e -> P b' e') by (unfold P; intros; lia).
    assert (WF : forall l, Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) l -> ivs_wf l).
    { intros l HF q Hq. pose proof (proj1 (Forall_forall _ _) HF q Hq) as [_ X]. unfold iv_wf, B, BackingAlgebra.S. lia. }
    assert (L16 : Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) (LZ16 p8)).
    { unfold LZ16, LZ5. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold P.
      - exact (MO 28%nat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE p8 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) E28 ltac:(unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE; lia)).
      - rewrite HI_A_val, HI_N_val. unfold AIMG_LO, AIMG_HI. lia.
      - rewrite GAP_A_val, GAP_N_val. unfold AIMG_LO, AIMG_HI. lia.
      - rewrite LO_N_val. change (bv_unsigned LO_A) with 0x7fff7000. unfold AIMG_LO, AIMG_HI. lia. }
    assert (L18 : Forall (fun iv : word * word => P (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv))) (LZ18 p8 sb p10)).
    { unfold LZ18. apply Forall_cons.
      - cbn [fst snd]. unfold P. exact (MO 36%nat N_PA p10 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) E36 ltac:(unfold N_PA; lia)).
      - unfold LZ17. apply (Forall_maps_subtract P); [apply WF; exact L16 | exact PM | exact L16]. }
    rewrite HLZ. unfold LZ_MAIN, LZ30, LZ24. apply Forall_cons.
    - cbn [fst snd]. exact (MO 105%nat 8388608 p24 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve) E105 ltac:(lia)).
    - apply (Forall_maps_subtract P); [apply WF; exact L18 | exact PM | exact L18].
  Qed.

  #[using="VI VE usp"] Lemma at_main_totsz : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    ivs_sum (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) <= asan_totsz.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    rewrite (at_main_maps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    rewrite (mf_res _ _ _ _ _ _ _ _ _ F), ivs_sum_app, resv_sum, ivs_sum_ledger_list.
    vm_compute. discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_vis_ok : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    Forall (fun bn : zexp * zexp => 0 <= zv V (fst bn) /\ 0 <= zv V (snd bn) /\ zv V (fst bn) mod 4096 = 0 /\ zv V (snd bn) mod 4096 = 0) asan_vis
    /\ zv V (snd (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                  ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))) <= 2155876351.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (V209 : 0 <= V 209%nat <= 15).
    { unfold V, V_of. fold E. rewrite (V'_209 E). clear. Z.div_mod_to_equations. lia. }
    assert (V208 : 4096 <= 4096 * V 208%nat).
    { rewrite (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)).
      destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ _ HMO _ _ _ _].
      pose proof (proj1 (Forall_forall _ _) HMO (EVar 28, 137439023104) ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as MO.
      unfold map_ok in MO. cbn [fst snd edenot] in MO. fold E in MO. lia. }
    assert (AL : forall i n, In (EVar i, n) (l_maps (L_MAIN lb)) -> bv_unsigned (ev E i) mod 4096 = 0).
    { intros i n Hin. destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ _ HMO _ _ _ _].
      pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MO. unfold map_ok in MO. cbn [fst snd edenot] in MO. exact (proj1 MO). }
    pose proof (AL 103%nat 4096 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as A103.
    pose proof (AL 102%nat 8192 ltac:(rewrite L_MAIN_maps; cbn [In]; in_solve)) as A102.
    split.
    - unfold asan_vis, asan_vis_app, asan_ghost. cbn [app].
      repeat (apply Forall_cons; [cbn [fst snd zv];
        (* [comment removed for export] *)
        first [ match goal with |- 0 <= 4096 * V ?k /\ _ => pose proof (HVR k); split; [lia|]; split; [lia|]; split; [rewrite Z.mul_comm; apply Z_mod_mult | reflexivity] end
              | split; [lia|]; split; [lia|]; split; reflexivity
              | rewrite ?K103, ?K102; pose proof (u64_range (ev E 103%nat)); pose proof (u64_range (ev E 102%nat)); split; [lia|]; split; [lia|]; split; [assumption | reflexivity]
              | idtac ] |]); try apply Forall_nil.
      + (* [comment removed for export] *) split; [lia|]. split; [lia|]. split; [|reflexivity]. clear. Z.div_mod_to_equations. lia.
      + (* [comment removed for export] *)
        assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
        split; [clear - PD TU SLo; lia|]. split; [clear - PD TU ULT; lia|]. split; clear; Z.div_mod_to_equations; lia.
    - assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
      cbn [snd zv]. clear - PD SLo ULT TU. lia.
  Qed.

  #[using="VI VE usp"] Lemma at_main_abytes : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes /\ ivz_wf (allow_of ASHOFF V asan_vis).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM V.
    destruct (at_main_vis_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as [VOK NS]. fold V in VOK, NS.
    split.
    - rewrite ivz_bytes_allow_of.
      pose proof (fold_cost_le ASHOFF V asan_vis eq_refl VOK) as LE.
      cbn [fold_right asan_vis asan_vis_app asan_ghost app fst snd] in LE |- *. cbn [snd] in NS.
      cbn [zv] in LE, NS.
      set (ns := -32768 * V 0%nat + -4096 * V 10%nat + 140737496743936) in *.
      assert (NS8 : ns / 8 <= 269484543) by (clear - NS; Z.div_mod_to_equations; lia).
      unfold asan_abytes.
      repeat match type of LE with context [?n / 8] => lazymatch n with ns => fail | _ => let v := eval vm_compute in (n / 8) in change (n / 8) with v in LE end end.
      clear - LE NS NS8. lia.
    - apply allow_of_wf; [reflexivity|]. eapply Forall_impl; [|exact VOK]. cbv beta. intros bn (_ & H & _). exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_allowed : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    forall p : word, bv_unsigned p mod 4096 = 0 -> page_allowedb (A_MAIN sp sb p12 a W p24) p = true ->
    aallowed (allow_of ASHOFF (V_of sp draw inp a tid c pl js) asan_vis) p.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM p PA HP.
    set (V := V_of sp draw inp a tid c pl js) in *.
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PV0 & PV6 & PV10 & USP & _).
    fold V in HVR, PV0, PV6, PV10, USP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SA16 sp brk mbase draw inp VI VE) as S16. fold usp in SLo, ULT, S16.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof HM as (HB & HW & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101 & E105 & AP24).
    set (E := EB' a tid c pl js) in *.
    pose proof (VP 38%nat 228%nat ltac:(apply in_nat2_b; vmeq_refl)) as V228.
    pose proof (VP 28%nat 208%nat ltac:(apply in_nat2_b; vmeq_refl)) as V208.
    pose proof (VP 105%nat 470%nat ltac:(apply in_nat2_b; vmeq_refl)) as V470.
    assert (E7 : ev E 7%nat = a) by reflexivity. rewrite E38 in V228. rewrite E28 in V208. rewrite E105 in V470.
    assert (V209 : V 209%nat = bv_unsigned p8 mod 65536 / 4096) by (unfold V, V_of; fold E; rewrite (V'_209 E), E28; reflexivity).
    assert (PD : 32768 * V 0%nat + 4096 * V 10%nat = usp / 4096 * 4096) by (rewrite PV0, PV10; clear; Z.div_mod_to_equations; lia).
    assert (TU : usp - 4095 <= usp / 4096 * 4096 <= usp) by (clear; Z.div_mod_to_equations; lia).
    pose proof (x9_facts sp S16 SLo ltac:(fold usp; lia)) as (X1 & X2 & X3 & X4 & X5 & X6 & _). fold usp in X2, X3.
    pose proof (shk_facts sp S16 SLo ltac:(fold usp; lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11). fold usp in Y9, Y10, Y11.
    (* [comment removed for export] *)
    set (STK := (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
                 ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))).
    assert (INS : In STK asan_vis) by (unfold STK, asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve).
    assert (STKSH : forall lo hi, (CSH + (usp / 4096 * 4096 - 8388608) / 8) / 4096 * 4096 <= lo -> hi <= SHB_HI -> lo <= bv_unsigned p -> bv_unsigned p + 4096 <= hi ->
                    aallowed (allow_of ASHOFF V asan_vis) p).
    { intros lo hi L1 L2 L3 L4.
      assert (Q1 : zv V (fst STK) = usp / 4096 * 4096 - 8388608) by (unfold STK; cbn [fst zv]; clear - PD; lia).
      assert (Q2 : zv V (fst STK) + zv V (snd STK) = 140737488355328) by (unfold STK; cbn [fst snd zv]; clear; lia).
      apply (aallowed_shadow ASHOFF V asan_vis STK p INS); rewrite ?Q2, ?Q1; unfold pagedown, pageup, ASHOFF.
      - unfold CSH in L1. clear - L1 L3. lia.
      - unfold SHB_HI in L2. change (140737488355328 / 8) with 17592186044416. clear - L2 L4. change ((2147450880 + 17592186044416 + 4095) / 4096 * 4096) with 17594333495296. lia. }
    unfold page_allowedb, A_MAIN, A10, A9, A9a, A8, A7, A5 in HP. cbn [existsb fst snd] in HP. unfold page_size in HP.
    repeat (apply orb_prop in HP as [HP|HP]); try discriminate HP;
      apply andb_prop in HP as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZLit 65536, ZLit 6242304) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv];
        [change (pagedown (ASHOFF + 65536 / 8)) with 2147459072 | change (pageup (ASHOFF + (65536 + 6242304) / 8)) with 2148241408]; clear - H1 H2; lia.
    - (* [comment removed for export] *)
      apply (aallowed_range ASHOFF V asan_vis (ZMul (ZLit 4096) (ZV 470), ZLit 8388608) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv]; unfold pagedown, pageup; rewrite <- V470 in H1, H2; clear - H1 H2; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      eapply STKSH; [ | | exact H1 | exact H2]; unfold Wdst, CSH, SHB_HI; fold usp; clear - SLo ULT; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      eapply STKSH; [ | | exact H1 | exact H2]; unfold CSH, SHB_HI in *; fold usp in WL; clear - SLo ULT WL WH; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZLit 65536, ZLit 6242304) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv];
        [change (pagedown (ASHOFF + 65536 / 8)) with 2147459072 | change (pageup (ASHOFF + (65536 + 6242304) / 8)) with 2148241408];
        pose proof HB as [_ _ _ _ _ _ _ _ _ T4 _ _]; destruct T4 as (_ & _ & _ & T4);
        assert (TPGc : TPG a = 2148220928) by (unfold TPG, TSH, CSH; rewrite T4; reflexivity);
        rewrite TPGc in H1, H2; clear - H1 H2; lia.
    - (* [comment removed for export] *)
      unfold HWLO, NSW, CSH in H1, H2.
      destruct (Z_le_gt_dec (bv_unsigned p + 4096) SHB_HI) as [C|C].
      + apply (STKSH ((XQv sp + 2147450880) / 4096 * 4096) SHB_HI); [| lia | exact H1 | exact C].
        unfold CSH. clear - X1 X2 X6 TU. Z.div_mod_to_equations. lia.
      + apply (aallowed_shadow ASHOFF V asan_vis (ZLit 140737488355328, ZLit 32768) p ltac:(unfold asan_vis, asan_ghost; apply in_or_app; right; cbn [In]; in_solve));
          cbn [fst snd zv]; unfold pagedown, pageup, ASHOFF; unfold SHB_HI in C; clear - C H2 PA X5 X6; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      eapply STKSH; [ | exact Y4 | exact H1 | exact H2].
      unfold PLOK, CSH. unfold stack_max_size in Y11. clear - Y11 TU. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZMul (ZLit 4096) (ZV 228), ZLit 65536) p ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv]; unfold pagedown, pageup, ASHOFF; unfold PLO12, PHI12, SH12 in H1, H2; rewrite <- V228 in H1, H2;
        set (k := V 228%nat) in *;
        assert (T0 : 4096 * k / 8 = 512 * k) by (clear; Z.div_mod_to_equations; lia);
        assert (T2 : (4096 * k + 65536) / 8 = 512 * k + 8192) by (clear; Z.div_mod_to_equations; lia);
        rewrite ?T0, ?T2; rewrite T0 in H1, H2; clear - H1 H2; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (aallowed_shadow ASHOFF V asan_vis (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096) p
               ltac:(unfold asan_vis, asan_vis_app; apply in_or_app; left; cbn [In]; in_solve));
        cbn [fst snd zv]; unfold pagedown, pageup, ASHOFF; rewrite V208, V209; unfold SHRI, RI in H1, H2; rewrite Hsb in H1, H2; unfold SBV in H1, H2;
        assert (P1 : bv_unsigned p8 mod 4096 = 0) by (clear - V208; Z.div_mod_to_equations; lia);
        clear - H1 H2 P1; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma at_main_pure_led : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    Forall (pfact_ok (V_of sp draw inp a tid c pl js)) (all_pairs asan_ledger).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (at_main_maps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as MAPS. fold V in MAPS.
    pose proof (V_page_addr sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as VP. fold V in VP.
    pose proof (at_main_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as ULT.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. fold usp in SLo, ULT.
    set (E := EB' a tid c pl js) in *.
    assert (E0 : ev E 0%nat = sp) by apply ev_EB_sp.
    assert (HSP : 0x7fff80000000 <= bv_unsigned (ev E 0%nat) < 2 ^ 47) by (rewrite E0; fold usp; lia).
    assert (K103 : V 1103%nat = bv_unsigned (ev E 103%nat)) by (unfold V, V_of; fold E; change 1103%nat with (KEEP + 103)%nat; apply (V'_keep E HSP)).
    assert (K102 : V 1102%nat = bv_unsigned (ev E 102%nat)) by (unfold V, V_of; fold E; change 1102%nat with (KEEP + 102)%nat; apply (V'_keep E HSP)).
    apply (all_pairs_ok V asan_ledger (vm_maps (m_vmmaps mdl))).
    - rewrite MAPS. reflexivity.
    - unfold asan_ledger. repeat (apply Forall_cons; [cbn [led_ok zv]; first
        [ (* [comment removed for export] *)
          match goal with |- 0 <= 4096 * V ?k < _ /\ _ =>
            let i := match k with 487%nat => constr:(107%nat) | 568%nat => constr:(106%nat) | 470%nat => constr:(105%nat) | 469%nat => constr:(104%nat)
                                | 393%nat => constr:(83%nat) | 310%nat => constr:(60%nat) | 245%nat => constr:(46%nat) | 228%nat => constr:(38%nat)
                                | 227%nat => constr:(37%nat) | 226%nat => constr:(36%nat) | 208%nat => constr:(28%nat) | 207%nat => constr:(27%nat)
                                | 78%nat => constr:(26%nat) | 700%nat => constr:(7%nat) end in
            rewrite (VP i k ltac:(apply in_nat2_b; vmeq_refl)); split; [apply u64_range | lia] end
        | split; lia
        | rewrite ?K103, ?K102; split; [apply u64_range | lia] ] |]). apply Forall_nil.
    - destruct HM as (HB & _). destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
      apply ivs_apart_sep. rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). exact (mf_apart _ _ _ _ _ _ _ _ _ F).
  Qed.
End Entry.
End TwB.
End MainReadyC.

(* [comment removed for export] *)
Module MainReady.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot2 BootS1 BootS2 BootS3 BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS5 BootS6 BootS7 BootS8 BootState. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootS10a BootExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RelSpec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require A3Kn MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainAux MainShadow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require RegsEqv0__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.RegsEqv0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.SrzEqv.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyC.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Instance mainready_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.

(* [comment removed for export] *)
Lemma ashadow0_range : forall V m lo n,
  ashadow0 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a /\ ~ ashadow_vis V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at SEGS m lo n /\ rw_cells SEGS m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold ashadow in Slo, Shi.
  apply overlay_zero_rw; [lia| unfold MainExport.two64; lia| lia| exact Z0].
Qed.

Lemma ashadow1_range : forall V m lo n,
  ashadow1 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a /\ ~ ashadow_exposed V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at SEGS m lo n /\ rw_cells SEGS m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold ashadow in Slo, Shi.
  apply overlay_zero_rw; [lia| unfold MainExport.two64; lia| lia| exact Z0].
Qed.

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Hypothesis HLIM : 2 ^ 33 <= lim.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.

  #[using="VI VE HLIM usp"] Theorem at_main_amodel : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    amodel (V_of sp draw inp a tid c pl js) en inp lim mdl.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (at_main_model sp brk mbase draw lim inp (mkst R (Z_to_bv 64 A_main) M ROM) mdl
                  (ex_intro _ w1 (ex_intro _ a (ex_intro _ tid (ex_intro _ c (ex_intro _ pl (ex_intro _ p8 (ex_intro _ sb (ex_intro _ p10
                  (ex_intro _ p12 (ex_intro _ p15 (ex_intro _ p24 (ex_intro _ W (ex_intro _ lb (ex_intro _ js (ex_intro _ R (ex_intro _ M
                  (conj Hjs (conj eq_refl HM))))))))))))))))))) as
      (G1 & G2 & G3 & (tid' & G4 & G4') & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
    pose proof (at_main_abytes sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as [AB AW]. fold V in AB, AW.
    pose proof HM as (HB & HW & Hlb & _).
    pose proof HB as [HR HKN HA HZ HLZ HMI F HMO RG HT Hcl Ht].
    constructor.
    - exact G1.
    - exact G2.
    - exact G3.
    - exact G5.
    - exact G7.
    - exists lb. split; [exact Hlb|]. exact (mf_brk _ _ _ _ _ _ _ _ _ F).
    - exact G8.
    - exact G6.
    - cbn [en_sp]. pose proof (SL sp brk mbase draw inp VI VE). pose proof (SH sp brk mbase draw inp VI VE). pose proof (SA16 sp brk mbase draw inp VI VE). auto.
    - exact G9.
    - rewrite (at_main_maps sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM). apply ledger_den_list. reflexivity.
    - apply ivs_apart_sep. rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). exact (mf_apart _ _ _ _ _ _ _ _ _ F).
    - exact (at_main_bounds sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - exact (at_main_lazy_bounds sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - destruct G11 as (_ & WN & _). apply Forall_forall. intros iv Hiv. pose proof (WN iv Hiv) as X. unfold iv_wf, B, BackingAlgebra.S in X. exact X.
    - exact (at_main_totsz sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - exact G12.
    - exact AB.
    - unfold asan_abytes in AB. clear - AB G12 HLIM. lia.
    - exact AW.
    - exact (minv_nodup _ _ HMI).
    - intros p Hp. split; [exact (minv_aligned _ _ HMI p Hp)|]. split; [exact (minv_lazy _ _ HMI p Hp)|].
      exact (at_main_allowed sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM p (minv_aligned _ _ HMI p Hp) (minv_allowed _ _ HMI p Hp)).
    - rewrite G3. apply RelSpec.in_fs_noabs. destruct VI as (_ & _ & _ & VR & _). exact VR.
    - intros t Ht'. rewrite G4 in Ht'. injection Ht' as <-. unfold PID_MAX_ENVELOPE. lia.
    - exact G11.
    - unfold NodesA.sh_entry_ok. cbn [fst snd]. repeat split; try lia; assumption.
    - unfold NodesA.sh_entry_ok. cbn [fst snd]. repeat split; try lia; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE HLIM"] Theorem at_main_open : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    let ms' := MS (mkRl (main_regs usp (Z.of_nat (length (in_argv inp))) 6165944 (V 1098%nat) (V 1099%nat) (V 1100%nat)))
                  bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None M (seg_rom SEGS) in
    amain_open en inp lim w1 V M ms' mdl
    /\ cfg_eqv (mkCfg ms' mdl) (mkCfg (mkst R (Z_to_bv 64 A_main) M ROM) mdl).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM V ms'.
    destruct (at_main_facts sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [HMF HPF]. fold V in HMF, HPF.
    apply Forall_app in HMF as [HMF HMFw]. apply Forall_app in HPF as [HPF HPFw].
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PIN). fold V in HVR, PIN.
    destruct (at_main_ro_stk sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [_ STK].
    pose proof (at_main_stack_shadow sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as SSZ. fold V in SSZ.
    pose proof (at_main_pure_win sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as PW. fold V in PW.
    pose proof (at_main_regs sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as RE. fold V in RE.
    split.
    - unfold amain_open. cbn [en_sp en_brk en_draw]. fold usp.
      split; [reflexivity|]. split; [exact HVR|]. split; [exact PIN|].
      split.
      { unfold asan_mem_facts, asan_mem_facts_w. apply Forall_app. split; [apply Forall_app; split; [exact HMF|] | destruct w1; exact HMFw].
        (* [comment removed for export] *)
        destruct PIN as (PV0 & PV6 & PV10 & USP & _).
        pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi, USP.
        assert (V0R : 4294901760 <= V 0%nat <= 4294967296 /\ 0 <= V 10%nat <= 7).
        { rewrite PV0, PV10. fold usp. clear - SLo SHi. Z.div_mod_to_equations. lia. }
        assert (GE : 0 <= zv V STKSH_BASE /\ zv V STKSH_BASE + zv V STKSH_LEN <= two64 /\ 0 <= zv V STKSH_LEN).
        { cbn [zv STKSH_BASE STKSH_LEN]. unfold two64. clear - V0R. lia. }
        destruct GE as (G1 & G2 & G3).
        destruct (overlay_zero_rw SEGS M (zv V STKSH_BASE) (zv V STKSH_LEN) G1 G2 G3 SSZ) as [WR _].
        destruct (at_main_stackstore sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [SSW SSZ2]. fold V in SSW, SSZ2.
        unfold asan_mem_facts_d. repeat apply Forall_cons; try apply Forall_nil; cbn [mfact_ok zv]; [exact WR | exact SSZ | exact SSW | exact SSZ2]. }
      split.
      { unfold asan_pure_facts, asan_pure_facts_d, asan_pure_facts_w. apply Forall_app. split; [| destruct w1; exact HPFw].
        apply Forall_app. split; [exact HPF|]. apply Forall_app. split; [exact PW|]. apply Forall_app.
        split; [exact (at_main_pure_x sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM)|]. apply Forall_app.
        split; [apply psym_ok; apply Forall_app; split; [exact HPF | exact PW]|].
        exact (at_main_pure_led sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM). }
      split; [exact (at_main_mem_inv sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM)|].
      split; [exact STK|].
      split.
      { intros x Hx. destruct HM as (HB & _). destruct HB as [_ _ HA _ _ _ _ _ _ _ _ _].
        apply HA. unfold wa. pose proof (u64_range sp) as SR. fold usp in SR. rewrite u_small by lia. fold usp. lia. }
      split; [exact (at_main_ashadow0 sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM)|].
      split; [exact (at_main_amodel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM)|].
      exact (at_main_ashadow1 sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - unfold ms'. change (mkst R (Z_to_bv 64 A_main) M ROM) with (MS R bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None M (seg_rom SEGS)).
      apply cfg_eqv_regs. apply regs_eqv0_sym. exact RE.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE HLIM usp"] Theorem boot_main_ready : forall (K : TSet),
    (forall ms mo, amain_at en inp lim ms mo -> srealizes SEGS (mkCfg ms mo) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K HK. apply (boot_main_cps sp brk mbase draw lim inp VI VE K ltac:(clear - HLIM; lia)).
    intros ms mdl (w1 & a & tid & c & pl & p8 & sb & p10 & p12 & p15 & p24 & W & lb & js & R & M & Hjs & -> & HM).
    destruct (at_main_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [OP EQV].
    eapply srealizes_eqv; [| exact EQV]. apply HK. eexists w1, _, M. exact OP.
  Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2 BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootExport.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.A3Kn.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainEntry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainShadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.RegsEqv0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.RegsEqv0__AS.SrzEqv.TwB.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyC.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Instance mainready_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.

(* [comment removed for export] *)
Lemma ashadow0_range : forall V m lo n,
  ashadow0 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a /\ ~ ashadow_vis V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at SEGS m lo n /\ rw_cells SEGS m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold ashadow in Slo, Shi.
  apply overlay_zero_rw; [lia| unfold AS.MainExport.TwB.two64; lia| lia| exact Z0].
Qed.

Lemma ashadow1_range : forall V m lo n,
  ashadow1 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a /\ ~ ashadow_exposed V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at SEGS m lo n /\ rw_cells SEGS m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold ashadow in Slo, Shi.
  apply overlay_zero_rw; [lia| unfold AS.MainExport.TwB.two64; lia| lia| exact Z0].
Qed.

Section Entry.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Hypothesis HLIM : 2 ^ 33 <= lim.
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation en := (mkEntry sp brk mbase draw).
  Let usp := bv_unsigned sp.

  #[using="VI VE HLIM usp"] Theorem at_main_amodel : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    amodel (V_of sp draw inp a tid c pl js) en inp lim mdl.
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM.
    set (V := V_of sp draw inp a tid c pl js) in *.
    pose proof (at_main_model sp brk mbase draw lim inp (mkst R (Z_to_bv 64 A_main) M ROM) mdl
                  (ex_intro _ w1 (ex_intro _ a (ex_intro _ tid (ex_intro _ c (ex_intro _ pl (ex_intro _ p8 (ex_intro _ sb (ex_intro _ p10
                  (ex_intro _ p12 (ex_intro _ p15 (ex_intro _ p24 (ex_intro _ W (ex_intro _ lb (ex_intro _ js (ex_intro _ R (ex_intro _ M
                  (conj Hjs (conj eq_refl HM))))))))))))))))))) as
      (G1 & G2 & G3 & (tid' & G4 & G4') & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
    pose proof (at_main_abytes sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as [AB AW]. fold V in AB, AW.
    pose proof HM as (HB & HW & Hlb & _).
    pose proof HB as [HR HKN HA HZ HLZ HMI F HMO RG HT Hcl Ht].
    constructor.
    - exact G1.
    - exact G2.
    - exact G3.
    - exact G5.
    - exact G7.
    - exists lb. split; [exact Hlb|]. exact (mf_brk _ _ _ _ _ _ _ _ _ F).
    - exact G8.
    - exact G6.
    - cbn [en_sp]. pose proof (SL sp brk mbase draw inp VI VE). pose proof (SH sp brk mbase draw inp VI VE). pose proof (SA16 sp brk mbase draw inp VI VE). auto.
    - exact G9.
    - rewrite (at_main_maps sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM). apply ledger_den_list. reflexivity.
    - apply ivs_apart_sep. rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). exact (mf_apart _ _ _ _ _ _ _ _ _ F).
    - exact (at_main_bounds sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - exact (at_main_lazy_bounds sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - destruct G11 as (_ & WN & _). apply Forall_forall. intros iv Hiv. pose proof (WN iv Hiv) as X. unfold iv_wf, B, BackingAlgebra.S in X. exact X.
    - exact (at_main_totsz sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - exact G12.
    - exact AB.
    - unfold asan_abytes in AB. clear - AB G12 HLIM. lia.
    - exact AW.
    - exact (minv_nodup _ _ HMI).
    - intros p Hp. split; [exact (minv_aligned _ _ HMI p Hp)|]. split; [exact (minv_lazy _ _ HMI p Hp)|].
      exact (at_main_allowed sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM p (minv_aligned _ _ HMI p Hp) (minv_allowed _ _ HMI p Hp)).
    - rewrite G3. apply RelSpec.in_fs_noabs. destruct VI as (_ & _ & _ & VR & _). exact VR.
    - intros t Ht'. rewrite G4 in Ht'. injection Ht' as <-. unfold PID_MAX_ENVELOPE. lia.
    - exact G11.
    - unfold NodesA.sh_entry_ok. cbn [fst snd]. repeat split; try lia; assumption.
    - unfold NodesA.sh_entry_ok. cbn [fst snd]. repeat split; try lia; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE HLIM"] Theorem at_main_open : forall (w1 : bool) a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    length js = 92%nat ->
    at_mainW sp brk mbase draw lim inp w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    let V := V_of sp draw inp a tid c pl js in
    let ms' := MS (mkRl (main_regs usp (Z.of_nat (length (in_argv inp))) 6166968 (V 1098%nat) (V 1099%nat) (V 1100%nat)))
                  bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None M (seg_rom SEGS) in
    amain_open en inp lim w1 V M ms' mdl
    /\ cfg_eqv (mkCfg ms' mdl) (mkCfg (mkst R (Z_to_bv 64 A_main) M ROM) mdl).
  Proof.
    intros w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM V ms'.
    destruct (at_main_facts sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [HMF HPF]. fold V in HMF, HPF.
    apply Forall_app in HMF as [HMF HMFw]. apply Forall_app in HPF as [HPF HPFw].
    destruct (at_main_pins sp brk mbase draw lim inp VI VE w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl HM) as (HVR & PIN). fold V in HVR, PIN.
    destruct (at_main_ro_stk sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [_ STK].
    pose proof (at_main_stack_shadow sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as SSZ. fold V in SSZ.
    pose proof (at_main_pure_win sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as PW. fold V in PW.
    pose proof (at_main_regs sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM) as RE. fold V in RE.
    split.
    - unfold amain_open. cbn [en_sp en_brk en_draw]. fold usp.
      split; [reflexivity|]. split; [exact HVR|]. split; [exact PIN|].
      split.
      { unfold asan_mem_facts, asan_mem_facts_w. apply Forall_app. split; [apply Forall_app; split; [exact HMF|] | destruct w1; exact HMFw].
        (* [comment removed for export] *)
        destruct PIN as (PV0 & PV6 & PV10 & USP & _).
        pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi. fold usp in SLo, SHi, USP.
        assert (V0R : 4294901760 <= V 0%nat <= 4294967296 /\ 0 <= V 10%nat <= 7).
        { rewrite PV0, PV10. fold usp. clear - SLo SHi. Z.div_mod_to_equations. lia. }
        assert (GE : 0 <= zv V STKSH_BASE /\ zv V STKSH_BASE + zv V STKSH_LEN <= two64 /\ 0 <= zv V STKSH_LEN).
        { cbn [zv STKSH_BASE STKSH_LEN]. unfold two64. clear - V0R. lia. }
        destruct GE as (G1 & G2 & G3).
        destruct (overlay_zero_rw SEGS M (zv V STKSH_BASE) (zv V STKSH_LEN) G1 G2 G3 SSZ) as [WR _].
        destruct (at_main_stackstore sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [SSW SSZ2]. fold V in SSW, SSZ2.
        unfold asan_mem_facts_d. repeat apply Forall_cons; try apply Forall_nil; cbn [mfact_ok zv]; [exact WR | exact SSZ | exact SSW | exact SSZ2]. }
      split.
      { unfold asan_pure_facts, asan_pure_facts_d, asan_pure_facts_w. apply Forall_app. split; [| destruct w1; exact HPFw].
        apply Forall_app. split; [exact HPF|]. apply Forall_app. split; [exact PW|]. apply Forall_app.
        split; [exact (at_main_pure_x sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM)|]. apply Forall_app.
        split; [apply psym_ok; apply Forall_app; split; [exact HPF | exact PW]|].
        exact (at_main_pure_led sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM). }
      split; [exact (at_main_mem_inv sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM)|].
      split; [exact STK|].
      split.
      { intros x Hx. destruct HM as (HB & _). destruct HB as [_ _ HA _ _ _ _ _ _ _ _ _].
        apply HA. unfold wa. pose proof (u64_range sp) as SR. fold usp in SR. rewrite u_small by lia. fold usp. lia. }
      split; [exact (at_main_ashadow0 sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM)|].
      split; [exact (at_main_amodel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM)|].
      exact (at_main_ashadow1 sp brk mbase draw lim inp VI VE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
    - unfold ms'. change (mkst R (Z_to_bv 64 A_main) M ROM) with (MS R bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None M (seg_rom SEGS)).
      apply cfg_eqv_regs. apply regs_eqv0_sym. exact RE.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE HLIM usp"] Theorem boot_main_ready : forall (K : TSet),
    (forall ms mo, amain_at en inp lim ms mo -> srealizes SEGS (mkCfg ms mo) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K HK. apply (boot_main_cps sp brk mbase draw lim inp VI VE K ltac:(clear - HLIM; lia)).
    intros ms mdl (w1 & a & tid & c & pl & p8 & sb & p10 & p12 & p15 & p24 & W & lb & js & R & M & Hjs & -> & HM).
    destruct (at_main_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HM) as [OP EQV].
    eapply srealizes_eqv; [| exact EQV]. apply HK. eexists w1, _, M. exact OP.
  Qed.
End Entry.
End TwB.
End MainReady.
