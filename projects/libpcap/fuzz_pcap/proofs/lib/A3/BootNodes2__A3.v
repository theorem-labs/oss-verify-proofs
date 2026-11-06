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
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require MuslMemset A3Sums.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanMemIsZero.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootNodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module BootNodes2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import MuslMemset A3Sums.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootNodes. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hcut (H : word -> bool) (lo n : Z) : word -> bool :=
  fun x => H x && negb ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + n)).

Lemma hcut_true : forall H lo n x, hcut H lo n x = true <-> H x = true /\ (bv_unsigned x < lo \/ lo + n <= bv_unsigned x).
Proof.
  intros H lo n x. unfold hcut. rewrite andb_true_iff, negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. tauto.
Qed.
Lemma hcut_old : forall H lo n x, hcut H lo n x = true -> H x = true.
Proof. intros H lo n x Hx. apply hcut_true in Hx. tauto. Qed.
Lemma hcut_false_in : forall H lo n x, lo <= bv_unsigned x < lo + n -> hcut H lo n x = false.
Proof.
  intros H lo n x Hx. unfold hcut. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn [andb negb]. apply andb_false_r.
Qed.
Lemma hcut_false_of : forall H lo n x, H x = false -> hcut H lo n x = false.
Proof. intros H lo n x Hx. unfold hcut. rewrite Hx. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ivs_apart_split : forall l (b s lo n : word),
  ivs_apart l -> In (b, s) l ->
  bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s -> 0 < bv_unsigned n ->
  exists l1 l2, l = l1 ++ (b, s) :: l2 /\ region_free (l1 ++ l2) lo n = true.
Proof.
  induction l as [|[b0 s0] l IH]; intros b s lo n HA Hin Hlo Hhi Hn; [destruct Hin|].
  cbn [ivs_apart] in HA. destruct HA as [HF HA]. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. exists [], l. split; [reflexivity|]. cbn [app].
    apply RefNodes.region_free_intro. intros b2 s2 Hin2. pose proof (proj1 (Forall_forall _ _) HF _ Hin2) as X. cbn [fst snd] in X. lia.
  - destruct (IH b s lo n HA Hin Hlo Hhi Hn) as (l1 & l2 & -> & Hrf). exists ((b0, s0) :: l1), l2. split; [reflexivity|].
    cbn [app region_free]. rewrite Hrf.
    pose proof (proj1 (Forall_forall _ _) HF (b, s) ltac:(apply in_app_iff; right; left; reflexivity)) as X. cbn [fst snd] in X.
    unfold iv_overlap.
    destruct X as [X|X]; [rewrite (proj2 (Z.ltb_ge (bv_unsigned lo) _)) by lia | rewrite (proj2 (Z.ltb_ge (bv_unsigned b0) _)) by lia];
      cbn [andb negb]; rewrite ?andb_false_r; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tiles_within : forall (l : list (word * word)) lo hi,
  tiles lo hi (List.map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) l) = true ->
  forall b s, In (b, s) l -> lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi.
Proof.
  induction l as [|[b0 s0] l IH]; intros lo hi Ht b s Hin; [destruct Hin|].
  cbn [tiles List.map fst snd] in Ht. apply andb_prop in Ht as [Ht Hr]. apply andb_prop in Ht as [Hb Hs].
  apply Z.eqb_eq in Hb. apply Z.leb_le in Hs.
  assert (TL : forall l' lo' hi', tiles lo' hi' l' = true -> Forall (fun q => 0 <= snd q) l' -> lo' <= hi').
  { clear. induction l' as [|[b s] l' IH]; cbn [tiles]; intros lo' hi' Ht Hp.
    - apply Z.eqb_eq in Ht. lia.
    - apply andb_prop in Ht as [Ht Hr]. apply andb_prop in Ht as [_ Hs]. apply Z.leb_le in Hs.
      apply Forall_cons_iff in Hp as [_ Hp]. pose proof (IH _ _ Hr Hp). lia. }
  assert (NN : Forall (fun q : Z * Z => 0 <= snd q) (List.map (fun p : word * word => (bv_unsigned (fst p), bv_unsigned (snd p))) l)).
  { apply Forall_forall. intros q Hq. apply in_map_iff in Hq as (p0 & <- & _). cbn [snd]. pose proof (u64_range (snd p0)). lia. }
  pose proof (TL _ _ _ Hr NN) as LE.
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. lia.
  - pose proof (IH _ _ Hr b s Hin). pose proof (u64_range s0). lia.
Qed.

Lemma reserved_free_of_apart : forall (a n : word),
  bv_unsigned a + bv_unsigned n <= A_img_lo \/ A_img_hi <= bv_unsigned a ->
  region_free (segments_reserved SEGS) a n = true.
Proof.
  intros a n Hap. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (tiles_within (segments_reserved SEGS) A_img_lo A_img_hi reserved_tiles b s Hin). lia.
Qed.

Section Theorems4.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  Definition lcommit (L : ledger) (n : Z) : ledger := Ledger (l_maps L) (l_brk L) (l_eager L + n).

  #[using="VI VE usp"] Theorem bs_mmap_fixedin_rw : forall H A a tid c pl js sr kn L hc lz R M mdl (eb : expr) (eo len pc : Z) (em : expr) (nm : Z) w (K : TSet),
    let E := EB' a tid c pl js in
    let nZ := page_round_up_Z len in
    let lo := bv_unsigned (edenot E eb) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> split_lit (sr_get sr 10%bv) = (eb, eo) -> sr_get sr 11%bv = ELit len ->
    sr_get sr 12%bv = ELit 3 -> sr_get sr 13%bv = ELit 50 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len ->
    In (em, nm) (l_maps L) -> sivs_sizes_ok (l_maps L) = true ->
    bv_unsigned (edenot E em) <= lo -> lo + nZ <= bv_unsigned (edenot E em) + nm -> lo mod 4096 = 0 ->
    (forall x : word, lo <= bv_unsigned x < lo + nZ -> H x = true) ->
    Forall (fun iv => snd iv <= lo \/ lo + nZ <= fst iv) A ->
    l_eager L + nZ + A_bytes A <= lim ->
    (forall R' mdl',
       bootS' (hcut H lo nZ) A a tid c pl js sr
              ([KZero (SA eb eo) (ELit nZ); KWr (SA eb eo) (ELit nZ)] ++ kn_keep MGrow kn kn eb eo (ELit nZ))
              (lcommit L nZ) hc (maps_subtract lz lo (lo + nZ)) R' (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl eb eo len pc em nm w K E nZ lo HB HF HE Hpc0 Hpc4
           S17 S10 S11 S12 S13 S14 S15 Hlen Hin Hs Hlo1 Hhi1 Hal Hhid HA2 Hbud HK. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. split; [lia|]. split; [lia|].
      unfold page_round_up_Z, page_size. apply Z_mod_mult. }
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    set (addr := Z_to_bv 64 lo).
    assert (Haddr : edenot (EB sp draw inp a tid c pl js) (sr_get sr 10%bv) = addr).
    { rewrite (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    set (n := Z_to_bv 64 nZ).
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
    pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hnm. cbn [snd] in Hnm.
    apply andb_prop in Hnm as [N0 N1]. apply Z.leb_le in N0. apply Z.ltb_lt in N1.
    assert (HinM : In (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (em, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) addr n = true).
    { unfold map_contains. apply existsb_exists. exists (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
    (* [comment removed for export] *)
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    assert (APM : ivs_apart (vm_maps (m_vmmaps mdl))) by (rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact APM0).
    destruct (ivs_apart_split _ _ _ addr n APM HinM
                ltac:(rewrite Ulo; lia) ltac:(rewrite Ulo, Hun, (u_small nm) by lia; lia) ltac:(rewrite Hun; lia)) as (l1 & l2 & EQM & Hrf12).
    pose proof (overlap_sum_one l1 (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) l2 addr n Hrf12) as OV.
    rewrite <- EQM, Ulo, Hun in OV.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdl addr n = true).
    { apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact (mf_wf _ _ _ _ _ _ _ _ _ F) |].
      rewrite vm_backing_used_split, Ulo, Hun, LIM. unfold page_size. cbn [lcommit l_eager] in Hbud. lia. }
    (* [comment removed for export] *)
    assert (Hrfr : region_free (vm_reserved (m_vmmaps mdl)) addr n = true).
    { rewrite (mf_res _ _ _ _ _ _ _ _ _ F). apply reserved_free_of_apart. rewrite Ulo, Hun. lia. }
    eapply (srz_mmap_fixedin_top SEGS R (Z_to_bv 64 pc) M ROM mdl w 3 (Z_to_bv 64 50) addr len K HF HE
              (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (or_intror eq_refl) mmap_flags_core_32).
    - rewrite (HR 10%bv). exact Haddr.
    - rewrite Ulo. unfold page_size. exact Hal.
    - rewrite Ulo. lia.
    - exact (G _ _ S11).
    - exact Hlen.
    - rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F), Ulo. fold nZ. unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - exact (G _ _ S13).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact Hrfr.
    - exact Hmc.
    - intros _. exact Hbud'.
    - (* [comment removed for export] *)
      cbn [Z.eqb]. rewrite pc_lit_add4 by lia. fold nZ n.
        set (mdl' := fixedin_ok_model 3 (Z_to_bv 64 50) addr n mdl).
      assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) eb) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
      assert (EQV : mrestrict (hcut H lo nZ) (zfill addr n M) = zfill addr n (mrestrict H M)).
      { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
        destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + nZ)); cbn [andb negb];
          rewrite ?andb_false_r, ?andb_true_r; try reflexivity; destruct (H x); reflexivity. }
      pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
      assert (LZout : forall p, page_in_ranges p (m_vm_lazy mdl') = true ->
                      page_in_ranges p (m_vm_lazy mdl) = true /\ (bv_unsigned p + 4096 <= lo \/ lo + nZ <= bv_unsigned p)).
      { intros p Hp. unfold mdl' in Hp. rewrite (fixedin_eager_lazy (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32) in Hp.
        split; [eapply pages_sub_maps_subtract; [exact W3 | | exact Hp]; rewrite Ulo, Hun; lia|].
        apply page_in_ranges_true in Hp as (q & Hq & Q1 & Q2).
        destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & R3). rewrite Ulo, Hun in R3. unfold page_size in Q2. lia. }
      apply (HK (regupd R 10%bv addr) mdl'). fold addr n. constructor.
      + apply (AsanNodesMmB.regs_ok_regupd_same _ sr R _ addr HR); [| intros X; apply (f_equal bv_unsigned) in X; discriminate X].
        rewrite (HR 10%bv). exact Haddr.
      + rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
        constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
        rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr n (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx. apply hcut_true in Hhx as [Hhd Hout].
        rewrite zfill_out by (rewrite Ulo, Hun; exact Hout). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhd).
      + unfold mdl'. rewrite (fixedin_eager_lazy (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32), Ulo, Hun, HLZ. reflexivity.
      + unfold mdl'. apply (MInv_fixedin_eager A (Z_to_bv 64 50) addr n mdl (mf_wf _ _ _ _ _ _ _ _ _ F)).
        * rewrite Ulo. unfold page_size. exact Hal.
        * rewrite Hun. unfold page_size. tauto.
        * rewrite Hun. lia.
        * apply mmap_noreserve_b_32.
        * constructor; assumption.
        * rewrite Ulo, Hun, LIM. cbn [lcommit l_eager] in Hbud. lia.
      + (* [comment removed for export] *)
        pose proof (fixedin_eager_unfold (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32) as UF.
        pose proof (model_ivs_wf_fixedin_eager (Z_to_bv 64 50) addr n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) ltac:(rewrite Hun; lia) mmap_noreserve_b_32) as WF'.
        pose proof (eager_used_fixedin_eager_le (Z_to_bv 64 50) addr n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) ltac:(rewrite Hun; lia) mmap_noreserve_b_32) as EGL.
        rewrite Ulo, Hun in EGL. unfold mdl'.
        constructor; cbn [lcommit l_maps l_brk l_eager].
        * rewrite (fixedin_eager_halted _ _ _ _ mmap_noreserve_b_32). exact Hh.
        * rewrite (fixedin_eager_reserved _ _ _ _ mmap_noreserve_b_32). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_init_sp _ _ _ _ mmap_noreserve_b_32). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_limit _ _ _ _ mmap_noreserve_b_32). exact LIM.
        * etransitivity; [| exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_brk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_mb _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * rewrite (fixedin_eager_maps _ _ _ _ mmap_noreserve_b_32). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (fixedin_eager_fs _ _ _ _ mmap_noreserve_b_32). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_fds _ _ _ _ mmap_noreserve_b_32). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_tid _ _ _ _ mmap_noreserve_b_32). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fixedin_eager_noaccess _ _ _ _ mmap_noreserve_b_32).
          apply na_clear_l_sub; [exact (proj1 (proj2 (mf_wf _ _ _ _ _ _ _ _ _ F))) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + (* [comment removed for export] *) exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
        * exact HAW.
        * intros x Hpx Hhx. destruct (LZout _ Hpx) as [Hp Hout]. apply (HCOV x Hp).
          unfold hcut in Hhx. apply andb_false_iff in Hhx as [Hhx|Hhx]; [exact Hhx|]. exfalso.
          apply negb_false_iff in Hhx. apply andb_prop in Hhx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size in Hout.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small in Hout by lia.
          assert (lo mod 4096 = 0 /\ nZ mod 4096 = 0) as [L1 L2] by (split; [exact Hal | tauto]).
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)). nia.
        * intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
        * exact Hhin.
        * intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
        * intros x Hx. apply hcut_true in Hx as [Hx Hout]. unfold mdl'.
          rewrite (fixedin_eager_lazy (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32), Ulo, Hun.
          rewrite page_in_ranges_subtract_out; [exact (Hhl x Hx) | exact W3 | lia |].
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia.
          assert (lo mod 4096 = 0 /\ nZ mod 4096 = 0) as [L1 L2] by (split; [exact Hal | tauto]).
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)). nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems5.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    bv_unsigned (edenot E e) + eo = lo ->
    (forall x : word, lo <= bv_unsigned x < lo + n -> H x = true) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= lo -> lo + n <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H lo n) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit n); KWr (SA e eo) (ELit n)] ++ kn_keep MGrow kn kn e eo (ELit n)) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo lo n rlo rhi E HB Hlo Hn Hpos Hlo0 Htop He Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (addr := Z_to_bv 64 lo). set (nw := Z_to_bv 64 n).
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = n) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, lo <= bv_unsigned x < lo + n -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) (Hhid x Hx)). }
    assert (EQV : mrestrict (hcut H lo n) M = zfill addr nw (mrestrict H M)).
    { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
      destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + n)); cbn [andb negb];
        rewrite ?andb_false_r, ?andb_true_r; try (destruct (H x); reflexivity).
      apply ZERO. lia. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; exact He).
    constructor.
    - exact HR.
    - rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose2 : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = true) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit m); KWr (SA e eo) (ELit m)] ++ kn_keep MGrow kn kn e eo (ELit m)) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)) as Ue.
    set (addr := Z_to_bv 64 d). set (nw := Z_to_bv 64 m).
    assert (Ulo : bv_unsigned addr = d) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = m) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) (Hhid x Hx)). }
    assert (EQV : mrestrict (hcut H d m) M = zfill addr nw (mrestrict H M)).
    { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
      destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb negb];
        rewrite ?andb_false_r, ?andb_true_r; try (destruct (H x); reflexivity).
      apply ZERO. lia. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
    constructor.
    - exact HR.
    - rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.

(* [comment removed for export] *)
Lemma know_ok_sub_b : forall segs E M kn1 kn2,
  forallb (fun k => existsb (APC.kentry_eqb k) kn1) kn2 = true -> know_ok segs E M kn1 -> know_ok segs E M kn2.
Proof.
  intros segs E M kn1 kn2 Hb HK. unfold know_ok in *. apply Forall_forall. intros k Hk.
  pose proof (proj1 (forallb_forall _ _) Hb k Hk) as Hx. apply existsb_exists in Hx as (k' & Hk' & He).
  apply KNA.kentry_eqb_eq in He. subst k'. exact (proj1 (Forall_forall _ _) HK k Hk').
Qed.

Lemma kn_vars_lt_filter : forall b f kn, kn_vars_lt b kn = true -> kn_vars_lt b (List.filter f kn) = true.
Proof.
  induction kn as [|K kn IH]; cbn [kn_vars_lt List.filter]; intros Hk; [reflexivity|].
  apply andb_prop in Hk as [H1 H2]. destruct (f K); cbn [kn_vars_lt]; rewrite ?H1, (IH H2); reflexivity.
Qed.

Section Theorems6.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memset : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo : Z) (iW : nat) (wlen cv n ret : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    sr_get sr 11%bv = ELit cv -> 0 <= cv < 2 ^ 64 ->
    edenot E (sr_get sr 12%bv) = Z_to_bv 64 n -> 0 <= n ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e eo) (ELit wlen)) -> n <= wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n <= bv_unsigned sp - stack_max_size ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' memset_clob) (sr_after_call_c sr memset_clob v)
              (KFill (SA e eo) (ELit n) cv :: kn_keep MGrow kn kn e eo (ELit n)) L hc lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo iW wlen cv n ret K E v d HB Hsr Hkn HL Hev S10 S11 Hcv S12 Hn S1 Hret HiW Hnw Hwlen Hd0 Hdn HK.
    subst E. unfold v in *. clear v.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d).
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; unfold stack_max_size in *; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 cv) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 n) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw (Z.to_nat n) = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e eo wlen eo (Z.to_nat n) HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    destruct (musl_memset_summary V dw (Z_to_bv 64 cv) (Z_to_bv 64 ret) n ROM R Hn ltac:(rewrite Ud; unfold stack_max_size in *; lia)
                Hst Hret G10 G11 G12 G1) as (R' & MS & P10 & AG & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memset) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := repeat (cbyte (Z_to_bv 64 cv)) (Z.to_nat n)) in *.
    set (V' := wbytes V dw bs) in *.
    assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; [unfold stack_max_size in *; lia | lia]. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      rewrite EB_app. apply (regs_after_clob memset_clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
      + intros r Hr. apply AG. exact Hr.
      + cbn. intros [X|[X|[X|[X|[X|[X|[]]]]]]]; apply (f_equal bv_unsigned) in X; discriminate X.
      + repeat constructor; cbn; intros X; repeat (destruct X as [X|X]; [apply (f_equal bv_unsigned) in X; discriminate X|]); exact X.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. rewrite Hev. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. exact Hkn. }
      constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        fold (EB sp draw inp a tid c pl js). fold d. rewrite !u_small by lia.
        split; [unfold stack_max_size in *; lia|].
        intros i Hi. unfold V'.
        replace (Z_to_bv 64 (d + i)) with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat i))) by (f_equal; rewrite Ud; lia).
        rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
        unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity.
      + apply (kn_keep_sound SEGS _ V V' MGrow); [exact HKN | exact HKN |].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold d. rewrite u_small by lia.
        rewrite <- Ud. replace n with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes.
        rewrite LEN, Ud. unfold stack_max_size in *. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold stack_max_size in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memset_c : forall (clob : list reg) H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo : Z) (iW : nat) (weo wlen cv n ret : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    incl memset_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    sr_get sr 11%bv = ELit cv -> 0 <= cv < 2 ^ 64 ->
    edenot E (sr_get sr 12%bv) = Z_to_bv 64 n -> 0 <= n ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e weo) (ELit wlen)) -> weo <= eo -> eo + n <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n <= bv_unsigned sp ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' clob) (sr_after_call_c sr clob v)
              (KFill (SA e eo) (ELit n) cv :: kn_keep MGrow kn kn e eo (ELit n)) L hc lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros clob H A a tid c pl js sr kn L hc lz R M mdl e eo iW weo wlen cv n ret K E v d HB Hincl Hc0 Hnd Hsr Hkn HL Hev S10 S11 Hcv S12 Hn S1 Hret HiW Hweo Hnw Hwlen Hd0 Hdn HK.
    subst E. unfold v in *. clear v.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d).
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; unfold stack_max_size in *; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 cv) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 n) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw (Z.to_nat n) = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e weo wlen eo (Z.to_nat n) HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    destruct (musl_memset_summary V dw (Z_to_bv 64 cv) (Z_to_bv 64 ret) n ROM R Hn ltac:(rewrite Ud; unfold stack_max_size in *; lia)
                Hst Hret G10 G11 G12 G1) as (R' & MS & P10 & AG & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memset) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := repeat (cbyte (Z_to_bv 64 cv)) (Z.to_nat n)) in *.
    set (V' := wbytes V dw bs) in *.
    assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; [unfold stack_max_size in *; lia | lia]. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      rewrite EB_app. apply (regs_after_clob clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
      + intros r Hr. apply AG. intros Hin. apply Hr. apply Hincl. exact Hin.
      + exact Hc0.
      + exact Hnd.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. rewrite Hev. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. exact Hkn. }
      constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        fold (EB sp draw inp a tid c pl js). fold d. rewrite !u_small by lia.
        split; [unfold stack_max_size in *; lia|].
        intros i Hi. unfold V'.
        replace (Z_to_bv 64 (d + i)) with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat i))) by (f_equal; rewrite Ud; lia).
        rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
        unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity.
      + apply (kn_keep_sound SEGS _ V V' MGrow); [exact HKN | exact HKN |].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold d. rewrite u_small by lia.
        rewrite <- Ud. replace n with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes.
        rewrite LEN, Ud. unfold stack_max_size in *. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold stack_max_size in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_mem_is_zero : forall (clob : list reg) H A a tid c pl js sr kn L hc lz R M mdl
      (e : expr) (eo : Z) (es : expr) (so : Z) (iZ iW : nat) (zeo zlen weo wlen n ret : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    let s := bv_unsigned (edenot E es) + so in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    incl memisz_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v es = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    edenot E (sr_get sr 11%bv) = Z_to_bv 64 n -> 0 <= n <= 2 ^ 40 ->
    split_lit (sr_get sr 2%bv) = (es, so) ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iZ = Some (KZero (SA e zeo) (ELit zlen)) -> zeo <= eo -> eo + n <= zeo + zlen -> zlen < 2 ^ 64 ->
    nth_error kn iW = Some (KWr (SA es weo) (ELit wlen)) -> weo <= so - 8 -> so <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n + 8 <= 2 ^ 64 -> 16 <= s -> s <= bv_unsigned sp -> (d + n <= s - 8 \/ s <= d) ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' clob) (sr_upd (sr_after_call_c sr clob v) (ridx 10%bv) (ELit 1))
              (kn_keep MGrow kn kn es (so - 8) (ELit 8)) L hc lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_mem_is_zero) M ROM) mdl) K.
  Proof.
    intros clob H A a tid c pl js sr kn L hc lz R M mdl e eo es so iZ iW zeo zlen weo wlen n ret K E v d s HB Hincl Hc0 Hnd Hsr Hkn HL Hevs
           S10 S11 Hn S2 S1 Hret HiZ Hzeo Hzn Hzlen HiW Hweo Hsow Hwlen Hd0 Hdnw Hs16 Hssp Hapart HK.
    subst E. unfold v in *. clear v.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d). set (sw := Z_to_bv 64 s).
    assert (Us : bv_unsigned sw = s) by (unfold sw; apply u_small; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G2 : getr R 2%bv = sw).
    { rewrite (HR 2%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S2). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 n) by (rewrite (HR 11%bv); exact S11).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    (* [comment removed for export] *)
    pose proof (know_nth _ _ V kn iZ _ HKN HiZ) as (Zfl & Zrd). unfold flat, estart, elenZ in Zfl, Zrd. cbn [a_base a_off edenot] in Zfl, Zrd.
    fold (EB sp draw inp a tid c pl js) in Zfl, Zrd. rewrite !u_small in Zfl, Zrd by lia.
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; lia).
    assert (RD : forall x : word, bv_unsigned dw <= bv_unsigned x < bv_unsigned dw + n -> rdn SEGS V x 1 = Some [Z_to_bv 8 0]).
    { intros x Hx. rewrite Ud in Hx. cbn [rdn].
      replace x with (Z_to_bv 64 (bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + zeo + (bv_unsigned x - (bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + zeo))))
        by (apply bv_eq; rewrite u_small; [lia | pose proof (u64_range x); lia]).
      rewrite (Zrd (bv_unsigned x - (bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + zeo))) by (unfold d in *; lia). reflexivity. }
    assert (Hst : store_ok SEGS V (Z_to_bv 64 (bv_unsigned sw - 8)) 8 = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW es weo wlen (so - 8) 8%nat HKN HiW ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as ST.
      rewrite adenot_SA in ST. rewrite Us. replace (bv_unsigned (edenot (EB sp draw inp a tid c pl js) es) + (so - 8)) with (s - 8) in ST by (unfold s; lia). exact ST. }
    destruct (a3_mem_is_zero V dw sw n ROM R (Z_to_bv 64 ret) Hn ltac:(rewrite Ud; lia) ltac:(rewrite Us; lia) Hst
                ltac:(rewrite Ud, Us; lia) RD Hret G1 G2 G10 G11) as (R' & MS & AG & P10 & P2 & P1).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_mem_is_zero) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := word_to_le_bytes 8 (Z_to_bv 64 ret)) in *.
    rewrite Us in *. set (aw := Z_to_bv 64 (s - 8)) in *.
    set (V' := wbytes V aw bs) in *.
    assert (LEN : length bs = 8%nat) by (unfold bs; apply length_N_to_le_bytes).
    assert (Ua : bv_unsigned aw = s - 8) by (unfold aw; apply u_small; lia).
    assert (V'out : forall x : word, bv_unsigned x < s - 8 \/ s <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ua; [lia | cbn; lia]. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      rewrite EB_app. eapply (regs_ok_upd1 _ _ R' R' 10%bv (ELit 1)).
      + apply (regs_after_clob clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
        * intros r Hr. apply AG. intros Hin. apply Hr. apply Hincl. exact Hin.
        * exact Hc0.
        * exact Hnd.
      + intros X. apply (f_equal bv_unsigned) in X. discriminate X.
      + exact P10.
      + intros r _. reflexivity.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { unfold kn_keep. apply kn_vars_lt_filter. exact Hkn. }
      apply (kn_keep_sound SEGS _ V V' MGrow); [exact HKN | exact HKN |].
      unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite u_small by lia.
      replace (bv_unsigned (edenot (EB sp draw inp a tid c pl js) es) + (so - 8)) with (bv_unsigned aw) by (rewrite Ua; unfold s; lia).
      replace 8 with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes. rewrite LEN, Ua. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by lia. unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems6.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.MuslMemset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Sums.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hcut (H : word -> bool) (lo n : Z) : word -> bool :=
  fun x => H x && negb ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + n)).

Lemma hcut_true : forall H lo n x, hcut H lo n x = true <-> H x = true /\ (bv_unsigned x < lo \/ lo + n <= bv_unsigned x).
Proof.
  intros H lo n x. unfold hcut. rewrite andb_true_iff, negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. tauto.
Qed.
Lemma hcut_old : forall H lo n x, hcut H lo n x = true -> H x = true.
Proof. intros H lo n x Hx. apply hcut_true in Hx. tauto. Qed.
Lemma hcut_false_in : forall H lo n x, lo <= bv_unsigned x < lo + n -> hcut H lo n x = false.
Proof.
  intros H lo n x Hx. unfold hcut. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn [andb negb]. apply andb_false_r.
Qed.
Lemma hcut_false_of : forall H lo n x, H x = false -> hcut H lo n x = false.
Proof. intros H lo n x Hx. unfold hcut. rewrite Hx. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ivs_apart_split : forall l (b s lo n : word),
  ivs_apart l -> In (b, s) l ->
  bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s -> 0 < bv_unsigned n ->
  exists l1 l2, l = l1 ++ (b, s) :: l2 /\ region_free (l1 ++ l2) lo n = true.
Proof.
  induction l as [|[b0 s0] l IH]; intros b s lo n HA Hin Hlo Hhi Hn; [destruct Hin|].
  cbn [ivs_apart] in HA. destruct HA as [HF HA]. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. exists [], l. split; [reflexivity|]. cbn [app].
    apply RefNodes.region_free_intro. intros b2 s2 Hin2. pose proof (proj1 (Forall_forall _ _) HF _ Hin2) as X. cbn [fst snd] in X. lia.
  - destruct (IH b s lo n HA Hin Hlo Hhi Hn) as (l1 & l2 & -> & Hrf). exists ((b0, s0) :: l1), l2. split; [reflexivity|].
    cbn [app region_free]. rewrite Hrf.
    pose proof (proj1 (Forall_forall _ _) HF (b, s) ltac:(apply in_app_iff; right; left; reflexivity)) as X. cbn [fst snd] in X.
    unfold iv_overlap.
    destruct X as [X|X]; [rewrite (proj2 (Z.ltb_ge (bv_unsigned lo) _)) by lia | rewrite (proj2 (Z.ltb_ge (bv_unsigned b0) _)) by lia];
      cbn [andb negb]; rewrite ?andb_false_r; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tiles_within : forall (l : list (word * word)) lo hi,
  tiles lo hi (List.map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) l) = true ->
  forall b s, In (b, s) l -> lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi.
Proof.
  induction l as [|[b0 s0] l IH]; intros lo hi Ht b s Hin; [destruct Hin|].
  cbn [tiles List.map fst snd] in Ht. apply andb_prop in Ht as [Ht Hr]. apply andb_prop in Ht as [Hb Hs].
  apply Z.eqb_eq in Hb. apply Z.leb_le in Hs.
  assert (TL : forall l' lo' hi', tiles lo' hi' l' = true -> Forall (fun q => 0 <= snd q) l' -> lo' <= hi').
  { clear. induction l' as [|[b s] l' IH]; cbn [tiles]; intros lo' hi' Ht Hp.
    - apply Z.eqb_eq in Ht. lia.
    - apply andb_prop in Ht as [Ht Hr]. apply andb_prop in Ht as [_ Hs]. apply Z.leb_le in Hs.
      apply Forall_cons_iff in Hp as [_ Hp]. pose proof (IH _ _ Hr Hp). lia. }
  assert (NN : Forall (fun q : Z * Z => 0 <= snd q) (List.map (fun p : word * word => (bv_unsigned (fst p), bv_unsigned (snd p))) l)).
  { apply Forall_forall. intros q Hq. apply in_map_iff in Hq as (p0 & <- & _). cbn [snd]. pose proof (u64_range (snd p0)). lia. }
  pose proof (TL _ _ _ Hr NN) as LE.
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. lia.
  - pose proof (IH _ _ Hr b s Hin). pose proof (u64_range s0). lia.
Qed.

Lemma reserved_free_of_apart : forall (a n : word),
  bv_unsigned a + bv_unsigned n <= A_img_lo \/ A_img_hi <= bv_unsigned a ->
  region_free (segments_reserved SEGS) a n = true.
Proof.
  intros a n Hap. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (tiles_within (segments_reserved SEGS) A_img_lo A_img_hi reserved_tiles b s Hin). lia.
Qed.

Section Theorems4.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  Definition lcommit (L : ledger) (n : Z) : ledger := Ledger (l_maps L) (l_brk L) (l_eager L + n).

  #[using="VI VE usp"] Theorem bs_mmap_fixedin_rw : forall H A a tid c pl js sr kn L hc lz R M mdl (eb : expr) (eo len pc : Z) (em : expr) (nm : Z) w (K : TSet),
    let E := EB' a tid c pl js in
    let nZ := page_round_up_Z len in
    let lo := bv_unsigned (edenot E eb) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> split_lit (sr_get sr 10%bv) = (eb, eo) -> sr_get sr 11%bv = ELit len ->
    sr_get sr 12%bv = ELit 3 -> sr_get sr 13%bv = ELit 50 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len ->
    In (em, nm) (l_maps L) -> sivs_sizes_ok (l_maps L) = true ->
    bv_unsigned (edenot E em) <= lo -> lo + nZ <= bv_unsigned (edenot E em) + nm -> lo mod 4096 = 0 ->
    (forall x : word, lo <= bv_unsigned x < lo + nZ -> H x = true) ->
    Forall (fun iv => snd iv <= lo \/ lo + nZ <= fst iv) A ->
    l_eager L + nZ + A_bytes A <= lim ->
    (forall R' mdl',
       bootS' (hcut H lo nZ) A a tid c pl js sr
              ([KZero (SA eb eo) (ELit nZ); KWr (SA eb eo) (ELit nZ)] ++ kn_keep MGrow kn kn eb eo (ELit nZ))
              (lcommit L nZ) hc (maps_subtract lz lo (lo + nZ)) R' (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl eb eo len pc em nm w K E nZ lo HB HF HE Hpc0 Hpc4
           S17 S10 S11 S12 S13 S14 S15 Hlen Hin Hs Hlo1 Hhi1 Hal Hhid HA2 Hbud HK. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. split; [lia|]. split; [lia|].
      unfold page_round_up_Z, page_size. apply Z_mod_mult. }
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    set (addr := Z_to_bv 64 lo).
    assert (Haddr : edenot (EB sp draw inp a tid c pl js) (sr_get sr 10%bv) = addr).
    { rewrite (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    set (n := Z_to_bv 64 nZ).
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
    pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hnm. cbn [snd] in Hnm.
    apply andb_prop in Hnm as [N0 N1]. apply Z.leb_le in N0. apply Z.ltb_lt in N1.
    assert (HinM : In (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (em, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) addr n = true).
    { unfold map_contains. apply existsb_exists. exists (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
    (* [comment removed for export] *)
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    assert (APM : ivs_apart (vm_maps (m_vmmaps mdl))) by (rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact APM0).
    destruct (ivs_apart_split _ _ _ addr n APM HinM
                ltac:(rewrite Ulo; lia) ltac:(rewrite Ulo, Hun, (u_small nm) by lia; lia) ltac:(rewrite Hun; lia)) as (l1 & l2 & EQM & Hrf12).
    pose proof (overlap_sum_one l1 (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) l2 addr n Hrf12) as OV.
    rewrite <- EQM, Ulo, Hun in OV.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdl addr n = true).
    { apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact (mf_wf _ _ _ _ _ _ _ _ _ F) |].
      rewrite vm_backing_used_split, Ulo, Hun, LIM. unfold page_size. cbn [lcommit l_eager] in Hbud. lia. }
    (* [comment removed for export] *)
    assert (Hrfr : region_free (vm_reserved (m_vmmaps mdl)) addr n = true).
    { rewrite (mf_res _ _ _ _ _ _ _ _ _ F). apply reserved_free_of_apart. rewrite Ulo, Hun. lia. }
    eapply (srz_mmap_fixedin_top SEGS R (Z_to_bv 64 pc) M ROM mdl w 3 (Z_to_bv 64 50) addr len K HF HE
              (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (or_intror eq_refl) mmap_flags_core_32).
    - rewrite (HR 10%bv). exact Haddr.
    - rewrite Ulo. unfold page_size. exact Hal.
    - rewrite Ulo. lia.
    - exact (G _ _ S11).
    - exact Hlen.
    - rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F), Ulo. fold nZ. unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - exact (G _ _ S13).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact Hrfr.
    - exact Hmc.
    - intros _. exact Hbud'.
    - (* [comment removed for export] *)
      cbn [Z.eqb]. rewrite pc_lit_add4 by lia. fold nZ n.
        set (mdl' := fixedin_ok_model 3 (Z_to_bv 64 50) addr n mdl).
      assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) eb) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
      assert (EQV : mrestrict (hcut H lo nZ) (zfill addr n M) = zfill addr n (mrestrict H M)).
      { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
        destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + nZ)); cbn [andb negb];
          rewrite ?andb_false_r, ?andb_true_r; try reflexivity; destruct (H x); reflexivity. }
      pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
      assert (LZout : forall p, page_in_ranges p (m_vm_lazy mdl') = true ->
                      page_in_ranges p (m_vm_lazy mdl) = true /\ (bv_unsigned p + 4096 <= lo \/ lo + nZ <= bv_unsigned p)).
      { intros p Hp. unfold mdl' in Hp. rewrite (fixedin_eager_lazy (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32) in Hp.
        split; [eapply pages_sub_maps_subtract; [exact W3 | | exact Hp]; rewrite Ulo, Hun; lia|].
        apply page_in_ranges_true in Hp as (q & Hq & Q1 & Q2).
        destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & R3). rewrite Ulo, Hun in R3. unfold page_size in Q2. lia. }
      apply (HK (regupd R 10%bv addr) mdl'). fold addr n. constructor.
      + apply (AsanNodesMmB.regs_ok_regupd_same _ sr R _ addr HR); [| intros X; apply (f_equal bv_unsigned) in X; discriminate X].
        rewrite (HR 10%bv). exact Haddr.
      + rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
        constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
        rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr n (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx. apply hcut_true in Hhx as [Hhd Hout].
        rewrite zfill_out by (rewrite Ulo, Hun; exact Hout). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhd).
      + unfold mdl'. rewrite (fixedin_eager_lazy (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32), Ulo, Hun, HLZ. reflexivity.
      + unfold mdl'. apply (MInv_fixedin_eager A (Z_to_bv 64 50) addr n mdl (mf_wf _ _ _ _ _ _ _ _ _ F)).
        * rewrite Ulo. unfold page_size. exact Hal.
        * rewrite Hun. unfold page_size. tauto.
        * rewrite Hun. lia.
        * apply mmap_noreserve_b_32.
        * constructor; assumption.
        * rewrite Ulo, Hun, LIM. cbn [lcommit l_eager] in Hbud. lia.
      + (* [comment removed for export] *)
        pose proof (fixedin_eager_unfold (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32) as UF.
        pose proof (model_ivs_wf_fixedin_eager (Z_to_bv 64 50) addr n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) ltac:(rewrite Hun; lia) mmap_noreserve_b_32) as WF'.
        pose proof (eager_used_fixedin_eager_le (Z_to_bv 64 50) addr n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) ltac:(rewrite Hun; lia) mmap_noreserve_b_32) as EGL.
        rewrite Ulo, Hun in EGL. unfold mdl'.
        constructor; cbn [lcommit l_maps l_brk l_eager].
        * rewrite (fixedin_eager_halted _ _ _ _ mmap_noreserve_b_32). exact Hh.
        * rewrite (fixedin_eager_reserved _ _ _ _ mmap_noreserve_b_32). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_init_sp _ _ _ _ mmap_noreserve_b_32). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_limit _ _ _ _ mmap_noreserve_b_32). exact LIM.
        * etransitivity; [| exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_brk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_mb _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * rewrite (fixedin_eager_maps _ _ _ _ mmap_noreserve_b_32). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (fixedin_eager_fs _ _ _ _ mmap_noreserve_b_32). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_fds _ _ _ _ mmap_noreserve_b_32). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_eager_tid _ _ _ _ mmap_noreserve_b_32). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fixedin_eager_noaccess _ _ _ _ mmap_noreserve_b_32).
          apply na_clear_l_sub; [exact (proj1 (proj2 (mf_wf _ _ _ _ _ _ _ _ _ F))) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + (* [comment removed for export] *) exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
        * exact HAW.
        * intros x Hpx Hhx. destruct (LZout _ Hpx) as [Hp Hout]. apply (HCOV x Hp).
          unfold hcut in Hhx. apply andb_false_iff in Hhx as [Hhx|Hhx]; [exact Hhx|]. exfalso.
          apply negb_false_iff in Hhx. apply andb_prop in Hhx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size in Hout.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small in Hout by lia.
          assert (lo mod 4096 = 0 /\ nZ mod 4096 = 0) as [L1 L2] by (split; [exact Hal | tauto]).
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)). nia.
        * intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
        * exact Hhin.
        * intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
        * intros x Hx. apply hcut_true in Hx as [Hx Hout]. unfold mdl'.
          rewrite (fixedin_eager_lazy (Z_to_bv 64 50) addr n mdl mmap_noreserve_b_32), Ulo, Hun.
          rewrite page_in_ranges_subtract_out; [exact (Hhl x Hx) | exact W3 | lia |].
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia.
          assert (lo mod 4096 = 0 /\ nZ mod 4096 = 0) as [L1 L2] by (split; [exact Hal | tauto]).
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)). nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems5.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    bv_unsigned (edenot E e) + eo = lo ->
    (forall x : word, lo <= bv_unsigned x < lo + n -> H x = true) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= lo -> lo + n <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H lo n) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit n); KWr (SA e eo) (ELit n)] ++ kn_keep MGrow kn kn e eo (ELit n)) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo lo n rlo rhi E HB Hlo Hn Hpos Hlo0 Htop He Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (addr := Z_to_bv 64 lo). set (nw := Z_to_bv 64 n).
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = n) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, lo <= bv_unsigned x < lo + n -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) (Hhid x Hx)). }
    assert (EQV : mrestrict (hcut H lo n) M = zfill addr nw (mrestrict H M)).
    { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
      destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + n)); cbn [andb negb];
        rewrite ?andb_false_r, ?andb_true_r; try (destruct (H x); reflexivity).
      apply ZERO. lia. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; exact He).
    constructor.
    - exact HR.
    - rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose2 : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = true) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit m); KWr (SA e eo) (ELit m)] ++ kn_keep MGrow kn kn e eo (ELit m)) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)) as Ue.
    set (addr := Z_to_bv 64 d). set (nw := Z_to_bv 64 m).
    assert (Ulo : bv_unsigned addr = d) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = m) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) (Hhid x Hx)). }
    assert (EQV : mrestrict (hcut H d m) M = zfill addr nw (mrestrict H M)).
    { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
      destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb negb];
        rewrite ?andb_false_r, ?andb_true_r; try (destruct (H x); reflexivity).
      apply ZERO. lia. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
    constructor.
    - exact HR.
    - rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.

(* [comment removed for export] *)
Lemma know_ok_sub_b : forall segs E M kn1 kn2,
  forallb (fun k => existsb (APC.kentry_eqb k) kn1) kn2 = true -> know_ok segs E M kn1 -> know_ok segs E M kn2.
Proof.
  intros segs E M kn1 kn2 Hb HK. unfold know_ok in *. apply Forall_forall. intros k Hk.
  pose proof (proj1 (forallb_forall _ _) Hb k Hk) as Hx. apply existsb_exists in Hx as (k' & Hk' & He).
  apply KNA.kentry_eqb_eq in He. subst k'. exact (proj1 (Forall_forall _ _) HK k Hk').
Qed.

Lemma kn_vars_lt_filter : forall b f kn, kn_vars_lt b kn = true -> kn_vars_lt b (List.filter f kn) = true.
Proof.
  induction kn as [|K kn IH]; cbn [kn_vars_lt List.filter]; intros Hk; [reflexivity|].
  apply andb_prop in Hk as [H1 H2]. destruct (f K); cbn [kn_vars_lt]; rewrite ?H1, (IH H2); reflexivity.
Qed.

Section Theorems6.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memset : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo : Z) (iW : nat) (wlen cv n ret : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    sr_get sr 11%bv = ELit cv -> 0 <= cv < 2 ^ 64 ->
    edenot E (sr_get sr 12%bv) = Z_to_bv 64 n -> 0 <= n ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e eo) (ELit wlen)) -> n <= wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n <= bv_unsigned sp - stack_max_size ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' memset_clob) (sr_after_call_c sr memset_clob v)
              (KFill (SA e eo) (ELit n) cv :: kn_keep MGrow kn kn e eo (ELit n)) L hc lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo iW wlen cv n ret K E v d HB Hsr Hkn HL Hev S10 S11 Hcv S12 Hn S1 Hret HiW Hnw Hwlen Hd0 Hdn HK.
    subst E. unfold v in *. clear v.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d).
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; unfold stack_max_size in *; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 cv) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 n) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw (Z.to_nat n) = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e eo wlen eo (Z.to_nat n) HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    destruct (musl_memset_summary V dw (Z_to_bv 64 cv) (Z_to_bv 64 ret) n ROM R Hn ltac:(rewrite Ud; unfold stack_max_size in *; lia)
                Hst Hret G10 G11 G12 G1) as (R' & MS & P10 & AG & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memset) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := repeat (cbyte (Z_to_bv 64 cv)) (Z.to_nat n)) in *.
    set (V' := wbytes V dw bs) in *.
    assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; [unfold stack_max_size in *; lia | lia]. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      rewrite EB_app. apply (regs_after_clob memset_clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
      + intros r Hr. apply AG. exact Hr.
      + cbn. intros [X|[X|[X|[X|[X|[X|[]]]]]]]; apply (f_equal bv_unsigned) in X; discriminate X.
      + repeat constructor; cbn; intros X; repeat (destruct X as [X|X]; [apply (f_equal bv_unsigned) in X; discriminate X|]); exact X.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. rewrite Hev. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. exact Hkn. }
      constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        fold (EB sp draw inp a tid c pl js). fold d. rewrite !u_small by lia.
        split; [unfold stack_max_size in *; lia|].
        intros i Hi. unfold V'.
        replace (Z_to_bv 64 (d + i)) with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat i))) by (f_equal; rewrite Ud; lia).
        rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
        unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity.
      + apply (kn_keep_sound SEGS _ V V' MGrow); [exact HKN | exact HKN |].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold d. rewrite u_small by lia.
        rewrite <- Ud. replace n with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes.
        rewrite LEN, Ud. unfold stack_max_size in *. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold stack_max_size in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memset_c : forall (clob : list reg) H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo : Z) (iW : nat) (weo wlen cv n ret : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    incl memset_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    sr_get sr 11%bv = ELit cv -> 0 <= cv < 2 ^ 64 ->
    edenot E (sr_get sr 12%bv) = Z_to_bv 64 n -> 0 <= n ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e weo) (ELit wlen)) -> weo <= eo -> eo + n <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n <= bv_unsigned sp ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' clob) (sr_after_call_c sr clob v)
              (KFill (SA e eo) (ELit n) cv :: kn_keep MGrow kn kn e eo (ELit n)) L hc lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros clob H A a tid c pl js sr kn L hc lz R M mdl e eo iW weo wlen cv n ret K E v d HB Hincl Hc0 Hnd Hsr Hkn HL Hev S10 S11 Hcv S12 Hn S1 Hret HiW Hweo Hnw Hwlen Hd0 Hdn HK.
    subst E. unfold v in *. clear v.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d).
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; unfold stack_max_size in *; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 cv) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 n) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw (Z.to_nat n) = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e weo wlen eo (Z.to_nat n) HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    destruct (musl_memset_summary V dw (Z_to_bv 64 cv) (Z_to_bv 64 ret) n ROM R Hn ltac:(rewrite Ud; unfold stack_max_size in *; lia)
                Hst Hret G10 G11 G12 G1) as (R' & MS & P10 & AG & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memset) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := repeat (cbyte (Z_to_bv 64 cv)) (Z.to_nat n)) in *.
    set (V' := wbytes V dw bs) in *.
    assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; [unfold stack_max_size in *; lia | lia]. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      rewrite EB_app. apply (regs_after_clob clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
      + intros r Hr. apply AG. intros Hin. apply Hr. apply Hincl. exact Hin.
      + exact Hc0.
      + exact Hnd.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. rewrite Hev. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. exact Hkn. }
      constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        fold (EB sp draw inp a tid c pl js). fold d. rewrite !u_small by lia.
        split; [unfold stack_max_size in *; lia|].
        intros i Hi. unfold V'.
        replace (Z_to_bv 64 (d + i)) with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat i))) by (f_equal; rewrite Ud; lia).
        rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
        unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity.
      + apply (kn_keep_sound SEGS _ V V' MGrow); [exact HKN | exact HKN |].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold d. rewrite u_small by lia.
        rewrite <- Ud. replace n with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes.
        rewrite LEN, Ud. unfold stack_max_size in *. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold stack_max_size in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_mem_is_zero : forall (clob : list reg) H A a tid c pl js sr kn L hc lz R M mdl
      (e : expr) (eo : Z) (es : expr) (so : Z) (iZ iW : nat) (zeo zlen weo wlen n ret : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    let s := bv_unsigned (edenot E es) + so in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    incl memisz_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v es = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    edenot E (sr_get sr 11%bv) = Z_to_bv 64 n -> 0 <= n <= 2 ^ 40 ->
    split_lit (sr_get sr 2%bv) = (es, so) ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iZ = Some (KZero (SA e zeo) (ELit zlen)) -> zeo <= eo -> eo + n <= zeo + zlen -> zlen < 2 ^ 64 ->
    nth_error kn iW = Some (KWr (SA es weo) (ELit wlen)) -> weo <= so - 8 -> so <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n + 8 <= 2 ^ 64 -> 16 <= s -> s <= bv_unsigned sp -> (d + n <= s - 8 \/ s <= d) ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' clob) (sr_upd (sr_after_call_c sr clob v) (ridx 10%bv) (ELit 1))
              (kn_keep MGrow kn kn es (so - 8) (ELit 8)) L hc lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_mem_is_zero) M ROM) mdl) K.
  Proof.
    intros clob H A a tid c pl js sr kn L hc lz R M mdl e eo es so iZ iW zeo zlen weo wlen n ret K E v d s HB Hincl Hc0 Hnd Hsr Hkn HL Hevs
           S10 S11 Hn S2 S1 Hret HiZ Hzeo Hzn Hzlen HiW Hweo Hsow Hwlen Hd0 Hdnw Hs16 Hssp Hapart HK.
    subst E. unfold v in *. clear v.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d). set (sw := Z_to_bv 64 s).
    assert (Us : bv_unsigned sw = s) by (unfold sw; apply u_small; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G2 : getr R 2%bv = sw).
    { rewrite (HR 2%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S2). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 n) by (rewrite (HR 11%bv); exact S11).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    (* [comment removed for export] *)
    pose proof (know_nth _ _ V kn iZ _ HKN HiZ) as (Zfl & Zrd). unfold flat, estart, elenZ in Zfl, Zrd. cbn [a_base a_off edenot] in Zfl, Zrd.
    fold (EB sp draw inp a tid c pl js) in Zfl, Zrd. rewrite !u_small in Zfl, Zrd by lia.
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; lia).
    assert (RD : forall x : word, bv_unsigned dw <= bv_unsigned x < bv_unsigned dw + n -> rdn SEGS V x 1 = Some [Z_to_bv 8 0]).
    { intros x Hx. rewrite Ud in Hx. cbn [rdn].
      replace x with (Z_to_bv 64 (bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + zeo + (bv_unsigned x - (bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + zeo))))
        by (apply bv_eq; rewrite u_small; [lia | pose proof (u64_range x); lia]).
      rewrite (Zrd (bv_unsigned x - (bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + zeo))) by (unfold d in *; lia). reflexivity. }
    assert (Hst : store_ok SEGS V (Z_to_bv 64 (bv_unsigned sw - 8)) 8 = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW es weo wlen (so - 8) 8%nat HKN HiW ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as ST.
      rewrite adenot_SA in ST. rewrite Us. replace (bv_unsigned (edenot (EB sp draw inp a tid c pl js) es) + (so - 8)) with (s - 8) in ST by (unfold s; lia). exact ST. }
    destruct (a3_mem_is_zero V dw sw n ROM R (Z_to_bv 64 ret) Hn ltac:(rewrite Ud; lia) ltac:(rewrite Us; lia) Hst
                ltac:(rewrite Ud, Us; lia) RD Hret G1 G2 G10 G11) as (R' & MS & AG & P10 & P2 & P1).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_mem_is_zero) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := word_to_le_bytes 8 (Z_to_bv 64 ret)) in *.
    rewrite Us in *. set (aw := Z_to_bv 64 (s - 8)) in *.
    set (V' := wbytes V aw bs) in *.
    assert (LEN : length bs = 8%nat) by (unfold bs; apply length_N_to_le_bytes).
    assert (Ua : bv_unsigned aw = s - 8) by (unfold aw; apply u_small; lia).
    assert (V'out : forall x : word, bv_unsigned x < s - 8 \/ s <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ua; [lia | cbn; lia]. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      rewrite EB_app. eapply (regs_ok_upd1 _ _ R' R' 10%bv (ELit 1)).
      + apply (regs_after_clob clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
        * intros r Hr. apply AG. intros Hin. apply Hr. apply Hincl. exact Hin.
        * exact Hc0.
        * exact Hnd.
      + intros X. apply (f_equal bv_unsigned) in X. discriminate X.
      + exact P10.
      + intros r _. reflexivity.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { unfold kn_keep. apply kn_vars_lt_filter. exact Hkn. }
      apply (kn_keep_sound SEGS _ V V' MGrow); [exact HKN | exact HKN |].
      unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite u_small by lia.
      replace (bv_unsigned (edenot (EB sp draw inp a tid c pl js) es) + (so - 8)) with (bv_unsigned aw) by (rewrite Ua; unfold s; lia).
      replace 8 with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes. rewrite LEN, Ua. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by lia. unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems6.
End TwB.
End BootNodes2.

(* [comment removed for export] *)
Module BootNodes3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import MuslMemset A3Sums.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootNodes. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes3_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.


(* [comment removed for export] *)
Definition lpop (L : ledger) : ledger := Ledger (List.tl (l_maps L)) (l_brk L) (l_eager L).

Section Theorems9.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_munmap_hd : forall H A a tid c pl js sr kn L hc lz R M mdl (v : nat) (nZ pc : Z) rest w (K : TSet),
    let E := EB' a tid c pl js in
    let p := ev E v in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 215 -> sr_get sr 10%bv = EVar v -> sr_get sr 11%bv = ELit nZ ->
    l_maps L = (EVar v, nZ) :: rest -> nZ mod 4096 = 0 ->
    (forall x : word, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ -> H x = false) ->
    hf_inmaps E (lpop L) hc ->
    In (ELit 0x7fff7000, 2 ^ 28) rest -> In (ELit 0x8fff7000, 2 ^ 41) rest -> In (ELit 0x2008fff7000, 0xdfff0001000) rest ->
    (forall R' mdl',
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (ELit 0)) (kn_keep MUnmap kn kn (EVar v) 0 (ELit nZ)) (lpop L) hc
              (maps_subtract lz (bv_unsigned p) (bv_unsigned p + nZ)) R' (unfill p (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (unfill p (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl v nZ pc rest w K E p HB HF HE Hpc0 Hpc4 S17 S10 S11 HL HnZ Hvis Hhin' I1 I2 I3 HK.
    subst E. destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (Ep : edenot (EB sp draw inp a tid c pl js) (EVar v) = p) by reflexivity.
    (* [comment removed for export] *)
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. apply Forall_cons_iff in MO as [MOK MOR].
    unfold map_ok in MOK. cbn [fst snd] in MOK. rewrite Ep in MOK. destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP0. pose proof AP0 as AP. rewrite HL in AP. cbn [dl List.map fst snd ivs_apart] in AP.
    rewrite Ep in AP. destruct AP as [APh APr]. fold (dl (EB sp draw inp a tid c pl js) rest) in APh, APr.
    set (n := Z_to_bv 64 nZ) in *.
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    rewrite Hun in APh.
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    assert (Hpr : page_round_up_Z nZ = nZ).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod nZ 4096 ltac:(lia)). rewrite Z.mul_comm.
      replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
      replace (nZ + 4096 - 1) with (4095 + (nZ / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    assert (HMAPS : vm_maps (m_vmmaps mdl) = (p, n) :: dl (EB sp draw inp a tid c pl js) rest).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), HL. reflexivity. }
    (* [comment removed for export] *)
    assert (HRM : map_remove (vm_maps (m_vmmaps mdl)) p = dl (EB sp draw inp a tid c pl js) rest).
    { rewrite HMAPS. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
      apply forallb_filter_id. apply forallb_forall. intros q Hq. apply negb_true_iff.
      pose proof (proj1 (Forall_forall _ _) APh q Hq) as Aq. cbv beta in Aq.
      pose proof (proj1 (Forall_forall _ _) MOR) as MR.
      unfold dl in Hq. apply in_map_iff in Hq as ([e en] & <- & Hin). cbn [fst snd] in Aq |- *.
      pose proof (MR _ Hin) as (_ & _ & En & Etop & _). cbn [fst snd] in En, Etop.
      pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)). rewrite (u_small en) in Aq by (unfold stack_max_size in *; lia).
      apply Bool.not_true_iff_false. intros X. apply bv_eqb_eq in X. rewrite X in Aq. lia. }
    eapply (srz_munmap_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w p nZ K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17)).
    - rewrite (HR 10%bv), S10. reflexivity.
    - unfold page_size. exact Mal.
    - exact (G _ _ S11).
    - exact Mn.
    - rewrite Hpr. unfold TASK_SIZE, stack_max_size in *. lia.
    - rewrite Hpr, HMAPS. cbn [map_has existsb fst snd]. rewrite !bv_eqb_refl. reflexivity.
    - rewrite Hpr, pc_lit_add4 by lia. fold n.
      set (mdl' := munmap_model p n mdl).
      assert (APART' : forall q, In q (map_remove (vm_maps (m_vmmaps mdl)) p) -> B q + S q <= bv_unsigned p \/ bv_unsigned p + bv_unsigned n <= B q).
      { intros q Hq. rewrite HRM in Hq. pose proof (proj1 (Forall_forall _ _) APh q Hq) as Aq. cbv beta in Aq. unfold B, S. rewrite Hun. lia. }
      apply (HK (regupd R 10%bv (Z_to_bv 64 0)) mdl'). constructor.
      + apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | reflexivity].
      + (* [comment removed for export] *)
        replace (mrestrict H (unfill p n M)) with (unfill p n (mrestrict H M))
          by (extensionality x; unfold mrestrict, unfill, zmem; destruct (H x), (_ && _)%bool; reflexivity).
        apply (kn_keep_sound SEGS _ (mrestrict H M) (unfill p n (mrestrict H M)) MUnmap); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold p. rewrite Z.add_0_r, u_small by lia.
        rewrite <- Hun. apply mem_change_unfill.
      + intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        rewrite unfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|]. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p + nZ)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + unfold mdl'. rewrite (munmap_lazy p n mdl), HLZ, Hun. reflexivity.
      + unfold mdl'. apply (MInv_munmap A p n mdl WF); try (rewrite ?Hun; unfold page_size; first [exact Mal | exact HnZ | lia]).
        * exact APART'.
        * exact HM.
      + (* [comment removed for export] *)
        pose proof (model_ivs_wf_munmap p n mdl WF ltac:(rewrite Hun; lia)) as WF'.
        pose proof (eager_used_munmap_le p n mdl WF ltac:(rewrite Hun; lia) APART') as EGL.
        unfold mdl'. constructor; cbn [lpop l_maps l_brk l_eager List.tl].
        * rewrite (munmap_halted p n mdl). exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_reserved p n mdl). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_init_sp p n mdl). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_limit p n mdl). exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_start_brk p n mdl). exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_brk p n mdl). exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_mmap_base p n mdl). exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_maps p n mdl), HRM, HL. reflexivity.
        * rewrite HL. exact APr.
        * pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * rewrite (munmap_fs p n mdl). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_fds p n mdl). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_tid p n mdl). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (munmap_noaccess p n mdl). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + (* [comment removed for export] *) unfold maps_ok, lpop. cbn [l_maps]. rewrite HL. cbn [List.tl]. exact MOR.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_munmap A p n mdl WF ltac:(rewrite Hun; lia)). exact HCOV.
        * intros x Hx. destruct (HIN x Hx) as (q & Hq & Hqx). rewrite HL in Hq. destruct Hq as [<-|Hq].
          -- exfalso. cbn [fst snd] in Hqx. rewrite Ep in Hqx. rewrite (Hvis x Hqx) in Hx. discriminate.
          -- exists q. split; [| exact Hqx]. unfold lpop. cbn [l_maps]. rewrite HL. exact Hq.
        * exact Hhin'.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite (munmap_lazy p n mdl), Hun.
          assert (Hout : ~ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ)) by (intros X; rewrite (Hvis x X) in Hx; discriminate).
          rewrite page_in_ranges_subtract_out; [exact (Hhl x Hx) | exact W3 | lia |].
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)). nia.
        * (* [comment removed for export] *)
          intros x Hx. unfold H2 in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold SHB_LO, SHB_HI in X1, X2.
          unfold lpop. cbn [l_maps]. rewrite HL. cbn [List.tl].
          destruct (Z.lt_ge_cases (bv_unsigned x) 0x8fff7000) as [|Y1]; [exists (ELit 0x7fff7000, 2 ^ 28); split; [exact I1 | cbn; rewrite u_small by lia; lia]|].
          destruct (Z.lt_ge_cases (bv_unsigned x) 0x2008fff7000) as [|Y2]; [exists (ELit 0x8fff7000, 2 ^ 41); split; [exact I2 | cbn; rewrite u_small by lia; lia]|].
          exists (ELit 0x2008fff7000, 0xdfff0001000). split; [exact I3 | cbn; rewrite u_small by lia; lia].
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems9.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.MuslMemset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Sums.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes3_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.


(* [comment removed for export] *)
Definition lpop (L : ledger) : ledger := Ledger (List.tl (l_maps L)) (l_brk L) (l_eager L).

Section Theorems9.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_munmap_hd : forall H A a tid c pl js sr kn L hc lz R M mdl (v : nat) (nZ pc : Z) rest w (K : TSet),
    let E := EB' a tid c pl js in
    let p := ev E v in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 215 -> sr_get sr 10%bv = EVar v -> sr_get sr 11%bv = ELit nZ ->
    l_maps L = (EVar v, nZ) :: rest -> nZ mod 4096 = 0 ->
    (forall x : word, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ -> H x = false) ->
    hf_inmaps E (lpop L) hc ->
    In (ELit 0x7fff7000, 2 ^ 28) rest -> In (ELit 0x8fff7000, 2 ^ 41) rest -> In (ELit 0x2008fff7000, 0xdfff0001000) rest ->
    (forall R' mdl',
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (ELit 0)) (kn_keep MUnmap kn kn (EVar v) 0 (ELit nZ)) (lpop L) hc
              (maps_subtract lz (bv_unsigned p) (bv_unsigned p + nZ)) R' (unfill p (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (unfill p (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl v nZ pc rest w K E p HB HF HE Hpc0 Hpc4 S17 S10 S11 HL HnZ Hvis Hhin' I1 I2 I3 HK.
    subst E. destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (Ep : edenot (EB sp draw inp a tid c pl js) (EVar v) = p) by reflexivity.
    (* [comment removed for export] *)
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. apply Forall_cons_iff in MO as [MOK MOR].
    unfold map_ok in MOK. cbn [fst snd] in MOK. rewrite Ep in MOK. destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP0. pose proof AP0 as AP. rewrite HL in AP. cbn [dl List.map fst snd ivs_apart] in AP.
    rewrite Ep in AP. destruct AP as [APh APr]. fold (dl (EB sp draw inp a tid c pl js) rest) in APh, APr.
    set (n := Z_to_bv 64 nZ) in *.
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    rewrite Hun in APh.
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    assert (Hpr : page_round_up_Z nZ = nZ).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod nZ 4096 ltac:(lia)). rewrite Z.mul_comm.
      replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
      replace (nZ + 4096 - 1) with (4095 + (nZ / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    assert (HMAPS : vm_maps (m_vmmaps mdl) = (p, n) :: dl (EB sp draw inp a tid c pl js) rest).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), HL. reflexivity. }
    (* [comment removed for export] *)
    assert (HRM : map_remove (vm_maps (m_vmmaps mdl)) p = dl (EB sp draw inp a tid c pl js) rest).
    { rewrite HMAPS. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
      apply forallb_filter_id. apply forallb_forall. intros q Hq. apply negb_true_iff.
      pose proof (proj1 (Forall_forall _ _) APh q Hq) as Aq. cbv beta in Aq.
      pose proof (proj1 (Forall_forall _ _) MOR) as MR.
      unfold dl in Hq. apply in_map_iff in Hq as ([e en] & <- & Hin). cbn [fst snd] in Aq |- *.
      pose proof (MR _ Hin) as (_ & _ & En & Etop & _). cbn [fst snd] in En, Etop.
      pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)). rewrite (u_small en) in Aq by (unfold stack_max_size in *; lia).
      apply Bool.not_true_iff_false. intros X. apply bv_eqb_eq in X. rewrite X in Aq. lia. }
    eapply (srz_munmap_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w p nZ K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17)).
    - rewrite (HR 10%bv), S10. reflexivity.
    - unfold page_size. exact Mal.
    - exact (G _ _ S11).
    - exact Mn.
    - rewrite Hpr. unfold TASK_SIZE, stack_max_size in *. lia.
    - rewrite Hpr, HMAPS. cbn [map_has existsb fst snd]. rewrite !bv_eqb_refl. reflexivity.
    - rewrite Hpr, pc_lit_add4 by lia. fold n.
      set (mdl' := munmap_model p n mdl).
      assert (APART' : forall q, In q (map_remove (vm_maps (m_vmmaps mdl)) p) -> B q + S q <= bv_unsigned p \/ bv_unsigned p + bv_unsigned n <= B q).
      { intros q Hq. rewrite HRM in Hq. pose proof (proj1 (Forall_forall _ _) APh q Hq) as Aq. cbv beta in Aq. unfold B, S. rewrite Hun. lia. }
      apply (HK (regupd R 10%bv (Z_to_bv 64 0)) mdl'). constructor.
      + apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | reflexivity].
      + (* [comment removed for export] *)
        replace (mrestrict H (unfill p n M)) with (unfill p n (mrestrict H M))
          by (extensionality x; unfold mrestrict, unfill, zmem; destruct (H x), (_ && _)%bool; reflexivity).
        apply (kn_keep_sound SEGS _ (mrestrict H M) (unfill p n (mrestrict H M)) MUnmap); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold p. rewrite Z.add_0_r, u_small by lia.
        rewrite <- Hun. apply mem_change_unfill.
      + intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        rewrite unfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|]. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p + nZ)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + unfold mdl'. rewrite (munmap_lazy p n mdl), HLZ, Hun. reflexivity.
      + unfold mdl'. apply (MInv_munmap A p n mdl WF); try (rewrite ?Hun; unfold page_size; first [exact Mal | exact HnZ | lia]).
        * exact APART'.
        * exact HM.
      + (* [comment removed for export] *)
        pose proof (model_ivs_wf_munmap p n mdl WF ltac:(rewrite Hun; lia)) as WF'.
        pose proof (eager_used_munmap_le p n mdl WF ltac:(rewrite Hun; lia) APART') as EGL.
        unfold mdl'. constructor; cbn [lpop l_maps l_brk l_eager List.tl].
        * rewrite (munmap_halted p n mdl). exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_reserved p n mdl). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_init_sp p n mdl). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_limit p n mdl). exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_start_brk p n mdl). exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_brk p n mdl). exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_mmap_base p n mdl). exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_maps p n mdl), HRM, HL. reflexivity.
        * rewrite HL. exact APr.
        * pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * rewrite (munmap_fs p n mdl). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_fds p n mdl). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (munmap_tid p n mdl). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (munmap_noaccess p n mdl). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + (* [comment removed for export] *) unfold maps_ok, lpop. cbn [l_maps]. rewrite HL. cbn [List.tl]. exact MOR.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_munmap A p n mdl WF ltac:(rewrite Hun; lia)). exact HCOV.
        * intros x Hx. destruct (HIN x Hx) as (q & Hq & Hqx). rewrite HL in Hq. destruct Hq as [<-|Hq].
          -- exfalso. cbn [fst snd] in Hqx. rewrite Ep in Hqx. rewrite (Hvis x Hqx) in Hx. discriminate.
          -- exists q. split; [| exact Hqx]. unfold lpop. cbn [l_maps]. rewrite HL. exact Hq.
        * exact Hhin'.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite (munmap_lazy p n mdl), Hun.
          assert (Hout : ~ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ)) by (intros X; rewrite (Hvis x X) in Hx; discriminate).
          rewrite page_in_ranges_subtract_out; [exact (Hhl x Hx) | exact W3 | lia |].
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)). nia.
        * (* [comment removed for export] *)
          intros x Hx. unfold H2 in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold SHB_LO, SHB_HI in X1, X2.
          unfold lpop. cbn [l_maps]. rewrite HL. cbn [List.tl].
          destruct (Z.lt_ge_cases (bv_unsigned x) 0x8fff7000) as [|Y1]; [exists (ELit 0x7fff7000, 2 ^ 28); split; [exact I1 | cbn; rewrite u_small by lia; lia]|].
          destruct (Z.lt_ge_cases (bv_unsigned x) 0x2008fff7000) as [|Y2]; [exists (ELit 0x8fff7000, 2 ^ 41); split; [exact I2 | cbn; rewrite u_small by lia; lia]|].
          exists (ELit 0x2008fff7000, 0xdfff0001000). split; [exact I3 | cbn; rewrite u_small by lia; lia].
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems9.
End TwB.
End BootNodes3.

(* [comment removed for export] *)
Module BootNodes4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import MuslMemset A3Sums.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootNodes. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes4_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_change_grow_mono : forall M M' lo n lo' n',
  mem_change MGrow M M' lo n -> lo' <= lo -> lo + n <= lo' + n' -> mem_change MGrow M M' lo' n'.
Proof. intros M M' lo n lo' n' [H1 H2] Ha Hb. split; [| exact H2]. intros x Hx. apply H1. lia. Qed.

Lemma kn_vars_lt_skipn : forall b j kn, kn_vars_lt b kn = true -> kn_vars_lt b (skipn j kn) = true.
Proof.
  intros b j; induction j as [|j IH]; intros kn Hk; [exact Hk|]. destruct kn as [|K kn]; [reflexivity|].
  cbn [skipn]. apply IH. cbn [kn_vars_lt] in Hk. apply andb_prop in Hk as [_ Hk]. exact Hk.
Qed.
Lemma know_ok_skipn : forall segs E M j kn, know_ok segs E M kn -> know_ok segs E M (skipn j kn).
Proof.
  intros segs E M j; induction j as [|j IH]; intros kn HK; [exact HK|]. destruct kn as [|K kn]; [constructor|].
  cbn [skipn]. apply IH. exact (Forall_inv_tail HK).
Qed.

Section Theorems10.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="Type"] Theorem bs_fresh2 : forall H A a tid c pl js sr kn L hc lz R M mdl (ws : list word) (sr' : list expr) (kf : list kentry),
    let v := length (VB' a tid c pl js) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    (regs_ok (EB' a tid c pl (js ++ ws)) sr R -> regs_ok (EB' a tid c pl (js ++ ws)) sr' R) ->
    know_ok SEGS (EB' a tid c pl (js ++ ws)) (mrestrict H M) kf ->
    bootS' H A a tid c pl (js ++ ws) sr' (kf ++ kn) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl ws sr' kf v HB Hsr Hkn HL HSR HKF.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    constructor; try assumption.
    - apply HSR. rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
    - apply (proj2 (know_ok_app SEGS _ _ _ _)). split; [exact HKF|]. rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - apply mfacts_env; assumption.
    - apply maps_ok_env; assumption.
    - apply regime_ok_env; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose3 : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = true \/ mrestrict H M x = Some (Z_to_bv 8 0)) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit m); KWr (SA e eo) (ELit m)] ++ kn_keep MGrow kn kn e eo (ELit m)) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)) as Ue.
    set (addr := Z_to_bv 64 d). set (nw := Z_to_bv 64 m).
    assert (Ulo : bv_unsigned addr = d) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = m) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. destruct (Hhid x Hx) as [Hh|Hv].
      - unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) Hh).
      - unfold mrestrict in Hv. destruct (H x); [discriminate | exact Hv]. }
    assert (EQV : mrestrict (hcut H d m) M = zfill addr nw (mrestrict H M)).
    { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
      destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb negb];
        rewrite ?andb_false_r, ?andb_true_r; try (destruct (H x); reflexivity).
      apply ZERO. lia. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
    constructor.
    - exact HR.
    - rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memset_cc : forall (clob : list reg) (j : nat) H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo : Z) (iW : nat) (weo wlen cv n ret : Z) (ce : expr) (ceo cn : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    expr_vars_lt v ce = true -> 0 <= cd -> cd <= d -> d + n <= cd + cn -> cn < 2 ^ 64 ->
    incl memset_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    sr_get sr 11%bv = ELit cv -> 0 <= cv < 2 ^ 64 ->
    edenot E (sr_get sr 12%bv) = Z_to_bv 64 n -> 0 <= n ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e weo) (ELit wlen)) -> weo <= eo -> eo + n <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n <= bv_unsigned sp ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' clob) (sr_after_call_c sr clob v)
              (KFill (SA e eo) (ELit n) cv :: kn_keep MGrow (skipn j kn) (skipn j kn) ce ceo (ELit cn)) L hc lz R' M' mdl' ->
       (forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> M' x = M x) ->
       (forall x : word, d <= bv_unsigned x < d + n -> M' x = Some (Z_to_bv 8 cv)) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros clob j H A a tid c pl js sr kn L hc lz R M mdl e eo iW weo wlen cv n ret ce ceo cn K E v d cd HB Hce Hcd0 Hcd1 Hcd2 Hcd3 Hincl Hc0 Hnd Hsr Hkn HL Hev S10 S11 Hcv S12 Hn S1 Hret HiW Hweo Hnw Hwlen Hd0 Hdn HK.
    subst E. unfold v in *. clear v. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d).
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; unfold stack_max_size in *; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 cv) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 n) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw (Z.to_nat n) = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e weo wlen eo (Z.to_nat n) HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    destruct (musl_memset_summary V dw (Z_to_bv 64 cv) (Z_to_bv 64 ret) n ROM R Hn ltac:(rewrite Ud; unfold stack_max_size in *; lia)
                Hst Hret G10 G11 G12 G1) as (R' & MS & P10 & AG & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memset) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := repeat (cbyte (Z_to_bv 64 cv)) (Z.to_nat n)) in *.
    set (V' := wbytes V dw bs) in *.
    assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; [unfold stack_max_size in *; lia | lia]. }
    assert (VIS : forall x : word, d <= bv_unsigned x < d + n -> H x = false).
    { intros x Hx. pose proof (store_ok_all SEGS V (Z.to_nat n) dw ltac:(rewrite Ud, Z2Nat.id by lia; unfold stack_max_size in *; lia) Hst x ltac:(rewrite Ud, Z2Nat.id by lia; lia)) as W.
      unfold V, wview, mrestrict in W. destruct (H x) eqn:EH; [| reflexivity]. exfalso.
      rewrite (HH x EH) in W. exact (W eq_refl). }
    apply HK; [constructor | |].
    13:{ intros x Hx. destruct (H x) eqn:EH; [rewrite (munrestrict_hidden _ _ _ _ EH); reflexivity|].
         rewrite (munrestrict_visible _ _ _ _ EH), V'out by exact Hx. unfold V. rewrite (mrestrict_visible' _ _ _ EH). reflexivity. }
    13:{ intros x Hx. rewrite (munrestrict_visible _ _ _ _ (VIS x Hx)). unfold V'.
         replace x with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat (bv_unsigned x - d)))) by (apply bv_eq; rewrite u_small; [lia | pose proof (u64_range x); lia]).
         rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
         unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity. }
    - (* [comment removed for export] *)
      rewrite EB_app. apply (regs_after_clob clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
      + intros r Hr. apply AG. intros Hin. apply Hr. apply Hincl. exact Hin.
      + exact Hc0.
      + exact Hnd.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. rewrite Hev. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. apply kn_vars_lt_skipn. exact Hkn. }
      constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        fold (EB sp draw inp a tid c pl js). fold d. rewrite !u_small by lia.
        split; [unfold stack_max_size in *; lia|].
        intros i Hi. unfold V'.
        replace (Z_to_bv 64 (d + i)) with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat i))) by (f_equal; rewrite Ud; lia).
        rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
        unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity.
      + apply (kn_keep_sound SEGS _ V V' MGrow); [apply know_ok_skipn; exact HKN | apply know_ok_skipn; exact HKN |].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite u_small by lia.
        apply (mem_change_grow_mono V V' d n); [| lia | lia].
        rewrite <- Ud. replace n with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes.
        rewrite LEN, Ud. unfold stack_max_size in *. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold stack_max_size in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.


  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose_wr : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = false -> M x <> None) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           (KWr (SA e eo) (ELit m) :: kn_keep MGrow kn kn e eo (ELit m)) L hc lz R M mdl
    /\ (forall x : word, d <= bv_unsigned x < d + m -> H x = true -> M x = Some (Z_to_bv 8 0)).
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)) as Ue.
    set (addr := Z_to_bv 64 d). set (nw := Z_to_bv 64 m).
    assert (Ulo : bv_unsigned addr = d) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = m) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> H x = true -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx Hh. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) Hh). }
    set (V' := mrestrict (hcut H d m) M).
    assert (CHG : mem_change MGrow (mrestrict H M) V' d m).
    { split.
      - intros x Hx. unfold V', mrestrict, hcut. destruct (H x); cbn [andb]; [| reflexivity].
        rewrite (proj2 (andb_false_iff _ _)); [reflexivity|].
        destruct Hx as [Hx|Hx]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
      - intros x Hx. unfold V', mrestrict, hcut in *. destruct (H x); cbn [andb negb] in *; [exfalso; exact (Hx eq_refl)|]. exact Hx. }
    assert (DEF : forall x : word, d <= bv_unsigned x < d + m -> V' x <> None).
    { intros x Hx. unfold V', mrestrict. rewrite (hcut_false_in H d m x Hx). destruct (H x) eqn:EH; [rewrite (ZERO x Hx EH); discriminate | exact (Hhid x Hx EH)]. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
    split; [| exact ZERO]. constructor.
    - exact HR.
    - fold V'. constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite Hea, Ulo, !u_small by lia.
        split; [unfold stack_max_size in *; lia|]. intros dd mm Hdd Hmm. apply store_ok_of_all; [rewrite u_small by (unfold stack_max_size in *; lia); unfold stack_max_size in *; lia|].
        intros x Hx. rewrite u_small in Hx by (unfold stack_max_size in *; lia). unfold wview.
        destruct (V' x) eqn:EV; [discriminate|]. exfalso. exact (DEF x ltac:(lia) EV).
      + apply (kn_keep_sound SEGS _ (mrestrict H M) V' MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, Ulo, u_small by lia. exact CHG.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems10.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems11.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_fixedin_lazy : forall H A a tid c pl js sr kn L hc lz R M mdl (lo len pc : Z) (em : expr) (nm : Z) w (K : TSet),
    let E := EB' a tid c pl js in
    let nZ := page_round_up_Z len in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> edenot E (sr_get sr 10%bv) = Z_to_bv 64 lo -> edenot E (sr_get sr 11%bv) = Z_to_bv 64 len ->
    sr_get sr 12%bv = ELit 3 -> sr_get sr 13%bv = ELit 16434 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> 0 <= lo -> lo mod 4096 = 0 ->
    In (em, nm) (l_maps L) -> sivs_sizes_ok (l_maps L) = true ->
    bv_unsigned (edenot E em) <= lo -> lo + nZ <= bv_unsigned (edenot E em) + nm ->
    map_contains lz (Z_to_bv 64 lo) (Z_to_bv 64 nZ) = true ->
    (forall x : word, lo <= bv_unsigned x < lo + nZ -> H x = true \/ mrestrict H M x = Some (Z_to_bv 8 0)) ->
    (forall r, In r hc -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= lo \/ lo + nZ <= fst (fst r)) ->
    (forall R' mdl',
       bootS' H A a tid c pl js sr kn L hc ((Z_to_bv 64 lo, Z_to_bv 64 nZ) :: maps_subtract lz lo (lo + nZ)) R'
              (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl lo len pc em nm w K E nZ HB HF HE Hpc0 Hpc4
           S17 S10 S11 S12 S13 S14 S15 Hlen Hlo0 Hal Hin Hs Hlo1 Hhi1 Hmcl Hhz Hhc HK. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. split; [lia|]. split; [lia|].
      unfold page_round_up_Z, page_size. apply Z_mod_mult. }
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    set (addr := Z_to_bv 64 lo) in *.
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    set (n := Z_to_bv 64 nZ) in *.
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hnm. cbn [snd] in Hnm.
    apply andb_prop in Hnm as [N0 N1]. apply Z.leb_le in N0. apply Z.ltb_lt in N1.
    assert (HinM : In (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (em, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) addr n = true).
    { unfold map_contains. apply existsb_exists. exists (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mmap_fixed_rw_budget_ok (Z_to_bv 64 16434) mdl addr n = true).
    { apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact WF | | | | |].
      - rewrite Ulo. unfold page_size. exact Hal.
      - rewrite Hun. unfold page_size. tauto.
      - rewrite Hun. lia.
      - rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      - rewrite vm_backing_used_split, LIM. unfold page_size. lia. }
    assert (Hrfr : region_free (vm_reserved (m_vmmaps mdl)) addr n = true).
    { rewrite (mf_res _ _ _ _ _ _ _ _ _ F). apply reserved_free_of_apart. rewrite Ulo, Hun. lia. }
    assert (G10 : getr R 10%bv = addr) by (rewrite (HR 10%bv); exact S10).
    eapply (srz_mmap_fixedin_top SEGS R (Z_to_bv 64 pc) M ROM mdl w 3 (Z_to_bv 64 16434) addr len K HF HE
              (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (or_intror eq_refl) mmap_flags_core_4032).
    - exact G10.
    - rewrite Ulo. unfold page_size. exact Hal.
    - rewrite Ulo. lia.
    - rewrite (HR 11%bv). exact S11.
    - exact Hlen.
    - rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F), Ulo. fold nZ. unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - rewrite (G _ _ S13). reflexivity.
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact Hrfr.
    - exact Hmc.
    - intros _. exact Hbud'.
    - (* [comment removed for export] *)
      cbn [Z.eqb]. rewrite pc_lit_add4 by lia. fold nZ n.
      set (mdl' := fixedin_ok_model 3 (Z_to_bv 64 16434) addr n mdl).
      assert (EQV : mrestrict H (zfill addr n M) = mrestrict H M).
      { extensionality x. unfold mrestrict. destruct (H x) eqn:EH; [reflexivity|]. unfold zfill, zmem. rewrite Ulo, Hun.
        destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + nZ)); cbn [andb]; try reflexivity.
        destruct (Hhz x ltac:(lia)) as [Hh|Hv]; [congruence|]. unfold mrestrict in Hv. rewrite EH in Hv. symmetry. exact Hv. }
      pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
      assert (F1 : bv_unsigned addr mod page_size = 0) by (rewrite Ulo; unfold page_size; exact Hal).
      assert (F2 : bv_unsigned n mod page_size = 0) by (rewrite Hun; unfold page_size; tauto).
      assert (F3 : 0 < bv_unsigned n) by (rewrite Hun; lia).
      assert (F4 : bv_unsigned addr + bv_unsigned n <= 2 ^ 64) by (rewrite Ulo, Hun; unfold stack_max_size in *; lia).
      pose proof mmap_noreserve_b_4032 as F5.
      set (fl := Z_to_bv 64 16434) in *.
      pose proof (fixedin_lazy_lazy fl addr n mdl F1 F2 F3 F4 F5) as LZ'. rewrite Ulo, Hun in LZ'.
      pose proof (model_ivs_wf_fixedin_lazy fl addr n mdl WF F3 F4 F5) as WF'.
      pose proof (eager_used_fixedin_lazy_le fl addr n mdl WF F1 F2 F3 F4 F5) as EGL.
      pose proof (fixedin_lazy_unfold fl addr n mdl F5) as UF.
      apply (HK (regupd R 10%bv addr) mdl'). constructor.
      + apply (AsanNodesMmB.regs_ok_regupd_same _ sr R _ addr HR); [exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate X].
      + rewrite EQV. exact HKN.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl]; [rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh]; [| rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)].
        destruct (Hhc r Hr) as [Hv|Hout]; [| exfalso; destruct r as [[rlo rhi] v]; cbn [fst snd] in Hout, Hx; lia].
        rewrite Hv. unfold zfill, zmem. rewrite Ulo, Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      + unfold mdl'. rewrite LZ', HLZ. reflexivity.
      + unfold mdl'. apply (MInv_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5). constructor; assumption.
      + (* [comment removed for export] *)
        unfold mdl'. constructor.
        * rewrite (fixedin_lazy_halted fl addr n mdl F5). exact Hh.
        * rewrite (fixedin_lazy_reserved fl addr n mdl F5). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_init_sp fl addr n mdl F5). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_limit fl addr n mdl F5). exact LIM.
        * etransitivity; [| exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_brk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_mb _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * rewrite (fixedin_lazy_maps fl addr n mdl F5). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (fixedin_lazy_fs fl addr n mdl F5). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_fds fl addr n mdl F5). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_tid fl addr n mdl F5). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fixedin_lazy_noaccess fl addr n mdl F5). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5); [| exact HCOV]. rewrite HLZ. exact Hmcl.
        * exact HIN.
        * exact Hhin.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite LZ'. rewrite page_in_ranges_cons. cbn [fst snd]. rewrite Ulo, Hun.
          pose proof (Hhl x Hx) as PL. pose proof (u64_range x) as Xr.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)) as XD. pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)) as XM.
          pose proof (Z.div_mod lo 4096 ltac:(lia)) as LD. assert (ND : nZ mod 4096 = 0) by tauto. pose proof (Z.div_mod nZ 4096 ltac:(lia)) as NDm.
          assert (PBx : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
          { unfold page_base, page_base_of, page_size. apply u_small. lia. }
          destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl].
          -- apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. left. rewrite PBx. unfold page_size. nia.
          -- destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh].
             ++ apply orb_true_intro. left. rewrite PBx. apply andb_true_intro. split; apply Z.leb_le; unfold page_size; nia.
             ++ apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. right. rewrite PBx. nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_fixedin_lazy2 : forall H A a tid c pl js sr kn L hc lz R M mdl (lo len pc : Z) (em : expr) (nm : Z) (ce : expr) (ceo cn : Z) w (K : TSet),
    let E := EB' a tid c pl js in
    let nZ := page_round_up_Z len in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    0 <= cd -> cd <= lo -> lo + nZ <= cd + cn -> cn < 2 ^ 64 ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> edenot E (sr_get sr 10%bv) = Z_to_bv 64 lo -> edenot E (sr_get sr 11%bv) = Z_to_bv 64 len ->
    sr_get sr 12%bv = ELit 3 -> sr_get sr 13%bv = ELit 16434 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> 0 <= lo -> lo mod 4096 = 0 ->
    In (em, nm) (l_maps L) -> sivs_sizes_ok (l_maps L) = true ->
    bv_unsigned (edenot E em) <= lo -> lo + nZ <= bv_unsigned (edenot E em) + nm ->
    map_contains lz (Z_to_bv 64 lo) (Z_to_bv 64 nZ) = true ->
    (forall r, In r hc -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= lo \/ lo + nZ <= fst (fst r)) ->
    (forall R' mdl',
       bootS' H A a tid c pl js sr (kn_keep MGrow kn kn ce ceo (ELit cn)) L hc ((Z_to_bv 64 lo, Z_to_bv 64 nZ) :: maps_subtract lz lo (lo + nZ)) R'
              (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl lo len pc em nm ce ceo cn w K E nZ cd HB Hcd0 Hcd1 Hcd2 Hcd3 HF HE Hpc0 Hpc4
           S17 S10 S11 S12 S13 S14 S15 Hlen Hlo0 Hal Hin Hs Hlo1 Hhi1 Hmcl Hhc HK. subst E. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. split; [lia|]. split; [lia|].
      unfold page_round_up_Z, page_size. apply Z_mod_mult. }
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    set (addr := Z_to_bv 64 lo) in *.
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    set (n := Z_to_bv 64 nZ) in *.
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hnm. cbn [snd] in Hnm.
    apply andb_prop in Hnm as [N0 N1]. apply Z.leb_le in N0. apply Z.ltb_lt in N1.
    assert (HinM : In (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (em, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) addr n = true).
    { unfold map_contains. apply existsb_exists. exists (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mmap_fixed_rw_budget_ok (Z_to_bv 64 16434) mdl addr n = true).
    { apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact WF | | | | |].
      - rewrite Ulo. unfold page_size. exact Hal.
      - rewrite Hun. unfold page_size. tauto.
      - rewrite Hun. lia.
      - rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      - rewrite vm_backing_used_split, LIM. unfold page_size. lia. }
    assert (Hrfr : region_free (vm_reserved (m_vmmaps mdl)) addr n = true).
    { rewrite (mf_res _ _ _ _ _ _ _ _ _ F). apply reserved_free_of_apart. rewrite Ulo, Hun. lia. }
    assert (G10 : getr R 10%bv = addr) by (rewrite (HR 10%bv); exact S10).
    eapply (srz_mmap_fixedin_top SEGS R (Z_to_bv 64 pc) M ROM mdl w 3 (Z_to_bv 64 16434) addr len K HF HE
              (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (or_intror eq_refl) mmap_flags_core_4032).
    - exact G10.
    - rewrite Ulo. unfold page_size. exact Hal.
    - rewrite Ulo. lia.
    - rewrite (HR 11%bv). exact S11.
    - exact Hlen.
    - rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F), Ulo. fold nZ. unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - rewrite (G _ _ S13). reflexivity.
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact Hrfr.
    - exact Hmc.
    - intros _. exact Hbud'.
    - (* [comment removed for export] *)
      cbn [Z.eqb]. rewrite pc_lit_add4 by lia. fold nZ n.
      set (mdl' := fixedin_ok_model 3 (Z_to_bv 64 16434) addr n mdl).
      assert (CHG : mem_change MGrow (mrestrict H M) (mrestrict H (zfill addr n M)) lo nZ).
      { split.
        - intros x Hx. unfold mrestrict. destruct (H x); [reflexivity|]. apply zfill_out. rewrite Ulo, Hun. lia.
        - intros x Hx. unfold mrestrict, zfill, zmem in *. destruct (H x); [exact Hx|]. destruct (_ && _)%bool; [discriminate | exact Hx]. }
      pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
      assert (F1 : bv_unsigned addr mod page_size = 0) by (rewrite Ulo; unfold page_size; exact Hal).
      assert (F2 : bv_unsigned n mod page_size = 0) by (rewrite Hun; unfold page_size; tauto).
      assert (F3 : 0 < bv_unsigned n) by (rewrite Hun; lia).
      assert (F4 : bv_unsigned addr + bv_unsigned n <= 2 ^ 64) by (rewrite Ulo, Hun; unfold stack_max_size in *; lia).
      pose proof mmap_noreserve_b_4032 as F5.
      set (fl := Z_to_bv 64 16434) in *.
      pose proof (fixedin_lazy_lazy fl addr n mdl F1 F2 F3 F4 F5) as LZ'. rewrite Ulo, Hun in LZ'.
      pose proof (model_ivs_wf_fixedin_lazy fl addr n mdl WF F3 F4 F5) as WF'.
      pose proof (eager_used_fixedin_lazy_le fl addr n mdl WF F1 F2 F3 F4 F5) as EGL.
      pose proof (fixedin_lazy_unfold fl addr n mdl F5) as UF.
      apply (HK (regupd R 10%bv addr) mdl'). constructor.
      + apply (AsanNodesMmB.regs_ok_regupd_same _ sr R _ addr HR); [exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate X].
      + apply (kn_keep_sound SEGS _ (mrestrict H M) (mrestrict H (zfill addr n M)) MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite u_small by lia.
        apply (mem_change_grow_mono _ _ lo nZ); [exact CHG | lia | lia].
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl]; [rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh]; [| rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)].
        destruct (Hhc r Hr) as [Hv|Hout]; [| exfalso; destruct r as [[rlo rhi] v]; cbn [fst snd] in Hout, Hx; lia].
        rewrite Hv. unfold zfill, zmem. rewrite Ulo, Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      + unfold mdl'. rewrite LZ', HLZ. reflexivity.
      + unfold mdl'. apply (MInv_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5). constructor; assumption.
      + (* [comment removed for export] *)
        unfold mdl'. constructor.
        * rewrite (fixedin_lazy_halted fl addr n mdl F5). exact Hh.
        * rewrite (fixedin_lazy_reserved fl addr n mdl F5). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_init_sp fl addr n mdl F5). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_limit fl addr n mdl F5). exact LIM.
        * etransitivity; [| exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_brk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_mb _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * rewrite (fixedin_lazy_maps fl addr n mdl F5). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (fixedin_lazy_fs fl addr n mdl F5). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_fds fl addr n mdl F5). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_tid fl addr n mdl F5). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fixedin_lazy_noaccess fl addr n mdl F5). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5); [| exact HCOV]. rewrite HLZ. exact Hmcl.
        * exact HIN.
        * exact Hhin.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite LZ'. rewrite page_in_ranges_cons. cbn [fst snd]. rewrite Ulo, Hun.
          pose proof (Hhl x Hx) as PL. pose proof (u64_range x) as Xr.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)) as XD. pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)) as XM.
          pose proof (Z.div_mod lo 4096 ltac:(lia)) as LD. assert (ND : nZ mod 4096 = 0) by tauto. pose proof (Z.div_mod nZ 4096 ltac:(lia)) as NDm.
          assert (PBx : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
          { unfold page_base, page_base_of, page_size. apply u_small. lia. }
          destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl].
          -- apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. left. rewrite PBx. unfold page_size. nia.
          -- destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh].
             ++ apply orb_true_intro. left. rewrite PBx. apply andb_true_intro. split; apply Z.leb_le; unfold page_size; nia.
             ++ apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. right. rewrite PBx. nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems11.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hhide (H : word -> bool) (lo n : Z) : word -> bool :=
  fun x => H x || ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + n)).
Lemma hhide_in : forall H lo n x, lo <= bv_unsigned x < lo + n -> hhide H lo n x = true.
Proof. intros H lo n x Hx. unfold hhide. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb]. apply orb_true_r. Qed.
Lemma hhide_cases : forall H lo n x, hhide H lo n x = true -> H x = true \/ lo <= bv_unsigned x < lo + n.
Proof.
  intros H lo n x Hx. unfold hhide in Hx. apply orb_prop in Hx as [Hx|Hx]; [left; exact Hx|].
  apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. right. lia.
Qed.
Lemma hhide_old : forall H lo n x, H x = true -> hhide H lo n x = true.
Proof. intros H lo n x Hx. unfold hhide. rewrite Hx. reflexivity. Qed.
Lemma hhide_false : forall H lo n x, hhide H lo n x = false -> H x = false /\ (bv_unsigned x < lo \/ lo + n <= bv_unsigned x).
Proof.
  intros H lo n x Hx. unfold hhide in Hx. apply orb_false_iff in Hx as [H1 H2]. split; [exact H1|].
  apply andb_false_iff in H2 as [H2|H2]; [apply Z.leb_gt in H2 | apply Z.ltb_ge in H2]; lia.
Qed.

(* [comment removed for export] *)
Lemma kn_keep_sound_hide : forall segs E M M' allkn kn ub uk un,
  know_ok segs E M allkn -> know_ok segs E M kn ->
  (forall x : word, bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA ub uk) <= bv_unsigned x < estart E (SA ub uk) + elenZ E un -> M' x = None \/ M' x = M x) ->
  know_ok segs E M' (kn_keep MUnmap allkn kn ub uk un).
Proof.
  intros segs E M M' allkn kn ub uk un Hall Hkn Hout Hin.
  unfold kn_keep. apply Forall_forall. intros K HK.
  apply filter_In in HK as [HinK Hkeep].
  pose proof (proj1 (Forall_forall _ _) Hkn K HinK) as HK.
  unfold keep_b in Hkeep.
  destruct (is_fact_b K) eqn:Hf.
  { destruct K; cbn [is_fact_b] in Hf; try discriminate; exact HK. }
  cbn [orb] in Hkeep. apply orb_prop in Hkeep as [Hsp | Hap].
  - destruct K; cbn [kimg_b] in Hsp; try discriminate.
    cbn [kentry_ok] in *. destruct HK as (H0 & Hhi & Hz). split; [exact H0|]. split; [exact Hhi|].
    intros i Hi.
    destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 i)) (estart E (SA ub uk))) as [Hl|Hge].
    + rewrite Hout by lia. apply Hz. exact Hi.
    + destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 i)) (estart E (SA ub uk) + elenZ E un)) as [Hl2|Hge2].
      * destruct (Hin (Z_to_bv 64 i) ltac:(lia)) as [Hn|Hs]; [exact Hn | rewrite Hs; apply Hz; exact Hi].
      * rewrite Hout by lia. apply Hz. exact Hi.
  - destruct (kapart_b_sound segs E M allkn ub uk un K Hall HK Hap Hf) as (ka & kl & Hshape & Hdis).
    eapply kentry_ok_mem_agree; [exact HK | exact Hshape |].
    intros _ x Hx. apply Hout. lia.
Qed.

Section Theorems12.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_hide : forall (j : nat) H A a tid c pl js sr kn L hc lz R M mdl (d m : Z) (em : expr) (nm : Z) (ce : expr) (ceo cn : Z),
    let E := EB' a tid c pl js in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    IMG_HI <= d -> 0 < m -> d + m <= bv_unsigned sp - stack_max_size ->
    (forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)) ->
    (forall r, In r hc -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= d \/ d + m <= fst (fst r)) ->
    In (em, nm) (l_maps L) -> bv_unsigned (edenot E em) <= d -> d + m <= bv_unsigned (edenot E em) + nm ->
    (forall x : word, d <= bv_unsigned x < d + m -> page_in_ranges (page_base x) lz = true) ->
    0 <= cd -> cd <= d -> d + m <= cd + cn -> cn < 2 ^ 64 ->
    bootS' (hhide H d m) A a tid c pl js sr (kn_keep MUnmap (skipn j kn) (skipn j kn) ce ceo (ELit cn)) L hc lz R M mdl.
  Proof.
    intros j H A a tid c pl js sr kn L hc lz R M mdl d m em nm ce ceo cn E cd HB Hd0 Hm Htop Hz Hhc Hin Hlo1 Hhi1 Hlz Hcd0 Hcd1 Hcd2 Hcd3.
    assert (Hd0' : 0 <= d) by (unfold IMG_HI in Hd0; lia).
    subst E. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    set (V' := mrestrict (hhide H d m) M).
    constructor.
    - exact HR.
    - fold V'. apply (kn_keep_sound_hide SEGS _ (mrestrict H M) V'); [apply know_ok_skipn; exact HKN | apply know_ok_skipn; exact HKN | |];
        unfold estart, elenZ; cbn [a_base a_off edenot]; fold (EB sp draw inp a tid c pl js); rewrite u_small by lia.
      + intros x Hx. unfold V', mrestrict, hhide. destruct (H x); cbn [orb]; [reflexivity|].
        rewrite (proj2 (andb_false_iff _ _)); [reflexivity|]. destruct Hx as [Hx|Hx]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
      + intros x Hx. unfold V', mrestrict, hhide. destruct (H x); cbn [orb]; [left; reflexivity|].
        destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb]; tauto.
    - exact HA.
    - unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx. apply hhide_cases in Hhx as [Hh|Hrg].
      + exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh).
      + rewrite (Hz x Hrg). destruct (Hhc r Hr) as [Hv|Hout]; [rewrite Hv; reflexivity|]. exfalso. destruct r as [[rlo rhi] v]. cbn [fst snd] in Hout, Hx. lia.
    - exact HLZ.
    - exact HM.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply hhide_cases in Hx as [Hx|Hx]; [apply HH; exact Hx|].
        (* [comment removed for export] *)
        apply (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                 ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy)).
        apply Z.leb_le. lia.
      + exact HAW.
      + intros w Hpw Hhw. apply hhide_false in Hhw as [Hhw _]. exact (HCOV w Hpw Hhw).
      + intros x Hx. apply hhide_cases in Hx as [Hx|Hx]; [exact (HIN x Hx)|]. exists (em, nm). split; [exact Hin|]. cbn [fst snd]. lia.
      + exact Hhin.
      + intros x Hx. unfold hhide. rewrite (Habv x Hx). cbn [orb]. apply andb_false_iff. right. apply Z.ltb_ge. unfold stack_max_size in *. lia.
      + intros x Hx. apply hhide_cases in Hx as [Hx|Hx]; [exact (Hhl x Hx)|]. rewrite HLZ. exact (Hlz x Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems12.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems13.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).

  #[using="Type"] Theorem bs_allow : forall H A a tid c pl js sr kn L hc lz R M mdl (lo n : Z),
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' H ((lo, lo + n) :: A) a tid c pl js sr kn L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl lo n HB Hlo Hn Hpos Hlo0 Hbud.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    constructor; try assumption.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - constructor; try assumption.
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
  Qed.
End Theorems13.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.MuslMemset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Sums.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes4_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_change_grow_mono : forall M M' lo n lo' n',
  mem_change MGrow M M' lo n -> lo' <= lo -> lo + n <= lo' + n' -> mem_change MGrow M M' lo' n'.
Proof. intros M M' lo n lo' n' [H1 H2] Ha Hb. split; [| exact H2]. intros x Hx. apply H1. lia. Qed.

Lemma kn_vars_lt_skipn : forall b j kn, kn_vars_lt b kn = true -> kn_vars_lt b (skipn j kn) = true.
Proof.
  intros b j; induction j as [|j IH]; intros kn Hk; [exact Hk|]. destruct kn as [|K kn]; [reflexivity|].
  cbn [skipn]. apply IH. cbn [kn_vars_lt] in Hk. apply andb_prop in Hk as [_ Hk]. exact Hk.
Qed.
Lemma know_ok_skipn : forall segs E M j kn, know_ok segs E M kn -> know_ok segs E M (skipn j kn).
Proof.
  intros segs E M j; induction j as [|j IH]; intros kn HK; [exact HK|]. destruct kn as [|K kn]; [constructor|].
  cbn [skipn]. apply IH. exact (Forall_inv_tail HK).
Qed.

Section Theorems10.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="Type"] Theorem bs_fresh2 : forall H A a tid c pl js sr kn L hc lz R M mdl (ws : list word) (sr' : list expr) (kf : list kentry),
    let v := length (VB' a tid c pl js) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    (regs_ok (EB' a tid c pl (js ++ ws)) sr R -> regs_ok (EB' a tid c pl (js ++ ws)) sr' R) ->
    know_ok SEGS (EB' a tid c pl (js ++ ws)) (mrestrict H M) kf ->
    bootS' H A a tid c pl (js ++ ws) sr' (kf ++ kn) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl ws sr' kf v HB Hsr Hkn HL HSR HKF.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    constructor; try assumption.
    - apply HSR. rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
    - apply (proj2 (know_ok_app SEGS _ _ _ _)). split; [exact HKF|]. rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - apply mfacts_env; assumption.
    - apply maps_ok_env; assumption.
    - apply regime_ok_env; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose3 : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = true \/ mrestrict H M x = Some (Z_to_bv 8 0)) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit m); KWr (SA e eo) (ELit m)] ++ kn_keep MGrow kn kn e eo (ELit m)) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)) as Ue.
    set (addr := Z_to_bv 64 d). set (nw := Z_to_bv 64 m).
    assert (Ulo : bv_unsigned addr = d) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = m) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. destruct (Hhid x Hx) as [Hh|Hv].
      - unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) Hh).
      - unfold mrestrict in Hv. destruct (H x); [discriminate | exact Hv]. }
    assert (EQV : mrestrict (hcut H d m) M = zfill addr nw (mrestrict H M)).
    { extensionality x. unfold mrestrict, hcut, zfill, zmem. rewrite Ulo, Hun.
      destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb negb];
        rewrite ?andb_false_r, ?andb_true_r; try (destruct (H x); reflexivity).
      apply ZERO. lia. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
    constructor.
    - exact HR.
    - rewrite EQV, <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | unfold stack_max_size in *; lia]|].
      rewrite Hun. apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill addr nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia. rewrite <- Hun. apply mem_change_zfill.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memset_cc : forall (clob : list reg) (j : nat) H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo : Z) (iW : nat) (weo wlen cv n ret : Z) (ce : expr) (ceo cn : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    expr_vars_lt v ce = true -> 0 <= cd -> cd <= d -> d + n <= cd + cn -> cn < 2 ^ 64 ->
    incl memset_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    sr_get sr 11%bv = ELit cv -> 0 <= cv < 2 ^ 64 ->
    edenot E (sr_get sr 12%bv) = Z_to_bv 64 n -> 0 <= n ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e weo) (ELit wlen)) -> weo <= eo -> eo + n <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + n <= bv_unsigned sp ->
    (forall R' M' mdl',
       bootS' H A a tid c pl (js ++ junk_c R' clob) (sr_after_call_c sr clob v)
              (KFill (SA e eo) (ELit n) cv :: kn_keep MGrow (skipn j kn) (skipn j kn) ce ceo (ELit cn)) L hc lz R' M' mdl' ->
       (forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> M' x = M x) ->
       (forall x : word, d <= bv_unsigned x < d + n -> M' x = Some (Z_to_bv 8 cv)) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros clob j H A a tid c pl js sr kn L hc lz R M mdl e eo iW weo wlen cv n ret ce ceo cn K E v d cd HB Hce Hcd0 Hcd1 Hcd2 Hcd3 Hincl Hc0 Hnd Hsr Hkn HL Hev S10 S11 Hcv S12 Hn S1 Hret HiW Hweo Hnw Hwlen Hd0 Hdn HK.
    subst E. unfold v in *. clear v. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d).
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; unfold stack_max_size in *; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = Z_to_bv 64 cv) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 n) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw (Z.to_nat n) = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e weo wlen eo (Z.to_nat n) HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    destruct (musl_memset_summary V dw (Z_to_bv 64 cv) (Z_to_bv 64 ret) n ROM R Hn ltac:(rewrite Ud; unfold stack_max_size in *; lia)
                Hst Hret G10 G11 G12 G1) as (R' & MS & P10 & AG & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memset) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (bs := repeat (cbyte (Z_to_bv 64 cv)) (Z.to_nat n)) in *.
    set (V' := wbytes V dw bs) in *.
    assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; [unfold stack_max_size in *; lia | lia]. }
    assert (VIS : forall x : word, d <= bv_unsigned x < d + n -> H x = false).
    { intros x Hx. pose proof (store_ok_all SEGS V (Z.to_nat n) dw ltac:(rewrite Ud, Z2Nat.id by lia; unfold stack_max_size in *; lia) Hst x ltac:(rewrite Ud, Z2Nat.id by lia; lia)) as W.
      unfold V, wview, mrestrict in W. destruct (H x) eqn:EH; [| reflexivity]. exfalso.
      rewrite (HH x EH) in W. exact (W eq_refl). }
    apply HK; [constructor | |].
    13:{ intros x Hx. destruct (H x) eqn:EH; [rewrite (munrestrict_hidden _ _ _ _ EH); reflexivity|].
         rewrite (munrestrict_visible _ _ _ _ EH), V'out by exact Hx. unfold V. rewrite (mrestrict_visible' _ _ _ EH). reflexivity. }
    13:{ intros x Hx. rewrite (munrestrict_visible _ _ _ _ (VIS x Hx)). unfold V'.
         replace x with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat (bv_unsigned x - d)))) by (apply bv_eq; rewrite u_small; [lia | pose proof (u64_range x); lia]).
         rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
         unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity. }
    - (* [comment removed for export] *)
      rewrite EB_app. apply (regs_after_clob clob (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) sr R R' Hsr HR).
      + intros r Hr. apply AG. intros Hin. apply Hr. apply Hincl. exact Hin.
      + exact Hc0.
      + exact Hnd.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. rewrite Hev. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. apply kn_vars_lt_skipn. exact Hkn. }
      constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        fold (EB sp draw inp a tid c pl js). fold d. rewrite !u_small by lia.
        split; [unfold stack_max_size in *; lia|].
        intros i Hi. unfold V'.
        replace (Z_to_bv 64 (d + i)) with (Z_to_bv 64 (bv_unsigned dw + Z.of_nat (Z.to_nat i))) by (f_equal; rewrite Ud; lia).
        rewrite wbytes_nth by (rewrite ?LEN, ?Ud; unfold stack_max_size in *; lia).
        unfold bs. rewrite nth_repeat_lt by lia. unfold cbyte. rewrite u_small by lia. reflexivity.
      + apply (kn_keep_sound SEGS _ V V' MGrow); [apply know_ok_skipn; exact HKN | apply know_ok_skipn; exact HKN |].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite u_small by lia.
        apply (mem_change_grow_mono V V' d n); [| lia | lia].
        rewrite <- Ud. replace n with (Z.of_nat (length bs)) by (rewrite LEN; lia). unfold V'. apply mem_change_wbytes.
        rewrite LEN, Ud. unfold stack_max_size in *. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold stack_max_size in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.


  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose_wr : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = false -> M x <> None) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           (KWr (SA e eo) (ELit m) :: kn_keep MGrow kn kn e eo (ELit m)) L hc lz R M mdl
    /\ (forall x : word, d <= bv_unsigned x < d + m -> H x = true -> M x = Some (Z_to_bv 8 0)).
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range (edenot (EB sp draw inp a tid c pl js) e)) as Ue.
    set (addr := Z_to_bv 64 d). set (nw := Z_to_bv 64 m).
    assert (Ulo : bv_unsigned addr = d) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    assert (Hun : bv_unsigned nw = m) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> H x = true -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx Hh. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) Hh). }
    set (V' := mrestrict (hcut H d m) M).
    assert (CHG : mem_change MGrow (mrestrict H M) V' d m).
    { split.
      - intros x Hx. unfold V', mrestrict, hcut. destruct (H x); cbn [andb]; [| reflexivity].
        rewrite (proj2 (andb_false_iff _ _)); [reflexivity|].
        destruct Hx as [Hx|Hx]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
      - intros x Hx. unfold V', mrestrict, hcut in *. destruct (H x); cbn [andb negb] in *; [exfalso; exact (Hx eq_refl)|]. exact Hx. }
    assert (DEF : forall x : word, d <= bv_unsigned x < d + m -> V' x <> None).
    { intros x Hx. unfold V', mrestrict. rewrite (hcut_false_in H d m x Hx). destruct (H x) eqn:EH; [rewrite (ZERO x Hx EH); discriminate | exact (Hhid x Hx EH)]. }
    assert (Hea : bv_unsigned (edenot (EB sp draw inp a tid c pl js) e) + eo = bv_unsigned addr) by (rewrite Ulo; reflexivity).
    split; [| exact ZERO]. constructor.
    - exact HR.
    - fold V'. constructor.
      + cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite Hea, Ulo, !u_small by lia.
        split; [unfold stack_max_size in *; lia|]. intros dd mm Hdd Hmm. apply store_ok_of_all; [rewrite u_small by (unfold stack_max_size in *; lia); unfold stack_max_size in *; lia|].
        intros x Hx. rewrite u_small in Hx by (unfold stack_max_size in *; lia). unfold wview.
        destruct (V' x) eqn:EV; [discriminate|]. exfalso. exact (DEF x ltac:(lia) EV).
      + apply (kn_keep_sound SEGS _ (mrestrict H M) V' MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, Ulo, u_small by lia. exact CHG.
    - exact HA.
    - apply (hf_ok_antimono H); [intros x Hx; exact (hcut_old _ _ _ _ Hx) | exact HZ].
    - exact HLZ.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply HH. exact (hcut_old _ _ _ _ Hx).
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. unfold hcut in Hhw. apply andb_false_iff in Hhw as [Hhw|Hhw].
        * pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
        * apply negb_false_iff in Hhw. apply andb_prop in Hhw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_intro. left.
          pose proof (u64_range w) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)).
          apply andb_true_intro. split; apply Z.leb_le; nia.
      + intros x Hx. apply HIN. exact (hcut_old _ _ _ _ Hx).
      + exact Hhin.
      + intros x Hx. apply hcut_false_of. apply Habv. exact Hx.
      + intros x Hx. apply Hhl. exact (hcut_old _ _ _ _ Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems10.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems11.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_fixedin_lazy : forall H A a tid c pl js sr kn L hc lz R M mdl (lo len pc : Z) (em : expr) (nm : Z) w (K : TSet),
    let E := EB' a tid c pl js in
    let nZ := page_round_up_Z len in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> edenot E (sr_get sr 10%bv) = Z_to_bv 64 lo -> edenot E (sr_get sr 11%bv) = Z_to_bv 64 len ->
    sr_get sr 12%bv = ELit 3 -> sr_get sr 13%bv = ELit 16434 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> 0 <= lo -> lo mod 4096 = 0 ->
    In (em, nm) (l_maps L) -> sivs_sizes_ok (l_maps L) = true ->
    bv_unsigned (edenot E em) <= lo -> lo + nZ <= bv_unsigned (edenot E em) + nm ->
    map_contains lz (Z_to_bv 64 lo) (Z_to_bv 64 nZ) = true ->
    (forall x : word, lo <= bv_unsigned x < lo + nZ -> H x = true \/ mrestrict H M x = Some (Z_to_bv 8 0)) ->
    (forall r, In r hc -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= lo \/ lo + nZ <= fst (fst r)) ->
    (forall R' mdl',
       bootS' H A a tid c pl js sr kn L hc ((Z_to_bv 64 lo, Z_to_bv 64 nZ) :: maps_subtract lz lo (lo + nZ)) R'
              (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl lo len pc em nm w K E nZ HB HF HE Hpc0 Hpc4
           S17 S10 S11 S12 S13 S14 S15 Hlen Hlo0 Hal Hin Hs Hlo1 Hhi1 Hmcl Hhz Hhc HK. subst E.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. split; [lia|]. split; [lia|].
      unfold page_round_up_Z, page_size. apply Z_mod_mult. }
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    set (addr := Z_to_bv 64 lo) in *.
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    set (n := Z_to_bv 64 nZ) in *.
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hnm. cbn [snd] in Hnm.
    apply andb_prop in Hnm as [N0 N1]. apply Z.leb_le in N0. apply Z.ltb_lt in N1.
    assert (HinM : In (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (em, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) addr n = true).
    { unfold map_contains. apply existsb_exists. exists (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mmap_fixed_rw_budget_ok (Z_to_bv 64 16434) mdl addr n = true).
    { apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact WF | | | | |].
      - rewrite Ulo. unfold page_size. exact Hal.
      - rewrite Hun. unfold page_size. tauto.
      - rewrite Hun. lia.
      - rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      - rewrite vm_backing_used_split, LIM. unfold page_size. lia. }
    assert (Hrfr : region_free (vm_reserved (m_vmmaps mdl)) addr n = true).
    { rewrite (mf_res _ _ _ _ _ _ _ _ _ F). apply reserved_free_of_apart. rewrite Ulo, Hun. lia. }
    assert (G10 : getr R 10%bv = addr) by (rewrite (HR 10%bv); exact S10).
    eapply (srz_mmap_fixedin_top SEGS R (Z_to_bv 64 pc) M ROM mdl w 3 (Z_to_bv 64 16434) addr len K HF HE
              (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (or_intror eq_refl) mmap_flags_core_4032).
    - exact G10.
    - rewrite Ulo. unfold page_size. exact Hal.
    - rewrite Ulo. lia.
    - rewrite (HR 11%bv). exact S11.
    - exact Hlen.
    - rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F), Ulo. fold nZ. unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - rewrite (G _ _ S13). reflexivity.
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact Hrfr.
    - exact Hmc.
    - intros _. exact Hbud'.
    - (* [comment removed for export] *)
      cbn [Z.eqb]. rewrite pc_lit_add4 by lia. fold nZ n.
      set (mdl' := fixedin_ok_model 3 (Z_to_bv 64 16434) addr n mdl).
      assert (EQV : mrestrict H (zfill addr n M) = mrestrict H M).
      { extensionality x. unfold mrestrict. destruct (H x) eqn:EH; [reflexivity|]. unfold zfill, zmem. rewrite Ulo, Hun.
        destruct (Z.leb_spec lo (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + nZ)); cbn [andb]; try reflexivity.
        destruct (Hhz x ltac:(lia)) as [Hh|Hv]; [congruence|]. unfold mrestrict in Hv. rewrite EH in Hv. symmetry. exact Hv. }
      pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
      assert (F1 : bv_unsigned addr mod page_size = 0) by (rewrite Ulo; unfold page_size; exact Hal).
      assert (F2 : bv_unsigned n mod page_size = 0) by (rewrite Hun; unfold page_size; tauto).
      assert (F3 : 0 < bv_unsigned n) by (rewrite Hun; lia).
      assert (F4 : bv_unsigned addr + bv_unsigned n <= 2 ^ 64) by (rewrite Ulo, Hun; unfold stack_max_size in *; lia).
      pose proof mmap_noreserve_b_4032 as F5.
      set (fl := Z_to_bv 64 16434) in *.
      pose proof (fixedin_lazy_lazy fl addr n mdl F1 F2 F3 F4 F5) as LZ'. rewrite Ulo, Hun in LZ'.
      pose proof (model_ivs_wf_fixedin_lazy fl addr n mdl WF F3 F4 F5) as WF'.
      pose proof (eager_used_fixedin_lazy_le fl addr n mdl WF F1 F2 F3 F4 F5) as EGL.
      pose proof (fixedin_lazy_unfold fl addr n mdl F5) as UF.
      apply (HK (regupd R 10%bv addr) mdl'). constructor.
      + apply (AsanNodesMmB.regs_ok_regupd_same _ sr R _ addr HR); [exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate X].
      + rewrite EQV. exact HKN.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl]; [rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh]; [| rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)].
        destruct (Hhc r Hr) as [Hv|Hout]; [| exfalso; destruct r as [[rlo rhi] v]; cbn [fst snd] in Hout, Hx; lia].
        rewrite Hv. unfold zfill, zmem. rewrite Ulo, Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      + unfold mdl'. rewrite LZ', HLZ. reflexivity.
      + unfold mdl'. apply (MInv_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5). constructor; assumption.
      + (* [comment removed for export] *)
        unfold mdl'. constructor.
        * rewrite (fixedin_lazy_halted fl addr n mdl F5). exact Hh.
        * rewrite (fixedin_lazy_reserved fl addr n mdl F5). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_init_sp fl addr n mdl F5). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_limit fl addr n mdl F5). exact LIM.
        * etransitivity; [| exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_brk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_mb _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * rewrite (fixedin_lazy_maps fl addr n mdl F5). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (fixedin_lazy_fs fl addr n mdl F5). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_fds fl addr n mdl F5). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_tid fl addr n mdl F5). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fixedin_lazy_noaccess fl addr n mdl F5). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5); [| exact HCOV]. rewrite HLZ. exact Hmcl.
        * exact HIN.
        * exact Hhin.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite LZ'. rewrite page_in_ranges_cons. cbn [fst snd]. rewrite Ulo, Hun.
          pose proof (Hhl x Hx) as PL. pose proof (u64_range x) as Xr.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)) as XD. pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)) as XM.
          pose proof (Z.div_mod lo 4096 ltac:(lia)) as LD. assert (ND : nZ mod 4096 = 0) by tauto. pose proof (Z.div_mod nZ 4096 ltac:(lia)) as NDm.
          assert (PBx : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
          { unfold page_base, page_base_of, page_size. apply u_small. lia. }
          destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl].
          -- apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. left. rewrite PBx. unfold page_size. nia.
          -- destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh].
             ++ apply orb_true_intro. left. rewrite PBx. apply andb_true_intro. split; apply Z.leb_le; unfold page_size; nia.
             ++ apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. right. rewrite PBx. nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_fixedin_lazy2 : forall H A a tid c pl js sr kn L hc lz R M mdl (lo len pc : Z) (em : expr) (nm : Z) (ce : expr) (ceo cn : Z) w (K : TSet),
    let E := EB' a tid c pl js in
    let nZ := page_round_up_Z len in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    0 <= cd -> cd <= lo -> lo + nZ <= cd + cn -> cn < 2 ^ 64 ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> edenot E (sr_get sr 10%bv) = Z_to_bv 64 lo -> edenot E (sr_get sr 11%bv) = Z_to_bv 64 len ->
    sr_get sr 12%bv = ELit 3 -> sr_get sr 13%bv = ELit 16434 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> 0 <= lo -> lo mod 4096 = 0 ->
    In (em, nm) (l_maps L) -> sivs_sizes_ok (l_maps L) = true ->
    bv_unsigned (edenot E em) <= lo -> lo + nZ <= bv_unsigned (edenot E em) + nm ->
    map_contains lz (Z_to_bv 64 lo) (Z_to_bv 64 nZ) = true ->
    (forall r, In r hc -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= lo \/ lo + nZ <= fst (fst r)) ->
    (forall R' mdl',
       bootS' H A a tid c pl js sr (kn_keep MGrow kn kn ce ceo (ELit cn)) L hc ((Z_to_bv 64 lo, Z_to_bv 64 nZ) :: maps_subtract lz lo (lo + nZ)) R'
              (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill (Z_to_bv 64 lo) (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl lo len pc em nm ce ceo cn w K E nZ cd HB Hcd0 Hcd1 Hcd2 Hcd3 HF HE Hpc0 Hpc4
           S17 S10 S11 S12 S13 S14 S15 Hlen Hlo0 Hal Hin Hs Hlo1 Hhi1 Hmcl Hhc HK. subst E. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. split; [lia|]. split; [lia|].
      unfold page_round_up_Z, page_size. apply Z_mod_mult. }
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    set (addr := Z_to_bv 64 lo) in *.
    assert (Ulo : bv_unsigned addr = lo) by (unfold addr; apply u_small; unfold stack_max_size in *; lia).
    set (n := Z_to_bv 64 nZ) in *.
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hnm. cbn [snd] in Hnm.
    apply andb_prop in Hnm as [N0 N1]. apply Z.leb_le in N0. apply Z.ltb_lt in N1.
    assert (HinM : In (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (em, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) addr n = true).
    { unfold map_contains. apply existsb_exists. exists (edenot (EB sp draw inp a tid c pl js) em, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mmap_fixed_rw_budget_ok (Z_to_bv 64 16434) mdl addr n = true).
    { apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact WF | | | | |].
      - rewrite Ulo. unfold page_size. exact Hal.
      - rewrite Hun. unfold page_size. tauto.
      - rewrite Hun. lia.
      - rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      - rewrite vm_backing_used_split, LIM. unfold page_size. lia. }
    assert (Hrfr : region_free (vm_reserved (m_vmmaps mdl)) addr n = true).
    { rewrite (mf_res _ _ _ _ _ _ _ _ _ F). apply reserved_free_of_apart. rewrite Ulo, Hun. lia. }
    assert (G10 : getr R 10%bv = addr) by (rewrite (HR 10%bv); exact S10).
    eapply (srz_mmap_fixedin_top SEGS R (Z_to_bv 64 pc) M ROM mdl w 3 (Z_to_bv 64 16434) addr len K HF HE
              (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (or_intror eq_refl) mmap_flags_core_4032).
    - exact G10.
    - rewrite Ulo. unfold page_size. exact Hal.
    - rewrite Ulo. lia.
    - rewrite (HR 11%bv). exact S11.
    - exact Hlen.
    - rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F), Ulo. fold nZ. unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - rewrite (G _ _ S13). reflexivity.
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact Hrfr.
    - exact Hmc.
    - intros _. exact Hbud'.
    - (* [comment removed for export] *)
      cbn [Z.eqb]. rewrite pc_lit_add4 by lia. fold nZ n.
      set (mdl' := fixedin_ok_model 3 (Z_to_bv 64 16434) addr n mdl).
      assert (CHG : mem_change MGrow (mrestrict H M) (mrestrict H (zfill addr n M)) lo nZ).
      { split.
        - intros x Hx. unfold mrestrict. destruct (H x); [reflexivity|]. apply zfill_out. rewrite Ulo, Hun. lia.
        - intros x Hx. unfold mrestrict, zfill, zmem in *. destruct (H x); [exact Hx|]. destruct (_ && _)%bool; [discriminate | exact Hx]. }
      pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
      assert (F1 : bv_unsigned addr mod page_size = 0) by (rewrite Ulo; unfold page_size; exact Hal).
      assert (F2 : bv_unsigned n mod page_size = 0) by (rewrite Hun; unfold page_size; tauto).
      assert (F3 : 0 < bv_unsigned n) by (rewrite Hun; lia).
      assert (F4 : bv_unsigned addr + bv_unsigned n <= 2 ^ 64) by (rewrite Ulo, Hun; unfold stack_max_size in *; lia).
      pose proof mmap_noreserve_b_4032 as F5.
      set (fl := Z_to_bv 64 16434) in *.
      pose proof (fixedin_lazy_lazy fl addr n mdl F1 F2 F3 F4 F5) as LZ'. rewrite Ulo, Hun in LZ'.
      pose proof (model_ivs_wf_fixedin_lazy fl addr n mdl WF F3 F4 F5) as WF'.
      pose proof (eager_used_fixedin_lazy_le fl addr n mdl WF F1 F2 F3 F4 F5) as EGL.
      pose proof (fixedin_lazy_unfold fl addr n mdl F5) as UF.
      apply (HK (regupd R 10%bv addr) mdl'). constructor.
      + apply (AsanNodesMmB.regs_ok_regupd_same _ sr R _ addr HR); [exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate X].
      + apply (kn_keep_sound SEGS _ (mrestrict H M) (mrestrict H (zfill addr n M)) MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). rewrite u_small by lia.
        apply (mem_change_grow_mono _ _ lo nZ); [exact CHG | lia | lia].
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl]; [rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh]; [| rewrite zfill_out by (rewrite Ulo, Hun; lia); exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)].
        destruct (Hhc r Hr) as [Hv|Hout]; [| exfalso; destruct r as [[rlo rhi] v]; cbn [fst snd] in Hout, Hx; lia].
        rewrite Hv. unfold zfill, zmem. rewrite Ulo, Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      + unfold mdl'. rewrite LZ', HLZ. reflexivity.
      + unfold mdl'. apply (MInv_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5). constructor; assumption.
      + (* [comment removed for export] *)
        unfold mdl'. constructor.
        * rewrite (fixedin_lazy_halted fl addr n mdl F5). exact Hh.
        * rewrite (fixedin_lazy_reserved fl addr n mdl F5). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_init_sp fl addr n mdl F5). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_limit fl addr n mdl F5). exact LIM.
        * etransitivity; [| exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_brk _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * etransitivity; [| exact (mf_mb _ _ _ _ _ _ _ _ _ F)]. rewrite UF. reflexivity.
        * rewrite (fixedin_lazy_maps fl addr n mdl F5). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (fixedin_lazy_fs fl addr n mdl F5). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_fds fl addr n mdl F5). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fixedin_lazy_tid fl addr n mdl F5). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fixedin_lazy_noaccess fl addr n mdl F5). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_fixedin_lazy A fl addr n mdl WF F1 F2 F3 F4 F5); [| exact HCOV]. rewrite HLZ. exact Hmcl.
        * exact HIN.
        * exact Hhin.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite LZ'. rewrite page_in_ranges_cons. cbn [fst snd]. rewrite Ulo, Hun.
          pose proof (Hhl x Hx) as PL. pose proof (u64_range x) as Xr.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)) as XD. pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)) as XM.
          pose proof (Z.div_mod lo 4096 ltac:(lia)) as LD. assert (ND : nZ mod 4096 = 0) by tauto. pose proof (Z.div_mod nZ 4096 ltac:(lia)) as NDm.
          assert (PBx : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
          { unfold page_base, page_base_of, page_size. apply u_small. lia. }
          destruct (Z.lt_ge_cases (bv_unsigned x) lo) as [Xl|Xl].
          -- apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. left. rewrite PBx. unfold page_size. nia.
          -- destruct (Z.lt_ge_cases (bv_unsigned x) (lo + nZ)) as [Xh|Xh].
             ++ apply orb_true_intro. left. rewrite PBx. apply andb_true_intro. split; apply Z.leb_le; unfold page_size; nia.
             ++ apply orb_true_intro. right. rewrite page_in_ranges_subtract_out; [exact PL | exact W3 | lia |]. right. rewrite PBx. nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems11.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hhide (H : word -> bool) (lo n : Z) : word -> bool :=
  fun x => H x || ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + n)).
Lemma hhide_in : forall H lo n x, lo <= bv_unsigned x < lo + n -> hhide H lo n x = true.
Proof. intros H lo n x Hx. unfold hhide. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb]. apply orb_true_r. Qed.
Lemma hhide_cases : forall H lo n x, hhide H lo n x = true -> H x = true \/ lo <= bv_unsigned x < lo + n.
Proof.
  intros H lo n x Hx. unfold hhide in Hx. apply orb_prop in Hx as [Hx|Hx]; [left; exact Hx|].
  apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. right. lia.
Qed.
Lemma hhide_old : forall H lo n x, H x = true -> hhide H lo n x = true.
Proof. intros H lo n x Hx. unfold hhide. rewrite Hx. reflexivity. Qed.
Lemma hhide_false : forall H lo n x, hhide H lo n x = false -> H x = false /\ (bv_unsigned x < lo \/ lo + n <= bv_unsigned x).
Proof.
  intros H lo n x Hx. unfold hhide in Hx. apply orb_false_iff in Hx as [H1 H2]. split; [exact H1|].
  apply andb_false_iff in H2 as [H2|H2]; [apply Z.leb_gt in H2 | apply Z.ltb_ge in H2]; lia.
Qed.

(* [comment removed for export] *)
Lemma kn_keep_sound_hide : forall segs E M M' allkn kn ub uk un,
  know_ok segs E M allkn -> know_ok segs E M kn ->
  (forall x : word, bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA ub uk) <= bv_unsigned x < estart E (SA ub uk) + elenZ E un -> M' x = None \/ M' x = M x) ->
  know_ok segs E M' (kn_keep MUnmap allkn kn ub uk un).
Proof.
  intros segs E M M' allkn kn ub uk un Hall Hkn Hout Hin.
  unfold kn_keep. apply Forall_forall. intros K HK.
  apply filter_In in HK as [HinK Hkeep].
  pose proof (proj1 (Forall_forall _ _) Hkn K HinK) as HK.
  unfold keep_b in Hkeep.
  destruct (is_fact_b K) eqn:Hf.
  { destruct K; cbn [is_fact_b] in Hf; try discriminate; exact HK. }
  cbn [orb] in Hkeep. apply orb_prop in Hkeep as [Hsp | Hap].
  - destruct K; cbn [kimg_b] in Hsp; try discriminate.
    cbn [kentry_ok] in *. destruct HK as (H0 & Hhi & Hz). split; [exact H0|]. split; [exact Hhi|].
    intros i Hi.
    destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 i)) (estart E (SA ub uk))) as [Hl|Hge].
    + rewrite Hout by lia. apply Hz. exact Hi.
    + destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 i)) (estart E (SA ub uk) + elenZ E un)) as [Hl2|Hge2].
      * destruct (Hin (Z_to_bv 64 i) ltac:(lia)) as [Hn|Hs]; [exact Hn | rewrite Hs; apply Hz; exact Hi].
      * rewrite Hout by lia. apply Hz. exact Hi.
  - destruct (kapart_b_sound segs E M allkn ub uk un K Hall HK Hap Hf) as (ka & kl & Hshape & Hdis).
    eapply kentry_ok_mem_agree; [exact HK | exact Hshape |].
    intros _ x Hx. apply Hout. lia.
Qed.

Section Theorems12.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_hide : forall (j : nat) H A a tid c pl js sr kn L hc lz R M mdl (d m : Z) (em : expr) (nm : Z) (ce : expr) (ceo cn : Z),
    let E := EB' a tid c pl js in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    IMG_HI <= d -> 0 < m -> d + m <= bv_unsigned sp - stack_max_size ->
    (forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)) ->
    (forall r, In r hc -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= d \/ d + m <= fst (fst r)) ->
    In (em, nm) (l_maps L) -> bv_unsigned (edenot E em) <= d -> d + m <= bv_unsigned (edenot E em) + nm ->
    (forall x : word, d <= bv_unsigned x < d + m -> page_in_ranges (page_base x) lz = true) ->
    0 <= cd -> cd <= d -> d + m <= cd + cn -> cn < 2 ^ 64 ->
    bootS' (hhide H d m) A a tid c pl js sr (kn_keep MUnmap (skipn j kn) (skipn j kn) ce ceo (ELit cn)) L hc lz R M mdl.
  Proof.
    intros j H A a tid c pl js sr kn L hc lz R M mdl d m em nm ce ceo cn E cd HB Hd0 Hm Htop Hz Hhc Hin Hlo1 Hhi1 Hlz Hcd0 Hcd1 Hcd2 Hcd3.
    assert (Hd0' : 0 <= d) by (unfold IMG_HI in Hd0; lia).
    subst E. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK. unfold map_ok in MOK. cbn [fst snd] in MOK.
    destruct MOK as (Mal & M4k & Mn & Mtop & Mimg).
    set (V' := mrestrict (hhide H d m) M).
    constructor.
    - exact HR.
    - fold V'. apply (kn_keep_sound_hide SEGS _ (mrestrict H M) V'); [apply know_ok_skipn; exact HKN | apply know_ok_skipn; exact HKN | |];
        unfold estart, elenZ; cbn [a_base a_off edenot]; fold (EB sp draw inp a tid c pl js); rewrite u_small by lia.
      + intros x Hx. unfold V', mrestrict, hhide. destruct (H x); cbn [orb]; [reflexivity|].
        rewrite (proj2 (andb_false_iff _ _)); [reflexivity|]. destruct Hx as [Hx|Hx]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
      + intros x Hx. unfold V', mrestrict, hhide. destruct (H x); cbn [orb]; [left; reflexivity|].
        destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb]; tauto.
    - exact HA.
    - unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx. apply hhide_cases in Hhx as [Hh|Hrg].
      + exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh).
      + rewrite (Hz x Hrg). destruct (Hhc r Hr) as [Hv|Hout]; [rewrite Hv; reflexivity|]. exfalso. destruct r as [[rlo rhi] v]. cbn [fst snd] in Hout, Hx. lia.
    - exact HLZ.
    - exact HM.
    - exact F.
    - exact HMO.
    - constructor.
      + intros x Hx. apply hhide_cases in Hx as [Hx|Hx]; [apply HH; exact Hx|].
        (* [comment removed for export] *)
        apply (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                 ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy)).
        apply Z.leb_le. lia.
      + exact HAW.
      + intros w Hpw Hhw. apply hhide_false in Hhw as [Hhw _]. exact (HCOV w Hpw Hhw).
      + intros x Hx. apply hhide_cases in Hx as [Hx|Hx]; [exact (HIN x Hx)|]. exists (em, nm). split; [exact Hin|]. cbn [fst snd]. lia.
      + exact Hhin.
      + intros x Hx. unfold hhide. rewrite (Habv x Hx). cbn [orb]. apply andb_false_iff. right. apply Z.ltb_ge. unfold stack_max_size in *. lia.
      + intros x Hx. apply hhide_cases in Hx as [Hx|Hx]; [exact (Hhl x Hx)|]. rewrite HLZ. exact (Hlz x Hx).
      + exact Hshd.
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems12.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems13.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).

  #[using="Type"] Theorem bs_allow : forall H A a tid c pl js sr kn L hc lz R M mdl (lo n : Z),
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo ->
    l_eager L + n + A_bytes A <= lim ->
    bootS' H ((lo, lo + n) :: A) a tid c pl js sr kn L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl lo n HB Hlo Hn Hpos Hlo0 Hbud.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    constructor; try assumption.
    - apply (MInv_mono A); [| | exact HM].
      + intros p Hp. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite Hp. apply orb_true_r.
      + cbn [A_bytes fst snd]. rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
    - constructor; try assumption.
      + constructor; [cbn [fst snd]; unfold page_size | exact HAW].
        split; [lia|]. split; [exact Hlo|]. rewrite Z.add_mod, Hlo, Hn by lia. reflexivity.
      + intros w Hpw Hhw. pose proof (HCOV w Hpw Hhw) as X. unfold page_allowedb in *. cbn [existsb fst snd]. rewrite X. apply orb_true_r.
  Qed.
End Theorems13.
End TwB.
End BootNodes4.
