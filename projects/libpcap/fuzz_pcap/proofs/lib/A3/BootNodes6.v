(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import MuslMemcpyBase MuslMemcpy MuslMemcpySpec A3Sums.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes6_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_le (B : Z) (K : kentry) : bool := match K with KImg lo hi => hi <=? B | _ => true end.

Lemma seg_rom_off : forall x : word, find_segment SEGS (bv_unsigned x) 1 = None -> seg_rom SEGS x = None.
Proof. intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Hx. reflexivity. Qed.

Lemma word_off_eq : forall (a x : word), bv_unsigned a <= bv_unsigned x -> (a + nat_to_word (Z.to_nat (bv_unsigned x - bv_unsigned a)))%bv = x.
Proof.
  intros a x H. pose proof (u64_range x). pose proof (u64_range a). apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned.
  rewrite u_small by lia. unfold bv_wrap. rewrite Z2Nat.id by lia.
  replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia. unfold bv_modulus. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma know_ok_grow : forall E M M' kn (lo hi B : Z),
  know_ok SEGS E M kn ->
  (forall x : word, M x <> None -> M' x = M x) ->
  (forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, lo <= bv_unsigned x < hi -> seg_rom SEGS x = None) ->
  forallb (kimg_le B) kn = true -> B <= lo ->
  know_ok SEGS E M' kn.
Proof.
  intros E M M' kn lo hi B HK Hdef Hout Hrom Himg HB. apply Forall_forall. intros K HinK.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KO.
  pose proof (proj1 (forallb_forall _ _) Himg _ HinK) as KI.
  (* [comment removed for export] *)
  assert (RD : forall (a : word) n bs j, rdn SEGS M a n = Some bs -> (j < n)%nat -> M' (a + nat_to_word j)%bv = M (a + nat_to_word j)%bv).
  { intros a n bs j Hr Hj. pose proof (rdn_rd1 SEGS M n a bs j Hr Hj) as D. unfold rd1 in D.
    destruct (M (a + nat_to_word j)%bv) as [bb|] eqn:Mx; [rewrite <- Mx; apply Hdef; rewrite Mx; discriminate|].
    rewrite <- Mx.
    destruct (Z.lt_ge_cases (bv_unsigned (a + nat_to_word j)%bv) lo) as [L|L]; [apply Hout; left; exact L|].
    destruct (Z.lt_ge_cases (bv_unsigned (a + nat_to_word j)%bv) hi) as [R|R]; [|apply Hout; right; exact R].
    rewrite (Hrom (a + nat_to_word j)%bv ltac:(split; [exact L | exact R])) in D. exfalso. apply D. reflexivity. }
  destruct K as [[b k] w v|[b k] l|[b k] l bk|ilo ihi|ae am|re rlo rhi|[b k] n|da1 dn1 da2 dn2|[b k] l c|[b k] l];
    cbn [kentry_ok kimg_le] in *; try exact KO.
  - (* [comment removed for export] *) destruct KO as (Hw8 & Hfl & Hrd). split; [exact Hw8|]. split; [exact Hfl|]. rewrite <- Hrd.
    pose proof (flat_u E (SA b k) _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_ext; [rewrite Hu; lia|]. intros x Hx.
    rewrite <- (word_off_eq (adenot E (SA b k)) x ltac:(lia)). apply (RD _ w _ _ Hrd). rewrite Hu in Hx. lia.
  - (* [comment removed for export] *) destruct KO as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite Hdef; [apply Hz; exact Hi | rewrite (Hz i Hi); discriminate].
  - (* [comment removed for export] *) destruct KO as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|].
    intros i Hi. rewrite Hdef; [apply Hz; exact Hi | rewrite (Hz i Hi); discriminate].
  - (* [comment removed for export] *) destruct KO as (H0 & Hhi & Hz). split; [exact H0|]. split; [exact Hhi|]. apply Z.leb_le in KI.
    intros i Hi. rewrite Hout; [apply Hz; exact Hi|]. left. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) destruct KO as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    apply (store_ok_mono SEGS m M M'); [| exact (Hst d m Hd Hm)]. intros x Hx. rewrite (Hdef x Hx). exact Hx.
  - (* [comment removed for export] *) destruct KO as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite Hdef; [apply Hz; exact Hi | rewrite (Hz i Hi); discriminate].
  - (* [comment removed for export] *) destruct KO as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite Hdef; [apply Hz; exact Hi | exact (Hz i Hi)].
Qed.

Lemma off_img' : forall x : word, IMG_HI <= bv_unsigned x -> find_segment SEGS (bv_unsigned x) 1 = None.
Proof.
  intros x Hx. exact (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                      ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy) x ltac:(apply Z.leb_le; exact Hx)).
Qed.

Section Theorems14.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose_keep : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n -> IMG_HI <= d ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = true) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    forallb (kimg_le IMG_HI) kn = true ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit m); KWr (SA e eo) (ELit m)] ++ kn) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Himg Hhid Hin Hrlo Hrhi Hbud Hkimg. subst E.
    pose proof (bs_expose2 sp brk mbase draw lim inp VI VE H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi
                  HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud) as HB2. cbv zeta in HB2. fold d in HB2.
    eapply bootS_reknow; [exact HB2 | auto |]. intros HK2.
    pose proof (Forall_inv HK2) as K1. pose proof (Forall_inv (Forall_inv_tail HK2)) as K2.
    constructor; [exact K1|]. constructor; [exact K2|].
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) (Hhid x Hx)). }
    apply (know_ok_grow _ (mrestrict H M) (mrestrict (hcut H d m) M) kn d (d + m) IMG_HI HKN).
    - intros x Hx. unfold mrestrict, hcut in *. destruct (H x); [exfalso; apply Hx; reflexivity|]. reflexivity.
    - intros x Hx. unfold mrestrict, hcut. destruct (H x); [|reflexivity]. cbn [andb].
      destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb negb]; try reflexivity. lia.
    - intros x Hx. apply seg_rom_off. apply off_img'. lia.
    - exact Hkimg.
    - exact Himg.
  Qed.
End Theorems14.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memcpy_clob : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Lemma wleb8_lez : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. unfold word_to_le_bytes, le_bytes_to_word. pose proof (lez_bound_len bs 8%nat H) as B.
  change (8 * Z.of_nat 8) with 64 in B. rewrite u_small by lia. rewrite <- H. apply Z_to_le_bytes_lez.
Qed.

Lemma saddr_vars_lt_weaken : forall b b' a, (b <= b')%nat -> saddr_vars_lt b a = true -> saddr_vars_lt b' a = true.
Proof. intros b b' [e k] Hb H. cbn [saddr_vars_lt] in *. exact (expr_vars_lt_weaken b b' e Hb H). Qed.
Lemma kentry_vars_lt_weaken : forall b b' K, (b <= b')%nat -> kentry_vars_lt b K = true -> kentry_vars_lt b' K = true.
Proof.
  intros b b' K Hb H. destruct K; cbn [kentry_vars_lt] in *; try reflexivity;
    repeat (apply andb_prop in H as [H ?X]); rewrite ?andb_true_iff; repeat split;
    try (eapply expr_vars_lt_weaken; [exact Hb | assumption]); try (eapply saddr_vars_lt_weaken; [exact Hb | assumption]).
Qed.
Lemma kn_vars_lt_weaken : forall b b' kn, (b <= b')%nat -> kn_vars_lt b kn = true -> kn_vars_lt b' kn = true.
Proof.
  intros b b' kn Hb. induction kn as [|K kn IH]; intros H; [reflexivity|]. cbn [kn_vars_lt] in *.
  apply andb_prop in H as [H1 H2]. rewrite (kentry_vars_lt_weaken b b' K Hb H1), (IH H2). reflexivity.
Qed.

Section Theorems15.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memcpy8 : forall (clob : list reg) (j : nat) H A a tid c pl js sr kn L hc lz R M mdl
      (e : expr) (eo : Z) (iW : nat) (weo wlen s ret : Z) (bs : list byte) (ce : expr) (ceo cn : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    expr_vars_lt v ce = true -> 0 <= cd -> cd <= d -> d + 8 <= cd + cn -> cn < 2 ^ 64 ->
    incl memcpy_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    edenot E (sr_get sr 11%bv) = Z_to_bv 64 s -> edenot E (sr_get sr 12%bv) = Z_to_bv 64 8 ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e weo) (ELit wlen)) -> weo <= eo -> eo + 8 <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + 8 <= bv_unsigned sp ->
    length bs = 8%nat -> rdn SEGS (mrestrict H M) (Z_to_bv 64 s) 8 = Some bs ->
    (d + 8 <= s \/ s + 8 <= d) -> 0 <= s -> s + 8 < 2 ^ 64 ->
    (forall R' M' mdl',
       bootS' H A a tid c pl ((js ++ [le_bytes_to_word bs]) ++ junk_c R' clob) (sr_after_call_c sr clob (Datatypes.S v))
              (KWord (SA e eo) 8%nat (EVar v) :: kn_keep MGrow (skipn j kn) (skipn j kn) ce ceo (ELit cn)) L hc lz R' M' mdl' ->
       (forall x : word, bv_unsigned x < d \/ d + 8 <= bv_unsigned x -> M' x = M x) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memcpy) M ROM) mdl) K.
  Proof.
    intros clob j H A a tid c pl js sr kn L hc lz R M mdl e eo iW weo wlen s ret bs ce ceo cn K E v d cd
           HB Hce Hcd0 Hcd1 Hcd2 Hcd3 Hincl Hc0 Hnd Hsr Hkn HL Hev S10 S11 S12 S1 Hret HiW Hweo Hnw Hwlen Hd0 Hdn
           LEN RDN Hdisj Hs0 Hs1 HK.
    subst E. unfold v in *. clear v. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d). set (sw := Z_to_bv 64 s) in *.
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; lia).
    assert (Us : bv_unsigned sw = s) by (unfold sw; apply u_small; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = sw) by (rewrite (HR 11%bv); exact S11).
    assert (G12 : getr R 12%bv = Z_to_bv 64 8) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw 8%nat = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e weo wlen eo 8%nat HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    assert (HMC : mcH V dw sw 8 bs).
    { constructor; rewrite ?LEN, ?Ud, ?Us; try lia; [exact RDN | exact Hst]. }
    destruct (musl_memcpy_spec V ROM dw sw 8 bs R (Z_to_bv 64 ret) HMC Hret G1 G10 G11 G12) as (R' & MS & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memcpy) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (V' := wbytes V dw bs) in *.
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + 8 <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; lia. }
    assert (VIS : forall x : word, d <= bv_unsigned x < d + 8 -> H x = false).
    { intros x Hx. pose proof (store_ok_all SEGS V 8%nat dw ltac:(rewrite Ud; lia) Hst x ltac:(rewrite Ud; lia)) as W.
      unfold V, wview, mrestrict in W. destruct (H x) eqn:EH; [| reflexivity]. exfalso.
      rewrite (HH x EH) in W. exact (W eq_refl). }
    assert (AG : forall r : reg, ~ In r clob -> getr R' r = getr R r).
    { intros r Hr. assert (Hm : ~ In r memcpy_clob) by (intros X; apply Hr, Hincl, X).
      destruct (bv_eq_dec 5 r 0%bv) as [->|N0]; [reflexivity|].
      (* [comment removed for export] *)
      destruct (bv_eq_dec 5 r 1%bv) as [->|N1]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 2%bv) as [->|N2]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 3%bv) as [->|N3]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 4%bv) as [->|N4]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 8%bv) as [->|N8]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 9%bv) as [->|N9]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 10%bv) as [->|N10]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 18%bv) as [->|N18]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 19%bv) as [->|N19]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 20%bv) as [->|N20]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 21%bv) as [->|N21]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 22%bv) as [->|N22]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 23%bv) as [->|N23]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 24%bv) as [->|N24]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 25%bv) as [->|N25]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 26%bv) as [->|N26]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 27%bv) as [->|N27]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      exfalso. unfold memcpy_clob in Hm. cbn [In] in Hm. pose proof (bv_unsigned_in_range 5 r) as RR. change (bv_modulus 5) with 32 in RR.
      assert (U0 : bv_unsigned r <> 0) by (intros X; apply N0; apply bv_eq; exact X).
      assert (U1 : bv_unsigned r <> 1) by (intros X; apply N1; apply bv_eq; exact X).
      assert (U2 : bv_unsigned r <> 2) by (intros X; apply N2; apply bv_eq; exact X).
      assert (U3 : bv_unsigned r <> 3) by (intros X; apply N3; apply bv_eq; exact X).
      assert (U4 : bv_unsigned r <> 4) by (intros X; apply N4; apply bv_eq; exact X).
      assert (U8 : bv_unsigned r <> 8) by (intros X; apply N8; apply bv_eq; exact X).
      assert (U9 : bv_unsigned r <> 9) by (intros X; apply N9; apply bv_eq; exact X).
      assert (U10 : bv_unsigned r <> 10) by (intros X; apply N10; apply bv_eq; exact X).
      assert (U18 : bv_unsigned r <> 18) by (intros X; apply N18; apply bv_eq; exact X).
      assert (U19 : bv_unsigned r <> 19) by (intros X; apply N19; apply bv_eq; exact X).
      assert (U20 : bv_unsigned r <> 20) by (intros X; apply N20; apply bv_eq; exact X).
      assert (U21 : bv_unsigned r <> 21) by (intros X; apply N21; apply bv_eq; exact X).
      assert (U22 : bv_unsigned r <> 22) by (intros X; apply N22; apply bv_eq; exact X).
      assert (U23 : bv_unsigned r <> 23) by (intros X; apply N23; apply bv_eq; exact X).
      assert (U24 : bv_unsigned r <> 24) by (intros X; apply N24; apply bv_eq; exact X).
      assert (U25 : bv_unsigned r <> 25) by (intros X; apply N25; apply bv_eq; exact X).
      assert (U26 : bv_unsigned r <> 26) by (intros X; apply N26; apply bv_eq; exact X).
      assert (U27 : bv_unsigned r <> 27) by (intros X; apply N27; apply bv_eq; exact X).
      assert (U5 : bv_unsigned r <> 5) by (intros X; apply Hm; do 0 right; left; apply bv_eq; symmetry; exact X).
      assert (U6 : bv_unsigned r <> 6) by (intros X; apply Hm; do 1 right; left; apply bv_eq; symmetry; exact X).
      assert (U7 : bv_unsigned r <> 7) by (intros X; apply Hm; do 2 right; left; apply bv_eq; symmetry; exact X).
      assert (U11 : bv_unsigned r <> 11) by (intros X; apply Hm; do 3 right; left; apply bv_eq; symmetry; exact X).
      assert (U12 : bv_unsigned r <> 12) by (intros X; apply Hm; do 4 right; left; apply bv_eq; symmetry; exact X).
      assert (U13 : bv_unsigned r <> 13) by (intros X; apply Hm; do 5 right; left; apply bv_eq; symmetry; exact X).
      assert (U14 : bv_unsigned r <> 14) by (intros X; apply Hm; do 6 right; left; apply bv_eq; symmetry; exact X).
      assert (U15 : bv_unsigned r <> 15) by (intros X; apply Hm; do 7 right; left; apply bv_eq; symmetry; exact X).
      assert (U16 : bv_unsigned r <> 16) by (intros X; apply Hm; do 8 right; left; apply bv_eq; symmetry; exact X).
      assert (U17 : bv_unsigned r <> 17) by (intros X; apply Hm; do 9 right; left; apply bv_eq; symmetry; exact X).
      assert (U28 : bv_unsigned r <> 28) by (intros X; apply Hm; do 10 right; left; apply bv_eq; symmetry; exact X).
      assert (U29 : bv_unsigned r <> 29) by (intros X; apply Hm; do 11 right; left; apply bv_eq; symmetry; exact X).
      assert (U30 : bv_unsigned r <> 30) by (intros X; apply Hm; do 12 right; left; apply bv_eq; symmetry; exact X).
      assert (U31 : bv_unsigned r <> 31) by (intros X; apply Hm; do 13 right; left; apply bv_eq; symmetry; exact X).
      lia. }
    set (w := le_bytes_to_word bs) in *.
    assert (VBapp : VB sp draw inp a tid c pl (js ++ [w]) = VB sp draw inp a tid c pl js ++ [w]) by (unfold VB; rewrite <- !app_assoc; reflexivity).
    assert (LENw : length (VB sp draw inp a tid c pl (js ++ [w])) = Datatypes.S (length (VB sp draw inp a tid c pl js))).
    { rewrite VBapp, length_app. cbn [length]. lia. }
    assert (Hsr1 : sr_vars_lt (length (VB sp draw inp a tid c pl (js ++ [w]))) sr = true).
    { rewrite LENw. apply (sr_vars_lt_weaken (length (VB sp draw inp a tid c pl js))); [lia | exact Hsr]. }
    assert (AGR : env_agree (length (VB sp draw inp a tid c pl js)) (EB sp draw inp a tid c pl js) (Env (vals_ev (VB sp draw inp a tid c pl js ++ [w])) (blobs0 draw (in_argv inp)))).
    { unfold EB. apply vals_app_agree. }
    apply HK; [constructor |].
    13:{ intros x Hx. destruct (H x) eqn:EH; [rewrite (munrestrict_hidden _ _ _ _ EH); reflexivity|].
         rewrite (munrestrict_visible _ _ _ _ EH), V'out by exact Hx. unfold V. rewrite (mrestrict_visible' _ _ _ EH). reflexivity. }
    - (* [comment removed for export] *)
      rewrite EB_app, <- LENw. apply (regs_after_clob clob (VB sp draw inp a tid c pl (js ++ [w])) (blobs0 draw (in_argv inp)) sr R R' Hsr1).
      + rewrite VBapp. apply env_app_regs; [exact Hsr | exact HR].
      + exact AG.
      + exact Hc0.
      + exact Hnd.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { rewrite LENw. cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb].
        rewrite (expr_vars_lt_weaken (length (VB sp draw inp a tid c pl js))) by (lia || exact Hev). cbn [andb].
        rewrite (proj2 (Nat.ltb_lt _ _)) by lia. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. apply kn_vars_lt_skipn. apply (kn_vars_lt_weaken (length (VB sp draw inp a tid c pl js))); [lia | exact Hkn]. }
      rewrite VBapp. constructor.
      + cbn [kentry_ok]. split; [lia|].
        assert (Ee : edenot (Env (vals_ev (VB sp draw inp a tid c pl js ++ [w])) (blobs0 draw (in_argv inp))) e = edenot (EB sp draw inp a tid c pl js) e).
        { symmetry. apply (edenot_agree (length (VB sp draw inp a tid c pl js))); [exact AGR | exact Hev]. }
        assert (Ew : edenot (Env (vals_ev (VB sp draw inp a tid c pl js ++ [w])) (blobs0 draw (in_argv inp))) (EVar (length (VB sp draw inp a tid c pl js))) = w).
        { cbn [edenot ev]. replace (length (VB sp draw inp a tid c pl js)) with (length (VB sp draw inp a tid c pl js) + 0)%nat by lia. rewrite vals_ev_app_r. reflexivity. }
        unfold flat, estart, elenZ. rewrite adenot_SA. cbn [a_base a_off]. rewrite Ee, Ew. fold d.
        split; [lia|]. unfold V'. fold dw. replace (word_to_le_bytes 8 w) with bs by (unfold w; symmetry; exact (wleb8_lez bs LEN)).
        rewrite <- LEN. apply rdn_wbytes_hit. rewrite LEN, Ud. lia.
      + apply (kn_keep_sound SEGS _ V V' MGrow).
        * apply know_ok_skipn. apply (know_ok_agree SEGS _ _ _ _ _ AGR); [| exact HKN]. exact Hkn.
        * apply know_ok_skipn. apply (know_ok_agree SEGS _ _ _ _ _ AGR); [| exact HKN]. exact Hkn.
        * unfold estart, elenZ. cbn [a_base a_off edenot].
          rewrite <- (edenot_agree (length (VB sp draw inp a tid c pl js)) _ _ ce AGR Hce). rewrite u_small by lia.
          apply (mem_change_grow_mono V V' d 8); [| lia | lia].
          rewrite <- Ud. replace 8 with (Z.of_nat (length bs)) by (rewrite LEN; reflexivity). unfold V'. apply mem_change_wbytes.
          rewrite LEN, Ud. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold usp in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - rewrite <- app_assoc. apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - rewrite <- app_assoc. apply maps_ok_env; [exact HL | exact HMO].
    - rewrite <- app_assoc. apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems15.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.MuslMemcpyBase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.MuslMemcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.MuslMemcpySpec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Sums.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.MemsetLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes6_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_le (B : Z) (K : kentry) : bool := match K with KImg lo hi => hi <=? B | _ => true end.

Lemma seg_rom_off : forall x : word, find_segment SEGS (bv_unsigned x) 1 = None -> seg_rom SEGS x = None.
Proof. intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Hx. reflexivity. Qed.

Lemma word_off_eq : forall (a x : word), bv_unsigned a <= bv_unsigned x -> (a + nat_to_word (Z.to_nat (bv_unsigned x - bv_unsigned a)))%bv = x.
Proof.
  intros a x H. pose proof (u64_range x). pose proof (u64_range a). apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned.
  rewrite u_small by lia. unfold bv_wrap. rewrite Z2Nat.id by lia.
  replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia. unfold bv_modulus. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma know_ok_grow : forall E M M' kn (lo hi B : Z),
  know_ok SEGS E M kn ->
  (forall x : word, M x <> None -> M' x = M x) ->
  (forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, lo <= bv_unsigned x < hi -> seg_rom SEGS x = None) ->
  forallb (kimg_le B) kn = true -> B <= lo ->
  know_ok SEGS E M' kn.
Proof.
  intros E M M' kn lo hi B HK Hdef Hout Hrom Himg HB. apply Forall_forall. intros K HinK.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KO.
  pose proof (proj1 (forallb_forall _ _) Himg _ HinK) as KI.
  (* [comment removed for export] *)
  assert (RD : forall (a : word) n bs j, rdn SEGS M a n = Some bs -> (j < n)%nat -> M' (a + nat_to_word j)%bv = M (a + nat_to_word j)%bv).
  { intros a n bs j Hr Hj. pose proof (rdn_rd1 SEGS M n a bs j Hr Hj) as D. unfold rd1 in D.
    destruct (M (a + nat_to_word j)%bv) as [bb|] eqn:Mx; [rewrite <- Mx; apply Hdef; rewrite Mx; discriminate|].
    rewrite <- Mx.
    destruct (Z.lt_ge_cases (bv_unsigned (a + nat_to_word j)%bv) lo) as [L|L]; [apply Hout; left; exact L|].
    destruct (Z.lt_ge_cases (bv_unsigned (a + nat_to_word j)%bv) hi) as [R|R]; [|apply Hout; right; exact R].
    rewrite (Hrom (a + nat_to_word j)%bv ltac:(split; [exact L | exact R])) in D. exfalso. apply D. reflexivity. }
  destruct K as [[b k] w v|[b k] l|[b k] l bk|ilo ihi|ae am|re rlo rhi|[b k] n|da1 dn1 da2 dn2|[b k] l c|[b k] l];
    cbn [kentry_ok kimg_le] in *; try exact KO.
  - (* [comment removed for export] *) destruct KO as (Hw8 & Hfl & Hrd). split; [exact Hw8|]. split; [exact Hfl|]. rewrite <- Hrd.
    pose proof (flat_u E (SA b k) _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_ext; [rewrite Hu; lia|]. intros x Hx.
    rewrite <- (word_off_eq (adenot E (SA b k)) x ltac:(lia)). apply (RD _ w _ _ Hrd). rewrite Hu in Hx. lia.
  - (* [comment removed for export] *) destruct KO as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite Hdef; [apply Hz; exact Hi | rewrite (Hz i Hi); discriminate].
  - (* [comment removed for export] *) destruct KO as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|].
    intros i Hi. rewrite Hdef; [apply Hz; exact Hi | rewrite (Hz i Hi); discriminate].
  - (* [comment removed for export] *) destruct KO as (H0 & Hhi & Hz). split; [exact H0|]. split; [exact Hhi|]. apply Z.leb_le in KI.
    intros i Hi. rewrite Hout; [apply Hz; exact Hi|]. left. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) destruct KO as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    apply (store_ok_mono SEGS m M M'); [| exact (Hst d m Hd Hm)]. intros x Hx. rewrite (Hdef x Hx). exact Hx.
  - (* [comment removed for export] *) destruct KO as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite Hdef; [apply Hz; exact Hi | rewrite (Hz i Hi); discriminate].
  - (* [comment removed for export] *) destruct KO as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite Hdef; [apply Hz; exact Hi | exact (Hz i Hi)].
Qed.

Lemma off_img' : forall x : word, IMG_HI <= bv_unsigned x -> find_segment SEGS (bv_unsigned x) 1 = None.
Proof.
  intros x Hx. exact (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                      ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy) x ltac:(apply Z.leb_le; exact Hx)).
Qed.

Section Theorems14.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_expose_keep : forall H A a tid c pl js sr kn L hc lz R M mdl (e : expr) (eo m lo n : Z) (rlo rhi : Z),
    let E := EB' a tid c pl js in
    let d := bv_unsigned (edenot E e) + eo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    lo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n -> 0 <= lo -> lo + n <= bv_unsigned sp - stack_max_size ->
    lo <= d -> 0 < m -> d + m <= lo + n -> IMG_HI <= d ->
    (forall x : word, d <= bv_unsigned x < d + m -> H x = true) ->
    In (rlo, rhi, Some (Z_to_bv 8 0)) hc -> rlo <= d -> d + m <= rhi ->
    l_eager L + n + A_bytes A <= lim ->
    forallb (kimg_le IMG_HI) kn = true ->
    bootS' (hcut H d m) ((lo, lo + n) :: A) a tid c pl js sr
           ([KZero (SA e eo) (ELit m); KWr (SA e eo) (ELit m)] ++ kn) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi E d HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Himg Hhid Hin Hrlo Hrhi Hbud Hkimg. subst E.
    pose proof (bs_expose2 sp brk mbase draw lim inp VI VE H A a tid c pl js sr kn L hc lz R M mdl e eo m lo n rlo rhi
                  HB Hlo Hn Hpos Hlo0 Htop Hd1 Hm Hd2 Hhid Hin Hrlo Hrhi Hbud) as HB2. cbv zeta in HB2. fold d in HB2.
    eapply bootS_reknow; [exact HB2 | auto |]. intros HK2.
    pose proof (Forall_inv HK2) as K1. pose proof (Forall_inv (Forall_inv_tail HK2)) as K2.
    constructor; [exact K1|]. constructor; [exact K2|].
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (ZERO : forall x : word, d <= bv_unsigned x < d + m -> M x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold hf_ok in HZ. exact (proj1 (Forall_forall _ _) HZ _ Hin x ltac:(cbn [fst snd]; lia) (Hhid x Hx)). }
    apply (know_ok_grow _ (mrestrict H M) (mrestrict (hcut H d m) M) kn d (d + m) IMG_HI HKN).
    - intros x Hx. unfold mrestrict, hcut in *. destruct (H x); [exfalso; apply Hx; reflexivity|]. reflexivity.
    - intros x Hx. unfold mrestrict, hcut. destruct (H x); [|reflexivity]. cbn [andb].
      destruct (Z.leb_spec d (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (d + m)); cbn [andb negb]; try reflexivity. lia.
    - intros x Hx. apply seg_rom_off. apply off_img'. lia.
    - exact Hkimg.
    - exact Himg.
  Qed.
End Theorems14.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memcpy_clob : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Lemma wleb8_lez : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. unfold word_to_le_bytes, le_bytes_to_word. pose proof (lez_bound_len bs 8%nat H) as B.
  change (8 * Z.of_nat 8) with 64 in B. rewrite u_small by lia. rewrite <- H. apply Z_to_le_bytes_lez.
Qed.

Lemma saddr_vars_lt_weaken : forall b b' a, (b <= b')%nat -> saddr_vars_lt b a = true -> saddr_vars_lt b' a = true.
Proof. intros b b' [e k] Hb H. cbn [saddr_vars_lt] in *. exact (expr_vars_lt_weaken b b' e Hb H). Qed.
Lemma kentry_vars_lt_weaken : forall b b' K, (b <= b')%nat -> kentry_vars_lt b K = true -> kentry_vars_lt b' K = true.
Proof.
  intros b b' K Hb H. destruct K; cbn [kentry_vars_lt] in *; try reflexivity;
    repeat (apply andb_prop in H as [H ?X]); rewrite ?andb_true_iff; repeat split;
    try (eapply expr_vars_lt_weaken; [exact Hb | assumption]); try (eapply saddr_vars_lt_weaken; [exact Hb | assumption]).
Qed.
Lemma kn_vars_lt_weaken : forall b b' kn, (b <= b')%nat -> kn_vars_lt b kn = true -> kn_vars_lt b' kn = true.
Proof.
  intros b b' kn Hb. induction kn as [|K kn IH]; intros H; [reflexivity|]. cbn [kn_vars_lt] in *.
  apply andb_prop in H as [H1 H2]. rewrite (kentry_vars_lt_weaken b b' K Hb H1), (IH H2). reflexivity.
Qed.

Section Theorems15.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem cross_musl_memcpy8 : forall (clob : list reg) (j : nat) H A a tid c pl js sr kn L hc lz R M mdl
      (e : expr) (eo : Z) (iW : nat) (weo wlen s ret : Z) (bs : list byte) (ce : expr) (ceo cn : Z) (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let d := bv_unsigned (edenot E e) + eo in
    let cd := bv_unsigned (edenot E ce) + ceo in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    expr_vars_lt v ce = true -> 0 <= cd -> cd <= d -> d + 8 <= cd + cn -> cn < 2 ^ 64 ->
    incl memcpy_clob clob -> ~ In (0%bv : reg) clob -> List.NoDup clob ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> expr_vars_lt v e = true ->
    split_lit (sr_get sr 10%bv) = (e, eo) ->
    edenot E (sr_get sr 11%bv) = Z_to_bv 64 s -> edenot E (sr_get sr 12%bv) = Z_to_bv 64 8 ->
    sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    nth_error kn iW = Some (KWr (SA e weo) (ELit wlen)) -> weo <= eo -> eo + 8 <= weo + wlen -> wlen < 2 ^ 64 ->
    0 <= d -> d + 8 <= bv_unsigned sp ->
    length bs = 8%nat -> rdn SEGS (mrestrict H M) (Z_to_bv 64 s) 8 = Some bs ->
    (d + 8 <= s \/ s + 8 <= d) -> 0 <= s -> s + 8 < 2 ^ 64 ->
    (forall R' M' mdl',
       bootS' H A a tid c pl ((js ++ [le_bytes_to_word bs]) ++ junk_c R' clob) (sr_after_call_c sr clob (Datatypes.S v))
              (KWord (SA e eo) 8%nat (EVar v) :: kn_keep MGrow (skipn j kn) (skipn j kn) ce ceo (ELit cn)) L hc lz R' M' mdl' ->
       (forall x : word, bv_unsigned x < d \/ d + 8 <= bv_unsigned x -> M' x = M x) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memcpy) M ROM) mdl) K.
  Proof.
    intros clob j H A a tid c pl js sr kn L hc lz R M mdl e eo iW weo wlen s ret bs ce ceo cn K E v d cd
           HB Hce Hcd0 Hcd1 Hcd2 Hcd3 Hincl Hc0 Hnd Hsr Hkn HL Hev S10 S11 S12 S1 Hret HiW Hweo Hnw Hwlen Hd0 Hdn
           LEN RDN Hdisj Hs0 Hs1 HK.
    subst E. unfold v in *. clear v. unfold cd in *. clear cd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    set (V := mrestrict H M) in *.
    set (dw := Z_to_bv 64 d). set (sw := Z_to_bv 64 s) in *.
    assert (Ud : bv_unsigned dw = d) by (unfold dw; apply u_small; lia).
    assert (Us : bv_unsigned sw = s) by (unfold sw; apply u_small; lia).
    assert (G10 : getr R 10%bv = dw).
    { rewrite (HR 10%bv), (split_lit_denot PH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) _ _ _ _ S10). reflexivity. }
    assert (G11 : getr R 11%bv = sw) by (rewrite (HR 11%bv); exact S11).
    assert (G12 : getr R 12%bv = Z_to_bv 64 8) by (rewrite (HR 12%bv); exact S12).
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (Hst : store_ok SEGS V dw 8%nat = true).
    { pose proof (kwr_store_ok SEGS _ V kn iW e weo wlen eo 8%nat HKN HiW ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
      rewrite adenot_SA in ST. exact ST. }
    assert (HMC : mcH V dw sw 8 bs).
    { constructor; rewrite ?LEN, ?Ud, ?Us; try lia; [exact RDN | exact Hst]. }
    destruct (musl_memcpy_spec V ROM dw sw 8 bs R (Z_to_bv 64 ret) HMC Hret G1 G10 G11 G12) as (R' & MS & KP).
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh.
    eapply (srz_msteps_A' SEGS H HH wx_nowrap A R (Z_to_bv 64 A_musl_memcpy) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [exact MS | exact HCOV | exact HAW | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (V' := wbytes V dw bs) in *.
    assert (V'out : forall x : word, bv_unsigned x < d \/ d + 8 <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LEN, Ud; lia. }
    assert (VIS : forall x : word, d <= bv_unsigned x < d + 8 -> H x = false).
    { intros x Hx. pose proof (store_ok_all SEGS V 8%nat dw ltac:(rewrite Ud; lia) Hst x ltac:(rewrite Ud; lia)) as W.
      unfold V, wview, mrestrict in W. destruct (H x) eqn:EH; [| reflexivity]. exfalso.
      rewrite (HH x EH) in W. exact (W eq_refl). }
    assert (AG : forall r : reg, ~ In r clob -> getr R' r = getr R r).
    { intros r Hr. assert (Hm : ~ In r memcpy_clob) by (intros X; apply Hr, Hincl, X).
      destruct (bv_eq_dec 5 r 0%bv) as [->|N0]; [reflexivity|].
      (* [comment removed for export] *)
      destruct (bv_eq_dec 5 r 1%bv) as [->|N1]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 2%bv) as [->|N2]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 3%bv) as [->|N3]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 4%bv) as [->|N4]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 8%bv) as [->|N8]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 9%bv) as [->|N9]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 10%bv) as [->|N10]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 18%bv) as [->|N18]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 19%bv) as [->|N19]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 20%bv) as [->|N20]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 21%bv) as [->|N21]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 22%bv) as [->|N22]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 23%bv) as [->|N23]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 24%bv) as [->|N24]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 25%bv) as [->|N25]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 26%bv) as [->|N26]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      destruct (bv_eq_dec 5 r 27%bv) as [->|N27]; [apply KP; unfold callee_kept; cbn [In]; clear; tauto|].
      exfalso. unfold memcpy_clob in Hm. cbn [In] in Hm. pose proof (bv_unsigned_in_range 5 r) as RR. change (bv_modulus 5) with 32 in RR.
      assert (U0 : bv_unsigned r <> 0) by (intros X; apply N0; apply bv_eq; exact X).
      assert (U1 : bv_unsigned r <> 1) by (intros X; apply N1; apply bv_eq; exact X).
      assert (U2 : bv_unsigned r <> 2) by (intros X; apply N2; apply bv_eq; exact X).
      assert (U3 : bv_unsigned r <> 3) by (intros X; apply N3; apply bv_eq; exact X).
      assert (U4 : bv_unsigned r <> 4) by (intros X; apply N4; apply bv_eq; exact X).
      assert (U8 : bv_unsigned r <> 8) by (intros X; apply N8; apply bv_eq; exact X).
      assert (U9 : bv_unsigned r <> 9) by (intros X; apply N9; apply bv_eq; exact X).
      assert (U10 : bv_unsigned r <> 10) by (intros X; apply N10; apply bv_eq; exact X).
      assert (U18 : bv_unsigned r <> 18) by (intros X; apply N18; apply bv_eq; exact X).
      assert (U19 : bv_unsigned r <> 19) by (intros X; apply N19; apply bv_eq; exact X).
      assert (U20 : bv_unsigned r <> 20) by (intros X; apply N20; apply bv_eq; exact X).
      assert (U21 : bv_unsigned r <> 21) by (intros X; apply N21; apply bv_eq; exact X).
      assert (U22 : bv_unsigned r <> 22) by (intros X; apply N22; apply bv_eq; exact X).
      assert (U23 : bv_unsigned r <> 23) by (intros X; apply N23; apply bv_eq; exact X).
      assert (U24 : bv_unsigned r <> 24) by (intros X; apply N24; apply bv_eq; exact X).
      assert (U25 : bv_unsigned r <> 25) by (intros X; apply N25; apply bv_eq; exact X).
      assert (U26 : bv_unsigned r <> 26) by (intros X; apply N26; apply bv_eq; exact X).
      assert (U27 : bv_unsigned r <> 27) by (intros X; apply N27; apply bv_eq; exact X).
      assert (U5 : bv_unsigned r <> 5) by (intros X; apply Hm; do 0 right; left; apply bv_eq; symmetry; exact X).
      assert (U6 : bv_unsigned r <> 6) by (intros X; apply Hm; do 1 right; left; apply bv_eq; symmetry; exact X).
      assert (U7 : bv_unsigned r <> 7) by (intros X; apply Hm; do 2 right; left; apply bv_eq; symmetry; exact X).
      assert (U11 : bv_unsigned r <> 11) by (intros X; apply Hm; do 3 right; left; apply bv_eq; symmetry; exact X).
      assert (U12 : bv_unsigned r <> 12) by (intros X; apply Hm; do 4 right; left; apply bv_eq; symmetry; exact X).
      assert (U13 : bv_unsigned r <> 13) by (intros X; apply Hm; do 5 right; left; apply bv_eq; symmetry; exact X).
      assert (U14 : bv_unsigned r <> 14) by (intros X; apply Hm; do 6 right; left; apply bv_eq; symmetry; exact X).
      assert (U15 : bv_unsigned r <> 15) by (intros X; apply Hm; do 7 right; left; apply bv_eq; symmetry; exact X).
      assert (U16 : bv_unsigned r <> 16) by (intros X; apply Hm; do 8 right; left; apply bv_eq; symmetry; exact X).
      assert (U17 : bv_unsigned r <> 17) by (intros X; apply Hm; do 9 right; left; apply bv_eq; symmetry; exact X).
      assert (U28 : bv_unsigned r <> 28) by (intros X; apply Hm; do 10 right; left; apply bv_eq; symmetry; exact X).
      assert (U29 : bv_unsigned r <> 29) by (intros X; apply Hm; do 11 right; left; apply bv_eq; symmetry; exact X).
      assert (U30 : bv_unsigned r <> 30) by (intros X; apply Hm; do 12 right; left; apply bv_eq; symmetry; exact X).
      assert (U31 : bv_unsigned r <> 31) by (intros X; apply Hm; do 13 right; left; apply bv_eq; symmetry; exact X).
      lia. }
    set (w := le_bytes_to_word bs) in *.
    assert (VBapp : VB sp draw inp a tid c pl (js ++ [w]) = VB sp draw inp a tid c pl js ++ [w]) by (unfold VB; rewrite <- !app_assoc; reflexivity).
    assert (LENw : length (VB sp draw inp a tid c pl (js ++ [w])) = Datatypes.S (length (VB sp draw inp a tid c pl js))).
    { rewrite VBapp, length_app. cbn [length]. lia. }
    assert (Hsr1 : sr_vars_lt (length (VB sp draw inp a tid c pl (js ++ [w]))) sr = true).
    { rewrite LENw. apply (sr_vars_lt_weaken (length (VB sp draw inp a tid c pl js))); [lia | exact Hsr]. }
    assert (AGR : env_agree (length (VB sp draw inp a tid c pl js)) (EB sp draw inp a tid c pl js) (Env (vals_ev (VB sp draw inp a tid c pl js ++ [w])) (blobs0 draw (in_argv inp)))).
    { unfold EB. apply vals_app_agree. }
    apply HK; [constructor |].
    13:{ intros x Hx. destruct (H x) eqn:EH; [rewrite (munrestrict_hidden _ _ _ _ EH); reflexivity|].
         rewrite (munrestrict_visible _ _ _ _ EH), V'out by exact Hx. unfold V. rewrite (mrestrict_visible' _ _ _ EH). reflexivity. }
    - (* [comment removed for export] *)
      rewrite EB_app, <- LENw. apply (regs_after_clob clob (VB sp draw inp a tid c pl (js ++ [w])) (blobs0 draw (in_argv inp)) sr R R' Hsr1).
      + rewrite VBapp. apply env_app_regs; [exact Hsr | exact HR].
      + exact AG.
      + exact Hc0.
      + exact Hnd.
    - (* [comment removed for export] *)
      rewrite EQV. rewrite EB_app. apply env_app_know.
      { rewrite LENw. cbn [kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb].
        rewrite (expr_vars_lt_weaken (length (VB sp draw inp a tid c pl js))) by (lia || exact Hev). cbn [andb].
        rewrite (proj2 (Nat.ltb_lt _ _)) by lia. cbn [andb].
        unfold kn_keep. apply kn_vars_lt_filter. apply kn_vars_lt_skipn. apply (kn_vars_lt_weaken (length (VB sp draw inp a tid c pl js))); [lia | exact Hkn]. }
      rewrite VBapp. constructor.
      + cbn [kentry_ok]. split; [lia|].
        assert (Ee : edenot (Env (vals_ev (VB sp draw inp a tid c pl js ++ [w])) (blobs0 draw (in_argv inp))) e = edenot (EB sp draw inp a tid c pl js) e).
        { symmetry. apply (edenot_agree (length (VB sp draw inp a tid c pl js))); [exact AGR | exact Hev]. }
        assert (Ew : edenot (Env (vals_ev (VB sp draw inp a tid c pl js ++ [w])) (blobs0 draw (in_argv inp))) (EVar (length (VB sp draw inp a tid c pl js))) = w).
        { cbn [edenot ev]. replace (length (VB sp draw inp a tid c pl js)) with (length (VB sp draw inp a tid c pl js) + 0)%nat by lia. rewrite vals_ev_app_r. reflexivity. }
        unfold flat, estart, elenZ. rewrite adenot_SA. cbn [a_base a_off]. rewrite Ee, Ew. fold d.
        split; [lia|]. unfold V'. fold dw. replace (word_to_le_bytes 8 w) with bs by (unfold w; symmetry; exact (wleb8_lez bs LEN)).
        rewrite <- LEN. apply rdn_wbytes_hit. rewrite LEN, Ud. lia.
      + apply (kn_keep_sound SEGS _ V V' MGrow).
        * apply know_ok_skipn. apply (know_ok_agree SEGS _ _ _ _ _ AGR); [| exact HKN]. exact Hkn.
        * apply know_ok_skipn. apply (know_ok_agree SEGS _ _ _ _ _ AGR); [| exact HKN]. exact Hkn.
        * unfold estart, elenZ. cbn [a_base a_off edenot].
          rewrite <- (edenot_agree (length (VB sp draw inp a tid c pl js)) _ _ ce AGR Hce). rewrite u_small by lia.
          apply (mem_change_grow_mono V V' d 8); [| lia | lia].
          rewrite <- Ud. replace 8 with (Z.of_nat (length bs)) by (rewrite LEN; reflexivity). unfold V'. apply mem_change_wbytes.
          rewrite LEN, Ud. lia.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hvx : H x = false) by (apply Habv; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hvx), V'out by (unfold usp in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hvx). apply HA. exact Hx.
    - (* [comment removed for export] *)
      unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh2).
    - rewrite (sbm_lazy _ _ HS'). exact HLZ.
    - exact HM'.
    - rewrite <- app_assoc. apply mfacts_env; [exact HL|]. eapply mfacts_sbm; [exact F | exact HS'].
    - rewrite <- app_assoc. apply maps_ok_env; [exact HL | exact HMO].
    - rewrite <- app_assoc. apply regime_ok_env; [exact HL|]. eapply regime_ok_sbm; [exact RG | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
End Theorems15.
End TwB.
