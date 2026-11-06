From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB KindB.
Import ListNotations.
Local Open Scope Z_scope.

Lemma wvm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma wvm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma find_segment_below : forall segs bot a n,
  forallb (fun s => bot <=? Z.of_N (seg_base s)) segs = true ->
  a + n <= bot -> 0 < n -> find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros bot a n H Ha Hn; cbn; [reflexivity|].
  cbn in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  destruct ((Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. lia.
  - exact (IH bot a n H2 Ha Hn).
Qed.

Lemma rsegs_bot : forallb (fun s => 0x10000 <=? Z.of_N (seg_base s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_none : forall x, 0 <= x -> (x < 0x10000 \/ 0x51000 <= x) -> find_segment rsegs x 1 = None.
Proof.
  intros x H0 [H|H].
  - apply (find_segment_below rsegs 0x10000); [exact rsegs_bot | lia | lia].
  - apply (find_segment_above rsegs 0x51000); [exact rsegs_top | lia | lia].
Qed.

Lemma rsegs_reserved :
  map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) =
  [(0x10000, 0x2000); (0x12000, 0xc000); (0x1e000, 0x1000); (0x1f000, 0x32000)].
Proof. vm_compute. reflexivity. Qed.

Lemma reserved_in : forall lo len, In (lo, len) [(0x10000, 0x2000); (0x12000, 0xc000); (0x1e000, 0x1000); (0x1f000, 0x32000)] ->
  exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) = lo /\ bv_unsigned (snd s) = len.
Proof.
  intros lo len H. rewrite <- rsegs_reserved in H. apply in_map_iff in H as (s & E & Hs).
  exists s. inversion E. auto.
Qed.

Lemma writable_off_present : forall m x, 0 <= x < 2 ^ 64 -> (x < 0x10000 \/ 0x51000 <= x) ->
  writable_at rsegs m x -> present m x.
Proof.
  intros m x Hx Hr Hw. unfold writable_at, wview in Hw. unfold present.
  destruct (m (Z_to_bv 64 x)) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply Hw.
  rewrite (Z_to_bv_unsigned 64 x). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. rewrite (rsegs_none x) by lia. reflexivity.
Qed.

Lemma present_mrd : forall (segs : list Segment) m x, present m x -> exists b, mrd segs m (wa x) = Some b.
Proof. intros segs m x (b & Hb). exists b. unfold mrd, wa. rewrite Hb. reflexivity. Qed.

Lemma present_bytes : forall (segs : list Segment) m D (n : nat), 0 <= D -> D + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present m (D + i)) ->
  exists bs, length bs = n /\ bytes_at segs m D bs.
Proof.
  intros segs m D n HD Hb HP. revert D HD Hb HP. induction n as [|n IH]; intros D HD Hb HP.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - destruct (present_mrd segs m D) as (b & Eb); [replace D with (D + 0) by lia; apply HP; lia|].
    destruct (IH (D + 1)) as (bs & Hl & Hbs); [lia | lia | intros i Hi; replace (D + 1 + i) with (D + (1 + i)) by lia; apply HP; lia|].
    exists (b :: bs). split; [cbn; lia|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn. rewrite Z.add_0_r. exact Eb.
    + cbn [length]. exact Hbs.
Qed.

Lemma present_rw_cells : forall m D n, 0 <= D -> 0 <= n -> D + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> present m (D + i)) ->
  exists junk, rw_cells rsegs m D [CB (Z.to_nat n) junk].
Proof.
  intros m D n HD Hn Hb HP.
  destruct (present_bytes rsegs m D (Z.to_nat n) HD ltac:(lia) ltac:(intros i Hi; apply HP; lia)) as (bs & Hl & Hbs).
  exists bs. split; [split|].
  - cbn. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hbs.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (HP i ltac:(lia)) as (b & E). unfold wview, wa. rewrite E. discriminate.
Qed.

Lemma wview_empty : forall m a, wview rsegs (fun _ => None) a <> None -> wview rsegs m a <> None.
Proof. intros m a H. unfold wview in *. destruct (m a); [discriminate | exact H]. Qed.

Lemma guard_wr : forall m, wr_at rsegs m 0x1e368 8 /\ wr_at rsegs m 0x4f978 8.
Proof.
  intros m. split; (split; [lia|]; split; [lia|]); intros i Hi; apply wview_empty;
    assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
    destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma pairwise_app : forall {T} (R : T -> T -> Prop) l1 l2, pairwise R (l1 ++ l2) ->
  pairwise R l1 /\ pairwise R l2 /\ forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros T R l1. induction l1 as [|z l1 IH]; intros l2 H; cbn in *.
  - split; [exact I|]. split; [exact H|]. intros x y [].
  - destruct H as [H1 H2]. destruct (IH l2 H2) as (P1 & P2 & P3).
    split; [split; [intros y Hy; apply H1; apply in_or_app; left; exact Hy | exact P1]|].
    split; [exact P2|]. intros x y [<-|Hx] Hy; [apply H1; apply in_or_app; right; exact Hy | exact (P3 x y Hx Hy)].
Qed.

Lemma rd_sym : forall x y, ranges_disjoint x y -> ranges_disjoint y x.
Proof. intros [a b] [c d]. unfold ranges_disjoint. cbn. lia. Qed.

Lemma pairwise_mid : forall b1 c b2, pairwise ranges_disjoint (b1 ++ c ++ b2) ->
  forall x y, In x (b1 ++ b2) -> In y c -> ranges_disjoint x y.
Proof.
  intros b1 c b2 H x y Hx Hy.
  destruct (pairwise_app _ b1 (c ++ b2) H) as (_ & P2 & P3).
  destruct (pairwise_app _ c b2 P2) as (_ & _ & Q3).
  apply in_app_or in Hx as [Hx|Hx].
  - apply P3; [exact Hx | apply in_or_app; left; exact Hy].
  - apply rd_sym. apply Q3; [exact Hy | exact Hx].
Qed.

Lemma app_cons_unique : forall {T} (b1 b2 c1 c2 : list T) (y : T),
  ~ In y b1 -> ~ In y c1 -> b1 ++ y :: b2 = c1 ++ y :: c2 -> b1 = c1 /\ b2 = c2.
Proof.
  intros T b1. induction b1 as [|x b1 IH]; intros b2 c1 c2 y H1 H2 E; destruct c1 as [|z c1]; cbn in *.
  - inversion E. auto.
  - inversion E; subst. exfalso. apply H2. left. reflexivity.
  - inversion E; subst. exfalso. apply H1. left. reflexivity.
  - injection E as Exz E'. subst z. destruct (IH b2 c1 c2 y ltac:(tauto) ltac:(tauto) E') as [-> ->]. auto.
Qed.

Lemma pairwise_notin : forall b1 b2 (y : Z * Z), pairwise ranges_disjoint (b1 ++ y :: b2) -> 0 < snd y ->
  ~ In y b1 /\ ~ In y b2.
Proof.
  intros b1 b2 y H Hy.
  destruct (pairwise_app _ b1 (y :: b2) H) as (_ & P2 & P3).
  split.
  - intros Hin. pose proof (P3 y y Hin (or_introl eq_refl)) as D. destruct y as [a k]. unfold ranges_disjoint in D. cbn in *. lia.
  - intros Hin. destruct P2 as [Q _]. pose proof (Q y Hin) as D. destruct y as [a k]. unfold ranges_disjoint in D. cbn in *. lia.
Qed.
