(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge Arr Bytes Mem Frame.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit Stdio_kit AHarness_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).
Notation gshA := harness_invA.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
Definition AFI_LTOI : Z := 0x7fc34.      (* [comment removed for export] *)
Definition AFI_ISFRAME : Z := 0x7fefc.   (* [comment removed for export] *)
Definition AFI_FHSIZE : Z := 0x7ffdc.    (* [comment removed for export] *)
Definition AFI_GFHA : Z := 0x800d8.      (* [comment removed for export] *)
Definition AFI_GFH : Z := 0x80bf4.       (* [comment removed for export] *)
Definition AFI_GFCS : Z := 0x80bfc.      (* [comment removed for export] *)
Definition AFI_FDS : Z := 0x80e38.       (* [comment removed for export] *)
Definition AFI_FFCS : Z := 0x812c8.      (* [comment removed for export] *)
Definition AFI_GDS : Z := 0x812f4.       (* [comment removed for export] *)
Definition AFI_DBOUND : Z := 0x81570.    (* [comment removed for export] *)
Definition AFI_FFSI : Z := 0x81628.      (* [comment removed for export] *)
Definition AFI_GDID : Z := 0x81cfc.      (* [comment removed for export] *)
Definition AFI_RSKIP : Z := 0x81f68.     (* [comment removed for export] *)
Definition AFI_DIDTAB : Z := 0x20d40.    (* [comment removed for export] *)
Definition AFI_FCSTAB : Z := 0x20d80.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFI_SM0 : Z := 0x3c5b4.       (* [comment removed for export] *)
Definition AFI_SM1 : Z := 0x3c728.       (* [comment removed for export] *)
Definition AFI_SM2 : Z := 0x3c8b8.       (* [comment removed for export] *)
Definition AFI_AMEMSET : Z := 0x5121c.   (* [comment removed for export] *)
Definition AFI_AMEMCPY : Z := 0x50d80.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFI_STACK : Z := 8192.
End CANSEC0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fake_lek (c : Z) (k : nat) (LB : list ablock) : Prop :=
  forall l : list Z, List.NoDup l -> (forall F, In F l -> exists n, In (mkABlock (ABFake c) F n) LB) -> (length l <= k)%nat.

Lemma fake_lek_none : forall c LB, (forall F n, ~ In (mkABlock (ABFake c) F n) LB) -> fake_lek c 0 LB.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=19078766453.5000001S".
intros c LB H [|F l] ND HL; [cbn; lia|]. exfalso. destruct (HL F ltac:(left; reflexivity)) as [n Hn]. exact (H F n Hn).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma fake_lek_nil : forall c k, fake_lek c k [].
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=67875639432.4000001S".
intros c k [|F l] ND HL; [cbn; lia|]. exfalso. destruct (HL F ltac:(left; reflexivity)) as [n Hn]. exact Hn. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma fake_lek_zero_not_in : forall c LB F n, fake_lek c 0 LB -> ~ In (mkABlock (ABFake c) F n) LB.
Proof.
  intros c LB F n H Hin. specialize (H [F] ltac:(constructor; [intros []| constructor]) ltac:(intros F' [<-|[]]; exists n; exact Hin)).
  cbn in H. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59310683405.6000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma fake_lek_mono : forall c k k' LB, (k <= k')%nat -> fake_lek c k LB -> fake_lek c k' LB.
Proof. intros c k k' LB Hk H l ND HL. specialize (H l ND HL). Local Ltac2 Set LiaHints.tbl := fun () => "0010=57810780461.9000006S2Hk1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma fake_lek_incl : forall c k LB LB',
  (forall F n, In (mkABlock (ABFake c) F n) LB' -> In (mkABlock (ABFake c) F n) LB) -> fake_lek c k LB -> fake_lek c k LB'.
Proof.
  intros c k LB LB' I H l ND HL. apply H; [exact ND|]. intros F HF. destruct (HL F HF) as [n Hn]. exists n. apply I. exact Hn.
Qed.

(* [comment removed for export] *)
Lemma fake_lek_push : forall c k b LB, (forall F n, b <> mkABlock (ABFake c) F n) -> fake_lek c k LB -> fake_lek c k (b :: LB).
Proof.
  intros c k b LB NB H. eapply fake_lek_incl; [| exact H]. intros F n [E|Hin]; [exfalso; exact (NB F n E)| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma fake_lek_pop : forall c k b LB, fake_lek c k (b :: LB) -> fake_lek c k LB.
Proof. intros c k b LB H. eapply fake_lek_incl; [| exact H]. intros F n Hin. right. exact Hin. Qed.

(* [comment removed for export] *)
Lemma fake_lek_pushc : forall c k F n LB, fake_lek c k LB -> fake_lek c (S k) (mkABlock (ABFake c) F n :: LB).
Proof.
  intros c k F n LB H l ND HL.
  assert (REST : forall l', List.NoDup l' -> ~ In F l' -> (forall x, In x l' -> In x l) -> (length l' <= k)%nat).
  { intros l' ND' NI SUB. apply H; [exact ND'|]. intros x Hx. destruct (HL x (SUB x Hx)) as [n' [E|Hin]].
    - exfalso. injection E as E _. apply NI. rewrite E. exact Hx.
    - exists n'. exact Hin. }
  destruct (in_dec Z.eq_dec F l) as [IN|NI].
  - destruct (in_split F l IN) as (l1 & l2 & ->).
    pose proof (NoDup_remove_1 l1 l2 F ND) as ND'. pose proof (NoDup_remove_2 l1 l2 F ND) as NI'.
    assert (LEN : (length (l1 ++ l2) <= k)%nat).
    { apply REST; [exact ND'| exact NI'|]. intros x Hx. apply in_app_iff in Hx. apply in_app_iff. cbn. tauto. }
    rewrite length_app in LEN |- *. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0020>44024253450.1261559098065.15000004009S2H0S3LEN".
lia.
  - pose proof (REST l ND NI (fun x Hx => Hx)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma fake_lek_pigeon : forall c k LB (fr : nat -> Z),
  fake_lek c k LB ->
  (forall i j, (i < S k)%nat -> (j < S k)%nat -> fr i = fr j -> i = j) ->
  (forall i, (i < S k)%nat -> exists n, In (mkABlock (ABFake c) (fr i) n) LB) -> False.
Proof.
  intros c k LB fr H INJ ALL.
  assert (ND : List.NoDup (map fr (seq 0 (S k)))).
  { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx, Hy. Local Ltac2 Set LiaHints.tbl := fun () => "0040>29379869476.1239909381336.1041520647615.1259310613357.1000000700;00B00GS2Hx2HyS2HiS2Hx2HyS3LEN".
apply INJ; [lia| lia| exact E]. }
  assert (HL : forall F, In F (map fr (seq 0 (S k))) -> exists n, In (mkABlock (ABFake c) F n) LB).
  { intros F HF. apply in_map_iff in HF. destruct HF as (i & <- & Hi). apply in_seq in Hi. apply ALL. lia. }
  pose proof (H _ ND HL) as LEN. rewrite length_map, length_seq in LEN. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition buf_atA (m : amem) (S : Z) (bl : list Z) : Prop :=
  bytes_at bsegs m S (map (Z_to_bv 8) bl) /\ Forall (fun c => 0 <= c < 256) bl.

(* [comment removed for export] *)
Definition Znth (i : Z) (l : list Z) : Z := nth (Z.to_nat i) l 0.

#[using="Type"] Lemma buf_atA_bound : forall m S bl, buf_atA m S bl -> 0 <= S /\ S + zlen bl <= 2^64.
Proof. intros m S bl [B _]. pose proof (bytes_at_bound _ _ _ _ B) as H. rewrite length_map in H. exact H. Qed.

#[using="Type"] Lemma buf_nthA : forall m S bl i, buf_atA m S bl -> 0 <= i < zlen bl ->
  nth_error (map (Z_to_bv 8) bl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i bl)) /\ 0 <= Znth i bl < 256.
Proof.
  intros m S bl i [_ F] Hi. unfold Znth.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<2322167807.7000004S2Hi".
assert (L : (Z.to_nat i < length bl)%nat) by lia.
  split.
  - rewrite nth_error_map. rewrite (nth_error_nth' bl 0 L). reflexivity.
  - apply (proj1 (Forall_forall _ _) F). apply nth_In. exact L.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma buf_readA : forall m S bl i, buf_atA m S bl -> 0 <= i < zlen bl ->
  ov_read_bytes bsegs m (wa (S + i)) 1 = Some [Z_to_bv 8 (Znth i bl)].
Proof.
  intros m S bl i B Hi. destruct (buf_nthA m S bl i B Hi) as [N _].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=10357916367.8000004S2Hi".
eapply (u8ro_read bsegs m S _ i); [exact (proj1 B)| exact N| lia| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma byte_litA : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48041415315.3000004S2Hc".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma buf_atA_frame : forall m m' S bl W,
  buf_atA m S bl -> munch W m m' -> disjoint_from W S (zlen bl) -> buf_atA m' S bl.
Proof.
  intros m m' S bl W [B F] MU HW. split; [|exact F].
  eapply (bytes_at_transport bsegs W m m'); [exact B| exact MU|]. rewrite length_map. exact HW.
Qed.

(* [comment removed for export] *)
Definition hcoverA (LB : list ablock) (S n : Z) : Prop :=
  n = 0 \/ exists p D N, In (mkABlock (ABHeap p) D N) LB /\ D <= S /\ S + n <= D + N.

#[using="Type"] Lemma hcoverA_sub : forall LB S n S' n', hcoverA LB S n -> S <= S' -> 0 <= n' -> S' + n' <= S + n -> hcoverA LB S' n'.
Proof.
  intros LB S n S' n' [->|(p & D & N & Hin & H1 & H2)] L1 L2 L3.
  - left. Local Ltac2 Set LiaHints.tbl := fun () => "0020>61704771158.169261757346.8  00000=00GS2H12H22L12L3S2L12L22L3".
lia.
  - destruct (Z.eq_dec n' 0) as [->|NZ]; [left; reflexivity|]. right. exists p, D, N. split; [exact Hin| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma hcoverA_cons_fake : forall c F fn LB S n, hcoverA LB S n -> hcoverA (mkABlock (ABFake c) F fn :: LB) S n.
Proof. intros c F fn LB S n [->|(p & D & N & Hin & H)]; [left; reflexivity| right]. exists p, D, N. split; [right; exact Hin| exact H]. Qed.

#[using="Type"] Lemma hcoverA_tail : forall c F fn LB S n, hcoverA (mkABlock (ABFake c) F fn :: LB) S n -> hcoverA LB S n.
Proof.
  intros c F fn LB S n [->|(p & D & N & [E|Hin] & H)]; [left; reflexivity| discriminate E| right]. exists p, D, N. split; [exact Hin| exact H].
Qed.

(* [comment removed for export] *)
Definition fcellA (m : amem) (LB : list ablock) (C k : Z) : Prop :=
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= C /\ C + k <= FA + FN /\ ablk FA (FA + FN) /\ FA mod 8 = 0)
  /\ unpoisoned m C (C + k).

(* [comment removed for export] *)
Definition shullA (RNG : footprint) (m : amem) (LB : list ablock) (A n : Z) : Prop :=
  exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= A /\ A + n <= FA + FN
    /\ FA mod 64 = 0 /\ FN mod 64 = 0 /\ 0 <= FA /\ FA + FN <= KEND
    /\ wr_at bsegs m (shad FA) (FN / 8) /\ rng RNG (shad FA) (FN / 8).

#[using="Type"] Lemma fcellA_cons : forall m LB b C k, fcellA m LB C k -> fcellA m (b :: LB) C k.
Proof. intros m LB b C k [(cls & FA & FN & Hin & H) U]. split; [| exact U]. exists cls, FA, FN. split; [right; exact Hin| exact H]. Qed.
#[using="Type"] Lemma shullA_cons : forall RNG m LB b A n, shullA RNG m LB A n -> shullA RNG m (b :: LB) A n.
Proof. intros RNG m LB b A n (cls & FA & FN & Hin & H). exists cls, FA, FN. split; [right; exact Hin| exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gshA_bytes : forall m, gshA m ->
  forall i, (i < 16)%nat -> m (wa (GSH_ADDR + Z.of_nat i)) = nth_error GSH_BYTES i.
Proof.
  intros m [[_ B] _] i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=10093995185.729978203842.847803118162.800000400:00@S2HiS2Hi1LS2Hi1L".
assert (L : (i < length GSH_BYTES)%nat) by (cbn; lia).
  specialize (B i L). rewrite ref_mrd_overlay in B; [exact B| right; unfold GSH_ADDR; rewrite wa_unsigned; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma gshA_zero : forall m a, gshA m -> (0x7fffc1a8 <= a < 0x7fffc1ac \/ 0x7fffc1b0 <= a < 0x7fffc1b4) -> m (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros m a G Ha.
  assert (E : exists i, (i < 16)%nat /\ a = GSH_ADDR + Z.of_nat i /\ nth_error GSH_BYTES i = Some (Z_to_bv 8 0)).
  { unfold GSH_ADDR. destruct Ha as [Ha|Ha].
    - exists (Z.to_nat (a - 0x7fffc1a8)). Local Ltac2 Set LiaHints.tbl := fun () => "0040=22341924691.546849911824.552394040975.556806186677.500000400800<00@S2HaS2HaS2HaS2Ha".
split; [lia|]. split; [lia|].
      assert (C : (Z.to_nat (a - 0x7fffc1a8) = 0 \/ Z.to_nat (a - 0x7fffc1a8) = 1 \/ Z.to_nat (a - 0x7fffc1a8) = 2 \/ Z.to_nat (a - 0x7fffc1a8) = 3)%nat) by lia.
      destruct C as [->|[->|[->| ->]]]; reflexivity.
    - exists (Z.to_nat (a - 0x7fffc1a8)). split; [lia|]. split; [lia|].
      assert (C : (Z.to_nat (a - 0x7fffc1a8) = 8 \/ Z.to_nat (a - 0x7fffc1a8) = 9 \/ Z.to_nat (a - 0x7fffc1a8) = 10 \/ Z.to_nat (a - 0x7fffc1a8) = 11)%nat) by lia.
      destruct C as [->|[->|[->| ->]]]; reflexivity. }
  destruct E as (i & Hi & -> & N). rewrite (gshA_bytes m G i Hi). exact N.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma gshA_mg : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, 0x7fffc1a8 <= a < 0x7fffc1b8 -> P a) -> gshA m -> gshA m'.
Proof.
  intros P m m' AG HP G. unfold harness_invA, GSH_ADDR in *. eapply rw_cells_magree; [exact AG| exact G|].
  intros a Ha. apply HP. cbn [cells_size csize Nat.add] in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41390299504.9000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma gsh_client : forall CI LB SP a, In (0x20d40, 0x20dc0)%Z CI -> 0x7fffc1a8 <= a < 0x7fffc1b8 -> aclient_addr CI LB SP a.
Proof.
  intros CI LB SP a HIN Ha. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
  right; left. exists (0x20d40, 0x20dc0)%Z. split; [exact HIN|]. cbn [fst snd]. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0010<8269956784.7000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.        (* [comment removed for export] *)
Variable rng_fs : alayout -> footprint -> Prop.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fake_flag_law : Prop :=
  forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Definition fake_release_law : Prop :=
  forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

(* [comment removed for export] *)
Definition sm_post (c SZ : Z) (NSH : nat) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (mkABlock (ABFake c) F SZ :: LB) m'
    /\ F mod SZ = 0 /\ ablk F (F + SZ) /\ F + SZ <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (SZ - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))]
    /\ rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) NSH)
    /\ rng RNG F SZ /\ rng RNG (shad F) (SZ / 8).

Definition sm_stmtk (c SZ : Z) (NSH : nat) (ENTRY : Z) (k : nat) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  fake_lek c k LB ->                                        (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4096 ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm_post c SZ NSH L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition stack_malloc_0_stmtk (k : nat) : Prop := sm_stmtk 0 64 1 AFI_SM0 k.     (* [comment removed for export] *)
Definition stack_malloc_1_stmtk (k : nat) : Prop := sm_stmtk 1 128 2 AFI_SM1 k.    (* [comment removed for export] *)
Definition stack_malloc_2_stmtk (k : nat) : Prop := sm_stmtk 2 256 4 AFI_SM2 k.    (* [comment removed for export] *)

#[using="Type"] Lemma sm_stmtk_mono : forall c SZ NSH E k k', (k' <= k)%nat -> sm_stmtk c SZ NSH E k -> sm_stmtk c SZ NSH E k'.
Proof.
  intros c SZ NSH E k k' Hk H. unfold sm_stmtk. intros until lo. intros AH LE MI ST B1 B2 SPT TP R1 R2 R3.
  eapply H; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. eapply fake_lek_mono; [exact Hk| exact LE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ltoiA_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' =>
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ frm0 fc'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG st LB m'
      /\ harness_invA m'.

Definition ltoiA_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
    AHEAP AI L RNG st LB m ->
    (forall b, In b LB -> exists p A n, b = HB p A n) ->                 (* [comment removed for export] *)
    payload_atA LB D payload ->                                          (* [comment removed for export] *)
    bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
    D mod 16 = 0 -> zlength payload < 2^26 ->
    harness_invA m ->                                                    (* [comment removed for export] *)
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
    bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    s0 = Z_to_bv 64 (zlength payload) ->
    mem_inv bsegs m -> frm0 fc ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    evtF bsegs RNG (ltoiA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
#[using="Type"] Lemma fuzz_oneA_of_ltoiA : ltoiA_stmt -> fuzz_oneA_stmt AI rng_fs.
Proof.
  intros LTOI. unfold fuzz_oneA_stmt. intros until rstk.
  intros AH LBH PAY PB PR D16 SZ HINV ST LO1 LO2 DEPTH SP16 RC R1 R2 R3 S0 MI FC TP A0 A1 RA HUL RS RI RIS RFS RR APS.
  unfold fuzz_oneA, Harness.fuzz_one. cbv zeta. apply implMA_ret.
  eapply evtF_mono.
  { eapply (LTOI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (aps_m s) LB D payload lo rstk);
      eassumption. }
  cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & E & MI' & FC' & ST' & HP & SSP & AH' & GI').
  unfold fuzz_oneA_post. split; [apply fp_le_refl|].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'.
  split; [exact E|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010?61482382924.105000001S".
split; [lia|]. split; [exact MI'|]. split; [exact FC'|]. split; [exact ST'|]. split; [exact HP|]. split; [exact SSP|].
  split; [exact AH'|]. split; [exact GI'| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Stmts.
End CANSEC1.
