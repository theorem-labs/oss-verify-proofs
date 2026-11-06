(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts.
Import ListNotations.
Open Scope Z_scope.

Definition A0_malloc : Z := 0x58630.
Definition A0_free : Z := 0x5862c.
Definition A0_realloc : Z := 0x58634.

Notation PC0_MALLOC := 362704%Z.
Notation PC0_FREE := 362352%Z.
Notation PC0_REALLOC := 363372%Z.

Notation A0_TP := 6187376%Z.

Definition block_shadow (n : Z) : list Z :=
  repeat 0 (Z.to_nat (n / 8)) ++ (if n mod 8 =? 0 then [] else [n mod 8]).

Definition a0_rzlog (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition a0_need (n : Z) : Z := ((Z.max n 8 + 7) / 8) * 8 + Z.shiftl 16 (a0_rzlog n).
Definition a0_csz (c : Z) : Z :=
  if c =? 31 then 64
  else if c <=? 16 then 32 * c
  else let c' := c - 16 in let t := Z.shiftl 512 (Z.shiftr c' 1) in t + (Z.shiftr t 1) * (Z.land c' 1).
Definition a0_class_of (size : Z) : Z :=
  if size <=? 512 then (size + 31) / 32
  else let l := Z.log2 size in
       Z.lor (2 * l) (Z.land (Z.shiftr size (l - 1)) 1) + Z.b2z (0 <? Z.land size (2 ^ (l - 1) - 1)) - 2.
Definition a0_cls (n : Z) : Z := if a0_need n <=? 65536 then a0_class_of (a0_need n) else 0.

Definition a0_nmin (c : Z) : Z :=
  nth (Z.to_nat c) [64513; 1; 17; 49; 65; 97; 97; 129; 161; 193; 225; 257; 289; 321; 353; 385; 417; 449; 641; 897; 1409; 1921; 2945;
                    3969; 5889; 7937; 12033; 16129; 24065; 32257; 48129; 1] 1.
Example a0_cls_samples : map a0_cls [0; 1; 16; 17; 24; 48; 49; 88; 96; 97; 4096; 7936; 64512; 64513; 65536; 1073741824]
                       = [1; 1; 1; 2; 2; 2; 3; 4; 4; 6; 23; 24; 30; 0; 0; 0].
Proof. reflexivity. Qed.
Example a0_csz_samples : map a0_csz [1; 2; 4; 16; 17; 18; 24; 30] = [32; 64; 128; 512; 768; 1024; 8192; 65536].
Proof. reflexivity. Qed.

Definition A0_MAXREQ : Z := 2^28.

Definition A0_QB : Z := 2^28 + 2^20.

Definition A0_CAP (c : Z) : Z :=
  if c <=? 4 then 0xe0000000 - 2 * 0x40000 - a0_csz c * (A0_QB / (a0_nmin c + 8) + 32)
  else if (6 <=? c) && (c <=? 8) then 2^31
  else 2^30.

Definition A0_SEC_CNT : Z := 2^14.
Definition A0_SEC_BYTES : Z := 2^31.
Definition A0_NSEC_MAX : Z := 54300000.
Example A0_CAP_samples : map (fun c => A0_CAP c / a0_csz c) [1; 2; 3; 4; 6; 24; 30] = [87481426; 47932671; 34413554; 25664438; 11184810; 131072; 16384].
Proof. reflexivity. Qed.

Fixpoint a0_chk (f : Z -> bool) (k : nat) (s : Z) : bool :=
  match k with O => true | S k' => f s && a0_chk f k' (s + 1) end.
Lemma a0_chk_ok : forall f k s0, a0_chk f k s0 = true -> forall s, s0 <= s < s0 + Z.of_nat k -> f s = true.
Proof.
  intros f k. induction k as [|k IH]; intros s0 HK s Hs; [lia|]. cbn [a0_chk] in HK. apply andb_true_iff in HK as [H1 H2].
  destruct (Z.eq_dec s s0) as [->|NE]; [exact H1|]. apply (IH (s0 + 1) H2). lia.
Qed.
Lemma a0_class_of_range : forall s, 1 <= s <= 65536 -> 1 <= a0_class_of s <= 30.
Proof.
  intros s Hs.
  pose proof (a0_chk_ok (fun s => (1 <=? a0_class_of s) && (a0_class_of s <=? 30)) (Z.to_nat 65536) 1 ltac:(vm_compute; reflexivity) s ltac:(lia)) as X.
  cbv beta in X. apply andb_true_iff in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Lemma a0_cls_range : forall n, 0 <= n -> 0 <= a0_cls n <= 30.
Proof.
  intros n Hn. unfold a0_cls. destruct (a0_need n <=? 65536) eqn:E; [| lia]. apply Z.leb_le in E.
  assert (1 <= a0_need n).
  { unfold a0_need. assert (8 <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia).
    assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia). lia. }
  pose proof (a0_class_of_range (a0_need n) ltac:(lia)). lia.
Qed.
Lemma a0_caps_ok : forall c, 0 <= c <= 31 -> 0 <= a0_csz c /\ (2^13 + 1) * a0_csz c <= A0_CAP c.
Proof.
  intros c Hc.
  pose proof (a0_chk_ok (fun c => (0 <=? a0_csz c) && ((2^13 + 1) * a0_csz c <=? A0_CAP c)) (Z.to_nat 32) 0 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X.
  cbv beta in X. apply andb_true_iff in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Section A.
Context {HC : HasCeiling}.
Variable FI : fs_if.

Definition rd64 (m : mem) (a : Z) (v : Z) : Prop := bytes_at asegs m a (le8 (Z_to_bv 64 v)) /\ 0 <= v < 2^64.
Definition valid_frame (top bottom a : Z) : Prop := bottom < a /\ a < top - 16 /\ a mod 8 = 0.
Fixpoint fpchain (m : mem) (top bottom a : Z) (ras : list Z) {struct ras} : Prop :=
  match ras with
  | [] => ~ valid_frame top bottom a
  | ra :: rest => valid_frame top bottom a /\ bottom + 16 <= a /\ rd64 m (a - 8) ra /\ 4096 <= ra
                  /\ exists a', rd64 m (a - 16) a' /\ fpchain m top a a' rest
  end.

#[using="Type"] Lemma fpchain_frame : forall ras m m' top bottom a W,
  fpchain m top bottom a ras -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => snd iv <= bottom) W ->
  fpchain m' top bottom a ras.
Proof.
  induction ras as [|ra rest IH]; intros m m' top bottom a W CH MU WM HW; cbn in *; [exact CH|].
  destruct CH as (V & V16 & R1 & R2 & a' & R3 & CH'). unfold valid_frame, rd64 in *.
  assert (DJ : forall A, bottom <= A -> disjoint_from W A 8).
  { intros A HA. clear -HW HA. induction W as [|[lo hi] W IHW]; cbn; [exact I|]. inversion HW as [|x l H1 H2]; subst. cbn in H1.
    split; [lia| apply IHW; exact H2]. }
  split; [exact V|]. split; [exact V16|]. split; [| split; [exact R2| exists a'; split]].
  - split; [| lia]. eapply bytes_at_transport; [exact (proj1 R1) | exact MU |]. rewrite length_le8. change (Z.of_nat 8) with 8%Z. apply DJ. lia.
  - split; [| lia]. eapply bytes_at_transport; [exact (proj1 R3) | exact MU |]. rewrite length_le8. change (Z.of_nat 8) with 8%Z. apply DJ. lia.
  - eapply IH; [exact CH' | exact MU | exact WM |]. eapply Forall_impl; [| exact HW]. cbv beta. intros iv Hiv. lia.
Qed.

Definition A0_TRACES : list (list Z) :=
  [[362704; 549064]
  ;[362704; 549148]
  ;[362352; 549184]
  ;[362352; 549488]
  ;[362704; 549800]
  ;[362352; 549948]
  ;[362352; 571252]
  ;[362352; 551492]
  ;[362704; 558204; 568020; 550756; 549904]
  ;[362704; 558204; 565248; 568104; 550756; 549904]
  ;[362352; 558912; 568020; 550756; 549904]
  ;[362352; 558912; 565248; 568104; 550756; 549904]
  ;[362352; 559056; 568020; 550756; 549904]
  ;[362352; 559056; 565248; 568104; 550756; 549904]
  ;[362704; 570684]
  ;[362352; 572744]
  ;[362352; 572940]
  ;[362704; 573116]
  ;[362352; 573716]
  ;[362352; 573988]
  ;[363372; 574108]
  ;[363372; 574132]
  ;[363372; 574740]
  ;[363372; 575004]
  ;[363372; 575540]
  ;[363372; 575564]

  ;[362704]
  ;[362352]    ].
#[using="Type"] Lemma A0_TRACES_length : length A0_TRACES = 28%nat. Proof. reflexivity. Qed.

Definition a0_static {HC : HasCeiling} (lo hi : Z) : Prop :=
  lo <= hi /\
  ( (0x10000 <= lo /\ hi <= 0xabde8)
  \/ (0xae6c0 <= lo /\ hi <= 0xaedc0)
  \/ (0x5d5f40 <= lo /\ hi <= 0x5e5fa0) \/ (0x5e5fc0 <= lo /\ hi <= 0x5e6060)
  \/ (0x5e68c8 <= lo /\ hi <= 0x5e68d0) \/ (0x6069b0 <= lo /\ hi <= 0x6069b8) \/ (0x6069c0 <= lo /\ hi <= 0x606be0)
  \/ (0x1457a0 <= lo /\ hi <= 0x1457a1)
  \/ (0x606be0 <= lo /\ hi <= 0x606be4) \/ (0x606c00 <= lo /\ hi <= 0x606c08) \/ (0x606fc0 <= lo /\ hi <= 0x607480)
  \/ (0x7fffa000 <= lo /\ hi <= 0x800b9200)
  \/ (sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo /\ hi <= 0x10007fff8000) ).

Definition a0_wsafe (x y : Z) : Prop := (y <= 0xa9000 \/ 0xabde8 <= x) /\ (y <= 0x6069b0 \/ 0x6069b8 <= x).

#[using="Type"] Lemma a0_static_s6 : a0_static (sh alloc_ceiling - sh alloc_ceiling mod 8) 0x10007fff8000.
Proof.
  pose proof alloc_ceiling_bounds as ACR. unfold a0_static. split; [unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia|].
  do 12 right. lia.
Qed.

#[using="Type"] Lemma fs_shadow_below_band : sh (FSB FI) + A0_FS_SHSIZE <= sh alloc_ceiling - sh alloc_ceiling mod 8.
Proof.
  pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _). pose proof alloc_ceiling_bounds as ACR. pose proof alloc_ceiling_aligned as A16.
  unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Record am_if := mkAM {
  am_K : Type;
  am_K_eqb : am_K -> am_K -> bool;
  am_K_eqb_eq : forall a b, am_K_eqb a b = true <-> a = b;
  aps : Type;

  am_ghost : aps -> (word -> bool) * list word;

  am_vm : aps -> VmState -> Prop;

  am_nsec : aps -> Z;
  RHEAP_A : aps -> list (block am_K) -> mem -> Prop;
  am_static : Z -> Z -> Prop;
  am_stack_top : Z;
  am_stack_bottom : Z;

  am_stack_ok : alloc_ceiling - 160 <= am_stack_bottom < alloc_ceiling + 4096 /\ am_stack_bottom + 2^23 = am_stack_top /\ am_stack_top <= 2^47 /\ am_stack_top mod 4096 = 0;

  am_sp0_strict : alloc_ceiling + 2^23 + 184 <= 2^47;
  am_block_range : forall s LB m b, RHEAP_A s LB m -> In b LB ->
      0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling
      /\ 0x609000 <= blk_addr b
      /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
      /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b);
  am_blocks_disjoint : forall s LB m b1 b2, RHEAP_A s LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1;
  am_blocks_nodup : forall s LB m, RHEAP_A s LB m -> NoDup (map blk_id LB);

  am_block_slack : forall s LB m b a, RHEAP_A s LB m -> In b LB ->
      blk_addr b - 16 <= a < round_up8 (blk_addr b + blk_size b) -> exists v, mrd asegs m (wa a) = Some v;

  am_block_shadow : forall s LB m b, RHEAP_A s LB m -> In b LB ->
      rw_cells asegs m (sh (blk_addr b)) (shadow_cells (block_shadow (blk_size b)));

  am_block_shread : forall s LB m b, RHEAP_A s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b);

  am_heap_frame : forall s LB m m' W,
      RHEAP_A s LB m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => alloc_ceiling <= fst iv
                        \/ (exists lo hi, am_static lo hi /\ lo <= fst iv /\ snd iv <= hi /\ a0_wsafe (fst iv) (snd iv))
                        \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                        \/ (FSB FI <= fst iv /\ snd iv <= FSB FI + A0_FS_SIZE)
                        \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE)) W ->
      RHEAP_A s LB m';
  am_heap_perm : forall s LB LB' m, RHEAP_A s LB m -> Permutation LB LB' -> RHEAP_A s LB' m;

  am_fsenv : forall s LB m, RHEAP_A s LB m -> FSENV FI m
}.

Variable AI : am_if.
Local Notation K := (am_K AI).
Local Notation BL := (list (block K)).
Local Notation PS := (aps AI).

Definition aclient (LB : BL) (q a : Z) : Prop :=
  q <= a
  \/ (exists lo hi, am_static AI lo hi /\ lo <= a < hi)
  \/ in_block LB a
  \/ (FSB FI <= a < FSB FI + A0_FS_SIZE) \/ (sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE)
  \/ (exists b, In b LB /\ sh (blk_addr b) <= a < sh (blk_addr b) + Z.of_nat (length (block_shadow (blk_size b)))).

Definition apres (LB : BL) (q : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient LB q a -> gkeep m m' (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
#[using="Type"] Lemma apres_refl : forall LB q m, apres LB q m m. Proof. intros LB q m a _ _; split; [apply gkeep_refl| auto]. Qed.
#[using="Type"] Lemma apres_trans : forall LB q m1 m2 m3, apres LB q m1 m2 -> apres LB q m2 m3 -> apres LB q m1 m3.
Proof. intros LB q m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [exact (gkeep_trans _ _ _ _ E1 E2)| auto]. Qed.

#[using="Type"] Lemma apres_mrd : forall LB q m m' a b, apres LB q m m' -> 0 <= a < 2^64 -> aclient LB q a ->
  mrd asegs m (wa a) = Some b -> mrd asegs m' (wa a) = Some b.
Proof. intros LB q m m' a b AP Ha Hc Hr. exact (gkeep_mrd m m' (wa a) b (proj1 (AP a Ha Hc)) Hr). Qed.
#[using="Type"] Lemma apres_eq : forall LB q m m' a, apres LB q m m' -> 0 <= a < 2^64 -> aclient LB q a ->
  mrd asegs m (wa a) <> None -> m' (wa a) = m (wa a).
Proof. intros LB q m m' a AP Ha Hc Hr. exact (gkeep_eq m m' (wa a) (proj1 (AP a Ha Hc)) Hr). Qed.

#[using="Type"] Lemma apres_gagree : forall LB q m m', apres LB q m m' -> gagree_on (aclient LB q) m m'.
Proof. intros LB q m m' H. exact H. Qed.

#[using="Type"] Lemma apres_of_gmunch : forall LB q W m m',
  gmunch W m m' -> wmono asegs m m' -> (forall a, 0 <= a < 2^64 -> aclient LB q a -> outside W a) -> apres LB q m m'.
Proof.
  intros LB q W m m' G WM HO a Ha Hc. split; [| intros Hw; apply WM; exact Hw].
  apply (gmunch_gkeep_at W m m' a G Ha). apply HO; assumption.
Qed.

Definition aclient_range (LB : BL) (q A n : Z) : Prop := forall a, A <= a < A + n -> aclient LB q a.
#[using="Type"] Lemma apres_bytes_at : forall LB q m m' A bs,
  apres LB q m m' -> bytes_at asegs m A bs -> aclient_range LB q A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros LB q m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (HB i Hi) as Hr. destruct (nth_error bs i) as [b|] eqn:En; [| exfalso; apply nth_error_None in En; lia].
  apply (apres_mrd LB q m m' _ b HP); [lia| apply HR; lia| exact Hr].
Qed.
#[using="Type"] Lemma apres_wr_at : forall LB q m m' A n, apres LB q m m' -> wr_at asegs m A n -> aclient_range LB q A n -> wr_at asegs m' A n.
Proof.
  intros LB q m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ Wv]. apply Wv. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma apres_rw_cells : forall LB q m m' A cs,
  apres LB q m m' -> rw_cells asegs m A cs -> aclient_range LB q A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros LB q m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply apres_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply apres_wr_at; eauto.
Qed.
#[using="Type"] Lemma aclient_range_above : forall LB q A n, q <= A -> aclient_range LB q A n.
Proof. intros LB q A n H a Ha. left. lia. Qed.
#[using="Type"] Lemma aclient_range_block : forall LB q A n b, In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> aclient_range LB q A n.
Proof. intros LB q A n b HIN H1 H2 a Ha. right; right; left. exists b. split; [exact HIN|]. lia. Qed.
#[using="Type"] Lemma aclient_range_static : forall LB q A n lo hi, am_static AI lo hi -> lo <= A -> A + n <= hi -> aclient_range LB q A n.
Proof. intros LB q A n lo hi HS H1 H2 a Ha. right; left. exists lo, hi. split; [exact HS|]. lia. Qed.
#[using="Type"] Lemma aclient_range_fs : forall LB q A n, FSB FI <= A -> A + n <= FSB FI + A0_FS_SIZE -> aclient_range LB q A n.
Proof. intros LB q A n H1 H2 a Ha. right; right; right; left. lia. Qed.
#[using="Type"] Lemma aclient_range_fs_shadow : forall LB q A n, sh (FSB FI) <= A -> A + n <= sh (FSB FI) + A0_FS_SHSIZE -> aclient_range LB q A n.
Proof. intros LB q A n H1 H2 a Ha. right; right; right; right; left. lia. Qed.

Definition lb_bytes (LB : BL) : Z := fold_right (fun b acc => blk_size b + acc) 0 LB.
Definition lb_cls (c : Z) (LB : BL) : BL := List.filter (fun b => a0_cls (blk_size b) =? c) LB.
Definition lbc (LB : BL) (c : Z) : Z := Z.of_nat (length (lb_cls c LB)).
Definition am_budget (s : PS) (LB : BL) (n : Z) : Prop :=
  if a0_cls n =? 0 then lbc LB 0 + 1 <= A0_SEC_CNT /\ lb_bytes (lb_cls 0 LB) + n <= A0_SEC_BYTES /\ am_nsec AI s + 1 <= A0_NSEC_MAX
  else (lbc LB (a0_cls n) + 1) * a0_csz (a0_cls n) <= A0_CAP (a0_cls n).

#[using="Type"] Lemma lbc_nonneg : forall LB c, 0 <= lbc LB c. Proof. intros. unfold lbc. lia. Qed.
#[using="Type"] Lemma lbc_nil : forall c, lbc [] c = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma lbc_cons : forall b LB c, lbc (b :: LB) c = (if a0_cls (blk_size b) =? c then 1 else 0) + lbc LB c.
Proof. intros b LB c. unfold lbc, lb_cls. cbn [List.filter]. destruct (a0_cls (blk_size b) =? c); cbn [length]; rewrite ?Nat2Z.inj_succ; lia. Qed.
#[using="Type"] Lemma lbc_app : forall LB1 LB2 c, lbc (LB1 ++ LB2) c = lbc LB1 c + lbc LB2 c.
Proof. intros. unfold lbc, lb_cls. rewrite List.filter_app, length_app, Nat2Z.inj_add. lia. Qed.
#[using="Type"] Lemma lbc_le_length : forall LB c, lbc LB c <= Z.of_nat (length LB).
Proof. intros LB c. unfold lbc, lb_cls. pose proof (List.filter_length_le (fun b : block K => a0_cls (blk_size b) =? c) LB). lia. Qed.
#[using="Type"] Lemma lb_cls_perm : forall c LB LB', Permutation LB LB' -> Permutation (lb_cls c LB) (lb_cls c LB').
Proof.
  intros c LB LB' HP. unfold lb_cls. induction HP as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; cbn [List.filter].
  - constructor.
  - destruct (a0_cls (blk_size x) =? c); [constructor|]; exact IH.
  - destruct (a0_cls (blk_size x) =? c); destruct (a0_cls (blk_size y) =? c); try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.
#[using="Type"] Lemma lbc_perm : forall LB LB' c, Permutation LB LB' -> lbc LB c = lbc LB' c.
Proof. intros LB LB' c HP. unfold lbc. rewrite (Permutation_length (lb_cls_perm c _ _ HP)). reflexivity. Qed.
#[using="Type"] Lemma lb_bytes_cons : forall b LB, lb_bytes (b :: LB) = blk_size b + lb_bytes LB. Proof. reflexivity. Qed.
#[using="Type"] Lemma lb_bytes_app : forall LB1 LB2, lb_bytes (LB1 ++ LB2) = lb_bytes LB1 + lb_bytes LB2.
Proof. induction LB1 as [|b l IH]; intros LB2; [reflexivity|]. cbn [app]. rewrite !lb_bytes_cons, IH. lia. Qed.
#[using="Type"] Lemma lb_bytes_perm : forall LB LB', Permutation LB LB' -> lb_bytes LB = lb_bytes LB'.
Proof.
  intros LB LB' HP. induction HP as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; rewrite ?lb_bytes_cons in *; lia.
Qed.

Inductive bl_sub : BL -> BL -> Prop :=
| bl_sub_nil : bl_sub [] []
| bl_sub_keep : forall b l l', bl_sub l l' -> bl_sub (b :: l) (b :: l')
| bl_sub_drop : forall b l l', bl_sub l l' -> bl_sub l (b :: l').
#[using="Type"] Lemma bl_sub_refl : forall l, bl_sub l l. Proof. induction l; constructor; assumption. Qed.
#[using="Type"] Lemma bl_sub_filter : forall (f : block K -> bool) l, bl_sub (List.filter f l) l.
Proof. intros f l. induction l as [|b l IH]; cbn [List.filter]; [constructor|]. destruct (f b); constructor; exact IH. Qed.
#[using="Type"] Lemma bl_sub_remove : forall k LB, bl_sub (lb_remove (am_K_eqb AI) k LB) LB.
Proof.
  intros k LB. unfold lb_remove. induction LB as [|b l IH]; [constructor|]. rewrite list_basics.list.filter_cons.
  match goal with |- context [decide ?P] => destruct (decide P) end; constructor; exact IH.
Qed.
#[using="Type"] Lemma bl_sub_trans : forall l1 l2 l3, bl_sub l1 l2 -> bl_sub l2 l3 -> bl_sub l1 l3.
Proof.
  intros l1 l2 l3 H12 H23. revert l1 H12. induction H23 as [| b l l' _ IH | b l l' _ IH]; intros l1 H12.
  - exact H12.
  - inversion H12; subst; constructor; apply IH; assumption.
  - constructor. apply IH. exact H12.
Qed.
#[using="Type"] Lemma bl_sub_cls : forall c l l', bl_sub l l' -> bl_sub (lb_cls c l) (lb_cls c l').
Proof.
  intros c l l' HS. unfold lb_cls. induction HS as [| b l l' _ IH | b l l' _ IH]; cbn [List.filter].
  - constructor.
  - destruct (a0_cls (blk_size b) =? c); [constructor|]; exact IH.
  - destruct (a0_cls (blk_size b) =? c); [constructor|]; exact IH.
Qed.
#[using="Type"] Lemma bl_sub_length : forall l l', bl_sub l l' -> (length l <= length l')%nat.
Proof. intros l l' HS. induction HS; cbn [length]; lia. Qed.
#[using="Type"] Lemma bl_sub_bytes : forall l l', Forall (fun b => 0 <= blk_size b) l' -> bl_sub l l' -> lb_bytes l <= lb_bytes l'.
Proof.
  intros l l' HF HS. induction HS as [| b l l' _ IH | b l l' _ IH]; rewrite ?lb_bytes_cons; [lia| |].
  - inversion HF; subst. specialize (IH ltac:(assumption)). lia.
  - inversion HF; subst. specialize (IH ltac:(assumption)). lia.
Qed.
#[using="Type"] Lemma lbc_sub : forall l l' c, bl_sub l l' -> lbc l c <= lbc l' c.
Proof. intros l l' c HS. unfold lbc. pose proof (bl_sub_length _ _ (bl_sub_cls c _ _ HS)). lia. Qed.

#[using="Type"] Lemma am_budget_sub : forall s LB LB' n,
  bl_sub LB LB' -> Forall (fun b => 0 <= blk_size b) LB' -> 0 <= n -> am_budget s LB' n -> am_budget s LB n.
Proof.
  intros s LB LB' n HS HF Hn HB. unfold am_budget in *. pose proof (lbc_sub _ _ (a0_cls n) HS) as L1.
  destruct (a0_cls n =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E in L1. destruct HB as (B1 & B2 & B3). split; [lia|]. split; [| exact B3].
    assert (HF0 : Forall (fun b : block K => 0 <= blk_size b) (lb_cls 0 LB')).
    { unfold lb_cls. apply Forall_forall. intros b Hb. apply List.filter_In in Hb as [Hb _]. exact (proj1 (Forall_forall _ _) HF b Hb). }
    pose proof (bl_sub_bytes _ _ HF0 (bl_sub_cls 0 _ _ HS)). lia.
  - pose proof (lbc_nonneg LB (a0_cls n)). pose proof (a0_cls_range n Hn) as CR. destruct (a0_caps_ok (a0_cls n) ltac:(lia)) as [C0 _]. nia.
Qed.

#[using="Type"] Lemma am_budget_sub_heap : forall s0 s LB LB' m n,
  RHEAP_A AI s0 LB' m -> bl_sub LB LB' -> 0 <= n -> am_budget s LB' n -> am_budget s LB n.
Proof.
  intros s0 s LB LB' m n HR HS Hn HB. eapply am_budget_sub; [exact HS| | exact Hn| exact HB].
  apply Forall_forall. intros b Hb. destruct (am_block_range AI _ _ _ _ HR Hb) as (_ & _ & R & _). exact R.
Qed.
#[using="Type"] Lemma am_budget_perm : forall s LB LB' n, Permutation LB LB' -> am_budget s LB n -> am_budget s LB' n.
Proof.
  intros s LB LB' n HP HB. unfold am_budget in *. destruct (a0_cls n =? 0).
  - rewrite <- (lbc_perm LB LB' 0 HP), <- (lb_bytes_perm _ _ (lb_cls_perm 0 _ _ HP)). exact HB.
  - rewrite <- (lbc_perm LB LB' (a0_cls n) HP). exact HB.
Qed.

#[using="Type"] Lemma am_budget_nsec : forall s s' LB n, am_nsec AI s' <= am_nsec AI s -> am_budget s LB n -> am_budget s' LB n.
Proof. intros s s' LB n HN HB. unfold am_budget in *. destruct (a0_cls n =? 0); [| exact HB]. destruct HB as (B1 & B2 & B3). repeat split; lia. Qed.
#[using="Type"] Lemma am_budget_small : forall s s' LB n, a0_cls n <> 0 -> am_budget s LB n -> am_budget s' LB n.
Proof. intros s s' LB n HN HB. unfold am_budget in *. destruct (a0_cls n =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction| exact HB]. Qed.

#[using="Type"] Lemma am_budget_of_length : forall s LB n, 0 <= n -> Z.of_nat (length LB) < 2^13 ->
  lb_bytes (lb_cls 0 LB) + n <= A0_SEC_BYTES -> am_nsec AI s + 1 <= A0_NSEC_MAX -> am_budget s LB n.
Proof.
  intros s LB n Hn HL HBY HNS. unfold am_budget. pose proof (lbc_le_length LB (a0_cls n)) as L1. pose proof (lbc_le_length LB 0) as L0.
  pose proof (lbc_nonneg LB (a0_cls n)) as L2.
  destruct (a0_cls n =? 0) eqn:E; [unfold A0_SEC_CNT; split; [lia| split; [exact HBY| exact HNS]]|].
  pose proof (a0_cls_range n Hn) as CR. destruct (a0_caps_ok (a0_cls n) ltac:(lia)) as [C0 C1]. nia.
Qed.

Definition alloc_frame_A (q lo : Z) (st : fsstate FI) (m m' : mem) (LBkeep : BL) : Prop :=
  mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
  /\ apres LBkeep q m m'.

Record a0_judg := mkAJ {
  AJ : (PS -> BL -> machine_state -> Prop) -> machine_state -> PS -> BL -> Prop;
  aj_ret : forall (Q : PS -> BL -> machine_state -> Prop) ms s LB, Q s LB ms -> AJ Q ms s LB;
  aj_mono : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
      AJ P ms s LB -> (forall s' LB' ms', P s' LB' ms' -> Q s' LB' ms') -> AJ Q ms s LB;
  aj_bind : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
      AJ P ms s LB -> (forall s' LB' ms', P s' LB' ms' -> AJ Q ms' s' LB') -> AJ Q ms s LB;
  aj_evt : forall (P : machine_state -> Prop) (Q : PS -> BL -> machine_state -> Prop) ms s LB,
      evt asegs P ms -> (forall ms', P ms' -> AJ Q ms' s LB) -> AJ Q ms s LB;
  aj_perm : forall Q ms s LB LB', Permutation LB LB' -> AJ Q ms s LB' -> AJ Q ms s LB
}.
Variable J : a0_judg.

Definition malloc_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LB : BL) (n lo : Z) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (k : K) (A : Z) (junk : list byte),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ alloc_frame_A q lo st m m' LB
    /\ LB' = (k, A, n) :: LB /\ RHEAP_A AI s' LB' m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
    /\ rw_cells asegs m' (sh A) (shadow_cells (block_shadow n))
    /\ wmono asegs m m'
    /\ am_nsec AI s' = am_nsec AI s + (if a0_cls n =? 0 then 1 else 0).
Definition malloc_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (n lo : Z) (ras : list Z),
  RHEAP_A AI s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top AI) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz n -> 0 <= n <= A0_MAXREQ -> am_budget s LB n ->
  AJ J (malloc_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_malloc) fc None m (seg_rom asegs))
    s LB.

Definition free_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LBrest : BL) (lo : Z) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ alloc_frame_A q lo st m m' LBrest
    /\ LB' = LBrest /\ RHEAP_A AI s' LBrest m'
    /\ am_nsec AI s' = am_nsec AI s.
Definition free_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (k : K) (A n lo : Z) (ras : list Z),
  RHEAP_A AI s LB m -> In (k, A, n) LB -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top AI) q (bv_unsigned s0) ras -> In (PC0_FREE :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz A ->
  AJ J (free_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s (lb_remove (am_K_eqb AI) k LB) lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_free) fc None m (seg_rom asegs))
    s LB.

Definition free_null_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (lo : Z) (ras : list Z),
  RHEAP_A AI s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top AI) q (bv_unsigned s0) ras -> In (PC0_FREE :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz 0 ->
  evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ alloc_frame_A q lo st m m' LB /\ wmono asegs m m' /\ RHEAP_A AI s LB m')
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_free) fc None m (seg_rom asegs)).

Definition realloc_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LBrest : BL) (n oldn lo : Z) (old : list byte) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (k' : K) (B : Z) (junk : list byte),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz B) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ alloc_frame_A q lo st m m' LBrest
    /\ LB' = (k', B, n) :: LBrest /\ RHEAP_A AI s' LB' m'
    /\ rw_cells asegs m' B [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n oldn)) old ++ junk)]
    /\ rw_cells asegs m' (sh B) (shadow_cells (block_shadow n))
    /\ am_nsec AI s' = am_nsec AI s + (if a0_cls n =? 0 then 1 else 0).
Definition realloc_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (k : K) (A oldn n lo : Z)
         (old : list byte) (ras : list Z),
  RHEAP_A AI s LB m -> In (k, A, oldn) LB -> rw_cells asegs m A [CB (Z.to_nat oldn) old] ->
  asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top AI) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz A -> a1 = wz n -> 0 < n <= A0_MAXREQ -> am_budget s LB n ->
  AJ J (realloc_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s (lb_remove (am_K_eqb AI) k LB) n oldn lo old m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_realloc) fc None m (seg_rom asegs))
    s LB.

Definition realloc_null_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (n lo : Z) (ras : list Z),
  RHEAP_A AI s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top AI) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz 0 -> a1 = wz n -> 0 <= n <= A0_MAXREQ -> am_budget s LB n ->
  AJ J (malloc_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_realloc) fc None m (seg_rom asegs))
    s LB.

Definition malloc_top_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (n lo : Z),
  RHEAP_A AI s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 ->
  am_stack_top AI <= q + 16 -> q <= alloc_ceiling + 2^23 ->
  mem_inv asegs m ->
  a0 = wz n -> 0 <= n <= A0_MAXREQ -> am_budget s LB n ->
  AJ J (malloc_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_malloc) fc None m (seg_rom asegs))
    s LB.
Definition free_top_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (k : K) (A n lo : Z),
  RHEAP_A AI s LB m -> In (k, A, n) LB -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 ->
  am_stack_top AI <= q + 16 -> q <= alloc_ceiling + 2^23 ->
  mem_inv asegs m ->
  a0 = wz A ->
  AJ J (free_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s (lb_remove (am_K_eqb AI) k LB) lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_free) fc None m (seg_rom asegs))
    s LB.

Record am_contracts := mkAC {
  ac_malloc : malloc_stmt_A;
  ac_free : free_stmt_A;
  ac_free_null : free_null_stmt_A;
  ac_realloc : realloc_stmt_A;
  ac_realloc_null : realloc_null_stmt_A;
  ac_malloc_top : malloc_top_stmt_A;
  ac_free_top : free_top_stmt_A
}.
End A.

