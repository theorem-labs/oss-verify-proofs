(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_identity_ingest.v, with its numbers changed; 577 of its 643 lines of code are new or changed and 428 lines of the source are left out. *)
(* The version arm of the walk of reac_identity_ingest (fuzz_identity.asan): ting_seg_ver, stated in
   lib/A/Prog/IngestSeg.v. The main path hands the arm over at 0x83994 (AF_ing_ver) with a0 = id,
   a2 = p, a3 = len, a6 = the shadow base, the 32-byte frame built and ra, s0, s1 saved in it, the
   call accepted, ad = 1536 and 8 <= len. The arm reads p[0..8), writes the eight raw bytes to
   id+28 (four sh), the three big-endian pairs to id+22, id+24, id+26 (three sh) and 1 to id+36
   (0x83ca0 .. 0x83cb8, the shared epilogue), then leaves through the tail with a4 = 1.
   The walk is one symbolic run from 0x83994 to the ret at 0x83cd0: the shadow checks of the payload
   load and of every store are decided by two shadow entries (the record's 38 bytes, the payload's
   first 8), so none of the __asan_report_* calls is reached.
   The bytes the arm leaves in the record are read off the final state's chunks. A chunk's value is a
   tree of SLL / SRL / OR over the payload-byte atoms; bab (below) maps such a tree to the source of
   each of its 64 bits, which gives each byte of the chunk by vm_compute. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ YC1g YC4b YC1h YC85
reac_identity_ingest IngestSeg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel RcIdentLib reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- bit sources -------------------------------------------------------------------------------
   A bsrc says what one bit of a symbolic value is: BZ, it is 0; BAt n i, it is bit i of atom n.
   bab e = Some l reads that off the shape of e: l holds the sources of e's bits 0, 1, ..., under the
   premise that every atom e names holds a byte. *)
Inductive bsrc : Type := BZ | BAt (n : nat) (i : nat).
Definition bmerge2 (a b : bsrc) : option bsrc :=
  match a, b with BZ, x => Some x | x, BZ => Some x | _, _ => None end.
Fixpoint bmerge (l1 l2 : list bsrc) : option (list bsrc) :=
  match l1, l2 with
  | [], _ => Some l2
  | _, [] => Some l1
  | a :: r1, b :: r2 =>
      match bmerge2 a b, bmerge r1 r2 with
      | Some c, Some r => Some (c :: r)
      | _, _ => None
      end
  end.
Definition bshl (l : list bsrc) (k : nat) : list bsrc := firstn 64 (repeat BZ k ++ l).
Definition bshr (l : list bsrc) (k : nat) : list bsrc := skipn k l.
Definition bbyte (n : nat) : list bsrc := map (fun i => BAt n i) (seq 0 8).
Fixpoint bab (e : sv) : option (list bsrc) :=
  match e with
  | SLit 0 => Some []
  | SOff n 0 => Some (bbyte n)
  | SAlu ALU_OR a b =>
      match bab a, bab b with Some la, Some lb => bmerge la lb | _, _ => None end
  | SAlu ALU_SLL a (SLit k) =>
      if ((0 <=? k) && (k <? 64))%bool then option_map (fun l => bshl l (Z.to_nat k)) (bab a) else None
  | SAlu ALU_SRL a (SLit k) =>
      if ((0 <=? k) && (k <? 64))%bool then option_map (fun l => bshr l (Z.to_nat k)) (bab a) else None
  | _ => None
  end.
Fixpoint bats (e : sv) : list nat :=
  match e with
  | SOff n _ => [n]
  | SAlu _ a b => bats a ++ bats b
  | _ => []
  end.
(* The payload-byte atoms of the arm are 33 .. 40; bab_at checks that a chunk's value names only
   those, and that its t-th byte is the eight bits of atom n. *)
Definition bats_ok (e : sv) : bool := forallb (fun n => ((33 <=? n) && (n <=? 40))%nat%bool) (bats e).
Definition bab_at (e : sv) (t : Z) (n : nat) : bool :=
  (bats_ok e &&
   match bab e with
   | None => false
   | Some l => forallb (fun i => match nth (Z.to_nat (8 * t) + i)%nat l BZ with
                                 | BAt m j => (Nat.eqb m n && Nat.eqb j i)%bool
                                 | BZ => false end) (seq 0 8)
   end)%bool.
Definition bsem (E : env) (s : bsrc) : bool :=
  match s with BZ => false | BAt n i => Z.testbit (bv_unsigned (ew E n)) (Z.of_nat i) end.
Definition bat_ok (E : env) (P : nat -> Prop) : Prop := forall n, P n -> 0 <= bv_unsigned (ew E n) < 256.
Lemma nth_repeat_BZ : forall k j, nth j (repeat BZ k) BZ = BZ.
Proof.
  induction k as [|k IH]; intros j; [destruct j; reflexivity|].
  destruct j as [|j]; [reflexivity|]. cbn [repeat nth]. apply IH.
Qed.
Lemma nth_repeat_app1 : forall (l : list bsrc) k j, (j < k)%nat -> nth j (repeat BZ k ++ l) BZ = BZ.
Proof.
  intros l k j H. rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat_BZ.
Qed.
Lemma nth_repeat_app2 : forall (l : list bsrc) k j, (k <= j)%nat -> nth j (repeat BZ k ++ l) BZ = nth (j - k) l BZ.
Proof.
  intros l k j H. rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length. reflexivity.
Qed.
Lemma nth_firstn_b : forall (l : list bsrc) n j, (j < n)%nat -> nth j (firstn n l) BZ = nth j l BZ.
Proof.
  induction l as [|x l IH]; intros n j H; destruct n as [|n]; try lia.
  - destruct j; reflexivity.
  - destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma nth_skipn_b : forall (l : list bsrc) k j, nth j (skipn k l) BZ = nth (k + j) l BZ.
Proof.
  induction l as [|x l IH]; intros k j.
  - rewrite skipn_nil. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma bmerge_len : forall l1 l2 l, bmerge l1 l2 = Some l -> (length l <= Nat.max (length l1) (length l2))%nat.
Proof.
  induction l1 as [|a r1 IH]; intros l2 l H; cbn [bmerge] in H.
  - injection H as <-. cbn [length]. lia.
  - destruct l2 as [|b r2]; [injection H as <-; cbn [length]; lia|].
    destruct (bmerge2 a b) as [c|] eqn:Hc; [|discriminate].
    destruct (bmerge r1 r2) as [r|] eqn:Hr; [|discriminate].
    injection H as <-. cbn [length]. pose proof (IH r2 r Hr). lia.
Qed.
Lemma bmerge_nth : forall E l1 l2 l j, bmerge l1 l2 = Some l ->
  bsem E (nth j l BZ) = (bsem E (nth j l1 BZ) || bsem E (nth j l2 BZ))%bool.
Proof.
  intros E. induction l1 as [|a r1 IH]; intros l2 l j H; cbn [bmerge] in H.
  - injection H as <-. destruct j; cbn [nth bsem]; reflexivity.
  - destruct l2 as [|b r2].
    { injection H as <-. destruct j; cbn [nth bsem]; symmetry; apply orb_false_r. }
    destruct (bmerge2 a b) as [c|] eqn:Hc; [|discriminate].
    destruct (bmerge r1 r2) as [r|] eqn:Hr; [|discriminate].
    injection H as <-. destruct j as [|j]; [|cbn [nth]; exact (IH r2 r j Hr)].
    cbn [nth]. destruct a as [|na ia], b as [|nb ib]; cbn [bmerge2] in Hc;
      try discriminate; injection Hc as <-; cbn [bsem];
      first [symmetry; apply orb_false_r | reflexivity].
Qed.
Lemma zcanon_bit : forall z i, 0 <= i < 64 -> Z.testbit (zcanon z) i = Z.testbit z i.
Proof.
  intros z i Hi. unfold zcanon, M64. rewrite <- (Z.mod_pow2_bits_low z 64 i) by lia. reflexivity.
Qed.
Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma u_alu64 : forall op (x y : word),
  bv_unsigned (alu64 op x y) = zalu64 op (bv_unsigned x) (bv_unsigned y).
Proof.
  intros op x y. pose proof (zalu64_sound op (bv_unsigned x) (bv_unsigned y)) as H.
  rewrite !Z_to_bv_bv_unsigned in H. rewrite H, Z_to_bv_unsigned.
  unfold zalu64, zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* bab is sound: bit i of e's value is what the i-th bsrc says. *)
Lemma bab_sound : forall (E : env) e l,
  bab e = Some l -> bat_ok E (fun n => In n (bats e)) ->
  (length l <= 64)%nat /\
  forall i, 0 <= i < 64 -> Z.testbit (bv_unsigned (sv_denot E e)) i = bsem E (nth (Z.to_nat i) l BZ).
Proof.
  intros E e. induction e as [z | n z | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb
    | op a IHa b IHb | sg wd a IHa | d ii wd | op a IHa | op a IHa b IHb | op a IHa b IHb c IHc];
    intros l Hb HA; cbn [bab] in Hb; try discriminate.
  - (* SLit *)
    destruct z; try discriminate. injection Hb as <-.
    split; [cbn [length]; lia|]. intros i Hi.
    cbn [sv_denot]. rewrite unsigned_lit_small by lia. rewrite Z.bits_0.
    destruct (Z.to_nat i); reflexivity.
  - (* SOff *)
    destruct z; try discriminate. injection Hb as <-.
    assert (HB : 0 <= bv_unsigned (ew E n) < 256) by (apply HA; cbn [bats]; left; reflexivity).
    split; [unfold bbyte; rewrite length_map, length_seq; lia|]. intros i Hi.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
    + unfold bbyte. rewrite (nth_indep _ BZ (BAt n 0%nat)) by (rewrite length_map, length_seq; lia).
      rewrite map_nth, seq_nth by lia. cbn [bsem]. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
    + rewrite nth_overflow by (unfold bbyte; rewrite length_map, length_seq; lia). cbn [bsem].
      apply (Z.bits_above_log2 (bv_unsigned (ew E n)) i); [lia|].
      destruct (Z.eq_dec (bv_unsigned (ew E n)) 0) as [Hz|Hz]; [rewrite Hz; cbn; lia|].
      apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia | lia].
  - (* SAlu *)
    assert (HAa : bat_ok E (fun q => In q (bats a)))
      by (intros q Hq; apply HA; cbn [bats]; apply in_or_app; left; exact Hq).
    assert (HAb : bat_ok E (fun q => In q (bats b)))
      by (intros q Hq; apply HA; cbn [bats]; apply in_or_app; right; exact Hq).
    destruct op; try discriminate.
    + (* ALU_SLL *)
      destruct b as [k | | | | | | | | | |]; try discriminate.
      destruct ((0 <=? k) && (k <? 64))%bool eqn:Hk; [|discriminate].
      apply andb_prop in Hk as [Hk0 Hk1]. apply Z.leb_le in Hk0. apply Z.ltb_lt in Hk1.
      destruct (bab a) as [la|] eqn:Hba; [|discriminate]. cbn [option_map] in Hb. injection Hb as <-.
      destruct (IHa la eq_refl HAa) as [Hlen Hbit].
      split; [unfold bshl; rewrite length_firstn; lia|]. intros i Hi.
      cbn [sv_denot]. rewrite u_alu64. cbn [sv_denot]. rewrite (unsigned_lit_small k) by lia.
      unfold zalu64. rewrite zcanon_bit by lia. cbn [zalu_raw].
      rewrite (zcanon_id k) by (unfold M64; lia).
      change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
      rewrite (Z.mod_small k (2 ^ 6)) by lia.
      destruct (Z_lt_le_dec i k) as [Hlt|Hge].
      * rewrite Z.shiftl_spec_low by lia. unfold bshl.
        rewrite nth_firstn_b by lia. rewrite nth_repeat_app1 by lia. reflexivity.
      * rewrite Z.shiftl_spec by lia. rewrite zcanon_bit by lia. rewrite (Hbit (i - k) ltac:(lia)).
        unfold bshl. rewrite nth_firstn_b by lia. rewrite nth_repeat_app2 by lia.
        f_equal. f_equal. lia.
    + (* ALU_SRL *)
      destruct b as [k | | | | | | | | | |]; try discriminate.
      destruct ((0 <=? k) && (k <? 64))%bool eqn:Hk; [|discriminate].
      apply andb_prop in Hk as [Hk0 Hk1]. apply Z.leb_le in Hk0. apply Z.ltb_lt in Hk1.
      destruct (bab a) as [la|] eqn:Hba; [|discriminate]. cbn [option_map] in Hb. injection Hb as <-.
      destruct (IHa la eq_refl HAa) as [Hlen Hbit].
      split; [unfold bshr; rewrite length_skipn; lia|]. intros i Hi.
      cbn [sv_denot]. rewrite u_alu64. cbn [sv_denot]. rewrite (unsigned_lit_small k) by lia.
      unfold zalu64. rewrite zcanon_bit by lia. cbn [zalu_raw].
      rewrite (zcanon_id k) by (unfold M64; lia).
      change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
      rewrite (Z.mod_small k (2 ^ 6)) by lia.
      rewrite Z.shiftr_spec by lia. unfold bshr. rewrite nth_skipn_b.
      destruct (Z_lt_le_dec (i + k) 64) as [Hlt|Hge].
      * rewrite zcanon_bit by lia. rewrite (Hbit (i + k) ltac:(lia)). f_equal. f_equal. lia.
      * unfold zcanon, M64. rewrite Z.mod_pow2_bits_high by lia.
        rewrite nth_overflow by lia. reflexivity.
    + (* ALU_OR *)
      destruct (bab a) as [la|] eqn:Hba; [|discriminate].
      destruct (bab b) as [lb|] eqn:Hbb; [|discriminate].
      destruct (IHa la eq_refl HAa) as [Hlena Hbita]. destruct (IHb lb eq_refl HAb) as [Hlenb Hbitb].
      split; [pose proof (bmerge_len la lb l Hb); lia|]. intros i Hi.
      cbn [sv_denot]. rewrite u_alu64.
      unfold zalu64. rewrite zcanon_bit by lia. cbn [zalu_raw].
      rewrite Z.lor_spec, !zcanon_bit by lia.
      rewrite (Hbita i Hi), (Hbitb i Hi).
      exact (eq_sym (bmerge_nth E la lb l (Z.to_nat i) Hb)).
Qed.
(* The byte a chunk of value e holds at position t, when bab says its eight bits are atom n's. *)
Lemma bab_byte : forall (E : env) (e : sv) (t : Z) (n : nat),
  bab_at e t n = true ->
  (forall q, (33 <= q <= 40)%nat -> 0 <= bv_unsigned (ew E q) < 256) ->
  0 <= t ->
  byte_of_word (sv_denot E e) t = Z_to_bv 8 (bv_unsigned (ew E n)).
Proof.
  intros E e t n Hat HB Ht. unfold bab_at in Hat. apply andb_prop in Hat as [Hbats Hf].
  destruct (bab e) as [l|] eqn:Hbe; [|discriminate Hf].
  assert (HA : bat_ok E (fun q => In q (bats e))).
  { intros q Hq. apply HB.
    pose proof (proj1 (forallb_forall _ _) Hbats q Hq) as Hq2.
    apply andb_prop in Hq2 as [H1 H2]. apply Nat.leb_le in H1. apply Nat.leb_le in H2. lia. }
  destruct (bab_sound E e l Hbe HA) as [Hlen Hbit].
  unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge]; [|rewrite !Z.mod_pow2_bits_high by lia; reflexivity].
  rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia.
  assert (Hin : In (Z.to_nat i) (seq 0 8)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hf (Z.to_nat i) Hin) as Hi8.
  cbv beta in Hi8.
  remember (nth (Z.to_nat (8 * t) + Z.to_nat i)%nat l BZ) as src eqn:Hn.
  destruct src as [|m jj]; [discriminate Hi8|].
  apply andb_prop in Hi8 as [Hm Hjj]. apply Nat.eqb_eq in Hm. apply Nat.eqb_eq in Hjj. subst m jj.
  assert (Hidx : (Z.to_nat (8 * t) + Z.to_nat i < length l)%nat).
  { destruct (Nat.lt_ge_cases (Z.to_nat (8 * t) + Z.to_nat i) (length l)) as [Hq|Hq]; [exact Hq|].
    rewrite nth_overflow in Hn by lia. discriminate Hn. }
  rewrite (Hbit (i + 8 * t) ltac:(lia)).
  replace (Z.to_nat (i + 8 * t)) with (Z.to_nat (8 * t) + Z.to_nat i)%nat by lia.
  rewrite <- Hn. cbn [bsem]. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma ver_b8 : forall b : byte, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (RcIdentModel.bz b))) = b.
Proof.
  intros b. unfold RcIdentModel.bz.
  pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H.
  rewrite unsigned_lit_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
(* ---- the symbolic start state at 0x83994 --------------------------------------------------------
   Atoms 0..31 are the registers at the hand-over (a0 = id is atom 10, a2 = p atom 12, a6 the shadow
   base atom 16); atoms 32 and 33 + j are reac_identity_ingest.v's ing_extra (the shadow base and the
   payload bytes, so pay_region_ok applies as it is); atoms 50, 51, 52 are the caller's ra, s0 and
   s1, which the frame holds. The regions are the frame (read-only: the arm writes no stack byte),
   the record (writable on the 15 bytes the arm writes) and the payload's first 8 bytes. *)
Definition ver_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [ YP09.mkChunk 8 (CVal 8 (SOff 52 0)); YP09.mkChunk 16 (CVal 8 (SOff 51 0));
      YP09.mkChunk 24 (CVal 8 (SOff 50 0)) ].
Definition ver_regions : smem := [ ver_frame; rec_region 22 37; pay_region 8 ].
Definition ver_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 38) 3);
            (12%nat, mkAF 4096 (2 ^ 47 - 8) 0); (16%nat, mkAF SB_ING SB_ING 0);
            (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
            (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0);
            (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0) ] [] [].
Definition ss_ver : sstate := mkSS AF_ing_ver sr_atoms ver_regions None ver_facts.
Definition VBx : sv := SOff 16 0.
Definition SH_ver : list shent := [ mkSHE 10 0 38; mkSHE 12 0 8 ].
(* The atoms of the arm's environment: ing_extra, then ra, s0, s1. *)
Definition ver_extra (regs : bvmap 5 word) (pb : list byte) : list word :=
  ing_extra pb ++ [getr regs 1; getr regs 8; getr regs 9].
Definition EV (regsT regs : bvmap 5 word) (pb : list byte) : env := Eimg (Ereg regsT (ver_extra regs pb)).
Lemma ver_chunk_byte : forall E m (base : Z) (cs : list YP09.chunk) (coff : Z) (w : N) (e : sv) (i a : Z),
  Forall (YP09.chunk_ok SEGS E m base) cs -> In (YP09.mkChunk coff (CVal w e)) cs ->
  0 <= i < Z.of_N w -> a = coff + i ->
  mbyte SEGS m (base + a) = Some (byte_of_word (sv_denot E e) i).
Proof.
  intros E m base cs coff w e i a HF Hin Hi ->.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hc.
  destruct (Hc i Hi) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2.
  injection Hb1 as <-. rewrite Z.add_assoc. exact Hb2.
Qed.
(* Where the arm's regions let it write: the 15 record bytes [22, 37). *)
Lemma ver_wrange : forall E a, in_wrange E ver_regions a ->
  bv_unsigned (ew E 10) + 22 <= a < bv_unsigned (ew E 10) + 37.
Proof.
  intros E a (r & Hr & Ha). unfold ver_regions in Hr. cbn [In] in Hr.
  destruct Hr as [Hr | [Hr | [Hr | []]]]; subst r;
    unfold ver_frame, rec_region, pay_region in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
Qed.
(* One byte the arm wrote: the chunk at offset coff holds atom n in its i-th byte, and atom n holds
   the payload byte that P names. *)
Ltac vwb HCH HBAT Hzi P coff i n :=
  let aa := eval compute in (coff + i)%Z in
  let jn := eval compute in (Z.to_nat aa) in
  change (Z.of_nat jn) with aa;
  erewrite (ver_chunk_byte _ _ _ _ coff _ _ i aa HCH
              ltac:(cbn [In]; repeat first [left; reflexivity | right]));
  [ cbn [nth_error]; f_equal;
    erewrite (bab_byte _ _ _ n);
      [ rewrite P; rewrite ver_b8; reflexivity
      | vm_compute; reflexivity
      | exact HBAT
      | exact (proj1 (Z.leb_le 0 i) eq_refl) ]
  | exact Hzi
  | reflexivity ].

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
(* An shent over the arm's base atom 16, as reac_identity_ingest.v's ing_shent gives one over 32. *)
Lemma ver_shent : forall (W : world SEGS) (m : word -> option byte) E (n : nat) a len,
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len ->
  ew E 16 = Z_to_bv 64 SB_ING -> ew E n = Z_to_bv 64 a -> 4096 <= a -> a + len <= 2 ^ 47 -> 0 <= len ->
  (a + len <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a) ->
  shent_ok SEGS VBx E (mrestrict (w_H W) m) (mkSHE n 0 len).
Proof.
  intros W m E n a len Hra E16 En Ha0 Ha1 Hl Happ.
  apply (shent_ok_of_range SEGS (w_H W) m E VBx n a len a 0 len Hra).
  - unfold VBx. rewrite (U_atom E 16 SB_ING E16) by (unfold SB_ING; lia). reflexivity.
  - exact (U_atom E n a En ltac:(lia)).
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
Qed.
Theorem pb_ting_seg_ver : ting_seg_ver B.
Proof.
  unfold ting_seg_ver.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb regsT memT mdT
    HARM Had Hlen8.
  unfold ing_arm_at in HARM.
  destruct HARM as (HJ & Hra & Hra4 & Hid & Hadr & Hp & Hlenr & Hal16 & Hlo & Hhi & Hpl & HNR &
    HREC & HPAY & Hev & Hlive & HJT & T10 & T12 & T13 & T16 & T2 & T1 & Hcs & Mra & Ms0 & Ms1 &
    KEEPT & GROWT).
  subst ad.
  assert (Hz01 : 0 <= 0 < 2) by lia.
  assert (Hz11 : 0 <= 1 < 2) by lia.
  assert (Hz1 : 0 <= 0 < 1) by lia.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ing_sp B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi) as Hsp.
  pose proof (ing_sp_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi) as Hceil.
  pose proof HJ as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & Hstatc & _).
  pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstatc as (Hsp0al & Hstk0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
  assert (Hslo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil0).
  assert (Hshi : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H470).
  pose proof HJT as (HART & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT & _).
  pose proof HREC as (HR1 & HR2 & HR3 & HR4 & HR5 & HR6 & HR7).
  assert (Hlen0 : 0 < len) by lia.
  destruct (ing_zones B LAWS STK sp0 FP ly S own lyc Sc W memc mdc (spZ regs) id idb p len pb
              HARc Hceil Hslo Hshi HREC HPAY Hlen0)
    as (Zi & Zp & Zpi & Zid0 & Zid1 & Zp0 & Zp1 & Zsp & bi & Li & Hbin & Hb1 & Hb2).
  assert (Zsp' : spZ regs <= id \/ id + 38 <= spZ regs - 4128)
    by (unfold INGEST_STK, ESTACK in Zsp; clear - Zsp; lia).
  assert (Hceil' : alloc_ceiling + 4128 <= spZ regs)
    by (unfold INGEST_STK, ESTACK in Hceil; clear - Hceil; lia).
  (* every record byte is off the image and off the callee's window *)
  assert (HRAP : forall a, id <= a < id + 38 ->
            ~ in_img SEGS a /\ ~ (spZ regs - INGEST_STK <= a < spZ regs) /\ 4096 <= a /\ a < 2 ^ 47)
    by (intros a Ha; exact (ting_rec_apart B LAWS STK sp0 FP ly S own lyc Sc W memc mdc (spZ regs)
                              id idb a HARc Hceil Hslo Hshi HREC Ha)).
  (* the record and the payload are off the shadow band *)
  assert (HAPR : id + 38 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= id).
  { destruct HR2 as [(cid & pos & Hin & Hr) | Hs].
    - pose proof (Hr id ltac:(lia)) as Hr0. unfold frame_rng, in_zr in Hr0. cbn [fst snd] in Hr0.
      pose proof (Hr (id + 37) ltac:(lia)) as Hr1. unfold frame_rng, in_zr in Hr1. cbn [fst snd] in Hr1.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (F0 & Fc & Fapp).
      pose proof (fs_frame_bytes_nonneg cid) as Hfb.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
    - unfold SHADOW_OFF in *. lia. }
  assert (HrqL : Li <= req_size Li)
    by (unfold req_size; destruct (Li =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
  assert (HAPP : p + 8 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= p).
  { destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc bi Li HARc Hbin) as (_ & H4096 & Hce & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
  (* ---- the environment -------------------------------------------------------------------------- *)
  remember (EV regsT regs pb) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsT (ver_extra regs pb)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (HAE0 : env_agree 32 (Ereg regsT (ver_extra regs pb)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 2 2%bv eq_refl); exact T2).
  assert (E10 : ew E 10 = Z_to_bv 64 id)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 10 10%bv eq_refl); exact T10).
  assert (E12 : ew E 12 = Z_to_bv 64 p)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 12 12%bv eq_refl); exact T12).
  assert (E16 : ew E 16 = Z_to_bv 64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 16 16%bv eq_refl); exact T16).
  assert (EXT : forall j, (j < 21)%nat -> ew E (32 + j) = nth j (ver_extra regs pb) (Z_to_bv 64 0))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (Hiel : length (ing_extra pb) = 18%nat)
    by (unfold ing_extra; cbn [length]; rewrite length_map, length_seq; reflexivity).
  assert (EP : forall j, (j < 17)%nat ->
            ew E (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j))).
  { intros j Hj. replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia.
    rewrite (EXT (Datatypes.S j) ltac:(lia)). unfold ver_extra.
    rewrite app_nth1 by (rewrite Hiel; lia). exact (ing_extra_pay pb j Hj). }
  assert (E50 : ew E 50 = getr regs 1).
  { replace 50%nat with (32 + 18)%nat by lia. rewrite (EXT 18%nat ltac:(lia)). unfold ver_extra.
    rewrite app_nth2 by (rewrite Hiel; lia). rewrite Hiel. reflexivity. }
  assert (E51 : ew E 51 = getr regs 8).
  { replace 51%nat with (32 + 19)%nat by lia. rewrite (EXT 19%nat ltac:(lia)). unfold ver_extra.
    rewrite app_nth2 by (rewrite Hiel; lia). rewrite Hiel. reflexivity. }
  assert (E52 : ew E 52 = getr regs 9).
  { replace 52%nat with (32 + 20)%nat by lia. rewrite (EXT 20%nat ltac:(lia)). unfold ver_extra.
    rewrite app_nth2 by (rewrite Hiel; lia). rewrite Hiel. reflexivity. }
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32)
    by (rewrite E2; apply unsigned_lit_small; lia).
  assert (Uid : bv_unsigned (ew E 10) = id) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (Up : bv_unsigned (ew E 12) = p) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (UR : forall w : word, 0 <= bv_unsigned w < 2 ^ 64) by (exact u64_range).
  (* the payload bytes are there at memT: they are not in the callee's frame *)
  assert (HPB : mbytes_at SEGS (mrestrict (w_H W) memT) p pb).
  { apply (mbytes_kept _ memc memT p pb); [|exact (proj2 HPAY)].
    intros j Hj. rewrite Hpl in Hj. apply KEEPT; lia. }
  (* ---- the start state -------------------------------------------------------------------------- *)
  assert (HS : st_ok_pi SEGS VAL E ss_ver
                 (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + AF_ing_ver)) memT (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_ver. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold ver_regions. repeat apply Forall_cons; try apply Forall_nil.
      + unfold YP09.region_ok, ver_frame.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 8 8 (SOff 52 0) (bv_unsigned (getr regs 9)));
            [cbn [sv_denot]; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | exact (UR (getr regs 9)) | zside |].
          replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact Ms1.
        * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 16 8 (SOff 51 0) (bv_unsigned (getr regs 8)));
            [cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | exact (UR (getr regs 8)) | zside |].
          replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact Ms0.
        * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 24 8 (SOff 50 0) (bv_unsigned (getr regs 1)));
            [cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | exact (UR (getr regs 1)) | zside |].
          replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact Mra.
      + apply (rec_region_ok E _ id 22 37 Uid ltac:(lia) ltac:(lia)).
        intros o Ho. apply (apresent_writable SEGS). apply GROWT.
        exact (proj2 (HR4 (id + o) ltac:(lia))).
      + apply (pay_region_ok E _ p pb 8 ltac:(lia) ltac:(rewrite Hpl; lia) E12 ltac:(lia)
                 ltac:(lia) EP HPB).
    - apply pairwise_disjoint_of_extents.
      unfold ver_regions, ver_frame, rec_region, pay_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite Usp, Uid, Up.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      assert (H8 : Z.of_nat 8 = 8) by reflexivity. rewrite H8.
      clear - Zsp' Zpi Zid0 Zid1 Zp0 Zp1 Hsp Hceil' Hlen8.
      repeat split; lia.
    - split; [|split; exact I]. cbn [ver_facts f_atoms atoms_ok].
      assert (HBY : forall j, (j < 17)%nat -> 0 <= bv_unsigned (ew E (33 + j)) < 256).
      { intros j Hj. rewrite (EP j Hj). unfold RcIdentModel.bz.
        pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb pb j)) as Hbb.
        change (bv_modulus 8) with 256 in Hbb.
        rewrite unsigned_lit_small by lia. lia. }
      repeat match goal with |- _ /\ _ => split end; try exact I;
        unfold afact_ok; cbn [af_lo af_hi af_al2].
      + rewrite Usp. change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
        replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia.
        rewrite Z_mod_plus_full. exact Hal16.
      + rewrite Uid. change (2 ^ 3) with 8. split; [lia|]. split; [exact HR1 | lia].
      + rewrite Up. rewrite Z.pow_0_r, Z.mod_1_r. lia.
      + rewrite E16, unsigned_lit_small by (unfold SB_ING; lia).
        rewrite Z.pow_0_r, Z.mod_1_r. unfold SB_ING. lia.
      + pose proof (HBY 0%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 1%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 2%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 3%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 4%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 5%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 6%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia.
      + pose proof (HBY 7%nat ltac:(lia)) as H. rewrite Z.pow_0_r, Z.mod_1_r. cbn in H |- *. lia. }
  (* ---- the shadow entries ----------------------------------------------------------------------- *)
  assert (SHOK : sh_ok SEGS VBx SH_ver E (mrestrict (w_H W) memT)).
  { unfold SH_ver, sh_ok. repeat apply Forall_cons; try apply Forall_nil.
    - apply (ver_shent W memT E 10 id 38); [| exact E16 | exact E10 | lia | lia | lia | exact HAPR].
      eapply (range_addressable_kept_win (aview SEGS (w_H W) memc) _ (spZ regs - 32) (spZ regs) id 38);
        [| unfold kHighShadowEnd; lia | lia | lia | exact HR5].
      intros s Hs Hns. apply KEEPT; lia.
    - apply (ver_shent W memT E 12 p 8); [| exact E16 | exact E12 | lia | lia | lia | exact HAPP].
      exact (range_addressable_of_block SEGS B LAWS lyc Sc W memT mdT bi Li p 8 HART Hbin
               ltac:(lia) ltac:(lia)). }
  (* ---- the run ---------------------------------------------------------------------------------- *)
  change memT with (ms_mem (mkst regsT (Z_to_bv 64 (BASE + AF_ing_ver)) memT (seg_rom SEGS))) in HJT.
  paj_run_tok RUN HS HJT SHOK Bspan_ING.
  { change (ss_mem ss_ver) with ver_regions. unfold ver_regions.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi ver_frame]; lia|].
    eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat id);
      [ reflexivity | exact Uid
      | cbn [YP09.r_wlo YP09.r_whi rec_region]; intros a Ha;
        exact (proj1 (HR4 a ltac:(clear - Ha; lia))) | ].
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi pay_region]; lia|].
    apply awr_ok_nil. }
  (* ---- the state at the ret --------------------------------------------------------------------- *)
  (* what the run kept: it wrote only the 15 record bytes *)
  assert (KEPTM : forall a, 0 <= a < 2 ^ 64 -> ~ (id + 22 <= a < id + 37) ->
            mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H W) memT) a).
  { intros a Ha Hw. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    intros Hin. apply Hw. pose proof (ver_wrange E (bv_unsigned (Z_to_bv 64 a)) Hin) as Hr.
    rewrite Uid, unsigned_lit_small in Hr by (clear - Ha; lia). exact Hr. }
  assert (KEPTJ : forall j, ((j <? 22) || (j =? 37))%nat%bool = true ->
            mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (id + Z.of_nat j) = nth_error idb j).
  { intros j Hj.
    assert (Hjb : (j < 22 \/ j = 37)%nat)
      by (apply orb_true_iff in Hj as [Hq|Hq];
          [left; apply Nat.ltb_lt; exact Hq | right; apply Nat.eqb_eq; exact Hq]).
    rewrite (KEPTM (id + Z.of_nat j) ltac:(clear - Hjb Zid0 Zid1; lia) ltac:(clear - Hjb; lia)).
    rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc memT (id + Z.of_nat j)
               (KEEPT (id + Z.of_nat j) ltac:(clear - Hjb Zid0 Zid1; lia)
                  ltac:(clear - Hjb Zsp' Hceil' Zid0 Zid1; lia))).
    unfold RcIdentModel.ID_SIZE in HR6.
    exact (HR7 j ltac:(clear - Hjb HR6; lia)). }
  assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
            ~ ting_E id p len a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hw He.
    transitivity (aview SEGS (w_H W) memT a); [| exact (KEEPT a Ha Hw)].
    unfold aview. rewrite KEPTM; [reflexivity | exact Ha |].
    intros Hr. apply He. unfold ting_E. split; [exact HNR | clear - Hr; lia]. }
  (* the environment of the final state *)
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (EfLow : forall n, (n < 512)%nat -> ew Ex n = ew E n) end.
  { intros n Hn. repeat (rewrite ew_ewset_other by (clear - Hn; lia)). reflexivity. }
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (HAEf : env_agree 32 (Ereg regsT (ver_extra regs pb)) Ex) end.
  { split; [intros n Hn; rewrite (EfLow n ltac:(clear - Hn; lia)); exact (proj1 HAE0 n Hn)
           | repeat rewrite ed_ewset; exact (proj2 HAE0)]. }
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (PF : forall j, (j < 17)%nat ->
              ew Ex (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j))) end.
  { intros j Hj. rewrite (EfLow (33 + j)%nat ltac:(clear - Hj; lia)). exact (EP j Hj). }
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (UidF : bv_unsigned (ew Ex 10) = id) end.
  { rewrite (EfLow 10%nat ltac:(clear - HNR; lia)). exact Uid. }
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (HBAT : forall q, (33 <= q <= 40)%nat -> 0 <= bv_unsigned (ew Ex q) < 256) end.
  { intros q Hq. replace q with (33 + (q - 33))%nat by (clear - Hq; lia).
    rewrite (PF (q - 33)%nat ltac:(clear - Hq; lia)). unfold RcIdentModel.bz.
    pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb pb (q - 33))) as Hbb.
    change (bv_modulus 8) with 256 in Hbb.
    rewrite unsigned_lit_small by (clear - Hbb; lia). exact Hbb. }
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (P33 : ew Ex 33 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 0)))
      by exact (PF 0%nat ltac:(clear - HNR; lia));
    assert (P34 : ew Ex 34 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 1)))
      by exact (PF 1%nat ltac:(clear - HNR; lia));
    assert (P35 : ew Ex 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 2)))
      by exact (PF 2%nat ltac:(clear - HNR; lia));
    assert (P36 : ew Ex 36 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 3)))
      by exact (PF 3%nat ltac:(clear - HNR; lia));
    assert (P37 : ew Ex 37 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 4)))
      by exact (PF 4%nat ltac:(clear - HNR; lia));
    assert (P38 : ew Ex 38 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 5)))
      by exact (PF 5%nat ltac:(clear - HNR; lia));
    assert (P39 : ew Ex 39 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 6)))
      by exact (PF 6%nat ltac:(clear - HNR; lia));
    assert (P40 : ew Ex 40 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 7)))
      by exact (PF 7%nat ltac:(clear - HNR; lia)) end.
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (st_ok_pi_region_nth Ex _ _ 1%nat _ HSx
                  ltac:(cbn [ss_mem nth_error]; reflexivity)) as HRR end.
  destruct HRR as (_ & _ & _ & HCH).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCH.
  cbn [ms_mem restrict] in HCH.
  rewrite UidF in HCH.
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  unfold treac_identity_ingest_post.
  split; [reflexivity|].
  exists (ms_regs ms), (ms_mem ms). eexists.
  split; [cbn [ms_regs]; rewrite R1, E50, Hra; reflexivity|].
  split; [unfold EV_INGEST; rewrite Z.add_0_r;
          apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJT|].
  split.
  { intros q Hq.
    destruct (Z.eq_dec q 2) as [Hq2|Hq2].
    { subst q. replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R2, Usp. replace (spZ regs - 32 + 32) with (spZ regs) by (clear - Hsp; lia).
      unfold spZ. apply Z_to_bv_bv_unsigned. }
    destruct (Z.eq_dec q 8) as [Hq8|Hq8].
    { subst q. replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R8. exact E51. }
    destruct (Z.eq_dec q 9) as [Hq9|Hq9].
    { subst q. replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R9. exact E52. }
    rewrite <- (Hcs q Hq Hq2).
    eapply (regs_kept_of_st_ok_pi _ _ _ _ _ ING_KEPT HS HAEf ltac:(vm_compute; reflexivity)).
    apply in_kept_of; [unfold acallee_saved in Hq; clear - Hq; lia|].
    assert (Hc : q = 3 \/ q = 4 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
                 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
      by (unfold acallee_saved in Hq; clear - Hq Hq2 Hq8 Hq9; lia).
    clear - Hc.
    repeat (destruct Hc as [Hc | Hc]; [try subst q; vm_compute; reflexivity |]).
    try subst q; vm_compute; reflexivity. }
  split.
  { rewrite R10. unfold reac_identity_ingest_c.ingest_ret. rewrite HNR.
    rewrite (RcIdentLib.ING_ver idb pb ltac:(rewrite Hpl; clear - Hlen8 Hlenr; lia)). reflexivity. }
  split.
  { eapply (ing_kept_of B LAWS lyc Sc W memc mdc (ms_mem ms) (spZ regs) (ting_E id p len)
              HARc Hceil ltac:(clear - Hsp; lia)).
    - exact KEEPA.
    - intros a Hpa. eapply apresent_grows; [exact HG | exact (GROWT a Hpa)].
    - intros a Ha.
      pose proof HJT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
      apply HpF. clear - Ha Hlo Hhi. unfold INGEST_STK, ESTACK in *. lia.
    - intros a Hi He. destruct He as (_ & Ha). exact (proj1 (HRAP a Ha) Hi). }
  (* ---- the record the arm leaves ----------------------------------------------------------------- *)
  intros _.
  rewrite (RcIdentLib.ING_ver idb pb ltac:(rewrite Hpl; clear - Hlen8 Hlenr; lia)). cbn [snd].
  rewrite !RcIdentLib.le16_be16.
  unfold RcIdentModel.OFF_RAW, RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR,
    RcIdentModel.OFF_PATCH, RcIdentModel.OFF_HAS_VER.
  unfold RcIdentModel.ID_SIZE in HR6.
  do 38 (destruct idb as [|?bb idb]; [cbn [length] in HR6; clear - HR6; lia|]).
  destruct idb as [|?bb idb]; [|cbn [length] in HR6; clear - HR6; lia].
  cbn [RcIdentModel.upd firstn skipn app length Nat.add].
  intros j Hj. cbn [length] in Hj.
  do 22 (destruct j as [|j];
         [ erewrite KEPTJ; [cbn [nth_error]; reflexivity | reflexivity] | ]).
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P36 22 0 36%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P35 22 1 35%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P38 24 0 38%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P37 24 1 37%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P40 26 0 40%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P39 26 1 39%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P33 28 0 33%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P34 28 1 34%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P35 30 0 35%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P36 30 1 36%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P37 32 0 37%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P38 32 1 38%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz01 P39 34 0 39%nat | ].
  destruct j as [|j]; [ vwb HCH HBAT Hz11 P40 34 1 40%nat | ].
  destruct j as [|j].
  { (* id + 36: the literal 1 *)
    change (Z.of_nat 36) with 36.
    erewrite (ver_chunk_byte _ _ _ _ 36 _ _ 0 36 HCH
                ltac:(cbn [In]; repeat first [left; reflexivity | right]));
      [ cbn [nth_error]; f_equal; cbn [sv_denot]; unfold byte_of_word;
        rewrite unsigned_lit_small by (clear - HNR; lia); reflexivity
      | exact Hz1 | reflexivity ]. }
  destruct j as [|j]; [ erewrite KEPTJ; [cbn [nth_error]; reflexivity | reflexivity] | ].
  exfalso. clear - Hj. lia.
Qed.
End h.
End f.
End d.
