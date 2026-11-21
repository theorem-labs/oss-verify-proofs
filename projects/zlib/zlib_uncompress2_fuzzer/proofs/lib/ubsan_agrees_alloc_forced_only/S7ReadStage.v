(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  MmapSim AllocSim StreamSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame MemSplit RefMemcpyLib
  LibKnowFrame LibKnowXfer S7ReadBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require S7Wseg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition CEIL : Z := 0x7fffff800000.
Definition SWIN : Z := 4294967296.
Definition cap_of (j : Z) : Z := 65536 * 2 ^ j.
Definition held_of (j : Z) : Z := 65536 * 2 ^ (j - 1).
Definition nb_of (j : Z) : Z := cap_of j + 4096.
Definition off_of (j : Z) : Z := 16 * (j + 2).
Definition W_of (j : Z) : Z := nb_of j + 4064.
Definition res_of (j : Z) : Z := 4060 - 16 * j.
Definition curslot (j : Z) : Z := if Z.odd j then 4160 else 4120.
Definition freeslot (j : Z) : Z := if Z.odd j then 4120 else 4160.
Definition hb (j : Z) : nat := (2 * Z.to_nat (j - 1))%nat.
Definition cb (j : Z) : nat := (2 * Z.to_nat (j - 1) + 1)%nat.


Definition bx (k : Z) : expr := EAlu ALU_ADD (EVar 5) (ELit k).
Definition BA (k : Z) : saddr := SA (EVar 5) k.

Definition sr_LOOP (buf : expr) (len cap : Z) : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x72f80; J 5; J 6; J 7;
   ELit 2; buf; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; ELit len; ELit 3; ELit cap; ELit RS; buf;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
Definition sr_MID (buf : expr) (len cap : Z) : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x72f80; J 5; J 6; J 7;
   ELit 2; buf; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; ELit len; ELit 3; ELit cap; ELit RS; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
Definition sr_HALF (j : Z) : list expr := sr_MID (bx (off_of j)) (held_of j) (cap_of j).
Definition sr_FULL (j : Z) : list expr := sr_LOOP (bx (off_of j)) (cap_of j) (cap_of j).

Definition kn_static (j : Z) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) 6144513;
   KRange (EVar 1) 0x7fff80000000 0x800000400000;
   KAlign (EVar 2) 4096; KRange (EVar 2) 0x1000 (CEIL - 8192);
   KDisj (SA (EVar 0) (-8388608)) SWIN (SA (EVar 2) 0) 8192;
   KDisj (LA 0x10000) 0x840d0 (SA (EVar 2) 0) 8192;
   KWr (SA (EVar 2) 4096) 4096;
   KAlign (EVar 5) 4096; KRange (EVar 5) 0x94000 (CEIL - nb_of j);
   KDisj (SA (EVar 0) (-8388608)) SWIN (BA 0) (nb_of j);
   KWr (BA 0) (nb_of j);
   KDisj (BA 0) (nb_of j) (SA (EVar 2) 4096) 4096;
   KWr (LA 0x22000) 0x72000;
   KImg 0x10000 0x22000;
   KImg 0 0x1000].

Definition kn_ctx (j : Z) : list kentry :=
  [KWord (LA 0x72edc) 4 (EVar 6);
   KWord (LA 0x931e8) 8 (EVar 7);
   KWord (LA 0x9320b) 1 (ELit 0);
   KWord (LA 0x93238) 8 (ELit 4096);
   KWord (LA 0x93278) 4 (ELit 0);
   KWord (LA 0x93280) 8 (EVar 8);
   KWord (LA 0x93288) 4 (ELit 1);
   KWord (LA 0x9328c) 4 (ELit (1 + j));
   KWord (LA 0x93290) 8 (mbx (freeslot j));
   KWord (LA 0x93298) 8 (mbx 4200);
   KWord (LA 0x932a0) 8 (ELit 99);
   KWord (LA 0x932a8) 8 (ELit 0);
   KWord (LA 0x932b8) 8 (mbx 4096);
   KWord (LA 0x932c0) 8 (mbx 4096);
   KWord (LA 0x932c8) 8 (mbx 8192);
   KWord (LA 0x93430) 8 (ELit 0);
   KWord (LA 0x935b0) 8 (ELit 0);
   KWord (LA 0x93610) 1 (ELit (1 + 2 * j))].

Definition kn_meta (j : Z) : list kentry :=
  [KWord (MBA 4096) 8 (EVar 8); KWord (MBA 4104) 8 (ELit 0); KWord (MBA 4112) 4 (ELit 101);
   KWord (MBA (curslot j)) 8 (ELit 0);
   KWord (MBA (curslot j + 8)) 8 (ELit 0);
   KWord (MBA (curslot j + 16)) 8 (EVar 5);
   KWord (MBA (curslot j + 24)) 4 (ELit 0);
   KWord (MBA (curslot j + 28)) 4 (ELit 0);
   KWord (MBA (curslot j + 32)) 8 (ELit (W_of j));
   KWord (MBA (freeslot j)) 8 (mbx (freeslot j));
   KWord (MBA (freeslot j + 8)) 8 (mbx (freeslot j));
   KWord (MBA (freeslot j + 16)) 8 (ELit 0);
   KWord (MBA (freeslot j + 24)) 8 (ELit 0);
   KWord (MBA (freeslot j + 32)) 8 (ELit 0);
   KZero (MBA 4200) (ELit 3992)].

Definition kn_hdr (j : Z) : list kentry :=
  [KWord (BA 0) 8 (mbx (curslot j));
   KZero (BA 8) (ELit 5);
   KWord (BA 13) 1 (ELit 224);
   KWord (BA 14) 2 (ELit (j + 1));
   KWord (BA (off_of j - 4)) 1 (ELit 0);
   KWord (BA (off_of j - 3)) 1 (ELit 160);
   KWord (BA (off_of j - 2)) 2 (ELit (j + 1))].
Definition kn_ftr (j : Z) : list kentry :=
  [KWord (BA (off_of j + cap_of j)) 1 (ELit 0);
   KWord (BA (nb_of j - 9)) 1 (ELit 0);
   KWord (BA (nb_of j - 8)) 4 (ELit (res_of j));
   KZero (BA (nb_of j - 4)) (ELit 4)].

Definition kn_buf_half (j : Z) : list kentry :=
  kn_hdr j ++ [KBlob (BA (off_of j)) (ELit (held_of j)) (hb j)] ++ kn_ftr j.
Definition kn_buf_full (j : Z) : list kentry :=
  kn_hdr j ++ [KBlob (BA (off_of j)) (ELit (held_of j)) (hb j);
               KBlob (BA (off_of j + held_of j)) (ELit (held_of j)) (cb j)] ++ kn_ftr j.

Definition kn_HALF (j : Z) : list kentry := kn_static j ++ kn_ctx j ++ kn_meta j ++ kn_buf_half j.
Definition kn_FULL (j : Z) : list kentry := kn_static j ++ kn_ctx j ++ kn_meta j ++ kn_buf_full j.



Definition pref (n : Z) (l : list byte) : list byte := firstn (Z.to_nat n) l.
Definition dropz (n : Z) (l : list byte) : list byte := skipn (Z.to_nat n) l.
Arguments pref : simpl never.
Arguments dropz : simpl never.
Global Strategy 1000 [pref dropz].

Lemma pref_length : forall n l, (0 <= n)%Z -> Z.of_nat (length (pref n l)) = Z.min n (Z.of_nat (length l)).
Proof. intros n l Hn. unfold pref. rewrite length_firstn. lia. Qed.

Lemma dropz_length : forall n l, (0 <= n)%Z -> Z.of_nat (length (dropz n l)) = Z.max 0 (Z.of_nat (length l) - n).
Proof. intros n l Hn. unfold dropz. rewrite length_skipn. lia. Qed.

Lemma file_read_pref : forall data (off cnt : Z),
  (0 <= off < 2 ^ 64)%Z -> (0 <= cnt < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = pref cnt (dropz off data).
Proof.
  intros data off cnt Ho Hc. rewrite file_read_unguarded. unfold pref, dropz, word_to_nat. rewrite !u_small by lia. reflexivity.
Qed.


Lemma pref_app : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  pref a l ++ pref b (dropz a l) = pref (a + b) l.
Proof.
  intros a b l Ha Hb. unfold pref, dropz. rewrite Z2Nat.inj_add by lia. rewrite firstn_skipn_comm.
  transitivity (firstn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l) ++ skipn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l)).
  - f_equal. rewrite firstn_firstn. f_equal. lia.
  - apply firstn_skipn.
Qed.


Lemma pref_all : forall n l, (Z.of_nat (length l) <= n)%Z -> pref n l = l.
Proof. intros n l H. unfold pref. apply firstn_all2. lia. Qed.

Definition gsize (m : nat) : Z := 65536 * 2 ^ (Z.of_nat m).
Definition gblobs (content : list byte) (k : nat) : list byte :=
  if Nat.even k then pref (gsize (Nat.div2 k)) content
  else pref (gsize (Nat.div2 k)) (dropz (gsize (Nat.div2 k)) content).


Definition vals_RD (sp0 p1 mb gm : word) (L : Z) (B e cw sw : word) (extra : list word) : list word :=
  [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; cw; sw; Z_to_bv 64 0] ++ extra.

Definition ENV_RD (sp0 p1 mb gm : word) (L : Z) (B e cw sw : word) (extra : list word) (content : list byte) : env :=
  Env (vals_ev (vals_RD sp0 p1 mb gm L B e cw sw extra)) (gblobs content).

Definition rd_cell (i : Z) : Prop :=
  (0x22e79 <= i < 0x32e79)%Z \/
  (0x72edc <= i < 0x72ee0)%Z \/ (0x9328c <= i < 0x932a8)%Z \/ (0x93430 <= i < 0x93438)%Z
  \/ (0x935b0 <= i < 0x935b8)%Z \/ (0x93610 <= i < 0x93611)%Z.

Definition pres (M0 M : word -> option byte) (sp0 : word) : Prop :=
  forall x : word,
    ((0x10000 <= bv_unsigned x < 0x94000)%Z /\ ~ rd_cell (bv_unsigned x))
    \/ (bv_unsigned sp0 - 128 <= bv_unsigned x)%Z ->
    M x = M0 x.

Lemma pres_refl : forall M sp0, pres M M sp0.
Proof. intros M sp0 x _. reflexivity. Qed.

Lemma pres_trans : forall M0 M1 M2 sp0, pres M0 M1 sp0 -> pres M1 M2 sp0 -> pres M0 M2 sp0.
Proof. intros M0 M1 M2 sp0 A B x Hx. rewrite (B x Hx). apply A, Hx. Qed.



Definition inb (lo hi k w : Z) : bool := Z.leb lo k && Z.leb (k + w) hi.

Definition store_pres_ok (kn : list kentry) (b : expr) (k w : Z) : bool :=
  match b with
  | ELit 0 => Z.leb 0 w && (inb 0x22e79 0x32e79 k w || inb 0x72edc 0x72ee0 k w || inb 0x9328c 0x932a8 k w
              || inb 0x93430 0x93438 k w || inb 0x935b0 0x935b8 k w || inb 0x93610 0x93611 k w)
  | EVar 0 => Z.leb (-6144513) k && Z.leb (k + w) (-128) && Z.leb 0 w
  | _ => match base_range kn b with
         | Some (lo, hi) =>
             (Z.leb 0x94000 (lo + k) || (Z.leb 0 (lo + k) && ranges_apart kn (ELit 0) 0x10000 0x840d0 b k w))
             && ranges_apart kn (EVar 0) (-8388608) SWIN b k w
             && Z.leb (hi + k + w) (0x7fff80000000 - 8388608 + SWIN) && Z.leb 0 w
         | None => false
         end
  end.

Fixpoint log_pres_ok (kn : list kentry) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE (SA b k) w _ :: rest => store_pres_ok kn b k (Z.of_nat w) && log_pres_ok kn rest
  end.

Lemma inb_sound : forall lo hi k w, inb lo hi k w = true -> (lo <= k /\ k + w <= hi)%Z.
Proof. intros lo hi k w H. unfold inb in H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia. Qed.

Lemma store_pres_ok_sound {RCa1 : RunCtx}  : forall E M kn b k w sp0,
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn -> ev E 0 = sp0 ->
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  store_pres_ok kn b k w = true ->
  let ua := bv_unsigned (adenot E (SA b k)) in
  (ua + w <= 2 ^ 64)%Z /\
  forall x : word,
    ((0x10000 <= bv_unsigned x < 0x94000)%Z /\ ~ rd_cell (bv_unsigned x)) \/ (bv_unsigned sp0 - 128 <= bv_unsigned x)%Z ->
    (bv_unsigned x < ua \/ ua + w <= bv_unsigned x)%Z.
Proof.
  intros E M kn b k w sp0 HK H0 Hsp Hb. unfold store_pres_ok in Hb.
  unfold adenot, v_addi. cbn [a_base a_off].
  Ltac other_base HK E k w H0 :=
      lazymatch goal with Hb : context [base_range ?kn ?bb] |- _ =>
        let lo := fresh "rlo" in let hi := fresh "rhi" in let HR := fresh "HR" in
        destruct (base_range kn bb) as [[lo hi]|] eqn:HR; [|discriminate];
        pose proof (base_range_sound (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ kn bb lo hi HK HR) as [? ?];
        apply andb_prop in Hb as [Hb ?Hw]; apply andb_prop in Hb as [Hb ?Hb2]; apply andb_prop in Hb as [Hb ?HbD];
        apply Z.leb_le in Hw; apply Z.leb_le in Hb2; unfold SWIN in Hb2;
        let HbS := fresh "HbS" in
        pose proof (ranges_apart_sound (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ kn _ _ _ _ _ _ HK HbD) as HbS; clear HbD;
        unfold estart in HbS; cbn [a_base a_off] in HbS; change (edenot E (EVar 0)) with (ev E 0) in HbS; rewrite H0 in HbS; unfold SWIN in HbS;
        let Hb1 := fresh "Hb1" in
        assert (Hb1 : (0 <= lo + k)%Z /\
                      (0x94000 <= lo + k \/ estart E (SA (ELit 0) 0x10000) + 0x840d0 <= estart E (SA bb k) \/ estart E (SA bb k) + w <= estart E (SA (ELit 0) 0x10000))%Z)
          by (apply orb_prop in Hb; destruct Hb as [Hb|Hb];
              [ apply Z.leb_le in Hb; lia
              | apply andb_prop in Hb as [?Hb0 Hb]; apply Z.leb_le in Hb0; split; [exact Hb0|];
                right; eapply ranges_apart_sound; [exact HK | exact Hb] ]);
        clear Hb; unfold estart in Hb1; cbn [a_base a_off] in Hb1; rewrite ?edenot_lit0 in Hb1;
        try (change (bv_unsigned (edenot _ (ELit 0))) with 0%Z in Hb1)
      end.
  destruct b as [z|n| | | | | |].
  1:{ destruct z as [|pz|nz].
      2,3: other_base HK E k w H0; rewrite u_small by lia; split; [lia|]; intros x Hx; lia.
      cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
      apply andb_prop in Hb as [Hw Hb]. apply Z.leb_le in Hw.
      assert (HH : ((0x22e79 <= k /\ k + w <= 0x32e79) \/ (0x72edc <= k /\ k + w <= 0x72ee0) \/ (0x9328c <= k /\ k + w <= 0x932a8) \/ (0x93430 <= k /\ k + w <= 0x93438)
                   \/ (0x935b0 <= k /\ k + w <= 0x935b8) \/ (0x93610 <= k /\ k + w <= 0x93611))%Z).
      { repeat (apply orb_prop in Hb; destruct Hb as [Hb|Hb]); try apply inb_sound in Hb; (first [solve [liafast_keep_section; tauto] | tauto]). }
      assert (Hk : (0 <= k /\ k + w <= 0x94000)%Z) by lia.
      rewrite u_small by lia. split; [lia|]. intros x Hx. unfold rd_cell in Hx. lia. }
  1:{ destruct n as [|n'].
      + cbn [edenot]. rewrite H0. apply andb_prop in Hb as [Hb Hw]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. apply Z.leb_le in Hw.
        rewrite u_small by lia. split; [lia|]. intros x Hx. lia.
      + other_base HK E k w H0. rewrite u_small by lia. split; [lia|]. intros x Hx. lia. }
  all: other_base HK E k w H0; rewrite u_small by lia; split; [lia|]; intros x Hx; lia.
Qed.

Lemma pres_mem_denot {RCa1 : RunCtx}  : forall E M kn log sp0,
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn -> ev E 0 = sp0 ->
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  log_pres_ok kn log = true ->
  pres M (mem_denot E M log) sp0.
Proof.
  intros E M kn log sp0 HK H0 Hsp. induction log as [|[[b k] w v] rest IH]; intros Hl.
  - apply pres_refl.
  - cbn [log_pres_ok] in Hl. apply andb_prop in Hl as [H1 H2].
    cbn [mem_denot]. intros x Hx.
    pose proof (store_pres_ok_sound E M kn b k (Z.of_nat w) sp0 HK H0 Hsp H1) as [Hnw Hout].
    rewrite MemSplit.wbytes_outside.
    + apply IH; assumption.
    + rewrite length_N_to_le_bytes. exact Hnw.
    + rewrite length_N_to_le_bytes. apply Hout. exact Hx.
Qed.

Lemma pres_mem_denot_trans {RCa1 : RunCtx}  : forall E M0 M kn log sp0,
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn -> ev E 0 = sp0 ->
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  log_pres_ok kn log = true ->
  pres M0 M sp0 -> pres M0 (mem_denot E M log) sp0.
Proof.
  intros. eapply pres_trans; [eassumption|]. eapply pres_mem_denot; eassumption.
Qed.

Definition vm_stage (VM : VmMaps) (sp0 mb B : word) (nb : Z) : Prop :=
  vm_reserved VM = segments_reserved RSEGS
  /\ vm_limit VM = source_alloc_limit
  /\ vm_init_sp VM = sp0
  /\ exists rest,
      vm_maps VM = (B, Z_to_bv 64 nb) :: rest
      /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 2 ^ 30)%Z
                          /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) rest
      /\ (length rest <= 8)%nat
      /\ (live_bytes rest <= 2 ^ 20)%Z
      /\ (exists p, In p rest /\ (bv_unsigned (fst p) <= bv_unsigned mb + 4096)%Z
                             /\ (bv_unsigned mb + 8192 <= bv_unsigned (fst p) + bv_unsigned (snd p))%Z)
      /\ Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned B
                          \/ bv_unsigned B + nb <= bv_unsigned (fst p))%Z) rest
      /\ seps rest.



Definition loop_at {RCa1 : RunCtx}  (sr : list expr) (kn : list kentry) (sp0 p1 mb gm : word) (L : Z) (B e cw sw : word) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  exists extra : list word, length extra = 32%nat
      /\ regs_ok (ENV_RD sp0 p1 mb gm L B e cw sw extra content) sr R
      /\ know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV_RD sp0 p1 mb gm L B e cw sw extra content) M kn.

Definition half {RCa1 : RunCtx}  (j : Z) (sp0 p1 mb gm : word) (L : Z) (B e cw sw : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) : Prop :=
  loop_at (sr_HALF j) (kn_HALF j) sp0 p1 mb gm L B e cw sw content R M
  /\ pres M0 M sp0
  /\ vm_stage VM sp0 mb B (nb_of j).

Definition full {RCa1 : RunCtx}  (j : Z) (sp0 p1 mb gm : word) (L : Z) (B e cw sw : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) : Prop :=
  loop_at (sr_FULL j) (kn_FULL j) sp0 p1 mb gm L B e cw sw content R M
  /\ pres M0 M sp0
  /\ vm_stage VM sp0 mb B (nb_of j).



Definition kn_POST (k : Z) : list kentry := kn_static k ++ kn_ctx k ++ kn_meta k ++
  [KWord (BA 0) 8 (mbx (curslot k)); KZero (BA 8) (ELit 5); KWord (BA 13) 1 (ELit 224);
   KWord (BA 14) 2 (ELit (k + 1)); KWord (BA (off_of k - 4)) 1 (ELit 0);
   KWord (BA (off_of k - 3)) 1 (ELit 160); KWord (BA (off_of k - 2)) 2 (ELit (k + 1));
   KWord (BA (off_of k + cap_of k)) 1 (ELit 0); KWord (BA (nb_of k - 9)) 1 (ELit 0);
   KWord (BA (nb_of k - 8)) 4 (ELit (res_of k)); KZero (BA (nb_of k - 4)) (ELit 4)].

Record read_post {RCa1 : RunCtx}  (k : Z) (sp0 p1 mb gm B e cw sw : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) : Prop := READ_POST {
  rk_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rk_gp : getr R 3 = Z_to_bv 64 0x10800;
  rk_tp : getr R 4 = Z_to_bv 64 0x72f80;
  rk_s0 : getr R 8 = Z_to_bv 64 2;
  rk_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned B + off_of k);
  rk_s2 : getr R 18 = p1;
  rk_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));
  rk_s4 : getr R 20 = Z_to_bv 64 3;
  rk_s5 : getr R 21 = Z_to_bv 64 (cap_of k);
  rk_s6 : getr R 22 = Z_to_bv 64 RS;
  rk_s7 : getr R 23 = Z_to_bv 64 0;
  rk_content : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (bv_unsigned B + off_of k)) (length content) = Some content;
  rk_pres : pres M0 M sp0;
  rk_know : exists extra : list word, length extra = 32%nat /\
      know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e cw sw extra content) M (kn_POST k);
  rk_vm : vm_stage VM sp0 mb B (nb_of k) }.
Arguments READ_POST {RCa1}.


Definition modelG (path : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) (off : Z) (V : VmMaps) : Model :=
  mkModelA (fds_file path (Z_to_bv 64 off)) V stdin0 fs0 None (Some tid) None.

Lemma modelG_read : forall path stdin0 fs0 tid off V (off' : word),
  with_fds (fd_insert (m_fds (modelG path stdin0 fs0 tid off V)) (Z_to_bv 64 3) (FdFile path off'))
           (modelG path stdin0 fs0 tid off V)
  = mkModelA (fds_file path off') V stdin0 fs0 None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma modelG_close : forall path stdin0 fs0 tid off V,
  with_fds (fd_remove (m_fds (modelG path stdin0 fs0 tid off V)) (Z_to_bv 64 3)) (modelG path stdin0 fs0 tid off V)
  = model_post V stdin0 fs0 tid.
Proof. intros. reflexivity. Qed.

Definition oom_leaf {RCa1 : RunCtx}  (sp0 : word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr R 3 = Z_to_bv 64 0x10800 /\ getr R 4 = Z_to_bv 64 0x72f80
  /\ pres M0 M sp0 /\ stack_writable M sp0.

Definition oom_branch {RCa1 : RunCtx}  (sp0 : word) (path : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word)
           (M0 : word -> option byte) (TOOM : TSet) : Prop :=
  forall R M off V, oom_leaf sp0 M0 R M ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x14b34) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (modelG path stdin0 fs0 tid off V)) TOOM.



Section LoopRegs.
  Variables (sp0 p1 mb gm : word) (L : Z) (B e cw sw : word) (content : list byte) (R : bvmap 5 word).
  Let E := ENV_RD sp0 p1 mb gm L B e cw sw (junk_vals R) content.



End LoopRegs.





Lemma wseg_data {RCa1 : RunCtx}  : wseg_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x22000) 466944 = true.
Proof.
  exact S7Wseg.data_window_wseg.
Qed.

Lemma data_store_ok {RCa1 : RunCtx}  : forall m a n,
  (0x22000 <= a)%Z -> (a + Z.of_nat n <= 0x94000)%Z -> store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) n = true.
Proof.
  intros m a n Ha Hn.
  eapply (store_ok_window (run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 0x22000) (Z_to_bv 64 a) 466944 n 0x22000 0x94000);
    [ apply u_small; lia | vm_cast_no_check (@eq_refl Z 0x94000%Z) | cbn; lia | apply wseg_data
    | rewrite u_small by lia; lia | rewrite u_small by lia; lia ].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
