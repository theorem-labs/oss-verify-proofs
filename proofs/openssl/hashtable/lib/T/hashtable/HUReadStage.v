(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require LedgerCfg RefNodes.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  MmapSim AllocSim StreamSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame MemSplit RefMemcpyLib
  LibKnowFrame LibKnowXfer HUTargetPre HUReadBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CEIL : Z := 0x7fffff800000.                 (* [comment removed for export] *)
Definition HUGE : Z := 18446744073709551616.           (* [comment removed for export] *)
Definition cap_of (j : Z) : Z := 65536 * 2 ^ j.
Definition held_of (j : Z) : Z := 65536 * 2 ^ (j - 1).
Definition nb_of (j : Z) : Z := cap_of j + 4096.        (* [comment removed for export] *)
Definition maplen_of (j : Z) : Z := 16 * 2 ^ j + 1.
Definition off_of (j : Z) : Z := 16 * (j + 2).          (* [comment removed for export] *)
Definition W_of (j : Z) : Z := nb_of j + 4064.          (* [comment removed for export] *)
Definition res_of (j : Z) : Z := 4060 - 16 * j.         (* [comment removed for export] *)
Definition curslot (j : Z) : Z := if Z.odd j then 4160 else 4120.   (* [comment removed for export] *)
Definition freeslot (j : Z) : Z := if Z.odd j then 4120 else 4160.
(* [comment removed for export] *)
Definition hb (j : Z) : nat := (2 * Z.to_nat (j - 1))%nat.
Definition cb (j : Z) : nat := (2 * Z.to_nat (j - 1) + 1)%nat.
Definition fb (j : Z) : nat := (2 * Z.to_nat j)%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bx (k : Z) : expr := EAlu ALU_ADD (EVar 5) (ELit k).     (* [comment removed for export] *)
Definition BA (k : Z) : saddr := SA (EVar 5) k.

(* [comment removed for export] *)
Definition sr_LOOP (buf : expr) (len cap : Z) : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x331ae8; J 5; J 6; J 7;
   ELit 2; buf; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; ELit len; ELit 3; ELit cap; ELit STAGE; buf;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_MID (buf : expr) (len cap : Z) : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x331ae8; J 5; J 6; J 7;
   ELit 2; buf; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; ELit len; ELit 3; ELit cap; ELit STAGE; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
Definition sr_HALF (j : Z) : list expr := sr_MID (bx (off_of j)) (held_of j) (cap_of j).
Definition sr_FULL (j : Z) : list expr := sr_LOOP (bx (off_of j)) (cap_of j) (cap_of j).

(* [comment removed for export] *)
Definition kn_static (j : Z) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 1) 0x7fff80000000 0x800000400000;
   KAlign (EVar 2) 4096; KRange (EVar 2) 0x1000 (CEIL - 8192);
   KDisj (LA 0x10000) 0x344000 (SA (EVar 2) 0) 8192;     (* [comment removed for export] *)
   KDisj (SA (EVar 0) (-8388608)) HUGE (SA (EVar 2) 0) 8192;   (* [comment removed for export] *)
   KWr (SA (EVar 2) 4096) 4096;
   KAlign (EVar 5) 4096; KRange (EVar 5) 0x354000 (CEIL - nb_of j);
   KDisj (SA (EVar 0) (-8388608)) HUGE (BA 0) (nb_of j);       (* [comment removed for export] *)
   KWr (BA 0) (nb_of j);
   KDisj (BA 0) (nb_of j) (SA (EVar 2) 4096) 4096;
   KWr (LA 0x31e000) 0x36000;                            (* [comment removed for export] *)
   KImg 0x10000 0x31e000;
   KImg 0 0x1000].                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kn_ctx (j : Z) : list kentry :=
  [KWord (LA 0x331a44) 4 (EVar 6);              (* [comment removed for export] *)
   KWord (LA 0x351b28) 8 (EVar 7);              (* [comment removed for export] *)
   KWord (LA 0x351d7b) 1 (ELit 0);              (* [comment removed for export] *)
   KWord (LA 0x351da8) 8 (ELit 4096);           (* [comment removed for export] *)
   KWord (LA 0x351de8) 4 (ELit 0);              (* [comment removed for export] *)
   KWord (LA 0x353250) 4 (ELit 0);              (* [comment removed for export] *)
   KWord (LA 0x351df0) 8 (EVar 8);              (* [comment removed for export] *)
   KWord (LA 0x351df8) 4 (ELit 1);              (* [comment removed for export] *)
   KWord (LA 0x351dfc) 4 (ELit (1 + j));        (* [comment removed for export] *)
   KWord (LA 0x351e00) 8 (mbx (freeslot j));    (* [comment removed for export] *)
   KWord (LA 0x351e08) 8 (mbx 4200);            (* [comment removed for export] *)
   KWord (LA 0x351e10) 8 (ELit 99);             (* [comment removed for export] *)
   KWord (LA 0x351e18) 8 (ELit 0);              (* [comment removed for export] *)
   KWord (LA 0x351e28) 8 (mbx 4096);            (* [comment removed for export] *)
   KWord (LA 0x351e30) 8 (mbx 4096);            (* [comment removed for export] *)
   KWord (LA 0x351e38) 8 (mbx 8192);            (* [comment removed for export] *)
   KWord (LA 0x351fa0) 8 (ELit 0);              (* [comment removed for export] *)
   KWord (LA 0x352120) 8 (ELit 0);              (* [comment removed for export] *)
   KWord (LA 0x352180) 1 (ELit (1 + 2 * j))].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kn_meta (j : Z) : list kentry :=
  [KWord (MBA 4096) 8 (EVar 8); KWord (MBA 4104) 8 (ELit 0); KWord (MBA 4112) 4 (ELit 101);   (* [comment removed for export] *)
   KWord (MBA (curslot j)) 8 (ELit 0);                 (* [comment removed for export] *)
   KWord (MBA (curslot j + 8)) 8 (ELit 0);             (* [comment removed for export] *)
   KWord (MBA (curslot j + 16)) 8 (EVar 5);            (* [comment removed for export] *)
   KWord (MBA (curslot j + 24)) 4 (ELit 0);            (* [comment removed for export] *)
   KWord (MBA (curslot j + 28)) 4 (ELit 0);            (* [comment removed for export] *)
   KWord (MBA (curslot j + 32)) 8 (ELit (W_of j));     (* [comment removed for export] *)
   KWord (MBA (freeslot j)) 8 (mbx (freeslot j));      (* [comment removed for export] *)
   KWord (MBA (freeslot j + 8)) 8 (mbx (freeslot j));  (* [comment removed for export] *)
   KWord (MBA (freeslot j + 16)) 8 (ELit 0);
   KWord (MBA (freeslot j + 24)) 8 (ELit 0);
   KWord (MBA (freeslot j + 32)) 8 (ELit 0);
   KZero (MBA 4200) (ELit 3992)].

(* [comment removed for export] *)
Definition kn_hdr (j : Z) : list kentry :=
  [KWord (BA 0) 8 (mbx (curslot j));                  (* [comment removed for export] *)
   KZero (BA 8) (ELit 5);                              (* [comment removed for export] *)
   KWord (BA 13) 1 (ELit 224);                         (* [comment removed for export] *)
   KWord (BA 14) 2 (ELit (j + 1));                     (* [comment removed for export] *)
   KWord (BA (off_of j - 4)) 1 (ELit 0);               (* [comment removed for export] *)
   KWord (BA (off_of j - 3)) 1 (ELit 160);             (* [comment removed for export] *)
   KWord (BA (off_of j - 2)) 2 (ELit (j + 1))].        (* [comment removed for export] *)
Definition kn_ftr (j : Z) : list kentry :=
  [KWord (BA (off_of j + cap_of j)) 1 (ELit 0);        (* [comment removed for export] *)
   KWord (BA (nb_of j - 9)) 1 (ELit 0);                (* [comment removed for export] *)
   KWord (BA (nb_of j - 8)) 4 (ELit (res_of j));       (* [comment removed for export] *)
   KZero (BA (nb_of j - 4)) (ELit 4)].                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kn_buf_half (j : Z) : list kentry :=
  kn_hdr j ++ [KBlob (BA (off_of j)) (ELit (held_of j)) (hb j)] ++ kn_ftr j.
Definition kn_buf_full (j : Z) : list kentry :=
  kn_hdr j ++ [KBlob (BA (off_of j)) (ELit (held_of j)) (hb j);
               KBlob (BA (off_of j + held_of j)) (ELit (held_of j)) (cb j)] ++ kn_ftr j.

Definition kn_HALF (j : Z) : list kentry := kn_static j ++ kn_ctx j ++ kn_meta j ++ kn_buf_half j.
Definition kn_FULL (j : Z) : list kentry := kn_static j ++ kn_ctx j ++ kn_meta j ++ kn_buf_full j.

(* [comment removed for export] *)
Definition kn_G0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 1) 0x7fff80000000 0x800000400000;
   KAlign (EVar 2) 4096; KRange (EVar 2) 0x1000 (CEIL - 8192);
   KDisj (LA 0x10000) 0x344000 (SA (EVar 2) 0) 8192;
   KDisj (SA (EVar 0) (-8388608)) HUGE (SA (EVar 2) 0) 8192;
   KWr (SA (EVar 2) 4096) 4096;
   KAlign (EVar 3) 4096; KRange (EVar 3) 0x354000 (CEIL - 69632);
   KDisj (SA (EVar 0) (-8388608)) HUGE (SA (EVar 3) 0) 69632;
   KWr (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 3) 0) 69632 (SA (EVar 2) 4096) 4096;
   KWr (LA 0x31e000) 0x36000;
   KWord (LA 0x331a44) 4 (EVar 6);
   KImg 0 0x1000] ++ kn_M1.
Definition kn_FULL0 : list kentry := kn_G0 ++ [KBlob (GMA 32) (ELit 65536) 0%nat].
Definition sr_FULL0 : list expr := sr_LOOP (gmx 32) 65536 65536.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pref (n : Z) (l : list byte) : list byte := firstn (Z.to_nat n) l.
Definition dropz (n : Z) (l : list byte) : list byte := skipn (Z.to_nat n) l.
Arguments pref : simpl never.
Arguments dropz : simpl never.
(* [comment removed for export] *)
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

Lemma dropz_0 : forall l, dropz 0 l = l.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pref_app : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  pref a l ++ pref b (dropz a l) = pref (a + b) l.
Proof.
  intros a b l Ha Hb. unfold pref, dropz. rewrite Z2Nat.inj_add by lia. rewrite firstn_skipn_comm.
  transitivity (firstn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l) ++ skipn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l)).
  - f_equal. rewrite firstn_firstn. f_equal. lia.
  - apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma pref_dropz_app : forall n l, pref n l ++ dropz n l = l.
Proof. intros n l. unfold pref, dropz. apply firstn_skipn. Qed.

(* [comment removed for export] *)
Lemma pref_all : forall n l, (Z.of_nat (length l) <= n)%Z -> pref n l = l.
Proof. intros n l H. unfold pref. apply firstn_all2. lia. Qed.

(* [comment removed for export] *)
Definition gsize (m : nat) : Z := 65536 * 2 ^ (Z.of_nat m).
Definition gblobs (content : list byte) (k : nat) : list byte :=
  if Nat.even k then pref (gsize (Nat.div2 k)) content
  else pref (gsize (Nat.div2 k)) (dropz (gsize (Nat.div2 k)) content).

Lemma gblobs_hb : forall j content, (1 <= j)%Z -> gblobs content (hb j) = pref (held_of j) content.
Proof.
  intros j content Hj. unfold gblobs, hb.
  rewrite Nat.even_mul. cbn [Nat.even orb]. rewrite Nat.div2_double.
  unfold gsize, held_of. do 2 f_equal. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma gblobs_cb : forall j content, (1 <= j)%Z ->
  gblobs content (cb j) = pref (held_of j) (dropz (held_of j) content).
Proof.
  intros j content Hj. unfold gblobs, cb.
  rewrite Nat.add_1_r, Nat.even_succ, Nat.odd_mul. cbn [Nat.odd andb]. rewrite Nat.div2_succ_double.
  unfold gsize, held_of. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma gblobs_fb : forall j content, (0 <= j)%Z -> gblobs content (fb j) = pref (cap_of j) content.
Proof.
  intros j content Hj. unfold gblobs, fb.
  rewrite Nat.even_mul. cbn [Nat.even orb]. rewrite Nat.div2_double.
  unfold gsize, cap_of. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma held_twice : forall j, (1 <= j)%Z -> (held_of j + held_of j = cap_of j)%Z.
Proof.
  intros j Hj. unfold held_of, cap_of. replace j with (j - 1 + 1)%Z at 3 by lia.
  rewrite Z.pow_add_r by lia. lia.
Qed.

Definition vals_RD (sp0 p1 mb bw gm : word) (L : Z) (B e can sec : word) (extra : list word) : list word :=
  [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra.

Definition ENV_RD (sp0 p1 mb bw gm : word) (L : Z) (B e can sec : word) (extra : list word) (content : list byte) : env :=
  Env (vals_ev (vals_RD sp0 p1 mb bw gm L B e can sec extra)) (gblobs content).

(* [comment removed for export] *)
Definition rd_cell (i : Z) : Prop :=
  (0x31ef09 <= i < 0x32ef09)%Z \/
  (0x331a44 <= i < 0x331a48)%Z \/ (0x351dfc <= i < 0x351e18)%Z \/ (0x351fa0 <= i < 0x351fa8)%Z
  \/ (0x352120 <= i < 0x352128)%Z \/ (0x352180 <= i < 0x352181)%Z.

(* [comment removed for export] *)
Definition pres (M0 M : word -> option byte) (sp0 : word) : Prop :=
  forall x : word,
    ((0x10000 <= bv_unsigned x < 0x354000)%Z /\ ~ rd_cell (bv_unsigned x))
    \/ (bv_unsigned sp0 - 128 <= bv_unsigned x)%Z ->
    M x = M0 x.

Lemma pres_refl : forall M sp0, pres M M sp0.
Proof. intros M sp0 x _. reflexivity. Qed.

Lemma pres_trans : forall M0 M1 M2 sp0, pres M0 M1 sp0 -> pres M1 M2 sp0 -> pres M0 M2 sp0.
Proof. intros M0 M1 M2 sp0 A B x Hx. rewrite (B x Hx). apply A, Hx. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pres_far : forall M M' sp0 (lo n : Z),
  (0x7fff80000000 <= bv_unsigned sp0)%Z ->
  (0x354000 <= lo)%Z -> (lo + n <= bv_unsigned sp0 - 8388608)%Z ->
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x)%Z -> M' x = M x) ->
  pres M M' sp0.
Proof.
  intros M M' sp0 lo n Hsp Hlo Hhi OUT x Hx. apply OUT. lia.
Qed.

Definition inb (lo hi k w : Z) : bool := Z.leb lo k && Z.leb (k + w) hi.

(* [comment removed for export] *)
Definition store_pres_ok (kn : list kentry) (b : expr) (k w : Z) : bool :=
  match b with
  | ELit 0 => Z.leb 0 w && (inb 0x31ef09 0x32ef09 k w || inb 0x331a44 0x331a48 k w || inb 0x351dfc 0x351e18 k w
              || inb 0x351fa0 0x351fa8 k w || inb 0x352120 0x352128 k w || inb 0x352180 0x352181 k w)
  | EVar 0 => Z.leb (-8388608) k && Z.leb (k + w) (-128) && Z.leb 0 w
  | _ => match base_range kn b with
         | Some (lo, hi) =>
             (Z.leb 0x354000 (lo + k) || (Z.leb 0 (lo + k) && ranges_apart kn (ELit 0) 0x10000 0x344000 b k w))
             && (kdisj_apart kn (EVar 0) (-8388608) HUGE b k w && Z.leb (hi + k + w) HUGE) && Z.leb 0 w
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

Lemma store_pres_ok_sound : forall E M kn b k w sp0,
  know_ok RSEGS E M kn -> ev E 0 = sp0 ->
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  store_pres_ok kn b k w = true ->
  let ua := bv_unsigned (adenot E (SA b k)) in
  (ua + w <= 2 ^ 64)%Z /\
  forall x : word,
    ((0x10000 <= bv_unsigned x < 0x354000)%Z /\ ~ rd_cell (bv_unsigned x)) \/ (bv_unsigned sp0 - 128 <= bv_unsigned x)%Z ->
    (bv_unsigned x < ua \/ ua + w <= bv_unsigned x)%Z.
Proof.
  intros E M kn b k w sp0 HK H0 Hsp Hb. unfold store_pres_ok in Hb.
  unfold adenot, v_addi. cbn [a_base a_off].
  Ltac other_base HK E H0 k w :=
      lazymatch goal with Hb : context [base_range ?kn ?bb] |- _ =>
        let lo := fresh "rlo" in let hi := fresh "rhi" in let HR := fresh "HR" in
        destruct (base_range kn bb) as [[lo hi]|] eqn:HR; [|discriminate];
        pose proof (base_range_sound RSEGS _ _ kn bb lo hi HK HR) as [? ?];
        apply andb_prop in Hb as [Hb ?Hw]; apply andb_prop in Hb as [Hb ?Hb2];
        apply andb_prop in Hb2 as [Hb2 ?Hb4]; apply Z.leb_le in Hb4; unfold HUGE in Hb4;
        apply Z.leb_le in Hw;
        let Hb1 := fresh "Hb1" in
        assert (Hb1 : (0 <= lo + k)%Z /\
                      (0x354000 <= lo + k \/ estart E (SA (ELit 0) 0x10000) + 0x344000 <= estart E (SA bb k) \/ estart E (SA bb k) + w <= estart E (SA (ELit 0) 0x10000))%Z)
          by (apply orb_prop in Hb; destruct Hb as [Hb|Hb];
              [ apply Z.leb_le in Hb; lia
              | apply andb_prop in Hb as [?Hb0 Hb]; apply Z.leb_le in Hb0; split; [exact Hb0|];
                right; eapply ranges_apart_sound; [exact HK | exact Hb] ]);
        clear Hb; unfold estart in Hb1; cbn [a_base a_off] in Hb1; rewrite ?edenot_lit0 in Hb1;
        try (change (bv_unsigned (edenot _ (ELit 0))) with 0%Z in Hb1);
        let Hb3 := fresh "Hb3" in
        pose proof (kdisj_apart_sound RSEGS _ _ kn (EVar 0) (-8388608) HUGE bb k w HK Hb2) as Hb3;
        clear Hb2; unfold estart, HUGE in Hb3; cbn [a_base a_off] in Hb3;
        change (edenot E (EVar 0)) with (ev E 0) in Hb3; rewrite H0 in Hb3;
        pose proof (u64_range (edenot E bb))
      end.
  destruct b as [z|n| | | | | |].
  1:{ destruct z as [|pz|nz].
      2,3: other_base HK E H0 k w; rewrite u_small by lia; split; [lia|]; intros x Hx; lia.
      cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
      apply andb_prop in Hb as [Hw Hb]. apply Z.leb_le in Hw.
      assert (HH : ((0x31ef09 <= k /\ k + w <= 0x32ef09) \/ (0x331a44 <= k /\ k + w <= 0x331a48) \/ (0x351dfc <= k /\ k + w <= 0x351e18)
                   \/ (0x351fa0 <= k /\ k + w <= 0x351fa8) \/ (0x352120 <= k /\ k + w <= 0x352128) \/ (0x352180 <= k /\ k + w <= 0x352181))%Z).
      { repeat (apply orb_prop in Hb; destruct Hb as [Hb|Hb]); try apply inb_sound in Hb; tauto. }
      assert (Hk : (0 <= k /\ k + w <= 0x354000)%Z) by lia.
      rewrite u_small by lia. split; [lia|]. intros x Hx. unfold rd_cell in Hx. lia. }
  1:{ destruct n as [|n'].
      + cbn [edenot]. rewrite H0. apply andb_prop in Hb as [Hb Hw]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. apply Z.leb_le in Hw.
        rewrite u_small by lia. split; [lia|]. intros x Hx. lia.
      + other_base HK E H0 k w. rewrite u_small by lia. split; [lia|]. intros x Hx. lia. }
  all: other_base HK E H0 k w; rewrite u_small by lia; split; [lia|]; intros x Hx; lia.
Qed.

(* [comment removed for export] *)
Lemma pres_mem_denot : forall E M kn log sp0,
  know_ok RSEGS E M kn -> ev E 0 = sp0 ->
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

Lemma pres_mem_denot_trans : forall E M0 M kn log sp0,
  know_ok RSEGS E M kn -> ev E 0 = sp0 ->
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  log_pres_ok kn log = true ->
  pres M0 M sp0 -> pres M0 (mem_denot E M log) sp0.
Proof.
  intros. eapply pres_trans; [eassumption|]. eapply pres_mem_denot; eassumption.
Qed.

(* [comment removed for export] *)
Definition vm_stage (VM : VmMaps) (sp0 mb bw B : word) (nb : Z) : Prop :=
  vm_reserved VM = segments_reserved RSEGS
  /\ (LIM <= vm_limit VM)%Z             (* [comment removed for export] *)
  /\ vm_init_sp VM = sp0                (* [comment removed for export] *)
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
      /\ seps rest
      /\ vm_ledger mb bw VM    (* [comment removed for export] *)
      /\ vm_exact VM sp0 mb bw B nb.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_exact_grow : forall (V V' : VmMaps) (sp0 mb bw B B' : word) (nb nb' : Z),
  vm_exact V sp0 mb bw B nb ->
  (0 < nb < 2 ^ 62)%Z -> (0 < nb' < 2 ^ 62)%Z ->
  vm_maps V' = map_remove ((B', Z_to_bv 64 nb') :: vm_maps V) B ->
  vm_noaccess V' = maps_subtract (vm_noaccess V) (bv_unsigned B) (bv_unsigned B + bv_unsigned (Z_to_bv 64 nb)) ->
  vm_start_brk V' = vm_start_brk V -> vm_brk V' = vm_brk V ->
  (bv_unsigned B' mod 4096 = 0)%Z -> (0 < bv_unsigned B')%Z -> (bv_unsigned B' + nb' <= bv_unsigned sp0 - 8388608)%Z ->
  region_free (segments_reserved RSEGS ++ vm_maps V) B' (Z_to_bv 64 nb') = true ->
  vm_exact V' sp0 mb bw B' nb'.
Proof.
  intros V V' sp0 mb bw B B' nb nb' (Xm & Xn & Xs & Xb & Xbw & Xr & Xal & Xpos & Xtop & Xrf & Xdj & Xbrk) Hnb Hnb' Em En Es Eb GA GP GC GF.
  assert (Un : bv_unsigned (Z_to_bv 64 nb) = nb) by (apply LedgerCfg.u64_lit; lia).
  assert (Un' : bv_unsigned (Z_to_bv 64 nb') = nb') by (apply LedgerCfg.u64_lit; lia).
  assert (U8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply LedgerCfg.u64_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 4096) = 4096%Z) by (apply LedgerCfg.u64_lit; lia).
  rewrite LedgerCfg.region_free_app in GF. apply andb_prop in GF as [GF1 GF2].
  pose proof (LedgerCfg.region_free_In_disj _ _ _ (B, Z_to_bv 64 nb) GF2 ltac:(rewrite Xm; left; reflexivity)) as D1.
  pose proof (LedgerCfg.region_free_In_disj _ _ _ (mb, Z_to_bv 64 8192) GF2 ltac:(rewrite Xm; right; left; reflexivity)) as D2.
  unfold LedgerCfg.e_disj, LedgerCfg.e_hi, LedgerCfg.e_lo, LedgerCfg.e_sz in D1, D2. cbn [fst snd] in D1, D2.
  rewrite Un, Un' in D1. rewrite U8, Un' in D2.
  assert (NB : B' <> B) by (intros E; rewrite E in D1; lia).
  assert (NM : mb <> B) by (intros E; rewrite E in Xdj; lia).
  unfold vm_exact. rewrite Em, En, Es, Eb, Xm, Xn.
  split. { rewrite RefNodes.map_remove_skip by exact NB. rewrite RefNodes.map_remove_head. rewrite RefNodes.map_remove_skip by exact NM. reflexivity. }
  split. { rewrite Un. apply LedgerCfg.maps_subtract_id; [lia|]. constructor; [|constructor].
           unfold LedgerCfg.e_sz, LedgerCfg.e_hi, LedgerCfg.e_lo, LedgerCfg.e_sz. cbn [fst snd]. rewrite U4. lia. }
  split; [exact Xs|]. split; [exact Xb|]. split; [exact Xbw|]. split; [exact Xr|].
  split; [exact GA|]. split; [exact GP|]. split; [exact GC|]. split; [exact GF1|]. split; [lia | exact Xbrk].
Qed.

(* [comment removed for export] *)
Lemma seps_filter : forall (f : word * word -> bool) l, seps l -> seps (List.filter f l).
Proof.
  intros f l H. induction H as [|p l Hp Hl IH]; cbn [List.filter]; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply incl_Forall with (l1 := l); [apply incl_filter | exact Hp].
Qed.

(* [comment removed for export] *)
Lemma vm_stage_seps : forall VM sp0 mb bw B nb, (0 < nb < 2 ^ 62)%Z -> (bv_unsigned B + nb <= 2 ^ 64)%Z ->
  vm_stage VM sp0 mb bw B nb -> seps (vm_maps VM)
  /\ Forall (fun p => (0 < bv_unsigned (snd p))%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM).
Proof.
  intros VM sp0 mb bw B nb Hnb Hnw (Vres & Vlim & Visp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps & Vlg).
  rewrite Vmaps. split.
  - constructor; [|exact Vseps]. eapply Forall_impl; [|exact Vdisj].
    intros [qb qs] Hq. unfold iv_disjoint. cbn [fst snd] in *. rewrite u_small by lia. lia.
  - constructor.
    + cbn [fst snd]. rewrite u_small by lia. lia.
    + eapply Forall_impl; [|exact Vsz]. intros [qb qs] Hq. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Definition loop_at (sr : list expr) (kn : list kentry) (sp0 p1 mb bw gm : word) (L : Z) (B e can sec : word) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  exists extra : list word, length extra = 32%nat
      /\ regs_ok (ENV_RD sp0 p1 mb bw gm L B e can sec extra content) sr R
      /\ know_ok RSEGS (ENV_RD sp0 p1 mb bw gm L B e can sec extra content) M kn.

Definition half (j : Z) (sp0 p1 mb bw gm : word) (L : Z) (B e can sec : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) : Prop :=
  loop_at (sr_HALF j) (kn_HALF j) sp0 p1 mb bw gm L B e can sec content R M
  /\ pres M0 M sp0
  /\ vm_stage VM sp0 mb bw B (nb_of j).

Definition full (j : Z) (sp0 p1 mb bw gm : word) (L : Z) (B e can sec : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) : Prop :=
  loop_at (sr_FULL j) (kn_FULL j) sp0 p1 mb bw gm L B e can sec content R M
  /\ pres M0 M sp0
  /\ vm_stage VM sp0 mb bw B (nb_of j).

(* [comment removed for export] *)
Definition full0 (sp0 p1 mb bw gm : word) (L : Z) (e can sec : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  loop_at sr_FULL0 kn_FULL0 sp0 p1 mb bw gm L (Z_to_bv 64 0) e can sec content R M
  /\ pres M0 M sp0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kn_POST (k : Z) : list kentry := kn_static k ++ kn_ctx k ++ kn_meta k ++
  [KWord (BA 0) 8 (mbx (curslot k)); KZero (BA 8) (ELit 5); KWord (BA 13) 1 (ELit 224);
   KWord (BA 14) 2 (ELit (k + 1)); KWord (BA (off_of k - 4)) 1 (ELit 0);
   KWord (BA (off_of k - 3)) 1 (ELit 160); KWord (BA (off_of k - 2)) 2 (ELit (k + 1));
   KWord (BA (off_of k + cap_of k)) 1 (ELit 0); KWord (BA (nb_of k - 9)) 1 (ELit 0);
   KWord (BA (nb_of k - 8)) 4 (ELit (res_of k)); KZero (BA (nb_of k - 4)) (ELit 4)].

Record read_post (k : Z) (sp0 p1 mb bw gm B e can sec : word) (content : list byte)
       (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) : Prop := READ_POST {
  rk_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rk_gp : getr R 3 = Z_to_bv 64 0x10800;
  rk_tp : getr R 4 = Z_to_bv 64 0x331ae8;
  rk_s0 : getr R 8 = Z_to_bv 64 2;
  rk_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned B + off_of k);          (* [comment removed for export] *)
  rk_s2 : getr R 18 = p1;
  rk_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));       (* [comment removed for export] *)
  rk_s4 : getr R 20 = Z_to_bv 64 3;
  rk_s5 : getr R 21 = Z_to_bv 64 (cap_of k);                          (* [comment removed for export] *)
  rk_s6 : getr R 22 = Z_to_bv 64 STAGE;                               (* [comment removed for export] *)
  rk_s7 : getr R 23 = Z_to_bv 64 0;                                   (* [comment removed for export] *)
  rk_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + off_of k)) (length content) = Some content;
  rk_pres : pres M0 M sp0;
  rk_know : exists extra : list word, length extra = 32%nat /\
      know_ok RSEGS (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) M (kn_POST k);
  rk_vm : vm_stage VM sp0 mb bw B (nb_of k) }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition oom_leaf (sp0 : word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr R 3 = Z_to_bv 64 0x10800 /\ getr R 4 = Z_to_bv 64 0x331ae8
  /\ pres M0 M sp0 /\ stack_writable M sp0.

Definition oom_branch (sp0 : word) (path : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word)
           (M0 : word -> option byte) (TOOM : TSet) : Prop :=
  forall R M off V, oom_leaf sp0 M0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe1c1c) M (seg_rom RSEGS)) (modelG path stdin0 fs0 tid off V)) TOOM.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LoopRegs.
  Variables (sp0 p1 mb bw gm : word) (L : Z) (B e can sec : word) (content : list byte) (R : bvmap 5 word).
  Let E := ENV_RD sp0 p1 mb bw gm L B e can sec (junk_vals R) content.

  Lemma lr_ev0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma lr_ev1 : ev E 1 = p1. Proof. reflexivity. Qed.
  Lemma lr_ev2 : ev E 2 = mb. Proof. reflexivity. Qed.
  Lemma lr_ev3 : ev E 3 = gm. Proof. reflexivity. Qed.
  Lemma lr_ev5 : ev E 5 = B. Proof. reflexivity. Qed.
  Lemma lr_ev6 : ev E 6 = e. Proof. reflexivity. Qed.
  Lemma lr_ev7 : ev E 7 = can. Proof. reflexivity. Qed.
  Lemma lr_ev8 : ev E 8 = sec. Proof. reflexivity. Qed.
  Lemma lr_evJ : forall i, (i < 32)%nat -> ev E (10 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV_RD, vals_RD. cbn [ev]. unfold vals_ev.
    change (10 + i)%nat with (length [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
    reflexivity.
  Qed.
  Lemma lr_spx : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. rewrite lr_ev0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
  Lemma lr_gmx : forall k, edenot E (gmx k) = Z_to_bv 64 (bv_unsigned gm + k).
  Proof. intros k. cbn [gmx edenot]. rewrite alu_add. unfold v_add. rewrite lr_ev3.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
  Lemma lr_bx : forall k, edenot E (bx k) = Z_to_bv 64 (bv_unsigned B + k).
  Proof. intros k. cbn [bx edenot]. rewrite alu_add. unfold v_add. rewrite lr_ev5.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
  Lemma lr_mbx : forall k, edenot E (mbx k) = Z_to_bv 64 (bv_unsigned mb + k).
  Proof. intros k. cbn [mbx edenot]. rewrite alu_add. unfold v_add. rewrite lr_ev2.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Lemma sr_LOOP_regs : forall (bufe : expr) (buf len cap : Z),
    edenot E bufe = Z_to_bv 64 buf ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x331ae8 ->
    getr R 8 = Z_to_bv 64 2 -> getr R 9 = Z_to_bv 64 buf -> getr R 18 = p1 -> getr R 19 = Z_to_bv 64 len ->
    getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 cap -> getr R 22 = Z_to_bv 64 STAGE -> getr R 23 = Z_to_bv 64 buf ->
    regs_ok E (sr_LOOP bufe len cap) R.
  Proof.
    intros bufe buf len cap Hbuf R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_LOOP all_regs].
    all: try (lazymatch goal with |- _ = edenot _ (spx ?k) => rewrite lr_spx, R2; f_equal; lia end).
    all: try (lazymatch goal with |- _ = edenot _ (J ?n) => unfold J; change (edenot E (EVar (10 + n))) with (ev E (10 + n)); rewrite lr_evJ by lia; reflexivity end).
    all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite lr_ev1; assumption).
    all: try (rewrite Hbuf; assumption).
    all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
  Qed.

  Lemma sr_MID_regs : forall (bufe : expr) (buf len cap : Z),
    edenot E bufe = Z_to_bv 64 buf ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x331ae8 ->
    getr R 8 = Z_to_bv 64 2 -> getr R 9 = Z_to_bv 64 buf -> getr R 18 = p1 -> getr R 19 = Z_to_bv 64 len ->
    getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 cap -> getr R 22 = Z_to_bv 64 STAGE ->
    regs_ok E (sr_MID bufe len cap) R.
  Proof.
    intros bufe buf len cap Hbuf R2 R3 R4 R8 R9 R18 R19 R20 R21 R22.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_MID all_regs].
    all: try (lazymatch goal with |- _ = edenot _ (spx ?k) => rewrite lr_spx, R2; f_equal; lia end).
    all: try (lazymatch goal with |- _ = edenot _ (J ?n) => unfold J; change (edenot E (EVar (10 + n))) with (ev E (10 + n)); rewrite lr_evJ by lia; reflexivity end).
    all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite lr_ev1; assumption).
    all: try (rewrite Hbuf; assumption).
    all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
  Qed.
End LoopRegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fetch_2775f0 : fetch_word RSEGS (Z_to_bv 64 0x2bd1dc) = Some ECALLW. Proof. vm_compute. reflexivity. Qed.
Lemma fetch_26e234 : fetch_word RSEGS (Z_to_bv 64 0x2b3e20) = Some ECALLW. Proof. vm_compute. reflexivity. Qed.
Lemma fetch_26e3a0 : fetch_word RSEGS (Z_to_bv 64 0x2b3f8c) = Some ECALLW. Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_reserved : segments_reserved RSEGS =
  [(Z_to_bv 64 65536, Z_to_bv 64 856064); (Z_to_bv 64 921600, Z_to_bv 64 1966080);
   (Z_to_bv 64 2887680, Z_to_bv 64 380928); (Z_to_bv 64 3268608, Z_to_bv 64 221184)].
Proof. vm_compute. reflexivity. Qed.

Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x31e000) 221184 = true.
Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.  (* [comment removed for export] *)

Lemma data_store_ok : forall m a n,
  (0x31e000 <= a)%Z -> (a + Z.of_nat n <= 0x354000)%Z -> store_ok RSEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros m a n Ha Hn.
  eapply (store_ok_window RSEGS m (Z_to_bv 64 0x31e000) (Z_to_bv 64 a) 221184 n 0x31e000 0x354000);
    [ apply u_small; lia | reflexivity | cbn; lia | apply wseg_data
    | rewrite u_small by lia; lia | rewrite u_small by lia; lia ].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
