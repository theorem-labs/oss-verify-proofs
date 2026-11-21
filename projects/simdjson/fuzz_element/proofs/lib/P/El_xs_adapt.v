(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the fixed-offset facts about the pre-revision ten-pair auxv (kn_auxv, kn_auxv_ok) are replaced by the revision's auxv walk (the key of every pair up to AT_NULL at 16k and this binary's AT_PHDR, AT_PHENT and AT_PHNUM values, for the CONFIG_RSEQ value rauxv_ok's walk fact names, with a readable span over the vector), since musl's static_dl_iterate_phdr walks the whole auxv on the __cxa_throw path, and the auxv region's fixed span is cut to the 16 bytes every layout has. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac RegsEquiv Arr Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.simdjson.fuzz_element.images Require Plain.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout InitMem Rnd Sj_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound El_xs_kitP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Notation EL_EHG := (0xe1c98)%Z (only parsing).
Notation EL_UNW := (0xe35b0)%Z (only parsing).
Notation XS_END := (0x705b8)%Z (only parsing).

Definition uw_bytes (uw : bool) : list Z := if uw then [0; 1; 0; 1; 0; 1; 0; 0] else [0; 0; 0; 0; 0; 0; 0; 0].

Definition XSP : expr := EVar 2.
Definition XBLK : expr := EVar 40.
Definition XAUXV : expr := EVar 41.

Definition xs_W : list wrange := [(XSP, -16384, 16); (XBLK, 0, 144); (ELit 0, EL_EHG, EL_EHG + 12); (ELit 0, EL_UNW, EL_UNW + 8)].
Definition xs_RW : list wrange := [(XSP, -16384, 16)].

Definition xs_regs0 : list expr :=
  [ELit 0; EVar 1; XSP; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9;
   EAlu ALU_ADD XBLK (ELit 128); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19;
   EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Definition kn_geom : list kentry :=
  [KRange XSP 0x700000000000 0x3fffffffffffffff; KAlign XSP 16;
   KRange XBLK 16 0x7fffff800000; KAlign XBLK 16;
   KRange XAUXV 0x700000000000 0xfffffffffffffff0;
   KDisj (SA XSP (-16384)) (ELit 16400) (SA XBLK 0) (ELit 144);
   KDisj (SA XSP (-16384)) (ELit 16400) (SA XAUXV 0) (ELit 16);
   KDisj (SA XBLK 0) (ELit 144) (SA XAUXV 0) (ELit 16);
   KDisj (SA XBLK 0) (ELit 144) (SA (ELit 0) 0x10000) (ELit 0xf5000)].
Definition kn_wr : list kentry :=
  [KWr (SA XSP (-16384)) (ELit 16400); KWr (SA XBLK 0) (ELit 144); KWr (SA (ELit 0) EL_EHG) (ELit 12); KWr (SA (ELit 0) EL_UNW) (ELit 8)].
Definition kn_img : list kentry := [KImg 0x10000 0xca000; KImg 0xcac10 0xd0848; KImg 0xd0850 0xd0878].
Definition kn_blk : list kentry := kzeros XBLK 0 144.
Definition kn_ehg : list kentry := [KWord (SA (ELit 0) EL_EHG) 8 (ELit 0); KWord (SA (ELit 0) (EL_EHG + 8)) 4 (ELit 0)].
Fixpoint kbytes (a : Z) (bs : list Z) : list kentry :=
  match bs with [] => [] | b :: bs' => KWord (SA (ELit 0) a) 1 (ELit b) :: kbytes (a + 1) bs' end.
Definition kn_unw (uw : bool) : list kentry := kbytes EL_UNW (uw_bytes uw).
Definition kn_consts : list kentry :=
  [KWord (SA (ELit 0) 0xd0848) 8 (ELit 0x1038f8);
   KWord (SA (ELit 0) 0xd18a0) 8 (ELit 0xcdf48); KWord (SA (ELit 0) 0xd18a8) 8 (ELit 0x70684);
   KWord (SA (ELit 0) 0xd18b8) 8 (ELit 0x53484); KWord (SA (ELit 0) 0xd18c0) 8 (ELit 0x53590)].
Definition kn_cells : list kentry :=
  [KWord (SA (ELit 0) 0x1038f8) 8 (EVar 42); KWord (SA (ELit 0) 0x103920) 8 XAUXV].
(* The old [kn_auxv] here claimed the ten COMPACTED pairs of the pre-revision
   auxv vector at XAUXV + 0 .. 152, AT_PHDR first, terminated by a LITERAL
   AT_NULL at 144/152.  The __cxa_throw path walks the auxv (musl's
   static_dl_iterate_phdr reads every pair's key up to AT_NULL, then the AT_PHDR,
   AT_PHENT and AT_PHNUM values), so the revision's vector is given instead, from
   [RMallocTree.rauxv_ok]'s walk fact at the CONFIG_RSEQ value [b] it names: the
   keys of the pairs and AT_NULL's at 16 k ([rauxv_keys b] then 0), this binary's
   three program-header values at 216, 232 and 248, a [KUnk] over the whole vector
   (so each value word the walk loads reads as a fresh variable), and the vector's
   disjointness from the frame and the block. *)
Definition auxv_span (b : bool) : Z := 16 * (Z.of_nat (length (rauxv_keys b)) + 1).
Fixpoint kn_keys (o : Z) (ks : list Z) : list kentry :=
  match ks with [] => [] | k :: r => KWord (SA XAUXV o) 8 (ELit k) :: kn_keys (o + 16) r end.
Definition kn_walk (b : bool) : list kentry :=
  [KDisj (SA XSP (-16384)) (ELit 16400) (SA XAUXV 0) (ELit (auxv_span b));
   KDisj (SA XBLK 0) (ELit 144) (SA XAUXV 0) (ELit (auxv_span b))]
  ++ kn_keys 0 (rauxv_keys b ++ [0])
  ++ [KWord (SA XAUXV 216) 8 (ELit (Z.of_N (ph_addr Plain.M.phdrs)));
      KWord (SA XAUXV 232) 8 (ELit (Z.of_N (ph_ent Plain.M.phdrs)));
      KWord (SA XAUXV 248) 8 (ELit (Z.of_N (ph_num Plain.M.phdrs)));
      KUnk (SA XAUXV 0) (ELit (auxv_span b))].
Definition xs_kn0 (raval : Z) (uw b : bool) : list kentry :=
  kn_geom ++ kn_wr ++ kn_img ++ kn_blk ++ kn_ehg ++ kn_unw uw ++ [KWord (SA XSP 0) 8 (EVar 49); KWord (SA XSP 8) 8 (ELit raval)] ++ kn_consts ++ kn_cells ++ kn_walk b.
Definition xs_ss0 (pc0 raval : Z) (uw b : bool) : sym_state := SS pc0 xs_regs0 [] (xs_kn0 raval uw b) 200.

Lemma estart_lit : forall E a, estart E (SA (ELit 0) a) = a.
Proof. intros E a. unfold estart. cbn [a_base a_off edenot]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia. Qed.
Lemma elenZ_lit' : forall E n, 0 <= n < 2^64 -> elenZ E (ELit n) = n.
Proof. intros E n H. rewrite elenZ_lit. apply Z.mod_small. exact H. Qed.

Lemma kwr_lit : forall E (m : word -> option byte) a n,
  0 <= a -> 0 <= n -> a + n < 2^64 -> wr_at psegs m a n -> kentry_ok psegs E m (KWr (SA (ELit 0) a) (ELit n)).
Proof.
  intros E m a n Ha Hn Hh (_ & _ & W). cbn [kentry_ok]. rewrite estart_lit, elenZ_lit' by lia.
  split; [unfold flat; rewrite estart_lit; lia|].
  intros d k Hd Hk. apply StoreOk.store_ok_of_all.
  - rewrite unsigned_lit by lia. lia.
  - intros x Hx. rewrite unsigned_lit in Hx by lia.
    specialize (W (bv_unsigned x - a) ltac:(lia)). replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in W by lia.
    unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
Qed.
Lemma kwr_var : forall E (m : word -> option byte) (v : nat) off n,
  0 <= bv_unsigned (ev E v) + off -> 0 <= n -> bv_unsigned (ev E v) + off + n < 2^64 ->
  wr_at psegs m (bv_unsigned (ev E v) + off) n -> kentry_ok psegs E m (KWr (SA (EVar v) off) (ELit n)).
Proof.
  intros E m v off n Ha Hn Hh (_ & _ & W). cbn [kentry_ok]. rewrite elenZ_lit' by lia.
  assert (ES : estart E (SA (EVar v) off) = bv_unsigned (ev E v) + off) by reflexivity.
  split; [unfold flat; rewrite ES; lia|]. rewrite ES.
  intros d k Hd Hk. apply StoreOk.store_ok_of_all.
  - rewrite unsigned_lit by lia. lia.
  - intros x Hx. rewrite unsigned_lit in Hx by lia.
    specialize (W (bv_unsigned x - (bv_unsigned (ev E v) + off)) ltac:(lia)).
    replace (bv_unsigned (ev E v) + off + (bv_unsigned x - (bv_unsigned (ev E v) + off))) with (bv_unsigned x) in W by lia.
    unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
Qed.

Lemma kword_at : forall E (m : word -> option byte) (b : expr) off (w : nat) (v : expr),
  (1 <= w <= 8)%nat -> 0 <= bv_unsigned (edenot E b) + off -> bv_unsigned (edenot E b) + off + Z.of_nat w <= 2^64 ->
  bytes_at psegs m (bv_unsigned (edenot E b) + off) (word_to_le_bytes w (edenot E v)) ->
  kentry_ok psegs E m (KWord (SA b off) w v).
Proof.
  intros E m b off w v Hw Ha Hh B. cbn [kentry_ok]. split; [lia|].
  assert (ES : estart E (SA b off) = bv_unsigned (edenot E b) + off) by reflexivity.
  split; [unfold flat; rewrite ES; lia|].
  pose proof (Mem.bytes_at_rdn psegs m _ _ 0 w B) as X.
  rewrite length_N_to_le_bytes in X. specialize (X ltac:(lia)). cbn [skipn Z.of_nat] in X. rewrite Z.add_0_r in X.
  rewrite firstn_all2 in X by (rewrite length_N_to_le_bytes; lia).
  rewrite rdn_common in X. rewrite adenot_SA. unfold wa in X. exact X.
Qed.

Lemma kimg_of_none : forall E (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2^64 -> (forall i, lo <= i < hi -> m (wa i) = None) -> kentry_ok psegs E m (KImg lo hi).
Proof. intros E m lo hi Hlo Hhi H. cbn [kentry_ok]. split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi. unfold wa in H. apply H. exact Hi. Qed.

Lemma psegs_ro : forall i, 0x10000 <= i < 0xca000 -> ro_addr psegs (wa i) = true.
Proof.
  intros i Hi. unfold ro_addr. unfold wa. rewrite unsigned_lit by lia.
  unfold psegs. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N].
  destruct (Z.leb_spec0 65536 i); destruct (Z.leb_spec0 (i + 1) (65536 + 176128)); cbn [andb]; try reflexivity; try lia.
  destruct (Z.leb_spec0 241664 i); destruct (Z.leb_spec0 (i + 1) (241664 + 585728)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma kimg_ro_P : forall E (m : word -> option byte), mem_inv psegs m -> kentry_ok psegs E m (KImg 0x10000 0xca000).
Proof.
  intros E m MI. apply kimg_of_none; [lia| lia|]. intros i Hi.
  destruct (m (wa i)) as [b|] eqn:Em; [|reflexivity]. exfalso.
  pose proof (Mem.mem_inv_ro psegs m (wa i) b MI Em) as X. rewrite psegs_ro in X by exact Hi. discriminate.
Qed.

Lemma psegs_top : InitMem.segs_top psegs = 0x105000.
Proof. reflexivity. Qed.
Lemma seg_rom_high : forall x : word, 0x105000 <= bv_unsigned x -> OSSVerify.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom psegs x = None.
Proof.
  intros x Hx. unfold PropExec.seg_rom, memory_read.
  rewrite (InitMem.find_segment_high psegs); [reflexivity| lia| rewrite psegs_top; exact Hx].
Qed.

Section Entry.
  Variables (R F : bvmap 5 word) (blk av : Z) (canary : word) (x16 x6 x11 x12 x23 rnd : Z) (w0 : word).

  Definition xs_E0 : env :=
    Env (fun n => if (n <? 32)%nat then reg_get R (Z_to_bv 5 (Z.of_nat n))
                  else if ((64 <=? n) && (n <? 96))%nat%bool then reg_get F (Z_to_bv 5 (Z.of_nat n - 64))
                  else nth (n - 40)%nat [wz blk; wz av; canary; wz x16; wz x11; wz rnd; wz x12; wz x23; wz x6; w0] (wz 0))
        (fun _ => []).

  Lemma xs_E0_reg : forall k, 0 <= k < 32 -> ev xs_E0 (Z.to_nat k) = reg_get R (Z_to_bv 5 k).
  Proof. intros k Hk. cbn [ev xs_E0]. replace (Z.to_nat k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite Z2Nat.id by lia. reflexivity. Qed.
  Lemma xs_E0_regn : forall n, (n < 32)%nat -> ev xs_E0 n = reg_get R (Z_to_bv 5 (Z.of_nat n)).
  Proof. intros n Hn. rewrite <- (Nat2Z.id n) at 1. apply xs_E0_reg. lia. Qed.
  Lemma xs_E0_fp : fp_ok xs_E0 F.
  Proof.
    intros i Hi. cbn [ev xs_E0]. replace (FPB + i <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; unfold FPB; lia).
    replace ((64 <=? FPB + i)%nat && (FPB + i <? 96)%nat)%bool with true.
    2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le| apply Nat.ltb_lt]; unfold FPB; lia. }
    f_equal. f_equal. unfold FPB. lia.
  Qed.
  Lemma xs_E0_40 : ev xs_E0 40 = wz blk. Proof. reflexivity. Qed.
  Lemma xs_E0_41 : ev xs_E0 41 = wz av. Proof. reflexivity. Qed.
  Lemma xs_E0_42 : ev xs_E0 42 = canary. Proof. reflexivity. Qed.
End Entry.

Lemma know_ok_app : forall E m k1 k2, know_ok psegs E m k1 -> know_ok psegs E m k2 -> know_ok psegs E m (k1 ++ k2).
Proof. intros. unfold know_ok. apply Forall_app. split; assumption. Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells psegs m A cs -> bytes_at psegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma kbytes_ok : forall E m a (bs : list Z),
  0 <= a -> a + Z.of_nat (length bs) < 2^64 -> Forall (fun b => 0 <= b < 256) bs ->
  bytes_at psegs m a (map (fun b => Z_to_bv 8 b) bs) -> know_ok psegs E m (kbytes a bs).
Proof.
  intros E m a bs. revert a. induction bs as [|b bs IH]; intros a Ha Hh HF B; [constructor|].
  cbn [kbytes]. cbn [length] in Hh. apply Forall_cons_iff in HF as [Hb HF]. cbn [map] in B. change (Z_to_bv 8 b :: map _ bs) with ([Z_to_bv 8 b] ++ map (fun b => Z_to_bv 8 b) bs) in B.
  apply Mem.bytes_at_app in B as [B1 B2]. cbn [length Z.of_nat Pos.of_succ_nat] in B2.
  constructor.
  - assert (U0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; rewrite unsigned_lit; lia).
    apply (kword_at E m (ELit 0) a 1 (ELit b)); rewrite ?U0; [lia| lia| lia|].
    cbn [edenot]. unfold word_to_le_bytes. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite Z.add_0_l. exact B1.
  - apply IH; [lia| lia| exact HF| exact B2].
Qed.

(* The auxv words [kn_walk] names, from [rauxv_ok]'s vector [u64s (map wz (flat_pairs L ++ [0; 0]))]. *)
Lemma xs_fp_len : forall L, length (flat_pairs L) = (2 * length L)%nat.
Proof. induction L as [|[k v] L IH]; [reflexivity|]. cbn [flat_pairs length]. rewrite IH. lia. Qed.

Lemma xs_fp_nth : forall L i p, nth_error L i = Some p ->
  nth_error (flat_pairs L) (2 * i) = Some (fst p) /\ nth_error (flat_pairs L) (2 * i + 1) = Some (snd p).
Proof.
  induction L as [|[k v] L IH]; intros i p H; [destruct i; discriminate|].
  destruct i as [|i].
  - cbn in H. injection H as <-. split; reflexivity.
  - cbn [nth_error] in H. destruct (IH i p H) as [H1 H2].
    replace (2 * S i + 1)%nat with (S (S (2 * i + 1))) by lia. replace (2 * S i)%nat with (S (S (2 * i))) by lia.
    split; [exact H1| exact H2].
Qed.

Lemma xs_u64s_word : forall m a ws j w, bytes_at psegs m a (u64s ws) -> nth_error ws j = Some w ->
  bytes_at psegs m (a + 8 * Z.of_nat j) (le8 w).
Proof.
  intros m a ws j w B Hn. destruct (u64s_split _ _ _ Hn) as (pre & post & _ & _ & Eu & Hlu).
  rewrite Eu in B. apply Mem.bytes_at_app in B as [_ B]. rewrite Hlu in B.
  apply Mem.bytes_at_app in B as [B _]. replace (a + Z.of_nat (8 * j)) with (a + 8 * Z.of_nat j) in B by lia. exact B.
Qed.

Lemma xs_readable : forall m a bs i, bytes_at psegs m a bs -> 0x105000 <= a -> (i < length bs)%nat ->
  m (wa (a + Z.of_nat i)) <> None.
Proof.
  intros m a bs i (H0 & H1 & H) Ha Hi E. specialize (H i Hi). unfold mrd in H. rewrite E in H.
  assert (SR : OSSVerify.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom psegs (wa (a + Z.of_nat i)) = None)
    by (apply seg_rom_high; rewrite wa_unsigned by lia; lia).
  assert (SR' : OSSVerify.Proofs.simdjson.fuzz_element.lib.Common.PropExec.seg_rom psegs (wa (a + Z.of_nat i)) = None) by exact SR.
  rewrite SR' in H. cbn in H. symmetry in H. apply nth_error_None in H. lia.
Qed.

Lemma xs_keys_ok : forall E m av (W : list Z) (j : nat) (ks : list Z),
  bv_unsigned (edenot E XAUXV) = av -> 0 <= av ->
  bytes_at psegs m av (u64s (map wz W)) -> av + 8 * Z.of_nat (length W) <= 2^64 ->
  (forall i k, nth_error ks i = Some k -> nth_error W (j + 2 * i) = Some k) ->
  know_ok psegs E m (kn_keys (8 * Z.of_nat j) ks).
Proof.
  intros E m av W j ks UAV H0 B HW. revert j. induction ks as [|k ks IH]; intros j HN; [constructor|].
  cbn [kn_keys]. constructor.
  - pose proof (HN 0%nat k eq_refl) as N0. rewrite Nat.mul_0_r, Nat.add_0_r in N0.
    assert (Hj : (j < length W)%nat) by (apply nth_error_Some; rewrite N0; discriminate).
    apply kword_at; rewrite ?UAV; [lia| lia| lia|]. cbn [edenot].
    exact (xs_u64s_word m av (map wz W) j (wz k) B ltac:(rewrite nth_error_map, N0; reflexivity)).
  - replace (8 * Z.of_nat j + 16) with (8 * Z.of_nat (j + 2)) by lia. refine (IH (j + 2)%nat _).
    intros i k' Hi. replace (j + 2 + 2 * i)%nat with (j + 2 * S i)%nat by lia. apply HN. exact Hi.
Qed.

(* The keys [kn_walk] names are the pairs' keys then AT_NULL's 0, at the even words. *)
Lemma xs_keys_nth : forall (L : list (Z * Z)) i k,
  nth_error (map fst L ++ [0]) i = Some k -> nth_error (flat_pairs L ++ [0; 0]) (2 * i) = Some k.
Proof.
  induction L as [|[k0 v0] L IH]; intros i k H.
  - destruct i as [|i]; cbn in H; [injection H as <-; reflexivity|]. destruct i; discriminate.
  - destruct i as [|i]; cbn in H.
    + injection H as <-. reflexivity.
    + replace (2 * S i)%nat with (S (S (2 * i))) by lia. exact (IH i k H).
Qed.

(* The value of pair [i] is the odd word [2 i + 1] of the vector. *)
Lemma xs_pair_val : forall (L : list (Z * Z)) i k v, nth_error L i = Some (k, v) ->
  nth_error (map wz (flat_pairs L ++ [0; 0])) (2 * i + 1) = Some (wz v).
Proof.
  intros L i k v H. destruct (xs_fp_nth L i (k, v) H) as [_ H2].
  rewrite nth_error_map, nth_error_app1; [rewrite H2; reflexivity|].
  apply nth_error_Some. rewrite H2. discriminate.
Qed.

Lemma stk_wr_at : forall m lo hi a n, stk psegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at psegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & ST) Ha Hn Hh. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (ST (a + i) ltac:(lia))).
Qed.

Section EntryOK.
  Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (blk lo B pc0 raval : Z) (canary w0 : word) (uw : bool).
  Let usp := bv_unsigned sp.
  Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (blk + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  Hypothesis HB : rw_cells psegs m blk [CB 144 (MallocRep.zeros 144)].
  Hypothesis RB : rblock_range blk 144.
  Hypothesis ST : stk psegs m lo (usp + 16).
  Hypothesis LO : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= usp - 16384.
  Hypothesis SPB : usp + 16 <= B.
  Hypothesis B62 : B < 2^62.
  Hypothesis AL : usp mod 16 = 0.
  Hypothesis AUX : rauxv_ok m B.
  Hypothesis MI : mem_inv psegs m.
  Hypothesis RELRO : pj_relro m.
  Hypothesis SSP : ssp_cells m canary.
  Hypothesis XD : rw_cells psegs m EL_XDATA [C8 (wz EL_XDATA_V0); C8 (wz EL_XDATA_V1)].
  Hypothesis HD : rw_cells psegs m EL_HDLR [C8 (wz EL_HDLR_V0); C8 (wz EL_HDLR_V1)].
  Hypothesis EHG : rw_cells psegs m EL_EHG [C8 (wz 0); C4 (wz 0)].
  Hypothesis UNW : rw_cells psegs m EL_UNW (uw_cells uw).
  Hypothesis W0S : rw_cells psegs m usp [C8 w0].
  Hypothesis RAS : rw_cells psegs m (usp + 8) [C8 (wz raval)].
  Hypothesis RAV : 0 <= raval < 2^64.

  (* The CONFIG_RSEQ value [b] is the one [rauxv_ok]'s walk fact names: the start state's
     knowledge of the auxv walk ([kn_walk]) is read at it. *)
  Theorem xs_entry : exists (b : bool) (E : env),
    CIX psegs fc E xs_W xs_RW m m (xs_ss0 pc0 raval uw b) (MS R F (Z_to_bv 64 pc0) fc None m (seg_rom psegs))
    /\ (forall k, 0 <= k < 32 -> ev E (Z.to_nat k) = reg_get R (Z_to_bv 5 k))
    /\ ev E 40 = wz blk /\ fp_ok E F.
  Proof.
    (* [rauxv_ok] is layout-agnostic in the revision: av, the pair list L, and the
       AT_RANDOM target rnd, with only generic bounds, and the walk fact: the keys of
       L for a CONFIG_RSEQ value [bw] and this binary's AT_PHDR, AT_PHENT and AT_PHNUM
       pairs.  The ten per-slot values the old ten-pair destruct named no longer exist. *)
    destruct AUX as (av & L & rnd & AC & AB & ARND & AH & HF).
    destruct AH as (H1 & H2 & H3 & H4 & H5 & H6).
    destruct HF as (_ & _ & _ & _ & bw & HKEYS & HP13 & HP14 & HP15).
    pose proof alloc_ceiling_range as CR.
    destruct RB as (RB1 & RB2 & RB3 & RB4 & RB5).
    exists bw.
    exists (xs_E0 R F blk av canary 0 0 0 0 0 0 w0).
    split; [| split; [apply xs_E0_reg| split; [reflexivity| apply xs_E0_fp]]].
    split; [cbn; unfold FPB; lia|].
    intros E' HA. destruct HA as [HA _].

    assert (EV : forall k, (k < 200)%nat -> ev E' k = ev (xs_E0 R F blk av canary 0 0 0 0 0 0 w0) k) by (intros k Hk; symmetry; apply HA; exact Hk).
    assert (E2 : ev E' 2 = sp) by (rewrite EV by lia; etransitivity; [apply (xs_E0_reg R F blk av canary 0 0 0 0 0 0 w0 2); lia| reflexivity]).
    assert (E40 : ev E' 40 = wz blk) by (rewrite EV by lia; reflexivity).
    assert (E41 : ev E' 41 = wz av) by (rewrite EV by lia; reflexivity).
    assert (E42 : ev E' 42 = canary) by (rewrite EV by lia; reflexivity).
    (* E43..E48 are gone with [kn_auxv]: those env slots now hold 0 and nothing reads them. *)
    assert (E49 : ev E' 49 = w0) by (rewrite EV by lia; reflexivity).
    assert (USP : bv_unsigned (edenot E' XSP) = usp) by (cbn [edenot XSP]; rewrite E2; reflexivity).
    assert (UBLK : bv_unsigned (edenot E' XBLK) = blk) by (cbn [edenot XBLK]; rewrite E40; apply unsigned_lit; lia).
    assert (UAV : bv_unsigned (edenot E' XAUXV) = av) by (cbn [edenot XAUXV]; rewrite E41; apply unsigned_lit; lia).
    assert (U0 : bv_unsigned (edenot E' (ELit 0)) = 0) by (cbn [edenot]; apply unsigned_lit; lia).
    exists R, F. cbn [s_pc s_regs s_log s_know s_next mem_denot xs_ss0].
    split; [reflexivity|].
    split.
    {
      intros r. reg_cases r;
        lazymatch goal with |- getr _ ?rr = edenot E' (sr_get xs_regs0 ?rr) =>
          let e := eval vm_compute in (sr_get xs_regs0 rr) in change (sr_get xs_regs0 rr) with e end;
        lazymatch goal with
        | |- _ = edenot E' (EVar ?k) => cbn [edenot]; rewrite EV by lia;
              rewrite (xs_E0_regn R F blk av canary 0 0 0 0 0 0 w0 k) by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
              unfold getr; lazymatch goal with |- (if ?c then _ else _) = _ => let t := eval vm_compute in c in change c with t end; reflexivity
        | |- _ = edenot E' (ELit 0) => reflexivity
        | |- _ => idtac
        end.

      cbn [edenot XBLK]. rewrite E40, PropExec.alu_add. unfold PropExec.v_add. subst R.
      unfold getr; lazymatch goal with |- (if ?c then _ else _) = _ => let t := eval vm_compute in c in change c with t end.
      destruct (reg_get_mkR_1_10_11_12 ra sp gp tp t0 t1 t2 s0 s1 (wz (blk + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as (_ & G10 & _ & _).
      rewrite G10. unfold wz. rewrite !unsigned_lit by lia. reflexivity. }
    split; [exact I|].
    split.
    {
      pose proof (rw_cells_bytes _ _ _ HB) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
      destruct HB as [_ WB]. cbn [cells_size csize Nat.add] in WB.
      destruct EHG as [[_ BE] WE]. cbn [cells_bytes cbytes cells_size csize Nat.add] in BE, WE. rewrite app_nil_r in BE.
      destruct UNW as [[_ BU] WU].
      destruct SSP as [[[_ BS1] _] [[_ BS2] _]]. cbn [cells_bytes cbytes] in BS1, BS2. rewrite app_nil_r in BS1, BS2.
      destruct XD as [[_ BX] _]. cbn [cells_bytes cbytes] in BX. rewrite app_nil_r in BX.
      destruct HD as [[_ BH] _]. cbn [cells_bytes cbytes] in BH. rewrite app_nil_r in BH.
      destruct RAS as [[_ BR] _]. cbn [cells_bytes cbytes] in BR. rewrite app_nil_r in BR.
      destruct W0S as [[_ B0] _]. cbn [cells_bytes cbytes] in B0. rewrite app_nil_r in B0.
      destruct AC as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
      unfold xs_kn0.
      apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app;
        [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app]]]]]]]].
      -   unfold kn_geom.
        assert (GE : forall a b : Z, a <= b -> a <= b) by (intros; lia).
        unfold know_ok. repeat apply Forall_cons; [.. | apply Forall_nil]; cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off edenot];
          rewrite ?E2, ?E40, ?E41; rewrite ?unsigned_lit by lia; clear GE BB BE BU BS1 BS2 BX BH BR B0 BA AB ARND WB WE WU; lia.
      -   unfold kn_wr. constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
        + apply kwr_var; rewrite ?E2; try lia. eapply stk_wr_at; [exact ST| lia| lia| lia].
        + apply kwr_var; rewrite ?E40, ?unsigned_lit; try lia. rewrite Z.add_0_r. exact WB.
        + apply kwr_lit; try lia. exact WE.
        + apply kwr_lit; try lia. replace 8 with (Z.of_nat (cells_size (uw_cells uw))) by (destruct uw; reflexivity). exact WU.
      -   unfold kn_img. constructor; [apply kimg_ro_P; exact MI|]. constructor; [| constructor; [| constructor]].
        + apply kimg_of_none; [lia| lia|]. intros i Hi. apply RELRO. lia.
        + apply kimg_of_none; [lia| lia|]. intros i Hi. apply RELRO. lia.
      -   unfold kn_blk. apply kzeros_ok; rewrite ?UBLK; try lia. rewrite Z.add_0_r. exact BB.
      -   unfold kn_ehg. apply Mem.bytes_at_app in BE as [BE1 BE2]. rewrite Mem.length_le8 in BE2.
        constructor; [| constructor; [| constructor]]; apply kword_at; rewrite ?U0; try lia; cbn [edenot]; [exact BE1| exact BE2].
      -   unfold kn_unw. apply kbytes_ok; [lia| destruct uw; cbn; lia| destruct uw; cbn; repeat constructor; lia|].
        destruct uw; cbn [uw_bytes map uw_cells cells_bytes cbytes app] in BU |- *; [exact BU|]. exact BU.
      -   constructor; [| constructor; [| constructor]]; apply kword_at; rewrite ?USP; try lia; cbn [edenot].
        + rewrite E49, Z.add_0_r. exact B0.
        + exact BR.
      -   unfold kn_consts.
        apply Mem.bytes_at_app in BX as [BX1 BX2]. rewrite Mem.length_le8 in BX2.
        apply Mem.bytes_at_app in BH as [BH1 BH2]. rewrite Mem.length_le8 in BH2.
        repeat (apply Forall_cons; [apply kword_at; rewrite ?U0; try lia; cbn [edenot]; rewrite ?Z.add_0_l; first [exact BS1| exact BX1| exact BX2| exact BH1| exact BH2] |]); apply Forall_nil.
      -   unfold kn_cells. constructor; [| constructor; [| constructor]]; apply kword_at; rewrite ?U0; try lia; cbn [edenot XAUXV].
        + rewrite E42. exact BS2.
        + rewrite E41. exact BA.
      -   unfold kn_walk.
        assert (LLEN : length L = length (rauxv_keys bw)) by (rewrite <- HKEYS, length_map; reflexivity).
        assert (SPL : auxv_span bw = 16 * (Z.of_nat (length L) + 1)) by (unfold auxv_span; rewrite LLEN; reflexivity).
        assert (LL : (15 < length L)%nat) by (apply nth_error_Some; rewrite HP15; discriminate).
        assert (WL : length (flat_pairs L ++ [0; 0]) = (2 * length L + 2)%nat) by (rewrite length_app, xs_fp_len; reflexivity).
        apply know_ok_app; [| apply know_ok_app].
        + (* the vector lies above the frame and the block: [B <= av] *)
          constructor; [| constructor; [| constructor]]; cbn [kentry_ok]; left; unfold estart; cbn [a_base a_off];
            rewrite ?USP, ?UBLK, ?UAV, elenZ_lit' by lia; lia.
        + refine (xs_keys_ok E' m av (flat_pairs L ++ [0; 0]) 0 (rauxv_keys bw ++ [0]) UAV ltac:(lia) AB ltac:(rewrite WL; lia) _).
          intros i k Hk. rewrite ?Nat.add_0_l. apply xs_keys_nth. rewrite HKEYS. exact Hk.
        + constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
          * apply kword_at; rewrite ?UAV; try lia. replace (av + 216) with (av + 8 * Z.of_nat (2 * 13 + 1)) by lia.
            exact (xs_u64s_word m av _ _ _ AB (xs_pair_val L 13 _ _ HP13)).
          * apply kword_at; rewrite ?UAV; try lia. replace (av + 232) with (av + 8 * Z.of_nat (2 * 14 + 1)) by lia.
            exact (xs_u64s_word m av _ _ _ AB (xs_pair_val L 14 _ _ HP14)).
          * apply kword_at; rewrite ?UAV; try lia. replace (av + 248) with (av + 8 * Z.of_nat (2 * 15 + 1)) by lia.
            exact (xs_u64s_word m av _ _ _ AB (xs_pair_val L 15 _ _ HP15)).
          * cbn [kentry_ok]. rewrite (elenZ_lit' E' (auxv_span bw)) by lia.
            unfold flat, estart. cbn [a_base a_off]. rewrite UAV.
            split; [lia|]. intros i Hi.
            assert (Hlen : (Z.to_nat i < length (u64s (map wz (flat_pairs L ++ [0%Z; 0%Z]))))%nat)
              by (rewrite u64s_length, length_map, WL; lia).
            pose proof (xs_readable m av _ (Z.to_nat i) AB ltac:(lia) Hlen) as RD.
            rewrite Z2Nat.id in RD by lia. unfold wa in RD. rewrite Z.add_0_r. exact RD.
      }
    split; [apply fullR_mkR|].
    split. { intros i Hi. rewrite EV by (unfold FPB; lia). apply xs_E0_fp. exact Hi. }
    cbn [ms_mem MS].
    split; [exact MI|]. split; [apply wmono_refl|]. split; [intros; reflexivity|]. split; [reflexivity|].

    intros x (wb & wlo & whi & HIn & Hx). cbn in HIn. destruct HIn as [HIn|[]]. injection HIn as <- <- <-.
    cbn [edenot XSP] in Hx. rewrite E2 in Hx.
    destruct ST as (_ & _ & STA). destruct (STA (bv_unsigned x) ltac:(lia)) as [_ [b Hb]].
    assert (SR : OSSVerify.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom psegs x = None) by (apply seg_rom_high; lia).
    split; [| exact SR].
    unfold mrd in Hb. unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb.
    destruct (m x) as [b'|] eqn:Emx; [discriminate|]. exfalso.
    assert (SR' : OSSVerify.Proofs.simdjson.fuzz_element.lib.Common.PropExec.seg_rom psegs x = None) by exact SR. rewrite SR' in Hb. discriminate.
  Qed.
End EntryOK.

Definition kentry_eqb_word (a : saddr) (w : nat) (v : expr) (K : kentry) : bool :=
  match K with KWord a' w' v' => (saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v')%bool | _ => false end.
Definition kn_has_word (kn : list kentry) (a : saddr) (w : nat) (v : expr) : bool := existsb (kentry_eqb_word a w v) kn.

Definition exit_check (s : sym_state) : bool :=
  (Z.eqb (s_pc s) XS_END
   && match s_log s with [] => true | _ => false end
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 10)) XBLK
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 1)) (ELit 0x7007c)
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 2)) (EAlu ALU_ADD XSP (ELit (-16)))
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 3)) (EVar 3)
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 4)) (EVar 4)
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 25)) (EVar 25) && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 26)) (EVar 26) && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 27)) (EVar 27)
   && kn_has_word (s_know s) (SA (ELit 0) EL_EHG) 8 (ELit 0)
   && kn_has_word (s_know s) (SA (ELit 0) (EL_EHG + 8)) 4 (ELit 0)
   && forallb (fun i => kn_has_word (s_know s) (SA (ELit 0) (EL_UNW + Z.of_nat i)) 1 (ELit (nth i (uw_bytes true) 0))) (seq 0 8)
   && kn_has_word (s_know s) (SA XSP 8) 8 (ELit 0x3bfb4))%bool.
Definition exit_ok (o : option sym_state) : bool := match o with Some s => exit_check s | None => false end.

Definition XS_FUEL : nat := 300000.
Definition XS_K : nat := 80.
