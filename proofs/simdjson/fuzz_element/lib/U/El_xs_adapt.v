(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac RegsEquiv Arr Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Sj_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import InitMem Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound El_xs_kitP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Notation EL_EHG := (0xedb98)%Z (only parsing).
Notation EL_UNW := (0xef4b0)%Z (only parsing).
Notation XS_END := (0x7c1b8)%Z (only parsing).

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
   KRange XAUXV 0x700000000000 0xffffffffffffff60;
   KDisj (SA XSP (-16384)) (ELit 16400) (SA XBLK 0) (ELit 144);
   KDisj (SA XSP (-16384)) (ELit 16400) (SA XAUXV 0) (ELit 160);
   KDisj (SA XBLK 0) (ELit 144) (SA XAUXV 0) (ELit 160);
   KDisj (SA XBLK 0) (ELit 144) (SA (ELit 0) 0x10000) (ELit 0x101000)].
Definition kn_wr : list kentry :=
  [KWr (SA XSP (-16384)) (ELit 16400); KWr (SA XBLK 0) (ELit 144); KWr (SA (ELit 0) EL_EHG) (ELit 12); KWr (SA (ELit 0) EL_UNW) (ELit 8)].
Definition kn_img : list kentry := [KImg 0x10000 0xd6000; KImg 0xd6810 0xdc448; KImg 0xdc450 0xdc478].
Definition kn_blk : list kentry := kzeros XBLK 0 144.
Definition kn_ehg : list kentry := [KWord (SA (ELit 0) EL_EHG) 8 (ELit 0); KWord (SA (ELit 0) (EL_EHG + 8)) 4 (ELit 0)].
Fixpoint kbytes (a : Z) (bs : list Z) : list kentry :=
  match bs with [] => [] | b :: bs' => KWord (SA (ELit 0) a) 1 (ELit b) :: kbytes (a + 1) bs' end.
Definition kn_unw (uw : bool) : list kentry := kbytes EL_UNW (uw_bytes uw).
Definition kn_consts : list kentry :=
  [KWord (SA (ELit 0) 0xdc448) 8 (ELit 0x10f7f8);
   KWord (SA (ELit 0) 0xdd4a0) 8 (ELit 0xd9b48); KWord (SA (ELit 0) 0xdd4a8) 8 (ELit 0x7c284);
   KWord (SA (ELit 0) 0xdd7b8) 8 (ELit 0x5f084); KWord (SA (ELit 0) 0xdd7c0) 8 (ELit 0x5f190)].
Definition kn_cells : list kentry :=
  [KWord (SA (ELit 0) 0x10f7f8) 8 (EVar 42); KWord (SA (ELit 0) 0x10f820) 8 XAUXV].
Definition kn_auxv : list kentry :=
  [KWord (SA XAUXV 0) 8 (ELit 3); KWord (SA XAUXV 8) 8 (ELit 0x10040);
   KWord (SA XAUXV 16) 8 (ELit 4); KWord (SA XAUXV 24) 8 (ELit 56);
   KWord (SA XAUXV 32) 8 (ELit 5); KWord (SA XAUXV 40) 8 (ELit 10);
   KWord (SA XAUXV 48) 8 (ELit 16); KWord (SA XAUXV 56) 8 (EVar 43);
   KWord (SA XAUXV 64) 8 (ELit 6); KWord (SA XAUXV 72) 8 (EVar 48);
   KWord (SA XAUXV 80) 8 (ELit 11); KWord (SA XAUXV 88) 8 (EVar 44);
   KWord (SA XAUXV 96) 8 (ELit 12); KWord (SA XAUXV 104) 8 (EVar 46);
   KWord (SA XAUXV 112) 8 (ELit 23); KWord (SA XAUXV 120) 8 (EVar 47);
   KWord (SA XAUXV 128) 8 (ELit 25); KWord (SA XAUXV 136) 8 (EVar 45);
   KWord (SA XAUXV 144) 8 (ELit 0); KWord (SA XAUXV 152) 8 (ELit 0)].
Definition xs_kn0 (raval : Z) (uw : bool) : list kentry :=
  kn_geom ++ kn_wr ++ kn_img ++ kn_blk ++ kn_ehg ++ kn_unw uw ++ [KWord (SA XSP 0) 8 (EVar 49); KWord (SA XSP 8) 8 (ELit raval)] ++ kn_consts ++ kn_cells ++ kn_auxv.
Definition xs_ss0 (pc0 raval : Z) (uw : bool) : sym_state := SS pc0 xs_regs0 [] (xs_kn0 raval uw) 200.

Lemma estart_lit : forall E a, estart E (SA (ELit 0) a) = a.
Proof. intros E a. unfold estart. cbn [a_base a_off edenot]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia. Qed.
Lemma elenZ_lit' : forall E n, 0 <= n < 2^64 -> elenZ E (ELit n) = n.
Proof. intros E n H. rewrite elenZ_lit. apply Z.mod_small. exact H. Qed.

Lemma kwr_lit : forall E (m : word -> option byte) a n,
  0 <= a -> 0 <= n -> a + n < 2^64 -> wr_at usegs m a n -> kentry_ok usegs E m (KWr (SA (ELit 0) a) (ELit n)).
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
  wr_at usegs m (bv_unsigned (ev E v) + off) n -> kentry_ok usegs E m (KWr (SA (EVar v) off) (ELit n)).
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
  bytes_at usegs m (bv_unsigned (edenot E b) + off) (word_to_le_bytes w (edenot E v)) ->
  kentry_ok usegs E m (KWord (SA b off) w v).
Proof.
  intros E m b off w v Hw Ha Hh B. cbn [kentry_ok]. split; [lia|].
  assert (ES : estart E (SA b off) = bv_unsigned (edenot E b) + off) by reflexivity.
  split; [unfold flat; rewrite ES; lia|].
  pose proof (Mem.bytes_at_rdn usegs m _ _ 0 w B) as X.
  rewrite length_N_to_le_bytes in X. specialize (X ltac:(lia)). cbn [skipn Z.of_nat] in X. rewrite Z.add_0_r in X.
  rewrite firstn_all2 in X by (rewrite length_N_to_le_bytes; lia).
  rewrite rdn_common in X. rewrite adenot_SA. unfold wa in X. exact X.
Qed.

Lemma kimg_of_none : forall E (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2^64 -> (forall i, lo <= i < hi -> m (wa i) = None) -> kentry_ok usegs E m (KImg lo hi).
Proof. intros E m lo hi Hlo Hhi H. cbn [kentry_ok]. split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi. unfold wa in H. apply H. exact Hi. Qed.

Lemma psegs_ro : forall i, 0x10000 <= i < 0xd6000 -> ro_addr usegs (wa i) = true.
Proof.
  intros i Hi. unfold ro_addr. unfold wa. rewrite unsigned_lit by lia.
  unfold usegs. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N].
  destruct (Z.leb_spec0 65536 i); destruct (Z.leb_spec0 (i + 1) (65536 + 176128)); cbn [andb]; try reflexivity; try lia.
  destruct (Z.leb_spec0 241664 i); destruct (Z.leb_spec0 (i + 1) (241664 + 634880)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma kimg_ro_P : forall E (m : word -> option byte), mem_inv usegs m -> kentry_ok usegs E m (KImg 0x10000 0xd6000).
Proof.
  intros E m MI. apply kimg_of_none; [lia| lia|]. intros i Hi.
  destruct (m (wa i)) as [b|] eqn:Em; [|reflexivity]. exfalso.
  pose proof (Mem.mem_inv_ro usegs m (wa i) b MI Em) as X. rewrite psegs_ro in X by exact Hi. discriminate.
Qed.

Lemma psegs_top : InitMem.segs_top usegs = 0x111000.
Proof. reflexivity. Qed.
Lemma seg_rom_high : forall x : word, 0x111000 <= bv_unsigned x -> OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom usegs x = None.
Proof.
  intros x Hx. unfold PropExec.seg_rom, memory_read.
  rewrite (InitMem.find_segment_high usegs); [reflexivity| lia| rewrite psegs_top; exact Hx].
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

Lemma know_ok_app : forall E m k1 k2, know_ok usegs E m k1 -> know_ok usegs E m k2 -> know_ok usegs E m (k1 ++ k2).
Proof. intros. unfold know_ok. apply Forall_app. split; assumption. Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells usegs m A cs -> bytes_at usegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma kbytes_ok : forall E m a (bs : list Z),
  0 <= a -> a + Z.of_nat (length bs) < 2^64 -> Forall (fun b => 0 <= b < 256) bs ->
  bytes_at usegs m a (map (fun b => Z_to_bv 8 b) bs) -> know_ok usegs E m (kbytes a bs).
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

Lemma kn_auxv_ok : forall E m av x16 x6 x11 x12 x23 rnd,
  ev E 41 = wz av -> ev E 43 = wz x16 -> ev E 48 = wz x6 -> ev E 44 = wz x11 -> ev E 46 = wz x12 -> ev E 47 = wz x23 -> ev E 45 = wz rnd ->
  0 <= av -> av + 160 <= 2^64 ->
  bytes_at usegs m av (u64s (auxv_list 0x10040 56 10 x16 x6 x11 x12 x23 rnd)) ->
  know_ok usegs E m kn_auxv.
Proof.
  intros E m av x16 x6 x11 x12 x23 rnd E41 E43 E48 E44 E46 E47 E45 Ha Hh B.
  unfold auxv_list in B. cbn [map u64s] in B. rewrite !app_nil_r in B.
  assert (UA : bv_unsigned (edenot E XAUXV) = av) by (cbn [edenot XAUXV]; rewrite E41; apply unsigned_lit; lia).
  unfold kn_auxv.
  do 19 (let B1 := fresh "B1" in
         apply Mem.bytes_at_app in B as [B1 B]; rewrite Mem.length_le8 in B;
         lazymatch type of B with bytes_at _ _ (?x + ?y + ?z) _ => let w := eval cbv in (y + z) in replace (x + y + z) with (x + w) in B by lia | _ => idtac end;
         constructor; [apply kword_at; rewrite ?UA; [lia| lia| lia| cbn [edenot]; unfold Mem.le8 in B1;
           rewrite ?E43, ?E48, ?E44, ?E46, ?E47, ?E45; rewrite ?Z.add_0_r;
           lazymatch goal with |- bytes_at _ _ ?a _ => lazymatch type of B1 with bytes_at _ _ ?a' _ => replace a with a' by lia end end; exact B1 ] |]).
  constructor; [| constructor]. apply kword_at; rewrite ?UA; [lia| lia| lia|]. cbn [edenot]. unfold Mem.le8 in B. exact B.
Qed.

Lemma stk_wr_at : forall m lo hi a n, stk usegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at usegs m a n.
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
  Hypothesis HB : rw_cells usegs m blk [CB 144 (MallocRep.zeros 144)].
  Hypothesis RB : rblock_range blk 144.
  Hypothesis ST : stk usegs m lo (usp + 16).
  Hypothesis LO : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= usp - 16384.
  Hypothesis SPB : usp + 16 <= B.
  Hypothesis B62 : B < 2^62.
  Hypothesis AL : usp mod 16 = 0.
  Hypothesis AUX : rauxv_ok m B.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis RELRO : pj_relro m.
  Hypothesis SSP : ssp_cells m canary.
  Hypothesis XD : rw_cells usegs m EL_XDATA [C8 (wz EL_XDATA_V0); C8 (wz EL_XDATA_V1)].
  Hypothesis HD : rw_cells usegs m EL_HDLR [C8 (wz EL_HDLR_V0); C8 (wz EL_HDLR_V1)].
  Hypothesis EHG : rw_cells usegs m EL_EHG [C8 (wz 0); C4 (wz 0)].
  Hypothesis UNW : rw_cells usegs m EL_UNW (uw_cells uw).
  Hypothesis W0S : rw_cells usegs m usp [C8 w0].
  Hypothesis RAS : rw_cells usegs m (usp + 8) [C8 (wz raval)].
  Hypothesis RAV : 0 <= raval < 2^64.

  Theorem xs_entry : exists E : env,
    CIX usegs fc E xs_W xs_RW m m (xs_ss0 pc0 raval uw) (MS R F (Z_to_bv 64 pc0) fc None m (seg_rom usegs))
    /\ (forall k, 0 <= k < 32 -> ev E (Z.to_nat k) = reg_get R (Z_to_bv 5 k))
    /\ ev E 40 = wz blk /\ fp_ok E F.
  Proof.
    destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AB & ARND & AH).
    destruct AH as (H1 & H2 & H3 & H4 & H5 & R3 & R4 & R5 & R16 & R6 & R11 & R12 & R23 & RR & P3 & P4 & P5).
    lazy in P3. lazy in P4. lazy in P5. subst x3 x4 x5.
    pose proof alloc_ceiling_range as CR.
    destruct RB as (RB1 & RB2 & RB3 & RB4 & RB5).
    exists (xs_E0 R F blk av canary x16 x6 x11 x12 x23 rnd w0).
    split; [| split; [apply xs_E0_reg| split; [reflexivity| apply xs_E0_fp]]].
    split; [cbn; unfold FPB; lia|].
    intros E' HA. destruct HA as [HA _].

    assert (EV : forall k, (k < 200)%nat -> ev E' k = ev (xs_E0 R F blk av canary x16 x6 x11 x12 x23 rnd w0) k) by (intros k Hk; symmetry; apply HA; exact Hk).
    assert (E2 : ev E' 2 = sp) by (rewrite EV by lia; etransitivity; [apply (xs_E0_reg R F blk av canary x16 x6 x11 x12 x23 rnd w0 2); lia| reflexivity]).
    assert (E40 : ev E' 40 = wz blk) by (rewrite EV by lia; reflexivity).
    assert (E41 : ev E' 41 = wz av) by (rewrite EV by lia; reflexivity).
    assert (E42 : ev E' 42 = canary) by (rewrite EV by lia; reflexivity).
    assert (E43 : ev E' 43 = wz x16) by (rewrite EV by lia; reflexivity).
    assert (E44 : ev E' 44 = wz x11) by (rewrite EV by lia; reflexivity).
    assert (E45 : ev E' 45 = wz rnd) by (rewrite EV by lia; reflexivity).
    assert (E46 : ev E' 46 = wz x12) by (rewrite EV by lia; reflexivity).
    assert (E47 : ev E' 47 = wz x23) by (rewrite EV by lia; reflexivity).
    assert (E48 : ev E' 48 = wz x6) by (rewrite EV by lia; reflexivity).
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
              rewrite (xs_E0_regn R F blk av canary x16 x6 x11 x12 x23 rnd w0 k) by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
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
      apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app; [| apply know_ok_app]]]]]]]].
      -   unfold kn_geom.
        assert (GE : forall a b : Z, a <= b -> a <= b) by (intros; lia).
        unfold know_ok. repeat apply Forall_cons; [.. | apply Forall_nil]; cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off edenot];
          rewrite ?E2, ?E40, ?E41; rewrite ?unsigned_lit by lia; clear GE BB BE BU BS1 BS2 BX BH BR B0 BA ARND WB WE WU; lia.
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
      -   eapply kn_auxv_ok; try eassumption; lia. }
    split; [apply fullR_mkR|].
    split. { intros i Hi. rewrite EV by (unfold FPB; lia). apply xs_E0_fp. exact Hi. }
    cbn [ms_mem MS].
    split; [exact MI|]. split; [apply wmono_refl|]. split; [intros; reflexivity|]. split; [reflexivity|].

    intros x (wb & wlo & whi & HIn & Hx). cbn in HIn. destruct HIn as [HIn|[]]. injection HIn as <- <- <-.
    cbn [edenot XSP] in Hx. rewrite E2 in Hx.
    destruct ST as (_ & _ & STA). destruct (STA (bv_unsigned x) ltac:(lia)) as [_ [b Hb]].
    assert (SR : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom usegs x = None) by (apply seg_rom_high; lia).
    split; [| exact SR].
    unfold mrd in Hb. unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb.
    destruct (m x) as [b'|] eqn:Emx; [discriminate|]. exfalso.
    assert (SR' : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Common.PropExec.seg_rom usegs x = None) by exact SR. rewrite SR' in Hb. discriminate.
  Qed.
End EntryOK.

Definition kentry_eqb_word (a : saddr) (w : nat) (v : expr) (K : kentry) : bool :=
  match K with KWord a' w' v' => (saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v')%bool | _ => false end.
Definition kn_has_word (kn : list kentry) (a : saddr) (w : nat) (v : expr) : bool := existsb (kentry_eqb_word a w v) kn.

Definition exit_check (s : sym_state) : bool :=
  (Z.eqb (s_pc s) XS_END
   && match s_log s with [] => true | _ => false end
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 10)) XBLK
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 1)) (ELit 0x7bc7c)
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 2)) (EAlu ALU_ADD XSP (ELit (-16)))
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 3)) (EVar 3)
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 4)) (EVar 4)
   && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 25)) (EVar 25) && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 26)) (EVar 26) && expr_eqb (sr_get (s_regs s) (Z_to_bv 5 27)) (EVar 27)
   && kn_has_word (s_know s) (SA (ELit 0) EL_EHG) 8 (ELit 0)
   && kn_has_word (s_know s) (SA (ELit 0) (EL_EHG + 8)) 4 (ELit 0)
   && forallb (fun i => kn_has_word (s_know s) (SA (ELit 0) (EL_UNW + Z.of_nat i)) 1 (ELit (nth i (uw_bytes true) 0))) (seq 0 8)
   && kn_has_word (s_know s) (SA XSP 8) 8 (ELit 0x3c520))%bool.
Definition exit_ok (o : option sym_state) : bool := match o with Some s => exit_check s | None => false end.

Definition XS_FUEL : nat := 300000.
Definition XS_K : nat := 80.
