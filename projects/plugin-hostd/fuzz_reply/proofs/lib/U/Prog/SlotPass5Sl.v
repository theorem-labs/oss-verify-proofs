From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRep HarnessRep relay_source_c
  relay_reads_c SlotPass5Run.
Import ListNotations.
Local Open Scope Z_scope.

Definition p5sl_call (SP lo op : Z) (m m' : word -> option byte) : Prop :=
  (op = 0 /\ m' = m) \/
  (op <> 0 /\ munch [(SP - RELAY_READS_K, SP)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP).

Fixpoint p5sl_mem (SP lo : Z) (es : list rentry) (fd op : nat -> Z) (k : nat) (m m' : word -> option byte)
    : Prop :=
  match k with
  | O => m' = m
  | S j => exists m1 m2 : word -> option byte,
      p5sl_mem SP lo es fd op j m m1 /\ p5sl_call SP lo (op j) m1 m2 /\
      m' = write_to_mem m2 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat j)) (le4 (Z_to_bv 64 (op5_rec es (fd j) (op j))))
  end.

Lemma p5sl_mem_S : forall (SP lo : Z) (es : list rentry) (fd op : nat -> Z) (j : nat) (m m1 m2 : word -> option byte),
  p5sl_mem SP lo es fd op j m m1 -> p5sl_call SP lo (op j) m1 m2 ->
  p5sl_mem SP lo es fd op (S j) m
    (write_to_mem m2 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat j)) (le4 (Z_to_bv 64 (op5_rec es (fd j) (op j))))).
Proof.
  intros SP lo es fd op j m m1 m2 H1 H2. exists m1, m2. split; [exact H1|split; [exact H2|reflexivity]].
Qed.

Lemma p5sl_ret : ret_pc (Z_to_bv 64 0x144b0) = Z_to_bv 64 0x144b0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma p5sl_iter : relay_reads_contract ->
  forall (SP lo fdi opi : Z) (es : list rentry) (g : word) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 -> lo + RELAY_READS_K <= SP -> 0 <= opi < 2 ^ 31 ->
  Z.of_nat (length es) < 2 ^ 31 -> Forall (fun e => -2 ^ 31 <= re_eof e < 2 ^ 31) es ->
  (es <> [] -> bv_unsigned g <> 0 /\ bv_unsigned g mod 8 = 0) ->
  (G_S + 384 <= SP - RELAY_READS_K \/ SP <= G_S) ->
  (G_NSRC + 4 <= SP - RELAY_READS_K \/ SP <= G_NSRC) ->
  (G_SRC + 8 <= SP - RELAY_READS_K \/ SP <= G_SRC) ->
  (es <> [] -> bv_unsigned g + 56 * Z.of_nat (length es) <= SP - RELAY_READS_K \/ SP <= bv_unsigned g) ->
  rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fdi); C4 (Z_to_bv 64 opi)] ->
  wr_at rsegs m (SP + 16) 16 ->
  (opi <> 0 -> -2 ^ 31 <= fdi < 2 ^ 31 /\
     bytes_at rsegs m G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es)))) /\ bytes_at rsegs m G_SRC (le8 g) /\
     src_table m (bv_unsigned g) es /\ mem_inv rsegs m /\ stk rsegs m lo SP /\
     (forall m2 : word -> option byte, munch [(SP - RELAY_READS_K, SP)] m m2 -> wmono rsegs m m2 ->
        wr_at rsegs m2 (SP + 16) 16)) ->
  evt rsegs (fun ms => exists (x1' x11' x12' x13' x14' x15' x16' x17' : word) (m2 : word -> option byte),
      p5sl_call SP lo opi m m2 /\
      op5_r_next SP i (op5_rec es fdi opi) x1' x3 x4 x5 x6 x7 x8 x9 x11' x12' x13' x14' x15' x16' x17' x20 x21 x22
        x24 x25 x26 x27 x28 x29 x30 x31 F fc m2 (seg_rom rsegs) ms)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x20 x21 x22 (Z_to_bv 64 (SP + 32))
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144a0) fc None m (seg_rom rsegs)).
Proof.
  intros RRC SP lo fdi opi es g i x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m Hi HS0 HS1 Hlo Hop Hlen HEof Hg HGS HNS HSR HGT HC WR HK.
  eapply evt_cut.
  { exact (op5_r_head SP fdi opi i x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26
             x27 x28 x29 x30 x31 F fc m (seg_rom rsegs) Hi HS0 HS1 Hop HC WR). }
  intros ms [(Hnz & ->)|(Hz & Hnx)].
  - destruct (HK Hnz) as (Hfd & HN & HG & HT & HI & HST & HW).
    assert (HB : bytes_at rsegs m (G_S + 96 * Z.of_nat i) (le4 (Z_to_bv 64 fdi))).
    { destruct HC as [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
      apply bytes_at_app in H. exact (proj1 H). }
    assert (HA : bv_unsigned (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) = G_S + 96 * Z.of_nat i)
      by (apply unsigned_lit; unfold G_S; lia).
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { apply (RRC (Z_to_bv 64 0x144b0) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
               (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29
               x30 x31 F fc m lo fdi g es).
      all: rewrite ?HA, ?HSP.
      all: first
        [ assumption
        | lia
        | (unfold G_S; lia)
        | (replace (G_S + 96 * Z.of_nat i) with ((25380 + 12 * Z.of_nat i) * 8) by (unfold G_S; lia);
           apply Z.mod_mul; lia) ]. }
    intros ms (a1 & a2 & a3 & a4 & a5 & a6 & a7 & m2 & -> & HMu & HWm & HI2 & HST2).
    rewrite HSP in HMu, HST2.
    rewrite p5sl_ret.
    replace (relay_reads_r fdi es) with (op5_rec es fdi opi)
      by (unfold op5_rec; rewrite (proj2 (Z.eqb_neq opi 0) Hnz), op5_hit_reads; reflexivity).
    eapply evt_mono.
    { exact (op5_r_ret SP (op5_rec es fdi opi) i (Z_to_bv 64 0x144b0) x3 x4 x5 x6 x7 x8 x9 a1 a2 a3 a4 a5 a6 a7 x20
               x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m2 (seg_rom rsegs) Hi HS0 HS1 (HW m2 HMu HWm)). }
    intros ms Hms. exists (Z_to_bv 64 0x144b0), a1, a2, a3, a4, a5, a6, a7, m2. split; [|exact Hms].
    right. exact (conj Hnz (conj HMu (conj HWm (conj HI2 HST2)))).
  - apply evt_done. exists x1, x11, x12, x13, x14, x15, x16, x17, m. split.
    + left. split; [exact Hz|reflexivity].
    + subst opi. replace (op5_rec es fdi 0) with 0 by reflexivity. exact Hnx.
Qed.

Lemma p5sl_rest : relay_reads_contract ->
  forall (SP lo : Z) (es : list rentry) (g : word) (fd op : nat -> Z)
    (x3 x4 x5 x6 x7 x8 x9 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 <= SP -> SP + 32 < 2 ^ 64 -> lo + RELAY_READS_K <= SP ->
  (forall i : nat, (i < 4)%nat -> 0 <= op i < 2 ^ 31 /\ (op i <> 0 -> -2 ^ 31 <= fd i < 2 ^ 31)) ->
  Z.of_nat (length es) < 2 ^ 31 -> Forall (fun e => -2 ^ 31 <= re_eof e < 2 ^ 31) es ->
  (es <> [] -> bv_unsigned g <> 0 /\ bv_unsigned g mod 8 = 0) ->
  (G_S + 384 <= SP - RELAY_READS_K \/ SP <= G_S) ->
  (G_NSRC + 4 <= SP - RELAY_READS_K \/ SP <= G_NSRC) ->
  (G_SRC + 8 <= SP - RELAY_READS_K \/ SP <= G_SRC) ->
  (es <> [] -> bv_unsigned g + 56 * Z.of_nat (length es) <= SP - RELAY_READS_K \/ SP <= bv_unsigned g) ->
  (forall (i : nat) (m1 : word -> option byte), (i < 4)%nat -> p5sl_mem SP lo es fd op i m m1 ->
     rw_cells rsegs m1 (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 (fd i)); C4 (Z_to_bv 64 (op i))] /\
     wr_at rsegs m1 (SP + 16) 16 /\
     (op i <> 0 ->
        bytes_at rsegs m1 G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es)))) /\ bytes_at rsegs m1 G_SRC (le8 g) /\
        src_table m1 (bv_unsigned g) es /\ mem_inv rsegs m1 /\ stk rsegs m1 lo SP /\
        (forall m2 : word -> option byte, munch [(SP - RELAY_READS_K, SP)] m1 m2 -> wmono rsegs m1 m2 ->
           wr_at rsegs m2 (SP + 16) 16))) ->
  forall (k i : nat) (x1 x10 x11 x12 x13 x14 x15 x16 x17 : word) (mi : word -> option byte),
  (i + k = 3)%nat -> p5sl_mem SP lo es fd op i m mi ->
  evt rsegs (fun ms => exists (x11' x12' x13' x14' x15' x16' x17' : word) (m' : word -> option byte),
      p5sl_mem SP lo es fd op 4 m m' /\
      ms = MS (mkR (Z_to_bv 64 0x144c8) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 (G_S + 384)) (Z_to_bv 64 (SP + 32)) x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27
                 x28 x29 x30 x31) F (Z_to_bv 64 0x13664) fc None m' (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x20 x21 x22 (Z_to_bv 64 (SP + 32))
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144a0) fc None mi (seg_rom rsegs)).
Proof.
  intros RRC SP lo es g fd op x3 x4 x5 x6 x7 x8 x9 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HS0 HS1 Hlo
    HR Hlen HEof Hg HGS HNS HSR HGT HP k.
  induction k as [|k IH]; intros i x1 x10 x11 x12 x13 x14 x15 x16 x17 mi Hk Hm.
  - assert (Hi : (i < 4)%nat) by lia.
    destruct (HR i Hi) as (Hop & Hfd). destruct (HP i mi Hi Hm) as (HC & WR & HK).
    eapply evt_cut.
    { exact (p5sl_iter RRC SP lo (fd i) (op i) es g i x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20
               x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc mi Hi HS0 HS1 Hlo Hop Hlen HEof Hg HGS HNS HSR HGT HC WR
               (fun Hnz => conj (Hfd Hnz) (HK Hnz))). }
    intros ms (x1' & y11 & y12 & y13 & y14 & y15 & y16 & y17 & m2 & Hcall & [(Hlt & _)|(H4 & ->)]); [lia|].
    assert (H3 : i = 3%nat) by lia. subst i.
    apply evt_done. exists y11, y12, y13, y14, y15, y16, y17. eexists.
    split; [exact (p5sl_mem_S SP lo es fd op 3 m mi m2 Hm Hcall)|reflexivity].
  - assert (Hi : (i < 4)%nat) by lia.
    destruct (HR i Hi) as (Hop & Hfd). destruct (HP i mi Hi Hm) as (HC & WR & HK).
    eapply evt_cut.
    { exact (p5sl_iter RRC SP lo (fd i) (op i) es g i x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20
               x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc mi Hi HS0 HS1 Hlo Hop Hlen HEof Hg HGS HNS HSR HGT HC WR
               (fun Hnz => conj (Hfd Hnz) (HK Hnz))). }
    intros ms (x1' & y11 & y12 & y13 & y14 & y15 & y16 & y17 & m2 & Hcall & [(_ & ->)|(H4 & _)]); [|lia].
    exact (IH (S i) x1' (Z_to_bv 64 (op5_rec es (fd i) (op i))) y11 y12 y13 y14 y15 y16 y17 _ ltac:(lia)
             (p5sl_mem_S SP lo es fd op i m mi m2 Hm Hcall)).
Qed.

Lemma p5_rloop : relay_reads_contract ->
  forall (SP lo : Z) (es : list rentry) (g : word) (fd op : nat -> Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 <= SP -> SP + 32 < 2 ^ 64 -> lo + RELAY_READS_K <= SP ->
  (forall i : nat, (i < 4)%nat -> 0 <= op i < 2 ^ 31 /\ (op i <> 0 -> -2 ^ 31 <= fd i < 2 ^ 31)) ->
  Z.of_nat (length es) < 2 ^ 31 -> Forall (fun e => -2 ^ 31 <= re_eof e < 2 ^ 31) es ->
  (es <> [] -> bv_unsigned g <> 0 /\ bv_unsigned g mod 8 = 0) ->
  (G_S + 384 <= SP - RELAY_READS_K \/ SP <= G_S) ->
  (G_NSRC + 4 <= SP - RELAY_READS_K \/ SP <= G_NSRC) ->
  (G_SRC + 8 <= SP - RELAY_READS_K \/ SP <= G_SRC) ->
  (es <> [] -> bv_unsigned g + 56 * Z.of_nat (length es) <= SP - RELAY_READS_K \/ SP <= bv_unsigned g) ->
  (forall (i : nat) (m1 : word -> option byte), (i < 4)%nat -> p5sl_mem SP lo es fd op i m m1 ->
     rw_cells rsegs m1 (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 (fd i)); C4 (Z_to_bv 64 (op i))] /\
     wr_at rsegs m1 (SP + 16) 16 /\
     (op i <> 0 ->
        bytes_at rsegs m1 G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es)))) /\ bytes_at rsegs m1 G_SRC (le8 g) /\
        src_table m1 (bv_unsigned g) es /\ mem_inv rsegs m1 /\ stk rsegs m1 lo SP /\
        (forall m2 : word -> option byte, munch [(SP - RELAY_READS_K, SP)] m1 m2 -> wmono rsegs m1 m2 ->
           wr_at rsegs m2 (SP + 16) 16))) ->
  evt rsegs (fun ms => exists (x11' x12' x13' x14' x15' x16' x17' : word) (m' : word -> option byte),
      p5sl_mem SP lo es fd op 4 m m' /\
      ms = MS (mkR (Z_to_bv 64 0x144c8) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 (G_S + 384)) (Z_to_bv 64 (SP + 32)) x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27
                 x28 x29 x30 x31) F (Z_to_bv 64 0x13664) fc None m' (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 (G_S + 96 * Z.of_nat 0)) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat 0)) x20 x21 x22 (Z_to_bv 64 (SP + 32))
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144a0) fc None m (seg_rom rsegs)).
Proof.
  intros RRC SP lo es g fd op x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m HS0 HS1 Hlo HR Hlen HEof Hg HGS HNS HSR HGT HP.
  exact (p5sl_rest RRC SP lo es g fd op x3 x4 x5 x6 x7 x8 x9 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HS0
           HS1 Hlo HR Hlen HEof Hg HGS HNS HSR HGT HP 3 0 x1 x10 x11 x12 x13 x14 x15 x16 x17 m eq_refl eq_refl).
Qed.
