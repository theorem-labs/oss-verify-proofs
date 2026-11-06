(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Arr Bytes ZBridge Image.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim HarnessM.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells ABase AKit AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AM_minify_ck.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AMINIFY : Z := 0xb9b50.
Definition MINIFY_STACK : Z := 32.

Definition b2z (b : bool) : Z := if b then 1 else 0.
Lemma b2z_range : forall b, 0 <= b2z b <= 1. Proof. intros []; cbn; lia. Qed.
Definition jt_ws (c : Z) : bool := (c =? 9) || (c =? 10) || (c =? 13) || (c =? 32).
Definition jt_meta (c : Z) : list Z := [ b2z (c =? 34); b2z (negb (c =? 92)); b2z (negb (jt_ws c)) ].
Notation jtb := (map (Z_to_bv 8) AJT_BYTES).

Lemma ajt_len : length AJT_BYTES = 768%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_bytes : forall m, rw_cells bsegs m AJT [CB 768 jtb] -> bytes_at bsegs m AJT jtb.
Proof. intros m [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B. Qed.

(* [comment removed for export] *)
Definition jt_chk (c : Z) : bool :=
  match skipn (Z.to_nat (3 * c)) AJT_BYTES with a :: b :: d :: _ => match jt_meta c with [a'; b'; d'] => (a =? a') && (b =? b') && (d =? d') | _ => false end | _ => false end.
Lemma jt_check : forallb jt_chk (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_read : forall m c k, rw_cells bsegs m AJT [CB 768 jtb] -> 0 <= c < 256 -> 0 <= k < 3 ->
  ov_read_bytes bsegs m (wa (AJT + (3 * c + k))) 1 = Some [Z_to_bv 8 (nth (Z.to_nat k) (jt_meta c) 0)].
Proof.
  intros m c k JT Hc Hk.
  assert (IN : In c (map Z.of_nat (seq 0 256))). { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) jt_check c IN) as H. unfold jt_chk in H.
  rewrite (bytes_at_read bsegs m AJT _ (3 * c + k) 1 (jt_bytes m JT)) by (rewrite ?length_map, ?ajt_len; lia).
  rewrite skipn_map. replace (Z.to_nat (3 * c + k)) with (Z.to_nat k + Z.to_nat (3 * c))%nat by lia. rewrite <- skipn_skipn.
  destruct (skipn (Z.to_nat (3 * c)) AJT_BYTES) as [|a [|b [|d r]]]; try discriminate.
  cbn [jt_meta] in H. rewrite !andb_true_iff, !Z.eqb_eq in H. destruct H as ((Ha & Hb) & Hd).
  assert (K : k = 0 \/ k = 1 \/ k = 2) by lia. destruct K as [->|[->| ->]]; subst a b d; [change (Z.to_nat 0) with 0%nat| change (Z.to_nat 1) with 1%nat| change (Z.to_nat 2) with 2%nat]; reflexivity.
Qed.

Lemma jt_read0 : forall m c, rw_cells bsegs m AJT [CB 768 jtb] -> 0 <= c < 256 -> ov_read_bytes bsegs m (wa (1541216 + 3 * c)) 1 = Some [Z_to_bv 8 (b2z (c =? 34))].
Proof. intros m c JT Hc. pose proof (jt_read m c 0 JT Hc ltac:(lia)) as R. unfold AJT in R. replace (1541216 + (3 * c + 0)) with (1541216 + 3 * c) in R by lia. exact R. Qed.
Lemma jt_read1 : forall m c, rw_cells bsegs m AJT [CB 768 jtb] -> 0 <= c < 256 -> ov_read_bytes bsegs m (wa (1541216 + 3 * c + 1)) 1 = Some [Z_to_bv 8 (b2z (negb (c =? 92)))].
Proof. intros m c JT Hc. pose proof (jt_read m c 1 JT Hc ltac:(lia)) as R. unfold AJT in R. replace (1541216 + (3 * c + 1)) with (1541216 + 3 * c + 1) in R by lia. exact R. Qed.
Lemma jt_read2 : forall m c, rw_cells bsegs m AJT [CB 768 jtb] -> 0 <= c < 256 -> ov_read_bytes bsegs m (wa (1541216 + 3 * c + 2)) 1 = Some [Z_to_bv 8 (b2z (negb (jt_ws c)))].
Proof. intros m c JT Hc. pose proof (jt_read m c 2 JT Hc ltac:(lia)) as R. unfold AJT in R. replace (1541216 + (3 * c + 2)) with (1541216 + 3 * c + 2) in R by lia. exact R. Qed.

Lemma firstn_S_nth : forall {A} (l : list A) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof. intros A l. induction l as [|x l IH]; intros [|k] d H; cbn in *; try lia; [reflexivity|]. rewrite (IH k d) by lia. reflexivity. Qed.

Lemma c1_rd_local : forall m s b, rw_cells bsegs m s [C1 b] -> ov_read_bytes bsegs m (wa s) 1 = Some [b].
Proof. intros m s b H. pose proof (rw_cells_read bsegs m s [C1 b] 0 (C1 b) H eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D DST RS : Z) (pl : list Z) (lo : Z).
  Notation n := (zlength pl).
  Notation SP := (bv_unsigned sp).
  Hypothesis BA : bytes_at bsegs m D (map (Z_to_bv 8) pl).
  Hypothesis PLR : Forall (fun c => 0 <= c < 256) pl.
  Hypothesis JTC : rw_cells bsegs m AJT [CB 768 jtb].      (* [comment removed for export] *)
  Hypothesis UNPD : unpoisoned m D (D + n).
  Hypothesis UNPJ : unpoisoned m AJT (AJT + 768).
  Hypothesis UNPT : unpoisoned m DST (DST + n).
  Hypothesis DLO : 0 < D.                                   (* [comment removed for export] *)
  Hypothesis D8 : D mod 8 = 0.
  Hypothesis T8 : DST mod 8 = 0.
  Hypothesis RS8 : RS mod 8 = 0.
  Hypothesis NLT : n < 2^26.
  Hypothesis LO : lo <= SP - 32.
  Hypothesis CLO : KHIGH <= lo.
  Hypothesis GOT0 : rt_got m.
  Hypothesis SHB0 : rt_shbase m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RISH : rng RNG 0x7fffa000 0xd8800.             (* [comment removed for export] *)
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH : rng RNG (shad D) (nshad n).
  Hypothesis RT : rng RNG DST n.
  Hypothesis RTS : rng RNG (shad DST) (nshad n).
  Hypothesis RRS : rng RNG RS 8.
  Hypothesis RRSS : rng RNG (shad RS) 1.

  Hypothesis DLE : D + n <= lo.
  Hypothesis TLE : DST + n <= lo.
  Hypothesis RLE : RS + 8 <= lo.
  Hypothesis TBLK : DST + n <= KLOW \/ KHIGH <= DST.       (* [comment removed for export] *)
  Hypothesis TD : DST + n <= D \/ D + n <= DST.             (* [comment removed for export] *)
  Hypothesis TR : DST + n <= RS \/ RS + 8 <= DST.           (* [comment removed for export] *)
  Hypothesis TJ : AJT + 768 <= DST \/ DST + n <= AJT.       (* [comment removed for export] *)
  Hypothesis T0 : 0 < DST.                                  (* [comment removed for export] *)
  Hypothesis TE : DST + n + 8 <= KEND.
  Hypothesis DE : D + n + 8 <= KEND.
  Hypothesis RS0 : 0 <= RS.
  Hypothesis RSE : RS + 8 <= KEND.

  Notation W := [(SP - 32, SP); (DST, DST + n); (RS, RS + 8)].
  Notation bs := (map (Z_to_bv 8) pl).

  Definition FRAME (m1 : word -> option byte) : Prop := rw_cells bsegs m1 (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra].
  Definition RSCELL (m1 : word -> option byte) : Prop :=
    (exists r0, rw_cells bsegs m1 RS [C8 r0]) /\ rw_cells bsegs m1 (Z.shiftr RS 3 + 2147450880) [C1 (Z_to_bv 8 0)].
  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at bsegs m1 D bs /\ unpoisoned m1 D (D + n) /\ unpoisoned m1 AJT (AJT + 768) /\ unpoisoned m1 DST (DST + n)
    /\ wr_at bsegs m1 DST n /\ RSCELL m1 /\ FRAME m1 /\ stk bsegs m1 lo (SP + -32)
    /\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 AJT [CB 768 jtb].

  (* [comment removed for export] *)
  Lemma payload_rd : forall m1 k, bytes_at bsegs m1 D bs -> 0 <= k < n ->
    ov_read_bytes bsegs m1 (wa (D + k)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat k) pl 0)] /\ 0 <= nth (Z.to_nat k) pl 0 < 256.
  Proof.
    intros m1 k B Hk. unfold zlength in Hk.
    pose proof (bytes_at_read bsegs m1 D bs k 1 B ltac:(lia) ltac:(rewrite length_map; lia)) as R.
    rewrite skipn_map in R. destruct (skipn (Z.to_nat k) pl) as [|c r] eqn:E.
    { exfalso. assert (L : length (skipn (Z.to_nat k) pl) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia. }
    assert (EN : nth (Z.to_nat k) pl 0 = c).
    { rewrite <- (firstn_skipn (Z.to_nat k) pl) at 1. rewrite E, app_nth2 by (rewrite length_firstn; lia).
      rewrite length_firstn. replace (Z.to_nat k - Nat.min (Z.to_nat k) (length pl))%nat with 0%nat by lia. reflexivity. }
    rewrite EN. split; [exact R|].
    rewrite Forall_forall in PLR. apply PLR. rewrite <- EN. apply nth_In. lia.
  Qed.

  Ltac ckrd UNP LOx HIx A b RDb CKb :=
    destruct (unpoisoned_check_rd bsegs _ LOx HIx A 1 UNP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDb & CKb);
    unfold shad, ASHOFF in RDb; replace (2147450880 + Z.shiftr A 3) with (Z.shiftr A 3 + 2147450880) in RDb by lia.
  Ltac ckcut L A bb CKb :=
    eapply evtF_cut;
    [ eapply L with (b := bb);
      [ lia
      | first [ exact CKb | lazymatch goal with |- _ \/ (_ /\ ?P mod 8 + _ - _ < _) => replace P with A by lia end; exact CKb ] ]
    | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; destruct_exs PO; subst ms' ].

  (* [comment removed for export] *)
  Notation GST pc mm vi x8 x9 vq x15 vp x18 vne x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp (Z_to_bv 64 vi) (Z_to_bv 64 (Z.lxor D 18446744073709551615)) (Z_to_bv 64 (Z.lxor DST 18446744073709551615))
             x8 x9 (Z_to_bv 64 vq) (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 DST) (Z_to_bv 64 RS) x15 (Z_to_bv 64 2147450880) (Z_to_bv 64 vp)
             x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1541216) (Z_to_bv 64 vne) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition mst (i : Z) : bool * bool := fold_left minify_step (firstn (Z.to_nat i) pl) (true, false).
  Lemma mst_succ : forall i, 0 <= i < n -> mst (i + 1) = minify_step (mst i) (nth (Z.to_nat i) pl 0).
  Proof.
    intros i Hi. unfold mst, zlength in *. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite (firstn_S_nth _ _ 0) by lia. rewrite fold_left_app. reflexivity.
  Qed.
  Lemma mst_all : unclosed pl = snd (mst n).
  Proof. unfold unclosed, mst, zlength. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition flag_chk (nez : Z) : bool :=
    forallb (fun x => forallb (fun y =>
       (Z.land nez (b2z x) =? b2z (Z.odd nez && x))
       && (0 <=? Z.lxor nez 255) && (Z.lxor nez 255 <? 256)
       && (0 <=? Z.lor (Z.lxor nez 255) (b2z y)) && (Z.lor (Z.lxor nez 255) (b2z y) <? 256)
       && Bool.eqb (Z.odd (Z.lor (Z.lxor nez 255) (b2z y))) (negb (Z.odd nez) || y)) [true; false]) [true; false].
  Lemma flag_check : forallb flag_chk (map Z.of_nat (seq 0 256)) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma flag_facts : forall nez x y, 0 <= nez < 256 ->
    Z.land nez (b2z x) = b2z (Z.odd nez && x)
    /\ 0 <= Z.lxor nez 255 < 256
    /\ 0 <= Z.lor (Z.lxor nez 255) (b2z y) < 256
    /\ Z.odd (Z.lor (Z.lxor nez 255) (b2z y)) = (negb (Z.odd nez) || y).
  Proof.
    intros nez x y Hn.
    assert (IN : In nez (map Z.of_nat (seq 0 256))). { apply in_map_iff. exists (Z.to_nat nez). split; [lia|]. apply in_seq. lia. }
    pose proof (proj1 (forallb_forall _ _) flag_check nez IN) as H. unfold flag_chk in H.
    rewrite forallb_forall in H. specialize (H x ltac:(destruct x; cbn; tauto)).
    rewrite forallb_forall in H. specialize (H y ltac:(destruct y; cbn; tauto)).
    rewrite !andb_true_iff in H. destruct H as (((((H1 & H2a) & H3a) & H2) & H3) & H4).
    apply Z.eqb_eq in H1. apply Z.leb_le in H2, H2a. apply Z.ltb_lt in H3, H3a. apply Bool.eqb_prop in H4. repeat split; assumption.
  Qed.

  Lemma b2z_lxor : forall a b, Z.lxor (b2z a) (b2z b) = b2z (xorb a b). Proof. intros [] []; reflexivity. Qed.
  Lemma b2z_lor : forall a b, Z.lor (b2z a) (b2z b) = b2z (a || b). Proof. intros [] []; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma INV_store : forall m1 pos (bl : list byte), length bl = 1%nat -> INV m1 -> 0 <= pos < n -> INV (write_to_mem m1 (wa (DST + pos)) bl).
  Proof.
    intros m1 pos bl LBL (BA1 & UD1 & UJ1 & UT1 & WT1 & [[r0 RSC1] RSS1] & FR1 & ST1 & MU1 & WM1 & MI1 & JT1) Hp.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. pose proof TE as TE'. unfold KEND in DE', TE'.
    assert (SOK : store_ok bsegs m1 (wa (DST + pos)) 1 = true) by (eapply wr_at_store_ok; [exact WT1| lia| lia]).
    set (m2 := write_to_mem m1 (wa (DST + pos)) bl).
    assert (MU2 : munch [(DST + pos, DST + pos + 1)] m1 m2).
    { apply munch_write; [apply munch_refl| lia| rewrite LBL; lia|]. cbn [inside]. rewrite LBL. left. cbn. lia. }
    assert (WM2 : wmono bsegs m1 m2) by (apply wmono_write; apply wmono_refl).
    assert (SHD : forall lo' hi', 0 <= lo' -> lo' < hi' -> hi' + 8 <= 2^47 -> disjoint_from [(DST + pos, DST + pos + 1)] (shad lo') (shad (hi' - 1) + 1 - shad lo')).
    { intros lo' hi' L0 LH HK. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. unfold KLOW, KHIGH in TBLK.
      destruct TBLK as [TB|TB]; [right| left]; Z.div_mod_to_equations; lia. }
    split. { eapply bytes_at_transport; [exact BA1| exact MU2|]. cbn [disjoint_from]. rewrite length_map. unfold zlength in *. split; [lia| exact I]. }
    split. { destruct (Z.eq_dec n 0) as [E0|NE0]; [lia|]. eapply unpoisoned_munch; [exact UD1| exact MU2|]. apply SHD; lia. }
    split. { eapply unpoisoned_munch; [exact UJ1| exact MU2|]. apply SHD; unfold AJT; lia. }
    split. { eapply unpoisoned_munch; [exact UT1| exact MU2|]. apply SHD; lia. }
    split. { apply wr_at_write. exact WT1. }
    split. { split.
      - exists r0. eapply rw_cells_transport; [exact RSC1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia| exact I].
      - eapply rw_cells_transport; [exact RSS1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        split; [| exact I]. rewrite Z.shiftr_div_pow2 by lia. pose proof RSE as RSE'. unfold KEND in RSE'. unfold KLOW, KHIGH in TBLK. destruct TBLK as [TB|TB]; [right| left]; Z.div_mod_to_equations; lia. }
    split. { unfold FRAME. eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia| exact I]. }
    split. { apply stk_write; [exact ST1| lia| rewrite LBL; lia]. }
    split. { apply munch_write; [exact MU1| lia| rewrite LBL; lia|]. cbn [inside]. rewrite LBL. right. left. cbn. lia. }
    split. { apply wmono_write. exact WM1. }
    split. { apply mem_inv_store; [exact MI1| rewrite LBL; exact SOK]. }
    eapply rw_cells_transport; [exact JT1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. unfold AJT in *. split; [clear - TJ Hp; lia| exact I].
  Qed.

  (* [comment removed for export] *)
  Definition mf_post : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' pos,
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if unclosed pl then 15 else 0)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ 0 <= pos <= n /\ rw_cells bsegs m' RS [C8 (Z_to_bv 64 pos)]
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SP.

  (* [comment removed for export] *)
  Lemma mf_exit : forall m1 pos (qo tb : bool) (y5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x28 x29 x31 : word),
    INV m1 -> 0 <= pos <= n -> xorb tb qo = unclosed pl ->
    evtF bsegs RNG mf_post
      (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp y5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 RS) (Z_to_bv 64 (b2z tb)) (Z_to_bv 64 2147450880) (Z_to_bv 64 pos)
               x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 (Z_to_bv 64 (b2z qo)) x31)
          F (Z_to_bv 64 0xb9c88) fc None m1 (seg_rom bsegs)).
  Proof.
    intros m1 pos qo tb y5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x28 x29 x31 (BA1 & UD1 & UJ1 & UT1 & WT1 & [[r0 RSC1] RSS1] & FR1 & ST1 & MU1 & WM1 & MI1 & JT1) Hp HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. unfold FRAME in FR1.
    pose proof RSE as RSE'. unfold KEND in RSE'.
    pose proof (c1_rd_local m1 _ _ RSS1) as RDS.
    unfold mf_post. rewrite <- HQ. clear HQ.
    destruct qo, tb; cbn [b2z xorb].
    all: do 7 zstep; change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
    all: zstep; if_false.
    all: zstep.              (* [comment removed for export] *)
    all: do 6 zstep.         (* [comment removed for export] *)
    all: release_frame FR1 ST1 (bv_unsigned sp).
    all: apply evtF_done; do 16 eexists; split; [reflexivity|]; split; [exact Hp|]; split; [exact RSC1|]; split; [exact MU1|]; split; [exact WM1|]; split; [exact MI1| exact ST1].
  Qed.
  (* [comment removed for export] *)
  Lemma mf_loop : forall fuel i m1 pos nez (x8 x9 x15 x18 x30 x31 : word),
    Z.of_nat fuel > n - i -> 0 <= i < n -> INV m1 -> 0 <= pos <= i -> 0 <= nez < 256 -> Z.odd nez = fst (mst i) ->
    evtF bsegs RNG mf_post (GST 0xb9b9c m1 i x8 x9 (b2z (snd (mst i))) x15 pos x18 nez x30 x31).
  Proof.
    induction fuel as [|fuel IH]; intros i m1 pos nez x8 x9 x15 x18 x30 x31 FUEL Hi INV1 Hp Hne HODD; [lia|].
    pose proof INV1 as (BA1 & UD1 & UJ1 & UT1 & WT1 & RSC1 & FR1 & ST1 & MU1 & WM1 & MI1 & JT1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. pose proof TE as TE'. unfold KEND in DE', TE'. unfold AJT in UJ1.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    destruct (payload_rd m1 i BA1 Hi) as [RDc CR]. set (c := nth (Z.to_nat i) pl 0) in *.
    destruct (mst i) as [neb qb] eqn:EM. cbn [fst snd] in *.
    pose proof (b2z_range qb) as QR. pose proof (b2z_range (c =? 34)) as M0R. pose proof (b2z_range (negb (c =? 92))) as M1R. pose proof (b2z_range (negb (jt_ws c))) as M2R.
    pose proof (jt_read0 m1 c JT1 CR) as RJ0. pose proof (jt_read1 m1 c JT1 CR) as RJ1. pose proof (jt_read2 m1 c JT1 CR) as RJ2.
    destruct (flag_facts nez (c =? 34) (negb (c =? 92)) Hne) as (FL1 & FL2 & FL3 & FL4).
    pose proof (b2z_range (Z.odd nez && (c =? 34))) as TBR. pose proof (b2z_range (xorb (Z.odd nez && (c =? 34)) qb)) as QNR.
    pose proof (b2z_range (negb (jt_ws c) || xorb (Z.odd nez && (c =? 34)) qb)) as PIR.
    assert (SOK : store_ok bsegs m1 (wa (DST + pos)) 1 = true) by (eapply wr_at_store_ok; [exact WT1| lia| lia]).
    (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?zb_lxor_ones in K by lia; clear - K Hi DE' DLO; lia| clear K]).   (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?zb_lxor_ones in K by lia; clear - K Hi Hp TE' T0; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. ckrd UD1 D (D + n) (D + i) b0 RDb0 CKb0. zstep. rewrite sxb_sval. ckcut ckb_b9c30 (D + i) b0 CKb0. clear RDb0 CKb0.
    zstep. rewrite zxb_lit by lia.                             (* [comment removed for export] *)
    zstep. zstep. zstep. replace (1541216 + c + Z.shiftl c 1) with (1541216 + 3 * c) by (rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. ckrd UJ1 1541216 (1541216 + 768) (1541216 + 3 * c) b1 RDb1 CKb1. zstep. rewrite sxb_sval. ckcut ckb_b9c50 (1541216 + 3 * c) b1 CKb1. clear RDb1 CKb1.
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. zstep. ckrd UT1 DST (DST + n) (DST + pos) b2 RDb2 CKb2. zstep. rewrite sxb_sval.   (* [comment removed for export] *)
    zstep. rewrite zxb_lit by lia.                             (* [comment removed for export] *)
    ckcut ckb_b9c68 (DST + pos) b2 CKb2. clear RDb2 CKb2.
    zstep.                                                     (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => set (m2 := mx) end.
    assert (INV2 : INV m2) by (apply INV_store; [reflexivity| exact INV1| lia]).
    pose proof INV2 as (BA2 & UD2 & UJ2 & UT2 & WT2 & RSC2 & FR2 & ST2 & MU2 & WM2 & MI2 & JT2). unfold AJT in UJ2.
    clear RJ0 RJ1 RJ2 RDc SOK. pose proof (jt_read1 m2 c JT2 CR) as RJ1. pose proof (jt_read2 m2 c JT2 CR) as RJ2.
    clearbody m2. clear BA1 UD1 UJ1 UT1 WT1 RSC1 FR1 ST1 MU1 WM1 MI1 JT1 INV1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ckrd UJ2 1541216 (1541216 + 768) (1541216 + 3 * c + 2) b3 RDb3 CKb3. zstep. rewrite sxb_sval. ckcut ckb_b9c80 (1541216 + 3 * c + 2) b3 CKb3. clear RDb3 CKb3.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ckrd UJ2 1541216 (1541216 + 768) (1541216 + 3 * c + 1) b4 RDb4 CKb4. zstep. rewrite sxb_sval.
    zstep. rewrite zxb_lit by lia.                             (* [comment removed for export] *)
    ckcut ckb_b9c98 (1541216 + 3 * c + 1) b4 CKb4. clear RDb4 CKb4.
    zstep. rewrite FL1.                                        (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. rewrite zxb_lit by lia.                             (* [comment removed for export] *)
    zstep. rewrite b2z_lxor.                                   (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. rewrite b2z_lor.                                    (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (EM1 : mst (i + 1) = (negb neb || negb (c =? 92), xorb qb ((c =? 34) && neb))) by (rewrite (mst_succ i Hi), EM; reflexivity).
    assert (QE : xorb (Z.odd nez && (c =? 34)) qb = xorb qb ((c =? 34) && neb)) by (rewrite HODD; destruct neb, qb, (c =? 34); reflexivity).
    zstep. if_cases Kn; zify_cond Kn.
    - (* [comment removed for export] *)
      assert (NEXT : forall vi vq vp vne (y8 y9 y15 y18 y30 y31 : word),
                vi = i + 1 -> vq = b2z (snd (mst (i + 1))) -> 0 <= vp <= i + 1 -> 0 <= vne < 256 -> Z.odd vne = fst (mst (i + 1)) ->
                evtF bsegs RNG mf_post (GST 0xb9b9c m2 vi y8 y9 vq y15 vp y18 vne y30 y31)).
      { intros vi vq vp vne y8 y9 y15 y18 y30 y31 -> -> H5 H7 HO. apply IH; [lia| rewrite ?unsigned_lit in Kn by lia; lia| exact INV2| exact H5| exact H7| exact HO]. }
      apply NEXT; [lia| rewrite EM1; cbn [snd]; rewrite QE; reflexivity| lia| exact FL3| rewrite EM1; cbn [fst]; rewrite FL4, HODD; reflexivity].
    - (* [comment removed for export] *)
      zstep.
      eapply (mf_exit m2 _ qb (Z.odd nez && (c =? 34))); [exact INV2| lia|].
      rewrite mst_all. replace n with (i + 1) by (rewrite ?unsigned_lit in Kn by lia; lia). rewrite EM1. cbn [snd]. exact QE.
  Qed.
  (* [comment removed for export] *)
  Hypothesis WT0 : wr_at bsegs m DST n.
  Hypothesis RSC0 : RSCELL m.
  Lemma mf_body : stk bsegs m lo SP -> mem_inv bsegs m ->
    evtF bsegs RNG mf_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 DST) (Z_to_bv 64 RS) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMINIFY) fc None m (seg_rom bsegs)).
  Proof.
    intros ST MI. unfold AMINIFY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. pose proof TE as TE'. pose proof RSE as RSE'. unfold KEND in DE', TE', RSE'.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    destruct (stk_carve bsegs m lo SP 32 ST ltac:(cbn; lia)) as [STL [jf FRJ]]. change (Z.of_nat 32) with 32 in STL, FRJ.
    assert (INV0 : forall m1, munch [(SP - 32, SP)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> FRAME m1 -> stk bsegs m1 lo (SP + -32) -> INV m1).
    { intros m1 MU1 WM1 MI1 FR1 ST1.
      assert (SHD : forall lo' hi', 0 <= lo' -> lo' < hi' -> hi' + 8 <= 2^47 -> disjoint_from [(SP - 32, SP)] (shad lo') (shad (hi' - 1) + 1 - shad lo')).
      { intros lo' hi' L0 LH HK. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. left. Z.div_mod_to_equations. lia. }
      destruct RSC0 as [[r0 RSa] RSb].
      split. { eapply bytes_at_transport; [exact BA| exact MU1|]. cbn [disjoint_from]. rewrite length_map. unfold zlength in *. split; [lia| exact I]. }
      split. { destruct (Z.eq_dec n 0) as [E0|NE0]; [rewrite E0, Z.add_0_r; apply unpoisoned_nil; lia|]. eapply unpoisoned_munch; [exact UNPD| exact MU1|]. apply SHD; lia. }
      split. { eapply unpoisoned_munch; [exact UNPJ| exact MU1|]. apply SHD; unfold AJT; lia. }
      split. { destruct (Z.eq_dec n 0) as [E0|NE0]; [rewrite E0, Z.add_0_r; apply unpoisoned_nil; lia|]. eapply unpoisoned_munch; [exact UNPT| exact MU1|]. apply SHD; lia. }
      split. { eapply wr_at_transport; [exact WT0| exact WM1]. }
      split. { split.
        - exists r0. eapply rw_cells_transport; [exact RSa| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia| exact I].
        - eapply rw_cells_transport; [exact RSb| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
          split; [| exact I]. rewrite Z.shiftr_div_pow2 by lia. left. Z.div_mod_to_equations. lia. }
      split; [exact FR1|]. split; [exact ST1|].
      split. { eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in *. tauto. }
      split; [exact WM1|]. split; [exact MI1|].
      eapply rw_cells_transport; [exact JTC| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. unfold AJT. split; [clear - CLO' LO; lia| exact I]. }
    clear ST. rename STL into ST. replace (SP - 32) with (SP + -32) in ST, FRJ by lia.
    pose proof (munch_refl [(SP - 32, SP)] m) as MUF.
    zstep.                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
    zstep. zstep. zstep.          (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (INV1 : INV mx) by (apply INV0; assumption) end.
    clear INV0 MU MUF WM MI ST FRJ.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    - (* [comment removed for export] *)
      assert (PLN : pl = []) by (destruct pl; [reflexivity| unfold zlength in K0; cbn [length] in K0; lia]).
      destruct INV1 as (_ & _ & _ & _ & _ & [[r0 RSC1] RSS1] & FR1 & ST1 & MU1 & WM1 & MI1 & _). unfold FRAME in FR1.
      pose proof (c1_rd_local _ _ _ RSS1) as RDS.
      do 5 zstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
      zstep. if_true.
      zstep.                      (* [comment removed for export] *)
      do 6 zstep.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evtF_done. unfold mf_post. replace (unclosed pl) with false by (rewrite PLN; reflexivity).
      do 15 eexists. exists 0. split; [reflexivity|]. split; [lia|]. split; [exact RSC1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1| exact ST1].
    - (* [comment removed for export] *)
      zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K DLO; lia| clear K]).   (* [comment removed for export] *)
      zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K T0; lia| clear K]).    (* [comment removed for export] *)
      zstep. zstep. zstep.        (* [comment removed for export] *)
      zstep. zstep.               (* [comment removed for export] *)
      zstep.                      (* [comment removed for export] *)
      zstep. zstep.               (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply (mf_loop (S (Z.to_nat n)) 0 _ 0 1); [lia| lia| exact INV1| lia| lia| reflexivity].
  Qed.
End P.

(* [comment removed for export] *)
Definition minify_stmtA : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D DST RS : Z) (pl : list Z) (lo : Z),
    bytes_at bsegs m D (map (Z_to_bv 8) pl) -> Forall (fun c => 0 <= c < 256) pl ->
    rw_cells bsegs m AJT [CB 768 (map (Z_to_bv 8) AJT_BYTES)] ->
    unpoisoned m D (D + zlength pl) -> unpoisoned m AJT (AJT + 768) -> unpoisoned m DST (DST + zlength pl) ->
    0 < D -> D mod 8 = 0 -> DST mod 8 = 0 -> RS mod 8 = 0 -> zlength pl < 2 ^ 26 ->
    lo <= bv_unsigned sp - MINIFY_STACK -> KHIGH <= lo ->
    rt_got m -> rt_shbase m ->
    rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG 0x7fffa000 0xd8800 ->
    rng RNG D (zlength pl) -> rng RNG (shad D) (nshad (zlength pl)) -> rng RNG DST (zlength pl) -> rng RNG (shad DST) (nshad (zlength pl)) ->
    rng RNG RS 8 -> rng RNG (shad RS) 1 ->
    D + zlength pl <= lo -> DST + zlength pl <= lo -> RS + 8 <= lo ->
    (DST + zlength pl <= KLOW \/ KHIGH <= DST) -> (DST + zlength pl <= D \/ D + zlength pl <= DST) -> (DST + zlength pl <= RS \/ RS + 8 <= DST) ->
    (AJT + 768 <= DST \/ DST + zlength pl <= AJT) ->
    0 < DST -> DST + zlength pl + 8 <= KEND -> D + zlength pl + 8 <= KEND -> 0 <= RS -> RS + 8 <= KEND ->
    wr_at bsegs m DST (zlength pl) ->
    ((exists r0, rw_cells bsegs m RS [C8 r0]) /\ rw_cells bsegs m (Z.shiftr RS 3 + 2147450880) [C1 (Z_to_bv 8 0)]) ->
    stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
    a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 (zlength pl) -> a3 = Z_to_bv 64 DST -> a4 = Z_to_bv 64 RS ->
    evtF bsegs RNG (mf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST RS pl lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMINIFY) fc None m (seg_rom bsegs)).

Theorem minify_proofA : minify_stmtA.
Proof.
  unfold minify_stmtA, MINIFY_STACK. intros until lo.
  intros BA PLR JTC UD UJ UT D0 D8 T8 RS8 NLT LO CLO GOT SHB RI RSTK RISH RD RSH RT RTS RRS RRSS DLE TLE RLE TBLK TD TR TJ T0 TE DE RS0 RSE WT RSC ST MI -> -> -> ->.
  eapply mf_body; eassumption.
Qed.

(* [comment removed for export] *)
Lemma minify_nilA : forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D RS lo : Z) (r0 : word),
  lo <= bv_unsigned sp - 32 -> KHIGH <= lo -> bv_unsigned sp + 16 <= 2^47 ->
  rt_got m -> rt_shbase m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RS 8 -> rng RNG (Z.shiftr RS 3 + 2147450880) 1 ->
  0 <= RS -> RS + 8 <= lo -> RS mod 8 = 0 ->
  rw_cells bsegs m RS [C8 r0] -> rw_cells bsegs m (Z.shiftr RS 3 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  (RS + 8 <= KLS \/ KHIGH <= RS) ->
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
  a2 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 RS ->
  evtF bsegs RNG (mf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m 0 RS [] lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMIN_FN) fc None m (seg_rom bsegs)).
Proof.
  intros until r0. intros LO CLO SPH GOT SHB RI RSTK RRS RRSS RS0 RSE RS8 RSC RSS RNS ST MI -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof atop_range as ATR. unfold KHIGH, KLS in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SHRS : 2147450880 <= Z.shiftr RS 3 + 2147450880 /\ Z.shiftr RS 3 + 2147450880 + 1 <= 0x10007fff8000)
    by (rewrite Z.shiftr_div_pow2 by lia; clear - RS0 RSE LO ATR RSP SPH; Z.div_mod_to_equations; lia).
  unfold mf_post, AMIN_FN. change (zlength (@nil Z)) with 0. cbn [unclosed fold_left snd].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0, 0 + 0); (RS, RS + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  zstep. zstep. zstep.          (* [comment removed for export] *)
  zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [clear Kz| exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia]).   (* [comment removed for export] *)
  zstep. zstep.                 (* [comment removed for export] *)
  zstep. zstep.                 (* [comment removed for export] *)
  zstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).   (* [comment removed for export] *)
  zstep. if_true.               (* [comment removed for export] *)
  zstep.                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                        (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with RSx : rw_cells bsegs mm RS _, STx : stk bsegs mm lo _, MIx : mem_inv bsegs mm |- _ =>
    do 14 eexists; exists mm, 0; split; [reflexivity|]; split; [lia|]; split; [exact RSx|]; split; [exact MU|]; split; [exact WM|]; split; [exact MIx| exact STx] end end.
Qed.
End CANSEC1.
