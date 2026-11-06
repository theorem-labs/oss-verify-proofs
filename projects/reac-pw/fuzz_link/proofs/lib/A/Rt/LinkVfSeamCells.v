(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): link's memory FILE between the two vocabularies of
   the GXA seam of musl vfprintf (LinkVfSeam.v).

   The contract (LinkVfDefs.v avfprintf_mf_realizes) states the FILE as LinkMfDefs.v's words over the harness's
   restricted store: amf_k (amemfile_at, the static fields fmemopen writes, the flags, the orientation, the write
   window with k bytes pending, the cookie), amf_dyn (the seven words the path changes, as values) and amf_pend (the k
   pending bytes at f + 280). GXA's walk (lib/CJ/RL/GXA/LinkVfMfA.v vfprintf_mf_a_stmt) states it as CJ cells: the
   232-byte FILE as mf_file (lib/Prog/mf_sink_c.v: 17 cells; the bytes between the fields it names are junk lists)
   and the buffer as two CB cells (the k pending bytes, then the rest).

   1. bytes: a value the harness's val_mem reads is the little-endian bytes of the CJ cell of that value
      (bytes_of_val_mem, val_mem_of_bytes), and a val_mem value is determined modulo its width (val_mem_inj);
   2. cells: one cell from its bytes and writability, a cell list from its head and tail (rw1_intro, rw_cons,
      rw_uncons_at);
   3. the FILE in (mf_file_in): the junk lists are the store's own bytes there (FMgxaSeamCells.rw_cells_block), the
      named cells are the contract's words; and GXA's side conditions on them (mf_side_in): the window is empty with
      k = 0 or active at f + 280 with k pending, F_NOWR is clear, the orientation is 0 or -1;
   4. the buffer in (mf_buf_in) and out (mf_buf_post);
   5. the FILE out (mf_file_post): GXA's post keeps every cell but wend / wpos / wbase / mode and the junk lists, so
      every other byte of the first 272 is the old one, and amf_k / amf_dyn hold at the new window. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Mem Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require G_fwritex.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require mf_sink_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMgxaSeamBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMgxaSeamCells FMgxaSeamReady.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module CJM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Module CJC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Cells.
Module CJS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.
Module MFS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.mf_sink_c.

(* ===================================================================================== *)
(* 1. bytes                                                                               *)
(* ===================================================================================== *)

Lemma mrd_mbyte : forall (m : word -> option byte) a, CJM.mrd tfibsegs m (CJM.wa a) = mbyte tfibsegs m a.
Proof. reflexivity. Qed.

Lemma le_byte_bv : forall v (n k : nat), (k < n)%nat ->
  Z_to_bv 8 (YO0f.le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v n k Hk. apply CJM.Z_to_bv8_mod. unfold YO0f.le_byte.
  rewrite <- (CJM.shiftr_mod_mod8 v (8 * Z.of_nat k) (8 * Z.of_nat n)) by lia.
  change (2 ^ 8) with 256. apply Z.mod_mod. lia.
Qed.

Lemma nth_le : forall (n : nat) z (k : nat), (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof. exact FMgxaSeamReady.nth_le_bytes. Qed.

(* the bytes val_mem reads are the little-endian bytes of the value *)
Lemma bytes_of_val_mem : forall (m : word -> option byte) a (n : nat) v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem tfibsegs m a n v ->
  CJM.bytes_at tfibsegs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v Ha Hn HV. split; [exact Ha|]. split; [rewrite CJM.length_Z_to_le_bytes; exact Hn|].
  intros i Hi. rewrite CJM.length_Z_to_le_bytes in Hi. rewrite (nth_le n v i Hi), mrd_mbyte, (HV i Hi).
  rewrite (le_byte_bv v n i Hi). reflexivity.
Qed.

Lemma val_mem_of_bytes : forall (m : word -> option byte) a (n : nat) v,
  CJM.bytes_at tfibsegs m a (Z_to_le_bytes n v) -> val_mem tfibsegs m a n v.
Proof.
  intros m a n v (_ & _ & HB) k Hk. rewrite <- mrd_mbyte.
  rewrite (HB k ltac:(rewrite CJM.length_Z_to_le_bytes; exact Hk)), (nth_le n v k Hk), (le_byte_bv v n k Hk).
  reflexivity.
Qed.

(* a val_mem value is determined modulo its width *)
Lemma val_mem_inj : forall (m : word -> option byte) a (n : nat) v1 v2, 0 <= v1 -> 0 <= v2 ->
  val_mem tfibsegs m a n v1 -> val_mem tfibsegs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2 V1 V2.
  assert (E : Z_to_le_bytes n v1 = Z_to_le_bytes n v2).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
    - rewrite (nth_le n v1 i Hi), (nth_le n v2 i Hi), <- (le_byte_bv v1 n i Hi), <- (le_byte_bv v2 n i Hi).
      specialize (V1 i Hi). specialize (V2 i Hi). rewrite <- V1, <- V2. reflexivity.
    - assert (N1 : nth_error (Z_to_le_bytes n v1) i = None)
        by (apply nth_error_None; rewrite CJM.length_Z_to_le_bytes; exact Hi).
      assert (N2 : nth_error (Z_to_le_bytes n v2) i = None)
        by (apply nth_error_None; rewrite CJM.length_Z_to_le_bytes; exact Hi).
      rewrite N1, N2. reflexivity. }
  rewrite <- (CJM.bytes_le_to_Z_to_le_bytes n v1 H1), <- (CJM.bytes_le_to_Z_to_le_bytes n v2 H2), E.
  reflexivity.
Qed.

(* the CJ cells of a w64 value *)
Lemma le8_w64 : forall v, CJM.le8 (w64 v) = Z_to_le_bytes 8 v.
Proof.
  intros v. unfold CJM.le8, word_to_le_bytes, w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ (8 * Z.of_nat 8)). apply CJM.Z_to_le_bytes_mod. lia.
Qed.

Lemma le4_w64 : forall v, CJM.le4 (w64 v) = Z_to_le_bytes 4 v.
Proof.
  intros v. unfold CJM.le4, w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply CJM.Z_to_le_bytes_mod. lia.
Qed.

Lemma le_bytes_eq_mod : forall (n : nat) z1 z2, z1 mod 2 ^ (8 * Z.of_nat n) = z2 mod 2 ^ (8 * Z.of_nat n) ->
  Z_to_le_bytes n z1 = Z_to_le_bytes n z2.
Proof.
  intros n z1 z2 E. rewrite <- (CJM.Z_to_le_bytes_mod n z1 (8 * Z.of_nat n)) by lia.
  rewrite <- (CJM.Z_to_le_bytes_mod n z2 (8 * Z.of_nat n)) by lia. rewrite E. reflexivity.
Qed.

(* the lock word's cell, C4 (-1), has the bytes of AU32M1 *)
Lemma le4_lock : CJM.le4 (Z_to_bv 64 (-1)) = Z_to_le_bytes 4 AU32M1.
Proof. change (Z_to_bv 64 (-1)) with (w64 (-1)). rewrite le4_w64. apply le_bytes_eq_mod. reflexivity. Qed.

(* ---- stores ---- *)
Lemma apresent_wr : forall (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> writable_at tfibsegs (cjstore H mem) a.
Proof. intros H mem a [Hh [b Hb]]. unfold writable_at, wview, cjstore, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma apresent_view : forall (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> aview tfibsegs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* bytes the walk leaves at a visible range are the restricted store's bytes *)
Lemma bytes_at_restrict : forall (H : word -> bool) (m : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> H (Z_to_bv 64 x) = false) ->
  CJM.bytes_at tfibsegs m a bs -> CJM.bytes_at tfibsegs (mrestrict H m) a bs.
Proof.
  intros H m a bs HV (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (HB i Hi). unfold CJM.mrd, mrestrict, CJM.wa. rewrite (HV (a + Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma same_bytes : forall (m1 m2 : word -> option byte) a bs x,
  CJM.bytes_at tfibsegs m1 a bs -> CJM.bytes_at tfibsegs m2 a bs -> a <= x < a + Z.of_nat (length bs) ->
  CJM.mrd tfibsegs m1 (CJM.wa x) = CJM.mrd tfibsegs m2 (CJM.wa x).
Proof.
  intros m1 m2 a bs x (_ & _ & B1) (_ & _ & B2) Hx.
  replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  rewrite (B1 (Z.to_nat (x - a)) ltac:(lia)), (B2 (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.

(* ===================================================================================== *)
(* 2. cells                                                                               *)
(* ===================================================================================== *)

Lemma rw1_intro : forall (m : word -> option byte) a c, CJC.cell_wf c ->
  CJM.bytes_at tfibsegs m a (CJC.cbytes c) -> CJM.wr_at tfibsegs m a (Z.of_nat (CJC.csize c)) ->
  CJS.rw_cells tfibsegs m a [c].
Proof.
  intros m a c Hw Hb Hr. split; [split|].
  - split; [exact Hw | exact I].
  - cbn [CJC.cells_bytes]. rewrite app_nil_r. exact Hb.
  - cbn [CJC.cells_size]. rewrite Nat.add_0_r. exact Hr.
Qed.

Lemma rw1_bytes : forall (m : word -> option byte) a c,
  CJS.rw_cells tfibsegs m a [c] -> CJM.bytes_at tfibsegs m a (CJC.cbytes c).
Proof. intros m a c [[_ Hb] _]. cbn [CJC.cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rw1_wf : forall (m : word -> option byte) a c, CJS.rw_cells tfibsegs m a [c] -> CJC.cell_wf c.
Proof. intros m a c [[[Hw _] _] _]. exact Hw. Qed.

Lemma rw_cons : forall (m : word -> option byte) a a' c cs,
  CJS.rw_cells tfibsegs m a [c] -> CJS.rw_cells tfibsegs m a' cs -> a' = a + Z.of_nat (CJC.csize c) ->
  CJS.rw_cells tfibsegs m a (c :: cs).
Proof.
  intros m a a' c cs H1 H2 ->. apply (proj2 (G_fwritex.rw_cells_app tfibsegs m a [c] cs)).
  split; [exact H1|]. cbn [CJC.cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma rw_uncons_at : forall (m : word -> option byte) a a' c cs,
  CJS.rw_cells tfibsegs m a (c :: cs) -> a' = a + Z.of_nat (CJC.csize c) ->
  CJS.rw_cells tfibsegs m a [c] /\ CJS.rw_cells tfibsegs m a' cs.
Proof.
  intros m a a' c cs H ->. apply (proj1 (G_fwritex.rw_cells_app tfibsegs m a [c] cs)) in H as [H1 H2].
  split; [exact H1|]. cbn [CJC.cells_size] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma rw_nil : forall (m : word -> option byte) a, 0 <= a <= 2 ^ 64 -> CJS.rw_cells tfibsegs m a [].
Proof.
  intros m a Ha. split; [split; [exact I | apply CJM.bytes_at_nil; exact Ha]|].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Local Ltac cons_at R T := apply (rw_cons _ _ _ _ _ R T); cbn [CJC.csize]; lia.
Local Ltac peel R a C := let R' := fresh "R" in
  destruct (rw_uncons_at _ _ a _ _ R ltac:(cbn [CJC.csize]; lia)) as [C R']; clear R; rename R' into R.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* one value cell of the harness's store, from val_mem and presence *)
Lemma rw1_val : forall (H : word -> bool) mem a (n : nat) v c,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> apresent H mem x) ->
  CJC.cbytes c = Z_to_le_bytes n v -> CJC.csize c = n -> CJC.cell_wf c ->
  val_mem tfibsegs (mrestrict H mem) a n v ->
  CJS.rw_cells tfibsegs (cjstore H mem) a [c].
Proof.
  intros H mem a n v c Ha Hn HP Eb Es Hw HV. apply rw1_intro; [exact Hw | |].
  - rewrite Eb. exact (bytes_of_val_mem _ a n v Ha Hn HV).
  - rewrite Es. apply wr_at_of_writable; [exact Ha | exact Hn |]. intros x Hx. exact (apresent_wr H mem x (HP x Hx)).
Qed.

(* one junk cell: the store's own bytes there *)
Lemma rw1_junk : forall (H : word -> bool) mem a (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> apresent H mem x) ->
  exists j, length j = n /\ CJS.rw_cells tfibsegs (cjstore H mem) a [CJC.CB n j].
Proof.
  intros H mem a n Ha Hn HP. apply FMgxaSeamCells.rw_cells_block; [exact Ha | exact Hn | |].
  - intros x Hx. exact (apresent_wr H mem x (HP x Hx)).
  - intros x Hx. exact (apresent_view H mem x (HP x Hx)).
Qed.

(* ===================================================================================== *)
(* 3. the FILE in                                                                         *)
(* ===================================================================================== *)

Variable MS : amemfile_syms.

Lemma mf_file_in : forall (H : word -> bool) mem f k fl om wend wpos wbase pos len,
  0 <= f -> f + 232 <= 2 ^ 64 ->
  (forall a, f <= a < f + 232 -> apresent H mem a) ->
  amf_k tfibsegs MS (mrestrict H mem) f k ->
  amf_dyn tfibsegs MS (mrestrict H mem) f fl om wend wpos wbase pos len ->
  exists jp jc j48 j64 j104 jx,
    CJS.rw_cells tfibsegs (cjstore H mem) f
      (MFS.mf_file (w64 fl) jp jc (w64 wend) (w64 wpos) j48 (w64 wbase) j64 (f + 280) j104 (w64 om)
         (w64 AU32M1) jx).
Proof.
  intros H mem f k fl om wend wpos wbase pos len Hf Hf1 HP ((_ & _ & _ & Hs & _ & _ & Hw & _) & _) Hd.
  destruct Hd as (_ & _ & _ & _ & _ & _ & _ & D0 & D136 & D32 & D40 & D56 & _ & _).
  destruct Hw as (W8 & W16 & _).
  unfold amemfile_static in Hs.
  destruct Hs as (_ & _ & _ & _ & _ & S88 & S96 & _ & _ & _ & _ & _ & S140 & S144 & _).
  unfold AMF_BUF, AMF_BUFSIZ in *. rewrite Z.add_0_r in D0.
  assert (HPs : forall a (n : nat), f <= a -> a + Z.of_nat n <= f + 232 ->
                  forall x, a <= x < a + Z.of_nat n -> apresent H mem x)
    by (intros a n Ha Hn x Hx; apply HP; lia).
  assert (Jp : exists j, length j = 4%nat /\ CJS.rw_cells tfibsegs (cjstore H mem) (f + 4) [CJC.CB 4 j])
    by exact (rw1_junk H mem (f + 4) 4 ltac:(lia) ltac:(lia) (HPs (f + 4) 4%nat ltac:(lia) ltac:(lia))).
  assert (Jc : exists j, length j = 8%nat /\ CJS.rw_cells tfibsegs (cjstore H mem) (f + 24) [CJC.CB 8 j])
    by exact (rw1_junk H mem (f + 24) 8 ltac:(lia) ltac:(lia) (HPs (f + 24) 8%nat ltac:(lia) ltac:(lia))).
  assert (J48 : exists j, length j = 8%nat /\ CJS.rw_cells tfibsegs (cjstore H mem) (f + 48) [CJC.CB 8 j])
    by exact (rw1_junk H mem (f + 48) 8 ltac:(lia) ltac:(lia) (HPs (f + 48) 8%nat ltac:(lia) ltac:(lia))).
  assert (J64 : exists j, length j = 24%nat /\ CJS.rw_cells tfibsegs (cjstore H mem) (f + 64) [CJC.CB 24 j])
    by exact (rw1_junk H mem (f + 64) 24 ltac:(lia) ltac:(lia) (HPs (f + 64) 24%nat ltac:(lia) ltac:(lia))).
  assert (J104 : exists j, length j = 32%nat /\ CJS.rw_cells tfibsegs (cjstore H mem) (f + 104) [CJC.CB 32 j])
    by exact (rw1_junk H mem (f + 104) 32 ltac:(lia) ltac:(lia) (HPs (f + 104) 32%nat ltac:(lia) ltac:(lia))).
  assert (Jx : exists j, length j = 84%nat /\ CJS.rw_cells tfibsegs (cjstore H mem) (f + 148) [CJC.CB 84 j])
    by exact (rw1_junk H mem (f + 148) 84 ltac:(lia) ltac:(lia) (HPs (f + 148) 84%nat ltac:(lia) ltac:(lia))).
  destruct Jp as (jp & Ljp & Rjp). destruct Jc as (jc & Ljc & Rjc). destruct J48 as (j48 & Lj48 & Rj48).
  destruct J64 as (j64 & Lj64 & Rj64). destruct J104 as (j104 & Lj104 & Rj104). destruct Jx as (jx & Ljx & Rjx).
  exists jp, jc, j48, j64, j104, jx.
  assert (V : forall a (n : nat) v c, f <= a -> a + Z.of_nat n <= f + 232 ->
            CJC.cbytes c = Z_to_le_bytes n v -> CJC.csize c = n -> CJC.cell_wf c ->
            val_mem tfibsegs (mrestrict H mem) a n v -> CJS.rw_cells tfibsegs (cjstore H mem) a [c])
    by (intros a n v c Ha Hn Eb Es Hw HV; exact (rw1_val H mem a n v c ltac:(lia) ltac:(lia) (HPs a n Ha Hn) Eb Es Hw HV)).
  pose proof (V f 4%nat fl (CJC.C4 (w64 fl)) ltac:(lia) ltac:(lia) (le4_w64 fl) eq_refl I D0) as R0.
  pose proof (V (f + 8) 8%nat 0 (CJC.C8 (w64 0)) ltac:(lia) ltac:(lia) (le8_w64 0) eq_refl I W8) as R8.
  pose proof (V (f + 16) 8%nat 0 (CJC.C8 (w64 0)) ltac:(lia) ltac:(lia) (le8_w64 0) eq_refl I W16) as R16.
  pose proof (V (f + 32) 8%nat wend (CJC.C8 (w64 wend)) ltac:(lia) ltac:(lia) (le8_w64 wend) eq_refl I D32) as R32.
  pose proof (V (f + 40) 8%nat wpos (CJC.C8 (w64 wpos)) ltac:(lia) ltac:(lia) (le8_w64 wpos) eq_refl I D40) as R40.
  pose proof (V (f + 56) 8%nat wbase (CJC.C8 (w64 wbase)) ltac:(lia) ltac:(lia) (le8_w64 wbase) eq_refl I D56) as R56.
  pose proof (V (f + 88) 8%nat (f + 280) (CJC.C8 (w64 (f + 280))) ltac:(lia) ltac:(lia) (le8_w64 _) eq_refl I S88)
    as R88.
  pose proof (V (f + 96) 8%nat 1024 (CJC.C8 (w64 1024)) ltac:(lia) ltac:(lia) (le8_w64 _) eq_refl I S96) as R96.
  pose proof (V (f + 136) 4%nat om (CJC.C4 (w64 om)) ltac:(lia) ltac:(lia) (le4_w64 om) eq_refl I D136) as R136.
  pose proof (V (f + 140) 4%nat AU32M1 (CJC.C4 (Z_to_bv 64 (-1))) ltac:(lia) ltac:(lia) le4_lock eq_refl I S140)
    as R140.
  pose proof (V (f + 144) 4%nat AU32M1 (CJC.C4 (w64 AU32M1)) ltac:(lia) ltac:(lia) (le4_w64 _) eq_refl I S144)
    as R144.
  pose proof (rw_nil (cjstore H mem) (f + 232) ltac:(lia)) as R232.
  assert (T148 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 148) [CJC.CB 84 jx]) by (cons_at Rjx R232).
  assert (T144 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 144) [CJC.C4 (w64 AU32M1); CJC.CB 84 jx])
    by (cons_at R144 T148).
  assert (T140 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 140)
                   [CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at R140 T144).
  assert (T136 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 136)
                   [CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at R136 T140).
  assert (T104 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 104)
                   [CJC.CB 32 j104; CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx])
    by (cons_at Rj104 T136).
  assert (T96 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 96)
                   [CJC.C8 (w64 1024); CJC.CB 32 j104; CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1));
                    CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at R96 T104).
  assert (T88 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 88)
                   [CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024); CJC.CB 32 j104; CJC.C4 (w64 om);
                    CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at R88 T96).
  assert (T64 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 64)
                   [CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024); CJC.CB 32 j104; CJC.C4 (w64 om);
                    CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at Rj64 T88).
  assert (T56 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 56)
                   [CJC.C8 (w64 wbase); CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024); CJC.CB 32 j104;
                    CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx])
    by (cons_at R56 T64).
  assert (T48 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 48)
                   [CJC.CB 8 j48; CJC.C8 (w64 wbase); CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024);
                    CJC.CB 32 j104; CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx])
    by (cons_at Rj48 T56).
  assert (T40 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 40)
                   [CJC.C8 (w64 wpos); CJC.CB 8 j48; CJC.C8 (w64 wbase); CJC.CB 24 j64; CJC.C8 (w64 (f + 280));
                    CJC.C8 (w64 1024); CJC.CB 32 j104; CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1));
                    CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at R40 T48).
  assert (T32 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 32)
                   [CJC.C8 (w64 wend); CJC.C8 (w64 wpos); CJC.CB 8 j48; CJC.C8 (w64 wbase); CJC.CB 24 j64;
                    CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024); CJC.CB 32 j104; CJC.C4 (w64 om);
                    CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at R32 T40).
  assert (T24 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 24)
                   [CJC.CB 8 jc; CJC.C8 (w64 wend); CJC.C8 (w64 wpos); CJC.CB 8 j48; CJC.C8 (w64 wbase);
                    CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024); CJC.CB 32 j104; CJC.C4 (w64 om);
                    CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx]) by (cons_at Rjc T32).
  assert (T16 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 16)
                   [CJC.C8 (w64 0); CJC.CB 8 jc; CJC.C8 (w64 wend); CJC.C8 (w64 wpos); CJC.CB 8 j48;
                    CJC.C8 (w64 wbase); CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024); CJC.CB 32 j104;
                    CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1); CJC.CB 84 jx])
    by (cons_at R16 T24).
  assert (T8 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 8)
                   [CJC.C8 (w64 0); CJC.C8 (w64 0); CJC.CB 8 jc; CJC.C8 (w64 wend); CJC.C8 (w64 wpos);
                    CJC.CB 8 j48; CJC.C8 (w64 wbase); CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024);
                    CJC.CB 32 j104; CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1);
                    CJC.CB 84 jx]) by (cons_at R8 T16).
  assert (T4 : CJS.rw_cells tfibsegs (cjstore H mem) (f + 4)
                   [CJC.CB 4 jp; CJC.C8 (w64 0); CJC.C8 (w64 0); CJC.CB 8 jc; CJC.C8 (w64 wend); CJC.C8 (w64 wpos);
                    CJC.CB 8 j48; CJC.C8 (w64 wbase); CJC.CB 24 j64; CJC.C8 (w64 (f + 280)); CJC.C8 (w64 1024);
                    CJC.CB 32 j104; CJC.C4 (w64 om); CJC.C4 (Z_to_bv 64 (-1)); CJC.C4 (w64 AU32M1);
                    CJC.CB 84 jx]) by (cons_at Rjp T8).
  unfold MFS.mf_file. cons_at R0 T4.
Qed.

(* the FILE's 17 cells, one by one *)
Lemma mf_file_split : forall (m : word -> option byte) f fl jp jc we wp j48 wb j64 buf j104 mode lbf jx,
  CJS.rw_cells tfibsegs m f (MFS.mf_file fl jp jc we wp j48 wb j64 buf j104 mode lbf jx) ->
  length jp = 4%nat /\ length jc = 8%nat /\ length j48 = 8%nat /\ length j64 = 24%nat /\
  length j104 = 32%nat /\ length jx = 84%nat /\
  CJM.bytes_at tfibsegs m f (CJM.le4 fl) /\ CJM.bytes_at tfibsegs m (f + 4) jp /\
  CJM.bytes_at tfibsegs m (f + 8) (CJM.le8 (w64 0)) /\ CJM.bytes_at tfibsegs m (f + 16) (CJM.le8 (w64 0)) /\
  CJM.bytes_at tfibsegs m (f + 24) jc /\ CJM.bytes_at tfibsegs m (f + 32) (CJM.le8 we) /\
  CJM.bytes_at tfibsegs m (f + 40) (CJM.le8 wp) /\ CJM.bytes_at tfibsegs m (f + 48) j48 /\
  CJM.bytes_at tfibsegs m (f + 56) (CJM.le8 wb) /\ CJM.bytes_at tfibsegs m (f + 64) j64 /\
  CJM.bytes_at tfibsegs m (f + 88) (CJM.le8 (w64 buf)) /\ CJM.bytes_at tfibsegs m (f + 96) (CJM.le8 (w64 1024)) /\
  CJM.bytes_at tfibsegs m (f + 104) j104 /\ CJM.bytes_at tfibsegs m (f + 136) (CJM.le4 mode) /\
  CJM.bytes_at tfibsegs m (f + 140) (CJM.le4 (Z_to_bv 64 (-1))) /\ CJM.bytes_at tfibsegs m (f + 144) (CJM.le4 lbf) /\
  CJM.bytes_at tfibsegs m (f + 148) jx.
Proof.
  intros m f fl jp jc we wp j48 wb j64 buf j104 mode lbf jx R. unfold MFS.mf_file in R.
  peel R (f + 4) C0. peel R (f + 8) C4. peel R (f + 16) C8. peel R (f + 24) C16. peel R (f + 32) C24.
  peel R (f + 40) C32. peel R (f + 48) C40. peel R (f + 56) C48. peel R (f + 64) C56. peel R (f + 88) C64.
  peel R (f + 96) C88. peel R (f + 104) C96. peel R (f + 136) C104. peel R (f + 140) C136. peel R (f + 144) C140.
  peel R (f + 148) C144.
  destruct (rw_uncons_at _ _ (f + 232) _ _ R ltac:(cbn [CJC.csize]; lia)) as [C148 _].
  pose proof (rw1_wf _ _ _ C4) as W4. pose proof (rw1_wf _ _ _ C24) as W24. pose proof (rw1_wf _ _ _ C48) as W48.
  pose proof (rw1_wf _ _ _ C64) as W64. pose proof (rw1_wf _ _ _ C104) as W104. pose proof (rw1_wf _ _ _ C148) as W148.
  cbn [CJC.cell_wf] in W4, W24, W48, W64, W104, W148.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    first [ exact (rw1_bytes _ _ _ C0) | exact (rw1_bytes _ _ _ C4) | exact (rw1_bytes _ _ _ C8)
          | exact (rw1_bytes _ _ _ C16) | exact (rw1_bytes _ _ _ C24) | exact (rw1_bytes _ _ _ C32)
          | exact (rw1_bytes _ _ _ C40) | exact (rw1_bytes _ _ _ C48) | exact (rw1_bytes _ _ _ C56)
          | exact (rw1_bytes _ _ _ C64) | exact (rw1_bytes _ _ _ C88) | exact (rw1_bytes _ _ _ C96)
          | exact (rw1_bytes _ _ _ C104) | exact (rw1_bytes _ _ _ C136) | exact (rw1_bytes _ _ _ C140)
          | exact (rw1_bytes _ _ _ C144) | exact (rw1_bytes _ _ _ C148) ].
Qed.

(* GXA's side conditions on the FILE (vfprintf_mf_a_stmt WST, FL8, MODE) from the contract's words *)
Lemma mf_side_in : forall (m : word -> option byte) f k fl om wend wpos wbase pos len,
  0 <= f -> f + 1304 < 2 ^ 64 ->
  amf_k tfibsegs MS m f k -> amf_dyn tfibsegs MS m f fl om wend wpos wbase pos len ->
  ((wend = 0 /\ k = 0) \/ (wend = f + 1304 /\ wpos = f + 280 + k /\ wbase = f + 280)) /\
  Z.land fl 8 = 0 /\ (om = 0 \/ om = 4294967295) /\ 0 <= k <= 1024.
Proof.
  intros m f k fl om wend wpos wbase pos len Hf Hf1 ((_ & _ & _ & _ & Hfl & Hom & _) & Hwin) Hd.
  destruct Hd as (Rfl & Rom & Rwe & Rwp & Rwb & _ & _ & D0 & D136 & D32 & D40 & D56 & _ & _).
  assert (E8 : forall v1 v2 a, 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> val_mem tfibsegs m a 8 v1 ->
                 val_mem tfibsegs m a 8 v2 -> v1 = v2).
  { intros v1 v2 a H1 H2 V1 V2. pose proof (val_mem_inj m a 8 v1 v2 ltac:(lia) ltac:(lia) V1 V2) as E.
    change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E. }
  assert (E4 : forall v1 v2 a, 0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 -> val_mem tfibsegs m a 4 v1 ->
                 val_mem tfibsegs m a 4 v2 -> v1 = v2).
  { intros v1 v2 a H1 H2 V1 V2. pose proof (val_mem_inj m a 4 v1 v2 ltac:(lia) ltac:(lia) V1 V2) as E.
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in E. rewrite !Z.mod_small in E by lia. exact E. }
  unfold amf_win, amemfile_flags, amemfile_omode in *. unfold AMF_BUF, AMF_BUFSIZ, AF_NORD, AF_ERR, AU32M1 in *.
  split; [|split; [|split]].
  - destruct Hwin as [(-> & W32 & W40 & W56) | (Hk & W32 & W40 & W56)].
    + left. split; [exact (E8 wend 0 (f + 32) Rwe ltac:(lia) D32 W32) | reflexivity].
    + right. split; [|split].
      * replace (f + 1304) with (f + 280 + 1024) by lia.
        exact (E8 wend (f + 280 + 1024) (f + 32) Rwe ltac:(lia) D32 W32).
      * assert (L40 : 0 <= f + 280 + k < 2 ^ 64) by lia.
        exact (E8 wpos (f + 280 + k) (f + 40) Rwp L40 D40 W40).
      * assert (L56 : 0 <= f + 280 < 2 ^ 64) by lia.
        exact (E8 wbase (f + 280) (f + 56) Rwb L56 D56 W56).
  - unfold amemfile_flags in Hfl.
    destruct Hfl as [F|F]; [rewrite (E4 fl 4 (f + 0) Rfl ltac:(lia) D0 F) | rewrite (E4 fl (4 + 32) (f + 0) Rfl ltac:(lia) D0 F)];
      reflexivity.
  - unfold amemfile_omode in Hom.
    destruct Hom as [O|O]; [left; exact (E4 om 0 (f + 136) Rom ltac:(lia) D136 O)
                           | right; exact (E4 om 4294967295 (f + 136) Rom ltac:(lia) D136 O)].
  - destruct Hwin as [(-> & _) | (Hk & _)]; lia.
Qed.

(* ===================================================================================== *)
(* 4. the buffer                                                                           *)
(* ===================================================================================== *)

(* the pending bytes are byte values *)
Lemma pend_range : forall (m : word -> option byte) f pb,
  amf_pend tfibsegs m f pb -> Forall (fun c => 0 <= c < 256) pb.
Proof.
  intros m f pb HP. apply Forall_forall. intros c Hc. apply (In_nth pb c 0) in Hc as (i & Hi & <-).
  specialize (HP i Hi). unfold amf_rd in HP. destruct (mbyte tfibsegs m (f + AMF_BUF + Z.of_nat i)) as [b|];
    [|discriminate HP]. cbn in HP. injection HP as <-. exact (FMgxaSeamCells.byte_range b).
Qed.

Lemma mf_buf_in : forall (H : word -> bool) mem f pb,
  0 <= f -> f + 1304 <= 2 ^ 64 -> (forall a, f + 280 <= a < f + 1304 -> apresent H mem a) ->
  amf_pend tfibsegs (mrestrict H mem) f pb -> Z.of_nat (length pb) <= 1024 ->
  exists bj, Z.of_nat (length (zb8 pb)) + Z.of_nat (length bj) = 1024 /\
    CJS.rw_cells tfibsegs (cjstore H mem) (f + 280) [CJC.CB (length (zb8 pb)) (zb8 pb); CJC.CB (length bj) bj].
Proof.
  intros H mem f pb Hf Hf1 HP HPB Hk.
  destruct (rw1_junk H mem (f + 280 + Z.of_nat (length pb)) (Z.to_nat (1024 - Z.of_nat (length pb)))
              ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply HP; lia)) as (bj & Lbj & Rbj).
  exists bj. rewrite zb8_length, Lbj. split; [lia|].
  apply (rw_cons _ _ (f + 280 + Z.of_nat (length pb))); [| | cbn [CJC.csize]; lia].
  - apply rw1_intro; [cbn [CJC.cell_wf]; exact (zb8_length pb) | |].
    + cbn [CJC.cbytes]. apply bytes_at_of_view; [lia | lia |].
      intros i Hi. exact (HPB i Hi).
    + cbn [CJC.csize]. apply wr_at_of_writable; [lia | lia |].
      intros x Hx. apply apresent_wr, HP. lia.
  - apply (rw_cons _ _ (f + 1304) _ _ Rbj); [apply rw_nil; lia | cbn [CJC.csize]; lia].
Qed.

Lemma mf_buf_post : forall (H : word -> bool) (m' : word -> option byte) f pb o (bj : list byte),
  (forall a, f + 280 <= a < f + 1304 -> H (Z_to_bv 64 a) = false) ->
  Forall (fun c => 0 <= c < 256) pb -> Forall (fun c => 0 <= c < 256) o ->
  Z.of_nat (length pb + length o) <= 1024 ->
  CJS.rw_cells tfibsegs m' (f + 280)
    [CJC.CB (length (zb8 pb ++ zb8 o)) (zb8 pb ++ zb8 o); CJC.CB (length bj) bj] ->
  amf_pend tfibsegs (mrestrict H m') f (pb ++ o).
Proof.
  intros H m' f pb o bj HV Rpb Ro Hl R.
  destruct (rw_uncons_at _ _ (f + 280 + Z.of_nat (length (zb8 pb ++ zb8 o))) _ _ R ltac:(cbn [CJC.csize]; lia))
    as [R1 _].
  pose proof (rw1_bytes _ _ _ R1) as B. cbn [CJC.cbytes] in B.
  replace (zb8 pb ++ zb8 o) with (zb8 (pb ++ o)) in B by (unfold zb8; rewrite map_app; reflexivity).
  apply bytes_at_restrict with (H := H) in B; [| rewrite zb8_length, length_app; intros x Hx; apply HV; lia].
  destruct B as (_ & _ & B). intros i Hi. unfold amf_rd. unfold AMF_BUF.
  rewrite <- mrd_mbyte, (B i ltac:(rewrite zb8_length; exact Hi)).
  unfold zb8. rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
  rewrite (map_nth (Z_to_bv 8) (pb ++ o) 0 i). cbn [option_map]. f_equal.
  assert (Hc : 0 <= nth i (pb ++ o) 0 < 256).
  { apply (proj1 (Forall_forall (fun c => 0 <= c < 256) (pb ++ o))); [apply Forall_app; split; assumption|].
    apply nth_In. exact Hi. }
  rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 8) with 256. lia.
Qed.

(* ===================================================================================== *)
(* 5. the FILE out                                                                         *)
(* ===================================================================================== *)

(* GXA's post keeps the bytes of every cell but wend, wpos, wbase and the orientation *)
Lemma mf_file_same : forall (m1 m2 : word -> option byte) f fl jp jc we1 wp1 j48 wb1 j64 buf j104 mode1 lbf jx
    we2 wp2 wb2 mode2,
  CJS.rw_cells tfibsegs m1 f (MFS.mf_file fl jp jc we1 wp1 j48 wb1 j64 buf j104 mode1 lbf jx) ->
  CJS.rw_cells tfibsegs m2 f (MFS.mf_file fl jp jc we2 wp2 j48 wb2 j64 buf j104 mode2 lbf jx) ->
  forall x, f <= x < f + 232 -> ~ (f + 32 <= x < f + 48) -> ~ (f + 56 <= x < f + 64) -> ~ (f + 136 <= x < f + 140) ->
  CJM.mrd tfibsegs m1 (CJM.wa x) = CJM.mrd tfibsegs m2 (CJM.wa x).
Proof.
  intros m1 m2 f fl jp jc we1 wp1 j48 wb1 j64 buf j104 mode1 lbf jx we2 wp2 wb2 mode2 R1 R2 x Hx N1 N2 N3.
  destruct (mf_file_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1)
    as (Ljp & Ljc & Lj48 & Lj64 & Lj104 & Ljx & A0 & A4 & A8 & A16 & A24 & _ & _ & A48 & _ & A64 & A88 & A96 &
        A104 & _ & A140 & A144 & A148).
  destruct (mf_file_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2)
    as (_ & _ & _ & _ & _ & _ & B0 & B4 & B8 & B16 & B24 & _ & _ & B48 & _ & B64 & B88 & B96 &
        B104 & _ & B140 & B144 & B148).
  pose proof (CJM.length_le4 fl) as L4a. pose proof (CJM.length_le4 (Z_to_bv 64 (-1))) as L4b.
  pose proof (CJM.length_le4 lbf) as L4c. pose proof (CJM.length_le8 (w64 0)) as L8a.
  pose proof (CJM.length_le8 (w64 buf)) as L8b. pose proof (CJM.length_le8 (w64 1024)) as L8c.
  destruct (Z_lt_le_dec x (f + 4)); [exact (same_bytes _ _ _ _ x A0 B0 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 8)); [exact (same_bytes _ _ _ _ x A4 B4 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 16)); [exact (same_bytes _ _ _ _ x A8 B8 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 24)); [exact (same_bytes _ _ _ _ x A16 B16 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 32)); [exact (same_bytes _ _ _ _ x A24 B24 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 56)); [exact (same_bytes _ _ _ _ x A48 B48 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 88)); [exact (same_bytes _ _ _ _ x A64 B64 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 96)); [exact (same_bytes _ _ _ _ x A88 B88 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 104)); [exact (same_bytes _ _ _ _ x A96 B96 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 136)); [exact (same_bytes _ _ _ _ x A104 B104 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 144)); [exact (same_bytes _ _ _ _ x A140 B140 ltac:(lia))|].
  destruct (Z_lt_le_dec x (f + 148)); [exact (same_bytes _ _ _ _ x A144 B144 ltac:(lia))|].
  exact (same_bytes _ _ _ _ x A148 B148 ltac:(lia)).
Qed.

(* the contract's FILE words at the new window, from the old ones and GXA's post *)
Lemma mf_file_post : forall (H : word -> bool) mem (m' : word -> option byte) f k k' fl om om' wend wpos wbase pos len
    jp jc j48 j64 j104 jx,
  0 <= f -> f + 1304 < 2 ^ 64 ->
  (forall a, f <= a < f + 232 -> H (Z_to_bv 64 a) = false) ->
  amf_k tfibsegs MS (mrestrict H mem) f k ->
  amf_dyn tfibsegs MS (mrestrict H mem) f fl om wend wpos wbase pos len ->
  CJS.rw_cells tfibsegs (cjstore H mem) f
    (MFS.mf_file (w64 fl) jp jc (w64 wend) (w64 wpos) j48 (w64 wbase) j64 (f + 280) j104 (w64 om) (w64 AU32M1) jx) ->
  CJS.rw_cells tfibsegs m' f
    (MFS.mf_file (w64 fl) jp jc (w64 (f + 1304)) (w64 (f + 280 + k')) j48 (w64 (f + 280)) j64 (f + 280) j104
       (w64 om') (w64 AU32M1) jx) ->
  (forall x, f + 232 <= x < f + AMF_ZEROED -> mbyte tfibsegs (mrestrict H m') x = mbyte tfibsegs (mrestrict H mem) x) ->
  0 <= k' <= AMF_BUFSIZ -> (om' = 0 \/ om' = AU32M1) ->
  amf_k tfibsegs MS (mrestrict H m') f k' /\
  amf_dyn tfibsegs MS (mrestrict H m') f fl om' (f + AMF_BUF + AMF_BUFSIZ) (f + AMF_BUF + k') (f + AMF_BUF) pos len.
Proof.
  intros H mem m' f k k' fl om om' wend wpos wbase pos len jp jc j48 j64 j104 jx Hf Hf1 HV HK HD R1 R2 HC Hk' Hom'.
  set (m := mrestrict H mem) in *. set (mr := mrestrict H m').
  (* the unchanged bytes of the first AMF_ZEROED *)
  assert (FR : forall x, f <= x < f + AMF_ZEROED -> ~ (f + 32 <= x < f + 48) -> ~ (f + 56 <= x < f + 64) ->
                 ~ (f + 136 <= x < f + 140) -> mbyte tfibsegs mr x = mbyte tfibsegs m x).
  { intros x Hx N1 N2 N3. unfold AMF_ZEROED in Hx. destruct (Z_lt_le_dec x (f + 232)) as [L|L].
    - pose proof (mf_file_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2 R1 x ltac:(lia) N1 N2 N3) as E.
      rewrite !mrd_mbyte in E. transitivity (mbyte tfibsegs m' x).
      + unfold mr, mbyte, mrestrict. rewrite (HV x ltac:(lia)). reflexivity.
      + rewrite E. reflexivity.
    - apply HC. unfold AMF_ZEROED. lia. }
  assert (HVf : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= AMF_ZEROED ->
                  (off + Z.of_nat n <= 32 \/ 48 <= off) -> (off + Z.of_nat n <= 56 \/ 64 <= off) ->
                  (off + Z.of_nat n <= 136 \/ 140 <= off) ->
                  val_mem tfibsegs m (f + off) n v -> val_mem tfibsegs mr (f + off) n v).
  { intros off n v H0 H1 H2 H3 H4 Hv. apply (amf_val_mem_frame tfibsegs m mr (f + off) n v); [|exact Hv].
    intros x Hx. apply FR; unfold AMF_ZEROED in *; lia. }
  (* the new words *)
  destruct (mf_file_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B32 & B40 & _ & B56 & _ & _ & _ & _ & B136 & _ & _ & _).
  assert (NW : forall a (n : nat) v, f <= a -> a + Z.of_nat n <= f + 232 ->
                 CJM.bytes_at tfibsegs m' a (Z_to_le_bytes n v) -> val_mem tfibsegs mr a n v).
  { intros a n v Ha Hn Hb. apply val_mem_of_bytes. apply bytes_at_restrict; [|exact Hb].
    rewrite CJM.length_Z_to_le_bytes. intros x Hx. apply HV. lia. }
  rewrite le8_w64 in B32, B40, B56. rewrite le4_w64 in B136.
  pose proof (NW (f + 32) 8%nat (f + 1304) ltac:(lia) ltac:(lia) B32) as V32.
  pose proof (NW (f + 40) 8%nat (f + 280 + k') ltac:(lia) ltac:(lia) B40) as V40.
  pose proof (NW (f + 56) 8%nat (f + 280) ltac:(lia) ltac:(lia) B56) as V56.
  pose proof (NW (f + 136) 4%nat om' ltac:(lia) ltac:(lia) B136) as V136.
  destruct HK as ((Hf0 & Hfb & Hf16 & Hs & Hfl & _ & Hw & Hc) & _).
  destruct HD as (Rfl & _ & _ & _ & _ & Rpl & Rlen & D0 & _ & _ & _ & _ & Dpos & Dlen).
  unfold AMF_BUF, AMF_BUFSIZ, AMF_COOKIE, AMF_ZEROED, AU32M1 in *.
  split; [split|].
  - split; [exact Hf0|]. split; [exact Hfb|]. split; [exact Hf16|].
    split; [|split; [|split; [|split]]].
    + unfold amemfile_static in *. unfold AMF_COOKIE in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with |- _ /\ _ => split end; (apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | assumption]).
    + unfold amemfile_flags in *. destruct Hfl as [F|F]; [left|right]; (apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | exact F]).
    + unfold amemfile_omode. destruct Hom' as [-> | ->]; [left | right]; exact V136.
    + destruct Hw as (W8 & W16 & _). unfold amemfile_window, AMF_BUF, AMF_BUFSIZ.
      split; [apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | exact W8]|].
      split; [apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | exact W16]|].
      right. exists k'. split; [exact Hk'|]. split; [replace (f + 280 + 1024) with (f + 1304) by lia; exact V32|].
      split; [exact V40 | exact V56].
    + unfold amemfile_cookie, AMF_COOKIE in *. destruct Hc as (p & l & Hpl & Hl & C1 & C2). exists p, l.
      split; [exact Hpl|]. split; [exact Hl|].
      split; (apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | assumption]).
  - right. split; [exact Hk'|].
    split; [unfold AMF_BUF, AMF_BUFSIZ; replace (f + 280 + 1024) with (f + 1304) by lia; exact V32|].
    split; [exact V40 | exact V56].
  - split; [exact Rfl|]. split; [destruct Hom' as [-> | ->]; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Rpl|]. split; [exact Rlen|].
    split; [apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | exact D0]|].
    split; [exact V136|].
    split; [unfold AMF_BUF, AMF_BUFSIZ; replace (f + 280 + 1024) with (f + 1304) by lia; exact V32|].
    split; [exact V40|]. split; [exact V56|].
    unfold AMF_COOKIE. split; (apply HVf; [lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | assumption]).
Qed.

End s.
