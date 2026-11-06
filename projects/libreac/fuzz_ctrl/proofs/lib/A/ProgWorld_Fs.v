(* lib/A/ProgWorld_Fs.v -- scratch proofs of ProgWorld.v's ctl_fs_of_AR_stmt (Section FsOfAstack) and ctl_fp_of_AR_stmt
   (Section RtOfCore) (group fs), for a Theorem Labs lane to copy into ProgWorld.v.  ITERATION-ONLY; type-check evidence on the
   planning core only, never acceptance.  rule 24: no function proved.  These are bridge lemmas over the core's world
   (AR / aview / cell_holds), not proofs of any binary function. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK04 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0s YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.AB1v A.AsanRT A.Img0 A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation segs := A.AB1v.tfibsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   Byte-level glue: the core's view (aview) against ctrl's mrd / bytes_at / stk. *)

Lemma pw_bv8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma pw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Hz.
Qed.

Lemma pw_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma pw_nth_seq : forall n i s, (i < n)%nat -> nth_error (seq s n) i = Some (s + i)%nat.
Proof.
  induction n as [|n IH]; intros i s Hi; [lia|].
  destruct i as [|i]; cbn [seq nth_error]; [apply f_equal; lia|].
  rewrite IH by lia. apply f_equal. lia.
Qed.

(* A byte the view reads is visible, and mrd reads it. *)
Lemma pw_view_mrd : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a = Some v ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false /\
  Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros W m a v Hv.
  assert (Hh : lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false).
  { destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv. rewrite Hh in Hv.
    unfold lib.Reusable.YK11.seg_rom in Hv.
    rewrite (lib.Reusable.YK04.memory_read1_hidden segs (lib.Reusable.YA0n.w_H W) (lib.Reusable.YA0n.w_Hoff W) _ Hh)
      in Hv.
    cbn [option_map] in Hv. discriminate Hv. }
  split; [exact Hh|].
  rewrite (A.ProgWorld.aview_vis_mrd W m a Hh) in Hv.
  destruct (Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as <-. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma pw_bytes_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a : Z) (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> exists b, nth_error bs i = Some b /\
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (a + Z.of_nat i) = Some (bv_unsigned b)) ->
  Lib.Mem.bytes_at A.Img0.rsegs m a bs.
Proof.
  intros W m a bs Ha Hb H. split; [exact Ha|]. split; [exact Hb|].
  intros i Hi. destruct (H i Hi) as (b & Hn & Hv). rewrite Hn.
  destruct (pw_view_mrd W m _ _ Hv) as [_ Hm]. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm. exact Hm.
Qed.

Lemma pw_byte_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a = Some v -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Z_to_bv 8 v :: nil).
Proof.
  intros W m a v Hv Ha Hr. apply (pw_bytes_of_view W); [lia | cbn [length]; lia |].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  exists (Z_to_bv 8 v). split; [reflexivity|]. rewrite pw_bv8, Z.mod_small by lia.
  replace (a + Z.of_nat 0) with a by lia. exact Hv.
Qed.

(* An 8-byte cell the view reads, as ctrl's le8 word. *)
Lemma pw_word_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  (forall k, (k < 8)%nat ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (a + Z.of_nat k) = Some (lib.Reusable.YG0f.le_byte v 8 k)) ->
  0 <= a -> a + 8 <= 2 ^ 64 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros W m a v Hv Ha Hb. apply (pw_bytes_of_view W); [exact Ha | rewrite Lib.Mem.length_le8; cbn; lia |].
  intros i Hi. rewrite Lib.Mem.length_le8 in Hi.
  exists (Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat i))). split.
  - unfold Lib.Mem.le8, word_to_le_bytes. apply pw_nth_le_bytes. exact Hi.
  - rewrite (Hv i Hi). apply f_equal. rewrite pw_bv8, Z_to_bv_unsigned. unfold lib.Reusable.YG0f.le_byte.
    change (8 * Z.of_nat 8) with 64. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

(* An 8-byte cell row (c8 ea ev) of the core's world, as ctrl's le8 word at its address. *)
Lemma pw_c8_bytes : forall (B : lib.Reusable.YG0f.asyms) ly (W : lib.Reusable.YA0n.world segs)
    (m : word -> option byte) (ea ev : lib.Reusable.YG0f.aexp) (a v : Z),
  lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    (lib.Reusable.YG0f.c8 ea ev) ->
  lib.Reusable.YG0f.aeval B ly ea = a -> lib.Reusable.YG0f.aeval B ly ev = v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros B ly W m ea ev a v Hc Ea Ev Ha Hb. unfold lib.Reusable.YG0f.cell_holds in Hc.
  cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.c8] in Hc.
  rewrite Ea, Ev in Hc. exact (pw_word_of_view W m a v Hc Ha Hb).
Qed.

Lemma pw_stk_of_present : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a) ->
  Lib.Frame.stk A.Img0.rsegs m lo hi.
Proof.
  intros W m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hp a Ha) as [_ (b & Hb)]. unfold Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* A 1-byte cell row (z1 ea v) of the core's world, as ctrl's byte at its address. *)
Lemma pw_z1_bytes : forall (B : lib.Reusable.YG0f.asyms) ly (W : lib.Reusable.YA0n.world segs)
    (m : word -> option byte) (ea : lib.Reusable.YG0f.aexp) (a v : Z),
  lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    (lib.Reusable.YG0f.z1 ea v) ->
  lib.Reusable.YG0f.aeval B ly ea = a -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Z_to_bv 8 v :: nil).
Proof.
  intros B ly W m ea a v Hc Ea Ha Hv. unfold lib.Reusable.YG0f.cell_holds in Hc.
  cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.z1
       lib.Reusable.YG0f.c1 lib.Reusable.YG0f.aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite Ea in Hc. replace (a + Z.of_nat 0) with a in Hc by lia.
  assert (E : lib.Reusable.YG0f.le_byte v 1 0 = v).
  { unfold lib.Reusable.YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia. }
  rewrite E in Hc. exact (pw_byte_of_view W m a v Hc Ha Hv).
Qed.

(* A 4-byte cell row (z4 ea v) of the core's world, as ctrl's le4 word at its address. *)
Lemma pw_z4_bytes : forall (B : lib.Reusable.YG0f.asyms) ly (W : lib.Reusable.YA0n.world segs)
    (m : word -> option byte) (ea : lib.Reusable.YG0f.aexp) (a v : Z),
  lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    (lib.Reusable.YG0f.z4 ea v) ->
  lib.Reusable.YG0f.aeval B ly ea = a -> 0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= v < 2 ^ 32 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Lib.Mem.le4 (Z_to_bv 64 v)).
Proof.
  intros B ly W m ea a v Hc Ea Ha Hb Hv. unfold lib.Reusable.YG0f.cell_holds in Hc.
  cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.z4
       lib.Reusable.YG0f.c4 lib.Reusable.YG0f.aeval] in Hc.
  rewrite Ea in Hc.
  apply (pw_bytes_of_view W); [exact Ha | rewrite Lib.Mem.length_le4; lia |].
  intros i Hi. rewrite Lib.Mem.length_le4 in Hi.
  exists (Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat i))). split.
  - unfold Lib.Mem.le4. apply pw_nth_le_bytes. exact Hi.
  - rewrite (Hc i Hi). apply f_equal. rewrite pw_bv8, pw_u64 by lia. unfold lib.Reusable.YG0f.le_byte.
    change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* A run of n single bytes at a, a + 1, ..., as one byte list. *)
Lemma pw_bytes_of_singles : forall (m : word -> option byte) (a n : Z) (f : Z -> byte),
  0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall j, 0 <= j < n -> Lib.Mem.bytes_at A.Img0.rsegs m (a + j) (f j :: nil)) ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (map (fun i : nat => f (Z.of_nat i)) (seq 0 (Z.to_nat n))).
Proof.
  intros m a n f Ha Hn Hb H. split; [exact Ha|].
  rewrite length_map, length_seq, Z2Nat.id by exact Hn. split; [exact Hb|].
  intros i Hi.
  rewrite nth_error_map, pw_nth_seq by exact Hi. cbn [option_map Nat.add].
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & Hj).
  specialize (Hj 0%nat ltac:(cbn [length]; lia)). cbn [nth_error] in Hj.
  replace (a + Z.of_nat i) with (a + Z.of_nat i + Z.of_nat 0) by lia. exact Hj.
Qed.

Lemma pw_in_sym : forall c ly, In c A.AF0m.Tfib_const_sym -> In c (A.AF0m.Tfib_const ly).
Proof. intros c ly H. unfold A.AF0m.Tfib_const. apply in_or_app. left. exact H. Qed.

Lemma pw_in_abs : forall c ly, In c A.AF0m.Tfib_const_abs -> In c (A.AF0m.Tfib_const ly).
Proof. intros c ly H. unfold A.AF0m.Tfib_const. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

(* pw_mem stays an in_eq / in_cons walk: pw_in_owned walks owned_extents, a two-row list of Z * Z, which
   YConstIn's row_eqb (over acell) does not type.  The CONST-table walks go through in_const_tbl, one vm_compute of
   `existsb (row_eqb row) tbl` on a closed goal, because the const table has 2135 rows on the record (a Theorem Labs lane 06:52Z). *)
Ltac pw_mem := repeat (first [apply in_eq | apply in_cons]).
Ltac pw_sym := apply pw_in_sym; lib.Reusable.YConstIn.in_const_tbl.
Ltac pw_abs := apply pw_in_abs; lib.Reusable.YConstIn.in_const_tbl.
Ltac pw_in_owned := unfold lib.Reusable.YG0f.owned_extents; pw_mem.
Ltac pw_num := cbn [lib.Reusable.YG0f.aeval];
  unfold A.Prog.asan_stack_malloc_c.TLS_INDEX, A.Prog.asan_stack_malloc_c.DTLS_TPOFF,
    A.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR, A.Prog.asan_stack_malloc_c.MUSL_TLS_GET_ADDR,
    A.Prog.asan_stack_malloc_c.TSD_KEY_INITED, A.Prog.asan_stack_malloc_c.TSD_KEY, A.Prog.asan_stack_malloc_c.GOT_CF,
    A.Prog.asan_stack_malloc_c.CF, A.Prog.asan_stack_malloc_c.GOT_VERBOSITY, A.Prog.asan_stack_malloc_c.VERBOSITY,
    A.AsanRT.RT_TP; lia.

Local Notation ANum := lib.Reusable.YG0f.ANum (only parsing).
Local Notation ATp := lib.Reusable.YG0f.ATp (only parsing).
Local Notation ATsd := lib.Reusable.YG0f.ATsd (only parsing).
Local Notation AC := lib.Reusable.YG0f.AC (only parsing).
Local Notation AT := lib.Reusable.YG0f.AT (only parsing).
Local Notation AD := lib.Reusable.YG0f.AD (only parsing).
Local Notation AF := lib.Reusable.YG0f.AF (only parsing).

Section Fs.
Context {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* An application-memory extent lies below the allocation ceiling. *)
Lemma pw_ext_range : forall lo len, lib.Reusable.YG0f.in_app lo len -> 4096 <= lo /\ lo + len <= 0x7fffff800000.
Proof.
  intros lo len [H0 H]. pose proof lib.Reusable.YG0f.ASAN_CEIL_range as [CR _].
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in H. lia.
Qed.

Lemma pw_app_mem_F : forall ly a,
  lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_F ly) lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YG0f.ly_F ly <= a < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize -> A.AsanRT.app_mem a.
Proof.
  intros ly a [H0 H] Ha. pose proof lib.Reusable.YG0f.ASAN_CEIL_range as [CR _].
  unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in H. lia.
Qed.

Lemma pw_F_in_owned : forall ly,
  In (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize) (lib.Reusable.YG0f.owned_extents ly).
Proof. intros ly. unfold lib.Reusable.YG0f.owned_extents. right; right; right; left. reflexivity. Qed.

Lemma pw_F_not_img : forall ly a, lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.ly_F ly <= a < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize ->
  ~ lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.ly_img ly).
Proof.
  intros ly a LO Ha.
  assert (EX : Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.owned_extents ly)).
  { apply Exists_exists. exists (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize).
    split; [apply pw_F_in_owned | unfold lib.Reusable.YG0n.in_zr; cbn [fst snd]; lia]. }
  exact (proj2 (proj2 (lib.Reusable.YG0s.owned_extents_bound ly a LO EX))).
Qed.

(* The side stack is above the image: AR's layout keeps (ly_F, kFakeStackSize) apart from ly_img (lo_disj through
   YG0s.owned_extents_bound), and ALedger's al_img puts every segment of A, the last ending at 0x5fe000 = ASAN_GT
   (A.ProgBridge.rsegs_spans), inside ly_img. *)
Lemma pw_F_above : forall ly S (W : lib.Reusable.YA0n.world segs) m md,
  lib.Reusable.YG0n.AR segs B ly S W m md -> A.Prog.asan_stack_malloc_c.ASAN_GT <= lib.Reusable.YG0f.ly_F ly.
Proof.
  intros ly S W m md (M & L & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (lib.Reusable.YG0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) _ (pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (pw_ext_range _ _ F1) as [F0 _].
  assert (Hm : In (659456, 5623808) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs)).
  { rewrite A.ProgBridge.rsegs_spans. right; right; right; left. reflexivity. }
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  pose proof (lib.Reusable.YG0n.al_img _ _ _ _ L sg Hsg) as [_ J2]. rewrite E1, E2 in J2.
  unfold A.Prog.asan_stack_malloc_c.ASAN_GT. unfold lib.Reusable.YG0f.kImgLo in I1.
  destruct (Z_lt_le_dec (lib.Reusable.YG0f.ly_F ly) 65536) as [Hlt|Hge].
  - exfalso. apply (pw_F_not_img ly 65536 LO); [unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
    unfold lib.Reusable.YG0n.in_zr. lia.
  - destruct (Z_lt_le_dec (lib.Reusable.YG0f.ly_F ly)
      (fst (lib.Reusable.YG0f.ly_img ly) + snd (lib.Reusable.YG0f.ly_img ly))) as [Hlt2|Hge2].
    + exfalso. apply (pw_F_not_img ly (lib.Reusable.YG0f.ly_F ly) LO); [unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
      unfold lib.Reusable.YG0n.in_zr. lia.
    + lia.
Qed.

(* Every side-stack byte is present (am_areas over (AF 0, kFakeStackSize), off the image). *)
Lemma pw_F_present : forall ly S (W : lib.Reusable.YA0n.world segs) m md a,
  lib.Reusable.YG0n.AR segs B ly S W m md ->
  lib.Reusable.YG0f.ly_F ly <= a < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a.
Proof.
  intros ly S W m md a (M & L & _) Ha.
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) _ (pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (pw_ext_range _ _ F1) as [F0 F2].
  pose proof (lib.Reusable.YG0n.am_areas _ _ _ _ M) as AA. unfold lib.Reusable.YG0n.aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  apply Forall_cons_iff in AA as [AF _].
  specialize (AF (a - lib.Reusable.YG0f.ly_F ly) ltac:(cbn [snd]; lia)).
  cbn [fst lib.Reusable.YG0f.aeval] in AF.
  replace (lib.Reusable.YG0f.ly_F ly + 0 + (a - lib.Reusable.YG0f.ly_F ly)) with a in AF by lia.
  apply (lib.Reusable.YG0s.aview_present segs ly S md (lib.Reusable.YA0n.w_H W) m a L); [lia | | exact AF].
  apply (pw_F_not_img ly a LO). exact Ha.
Qed.

(* (1) ctl_fs_of_AR. *)
Lemma ctl_fs_of_AR : A.ProgWorld.ctl_fs_of_AR_stmt B.
Proof.
  intros Hgeom LAWS ly S W m md HAR HGT. cbv zeta.
  pose proof HAR as (M & L & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) _ (pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (pw_ext_range _ _ F1) as [F0 F2].
  assert (ESZ : A.Prog.asan_stack_malloc_c.FS_SIZE = lib.Reusable.YG0f.kFakeStackSize) by reflexivity.
  split; [|split].
  - (* stk over the whole side stack *)
    rewrite ESZ. apply (pw_stk_of_present W); [lia | lia |].
    intros a Ha. exact (pw_F_present ly S W m md a HAR Ha).
  - (* the flag bytes: am_flags (fs_flags_ok) *)
    intros c j Hc Hj.
    destruct (A.ProgWorld.ctl_fs_geom (lib.Reusable.YG0f.ly_F ly) (Z.of_nat c) j ltac:(lia))
      as (G1 & _ & _ & G4 & _).
    rewrite Nat2Z.id in G1, G4. rewrite G1 in Hj. rewrite G4.
    pose proof (lib.Reusable.YG0n.am_flags _ _ _ _ M (Z.of_nat c) j ltac:(lia) Hj) as Hf.
    unfold lib.Reusable.YG0f.flag_addr in Hf.
    pose proof (lib.Reusable.YG0s.flag_off_bounds (Z.of_nat c) j ltac:(lia) Hj) as FB.
    unfold lib.Reusable.YG0f.kFakeFlagsOff, lib.Reusable.YG0f.kFakeFramesOff in FB.
    unfold lib.Reusable.YG0f.kFakeStackSize in F2.
    apply (pw_byte_of_view W m _ _ Hf); [lia|].
    destruct (lib.Reusable.YG00.mem_pos (lib.Reusable.YG01.frames S) (Z.of_nat c) j); lia.
  - (* the hint words: am_cells over fs_cells *)
    intros c Hc.
    pose proof (lib.Reusable.YG0n.am_cells _ _ _ _ M) as XC. unfold lib.Reusable.YG0n.acells in XC.
    do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _].
    unfold lib.Reusable.YG0n.fs_cells in XF.
    apply Forall_cons_iff in XF as [_ XF]. apply Forall_cons_iff in XF as [_ XH].
    pose proof (lib.Reusable.YG01.wfs_hints _
      (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ (lib.Reusable.YG0n.am_wf _ _ _ _ M))) as [LH _].
    set (hs := lib.Reusable.YG00.fs_hint (lib.Reusable.YG00.st_fs S)) in *.
    assert (Hin : In (lib.Reusable.YG0f.z8 (lib.Reusable.YG0f.AF (8 * Z.of_nat c)) (nth c hs 0))
                   (map (fun iv : nat * Z => lib.Reusable.YG0f.z8 (lib.Reusable.YG0f.AF (8 * Z.of_nat (fst iv))) (snd iv))
                      (combine (seq 0 11) hs))).
    { apply in_map_iff. exists (c, nth c hs 0). split; [reflexivity|].
      replace (c, nth c hs 0) with (nth c (combine (seq 0 11) hs) (0%nat, 0)).
      - apply nth_In. rewrite length_combine, length_seq, LH. lia.
      - rewrite combine_nth by (rewrite length_seq, LH; reflexivity). rewrite seq_nth by lia. reflexivity. }
    pose proof (proj1 (Forall_forall _ _) XH _ Hin) as Hcell.
    exists (Z_to_bv 64 (nth c hs 0)).
    unfold A.Prog.asan_stack_malloc_c.fs_hint. unfold lib.Reusable.YG0f.kFakeStackSize in F2.
    apply (pw_c8_bytes B ly W m _ _ _ _ Hcell); [reflexivity | reflexivity | lia | lia].
Qed.

(* Rows of the bundle's const table (am_const under CtrlTSyms: as_const B ly = Tfib_const ly, AF0m.v:310). *)
Lemma pw_row : forall (TS : A.AF0m.CtrlTSyms B) ly S (W : lib.Reusable.YA0n.world segs) m md c,
  lib.Reusable.YG0n.AR segs B ly S W m md -> In c (A.AF0m.Tfib_const ly) ->
  lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) c.
Proof.
  intros TS ly S W m md c (M & _) Hin. pose proof (lib.Reusable.YG0n.am_const _ _ _ _ M) as C.
  rewrite (A.AF0m.ts_const B TS ly) in C. exact (proj1 (Forall_forall _ _) C c Hin).
Qed.

Lemma pw_c8_row : forall (TS : A.AF0m.CtrlTSyms B) ly S (W : lib.Reusable.YA0n.world segs) m md
    (ea ev : lib.Reusable.YG0f.aexp) (a v : Z),
  lib.Reusable.YG0n.AR segs B ly S W m md -> In (lib.Reusable.YG0f.c8 ea ev) (A.AF0m.Tfib_const ly) ->
  lib.Reusable.YG0f.aeval B ly ea = a -> lib.Reusable.YG0f.aeval B ly ev = v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros TS ly S W m md ea ev a v HAR Hin Ea Ev Ha Hb.
  exact (pw_c8_bytes B ly W m ea ev a v (pw_row TS ly S W m md _ HAR Hin) Ea Ev Ha Hb).
Qed.

Lemma pw_z1_row : forall (TS : A.AF0m.CtrlTSyms B) ly S (W : lib.Reusable.YA0n.world segs) m md
    (ea : lib.Reusable.YG0f.aexp) (a v : Z),
  lib.Reusable.YG0n.AR segs B ly S W m md -> In (lib.Reusable.YG0f.z1 ea v) (A.AF0m.Tfib_const ly) ->
  lib.Reusable.YG0f.aeval B ly ea = a -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Z_to_bv 8 v :: nil).
Proof.
  intros TS ly S W m md ea a v HAR Hin Ea Ha Hv.
  exact (pw_z1_bytes B ly W m ea a v (pw_row TS ly S W m md _ HAR Hin) Ea Ha Hv).
Qed.

Lemma pw_z4_row : forall (TS : A.AF0m.CtrlTSyms B) ly S (W : lib.Reusable.YA0n.world segs) m md
    (ea : lib.Reusable.YG0f.aexp) (a v : Z),
  lib.Reusable.YG0n.AR segs B ly S W m md -> In (lib.Reusable.YG0f.z4 ea v) (A.AF0m.Tfib_const ly) ->
  lib.Reusable.YG0f.aeval B ly ea = a -> 0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= v < 2 ^ 32 ->
  Lib.Mem.bytes_at A.Img0.rsegs m a (Lib.Mem.le4 (Z_to_bv 64 v)).
Proof.
  intros TS ly S W m md ea a v HAR Hin Ea Ha Hb Hv.
  exact (pw_z4_bytes B ly W m ea a v (pw_row TS ly S W m md _ HAR Hin) Ea Ha Hb Hv).
Qed.

Lemma pw_owned_range : forall ly e, lib.Reusable.YG0f.layout_ok ly -> In e (lib.Reusable.YG0f.owned_extents ly) ->
  4096 <= fst e /\ fst e + snd e <= 0x7fffff800000.
Proof.
  intros ly e LO Hin. apply pw_ext_range. exact (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) e Hin).
Qed.

(* (2) ctl_fp_of_AR.  Proved from AR directly (no ctl_tls_of_AR hypothesis): asan_tls_cells at DT = TP+32,
   TS = ly_tsd, C = ly_C, T = ly_T, DB = ly_D, k = 0 from the const rows (absolute AF0m.v:90-91, 101-103, 112,
   117-118, 135, 137, 174, 186; symbolic :24-28); the TP word from `c8 (ATp 0) (AF 0)` (:27); fs_place and fp_cls
   from ctl_fs_of_AR; FS+88 / FS+96 from fs_cells (YG0n.v:100-101). *)
Lemma ctl_fp_of_AR : A.ProgWorld.ctl_fp_of_AR_stmt B.
Proof.
  intros TS LAWS ly S W m md cs lo hi Wr D HAR Hcs Hlo Happ HdW HdD.
  pose proof HAR as (M & L & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (pw_F_above ly S W m md HAR) as HGT.
  pose proof (ctl_fs_of_AR A.ProgWorld.ctl_fs_geom LAWS ly S W m md HAR HGT) as HF. cbv zeta in HF.
  destruct HF as (Fs1 & Fs2 & Fs3).
  assert (Etp : lib.Reusable.YG0f.as_tp B = 0x5db810) by (rewrite (A.AF0m.ts_tp B TS); reflexivity).
  pose proof (lib.Reusable.YG0n.am_tsd _ _ _ _ M) as Htsd.
  rewrite (A.AF0m.ts_tsd B TS) in Htsd. unfold A.AF0m.TFIB_TSD in Htsd.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) _ (pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1.
  assert (HT : In (lib.Reusable.YG0f.ly_T ly, lib.Reusable.YG0f.kThreadObjSize) (lib.Reusable.YG0f.owned_extents ly))
    by pw_in_owned.
  assert (HC : In (lib.Reusable.YG0f.ly_C ly, 256) (lib.Reusable.YG0f.owned_extents ly)) by pw_in_owned.
  assert (HD : In (lib.Reusable.YG0f.ly_D ly, 4096) (lib.Reusable.YG0f.owned_extents ly)) by pw_in_owned.
  destruct (pw_owned_range ly _ LO (pw_F_in_owned ly)) as [RF0 RF1].
  destruct (pw_owned_range ly _ LO HT) as [RT0 RT1].
  destruct (pw_owned_range ly _ LO HC) as [RC0 RC1].
  destruct (pw_owned_range ly _ LO HD) as [RD0 RD1].
  cbn [fst snd] in RF0, RF1, RT0, RT1, RC0, RC1, RD0, RD1.
  unfold lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kThreadObjSize in RF1, RT1.
  (* the thread cells *)
  assert (X1 : A.Prog.asan_stack_malloc_c.asan_tls_cells m A.AsanRT.RT_TP (Z_to_bv 64 (A.AsanRT.RT_TP + 32))
                 (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd ly)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly))
                 (Z_to_bv 64 (lib.Reusable.YG0f.ly_T ly)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)) 0).
  { unfold A.Prog.asan_stack_malloc_c.asan_tls_cells.
    rewrite (pw_u64 (A.AsanRT.RT_TP + 32)) by (unfold A.AsanRT.RT_TP; lia).
    rewrite (pw_u64 (lib.Reusable.YG0f.ly_tsd ly)), (pw_u64 (lib.Reusable.YG0f.ly_C ly)),
      (pw_u64 (lib.Reusable.YG0f.ly_T ly)), (pw_u64 (lib.Reusable.YG0f.ly_D ly)) by lia.
    repeat (match goal with |- _ /\ _ => split end).
    - apply (proj2 (Lib.Mem.bytes_at_app _ _ _ _ _)). rewrite Lib.Mem.length_le8. split.
      + apply (pw_c8_row TS ly S W m md (ANum 0xa07b0) (ANum 1)); [exact HAR | pw_abs | pw_num ..].
      + replace (Z_to_bv 64 (-2048)) with (Z_to_bv 64 0xfffffffffffff800) by (apply bv_eq; vm_compute; reflexivity).
        apply (pw_c8_row TS ly S W m md (ANum 0xa07b8) (ANum 0xfffffffffffff800)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ANum 0xa1870) (ANum 0x98800)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ANum 0x5db808) (ANum 0x5db830)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ANum 0x5db838) (ANum 0x5dc010)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_z1_row TS ly S W m md (ANum 0xa80e0) _ 1); [exact HAR | pw_abs | pw_num ..].
    - lia.
    - lia.
    - apply (pw_z4_row TS ly S W m md (ANum 0xa80e4) _ 0); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ATp (-88)) (ATsd 0)); [exact HAR | pw_sym | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ATsd 0) (AC 0)); [exact HAR | pw_sym | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (AC 152) (AT 0)); [exact HAR | pw_sym | pw_num ..].
    - exists (Z_to_bv 64 0x5dbf48), (Z_to_bv 64 0x5dc024).
      apply (proj2 (Lib.Mem.bytes_at_app _ _ _ _ _)). rewrite Lib.Mem.length_le8. split.
      + apply (pw_c8_row TS ly S W m md (AT 48) (ANum 0x5dbf48)); [exact HAR | pw_sym | pw_num ..].
      + apply (pw_c8_row TS ly S W m md (AT 56) (ANum 0x5dc024)); [exact HAR | pw_sym | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ANum 0x9fac0) (ANum 0x13a3a8)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_z1_row TS ly S W m md (ANum 0x13a431) _ 1); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ANum 0x9fb20) (ANum 0x138318)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_z4_row TS ly S W m md (ANum 0x138318) _ 0); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ANum 0xa07c0) (ANum 8)); [exact HAR | pw_abs | pw_num ..].
    - apply (pw_c8_row TS ly S W m md (ATp 8) (AD 0)); [exact HAR | pw_sym | pw_num ..].
    - lia.
    - apply (pw_c8_row TS ly S W m md (AD 24) (ATp 0)); [exact HAR | pw_sym | pw_num ..]. }
  (* the TP word: `c8 (ATp 0) (AF 0)` *)
  assert (X2 : Lib.Mem.bytes_at A.Img0.rsegs m A.AsanRT.RT_TP (Lib.Mem.le8 (Z_to_bv 64 (lib.Reusable.YG0f.ly_F ly)))).
  { apply (pw_c8_row TS ly S W m md (ATp 0) (AF 0)); [exact HAR | pw_sym | pw_num ..]. }
  assert (X3 : A.Prog.asan_stack_malloc_c.fs_place m (lib.Reusable.YG0f.ly_F ly)).
  { unfold A.Prog.asan_stack_malloc_c.fs_place.
    split; [lia|]. split; [exact (lib.Reusable.YG0f.lo_F_al _ LO)|]. split; [exact HGT|]. split; [|exact Fs1].
    intros a Ha. apply (pw_app_mem_F ly a F1). unfold A.Prog.asan_stack_malloc_c.FS_SIZE in Ha.
    unfold lib.Reusable.YG0f.kFakeStackSize. lia. }
  (* FS+88 / FS+96: the first two rows of fs_cells *)
  pose proof (lib.Reusable.YG0n.am_cells _ _ _ _ M) as XC. unfold lib.Reusable.YG0n.acells in XC.
  do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _].
  unfold lib.Reusable.YG0n.fs_cells in XF.
  apply Forall_cons_iff in XF as [C88 XF]. apply Forall_cons_iff in XF as [C96 _].
  assert (X4 : Lib.Mem.bytes_at A.Img0.rsegs m (lib.Reusable.YG0f.ly_F ly + 88) (Lib.Mem.le8 (Z_to_bv 64 20))).
  { apply (pw_c8_bytes B ly W m (AF 88) (ANum lib.Reusable.YG00.kStackSizeLog) _ _ C88);
      [reflexivity | reflexivity | lia | lia]. }
  assert (X5 : Lib.Mem.bytes_at A.Img0.rsegs m (lib.Reusable.YG0f.ly_F ly + 96) (Z_to_bv 8 0 :: nil)).
  { apply (pw_z1_bytes B ly W m (AF 96) _ 0 C96); [reflexivity | lia | lia]. }
  (* fp_cls for every class of cs: the hint word and the fs_M c flag bytes *)
  assert (X6 : Forall (A.Prog.RcAsanFP.fp_cls m (lib.Reusable.YG0f.ly_F ly)) cs).
  { apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hc6. cbn beta in Hc6.
    unfold A.Prog.RcAsanFP.fp_cls. split; [exact Hc6|].
    destruct (Fs3 c ltac:(lia)) as (h & Hh).
    destruct (A.ProgWorld.ctl_fs_geom (lib.Reusable.YG0f.ly_F ly) (Z.of_nat c) 0 ltac:(lia)) as (G1 & _ & _ & G4 & _).
    rewrite Nat2Z.id in G1, G4.
    pose proof (lib.Reusable.YG0s.flags_ok (Z.of_nat c) ltac:(lia)) as [FO1 FO2].
    unfold lib.Reusable.YG0f.fs_flag_off, lib.Reusable.YG0f.kFakeFlagsOff in G4.
    assert (HM : 0 <= A.Prog.asan_stack_malloc_c.fs_M c)
      by (unfold A.Prog.asan_stack_malloc_c.fs_M; apply Z.pow_nonneg; lia).
    exists h, (map (fun i : nat => Z_to_bv 8 (if lib.Reusable.YG00.mem_pos (lib.Reusable.YG01.frames S) (Z.of_nat c)
                                              (Z.of_nat i) then 1 else 0))
                 (seq 0 (Z.to_nat (A.Prog.asan_stack_malloc_c.fs_M c)))).
    split; [exact Hh|]. split; [|split].
    - apply (pw_bytes_of_singles m _ _ (fun j => Z_to_bv 8 (if lib.Reusable.YG00.mem_pos (lib.Reusable.YG01.frames S)
                                                         (Z.of_nat c) j then 1 else 0)));
        [lia | exact HM | lia |].
      intros j Hj. cbn beta.
      replace (A.Prog.asan_stack_malloc_c.fs_flag (lib.Reusable.YG0f.ly_F ly) c 0 + j)
        with (A.Prog.asan_stack_malloc_c.fs_flag (lib.Reusable.YG0f.ly_F ly) c j)
        by (unfold A.Prog.asan_stack_malloc_c.fs_flag; lia).
      apply Fs2; [lia | exact Hj].
    - rewrite length_map, length_seq. apply Z2Nat.id. exact HM.
    - apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (i & <- & _).
      match goal with |- context [if ?x then _ else _] => destruct x end; [right | left]; reflexivity. }
  unfold A.Prog.RcAsanFP.fp.
  exists (Z_to_bv 64 (A.AsanRT.RT_TP + 32)), (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd ly)),
    (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly)), (Z_to_bv 64 (lib.Reusable.YG0f.ly_T ly)),
    (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)), 0.
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj Hlo (conj Happ (conj HdW HdD))))))))).
Qed.

(* ProgWorld.ctl_frame_above_img (statement in lib/A/ProgWorld.v Section FrameAbove): a live fake frame of any class lies
   above the image.  pw_F_above gives ASAN_GT <= ly_F ly; the frames' bounds 0 <= cid, 0 <= pos are AR's Wf (wfs_live,
   YG01.v:313); fs_frame_off cid pos >= 0. *)
Lemma ctl_frame_above_img : A.ProgWorld.ctl_frame_above_img_stmt B.
Proof.
  intros ly S W m md cid pos HAR Hin.
  pose proof (pw_F_above ly S W m md HAR) as HF. unfold A.Prog.asan_stack_malloc_c.ASAN_GT in HF.
  destruct HAR as (HARm & _).
  destruct HARm as [HWf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof (lib.Reusable.YG01.wfs_live _ (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ HWf)) as Hlive.
  pose proof (proj1 (Forall_forall _ _) Hlive (cid, pos) Hin) as Hpos. cbn [fst snd] in Hpos.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG0f.kFakeFramesOff.
  rewrite Z.shiftl_1_l. change lib.Reusable.YG00.kStackSizeLog with 20.
  assert (0 <= cid * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
  assert (0 <= pos * lib.Reusable.YG00.fs_frame_bytes cid).
  { apply Z.mul_nonneg_nonneg; [lia|]. unfold lib.Reusable.YG00.fs_frame_bytes. apply Z.shiftl_nonneg. lia. }
  lia.
Qed.

End Fs.
